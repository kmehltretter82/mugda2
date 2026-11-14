#!/usr/bin/env python3
"""Audit every declaration from the project's Lean modules using Lean's environment.

The report records kernel axiom dependencies, not a source-text approximation.
Only the Python standard library and the pinned Lean toolchain are required.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import subprocess
import sys
import tempfile


ALLOWED_AXIOMS = frozenset({"propext", "Quot.sound"})
EXCLUDED_DIRECTORIES = frozenset(
    {".git", ".lake", ".venv", "build", "node_modules", "scripts"}
)
REPORT_PREFIX = "MUGDA2_AXIOM_AUDIT "


class AuditError(Exception):
    """A failed build, malformed report, or trust-policy violation."""


def source_modules(root: Path) -> list[tuple[str, Path]]:
    """Discover modules without relying on namespace spelling or a theorem list."""
    sources = []
    for directory, children, files in os.walk(root):
        children[:] = sorted(
            child for child in children if child not in EXCLUDED_DIRECTORIES
        )
        for filename in sorted(files):
            if not filename.endswith(".lean") or filename == "lakefile.lean":
                continue
            path = Path(directory, filename)
            relative = path.relative_to(root).with_suffix("")
            module = ".".join(relative.parts)
            if not all(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", p) for p in relative.parts):
                raise AuditError(f"Unsupported module path: {path.relative_to(root)}")
            sources.append((module, path))
    if not sources:
        raise AuditError("No project Lean modules found")
    return sorted(sources)


def code_without_comments_and_strings(source: str) -> str:
    """Erase Lean comments and string literals while preserving line positions.

    Kernel dependency collection also checks expressions embedded in interpolated
    strings; this lexer is only the additional source ban on unsafe/partial code.
    """
    result = list(source)
    index = 0
    depth = 0
    in_string = False
    while index < len(source):
        if depth:
            if source.startswith("/-", index):
                result[index : index + 2] = "  "
                depth += 1
                index += 2
            elif source.startswith("-/", index):
                result[index : index + 2] = "  "
                depth -= 1
                index += 2
            else:
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif in_string:
            if source[index] == "\\" and index + 1 < len(source):
                result[index] = " "
                if source[index + 1] != "\n":
                    result[index + 1] = " "
                index += 2
            else:
                if source[index] == '"':
                    in_string = False
                if source[index] != "\n":
                    result[index] = " "
                index += 1
        elif source.startswith("--", index):
            end = source.find("\n", index)
            if end == -1:
                end = len(source)
            result[index:end] = " " * (end - index)
            index = end
        elif source.startswith("/-", index):
            result[index : index + 2] = "  "
            depth = 1
            index += 2
        elif source[index] == '"':
            result[index] = " "
            in_string = True
            index += 1
        else:
            index += 1
    return "".join(result)


def source_policy_violations(source: str) -> list[tuple[int, str]]:
    code = code_without_comments_and_strings(source)
    violations = []
    pattern = re.compile(
        r"(?<![\w`])(?:sorry|unsafe|partial|native_decide|Classical\.choice)(?!\w)"
    )
    for match in pattern.finditer(code):
        violations.append((code.count("\n", 0, match.start()) + 1, match.group()))
    return violations


def run(
    command: list[str], root: Path, *, source: str | None = None,
    environment: dict[str, str] | None = None,
) -> str:
    completed = subprocess.run(
        command, cwd=root, input=source, text=True, capture_output=True, check=False,
        env=None if environment is None else {**os.environ, **environment},
    )
    if completed.returncode:
        detail = (completed.stdout + completed.stderr).strip()
        raise AuditError(
            f"{shlex.join(command)} failed ({completed.returncode})\n{detail}"
        )
    if completed.stderr:
        print(completed.stderr, end="", file=sys.stderr)
    return completed.stdout


def audit_support_source() -> str:
    # A non-`module` audit root imports all private data, including declarations
    # in modern `module` files, and can also inspect legacy Lean modules.
    return "import Lean\n\n" + r'''
open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

private def auditDerivingOrigin? (env : Environment) (parent : Name)
    (index : ModuleIdx) : CommandElabM (Option Json) := do
  let some (.opaqueInfo parentValue) := env.find? parent | return none
  if parentValue.isUnsafe then return none
  let instanceName := parent.getPrefix
  let some (.defnInfo instanceValue) := env.find? instanceName | return none
  let instanceType := instanceValue.type.getForallBody
  let some className := instanceType.getAppFn.constName? | return none
  unless className == ``BEq || className == ``Repr do return none
  unless instanceValue.safety == DefinitionSafety.safe &&
      env.getModuleIdxFor? instanceName == some index &&
      (instanceValue.value.find? (·.isConstOf parent)).isSome do return none
  unless ← liftCoreM (Meta.isInstance instanceName) do return none
  let some target := instanceType.getAppArgs[0]? | return none
  let some targetName := target.getAppFn.constName? | return none
  let some (.inductInfo targetInfo) := env.find? targetName | return none
  unless env.getModuleIdxFor? targetName == some index &&
      (targetInfo.isNested || targetInfo.all.length > 1) do return none
  let some parentRanges ← findDeclarationRanges? parent | return none
  let some instanceRanges ← findDeclarationRanges? instanceName | return none
  let some targetRanges ← findDeclarationRanges? targetName | return none
  unless parentRanges.selectionRange == instanceRanges.selectionRange do return none
  let range := parentRanges.selectionRange
  let declaration := targetRanges.range
  return some <| Json.mkObj [
    ("class", toJson className.toString),
    ("instance", toJson instanceName.toString),
    ("inductive", toJson targetName.toString),
    ("line", toJson range.pos.line),
    ("column", toJson range.pos.column),
    ("endLine", toJson range.endPos.line),
    ("endColumn", toJson range.endPos.column),
    ("declarationLine", toJson declaration.pos.line),
    ("declarationColumn", toJson declaration.pos.column),
    ("declarationEndLine", toJson declaration.endPos.line),
    ("declarationEndColumn", toJson declaration.endPos.column)]

elab "#mugda2_audit " projectModule:ident : command => do
  let env := (← getEnv).setExporting false
  let projectModules : Array Name := #[projectModule.getId]
  let mut entries : Array Json := #[]
  let constants := env.constants.toList.toArray.qsort (fun a b => Name.lt a.1 b.1)
  for (name, info) in constants do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if projectModules.contains moduleName then
        let axioms := (← collectAxioms name).qsort Name.lt
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .inductInfo _ => "inductive"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
        let isPartial := match info with
          | .defnInfo value => value.safety == DefinitionSafety.partial
          | _ => false
        -- Lean emits a partial executable implementation even for a safe,
        -- kernel-checked recursive definition. Identify it using the compiler's
        -- naming API plus the parent's actual recursive/safety/type metadata.
        let mut compilerParent : Option String := none
        let mut compilerKind : Option String := none
        let mut derivingOrigin : Option Json := none
        if let some parent := Compiler.isUnsafeRecName? name then
          if let some parentInfo := env.find? parent then
            if let .defnInfo childInfo := info then
              if childInfo.safety == DefinitionSafety.partial &&
                  childInfo.type == parentInfo.type &&
                  childInfo.levelParams == parentInfo.levelParams &&
                  env.getModuleIdxFor? parent == some index then
                match parentInfo with
                | .defnInfo parentValue =>
                  if parentValue.safety == DefinitionSafety.safe then
                    if ← liftCoreM (Meta.isRecursiveDefinition parent) then
                      compilerParent := some parent.toString
                      compilerKind := some "total-recursion"
                | .opaqueInfo _ =>
                  -- Nested/mutual deriving uses a safe opaque logical wrapper
                  -- with a partial executable body. Recognize its tagged class
                  -- instance, referenced helper, inductive target, and common
                  -- source range; Python also verifies the deriving source text.
                  if let some origin ← auditDerivingOrigin? env parent index then
                    compilerParent := some parent.toString
                    compilerKind := some "partial-deriving"
                    derivingOrigin := some origin
                | _ => pure ()
        entries := entries.push <| Json.mkObj [
          ("name", toJson name.toString),
          ("module", toJson moduleName.toString),
          ("kind", toJson kind),
          ("unsafe", toJson info.isUnsafe),
          ("partial", toJson isPartial),
          ("compilerImplementationOf", toJson compilerParent),
          ("compilerImplementationKind", toJson compilerKind),
          ("derivingOrigin", toJson derivingOrigin),
          ("axioms", toJson (axioms.map Name.toString))]
  liftIO <| IO.println ("MUGDA2_AXIOM_AUDIT " ++ (toJson entries).compress)
'''


def audit_command(modules: list[str]) -> str:
    if len(modules) != 1:
        raise AuditError("Each audit command must inspect exactly one module")
    module = modules[0]
    return f"import {module}\nimport Mugda2AuditSupport\n#mugda2_audit {module}\n"


def prepare_support(root: Path, lake: list[str], lean_version: str) -> tuple[dict, dict]:
    """Compile the static command once; key the cache by exact source and Lean build."""
    source = audit_support_source()
    source_digest = hashlib.sha256(source.encode()).hexdigest()
    key = hashlib.sha256((lean_version + "\0" + source).encode()).hexdigest()
    cache = Path(__file__).resolve().parents[1] / ".lake/build/audit/support" / key
    cache.mkdir(parents=True, exist_ok=True)
    lean_file = cache / "Mugda2AuditSupport.lean"
    olean_file = cache / "Mugda2AuditSupport.olean"
    manifest_file = cache / "manifest.json"
    manifest = {}
    try:
        manifest = json.loads(manifest_file.read_text())
    except (OSError, json.JSONDecodeError):
        pass
    valid = (
        olean_file.is_file() and lean_file.is_file()
        and lean_file.read_text(encoding="utf-8") == source
        and manifest.get("sourceSha256") == source_digest
        and manifest.get("leanVersion") == lean_version
        and manifest.get("oleanSha256") == hashlib.sha256(olean_file.read_bytes()).hexdigest()
    )
    if not valid:
        print("Compiling the Lean axiom-audit command...", flush=True)
        lean_file.write_text(source, encoding="utf-8")
        with tempfile.NamedTemporaryFile(dir=cache, suffix=".olean", delete=False) as stream:
            compiled = Path(stream.name)
        try:
            output = run(
                [*lake, "env", "lean", "-R", str(cache), "-o", str(compiled), str(lean_file)], root
            )
            if output:
                print(output, end="")
            compiled.replace(olean_file)
        finally:
            compiled.unlink(missing_ok=True)
        manifest = {
            "sourceSha256": source_digest, "leanVersion": lean_version,
            "oleanSha256": hashlib.sha256(olean_file.read_bytes()).hexdigest(),
        }
        manifest_file.write_text(json.dumps(manifest, sort_keys=True) + "\n", encoding="utf-8")
    previous_path = os.environ.get("LEAN_PATH", "")
    search_path = str(cache) + (os.pathsep + previous_path if previous_path else "")
    return {"LEAN_PATH": search_path}, manifest


def verify_deriving_origin(entry: dict, source_texts: dict[str, str]) -> None:
    origin = entry.get("derivingOrigin")
    source = source_texts.get(entry["module"])
    if not isinstance(origin, dict) or source is None:
        raise AuditError(f"Missing deriving source evidence: {entry['module']}:{entry['name']}")
    class_name = origin.get("class")
    if class_name not in {"BEq", "Repr"}:
        raise AuditError("Unrecognized partial deriving class")
    lines = source.splitlines(keepends=True)

    def offset(line_key: str, column_key: str) -> int:
        line, column = origin.get(line_key), origin.get(column_key)
        if (
            not isinstance(line, int) or not isinstance(column, int)
            or line < 1 or line > len(lines) or column < 0
            or column > len(lines[line - 1].rstrip("\r\n"))
        ):
            raise AuditError("Invalid deriving source position")
        return sum(map(len, lines[: line - 1])) + column

    start, end = offset("line", "column"), offset("endLine", "endColumn")
    declaration_start = offset("declarationLine", "declarationColumn")
    declaration_end = offset("declarationEndLine", "declarationEndColumn")
    code = code_without_comments_and_strings(source)
    if not declaration_start <= start < end <= declaration_end or code[start:end] != class_name:
        raise AuditError("Deriving metadata does not select its class in the inductive declaration")
    deriving_tokens = list(re.finditer(r"\bderiving\b", code[declaration_start:start]))
    if not deriving_tokens:
        raise AuditError("Generated partial implementation has no source deriving clause")
    clause_start = declaration_start + deriving_tokens[-1].start()
    clause = code[clause_start:end]
    if not re.fullmatch(
        r"deriving\s+(?:(?:expose\s+)?[\w.]+\s*,\s*)*(?:expose\s+)?" + class_name,
        clause,
    ):
        raise AuditError("Generated partial implementation does not originate in a deriving class list")


def validate_declarations(
    declarations: object, modules: list[str], source_texts: dict[str, str] | None = None
) -> list[dict]:
    if not isinstance(declarations, list) or not declarations:
        raise AuditError("Lean returned no project declarations")
    seen_declarations = set()
    by_identity = {}
    violations = []
    for entry in declarations:
        if (
            not isinstance(entry, dict)
            or not isinstance(entry.get("name"), str)
            or entry.get("module") not in modules
            or not isinstance(entry.get("axioms"), list)
            or not all(isinstance(axiom, str) for axiom in entry["axioms"])
            or not isinstance(entry.get("unsafe"), bool)
            or not isinstance(entry.get("partial"), bool)
        ):
            raise AuditError("Malformed declaration in Lean audit output")
        name = entry["name"]
        key = (entry["module"], name)
        if key in seen_declarations:
            raise AuditError(f"Duplicate declaration in Lean audit output: {key}")
        seen_declarations.add(key)
        by_identity[key] = entry
        display_name = f"{entry['module']}:{name}"
        forbidden = set(entry["axioms"]) - ALLOWED_AXIOMS
        if forbidden:
            violations.append(f"{display_name}: unapproved axioms {', '.join(sorted(forbidden))}")
        if entry.get("kind") == "axiom":
            violations.append(f"{display_name}: project axiom declaration")
        compiler_parent = entry.get("compilerImplementationOf")
        compiler_kind = entry.get("compilerImplementationKind")
        if compiler_parent is not None and (
            not isinstance(compiler_parent, str)
            or entry.get("kind") != "definition"
            or not entry["partial"]
            or name != compiler_parent + "._unsafe_rec"
            or compiler_kind not in {"total-recursion", "partial-deriving"}
        ):
            raise AuditError(f"Invalid compiler implementation metadata: {display_name}")
        if entry["unsafe"] or (entry["partial"] and compiler_parent is None):
            violations.append(f"{display_name}: unsafe or partial declaration")
    for entry in declarations:
        compiler_parent = entry.get("compilerImplementationOf")
        if compiler_parent is not None:
            parent = by_identity.get((entry["module"], compiler_parent))
            expected_kind = "opaque" if entry["compilerImplementationKind"] == "partial-deriving" else "definition"
            if (
                parent is None or parent.get("kind") != expected_kind
                or parent["unsafe"] or parent["partial"]
            ):
                raise AuditError(
                    f"Compiler implementation has no audited safe parent: {entry['module']}:{entry['name']}"
                )
            if entry["compilerImplementationKind"] == "partial-deriving":
                verify_deriving_origin(entry, source_texts or {})
    # A module can legitimately consist solely of imports (Mugda2.lean).
    if not any(entry.get("kind") == "theorem" for entry in declarations):
        raise AuditError("No project theorems were audited")
    if violations:
        raise AuditError("Trust audit failed:\n" + "\n".join(violations))
    return declarations


def audit(root: Path, lake: list[str], report: Path) -> dict:
    sources = source_modules(root)
    source_digests = {}
    violations = []
    for _, path in sources:
        source = path.read_text(encoding="utf-8")
        source_digests[path.relative_to(root).as_posix()] = hashlib.sha256(
            path.read_bytes()
        ).hexdigest()
        for line, token in source_policy_violations(source):
            violations.append(f"{path.relative_to(root)}:{line}: forbidden token {token}")
    if violations:
        raise AuditError("Source policy failed:\n" + "\n".join(violations))
    modules = [module for module, _ in sources]
    # Build every discovered module, including files not yet imported by the root.
    # subprocess return codes are checked directly: no shell pipeline can hide errors.
    build_output = run([*lake, "build", *modules], root)
    if build_output:
        print(build_output, end="")
    lean_version = run([*lake, "env", "lean", "--version"], root).strip()
    support_environment, support_manifest = prepare_support(root, lake, lean_version)
    declarations = []
    # Executable roots may legitimately define the same global `main`. Importing
    # them together can shadow declarations or fail before we inspect them, so
    # collect each module's own declarations in a separate Lean environment.
    for module in modules:
        output = run(
            [*lake, "env", "lean", "--stdin"], root, source=audit_command([module]),
            environment=support_environment,
        )
        payloads = [
            line[len(REPORT_PREFIX) :]
            for line in output.splitlines()
            if line.startswith(REPORT_PREFIX)
        ]
        if len(payloads) != 1:
            raise AuditError(
                f"Expected one Lean audit payload for {module}; received {len(payloads)}\n{output}"
            )
        try:
            entries = json.loads(payloads[0])
        except json.JSONDecodeError as error:
            raise AuditError(f"Invalid Lean JSON audit output for {module}: {error}") from error
        if not isinstance(entries, list) or any(
            not isinstance(entry, dict) or entry.get("module") != module
            for entry in entries
        ):
            raise AuditError(f"Malformed or wrong-module declarations returned for {module}")
        declarations.extend(entries)
    declarations = validate_declarations(
        declarations, modules,
        {module: path.read_text(encoding="utf-8") for module, path in sources},
    )
    declarations.sort(key=lambda entry: (entry["module"], entry["name"]))
    current_sources = {
        path.relative_to(root).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
        for _, path in source_modules(root)
    }
    if current_sources != source_digests:
        raise AuditError("Lean sources changed during the audit; rerun against a stable worktree")
    result = {
        "schemaVersion": 1,
        "leanVersion": lean_version,
        "auditSupport": support_manifest,
        "toolchain": (root / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "buildInputs": {
            filename: hashlib.sha256((root / filename).read_bytes()).hexdigest()
            for filename in ("lean-toolchain", "lakefile.lean", "lake-manifest.json")
            if (root / filename).is_file()
        },
        "allowedAxioms": sorted(ALLOWED_AXIOMS),
        "modules": modules,
        "sources": source_digests,
        "declarationCount": len(declarations),
        "theoremCount": sum(entry["kind"] == "theorem" for entry in declarations),
        "compilerImplementationCount": sum(
            entry.get("compilerImplementationOf") is not None for entry in declarations
        ),
        "partialDerivingImplementationCount": sum(
            entry.get("compilerImplementationKind") == "partial-deriving" for entry in declarations
        ),
        "runtimeTrustBoundary": (
            "Compiler-generated recursive implementations are runtime artifacts. "
            "Partial BEq/Repr deriving implementations have safe opaque logical wrappers; "
            "kernel axiom checks do not prove their runtime termination or equivalence to those wrappers. "
            "Native execution also trusts the Lean compiler and runtime."
        ),
        "declarations": declarations,
    }
    # Publish only a complete passing report, atomically and without shared /tmp files.
    report.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        mode="w", encoding="utf-8", dir=report.parent, prefix=".axioms-", delete=False
    ) as stream:
        temporary = Path(stream.name)
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    try:
        temporary.replace(report)
    finally:
        temporary.unlink(missing_ok=True)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--lake", default="lake", help="Lake executable and optional arguments")
    parser.add_argument("--report", type=Path, default=Path(".lake/build/audit/axioms.json"))
    options = parser.parse_args()
    root = options.root.resolve()
    report = options.report if options.report.is_absolute() else root / options.report
    # A failed run must not leave an older passing report at the advertised path.
    report.unlink(missing_ok=True)
    try:
        result = audit(root, shlex.split(options.lake), report)
    except (AuditError, OSError) as error:
        print(f"Axiom audit error: {error}", file=sys.stderr)
        return 1
    print(
        f"Audited {result['theoremCount']} theorems and "
        f"{result['declarationCount']} total declarations from {len(result['modules'])} modules."
    )
    print(
        f"Labeled {result['compilerImplementationCount']} compiler-generated recursive implementations; "
        "their safe parents and axiom dependencies were also checked."
    )
    if result["partialDerivingImplementationCount"]:
        print(
            f"Of these, {result['partialDerivingImplementationCount']} are partial BEq/Repr deriving "
            "runtime artifacts with verified source origins; see runtimeTrustBoundary in the report."
        )
    print(f"Allowed kernel axioms: {', '.join(result['allowedAxioms'])}. Report: {report}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
