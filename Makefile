LAKE ?= lake
PYTHON ?= python3
MUGDA2 := .lake/build/bin/mugda2
MUGDA2_REGRESSION := .lake/build/bin/mugda2-regression

.PHONY: all build check-axioms test-audit test-checker test-experiments test clean

# The audit and executable build share Lake's module output directory.
.NOTPARALLEL:

all: build

build:
	$(LAKE) build

check-axioms:
	$(PYTHON) scripts/audit_axioms.py --lake "$(LAKE)"

test-audit:
	$(PYTHON) scripts/test_audit_axioms.py

test-checker: build
	$(MUGDA2_REGRESSION)
	$(PYTHON) tests/checker_cli.py
	$(PYTHON) tests/coverage_matrix_cli.py

test-experiments: build
	$(PYTHON) scripts/test_experiments.py
	$(PYTHON) scripts/run_experiments.py docs/experiments/host-controls-v2.json --validate-only --report .lake/build/experiments/registration.json
	$(PYTHON) tests/experiments_runtime.py

test: check-axioms test-audit test-checker test-experiments
	@echo "=== Running Mugda2 Giralf / EXP-A Benchmark Executable ==="
	$(MUGDA2)

clean:
	$(LAKE) clean
