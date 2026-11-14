import Mugda2.Legacy.Core

namespace MugdaCore

/-! Executable fixtures from the pinned baseline verification suite -/

section VerificationSuite

/- `sized data SNat : Size -> Set { zero : (i : Size) -> SNat ($ i) ; succ : (i : Size) -> SNat i -> SNat ($ i) }` -/
def snatDecl : Declaration :=
  .DataDecl "SNat" .Sized .Ind [] [] (.Pi "i" .Size .Set)
    [ .mk "zero" (.Pi "i" .Size (.App (.Def "SNat") [.Succ (.Var "i")]))
    , .mk "succ" (.Pi "i" .Size (.Pi "" (.App (.Def "SNat") [.Var "i"]) (.App (.Def "SNat") [.Succ (.Var "i")])))
    ]

/- `fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i` (Euclidean subtraction, `examples/snat.ma`) -/
def subDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "sub"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "j" .Size
               (.Pi "" (.App (.Def "SNat") [.Var "j"])
                 (.App (.Def "SNat") [.Var "i"])))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "zero" [.VarP "i"], .VarP "j", .VarP "y"]
             (.App (.Con .Ind "zero") [.Var "i"])
       , .mk [.VarP "i", .VarP "x", .DotP (.Succ (.Var "j")), .ConP .Ind "zero" [.VarP "j"]]
             (.Var "x")
       , .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "succ" [.VarP "i", .VarP "x"],
              .DotP (.Succ (.Var "j")), .ConP .Ind "succ" [.VarP "j", .VarP "y"]]
             (.App (.Def "sub") [.Succ (.Var "i"), .Var "x", .Var "j", .Var "y"])
       ]
     )]

/- Counterexample `snat_mat_bug.ma` (Bugs 1 & 3):
    `fun loop : (i : Size) -> SNat i -> SNat i -> SNat #` -/
def snatMatBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loop"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.Pi "" (.App (.Def "SNat") [.Var "i"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [ .DotP (.Succ (.Succ (.Succ (.Var "i"))))
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")),
                   .ConP .Ind "succ" [.VarP "i", .VarP "z"]]]
             , .ConP .Ind "succ" [.DotP (.Succ (.Succ (.Var "i"))),
                 .ConP .Ind "succ" [.DotP (.Succ (.Var "i")), .VarP "w"]]
             ]
             (.App (.Def "loop")
               [ .Succ (.Succ (.Succ (.Var "i")))
               , .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]
               , .App (.Con .Ind "succ") [.Succ (.Succ (.Var "i")),
                   .App (.Con .Ind "succ") [.Succ (.Var "i"), .Var "w"]]
               ])
       ]
     )]

/- **Baseline fixture 1 (Positive Adequacy — `SNat` + `sub`)** -/

/- **Baseline fixture 2 (Counterexample Rejection — Bug 1 & Bug 3 `snat_mat_bug.ma`)** -/

/- `sized data Wrap (+ A : Set) : Size -> Set { wrap : (i : Size) -> A -> Wrap A ($ i) }` -/
def wrapDecl : Declaration :=
  .DataDecl "Wrap" .Sized .Ind [.SPos] [("A", .Set)] (.Pi "i" .Size .Set)
    [ .mk "wrap" (.Pi "i" .Size (.Pi "" (.Var "A") (.App (.Def "Wrap") [.Var "A", .Succ (.Var "i")]))) ]

/- Counterexample `loop_wrapped.ma` (Bugs 1 & 2) -/
def badWrapFunDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "badWrap"
         (.Pi "j" .Size
           (.Pi "" (.App (.Def "Wrap") [.Pi "" (.App (.Def "SNat") [.Var "j"]) (.App (.Def "SNat") [.Infty]), .Var "j"])
             (.Pi "" (.App (.Def "SNat") [.Var "j"])
               (.App (.Def "SNat") [.Infty]))))
     , [ .mk [.DotP (.Succ (.Var "i")), .ConP .Ind "wrap" [.VarP "i", .VarP "f"], .VarP "x"]
             (.App (.Var "f") [.Var "x"])
       ]
     )]

/- **Baseline fixture 3 (Counterexample Rejection — Bug 1 & Bug 2 `Wrap` Parameter Smuggling)** -/

/- Counterexample `llet_bug.ma` (Bug 4 — recursive call hidden inside a local `let` binding) -/
def lletBugDecl : Declaration :=
  .FunDecl .Ind
    [( .mk "loopLet"
         (.Pi "i" .Size
           (.Pi "" (.App (.Def "SNat") [.Var "i"])
             (.App (.Def "SNat") [.Infty])))
     , [ .mk [.VarP "i", .VarP "x"]
             (.LLet "y" (.App (.Def "SNat") [.Infty])
               (.App (.Def "loopLet") [.Var "i", .Var "x"])
               (.Var "y"))
       ]
     )]

/- **Baseline fixture 4 (Counterexample Rejection — Bug 4 `LLet` Call Extraction)** -/

/- **Baseline fixture 5 (End-to-End `.ma` Source — Euclidean Division `div` in `examples/snat.ma`)** -/
def snatDivSource : String := "
sized data SNat : Size -> Set
{ zero : (i : Size) -> SNat ($ i)
; succ : (i : Size) -> SNat i -> SNat ($ i)
}

fun sub : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ sub .($ i) (zero i) j y = zero i
; sub i x .($ j) (zero j) = x
; sub .($ i) (succ i x) .($ j) (succ j y) = sub ($ i) x j y
}

fun div : (i : Size) -> SNat i -> (j : Size) -> SNat j -> SNat i
{ div .($ i) (zero i) j y = zero i
; div .($ i) (succ i x) j y = succ i (div i (sub i x j y) j y)
}
"


/- **Baseline fixture 6 (End-to-End `.ma` Source Rejection — Cody Roux's `cody_nowraps.ma`)** -/
def codyNoWrapsSource : String := "
data Nat : Set
{ zero : Nat
; succ : Nat -> Nat
}

sized data O : Size -> Set
{ Z : (i : Size) -> O ($ i)
; S : (i : Size) -> O i -> O ($ i)
; L : (i : Size) -> (Nat -> O i) -> O ($ i)
; M : (i : Size) -> O i -> O i -> O ($ i)
}

fun loop : (i : Size) -> O i -> O i -> Nat
{ loop .($ ($ ($ i)))
       (M .($ ($ i)) (L .($ i) g) (Z .($ i)))
       (M .($ ($ i)) (L .($ i) f) (S .($ i) (S i z)))
  = loop ($ ($ i))
         (M ($ i) (L i g) (Z i))
         (M ($ i) (g zero) (f zero))
; loop i x y = zero
}
"


/- **Baseline fixture 7 (End-to-End Coinductive Fibonacci Stream & Evaluation — `examples/fib.ma`)** -/
def fibSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

fun add : Nat -> Nat -> Nat {
  add zero = \\y -> y;
  add (succ x) = \\y -> succ (add x y)
}

sized codata Stream : Size -> Set {
  cons : (i : Size) -> Nat -> Stream i -> Stream ($ i)
}

fun tail : Stream # -> Stream # {
  tail (cons .# x xs) = xs
}

fun head : Stream # -> Nat {
  head (cons .# x xs) = x
}

fun nth : Nat -> Stream # -> Nat {
  nth zero xs = head xs;
  nth (succ x) xs = nth x (tail xs)
}

let 1 : Nat = (succ zero)

cofun fib' : (x : Nat) -> (y : Nat) -> (i : Size) -> Stream i {
  fib' x y ($ i) = cons i x (fib' y (add x y) i)
}

let fib : Stream # = (fib' 1 1 #)
let 4 : Nat = (succ (succ (succ 1)))
eval let fib4 : Nat = nth 4 fib
"


/- **Baseline fixture 8 (End-to-End `ORDER_+` Matrix Termination — `addpair` and `ack` in `examples/natpair.ma`)** -/
def natpairSource : String := "
data Nat : Set {
  zero : Nat;
  succ : Nat -> Nat
}

data NatPair : Set {
  Pair : Nat -> Nat -> NatPair
}

fun addpair : NatPair -> Nat {
  addpair (Pair x zero) = x;
  addpair (Pair x (succ y)) = succ (addpair (Pair x y))
}

fun ack : NatPair -> Nat {
  ack (Pair zero y) = succ y;
  ack (Pair (succ x) zero) = ack (Pair x (succ zero));
  ack (Pair (succ x) (succ y)) = ack (Pair x (ack (Pair (succ x) y)))
}
"


end VerificationSuite

end MugdaCore
