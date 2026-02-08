import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Formula
import Mettapedia.OSLF.PiCalculus.Syntax

/-!
# π-Calculus OSLF Instance

Fifth example instantiation of the OSLF pipeline: the asynchronous, choice-free
π-calculus following Lybech (2022). Exercises the OSLF framework with:

- **Single sort**: `Proc` (atomic names are free variables, not a separate sort)
- **Six constructors**: `PiNil`, `PiPar`, `PiInp`, `PiOut`, `PiNu`, `PiRep`
- **One reduction rule**: COMM (+ ParCong for congruence)

## Sort Structure

```
  Proc (single sort)
   |
   +-- PiNil : 0-ary
   +-- PiPar : bag(Proc)
   +-- PiInp : Proc × [Proc → Proc]   (channel, abstraction)
   +-- PiOut : Proc × Proc             (channel, value)
   +-- PiNu  : [Proc → Proc]           (restriction binder)
   +-- PiRep : Proc × [Proc → Proc]    (channel, abstraction)
```

## Comparison with ρ-Calculus

| Feature | π-calculus | ρ-calculus |
|---------|-----------|------------|
| Sorts   | 1 (Proc)  | 2 (Proc, Name) |
| Names   | Atomic strings | Quoted processes @(P) |
| COMM    | P[z/y] (name sub) | P[@Q/y] (process sub + quote) |
| Restriction | PiNu (first-class) | Not built-in |
| Replication | PiRep (guarded) | Not built-in |

## References

- Lybech (2022), "Encodability and Separation for a Reflective Higher-Order Calculus"
- Milner (1999), "Communicating and Mobile Systems: the π-Calculus"
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.OSLF.PiCalculus.PiCalcInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar openBVar)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.Formula

/-! ## Language Definition -/

/-- π-Calculus: asynchronous, choice-free, with restriction and replication.

    - **Sorts**: `["Proc"]` (single sort; names are free variables)
    - **Proc constructors**: `PiNil`, `PiPar`, `PiInp`, `PiOut`, `PiNu`, `PiRep`
    - **Reductions**: COMM (x(y).P | x<z> → P[z/y]), plus ParCong -/
def piCalc : LanguageDef := {
  name := "PiCalc",
  types := ["Proc"],
  terms := [
    -- PiNil: inaction (0)
    { label := "PiNil", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },

    -- PiPar: parallel composition as flat bag {P₁ | P₂ | ...}
    { label := "PiPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"] },

    -- PiInp: input x(y).P where y is bound via λ
    { label := "PiInp", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Proc"),
                 .abstraction "body" (TypeExpr.arrow (TypeExpr.base "Proc") (TypeExpr.base "Proc"))],
      syntaxPattern := [.nonTerminal "x", .terminal "(", .terminal "y", .terminal ")",
                        .terminal ".", .nonTerminal "body"] },

    -- PiOut: async output x<z> (no continuation)
    { label := "PiOut", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Proc"), .simple "z" (TypeExpr.base "Proc")],
      syntaxPattern := [.nonTerminal "x", .terminal "<", .nonTerminal "z", .terminal ">"] },

    -- PiNu: restriction (νx)P where x is bound via λ
    { label := "PiNu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Proc") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },

    -- PiRep: guarded replication !x(y).P where y is bound via λ
    { label := "PiRep", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Proc"),
                 .abstraction "body" (TypeExpr.arrow (TypeExpr.base "Proc") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "!", .nonTerminal "x", .terminal "(", .terminal "y",
                        .terminal ")", .terminal ".", .nonTerminal "body"] }
  ],
  equations := [],   -- par laws handled by hashBag; no reflection equation
  rewrites := [
    -- Comm: x(y).P | x<z> ~> P[z/y]
    -- In LN: PiInp(x, λ.body) + PiOut(x, z) in a bag ~> body[z/BVar0] in a bag
    { name := "Comm",
      typeContext := [("x", TypeExpr.base "Proc"), ("body", TypeExpr.base "Proc"),
                      ("z", TypeExpr.base "Proc")],
      premises := [],
      left := .collection .hashBag [
        .apply "PiInp" [.fvar "x", .lambda (.fvar "body")],
        .apply "PiOut" [.fvar "x", .fvar "z"]
      ] (some "rest"),
      right := .collection .hashBag [
        .subst (.fvar "body") (.fvar "z")
      ] (some "rest") },

    -- ParCong: {S | rest} ~> {T | rest} if S ~> T
    { name := "ParCong",
      typeContext := [],
      premises := [.congruence (.fvar "S") (.fvar "T")],
      left := .collection .hashBag [.fvar "S"] (some "rest"),
      right := .collection .hashBag [.fvar "T"] (some "rest") }
  ]
}

/-! ## Helper: Pattern-level parallel composition (flattens bags) -/

/-- Parallel composition in π-Pattern representation. Flattens nested bags. -/
def piPar (P Q : Pattern) : Pattern :=
  match P, Q with
  | .collection .hashBag ps none, .collection .hashBag qs none =>
      .collection .hashBag (ps ++ qs) none
  | .collection .hashBag ps none, q =>
      .collection .hashBag (ps ++ [q]) none
  | p, .collection .hashBag qs none =>
      .collection .hashBag (p :: qs) none
  | p, q => .collection .hashBag [p, q] none

/-! ## Bridge: Process ↔ Pattern

Map between the inductive `Process` type (from PiCalculus.Syntax) and the
MeTTaIL `Pattern` type used by the OSLF engine. -/

/-- Map a π-calculus Process to a MeTTaIL Pattern.

    Uses locally nameless representation:
    - Free names become `.fvar x`
    - Bound names become `.bvar` via `closeFVar`
    - Input/restriction/replication use `.lambda` for binders -/
def piToPattern : Process → Pattern
  | .nil => .apply "PiNil" []
  | .par P Q => piPar (piToPattern P) (piToPattern Q)
  | .input x y P => .apply "PiInp" [.fvar x, .lambda (closeFVar 0 y (piToPattern P))]
  | .output x z => .apply "PiOut" [.fvar x, .fvar z]
  | .nu x P => .apply "PiNu" [.lambda (closeFVar 0 x (piToPattern P))]
  | .replicate x y P => .apply "PiRep" [.fvar x, .lambda (closeFVar 0 y (piToPattern P))]

/-! ## OSLF Type System (automatic) -/

/-- The rewrite system for π-calculus. -/
def piCalcRewriteSystem := langRewriteSystem piCalc

/-- The reduction span for π-calculus. -/
def piCalcSpan := langSpan piCalc

/-- The step-future modal operator ◇π. -/
def piCalcDiamond := langDiamond piCalc

/-- The step-past modal operator □π. -/
def piCalcBox := langBox piCalc

/-- The OSLF type system for π-calculus with proven Galois connection ◇π ⊣ □π. -/
def piCalcOSLF := langOSLF piCalc

/-- The Galois connection ◇π ⊣ □π: automatic from the framework. -/
theorem piCalcGalois : GaloisConnection (piCalcDiamond) (piCalcBox) :=
  langGalois piCalc

/-! ## Executable Demos

Verify that the OSLF rewrite engine correctly simulates π-calculus reduction. -/

-- Demo 1: COMM — x(y).0 | x<z> → 0
-- In MeTTaIL: {PiInp(.fvar "x", λ.PiNil), PiOut(.fvar "x", .fvar "z")} → {0}
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let process := Pattern.collection .hashBag [inp, out] none
  rewriteWithContext piCalc process
  -- Expected: [{PiNil[]}] (the .subst resolves to PiNil since body has no BVar 0)

-- Demo 2: COMM — x(y).y<w> | x<z> → z<w>
-- Input body uses BVar 0 (the bound y), which gets substituted with z
#eval
  let body := Pattern.apply "PiOut" [.bvar 0, .fvar "w"]  -- y<w> in LN
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda body]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let process := Pattern.collection .hashBag [inp, out] none
  rewriteWithContext piCalc process
  -- Expected: [{PiOut(.fvar "z", .fvar "w")}] (z<w>)

-- Demo 3: COMM with rest — x(y).0 | x<z> | P → 0 | P
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let extra := Pattern.apply "PiOut" [.fvar "a", .fvar "b"]
  let process := Pattern.collection .hashBag [inp, out, extra] none
  rewriteWithContext piCalc process
  -- Expected: [{PiNil[], PiOut(.fvar "a", .fvar "b")}]

-- Demo 4: No reduction — mismatched channels
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "y", .fvar "z"]  -- different channel!
  let process := Pattern.collection .hashBag [inp, out] none
  rewriteWithContext piCalc process
  -- Expected: [] (no reduction possible)

-- Demo 5: Reduction under par via ParCong
-- {x(y).0 | x<z> | P} — the ParCong rule allows COMM inside the bag
-- (This is already handled by Demo 3 since COMM matches in the bag)

-- Demo 6: piToPattern bridge — verify encoding of a simple process
#eval
  let P : Process := .par (.input "x" "y" .nil) (.output "x" "z")
  piToPattern P
  -- Expected: hashBag[PiInp(.fvar "x", λ.PiNil[]), PiOut(.fvar "x", .fvar "z")]

-- Demo 7: piToPattern + rewrite — full pipeline
-- x(y).0 | x<z> as Process → Pattern → reduce
#eval
  let P : Process := .par (.input "x" "y" .nil) (.output "x" "z")
  rewriteWithContext piCalc (piToPattern P)
  -- Expected: [{PiNil[]}] (COMM fires, body 0 has no y references)

-- Demo 8: piToPattern with non-trivial body
-- x(y).y<w> | x<z> → z<w>
#eval
  let P : Process := .par (.input "x" "y" (.output "y" "w")) (.output "x" "z")
  let pat := piToPattern P
  (pat, rewriteWithContext piCalc pat)
  -- Expected pattern has closeFVar applied, reduction produces z<w>

/-! ## Structural Theorems -/

/-- piCalc has exactly 6 constructors. -/
theorem piCalc_terms_length : piCalc.terms.length = 6 := by native_decide

/-- piCalc has one sort. -/
theorem piCalc_types_length : piCalc.types.length = 1 := by native_decide

/-- piCalc has 2 rewrite rules (COMM + ParCong). -/
theorem piCalc_rewrites_length : piCalc.rewrites.length = 2 := by native_decide

/-- piCalc has no equations (par laws handled by bag structure). -/
theorem piCalc_equations_length : piCalc.equations.length = 0 := by native_decide

end Mettapedia.OSLF.PiCalculus.PiCalcInstance
