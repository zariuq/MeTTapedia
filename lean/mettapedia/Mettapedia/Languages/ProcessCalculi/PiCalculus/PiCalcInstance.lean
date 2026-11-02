import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Match
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.OSLF.Framework.ConstructorCategory
import Mettapedia.OSLF.Framework.DerivedTyping
import Mettapedia.OSLF.Formula
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Syntax

/-!
# π-Calculus OSLF Instance

Fifth example instantiation of the OSLF pipeline: the asynchronous, choice-free
π-calculus following Lybech (2022). Exercises the OSLF framework with:

- **Two sorts**: `Proc` and `Name`; names are variables of the name sort, bound by input and restriction
- **Six constructors**: `PiNil`, `PiPar`, `PiInp`, `PiOut`, `PiNu`, `PiRep`; replication `!P` takes any process
- **Equations**: the laws of restriction (inaction, exchange, scope extrusion) and of replication (unfolding
  `!P = {P, !P}`, `!0 = 0`, `!!P = !P`, `!{P, Q} = {!P, !Q}`, `{!P, !P} = !P`), besides the parallel laws of its bag
- **Base reduction rule**: COMM, with descent through parallel composition and restriction

## Operational scope

The authored internal relation supplies COMM, with descent through parallel composition and restriction. A
replicated process takes part in a reaction through its unfolding, a law of the static theory: a server `!x(y).P`
receives as the copy `x(y).P` beside it. Raw rule firings retain their bag representation, whereas the named relation
uses structural congruence, including the parallel unit. `PresentationBoundary` records the remaining operational
boundaries. The generated OSLF belongs to the authored rules read modulo the declared laws.

## Sort Structure

```
  Proc
   |
   +-- PiNil : 0-ary
   +-- PiPar : bag(Proc)
   +-- PiInp : Name × [Name → Proc]   (channel, abstraction)
   +-- PiOut : Name × Name             (channel, value)
   +-- PiNu  : [Name → Proc]           (restriction binder)
   +-- PiRep : Proc                     (replication)
  Name: variables only
```

## Comparison with ρ-Calculus

| Feature | π-calculus | ρ-calculus |
|---------|-----------|------------|
| Sorts   | 2 (Proc, Name) | 2 (Proc, Name) |
| Names   | Variables of the name sort | Quoted processes @(P) |
| COMM    | P[z/y] (name sub) | P[@Q/y] (process sub + quote) |
| Restriction | PiNu (first-class) | Not built-in |
| Replication | PiRep, with its laws | Not built-in |

## References

- Lybech (2022), "Encodability and Separation for a Reflective Higher-Order Calculus"
- Milner (1999), "Communicating and Mobile Systems: the π-Calculus"
- Meredith & Stay, "Operational Semantics in Logical Form"
-/

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar openBVar)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.ConstructorCategory
open Mettapedia.OSLF.Framework.DerivedTyping
open Mettapedia.OSLF.Formula

/-! ## Language Definition -/

/-! ## Structural laws of restriction

Restricting a name in inaction gives inaction, two restrictions exchange, and a restriction extrudes over a parallel
component. Each declares which bound names its metavariables may use: the exchanged body takes the two names in the
other order, and the extruded-over components may not use the restricted name. -/

/-- `(νx) 0 = 0` -/
def restrictionNil : Equation where
  name := "RestrictionNil"
  typeContext := []
  premises := []
  left := .apply "PiNu" [.lambda none (.apply "PiNil" [])]
  right := .apply "PiNil" []

/-- `(νx)(νy) P = (νy)(νx) P` -/
def restrictionExchange : Equation where
  name := "RestrictionExchange"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none (.fvar "P")])]
  right := .apply "PiNu" [.lambda none (.apply "PiNu" [.lambda none (.fvar "P")])]
  bindings := some
    { dependencies := [("P", [.base "Name", .base "Name"])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0, 0], arguments := [.bvar 0, .bvar 1] },
         { name := "P", site := .right, path := [0, 0, 0, 0], arguments := [.bvar 1, .bvar 0] }] }

/-- `{(νx) P | rest} = (νx) {P | rest}`, the rest not using `x` -/
def scopeExtrusion : Equation where
  name := "ScopeExtrusion"
  typeContext := [("P", .base "Proc"), ("rest", .collection .hashBag (.base "Proc"))]
  premises := []
  left := .collection .hashBag [.apply "PiNu" [.lambda none (.fvar "P")]] (some "rest")
  right := .apply "PiNu" [.lambda none (.collection .hashBag [.fvar "P"] (some "rest"))]
  bindings := some
    { dependencies := [("P", [.base "Name"]), ("rest", [])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .left, path := [1], arguments := [] },
         { name := "P", site := .right, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .right, path := [0, 0, 1], arguments := [] }] }

/-! ## Laws of replication

A replicated process stands for unboundedly many copies of itself: it unfolds into a copy beside itself, replicated
inaction is inaction, replication is idempotent, it distributes over parallel composition, and two replications of one
process are one. Every law relates strongly bisimilar processes. -/

/-- `!P = {P, !P}` -/
def replicationUnfold : Equation where
  name := "ReplicationUnfold"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "PiRep" [.fvar "P"]
  right := .collection .hashBag [.fvar "P", .apply "PiRep" [.fvar "P"]] none

/-- `!0 = 0` -/
def replicationNil : Equation where
  name := "ReplicationNil"
  typeContext := []
  premises := []
  left := .apply "PiRep" [.apply "PiNil" []]
  right := .apply "PiNil" []

/-- `!!P = !P` -/
def replicationTwice : Equation where
  name := "ReplicationTwice"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "PiRep" [.apply "PiRep" [.fvar "P"]]
  right := .apply "PiRep" [.fvar "P"]

/-- `!{P, Q} = {!P, !Q}` -/
def replicationPar : Equation where
  name := "ReplicationPar"
  typeContext := [("P", .base "Proc"), ("Q", .base "Proc")]
  premises := []
  left := .apply "PiRep" [.collection .hashBag [.fvar "P", .fvar "Q"] none]
  right := .collection .hashBag [.apply "PiRep" [.fvar "P"], .apply "PiRep" [.fvar "Q"]] none

/-- `{!P, !P} = !P` -/
def replicationIdempotent : Equation where
  name := "ReplicationIdempotent"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .collection .hashBag [.apply "PiRep" [.fvar "P"], .apply "PiRep" [.fvar "P"]] none
  right := .apply "PiRep" [.fvar "P"]

/-- π-Calculus: asynchronous, choice-free, with restriction and replication.

    - **Sorts**: `["Proc", "Name"]` (names are variables of the name sort)
    - **Proc constructors**: `PiNil`, `PiPar`, `PiInp`, `PiOut`, `PiNu`, `PiRep`
    - **Equations**: restriction of inaction, exchange of restrictions and scope extrusion; unfolding, inaction,
      idempotence, distribution and duplication of replication; besides the parallel laws of its bag
    - **Reductions**: COMM, ParCong and ResCong -/
def piCalc : LanguageDef := {
  name := "PiCalc",
  types := ["Proc", "Name"],
  terms := [
    -- PiNil: inaction (0)
    { label := "PiNil", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },

    -- PiPar: parallel composition as flat bag {P₁ | P₂ | ...}
    { label := "PiPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "PiNil" } },

    -- PiInp: input x(y).P where y is bound via λ
    { label := "PiInp", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Name"),
                 .abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.nonTerminal "x", .terminal "(", .terminal "y", .terminal ")",
                        .terminal ".", .nonTerminal "body"] },

    -- PiOut: async output x<z> (no continuation)
    { label := "PiOut", category := "Proc",
      params := [.simple "x" (TypeExpr.base "Name"), .simple "z" (TypeExpr.base "Name")],
      syntaxPattern := [.nonTerminal "x", .terminal "<", .nonTerminal "z", .terminal ">"] },

    -- PiNu: restriction (νx)P where x is bound via λ
    { label := "PiNu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },

    -- PiRep: replication !P of any process
    { label := "PiRep", category := "Proc",
      params := [.simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "!", .nonTerminal "p"] }
  ],
  -- The parallel monoid laws come from the declared collection algebra.
  equations := [restrictionNil, restrictionExchange, scopeExtrusion, replicationUnfold, replicationNil,
    replicationTwice, replicationPar, replicationIdempotent],
  rewrites := [
    -- Comm: x(y).P | x<z> ~> P[z/y]
    -- In LN: PiInp(x, λ.body) + PiOut(x, z) in a bag ~> body[z/BVar0] in a bag
    { name := "Comm",
      typeContext := [("x", TypeExpr.base "Name"), ("body", TypeExpr.base "Proc"),
                      ("z", TypeExpr.base "Name")],
      premises := [],
      left := .collection .hashBag [
        .apply "PiInp" [.fvar "x", .lambda none (.fvar "body")],
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
      right := .collection .hashBag [.fvar "T"] (some "rest") },

    -- ResCong: a body step is interpreted in the surrounding restriction.
    -- Both the captured source and the premise-produced target are re-emitted
    -- at the same local binder depth.
    { name := "ResCong",
      typeContext := [],
      premises := [.congruence (.fvar "S") (.fvar "T")],
      left := .apply "PiNu" [.lambda none (.fvar "S")],
      right := .apply "PiNu" [.lambda none (.fvar "T")] }
  ]
}

/-- π-calculus reducts at an explicit authored-context depth.  Depth one
contains root COMM steps; each surrounding `ParCong` or `ResCong`
consumes one further unit. -/
def piCalcReducts (contextDepth : Nat) (process : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises RelationEnv.empty) piCalc contextDepth process

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

/-- Top-level components used by flattened parallel composition. -/
def piComponents : Pattern → List Pattern
  | .collection .hashBag elements none => elements
  | p => [p]

/-- A non-bag term contributes one component. -/
theorem piComponents_non_bag (P : Pattern)
    (notBag : ∀ elements, P ≠ .collection .hashBag elements none) : piComponents P = [P] := by
  cases P with
  | collection kind elements rest =>
      cases kind with
      | hashBag => cases rest with
        | none => exact False.elim (notBag elements rfl)
        | some _ => rfl
      | vec | hashSet => rfl
  | _ => rfl

/-- The binary parallel representation concatenates its component spines. -/
theorem piPar_components (P Q : Pattern) :
    piPar P Q = .collection .hashBag (piComponents P ++ piComponents Q) none := by
  unfold piPar
  split
  · rfl
  · rw [piComponents_non_bag Q (by assumption)]; rfl
  · rw [piComponents_non_bag _ (by assumption)]; rfl
  · rw [piComponents_non_bag _ (by assumption), piComponents_non_bag _ (by assumption)]; rfl

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
  | .input x y P => .apply "PiInp" [.fvar x, .lambda none (closeFVar 0 y (piToPattern P))]
  | .output x z => .apply "PiOut" [.fvar x, .fvar z]
  | .nu x P => .apply "PiNu" [.lambda none (closeFVar 0 x (piToPattern P))]
  | .replicate x y P => .apply "PiRep" [.apply "PiInp" [.fvar x, .lambda none (closeFVar 0 y (piToPattern P))]]

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
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let process := Pattern.collection .hashBag [inp, out] none
  piCalcReducts 1 process
  -- Expected: [{PiNil[]}] (the .subst resolves to PiNil since body has no BVar 0)

-- Demo 2: COMM — x(y).y<w> | x<z> → z<w>
-- Input body uses BVar 0 (the bound y), which gets substituted with z
#eval
  let body := Pattern.apply "PiOut" [.bvar 0, .fvar "w"]  -- y<w> in LN
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda none body]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let process := Pattern.collection .hashBag [inp, out] none
  piCalcReducts 1 process
  -- Expected: [{PiOut(.fvar "z", .fvar "w")}] (z<w>)

-- Demo 3: COMM with rest — x(y).0 | x<z> | P → 0 | P
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let extra := Pattern.apply "PiOut" [.fvar "a", .fvar "b"]
  let process := Pattern.collection .hashBag [inp, out, extra] none
  piCalcReducts 1 process
  -- Expected: [{PiNil[], PiOut(.fvar "a", .fvar "b")}]

-- Demo 4: No reduction — mismatched channels
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "y", .fvar "z"]  -- different channel!
  let process := Pattern.collection .hashBag [inp, out] none
  piCalcReducts 1 process
  -- Expected: [] (no reduction possible)

-- Demo 5: Reduction of a nested bag via the authored ParCong rule.
#eval
  let inp := Pattern.apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])]
  let out := Pattern.apply "PiOut" [.fvar "x", .fvar "z"]
  let inner := Pattern.collection .hashBag [inp, out] none
  let outer := Pattern.collection .hashBag [inner, .apply "PiNil" []] none
  piCalcReducts 2 outer

-- Demo 6: piToPattern bridge — verify encoding of a simple process
#eval
  let P : Process := .par (.input "x" "y" .nil) (.output "x" "z")
  piToPattern P
  -- Expected: hashBag[PiInp(.fvar "x", λ.PiNil[]), PiOut(.fvar "x", .fvar "z")]

-- Demo 7: piToPattern + rewrite — full pipeline
-- x(y).0 | x<z> as Process → Pattern → reduce
#eval
  let P : Process := .par (.input "x" "y" .nil) (.output "x" "z")
  piCalcReducts 1 (piToPattern P)
  -- Expected: [{PiNil[]}] (COMM fires, body 0 has no y references)

-- Demo 8: piToPattern with non-trivial body
-- x(y).y<w> | x<z> → z<w>
#eval
  let P : Process := .par (.input "x" "y" (.output "y" "w")) (.output "x" "z")
  let pat := piToPattern P
  (pat, piCalcReducts 1 pat)
  -- Expected pattern has closeFVar applied, reduction produces z<w>

/-! ## Structural Theorems -/

/-- piCalc has exactly 6 constructors. -/
theorem piCalc_terms_length : piCalc.terms.length = 6 := by decide

/-- piCalc has two sorts, processes and names. -/
theorem piCalc_types_length : piCalc.types.length = 2 := by decide

/-- piCalc has one COMM rule and two authored contextual rules. -/
theorem piCalc_rewrites_length : piCalc.rewrites.length = 3 := by decide

/-- Eight laws are authored: three of restriction (inaction, exchange and extrusion) and five of replication; the
parallel laws come from its algebra declaration. -/
theorem piCalc_equations_length : piCalc.equations.length = 8 := by decide

/-! ## Authored contextual boundary -/

private def commRedexPattern : Pattern :=
  .collection .hashBag
    [.apply "PiInp" [.fvar "x", .lambda none (.apply "PiNil" [])],
      .apply "PiOut" [.fvar "x", .fvar "z"]] none

private def nestedCommPattern : Pattern :=
  .collection .hashBag [commRedexPattern, .apply "PiNil" []] none

private def nestedCommResult : Pattern :=
  .collection .hashBag
    [.collection .hashBag [.apply "PiNil" []] none, .apply "PiNil" []] none

/-- The authored `ParCong` schema lifts a COMM step through one parallel
context. -/
theorem nestedCommResult_mem_piCalcReducts :
    nestedCommResult ∈ piCalcReducts 2 nestedCommPattern := by
  decide +kernel

/-- `piCalc` authors no contextual schema beneath input binders. -/
theorem piCalcReducts_input_eq_nil :
    piCalcReducts 2
      (.apply "PiInp" [.fvar "a", .lambda none commRedexPattern]) = [] := by
  decide +kernel

/-- `ParCong` is specific to bag parallel composition; it grants no descent
through set representation. -/
theorem piCalcReducts_set_eq_nil :
    piCalcReducts 2 (.collection .hashSet [commRedexPattern] none) = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
