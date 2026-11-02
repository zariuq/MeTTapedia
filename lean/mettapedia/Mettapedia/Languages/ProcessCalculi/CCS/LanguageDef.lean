import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation
import Mettapedia.OSLF.MeTTaIL.FlowAdmission
import Mettapedia.OSLF.MeTTaIL.EquationalAdmission

/-!
# CCS as a language definition

Milner's calculus of communicating systems, in its reaction presentation: processes are inaction, parallel
composition, restriction of a name and guarded sums, and a guard is an action, a co-action or the silent action,
each prefixing a process.

- Parallel composition is a bag with unit `CNil`, so its associativity, commutativity and unit law are the
  presentation's own collection laws.
- A sum is a multiset of guards (`CSum`), so the summands of a sum stand in no order; the empty sum is inaction
  (`emptySum`, stated as `(νx) 0`, which restriction of inaction makes `0`).
- Restriction (`CNu`) binds a name over a process, with the laws of restriction: restriction of inaction, exchange
  of restrictions and scope extrusion.
- Names are variables of their own sort, free or bound by a restriction.

The rules are the reaction rules. An action and the co-action on the same name, each a summand of a sum standing
in a parallel composition, react: both continuations are released and the other summands of the two sums are
discarded (`React`). A silent summand is taken, discarding the others (`Tau`). Reaction happens inside a parallel
composition and under a restriction (`ParCong`, `ResCong`).

## References

- Milner (1999), "Communicating and Mobile Systems: the π-Calculus", chapters 4 and 5
- Sangiorgi and Walker (2001), "The π-calculus: A Theory of Mobile Processes", section 1.1
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-! ## The laws of restriction and of sums -/

/-- `(νx) 0 = 0` -/
def restrictionNil : Equation where
  name := "RestrictionNil"
  typeContext := []
  premises := []
  left := .apply "CNu" [.lambda none (.apply "CNil" [])]
  right := .apply "CNil" []

/-- `(νx)(νy) P = (νy)(νx) P` -/
def restrictionExchange : Equation where
  name := "RestrictionExchange"
  typeContext := [("P", .base "Proc")]
  premises := []
  left := .apply "CNu" [.lambda none (.apply "CNu" [.lambda none (.fvar "P")])]
  right := .apply "CNu" [.lambda none (.apply "CNu" [.lambda none (.fvar "P")])]
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
  left := .collection .hashBag [.apply "CNu" [.lambda none (.fvar "P")]] (some "rest")
  right := .apply "CNu" [.lambda none (.collection .hashBag [.fvar "P"] (some "rest"))]
  bindings := some
    { dependencies := [("P", [.base "Name"]), ("rest", [])]
      occurrences :=
        [{ name := "P", site := .left, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .left, path := [1], arguments := [] },
         { name := "P", site := .right, path := [0, 0, 0], arguments := [.bvar 0] },
         { name := "rest", site := .right, path := [0, 0, 1], arguments := [] }] }

/-- `[] = (νx) 0`: the empty sum is inaction. -/
def emptySum : Equation where
  name := "EmptyUnit"
  typeContext := []
  premises := []
  left := .apply "CSum" [.collection .hashBag [] none]
  right := .apply "CNu" [.lambda none (.apply "CNil" [])]
  bindings := some { dependencies := [], occurrences := [] }

/-! ## The reaction rules -/

/-- `[a.p + m] | [~a.q + n] | rest ~> p | q | rest` -/
def ccsReactRewrite : RewriteRule where
  name := "React"
  typeContext := [("a", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")]
  premises := []
  left := .collection .hashBag [
    .apply "CSum" [.collection .hashBag [.apply "CAct" [.fvar "a", .fvar "p"]] (some "m")],
    .apply "CSum" [.collection .hashBag [.apply "CCoAct" [.fvar "a", .fvar "q"]] (some "n")]
  ] (some "rest")
  right := .collection .hashBag [.fvar "p", .fvar "q"] (some "rest")

/-- `[τ.p + m] ~> p` -/
def ccsTauRewrite : RewriteRule where
  name := "Tau"
  typeContext := [("p", .base "Proc")]
  premises := []
  left := .apply "CSum" [.collection .hashBag [.apply "CTau" [.fvar "p"]] (some "m")]
  right := .fvar "p"

/-- `{S | rest} ~> {T | rest}` if `S ~> T` -/
def ccsParCongRewrite : RewriteRule where
  name := "ParCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .collection .hashBag [.fvar "S"] (some "rest")
  right := .collection .hashBag [.fvar "T"] (some "rest")

/-- `(νx) S ~> (νx) T` if `S ~> T` -/
def ccsResCongRewrite : RewriteRule where
  name := "ResCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .apply "CNu" [.lambda none (.fvar "S")]
  right := .apply "CNu" [.lambda none (.fvar "T")]

/-- **CCS**, finite: inaction, parallel composition, guarded sums and restriction; actions, co-actions and the silent
action as guards.

- **Sorts**: `["Proc", "Name", "Guard"]` (names are variables of the name sort)
- **Equations**: restriction of inaction, exchange of restrictions, scope extrusion and the empty sum, besides the
  laws of the parallel bag and of the multiset of summands
- **Reductions**: React, Tau, ParCong and ResCong -/
def ccsCalc : LanguageDef := {
  name := "CCS",
  types := ["Proc", "Name", "Guard"],
  terms := [
    -- CNil . |- "0" : Proc
    { label := "CNil", category := "Proc", params := [],
      syntaxPattern := [.terminal "0"] },

    -- CPar . ps:HashBag(Proc) |- "{" ps.*sep("|") "}" : Proc
    { label := "CPar", category := "Proc",
      params := [.simple "ps" (TypeExpr.bag (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "{", .nonTerminal "ps", .separator "|", .terminal "}"],
      algebra? := some { flatten := true, unit := some "CNil" } },

    -- CSum . gs:HashBag(Guard) |- "[" gs.*sep("+") "]" : Proc
    { label := "CSum", category := "Proc",
      params := [.simple "gs" (TypeExpr.bag (TypeExpr.base "Guard"))],
      syntaxPattern := [.terminal "[", .nonTerminal "gs", .separator "+", .terminal "]"],
      collectionRepresentation := .wrapped },

    -- CNu . body:[Name -> Proc] |- "ν" body : Proc
    { label := "CNu", category := "Proc",
      params := [.abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
      syntaxPattern := [.terminal "ν", .nonTerminal "body"] },

    -- CAct . a:Name, p:Proc |- a "." p : Guard
    { label := "CAct", category := "Guard",
      params := [.simple "a" (TypeExpr.base "Name"), .simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.nonTerminal "a", .terminal ".", .nonTerminal "p"] },

    -- CCoAct . a:Name, p:Proc |- "~" a "." p : Guard
    { label := "CCoAct", category := "Guard",
      params := [.simple "a" (TypeExpr.base "Name"), .simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "~", .nonTerminal "a", .terminal ".", .nonTerminal "p"] },

    -- CTau . p:Proc |- "τ" "." p : Guard
    { label := "CTau", category := "Guard",
      params := [.simple "p" (TypeExpr.base "Proc")],
      syntaxPattern := [.terminal "τ", .terminal ".", .nonTerminal "p"] }
  ],
  equations := [restrictionNil, restrictionExchange, scopeExtrusion, emptySum],
  rewrites := [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite]
}

theorem ccsCalc_rewrites :
    ccsCalc.rewrites = [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite] :=
  rfl

/-! ## Admission -/

theorem ccsReactRewrite_validates : LanguageDef.validateRewrite ccsCalc ccsReactRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsReactRewrite, ccsCalc]

theorem ccsTauRewrite_validates : LanguageDef.validateRewrite ccsCalc ccsTauRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsTauRewrite, ccsCalc]

theorem ccsParCongRewrite_validates : LanguageDef.validateRewrite ccsCalc ccsParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsParCongRewrite, ccsCalc]

theorem ccsResCongRewrite_validates : LanguageDef.validateRewrite ccsCalc ccsResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsResCongRewrite, ccsCalc]

/-- The definition passes the declaration gate. -/
theorem ccsCalc_validate_eq_nil : ccsCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro equation membership
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;>
      apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
        first
          | rfl
          | decide
          | rule_patterns [restrictionNil, restrictionExchange, scopeExtrusion, emptySum, ccsCalc]
  · intro rewrite membership
    rw [ccsCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact ccsReactRewrite_validates
    · exact ccsTauRewrite_validates
    · exact ccsParCongRewrite_validates
    · exact ccsResCongRewrite_validates

/-- The reaction rules bind every variable of their contracta in their redexes, the contextual rules read only their
reduction hypotheses, and each law has the same variables on both sides. -/
theorem ccsCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    ccsCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [ccsCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [ccsReactRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .plain rfl ?_
      intro name nameMembership
      simp [ccsTauRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [ccsParCongRewrite, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [ccsParCongRewrite, Pattern.freeFvarNames] at nameMembership ⊢
        tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [ccsResCongRewrite, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [ccsResCongRewrite, Pattern.freeFvarNames] at nameMembership ⊢
        tauto
  · intro equation membership
    simp only [ccsCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNil, restrictionExchange, scopeExtrusion, emptySum, Pattern.freeFvarNames]

/-- The definition passes the ordered binding-flow gate with no external relation mode. -/
theorem ccsCalc_executionAdmissionErrors_eq_nil : ccsCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes ccsCalc ccsCalc_validate_eq_nil
    (ccsCalc_executionFlowErrors_eq_nil [])

/-- The engine with no external relations. -/
abbrev base : BasePremiseEvaluator := engineBasePremises RelationEnv.empty

/-! ## Processes -/

/-- Inaction. -/
def nil : Pattern := .apply "CNil" []

/-- The parallel composition of `processes`. -/
def par (processes : List Pattern) : Pattern := .collection .hashBag processes none

/-- The sum of `guards`. -/
def sum (guards : List Pattern) : Pattern := .apply "CSum" [.collection .hashBag guards none]

/-- `(νx) body`, the restricted name being the bound variable `0` of `body`. -/
def nu (body : Pattern) : Pattern := .apply "CNu" [.lambda none body]

/-- The action on `name`, then `continuation`. -/
def act (name continuation : Pattern) : Pattern := .apply "CAct" [name, continuation]

/-- The co-action on `name`, then `continuation`. -/
def coact (name continuation : Pattern) : Pattern := .apply "CCoAct" [name, continuation]

/-- The silent action, then `continuation`. -/
def tau (continuation : Pattern) : Pattern := .apply "CTau" [continuation]

/-- The free names `a` and `b`. -/
def nameA : Pattern := .fvar "a"
def nameB : Pattern := .fvar "b"

/-! ## Reactions -/

/-- `a.0 | ~a.(a.0)`. -/
def handshake : Pattern := par [sum [act nameA nil], sum [coact nameA (sum [act nameA nil])]]

/-- `0 | a.0`: both continuations, released side by side. -/
def handshakeDone : Pattern := par [nil, sum [act nameA nil]]

/-- An action and its co-action on one name react. -/
theorem handshake_steps : Step base ccsCalc handshake handshakeDone :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `(a.0 + b.0) | ~a.0`: a choice. -/
def choice : Pattern := par [sum [act nameA nil, act nameB nil], sum [coact nameA nil]]

/-- **A reaction resolves a choice**: the summand `b.0` is discarded. -/
theorem choice_steps : Step base ccsCalc choice (par [nil, nil]) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `τ.(a.0) + b.0`. -/
def silent : Pattern := sum [tau (sum [act nameA nil]), act nameB nil]

/-- **A silent summand is taken**, discarding the others. -/
theorem silent_steps : Step base ccsCalc silent (sum [act nameA nil]) :=
  exists_mem_rewriteAt_iff_step.mp ⟨1, by decide +kernel⟩

/-- `(νx)(x.0 | ~x.0)`: a reaction on a private name. -/
def privateHandshake : Pattern := nu (par [sum [act (.bvar 0) nil], sum [coact (.bvar 0) nil]])

/-- **A reaction happens under a restriction.** -/
theorem private_steps : Step base ccsCalc privateHandshake (nu (par [nil, nil])) :=
  exists_mem_rewriteAt_iff_step.mp ⟨2, by decide +kernel⟩

/-- `a.0 | ~b.0`: the names differ. -/
def mismatch : Pattern := par [sum [act nameA nil], sum [coact nameB nil]]

/-- Prefixes on different names do not react. -/
theorem mismatch_stuck : rewriteAt base ccsCalc 2 mismatch = [] := by
  decide +kernel

/-- `a.(~a.0)`: a guard holds its continuation back. -/
def guarded : Pattern := sum [act nameA (sum [coact nameA nil])]

/-- **A guard holds its continuation back**: the co-action under the action does not react with it. -/
theorem guarded_stuck : rewriteAt base ccsCalc 2 guarded = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.CCS
