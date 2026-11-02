import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# The π-calculus with guarded sums

Milner's π-calculus with guarded choice: a sum is a multiset of guards, each an input, an output of a name followed by
a process, or a silent prefix followed by a process; beside it, parallel composition, restriction and replication of
any process.

- Parallel composition is a bag with unit `PiNil`, so its associativity, commutativity and unit law are the
  presentation's own collection laws.
- A sum is a multiset of guards (`PiSum`), so its summands stand in no order; the empty sum is inaction (`emptySum`,
  stated as `(νx) 0`, which restriction of inaction makes `0`).
- Restriction (`PiNu`) binds a name over a process, with the laws of restriction: restriction of inaction, exchange of
  restrictions and scope extrusion.
- Replication (`PiRep`) takes any process, with the laws of replication: unfolding, inaction, idempotence,
  distribution and duplication.

The rules are the reaction rules. An input and an output on the same channel, each a summand of a sum standing in a
parallel composition, communicate: the input's body receives the output's datum, the output's continuation is
released, and the other summands of the two sums are discarded (`Comm`). A silent summand is taken, discarding the
others (`Tau`). Reaction happens inside a parallel composition and under a restriction (`ParCong`, `ResCong`). A
replicated process takes part through its unfolding, a law, not a rule.

## References

- Milner (1999), "Communicating and Mobile Systems: the π-Calculus", chapter 9
- Sangiorgi and Walker (2001), "The π-calculus: A Theory of Mobile Processes", section 1.1
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

/-! ## The definition -/

/-- A guarded sum: a multiset of guards. -/
def piSumRule : GrammarRule :=
  { label := "PiSum", category := "Proc",
    params := [.simple "gs" (TypeExpr.bag (TypeExpr.base "Guard"))],
    syntaxPattern := [.terminal "[", .nonTerminal "gs", .separator "+", .terminal "]"],
    collectionRepresentation := .wrapped }

/-- An input guard `x(y).P`, its body abstracted over the received name. -/
def piRecvRule : GrammarRule :=
  { label := "PiRecv", category := "Guard",
    params := [.simple "x" (TypeExpr.base "Name"),
      .abstraction "body" (TypeExpr.arrow (TypeExpr.base "Name") (TypeExpr.base "Proc"))],
    syntaxPattern := [.nonTerminal "x", .terminal "(", .terminal "y", .terminal ")", .terminal ".",
      .nonTerminal "body"] }

/-- An output guard `x⟨z⟩.K`: a name sent on a channel, followed by a process. -/
def piSendRule : GrammarRule :=
  { label := "PiSend", category := "Guard",
    params := [.simple "x" (.base "Name"), .simple "z" (.base "Name"), .simple "k" (.base "Proc")],
    syntaxPattern := [.nonTerminal "x", .terminal "<", .nonTerminal "z", .terminal ">", .terminal ".",
      .nonTerminal "k"] }

/-- A silent guard `τ.K`. -/
def piTauRule : GrammarRule :=
  { label := "PiTau", category := "Guard",
    params := [.simple "k" (.base "Proc")],
    syntaxPattern := [.terminal "τ", .terminal ".", .nonTerminal "k"] }

/-- `[] = (νx) 0`: the empty sum is inaction. -/
def emptySum : Equation where
  name := "EmptyUnit"
  typeContext := []
  premises := []
  left := .apply "PiSum" [.collection .hashBag [] none]
  right := .apply "PiNu" [.lambda none (.apply "PiNil" [])]
  bindings := some { dependencies := [], occurrences := [] }

/-- `{[x(y).P + m], [x⟨z⟩.K + n] | rest} ~> {P[z/y], K | rest}` -/
def piSumCommRewrite : RewriteRule where
  name := "Comm"
  typeContext := [("x", .base "Name"), ("body", .base "Proc"), ("z", .base "Name"), ("k", .base "Proc")]
  premises := []
  left := .collection .hashBag [
    .apply "PiSum" [.collection .hashBag [.apply "PiRecv" [.fvar "x", .lambda none (.fvar "body")]] (some "m")],
    .apply "PiSum" [.collection .hashBag [.apply "PiSend" [.fvar "x", .fvar "z", .fvar "k"]] (some "n")]
  ] (some "rest")
  right := .collection .hashBag [.subst (.fvar "body") (.fvar "z"), .fvar "k"] (some "rest")

/-- `[τ.k + m] ~> k` -/
def piSumTauRewrite : RewriteRule where
  name := "Tau"
  typeContext := [("k", .base "Proc")]
  premises := []
  left := .apply "PiSum" [.collection .hashBag [.apply "PiTau" [.fvar "k"]] (some "m")]
  right := .fvar "k"

/-- **The π-calculus with guarded sums**: inaction, parallel composition, guarded sums, restriction and replication;
inputs, outputs followed by a process and silent prefixes as guards.

- **Sorts**: `["Proc", "Name", "Guard"]` (names are variables of the name sort)
- **Equations**: restriction of inaction, exchange of restrictions, scope extrusion and the empty sum; unfolding,
  inaction, idempotence, distribution and duplication of replication; besides the laws of the parallel bag and of the
  multiset of summands
- **Reductions**: Comm, Tau, ParCong and ResCong -/
def piSumCalc : LanguageDef :=
  { name := "PiSumCalc"
    types := ["Proc", "Name", "Guard"]
    terms := [piCalc.terms[0], piCalc.terms[1], piSumRule, piCalc.terms[4], piCalc.terms[5], piRecvRule, piSendRule,
      piTauRule]
    equations := [restrictionNil, restrictionExchange, scopeExtrusion, emptySum, replicationUnfold, replicationNil,
      replicationTwice, replicationPar, replicationIdempotent]
    rewrites := [piSumCommRewrite, piSumTauRewrite, piParCongRewrite, piResCongRewrite] }

theorem piSumCalc_rewrites :
    piSumCalc.rewrites = [piSumCommRewrite, piSumTauRewrite, piParCongRewrite, piResCongRewrite] :=
  rfl

/-! ## Admission -/

theorem piSumCommRewrite_validates : LanguageDef.validateRewrite piSumCalc piSumCommRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [piSumCommRewrite, piSumCalc, piSumRule, piRecvRule, piSendRule, piTauRule, piCalc]

theorem piSumTauRewrite_validates : LanguageDef.validateRewrite piSumCalc piSumTauRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [piSumTauRewrite, piSumCalc, piSumRule, piRecvRule, piSendRule, piTauRule, piCalc]

theorem piSum_parCong_validates : LanguageDef.validateRewrite piSumCalc piParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piParCongRewrite, piSumCalc, piSumRule, piRecvRule, piSendRule, piTauRule, piCalc]

theorem piSum_resCong_validates : LanguageDef.validateRewrite piSumCalc piResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [piResCongRewrite, piSumCalc, piSumRule, piRecvRule, piSendRule, piTauRule, piCalc]

/-- The π-calculus with sums passes the declaration gate. -/
theorem piSumCalc_validate_eq_nil : piSumCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro equation membership
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
        first
          | rfl
          | decide
          | rule_patterns [restrictionNil, restrictionExchange, scopeExtrusion, emptySum, replicationUnfold,
              replicationNil, replicationTwice, replicationPar, replicationIdempotent, piSumCalc, piSumRule,
              piRecvRule, piSendRule, piTauRule, piCalc]
  · intro rewrite membership
    rw [piSumCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact piSumCommRewrite_validates
    · exact piSumTauRewrite_validates
    · exact piSum_parCong_validates
    · exact piSum_resCong_validates

/-- The reaction rules bind every variable of their contracta in their redexes, the contextual rules read only their
reduction hypotheses, and each law has the same variables on both sides. -/
theorem piSumCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    piSumCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [piSumCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · refine .plain rfl ?_
      intro name nameMembership
      simp [piSumCommRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .plain rfl ?_
      intro name nameMembership
      simp [piSumTauRewrite, Pattern.freeFvarNames] at nameMembership ⊢
      tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [piParCongRewrite, piCalc, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [piParCongRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
        tauto
    · refine .contextual "S" "T" rfl ?_ ?_
      · simp [piResCongRewrite, piCalc, Pattern.freeFvarNames]
      · intro name nameMembership
        simp [piResCongRewrite, piCalc, Pattern.freeFvarNames] at nameMembership ⊢
        tauto
  · intro equation membership
    simp only [piSumCalc, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNil, restrictionExchange, scopeExtrusion, emptySum, replicationUnfold, replicationNil,
          replicationTwice, replicationPar, replicationIdempotent, Pattern.freeFvarNames]

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem piSumCalc_executionAdmissionErrors_eq_nil : piSumCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes piSumCalc piSumCalc_validate_eq_nil
    (piSumCalc_executionFlowErrors_eq_nil [])

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums
