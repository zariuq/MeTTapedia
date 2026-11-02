import Mettapedia.Languages.ProcessCalculi.CCS.Blocks
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# CCS with replication

Milner's CCS in its reaction presentation with replication: beside inaction, parallel composition, guarded sums and
restriction, a process may be replicated (`CRep`), with the laws of replication: unfolding `!P = {P, !P}`, inaction
`!0 = 0`, idempotence `!!P = !P`, distribution `!{P, Q} = {!P, !Q}` and duplication `{!P, !P} = !P`.

The rules are those of finite CCS: an action and the co-action on the same name, each a summand of a sum standing in a
parallel composition, react (`React`); a silent summand is taken (`Tau`); reaction happens inside a parallel
composition and under a restriction (`ParCong`, `ResCong`). A replicated process takes part through its unfolding, a
law, not a rule.

`ccsRepCalc` is a calculus with restriction and replication in the sense of the restriction-block theory
(`ccsRepReplicationLanguage`): its declared laws are exactly those of restriction, of the empty sum and of
replication, so the replication theory's canonical form decides its static theory.

## References

- Milner (1999), "Communicating and Mobile Systems: the π-Calculus", chapters 4, 5 and 9
- Busi, Gabbrielli and Zavattaro (2009), "On the expressive power of recursion, replication and iteration in process
  calculi", Mathematical Structures in Computer Science 19(6)
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.Replicated

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.ProcessCalculi.CCS
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock)

/-! ## The definition -/

/-- Replication of a process: `!P`. -/
def ccsRepRule : GrammarRule :=
  { label := "CRep", category := "Proc",
    params := [.simple "p" (TypeExpr.base "Proc")],
    syntaxPattern := [.terminal "!", .nonTerminal "p"] }

/-- CCS's blocks with replication of any process, read by the refined labelling. -/
abbrev ccsRepBlock : ReplicationBlock := ⟨ccsBlock, "CRep", true⟩

@[simp] theorem ccsRepBlock_toBlock : ccsRepBlock.toBlock = ccsBlock := rfl
@[simp] theorem ccsRepBlock_replicate : ccsRepBlock.replicate = "CRep" := rfl

/-- **CCS with replication**: inaction, parallel composition, guarded sums, restriction and replication; actions,
co-actions and the silent action as guards.

- **Sorts**: `["Proc", "Name", "Guard"]` (names are variables of the name sort)
- **Equations**: restriction of inaction, exchange of restrictions, scope extrusion and the empty sum; unfolding,
  inaction, idempotence, distribution and duplication of replication; besides the laws of the parallel bag and of the
  multiset of summands
- **Reductions**: React, Tau, ParCong and ResCong -/
def ccsRepCalc : LanguageDef :=
  { name := "CCSRep"
    types := ["Proc", "Name", "Guard"]
    terms := [ccsCalc.terms[0], ccsCalc.terms[1], ccsCalc.terms[2], ccsCalc.terms[3], ccsCalc.terms[4],
      ccsCalc.terms[5], ccsCalc.terms[6], ccsRepRule]
    equations := replicationBlockLaws ccsRepBlock
    rewrites := [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite] }

theorem ccsRepCalc_rewrites :
    ccsRepCalc.rewrites = [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite] :=
  rfl

/-- CCS with replication declares exactly the laws of restriction, of the empty sum and of replication. -/
theorem ccsRepCalc_equations : ccsRepCalc.equations = replicationBlockLaws ccsRepBlock := rfl

/-! ## Admission -/

theorem ccsRep_react_validates : LanguageDef.validateRewrite ccsRepCalc ccsReactRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsReactRewrite, ccsRepCalc, ccsCalc, ccsRepRule]

theorem ccsRep_tau_validates : LanguageDef.validateRewrite ccsRepCalc ccsTauRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_premiseFree <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsTauRewrite, ccsRepCalc, ccsCalc, ccsRepRule]

theorem ccsRep_parCong_validates : LanguageDef.validateRewrite ccsRepCalc ccsParCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsParCongRewrite, ccsRepCalc, ccsCalc, ccsRepRule]

theorem ccsRep_resCong_validates : LanguageDef.validateRewrite ccsRepCalc ccsResCongRewrite = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S") (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [ccsResCongRewrite, ccsRepCalc, ccsCalc, ccsRepRule]

theorem ccsRep_equations_validate :
    ∀ equation ∈ ccsRepCalc.equations, LanguageDef.validateEquation ccsRepCalc equation = [] := by
  intro equation membership
  simp only [ccsRepCalc, replicationBlockLaws, blockLaws, replicationLaws, ccsBlock, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply LanguageDef.validateEquation_eq_nil_of_premiseFree <;>
      first
        | rfl
        | decide
        | rule_patterns [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, emptyUnitOf, replicationUnfoldOf,
            replicationNilOf, replicationTwiceOf, replicationParOf, replicationIdempotentOf, ccsRepCalc, ccsCalc,
            ccsRepRule]

/-- CCS with replication passes the declaration gate. -/
theorem ccsRepCalc_validate_eq_nil : ccsRepCalc.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_concreteSyntaxEquationsAndRewrites
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · exact ccsRep_equations_validate
  · intro rewrite membership
    rw [ccsRepCalc_rewrites] at membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl
    · exact ccsRep_react_validates
    · exact ccsRep_tau_validates
    · exact ccsRep_parCong_validates
    · exact ccsRep_resCong_validates

/-- The reaction rules bind every variable of their contracta in their redexes, the contextual rules read only their
reduction hypotheses, and each law has the same variables on both sides. -/
theorem ccsRepCalc_executionFlowErrors_eq_nil (modes : RelationModeTable) :
    ccsRepCalc.executionFlowErrors modes = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_ruleAndEquationFlows
  · intro rule membership
    rw [ccsRepCalc_rewrites] at membership
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
    simp only [ccsRepCalc, replicationBlockLaws, blockLaws, replicationLaws, ccsBlock, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at membership
    rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> refine ⟨rfl, ?_, ?_⟩ <;>
      · intro name nameMembership
        simp_all [restrictionNilOf, restrictionExchangeOf, scopeExtrusionOf, emptyUnitOf, replicationUnfoldOf,
          replicationNilOf, replicationTwiceOf, replicationParOf, replicationIdempotentOf, Pattern.freeFvarNames]

/-- The calculus passes the ordered binding-flow gate with no relation mode. -/
theorem ccsRepCalc_executionAdmissionErrors_eq_nil : ccsRepCalc.executionAdmissionErrors [] = [] :=
  LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes ccsRepCalc ccsRepCalc_validate_eq_nil
    (ccsRepCalc_executionFlowErrors_eq_nil [])

/-! ## A calculus with restriction and replication -/

/-- The sum is a named multiset of guards. -/
theorem sum_namedMultiset : NamedMultiset ccsRepCalc.terms[2] "Proc" :=
  ⟨rfl, rfl, ⟨"gs", "Guard", rfl, by decide⟩⟩

/-- Parallel composition is a bare bag beside the sum. -/
theorem ccsRep_parallelBag : ParallelBag ccsRepCalc ccsRepCalc.terms[1] "CNil" ["CSum"] where
  bagAuthored := List.getElem_mem (by decide)
  bagShape := ⟨"ps", rfl⟩
  bagAlgebra := rfl
  representedBare := rfl
  unitAuthored := ⟨ccsRepCalc.terms[0], List.getElem_mem (by decide), rfl, rfl, rfl⟩
  otherParameters := by
    intro rule member notBag
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · left; simp [ccsCalc]
    · exact absurd rfl notBag
    · exact .inr ⟨by simp [ccsCalc], sum_namedMultiset⟩
    all_goals left; simp [ccsCalc, ccsRepRule, TermParam.typeExpr,
      Mettapedia.GSLT.LanguageDef.BagNormalForm.collectionFree]

/-- **CCS with replication is a calculus with restriction and replication.** -/
instance ccsRepReplicationLanguage : ReplicationLanguage ccsRepCalc ccsRepBlock where
  bag := ⟨ccsRepCalc.terms[1], ccsRep_parallelBag, rfl⟩
  equations := rfl
  restrictAuthored := ⟨ccsRepCalc.terms[3], List.getElem_mem (by decide), rfl⟩
  restrictShape := by
    intro rule member labelIs
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ccsCalc, ccsRepRule]
  unitShape := by
    intro rule member labelIs
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ccsCalc, ccsRepRule]
  multisetShape := by
    intro rule member listed
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ccsCalc, ccsRepRule] at listed
    exact sum_namedMultiset
  emptyUnitShape := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    refine ⟨by simp, fun rule member labelIs => ?_⟩
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ccsCalc, ccsRepRule]
  emptyUnitAuthored := by
    intro label listed
    simp only [List.mem_cons, List.not_mem_nil, or_false] at listed
    subst listed
    exact ⟨ccsRepCalc.terms[2], List.getElem_mem (by decide), rfl⟩
  labelsUnique := by decide
  params := by
    intro rule member notBare notMultiset parameter present
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [ccsCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [ccsCalc] at notMultiset
    all_goals
      simp only [ccsCalc, ccsRepRule, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp [parameterType?]
  arrowsAbstract := by
    intro rule member notBare notMultiset parameter present domain sort found
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [ccsCalc] at present
    · exact absurd ⟨"ps", .hashBag, .base "Proc", rfl⟩ notBare
    · simp [ccsCalc] at notMultiset
    all_goals
      simp only [ccsCalc, ccsRepRule, List.getElem_cons_succ, List.getElem_cons_zero, List.mem_cons,
        List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl <;> simp_all [parameterType?]
  replicateAuthored := ⟨ccsRepCalc.terms[7], List.getElem_mem (by decide), rfl⟩
  replicateShape := by
    intro rule member labelIs
    simp only [ccsRepCalc, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [ccsCalc, ccsRepRule]
  replicateFresh := by decide

/-- **The signature of CCS with replication is a restriction-block signature.** -/
instance ccsRepBlockSignature : BlockSignature ccsRepCalc ccsBlock := ccsRepReplicationLanguage.toBlockSignature

end Mettapedia.Languages.ProcessCalculi.CCS.Replicated
