import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mettapedia.OSLF.Syntax.RhoOperationalClosure

/-!
# The Chapter 7 Drop rule as an authored LanguageDef profile

This declaration leaves the established `rhoCalc` unchanged.  It appends the
source's process-sorted Drop rule to its actual list of authored rules, which
already contains COMM and ParCong.  The intrinsic binary-ACU profile and this
hash-bag profile still require a proved general interpretation between them.
-/

namespace Mettapedia.OSLF.Binding.RhoSchema.Authored

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

set_option autoImplicit false

/-- `PDrop (NQuote P) ~> P`, the source's unconditional Drop rule. -/
def rhoDropRewrite : RewriteRule where
  name := "Drop"
  typeContext := [("P", TypeExpr.proc)]
  premises := []
  left := .apply "PDrop" [.apply "NQuote" [.fvar "P"]]
  right := .fvar "P"

/-- The existing canonical declaration with the missing source rule added
as a separately named profile. -/
def rhoCalcWithDrop : LanguageDef :=
  { rhoCalc with rewrites := rhoCalc.rewrites ++ [rhoDropRewrite] }

theorem rhoCalcWithDrop_rules :
    rhoCalcWithDrop.rewrites.map (·.name) = ["Comm", "ParCong", "Drop"] := rfl

/-- The three-rule authored profile passes the actual structural validator. -/
theorem rhoCalcWithDrop_valid : rhoCalcWithDrop.validate = [] := by
  simp [LanguageDef.validate, rhoCalcWithDrop, rhoCalc, rhoDropRewrite,
    rhoCommRewrite, rhoParCongRewrite,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateEquation, LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseType, TypeExpr.proc,
    TypeExpr.name, TypeExpr.funType, TypeExpr.bag,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  all_goals decide +kernel

/-- Isolate the new premise-free rule for an ordered-flow proof. -/
private def dropOnly : LanguageDef :=
  { rhoCalc with equations := [], rewrites := [rhoDropRewrite] }

private theorem dropOnly_flow : dropOnly.executionFlowErrors [] = [] := by
  apply LanguageDef.executionFlowErrors_eq_nil_of_premiseFree
  · rfl
  · intro rule member
    simp only [dropOnly, List.mem_singleton] at member
    subst rule
    rfl
  · intro rule member name rightMember
    simp only [dropOnly, List.mem_singleton] at member
    subst rule
    simpa [rhoDropRewrite, Pattern.freeFvarNames] using rightMember

/-- The added rule also passes the ordered executable binding-flow gate. -/
theorem rhoCalcWithDrop_execution_admitted :
    rhoCalcWithDrop.executionAdmissionErrors [] = [] := by
  apply LanguageDef.executionAdmissionErrors_eq_nil_of_emptyModes
    rhoCalcWithDrop rhoCalcWithDrop_valid
  have oldAdmission := rhoCalc_executionAdmissionErrors_eq_nil
  have oldFlow : rhoCalc.executionFlowErrors [] = [] := by
    unfold LanguageDef.executionAdmissionErrors at oldAdmission
    simp only [List.append_eq_nil_iff] at oldAdmission
    exact oldAdmission.2
  have newFlow := dropOnly_flow
  unfold LanguageDef.executionFlowErrors at oldFlow newFlow ⊢
  simp only [rhoCalcWithDrop, dropOnly, List.flatMap_append,
    List.flatMap_singleton, List.flatMap_nil] at *
  simp only [List.append_eq_nil_iff] at oldFlow newFlow
  simp [oldFlow.1, oldFlow.2, newFlow.1]

/-- The closed quote/drop test on the canonical pattern carrier. -/
def dropQuotedZero : Pattern :=
  .apply "PDrop" [.apply "NQuote" [.apply "PZero" []]]

def zero : Pattern := .apply "PZero" []

/-- The actual bounded authored rule interpreter performs the Drop step. -/
theorem authored_drop_fires :
    zero ∈ reducts rhoCalcWithDrop 1 dropQuotedZero := by
  decide +kernel

/-- The executable firing also inhabits the independently specified least
contextual relation, by the compiler correctness theorem. -/
theorem authored_drop_is_step :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop
      dropQuotedZero zero := by
  apply exists_mem_rewriteAt_iff_step.mp
  exact ⟨1, authored_drop_fires⟩

/-- Every old contextual derivation remains valid in the larger authored
profile, including recursive ParCong derivations. -/
theorem authored_core_step_in_extension {source target : Pattern}
    (step : Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalc source target) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop source target := by
  apply Mettapedia.OSLF.MeTTaIL.ContextualStep.Step.mono_rules
    (lang₁ := rhoCalc) (lang₂ := rhoCalcWithDrop) ?_ step
  intro rule member
  exact List.mem_append.mpr (Or.inl member)

/-- At the same contextual depth the old declaration does not perform it. -/
theorem authored_comm_only_does_not_drop :
    reducts rhoCalc 1 dropQuotedZero = [] := by
  decide +kernel

/-- No finite contextual derivation from the established authored core can
start at this Drop redex: neither COMM nor ParCong matches its outer shape. -/
theorem authored_comm_only_never_drops (target : Pattern) :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalc dropQuotedZero target := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  simp only [rhoCalc, List.mem_cons] at member
  rcases member with first | second
  · cases first
    decide +kernel
  · rcases second with second | impossible
    · cases second
      decide +kernel
    · cases impossible

/-- Inclusion is proper on the common program carrier: Drop adds an actual
one-step behavior that the established authored core cannot derive. -/
theorem authored_drop_is_proper_extension :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalcWithDrop dropQuotedZero zero ∧
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step
      (engineBasePremises RelationEnv.empty) rhoCalc dropQuotedZero zero :=
  ⟨authored_drop_is_step, authored_comm_only_never_drops zero⟩

end Mettapedia.OSLF.Binding.RhoSchema.Authored
