import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.MILNativeMaterialization

/-!
# Executable materialization controls in the formed learned vocabulary

The expected native terms are independently written constructor applications.
The primitive slots are distinct and the chain retains both child programs.
Malformed proof structure is rejected even when another proof of the requested
goal succeeds. These tests invoke the executable materializer, not an alias of
the expected native term or a noncomputable selected derivation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILNativeMaterialization.Examples

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Presentation MILCheckedChain MILCheckedNativePrograms

def motherNative : Tower.Tm 5 :=
  IntrinsicMILHypothesis.primitiveApp (.var 4) (.var 3) (.var 2) (.var 2) (.var 1)

def fatherNative : Tower.Tm 5 :=
  IntrinsicMILHypothesis.primitiveApp (.var 4) (.var 3) (.var 2) (.var 2) (.var 0)

def grandparentNative : Tower.Tm 5 :=
  IntrinsicMILHypothesis.chainApp (.var 4) (.var 3) (.var 2) (.var 2) (.var 2)
    motherNative fatherNative

def swappedChildren : RawProof :=
  .node ⟨chainRule.id, [alice, bob, carol]⟩ [fatherProof, motherProof]

def missingChild : RawProof :=
  .node ⟨chainRule.id, [alice, bob, carol]⟩ [motherProof]

private theorem motherApplication :
    RuleApplication learned.target ⟨motherRule.id, []⟩ [] (relates alice bob) := by
  apply instantiateRule?_eq_some_iff_application.mp
  have lookup : learned.target.1.lookupRule? motherRule.id = some motherRule := by decide
  simp only [instantiateRule?, lookup]
  simp [motherRule, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?, relates, alice, bob]

private theorem fatherApplication :
    RuleApplication learned.target ⟨fatherRule.id, []⟩ [] (relates bob carol) := by
  apply instantiateRule?_eq_some_iff_application.mp
  have lookup : learned.target.1.lookupRule? fatherRule.id = some fatherRule := by decide
  simp only [instantiateRule?, lookup]
  simp [fatherRule, argumentsValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?, relates, bob, carol]

private theorem chainApplication :
    RuleApplication learned.target ⟨chainRule.id, [alice, bob, carol]⟩
      [relates alice bob, relates bob carol] (relates alice carol) := by
  apply instantiateRule?_eq_some_iff_application.mp
  have lookup : learned.target.1.lookupRule? chainRule.id = some chainRule := by decide
  simp only [instantiateRule?, lookup]
  simp [chainRule, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?, instantiateSchemaAt?,
    instantiateSchemas?, instantiateSchemasAt?, lookupArgumentAt?, relates, alice, bob, carol,
    Pattern.isGroundAt, Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def motherDerivation : Derivation learned.target (relates alice bob) :=
  .byRule ⟨motherRule.id, []⟩ motherApplication .nil

private def fatherDerivation : Derivation learned.target (relates bob carol) :=
  .byRule ⟨fatherRule.id, []⟩ fatherApplication .nil

private def chainDerivation : Derivation learned.target (relates alice carol) :=
  .byRule ⟨chainRule.id, [alice, bob, carol]⟩ chainApplication
    (.cons motherDerivation (.cons fatherDerivation .nil))

private theorem reach_classifies {source target : Pattern}
    (evidence : MILLearnedProofRelevantAdmission.Reach source target) :
    (source = alice ∧ target = bob ∧ HEq evidence MILLearnedProofRelevantAdmission.Reach.mother) ∨
    (source = bob ∧ target = carol ∧ HEq evidence MILLearnedProofRelevantAdmission.Reach.father) ∨
    (source = alice ∧ target = carol ∧
      HEq evidence (MILLearnedProofRelevantAdmission.Reach.chain .mother .father)) := by
  have ab : alice ≠ bob := by decide
  have ac : alice ≠ carol := by decide
  have bc : bob ≠ carol := by decide
  induction evidence with
  | mother => exact Or.inl ⟨rfl, rfl, HEq.rfl⟩
  | father => exact Or.inr (Or.inl ⟨rfl, rfl, HEq.rfl⟩)
  | chain first second firstIH secondIH =>
      rcases firstIH with firstIH | firstIH | firstIH <;>
        rcases secondIH with secondIH | secondIH | secondIH <;>
        rcases firstIH with ⟨rfl, rfl, firstEq⟩ <;>
        rcases secondIH with ⟨middleEq, targetEq, secondEq⟩
      all_goals try exact False.elim (ab middleEq.symm)
      all_goals try exact False.elim (ac middleEq.symm)
      all_goals try exact False.elim (bc middleEq.symm)
      cases targetEq
      cases eq_of_heq firstEq
      cases eq_of_heq secondEq
      exact Or.inr (Or.inr ⟨rfl, rfl, HEq.rfl⟩)

theorem mother_materialized :
    materialize? FormedQuotationCanary.quotation alice bob motherProof = some motherNative := by
  change materialize? FormedQuotationCanary.quotation alice bob motherDerivation.erase = _
  rw [materialize_derivation]
  have ab : alice ≠ bob := by decide
  have bc : bob ≠ carol := by decide
  have classified := reach_classifies (semantics.interpret motherDerivation)
  simp only [true_and, ab, bc, false_and, or_false] at classified
  rw [eq_of_heq classified]
  rfl

theorem father_materialized :
    materialize? FormedQuotationCanary.quotation bob carol fatherProof = some fatherNative := by
  change materialize? FormedQuotationCanary.quotation bob carol fatherDerivation.erase = _
  rw [materialize_derivation]
  have ba : bob ≠ alice := by decide
  have cb : carol ≠ bob := by decide
  have classified := reach_classifies (semantics.interpret fatherDerivation)
  simp only [true_and, ba, cb, false_and, or_false, false_or] at classified
  rw [eq_of_heq classified]
  rfl

theorem grandparent_materialized :
    materialize? FormedQuotationCanary.quotation alice carol grandparentProof = some grandparentNative := by
  change materialize? FormedQuotationCanary.quotation alice carol chainDerivation.erase = _
  rw [materialize_derivation]
  have ab : alice ≠ bob := by decide
  have cb : carol ≠ bob := by decide
  have classified := reach_classifies (semantics.interpret chainDerivation)
  simp only [true_and, ab, cb, false_and, false_or] at classified
  rw [eq_of_heq classified]
  rfl

theorem distinct_primitive_slots : motherNative ≠ fatherNative := by decide

theorem chain_not_replaced_by_primitive :
    materialize? FormedQuotationCanary.quotation alice carol grandparentProof ≠ some motherNative := by
  rw [grandparent_materialized]
  decide

theorem wrong_middle_rejected :
    materialize? FormedQuotationCanary.quotation alice bob wrongMiddleProof = none := by
  exact (materialize_eq_none_iff _ _ _ _).mpr wrongMiddleProof_rejected

theorem wrong_goal_rejected :
    materialize? FormedQuotationCanary.quotation alice bob grandparentProof = none := by
  apply (materialize_eq_none_iff _ _ _ _).mpr
  cases checked : checkRaw learned.target (relates alice bob) grandparentProof with
  | false => rfl
  | true =>
      have same := checkRaw_goal_unique grandparentProof_checked checked
      have different : relates alice carol ≠ relates alice bob := by decide
      exact False.elim (different same)

theorem swapped_children_rejected :
    materialize? FormedQuotationCanary.quotation alice carol swappedChildren = none := by
  apply (materialize_eq_none_iff _ _ _ _).mpr
  have outer := instantiateRule?_eq_some_iff_application.mpr chainApplication
  have inner := instantiateRule?_eq_some_iff_application.mpr fatherApplication
  simp only [swappedChildren, fatherProof, checkRaw, outer, inner, decide_true, checkRawChildren]
  have different : decide (relates bob carol = relates alice bob) = false := by decide
  rw [different]
  rfl

theorem missing_child_rejected :
    materialize? FormedQuotationCanary.quotation alice carol missingChild = none := by
  apply (materialize_eq_none_iff _ _ _ _).mpr
  have outer := instantiateRule?_eq_some_iff_application.mpr chainApplication
  simp only [missingChild, checkRaw, outer, decide_true, checkRawChildren, Bool.and_false]

theorem rejection_is_not_goal_refutation :
    materialize? FormedQuotationCanary.quotation alice bob wrongMiddleProof = none ∧
      materialize? FormedQuotationCanary.quotation alice bob motherProof = some motherNative :=
  ⟨wrong_middle_rejected, mother_materialized⟩

theorem materialized_grandparent_refined :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules FormedQuotationCanary.contextSPSMF
      grandparentNative (FormedQuotationCanary.quotation.hypothesisType () ()).code :=
  materialize_judgment RawInferenceMILWorkload.quotation_typed
    RawInferenceMILWorkload.quotation_context_formed grandparent_materialized

theorem materialized_grandparent_meaning :
    ∃ program : CheckedRawNativeProgram FormedQuotationCanary.quotation alice carol grandparentProof,
      program.toChecked.nativeTerm.code = grandparentNative ∧
      Nonempty (MILLearnedProofRelevantAdmission.Reach alice carol) ∧
      Nonempty (program.toChecked.intrinsicProgram.denotation.evidence alice carol) :=
  materialize_meaning grandparent_materialized

-- Compiled evaluation is additionally exercised independently of proof reduction.
#eval decide (materialize? FormedQuotationCanary.quotation alice carol grandparentProof =
  some grandparentNative)
#eval (materialize? FormedQuotationCanary.quotation alice bob wrongMiddleProof).isNone
#eval (materialize? FormedQuotationCanary.quotation alice carol swappedChildren).isNone

#print axioms mother_materialized
#print axioms father_materialized
#print axioms grandparent_materialized
#print axioms distinct_primitive_slots
#print axioms chain_not_replaced_by_primitive
#print axioms wrong_middle_rejected
#print axioms wrong_goal_rejected
#print axioms swapped_children_rejected
#print axioms missing_child_rejected
#print axioms rejection_is_not_goal_refutation
#print axioms materialized_grandparent_refined
#print axioms materialized_grandparent_meaning

end MILNativeMaterialization.Examples
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
