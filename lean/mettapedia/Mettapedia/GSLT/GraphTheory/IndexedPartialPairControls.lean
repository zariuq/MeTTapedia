import Mettapedia.GSLT.GraphTheory.IndexedPartialPair
import Mettapedia.GSLT.Core.WebSemanticsControls

/-!
# Infinite-family controls for guarded partial-pair completion

The family has every natural number as an index. Pure coding is preserved and
reflected for any selected factor; the next index supplies a mixed-support
negative case whose completion really introduces a fresh token. Actual lambda
identity observations retain the different arguments zero and one.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.IndexedFamilyControls

open Mettapedia.GSLT.Core IndexedFamily FactorFlattening FactorInterpretation

private def models (_ : Nat) : GraphModel := GraphModel.naturalModel
private noncomputable abbrev pair := partialPair models
private noncomputable abbrev completed := Completion.graphModel pair
private abbrev selected (index : Nat) := factorEmbedding models index

private def mixedSupport (index : Nat) : Finset (IndexedFamily.Carrier models) :=
  {embedding models (index + 1) (0 : Nat)}

theorem every_pure_code_preserved (index : Nat) (support : Finset Nat) (output : Nat) :
    pair.coding.code (support.map (embedding models index), embedding models index output) =
      some (embedding models index (GraphModel.naturalModel.code support output)) :=
  code_preserves models index support output

theorem next_factor_support_undefined (index : Nat) :
    pair.coding.code (mixedSupport index, embedding models index (0 : Nat)) = none :=
  code_undefined_of_other_mem models index (index + 1) (Nat.succ_ne_self index)
    _ _ _ (Finset.mem_singleton_self _)

private noncomputable def missing (index : Nat) : CompletionStep.Missing pair :=
  ⟨(mixedSupport index, embedding models index (0 : Nat)), next_factor_support_undefined index⟩

private noncomputable def mixedCode (index : Nat) : completed.Carrier :=
  completed.code ((mixedSupport index).map (Completion.embed pair 0))
    (Completion.embed pair 0 (embedding models index (0 : Nat)))

theorem completion_supplies_actual_fresh_code (index : Nat) :
    mixedCode index = Completion.embed pair 1 (Sum.inr (missing index)) :=
  Completion.code_fills_stage_missing pair 0 _ _ (missing index).property

theorem mixed_code_not_any_original (index : Nat) (old : pair.Carrier) :
    mixedCode index ≠ Completion.embed pair 0 old := by
  intro equal
  have included : Completion.embed pair 1 (Sum.inl old) = Completion.embed pair 0 old :=
    Completion.embed_inclusion pair (Nat.le_succ 0) old
  have clash := (Completion.embed pair 1).injective
    ((completion_supplies_actual_fresh_code index).symm.trans (equal.trans included.symm))
  cases clash

theorem completed_pure_code_preserved (index : Nat) (support : Finset Nat) (output : Nat) :
    completed.code (support.map (factorEmbed (selected index)))
      (factorEmbed (selected index) output) =
      factorEmbed (selected index) (GraphModel.naturalModel.code support output) :=
  code_factor (selected index) support output

/-- Reflection keeps the entire completed support, not just its projection. -/
theorem completed_pure_code_reflects (index : Nat)
    (support : Finset completed.Carrier) (output : completed.Carrier) (token : Nat) :
    completed.code support output = factorEmbed (selected index) token ↔
      ∃ (factorSupport : Finset Nat) (factorOutput : Nat),
        GraphModel.naturalModel.code factorSupport factorOutput = token ∧
        support = factorSupport.map (factorEmbed (selected index)) ∧
        output = factorEmbed (selected index) factorOutput :=
  code_eq_factor_iff (selected index) support output token

theorem selected_factor_rejects_next_token (index : Nat) :
    (selected index).selector (embedding models (index + 1) (0 : Nat)) = none := by
  apply ((selected index).selector_none_iff _).mpr
  rintro ⟨value, equal⟩
  exact Nat.succ_ne_self index (congrArg Sigma.fst equal).symm

/-- The same existing interpreter theorem applies at each index of the
infinite family; these are real arguments, not a constant observation. -/
theorem actual_identity_input (index value : Nat) :
    (factorEmbed (selected index)) ⁻¹'
      interpret completed (liftEnv (selected index) (fun _ => {value}))
        (.app LambdaTerm.I (.var 0)) = {value} := by
  refine (interpret_lift_factor (selected index)
    (.app LambdaTerm.I (.var 0)) (fun _ => {value})).trans ?_
  change GraphModel.naturalModel.apply
    (interpret GraphModel.naturalModel (fun _ => {value}) LambdaTerm.I) {value} = {value}
  rw [interpret_I]
  exact GraphModel.naturalModel.identity_application _

theorem actual_inputs_zero_one_differ (index : Nat) :
    (factorEmbed (selected index)) ⁻¹'
      interpret completed (liftEnv (selected index) (fun _ => {(0 : Nat)}))
        (.app LambdaTerm.I (.var 0)) ≠
    (factorEmbed (selected index)) ⁻¹'
      interpret completed (liftEnv (selected index) (fun _ => {(1 : Nat)}))
        (.app LambdaTerm.I (.var 0)) := by
  rw [actual_identity_input, actual_identity_input]
  exact fun equal => (show (0 : Nat) ≠ 1 by decide) (Set.singleton_injective equal)

theorem actual_infinite_family_lower_bound (index : Nat) :
    lambdaTheoryOf completed ≤ lambdaTheoryOf (models index) :=
  completion_theory_lower_bound models index

/-- The indexed model construction also supplies the abstract graph-theory
existence result, retaining actual model witnesses for the theory family. -/
theorem actual_theory_family_has_graph_lower_bound :
    ∃ lower : LambdaTheory, IsGraphTheory lower ∧
      ∀ index : Nat, lower ≤ lambdaTheoryOf (models index) :=
  graphTheories_lower_bound (fun index => lambdaTheoryOf (models index))
    (fun index => lambdaTheoryOf_isGraphTheory (models index))

end Mettapedia.GSLT.GraphTheory.PartialPair.IndexedFamilyControls
