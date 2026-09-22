import Mettapedia.GSLT.GraphTheory.FactorInterpretation
import Mettapedia.GSLT.Core.WebSemanticsControls

/-!
# Actual-interpreter controls for factor comparison

Distinct identity inputs survive exact factor comparison. A literal mixed-code
environment is not flattening-closed, and its application has a factor output
that is absent from factor interpretation. Thus the environment-closure
hypothesis cannot simply be omitted from the proved comparison theorem.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.FactorInterpretationControls

open Mettapedia.GSLT.Core FactorFlattening FactorInterpretation

private abbrev natPair : PartialPair :=
  disjointUnion GraphModel.naturalModel GraphModel.naturalModel

private abbrev leftFactor : FactorEmbedding natPair GraphModel.naturalModel :=
  FactorEmbedding.left GraphModel.naturalModel GraphModel.naturalModel

private abbrev rightFactor : FactorEmbedding natPair GraphModel.naturalModel :=
  FactorEmbedding.right GraphModel.naturalModel GraphModel.naturalModel

private noncomputable abbrev completed : GraphModel := Completion.graphModel natPair

private def mixedSupport : Finset (Nat ⊕ Nat) := {Sum.inr 0}

private def missingMixed : CompletionStep.Missing natPair :=
  ⟨(mixedSupport, Sum.inl (0 : Nat)),
    disjointUnionCode_inl_none_of_inr_mem GraphModel.naturalModel GraphModel.naturalModel
      _ (0 : Nat) (0 : Nat) (Finset.mem_singleton_self (Sum.inr (0 : Nat)))⟩

private noncomputable def mixedCode : completed.Carrier :=
  completed.code (mixedSupport.map (Completion.embed natPair 0))
    (Completion.embed natPair 0 (Sum.inl (0 : Nat)))

private noncomputable def literalEnv : Env completed
  | 0 => {mixedCode}
  | 1 => {Completion.embed natPair 0 (Sum.inr (0 : Nat))}
  | _ + 2 => ∅

private def application : LambdaTerm := .app (.var 0) (.var 1)

theorem mixed_code_is_fresh : mixedCode = Completion.embed natPair 1 (Sum.inr missingMixed) :=
  Completion.code_fills_stage_missing natPair 0 _ _ missingMixed.property

theorem mixed_code_is_outside_original_factor (value : Nat) :
    mixedCode ≠ factorEmbed leftFactor value := by
  intro h
  have hLeft : Completion.embed natPair 1 (Sum.inl (Sum.inl value)) =
      factorEmbed leftFactor value :=
    Completion.embed_inclusion natPair (Nat.le_succ 0) (Sum.inl value)
  have hClash := (Completion.embed natPair 1).injective
    (mixed_code_is_fresh.symm.trans (h.trans hLeft.symm))
  cases hClash

theorem literal_environment_not_closed :
    ¬ClosedEnv leftFactor literalEnv := by
  intro h
  have hMember := h 0 mixedCode (Set.mem_singleton mixedCode)
  have hFlat := flatten_code_of_some leftFactor
    (mixedSupport.map (Completion.embed natPair 0))
    (Completion.embed natPair 0 (Sum.inl (0 : Nat))) (0 : Nat) (decoder_factor leftFactor (0 : Nat))
  have hEq := (Set.mem_singleton_iff.mp hMember).symm.trans hFlat
  exact mixed_code_is_outside_original_factor _ hEq

theorem literal_application_has_factor_output :
    factorEmbed leftFactor (0 : Nat) ∈
      interpret completed literalEnv application := by
  refine ⟨mixedSupport.map (Completion.embed natPair 0), ?_, Set.mem_singleton mixedCode⟩
  intro token hToken
  obtain ⟨old, hOld, rfl⟩ := Finset.mem_map.mp hToken
  have hOldEq := Finset.mem_singleton.mp hOld
  subst old
  exact Set.mem_singleton _

theorem literal_factor_environment_zero_empty :
    factorEnv leftFactor literalEnv 0 = ∅ := by
  ext value
  constructor
  · intro h
    exact False.elim (mixed_code_is_outside_original_factor value
      (Set.mem_singleton_iff.mp h).symm)
  · exact False.elim

theorem literal_factor_application_empty :
    interpret GraphModel.naturalModel
      (factorEnv leftFactor literalEnv) application = ∅ := by
  change GraphModel.naturalModel.apply
    (factorEnv leftFactor literalEnv 0)
    (factorEnv leftFactor literalEnv 1) = ∅
  rw [literal_factor_environment_zero_empty, GraphModel.apply_empty]

theorem factor_comparison_fails_without_environment_closure :
    ¬(factorEmbed leftFactor (0 : Nat) ∈
        interpret completed literalEnv application ↔
      (0 : Nat) ∈ interpret GraphModel.naturalModel
        (factorEnv leftFactor literalEnv) application) := by
  intro h
  have hFalse := h.mp literal_application_has_factor_output
  rw [literal_factor_application_empty] at hFalse
  exact hFalse

theorem actual_identity_factor_input (value : Nat) :
    (factorEmbed leftFactor) ⁻¹'
      interpret completed
        (liftEnv leftFactor (fun _ => {value}))
        (.app LambdaTerm.I (.var 0)) = {value} := by
  refine (interpret_lift_factor leftFactor
    (.app LambdaTerm.I (.var 0)) (fun _ => {value})).trans ?_
  change GraphModel.naturalModel.apply
    (interpret GraphModel.naturalModel (fun _ => {value}) LambdaTerm.I) {value} = {value}
  rw [interpret_I]
  exact GraphModel.naturalModel.identity_application _

theorem identity_factor_comparison_distinguishes_actual_inputs :
    (factorEmbed leftFactor) ⁻¹'
      interpret completed
        (liftEnv leftFactor (fun _ => {(0 : Nat)}))
        (.app LambdaTerm.I (.var 0)) ≠
    (factorEmbed leftFactor) ⁻¹'
      interpret completed
        (liftEnv leftFactor (fun _ => {(1 : Nat)}))
        (.app LambdaTerm.I (.var 0)) := by
  rw [actual_identity_factor_input, actual_identity_factor_input]
  exact fun h => (show (0 : Nat) ≠ 1 by decide) (Set.singleton_injective h)

theorem actual_identity_right_factor_input (value : Nat) :
    (factorEmbed rightFactor) ⁻¹' interpret completed
      (liftEnv rightFactor (fun _ => {value})) (.app LambdaTerm.I (.var 0)) = {value} := by
  refine (interpret_lift_factor rightFactor
    (.app LambdaTerm.I (.var 0)) (fun _ => {value})).trans ?_
  change GraphModel.naturalModel.apply
    (interpret GraphModel.naturalModel (fun _ => {value}) LambdaTerm.I) {value} = {value}
  rw [interpret_I]
  exact GraphModel.naturalModel.identity_application _

theorem right_factor_comparison_distinguishes_actual_inputs :
    (factorEmbed rightFactor) ⁻¹' interpret completed
      (liftEnv rightFactor (fun _ => {(0 : Nat)})) (.app LambdaTerm.I (.var 0)) ≠
    (factorEmbed rightFactor) ⁻¹' interpret completed
      (liftEnv rightFactor (fun _ => {(1 : Nat)})) (.app LambdaTerm.I (.var 0)) := by
  rw [actual_identity_right_factor_input, actual_identity_right_factor_input]
  exact fun h => (show (0 : Nat) ≠ 1 by decide) (Set.singleton_injective h)

theorem actual_completion_theory_below_both_factors :
    lambdaTheoryOf completed ≤ lambdaTheoryOf GraphModel.naturalModel ∧
      lambdaTheoryOf completed ≤ lambdaTheoryOf GraphModel.naturalModel :=
  disjointUnion_theory_lower_bound GraphModel.naturalModel GraphModel.naturalModel

end Mettapedia.GSLT.GraphTheory.PartialPair.FactorInterpretationControls
