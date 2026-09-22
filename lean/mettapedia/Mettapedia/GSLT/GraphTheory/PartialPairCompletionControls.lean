import Mettapedia.GSLT.GraphTheory.PartialPairCompletion
import Mettapedia.GSLT.Core.WebSemanticsControls
import Mettapedia.GSLT.GraphTheory.Interpretation

/-!
# Completed-model controls

The actual canonical completion of a disjoint union of genuine Nat graph
models preserves pure codes, distinguishes full mixed supports, and codes
fresh-dependent inputs. Its native lambda identity retains distinct actual
inputs rather than returning a fixed result.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionControls

open Mettapedia.GSLT.Core CompletionStages

private abbrev natPair : PartialPair :=
  disjointUnion GraphModel.naturalModel GraphModel.naturalModel

private def mixedInput : CompletionStep.Missing natPair :=
  ⟨(({Sum.inr 0} : Finset (Nat ⊕ Nat)), Sum.inl (0 : Nat)),
    disjointUnionCode_inl_none_of_inr_mem GraphModel.naturalModel GraphModel.naturalModel
      _ (0 : Nat) (0 : Nat)
      (Finset.mem_singleton_self (Sum.inr (0 : Nat)))⟩

private def freshOutputInput : CompletionStep.Missing (stage natPair 1) :=
  ⟨((∅ : Finset (stage natPair 1).Carrier), Sum.inr mixedInput), rfl⟩

private def freshSupportInput : CompletionStep.Missing (stage natPair 1) :=
  ⟨(({Sum.inr mixedInput} : Finset (stage natPair 1).Carrier), Sum.inr mixedInput), rfl⟩

theorem completed_pure_code_preserved (support : Finset Nat) (output : Nat) :
    (Completion.graphModel natPair).coding.code
      ((support.map Function.Embedding.inl).map (Completion.embed natPair 0),
        Completion.embed natPair 0 (Sum.inl output)) =
      Completion.embed natPair 0
        (Sum.inl (GraphModel.naturalModel.coding.code (support, output))) :=
  Completion.code_preserves_original natPair _ _ _
    (disjointUnionCode_left GraphModel.naturalModel GraphModel.naturalModel support output)

theorem completed_mixed_code_is_actual_fresh_token :
    (Completion.graphModel natPair).coding.code
      (({Sum.inr 0} : Finset (Nat ⊕ Nat)).map (Completion.embed natPair 0),
        Completion.embed natPair 0 (Sum.inl (0 : Nat))) =
      Completion.embed natPair 1 (Sum.inr mixedInput) :=
  Completion.code_fills_stage_missing natPair 0 _ _ mixedInput.property

theorem completed_mixed_code_differs_from_pure :
    (Completion.graphModel natPair).coding.code
      ((∅ : Finset (Nat ⊕ Nat)).map (Completion.embed natPair 0),
        Completion.embed natPair 0 (Sum.inl (0 : Nat))) ≠
    (Completion.graphModel natPair).coding.code
      (({Sum.inr 0} : Finset (Nat ⊕ Nat)).map (Completion.embed natPair 0),
        Completion.embed natPair 0 (Sum.inl (0 : Nat))) := by
  intro h
  have hInputs := (Completion.graphModel natPair).coding.injective h
  have hSupports := Finset.map_injective (Completion.embed natPair 0)
    (congrArg Prod.fst hInputs)
  exact Finset.empty_ne_singleton _ hSupports

theorem completed_first_fresh_output_has_code :
    (Completion.graphModel natPair).coding.code
      ((∅ : Finset (stage natPair 1).Carrier).map (Completion.embed natPair 1),
        Completion.embed natPair 1 (Sum.inr mixedInput)) =
      Completion.embed natPair 2 (Sum.inr freshOutputInput) :=
  Completion.code_fills_stage_missing natPair 1 _ _ freshOutputInput.property

theorem completed_first_fresh_full_support_has_code :
    (Completion.graphModel natPair).coding.code
      (({Sum.inr mixedInput} : Finset (stage natPair 1).Carrier).map (Completion.embed natPair 1),
        Completion.embed natPair 1 (Sum.inr mixedInput)) =
      Completion.embed natPair 2 (Sum.inr freshSupportInput) :=
  Completion.code_fills_stage_missing natPair 1 _ _ freshSupportInput.property

theorem completed_fresh_dependent_codes_distinct :
    (Completion.graphModel natPair).coding.code
      ((∅ : Finset (stage natPair 1).Carrier).map (Completion.embed natPair 1),
        Completion.embed natPair 1 (Sum.inr mixedInput)) ≠
    (Completion.graphModel natPair).coding.code
      (({Sum.inr mixedInput} : Finset (stage natPair 1).Carrier).map (Completion.embed natPair 1),
        Completion.embed natPair 1 (Sum.inr mixedInput)) := by
  intro h
  have hInputs := (Completion.graphModel natPair).coding.injective h
  have hSupports := Finset.map_injective (Completion.embed natPair 1)
    (congrArg Prod.fst hInputs)
  exact Finset.empty_ne_singleton _ hSupports

theorem completed_original_tokens_distinct :
    Completion.embed natPair 0 (Sum.inl (0 : Nat)) ≠
      Completion.embed natPair 0 (Sum.inl (1 : Nat)) := by
  intro h
  have hNumbers := Sum.inl.inj ((Completion.embed natPair 0).injective h)
  exact (show (0 : Nat) ≠ 1 by decide) hNumbers

theorem completed_native_identity_returns_zero :
    let D := Completion.graphModel natPair
    ∀ ρ : Env D, D.apply (interpret D ρ LambdaTerm.I)
      {Completion.embed natPair 0 (Sum.inl (0 : Nat))} =
        {Completion.embed natPair 0 (Sum.inl (0 : Nat))} := by
  intro D ρ
  rw [interpret_I]
  exact D.identity_application _

theorem completed_native_identity_returns_one :
    let D := Completion.graphModel natPair
    ∀ ρ : Env D, D.apply (interpret D ρ LambdaTerm.I)
      {Completion.embed natPair 0 (Sum.inl (1 : Nat))} =
        {Completion.embed natPair 0 (Sum.inl (1 : Nat))} := by
  intro D ρ
  rw [interpret_I]
  exact D.identity_application _

theorem completed_native_identity_distinguishes_zero_one :
    let D := Completion.graphModel natPair
    ∀ ρ : Env D, D.apply (interpret D ρ LambdaTerm.I)
      {Completion.embed natPair 0 (Sum.inl (0 : Nat))} ≠
    D.apply (interpret D ρ LambdaTerm.I) {Completion.embed natPair 0 (Sum.inl (1 : Nat))} := by
  intro D ρ
  rw [interpret_I]
  exact D.identity_distinguishes_inputs _ _ completed_original_tokens_distinct

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionControls
