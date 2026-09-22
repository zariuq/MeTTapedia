import Mettapedia.GSLT.GraphTheory.PartialPairCompletionStages

/-!
# Stage-iteration controls

The second stage fills inputs involving first-stage fresh tokens while
retaining old codes and full supports. It neither collapses different fresh
tokens nor reflects unconditional definedness back to an earlier stage.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStagesControls

open CompletionStages

private def freshOutputInput (pair : PartialPair) (fresh : CompletionStep.Missing pair) :
    CompletionStep.Missing (stage pair 1) :=
  ⟨((∅ : Finset (CompletionStep.Carrier pair)), Sum.inr fresh), rfl⟩

private def freshSupportInput (pair : PartialPair) (fresh : CompletionStep.Missing pair) :
    CompletionStep.Missing (stage pair 1) :=
  ⟨(({Sum.inr fresh} : Finset (CompletionStep.Carrier pair)), Sum.inr fresh), rfl⟩

theorem old_code_preserved_twice (pair : PartialPair) (support : Finset pair.Carrier)
    (output token : pair.Carrier) (h : pair.coding.code (support, output) = some token) :
    (stage pair 2).coding.code
      ((support.map Function.Embedding.inl).map Function.Embedding.inl,
        Sum.inl (Sum.inl output)) = some (Sum.inl (Sum.inl token)) :=
  CompletionStep.code_preserves_defined (stage pair 1) _ _ _
    (CompletionStep.code_preserves_defined pair support output token h)

theorem first_fresh_output_undefined_at_first_stage (pair : PartialPair)
    (fresh : CompletionStep.Missing pair) :
    (stage pair 1).coding.code
      ((∅ : Finset (stage pair 1).Carrier), Sum.inr fresh) = none := rfl

theorem first_fresh_output_defined_at_second_stage (pair : PartialPair)
    (fresh : CompletionStep.Missing pair) :
    (stage pair 2).coding.code
      ((∅ : Finset (stage pair 1).Carrier).map Function.Embedding.inl,
        Sum.inl (Sum.inr fresh)) = some (Sum.inr (freshOutputInput pair fresh)) :=
  CompletionStep.code_fills_missing (stage pair 1) _ _
    (freshOutputInput pair fresh).property

theorem first_fresh_full_support_defined_at_second_stage (pair : PartialPair)
    (fresh : CompletionStep.Missing pair) :
    (stage pair 2).coding.code
      (({Sum.inr fresh} : Finset (stage pair 1).Carrier).map Function.Embedding.inl,
        Sum.inl (Sum.inr fresh)) = some (Sum.inr (freshSupportInput pair fresh)) :=
  CompletionStep.code_fills_missing (stage pair 1) _ _
    (freshSupportInput pair fresh).property

theorem second_stage_fresh_codes_retain_full_support (pair : PartialPair)
    (fresh : CompletionStep.Missing pair) :
    (stage pair 2).coding.code
      ((∅ : Finset (stage pair 1).Carrier).map Function.Embedding.inl,
        Sum.inl (Sum.inr fresh)) ≠
    (stage pair 2).coding.code
      (({Sum.inr fresh} : Finset (stage pair 1).Carrier).map Function.Embedding.inl,
        Sum.inl (Sum.inr fresh)) := by
  rw [first_fresh_output_defined_at_second_stage,
    first_fresh_full_support_defined_at_second_stage]
  intro h
  have hTokens := Sum.inr.inj (Option.some.inj h)
  have hSupports := congrArg (fun input => input.val.1) hTokens
  change (∅ : Finset (stage pair 1).Carrier) = {Sum.inr fresh} at hSupports
  exact Finset.empty_ne_singleton _ hSupports

theorem distinct_missing_tokens_stay_distinct (pair : PartialPair)
    (first second : CompletionStep.Missing pair) (hInputs : first.val ≠ second.val)
    {m : Nat} (h : 1 ≤ m) :
    inclusion pair h (Sum.inr first) ≠ inclusion pair h (Sum.inr second) := by
  intro hOutputs
  have hFresh := Sum.inr.inj ((inclusion pair h).injective hOutputs)
  exact hInputs (congrArg Subtype.val hFresh)

/-- Filling a missing input is a real increase of the coding domain. -/
theorem unconditional_definedness_not_reflected (pair : PartialPair)
    (missing : CompletionStep.Missing pair) :
    missing.val ∉ pair.domain ∧
      (missing.val.1.map Function.Embedding.inl, Sum.inl missing.val.2) ∈
        (stage pair 1).domain := by
  constructor
  · rintro ⟨token, hToken⟩
    rw [missing.property] at hToken
    cases hToken
  · exact ⟨Sum.inr missing,
      CompletionStep.code_fills_missing pair _ _ missing.property⟩

/-- A newly defined code still cannot impersonate an old carrier output. -/
theorem missing_input_ne_preserved_output (pair : PartialPair)
    (missing : CompletionStep.Missing pair) (token : pair.Carrier) :
    (stage pair 1).coding.code
      (missing.val.1.map Function.Embedding.inl, Sum.inl missing.val.2) ≠
        some (Sum.inl token) := by
  intro h
  have hOld := (successor_code_old_output_iff pair _ _ token).mp h
  rw [missing.property] at hOld
  cases hOld

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionStagesControls
