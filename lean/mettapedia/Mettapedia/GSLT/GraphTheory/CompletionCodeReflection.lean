import Mettapedia.GSLT.GraphTheory.PartialPairCompletion

/-!
# Full-input reflection for codes landing in the original partial pair

A completed code equal to an original token must have its entire finite
support and output in the original carrier, with an already-defined original
code. This reflects arbitrary completed inputs, rather than assuming that
the input already lies in an old stage.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.CompletionCodeReflection

open Mettapedia.GSLT.Core CompletionStages

theorem stage_code_base_input (pair : PartialPair) (n : Nat)
    (support : Finset (stage pair n).Carrier) (output : (stage pair n).Carrier)
    (token : pair.Carrier)
    (hCode : (stage pair n).coding.code (support, output) =
      some (inclusion pair (Nat.zero_le n) token)) :
    ∃ (originalSupport : Finset pair.Carrier) (originalOutput : pair.Carrier),
      pair.coding.code (originalSupport, originalOutput) = some token ∧
      support = originalSupport.map (inclusion pair (Nat.zero_le n)) ∧
      output = inclusion pair (Nat.zero_le n) originalOutput := by
  induction n with
  | zero =>
      rw [inclusion_self] at hCode ⊢
      exact ⟨support, output, hCode, Finset.map_refl.symm, rfl⟩
  | succ n ih =>
      rw [inclusion_succ pair (Nat.zero_le n)] at hCode
      cases output with
      | inr fresh => cases hCode
      | inl oldOutput =>
          obtain ⟨hTwoSort, hOld⟩ :=
            (CompletionStep.code_inl_some_iff (stage pair n) support oldOutput
              (Sum.inl (inclusion pair (Nat.zero_le n) token))).mp hCode
          cases hPrevious : (stage pair n).coding.code (support.toLeft, oldOutput) with
          | none =>
              rw [CompletionStep.oldCode_of_missing _ _ hPrevious] at hOld
              cases hOld
          | some oldToken =>
              rw [CompletionStep.oldCode_of_defined _ _ oldToken hPrevious] at hOld
              have hPreviousCode := hPrevious.trans (congrArg some (Sum.inl.inj hOld))
              obtain ⟨a, x, hOriginal, hSupport, hOutput⟩ :=
                ih support.toLeft oldOutput hPreviousCode
              refine ⟨a, x, hOriginal, ?_, ?_⟩
              · exact hTwoSort.trans
                  ((congrArg (Finset.map Function.Embedding.inl) hSupport).trans
                    (Finset.map_map _ _ _ |>.trans
                      (congrArg (fun f : pair.Carrier ↪ (stage pair (n + 1)).Carrier => a.map f)
                        (inclusion_succ pair (Nat.zero_le n)).symm)))
              · rw [inclusion_succ pair (Nat.zero_le n)]
                exact congrArg Sum.inl hOutput

/-- Later stages cannot manufacture a code impersonating an original token. -/
theorem code_eq_original_iff (pair : PartialPair)
    (support : Finset (Completion.Carrier pair)) (output : Completion.Carrier pair)
    (token : pair.Carrier) :
    Completion.code pair (support, output) = Completion.embed pair 0 token ↔
      ∃ (originalSupport : Finset pair.Carrier) (originalOutput : pair.Carrier),
        pair.coding.code (originalSupport, originalOutput) = some token ∧
        support = originalSupport.map (Completion.embed pair 0) ∧
        output = Completion.embed pair 0 originalOutput := by
  constructor
  · intro h
    obtain ⟨n, a, x, t, hA, hX, hCode, hT⟩ :=
      (Completion.code_eq_iff pair (support, output) (Completion.embed pair 0 token)).mp h
    have hToken : t = inclusion pair (Nat.zero_le n) token := by
      apply (Completion.embed pair n).injective
      exact hT.trans (Completion.embed_inclusion pair (Nat.zero_le n) token).symm
    rw [hToken] at hCode
    obtain ⟨originalSupport, originalOutput, hOriginal, hSupport, hOutput⟩ :=
      stage_code_base_input pair n a x token hCode
    refine ⟨originalSupport, originalOutput, hOriginal, ?_, ?_⟩
    · exact hA.symm.trans ((congrArg (Finset.map (Completion.embed pair n)) hSupport).trans
        (Completion.support_embed pair (Nat.zero_le n) originalSupport))
    · exact hX.symm.trans ((congrArg (Completion.embed pair n) hOutput).trans
        (Completion.embed_inclusion pair (Nat.zero_le n) originalOutput))
  · rintro ⟨a, x, hCode, rfl, rfl⟩
    exact Completion.code_preserves_original pair a x token hCode

end Mettapedia.GSLT.GraphTheory.PartialPair.CompletionCodeReflection
