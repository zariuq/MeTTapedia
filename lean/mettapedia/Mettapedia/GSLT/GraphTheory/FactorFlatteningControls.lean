import Mettapedia.GSLT.GraphTheory.FactorFlattening
import Mettapedia.GSLT.Core.WebSemanticsControls

/-!
# Information-loss controls for source factor flattening

The genuine canonical completion keeps pure and mixed full-support codes
distinct. Its source flattening identifies the two when the opposite-factor
support is discarded. This is not a failure of the completed coding injection
and does not establish interpretation invariance under inverse image.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.FactorFlatteningControls

open Mettapedia.GSLT.Core FactorFlattening

private abbrev natPair : PartialPair :=
  disjointUnion GraphModel.naturalModel GraphModel.naturalModel

private abbrev leftFactor : FactorEmbedding natPair GraphModel.naturalModel :=
  FactorEmbedding.left GraphModel.naturalModel GraphModel.naturalModel

private def mixedSupport : Finset (Nat ⊕ Nat) := {Sum.inr 0}

private noncomputable def pureCode : Completion.Carrier natPair :=
  Completion.code natPair ((∅ : Finset (Nat ⊕ Nat)).map (Completion.embed natPair 0),
    Completion.embed natPair 0 (Sum.inl (0 : Nat)))

private noncomputable def mixedCode : Completion.Carrier natPair :=
  Completion.code natPair (mixedSupport.map (Completion.embed natPair 0),
    Completion.embed natPair 0 (Sum.inl (0 : Nat)))

private def missingMixed : CompletionStep.Missing natPair :=
  ⟨(mixedSupport, Sum.inl (0 : Nat)),
    disjointUnionCode_inl_none_of_inr_mem GraphModel.naturalModel GraphModel.naturalModel
      _ (0 : Nat) (0 : Nat) (Finset.mem_singleton_self (Sum.inr (0 : Nat)))⟩

theorem pure_code_is_old_factor_code :
    pureCode = factorEmbed leftFactor
      (GraphModel.naturalModel.coding.code ((∅ : Finset Nat), (0 : Nat))) := by
  exact Completion.code_preserves_original natPair _ _ _
    (disjointUnionCode_left GraphModel.naturalModel GraphModel.naturalModel ∅ (0 : Nat))

theorem mixed_code_is_actual_fresh_token :
    mixedCode = Completion.embed natPair 1 (Sum.inr missingMixed) :=
  Completion.code_fills_stage_missing natPair 0 _ _ missingMixed.property

theorem pure_and_mixed_codes_are_distinct : pureCode ≠ mixedCode := by
  intro h
  have hInputs := Completion.code_injective natPair h
  have hSupports := Finset.map_injective (Completion.embed natPair 0)
    (congrArg Prod.fst hInputs)
  exact Finset.empty_ne_singleton _ hSupports

theorem mixed_support_factor_projection_empty :
    projection leftFactor
      (mixedSupport.map (Completion.embed natPair 0)) = ∅ := by
  refine (projection_embed leftFactor 0
    mixedSupport).trans ?_
  refine (stageProjection_zero leftFactor
    mixedSupport).trans ?_
  ext value
  exact (leftFactor.mem_projection_iff mixedSupport value).trans
    (by
      constructor
      · intro h
        have hBad := Finset.mem_singleton.mp h
        cases hBad
      · intro h
        exact False.elim (Finset.notMem_empty value h))

theorem mixed_code_flattens_to_old_factor_code :
    flatten leftFactor mixedCode =
      factorEmbed leftFactor
        (GraphModel.naturalModel.coding.code ((∅ : Finset Nat), (0 : Nat))) := by
  have h := flatten_code_of_some leftFactor
    (mixedSupport.map (Completion.embed natPair 0))
    (Completion.embed natPair 0 (Sum.inl (0 : Nat))) (0 : Nat) (decoder_factor leftFactor (0 : Nat))
  exact h.trans (congrArg (fun support : Finset Nat =>
    factorEmbed leftFactor
      (GraphModel.naturalModel.coding.code (support, (0 : Nat))))
        mixed_support_factor_projection_empty)

theorem distinct_completed_codes_share_flattening :
    pureCode ≠ mixedCode ∧
      flatten leftFactor pureCode =
        flatten leftFactor mixedCode := by
  refine ⟨pure_and_mixed_codes_are_distinct, ?_⟩
  rw [pure_code_is_old_factor_code, flatten_factor, mixed_code_flattens_to_old_factor_code]

theorem actual_factor_flattening_not_injective :
    ¬Function.Injective (flatten leftFactor) := by
  intro h
  exact distinct_completed_codes_share_flattening.1
    (h distinct_completed_codes_share_flattening.2)

theorem old_right_token_is_retained :
    flatten leftFactor
      (Completion.embed natPair 0 (Sum.inr (0 : Nat))) =
      Completion.embed natPair 0 (Sum.inr (0 : Nat)) :=
  flatten_original leftFactor _

theorem old_right_token_does_not_land_in_left_factor :
    ∀ value : Nat, flatten leftFactor
      (Completion.embed natPair 0 (Sum.inr (0 : Nat))) ≠
        factorEmbed leftFactor value := by
  intro value h
  have hDecoder := (flatten_eq_factor_iff leftFactor _ _).mp h
  have hNone : leftFactor.selector (Sum.inr (0 : Nat)) = none :=
    (leftFactor.selector_none_iff _).mpr (by
      rintro ⟨old, hOld⟩
      cases hOld)
  have hBad := hNone.symm.trans hDecoder
  cases hBad

end Mettapedia.GSLT.GraphTheory.PartialPair.FactorFlatteningControls
