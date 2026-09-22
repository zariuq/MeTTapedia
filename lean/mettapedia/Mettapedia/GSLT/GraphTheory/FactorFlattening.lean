import Mettapedia.GSLT.GraphTheory.PartialPairCompletion
import Mettapedia.GSLT.GraphTheory.PartialPairFactorEmbedding
import Mathlib.Data.Finset.Option

/-!
# Selected-factor flattening of an actual canonical completion

Bucciarelli–Salibra §3.1 Definition 7 fixes old tokens and sends a fresh
full-pair token into the factor exactly when its recursively flattened
output lies there. The stage decoder below records that factor value, not
an injective encoding. Its coherent direct-limit lift defines the actual
flattening into the completed model. No interpretation invariance or
theory-intersection conclusion is assumed by this construction.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.FactorFlattening

open Mettapedia.GSLT.Core CompletionStages

noncomputable local instance (pair : PartialPair) :
    DecidableEq (Completion.Carrier pair) := Classical.decEq _

noncomputable def stageDecoder {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) :
    (n : Nat) → (stage pair n).Carrier → Option factor.Carrier
  | 0, token => e.selector token
  | n + 1, .inl token => stageDecoder e n token
  | n + 1, .inr missing =>
      (stageDecoder e n missing.val.2).map (fun output =>
        factor.coding.code (Finset.eraseNone (missing.val.1.image (stageDecoder e n)), output))

noncomputable def stageProjection {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (n : Nat)
    (support : Finset (stage pair n).Carrier) : Finset factor.Carrier :=
  Finset.eraseNone (support.image (stageDecoder e n))

theorem stageDecoder_inclusion {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) {n m : Nat} (h : n ≤ m)
    (token : (stage pair n).Carrier) :
    stageDecoder e m (inclusion pair h token) =
      stageDecoder e n token := by
  induction h with
  | refl => rw [inclusion_self]; rfl
  | @step m h ih =>
      rw [inclusion_succ pair h]
      exact ih

theorem stageProjection_inclusion {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) {n m : Nat} (h : n ≤ m)
    (support : Finset (stage pair n).Carrier) :
    stageProjection e m (support.map (inclusion pair h)) =
      stageProjection e n support := by
  ext token
  simp only [stageProjection, Finset.mem_eraseNone, Finset.mem_image, Finset.mem_map]
  constructor
  · rintro ⟨large, ⟨old, hOld, rfl⟩, hValue⟩
    exact ⟨old, hOld, (stageDecoder_inclusion e h old).symm.trans hValue⟩
  · rintro ⟨old, hOld, hValue⟩
    exact ⟨inclusion pair h old, ⟨old, hOld, rfl⟩,
      (stageDecoder_inclusion e h old).trans hValue⟩

theorem stageProjection_old {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (n : Nat)
    (support : Finset (stage pair n).Carrier) :
    stageProjection e (n + 1) (support.map Function.Embedding.inl) =
      stageProjection e n support := by
  exact (congrArg (fun f : (stage pair n).Carrier ↪
      (stage pair (n + 1)).Carrier =>
        stageProjection e (n + 1) (support.map f))
      (inclusion_next pair n)).symm.trans
    (stageProjection_inclusion e (Nat.le_succ n) support)

theorem stageProjection_zero {pair : PartialPair} {factor : GraphModel}
    (e : FactorEmbedding pair factor) (support : Finset pair.Carrier) :
    stageProjection e 0 support = e.projection support := rfl

/-- Actual defined stage codes obey the source factor-decoding equation. -/
theorem stageDecoder_code {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (n : Nat)
    (support : Finset (stage pair n).Carrier)
    (output token : (stage pair n).Carrier)
    (hCode : (stage pair n).coding.code (support, output) = some token) :
    stageDecoder e n token = (stageDecoder e n output).map
      (fun value => factor.coding.code (stageProjection e n support, value)) := by
  induction n with
  | zero => exact e.selector_code support output token hCode
  | succ n ih =>
      cases output with
      | inr missing => cases hCode
      | inl output =>
          obtain ⟨hTwoSort, hToken⟩ :=
            (CompletionStep.code_inl_some_iff (stage pair n)
              support output token).mp hCode
          subst token
          have hProjection : stageProjection e (n + 1) support =
              stageProjection e n support.toLeft :=
            (congrArg (stageProjection e (n + 1)) hTwoSort).trans
              (stageProjection_old e n support.toLeft)
          cases hOld : (stage pair n).coding.code (support.toLeft, output) with
          | none =>
              rw [CompletionStep.oldCode_of_missing _ _ hOld]
              simp only [stageDecoder, hProjection]
              rfl
          | some oldToken =>
              rw [CompletionStep.oldCode_of_defined _ _ oldToken hOld]
              simp only [stageDecoder, hProjection]
              exact ih support.toLeft output oldToken hOld

noncomputable def decoder {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) : Completion.Carrier pair → Option factor.Carrier :=
  DirectLimit.lift (fun _ _ h => inclusion pair h)
    (stageDecoder e) (fun _ _ h token => (stageDecoder_inclusion e h token).symm)

theorem decoder_embed {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (n : Nat)
    (token : (stage pair n).Carrier) :
    decoder e (Completion.embed pair n token) =
      stageDecoder e n token := rfl

def factorEmbed {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) : factor.Carrier ↪ Completion.Carrier pair :=
  e.embedding.trans (Completion.embed pair 0)

theorem decoder_factor {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (token : factor.Carrier) :
    decoder e (factorEmbed e token) = some token :=
  e.selector_embedding token

theorem decoder_original {pair : PartialPair} {factor : GraphModel}
    (e : FactorEmbedding pair factor) (token : pair.Carrier) :
    decoder e (Completion.embed pair 0 token) = e.selector token := rfl

noncomputable def projection {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair)) : Finset factor.Carrier :=
  Finset.eraseNone (support.image (decoder e))

theorem mem_projection_iff {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair)) (token : factor.Carrier) :
    token ∈ projection e support ↔
      ∃ old ∈ support, decoder e old = some token := by
  simp only [projection, Finset.mem_eraseNone, Finset.mem_image]

theorem projection_embed {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (n : Nat)
    (support : Finset (stage pair n).Carrier) :
    projection e (support.map (Completion.embed pair n)) =
      stageProjection e n support := by
  ext token
  simp only [mem_projection_iff, stageProjection, Finset.mem_eraseNone, Finset.mem_image,
    Finset.mem_map]
  constructor
  · rintro ⟨large, ⟨old, hOld, rfl⟩, hValue⟩
    exact ⟨old, hOld, hValue⟩
  · rintro ⟨old, hOld, hValue⟩
    exact ⟨Completion.embed pair n old, ⟨old, hOld, rfl⟩, hValue⟩

/-- The actual completed-model coding law, including its finite factor support. -/
theorem decoder_code {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair))
    (output : Completion.Carrier pair) :
    decoder e (Completion.code pair (support, output)) =
      (decoder e output).map (fun value => factor.coding.code (projection e support, value)) := by
  obtain ⟨n, oldSupport, oldOutput, oldToken, hSupport, hOutput, hCode, hToken⟩ :=
    Completion.code_spec pair (support, output)
  change oldSupport.map (Completion.embed pair n) = support at hSupport
  change Completion.embed pair n oldOutput = output at hOutput
  rw [← hToken, ← hOutput, ← hSupport, decoder_embed, decoder_embed, projection_embed]
  exact stageDecoder_code e n oldSupport oldOutput oldToken hCode

/-- The source E→E flattening keeps a token unchanged when it does not land in the factor. -/
noncomputable def flatten {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (token : Completion.Carrier pair) :
    Completion.Carrier pair :=
  match decoder e token with
  | some value => factorEmbed e value
  | none => token

theorem flatten_factor {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor) (token : factor.Carrier) :
    flatten e (factorEmbed e token) = factorEmbed e token := by
  simp only [flatten, decoder_factor]

/-- All original tokens are fixed, including those outside the selected factor. -/
theorem flatten_original {pair : PartialPair} {factor : GraphModel}
    (e : FactorEmbedding pair factor) (token : pair.Carrier) :
    flatten e (Completion.embed pair 0 token) = Completion.embed pair 0 token := by
  cases h : e.selector token with
  | none => simp only [flatten, decoder_original, h]
  | some value =>
      have hToken := (e.selector_some_iff token value).mp h
      simp only [flatten, decoder_original, h]
      exact congrArg (Completion.embed pair 0) hToken.symm

theorem flatten_eq_factor_iff {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (token : Completion.Carrier pair) (value : factor.Carrier) :
    flatten e token = factorEmbed e value ↔ decoder e token = some value := by
  unfold flatten
  cases h : decoder e token with
  | none =>
      constructor
      · intro hToken
        have hValue := decoder_factor e value
        rw [← hToken, h] at hValue
        cases hValue
      · intro hValue; cases hValue
  | some old =>
      simp only [EmbeddingLike.apply_eq_iff_eq, Option.some.injEq]

theorem flatten_idempotent {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (token : Completion.Carrier pair) :
    flatten e (flatten e token) = flatten e token := by
  cases h : decoder e token with
  | none => simp only [flatten, h]
  | some value => simp only [flatten, h, decoder_factor]

/-- The finite factor support is the factor part of the flattened full image. -/
theorem mem_flatten_image_factor_iff {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair)) (value : factor.Carrier) :
    factorEmbed e value ∈ support.image (flatten e) ↔
      value ∈ projection e support := by
  simp only [Finset.mem_image, flatten_eq_factor_iff, mem_projection_iff]

/-- Source Fact 8(a): flattening fixes every output outside the selected factor. -/
theorem flatten_eq_self_of_outside {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (token : Completion.Carrier pair)
    (h : ∀ value, flatten e token ≠ factorEmbed e value) :
    flatten e token = token := by
  cases hValue : decoder e token with
  | none => simp only [flatten, hValue]
  | some value => exact False.elim (h value ((flatten_eq_factor_iff e _ _).mpr hValue))

/-- Closing a finite support under flattening changes none of its factor support. -/
theorem mem_closed_support_factor_iff {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair)) (value : factor.Carrier) :
    factorEmbed e value ∈ support ∪ support.image (flatten e) ↔
      value ∈ projection e support := by
  rw [Finset.mem_union, mem_flatten_image_factor_iff]
  constructor
  · rintro (hOld | hValue)
    · exact (mem_projection_iff e support value).mpr
        ⟨factorEmbed e value, hOld, decoder_factor e value⟩
    · exact hValue
  · exact Or.inr

theorem projection_flatten_image {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair)) :
    projection e (support.image (flatten e)) = projection e support := by
  ext value
  simp only [mem_projection_iff, Finset.mem_image]
  constructor
  · rintro ⟨token, ⟨old, hOld, rfl⟩, hValue⟩
    cases h : decoder e old with
    | none =>
        exact ⟨old, hOld, by simpa only [flatten, h] using hValue⟩
    | some v =>
        simp only [flatten, h, decoder_factor, Option.some.injEq] at hValue
        exact ⟨old, hOld, h.trans (congrArg some hValue)⟩
  · rintro ⟨old, hOld, hValue⟩
    exact ⟨flatten e old, ⟨old, hOld, rfl⟩,
      by simp only [flatten, hValue, decoder_factor]⟩

/-- Definition 7's coding clause when the flattened output belongs to the factor. -/
theorem flatten_code_of_some {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair))
    (output : Completion.Carrier pair) (value : factor.Carrier)
    (h : decoder e output = some value) :
    flatten e (Completion.code pair (support, output)) =
      factorEmbed e (factor.coding.code (projection e support, value)) := by
  apply (flatten_eq_factor_iff e _ _).mpr
  rw [decoder_code, h]
  rfl

/-- The other coding clause retains the completed token; it does not project it away. -/
theorem flatten_code_of_none {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)
    (support : Finset (Completion.Carrier pair))
    (output : Completion.Carrier pair)
    (h : decoder e output = none) :
    flatten e (Completion.code pair (support, output)) =
      Completion.code pair (support, output) := by
  simp only [flatten, decoder_code, h, Option.map_none]

end Mettapedia.GSLT.GraphTheory.PartialPair.FactorFlattening
