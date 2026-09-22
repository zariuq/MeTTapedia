import Mettapedia.GSLT.GraphTheory.PartialPair
import Mathlib.Data.Finset.Option

/-!
# Primitive factor embeddings of partial pairs

The source disjoint union isolates a factor's full finite inputs and outputs.
These original-carrier coding laws suffice for the canonical completion's
factor comparison. No interpreter, closure preservation, or theory-inclusion
result is an assumption of this interface.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair

open Mettapedia.GSLT.Core

structure FactorEmbedding (pair : PartialPair) (factor : GraphModel) where
  embedding : factor.Carrier ↪ pair.Carrier
  code_eq_factor_iff (support : Finset pair.Carrier) (output : pair.Carrier)
      (token : factor.Carrier) :
    pair.coding.code (support, output) = some (embedding token) ↔
      ∃ (factorSupport : Finset factor.Carrier) (factorOutput : factor.Carrier),
        factor.code factorSupport factorOutput = token ∧
        support = factorSupport.map embedding ∧ output = embedding factorOutput
  output_isolation (support : Finset pair.Carrier) (output token : pair.Carrier)
      (hCode : pair.coding.code (support, output) = some token)
      (hOutput : output ∈ Set.range embedding) : token ∈ Set.range embedding

namespace FactorEmbedding

variable {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)

/-- The optional inverse is derived from the actual injective embedding. -/
noncomputable def selector (token : pair.Carrier) : Option factor.Carrier := by
  classical
  exact if h : ∃ value, e.embedding value = token then some (Classical.choose h) else none

theorem selector_some_iff (token : pair.Carrier) (value : factor.Carrier) :
    e.selector token = some value ↔ token = e.embedding value := by
  classical
  unfold selector
  split
  · rename_i h
    constructor
    · intro hValue
      have hChosen := Option.some.inj hValue
      exact (Classical.choose_spec h).symm.trans (congrArg e.embedding hChosen)
    · intro hValue
      exact congrArg some (e.embedding.injective ((Classical.choose_spec h).trans hValue))
  · rename_i h
    constructor
    · intro hValue; cases hValue
    · intro hValue; exact False.elim (h ⟨value, hValue.symm⟩)

theorem selector_embedding (value : factor.Carrier) :
    e.selector (e.embedding value) = some value :=
  (e.selector_some_iff _ _).mpr rfl

theorem selector_none_iff (token : pair.Carrier) :
    e.selector token = none ↔ token ∉ Set.range e.embedding := by
  constructor
  · intro hNone ⟨value, hValue⟩
    have hSome := (e.selector_some_iff token value).mpr hValue.symm
    have hBad := hNone.symm.trans hSome
    cases hBad
  · intro hOutside
    cases h : e.selector token with
    | none => rfl
    | some value => exact False.elim (hOutside ⟨value, ((e.selector_some_iff _ _).mp h).symm⟩)

noncomputable def projection (support : Finset pair.Carrier) : Finset factor.Carrier :=
  Finset.eraseNone (support.image e.selector)

theorem mem_projection_iff (support : Finset pair.Carrier) (value : factor.Carrier) :
    value ∈ e.projection support ↔ e.embedding value ∈ support := by
  simp only [projection, Finset.mem_eraseNone, Finset.mem_image, selector_some_iff]
  exact ⟨fun ⟨old, hOld, hValue⟩ => hValue ▸ hOld,
    fun hValue => ⟨e.embedding value, hValue, rfl⟩⟩

theorem projection_embedding (support : Finset factor.Carrier) :
    e.projection (support.map e.embedding) = support := by
  ext value
  exact (e.mem_projection_iff _ _).trans (Finset.mem_map' e.embedding)

theorem code_preserves_factor (support : Finset factor.Carrier) (output : factor.Carrier) :
    pair.coding.code (support.map e.embedding, e.embedding output) =
      some (e.embedding (factor.code support output)) :=
  (e.code_eq_factor_iff _ _ _).mpr ⟨support, output, rfl, rfl, rfl⟩

/-- Original defined coding obeys the factor-decoding equation. -/
theorem selector_code (support : Finset pair.Carrier) (output token : pair.Carrier)
    (hCode : pair.coding.code (support, output) = some token) :
    e.selector token = (e.selector output).map
      (fun value => factor.coding.code (e.projection support, value)) := by
  cases hOutput : e.selector output with
  | none =>
      cases hToken : e.selector token with
      | none => rfl
      | some value =>
          have hTokenEq := (e.selector_some_iff token value).mp hToken
          have hFactorCode := hCode.trans (congrArg some hTokenEq)
          obtain ⟨a, x, _, _, hOut⟩ := (e.code_eq_factor_iff _ _ _).mp hFactorCode
          exact False.elim (((e.selector_none_iff output).mp hOutput) ⟨x, hOut.symm⟩)
  | some value =>
      have hOut := (e.selector_some_iff output value).mp hOutput
      obtain ⟨factorToken, hToken⟩ :=
        e.output_isolation support output token hCode ⟨value, hOut.symm⟩
      obtain ⟨a, x, hFactorCode, hSupport, hOutputEq⟩ :=
        (e.code_eq_factor_iff support output factorToken).mp
          (hCode.trans (congrArg some hToken.symm))
      have hX : x = value := e.embedding.injective (hOutputEq.symm.trans hOut)
      subst x
      have hProjection : e.projection support = a :=
        (congrArg e.projection hSupport).trans (e.projection_embedding a)
      have hSelect := e.selector_embedding factorToken
      rw [hToken] at hSelect
      change e.selector token = some (factor.code (e.projection support) value)
      exact hSelect.trans (congrArg some
        (hFactorCode.symm.trans (congrArg (fun support => factor.code support value)
          hProjection.symm)))

/-- Concrete source factor selection: the left factor of the disjoint union. -/
def left (D₁ D₂ : GraphModel) : FactorEmbedding (disjointUnion D₁ D₂) D₁ where
  embedding := Function.Embedding.inl
  code_eq_factor_iff support output token := by
    constructor
    · intro h
      cases output with
      | inr x =>
          have hBad := (disjointUnionCode_inr_some_iff D₁ D₂ support x (Sum.inl token)).mp h
          cases hBad.2
      | inl x =>
          obtain ⟨hTwoSort, hCode⟩ :=
            (disjointUnionCode_inl_some_iff D₁ D₂ support x (Sum.inl token)).mp h
          exact ⟨projectLeft support, x, Sum.inl.inj hCode, hTwoSort, rfl⟩
    · rintro ⟨a, x, rfl, rfl, rfl⟩
      exact disjointUnionCode_left D₁ D₂ a x
  output_isolation support output token hCode hOutput := by
    obtain ⟨x, rfl⟩ := hOutput
    obtain ⟨_, hToken⟩ := (disjointUnionCode_inl_some_iff D₁ D₂ support x token).mp hCode
    exact ⟨D₁.coding.code (projectLeft support, x), hToken⟩

/-- The right factor discharges the same primitive laws, not another interpreter. -/
def right (D₁ D₂ : GraphModel) : FactorEmbedding (disjointUnion D₁ D₂) D₂ where
  embedding := Function.Embedding.inr
  code_eq_factor_iff support output token := by
    constructor
    · intro h
      cases output with
      | inl x =>
          have hBad := (disjointUnionCode_inl_some_iff D₁ D₂ support x (Sum.inr token)).mp h
          cases hBad.2
      | inr x =>
          obtain ⟨hTwoSort, hCode⟩ :=
            (disjointUnionCode_inr_some_iff D₁ D₂ support x (Sum.inr token)).mp h
          exact ⟨projectRight support, x, Sum.inr.inj hCode, hTwoSort, rfl⟩
    · rintro ⟨a, x, rfl, rfl, rfl⟩
      exact disjointUnionCode_right D₁ D₂ a x
  output_isolation support output token hCode hOutput := by
    obtain ⟨x, rfl⟩ := hOutput
    obtain ⟨_, hToken⟩ := (disjointUnionCode_inr_some_iff D₁ D₂ support x token).mp hCode
    exact ⟨D₂.coding.code (projectRight support, x), hToken⟩

end FactorEmbedding
end Mettapedia.GSLT.GraphTheory.PartialPair
