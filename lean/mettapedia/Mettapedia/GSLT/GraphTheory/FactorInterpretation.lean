import Mettapedia.GSLT.GraphTheory.FactorFlattening
import Mettapedia.GSLT.GraphTheory.CompletionCodeReflection
import Mettapedia.GSLT.GraphTheory.Interpretation

/-!
# Source factor comparison for the actual graph interpreter

Full-input coding reflection and flattening-closed environments are the
semantic hypotheses used in Bucciarelli–Salibra §3.1. The comparison below
uses the existing powerset interpreter and actual canonical completion;
flattening is neither an injective encoding nor an assumed interpretation
transport.
-/

namespace Mettapedia.GSLT.GraphTheory.PartialPair.FactorInterpretation

open Mettapedia.GSLT.Core FactorFlattening CompletionCodeReflection

variable {pair : PartialPair} {factor : GraphModel} (e : FactorEmbedding pair factor)

local notation "E" => Completion.graphModel pair
local notation "ι" => (factorEmbed e : GraphModel.Carrier factor ↪
  GraphModel.Carrier (Completion.graphModel pair))
local notation "f" => (flatten e :
  GraphModel.Carrier (Completion.graphModel pair) →
    GraphModel.Carrier (Completion.graphModel pair))

noncomputable local instance :
    DecidableEq (Completion.Carrier pair) := Classical.decEq _

/-- Preservation of pure factor coding in the actual completed model. -/
theorem code_factor (support : Finset factor.Carrier) (output : factor.Carrier) :
    (E).code (support.map ι) (ι output) = ι (factor.code support output) := by
  have h := Completion.code_preserves_original pair
    (support.map e.embedding) (e.embedding output)
    (e.embedding (factor.code support output))
    (e.code_preserves_factor support output)
  have hSupport : (support.map e.embedding).map
      (Completion.embed pair 0) = support.map ι := Finset.map_map _ _ _
  exact (congrArg (fun a : Finset (E).Carrier =>
    Completion.code pair (a, ι output)) hSupport).symm.trans h

/-- Landing in the factor reflects the entire input, not merely its output. -/
theorem code_eq_factor_iff (support : Finset (E).Carrier) (output : (E).Carrier)
    (token : factor.Carrier) :
    (E).code support output = ι token ↔
      ∃ (factorSupport : Finset factor.Carrier) (factorOutput : factor.Carrier),
        factor.code factorSupport factorOutput = token ∧
        support = factorSupport.map ι ∧ output = ι factorOutput := by
  constructor
  · intro h
    obtain ⟨a, x, hOriginal, hSupport, hOutput⟩ :=
      (code_eq_original_iff pair support output (e.embedding token)).mp h
    obtain ⟨b, y, hCode, hTwoSort, hOut⟩ := (e.code_eq_factor_iff a x token).mp hOriginal
    refine ⟨b, y, hCode, ?_, ?_⟩
    · exact hSupport.trans ((congrArg (Finset.map (Completion.embed pair 0))
        hTwoSort).trans (Finset.map_map _ _ _))
    · exact hOutput.trans (congrArg (Completion.embed pair 0) hOut)
  · rintro ⟨a, x, rfl, rfl, rfl⟩
    exact code_factor e a x

/-- Source Definition 9, expressed as closure under the actual flattening. -/
def Closed (values : Set (E).Carrier) : Prop := ∀ token ∈ values, f token ∈ values

def ClosedEnv (ρ : Env E) : Prop := ∀ n, Closed e (ρ n)

/-- Factor-valued restriction of an environment, using the actual factor embedding. -/
def factorEnv (ρ : Env E) : Env factor := fun n => ι ⁻¹' ρ n

def liftEnv (ρ : Env factor) : Env E := fun n => ι '' ρ n

/-- A finite input closed under flattening, as in source Lemma 10. -/
noncomputable def supportClosure (support : Finset (E).Carrier) : Finset (E).Carrier :=
  support ∪ support.image f

theorem closed_supportClosure (support : Finset (E).Carrier) :
    Closed e (↑(supportClosure e support) : Set (E).Carrier) := by
  intro token hToken
  rcases Finset.mem_union.mp hToken with hOld | hImage
  · exact Finset.mem_union.mpr (Or.inr (Finset.mem_image_of_mem f hOld))
  · obtain ⟨old, hOld, rfl⟩ := Finset.mem_image.mp hImage
    exact Finset.mem_union.mpr (Or.inr
      ((flatten_idempotent e old).symm ▸ Finset.mem_image_of_mem f hOld))

theorem closed_pure_support (support : Finset factor.Carrier) :
    Closed e
      (↑(support.map ι) : Set (Completion.Carrier pair)) := by
  intro token hToken
  obtain ⟨value, hValue, rfl⟩ := Finset.mem_map.mp hToken
  exact (flatten_factor e value).symm ▸ Finset.mem_map_of_mem ι hValue

theorem closedEnv_extend (ρ : Env E) (values : Set (E).Carrier)
    (hρ : ClosedEnv e ρ) (hValues : Closed e values) :
    ClosedEnv e (ρ.extend values) := by
  intro n
  cases n with
  | zero => exact hValues
  | succ n => exact hρ n

theorem factorEnv_extend_closure (ρ : Env E) (support : Finset (E).Carrier) :
    factorEnv e (ρ.extend (↑(supportClosure e support) : Set (E).Carrier)) =
      (factorEnv e ρ).extend (↑(projection e support) : Set factor.Carrier) := by
  funext n
  cases n with
  | zero =>
      ext value
      exact mem_closed_support_factor_iff e support value
  | succ n => rfl

theorem factorEnv_extend_pure (ρ : Env E) (support : Finset factor.Carrier) :
    factorEnv e (ρ.extend
      (↑(support.map ι) : Set (Completion.Carrier pair))) =
      (factorEnv e ρ).extend (↑support : Set factor.Carrier) := by
  funext n
  cases n with
  | zero => ext value; exact Finset.mem_map' ι
  | succ n => rfl

theorem closedEnv_lift (ρ : Env factor) : ClosedEnv e (liftEnv e ρ) := by
  intro n token hToken
  obtain ⟨value, hValue, rfl⟩ := hToken
  exact ⟨value, hValue, (flatten_factor e value).symm⟩

theorem factorEnv_lift (ρ : Env factor) : factorEnv e (liftEnv e ρ) = ρ := by
  funext n
  exact Set.preimage_image_eq _ (ι).injective

/-- Finite factor witnesses extracted from a support remain in every closed superset. -/
theorem mapped_projection_subset (support : Finset (E).Carrier) (values : Set (E).Carrier)
    (hValues : Closed e values) (hSupport : (↑support : Set (E).Carrier) ⊆ values) :
    (↑((projection e support).map ι) :
      Set (Completion.Carrier pair)) ⊆ values := by
  intro token hToken
  obtain ⟨value, hValue, rfl⟩ := Finset.mem_map.mp hToken
  obtain ⟨old, hOld, hDecoder⟩ := (mem_projection_iff e support value).mp hValue
  exact ((flatten_eq_factor_iff e old value).mpr hDecoder) ▸ hValues old (hSupport hOld)

/-- Simultaneous source closure and exact factor comparison, for arbitrary terms
and genuinely flattening-closed environments of the actual completed model. -/
theorem interpret_closed_factor (term : LambdaTerm) :
    ∀ (ρ : Env E), ClosedEnv e ρ →
      Closed e (interpret E ρ term) ∧
        ∀ value : factor.Carrier, ι value ∈ interpret E ρ term ↔
          value ∈ interpret factor (factorEnv e ρ) term := by
  induction term with
  | var n =>
      intro ρ hρ
      exact ⟨hρ n, fun _ => Iff.rfl⟩
  | lam body ih =>
      intro ρ hρ
      have hTwoSort (a : Finset factor.Carrier) :
          ClosedEnv e (ρ.extend
            (↑(a.map ι) : Set (Completion.Carrier pair))) :=
        closedEnv_extend e ρ _ hρ (closed_pure_support e a)
      constructor
      · rintro token ⟨a, z, rfl, hz⟩
        cases hDecoder : decoder e z with
        | none =>
            exact (flatten_code_of_none e a z hDecoder).symm ▸ ⟨a, z, rfl, hz⟩
        | some value =>
            have hLarge := ih (ρ.extend (↑(supportClosure e a) : Set (E).Carrier))
              (closedEnv_extend e ρ _ hρ (closed_supportClosure e a))
            have hzLarge : z ∈ interpret E
                (ρ.extend (↑(supportClosure e a) : Set (E).Carrier)) body :=
              interpret_mono E body (fun n => by
                cases n with
                | zero =>
                    intro x hx
                    exact Finset.mem_union.mpr (Or.inl hx)
                | succ n => exact Set.Subset.rfl) hz
            have hValueLarge := ((flatten_eq_factor_iff e z value).mpr hDecoder) ▸
              hLarge.1 z hzLarge
            have hFactor := (hLarge.2 value).mp hValueLarge
            rw [factorEnv_extend_closure] at hFactor
            have hSmall := (ih
              (ρ.extend (↑((projection e a).map ι) :
                Set (Completion.Carrier pair)))
              (hTwoSort (projection e a))).2 value
            rw [factorEnv_extend_pure] at hSmall
            have hCodeSmall : (E).code ((projection e a).map ι) (ι value) ∈
                interpret E ρ (.lam body) :=
              ⟨(projection e a).map ι, ι value, rfl, hSmall.mpr hFactor⟩
            have hFlatCode : f ((E).code a z) =
                (E).code ((projection e a).map ι) (ι value) :=
              (flatten_code_of_some e a z value hDecoder).trans
                (code_factor e (projection e a) value).symm
            exact hFlatCode.symm ▸ hCodeSmall
      · intro value
        constructor
        · rintro ⟨a, z, hCode, hz⟩
          obtain ⟨b, x, hFactorCode, rfl, rfl⟩ :=
            (code_eq_factor_iff e a z value).mp hCode.symm
          have hBody := (ih (ρ.extend (↑(b.map ι) :
            Set (Completion.Carrier pair))) (hTwoSort b)).2 x
          rw [factorEnv_extend_pure] at hBody
          exact ⟨b, x, hFactorCode.symm, hBody.mp hz⟩
        · rintro ⟨b, x, hCode, hx⟩
          have hBody := (ih (ρ.extend (↑(b.map ι) :
            Set (Completion.Carrier pair))) (hTwoSort b)).2 x
          rw [factorEnv_extend_pure] at hBody
          refine ⟨b.map ι, ι x, ?_, hBody.mpr hx⟩
          exact (congrArg ι hCode).trans (code_factor e b x).symm
  | app fn arg ihFn ihArg =>
      intro ρ hρ
      have hFn := ihFn ρ hρ
      have hArg := ihArg ρ hρ
      constructor
      · rintro z ⟨a, ha, hCode⟩
        cases hDecoder : decoder e z with
        | none =>
            exact (show f z = z by simp only [flatten, hDecoder]; rfl).symm ▸ ⟨a, ha, hCode⟩
        | some value =>
            have hFlatCode : f ((E).code a z) =
                (E).code ((projection e a).map ι) (ι value) :=
              (flatten_code_of_some e a z value hDecoder).trans
                (code_factor e (projection e a) value).symm
            have hCodeSmall := hFlatCode ▸ hFn.1 ((E).code a z) hCode
            have hSmall : ι value ∈ interpret E ρ (.app fn arg) :=
              ⟨(projection e a).map ι,
                mapped_projection_subset e a _ hArg.1 ha, hCodeSmall⟩
            exact ((flatten_eq_factor_iff e z value).mpr hDecoder).symm ▸ hSmall
      · intro value
        constructor
        · rintro ⟨a, ha, hCode⟩
          have hFlatCode : f ((E).code a (ι value)) =
              ι (factor.code (projection e a) value) :=
            flatten_code_of_some e a (ι value) value (decoder_factor e value)
          have hFactorCode := (hFn.2 (factor.code (projection e a) value)).mp
            (hFlatCode ▸ hFn.1 ((E).code a (ι value)) hCode)
          refine ⟨projection e a, ?_, hFactorCode⟩
          intro x hx
          apply (hArg.2 x).mp
          exact mapped_projection_subset e a _ hArg.1 ha
            (Finset.mem_map_of_mem ι hx)
        · rintro ⟨b, hb, hCode⟩
          refine ⟨b.map ι, ?_, ?_⟩
          · intro x hx
            obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
            exact (hArg.2 y).mpr (hb hy)
          · exact (code_factor e b value).symm ▸
              (hFn.2 (factor.code b value)).mpr hCode

/-- Source Proposition 12(a), for the selected factor of the actual canonical completion. -/
theorem interpret_closed (term : LambdaTerm) (ρ : Env E) (hρ : ClosedEnv e ρ) :
    Closed e (interpret E ρ term) :=
  (interpret_closed_factor e term ρ hρ).1

def restrictEnv (ρ : Env E) : Env E := fun n => ρ n ∩ Set.range ι

theorem closedEnv_restrict (ρ : Env E) : ClosedEnv e (restrictEnv e ρ) := by
  intro n token hToken
  obtain ⟨hMember, value, rfl⟩ := hToken
  exact (flatten_factor e value).symm ▸ ⟨hMember, ⟨value, rfl⟩⟩

theorem factorEnv_restrict (ρ : Env E) :
    factorEnv e (restrictEnv e ρ) = factorEnv e ρ := by
  funext n
  ext value
  exact ⟨fun h => h.1, fun h => ⟨h, ⟨value, rfl⟩⟩⟩

/-- Source Proposition 12(b): factor outputs persist under genuine factor restriction. -/
theorem interpret_restrict_subset (term : LambdaTerm) (ρ : Env E)
    (hρ : ClosedEnv e ρ) :
    interpret E ρ term ∩ Set.range ι ⊆ interpret E (restrictEnv e ρ) term := by
  rintro token ⟨hTerm, value, rfl⟩
  have hFactor := ((interpret_closed_factor e term ρ hρ).2 value).mp hTerm
  have hRestricted := (interpret_closed_factor e term (restrictEnv e ρ)
    (closedEnv_restrict e ρ)).2 value
  rw [factorEnv_restrict] at hRestricted
  exact hRestricted.mpr hFactor

/-- Source Proposition 13: actual factor-valued environments have exact interpreter comparison. -/
theorem interpret_lift_factor (term : LambdaTerm) (ρ : Env factor) :
    ι ⁻¹' interpret E (liftEnv e ρ) term = interpret factor ρ term := by
  ext value
  have h := (interpret_closed_factor e term (liftEnv e ρ)
    (closedEnv_lift e ρ)).2 value
  rw [factorEnv_lift] at h
  exact h

include e in
/-- Source Theorem 14's inclusion for any original factor satisfying the primitive coding laws.
This concerns all environments of the existing induced lambda theories. -/
theorem theory_subset_factor : theoryOf E ⊆ theoryOf factor := by
  intro equation hEquation ρ
  have hE := hEquation (liftEnv e ρ)
  calc
    interpret factor ρ equation.lhs = ι ⁻¹' interpret E (liftEnv e ρ) equation.lhs :=
      (interpret_lift_factor e equation.lhs ρ).symm
    _ = ι ⁻¹' interpret E (liftEnv e ρ) equation.rhs := congrArg (Set.preimage ι) hE
    _ = interpret factor ρ equation.rhs := interpret_lift_factor e equation.rhs ρ

/-- Both actual disjoint-union factors contain the induced theory of their canonical completion.
This is a lower bound, not an equality with the intersection. -/
theorem disjointUnion_theory_lower_bound (D₁ D₂ : GraphModel) :
    lambdaTheoryOf (Completion.graphModel (disjointUnion D₁ D₂)) ≤ lambdaTheoryOf D₁ ∧
      lambdaTheoryOf (Completion.graphModel (disjointUnion D₁ D₂)) ≤ lambdaTheoryOf D₂ := by
  exact ⟨theory_subset_factor (FactorEmbedding.left D₁ D₂),
    theory_subset_factor (FactorEmbedding.right D₁ D₂)⟩

end Mettapedia.GSLT.GraphTheory.PartialPair.FactorInterpretation

namespace Mettapedia.GSLT.GraphTheory

open Mettapedia.GSLT.Core PartialPair

/-- Two graph theories have a graph-theory lower bound, witnessed by the
actual canonical completion of the disjoint union of their model witnesses.
Containment need not be equality with the intersection. -/
theorem graphTheory_inter (T₁ T₂ : LambdaTheory)
    (h₁ : IsGraphTheory T₁) (h₂ : IsGraphTheory T₂) :
    ∃ T : LambdaTheory, IsGraphTheory T ∧ T.equations ⊆ T₁.equations ∩ T₂.equations := by
  obtain ⟨D₁, h₁⟩ := h₁
  obtain ⟨D₂, h₂⟩ := h₂
  refine ⟨lambdaTheoryOf (Completion.graphModel (disjointUnion D₁ D₂)),
    lambdaTheoryOf_isGraphTheory _, ?_⟩
  have hBoth := FactorInterpretation.disjointUnion_theory_lower_bound D₁ D₂
  intro equation hEquation
  constructor
  · rw [h₁]
    exact hBoth.1 hEquation
  · rw [h₂]
    exact hBoth.2 hEquation

end Mettapedia.GSLT.GraphTheory
