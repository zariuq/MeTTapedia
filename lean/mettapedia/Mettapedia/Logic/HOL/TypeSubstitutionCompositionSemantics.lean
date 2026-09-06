import Mettapedia.Logic.HOL.TypeSubstitutionSemantics
import Mettapedia.Logic.HOL.Syntax.TypeSubstitutionComposition
import Mettapedia.Logic.HOL.TypeSubstitutionDerivation

/-!
# Satisfaction coherence for successive type interpretations

The standard-domain reduct depends on the target's carriers and constants,
but not on its admissibility predicate.  Consequently its composition law
holds on sentences even when the original target model is not full: both
routes use the same standardization.  Full domains suffice for the identity
satisfaction law against the original model; no converse is asserted.

These are satisfaction laws and carrier equivalences, not a new category of
Henkin models or a claim of model expansion along every type interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v v' v'' w

variable {Base Base' Base'' : Type u}
  {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}
  {Const'' : Ty Base'' → Type v''}

namespace HenkinModel

/-- A standard-domain reduct ignores the original target admissibility data. -/
theorem standardTypeReduct_standard
    (σ : Base → Ty Base')
    (constants : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (M : HenkinModel.{u, v', w} Base' Const') :
    standardTypeReduct σ constants (standard M.Carrier M.constDen) =
      standardTypeReduct σ constants M := rfl

/-- Under the identity type interpretation, the source agrees with the
standardization of the original model on all sentences. -/
theorem standardTypeReduct_id_standard_models
    (M : HenkinModel.{u, v, w} Base Const) (φ : ClosedFormula Const) :
    (standardTypeReduct (Const' := Const) Ty.base
        (fun {a} c => (Ty.substitute_id a).symm ▸ c) M).models φ ↔
      (standard M.Carrier M.constDen).models φ := by
  rw [← standardTypeReduct_standard]
  simpa only [mapTypes_id_closed] using
    models_mapTypes (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c)
      (standard M.Carrier M.constDen) (fullDomains_standard _ _) φ

/-- Full domains make the identity interpretation truth-preserving against
the original model, not merely against its standardization. -/
theorem standardTypeReduct_id_models
    (M : HenkinModel.{u, v, w} Base Const) (full : M.FullDomains)
    (φ : ClosedFormula Const) :
    (standardTypeReduct (Const' := Const) Ty.base
        (fun {a} c => (Ty.substitute_id a).symm ▸ c) M).models φ ↔ M.models φ := by
  simpa only [mapTypes_id_closed] using
    models_mapTypes (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c) M full φ

/-- Standard-domain reduction cannot be literally the original non-full
model. This is a conditional boundary on model equality, not a claim that
every non-full model is separated by a closed sentence. -/
theorem standardTypeReduct_id_ne_of_not_fullDomains
    (M : HenkinModel.{u, v, w} Base Const) (not_full : ¬ M.FullDomains) :
    standardTypeReduct (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c) M ≠ M := by
  intro equal
  apply not_full
  rw [← equal]
  exact standardTypeReduct_fullDomains _ _ _

/-- Contravariant model reduction composes on satisfaction. No fullness
assumption on the original model is needed, since the source of either route
is a standard-domain model. -/
theorem standardTypeReduct_comp_models
    (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    (M : HenkinModel.{u, v'', w} Base'' Const'') (φ : ClosedFormula Const) :
    (standardTypeReduct σ first (standardTypeReduct τ second M)).models φ ↔
      (standardTypeReduct (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) M).models φ := by
  let fullModel : HenkinModel.{u, v'', w} Base'' Const'' :=
    standard M.Carrier M.constDen
  have full : fullModel.FullDomains := fullDomains_standard _ _
  calc
    (standardTypeReduct σ first (standardTypeReduct τ second M)).models φ ↔
        (standardTypeReduct τ second fullModel).models (mapTypes σ first φ) :=
      models_mapTypes σ first (standardTypeReduct τ second M)
        (standardTypeReduct_fullDomains _ _ _) φ
    _ ↔ fullModel.models (mapTypes τ second (mapTypes σ first φ)) :=
      models_mapTypes τ second fullModel full (mapTypes σ first φ)
    _ ↔ fullModel.models
        (mapTypes (fun b => Ty.substitute τ (σ b))
          (composeTypeConstants σ τ first second) φ) := by
      rw [mapTypes_comp_closed]
    _ ↔ (standardTypeReduct (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) M).models φ :=
      (models_mapTypes (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) fullModel full φ).symm

/-- Iterated and composite reducts have canonically equivalent base carriers. -/
def standardTypeReduct_comp_carrierEquiv
    (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    (M : HenkinModel.{u, v'', w} Base'' Const'') (b : Base) :
    (standardTypeReduct σ first (standardTypeReduct τ second M)).Carrier b ≃
      (standardTypeReduct (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) M).Carrier b :=
  Ty.denoteSubstituteEquiv τ M.Carrier (σ b)

end HenkinModel

namespace TypeSubstitutionExample

/-- A full two-element model supplies a nontrivial target function hierarchy. -/
def booleanFunctionModel : HenkinModel.{0, 0, 0} Unit (NoConstants Unit) :=
  HenkinModel.standard (fun _ => ULift.{1} Bool) (fun {_} constant => nomatch constant)

/-- Two genuine function-type substitutions preserve the quantified beta law;
the iterated and composite source models agree on that sentence. -/
theorem iterated_function_beta :
    let σ := functionInterpretation
    let τ := functionInterpretation
    let first : ∀ {a}, NoConstants Unit a → NoConstants Unit (Ty.substitute σ a) :=
      noConstantsMap σ
    let second : ∀ {a}, NoConstants Unit a → NoConstants Unit (Ty.substitute τ a) :=
      noConstantsMap τ
    let iterated := HenkinModel.standardTypeReduct σ first
      (HenkinModel.standardTypeReduct τ second booleanFunctionModel)
    let composite := HenkinModel.standardTypeReduct
      (fun b => Ty.substitute τ (σ b))
      (composeTypeConstants σ τ first second) booleanFunctionModel
    iterated.models (quantifiedBeta (.base ())) ∧
      composite.models (quantifiedBeta (.base ())) := by
  dsimp only
  have sourceProof := quantifiedBeta_provable (.base ())
  have firstHolds := Soundness.extTheorem_sound sourceProof
    (HenkinModel.standardTypeReduct functionInterpretation
      (noConstantsMap functionInterpretation)
      (HenkinModel.standardTypeReduct functionInterpretation
        (noConstantsMap functionInterpretation) booleanFunctionModel))
    (HenkinModel.functionsRespectEqv_of_fullDomains _
      (HenkinModel.standardTypeReduct_fullDomains _ _ _))
  exact ⟨firstHolds, (HenkinModel.standardTypeReduct_comp_models _ _ _ _ _ _).mp firstHolds⟩

end TypeSubstitutionExample

#print axioms HenkinModel.standardTypeReduct_id_standard_models
#print axioms HenkinModel.standardTypeReduct_id_models
#print axioms HenkinModel.standardTypeReduct_comp_models
#print axioms HenkinModel.standardTypeReduct_id_ne_of_not_fullDomains
#print axioms TypeSubstitutionExample.iterated_function_beta

end Mettapedia.Logic.HOL
