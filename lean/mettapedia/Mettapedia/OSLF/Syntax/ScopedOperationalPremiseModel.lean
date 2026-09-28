import Mettapedia.OSLF.Syntax.CategoricalScopedEventPremise
import Mettapedia.OSLF.Syntax.ScopedOperationalEvidenceExponential
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Actual operational models as scoped premise requests

The target-independent pullback interface for a binder-local firing is
instantiated by every substitution-operational model. Its event object is
the model's individual-evidence presheaf; its endpoint object is the pair
of state presheaves. The full-endpoint request recovers precisely the
existing scoped-evidence function object, which is naturally equivalent to
evidence under the extended context.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.CategoricalScopedEventPremise
open Mettapedia.OSLF.Binding.MultiBinderPresheaf

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Pair the source and target of each individual firing without taking an
image or identifying events with equal endpoints. -/
noncomputable def modelEndpointPair (Y : SubstitutionModel R A) :
    modelEvents R Y ⟶ states A ⨯ states A :=
  prod.lift (modelSource R Y) (modelTarget R Y)

/-- One model's complete scoped event carrier, seen as a request whose
parameter is the requested endpoint function. -/
noncomputable def modelRequest (scope : Ctx S)
    (Y : SubstitutionModel R A) :
    Request (binders A scope)
      ((ihom (binders A scope)).obj (states A ⨯ states A))
      (modelEvents R Y) (states A ⨯ states A) :=
  allEndpointsRequest (modelEndpointPair R Y)

/-- The general pullback object of a scoped premise specializes to the
actual retained event presheaf under its ordered binder extension. -/
noncomputable def modelWitnessIso (scope : Ctx S)
    (Y : SubstitutionModel R A) :
    Witness (modelRequest R scope Y) ≅
      scopedEvidence A scope (modelEvents R Y) :=
  allEndpointsWitnessIso (B := binders A scope) (modelEndpointPair R Y) ≪≫
    scopedEvidenceIso A scope (modelEvents R Y)

/-- Every genuine operational-model map preserves the paired endpoints of
each individual firing. This is the square required to map premise objects. -/
theorem modelEndpointPair_map {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    mapModelEvents R h ≫ modelEndpointPair R Z =
      modelEndpointPair R Y := by
  apply prod.hom_ext
  · have hs := (mapModelGraph R h).source_comm
    change mapModelEvents R h ≫ modelSource R Z = modelSource R Y at hs
    simpa only [modelEndpointPair, Category.assoc, prod.lift_fst] using hs
  · have ht := (mapModelGraph R h).target_comm
    change mapModelEvents R h ≫ modelTarget R Z = modelTarget R Y at ht
    simpa only [modelEndpointPair, Category.assoc, prod.lift_snd] using ht

/-- Any ordinary model map induces a map of complete scoped requests; no
event-surjectivity or endpoint reflection is assumed. -/
noncomputable def modelRequestMap (scope : Ctx S)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    Map (modelRequest R scope Y) (modelRequest R scope Z) where
  parameter := 𝟙 _
  event := mapModelEvents R h
  endpoint := 𝟙 _
  endpoint_comm := by
    change mapModelEvents R h ≫ modelEndpointPair R Z =
      modelEndpointPair R Y ≫ 𝟙 _
    simpa only [Category.comp_id] using modelEndpointPair_map R h
  required_comm := by simp [modelRequest, allEndpointsRequest]

/-- The generic pullback map agrees with the already established map of
actual evidence under a binder context. This square transports the complete
firing value, including its ordered premise tree. -/
theorem modelWitnessIso_map (scope : Ctx S)
    {Y Z : SubstitutionModel R A}
    (h : SubstitutionModel.Hom R Y Z) :
    mapWitness (modelRequest R scope Y) (modelRequestMap R scope h) ≫
      (modelWitnessIso R scope Z).hom =
    (modelWitnessIso R scope Y).hom ≫
      (scopedEvidenceFunctor A scope).map (mapModelEvents R h) := by
  have natural := (scopedEvidenceFunctorIso A scope).hom.naturality
    (mapModelEvents R h)
  let isoY : (FunctorToTypes.rightAdj (binders A scope)).obj
      (modelEvents R Y) ≅ scopedEvidence A scope (modelEvents R Y) :=
    scopedEvidenceIso A scope (modelEvents R Y)
  let isoZ : (FunctorToTypes.rightAdj (binders A scope)).obj
      (modelEvents R Z) ≅ scopedEvidence A scope (modelEvents R Z) :=
    scopedEvidenceIso A scope (modelEvents R Z)
  change (FunctorToTypes.rightAdj (binders A scope)).map
      (mapModelEvents R h) ≫
      isoZ.hom =
    isoY.hom ≫
      (scopedEvidenceFunctor A scope).map (mapModelEvents R h) at natural
  let eventY : Witness (modelRequest R scope Y) ⟶
      (FunctorToTypes.rightAdj (binders A scope)).obj (modelEvents R Y) :=
    event (modelRequest R scope Y)
  let eventZ : Witness (modelRequest R scope Z) ⟶
      (FunctorToTypes.rightAdj (binders A scope)).obj (modelEvents R Z) :=
    event (modelRequest R scope Z)
  have eventSquare :
      mapWitness (modelRequest R scope Y) (modelRequestMap R scope h) ≫
        eventZ =
      eventY ≫
        (FunctorToTypes.rightAdj (binders A scope)).map
          (mapModelEvents R h) := by
    exact mapWitness_event _ _
  change (mapWitness (modelRequest R scope Y) (modelRequestMap R scope h) ≫
      eventZ) ≫
      isoZ.hom =
    (eventY ≫
      isoY.hom) ≫
      (scopedEvidenceFunctor A scope).map (mapModelEvents R h)
  rw [eventSquare]
  simp only [Category.assoc, natural]
  exact (Category.assoc _ _ _).symm

/-- The retained evidence presheaf varies functorially with ordinary
substitution-operational model maps. -/
noncomputable def modelEventsFunctor
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    SubstitutionModel R A ⥤ (Base A ⥤ Type u) where
  obj Y := modelEvents R Y
  map h := mapModelEvents R h
  map_id Y := by
    ext X event
    rfl
  map_comp f g := by
    ext X event
    rfl

/-- Each operational model yields a package of independently specified
parameters, events and endpoints for a binder-local premise. -/
noncomputable def modelPackageFunctor (scope : Ctx S) :
    SubstitutionModel R A ⥤
      Package (binders A scope) where
  obj Y := ⟨_, _, _, modelRequest R scope Y⟩
  map h := modelRequestMap R scope h
  map_id Y := by
    apply Map.ext
    · rfl
    · ext X event
      rfl
    · rfl
  map_comp f g := by
    apply Map.ext
    · rfl
    · ext X event
      rfl
    · rfl

/-- The target-side pullback construction and the actual binder-extended
event presheaf are naturally the same across all lawful model maps. -/
noncomputable def modelWitnessNaturalIso (scope : Ctx S) :
    modelPackageFunctor R scope ⋙ witnessFunctor (binders A scope) ≅
      modelEventsFunctor R A ⋙ scopedEvidenceFunctor A scope := by
  refine NatIso.ofComponents (fun Y => modelWitnessIso R scope Y) ?_
  intro Y Z h
  exact modelWitnessIso_map R scope h

end Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel

#print axioms Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel.modelWitnessIso
#print axioms Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel.modelRequestMap
#print axioms Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel.modelWitnessIso_map
#print axioms Mettapedia.OSLF.Binding.ScopedOperationalPremiseModel.modelWitnessNaturalIso
