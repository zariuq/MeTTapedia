import Mettapedia.Logic.PLNWorldModelInstitution
import Mettapedia.Logic.PLNWorldModelHyperdoctrine

/-!
# WM Categorical Bridge Endpoint

This module connects:

- institution-style satisfaction transport (`PLNWorldModelInstitution`), and
- hyperdoctrine-style Beck-Chevalley transport (`PLNWorldModelHyperdoctrine`)

in one explicit endpoint theorem.
-/

namespace Mettapedia.Logic.PLNWorldModelCategoricalBridge

open CategoryTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelInstitution
open Mettapedia.Logic.PLNWorldModelHyperdoctrine
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale

universe u v w x

variable {State : Type x} [EvidenceType State]

namespace WMHyperdoctrine

variable (H : WMHyperdoctrine State)

/-- One-sort WM signature wrapper around queries at object `X`. -/
def singletonSig (X : H.Obj) : WMSignature where
  Srt := PUnit
  Query := fun _ => H.query X

/-- Singleton-signature morphism induced by query reindexing along `f`. -/
def singletonReindexSigMorphism {X Y : H.Obj} (f : X ⟶ Y) :
    WMSigMorphism (singletonSig (H := H) Y) (singletonSig (H := H) X) where
  mapSort := fun _ => PUnit.unit
  mapQuery := by
    intro _ q
    exact H.reindexQuery f q

/-- WM semantics on singleton signatures, induced from `H.worldModel`. -/
def singletonWorldModelSigma (X : H.Obj) :
    WorldModelSigma State PUnit (fun _ => H.query X) where
  evidence := fun W q =>
    letI : WorldModelSigma State H.Obj H.query := H.worldModel
    WorldModelSigma.evidenceAt (State := State) (Srt := H.Obj) (Query := H.query) W q.2
  evidence_add := by
    intro W₁ W₂ q
    letI : WorldModelSigma State H.Obj H.query := H.worldModel
    simpa [WorldModelSigma.evidenceAt] using
      (WorldModelSigma.evidenceAt_add
        (State := State) (Srt := H.Obj) (Query := H.query) W₁ W₂ q.2)

/-- Categorical endpoint surface combining institution transport and
Beck-Chevalley transport. -/
abbrev EndpointStatement
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (W : State) (φ : H.query B) : Prop :=
  (letI : WorldModelSigma State
    (singletonSig (H := H) A).Srt (singletonSig (H := H) A).Query :=
      singletonWorldModelSigma (H := H) A
   letI : WorldModelSigma State
    (singletonSig (H := H) D).Srt (singletonSig (H := H) D).Query :=
      reindexWorldModelSigma
        (State := State)
        (sigma := singletonReindexSigMorphism (H := H) f)
   satEvidence (State := State) (singletonSig (H := H) D) W
     ⟨PUnit.unit, H.existsQuery g φ⟩ =
    satEvidence (State := State) (singletonSig (H := H) A) W
      (mapSentence (singletonReindexSigMorphism (H := H) f)
        ⟨PUnit.unit, H.existsQuery g φ⟩))
  ∧
  H.interpret (H.reindexQuery f (H.existsQuery g φ)) =
    H.interpret (H.existsQuery π₁ (H.reindexQuery π₂ φ))

/-- Categorical endpoint surface combining institution transport and
Beck-Chevalley transport. -/
abbrev EndpointSurface (H : WMHyperdoctrine State) : Prop :=
  ∀ {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (_hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B),
    EndpointStatement (H := H) π₁ π₂ f g W φ

/-- Unified endpoint:
institution satisfaction transport for reindexing and
hyperdoctrine Beck-Chevalley transport for `reindex ∘ exists`. -/
theorem institution_beckChevalley_endpoint
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B) :
    EndpointStatement (H := H) π₁ π₂ f g W φ := by
  constructor
  · letI : WorldModelSigma State
      (singletonSig (H := H) A).Srt (singletonSig (H := H) A).Query :=
        singletonWorldModelSigma (H := H) A
    simpa using
      (satisfactionCondition_evidence
        (State := State)
        (sig1 := singletonSig (H := H) D)
        (sig2 := singletonSig (H := H) A)
        (sigma := singletonReindexSigMorphism (H := H) f)
        W
        ⟨PUnit.unit, H.existsQuery g φ⟩)
  · simpa using H.beckChevalley_transport_exists π₁ π₂ f g hpb φ

/-- The new categorical endpoint surface is derivable directly from the unified
endpoint theorem. -/
theorem endpointSurface_of_hyperdoctrine
    (H : WMHyperdoctrine State) :
    EndpointSurface (H := H) :=
  institution_beckChevalley_endpoint (H := H)

end WMHyperdoctrine

end Mettapedia.Logic.PLNWorldModelCategoricalBridge
