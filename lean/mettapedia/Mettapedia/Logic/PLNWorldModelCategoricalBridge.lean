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
    WMSigMorphism (H.singletonSig Y) (H.singletonSig X) where
  mapSort := fun _ => PUnit.unit
  mapQuery := by
    intro _ q
    exact H.reindexQuery f q

/-- WM semantics on singleton signatures, induced from `H.worldModel`. -/
def singletonWorldModelSigma (X : H.Obj) :
    WorldModelSigma State PUnit (fun _ => H.query X) where
  evidence := fun W q =>
    WorldModelSigma.evidenceAt (State := State) (Srt := H.Obj) (Query := H.query) W q.2
  evidence_add := by
    intro W₁ W₂ q
    simpa [WorldModelSigma.evidenceAt] using
      (WorldModelSigma.evidenceAt_add
        (State := State) (Srt := H.Obj) (Query := H.query) W₁ W₂ q.2)

/-- Unified endpoint:
institution satisfaction transport for reindexing and
hyperdoctrine Beck-Chevalley transport for `reindex ∘ exists`. -/
theorem institution_beckChevalley_endpoint
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (W : State) (φ : H.query B) :
    let sigB := H.singletonSig B
    let sigA := H.singletonSig A
    let sigma := H.singletonReindexSigMorphism f
    letI : WorldModelSigma State sigA.Srt sigA.Query :=
      H.singletonWorldModelSigma A
    letI : WorldModelSigma State sigB.Srt sigB.Query :=
      reindexWorldModelSigma (State := State) (sig1 := sigB) (sig2 := sigA) sigma
    satEvidence (State := State) sigB W ⟨PUnit.unit, H.existsQuery g φ⟩ =
      satEvidence (State := State) sigA W
        (mapSentence sigma ⟨PUnit.unit, H.existsQuery g φ⟩)
    ∧
    H.interpret (H.reindexQuery f (H.existsQuery g φ)) =
      H.interpret (H.existsQuery π₁ (H.reindexQuery π₂ φ)) := by
  constructor
  · simp [singletonSig, singletonReindexSigMorphism, satEvidence,
      satisfactionCondition_evidence, reindexWorldModelSigma, mapSentence,
      singletonWorldModelSigma, WorldModelSigma.evidenceAt]
  · simpa using H.beckChevalley_transport_exists π₁ π₂ f g hpb φ

end WMHyperdoctrine

end Mettapedia.Logic.PLNWorldModelCategoricalBridge
