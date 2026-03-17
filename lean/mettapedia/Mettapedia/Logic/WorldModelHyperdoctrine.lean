import Mettapedia.Logic.PLNWorldModel
import Mettapedia.GSLT.Topos.PredicateFibration

/-!
# WM Hyperdoctrine Layer (Typed Queries + Change-of-Base)

This module provides a conservative hyperdoctrine-style wrapper for the WM
typed query layer (`WorldModelSigma`), linked to the existing GSLT
change-of-base interface and Beck-Chevalley condition.

The design is intentionally explicit:
- typed queries indexed by base objects,
- reindexing / existential / universal query operators,
- interpretation into a predicate fibration,
- compatibility laws (query-operator ↔ change-of-base),
- Beck-Chevalley transport theorem at the query interpretation layer.
-/

namespace Mettapedia.Logic.PLNWorldModelHyperdoctrine

open CategoryTheory
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Topos
open scoped ENNReal

universe u v w x

/-- Hyperdoctrine-style WM bundle over a categorical base. -/
structure WMHyperdoctrine (State : Type x) [EvidenceType State] where
  /-- Base objects (contexts/sorts). -/
  Obj : Type u
  /-- Base category structure. -/
  instCategory : Category.{v} Obj
  /-- Predicate fibration over the base. -/
  predFib : PredicateFib Obj
  /-- Typed query family indexed by base objects. -/
  query : Obj → Type w
  /-- WM semantics over object-indexed typed queries. -/
  worldModel : WorldModelSigma State Obj query
  /-- Reindexing (pullback) on queries. -/
  reindexQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query Y → query X
  /-- Existential transport on queries. -/
  existsQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query X → query Y
  /-- Universal transport on queries. -/
  forallQuery : ∀ {X Y : Obj}, (X ⟶ Y) → query X → query Y
  /-- Interpretation of queries into fibration predicates. -/
  interpret : ∀ {X : Obj}, query X → predFib.Sub X
  /-- Concrete change-of-base structure reused from GSLT. -/
  cob : ChangeOfBase (PredicateFib.toSubobjectFibration predFib)
  /-- Beck-Chevalley law at the fibration level. -/
  beckChevalley : BeckChevalleyCondition predFib cob
  /-- Reindexing compatibility with pullback. -/
  reindex_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query Y),
      interpret (reindexQuery f φ) = cob.pullback f (interpret φ)
  /-- Existential compatibility with direct image. -/
  exists_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query X),
      interpret (existsQuery f φ) = cob.directImage f (interpret φ)
  /-- Universal compatibility with universal image. -/
  forall_interp :
    ∀ {X Y : Obj} (f : X ⟶ Y) (φ : query X),
      interpret (forallQuery f φ) = cob.universalImage f (interpret φ)

attribute [instance] WMHyperdoctrine.instCategory

namespace WMHyperdoctrine

variable {State : Type x} [EvidenceType State]
variable (H : WMHyperdoctrine State)

/-- BinaryEvidence extracted for an object-indexed query. -/
def evidenceAt (W : State) {X : H.Obj} (φ : H.query X) : BinaryEvidence := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.evidenceAt (State := State) (Srt := H.Obj) (Query := H.query) W φ

/-- Strength view for an object-indexed query. -/
noncomputable def queryStrengthAt (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryStrengthAt (State := State) (Srt := H.Obj) (Query := H.query) W φ

/-- Context-sensitive strength view for an object-indexed query. -/
noncomputable def queryStrengthWithAt
    (ctx : BinaryContext) (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryStrengthWithAt
    (State := State) (Srt := H.Obj) (Query := H.query) ctx W φ

/-- Confidence view for an object-indexed query. -/
noncomputable def queryConfidenceAt
    (κ : ℝ≥0∞) (W : State) {X : H.Obj} (φ : H.query X) : ℝ≥0∞ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  exact WorldModelSigma.queryConfidenceAt
    (State := State) (Srt := H.Obj) (Query := H.query) κ W φ

/-- Additivity transport of evidence in the hyperdoctrine WM bundle. -/
theorem evidenceAt_add
    (W₁ W₂ : State) {X : H.Obj} (φ : H.query X) :
    H.evidenceAt (W₁ + W₂) φ = H.evidenceAt W₁ φ + H.evidenceAt W₂ φ := by
  letI : WorldModelSigma State H.Obj H.query := H.worldModel
  simpa [evidenceAt] using
    (WorldModelSigma.evidenceAt_add (State := State) (Srt := H.Obj) (Query := H.query) W₁ W₂ φ)

/-- Reindex-then-existential transport obeys Beck-Chevalley at query interpretation level. -/
theorem beckChevalley_transport_exists
    {P A B D : H.Obj}
    (π₁ : P ⟶ A) (π₂ : P ⟶ B) (f : A ⟶ D) (g : B ⟶ D)
    (hpb : IsPullback π₁ π₂ f g)
    [Mono f] [Mono π₂]
    (φ : H.query B) :
    H.interpret (H.reindexQuery f (H.existsQuery g φ)) =
      H.interpret (H.existsQuery π₁ (H.reindexQuery π₂ φ)) := by
  calc
    H.interpret (H.reindexQuery f (H.existsQuery g φ))
        = H.cob.pullback f (H.interpret (H.existsQuery g φ)) := by
            simpa using H.reindex_interp f (H.existsQuery g φ)
    _ = H.cob.pullback f (H.cob.directImage g (H.interpret φ)) := by
          simpa using congrArg (H.cob.pullback f) (H.exists_interp g φ)
    _ = H.cob.directImage π₁ (H.cob.pullback π₂ (H.interpret φ)) := by
          exact H.beckChevalley π₁ π₂ f g hpb (H.interpret φ)
    _ = H.cob.directImage π₁ (H.interpret (H.reindexQuery π₂ φ)) := by
          simpa using congrArg (H.cob.directImage π₁) (H.reindex_interp π₂ φ).symm
    _ = H.interpret (H.existsQuery π₁ (H.reindexQuery π₂ φ)) := by
          simpa using (H.exists_interp π₁ (H.reindexQuery π₂ φ)).symm

end WMHyperdoctrine

end Mettapedia.Logic.PLNWorldModelHyperdoctrine

