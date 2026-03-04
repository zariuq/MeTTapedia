import Mettapedia.Logic.PLNWorldModel

/-!
# WM Institution Layer (Evidence-Valued)

This module adds a conservative institution-style layer over `WorldModelSigma`:

- signatures = sort-indexed query families,
- signature morphisms = sort/query transport maps,
- models = WM states (fixed `State` carrier),
- satisfaction value = extracted evidence (and derived scalar views).

The core institution law here is an explicit satisfaction condition under
query transport.
-/

namespace Mettapedia.Logic.PLNWorldModelInstitution

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

universe x

/-- Signature object for typed WM queries. -/
structure WMSignature where
  Srt : Type
  Query : Srt → Type

/-- Sentence object for a WM signature (`Sigma Query`). -/
abbrev Sentence (sig : WMSignature) := Sigma sig.Query

/-- Signature morphism: sort map + query transport along the mapped sort. -/
structure WMSigMorphism (sig1 sig2 : WMSignature) where
  mapSort : sig1.Srt → sig2.Srt
  mapQuery : ∀ {s : sig1.Srt}, sig1.Query s → sig2.Query (mapSort s)

/-- Sentence transport along a signature morphism. -/
def mapSentence {sig1 sig2 : WMSignature} (sigma : WMSigMorphism sig1 sig2) :
    Sentence sig1 → Sentence sig2
  | ⟨s, q⟩ => ⟨sigma.mapSort s, sigma.mapQuery q⟩

/-- Identity signature morphism. -/
def id (sig : WMSignature) : WMSigMorphism sig sig where
  mapSort := fun s => s
  mapQuery := fun q => q

/-- Composition of signature morphisms. -/
def comp {sig1 sig2 sig3 : WMSignature}
    (sigma12 : WMSigMorphism sig1 sig2) (sigma23 : WMSigMorphism sig2 sig3) :
    WMSigMorphism sig1 sig3 where
  mapSort := fun s => sigma23.mapSort (sigma12.mapSort s)
  mapQuery := fun q => sigma23.mapQuery (sigma12.mapQuery q)

@[simp] theorem mapSentence_id (sig : WMSignature) (q : Sentence sig) :
    mapSentence (id sig) q = q := by
  cases q
  rfl

@[simp] theorem mapSentence_comp
    {sig1 sig2 sig3 : WMSignature}
    (sigma12 : WMSigMorphism sig1 sig2) (sigma23 : WMSigMorphism sig2 sig3)
    (q : Sentence sig1) :
    mapSentence (comp sigma12 sigma23) q =
      mapSentence sigma23 (mapSentence sigma12 q) := by
  cases q
  rfl

variable {State : Type x} [EvidenceType State]

/-- Reindex a typed WM instance along a signature/query transport map. -/
def reindexWorldModelSigma
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query] :
    WorldModelSigma State sig1.Srt sig1.Query where
  evidence := fun W q => WorldModelSigma.evidence W (mapSentence sigma q)
  evidence_add := by
    intro W1 W2 q
    simpa [mapSentence] using
      (WorldModelSigma.evidence_add (State := State) (Srt := sig2.Srt) (Query := sig2.Query)
        W1 W2 (mapSentence sigma q))

/-- Evidence-valued satisfaction at a state for a signature sentence. -/
def satEvidence
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (W : State) (phi : Sentence sig) : Evidence :=
  WorldModelSigma.evidence W phi

/-- Strength-valued satisfaction view. -/
noncomputable def satStrength
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  Evidence.toStrength (satEvidence (State := State) sig W phi)

/-- Context-sensitive strength-valued satisfaction view. -/
noncomputable def satStrengthWith
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (ctx : BinaryContext) (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  Evidence.strengthWith ctx (satEvidence (State := State) sig W phi)

/-- Confidence-valued satisfaction view. -/
noncomputable def satConfidence
    (sig : WMSignature) [WorldModelSigma State sig.Srt sig.Query]
    (kappa : ℝ≥0∞) (W : State) (phi : Sentence sig) : ℝ≥0∞ :=
  Evidence.toConfidence kappa (satEvidence (State := State) sig W phi)

/-- Satisfaction condition (evidence level) under signature/query transport. -/
theorem satisfactionCondition_evidence
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satEvidence (State := State) sig1 W phi =
      satEvidence (State := State) sig2 W (mapSentence sigma phi) := by
  simp [satEvidence, reindexWorldModelSigma, mapSentence]

/-- Satisfaction condition (strength view) under signature/query transport. -/
theorem satisfactionCondition_strength
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satStrength (State := State) sig1 W phi =
      satStrength (State := State) sig2 W (mapSentence sigma phi) := by
  simpa [satStrength] using
    congrArg Evidence.toStrength
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- Satisfaction condition (context-sensitive strength view). -/
theorem satisfactionCondition_strengthWith
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (ctx : BinaryContext) (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satStrengthWith (State := State) sig1 ctx W phi =
      satStrengthWith (State := State) sig2 ctx W (mapSentence sigma phi) := by
  simpa [satStrengthWith] using
    congrArg (Evidence.strengthWith ctx)
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- Satisfaction condition (confidence view). -/
theorem satisfactionCondition_confidence
    {sig1 sig2 : WMSignature}
    (sigma : WMSigMorphism sig1 sig2)
    [WorldModelSigma State sig2.Srt sig2.Query]
    (kappa : ℝ≥0∞) (W : State) (phi : Sentence sig1) :
    letI : WorldModelSigma State sig1.Srt sig1.Query :=
      reindexWorldModelSigma (State := State) sigma
    satConfidence (State := State) sig1 kappa W phi =
      satConfidence (State := State) sig2 kappa W (mapSentence sigma phi) := by
  simpa [satConfidence] using
    congrArg (Evidence.toConfidence kappa)
      (satisfactionCondition_evidence (State := State) (sigma := sigma) W phi)

/-- Institution bundle over WM signatures with explicit satisfaction condition. -/
structure WMInstitution where
  /-- State carrier and evidence algebra. -/
  State : Type
  instEvidenceType : EvidenceType State
  /-- Signature objects. -/
  Sig : Type
  /-- Sort/query family assigned to each signature. -/
  sigData : Sig → WMSignature
  /-- Signature morphisms. -/
  Hom : Sig → Sig → Type
  /-- Identity morphism. -/
  id : ∀ sig, Hom sig sig
  /-- Composition. -/
  comp : ∀ {sig1 sig2 sig3}, Hom sig1 sig2 → Hom sig2 sig3 → Hom sig1 sig3
  /-- Query-transport action of signature morphisms. -/
  mapHom :
    ∀ {sig1 sig2}, Hom sig1 sig2 →
      WMSigMorphism (sigData sig1) (sigData sig2)
  /-- WM semantics at each signature. -/
  worldModel :
    ∀ sig, WorldModelSigma State (sigData sig).Srt (sigData sig).Query
  /-- Evidence-valued satisfaction condition. -/
  sat_condition :
    ∀ {sig1 sig2} (h : Hom sig1 sig2) (W : State)
      (phi : Sentence (sigData sig1)),
      letI : EvidenceType State := instEvidenceType
      letI : WorldModelSigma State (sigData sig2).Srt (sigData sig2).Query :=
        worldModel sig2
      letI : WorldModelSigma State (sigData sig1).Srt (sigData sig1).Query :=
        reindexWorldModelSigma (State := State) (mapHom h)
      satEvidence (State := State) (sigData sig1) W phi =
        satEvidence (State := State) (sigData sig2) W ((mapSentence (mapHom h)) phi)

attribute [instance] WMInstitution.instEvidenceType

namespace WMInstitution

/-- Strength-level satisfaction transport derived from institution evidence law. -/
theorem sat_condition_strength
    (I : WMInstitution)
    {sig1 sig2 : I.Sig}
    (h : I.Hom sig1 sig2) (W : I.State)
    (phi : Sentence (I.sigData sig1)) :
    letI : WorldModelSigma I.State (I.sigData sig2).Srt (I.sigData sig2).Query :=
      I.worldModel sig2
    letI : WorldModelSigma I.State (I.sigData sig1).Srt (I.sigData sig1).Query :=
      reindexWorldModelSigma (State := I.State) (I.mapHom h)
    satStrength (State := I.State) (I.sigData sig1) W phi =
      satStrength (State := I.State) (I.sigData sig2) W
        ((mapSentence (I.mapHom h)) phi) := by
  simpa [satStrength] using
    congrArg Evidence.toStrength (I.sat_condition h W phi)

end WMInstitution

end Mettapedia.Logic.PLNWorldModelInstitution
