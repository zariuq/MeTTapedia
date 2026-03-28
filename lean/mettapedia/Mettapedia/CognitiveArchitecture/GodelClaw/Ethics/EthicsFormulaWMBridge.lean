import Mettapedia.CognitiveArchitecture.GodelClaw.Ethics.ProtectedGoals
import Mettapedia.Ethics.Core
import Mettapedia.CognitiveArchitecture.Values.DeontologicalLayer
import Mettapedia.Logic.MarkovLogicClauseFactorGraph
import Mettapedia.Logic.MarkovLogicInfiniteSpecification

/-!
# Ethics Formula to WM Bridge

This module gives a deliberately modest extraction layer from ethics-side
sentences into WM queries.

The point is not to pretend we already have a full SUMO/ESO semantics inside
the MLN world model.  Instead, we expose a typed interface:

- ontology-side ethical anchors and labeled FOET-style sentences,
- an application-specific encoder into WM atoms,
- compilation into WM singleton queries,
- and alignment lemmas showing that deontic/value translations can compile to
  the same WM query when the encoder respects the FOET tag map.

This is the honest first bridge from the ethics ontology lane into the proved
WM meta-stability machinery.
-/

namespace Mettapedia.CognitiveArchitecture.GodelClaw.Ethics

open Mettapedia.Ethics
open Mettapedia.CognitiveArchitecture.Values.Deontological
open Mettapedia.CognitiveArchitecture.Values.Relational
open Mettapedia.Logic.MarkovLogicClauseFactorGraph
open Mettapedia.Logic.MarkovLogicInfiniteSpecification

universe u v w

/-- A typed ontology-side ethical anchor before WM compilation. -/
inductive EthicalAnchor (Agent : Type u) (Label : Type v) where
  | epistemicUniversalLove : Agent → EthicalAnchor Agent Label
  | moralValue : Agent → MoralValueAttribute → Label → EthicalAnchor Agent Label
  | deontic : Agent → DeonticAttribute → Label → EthicalAnchor Agent Label
  | universalDuty : Agent → UniversalDuty → EthicalAnchor Agent Label
  | relational : Agent → Agent → RelationalValueType → EthicalAnchor Agent Label
  deriving DecidableEq, Repr

/-- Application-specific encoding from typed ethical anchors into WM atoms. -/
structure EthicsQueryEncoder (Agent : Type u) (Label : Type v) (Atom : Type w) where
  epistemicUniversalLoveAtom : Agent → Atom
  moralValueAtom : Agent → MoralValueAttribute → Label → Atom
  deonticAtom : Agent → DeonticAttribute → Label → Atom
  universalDutyAtom : Agent → UniversalDuty → Atom
  relationalAtom : Agent → Agent → RelationalValueType → Atom

/-- FOET-style alignment at the WM-atom level: deontic and value translations
compile to the same atom. -/
def EthicsQueryEncoder.DeonticValueAligned
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (enc : EthicsQueryEncoder Agent Label Atom) : Prop :=
  ∀ a d l, enc.deonticAtom a d l = enc.moralValueAtom a (deonticToMoralValue d) l

/-- Compile an ethical anchor to a singleton WM query. -/
def EthicalAnchor.toQuery
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (anchor : EthicalAnchor Agent Label) : ConstraintQuery Atom :=
  match anchor with
  | .epistemicUniversalLove a => [⟨enc.epistemicUniversalLoveAtom a, true⟩]
  | .moralValue a tag l => [⟨enc.moralValueAtom a tag l, true⟩]
  | .deontic a tag l => [⟨enc.deonticAtom a tag l, true⟩]
  | .universalDuty a d => [⟨enc.universalDutyAtom a d, true⟩]
  | .relational a b r => [⟨enc.relationalAtom a b r, true⟩]

/-- Support on a region reduces to the encoded anchor atom lying in that region. -/
def EthicalAnchor.supportedOn
    {Agent : Type u} {Label : Type v} {Atom : Type w}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom) (anchor : EthicalAnchor Agent Label) : Prop :=
  match anchor with
  | .epistemicUniversalLove a => enc.epistemicUniversalLoveAtom a ∈ Γ
  | .moralValue a tag l => enc.moralValueAtom a tag l ∈ Γ
  | .deontic a tag l => enc.deonticAtom a tag l ∈ Γ
  | .universalDuty a d => enc.universalDutyAtom a d ∈ Γ
  | .relational a b r => enc.relationalAtom a b r ∈ Γ

theorem EthicalAnchor.toQuery_supported
    {Agent : Type u} {Label : Type v} {Atom : Type w} [DecidableEq Atom]
    (enc : EthicsQueryEncoder Agent Label Atom)
    (Γ : Region Atom) (anchor : EthicalAnchor Agent Label)
    (hsupp : anchor.supportedOn enc Γ) :
    ∀ p ∈ anchor.toQuery enc, (p : Sigma fun _ : Atom => Bool).1 ∈ Γ := by
  cases anchor <;> simpa [EthicalAnchor.toQuery, EthicalAnchor.supportedOn] using hsupp

/-- Labeled FOET-style value sentence for extraction into a WM anchor. -/
structure LabeledValueJudgmentSentence (World : Type u) (Agent : Type v) (Label : Type w) where
  agent : Agent
  label : Label
  sentence : ValueJudgmentSentence World

/-- Labeled FOET-style deontic sentence for extraction into a WM anchor. -/
structure LabeledDeonticSentence (World : Type u) (Agent : Type v) (Label : Type w) where
  agent : Agent
  label : Label
  sentence : DeonticSentence World

/-- Extract a labeled value sentence to an ontology-side anchor. -/
def LabeledValueJudgmentSentence.toAnchor
    {World : Type u} {Agent : Type v} {Label : Type w}
    (s : LabeledValueJudgmentSentence World Agent Label) :
    EthicalAnchor Agent Label :=
  .moralValue s.agent s.sentence.tag s.label

/-- Extract a labeled deontic sentence to an ontology-side anchor. -/
def LabeledDeonticSentence.toAnchor
    {World : Type u} {Agent : Type v} {Label : Type w}
    (s : LabeledDeonticSentence World Agent Label) :
    EthicalAnchor Agent Label :=
  .deontic s.agent s.sentence.tag s.label

/-- FOET deontic-to-value translation lifted to labeled sentences. -/
def LabeledDeonticSentence.toValue
    {World : Type u} {Agent : Type v} {Label : Type w}
    (s : LabeledDeonticSentence World Agent Label) :
    LabeledValueJudgmentSentence World Agent Label where
  agent := s.agent
  label := s.label
  sentence := s.sentence.toValue

/-- If the encoder respects the FOET deontic/value tag map, then the WM query
compiled from a labeled deontic sentence agrees exactly with the WM query
compiled from its labeled value translation. -/
theorem LabeledDeonticSentence.toQuery_toValue_eq_of_aligned
    {World : Type u} {Agent : Type v} {Label : Type w} {Atom : Type*}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (hAlign : enc.DeonticValueAligned)
    (s : LabeledDeonticSentence World Agent Label) :
    (s.toAnchor.toQuery enc) = (s.toValue.toAnchor.toQuery enc) := by
  cases s with
  | mk agent label sentence =>
      cases sentence with
      | mk tag formula =>
          simp [LabeledDeonticSentence.toAnchor, LabeledDeonticSentence.toValue,
            LabeledValueJudgmentSentence.toAnchor, EthicalAnchor.toQuery,
            EthicsQueryEncoder.DeonticValueAligned] at hAlign ⊢
          exact hAlign agent tag label

/-- Four distinguished ontology anchors matching the protected-ethics family. -/
structure ProtectedEthicsAnchors (Agent : Type u) (Label : Type v) where
  epistemicUniversalLove : EthicalAnchor Agent Label
  nonMaleficence : EthicalAnchor Agent Label
  consent : EthicalAnchor Agent Label
  reciprocity : EthicalAnchor Agent Label

/-- Compile four ontology anchors into the protected ethics-query family used by
the meta-stability theorems. -/
def ProtectedEthicsAnchors.toProtectedEthicsQueryFamily
    {Agent : Type u} {Label : Type v} {Atom : Type w} [DecidableEq Atom]
    {Γ : Region Atom}
    (enc : EthicsQueryEncoder Agent Label Atom)
    (anchors : ProtectedEthicsAnchors Agent Label)
    (hEUL : anchors.epistemicUniversalLove.supportedOn enc Γ)
    (hNoHarm : anchors.nonMaleficence.supportedOn enc Γ)
    (hConsent : anchors.consent.supportedOn enc Γ)
    (hReciprocity : anchors.reciprocity.supportedOn enc Γ) :
    ProtectedEthicsQueryFamily Γ where
  goals :=
    { anchors.epistemicUniversalLove.toQuery enc,
      anchors.nonMaleficence.toQuery enc,
      anchors.consent.toQuery enc,
      anchors.reciprocity.toQuery enc }
  supported := by
    intro q hq
    simp at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact EthicalAnchor.toQuery_supported enc Γ anchors.epistemicUniversalLove hEUL
    · exact EthicalAnchor.toQuery_supported enc Γ anchors.nonMaleficence hNoHarm
    · exact EthicalAnchor.toQuery_supported enc Γ anchors.consent hConsent
    · exact EthicalAnchor.toQuery_supported enc Γ anchors.reciprocity hReciprocity
  epistemicUniversalLoveQuery := anchors.epistemicUniversalLove.toQuery enc
  nonMaleficenceQuery := anchors.nonMaleficence.toQuery enc
  consentQuery := anchors.consent.toQuery enc
  reciprocityQuery := anchors.reciprocity.toQuery enc
  mem_epistemicUniversalLove := by simp
  mem_nonMaleficence := by simp
  mem_consent := by simp
  mem_reciprocity := by simp

/-- Observation frontier extracted from ontology-side ethical anchors.

This is directly compatible with the Hyperseed `frontier : Obs → Set Query`
interface by taking `Query := ConstraintQuery Atom`. -/
def ethicalAnchorFrontier
    {Obs : Type*} {Agent : Type u} {Label : Type v} {Atom : Type w}
    (extract : Obs → Set (EthicalAnchor Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom) :
    Obs → Set (ConstraintQuery Atom) :=
  fun o => { q | ∃ anchor ∈ extract o, q = anchor.toQuery enc }

@[simp] theorem mem_ethicalAnchorFrontier
    {Obs : Type*} {Agent : Type u} {Label : Type v} {Atom : Type w}
    (extract : Obs → Set (EthicalAnchor Agent Label))
    (enc : EthicsQueryEncoder Agent Label Atom)
    (o : Obs) (q : ConstraintQuery Atom) :
    q ∈ ethicalAnchorFrontier extract enc o ↔
      ∃ anchor ∈ extract o, q = anchor.toQuery enc := by
  rfl

end Mettapedia.CognitiveArchitecture.GodelClaw.Ethics
