import Mettapedia.Ethics.TargetCenteredVirtue
import Mettapedia.KR.ConceptOntology.ConstructionBase
import Mettapedia.KR.ConceptOntology.FCA
import Mettapedia.PLN.Evidence.BinEvNat

/-!
# Ethical Concept Formation from Target-Centered Virtue Structure

Formal concept analysis can organize observed ethical cases without replacing
the ethical ontology.  Cases are objects; field, mode, target, value-basis, and
verdict facts are attributes; and incidence is computed from an existing
target-centered virtue theory.

The resulting concepts are therefore evidence-derived views of a prior typed
ontology.  They can support learning new candidate groupings of situations and
responses, while the identities of agents, actions, virtues, values, and
judgments remain intact.
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.EthicalConceptFormation

open Mettapedia.Ethics
open Mettapedia.Ethics.TargetCenteredVirtue
open Mettapedia.KR.ConceptOntology

universe uAgent uSituation uAction uValue uVirtue

/-- One observed agent/situation/action case. -/
structure EthicalCase
    (Agent : Type uAgent) (Situation : Type uSituation)
    (Action : Type uAction) where
  agent : Agent
  situation : Situation
  action : Action
  deriving DecidableEq

/-- Attributes available to concept formation from a target-centered virtue
theory. -/
inductive EthicalAttribute
    (Virtue : Type uVirtue) (Value : Type uValue) : Type (max uVirtue uValue) where
  | inField (virtue : Virtue)
  | usesMode (virtue : Virtue)
  | hitsTarget (virtue : Virtue)
  | respondsToValue (value : Value)
  | supportsVerdict (verdict : MoralValueAttribute)
  deriving DecidableEq

/-- Incidence is derived from the actual virtue specifications.  In
particular, `hitsTarget` entails both field membership and the declared mode;
it is not an unstructured label supplied by the concept learner. -/
def incidence
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value) :
    EthicalCase Agent Situation Action → EthicalAttribute Virtue Value → Prop
  | observed, .inField virtue =>
      virtue ∈ theory.included ∧
        (theory.spec virtue).field observed.situation
  | observed, .usesMode virtue =>
      virtue ∈ theory.included ∧
        (theory.spec virtue).mode observed.agent observed.situation observed.action
  | observed, .hitsTarget virtue =>
      virtue ∈ theory.included ∧
        (theory.spec virtue).ActionHitsTarget
          observed.agent observed.situation observed.action
  | observed, .respondsToValue value =>
      ∃ virtue, virtue ∈ theory.included ∧
        value ∈ (theory.spec virtue).basis ∧
        (theory.spec virtue).ActionHitsTarget
          observed.agent observed.situation observed.action
  | observed, .supportsVerdict verdict =>
      theory.SupportsVerdict
        observed.agent observed.situation observed.action verdict

/-- The identity gate turns a proposition-valued incidence relation into the
standard FCA interface without adding or discarding evidence. -/
def truthGate : EvidenceGate Prop where
  accept proposition := proposition
  mono := by
    intro first second implies holds
    exact implies holds

/-- Formal concepts generated from the ethical incidence relation. -/
abbrev EthicalConcept
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value) :=
  CrispConcept truthGate (incidence theory)

/-- The observed cases possessing one ethical attribute. -/
def attributeExtent
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (feature : EthicalAttribute Virtue Value) :
    Set (EthicalCase Agent Situation Action) :=
  crispExtent truthGate (incidence theory) feature

@[simp] theorem mem_attributeExtent_iff
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (observed : EthicalCase Agent Situation Action)
    (feature : EthicalAttribute Virtue Value) :
    observed ∈ attributeExtent theory feature ↔
      incidence theory observed feature := by
  simp [attributeExtent, truthGate]

theorem hitsTarget_extent_subset_field_extent
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (virtue : Virtue) :
    attributeExtent theory (.hitsTarget virtue) ⊆
      attributeExtent theory (.inField virtue) := by
  intro observed member
  rw [mem_attributeExtent_iff] at member ⊢
  exact ⟨member.1, member.2.1⟩

theorem hitsTarget_extent_subset_mode_extent
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (virtue : Virtue) :
    attributeExtent theory (.hitsTarget virtue) ⊆
      attributeExtent theory (.usesMode virtue) := by
  intro observed member
  rw [mem_attributeExtent_iff] at member ⊢
  exact ⟨member.1, member.2.2.1⟩

/-! ## Open-world, observer-indexed concept formation -/

/-- Turn a target-centered virtue theory into the standard open-world
construction base. The index type and visibility map remain explicit: a time,
budget, community, or observer may reveal a different set of ethical cases. -/
def constructionBase
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (Indexicality : Type*)
    (visibleAt : Indexicality → Set (EthicalCase Agent Situation Action)) :
    ConstructionBase where
  Phenomena := EthicalCase Agent Situation Action
  Abstract := EthicalAttribute Virtue Value
  Indexicality := Indexicality
  incidence := incidence theory
  visibleAt := visibleAt

@[simp] theorem constructionBase_incidence
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (Indexicality : Type*)
    (visibleAt : Indexicality → Set (EthicalCase Agent Situation Action))
    (observed : EthicalCase Agent Situation Action)
    (feature : EthicalAttribute Virtue Value) :
    (constructionBase theory Indexicality visibleAt).incidence observed feature ↔
      incidence theory observed feature :=
  Iff.rfl

/-- Refining an ethical observer means seeing every case seen by the earlier
observer. The resulting closure is antitone: additional cases may refute a
premature concept implication, but cannot manufacture support by hiding a
counterexample. -/
theorem closure_antitone_of_observer_refinement
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (Indexicality : Type*)
    (visibleAt : Indexicality → Set (EthicalCase Agent Situation Action))
    {earlier later : Indexicality}
    (refines : visibleAt earlier ⊆ visibleAt later)
    (premise : Set (EthicalAttribute Virtue Value)) :
    (constructionBase theory Indexicality visibleAt).closureAt later premise ⊆
      (constructionBase theory Indexicality visibleAt).closureAt earlier premise := by
  exact ConstructionBase.closureAt_antitone_of_refines
    (constructionBase theory Indexicality visibleAt) premise refines

/-! ## WM-PLN evidence from typed ethical observations -/

open Mettapedia.PLN.Evidence

/-- An ethical observation carries either proof that a typed incidence holds
or proof that it does not. This prevents an evidence packet from silently
reversing the ontology-level judgment it claims to record. -/
inductive EthicalObservation
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value) where
  | supports
      (observed : EthicalCase Agent Situation Action)
      (feature : EthicalAttribute Virtue Value)
      (witness : incidence theory observed feature) : EthicalObservation theory
  | refutes
      (observed : EthicalCase Agent Situation Action)
      (feature : EthicalAttribute Virtue Value)
      (witness : ¬ incidence theory observed feature) : EthicalObservation theory

/-- One positive WM-PLN count. -/
def positiveObservationEvidence : BinEvNat := ⟨1, 0⟩

/-- One negative WM-PLN count. -/
def negativeObservationEvidence : BinEvNat := ⟨0, 1⟩

/-- Query-indexed evidence encoder for typed ethical observations. Only the
matching case/attribute query receives the packet; all other queries receive
zero evidence. Multiset aggregation is inherited from WM-PLN's canonical
additive observation extension. -/
def ethicalObservationEncoder
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    [DecidableEq Agent] [DecidableEq Situation] [DecidableEq Action]
    [DecidableEq Virtue] [DecidableEq Value]
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value) :
    ObservationEncoder (EthicalObservation theory)
      (EthicalCase Agent Situation Action)
      (EthicalAttribute Virtue Value) BinEvNat where
  observe observation query :=
    match observation with
    | .supports observed feature _ =>
        if observed = query.1 ∧ feature = query.2 then
          positiveObservationEvidence
        else 0
    | .refutes observed feature _ =>
        if observed = query.1 ∧ feature = query.2 then
          negativeObservationEvidence
        else 0

@[simp] theorem ethicalObservationEncoder_supports_self
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    [DecidableEq Agent] [DecidableEq Situation] [DecidableEq Action]
    [DecidableEq Virtue] [DecidableEq Value]
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (observed : EthicalCase Agent Situation Action)
    (feature : EthicalAttribute Virtue Value)
    (witness : incidence theory observed feature) :
    (ethicalObservationEncoder theory).observe
        (.supports observed feature witness) (observed, feature) =
      positiveObservationEvidence := by
  simp [ethicalObservationEncoder]

@[simp] theorem ethicalObservationEncoder_refutes_self
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    [DecidableEq Agent] [DecidableEq Situation] [DecidableEq Action]
    [DecidableEq Virtue] [DecidableEq Value]
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (observed : EthicalCase Agent Situation Action)
    (feature : EthicalAttribute Virtue Value)
    (witness : ¬ incidence theory observed feature) :
    (ethicalObservationEncoder theory).observe
        (.refutes observed feature witness) (observed, feature) =
      negativeObservationEvidence := by
  simp [ethicalObservationEncoder]

@[simp] theorem ethicalObservationEncoder_supports_other_case
    {Virtue : Type uVirtue}
    {Agent : Type uAgent} {Situation : Type uSituation}
    {Action : Type uAction} {Value : Type uValue}
    [DecidableEq Agent] [DecidableEq Situation] [DecidableEq Action]
    [DecidableEq Virtue] [DecidableEq Value]
    (theory : TargetCenteredVirtue.Theory Virtue Agent Situation Action Value)
    (observed other : EthicalCase Agent Situation Action)
    (feature : EthicalAttribute Virtue Value)
    (witness : incidence theory observed feature)
    (different : observed ≠ other) :
    (ethicalObservationEncoder theory).observe
        (.supports observed feature witness) (other, feature) = 0 := by
  simp [ethicalObservationEncoder, different]

/-! ## Rescue concept canaries -/

abbrev RescueCase :=
  EthicalCase RescueAgent RescueSituation RescueAction

def emergencyCrossCase : RescueCase :=
  ⟨.helper, .emergency, .cross⟩

def ordinaryCrossCase : RescueCase :=
  ⟨.helper, .ordinary, .cross⟩

/-- Two observer horizons for the rescue specimen. -/
inductive RescueObservationView
  | emergencyOnly
  | emergencyAndOrdinary
  deriving DecidableEq

def rescueVisibleAt : RescueObservationView → Set RescueCase
  | .emergencyOnly => {emergencyCrossCase}
  | .emergencyAndOrdinary => {emergencyCrossCase, ordinaryCrossCase}

def rescueConstructionBase : ConstructionBase :=
  constructionBase rescueTheory RescueObservationView rescueVisibleAt

theorem rescue_emergencyOnly_refines_emergencyAndOrdinary :
    rescueConstructionBase.Refines .emergencyOnly .emergencyAndOrdinary := by
  intro observed visible
  simp only [rescueConstructionBase, constructionBase,
    rescueVisibleAt] at visible ⊢
  exact Or.inl visible

theorem emergencyCross_mem_courageTarget_extent :
    emergencyCrossCase ∈
      attributeExtent rescueTheory (.hitsTarget RescueVirtue.courage) := by
  rw [mem_attributeExtent_iff]
  exact ⟨by simp [rescueTheory], emergencyCross_hits_courage_target⟩

theorem ordinaryCross_not_mem_courageTarget_extent :
    ordinaryCrossCase ∉
      attributeExtent rescueTheory (.hitsTarget RescueVirtue.courage) := by
  intro member
  rw [mem_attributeExtent_iff] at member
  exact ordinaryCross_does_not_hit_courage_target member.2

def emergencyCourageSupport : EthicalObservation rescueTheory :=
  .supports emergencyCrossCase (.hitsTarget RescueVirtue.courage)
    ⟨by simp [rescueTheory], emergencyCross_hits_courage_target⟩

def ordinaryCourageRefutation : EthicalObservation rescueTheory :=
  .refutes ordinaryCrossCase (.hitsTarget RescueVirtue.courage) (by
    intro observed
    exact ordinaryCross_does_not_hit_courage_target observed.2)

theorem emergencyCourageSupport_records_positive_evidence :
    (ethicalObservationEncoder rescueTheory).observe emergencyCourageSupport
        (emergencyCrossCase, .hitsTarget RescueVirtue.courage) =
      positiveObservationEvidence := by
  simp [emergencyCourageSupport]

theorem ordinaryCourageRefutation_records_negative_evidence :
    (ethicalObservationEncoder rescueTheory).observe ordinaryCourageRefutation
        (ordinaryCrossCase, .hitsTarget RescueVirtue.courage) =
      negativeObservationEvidence := by
  simp [ordinaryCourageRefutation]

theorem emergencyCross_mem_preservationOfLife_extent :
    emergencyCrossCase ∈
      attributeExtent rescueTheory
        (.respondsToValue RescueValue.preservationOfLife) := by
  rw [mem_attributeExtent_iff]
  exact ⟨.courage, by simp [rescueTheory], by simp [rescueTheory, courageSpec],
    emergencyCross_hits_courage_target⟩

/-! ## Axiom audit -/

#print axioms mem_attributeExtent_iff
#print axioms hitsTarget_extent_subset_field_extent
#print axioms hitsTarget_extent_subset_mode_extent
#print axioms closure_antitone_of_observer_refinement
#print axioms ethicalObservationEncoder_supports_self
#print axioms ethicalObservationEncoder_refutes_self
#print axioms ethicalObservationEncoder_supports_other_case
#print axioms rescue_emergencyOnly_refines_emergencyAndOrdinary
#print axioms emergencyCross_mem_courageTarget_extent
#print axioms ordinaryCross_not_mem_courageTarget_extent
#print axioms emergencyCourageSupport_records_positive_evidence
#print axioms ordinaryCourageRefutation_records_negative_evidence
#print axioms emergencyCross_mem_preservationOfLife_extent

end Mettapedia.Ethics.EthicalConceptFormation
