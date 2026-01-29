/-
# Values to FOET Bridge

This module provides a bridge between the Mettapedia Values formalization
(extending OpenPsi/MicroPsi) and the FOET (Foundations of Ethics) ontology.

## Key Mappings

1. **ValueType → FOET structures**: Map our 20 value types to FOET's typed system
2. **MoralFoundations → FOET paradigms**: Haidt's foundations to ethical paradigms
3. **DeontologicalLayer → FOET constraints**: Our forbidden/required to FOET deontology
4. **Unified semantics**: Combine both approaches in a model-theoretic framework

## Design Philosophy

FOET is a philosophical ontology rooted in SUMO and KIF traditions.
Our Values module is a cognitive architecture extension.
The bridge preserves both:
- FOET's philosophical rigor and inter-paradigm translation machinery
- Values module's practical cognitive architecture integration

## References

- FOET: gardenofminds.art/esowiki/ethics/
- Schwartz, "A Theory of Cultural Values" (1992)
- Haidt, "The Righteous Mind" (2012)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic
import Mettapedia.CognitiveArchitecture.Values.SchwartzValues
import Mettapedia.CognitiveArchitecture.Values.MoralFoundations
import Mettapedia.CognitiveArchitecture.Values.DeontologicalLayer

namespace Mettapedia.CognitiveArchitecture.Values.FOETBridge

open Mettapedia.CognitiveArchitecture.Values
open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## FOET-Compatible Type Definitions

These mirror FOET's type structure but integrate with our value types.
-/

universe u

/-- FOET-style formula as world → Prop -/
abbrev Formula (World : Type u) : Type u := World → Prop

/-- FOET-style theory as set of sentences -/
abbrev Theory (S : Type u) : Type u := S → Prop

/-- FOET-style semantics -/
structure Semantics (S : Type u) (M : Type v) : Type (max u v) where
  Sat : M → S → Prop

/-- Models relation: m satisfies all sentences in T -/
def Models {S : Type u} {M : Type v} (sem : Semantics S M) (m : M) (T : Theory S) : Prop :=
  ∀ s, T s → sem.Sat m s

/-- Entailment: T entails φ if every model of T satisfies φ -/
def Entails {S : Type u} {M : Type v} (sem : Semantics S M) (T : Theory S) (φ : S) : Prop :=
  ∀ m, Models sem m T → sem.Sat m φ

/-! ## Moral Value Attributes (FOET-style)

Extended from FOET's 3-way deontic to support Haidt's 6 foundations.
-/

/-- Extended moral value tags incorporating moral foundations -/
inductive ExtendedMoralAttribute where
  -- FOET's original 3
  | morallyGood : ExtendedMoralAttribute
  | morallyBad : ExtendedMoralAttribute
  | morallyPermissible : ExtendedMoralAttribute
  -- Haidt's 6 foundations as moral modalities
  | careViolation : ExtendedMoralAttribute      -- Harm done
  | careEnactment : ExtendedMoralAttribute      -- Care given
  | fairnessViolation : ExtendedMoralAttribute  -- Injustice/cheating
  | fairnessEnactment : ExtendedMoralAttribute  -- Justice enacted
  | loyaltyViolation : ExtendedMoralAttribute   -- Betrayal
  | loyaltyEnactment : ExtendedMoralAttribute   -- Loyalty demonstrated
  | authorityViolation : ExtendedMoralAttribute -- Subversion
  | authorityEnactment : ExtendedMoralAttribute -- Respect shown
  | sanctityViolation : ExtendedMoralAttribute  -- Degradation/impurity
  | sanctityEnactment : ExtendedMoralAttribute  -- Purity/elevation
  | libertyViolation : ExtendedMoralAttribute   -- Oppression
  | libertyEnactment : ExtendedMoralAttribute   -- Freedom protected
  deriving DecidableEq, Repr

/-- Standard FOET moral attribute (subset) -/
inductive StandardMoralAttribute where
  | morallyGood : StandardMoralAttribute
  | morallyBad : StandardMoralAttribute
  | morallyPermissible : StandardMoralAttribute
  deriving DecidableEq, Repr

/-- Embed standard into extended -/
def standardToExtended : StandardMoralAttribute → ExtendedMoralAttribute
  | .morallyGood => .morallyGood
  | .morallyBad => .morallyBad
  | .morallyPermissible => .morallyPermissible

/-- Map Haidt foundations to extended attributes (positive/enactment) -/
def foundationToEnactment : MoralFoundations.Foundation → ExtendedMoralAttribute
  | .careHarm => .careEnactment
  | .fairness => .fairnessEnactment
  | .loyalty => .loyaltyEnactment
  | .authority => .authorityEnactment
  | .sanctity => .sanctityEnactment
  | .liberty => .libertyEnactment

/-- Map Haidt foundations to extended attributes (negative/violation) -/
def foundationToViolation : MoralFoundations.Foundation → ExtendedMoralAttribute
  | .careHarm => .careViolation
  | .fairness => .fairnessViolation
  | .loyalty => .loyaltyViolation
  | .authority => .authorityViolation
  | .sanctity => .sanctityViolation
  | .liberty => .libertyViolation

/-! ## Extended Value Judgment Sentences

FOET-style sentences with our extended moral attributes.
-/

/-- Extended value judgment sentence -/
structure ExtendedValueSentence (World : Type*) where
  tag : ExtendedMoralAttribute
  formula : Formula World

/-- Theory of extended value sentences -/
abbrev ExtendedValueTheory (World : Type*) :=
  Theory (ExtendedValueSentence World)

/-- Semantics for extended value sentences -/
structure ExtendedValueSemantics (World : Type*) where
  morally : ExtendedMoralAttribute → Formula World → Formula World

def ExtendedValueSemantics.sat {World : Type*} (sem : ExtendedValueSemantics World)
    (w : World) (s : ExtendedValueSentence World) : Prop :=
  sem.morally s.tag s.formula w

def extendedValueSentenceSemantics (World : Type*) (sem : ExtendedValueSemantics World) :
    Semantics (ExtendedValueSentence World) World :=
  ⟨fun w s => sem.sat w s⟩

/-! ## Value Type Integration

Connect our ValueType to FOET's typed structure.
-/

/-- Map ValueType to whether it implies a positive or negative valence -/
def valueTypeValence : ValueType → Bool
  | .benevolence => true   -- Positive (care for in-group)
  | .universalism => true  -- Positive (care for all)
  | .careHarm => true      -- Positive when enacted
  | .fairness => true
  | .liberty => true
  | .power => false        -- Can be negative (domination)
  | _ => true              -- Most values are positive when satisfied

/-- Create an extended value sentence from a ValueType and formula -/
def valueTypeToSentence {World : Type*} (v : ValueType) (φ : Formula World) :
    ExtendedValueSentence World :=
  { tag := if valueTypeValence v then .morallyGood else .morallyPermissible
    formula := φ }

/-- Create a foundation-specific sentence -/
def foundationToSentence {World : Type*} (f : MoralFoundations.Foundation)
    (enacted : Bool) (φ : Formula World) : ExtendedValueSentence World :=
  { tag := if enacted then foundationToEnactment f else foundationToViolation f
    formula := φ }

/-! ## Deontological Integration

Connect our DeontologicalLayer to FOET's paradigms.
-/

/-- FOET-style deontic attributes -/
inductive DeonticAttribute where
  | obligation : DeonticAttribute
  | prohibition : DeonticAttribute
  | permission : DeonticAttribute
  deriving DecidableEq, Repr

/-- FOET-style deontic sentence -/
structure DeonticSentence (World : Type*) where
  tag : DeonticAttribute
  formula : Formula World

/-- Map our deontological status to FOET deontic attribute -/
def statusToDeontic : Deontological.DeontologicalStatus → DeonticAttribute
  | .forbidden => .prohibition
  | .required => .obligation
  | .permitted => .permission

/-- Get the aggregate status of an action from a constraint set -/
def aggregateStatus {Action : Type*} (cs : Deontological.ConstraintSet Action) (a : Action) :
    Deontological.DeontologicalStatus :=
  if Deontological.isForbidden cs a then .forbidden
  else if Deontological.isRequired cs a then .required
  else .permitted

/-- Convert our deontological constraint to FOET deontic theory -/
def constraintToDeonticTheory {World : Type*} {Action : Type*}
    (cs : Deontological.ConstraintSet Action) (actionToFormula : Action → Formula World) :
    Theory (DeonticSentence World) :=
  fun s =>
    ∃ a : Action, statusToDeontic (aggregateStatus cs a) = s.tag ∧ s.formula = actionToFormula a

/-! ## Deontic to Value Translation (FOET-style)

Bidirectional translation between deontic and value paradigms.
-/

/-- Standard deontic → moral value mapping (from FOET) -/
def deonticToMoral : DeonticAttribute → StandardMoralAttribute
  | .obligation => .morallyGood
  | .prohibition => .morallyBad
  | .permission => .morallyPermissible

/-- Inverse mapping -/
def moralToDeontic : StandardMoralAttribute → DeonticAttribute
  | .morallyGood => .obligation
  | .morallyBad => .prohibition
  | .morallyPermissible => .permission

theorem deonticToMoral_moralToDeontic (m : StandardMoralAttribute) :
    deonticToMoral (moralToDeontic m) = m := by
  cases m <;> rfl

theorem moralToDeontic_deonticToMoral (d : DeonticAttribute) :
    moralToDeontic (deonticToMoral d) = d := by
  cases d <;> rfl

/-- Translate deontic sentence to (standard) value sentence -/
def deonticToValue {World : Type*} (s : DeonticSentence World) :
    ExtendedValueSentence World :=
  { tag := standardToExtended (deonticToMoral s.tag)
    formula := s.formula }

/-! ## Unified Value Semantics

A semantics that handles both our extended values and FOET's paradigms.
-/

/-- Unified world state combining cognitive and philosophical aspects -/
structure UnifiedWorld where
  /-- Current value satisfaction levels -/
  valueSatisfaction : ValueSatisfaction
  /-- Current moral foundation sensitivities -/
  foundationProfile : MoralFoundations.MoralProfile
  /-- Base world state for formulas -/
  baseWorld : Unit  -- Placeholder; specialize in applications

/-- Unified semantics combining value and deontic interpretations -/
def unifiedSemantics : ExtendedValueSemantics UnifiedWorld :=
  { morally := fun attr φ w =>
      match attr with
      | .morallyGood => φ w
      | .morallyBad => ¬φ w
      | .morallyPermissible => φ w  -- Permissible means can be true
      -- Foundation-based evaluation uses profile sensitivity
      | .careEnactment => φ w ∧ w.foundationProfile.sensitivity .careHarm > ⟨0.5, by norm_num, by norm_num⟩
      | .careViolation => φ w ∧ w.foundationProfile.sensitivity .careHarm > ⟨0.5, by norm_num, by norm_num⟩
      | .fairnessEnactment => φ w ∧ w.foundationProfile.sensitivity .fairness > ⟨0.5, by norm_num, by norm_num⟩
      | .fairnessViolation => φ w ∧ w.foundationProfile.sensitivity .fairness > ⟨0.5, by norm_num, by norm_num⟩
      | .loyaltyEnactment => φ w ∧ w.foundationProfile.sensitivity .loyalty > ⟨0.5, by norm_num, by norm_num⟩
      | .loyaltyViolation => φ w ∧ w.foundationProfile.sensitivity .loyalty > ⟨0.5, by norm_num, by norm_num⟩
      | .authorityEnactment => φ w ∧ w.foundationProfile.sensitivity .authority > ⟨0.5, by norm_num, by norm_num⟩
      | .authorityViolation => φ w ∧ w.foundationProfile.sensitivity .authority > ⟨0.5, by norm_num, by norm_num⟩
      | .sanctityEnactment => φ w ∧ w.foundationProfile.sensitivity .sanctity > ⟨0.5, by norm_num, by norm_num⟩
      | .sanctityViolation => φ w ∧ w.foundationProfile.sensitivity .sanctity > ⟨0.5, by norm_num, by norm_num⟩
      | .libertyEnactment => φ w ∧ w.foundationProfile.sensitivity .liberty > ⟨0.5, by norm_num, by norm_num⟩
      | .libertyViolation => φ w ∧ w.foundationProfile.sensitivity .liberty > ⟨0.5, by norm_num, by norm_num⟩ }

/-! ## Coverage and Completeness Theorems -/

/-- Our extended system covers all FOET standard attributes -/
theorem covers_standard_moral (attr : StandardMoralAttribute) :
    ∃ ext : ExtendedMoralAttribute, ext = standardToExtended attr := by
  exact ⟨standardToExtended attr, rfl⟩

/-- Our extended system covers all Haidt foundations (both polarities) -/
theorem covers_all_foundations (f : MoralFoundations.Foundation) :
    (∃ ext : ExtendedMoralAttribute, ext = foundationToEnactment f) ∧
    (∃ ext : ExtendedMoralAttribute, ext = foundationToViolation f) := by
  exact ⟨⟨foundationToEnactment f, rfl⟩, ⟨foundationToViolation f, rfl⟩⟩

/-- Deontic → Value translation is injective on tags -/
theorem deontic_value_tag_injective (d1 d2 : DeonticAttribute) :
    deonticToMoral d1 = deonticToMoral d2 → d1 = d2 := by
  intro h
  cases d1 <;> cases d2 <;> simp_all [deonticToMoral]

/-- Extended attributes are strictly larger than standard -/
theorem extended_strictly_larger :
    ∃ ext : ExtendedMoralAttribute,
      ∀ std : StandardMoralAttribute, ext ≠ standardToExtended std := by
  use .careEnactment
  intro std
  cases std <;> simp [standardToExtended]

/-! ## SUMO-Compatible Signature

A simplified SUMO ethics signature compatible with our value types.
-/

/-- SUMO-style ethics signature for our value system -/
structure ValueSumoSig (World : Type*) where
  Agent : Type*
  /-- Which values an agent holds -/
  holdsValue : Agent → ValueType → Formula World
  /-- How strongly an agent holds a value -/
  valueStrength : Agent → ValueType → UnitValue
  /-- Which moral foundations an agent is sensitive to -/
  foundationSensitivity : Agent → MoralFoundations.Foundation → UnitValue
  /-- Agent's deontological constraints -/
  hasConstraint : Agent → DeonticAttribute → Formula World → Formula World

/-- Construct a formula stating agent cares about value at threshold -/
def ValueSumoSig.caresAbout {World : Type*} (sig : ValueSumoSig World)
    (a : sig.Agent) (v : ValueType) (threshold : UnitValue) : Formula World :=
  fun w => sig.holdsValue a v w ∧ sig.valueStrength a v ≥ threshold

/-- Construct a formula stating agent is sensitive to foundation -/
def ValueSumoSig.isSensitiveTo {World : Type*} (sig : ValueSumoSig World)
    (a : sig.Agent) (f : MoralFoundations.Foundation) (threshold : UnitValue) : Formula World :=
  fun _ => sig.foundationSensitivity a f ≥ threshold

/-! ## Bridge Theorems

Key results connecting the two formalizations.
-/

/-- The Values module covers what FOET covers, plus more -/
theorem values_extends_foet :
    (∀ std : StandardMoralAttribute, ∃ ext : ExtendedMoralAttribute, ext = standardToExtended std) ∧
    (∃ ext : ExtendedMoralAttribute, ∀ std : StandardMoralAttribute, ext ≠ standardToExtended std) := by
  constructor
  · exact covers_standard_moral
  · exact extended_strictly_larger

/-- Foundation polarity is preserved: enactment ≠ violation for same foundation -/
theorem foundation_polarity_distinct (f : MoralFoundations.Foundation) :
    foundationToEnactment f ≠ foundationToViolation f := by
  cases f <;> simp [foundationToEnactment, foundationToViolation]

/-- The deontic-value roundtrip is the identity -/
theorem deontic_value_roundtrip (d : DeonticAttribute) :
    moralToDeontic (deonticToMoral d) = d :=
  moralToDeontic_deonticToMoral d

end Mettapedia.CognitiveArchitecture.Values.FOETBridge
