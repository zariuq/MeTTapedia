/-
# Unified Value System: Basic Definitions

This module provides the foundation for a unified value system that extends
OpenPsi and MicroPsi to handle the full scope of known human values.

## Value Frameworks Integrated

1. **Schwartz's Theory of Basic Values** (10 universal values)
2. **Haidt's Moral Foundations Theory** (6 moral foundations)
3. **Deontological constraints** (forbidden/required actions)
4. **Relational values** (trust, loyalty, love for specific individuals)
5. **Temporal values** (legacy, future generations)
6. **Meta-values** (value learning, moral uncertainty)

## References

- Schwartz, "A Theory of Cultural Values" (1992)
- Haidt, "The Righteous Mind" (2012)
- Russell, "Human Compatible" (2019)
- Kluckhohn, "Values and Value-Orientations" (1951)
-/

import Mettapedia.CognitiveArchitecture.OpenPsi.Basic

namespace Mettapedia.CognitiveArchitecture.Values

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Core Value Type

A unified taxonomy of human values spanning multiple theoretical frameworks.
-/

/-- Unified value taxonomy spanning Schwartz, Haidt, and extensions.
    These represent what beings care about - abstract entities that
    influence action selection and event evaluation.
    Reference: Kluckhohn's definition of values. -/
inductive ValueType where
  -- Schwartz's 10 Basic Human Values (circular structure)
  | selfDirection : ValueType  -- Independent thought, creativity, autonomy
  | stimulation : ValueType    -- Excitement, novelty, challenge
  | hedonism : ValueType       -- Pleasure, sensuous gratification
  | achievement : ValueType    -- Personal success, competence demonstration
  | power : ValueType          -- Social status, control over resources/people
  | security : ValueType       -- Safety, stability, harmony
  | conformity : ValueType     -- Restraint, obedience, politeness
  | tradition : ValueType      -- Respect for customs, culture, heritage
  | benevolence : ValueType    -- Welfare of close others (in-group care)
  | universalism : ValueType   -- Understanding, tolerance, protecting all
  -- Haidt's 6 Moral Foundations (not reducible to Schwartz)
  | careHarm : ValueType       -- Protecting others from harm
  | fairness : ValueType       -- Justice, rights, reciprocity
  | loyalty : ValueType        -- Group loyalty, patriotism, betrayal-avoidance
  | authority : ValueType      -- Respect for tradition, hierarchy
  | sanctity : ValueType       -- Purity, disgust-avoidance, sacredness
  | liberty : ValueType        -- Freedom from tyranny/oppression
  -- Meta-values (about values themselves)
  | valueLearning : ValueType      -- Learning what to value
  | moralUncertainty : ValueType   -- Acting under value uncertainty
  | valuePluralism : ValueType     -- Respecting others' different values
  | corrigibility : ValueType      -- Openness to value correction
  deriving DecidableEq, Repr

/-- Value importance weight: how much an agent prioritizes this value -/
structure ValueWeight where
  value : ValueType
  importance : UnitValue
  deriving Repr

/-- A value system assigns importance weights to all values -/
structure ValueSystem where
  /-- Importance weight for each value type -/
  weights : ValueType → UnitValue
  /-- Minimum acceptable satisfaction for each value -/
  thresholds : ValueType → UnitValue

/-! ## Value Categories

Values can be categorized by their nature and function.
-/

/-- Value categories based on theoretical framework -/
inductive ValueCategory where
  | schwartz : ValueCategory      -- Schwartz's 10 basic values
  | moralFoundation : ValueCategory  -- Haidt's moral foundations
  | metaValue : ValueCategory     -- Values about values
  deriving DecidableEq, Repr

/-- Classify a value by its theoretical origin -/
def valueCategory : ValueType → ValueCategory
  | .selfDirection => .schwartz
  | .stimulation => .schwartz
  | .hedonism => .schwartz
  | .achievement => .schwartz
  | .power => .schwartz
  | .security => .schwartz
  | .conformity => .schwartz
  | .tradition => .schwartz
  | .benevolence => .schwartz
  | .universalism => .schwartz
  | .careHarm => .moralFoundation
  | .fairness => .moralFoundation
  | .loyalty => .moralFoundation
  | .authority => .moralFoundation
  | .sanctity => .moralFoundation
  | .liberty => .moralFoundation
  | .valueLearning => .metaValue
  | .moralUncertainty => .metaValue
  | .valuePluralism => .metaValue
  | .corrigibility => .metaValue

/-- All Schwartz values -/
def schwartzValues : List ValueType :=
  [.selfDirection, .stimulation, .hedonism, .achievement, .power,
   .security, .conformity, .tradition, .benevolence, .universalism]

/-- All moral foundations -/
def moralFoundations : List ValueType :=
  [.careHarm, .fairness, .loyalty, .authority, .sanctity, .liberty]

/-- All meta-values -/
def metaValues : List ValueType :=
  [.valueLearning, .moralUncertainty, .valuePluralism, .corrigibility]

/-- All value types -/
def allValues : List ValueType :=
  schwartzValues ++ moralFoundations ++ metaValues

/-! ## Value Satisfaction

How well a value is currently being satisfied.
-/

/-- Value satisfaction state: current satisfaction level for each value -/
structure ValueSatisfaction where
  /-- Satisfaction level for each value (0 = unsatisfied, 1 = fully satisfied) -/
  satisfaction : ValueType → UnitValue

/-- Value deficit: how much a value needs attention -/
def valueDeficit (sat : ValueSatisfaction) (v : ValueType) : UnitValue :=
  ⟨1 - (sat.satisfaction v).val,
   by constructor
      · linarith [(sat.satisfaction v).property.2]
      · linarith [(sat.satisfaction v).property.1]⟩

/-! ## Value-Demand Bridge

Connect values to the existing OpenPsi/MicroPsi demand framework.
-/

/-- Some values map to OpenPsi demands -/
def valueToDemand : ValueType → Option OpenPsi.DemandType
  | .achievement => some .competence    -- Achievement ≈ Competence
  | .security => some .integrity        -- Security ≈ Integrity
  | .benevolence => some .affiliation   -- Benevolence ≈ Affiliation (partial)
  | _ => none                           -- Most values have no demand equivalent

/-- Values that have no corresponding demand (the gap we're filling) -/
def valueHasNoDemand (v : ValueType) : Bool :=
  (valueToDemand v).isNone

/-- Count of values with no demand equivalent -/
def gapCount : Nat :=
  allValues.filter valueHasNoDemand |>.length

/-- Most values (17 of 20) have no demand equivalent -/
theorem most_values_are_new : gapCount ≥ 17 := by
  native_decide

/-! ## Value Properties

Intrinsic vs extrinsic, positive vs negative values.
-/

/-- Intrinsic values: valuable in themselves -/
def isIntrinsic : ValueType → Bool
  | .hedonism => true       -- Pleasure is intrinsically valuable
  | .benevolence => true    -- Caring is intrinsically valuable
  | .universalism => true   -- Universal care is intrinsically valuable
  | .careHarm => true       -- Care for others is intrinsic
  | _ => false              -- Most are instrumentally valuable

/-- Self-transcendent vs self-enhancing values (Schwartz distinction) -/
inductive ValueOrientation where
  | selfEnhancing : ValueOrientation    -- Focus on self (power, achievement)
  | selfTranscending : ValueOrientation -- Focus on others (benevolence, universalism)
  | openness : ValueOrientation         -- Open to change (stimulation, self-direction)
  | conservation : ValueOrientation     -- Preserve status quo (tradition, conformity, security)
  deriving DecidableEq, Repr

/-- Classify Schwartz values by orientation -/
def schwartzOrientation : ValueType → Option ValueOrientation
  | .selfDirection => some .openness
  | .stimulation => some .openness
  | .hedonism => none  -- Between self-enhancement and openness
  | .achievement => some .selfEnhancing
  | .power => some .selfEnhancing
  | .security => some .conservation
  | .conformity => some .conservation
  | .tradition => some .conservation
  | .benevolence => some .selfTranscending
  | .universalism => some .selfTranscending
  | _ => none  -- Not a Schwartz value

/-! ## Coverage Theorems

Prove that the unified model covers all major value frameworks.
-/

/-- All 10 Schwartz values are represented -/
theorem schwartz_complete : schwartzValues.length = 10 := by rfl

/-- All 6 moral foundations are represented -/
theorem moral_foundations_complete : moralFoundations.length = 6 := by rfl

/-- Total unique values in the unified model -/
theorem total_values : allValues.length = 20 := by rfl

/-- OpenPsi only covers 3 of 20 values (15%) -/
theorem openPsi_coverage_limited :
    (allValues.filter (fun v => (valueToDemand v).isSome)).length ≤ 3 := by
  native_decide

end Mettapedia.CognitiveArchitecture.Values
