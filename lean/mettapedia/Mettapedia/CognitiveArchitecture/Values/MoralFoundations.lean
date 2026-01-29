/-
# Moral Foundations Theory (Haidt)

Formalization of Jonathan Haidt's Moral Foundations Theory, which identifies
six innate psychological systems that form the basis of moral reasoning.

## The Six Foundations

1. **Care/Harm** - Protecting others from harm, empathy, compassion
2. **Fairness/Cheating** - Justice, rights, reciprocity, proportionality
3. **Loyalty/Betrayal** - Group loyalty, patriotism, self-sacrifice for group
4. **Authority/Subversion** - Respect for tradition, hierarchy, legitimate authority
5. **Sanctity/Degradation** - Purity, avoiding contamination, sacredness
6. **Liberty/Oppression** - Freedom from tyranny, autonomy (added later)

## Key Insight

Moral judgment is primarily intuitive (emotional), not reasoned.
These foundations are like "taste buds" - innate but culturally refined.

## References

- Haidt, "The Righteous Mind" (2012)
- Graham et al., "Moral Foundations Theory" (2013)
-/

import Mettapedia.CognitiveArchitecture.Values.Basic

namespace Mettapedia.CognitiveArchitecture.Values.MoralFoundations

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)
open Mettapedia.CognitiveArchitecture.Values (ValueType)

/-! ## Moral Foundation Types

The six moral foundations with their defining characteristics.
-/

/-- Haidt's six moral foundations -/
inductive Foundation where
  | careHarm : Foundation       -- Protecting others from harm
  | fairness : Foundation       -- Justice, rights, reciprocity
  | loyalty : Foundation        -- Group loyalty, patriotism
  | authority : Foundation      -- Respect for tradition, hierarchy
  | sanctity : Foundation       -- Purity, sacredness
  | liberty : Foundation        -- Freedom from oppression
  deriving DecidableEq, Repr

/-- Each foundation has a virtue/vice pair -/
structure FoundationPair where
  foundation : Foundation
  virtue : String
  vice : String
  deriving Repr

/-- The virtue/vice pairs for each foundation -/
def foundationPairs : List FoundationPair :=
  [{ foundation := .careHarm, virtue := "compassion", vice := "cruelty" },
   { foundation := .fairness, virtue := "justice", vice := "cheating" },
   { foundation := .loyalty, virtue := "loyalty", vice := "betrayal" },
   { foundation := .authority, virtue := "respect", vice := "subversion" },
   { foundation := .sanctity, virtue := "purity", vice := "degradation" },
   { foundation := .liberty, virtue := "freedom", vice := "oppression" }]

/-! ## Moral Foundation Sensitivity

Different individuals/cultures have different sensitivities to each foundation.
This explains why the same action can be seen as moral or immoral.
-/

/-- Sensitivity profile: how strongly each foundation is weighted -/
structure MoralProfile where
  sensitivity : Foundation → UnitValue

/-- Liberal moral profile (emphasizes Care, Fairness, Liberty) -/
def liberalProfile : MoralProfile :=
  { sensitivity := fun f => match f with
      | .careHarm => ⟨0.9, by norm_num, by norm_num⟩
      | .fairness => ⟨0.9, by norm_num, by norm_num⟩
      | .loyalty => ⟨0.3, by norm_num, by norm_num⟩
      | .authority => ⟨0.2, by norm_num, by norm_num⟩
      | .sanctity => ⟨0.2, by norm_num, by norm_num⟩
      | .liberty => ⟨0.8, by norm_num, by norm_num⟩ }

/-- Conservative moral profile (more balanced across all foundations) -/
def conservativeProfile : MoralProfile :=
  { sensitivity := fun f => match f with
      | .careHarm => ⟨0.7, by norm_num, by norm_num⟩
      | .fairness => ⟨0.7, by norm_num, by norm_num⟩
      | .loyalty => ⟨0.8, by norm_num, by norm_num⟩
      | .authority => ⟨0.8, by norm_num, by norm_num⟩
      | .sanctity => ⟨0.8, by norm_num, by norm_num⟩
      | .liberty => ⟨0.6, by norm_num, by norm_num⟩ }

/-- Libertarian moral profile (emphasizes Liberty strongly) -/
def libertarianProfile : MoralProfile :=
  { sensitivity := fun f => match f with
      | .careHarm => ⟨0.5, by norm_num, by norm_num⟩
      | .fairness => ⟨0.6, by norm_num, by norm_num⟩
      | .loyalty => ⟨0.3, by norm_num, by norm_num⟩
      | .authority => ⟨0.2, by norm_num, by norm_num⟩
      | .sanctity => ⟨0.2, by norm_num, by norm_num⟩
      | .liberty => ⟨1.0, by norm_num, by norm_num⟩ }

/-! ## Moral Triggers

Each foundation is triggered by specific types of situations/stimuli.
-/

/-- Types of moral triggers -/
inductive MoralTrigger where
  | sufferingWitnessed : MoralTrigger    -- Triggers Care/Harm
  | unfairTreatment : MoralTrigger       -- Triggers Fairness
  | groupThreat : MoralTrigger           -- Triggers Loyalty
  | disrespectShown : MoralTrigger       -- Triggers Authority
  | contaminationRisk : MoralTrigger     -- Triggers Sanctity
  | freedomRestricted : MoralTrigger     -- Triggers Liberty
  deriving DecidableEq, Repr

/-- Which foundation does a trigger activate? -/
def triggerToFoundation : MoralTrigger → Foundation
  | .sufferingWitnessed => .careHarm
  | .unfairTreatment => .fairness
  | .groupThreat => .loyalty
  | .disrespectShown => .authority
  | .contaminationRisk => .sanctity
  | .freedomRestricted => .liberty

/-! ## Moral Judgments

Moral judgments emerge from foundation activation.
-/

/-- A moral judgment with its foundation basis -/
structure MoralJudgment where
  /-- The action being judged -/
  action : String
  /-- Activation level for each foundation -/
  activation : Foundation → UnitValue
  /-- Overall moral valence (-1 = immoral, +1 = moral) -/
  valence : ℚ
  h_valence : -1 ≤ valence ∧ valence ≤ 1

/-- Compute moral judgment given a profile and foundation activations -/
def computeJudgment (profile : MoralProfile) (activation : Foundation → UnitValue) : ℚ :=
  let foundations := [Foundation.careHarm, .fairness, .loyalty, .authority, .sanctity, .liberty]
  let weighted := foundations.map fun f =>
    (profile.sensitivity f).val * (activation f).val
  weighted.sum / 6

/-! ## Foundation-Value Bridge

Connect moral foundations to the unified value taxonomy.
-/

/-- Map foundations to ValueType -/
def foundationToValue : Foundation → ValueType
  | .careHarm => .careHarm
  | .fairness => .fairness
  | .loyalty => .loyalty
  | .authority => .authority
  | .sanctity => .sanctity
  | .liberty => .liberty

/-- The mapping is injective (each foundation maps to distinct value) -/
theorem foundation_value_injective :
    Function.Injective foundationToValue := by
  intro f1 f2 h
  cases f1 <;> cases f2 <;> simp [foundationToValue] at h <;> rfl

/-! ## Moral Foundations vs OpenPsi/MicroPsi

Neither OpenPsi nor MicroPsi has any moral foundation.
-/

/-- Check if a moral foundation is covered by OpenPsi demands -/
def openPsiCoversFoundation : Foundation → Bool
  | .careHarm => false    -- Integrity is self-care, not other-care
  | .fairness => false    -- No fairness demand
  | .loyalty => false     -- Affiliation ≠ loyalty
  | .authority => false   -- No authority demand
  | .sanctity => false    -- No purity demand
  | .liberty => false     -- No liberty demand

/-- Check if a moral foundation is covered by MicroPsi demands -/
def microPsiCoversFoundation : Foundation → Bool
  | .careHarm => false    -- Intactness is self-care
  | .fairness => false    -- No fairness demand
  | .loyalty => false     -- Affiliation ≠ loyalty
  | .authority => false   -- No authority demand
  | .sanctity => false    -- No purity demand
  | .liberty => false     -- Exploration ≠ liberty

/-- Neither model covers ANY moral foundation -/
theorem no_foundations_covered :
    (∀ f : Foundation, openPsiCoversFoundation f = false) ∧
    (∀ f : Foundation, microPsiCoversFoundation f = false) := by
  constructor <;> intro f <;> cases f <;> rfl

/-! ## All Six Foundations -/

/-- List of all foundations -/
def allFoundations : List Foundation :=
  [.careHarm, .fairness, .loyalty, .authority, .sanctity, .liberty]

/-- There are exactly 6 foundations -/
theorem foundation_count : allFoundations.length = 6 := by rfl

/-- Profiles differ significantly between political orientations -/
theorem profiles_differ :
    liberalProfile.sensitivity .loyalty ≠ conservativeProfile.sensitivity .loyalty := by
  intro h
  simp only [liberalProfile, conservativeProfile] at h
  have heq : (⟨0.3, by norm_num, by norm_num⟩ : UnitValue) =
             (⟨0.8, by norm_num, by norm_num⟩ : UnitValue) := h
  have hval : (0.3 : ℚ) = 0.8 := congrArg Subtype.val heq
  norm_num at hval

end Mettapedia.CognitiveArchitecture.Values.MoralFoundations
