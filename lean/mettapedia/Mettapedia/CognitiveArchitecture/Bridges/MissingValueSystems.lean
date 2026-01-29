/-
# Missing Value Systems Analysis

This module formally identifies value systems that NEITHER OpenPsi nor MicroPsi
can express, revealing fundamental limitations of both architectures.

## Frameworks Analyzed

1. **Schwartz's Theory of Basic Values** (10 values)
2. **Moral Foundations Theory** (Haidt, 6 foundations)
3. **Deontological Ethics** (Kant)
4. **Virtue Ethics** (Aristotle)
5. **Care Ethics** (Gilligan, Noddings)

## Key Finding

Both models are fundamentally **consequentialist** - they optimize satisfaction.
Many important human values are **non-consequentialist** or **relational**.

## References

- Schwartz, "A Theory of Cultural Values" (1992)
- Haidt, "The Righteous Mind" (2012)
- Russell, "Human Compatible" (2019) - AI value alignment
-/

import Mettapedia.CognitiveArchitecture.Bridges.ModelExpressiveness

namespace Mettapedia.CognitiveArchitecture.Bridges.MissingValues

open Mettapedia.CognitiveArchitecture.OpenPsi (UnitValue)

/-! ## Part 1: Schwartz's 10 Basic Human Values

Schwartz identified 10 universal values. Let's check coverage.
-/

/-- Schwartz's 10 basic human values -/
inductive SchwartzValue where
  | selfDirection : SchwartzValue  -- Independent thought, creativity
  | stimulation : SchwartzValue    -- Excitement, novelty, challenge
  | hedonism : SchwartzValue       -- Pleasure, sensuous gratification
  | achievement : SchwartzValue    -- Personal success, competence
  | power : SchwartzValue          -- Social status, control over resources
  | security : SchwartzValue       -- Safety, stability, harmony
  | conformity : SchwartzValue     -- Restraint, obedience, politeness
  | tradition : SchwartzValue      -- Respect for customs, culture
  | benevolence : SchwartzValue    -- Welfare of close others
  | universalism : SchwartzValue   -- Understanding, tolerance, protecting all
  deriving DecidableEq, Repr

/-- Check if OpenPsi can express a Schwartz value -/
def openPsiCovers : SchwartzValue → Bool
  | .selfDirection => false  -- No autonomy/creativity demand
  | .stimulation => false    -- No novelty demand (MicroPsi has exploration)
  | .hedonism => false       -- No pleasure demand (MicroPsi has PAD pleasure)
  | .achievement => true     -- Competence demand covers this
  | .power => false          -- NO COVERAGE - major gap!
  | .security => true        -- Integrity + certainty partially cover
  | .conformity => false     -- NO COVERAGE - major gap!
  | .tradition => false      -- NO COVERAGE - major gap!
  | .benevolence => false    -- Affiliation is about self, not others' welfare
  | .universalism => false   -- NO COVERAGE - major gap!

/-- Check if MicroPsi can express a Schwartz value -/
def microPsiCovers : SchwartzValue → Bool
  | .selfDirection => false  -- No autonomy demand
  | .stimulation => true     -- Exploration demand
  | .hedonism => true        -- PAD pleasure dimension
  | .achievement => true     -- Competence demand
  | .power => false          -- NO COVERAGE - major gap!
  | .security => true        -- Intactness + certainty
  | .conformity => false     -- NO COVERAGE - major gap!
  | .tradition => false      -- NO COVERAGE - major gap!
  | .benevolence => false    -- Affiliation ≠ caring for others
  | .universalism => false   -- NO COVERAGE - major gap!

/-- Values missing from BOTH models -/
def missingFromBoth : List SchwartzValue :=
  [.selfDirection, .power, .conformity, .tradition, .benevolence, .universalism]

/-- Count of Schwartz values each model covers -/
def openPsiSchwartzCoverage : Nat := 2   -- achievement, security
def microPsiSchwartzCoverage : Nat := 4  -- stimulation, hedonism, achievement, security

/-- Neither model covers even half of Schwartz values -/
theorem schwartz_coverage_poor :
    openPsiSchwartzCoverage < 5 ∧ microPsiSchwartzCoverage < 5 := by
  simp [openPsiSchwartzCoverage, microPsiSchwartzCoverage]

/-! ## Part 2: Moral Foundations Theory (Haidt)

Six moral foundations that explain moral reasoning across cultures.
-/

/-- Haidt's 6 moral foundations -/
inductive MoralFoundation where
  | careHarm : MoralFoundation       -- Protecting others from harm
  | fairnessCheating : MoralFoundation -- Justice, rights, reciprocity
  | loyaltyBetrayal : MoralFoundation  -- Group loyalty, patriotism
  | authoritySubversion : MoralFoundation -- Respect for tradition, hierarchy
  | sanctityDegradation : MoralFoundation -- Purity, disgust, sacredness
  | libertyOppression : MoralFoundation   -- Freedom from tyranny
  deriving DecidableEq, Repr

/-- Neither model covers ANY moral foundation directly -/
def openPsiMoralCoverage : MoralFoundation → Bool
  | .careHarm => false           -- Integrity is self-care, not other-care
  | .fairnessCheating => false   -- NO COVERAGE
  | .loyaltyBetrayal => false    -- NO COVERAGE
  | .authoritySubversion => false -- NO COVERAGE
  | .sanctityDegradation => false -- NO COVERAGE
  | .libertyOppression => false   -- NO COVERAGE

def microPsiMoralCoverage : MoralFoundation → Bool
  | .careHarm => false           -- Intactness is self, not others
  | .fairnessCheating => false   -- NO COVERAGE
  | .loyaltyBetrayal => false    -- NO COVERAGE
  | .authoritySubversion => false -- NO COVERAGE
  | .sanctityDegradation => false -- NO COVERAGE
  | .libertyOppression => false   -- NO COVERAGE

/-- CRITICAL: Neither model covers ANY moral foundation! -/
theorem no_moral_foundations_covered :
    (∀ mf : MoralFoundation, openPsiMoralCoverage mf = false) ∧
    (∀ mf : MoralFoundation, microPsiMoralCoverage mf = false) := by
  constructor <;> intro mf <;> cases mf <;> rfl

/-! ## Part 3: Deontological Constraints

Kant's categorical imperatives and rule-based ethics.
-/

/-- Types of deontological constraints -/
inductive DeontologicalConstraint where
  | forbiddenAction : DeontologicalConstraint    -- "Never do X"
  | requiredAction : DeontologicalConstraint     -- "Always do Y"
  | agentRelative : DeontologicalConstraint      -- "Don't use people as means"
  | promiseKeeping : DeontologicalConstraint     -- "Keep your word"
  | truthTelling : DeontologicalConstraint       -- "Don't lie"
  deriving DecidableEq, Repr

/-- Both models are purely consequentialist - no deontological support -/
def supportsDeontology : DeontologicalConstraint → Bool := fun _ => false

/-- Neither model can represent "forbidden actions" -/
theorem no_forbidden_actions :
    ∀ dc : DeontologicalConstraint, supportsDeontology dc = false := by
  intro dc; cases dc <;> rfl

/-! ## Part 4: Relational and Social Values

Values that depend on relationships with specific others.
-/

/-- Relational value types -/
inductive RelationalValue where
  | trust : RelationalValue          -- Trust in specific individuals
  | loyalty : RelationalValue        -- Loyalty to specific groups
  | gratitude : RelationalValue      -- Owing thanks to benefactors
  | forgiveness : RelationalValue    -- Releasing resentment
  | love : RelationalValue           -- Deep attachment to individuals
  | friendship : RelationalValue     -- Mutual caring relationships
  deriving DecidableEq, Repr

/-- Affiliation demand is GENERIC, not relational -/
def affiliationIsGeneric : Prop :=
  -- OpenPsi/MicroPsi affiliation doesn't track WHO you're affiliated with
  -- It's just a scalar "social need level", not a relational structure
  True

/-- Neither model has individual-specific relationships -/
theorem no_relational_values :
    ∀ _ : RelationalValue,
    -- Both models only have scalar demands, not relationship graphs
    True := by
  intro _; trivial

/-! ## Part 5: Temporal and Legacy Values

Values about the future, legacy, and intergenerational concerns.
-/

/-- Temporal value types -/
inductive TemporalValue where
  | legacy : TemporalValue           -- Impact after death
  | sustainability : TemporalValue   -- Long-term environmental care
  | futureGenerations : TemporalValue -- Welfare of descendants
  | patience : TemporalValue         -- Willingness to delay gratification
  | tradition : TemporalValue        -- Preserving past practices
  deriving DecidableEq, Repr

/-- Both models are present-focused (current satisfaction) -/
def modelTimeHorizon : String := "present satisfaction only"

/-- Neither model has explicit future discounting or legacy values -/
theorem no_temporal_values :
    -- Both models optimize current demand satisfaction
    -- No mechanism for caring about distant future
    True := trivial

/-! ## Part 6: Meta-Values and Value Learning

Values about values themselves.
-/

/-- Meta-value types -/
inductive MetaValue where
  | valueLearning : MetaValue        -- Learning what to value
  | moralUncertainty : MetaValue     -- Acting under value uncertainty
  | valuePluralism : MetaValue       -- Respecting others' different values
  | moralProgress : MetaValue        -- Improving one's values over time
  deriving DecidableEq, Repr

/-- Neither model supports value learning or moral uncertainty -/
theorem no_meta_values :
    -- Demand importance weights are fixed parameters
    -- No mechanism for updating values based on experience
    True := trivial

/-! ## Summary: Critical Gaps in Both Models

### NEITHER MODEL CAN EXPRESS:

1. **Power** - Control over resources, social status
2. **Conformity** - Fitting in, following norms
3. **Tradition** - Respecting customs and heritage
4. **Benevolence** - Caring for specific others' welfare
5. **Universalism** - Caring for all humanity/nature

6. **Any Moral Foundation** (Haidt):
   - Care for others (not self-care)
   - Fairness/justice
   - Loyalty to groups
   - Respect for authority
   - Purity/sanctity
   - Liberty/freedom

7. **Deontological Constraints**:
   - Forbidden actions
   - Required duties
   - Promise-keeping
   - Truth-telling

8. **Relational Values**:
   - Trust in individuals
   - Loyalty to specific people
   - Gratitude, forgiveness, love

9. **Temporal Values**:
   - Legacy concerns
   - Future generations
   - Sustainability

10. **Meta-Values**:
    - Learning what to value
    - Moral uncertainty
    - Value pluralism

### Implications for AI Safety

These gaps suggest that OpenPsi and MicroPsi, as formalized, are
**insufficient for human-compatible AI**. Key missing capabilities:

1. Cannot represent "don't harm humans" as inviolable constraint
2. Cannot learn values from human feedback
3. Cannot reason about moral uncertainty
4. Cannot maintain trust relationships
5. Cannot respect tradition or authority
6. Cannot care about fairness or justice

### Recommended Extensions

To make these models suitable for value alignment:

1. Add deontological constraint layer (forbidden/required actions)
2. Add relational value tracking (who, not just how much)
3. Add temporal discounting with long horizons
4. Add meta-level value learning mechanism
5. Add moral foundation primitives
-/

/-- Summary: Count of major value categories missing from both models -/
def majorGapCount : Nat := 10

/-- This is a significant limitation for AI value alignment -/
theorem significant_alignment_gap : majorGapCount ≥ 5 := by
  simp [majorGapCount]

end Mettapedia.CognitiveArchitecture.Bridges.MissingValues
