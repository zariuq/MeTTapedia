import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDeterminism
import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard

/-!
# The dialect-projection boundary

The derived native theory is intended to be one spine from which authored HE,
PeTTa, Prime, and future dialect calculi are obtained by projection plus small,
named quirk deltas.  The present tree already proves the weaker prerequisite:
the observed HE and PeTTa requirements are exact projections of the Prime
requirement bag.

That prerequisite is not the authored-calculus theorem.  Rule counts live in
several different presentations (typing, determinism, guards, operational
rewrites, and regression suites), and an observation bag cannot determine any
of them.  This module makes both facts explicit and gives the nondegenerate
target interface for the later exact calculus instances.
-/

namespace Mettapedia.Languages.MeTTa.NativeTypeTheory.DialectProjectionBoundary

/-! ## Exact capability projections already available -/

/-- Project the native observed requirement spine onto precisely the
requirements selected by a dialect bag. -/
def projectRequirements (bag : ObservationBag) : List Requirement :=
  primeBag.requirements.filter (fun requirement => requirement ∈ bag.requirements)

theorem he_requirements_are_native_projection :
    projectRequirements heBag = heBag.requirements := by
  decide

theorem petta_requirements_are_native_projection :
    projectRequirements pettaBag = pettaBag.requirements := by
  decide

theorem zero_requirements_are_native_projection :
    projectRequirements zeroBag = zeroBag.requirements := by
  decide

/-- Prime projects to the full observed spine. -/
theorem prime_requirements_are_identity_projection :
    projectRequirements primeBag = primeBag.requirements := by
  decide

/-! ## The honest authored-calculus target -/

/-- A nondegenerate exact projection of one finite native rule presentation
into one authored dialect presentation.

The equality is the desired "projection plus quirk delta" theorem.  The two
strictness fields rule out empty/constant witnesses: at least one native rule
must survive, and the delta must be strictly smaller than the dialect
calculus.  Concrete HE, PeTTa, and Prime instances require a common finite
native rule carrier; they cannot be inferred from observation bags. -/
structure ExactDialectCalculusProjection
    (NativeRule DialectRule : Type*) where
  nativeRules : List NativeRule
  dialectRules : List DialectRule
  project : NativeRule → Option DialectRule
  quirkDelta : List DialectRule
  exact_decomposition :
    dialectRules = nativeRules.filterMap project ++ quirkDelta
  shared_rule_survives : ∃ native dialect, native ∈ nativeRules ∧
    project native = some dialect
  delta_is_strictly_smaller : quirkDelta.length < dialectRules.length

theorem ExactDialectCalculusProjection.dialect_nonempty
    {NativeRule DialectRule : Type*}
    (projection : ExactDialectCalculusProjection NativeRule DialectRule) :
    projection.dialectRules ≠ [] := by
  intro empty
  have lengthZero : projection.dialectRules.length = 0 := by
    simp [empty]
  have := projection.delta_is_strictly_smaller
  omega

/-! ## Negative canary: bags do not determine authored rule inventories -/

/-- Only the information that an observation bag exposes about a calculus.
The rule count is retained separately so factorization can be tested. -/
structure CalculusInventory where
  label : String
  observations : List Observation
  ruleCount : Nat

/-- The actual HE typing-calculus inventory. -/
def heTypingInventory : CalculusInventory where
  label := "HE typing"
  observations := heBag.observed
  ruleCount := Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT.calculus.rules.length

/-- The actual base PeTTa typing-calculus inventory. -/
def pettaTypingInventory : CalculusInventory where
  label := "PeTTa base typing"
  observations := pettaBag.observed
  ruleCount :=
    Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT.calculus.rules.length

theorem he_typing_rule_count : heTypingInventory.ruleCount = 22 :=
  Mettapedia.Languages.MeTTa.HE.TypeSystemGSLT.rule_count

theorem petta_typing_rule_count : pettaTypingInventory.ruleCount = 21 :=
  Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT.calculus_rule_count

/-- HE and PeTTa currently force the same observed typing requirements, yet
their authored base typing calculi have different sizes. -/
theorem equal_observations_different_authored_rule_counts :
    heTypingInventory.observations = pettaTypingInventory.observations ∧
      heTypingInventory.ruleCount ≠ pettaTypingInventory.ruleCount := by
  constructor
  · rfl
  · rw [he_typing_rule_count, petta_typing_rule_count]
    decide

/-- Consequently no function of the observed property list alone recovers
the actual authored typing-rule count for these two dialects. -/
theorem observation_bag_does_not_determine_authored_rule_count :
    ¬ ∃ determine : List Observation → Nat,
      heTypingInventory.ruleCount = determine heTypingInventory.observations ∧
      pettaTypingInventory.ruleCount =
        determine pettaTypingInventory.observations := by
  rintro ⟨determine, heCount, pettaCount⟩
  have sameObservation := equal_observations_different_authored_rule_counts.1
  have sameCount : heTypingInventory.ruleCount = pettaTypingInventory.ruleCount := by
    calc
      heTypingInventory.ruleCount = determine heTypingInventory.observations := heCount
      _ = determine pettaTypingInventory.observations := congrArg determine sameObservation
      _ = pettaTypingInventory.ruleCount := pettaCount.symm
  exact equal_observations_different_authored_rule_counts.2 sameCount

/-! ## Rule-inventory census -/

/-- Two publicly exposed PeTTa typing presentations are distinct calculi,
not one 132-rule authored object: base typing has 21 rules and the guard
profile has 72.  The determinism module independently pins its private
calculus at 50 rules. -/
theorem petta_base_and_guard_have_distinct_rule_counts :
    Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT.calculus.rules.length = 21 ∧
    Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard.guardCalculus.rules.length = 72 := by
  exact ⟨Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT.calculus_rule_count,
    Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard.guard_rule_count⟩

end Mettapedia.Languages.MeTTa.NativeTypeTheory.DialectProjectionBoundary
