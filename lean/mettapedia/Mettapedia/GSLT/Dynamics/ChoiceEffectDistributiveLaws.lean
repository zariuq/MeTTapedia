import Mettapedia.GSLT.Dynamics.ContextualControlSurface
import Mettapedia.GSLT.Dynamics.InterventionalValueBoundary
import Mettapedia.GSLT.Dynamics.SymmetryAwareResolution
import Mathlib.Tactic

/-!
# Distributive boundaries for value, choice, and effects

Several useful operations commute with occurrence-family choice: attaching a
candidate-local value, filtering locally, and retaining isolated worlds.  The
same is false for exact maximum, normalization, shared-state execution,
deterministic resolution of a symmetric family, and causal intervention.

This module collects those boundaries in one syntax-independent interface and
adds two effect laws:

* an authored state merge retains every answer, value, branch receipt, and
  deferred intent because it changes only the delta coordinate;
* no occurrence-preserving post-hoc resolver over isolated worlds can emulate
  shared execution when one branch reads another branch's write.

The result is a small distributive-law matrix suitable for later GSLT and
space-policy instances.  It deliberately does not choose a default handler.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ChoiceEffectDistributiveLaws

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Dynamics.CandidateLocalResolution
open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation

universe uCandidate uValue uState uDelta uAnswer uIntent uView

/-! ## Occurrence-family homomorphisms -/

/-- A family transformation distributes over independent occurrence-family
choice when it is a commutative-monoid homomorphism for bag addition. -/
def DistributesOverChoice
    {Candidate : Type uCandidate} {Output : Type*}
    (transform : Multiset Candidate → Multiset Output) : Prop :=
  ∀ left right, transform (left + right) = transform left + transform right

/-- Retaining the family is distributive. -/
theorem retain_distributesOverChoice (Candidate : Type uCandidate) :
    DistributesOverChoice (id : Multiset Candidate → Multiset Candidate) := by
  intro left right
  rfl

/-- Attach one local value to each occurrence.  Equal structural candidates
remain separate occurrences even when their values happen to agree. -/
def attachValueFamily
    {Candidate : Type uCandidate} {Value : Type uValue}
    (value : Candidate → Value) (candidates : Multiset Candidate) :
    Multiset (Candidate × Value) :=
  candidates.map fun candidate => (candidate, value candidate)

/-- Candidate-local value attachment distributes over family choice. -/
theorem attachValueFamily_distributesOverChoice
    {Candidate : Type uCandidate} {Value : Type uValue}
    (value : Candidate → Value) :
    DistributesOverChoice (attachValueFamily value) := by
  intro left right
  exact Multiset.map_add _ left right

/-- Value attachment preserves occurrence multiplicity exactly. -/
theorem attachValueFamily_card
    {Candidate : Type uCandidate} {Value : Type uValue}
    (value : Candidate → Value) (candidates : Multiset Candidate) :
    (attachValueFamily value candidates).card = candidates.card := by
  exact Multiset.card_map _ _

/-- Every pure candidate-local clause lies on the distributive side. -/
theorem localClause_distributesOverChoice
    {Candidate : Type uCandidate} {Value : Type uValue} {Output : Type*}
    (clause : Clause Candidate Value Output) :
    DistributesOverChoice clause.runBag := by
  exact clause.runBag_add

/-- Exact maximum lies on the family-relative side whenever one occurrence
strictly outweighs another. -/
theorem max_does_not_distributeOverChoice
    {Candidate : Type uCandidate} (weight : Candidate → Nat)
    {low high : Candidate} (outweighed : weight low < weight high) :
    ¬ DistributesOverChoice (maxSelector weight) :=
  maxSelector_not_additive weight outweighed

/-- Normalized share is competitor-relative even when every local weight is
strictly positive. -/
theorem normalization_depends_on_family :
    ∃ weight : Bool → ℝ, ∃ candidate : Bool,
      ∃ first second : Multiset Bool,
        candidate ∈ first ∧ candidate ∈ second ∧
        (∀ other ∈ first, 0 < weight other) ∧
        (∀ other ∈ second, 0 < weight other) ∧
        raceShare weight first candidate ≠ raceShare weight second candidate :=
  normalizedShare_not_candidatewise

/-! ## Values over contextual worlds -/

/-- Attach a value to the answer coordinate of one isolated world without
changing its branch receipt, state delta, state, or deferred intents. -/
def valueWorld
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent} {Value : Type uValue}
    (value : Answer → Value)
    (world : ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent) :
    ContextualDeltaHandlers.DeltaWorld State Delta (Answer × Value) Intent :=
  { branch := world.branch
    answer := (world.answer, value world.answer)
    delta := world.delta
    state := world.state
    intents := world.intents }

def valueWorlds
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent} {Value : Type uValue}
    (value : Answer → Value)
    (worlds : List
      (ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent)) :
    List (ContextualDeltaHandlers.DeltaWorld
      State Delta (Answer × Value) Intent) :=
  worlds.map (valueWorld value)

/-- Valuing isolated worlds distributes over the concatenation introduced by
an alternative. -/
theorem valueWorlds_append
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent} {Value : Type uValue}
    (value : Answer → Value)
    (left right : List
      (ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent)) :
    valueWorlds value (left ++ right) =
      valueWorlds value left ++ valueWorlds value right := by
  exact List.map_append

/-! ## Authored merge changes only the delta coordinate -/

/-- A successful alternative merge retains the exact contextual world list.
In particular, it cannot erase answers, values, occurrence traces, or intent
receipts. -/
theorem mergeWorlds_preserves_worlds
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent}
    (algebra : ContextualDeltaHandlers.DeltaAlgebra State Delta)
    (parent : State)
    (resolver : ContextualDeltaHandlers.AlternativeMerge Delta)
    (worlds : List
      (ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent))
    (merged : ContextualDeltaHandlers.Merged State Delta Answer Intent)
    (success : ContextualDeltaHandlers.mergeWorlds
      algebra parent resolver worlds = some merged) :
    merged.worlds = worlds := by
  unfold ContextualDeltaHandlers.mergeWorlds at success
  cases resolution : resolver.merge
      (ContextualDeltaHandlers.worldDeltas worlds) with
  | none => simp [resolution] at success
  | some delta =>
      simp [resolution] at success
      subst merged
      rfl

/-- Every view of the occurrence worlds, including typed values and deferred
intent receipts, is therefore preserved by a successful state merge. -/
theorem mergeWorlds_preserves_view
    {State : Type uState} {Delta : Type uDelta}
    {Answer : Type uAnswer} {Intent : Type uIntent} {View : Type uView}
    (algebra : ContextualDeltaHandlers.DeltaAlgebra State Delta)
    (parent : State)
    (resolver : ContextualDeltaHandlers.AlternativeMerge Delta)
    (worlds : List
      (ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent))
    (merged : ContextualDeltaHandlers.Merged State Delta Answer Intent)
    (view : ContextualDeltaHandlers.DeltaWorld State Delta Answer Intent → View)
    (success : ContextualDeltaHandlers.mergeWorlds
      algebra parent resolver worlds = some merged) :
    merged.worlds.map view = worlds.map view := by
  rw [mergeWorlds_preserves_worlds algebra parent resolver worlds merged success]

/-! ## Shared state is not post-hoc resolution -/

/-- A post-hoc policy is occurrence-preserving when it returns exactly the
answer bag produced by isolated exploration. -/
def RetainsIsolatedAnswers
    {State : Type uState} {Answer : Type uAnswer} {Intent : Type uIntent}
    (policy : List
      (ContextualEffectHandlers.WorldResult State Answer Intent) →
        Multiset Answer) : Prop :=
  ∀ worlds, policy worlds =
    (worlds.map ContextualEffectHandlers.WorldResult.answer : Multiset Answer)

def isolatedIncrementAnswers : Multiset Nat :=
  ((ContextualEffectHandlers.runWorlds
      ContextualEffectHandlers.Canary.twoIncrements 0).map
    ContextualEffectHandlers.WorldResult.answer : Multiset Nat)

def sharedIncrementAnswers : Multiset Nat :=
  ((ContextualEffectHandlers.runShared
      ContextualEffectHandlers.Canary.twoIncrements 0).answers : Multiset Nat)

/-- The same program gives different answer bags under isolated and shared
state because the second shared branch observes the first branch's write. -/
theorem isolated_shared_increment_answers_differ :
    isolatedIncrementAnswers ≠ sharedIncrementAnswers := by
  change (([0, 0] : List Nat) : Multiset Nat) ≠
    (([0, 1] : List Nat) : Multiset Nat)
  intro equal
  have counts := congrArg (Multiset.count 1) equal
  norm_num at counts

/-- Negative control: shared execution cannot be recovered by any post-hoc
resolver that preserves the occurrences discovered under isolated worlds. -/
theorem no_occurrencePreserving_postHoc_policy_recovers_shared :
    ¬ ∃ policy : List
        (ContextualEffectHandlers.WorldResult Nat Nat Unit) → Multiset Nat,
      RetainsIsolatedAnswers policy ∧
        policy (ContextualEffectHandlers.runWorlds
          ContextualEffectHandlers.Canary.twoIncrements 0) =
          sharedIncrementAnswers := by
  rintro ⟨policy, retains, recovers⟩
  have retained := retains
    (ContextualEffectHandlers.runWorlds
      ContextualEffectHandlers.Canary.twoIncrements 0)
  rw [recovers] at retained
  exact isolated_shared_increment_answers_differ retained.symm

/-! ## Symmetry and causal structure remain separate authorities -/

/-- An invariant local value ties the symmetric Boolean pair, while no
equivariant deterministic family resolver can select one member. -/
theorem invariant_values_do_not_supply_symmetric_choice :
    (∀ {Value : Type*} (value : Bool → Value),
      SymmetryAwareResolution.InvariantValuation
          (Equiv.Perm Bool) Bool value →
        value false = value true) ∧
      ¬ ∃ resolver : Multiset Bool → Multiset Bool,
        SymmetryAwareResolution.EquivariantResolver
            (Equiv.Perm Bool) Bool resolver ∧
          ∃ chosen : Bool,
            resolver SymmetryAwareResolution.boolPair = {chosen} := by
  constructor
  · intro Value value invariant
    exact SymmetryAwareResolution.invariantValuation_ties_boolPair
      value invariant
  · exact
      SymmetryAwareResolution.no_equivariant_singleton_resolution_of_boolPair

/-- Equality of an observational value channel still does not supply causal
intervention authority. -/
theorem observational_values_do_not_supply_intervention :
    InterventionalValueBoundary.observationalValue
        InterventionalValueBoundary.xCausesY =
      InterventionalValueBoundary.observationalValue
        InterventionalValueBoundary.yCausesX ∧
      ¬ InterventionalValueBoundary.InterventionallyEquivalent
        InterventionalValueBoundary.xCausesY
        InterventionalValueBoundary.yCausesX := by
  exact ⟨InterventionalValueBoundary.oppositeDirections_same_observationalValue,
    InterventionalValueBoundary.observationalEquivalence_does_not_imply_interventionalEquivalence.2⟩

/-! ## Axiom audit -/

#print axioms attachValueFamily_distributesOverChoice
#print axioms localClause_distributesOverChoice
#print axioms max_does_not_distributeOverChoice
#print axioms normalization_depends_on_family
#print axioms valueWorlds_append
#print axioms mergeWorlds_preserves_view
#print axioms no_occurrencePreserving_postHoc_policy_recovers_shared
#print axioms invariant_values_do_not_supply_symmetric_choice
#print axioms observational_values_do_not_supply_intervention

end Mettapedia.GSLT.Dynamics.ChoiceEffectDistributiveLaws
