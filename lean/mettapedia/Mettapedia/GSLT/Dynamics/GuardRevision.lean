import Mettapedia.TypeTheory.ObserverErasure
import Mettapedia.GSLT.Dynamics.GuardedWork
import Mettapedia.GSLT.Core.SearchStreamProductivity
import Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission

/-!
# Reusing a hoisted guard across world revisions

A query guards candidates and values the survivors.  Hoisting the guard before
a pure, total valuation preserves every ordered, duplicated occurrence
(`GuardedWork.hoist_guard`), and so does every finite requested prefix of a
stream of candidate batches (`streamPrefix_hoist_guard`).

The hoisted result computed at one revision of the world may be reused at
another exactly when the revision cannot change the guard.  Revisions and the
dependencies selected for reuse are NIK's `DependencySystem`.  A guard retained
at one revision is the one-policy family `guardPolicy`; its live meaning at a
revision is the guard computed there (`liveGuard`), and the claim that the
selected dependencies account for every change of the guard is NIK's
`DependenciesAdequate` for that family.  Under adequacy, a revision with the
same selected dependencies (`SameDependencies`) keeps the cached hoisted result
equal to the eager result of the revised world, for every finite prefix of a
stream of batches.  A selection that omits a fact the guard reads is refuted by
one collision (`not_dependenciesAdequate_of_collision`).

Hoisting is an equivalence only for a pure, total valuation: across a partial
valuation it changes whether the query finishes.

The factorization criterion (`NonFactorization.Factors`) decides which
observers the result serves after an erasure.  Keeping only the values of the
answers serves an observer of the values, but not one asking which candidates
supported them, and removing duplicate values does not serve an occurrence
count.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.GuardRevision

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.Core.SearchStreamProductivity
open Mettapedia.GSLT.Dynamics.GuardedWork
open Mettapedia.GSLT.Dynamics.ContextualCandidateValuation
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission.PolicyFamilyAdmittedAt

universe uRevision uDependency uDependencyValue uC uA

variable {Candidate : Type uC} {Value : Type uA}

/-! ## Finite prefixes of a hoisted stream -/

/-- Every finite requested prefix of a stream of candidate batches is
unchanged by hoisting the guard. -/
theorem streamPrefix_hoist_guard (guard : Candidate → Bool) (value : Candidate → Value)
    (batches : Nat → List Candidate) (demand : Nat) :
    streamPrefix (fun epoch => valueThenGuard guard value (batches epoch)) demand =
      streamPrefix (fun epoch => guardThenValue guard value (batches epoch)) demand :=
  congrArg (fun expected => streamPrefix expected demand)
    (funext fun epoch => hoist_guard guard value (batches epoch))

/-! ## Reuse under revision -/

/-- A guard retained at one revision, as a one-policy family over candidates. -/
def guardPolicy (guard : Candidate → Bool) : PolicyFamily Candidate where
  Policy := Unit
  Result := fun _ => Bool
  decide := fun _ => guard

variable {dependencies :
  DependencySystem.{uRevision, uDependency, uDependencyValue}}

/-- The live meaning of a retained guard: the guard computed at each
revision. -/
def liveGuard (guardOf : dependencies.Revision → Candidate → Bool)
    (guard : Candidate → Bool) :
    dependencies.Revision → (policy : (guardPolicy guard).Policy) → Candidate →
      (guardPolicy guard).Result policy :=
  fun revision _ => guardOf revision

/-- The guard retained at the admitted revision has its live meaning there. -/
theorem liveGuard_retained (guardOf : dependencies.Revision → Candidate → Bool)
    (admitted : dependencies.Revision) :
    RetainedMeaning (liveGuard guardOf (guardOf admitted)) admitted :=
  fun _ _ => rfl

/-- If the selected dependencies account for every change of the guard and a
revision keeps them, the hoisted result of the admitted revision is the eager
result of the current one. -/
theorem reuse_of_kept_dependencies
    {guardOf : dependencies.Revision → Candidate → Bool}
    {admitted current : dependencies.Revision}
    (adequate : DependenciesAdequate (liveGuard guardOf (guardOf admitted)))
    (kept : dependencies.SameDependencies admitted current)
    (value : Candidate → Value) (candidates : List Candidate) :
    guardThenValue (guardOf admitted) value candidates =
      valueThenGuard (guardOf current) value candidates := by
  have sameGuard : guardOf admitted = guardOf current :=
    funext fun candidate => adequate admitted current kept () candidate
  rw [sameGuard, hoist_guard]

/-- Every finite requested prefix of a stream of candidate batches is reused
alike. -/
theorem reuse_of_kept_dependencies_prefix
    {guardOf : dependencies.Revision → Candidate → Bool}
    {admitted current : dependencies.Revision}
    (adequate : DependenciesAdequate (liveGuard guardOf (guardOf admitted)))
    (kept : dependencies.SameDependencies admitted current)
    (value : Candidate → Value) (batches : Nat → List Candidate) (demand : Nat) :
    streamPrefix
        (fun epoch => guardThenValue (guardOf admitted) value (batches epoch)) demand =
      streamPrefix
        (fun epoch => valueThenGuard (guardOf current) value (batches epoch)) demand :=
  congrArg (fun expected => streamPrefix expected demand)
    (funext fun epoch => reuse_of_kept_dependencies adequate kept value (batches epoch))

/-! ## A world with a relevant and an irrelevant fact -/

section Example

/-- A world: the threshold the guard reads, and a note it ignores. -/
structure Facts where
  threshold : Nat
  note : Nat
  deriving DecidableEq

/-- The guard admits candidates below the threshold. -/
def guardOf (world : Facts) (candidate : Nat) : Bool :=
  decide (candidate < world.threshold)

/-- Revisions are worlds; the guard's selected dependency is the threshold. -/
def thresholdDependencies : DependencySystem where
  Revision := Facts
  Dependency := Unit
  Value := Nat
  read world _ := world.threshold

def before : Facts := ⟨3, 0⟩

/-- Revising the note keeps the threshold. -/
def noteRevised : Facts := ⟨3, 7⟩

/-- Revising the threshold changes the fact the guard reads. -/
def thresholdRevised : Facts := ⟨2, 0⟩

/-- The threshold accounts for every change of the guard. -/
theorem threshold_adequate :
    DependenciesAdequate
      (liveGuard (dependencies := thresholdDependencies) guardOf (guardOf before)) := by
  intro first second same _ candidate
  have threshold : first.threshold = second.threshold := same ()
  change decide (candidate < first.threshold) = decide (candidate < second.threshold)
  rw [threshold]

/-- An irrelevant revision: the cached hoisted result is still correct. -/
theorem irrelevant_revision_reuses (value : Nat → Nat) (candidates : List Nat) :
    guardThenValue (guardOf before) value candidates =
      valueThenGuard (guardOf noteRevised) value candidates :=
  reuse_of_kept_dependencies threshold_adequate (fun _ => rfl) value candidates

/-- A relevant revision: reusing the cached result gives the wrong answers. -/
theorem relevant_revision_invalidates :
    guardThenValue (guardOf before) id [1, 2, 2] ≠
      valueThenGuard (guardOf thresholdRevised) id [1, 2, 2] := by
  decide

/-- The relevant revision does not keep the selected dependencies. -/
theorem relevant_revision_not_kept :
    ¬ thresholdDependencies.SameDependencies before thresholdRevised := by
  intro same
  have changed : (3 : Nat) = 2 := same ()
  exact absurd changed (by decide)

/-- A stale guard: selecting only the note omits the threshold that the guard
reads, and one collision refutes the adequacy claim. -/
def noteDependencies : DependencySystem where
  Revision := Facts
  Dependency := Unit
  Value := Nat
  read world _ := world.note

theorem note_selection_not_adequate :
    ¬ DependenciesAdequate
      (liveGuard (dependencies := noteDependencies) guardOf (guardOf before)) :=
  not_dependenciesAdequate_of_collision _
    (first := before) (second := thresholdRevised) (fun _ => rfl) () 2 (by
      change guardOf before 2 ≠ guardOf thresholdRevised 2
      decide)

end Example

/-! ## Observers of the answers -/

section Observers

/-- Keep only the values of the answers. -/
def valuesOnly (rows : List (ValuedOccurrence Nat Nat)) : List Nat := rows.map (·.value)

/-- Which candidates supported the answers. -/
def support (rows : List (ValuedOccurrence Nat Nat)) : List Nat := rows.map (·.occurrence)

/-- Keeping only values serves an observer of the values. -/
theorem sum_factors_through_values :
    Factors valuesOnly (fun rows : List (ValuedOccurrence Nat Nat) =>
      (rows.map (·.value)).sum) :=
  ⟨List.sum, fun _ => rfl⟩

/-- Two runs with the same values from different candidates. -/
def supportFiber : NonTrivialFiber valuesOnly support where
  left := guardThenValue (fun _ => true) (fun _ => 0) [1]
  right := guardThenValue (fun _ => true) (fun _ => 0) [2]
  sameShadow := by decide
  differentValue := by decide

/-- Values alone do not serve an observer asking which candidates supported
the answers. -/
theorem support_not_factors_through_values : ¬ Factors valuesOnly support :=
  supportFiber.not_factors

/-- Keeping the support alongside the values restores that observer. -/
theorem support_factors_when_retained :
    Factors (fun rows : List (ValuedOccurrence Nat Nat) => (valuesOnly rows, support rows))
      support :=
  factors_retain valuesOnly support

/-- The hoisted query keeps both occurrences of `2`; removing duplicate values
identifies it with the run on one occurrence. -/
def dedupCountFiber :
    NonTrivialFiber (fun rows : List (ValuedOccurrence Nat Nat) => (valuesOnly rows).dedup)
      (fun rows => (valuesOnly rows).count 20) where
  left := guardThenValue (fun _ => true) (· * 10) [2, 2]
  right := guardThenValue (fun _ => true) (· * 10) [2]
  sameShadow := by decide
  differentValue := by decide

/-- Removing duplicate values does not serve an observer that counts the
occurrences of a value. -/
theorem count_not_factors_through_dedup :
    ¬ Factors (fun rows : List (ValuedOccurrence Nat Nat) => (valuesOnly rows).dedup)
      (fun rows => (valuesOnly rows).count 20) :=
  dedupCountFiber.not_factors

end Observers

/-! ## Partial valuations -/

section Partial

/-- Value every candidate, then keep the admitted ones. An undefined value
anywhere leaves the whole query undefined. -/
def eagerPartial (guard : Nat → Bool) (value : Nat → Option Nat) (candidates : List Nat) :
    Option (List Nat) :=
  (candidates.mapM value).map fun values =>
    ((candidates.zip values).filter fun row => guard row.1).map Prod.snd

/-- Keep the admitted candidates, then value only those. -/
def hoistedPartial (guard : Nat → Bool) (value : Nat → Option Nat) (candidates : List Nat) :
    Option (List Nat) :=
  (candidates.filter guard).mapM value

/-- A valuation undefined at zero. -/
def undefinedAtZero (candidate : Nat) : Option Nat :=
  if candidate = 0 then none else some (candidate * 10)

/-- Hoisting the guard across a partial valuation changes whether the query
finishes: evaluating first fails on the rejected candidate zero, while guarding
first never values it. Hoisting across a divergence boundary is not an
equivalence for an observer of completion. -/
theorem hoisting_changes_completion :
    eagerPartial (fun candidate => decide (0 < candidate)) undefinedAtZero [0, 1] = none ∧
      hoistedPartial (fun candidate => decide (0 < candidate)) undefinedAtZero [0, 1] =
        some [10] := by
  decide

/-- The completion observer separates the two runs. -/
theorem completion_separates :
    (eagerPartial (fun candidate => decide (0 < candidate)) undefinedAtZero [0, 1]).isSome ≠
      (hoistedPartial (fun candidate => decide (0 < candidate)) undefinedAtZero [0, 1]).isSome := by
  decide

end Partial

#print axioms streamPrefix_hoist_guard
#print axioms liveGuard_retained
#print axioms reuse_of_kept_dependencies
#print axioms reuse_of_kept_dependencies_prefix
#print axioms threshold_adequate
#print axioms irrelevant_revision_reuses
#print axioms relevant_revision_invalidates
#print axioms relevant_revision_not_kept
#print axioms note_selection_not_adequate
#print axioms sum_factors_through_values
#print axioms support_not_factors_through_values
#print axioms support_factors_when_retained
#print axioms count_not_factors_through_dedup
#print axioms hoisting_changes_completion
#print axioms completion_separates

end Mettapedia.GSLT.Dynamics.GuardRevision
