import Mettapedia.GSLT.Core.DemandExecution
import Mettapedia.Algorithms.CertifiedFiniteChoice
import Mathlib.Data.List.Sublists

/-!
# Complete joint selection from an observed occurrence stream

The selector searches every collection of a prescribed size.  Its witness
predicate is independent of the selection algorithm.  A failed finite prefix
is not an impossibility result for an unfinished source computation.

For streaming liveness, a goal must be invariant under permutation of its
witness collection.  Fair enumeration then eventually exposes every finite
reachable collection, including collections whose members have equal values
but distinct occurrence identities.  No greedy commitment is required.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.JointDemand

open BranchingTemporal
open InferenceControl (Controller)

variable {Answer Node Memory : Type*}

/-- An independently stated joint witness obligation. -/
def Witness (goal : List Answer → Bool) (requested : Nat)
    (seen chosen : List Answer) : Prop :=
  chosen.Sublist seen ∧ chosen.length = requested ∧ goal chosen = true

/-- Enumerate collections, retaining occurrence positions and alternatives. -/
def candidates (goal : List Answer → Bool) (requested : Nat)
    (seen : List Answer) : List (List Answer) :=
  (List.sublistsLen requested seen).filter goal

theorem mem_candidates_iff (goal : List Answer → Bool) (requested : Nat)
    (seen chosen : List Answer) :
    chosen ∈ candidates goal requested seen ↔ Witness goal requested seen chosen := by
  simp only [candidates, List.mem_filter, List.mem_sublistsLen, Witness]
  tauto

def select (goal : List Answer → Bool) (requested : Nat)
    (seen : List Answer) : Option (List Answer) :=
  (List.sublistsLen requested seen).find? goal

theorem select_sound (goal : List Answer → Bool) (requested : Nat)
    (seen chosen : List Answer) (found : select goal requested seen = some chosen) :
    Witness goal requested seen chosen := by
  have included := List.mem_sublistsLen.mp (List.mem_of_find?_eq_some found)
  exact ⟨included.1, included.2, List.find?_some found⟩

/-- Exhausting all collections proves absence among the seen occurrences. -/
theorem select_none_iff (goal : List Answer → Bool) (requested : Nat)
    (seen : List Answer) :
    select goal requested seen = none ↔ ¬ ∃ chosen, Witness goal requested seen chosen := by
  rw [select, List.find?_eq_none]
  constructor
  · intro empty ⟨chosen, sublist, count, accepts⟩
    exact empty chosen (List.mem_sublistsLen.mpr ⟨sublist, count⟩) accepts
  · intro impossible chosen included accepts
    have member := List.mem_sublistsLen.mp included
    exact impossible ⟨chosen, member.1, member.2, accepts⟩

def enough (goal : List Answer → Bool) (requested : Nat) (seen : List Answer) : Bool :=
  (select goal requested seen).isSome

theorem enough_iff (goal : List Answer → Bool) (requested : Nat) (seen : List Answer) :
    enough goal requested seen = true ↔ ∃ chosen, Witness goal requested seen chosen := by
  cases result : select goal requested seen with
  | none =>
      have absent := (select_none_iff goal requested seen).mp result
      simp [enough, result, absent]
  | some chosen =>
      have accepts := select_sound goal requested seen chosen result
      constructor
      · intro _
        exact ⟨chosen, accepts⟩
      · intro _
        simp [enough, result]

/-- Earlier solutions remain available when more occurrences are emitted. -/
theorem witness_mono (goal : List Answer → Bool) (requested : Nat)
    {early later chosen : List Answer} (extended : early.Sublist later)
    (witness : Witness goal requested early chosen) :
    Witness goal requested later chosen :=
  ⟨witness.1.trans extended, witness.2⟩

theorem enough_mono (goal : List Answer → Bool) (requested : Nat)
    {early later : List Answer} (extended : early.Sublist later)
    (satisfied : enough goal requested early = true) :
    enough goal requested later = true := by
  obtain ⟨chosen, witness⟩ := (enough_iff goal requested early).mp satisfied
  exact (enough_iff goal requested later).mpr
    ⟨chosen, witness_mono goal requested extended witness⟩

/-- This maximizes a joint score over the complete seen collection family.
It makes no claim that an open stream contains no better future collection. -/
def bestInPrefix (goal : List Answer → Bool) (requested : Nat)
    (score : List Answer → ℚ) (seen : List Answer) : Option (List Answer) :=
  Algorithms.CertifiedFiniteChoice.chooseBest score (candidates goal requested seen)

theorem bestInPrefix_correct (goal : List Answer → Bool) (requested : Nat)
    (score : List Answer → ℚ) (seen chosen : List Answer)
    (found : bestInPrefix goal requested score seen = some chosen) :
    Witness goal requested seen chosen ∧
      ∀ other, Witness goal requested seen other → score other ≤ score chosen := by
  obtain ⟨included, maximal⟩ := Algorithms.CertifiedFiniteChoice.chooseBest_correct
    score (candidates goal requested seen) chosen found
  refine ⟨(mem_candidates_iff goal requested seen chosen).mp included, ?_⟩
  intro other witness
  exact maximal other ((mem_candidates_iff goal requested seen other).mpr witness)

/-- The finite witness goal treats a collection independently of enumeration
order.  Order-sensitive stream goals use their own stronger contract. -/
def OrderIndependent (goal : List Answer → Bool) : Prop :=
  ∀ first second : List Answer, first.Perm second → goal first = goal second

/-- Every required obligation has a retained witness.  The predicate may use
the witness's path, bindings or provenance instead of only its result value. -/
def coverageGoal {Obligation : Type*} (covers : Answer → Obligation → Bool)
    (required : List Obligation) (chosen : List Answer) : Bool :=
  required.all (fun obligation => chosen.any (fun answer => covers answer obligation))

theorem coverage_orderIndependent {Obligation : Type*}
    (covers : Answer → Obligation → Bool) (required : List Obligation) :
    OrderIndependent (coverageGoal covers required) := by
  intro first second same
  unfold coverageGoal
  have predicates :
      (fun obligation => first.any (fun answer => covers answer obligation)) =
      (fun obligation => second.any (fun answer => covers answer obligation)) := by
    funext obligation
    exact same.any_eq
  rw [predicates]

/-- A forbidden family cannot be present in its entirety.  Pairs express
ordinary conflicts; larger families express joint resource constraints. -/
def compatibleGoal [DecidableEq Answer] (forbidden : List (List Answer))
    (chosen : List Answer) : Bool :=
  forbidden.all (fun group => !group.all (fun answer => decide (answer ∈ chosen)))

theorem compatible_orderIndependent [DecidableEq Answer]
    (forbidden : List (List Answer)) : OrderIndependent (compatibleGoal forbidden) := by
  intro first second same
  simp only [compatibleGoal, same.mem_iff]

def coverageCompatibleGoal {Obligation : Type*} [DecidableEq Answer]
    (covers : Answer → Obligation → Bool) (required : List Obligation)
    (forbidden : List (List Answer)) (chosen : List Answer) : Bool :=
  coverageGoal covers required chosen && compatibleGoal forbidden chosen

theorem coverageCompatible_orderIndependent {Obligation : Type*} [DecidableEq Answer]
    (covers : Answer → Obligation → Bool) (required : List Obligation)
    (forbidden : List (List Answer)) :
    OrderIndependent (coverageCompatibleGoal covers required forbidden) := by
  intro first second same
  simp only [coverageCompatibleGoal,
    coverage_orderIndependent covers required first second same,
    compatible_orderIndependent forbidden first second same]

/-- A collection exposed in another order has a selectable representative
with the same multiplicities. -/
theorem enough_of_subperm (goal : List Answer → Bool) (orderIndependent : OrderIndependent goal)
    (requested : Nat) (seen witnesses : List Answer)
    (included : witnesses.Subperm seen) (count : witnesses.length = requested)
    (accepts : goal witnesses = true) : enough goal requested seen = true := by
  obtain ⟨representative, same, sublist⟩ := included
  apply (enough_iff goal requested seen).mpr
  exact ⟨representative, sublist, same.length_eq.trans count,
    (orderIndependent representative witnesses same).trans accepts⟩

/-- Fair source enumeration eventually satisfies every finite reachable
joint goal.  The witness collection is retained as an alternative, not fixed
by accepting an earlier locally attractive occurrence. -/
theorem fair_joint_liveness
    (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (fair : InferenceControl.Snapshot.FairFrom system controller roots)
    (goal : List Answer → Bool) (orderIndependent : OrderIndependent goal)
    (requested : Nat) (witnesses : List (Emission Node Answer))
    (distinct : witnesses.Nodup)
    (count : witnesses.length = requested)
    (accepts : goal (witnesses.map Emission.value) = true)
    (valid : ∀ event ∈ witnesses, EventValid system roots event) :
    ∃ fuel, DemandExecution.satisfied (enough goal requested)
      (DemandExecution.run system controller (enough goal requested) fuel
        (InferenceControl.Snapshot.initial controller roots)) = true := by
  obtain ⟨fuel, subset⟩ :=
    DemandExecution.reachable_events_cooccur system controller roots fair witnesses valid
  refine ⟨fuel, DemandExecution.satisfied_of_full_run system controller
    (enough goal requested) fuel _ ?_⟩
  apply enough_of_subperm goal orderIndependent requested _
    (witnesses.map Emission.value)
  · obtain ⟨representative, same, sublist⟩ := distinct.subperm subset
    exact ⟨representative.map Emission.value, same.map Emission.value,
      sublist.map Emission.value⟩
  · simpa using count
  · exact accepts

namespace Controls

/-- Routes 0 and 1 cover the same obligation; routes 2 through 7 cover the
remaining six.  The first seven therefore fail, although seven can suffice. -/
def coveredObligation (route : Nat) : Nat :=
  if route = 0 then 0 else route - 1

def coversSeven (routes : List Nat) : Bool :=
  (List.range 7).all (fun obligation =>
    routes.any (fun route => decide (coveredObligation route = obligation)))

example : coversSeven ((List.range 8).take 7) = false := by decide
example : enough coversSeven 7 (List.range 8) = true := by decide
example : select coversSeven 7 (List.range 7) = none := by decide

/-- A locally attractive first route conflicts with both members of the
valid pair.  Complete collection search retains the pair as an alternative. -/
def compatiblePair (routes : List Nat) : Bool :=
  decide (1 ∈ routes ∧ 2 ∈ routes ∧ 0 ∉ routes)

example : compatiblePair [0, 1] = false := by decide
example : select compatiblePair 2 [0, 1, 2] = some [1, 2] := by decide

/-- Equal answer values at different occurrence positions remain usable. -/
example : select (fun routes : List Nat => decide (routes = [4, 4])) 2 [4, 4] =
    some [4, 4] := by decide

end Controls

end Mettapedia.GSLT.Core.JointDemand
