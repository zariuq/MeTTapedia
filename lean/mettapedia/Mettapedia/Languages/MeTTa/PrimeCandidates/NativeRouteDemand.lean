import Mettapedia.Languages.MeTTa.PrimeCandidates.NativeObservationScopes
import Mettapedia.GSLT.Core.FiniteSearchCertificate
import Mettapedia.GSLT.Core.ResumableJointSelection
import Mettapedia.GSLT.Scope.ConsumerDescent
import Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.SubmodularCoverageGreedy

/-!
# Bound route computations and their joint observation

The route source is an authored equation graph with two branches, eight
physical alternatives and a shared lazy trunk computation in each path.
The clients observe actual Need evaluation before selecting a collection.
The collection search uses the existing include/exclude work machine.

Executable finite source certificates derive residual bags and sufficient
exhaustion allowances. They are verification evidence, not a requirement to
enumerate the complete source before answering a live query.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeRouteDemand

open NativeEquationNeed
open NativeEquationNeed.Controls (integer call)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Core
open BranchingTemporal
open InferenceControl

def routeBody (identity : Nat) : Atom :=
  call "let" [.var "shared", call "trunk" [.var "seed"],
    call "Route" [integer identity, call "Pair" [.var "shared", .var "shared"],
      integer (if identity ≤ 1 then 0 else identity - 1)]]

def program : Program :=
  [⟨"paths", ["seed"], call "left" [.var "seed"]⟩,
   ⟨"paths", ["seed"], call "right" [.var "seed"]⟩,
   ⟨"trunk", ["seed"], call "+" [.var "seed", integer 1]⟩] ++
  (List.range 8).map (fun identity =>
    ⟨if identity ≤ 1 then "left" else "right", ["seed"], routeBody identity⟩)

def query (seed : Int) : Atom := call "paths" [integer seed]

def expected (seed : Int) (identity : Nat) : Atom :=
  call "Route" [integer identity, call "Pair" [integer (seed + 1), integer (seed + 1)],
    integer (if identity ≤ 1 then 0 else identity - 1)]

def root (seed : Int) := WorkOccurrence.root (initial (query seed))

def covers (route : Atom) (obligation : Nat) : Bool :=
  match route with
  | .expression [.symbol "Route", _, _, .grounded (.int represented)] =>
      represented == Int.ofNat obligation
  | _ => false

def identity? : Atom → Option Int
  | .expression [.symbol "Route", .grounded (.int identity), _, _] => some identity
  | _ => none

def coversAll : List Atom → Bool := JointDemand.coverageGoal covers (List.range 7)

def compatible (collection : List Atom) : Bool :=
  !(collection.any (fun route => identity? route == some 0) &&
    collection.any (fun route => identity? route == some 7))

def jointGoal (collection : List Atom) : Bool := coversAll collection && compatible collection

/-- Coverage and compatibility guide partial collections without discarding
them. Including a route changes which obligations remain uncovered. -/
def jointPriority (collection : List Atom) : Nat :=
  (if compatible collection then 0 else 8) +
    ((List.range 7).filter fun obligation =>
      !(collection.any fun route => covers route obligation)).length

def any (seed : Int) (requested allowance : Nat) : List Atom :=
  values program (query seed) requested allowance

def joint (seed : Int) (sourceAllowance collectionAllowance : Nat) :=
  let seen := any seed 8 sourceAllowance
  ResumableJointSelection.run jointGoal
    (ResumableJointSelection.adaptiveController jointPriority) collectionAllowance
    (Snapshot.initial (ResumableJointSelection.adaptiveController jointPriority)
      [ResumableJointSelection.initial 7 seen])

/-- The collection verifier searches actual computed routes and agrees with
the independent finite collection specification, including rejected siblings. -/
theorem completed_joint_correct (seed : Int) (allowance : Nat) :
    let seen := any seed 8 allowance
    let roots := [ResumableJointSelection.initial 7 seen]
    let budget := foldRanks (WellFoundedSearch.descent
      (ResumableJointSelection.system jointGoal) (ResumableJointSelection.depth jointGoal)).rank roots
    let result := Snapshot.run (ResumableJointSelection.system jointGoal)
      (ResumableJointSelection.adaptiveController jointPriority) budget
      (Snapshot.initial (ResumableJointSelection.adaptiveController jointPriority) roots)
    result.search.frontier = [] ∧ eventBag result.search.events =
      (JointDemand.candidates jointGoal 7 seen : Multiset (List Atom)) :=
  ResumableJointSelection.adaptive_complete jointGoal jointPriority 7 (any seed 8 allowance)

/-- The two routes initially have equal coverage. After choosing route zero,
its duplicate loses to the route covering the next obligation. -/
theorem partial_selection_changes_priority :
    jointPriority [expected 4 1] = jointPriority [expected 4 2] ∧
      jointPriority [expected 4 0, expected 4 2] <
        jointPriority [expected 4 0, expected 4 1] := by decide +kernel

/-- A concrete native pause retains the source occurrence frontier, controller
memory, heaps and return frames. Its finite bag is constructed from source
steps, rather than supplied as an additive-correspondence hypothesis. -/
theorem native_residual_account (seed : Int) (depth allowance : Nat)
    (certified : FiniteSearchCertificate.Certified (occurrenceSystem program) depth (root seed))
    (goal : List (Outcome × List Nat) → Bool) :
    FiniteSearchCertificate.account (occurrenceSystem program) depth
      (DemandExecution.run (occurrenceSystem program)
        (Controller.fixed Scheduler.breadthFirst) goal allowance
        (Snapshot.initial (Controller.fixed Scheduler.breadthFirst) [root seed])).search =
      FiniteSearchCertificate.finiteBag (occurrenceSystem program) depth (root seed) := by
  have accounted := FiniteSearchCertificate.demanded_account (occurrenceSystem program) depth
    (Controller.fixed Scheduler.breadthFirst) [root seed]
    (by intro node member; simpa using List.mem_singleton.mp member ▸ certified)
    goal allowance (Snapshot.initial (Controller.fixed Scheduler.breadthFirst) [root seed])
    (initial_sound _ _)
  simpa [FiniteSearchCertificate.account, Snapshot.initial, BranchingTemporal.initial,
    eventBag, foldValues] using accounted

theorem source_exhaustion (seed : Int) (depth : Nat)
    (certified : FiniteSearchCertificate.Certified (occurrenceSystem program) depth (root seed))
    {Memory : Type*}
    (controller : Controller (WorkOccurrence NativeMachine) (Outcome × List Nat) Memory) :
    (Snapshot.run (occurrenceSystem program) controller
      (FiniteSearchCertificate.finiteWork (occurrenceSystem program) depth (root seed))
      (Snapshot.initial controller [root seed])).search.frontier = [] := by
  simpa [foldRanks] using FiniteSearchCertificate.completes_at_work
    (occurrenceSystem program) depth controller [root seed]
    (by intro node member; simpa using List.mem_singleton.mp member ▸ certified)

/- The erased view retains the trunk result but forgets path and obligation
identity. Existence descends, distinct-route and joint consumers do not. -/
def payload : Atom → Atom
  | .expression [.symbol "Route", _, value, _] => value
  | other => other

def view (routes : List Atom) : List Atom := routes.map payload

def existsRoute (routes : List Atom) : Bool := !routes.isEmpty

theorem existence_descends :
    Mettapedia.GSLT.Core.NonFactorization.Factors view existsRoute :=
  ⟨fun values => !values.isEmpty, fun routes => by simp [view, existsRoute]⟩

def distinctSeven (routes : List Atom) : Bool :=
  decide (7 ≤ (routes.filterMap identity?).eraseDups.length)

def allRoutes : List Atom := (List.range 8).map (expected 4)
def duplicates : List Atom := List.replicate 8 (expected 4 0)

theorem distinct_does_not_descend :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors view distinctSeven := by
  intro factor
  have same : view allRoutes = view duplicates := by decide +kernel
  have wrong := factor.constantOnFibers allRoutes duplicates same
  have separate : distinctSeven allRoutes ≠ distinctSeven duplicates := by decide +kernel
  exact separate wrong

theorem joint_does_not_descend :
    ¬ Mettapedia.GSLT.Core.NonFactorization.Factors view coversAll := by
  intro factor
  have same : view allRoutes = view duplicates := by decide +kernel
  have wrong := factor.constantOnFibers allRoutes duplicates same
  have separate : coversAll allRoutes ≠ coversAll duplicates := by decide +kernel
  exact separate wrong

namespace CoverageApproximation

open Mettapedia.MachineLearning.SearchGuidance.ProgramDiscovery.AdaptivePortfolio

/-- The portfolio retains physical route identity while coverage counts each
obligation only once. This utility does not encode compatibility. -/
def model : PortfolioModel Unit (Fin 8) (Fin 7) where
  arms := Finset.univ
  accepted _ identity := Finset.univ.filter fun obligation =>
    covers (expected 4 identity.val) obligation.val
  armBudget := 7
  primaryBP := 0
  opportunityBP := 1
  primaryBP_mem := Finset.mem_univ _
  opportunityBP_mem := Finset.mem_univ _
  bpArms_distinct := by decide

theorem actual_routes : any 4 8 3000 = allRoutes := by decide +kernel

/-- Targets are read from the result of the authored Need program. They are
not an unverified catalogue supplied to a coverage selector. -/
theorem accepted_iff_native_target (identity : Fin 8) (obligation : Fin 7) :
    obligation ∈ model.accepted () identity ↔
      covers ((any 4 8 3000)[identity.val]?.getD (.symbol "missing"))
        obligation.val = true := by
  rw [actual_routes]
  fin_cases identity <;> fin_cases obligation <;> decide +kernel

def chosen : Nat → Fin 8
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 5
  | 5 => 6
  | _ => 7

/-- Only the seven actual rounds are required; later repeated selections are
irrelevant and cannot satisfy the distinct-arm greedy contract. -/
theorem finite_greedy_run : IsMarginalGreedyRun model () chosen 7 := by
  intro step before
  interval_cases step <;> unfold IsMarginalGreedyStep <;> decide +kernel

theorem coverage_bound (comparator : Finset (Fin 8))
    (feasible : Feasible model comparator) :
    (1 - ((6 / 7 : ℝ) ^ 7)) *
      (verifiedUnionCoverage model () comparator : ℝ) ≤
        (verifiedUnionCoverage model () (greedyPrefix chosen 7) : ℝ) := by
  have bound := greedyPrefix_coverage_ge_finiteFactor
    model () chosen comparator (by decide) feasible 7 finite_greedy_run
  norm_num [model] at bound ⊢
  exact bound

def greedyRoutes : List Atom :=
  (List.range 7).map fun round => expected 4 (chosen round).val

theorem greedy_routes_represent_prefix :
    greedyRoutes.toFinset = (greedyPrefix chosen 7).image
      (fun identity => expected 4 identity.val) := by decide +kernel

theorem greedy_covers_all : coversAll greedyRoutes = true := by decide +kernel
theorem greedy_is_incompatible : jointGoal greedyRoutes = false := by decide +kernel
theorem exact_joint_finds_compatible :
    (joint 4 3000 1000).search.events.length = 1 := by decide +kernel

end CoverageApproximation

namespace Controls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

example : any 4 8 3000 = allRoutes := by decide +kernel
example : any 4 7 3000 = allRoutes.take 7 := by decide +kernel
example : JointDemand.select coversAll 7 (any 4 7 3000) = none := by decide +kernel
example : (JointDemand.select coversAll 7 (any 4 8 3000)).isSome = true := by decide +kernel

/- The locally attractive route zero excludes the necessary final route;
the resumable exact search finds the sibling solution using route one. -/
example : jointGoal (allRoutes.take 7) = false := by decide +kernel
example : (joint 4 3000 1000).search.events.length = 1 := by decide +kernel
example : (joint 4 3000 1).search.frontier ≠ [] := by decide +kernel

example : (FiniteSearchCertificate.build (occurrenceSystem program) 100 (root 4)).isSome = false :=
  by decide +kernel
example : (FiniteSearchCertificate.build (occurrenceSystem program) 400 (root 4)).isSome = true :=
  by decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeRouteDemand
