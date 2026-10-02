import Mettapedia.GSLT.Core.DemandExecution
import Mettapedia.Algorithms.CertifiedFiniteChoice

/-!
# Certified publication from a partially explored weighted search

The source semantics is finite operational reachability.  Every source answer
is either already emitted or still reachable from the current residual.
This coverage invariant is proved from the actual expansion algorithm.

Local lower bounds need two structural laws: they bound emissions and are
monotone along generated successors.  These imply bounds for every future
answer, including answers on an infinite search.  A buffered minimum may be
published when it beats all residual bounds, independently of expansion order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.BoundedPublication

open BranchingTemporal
open InferenceControl (Controller)

variable {Node Answer Memory : Type*}

theorem generated_after_expansion (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (frontier : List Node) (picked : Node) (pending : List Node)
    (ordered : scheduler.reorder frontier = picked :: pending) {target : Node}
    (reachable : Generated system frontier target) :
    target = picked ∨ Generated system
      (scheduler.integrate pending (system.successors picked)) target := by
  induction reachable with
  | @root node member =>
      have inOrder : node ∈ picked :: pending := by
        rw [← ordered]
        exact scheduler.mem_reorder_iff.mpr member
      rcases List.mem_cons.mp inOrder with same | retained
      · exact Or.inl same
      · exact Or.inr (.root (scheduler.mem_integrate_iff.mpr (Or.inl retained)))
  | @successor parent child previous next ih =>
      rcases ih with selected | retained
      · subst parent
        exact Or.inr (.root (scheduler.mem_integrate_iff.mpr (Or.inr next)))
      · exact Or.inr (.successor retained next)

/-- Source answers have an emitted receipt or a remaining operational path. -/
def Covers (system : BranchingSystem Node Answer) (roots : List Node)
    (snapshot : BranchingTemporal.Snapshot Node Answer) : Prop :=
  ∀ node answer, Generated system roots node → system.emit node = some answer →
    (⟨node, answer⟩ : Emission Node Answer) ∈ snapshot.events ∨
      Generated system snapshot.frontier node

theorem initial_covers (system : BranchingSystem Node Answer) (roots : List Node) :
    Covers system roots (BranchingTemporal.initial roots) := by
  intro node answer reachable _
  exact Or.inr reachable

theorem covers_tick (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (snapshot : BranchingTemporal.Snapshot Node Answer)
    (covers : Covers system roots snapshot) :
    Covers system roots (BranchingTemporal.tick system scheduler snapshot) := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simpa [BranchingTemporal.tick, ordered] using covers
  | cons picked pending =>
      intro node answer reachable emits
      rcases covers node answer reachable emits with emitted | remaining
      · exact Or.inl ((BranchingTemporal.events_prefix_tick system scheduler snapshot).subset
          emitted)
      · rcases generated_after_expansion system scheduler snapshot.frontier picked pending
          ordered remaining with selected | retained
        · subst node
          apply Or.inl
          exact BranchingTemporal.event_mem_tick_of_selected system scheduler snapshot
            (by simp [BranchingTemporal.selected, ordered]) emits
        · exact Or.inr (by simpa [BranchingTemporal.tick, ordered] using retained)

theorem covers_controlled_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node) (fuel : Nat) :
    Covers system roots (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search := by
  induction fuel with
  | zero => exact initial_covers system roots
  | succ fuel ih =>
      exact covers_tick system
        (controller.scheduler (InferenceControl.Snapshot.run system controller fuel
          (InferenceControl.Snapshot.initial controller roots)).memory) roots _ ih

theorem covers_demand_run (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (roots : List Node)
    (goal : List Answer → Bool) (fuel : Nat) :
    Covers system roots (DemandExecution.run system controller goal fuel
      (InferenceControl.Snapshot.initial controller roots)).search := by
  obtain ⟨used, _, same⟩ := DemandExecution.run_prefix system controller goal fuel
    (InferenceControl.Snapshot.initial controller roots)
  rw [same]
  exact covers_controlled_run system controller roots used

/-- Structural lower-bound conditions, checked on local transitions. -/
structure LocalBounds (system : BranchingSystem Node Answer)
    (cost : Answer → Nat) (bound : Node → Nat) : Prop where
  emission : ∀ node answer, system.emit node = some answer → bound node ≤ cost answer
  successor : ∀ node child, child ∈ system.successors node → bound node ≤ bound child

theorem generated_bound (system : BranchingSystem Node Answer) (cost : Answer → Nat)
    (bound : Node → Nat) (valid : LocalBounds system cost bound) (roots : List Node)
    {node : Node} (reachable : Generated system roots node) :
    ∃ root ∈ roots, bound root ≤ bound node := by
  induction reachable with
  | @root node member => exact ⟨node, member, le_rfl⟩
  | @successor parent child previous next ih =>
      obtain ⟨root, member, earlier⟩ := ih
      exact ⟨root, member, earlier.trans (valid.successor parent child next)⟩

def checkResidual (cost : Answer → Nat) (bound : Node → Nat)
    (candidate : Answer) (frontier : List Node) : Bool :=
  frontier.all (fun node => decide (cost candidate ≤ bound node))

/-- The finite root check bounds all uncomputed descendants. -/
theorem checkResidual_sound (system : BranchingSystem Node Answer) (cost : Answer → Nat)
    (bound : Node → Nat) (valid : LocalBounds system cost bound)
    (candidate : Answer) (frontier : List Node)
    (checked : checkResidual cost bound candidate frontier = true)
    {node : Node} {answer : Answer} (reachable : Generated system frontier node)
    (emits : system.emit node = some answer) : cost candidate ≤ cost answer := by
  obtain ⟨root, member, earlier⟩ := generated_bound system cost bound valid frontier reachable
  have rootBound : cost candidate ≤ bound root := by
    exact of_decide_eq_true ((List.all_eq_true.mp checked) root member)
  exact rootBound.trans (earlier.trans (valid.emission node answer emits))

/-- Compute a buffered minimum, then check the residual.  An unproved
heuristic priority is not used as a lower bound. -/
def publishMinimum (cost : Answer → Nat) (bound : Node → Nat)
    (snapshot : BranchingTemporal.Snapshot Node Answer) : Option Answer :=
  match Algorithms.CertifiedFiniteChoice.chooseBest (fun answer => -(cost answer : Rat))
      (snapshot.events.map Emission.value) with
  | none => none
  | some candidate => if checkResidual cost bound candidate snapshot.frontier
      then some candidate else none

theorem publishMinimum_correct (system : BranchingSystem Node Answer)
    (cost : Answer → Nat) (bound : Node → Nat) (valid : LocalBounds system cost bound)
    (roots : List Node) (snapshot : BranchingTemporal.Snapshot Node Answer)
    (covers : Covers system roots snapshot) (sound : snapshot.Sound system roots)
    (candidate : Answer) (published : publishMinimum cost bound snapshot = some candidate) :
    (∃ node, Generated system roots node ∧ system.emit node = some candidate) ∧
      ∀ node answer, Generated system roots node → system.emit node = some answer →
        cost candidate ≤ cost answer := by
  cases winner : Algorithms.CertifiedFiniteChoice.chooseBest
      (fun answer => -(cost answer : Rat)) (snapshot.events.map Emission.value) with
  | none => simp [publishMinimum, winner] at published
  | some chosen =>
      have checked : checkResidual cost bound chosen snapshot.frontier = true := by
        by_contra refuses
        simp [publishMinimum, winner, refuses] at published
      have same : chosen = candidate := by
        simpa [publishMinimum, winner, checked] using published
      subst chosen
      obtain ⟨included, minimal⟩ := Algorithms.CertifiedFiniteChoice.chooseBest_correct
        (fun answer => -(cost answer : Rat)) (snapshot.events.map Emission.value)
          candidate winner
      obtain ⟨event, emitted, value⟩ := List.mem_map.mp included
      refine ⟨⟨event.origin, (sound.2 event emitted).1, ?_⟩, ?_⟩
      · rw [← value]
        exact (sound.2 event emitted).2
      · intro node answer reachable emits
        rcases covers node answer reachable emits with observed | remaining
        · have compare := minimal answer (List.mem_map.mpr
            ⟨⟨node, answer⟩, observed, rfl⟩)
          have rational : (cost candidate : Rat) ≤ cost answer := by linarith
          exact_mod_cast rational
        · exact checkResidual_sound system cost bound valid candidate snapshot.frontier
            checked remaining emits

/-- Publication safety holds for any lawful controller, including protected
age turns which explore an expensive branch before a cheaper one. -/
theorem controlled_publication_correct (system : BranchingSystem Node Answer)
    (controller : Controller Node Answer Memory) (cost : Answer → Nat) (bound : Node → Nat)
    (valid : LocalBounds system cost bound) (roots : List Node) (fuel : Nat)
    (candidate : Answer)
    (published : publishMinimum cost bound (InferenceControl.Snapshot.run system controller fuel
      (InferenceControl.Snapshot.initial controller roots)).search = some candidate) :
    (∃ node, Generated system roots node ∧ system.emit node = some candidate) ∧
      ∀ node answer, Generated system roots node → system.emit node = some answer →
        cost candidate ≤ cost answer := by
  apply publishMinimum_correct system cost bound valid roots _
    (covers_controlled_run system controller roots fuel)
    (InferenceControl.Snapshot.sound_run system controller
      (BranchingTemporal.initial_sound system roots) fuel) candidate published

namespace Controls

inductive Work where
  | start | expensive | delayed | cheap | later
  deriving DecidableEq, Repr

def system : BranchingSystem Work Nat where
  emit
    | .expensive => some 8
    | .cheap => some 2
    | .later => some 9
    | _ => none
  successors
    | .start => [.expensive, .delayed]
    | .delayed => [.cheap, .later]
    | _ => []

def bound : Work → Nat
  | .start => 0
  | .expensive => 8
  | .delayed => 2
  | .cheap => 2
  | .later => 9

theorem localBounds : LocalBounds system id bound := by
  constructor
  · intro node answer emits
    cases node <;> simp_all [system, bound]
  · intro node child member
    cases node <;> cases child <;> simp_all [system, bound]

def controller : Controller Work Nat Unit := Controller.fixed Scheduler.breadthFirst

example : publishMinimum id bound (InferenceControl.Snapshot.run system controller 2
    (InferenceControl.Snapshot.initial controller [.start])).search = none := by decide

/-- The cheap answer is certified while a more costly branch is still live. -/
example : publishMinimum id bound (InferenceControl.Snapshot.run system controller 4
    (InferenceControl.Snapshot.initial controller [.start])).search = some 2 := by decide

example : (InferenceControl.Snapshot.run system controller 4
    (InferenceControl.Snapshot.initial controller [.start])).search.frontier = [.later] := by decide

/-- An invented bound can pass the finite check and publish a wrong minimum.
Its failure of the structural contract is independently checked. -/
def invalidBound : Work → Nat := fun _ => 10

example : ¬ LocalBounds system id invalidBound := by
  intro valid
  have impossible := valid.emission Work.cheap 2 rfl
  simp [invalidBound] at impossible

example : publishMinimum id invalidBound (InferenceControl.Snapshot.run system controller 2
    (InferenceControl.Snapshot.initial controller [.start])).search = some 8 := by decide

end Controls

end Mettapedia.GSLT.Core.BoundedPublication
