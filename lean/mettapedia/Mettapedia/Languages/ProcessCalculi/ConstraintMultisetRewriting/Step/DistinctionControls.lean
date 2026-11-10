import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DistinctionMinimization

/-!
# Distinction/transform controls from MeTTaDinC

The eight-state machine has three bits, observes the first, and swaps the
first two. Keeping the first bit fails; keeping the first two is the exact
coarsest behavioural quotient. The access-protocol example distinguishes
exact induction from a sound nondeterministic over-approximation. A disabled
action control checks that availability is observable in branching semantics.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite.Controls
open Machine

abbrev Bits := Bool × Bool × Bool
def swap (s : Bits) : Bits := (s.2.1, s.1, s.2.2)
def keepAB (s : Bits) : Bool × Bool := (s.1, s.2.1)
def eight : Machine Bits Unit Bool := ⟨Prod.fst, fun s _ => [swap s]⟩

theorem keepA_refused : eight.checkEncoding Prod.fst = false := by decide
theorem keepAB_checked : eight.checkEncoding keepAB = true := by decide

theorem keepA_separating_pair :
    (false, false, false).1 = (false, true, false).1 ∧
      (swap (false, false, false)).1 ≠ (swap (false, true, false)).1 := by decide

theorem keepAB_exact : eight.ExactEncoding keepAB :=
  (eight.checkEncoding_exact keepAB).mp keepAB_checked

def abRelation : Finset (Bits × Bits) := Finset.univ.filter fun p => keepAB p.1 = keepAB p.2

theorem behaviour_is_ab : eight.behaviour = abRelation := by
  apply Finset.Subset.antisymm
  · intro p related
    have first := eight.behaviour_preserves related
    have good := eight.stable_good eight.behaviour_stable related
    obtain ⟨target, member, nextRelated⟩ := (good.2 ()).1 (swap p.1) (List.mem_singleton_self _)
    have eqn : target = swap p.2 := List.mem_singleton.mp member
    subst target
    have second := eight.behaviour_preserves nextRelated
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext first second⟩
  · exact eight.behaviour_greatest ((eight.checkEncoding_iff keepAB).mp keepAB_checked)

def classes : Finset (Finset Bits) := Finset.univ.image fun s =>
  Finset.univ.filter fun t => (s, t) ∈ eight.behaviour

theorem exactly_four_classes : classes.card = 4 := by
  unfold classes
  rw [behaviour_is_ab]
  decide

/-- Extra hidden bit retained in the source, while the exact quotient still runs. -/
theorem swap_is_actual_firing :
    Race.Generic.Moves eight.step.toStep Machine.offers (0, (false, true, false)) ()
      (1, (true, false, false)) :=
  eight.every_successor_fires _ _ _ (List.mem_singleton_self _)

theorem no_invented_swap :
    ¬ Race.Generic.Moves eight.step.toStep Machine.offers (0, (false, true, false)) ()
      (1, (true, true, false)) := by
  intro move
  have member := eight.no_extra_successor _ _ _ move
  simp [eight, swap] at member

def availability : Machine Bool Unit Unit :=
  ⟨fun _ => (), fun s _ => if s then [s] else []⟩

theorem same_readout_not_same_availability :
    availability.read false = availability.read true ∧
      availability.checkEncoding (fun _ => ()) = false := by decide

inductive Login where
  | s0 | s1 | s2 | locked | auth | admin
  deriving DecidableEq, Fintype, Repr
inductive Stage where
  | start | locked | auth | admin
  deriving DecidableEq, Fintype, Repr
inductive Action where
  | fail | ok | escalate
  deriving DecidableEq, Fintype, Repr

def stage : Login → Stage
  | .s0 | .s1 | .s2 => .start
  | .locked => .locked
  | .auth => .auth
  | .admin => .admin

def accessNext : Login → Action → Login
  | .s0, .fail => .s1
  | .s1, .fail => .s2
  | .s2, .fail => .locked
  | .s0, .ok | .s1, .ok | .s2, .ok => .auth
  | .auth, .escalate => .admin
  | s, _ => s

def access : Machine Login Action Stage := ⟨stage, fun s a => [accessNext s a]⟩

def accessAbstract : Machine Stage Action Stage := ⟨id, fun s a =>
  match s, a with
  | .start, .fail => [.start, .locked]
  | .start, .ok => [.auth]
  | .auth, .escalate => [.admin]
  | s, _ => [s]⟩

theorem access_not_exact : access.checkEncoding stage = false := by decide

/-- Forward simulation is useful, but is weaker than an exact quotient. -/
theorem access_simulation : ∀ s a t, t ∈ access.next s a → stage t ∈ accessAbstract.next (stage s) a := by
  decide

/-- The abstract lockout is spurious from this particular concrete representative. -/
theorem access_extra_behaviour :
    Stage.locked ∈ accessAbstract.next (stage Login.s0) .fail ∧
      ¬ ∃ t ∈ access.next .s0 .fail, stage t = .locked := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DistinctionFinite.Controls
