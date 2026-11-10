import Mettapedia.Machines.QueryState
import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic

/-!
# Shared worlds, isolated branches, and observation-qualified reordering

Actions are atomic state services. Shared execution uses the existing adaptive
query interpreter; isolated execution starts each action in the same input
world and retains each separate resulting world. These are abstract policies,
not definitions or equivalence claims for any entire MeTTa or process calculus.

Read-only services agree on ordered answers in these two policies. Writes can
separate them. Within shared execution, commuting updates and stable replies
permit exchanging adjacent actions in any prefix/suffix context, preserving
the answer bag and final world. They do not preserve the first answer. Nor
does commuting final state alone suffice to preserve even the answer bag.

The atomicity assumption is explicit in the action type. No theorem here
implements concurrent publication, resolves races, or derives authority from
channel syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OperatorChoice.WorldProfiles

open Mettapedia.Machines.ReadOnlyQuery (Program)
open Mettapedia.Machines.QueryState (run)

variable {World Reply : Type}

abbrev Action (World Reply : Type) := World → Reply × World

/-- A program making the requested service calls in order. -/
def perform : List (Action World Reply) → Program (Action World Reply) Reply (List Reply)
  | [] => .pure []
  | action :: rest => .read action fun answer =>
      Mettapedia.Machines.ReadOnlyQuery.map (answer :: ·) (perform rest)

/-- Shared execution is a projection of the existing state-threaded evaluator. -/
def shared (actions : List (Action World Reply)) (world : World) : List Reply × World :=
  let result := run (fun state action => action state) (perform actions) world
  (result.answer, result.state)

@[simp] theorem shared_nil (world : World) : shared ([] : List (Action World Reply)) world =
    ([], world) := rfl

theorem shared_cons (action : Action World Reply) (rest : List (Action World Reply))
    (world : World) :
    shared (action :: rest) world =
      let first := action world
      let later := shared rest first.2
      (first.1 :: later.1, later.2) := by
  simp [shared, perform, run, Mettapedia.Machines.QueryState.run_map]

/-- Branch results include their own worlds. There is no implicit merge. -/
def isolated (actions : List (Action World Reply)) (world : World) : List (Reply × World) :=
  actions.map (fun action => action world)

/-- Pure services can use either policy without changing occurrence order,
multiplicity, answers, or the shared world. -/
theorem shared_eq_isolated_of_readOnly (actions : List (Action World Reply))
    (readOnly : ∀ action ∈ actions, ∀ world, (action world).2 = world)
    (world : World) :
    shared actions world = ((isolated actions world).map Prod.fst, world) := by
  induction actions with
  | nil => rfl
  | cons action rest ih =>
      rw [shared_cons]
      dsimp only
      rw [readOnly action (by simp) world]
      have restReadOnly : ∀ next ∈ rest, ∀ state, (next state).2 = state := by
        intro next member
        exact readOnly next (by simp [member])
      rw [ih restReadOnly]
      rfl

theorem shared_append (first second : List (Action World Reply)) (world : World) :
    shared (first ++ second) world =
      let before := shared first world
      let after := shared second before.2
      (before.1 ++ after.1, after.2) := by
  induction first generalizing world with
  | nil => simp
  | cons action rest ih =>
      simp only [List.cons_append, shared_cons, ih, List.cons_append]

/-- Independent actions commute on state and cannot change each other's reply.
These are separate obligations; commuting updates alone is insufficient. -/
structure Independent (first second : Action World Reply) : Prop where
  updates : Function.Commute (fun world => (first world).2) (fun world => (second world).2)
  first_reply : ∀ world, (first (second world).2).1 = (first world).1
  second_reply : ∀ world, (second (first world).2).1 = (second world).1

/-- The local exchange law observes a bag of replies and the reached world. -/
theorem independent_swap (first second : Action World Reply)
    (independent : Independent first second) (rest : List (Action World Reply))
    (world : World) :
    (shared (first :: second :: rest) world).1.Perm
      (shared (second :: first :: rest) world).1 ∧
    (shared (first :: second :: rest) world).2 =
      (shared (second :: first :: rest) world).2 := by
  simp only [shared_cons]
  have updates := independent.updates world
  dsimp only at updates
  rw [independent.second_reply, independent.first_reply, updates]
  exact ⟨List.Perm.swap _ _ _, rfl⟩

/-- The same law holds inside every finite prefix and suffix context.
The suffix resumes the same world, so it may itself have arbitrary effects. -/
theorem independent_swap_in_context (first second : Action World Reply)
    (independent : Independent first second)
    (before after : List (Action World Reply)) (world : World) :
    (shared (before ++ first :: second :: after) world).1.Perm
      (shared (before ++ second :: first :: after) world).1 ∧
    (shared (before ++ first :: second :: after) world).2 =
      (shared (before ++ second :: first :: after) world).2 := by
  rw [shared_append, shared_append]
  have exchanged := independent_swap first second independent after (shared before world).2
  exact ⟨List.Perm.append_left _ exchanged.1, exchanged.2⟩

namespace Controls

def putTrue : Action Bool Bool := fun _ => (true, true)
def readBool : Action Bool Bool := fun world => (world, world)

/-- A later shared read sees the write; the isolated read sees its own input. -/
theorem shared_and_isolated_differ :
    shared [putTrue, readBool] false = ([true, true], true) ∧
    isolated [putTrue, readBool] false = [(true, true), (false, false)] ∧
    (shared [putTrue, readBool] false).1 ≠
      (isolated [putTrue, readBool] false).map Prod.fst := by
  exact ⟨rfl, rfl, by decide⟩

def incrementLeft : Action (Nat × Nat) Nat := fun world =>
  (world.1, (world.1 + 1, world.2))

def incrementRight : Action (Nat × Nat) Nat := fun world =>
  (world.2, (world.1, world.2 + 1))

theorem independent_coordinates : Independent incrementLeft incrementRight := by
  constructor <;> intro world <;> rfl

/-- Nontrivial writes commute and preserve each other's observations, so their
bag and endpoint commute. The ordered first-answer observer still separates them. -/
theorem independent_writes_change_first :
    (shared [incrementLeft, incrementRight] (0, 1)).1.Perm
      (shared [incrementRight, incrementLeft] (0, 1)).1 ∧
    (shared [incrementLeft, incrementRight] (0, 1)).2 = (1, 2) ∧
    (shared [incrementRight, incrementLeft] (0, 1)).2 = (1, 2) ∧
    (shared [incrementLeft, incrementRight] (0, 1)).1.head? ≠
      (shared [incrementRight, incrementLeft] (0, 1)).1.head? := by
  exact ⟨(independent_swap _ _ independent_coordinates [] (0, 1)).1,
    rfl, rfl, by decide⟩

def readCounter : Action Nat Nat := fun world => (world, world)
def incrementCounter : Action Nat Nat := fun world => (world, world + 1)

/-- Equal final states under both orders do not imply equal answer bags. -/
theorem commuting_updates_do_not_preserve_replies :
    Function.Commute (fun world => (readCounter world).2)
      (fun world => (incrementCounter world).2) ∧
    (shared [readCounter, incrementCounter] 0).2 =
      (shared [incrementCounter, readCounter] 0).2 ∧
    ¬ (shared [readCounter, incrementCounter] 0).1.Perm
      (shared [incrementCounter, readCounter] 0).1 := by
  refine ⟨fun _ => rfl, rfl, ?_⟩
  change ¬ ([0, 0] : List Nat).Perm [0, 1]
  intro perm
  have counts := perm.count_eq 0
  simp at counts

end Controls

end Mettapedia.Machines.OperatorChoice.WorldProfiles
