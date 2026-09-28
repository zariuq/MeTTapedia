import Mettapedia.Machines.Cursor.FairObservation

/-!
# Search-order qualification for bounded and effectful observations

The actual native bounded collector distinguishes a completed answer bag from
an ordered prefix, a first answer, and the world produced while obtaining it.
All answer types remain generic: these laws apply to learned closures and
proof witnesses as well as first-order values.

Changing the order of two total, pure guards over one fixed candidate sequence
is justified below. Changing candidate generation, divergence, or observable
effects is a different transformation. Equal complete answer bags alone do
not justify it. The branching canary uses the existing search machine and the
same transition system under two schedulers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ObservationOrder

open Mettapedia.GSLT.LanguageDef
open HostCalls (Pull)
open NativeControlBoundedCursor (collectBounded)
open NativeControlEffectCursor (collectCounted)

variable {Answer : Type}

/-- Enumerate occurrences without evaluating their payloads, and record each
delivered occurrence in the world. The world makes order observable. -/
def listPull : List Answer → List Answer → List Answer × Pull (List Answer) Answer
  | [], world => (world, .done)
  | answer :: rest, world => (world ++ [answer], .yield answer rest)

/-- Full collection retains order, multiplicity, terminal effects and the
terminal poll receipt. No set quotient is used by the enumerator. -/
theorem list_collect_all (answers world : List Answer) :
    collectCounted listPull (answers.length + 1) answers world =
      (answers.length + 1, world ++ answers, some answers) := by
  induction answers generalizing world with
  | nil => simp [collectCounted, listPull]
  | cons answer rest ih =>
      simp [List.length_cons, collectCounted, listPull, ih, List.append_assoc,
        Nat.add_comm]

/-- Bounded enumeration performs exactly the requested prefix and leaves its
unobserved suffix intact. In particular, the last requested value does not
cause a speculative next poll. -/
theorem list_collect_prefix (answers world : List Answer) (demand : Nat)
    (enough : demand ≤ answers.length) :
    collectBounded listPull demand demand answers world =
      (demand, ⟨answers.drop demand, world ++ answers.take demand,
        answers.take demand, 0, .limit⟩) := by
  induction demand generalizing answers world with
  | zero => simp [collectBounded]
  | succ demand ih =>
      cases answers with
      | nil => simp at enough
      | cons answer rest =>
          have enoughRest : demand ≤ rest.length := by simpa using enough
          simp [collectBounded, listPull, ih rest (world ++ [answer]) enoughRest,
            NativeControlBoundedCursor.Snapshot.prefix, List.append_assoc, Nat.add_comm]

/-- Two complete ordered observations license equal bounded answer prefixes.
This statement deliberately does not equate worlds after early stopping. -/
theorem bounded_answers_of_same_ordered_completion
    {Left Right World : Type}
    (leftPull : Left → World → World × Pull Left Answer)
    (rightPull : Right → World → World × Pull Right Answer)
    (left : Left) (right : Right) (world leftWorld rightWorld : World)
    (leftFuel rightFuel leftSpent rightSpent demand : Nat)
    (answers : List Answer)
    (leftComplete : collectCounted leftPull leftFuel left world =
      (leftSpent, leftWorld, some answers))
    (rightComplete : collectCounted rightPull rightFuel right world =
      (rightSpent, rightWorld, some answers)) :
    (collectBounded leftPull leftFuel demand left world).2.answers =
      (collectBounded rightPull rightFuel demand right world).2.answers := by
  rw [NativeControlBoundedCursor.prefix_of_complete_collection leftPull
    leftFuel demand left world leftSpent leftWorld answers leftComplete,
    NativeControlBoundedCursor.prefix_of_complete_collection rightPull
    rightFuel demand right world rightSpent rightWorld answers rightComplete]

/-- The family of all finite-prefix observers determines the ordered list.
A permutation quotient cannot provide this family in general. -/
theorem all_prefixes_equal_iff (left right : List Answer) :
    (∀ demand, left.take demand = right.take demand) ↔ left = right := by
  constructor
  · intro prefixes
    have both := prefixes (left.length + right.length)
    simpa only [List.take_of_length_le (Nat.le_add_right _ _),
      List.take_of_length_le (Nat.le_add_left _ _)] using both
  · intro same
    simp [same]

/-- Both guards are total Boolean functions and operate on the same candidate
sequence. Their order preserves accepted occurrence order and multiplicity. -/
theorem pure_guard_order (first second : Answer → Bool) (candidates : List Answer) :
    (candidates.filter first).filter second =
      (candidates.filter second).filter first := by
  induction candidates with
  | nil => rfl
  | cons candidate rest ih =>
      cases firstCase : first candidate <;> cases secondCase : second candidate <;>
        simp [firstCase, secondCase, ih]

theorem pure_guard_order_preserves_once (first second : Answer → Bool)
    (candidates : List Answer) :
    ((candidates.filter first).filter second).head? =
      ((candidates.filter second).filter first).head? := by
  rw [pure_guard_order]

namespace Controls

/-- Same complete answer bag, different first answer and effect sequence.
These are executions of the native collector, not a separately defined
semantics for `once`. -/
theorem same_bag_different_once :
    ([1, 2] : List Nat).Perm [2, 1] ∧
    collectCounted listPull 3 [1, 2] [] = (3, [1, 2], some [1, 2]) ∧
    collectCounted listPull 3 [2, 1] [] = (3, [2, 1], some [2, 1]) ∧
    (collectBounded listPull 1 1 [1, 2] []).2.answers = [1] ∧
    (collectBounded listPull 1 1 [2, 1] []).2.answers = [2] ∧
    (collectBounded listPull 1 1 [1, 2] []).2.world ≠
      (collectBounded listPull 1 1 [2, 1] []).2.world := by
  exact ⟨List.Perm.swap _ _ [], rfl, rfl, rfl, rfl, by decide⟩

/-- The same first answer is weaker than preserving `select 2`: evidence
reordering can leave one test unchanged and change a larger observation. -/
theorem same_once_different_select :
    ([1, 2, 3] : List Nat).Perm [1, 3, 2] ∧
    (collectBounded listPull 1 1 [1, 2, 3] []).2.answers =
      (collectBounded listPull 1 1 [1, 3, 2] []).2.answers ∧
    (collectBounded listPull 2 2 [1, 2, 3] []).2.answers ≠
      (collectBounded listPull 2 2 [1, 3, 2] []).2.answers := by
  exact ⟨List.Perm.cons 1 (List.Perm.swap _ _ []), rfl, by decide⟩

open Mettapedia.GSLT.Core.BranchingTemporal

/-- The declarative generated answer belongs to one unchanged transition
system. Depth-first search never reaches it; breadth-first search does in two
ticks. Keeping the rules does not establish productivity of the chosen search. -/
theorem same_rules_different_productivity :
    Generated Starvation.system Starvation.roots .answer ∧
    (∀ fuel, (run Starvation.system Scheduler.depthFirst fuel
      (initial Starvation.roots)).events = []) ∧
    (⟨.answer, 42⟩ : Emission Starvation.Node Nat) ∈
      (run Starvation.system Scheduler.breadthFirst 2
        (initial Starvation.roots)).events := by
  refine ⟨Starvation.answer_is_generated, ?_, Starvation.breadthFirst_emits_answer⟩
  intro fuel
  rw [Starvation.depthFirst_run_fixed]
  rfl

end Controls

#print axioms list_collect_prefix
#print axioms bounded_answers_of_same_ordered_completion
#print axioms pure_guard_order
#print axioms Controls.same_bag_different_once
#print axioms Controls.same_rules_different_productivity

end Mettapedia.Machines.Cursor.ObservationOrder
