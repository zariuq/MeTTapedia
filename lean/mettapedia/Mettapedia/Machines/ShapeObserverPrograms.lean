import Mettapedia.Machines.ShapeHeadRouting

/-!
# Adaptive observers of mixed row and compact stores

Primitive bag refinement lifts to programs that choose their next operation
from previous answers. Membership guards may therefore read earlier writes;
correctness is not limited to a fixed precomputed query list. Complete answer
traces, returned values and final bags agree with the independent all-rows
interpreter. The observation grammar has pure predicates and sequential
effects; it does not include occurrence order or concurrent readers.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeObserverPrograms

open ShapeHeadRouting

variable {Head Fact Result : Type} [DecidableEq Head] [DecidableEq Fact]

inductive Program (Head Fact Result : Type) where
  | done (value : Result)
  | ask (operation : Op Head Fact) (next : Answer Fact → Program Head Fact Result)

def execute (head : Fact → Head) (eligible : Fact → Bool) :
    Program Head Fact Result → State Head Fact → (Result × List (Answer Fact)) × State Head Fact
  | .done result, state => ((result, []), state)
  | .ask op next, state =>
      let first := step head eligible op state
      let later := execute head eligible (next first.1) first.2
      ((later.1.1, first.1 :: later.1.2), later.2)

def reference : Program Head Fact Result → Multiset Fact →
    (Result × List (Answer Fact)) × Multiset Fact
  | .done result, rows => ((result, []), rows)
  | .ask op next, rows =>
      let first := referenceStep op rows
      let later := reference (next first.1) first.2
      ((later.1.1, first.1 :: later.1.2), later.2)

theorem execute_refines (head : Fact → Head) (eligible : Fact → Bool)
    (program : Program Head Fact Result) (state : State Head Fact) :
    ((execute head eligible program state).1, observe (execute head eligible program state).2) =
      reference program (observe state) := by
  induction program generalizing state with
  | done value => rfl
  | ask op next ih =>
      have hs := step_refines head eligible op state
      have ha := congrArg Prod.fst hs
      have hstate := congrArg Prod.snd hs
      dsimp only at ha hstate
      have hlater := ih (step head eligible op state).1 (step head eligible op state).2
      have hv := congrArg Prod.fst hlater
      have hf := congrArg Prod.snd hlater
      dsimp only at hv hf
      simp only [execute, reference]
      rw [hv, hf, hstate, ha]

theorem representation_independent (head : Fact → Head) (eligible : Fact → Bool)
    (program : Program Head Fact Result) (left right : State Head Fact)
    (same : observe left = observe right) :
    ((execute head eligible program left).1, observe (execute head eligible program left).2) =
      ((execute head eligible program right).1, observe (execute head eligible program right).2) := by
  rw [execute_refines, execute_refines, same]

/-- A guard is derived from logical multiplicity, not record presence. -/
def ifPresent (fact : Fact) (yes no : Program Head Fact Result) : Program Head Fact Result :=
  .ask (.count fact) fun answer => match answer with
    | .count 0 => no
    | .count (_ + 1) => yes
    | _ => no

def insertThen (fact : Fact) (next : Program Head Fact Result) : Program Head Fact Result :=
  .ask (.insert fact) fun _ => next

def ensure (fact : Fact) : Program Head Fact Bool :=
  ifPresent fact (.done false) (insertThen fact (.done true))

namespace Controls

def compactOnly : State Unit Nat := ⟨fun _ => true, ⟨{7}, 0⟩⟩

/-- A missing ordinary row is not a missing fact. -/
theorem recordless_is_present :
    (execute (fun _ => ()) (fun _ => true) (ensure 7) compactOnly).1.1 = false ∧
    compactOnly.data.rows.count 7 = 0 := by decide

def twice : Program Unit Nat Nat :=
  insertThen 7 (insertThen 7 (.ask (.count 7) fun answer => match answer with
    | .count n => .done n
    | _ => .done 0))

theorem bag_effects_keep_both_copies :
    (execute (fun _ => ()) (fun _ => true) twice (fromRows 0)).1.1 = 2 := by decide

def guardedTwice : Program Unit Nat Nat :=
  ifPresent 7 (.done 0)
    (insertThen 7 (ifPresent 7 (.done 1) (insertThen 7 (.done 2))))

theorem second_guard_sees_first_write :
    (execute (fun _ => ()) (fun _ => true) guardedTwice (fromRows 0)).1.1 = 1 ∧
    (observe (execute (fun _ => ()) (fun _ => true) guardedTwice (fromRows 0)).2).count 7 = 1 := by decide

end Controls

#print axioms execute_refines
#print axioms representation_independent
#print axioms Controls.recordless_is_present
#print axioms Controls.bag_effects_keep_both_copies

end Mettapedia.Machines.ShapeObserverPrograms
