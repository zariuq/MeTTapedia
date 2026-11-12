import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EventMultiplicityRealization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ExecutionRectangleControls
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum

/-!
# Native event fibres, parallel realization and loss of origins

The tell program is used with empty, single, double and infinite choice fibres.
Two origin-tagged components realize to four native firings. Erasing origins
keeps the successor set but changes the event multiplicity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicityControls

open Presentation.Controls (Store frame effect)
open ExecutionRectangleControls (after after_succ)
open EventMultiplicity

def program (Choices : Type) : Step frame Nat Store (fun _ => Choices) :=
  (Step.ofEffect effect (fun _ _ => True)).reindex (fun _ => ())

theorem admitted {Choices : Type} (state : Store) (choice : Choices) :
    (program Choices).Admits (s := state) choice :=
  ⟨Presentation.Controls.prepares state (), trivial⟩

abbrev native (Choices : Type) := (program Choices).eventSystem (fun _ => ())

def nativeChoices (Choices : Type) (state : Store) : Choices ≃ (native Choices).Choice state where
  toFun choice := ⟨choice, admitted state choice⟩
  invFun choice := choice.val
  left_inv _ := rfl
  right_inv _ := rfl

theorem empty_native_fibre (state : Store) : ¬Nonempty ((native Empty).Choice state) := by
  rintro ⟨choice⟩
  exact choice.val.elim

def infinite_native_fibre (state : Store) : Nat ≃ (native Nat).Choice state := nativeChoices Nat state

def successorSet (Choices : Type) (state : Store) : Set Store :=
  {target | ∃ choice : (native Choices).Choice state, (native Choices).next state choice = target}

theorem inhabited_successor_set (Choices : Type) (witness : Choices) (state : Store) :
    successorSet Choices state = {state ++ [(true, false)]} := by
  ext target
  constructor
  · rintro ⟨choice, equal⟩
    exact equal.symm
  · intro equal
    exact ⟨nativeChoices Choices state witness, equal.symm⟩

theorem equal_successor_sets (state : Store) : successorSet Bool state = successorSet Unit state := by
  rw [inhabited_successor_set Bool false, inhabited_successor_set Unit ()]

theorem double_is_not_single (left right : Store) :
    ¬Bisimilar (native Bool) left (native Unit) right := by
  rintro ⟨_, ⟨b⟩, related⟩
  let collapse : Bool ≃ Unit := (nativeChoices Bool left).trans
    ((b.choices related).trans (nativeChoices Unit right).symm)
  have impossible : false = true := collapse.injective (Subsingleton.elim _ _)
  cases impossible

def counter (Choices : Type) : System Nat Unit where
  Choice _ := Choices
  next count _ := count + 1
  action _ _ := ()

def nativeCounter (Choices : Type) : Realization (counter Choices) (native Choices) where
  state count := after [] count
  choices count := nativeChoices Choices (after [] count)
  actions _ _ := rfl
  successors count _ := after_succ [] count

def nativeParallel : Realization (asynchronous (counter Bool) (counter Bool)) (native (Bool ⊕ Bool)) where
  state counts := after [] (counts.1 + counts.2)
  choices counts := nativeChoices (Bool ⊕ Bool) (after [] (counts.1 + counts.2))
  actions _ _ := rfl
  successors counts choice := by
    cases choice with
    | inl choice =>
        change after [] ((counts.1 + 1) + counts.2) = after [] (counts.1 + counts.2) ++ [(true, false)]
        rw [show (counts.1 + 1) + counts.2 = (counts.1 + counts.2) + 1 by omega]
        exact after_succ [] _
    | inr choice =>
        change after [] (counts.1 + (counts.2 + 1)) = after [] (counts.1 + counts.2) ++ [(true, false)]
        rw [← Nat.add_assoc]
        exact after_succ [] _

/-- Every finite parallel history corresponds bijectively to a native run of the same length. -/
def nativeParallelExecutions (count left right : Nat) :
    (asynchronous (counter Bool) (counter Bool)).Execution count (left, right) ≃
      {run : (program (Bool ⊕ Bool)).Run (after [] (left + right)) // run.word.length = count} :=
  (nativeParallel.bisimulation.executions count rfl).trans
    ((program (Bool ⊕ Bool)).countedExecutionRunEquiv (fun _ => ()) (after [] (left + right)) count)

def shifted (offset : Nat) : Bisimulation (counter Bool) (counter Bool) (fun n m => n + offset = m) where
  choices _ := Equiv.refl _
  actions _ _ := rfl
  successors same _ := by change _ + 1 + offset = _ + 1; omega

theorem shift_bisimilar (count offset : Nat) : Bisimilar (counter Bool) count (counter Bool) (count + offset) :=
  ⟨_, ⟨shifted offset⟩, rfl⟩

/-- The general parallel theorem reaches a real native profile of the core. -/
theorem native_parallel_congruence (n m offset₁ offset₂ : Nat) :
    Bisimilar (native (Bool ⊕ Bool)) (after [] (n + m))
      (native (Bool ⊕ Bool)) (after [] ((n + offset₁) + (m + offset₂))) :=
  realized_parallel_congruence nativeParallel (shift_bisimilar n offset₁) (shift_bisimilar m offset₂)

theorem origin_erasure_changes_multiplicity (left right : Store) :
    ¬Bisimilar (native (Bool ⊕ Bool)) left (native Bool) right := by
  rintro ⟨_, ⟨b⟩, related⟩
  let erased : (Bool ⊕ Bool) ≃ Bool := (nativeChoices (Bool ⊕ Bool) left).trans
    ((b.choices related).trans (nativeChoices Bool right).symm)
  have sameCard := Fintype.card_congr erased
  simp at sameCard

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.EventMultiplicityControls
