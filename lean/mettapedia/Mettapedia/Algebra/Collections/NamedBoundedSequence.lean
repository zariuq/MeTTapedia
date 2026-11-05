import Mettapedia.Algebra.Collections.BoundedSequenceUnification
import Mathlib.Data.List.Basic

/-!
# Bounded sequence families over actual input variable names

The two input words supply their finite active-name inventory. Lowering to
dense positions preserves substitution and the original word equation. The
existing bounded solver then enumerates its symbolic families. Completeness
constrains only original active names; variables outside that inventory are
not part of the equation and remain unrestricted in its instances.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.Unification.NamedBoundedSequence

open Unification (Word)
open BoundedSequence (applyInto Solves Within Candidate values)

universe u v w z
variable {A : Type u} {X : Type v} {Y : Type w} {Z : Type z}

def variableNames (word : Word A X) : List X :=
  word.filterMap fun token => match token with | .inl _ => none | .inr name => some name

theorem mem_variableNames (name : X) (word : Word A X) : name ∈ variableNames word ↔ Sum.inr name ∈ word := by
  simp only [variableNames, List.mem_filterMap]
  constructor
  · rintro ⟨token, member, found⟩
    cases token with
    | inl => cases found
    | inr other => cases Option.some.inj found; exact member
  · intro member
    exact ⟨.inr name, member, rfl⟩

variable [DecidableEq X]

def inventory (left right : Word A X) : List X := (variableNames (left ++ right)).eraseDups

theorem mem_inventory (name : X) (left right : Word A X) :
    name ∈ inventory left right ↔ Sum.inr name ∈ left ∨ Sum.inr name ∈ right := by
  simp only [inventory, List.mem_eraseDups, mem_variableNames, List.mem_append]

def Covered (names : List X) (word : Word A X) : Prop := ∀ name, Sum.inr name ∈ word → name ∈ names

def index (names : List X) (name : X) (member : name ∈ names) : Fin names.length :=
  ⟨names.idxOf name, List.idxOf_lt_length_of_mem member⟩

theorem name_index (names : List X) (name : X) (member : name ∈ names) :
    names.get (index names name member) = name := List.idxOf_get _

def lowerWord (names : List X) : (word : Word A X) → Covered names word → Word A (Fin names.length)
  | [], _ => []
  | .inl value :: rest, covered =>
      .inl value :: lowerWord names rest (fun name member => covered name (List.mem_cons_of_mem _ member))
  | .inr name :: rest, covered =>
      .inr (index names name (covered name List.mem_cons_self)) ::
        lowerWord names rest (fun name member => covered name (List.mem_cons_of_mem _ member))

def restrict (names : List X) (substitution : X → Word A Y) : Fin names.length → Word A Y :=
  fun slot => substitution (names.get slot)

def lift (names : List X) (substitution : Fin names.length → Word A Y) : X → Word A Y :=
  fun name => if member : name ∈ names then substitution (index names name member) else []

/-- Closed input membership supplies each lookup proof; no external codec
correctness certificate is an argument. -/
theorem apply_restrict (names : List X) (substitution : X → Word A Y) (word : Word A X) (covered : Covered names word) :
    applyInto (restrict names substitution) (lowerWord names word covered) = applyInto substitution word := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
    have tail := ih (fun name member => covered name (List.mem_cons_of_mem _ member))
    cases token with
    | inl value =>
        simp only [lowerWord, BoundedSequence.applyInto_constant]
        exact congrArg (List.cons (.inl value)) tail
    | inr name =>
        simp only [lowerWord, BoundedSequence.applyInto_variable, restrict, name_index]
        exact congrArg (substitution name ++ ·) tail

theorem apply_lift (names : List X) (substitution : Fin names.length → Word A Y)
    (word : Word A X) (covered : Covered names word) :
    applyInto (lift names substitution) word = applyInto substitution (lowerWord names word covered) := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
    have tail := ih (fun name member => covered name (List.mem_cons_of_mem _ member))
    cases token with
    | inl value =>
        simp only [lowerWord, BoundedSequence.applyInto_constant]
        exact congrArg (List.cons (.inl value)) tail
    | inr name =>
        simp only [lowerWord, BoundedSequence.applyInto_variable, lift, dif_pos (covered name List.mem_cons_self)]
        exact congrArg (substitution (index names name (covered name List.mem_cons_self)) ++ ·) tail

omit [DecidableEq X] in
theorem apply_agrees (first second : X → Word A Y) (word : Word A X)
    (agrees : ∀ name, Sum.inr name ∈ word → first name = second name) : applyInto first word = applyInto second word := by
  induction word with
  | nil => rfl
  | cons token rest ih =>
    have tail := ih (fun name member => agrees name (List.mem_cons_of_mem _ member))
    cases token with
    | inl value => exact congrArg (List.cons (.inl value)) tail
    | inr name =>
        simp only [BoundedSequence.applyInto_variable, agrees name List.mem_cons_self, tail]

theorem left_covered (left right : Word A X) : Covered (inventory left right) left :=
  fun name member => (mem_inventory name left right).mpr (Or.inl member)

theorem right_covered (left right : Word A X) : Covered (inventory left right) right :=
  fun name member => (mem_inventory name left right).mpr (Or.inr member)

def loweredLeft (left right : Word A X) : Word A (Fin (inventory left right).length) :=
  lowerWord (inventory left right) left (left_covered left right)
def loweredRight (left right : Word A X) : Word A (Fin (inventory left right).length) :=
  lowerWord (inventory left right) right (right_covered left right)

variable [DecidableEq A]

abbrev Code (left right : Word A X) (bound : Nat) :=
  Candidate (BoundedSequence.constantsOf (loweredLeft left right) ∪ BoundedSequence.constantsOf (loweredRight left right))
    (inventory left right).length bound

/-- The actual finite search uses only names and constants collected from
the inputs; neither ambient type is required to be finite. -/
def solveBounded (left right : Word A X) (bound : Nat) : Finset (Code left right bound) :=
  BoundedSequence.solveBounded (inventory left right).length bound (loweredLeft left right) (loweredRight left right)

def liftCode (left right : Word A X) (bound : Nat) (code : Code left right bound) :
    X → Word A (Fin ((inventory left right).length * bound)) := lift (inventory left right) (values code)

def WithinActive (left right : Word A X) (bound : Nat) (substitution : X → Word A Y) : Prop :=
  ∀ name ∈ inventory left right, (substitution name).length ≤ bound

def InstanceOnActive (left right : Word A X) (general : X → Word A Y) (specific : X → Word A Z) : Prop :=
  ∃ residual : Y → Word A Z, ∀ name ∈ inventory left right, applyInto residual (general name) = specific name

theorem liftCode_outside (left right : Word A X) (bound : Nat) (code : Code left right bound) (name : X)
    (outside : name ∉ inventory left right) : liftCode left right bound code name = [] := by
  simp only [liftCode, lift, dif_neg outside]

theorem liftCode_bounded (left right : Word A X) (bound : Nat) (code : Code left right bound) :
    Within bound (liftCode left right bound code) := by
  intro name
  unfold liftCode lift
  split
  · exact BoundedSequence.values_bounded code _
  · simp

theorem sound (left right : Word A X) (bound : Nat) (code : Code left right bound)
    (member : code ∈ solveBounded left right bound) : Solves left right (liftCode left right bound code) := by
  have core := (BoundedSequence.mem_unifiers code).mp member
  change applyInto (lift (inventory left right) (values code)) left =
    applyInto (lift (inventory left right) (values code)) right
  rw [apply_lift _ _ left (left_covered left right), apply_lift _ _ right (right_covered left right)]
  exact core

theorem all_instances_solve (left right : Word A X) (bound : Nat) (code : Code left right bound)
    (member : code ∈ solveBounded left right bound) (substitution : X → Word A Y)
    (represented : InstanceOnActive left right (liftCode left right bound code) substitution) :
    Solves left right substitution := by
  obtain ⟨residual, agrees⟩ := represented
  have composed := congrArg (applyInto residual) (sound left right bound code member)
  simp only [BoundedSequence.applyInto_compose] at composed
  have leftSame := apply_agrees (fun name => applyInto residual (liftCode left right bound code name)) substitution left
    (fun name present => agrees name ((mem_inventory name left right).mpr (Or.inl present)))
  have rightSame := apply_agrees (fun name => applyInto residual (liftCode left right bound code name)) substitution right
    (fun name present => agrees name ((mem_inventory name left right).mpr (Or.inr present)))
  exact leftSame.symm.trans (composed.trans rightSame)

/-- Completeness is on the original active names. Off-support images of the
specific substitution are unrestricted and need not equal the lifted empty
default or obey the bound. -/
theorem complete (left right : Word A X) (bound : Nat) (substitution : X → Word A Y)
    (solved : Solves left right substitution) (within : WithinActive left right bound substitution) :
    ∃ code ∈ solveBounded left right bound, InstanceOnActive left right (liftCode left right bound code) substitution := by
  let names := inventory left right
  have denseSolved : Solves (loweredLeft left right) (loweredRight left right) (restrict names substitution) := by
    exact (apply_restrict names substitution left (left_covered left right)).trans
      (solved.trans (apply_restrict names substitution right (right_covered left right)).symm)
  have denseWithin : Within bound (restrict names substitution) :=
    fun slot => within (names.get slot) (List.get_mem names slot)
  obtain ⟨code, member, residual, represented⟩ := BoundedSequence.solveBounded_complete names.length bound
    (loweredLeft left right) (loweredRight left right) (restrict names substitution) denseSolved denseWithin
  refine ⟨code, member, residual, ?_⟩
  intro name present
  have actual := represented (index names name present)
  simpa only [liftCode, lift, dif_pos present, restrict, name_index] using actual

omit [DecidableEq A] in
/-- Altering only unused original variables cannot change this equation. -/
theorem off_support_changes_irrelevant (left right : Word A X) (first second : X → Word A Y)
    (agrees : ∀ name ∈ inventory left right, first name = second name) :
    Solves left right first ↔ Solves left right second := by
  have leftSame := apply_agrees first second left (fun name present => agrees name (left_covered left right name present))
  have rightSame := apply_agrees first second right (fun name present => agrees name (right_covered left right name present))
  unfold Solves
  rw [leftSame, rightSame]

namespace Controls

theorem inventory_uses_actual_names_once :
    inventory ([.inr 42, .inl 7, .inr 42] : Word Nat Nat) [.inr 8, .inr 42] = [42, 8] := by decide

def substitution : Nat → Word Nat Unit := fun name =>
  if name = 42 then [.inl 7] else [.inl 8, .inl 9]

theorem unrelated_images_need_not_obey_the_bound :
    WithinActive ([.inr 42] : Word Nat Nat) [.inl 7] 1 substitution ∧ ¬ Within 1 substitution := by
  constructor
  · intro name member
    have same : name = 42 := by simpa [mem_inventory] using member
    subst name
    decide
  · intro bounded
    have impossible := bounded 0
    simp [substitution] at impossible

theorem actual_named_family_covers_the_solution :
    ∃ code ∈ solveBounded ([.inr 42] : Word Nat Nat) [.inl 7] 1,
      InstanceOnActive [.inr 42] [.inl 7] (liftCode [.inr 42] [.inl 7] 1 code) substitution :=
  complete _ _ 1 substitution (by simp [Solves, applyInto, substitution]) unrelated_images_need_not_obey_the_bound.1

theorem empty_problem_has_no_active_names : inventory ([] : Word Empty Nat) [] = [] := rfl

theorem unused_name_is_not_captured (code : Code ([.inr 42] : Word Nat Nat) [.inl 7] 1) :
    liftCode [.inr 42] [.inl 7] 1 code 99 = [] := liftCode_outside _ _ _ _ _ (by decide)

end Controls

end Mettapedia.Algebra.Collections.Unification.NamedBoundedSequence

#print axioms Mettapedia.Algebra.Collections.Unification.NamedBoundedSequence.sound
#print axioms Mettapedia.Algebra.Collections.Unification.NamedBoundedSequence.complete
