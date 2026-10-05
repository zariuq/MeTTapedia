import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicSoundness
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Infinite contextual controls for first-order logic

The value carrier is the natural numbers and the context category has all
natural stages. Membership becomes available after stage zero. This is a
model of the logical rules, not a proposed model of material set axioms.
It distinguishes full future forcing from present truth and validates an
actual equality-elimination derivation without making a classical rule valid.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicControls

open _root_.CategoryTheory ContextualMaterialLogic

def values : ℕ ⥤ Type where
  obj _ := ℕ
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def model : Model values where
  member point child parent := 0 < point ∧ child = parent
  member_transport := by
    intro point target arrow child parent available
    exact ⟨Nat.lt_of_lt_of_le available.1 (leOfHom arrow), available.2⟩

def selfMember : Formula 1 := .member 0 0

def negate {n : Nat} (formula : Formula n) : Formula n := .imply formula .bottom

def environment (value : ℕ) : Environment values 1 0 := fun _ => value

theorem initial_false (value : ℕ) : ¬ force values model selfMember 0 (environment value) :=
  fun available => Nat.lt_irrefl 0 available.1

theorem every_stage_has_later_truth (point : ℕ) (assignment : Environment values 1 point) :
    force values model selfMember (point+1)
      (ContextualMaterialLogic.transport values (homOfLE (Nat.le_succ point)) assignment) :=
  ⟨Nat.zero_lt_succ point, rfl⟩

theorem negation_empty (point : ℕ) (assignment : Environment values 1 point) :
    ¬ force values model (negate selfMember) point assignment :=
  fun absent => absent (point+1) (homOfLE (Nat.le_succ point))
    (every_stage_has_later_truth point assignment)

theorem double_negation_holds (point : ℕ) (assignment : Environment values 1 point) :
    force values model (negate (negate selfMember)) point assignment := by
  intro target arrow absent
  exact negation_empty target (ContextualMaterialLogic.transport values arrow assignment) absent

theorem excluded_middle_fails (value : ℕ) :
    ¬ force values model (.either selfMember (negate selfMember)) 0 (environment value) :=
  fun alternatives => alternatives.elim (initial_false value) (negation_empty 0 (environment value))

theorem double_negation_elimination_fails (value : ℕ) :
    ¬ force values model (.imply (negate (negate selfMember)) selfMember) 0 (environment value) :=
  fun implication => initial_false value
    (force_modusPonens model _ _ 0 (environment value) implication
      (double_negation_holds 0 (environment value)))

theorem present_universal_absence (value : ℕ) :
    ∀ child : ℕ, ¬ model.member 0 child value :=
  fun _ available => Nat.lt_irrefl 0 available.1

/-- A present universal absence claim does not validate the corresponding
first-order formula, which checks future values and arrows. -/
theorem full_universal_absence_fails (value : ℕ) :
    ¬ force values model (.all (.imply (.member 0 1) .bottom)) 0 (environment value) := by
  intro absent
  have future := absent 1 (homOfLE (Nat.zero_le 1)) value
  have current := future 1 (𝟙 1)
  rw [ContextualMaterialLogic.transport_id] at current
  exact current ⟨Nat.zero_lt_succ 0, rfl⟩

def equalityConsumer : Derivation
    [Formula.equal (n := 2) 0 1, Formula.member 0 1] (Formula.member 1 1) :=
  Derivation.equalElim (body := Formula.member 0 2) (first := 0) (second := 1)
    (Derivation.hypothesis (List.mem_cons_self))
    (Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem equality_consumer_sound (point : ℕ) (assignment : Environment values 2 point)
    (same : assignment 0 = assignment 1) (belongs : model.member point (assignment 0) (assignment 1)) :
    model.member point (assignment 1) (assignment 1) := by
  apply derivation_sound model equalityConsumer point assignment
  intro formula included
  rcases List.mem_cons.mp included with rfl | tail
  · exact same
  · rcases List.mem_cons.mp tail with rfl | empty
    · exact belongs
    · exact (List.not_mem_nil empty).elim

theorem no_closed_excluded_middle_proof :
    ¬ Nonempty (Derivation [] (.either selfMember (negate selfMember))) := by
  rintro ⟨derivation⟩
  exact excluded_middle_fails 0 (closed_derivation_sound model derivation 0 (environment 0))

theorem no_closed_double_negation_elimination_proof :
    ¬ Nonempty (Derivation [] (.imply (negate (negate selfMember)) selfMember)) := by
  rintro ⟨derivation⟩
  exact double_negation_elimination_fails 0 (closed_derivation_sound model derivation 0 (environment 0))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogicControls
