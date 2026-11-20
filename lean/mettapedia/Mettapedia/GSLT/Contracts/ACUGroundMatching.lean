import Mettapedia.GSLT.Contracts.ACUReplacement
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Multiset.Powerset

/-!
# Complete substitution search for a ground ACU redex

Meta variables range over operand bags of one declared operator. When
every declared variable occurs in the left-hand side, each of its
bindings must fit inside the subject bag. The executable search uses
that finite bound, tests the whole instantiated left side, and
retains the complementary frame. In particular, taking common
operands independently does not accept a repeated variable twice.

This is matching an open pattern against a ground subject; it is not
a two-sided ACU unifier. The cost can be exponential. Equations do
not erase the distinction between competing rule instances or make
finding the instances free.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.ACUReplacement.GroundMatching

universe u v

variable {Var : Type u} {Atom : Type v}

inductive Template (Var : Type u) (Atom : Type v) where
  | hole (v : Var)
  | atom (a : Atom)
  | unit
  | op (left right : Template Var Atom)
  deriving DecidableEq

def Template.occurs (v : Var) : Template Var Atom → Prop
  | .hole w => v = w
  | .atom _ | .unit => False
  | .op a b => a.occurs v ∨ b.occurs v

def Template.instantiate (values : Var → Term Atom) : Template Var Atom → Term Atom
  | .hole v => values v
  | .atom a => .atom a
  | .unit => .unit
  | .op a b => .op (a.instantiate values) (b.instantiate values)

def Template.evaluate (values : Var → Multiset Atom) : Template Var Atom → Multiset Atom
  | .hole v => values v
  | .atom a => {a}
  | .unit => 0
  | .op a b => a.evaluate values + b.evaluate values

theorem Template.operands_instantiate (p : Template Var Atom) (values : Var → Term Atom) :
    operands (p.instantiate values) = p.evaluate (fun v => operands (values v)) := by
  induction p with
  | hole _ | atom _ | unit => rfl
  | op _ _ first second => simp only [Template.instantiate, Template.evaluate, operands, first, second]

/-- Even one appearance bounds the value of a variable by the whole
instantiated left side. The final applicability test still counts
*all* its appearances. -/
theorem Template.binding_le {p : Template Var Atom} {v : Var} (needed : p.occurs v)
    (values : Var → Multiset Atom) : values v ≤ p.evaluate values := by
  induction p with
  | hole w =>
      change v = w at needed
      subst w
      exact le_rfl
  | atom _ | unit => exact False.elim needed
  | op a b first second =>
      rcases needed with left | right
      · exact (first left).trans (Multiset.le_add_right _ _)
      · exact (second right).trans (Multiset.le_add_left _ _)

structure Schema (Var : Type u) (Atom : Type v) where
  lhs : Template Var Atom
  rhs : Template Var Atom
  inputsBound : ∀ v, lhs.occurs v

def Schema.instanceAt (rule : Schema Var Atom) (values : Var → Term Atom) : Rule Atom :=
  ⟨rule.lhs.instantiate values, rule.rhs.instantiate values⟩

def Schema.instantiates (rule : Schema Var Atom) (instanceRule : Rule Atom) : Prop :=
  ∃ values, rule.instanceAt values = instanceRule

section Search

variable [Fintype Var] [DecidableEq Var] [DecidableEq Atom]

/-- All value maps in the uniform finite bound. Distinct spellings
of a bound bag are not separately enumerated. -/
def assignments (subject : Multiset Atom) : Finset (Var → Multiset Atom) :=
  Fintype.piFinset fun _ => subject.powerset.toFinset

theorem mem_assignments (subject : Multiset Atom) (values : Var → Multiset Atom) :
    values ∈ assignments subject ↔ ∀ v, values v ≤ subject := by
  simp [assignments, Fintype.mem_piFinset, Multiset.mem_powerset]

def fits (rule : Schema Var Atom) (subject : Multiset Atom) :
    Finset (Var → Multiset Atom) :=
  (assignments subject).filter fun values => rule.lhs.evaluate values ≤ subject

/-- Every matching substitution and its retained frame, on ground
operand keys. A consumer that needs the actual answer bindings may
retain this set instead of projecting it to successor classes. -/
theorem mem_fits_iff (rule : Schema Var Atom) (subject : Multiset Atom)
    (values : Var → Multiset Atom) :
    values ∈ fits rule subject ↔ ∃ frame, subject = rule.lhs.evaluate values + frame := by
  rw [fits, Finset.mem_filter, mem_assignments]
  constructor
  · exact fun bound => Multiset.le_iff_exists_add.mp bound.2
  · intro frame
    have fitsSubject := Multiset.le_iff_exists_add.mpr frame
    exact ⟨fun v => ((Template.binding_le (rule.inputsBound v) values)).trans fitsSubject, fitsSubject⟩

def successorKeys (rule : Schema Var Atom) (subject : Multiset Atom) : Finset (Multiset Atom) :=
  (fits rule subject).image fun values =>
    rule.rhs.evaluate values + (subject - rule.lhs.evaluate values)

theorem mem_successorKeys_iff (rule : Schema Var Atom) (before after : Multiset Atom) :
    after ∈ successorKeys rule before ↔
      ∃ values frame, before = rule.lhs.evaluate values + frame ∧
        after = rule.rhs.evaluate values + frame := by
  simp only [successorKeys, Finset.mem_image, mem_fits_iff]
  constructor
  · rintro ⟨values, ⟨frame, full⟩, result⟩
    refine ⟨values, frame, full, ?_⟩
    rw [← result, full, Multiset.add_comm (rule.lhs.evaluate values) frame,
      Multiset.add_sub_cancel_right]
  · rintro ⟨values, frame, full, result⟩
    refine ⟨values, ⟨frame, full⟩, ?_⟩
    rw [full, Multiset.add_comm (rule.lhs.evaluate values) frame,
      Multiset.add_sub_cancel_right, result]

omit [Fintype Var] [DecidableEq Var] [DecidableEq Atom] in
private theorem values_have_spellings (values : Var → Multiset Atom) :
    ∃ concrete : Var → Term Atom, ∀ v, operands (concrete v) = values v := by
  have reps (v : Var) : ∃ xs : List Atom, (xs : Multiset Atom) = values v :=
    Quotient.exists_rep (values v)
  choose spelling agrees using reps
  exact ⟨fun v => spell (spelling v), fun v => (operands_spell (spelling v)).trans (agrees v)⟩

theorem canonical_successors_exact (rule : Schema Var Atom) (before after : Term Atom) :
    operands after ∈ successorKeys rule (operands before) ↔ Reduces rule.instantiates before after := by
  rw [mem_successorKeys_iff, reduces_iff_extension]
  constructor
  · rintro ⟨values, frame, left, right⟩
    obtain ⟨concrete, same⟩ := values_have_spellings values
    have equal : (fun v => operands (concrete v)) = values := funext same
    refine ⟨rule.instanceAt concrete, ⟨concrete, rfl⟩, frame, ?_, ?_⟩
    · simpa only [Schema.instanceAt, Template.operands_instantiate, equal] using left
    · simpa only [Schema.instanceAt, Template.operands_instantiate, equal] using right
  · rintro ⟨instanceRule, ⟨concrete, rfl⟩, frame, left, right⟩
    refine ⟨fun v => operands (concrete v), frame, ?_, ?_⟩
    · simpa only [Schema.instanceAt, Template.operands_instantiate] using left
    · simpa only [Schema.instanceAt, Template.operands_instantiate] using right

end Search

namespace Controls

private def double : Schema (Fin 1) Nat :=
  ⟨.op (.hole 0) (.hole 0), .op (.atom 9) (.hole 0), by
    intro v
    left
    exact Subsingleton.elim _ _⟩

private def input : Multiset Nat := ([1, 1, 2] : List Nat)

theorem nonlinear_rule_can_bind_the_repeated_value :
    (([9, 1, 2] : List Nat) : Multiset Nat) ∈ successorKeys double input := by
  apply (mem_successorKeys_iff ..).mpr
  exact ⟨fun _ => {1}, {2}, by decide, by decide⟩

theorem nonlinear_rule_cannot_use_a_single_copy_twice :
    (fun _ : Fin 1 => ({2} : Multiset Nat)) ∉ fits double input := by
  intro chosen
  have applies := (Finset.mem_filter.mp chosen).2
  exact (by decide : ¬ (([2, 2] : List Nat) : Multiset Nat) ≤ input) applies

end Controls

#print axioms Template.binding_le
#print axioms mem_fits_iff
#print axioms canonical_successors_exact
#print axioms Controls.nonlinear_rule_can_bind_the_repeated_value
#print axioms Controls.nonlinear_rule_cannot_use_a_single_copy_twice

end Mettapedia.GSLT.Contracts.ACUReplacement.GroundMatching
