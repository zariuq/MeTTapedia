import Mettapedia.Computability.RegularLanguages.IntervalClasses

/-!
# Composed interval-class compilation

Admitted properties and explicit domains supply interval leaves. The expression
compiler normalizes unions and lowers intersections to two differences, as the
native-data compiler does. Its membership specification is compositional logic,
not the compiled interval result. These laws do not assert UCD-table correctness
or correspondence with unchecked native memory operations.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.ClassExpressions

open IntervalClasses

inductive Expr where
  | leaf (ranges : List Interval)
  | union (left right : Expr)
  | intersection (left right : Expr)
  | difference (left right : Expr)
  | complement (domain : List Interval) (expression : Expr)
  deriving DecidableEq, Repr

def WellFormed : Expr → Prop
  | .leaf ranges => Valid ranges
  | .union left right | .intersection left right | .difference left right =>
      WellFormed left ∧ WellFormed right
  | .complement domain expression => Valid domain ∧ WellFormed expression

/-- Independent pointwise specification. Complements name their universe. -/
def Denote : Expr → Nat → Prop
  | .leaf ranges, x => Contains ranges x
  | .union left right, x => Denote left x ∨ Denote right x
  | .intersection left right, x => Denote left x ∧ Denote right x
  | .difference left right, x => Denote left x ∧ ¬ Denote right x
  | .complement domain expression, x => Contains domain x ∧ ¬ Denote expression x

def compile : Expr → List Interval
  | .leaf ranges => normalize ranges
  | .union left right => normalize (compile left ++ compile right)
  | .intersection left right =>
      IntervalClasses.difference (compile left)
        (IntervalClasses.difference (compile left) (compile right))
  | .difference left right => IntervalClasses.difference (compile left) (compile right)
  | .complement domain expression => IntervalClasses.difference domain (compile expression)

private theorem valid_append {left right : List Interval}
    (hl : Valid left) (hr : Valid right) : Valid (left ++ right) := by
  intro range member
  rcases List.mem_append.mp member with member | member
  · exact hl range member
  · exact hr range member

theorem compile_valid (expression : Expr) (wellFormed : WellFormed expression) :
    Valid (compile expression) := by
  induction expression with
  | leaf ranges => exact normalize_valid ranges wellFormed
  | union left right ihl ihr =>
      exact normalize_valid _ (valid_append (ihl wellFormed.1) (ihr wellFormed.2))
  | intersection left right ihl _ =>
      exact difference_valid _ _ (ihl wellFormed.1)
  | difference left right ihl _ =>
      exact difference_valid _ _ (ihl wellFormed.1)
  | complement domain expression _ =>
      exact difference_valid _ _ wellFormed.1

/-- Every compiled operation implements its independently stated membership. -/
theorem compile_contains (expression : Expr) (wellFormed : WellFormed expression)
    (x : Nat) : Contains (compile expression) x ↔ Denote expression x := by
  induction expression with
  | leaf ranges => exact normalize_contains ranges wellFormed x
  | union left right ihl ihr =>
      rw [compile, normalize_contains _
        (valid_append (compile_valid left wellFormed.1) (compile_valid right wellFormed.2)),
        contains_append, ihl wellFormed.1, ihr wellFormed.2]
      rfl
  | intersection left right ihl ihr =>
      have hl := compile_valid left wellFormed.1
      have hr := compile_valid right wellFormed.2
      rw [compile, difference_contains _ _ hl (difference_valid _ _ hl),
        difference_contains _ _ hl hr, ihl wellFormed.1, ihr wellFormed.2]
      simp only [Denote]
      tauto
  | difference left right ihl ihr =>
      rw [compile, difference_contains _ _
        (compile_valid left wellFormed.1) (compile_valid right wellFormed.2),
        ihl wellFormed.1, ihr wellFormed.2]
      rfl
  | complement domain expression ih =>
      rw [compile, difference_contains _ _ wellFormed.1
        (compile_valid expression wellFormed.2), ih wellFormed.2]
      rfl

theorem double_complement_projects (domain : List Interval) (expression : Expr)
    (validDomain : Valid domain) (wellFormed : WellFormed expression) (x : Nat) :
    Contains (compile (.complement domain (.complement domain expression))) x ↔
      Contains domain x ∧ Denote expression x := by
  rw [compile_contains (.complement domain (.complement domain expression))
    ⟨validDomain, validDomain, wellFormed⟩]
  simp only [Denote]
  tauto

theorem compile_intersection_commutes (left right : Expr)
    (hl : WellFormed left) (hr : WellFormed right) (x : Nat) :
    Contains (compile (.intersection left right)) x ↔
      Contains (compile (.intersection right left)) x := by
  rw [compile_contains (.intersection left right) ⟨hl, hr⟩,
    compile_contains (.intersection right left) ⟨hr, hl⟩]
  exact and_comm

theorem compile_difference_excludes (left right : Expr)
    (hl : WellFormed left) (hr : WellFormed right) (x : Nat)
    (present : Contains (compile (.difference left right)) x) :
    ¬ Contains (compile right) x := by
  rw [compile_contains _ hr]
  exact ((compile_contains (.difference left right) ⟨hl, hr⟩ x).mp present).2

def asciiDecimal : Expr := .leaf [⟨48, 57⟩]

def asciiHex : Expr := .union asciiDecimal
  (.union (.leaf [⟨65, 70⟩]) (.leaf [⟨97, 102⟩]))

theorem asciiDecimal_wellFormed : WellFormed asciiDecimal := by
  simp [asciiDecimal, WellFormed, Valid, Interval.Valid]

theorem asciiHex_wellFormed : WellFormed asciiHex := by
  simp [asciiHex, asciiDecimal, WellFormed, Valid, Interval.Valid]

theorem asciiDecimal_contains (x : Nat) :
    Contains (compile asciiDecimal) x ↔ 48 ≤ x ∧ x ≤ 57 := by
  rw [compile_contains _ asciiDecimal_wellFormed]
  simp [asciiDecimal, Denote, Contains, Interval.Contains]

theorem asciiHex_contains (x : Nat) :
    Contains (compile asciiHex) x ↔
      (48 ≤ x ∧ x ≤ 57) ∨ (65 ≤ x ∧ x ≤ 70) ∨ (97 ≤ x ∧ x ≤ 102) := by
  rw [compile_contains _ asciiHex_wellFormed]
  simp [asciiHex, asciiDecimal, Denote, Contains, Interval.Contains]

theorem asciiHex_values_bounded (x : Nat) (present : Contains (compile asciiHex) x) :
    x < 128 := by
  rw [asciiHex_contains] at present
  omega

/-- Restricting a digit class to ASCII cannot admit a non-ASCII digit. -/
theorem ascii_projection_bounded (digits : Expr) (wellFormed : WellFormed digits)
    (x : Nat) (present : Contains (compile (.intersection digits (.leaf [⟨0, 127⟩]))) x) :
    x < 128 := by
  have asciiValid : WellFormed (.leaf [⟨0, 127⟩]) := by
    simp [WellFormed, Valid, Interval.Valid]
  have bound := ((compile_contains (.intersection digits (.leaf [⟨0, 127⟩]))
    ⟨wellFormed, asciiValid⟩ x).mp present).2
  simp only [Denote, Contains, List.mem_singleton, exists_eq_left, Interval.Contains] at bound
  omega

theorem scalar_class_contains (x : Nat) :
    Contains (compile (.leaf scalars)) x ↔
      x ≤ 0x10ffff ∧ ¬ (0xd800 ≤ x ∧ x ≤ 0xdfff) := by
  have wellFormed : WellFormed (.leaf scalars) := by
    simp [WellFormed, scalars, Valid, Interval.Valid]
  rw [compile_contains _ wellFormed]
  exact scalar_membership x

/-! Positive and negative controls: a valid code point can be a non-scalar;
Unicode decimal recognition does not change JSON's ASCII lexical policy. -/

example : Contains (compile asciiHex) 0x41 := (asciiHex_contains _).mpr (by omega)
example : ¬ Contains (compile asciiHex) 0xff21 := by rw [asciiHex_contains]; omega
example : ¬ Contains (compile asciiDecimal) 0x663 := by rw [asciiDecimal_contains]; omega
example : Contains (compile (.leaf codePoints)) 0xd800 := by
  simp [compile, codePoints, IntervalClasses.normalize, IntervalClasses.insert,
    Contains, Interval.Contains]
example : ¬ Contains (compile (.leaf scalars)) 0xd800 := by
  rw [scalar_class_contains]
  omega

#print axioms compile_valid
#print axioms compile_contains
#print axioms double_complement_projects
#print axioms compile_difference_excludes
#print axioms asciiHex_contains
#print axioms ascii_projection_bounded
#print axioms scalar_class_contains

end Mettapedia.Computability.RegularLanguages.ClassExpressions
