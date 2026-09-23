import Mettapedia.Languages.MeTTa.HE.Spec.Type

/-!
# Operands against a symbol that no annotation names

A typed equality compares its operands only when they share a type: some
type of one operand matches some type of the other.  A symbol that no
`(: symbol type)` annotation names has the single type `%Undefined%`, and
`match_types` takes `%Undefined%` as a wildcard on either side.  Such a
symbol therefore shares a type with every operand, in either position, and a
compiled program may record that fact once instead of asking for both types
at each comparison.

The fact reads only the annotations that name the symbol
(`undeclared_iff`): atoms that do not annotate it can be added or removed
without disturbing it.  Declaring the symbol replaces the default type with
its declared types; `%Undefined%` remains a type if explicitly declared.
-/

namespace Mettapedia.Languages.MeTTa.UndeclaredOperandType

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Type

/-- Two operands share a type when either one has no type, or some type of
the right operand matches some type of the left one from no bindings. -/
def SharesType (space : Space) (left right : Atom) : Prop :=
  (∀ type, ¬TypeOfRel space left type) ∨
  (∀ type, ¬TypeOfRel space right type) ∨
  ∃ leftType rightType output,
    TypeOfRel space left leftType ∧ TypeOfRel space right rightType ∧
    TypeMatchRel rightType leftType Bindings.empty output

/-- No atom annotates the target exactly when annotation extraction finds
no type. -/
theorem undeclared_iff (target : Atom) (atoms : List Atom) :
    AnnotationTypesRel target atoms [] ↔
      ∀ atom ∈ atoms, ∀ type,
        atom ≠ .expression [.symbol ":", target, type] := by
  induction atoms with
  | nil => exact ⟨fun _ => by simp, fun _ => .nil⟩
  | cons head tail induction =>
      constructor
      · intro extracted
        cases extracted with
        | skip notAnnotation rest =>
            intro atom member type
            rcases List.mem_cons.1 member with same | later
            · subst same
              exact notAnnotation type
            · exact (induction.1 rest) atom later type
      · intro none
        exact .skip (none head (by simp))
          (induction.2 fun atom member => none atom (by simp [member]))

/-- Appending atoms keeps a symbol undeclared exactly when they do not
annotate it either. -/
theorem undeclared_append_iff (target : Atom) (atoms more : List Atom) :
    AnnotationTypesRel target (atoms ++ more) [] ↔
      AnnotationTypesRel target atoms [] ∧
        AnnotationTypesRel target more [] := by
  simp only [undeclared_iff, List.mem_append]
  constructor
  · intro none
    exact ⟨fun atom member => none atom (Or.inl member),
      fun atom member => none atom (Or.inr member)⟩
  · rintro ⟨early, late⟩ atom (member | member)
    · exact early atom member
    · exact late atom member

/-- A symbol that no annotation names has exactly the type `%Undefined%`. -/
theorem typeOf_undeclared {space : Space} {name : String}
    (undeclared : AnnotationTypesRel (.symbol name) space.atoms [])
    (type : Atom) :
    TypeOfRel space (.symbol name) type ↔ type = Atom.undefinedType := by
  constructor
  · rintro ⟨types, typed, member⟩
    cases typed with
    | symbolKnown extracted nonempty =>
        exact (nonempty (AnnotationTypesRel.unique extracted undeclared)).elim
    | symbolUndefined _ => simpa using member
  · rintro rfl
    exact ⟨[Atom.undefinedType], .symbolUndefined undeclared, by simp⟩

/-- An undeclared symbol on the left shares a type with every operand. -/
theorem sharesType_undeclared_left {space : Space} {name : String}
    (undeclared : AnnotationTypesRel (.symbol name) space.atoms [])
    (right : Atom) :
    SharesType space (.symbol name) right := by
  by_cases typed : ∃ rightType, TypeOfRel space right rightType
  · obtain ⟨rightType, rightTyped⟩ := typed
    exact Or.inr (Or.inr ⟨Atom.undefinedType, rightType, Bindings.empty,
      (typeOf_undeclared undeclared _).2 rfl, rightTyped,
      .undefinedRight rightType Bindings.empty⟩)
  · exact Or.inr (Or.inl fun type rightTyped => typed ⟨type, rightTyped⟩)

/-- An undeclared symbol on the right shares a type with every operand. -/
theorem sharesType_undeclared_right {space : Space} {name : String}
    (undeclared : AnnotationTypesRel (.symbol name) space.atoms [])
    (left : Atom) :
    SharesType space left (.symbol name) := by
  by_cases typed : ∃ leftType, TypeOfRel space left leftType
  · obtain ⟨leftType, leftTyped⟩ := typed
    exact Or.inr (Or.inr ⟨leftType, Atom.undefinedType, Bindings.empty,
      leftTyped, (typeOf_undeclared undeclared _).2 rfl,
      .undefinedLeft leftType Bindings.empty⟩)
  · exact Or.inl fun type leftTyped => typed ⟨type, leftTyped⟩

/-! ## Controls -/

private def labelled : Space :=
  ⟨[.expression [.symbol ":", .symbol "Tag", .symbol "Label"]]⟩

/-- Positive: in a space without annotations, `Nil` shares a type with a
number. -/
example : SharesType ⟨[]⟩ (.symbol "Nil") (.grounded (.int 1)) :=
  sharesType_undeclared_left .nil _

/-- Negative: once `Tag` is declared, `%Undefined%` is no longer among its
types, so the wildcard argument no longer applies to it. -/
example : ¬TypeOfRel labelled (.symbol "Tag") Atom.undefinedType := by
  rintro ⟨types, typed, member⟩
  cases typed with
  | symbolKnown extracted _ =>
      have found : types = [.symbol "Label"] :=
        AnnotationTypesRel.unique extracted (.hit .nil)
      subst found
      simp [Atom.undefinedType] at member
  | symbolUndefined extracted =>
      have found : ([] : List Atom) = [.symbol "Label"] :=
        AnnotationTypesRel.unique extracted (.hit .nil)
      simp at found

end Mettapedia.Languages.MeTTa.UndeclaredOperandType
