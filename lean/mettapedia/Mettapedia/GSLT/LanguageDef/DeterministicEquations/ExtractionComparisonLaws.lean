import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionEliminationLaws
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.DataEquality

/-! # Checked comparisons and lazy Boolean composition

Structural data equality implements source equality only after injectivity of
the actual source encoder has been proved. Branch composition runs the selected
body; the unselected body is not an evaluated operand. Existing primitive
computations transport through explicit agreement on the retained program.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction

theorem encodeByte_injective : Function.Injective encodeByte := by
  intro left right same
  have values := natural_injective same
  exact UInt8.toNat_inj.mp values

theorem encodeList_injective {α : Type} {encode : α → Term}
    (injective : Function.Injective encode) : Function.Injective (encodeList encode) := by
  intro left
  induction left with
  | nil =>
      intro right same
      cases right with
      | nil => rfl
      | cons first rest => cases same
  | cons first rest ih =>
      intro right same
      cases right with
      | nil => cases same
      | cons other others =>
          have fields : encode first = encode other ∧ encodeList encode rest = encodeList encode others := by
            simpa only [encodeList, List.map_cons, Term.list.injEq, List.cons.injEq] using same
          exact congrArg₂ List.cons (injective fields.1) (ih fields.2)

theorem base_primitive_to_data {head : String} {arguments : List Term} {result : PrimitiveResult}
    (different : head ≠ "nik:data-eq")
    (computed : productDivisionHost.primitive head arguments = result) :
    dataEqualityHost.primitive head arguments = result :=
  (dataEqualityHost_prior head arguments different).trans computed

theorem base_computation_to_data (program : Program)
    (absent : "nik:data-eq" ∉ program.calledHeads)
    (head : String) (used : head ∈ program.calledHeads) (arguments : List Term) (result : Term)
    (computed : Applies program productDivisionHost head arguments result) :
    Applies program dataEqualityHost head arguments result :=
  (Applies.host_iff program (dataEqualityHost_agrees _ absent) head used arguments result).mp computed

theorem data_head_absent (program : Program)
    (absent : program.calledHeads.contains "nik:data-eq" = false) :
    "nik:data-eq" ∉ program.calledHeads := by
  simpa using absent

theorem encoded_comparison {α : Type} [DecidableEq α] {program : Program}
    (encode : α → Term) (injective : Function.Injective encode) (left right : α)
    (undefined : program.defines "nik:data-eq" = false) :
    Applies program dataEqualityHost "nik:data-eq" [encode left, encode right]
      (boolean (decide (left = right))) :=
  Applies.primitive undefined (dataEqualityHost_encoded encode injective left right)

theorem encoded_beq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (encode : α → Term) (injective : Function.Injective encode) (left right : α) :
    dataEqualityHost.primitive "nik:data-eq" [encode left, encode right] =
      .value (boolean (left == right)) := by
  rw [Bool.beq_eq_decide_eq]
  exact dataEqualityHost_encoded encode injective left right

theorem decision_and (left right : Prop) [Decidable left] [Decidable right]
    [Decidable (left ∧ right)] :
    decide (left ∧ right) = (if left then decide right else false) := by
  by_cases holds : left <;> simp [holds]

theorem decision_or (left right : Prop) [Decidable left] [Decidable right]
    [Decidable (left ∨ right)] :
    decide (left ∨ right) = (if left then true else decide right) := by
  by_cases holds : left <;> simp [holds]

theorem boolean_if (condition whenTrue whenFalse : Bool) :
    (if condition then boolean whenTrue else boolean whenFalse) =
      boolean (if condition then whenTrue else whenFalse) := by
  cases condition <;> rfl

theorem association_lookup_cons {α β : Type} [BEq α] [LawfulBEq α] [DecidableEq α]
    (key found : α) (value : β) (rest : List (α × β)) :
    ((found, value) :: rest).lookup key =
      (if key = found then some value else rest.lookup key) := by
  rw [List.lookup_cons, Bool.beq_eq_decide_eq]
  by_cases same : key = found <;> simp [same]

theorem applies_boolean_values {program : Program} {host : Host}
    (head : String) (captures : List Term) (condition : Bool) (whenFalse whenTrue : Term)
    (falseCase : Applies program host head (.sym "False" :: captures) whenFalse)
    (trueCase : Applies program host head (.sym "True" :: captures) whenTrue) :
    Applies program host head (boolean condition :: captures)
      (if condition then whenTrue else whenFalse) :=
  applies_bool_elimination id head captures condition whenFalse whenTrue falseCase trueCase

/-- Removing foreign heads preserves the first selected row and its bindings. -/
theorem selection_head_filter (program : Program) (head : String) (arguments : List Term) :
    program.select head arguments =
      Program.select (program.filter (fun row : Equation => decide (row.head = head))) head arguments := by
  induction program with
  | nil => rfl
  | cons row rest ih =>
      simp only [Program.select] at ih ⊢
      by_cases same : row.head = head
      · simp only [List.filter_cons, same, decide_true, if_true, List.findSome?_cons]
        rw [ih]
      · simpa only [List.filter_cons, same, decide_false, if_false,
          List.findSome?_cons, false_and, Bool.false_eq_true] using ih

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction
