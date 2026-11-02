import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRScalarReading
import Std.Data.String.ToNat

/-! The compact CHR encoding separates predicates and ground values. Equal
successful encodings imply equal source data, including recursively nested
tuples. Pool indices retain their actual entries; no uniqueness assumption on
the vocabulary is needed for this direction. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ValueInjectivity

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax

private theorem reference_injective (tag : String) {first second : Nat}
    (same : Pattern.fvar (tag ++ toString first) = .fvar (tag ++ toString second)) : first = second := by
  have names := Pattern.fvar.inj same
  exact Nat.repr_injective ((String.append_right_inj tag).mp names)

theorem scalar_injective : Function.Injective scalarRef := by
  intro first second same
  exact reference_injective "chr:scalar:" same

theorem predicate_injective : Function.Injective predicateRef := by
  intro first second same
  exact reference_injective "chr:predicate:" same

private theorem indexed_value_unique {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (first second : α) (index : Nat)
    (left : items.idxOf? first = some index) (right : items.idxOf? second = some index) : first = second := by
  obtain ⟨within, firstAt, _⟩ := List.idxOf?_eq_some_iff.mp left
  obtain ⟨_, secondAt, _⟩ := List.idxOf?_eq_some_iff.mp right
  exact firstAt.symm.trans secondAt

theorem traverse_cons {α β : Type} (encode : α → Option β) (first : α) (rest : List α)
    (outputs : List β) (encoded : (first :: rest).mapM encode = some outputs) :
    ∃ value values, encode first = some value ∧ rest.mapM encode = some values ∧ outputs = value :: values := by
  rw [List.mapM_cons] at encoded
  change ((encode first).bind fun value => (rest.mapM encode).bind fun values => some (value :: values)) =
    some outputs at encoded
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
  obtain ⟨value, firstRead, values, restRead, same⟩ := encoded
  exact ⟨value, values, firstRead, restRead, same.symm⟩

private theorem traverse_injective {α β : Type} (encode : α → Option β)
    (first second : List α) (codes : List β)
    (step : ∀ item ∈ first, ∀ other code, encode item = some code → encode other = some code → item = other)
    (left : first.mapM encode = some codes) (right : second.mapM encode = some codes) : first = second := by
  induction first generalizing second codes with
  | nil =>
    have empty : codes = [] := by simpa using left.symm
    subst codes
    cases second with
    | nil => rfl
    | cons item rest => obtain ⟨_, _, _, _, same⟩ := traverse_cons encode item rest [] right; cases same
  | cons item rest ih =>
    obtain ⟨code, tail, itemRead, restRead, same⟩ := traverse_cons encode item rest codes left
    subst codes
    cases second with
    | nil => simp at right
    | cons other others =>
      obtain ⟨otherCode, otherTail, otherRead, othersRead, same⟩ := traverse_cons encode other others (code :: tail) right
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      have headSame := step item List.mem_cons_self other code itemRead otherRead
      have tailSame := ih others tail (fun child member => step child (List.mem_cons_of_mem item member)) restRead othersRead
      exact congrArg₂ List.cons headSame tailSame

theorem tuple_encoding (vocabulary : Vocabulary) (fields : List Value) (code : Pattern)
    (encoded : value? vocabulary (.tuple fields) = some code) :
    ∃ values, fields.mapM (value? vocabulary) = some values ∧ code = .apply "ChrTuple" [vector values] := by
  rw [value?] at encoded
  change ((fields.mapM (value? vocabulary)).bind fun values =>
    some (Pattern.apply "ChrTuple" [vector values])) = some code at encoded
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at encoded
  obtain ⟨values, read, same⟩ := encoded
  exact ⟨values, read, same.symm⟩

theorem value_injective (vocabulary : Vocabulary) (first second : Value) (code : Pattern)
    (left : value? vocabulary first = some code) (right : value? vocabulary second = some code) : first = second := by
  cases first with
  | integer number =>
    have same : integer number = code := by simpa only [value?, Option.some.injEq] using left
    subst code
    cases second with
    | integer other =>
      have same : integer other = integer number := by simpa only [value?, Option.some.injEq] using right
      exact congrArg Value.integer (ScalarReading.integer_injective same).symm
    | atom name =>
      cases indexRead : vocabulary.scalars.idxOf? (.atom name) with
      | none => simp [value?, indexRead] at right
      | some index => simp [value?, indexRead, scalarRef, integer] at right
    | tuple fields =>
      obtain ⟨values, _, same⟩ := tuple_encoding vocabulary fields (integer number) right
      simp [integer] at same
  | atom name =>
    cases indexRead : vocabulary.scalars.idxOf? (.atom name) with
    | none => simp [value?, indexRead] at left
    | some index =>
      have same : scalarRef index = code := by simpa [value?, indexRead] using left
      subst code
      cases second with
      | integer number => simp [value?, scalarRef, integer] at right
      | atom other =>
        cases otherRead : vocabulary.scalars.idxOf? (.atom other) with
        | none => simp [value?, otherRead] at right
        | some otherIndex =>
          have same : scalarRef otherIndex = scalarRef index := by simpa [value?, otherRead] using right
          have sameIndex := scalar_injective same
          subst otherIndex
          exact indexed_value_unique vocabulary.scalars (.atom name) (.atom other) index indexRead otherRead
      | tuple fields =>
        obtain ⟨values, _, same⟩ := tuple_encoding vocabulary fields (scalarRef index) right
        simp [scalarRef] at same
  | tuple fields =>
    obtain ⟨values, fieldsRead, rfl⟩ := tuple_encoding vocabulary fields code left
    cases second with
    | integer number => simp [value?, integer] at right
    | atom name =>
      cases indexRead : vocabulary.scalars.idxOf? (.atom name) with
      | none => simp [value?, indexRead] at right
      | some index => simp [value?, indexRead, scalarRef] at right
    | tuple others =>
      obtain ⟨otherValues, othersRead, same⟩ := tuple_encoding vocabulary others (.apply "ChrTuple" [vector values]) right
      have sameValues : values = otherValues := by simpa [vector] using same
      subst otherValues
      apply congrArg Value.tuple
      exact traverse_injective (value? vocabulary) fields others values
        (fun field _ other result firstRead secondRead => value_injective vocabulary field other result firstRead secondRead)
        fieldsRead othersRead
termination_by sizeOf first

theorem constraint_injective (vocabulary : Vocabulary) (first second : Constraint) (code : Pattern)
    (left : constraint? vocabulary first = some code) (right : constraint? vocabulary second = some code) :
    first = second := by
  change ((vocabulary.predicates.idxOf? first.name).bind fun index =>
    (first.arguments.mapM (value? vocabulary)).bind fun fields =>
      some (Pattern.apply "ChrConstraint" [predicateRef index, vector fields])) = some code at left
  change ((vocabulary.predicates.idxOf? second.name).bind fun index =>
    (second.arguments.mapM (value? vocabulary)).bind fun fields =>
      some (Pattern.apply "ChrConstraint" [predicateRef index, vector fields])) = some code at right
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at left right
  obtain ⟨firstIndex, firstName, firstFields, firstRead, same⟩ := left
  obtain ⟨secondIndex, secondName, secondFields, secondRead, otherSame⟩ := right
  have arguments := (Pattern.apply.inj (same.trans otherSame.symm)).2
  have sameIndex := predicate_injective (List.cons.inj arguments).1
  subst secondIndex
  have names := indexed_value_unique vocabulary.predicates first.name second.name firstIndex firstName secondName
  have fieldsSame : firstFields = secondFields := by
    simpa only [vector, Pattern.collection.injEq, true_and, and_true] using
      (List.cons.inj (List.cons.inj arguments).2).1
  subst secondFields
  have values := traverse_injective (value? vocabulary) first.arguments second.arguments firstFields
    (fun field _ other result leftRead rightRead => value_injective vocabulary field other result leftRead rightRead)
    firstRead secondRead
  cases first
  cases second
  cases names
  cases values
  rfl

#print axioms value_injective
#print axioms constraint_injective

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ValueInjectivity
