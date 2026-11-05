import Mettapedia.GSLT.LanguageDef.Collections.CoreList

/-!
# Exact printing of core lists on the CeTTa wire

These laws concern the existing `CettaWire.encodeList` and `Term.render`.
The wire spells the empty list `LNil` and each cell `(LCons element tail)`,
with one separating space before each argument. Element rendering remains
the element encoder's responsibility; strings use the existing `reprStr`.

The fold equations below specify that actual printer, rather than defining
another printer. They do not assert a text-parser round trip. In particular,
symbols are printed verbatim: unrestricted symbol names can collide with
numbers or even with a different application shape. The controls exhibit
those boundaries alongside exact order, multiplicity and string spelling.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.WirePrinting

open CettaWire (Term encodeList decodeList)

universe u v

theorem encoded_nil {α : Type u} (encode : α → Term) :
    (encodeList encode []).render = "LNil" := rfl

theorem encoded_cons {α : Type u} (encode : α → Term) (value : α) (values : List α) :
    (encodeList encode (value :: values)).render =
      "(LCons " ++ (encode value).render ++ " " ++ (encodeList encode values).render ++ ")" := by
  simp [encodeList, Term.render, Term.renderArguments, String.append_assoc]
  rw [← String.append_assoc]
  rfl

/-- Exact delimiter/spacing and ordered nesting for every element encoder. -/
theorem encoded_fold {α : Type u} (encode : α → Term) (values : List α) :
    (encodeList encode values).render =
      values.foldr (fun value tail => "(LCons " ++ (encode value).render ++ " " ++ tail ++ ")") "LNil" := by
  induction values with
  | nil => rfl
  | cons value values ih => rw [encoded_cons, List.foldr_cons, ih]

/-- A separately established element-printing contract composes with the
list encoder without changing the order or number of element occurrences. -/
theorem encoded_elements {α : Type u} (encode : α → Term) (text : α → String)
    (elements : ∀ value, (encode value).render = text value) (values : List α) :
    (encodeList encode values).render =
      values.foldr (fun value tail => "(LCons " ++ text value ++ " " ++ tail ++ ")") "LNil" := by
  rw [encoded_fold]
  simp only [elements]

/-- Appending source lists nests the later list at the first list's final
tail position; it is not concatenation of two complete printed values. -/
theorem encoded_append {α : Type u} (encode : α → Term) (first later : List α) :
    (encodeList encode (first ++ later)).render =
      first.foldr (fun value tail => "(LCons " ++ (encode value).render ++ " " ++ tail ++ ")")
        (encodeList encode later).render := by
  induction first with
  | nil => rfl
  | cons value values ih =>
    rw [List.cons_append, encoded_cons, List.foldr_cons, ih]

theorem encoded_map {α : Type u} {β : Type v} (encode : β → Term)
    (transform : α → β) (values : List α) :
    (encodeList encode (values.map transform)).render = (encodeList (encode ∘ transform) values).render :=
  congrArg Term.render (CettaWire.encodeList_map encode transform values)

/-- The existing core manifestation uses exactly this physical encoder. -/
theorem core_wire_elements {α : Type u} (encode : α → Term) (values : List α) :
    (CoreList.wire.write (values.map encode)).render = (encodeList encode values).render := by
  simp only [CoreList.wire, CettaWire.encodeList_map, Function.id_comp]

theorem core_wire_fold (values : List Term) :
    (CoreList.wire.write values).render =
      values.foldr (fun value tail => "(LCons " ++ value.render ++ " " ++ tail ++ ")") "LNil" :=
  encoded_fold id values

theorem core_wire_element_text {α : Type u} (encode : α → Term) (text : α → String)
    (elements : ∀ value, (encode value).render = text value) (values : List α) :
    (CoreList.wire.write (values.map encode)).render =
      values.foldr (fun value tail => "(LCons " ++ text value ++ " " ++ tail ++ ")") "LNil" := by
  rw [core_wire_elements]
  exact encoded_elements encode text elements values

theorem strings (values : List String) :
    (encodeList Term.string values).render =
      values.foldr (fun value tail => "(LCons " ++ reprStr value ++ " " ++ tail ++ ")") "LNil" :=
  encoded_elements Term.string reprStr (fun _ => rfl) values

theorem symbols (values : List String) :
    (encodeList Term.symbol values).render =
      values.foldr (fun value tail => "(LCons " ++ value ++ " " ++ tail ++ ")") "LNil" :=
  encoded_elements Term.symbol id (fun _ => rfl) values

theorem naturals (values : List Nat) :
    (encodeList Term.natural values).render =
      values.foldr (fun value tail => "(LCons " ++ toString value ++ " " ++ tail ++ ")") "LNil" :=
  encoded_elements Term.natural toString (fun _ => rfl) values

namespace Controls

theorem empty_is_wire_nil :
    (CoreList.wire.write []).render = "LNil" ∧
      (CoreList.wire.write []).render ≠ "()" ∧ (CoreList.wire.write []).render ≠ "(LNil)" := by decide

theorem symbols_keep_order_and_duplicates :
    (encodeList Term.symbol ["a", "b", "a"]).render = "(LCons a (LCons b (LCons a LNil)))" ∧
      (encodeList Term.symbol ["a", "b"]).render ≠ (encodeList Term.symbol ["b", "a"]).render ∧
      (encodeList Term.symbol ["a", "a"]).render ≠ (encodeList Term.symbol ["a"]).render := by decide

/-- Concrete natural spelling is checked by kernel reduction. -/
theorem naturals_have_decimal_spelling :
    (encodeList Term.natural [0, 7, 42]).render = "(LCons 0 (LCons 7 (LCons 42 LNil)))" := by decide

-- `reprStr` uses the library pretty-printer, whose recursive engine is
-- opaque to kernel reduction. These are executable spelling controls;
-- the theorem `strings` above proves composition with its actual result.
#guard (encodeList Term.string ["a b", "c"]).render == "(LCons \"a b\" (LCons \"c\" LNil))"
#guard (Term.string "a\"b").render == "\"a\\\"b\""
#guard (Term.string "a\\b").render == "\"a\\\\b\""
#guard (Term.string "\n").render == "\"\\n\""
#guard (encodeList Term.natural [7]).render != (encodeList Term.string ["7"]).render

theorem nested_lists_use_the_same_encoder :
    (encodeList (encodeList Term.natural) [[], [1, 2]]).render =
      "(LCons LNil (LCons (LCons 1 (LCons 2 LNil)) LNil))" := by decide

theorem wrong_arity_and_improper_tail_are_not_lists :
    decodeList some (.application "LNil" []) = (none : Option (List Term)) ∧
      decodeList some (.application "LCons" [.symbol "a"]) = (none : Option (List Term)) ∧
      decodeList some (.application "LCons" [.symbol "a", .symbol "tail"]) = (none : Option (List Term)) := by
  simp [decodeList]

/-- Injectivity of the typed list encoder does not imply text injectivity
for the unrestricted physical symbol constructor. -/
theorem numeric_symbol_collides_in_text :
    Term.symbol "7" ≠ Term.natural 7 ∧ (Term.symbol "7").render = (Term.natural 7).render := by
  constructor
  · intro same
    cases same
  · decide

/-- A verbatim space-containing symbol makes a valid one-cell list print
like a wrong-arity application. Typed decoding still distinguishes them. -/
theorem unrestricted_symbol_can_hide_wrong_arity :
    (encodeList id [Term.symbol "a b"]).render =
        (Term.application "LCons" [.symbol "a", .symbol "b", .symbol "LNil"]).render ∧
      decodeList some (encodeList id [Term.symbol "a b"]) = some [Term.symbol "a b"] ∧
      decodeList some (.application "LCons" [.symbol "a", .symbol "b", .symbol "LNil"]) =
        (none : Option (List Term)) := by
  exact ⟨by decide, CettaWire.decodeList_encodeList some id (fun _ => rfl) _, by simp [decodeList]⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.WirePrinting
