import Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

/-! Which atoms and programs render. Integers and strings always render,
symbols and variables exactly when their spelling is safe, and an expression
exactly when its items do. A program renders exactly when its loaded forms
do, and a balanced program followed by another exactly when both do. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem chars?_symbol (symbol : String) : (chars? (.symbol symbol)).isSome = symbolSafe symbol := by
  unfold chars?
  cases symbolSafe symbol <;> rfl

theorem chars?_var (name : String) : (chars? (.var name)).isSome = variableSafe name := by
  unfold chars?
  cases variableSafe name <;> rfl

theorem chars?_int (value : Int) : (chars? (.grounded (.int value))).isSome = true := by
  unfold chars?
  rfl

theorem chars?_string (value : String) : (chars? (.grounded (.string value))).isSome = true := by
  unfold chars?
  rfl

theorem chars?_expression (items : List Atom) :
    (chars? (.expression items)).isSome = (charsList? items).isSome := by
  unfold chars?
  cases charsList? items <;> rfl

/-- A list of atoms renders exactly when each atom does. -/
theorem charsList?_isSome : ∀ (items : List Atom),
    (charsList? items).isSome = true ↔ ∀ item ∈ items, (chars? item).isSome = true
  | [] => by simp [charsList?]
  | item :: items => by
    have rest := charsList?_isSome items
    unfold charsList?
    cases first : chars? item <;> cases later : charsList? items <;> simp_all

/-- A program renders exactly when each of its loaded forms does. -/
theorem renderProgram?_isSome (program : SpaceSemantics.Program) :
    (renderProgram? program).isSome = true ↔
      ∀ atom ∈ SpaceSemantics.loadedAtoms program, (chars? atom).isSome = true := by
  unfold renderProgram?
  rw [Option.isSome_map]
  exact charsList?_isSome _

/-- A balanced program followed by another renders exactly when both do. -/
theorem renderProgram?_append {first second : SpaceSemantics.Program} (balanced : SpaceSemantics.Balanced first) :
    (renderProgram? (first.append second)).isSome = true ↔
      (renderProgram? first).isSome = true ∧ (renderProgram? second).isSome = true := by
  simp only [renderProgram?_isSome, SpaceSemantics.loadedAtoms_append balanced, List.mem_append]
  exact ⟨fun both => ⟨fun atom inside => both atom (.inl inside), fun atom inside => both atom (.inr inside)⟩,
    fun ⟨left, right⟩ atom inside => inside.elim (left atom) (right atom)⟩

/-- Negative control: the anonymous variable marker has no spelling, so an
expression holding it does not render. -/
theorem anonymous_item_refused : (chars? (.expression [.symbol "f", .var "_"])).isSome = false := by
  decide

/-- Positive control: an expression of a safe symbol, a variable, an integer
and a string renders. -/
theorem mixed_items_rendered :
    (chars? (.expression [.symbol "f", .var "x", .grounded (.int (-3)), .grounded (.string "é")])).isSome = true := by
  decide

#print axioms charsList?_isSome
#print axioms renderProgram?_isSome
#print axioms renderProgram?_append

end Mettapedia.Languages.MeTTa.PeTTa.ReadAfterRender
