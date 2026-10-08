import Mettapedia.Languages.MM0.MeTTa.Data.VectorPublication

/-!
# Clearing private MM0 stores

The retained source removes a caller-supplied expression pattern in one pass.
The proof-vector and cache callers supply distinct variables of their actual
row arity. The reference enumeration loop is also checked, including duplicate
occurrences; both paths clear the private rows and preserve other spaces and
cells. Row shape is independent of proof validity and cache currency.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SpaceClearing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Store (natural)

private def environment (handle : Handle) (items : List Atom) (index : Nat) : Subst :=
  [("size", natural items.length), ("index", natural index),
    ("rows", .expression items), ("space", handleValue handle)]

private def without (stored removed : List Atom) : List Atom :=
  stored.filter fun row => !removed.any (fun pattern => Effects.removalMatches pattern row)

private theorem without_after_erase (stored removed : List Atom) (first : Atom) :
    without (stored.filter fun row => !Effects.removalMatches first row) removed =
      without stored (first :: removed) := by
  simp only [without, List.filter_filter, List.any_cons]
  congr 1
  funext row
  cases Effects.removalMatches first row <;>
    cases removed.any (fun pattern => Effects.removalMatches pattern row) <;> rfl

private theorem remove_clause (handle : Handle) (items : List Atom) (index : Nat) :
    clauses program "mm0:remove-rows"
      [handleValue handle, .expression items, natural index, natural items.length] =
      [.evaluate (environment handle items index) removeRowsEquation.body] := by
  rw [clauses_use_only_the_named_equations, remove_rows_equation_is_unique]
  simp [remove_rows_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private def loopBody : Atom :=
  match removeRowsEquation.body with
  | .expression [_, _, body, _] => body
  | _ => .expression []

private def erasedBody : Atom :=
  match loopBody with
  | .expression [_, _, _, .expression [_, _, _, body]] => body
  | _ => .expression []

private theorem body_shape :
    removeRowsEquation.body = .expression [.symbol "if",
      .expression [.symbol "<", .var "index", .var "size"], loopBody,
      .grounded (.bool true)] := by decide

private theorem loop_body_shape :
    loopBody = .expression [.symbol "let", .var "row",
      .expression [.symbol "index-atom", .var "rows", .var "index"],
      .expression [.symbol "let", .var "removed",
        .expression [.symbol "remove-atom", .var "space", .var "row"], erasedBody]] := by decide

private theorem erased_body_shape :
    erasedBody = .expression [.symbol "mm0:remove-rows", .var "space", .var "rows",
      .expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"] := by decide

private theorem next_call_returns (bindings : Subst) (before after : State)
    (handle : Handle) (items : List Atom) (index : Nat)
    (spaceCaptured : applySubst bindings (.var "space") = handleValue handle)
    (rowsCaptured : applySubst bindings (.var "rows") = .expression items)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (sizeCaptured : applySubst bindings (.var "size") = natural items.length)
    (child : PureReturns program (environment handle items (index + 1)) before
      removeRowsEquation.body after (boolean true)) :
    PureReturns program bindings before erasedBody after (boolean true) := by
  rw [erased_body_shape]
  apply call_returns program bindings before after "mm0:remove-rows" _ _ (by decide) _ (by decide)
  have entered := authored_function_arguments_return program bindings
    (environment handle items (index + 1)) before after "mm0:remove-rows"
    [handleValue handle, .expression items, natural (index + 1), natural items.length] 4
    removeRowsEquation.body (boolean true) (by decide) (by decide)
    (remove_clause handle items (index + 1)) child
  have last := variable_arguments_return program bindings before after (.function "mm0:remove-rows")
    ["size"] [handleValue handle, .expression items, natural (index + 1)] 3 (boolean true)
    (by simpa only [List.map_cons, List.map_nil, sizeCaptured, List.cons_append,
      List.nil_append, List.length_cons, List.length_nil, Nat.reduceAdd] using entered)
  have increment : PureReturns program bindings before
      (.expression [.symbol "+", .var "index", .grounded (.int 1)]) before (natural (index + 1)) := by
    apply native_binary_call_returns program bindings before before before before "+"
      _ _ (natural index) (.grounded (.int 1)) _
      (by decide) (by decide) (by decide) (by decide) _
      (grounded_returns program bindings before (.int 1)) _ (by decide)
    · simpa only [indexCaptured] using variable_returns program bindings before "index"
    · simp [StdLib.apply, natural, Int.natCast_add]
  have next := evaluated_argument_returns program bindings before before after (.function "mm0:remove-rows")
    (.expression [.symbol "+", .var "index", .grounded (.int 1)]) (natural (index + 1))
    (boolean true) [.var "size"] [handleValue handle, .expression items] 2
    (by decide +kernel) increment last
  have rows := raw_argument_answers program bindings before after "mm0:remove-rows" (.var "rows")
    [.expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"]
    [handleValue handle] 1 [boolean true] (by decide)
    (by simpa only [rowsCaptured, List.cons_append, List.nil_append, Nat.reduceAdd] using next)
  exact raw_argument_answers program bindings before after "mm0:remove-rows" (.var "space")
    [.var "rows", .expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"]
    [] 0 [boolean true] (by decide) (by simpa only [spaceCaptured, List.nil_append] using rows)

private theorem remove_body_returns (remaining processed : List Atom) (before : State)
    (handle : Handle) (stored : List Atom) (represented : before.read handle = some stored)
    (admitted : ∀ item ∈ remaining, ∃ first rest, item = .expression (first :: rest)) :
    ∃ after, PureReturns program (environment handle (processed ++ remaining) processed.length) before
        removeRowsEquation.body after (boolean true) ∧
      after.read handle = some (without stored remaining) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  induction remaining generalizing processed before stored with
  | nil =>
      refine ⟨before, ?_, ?_, fun _ _ => rfl, rfl⟩
      · rw [body_shape]
        apply if_returns program _ before before before _ _ _ _ _
        · apply native_variable_call_returns program _ before before "<" ["index", "size"]
            (boolean false) (by decide) (by decide) _ (by decide)
          simp [environment, applySubst, Subst.lookup, StdLib.apply, natural, boolean]
        · exact grounded_returns program _ before (.bool true)
      · simpa [without] using represented
  | cons first rest ih =>
      obtain ⟨head, fields, same⟩ := admitted first (by simp)
      subst first
      let first : Atom := .expression (head :: fields)
      have firstShape : first = .expression (head :: fields) := rfl
      obtain ⟨middle, erased⟩ := Effects.erase_exists_of_read_some represented first
      change Effects.erase before handle (.expression (head :: fields)) = some middle at erased
      obtain ⟨oldRows, readBefore, readMiddle⟩ := Effects.erase_reads_back erased
      have old : oldRows = stored := Option.some.inj (readBefore.symm.trans represented)
      subst oldRows
      obtain ⟨after, child, readAfter, otherAfter, cellsAfter⟩ :=
        ih (processed ++ [first]) middle (stored.filter fun row => !Effects.removalMatches first row) readMiddle
          (fun item member => admitted item (by simp [member]))
      let items := processed ++ first :: rest
      let bindings := environment handle items processed.length
      let withRow := ("row", first) :: bindings
      let withErased := ("removed", boolean true) :: withRow
      refine ⟨after, ?_, ?_, ?_, ?_⟩
      · rw [body_shape]
        apply if_returns program bindings before before after _ _ _ _ _
        · apply native_variable_call_returns program bindings before before "<" ["index", "size"]
            (boolean true) (by decide) (by decide) _ (by decide)
          simp [bindings, environment, items, applySubst, Subst.lookup,
            StdLib.apply, natural, boolean]
        · change PureReturns program bindings before loopBody after (boolean true)
          rw [loop_body_shape]
          apply let_returns program bindings withRow before before after (.var "row") _ _ first _
          · apply native_variable_call_returns program bindings before before "index-atom" ["rows", "index"]
              first (by decide) (by decide) _ (by decide)
            simp [bindings, environment, items, applySubst, Subst.lookup, StdLib.apply,
              natural]
          · simp [SpaceSemantics.matchValue, matchAtom, bindings, environment, Subst.lookup, withRow]
          · apply let_returns program withRow withErased before middle after (.var "removed") _ _
              (boolean true) _
            · apply native_variable_call_returns program withRow before middle "remove-atom" ["space", "row"]
                (boolean true) (by decide) (by decide) _ (by decide)
              simp [withRow, bindings, environment, applySubst, Subst.lookup, StdLib.apply, represented, firstShape, erased]
            · simp [SpaceSemantics.matchValue, matchAtom, withRow, bindings, environment,
                Subst.lookup, withErased]
            · apply next_call_returns withErased middle after handle items processed.length
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simpa [items, List.append_assoc] using child
      · simpa [without_after_erase] using readAfter
      · intro other different
        rw [otherAfter other different, Effects.erase_read_other erased different]
      · rw [cellsAfter, Effects.erase_preserves_cells erased]

private def clearEnvironment (handle : Handle) : Subst := [("space", handleValue handle)]

def enumeratedClearBody : Atom :=
  .expression [.symbol "let", .var "rows",
    .expression [.symbol "collapse", .expression [.symbol "get-atoms", .var "space"]],
    .expression [.symbol "mm0:remove-rows", .var "space", .var "rows",
      .grounded (.int 0), .expression [.symbol "size-atom", .var "rows"]]]

private def clearRowsBody : Atom :=
  match enumeratedClearBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private theorem clear_body_shape :
    enumeratedClearBody = .expression [.symbol "let", .var "rows",
      .expression [.symbol "collapse", .expression [.symbol "get-atoms", .var "space"]],
      clearRowsBody] := by decide

private theorem clear_rows_body_shape :
    clearRowsBody = .expression [.symbol "mm0:remove-rows", .var "space", .var "rows",
      .grounded (.int 0), .expression [.symbol "size-atom", .var "rows"]] := by decide

private theorem clear_rows_returns (before after : State) (handle : Handle) (items : List Atom)
    (child : PureReturns program (environment handle items 0) before
      removeRowsEquation.body after (boolean true)) :
    PureReturns program (("rows", .expression items) :: clearEnvironment handle) before
      clearRowsBody after (boolean true) := by
  let bindings := ("rows", .expression items) :: clearEnvironment handle
  rw [clear_rows_body_shape]
  apply call_returns program bindings before after "mm0:remove-rows" _ _ (by decide) _ (by decide)
  have entered := authored_function_arguments_return program bindings
    (environment handle items 0) before after "mm0:remove-rows"
    [handleValue handle, .expression items, natural 0, natural items.length] 4
    removeRowsEquation.body (boolean true) (by decide) (by decide)
    (remove_clause handle items 0) child
  have size : PureReturns program bindings before
      (.expression [.symbol "size-atom", .var "rows"]) before (natural items.length) := by
    apply native_variable_call_returns program bindings before before "size-atom" ["rows"]
      _ (by decide) (by decide) _ (by decide)
    simp [bindings, clearEnvironment, applySubst, Subst.lookup, StdLib.apply, natural]
  have last := evaluated_argument_returns program bindings before before after (.function "mm0:remove-rows")
    (.expression [.symbol "size-atom", .var "rows"]) (natural items.length) (boolean true)
    [] [handleValue handle, .expression items, natural 0] 3 (by decide +kernel) size entered
  have index := evaluated_argument_returns program bindings before before after (.function "mm0:remove-rows")
    (.grounded (.int 0)) (natural 0) (boolean true)
    [.expression [.symbol "size-atom", .var "rows"]] [handleValue handle, .expression items] 2
    (by decide +kernel) (grounded_returns program bindings before (.int 0)) last
  have rows := raw_argument_answers program bindings before after "mm0:remove-rows" (.var "rows")
    [.grounded (.int 0), .expression [.symbol "size-atom", .var "rows"]]
    [handleValue handle] 1 [boolean true] (by decide)
    (by simpa [bindings, clearEnvironment, applySubst, Subst.lookup] using index)
  exact raw_argument_answers program bindings before after "mm0:remove-rows" (.var "space")
    [.var "rows", .grounded (.int 0), .expression [.symbol "size-atom", .var "rows"]]
    [] 0 [boolean true] (by decide)
    (by simpa [bindings, clearEnvironment, applySubst, Subst.lookup] using rows)

theorem enumerated_clear_returns (before : State) (handle : Handle) (stored : List Atom)
    (represented : before.read handle = some stored)
    (admitted : ∀ item ∈ stored, ∃ first rest, item = .expression (first :: rest)) :
    ∃ after, PureReturns program (clearEnvironment handle) before enumeratedClearBody after
        (boolean true) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, child, readAfter, otherAfter, cellsAfter⟩ :=
    remove_body_returns stored [] before handle stored represented admitted
  refine ⟨after, ?_, ?_, otherAfter, cellsAfter⟩
  · rw [clear_body_shape]
    let bindings := clearEnvironment handle
    let bound := ("rows", .expression stored) :: bindings
    apply let_returns program bindings bound before before after (.var "rows") _ _ (.expression stored) _
    · apply collapse_returns program bindings before before _ stored
      apply native_variable_call_answers program bindings before before "get-atoms" ["space"]
        stored (by decide) (by decide) _ (by decide)
      simp [bindings, clearEnvironment, applySubst, Subst.lookup, StdLib.apply, represented]
    · simp [SpaceSemantics.matchValue, matchAtom, bindings, clearEnvironment, Subst.lookup, bound]
    · exact clear_rows_returns before after handle stored (by simpa using child)
  · have empty : without stored stored = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro atom member
      obtain ⟨first, rest, same⟩ := admitted atom member
      have selected : stored.any (fun pattern => Effects.removalMatches pattern atom) = true :=
        List.any_eq_true.mpr ⟨atom, member, by rw [same]; exact Effects.removalMatches_self _ _⟩
      simp [selected]
    simpa [empty] using readAfter


/-! ## The one-pass helper and its concrete private-row patterns -/

def proofPattern : Atom := .expression [.var "reset0", .var "reset1"]

def cachePattern : Atom :=
  .expression [.var "reset0", .var "reset1", .var "reset2", .var "reset3"]

theorem proof_pattern_selects {stored : List Atom}
    (shaped : Effects.RowsHaveArity 2 stored) :
    ∀ row ∈ stored, Effects.removalMatches proofPattern row = true := by
  intro row member
  obtain ⟨fields, same, arity⟩ := shaped row member
  obtain ⟨first, second, fieldsEq⟩ := List.length_eq_two.mp arity
  subst fields
  subst row
  simp [Effects.removalMatches, proofPattern, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

theorem cache_pattern_selects {stored : List Atom}
    (shaped : Effects.RowsHaveArity 4 stored) :
    ∀ row ∈ stored, Effects.removalMatches cachePattern row = true := by
  intro row member
  obtain ⟨fields, same, arity⟩ := shaped row member
  obtain ⟨first, second, third, fourth, fieldsEq⟩ := List.length_eq_four.mp arity
  subst fields
  subst row
  simp [Effects.removalMatches, cachePattern, matchAtom,
    matchAtom.matchAtomList, Subst.lookup]

private def patternEnvironment (handle : Handle) (pattern : Atom) : Subst :=
  [("pattern", pattern), ("space", handleValue handle)]

private theorem pattern_body_shape :
    clearSpaceEquation.body = .expression [.symbol "let", .var "removed",
      .expression [.symbol "remove-atom", .var "space", .var "pattern"],
      .grounded (.bool true)] := by decide

/-- The actual retained body makes one removal call and returns the same Boolean
receipt. The selected-row premise is discharged by the concrete callers below. -/
theorem clear_body_returns (before : State) (handle : Handle) (stored : List Atom)
    (pattern : Atom) (represented : before.read handle = some stored)
    (nonempty : ∃ first rest, pattern = .expression (first :: rest))
    (selected : ∀ row ∈ stored, Effects.removalMatches pattern row = true) :
    ∃ after, PureReturns program (patternEnvironment handle pattern) before
        clearSpaceEquation.body after (boolean true) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨first, rest, rfl⟩ := nonempty
  obtain ⟨after, erased, empty, others, cells⟩ :=
    Effects.erase_all_selected represented selected
  let bindings := patternEnvironment handle (.expression (first :: rest))
  let bound := ("removed", boolean true) :: bindings
  refine ⟨after, ?_, empty, others, cells⟩
  rw [pattern_body_shape]
  apply let_returns program bindings bound before after after (.var "removed") _ _
    (boolean true) _
  · apply native_variable_call_returns program bindings before after "remove-atom"
      ["space", "pattern"] (boolean true) (by decide) (by decide) _ (by decide)
    simp [bindings, patternEnvironment, applySubst, Subst.lookup,
      StdLib.apply, represented, erased]
  · simp [SpaceSemantics.matchValue, matchAtom, bindings, patternEnvironment, bound, Subst.lookup]
  · exact grounded_returns program bound after (.bool true)

/-- The pattern is captured as data. Its variables must remain fresh in the
caller; the actual vector and declaration environments establish this. -/
theorem clear_returns (bindings : Subst) (before : State) (handle : Handle) (stored : List Atom)
    (spaceName : String) (pattern : Atom) (represented : before.read handle = some stored)
    (spaceCaptured : applySubst bindings (.var spaceName) = handleValue handle)
    (patternCaptured : applySubst bindings pattern = pattern)
    (nonempty : ∃ first rest, pattern = .expression (first :: rest))
    (selected : ∀ row ∈ stored, Effects.removalMatches pattern row = true) :
    ∃ after, PureReturns program bindings before
        (.expression [.symbol "mm0:clear-space", .var spaceName, pattern]) after (boolean true) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, body, empty, others, cells⟩ :=
    clear_body_returns before handle stored pattern represented nonempty selected
  refine ⟨after, ?_, empty, others, cells⟩
  apply raw_call_returns program bindings before after "mm0:clear-space"
    [.var spaceName, pattern] (boolean true) (by decide) _ _ (by decide)
  · intro index bounded
    have cases : index = 0 ∨ index = 1 := by
      change index < 2 at bounded
      omega
    rcases cases with rfl | rfl <;> decide
  · simp only [List.map_cons, List.map_nil, spaceCaptured, patternCaptured]
    apply authored_function_arguments_return program bindings (patternEnvironment handle pattern)
      before after "mm0:clear-space" [handleValue handle, pattern] 2
      clearSpaceEquation.body (boolean true) (by decide) (by decide) _ body
    rw [clauses_use_only_the_named_equations, clear_space_equation_is_unique]
    simp [clear_space_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, Subst.lookup, patternEnvironment]

/-- Both algorithms preserve all final space readings and cells. This observation
is at the private helper's return, not its internal mutation-step history. -/
theorem pattern_refines_enumeration (before : State) (handle : Handle) (stored : List Atom)
    (pattern : Atom) (represented : before.read handle = some stored)
    (admitted : ∀ item ∈ stored, ∃ first rest, item = .expression (first :: rest))
    (nonempty : ∃ first rest, pattern = .expression (first :: rest))
    (selected : ∀ row ∈ stored, Effects.removalMatches pattern row = true) :
    ∃ reference actual,
      PureReturns program (clearEnvironment handle) before enumeratedClearBody reference (boolean true) ∧
      PureReturns program (patternEnvironment handle pattern) before clearSpaceEquation.body actual (boolean true) ∧
      (∀ other, actual.read other = reference.read other) ∧ actual.cells = reference.cells := by
  obtain ⟨reference, referenceRun, referenceEmpty, referenceOthers, referenceCells⟩ :=
    enumerated_clear_returns before handle stored represented admitted
  obtain ⟨actual, actualRun, actualEmpty, actualOthers, actualCells⟩ :=
    clear_body_returns before handle stored pattern represented nonempty selected
  refine ⟨reference, actual, referenceRun, actualRun, ?_, actualCells.trans referenceCells.symm⟩
  intro other
  by_cases same : other = handle
  · subst other; exact actualEmpty.trans referenceEmpty.symm
  · exact (actualOthers other same).trans (referenceOthers other same).symm

theorem repeated_pattern_variable_does_not_clear :
    Effects.removalMatches (.expression [.var "same", .var "same"])
      (.expression [.symbol "left", .symbol "right"]) = false := by decide

theorem wrong_row_arity_survives :
    Effects.removalMatches proofPattern
      (.expression [.symbol "a", .symbol "b", .symbol "c"]) = false := by decide

theorem bare_variable_is_not_clear :
    Effects.removalMatches (.var "all")
      (.expression [.symbol "a", .symbol "b"]) = false := rfl

end Mettapedia.Languages.MM0.MeTTa.SpaceClearing
