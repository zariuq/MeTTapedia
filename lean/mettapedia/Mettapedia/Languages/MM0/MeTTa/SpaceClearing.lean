import Mettapedia.Languages.MM0.MeTTa.VectorPublication

/-!
# Clearing private MM0 stores

The retained source first collects the current rows, then removes them in
order. The proofs execute that loop, including duplicate occurrences. Its
postcondition clears the selected space and preserves other spaces and cells.
This supplies the concrete reset needed by the proof-vector and cache epochs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SpaceClearing

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean handleValue)
open NamedSpaces (Handle)
open Store (natural)

private def environment (handle : Handle) (items : List Atom) (index : Nat) : Subst :=
  [("size", natural items.length), ("index", natural index),
    ("rows", .expression items), ("space", handleValue handle)]

private def without (stored removed : List Atom) : List Atom :=
  stored.filter fun atom => decide (atom ∉ removed)

private theorem without_after_erase (stored removed : List Atom) (first : Atom) :
    without (stored.filter (· != first)) removed = without stored (first :: removed) := by
  simp only [without, List.filter_filter]
  congr 1
  funext atom
  apply Bool.eq_iff_iff.mpr
  simp [List.mem_cons, not_or, and_comm]

private theorem remove_clause (handle : Handle) (items : List Atom) (index : Nat) :
    clauses program "mm0:remove-rows"
      [handleValue handle, .expression items, natural index, natural items.length] =
      [.evaluate (environment handle items index) removeRowsEquation.body] := by
  rw [clauses_use_only_the_named_equations, remove_rows_equation_is_unique]
  simp [remove_rows_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
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
    · simp [SourcePrimitives.apply, natural, Int.natCast_add]
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
    (handle : Handle) (stored : List Atom) (represented : before.read handle = some stored) :
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
          simp [environment, applySubst, Subst.lookup, SourcePrimitives.apply, natural, boolean]
        · exact grounded_returns program _ before (.bool true)
      · simpa [without] using represented
  | cons first rest ih =>
      obtain ⟨middle, erased⟩ := SourcePrimitives.erase_exists_of_read_some represented first
      obtain ⟨oldRows, readBefore, readMiddle⟩ := SourcePrimitives.erase_reads_back erased
      have old : oldRows = stored := Option.some.inj (readBefore.symm.trans represented)
      subst oldRows
      obtain ⟨after, child, readAfter, otherAfter, cellsAfter⟩ :=
        ih (processed ++ [first]) middle (stored.filter (· != first)) readMiddle
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
            SourcePrimitives.apply, natural, boolean]
        · change PureReturns program bindings before loopBody after (boolean true)
          rw [loop_body_shape]
          apply let_returns program bindings withRow before before after (.var "row") _ _ first _
          · apply native_variable_call_returns program bindings before before "index-atom" ["rows", "index"]
              first (by decide) (by decide) _ (by decide)
            simp [bindings, environment, items, applySubst, Subst.lookup, SourcePrimitives.apply,
              natural]
          · simp [SourceProgram.matchValue, matchAtom, bindings, environment, Subst.lookup, withRow]
          · apply let_returns program withRow withErased before middle after (.var "removed") _ _
              (boolean true) _
            · apply native_variable_call_returns program withRow before middle "remove-atom" ["space", "row"]
                (boolean true) (by decide) (by decide) _ (by decide)
              simp [withRow, bindings, environment, applySubst, Subst.lookup, SourcePrimitives.apply, erased]
            · simp [SourceProgram.matchValue, matchAtom, withRow, bindings, environment,
                Subst.lookup, withErased]
            · apply next_call_returns withErased middle after handle items processed.length
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simp [withErased, withRow, bindings, environment, applySubst, Subst.lookup]
              · simpa [items, List.append_assoc] using child
      · simpa [without_after_erase] using readAfter
      · intro other different
        rw [otherAfter other different, SourcePrimitives.erase_read_other erased different]
      · rw [cellsAfter, SourcePrimitives.erase_preserves_cells erased]

private def clearEnvironment (handle : Handle) : Subst := [("space", handleValue handle)]

private def clearRowsBody : Atom :=
  match clearSpaceEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private theorem clear_body_shape :
    clearSpaceEquation.body = .expression [.symbol "let", .var "rows",
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
    simp [bindings, clearEnvironment, applySubst, Subst.lookup, SourcePrimitives.apply, natural]
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

theorem clear_body_returns (before : State) (handle : Handle) (stored : List Atom)
    (represented : before.read handle = some stored) :
    ∃ after, PureReturns program (clearEnvironment handle) before clearSpaceEquation.body after
        (boolean true) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, child, readAfter, otherAfter, cellsAfter⟩ :=
    remove_body_returns stored [] before handle stored represented
  refine ⟨after, ?_, ?_, otherAfter, cellsAfter⟩
  · rw [clear_body_shape]
    let bindings := clearEnvironment handle
    let bound := ("rows", .expression stored) :: bindings
    apply let_returns program bindings bound before before after (.var "rows") _ _ (.expression stored) _
    · apply collapse_returns program bindings before before _ stored
      apply native_variable_call_answers program bindings before before "get-atoms" ["space"]
        stored (by decide) (by decide) _ (by decide)
      simp [bindings, clearEnvironment, applySubst, Subst.lookup, SourcePrimitives.apply, represented]
    · simp [SourceProgram.matchValue, matchAtom, bindings, clearEnvironment, Subst.lookup, bound]
    · exact clear_rows_returns before after handle stored (by simpa using child)
  · have empty : without stored stored = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro atom member
      simp [member]
    simpa [empty] using readAfter

theorem clear_returns (bindings : Subst) (before : State) (handle : Handle) (stored : List Atom)
    (spaceName : String) (represented : before.read handle = some stored)
    (spaceCaptured : applySubst bindings (.var spaceName) = handleValue handle) :
    ∃ after, PureReturns program bindings before
        (.expression [.symbol "mm0:clear-space", .var spaceName]) after (boolean true) ∧
      after.read handle = some [] ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, body, empty, otherAfter, cellsAfter⟩ := clear_body_returns before handle stored represented
  refine ⟨after, ?_, empty, otherAfter, cellsAfter⟩
  apply authored_variable_call_returns program bindings (clearEnvironment handle) before after
    "mm0:clear-space" [spaceName] clearSpaceEquation.body (boolean true)
    (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, clear_space_equation_is_unique]
  simp [clear_space_formals, spaceCaptured, SourceProgram.matchValue,
    SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, clearEnvironment]

end Mettapedia.Languages.MM0.MeTTa.SpaceClearing
