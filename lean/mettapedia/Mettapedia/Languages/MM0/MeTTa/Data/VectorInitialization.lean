import Mettapedia.Languages.MM0.MeTTa.Data.SpaceClearing

/-!
# Initializing the retained proof vector

The pinned `mm0:vector` clears its allocated proof space and loads the supplied
hypotheses in order. The resulting indexed rows are exactly the dense prefix,
with no stale entries. Other spaces and state cells are preserved. The values
are data: loading them does not execute expressions stored as hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.VectorInitialization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Store (natural row)
open VectorAccess (vectorValue)

private def environment (handle : Handle) (items : List Atom) (index : Nat) : Subst :=
  [("size", natural items.length), ("index", natural index),
    ("items", .expression items), ("space", handleValue handle)]

private theorem load_clause (handle : Handle) (items : List Atom) (index : Nat) :
    clauses program "mm0:vector-load"
      [handleValue handle, .expression items, natural index, natural items.length] =
      [.evaluate (environment handle items index) vectorLoadEquation.body] := by
  rw [clauses_use_only_the_named_equations, vector_load_equation_is_unique]
  simp [vector_load_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private def loopBody : Atom :=
  match vectorLoadEquation.body with
  | .expression [_, _, body, _] => body
  | _ => .expression []

private def nextBody : Atom :=
  match loopBody with
  | .expression [_, _, _, .expression [_, _, _, body]] => body
  | _ => .expression []

private theorem body_shape :
    vectorLoadEquation.body = .expression [.symbol "if",
      .expression [.symbol "<", .var "index", .var "size"], loopBody,
      .expression [.symbol "MM0:Vector", .var "space", .var "size"]] := by decide

private theorem loop_body_shape :
    loopBody = .expression [.symbol "let", .var "value",
      .expression [.symbol "index-atom", .var "items", .var "index"],
      .expression [.symbol "let", .var "done",
        .expression [.symbol "add-atom", .var "space", .expression [.var "index", .var "value"]],
        nextBody]] := by decide

private theorem next_body_shape :
    nextBody = .expression [.symbol "mm0:vector-load", .var "space", .var "items",
      .expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"] := by decide

private theorem next_returns (bindings : Subst) (before after : State)
    (handle : Handle) (items : List Atom) (index : Nat)
    (spaceCaptured : applySubst bindings (.var "space") = handleValue handle)
    (itemsCaptured : applySubst bindings (.var "items") = .expression items)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (sizeCaptured : applySubst bindings (.var "size") = natural items.length)
    (child : PureReturns program (environment handle items (index + 1)) before
      vectorLoadEquation.body after (vectorValue handle items.length)) :
    PureReturns program bindings before nextBody after (vectorValue handle items.length) := by
  rw [next_body_shape]
  apply call_returns program bindings before after "mm0:vector-load" _ _ (by decide) _ (by decide)
  have entered := authored_function_arguments_return program bindings
    (environment handle items (index + 1)) before after "mm0:vector-load"
    [handleValue handle, .expression items, natural (index + 1), natural items.length] 4
    vectorLoadEquation.body _ (by decide) (by decide) (load_clause handle items (index + 1)) child
  have last := variable_arguments_return program bindings before after (.function "mm0:vector-load")
    ["size"] [handleValue handle, .expression items, natural (index + 1)] 3 _
    (by simpa only [List.map_cons, List.map_nil, sizeCaptured, List.cons_append,
      List.nil_append, List.length_cons, List.length_nil, Nat.reduceAdd] using entered)
  have increment : PureReturns program bindings before
      (.expression [.symbol "+", .var "index", .grounded (.int 1)]) before (natural (index + 1)) := by
    apply native_binary_call_returns program bindings before before before before "+" _ _
      (natural index) (.grounded (.int 1)) _ (by decide) (by decide) (by decide) (by decide) _
      (grounded_returns program bindings before (.int 1)) _ (by decide)
    · simpa only [indexCaptured] using variable_returns program bindings before "index"
    · simp [StdLib.apply, natural, Int.natCast_add]
  have next := evaluated_argument_returns program bindings before before after (.function "mm0:vector-load")
    (.expression [.symbol "+", .var "index", .grounded (.int 1)]) (natural (index + 1)) _
    [.var "size"] [handleValue handle, .expression items] 2 (by decide +kernel) increment last
  have itemsPath := raw_argument_answers program bindings before after "mm0:vector-load" (.var "items")
    [.expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"]
    [handleValue handle] 1 [vectorValue handle items.length] (by decide)
    (by simpa only [itemsCaptured, List.cons_append, List.nil_append, Nat.reduceAdd] using next)
  exact raw_argument_answers program bindings before after "mm0:vector-load" (.var "space")
    [.var "items", .expression [.symbol "+", .var "index", .grounded (.int 1)], .var "size"]
    [] 0 [vectorValue handle items.length] (by decide)
    (by simpa only [spaceCaptured, List.nil_append] using itemsPath)

private theorem load_body_returns (remaining processed : List Atom) (before : State) (handle : Handle)
    (represented : Store.Represents before handle (Store.enumerate processed)) :
    ∃ after, PureReturns program (environment handle (processed ++ remaining) processed.length) before
        vectorLoadEquation.body after (vectorValue handle (processed ++ remaining).length) ∧
      Store.Represents after handle (Store.enumerate (processed ++ remaining)) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  induction remaining generalizing processed before with
  | nil =>
      refine ⟨before, ?_, by simpa using represented, fun _ _ => rfl, rfl⟩
      rw [body_shape]
      apply if_returns program _ before before before _ _ _ _ _
      · apply native_variable_call_returns program _ before before "<" ["index", "size"]
          (boolean false) (by decide) (by decide) _ (by decide)
        simp [environment, applySubst, Subst.lookup, StdLib.apply, natural, boolean]
      · simpa [environment, applySubst, Subst.lookup, vectorValue, List.append_nil, boolean] using
          constructor_variables_return program (environment handle processed processed.length)
            before "MM0:Vector" ["space", "size"] vector_is_data_constructor (by decide)
  | cons first rest ih =>
      obtain ⟨middle, inserted⟩ := Effects.insert_exists_of_read_some represented
        (row (processed.length, first))
      have published := VectorPublication.publication_preserves_dense_prefix represented inserted
      obtain ⟨after, child, readAfter, otherAfter, cellsAfter⟩ :=
        ih (processed ++ [first]) middle published
      let items := processed ++ first :: rest
      let bindings := environment handle items processed.length
      let withValue := ("value", first) :: bindings
      let withDone := ("done", boolean true) :: withValue
      refine ⟨after, ?_, ?_, ?_, ?_⟩
      · rw [body_shape]
        apply if_returns program bindings before before after _ _ _ _ _
        · apply native_variable_call_returns program bindings before before "<" ["index", "size"]
            (boolean true) (by decide) (by decide) _ (by decide)
          simp [bindings, environment, items, applySubst, Subst.lookup,
            StdLib.apply, natural, boolean]
        · change PureReturns program bindings before loopBody after (vectorValue handle items.length)
          rw [loop_body_shape]
          apply let_returns program bindings withValue before before after (.var "value") _ _ first _
          · apply native_variable_call_returns program bindings before before "index-atom" ["items", "index"]
              first (by decide) (by decide) _ (by decide)
            simp [bindings, environment, items, applySubst, Subst.lookup, StdLib.apply, natural]
          · simp [SpaceSemantics.matchValue, matchAtom, bindings, environment, Subst.lookup, withValue]
          · apply let_returns program withValue withDone before middle after (.var "done") _ _
              (boolean true) _ _ _ _
            · apply call_returns program withValue before middle "add-atom" _ _ (by decide) _ (by decide)
              have insertedPath := native_function_arguments_return program withValue before middle "add-atom"
                [handleValue handle, row (processed.length, first)] 2 (boolean true)
                (by decide) (by decide) (by simp [StdLib.apply, inserted])
              have last := raw_argument_answers program withValue before middle "add-atom"
                (.expression [.var "index", .var "value"]) [] [handleValue handle] 1 [boolean true]
                (by decide) (by simpa [withValue, bindings, environment, row, applySubst,
                  applySubst.applySubstList, Subst.lookup] using insertedPath)
              exact evaluated_argument_returns program withValue before before middle (.function "add-atom")
                (.var "space") (handleValue handle) _ _ [] 0 (by decide)
                (by simpa [withValue, bindings, environment, applySubst, Subst.lookup] using
                  variable_returns program withValue before "space") last
            · simp [SpaceSemantics.matchValue, matchAtom, withValue, bindings, environment, Subst.lookup, withDone]
            · apply next_returns withDone middle after handle items processed.length
              · simp [withDone, withValue, bindings, environment, applySubst, Subst.lookup]
              · simp [withDone, withValue, bindings, environment, applySubst, Subst.lookup]
              · simp [withDone, withValue, bindings, environment, applySubst, Subst.lookup]
              · simp [withDone, withValue, bindings, environment, applySubst, Subst.lookup]
              · simpa [items, List.append_assoc] using child
      · simpa [List.append_assoc] using readAfter
      · intro other different
        rw [otherAfter other different, Effects.insert_read_other inserted different]
      · rw [cellsAfter, Effects.insert_preserves_cells inserted]

private def vectorEnvironment (items : List Atom) : Subst := [("items", .expression items)]

private def clearedBody : Atom :=
  match vectorEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def loadBody : Atom :=
  match clearedBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private theorem vector_body_shape :
    vectorEquation.body = .expression [.symbol "let", .var "space",
      .expression [.symbol "get-state", .symbol "mm0-proof-store"], clearedBody] := by decide

private theorem cleared_body_shape :
    clearedBody = .expression [.symbol "let", .var "cleared",
      .expression [.symbol "mm0:clear-space", .var "space", SpaceClearing.proofPattern], loadBody] := by decide

private theorem load_body_shape :
    loadBody = .expression [.symbol "mm0:vector-load", .var "space", .var "items",
      .grounded (.int 0), .expression [.symbol "size-atom", .var "items"]] := by decide

private theorem load_returns (bindings : Subst) (before after : State) (handle : Handle) (items : List Atom)
    (spaceCaptured : applySubst bindings (.var "space") = handleValue handle)
    (itemsCaptured : applySubst bindings (.var "items") = .expression items)
    (child : PureReturns program (environment handle items 0) before vectorLoadEquation.body after
      (vectorValue handle items.length)) :
    PureReturns program bindings before loadBody after (vectorValue handle items.length) := by
  rw [load_body_shape]
  apply call_returns program bindings before after "mm0:vector-load" _ _ (by decide) _ (by decide)
  have entered := authored_function_arguments_return program bindings (environment handle items 0)
    before after "mm0:vector-load" [handleValue handle, .expression items, natural 0, natural items.length] 4
    vectorLoadEquation.body _ (by decide) (by decide) (load_clause handle items 0) child
  have size : PureReturns program bindings before (.expression [.symbol "size-atom", .var "items"])
      before (natural items.length) := by
    apply native_variable_call_returns program bindings before before "size-atom" ["items"] _
      (by decide) (by decide) _ (by decide)
    simp [itemsCaptured, StdLib.apply, natural]
  have last := evaluated_argument_returns program bindings before before after (.function "mm0:vector-load")
    (.expression [.symbol "size-atom", .var "items"]) (natural items.length) _
    [] [handleValue handle, .expression items, natural 0] 3 (by decide +kernel) size entered
  have zero := evaluated_argument_returns program bindings before before after (.function "mm0:vector-load")
    (.grounded (.int 0)) (natural 0) _ [.expression [.symbol "size-atom", .var "items"]]
    [handleValue handle, .expression items] 2 (by decide +kernel)
    (grounded_returns program bindings before (.int 0)) last
  have itemsPath := raw_argument_answers program bindings before after "mm0:vector-load" (.var "items")
    [.grounded (.int 0), .expression [.symbol "size-atom", .var "items"]]
    [handleValue handle] 1 [vectorValue handle items.length] (by decide)
    (by simpa only [itemsCaptured, List.cons_append, List.nil_append] using zero)
  exact raw_argument_answers program bindings before after "mm0:vector-load" (.var "space")
    [.var "items", .grounded (.int 0), .expression [.symbol "size-atom", .var "items"]]
    [] 0 [vectorValue handle items.length] (by decide)
    (by simpa only [spaceCaptured, List.nil_append] using itemsPath)

theorem vector_body_returns (before : State) (handle : Handle) (stored items : List Atom)
    (current : before.cells "mm0-proof-store" = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 2 stored) :
    ∃ after, PureReturns program (vectorEnvironment items) before vectorEquation.body after
        (vectorValue handle items.length) ∧
      Store.Represents after handle (Store.enumerate items) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  let bindings := vectorEnvironment items
  let withSpace := ("space", handleValue handle) :: bindings
  let withCleared := ("cleared", boolean true) :: withSpace
  obtain ⟨middle, clear, empty, clearOthers, clearCells⟩ := SpaceClearing.clear_returns
    withSpace before handle stored "space" SpaceClearing.proofPattern allocated
    (by simp [withSpace, applySubst, Subst.lookup])
    (by simp [SpaceClearing.proofPattern, withSpace, bindings, vectorEnvironment, applySubst, applySubst.applySubstList, Subst.lookup])
    ⟨_, _, rfl⟩ (SpaceClearing.proof_pattern_selects shaped)
  obtain ⟨after, child, represented, loadOthers, loadCells⟩ :=
    load_body_returns items [] middle handle empty
  refine ⟨after, ?_, by simpa using represented, ?_, ?_⟩
  · rw [vector_body_shape]
    apply let_returns program bindings withSpace before before after (.var "space") _ _
      (handleValue handle) _ _ _ _
    · apply native_unary_call_returns program bindings before before before "get-state"
        (.symbol "mm0-proof-store") _ _ (by decide) (by decide) (by decide)
        (symbol_returns program bindings before "mm0-proof-store") _ (by decide)
      simp [StdLib.apply, current]
    · simp [SpaceSemantics.matchValue, matchAtom, bindings, vectorEnvironment, Subst.lookup, withSpace]
    · rw [cleared_body_shape]
      apply let_returns program withSpace withCleared before middle after (.var "cleared") _ _
        (boolean true) _ clear _ _
      · simp [SpaceSemantics.matchValue, matchAtom, withSpace, bindings, vectorEnvironment, Subst.lookup, withCleared]
      · apply load_returns withCleared middle after handle items
        · simp [withCleared, withSpace, applySubst, Subst.lookup]
        · simp [withCleared, withSpace, bindings, vectorEnvironment, applySubst, Subst.lookup]
        · simpa using child
  · intro other different
    rw [loadOthers other different, clearOthers other different]
  · rw [loadCells, clearCells]

/-- A captured hypothesis list is initialized by the same retained function.
The prior values may be stale, duplicated or invalid. Their two-field layout
is inherited from the store writers; clearing precedes loading. -/
theorem vector_captured_returns (bindings : Subst) (before : State) (handle : Handle)
    (stored items : List Atom) (itemsName : String)
    (captured : applySubst bindings (.var itemsName) = ListAccess.listValue items)
    (current : before.cells "mm0-proof-store" = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 2 stored) :
    ∃ after, PureReturns program bindings before
        (.expression [.symbol "mm0:vector", .var itemsName]) after
        (vectorValue handle items.length) ∧
      Store.Represents after handle (Store.enumerate items) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, body, represented, others, cells⟩ :=
    vector_body_returns before handle stored items current allocated shaped
  refine ⟨after, ?_, represented, others, cells⟩
  apply authored_variable_call_returns program bindings (vectorEnvironment items) before after
    "mm0:vector" [itemsName] vectorEquation.body _ (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, vector_equation_is_unique]
  simp [captured, vector_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
    matchAtom, ListAccess.listValue, Subst.lookup, vectorEnvironment]

/-- The public call initializes precisely the supplied finite hypotheses. -/
theorem vector_returns (before : State) (handle : Handle) (stored items : List Atom)
    (current : before.cells "mm0-proof-store" = some (handleValue handle))
    (allocated : before.read handle = some stored)
    (shaped : Effects.RowsHaveArity 2 stored) :
    ∃ after, PureReturns program [] before
        (.expression [.symbol "mm0:vector", ListAccess.listValue items]) after
        (vectorValue handle items.length) ∧
      Store.Represents after handle (Store.enumerate items) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  obtain ⟨after, body, represented, others, cells⟩ :=
    vector_body_returns before handle stored items current allocated shaped
  refine ⟨after, ?_, represented, others, cells⟩
  apply raw_call_returns program [] before after "mm0:vector" [ListAccess.listValue items]
    _ (by decide) _ _ (by decide)
  · intro index bounded
    have zero : index = 0 := by simpa using bounded
    subst index
    decide
  · simp only [List.map_cons, List.map_nil, Mettapedia.Languages.ProcessCalculi.MORK.applySubst_nil]
    apply authored_function_arguments_return program [] (vectorEnvironment items)
      before after "mm0:vector" [ListAccess.listValue items] 1 vectorEquation.body _
      (by decide) (by decide) _ body
    rw [clauses_use_only_the_named_equations, vector_equation_is_unique]
    simp [vector_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
      matchAtom, ListAccess.listValue, Subst.lookup, vectorEnvironment]

end Mettapedia.Languages.MM0.MeTTa.VectorInitialization
