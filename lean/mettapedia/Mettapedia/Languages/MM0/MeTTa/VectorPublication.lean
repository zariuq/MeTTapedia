import Mettapedia.Languages.MM0.MeTTa.VectorAccess

/-!
# Publication in the retained MM0 proof vector

The actual `mm0:vector-snoc` body appends one indexed row and increases the
visible prefix. Publication preserves every other space and all state cells.
This is a representation theorem; the shared-proof driver must separately
establish that the supplied conclusion was checked in its current scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.VectorPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean handleValue)
open NamedSpaces (Handle)
open Store (natural row)
open VectorAccess (vectorValue)

private def environment (handle : Handle) (size : Nat) (value : Atom) : Subst :=
  [("value", value), ("size", natural size), ("space", handleValue handle)]

theorem publication_clause (handle : Handle) (size : Nat) (value : Atom) :
    clauses program "mm0:vector-snoc" [vectorValue handle size, value] =
      [.evaluate (environment handle size value) vectorSnocEquation.body] := by
  rw [clauses_use_only_the_named_equations, vector_snoc_equation_is_unique]
  simp [vector_snoc_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    vectorValue, matchAtom, Subst.lookup, environment]

private theorem body_shape :
    vectorSnocEquation.body = .expression [.symbol "let", .var "done",
      .expression [.symbol "add-atom", .var "space", .expression [.var "size", .var "value"]],
      .expression [.symbol "MM0:Vector", .var "space",
        .expression [.symbol "+", .var "size", .grounded (.int 1)]]] := by decide

private theorem incremented_vector_returns (state : State) (handle : Handle) (size : Nat)
    (value : Atom) :
    PureReturns program (("done", boolean true) :: environment handle size value) state
      (.expression [.symbol "MM0:Vector", .var "space",
        .expression [.symbol "+", .var "size", .grounded (.int 1)]]) state
      (vectorValue handle (size + 1)) := by
  let bindings := ("done", boolean true) :: environment handle size value
  have increment : PureReturns program bindings state
      (.expression [.symbol "+", .var "size", .grounded (.int 1)]) state
      (natural (size + 1)) := by
    apply native_binary_call_returns program bindings state state state state "+"
      (.var "size") (.grounded (.int 1)) (natural size) (.grounded (.int 1)) _
      (by decide) (by decide) (by decide) (by decide) _
      (grounded_returns program bindings state (.int 1)) _ (by decide)
    · simpa [bindings, environment, applySubst, Subst.lookup] using
        variable_returns program bindings state "size"
    · simp [SourcePrimitives.apply, natural, Int.natCast_add]
  apply data_call_returns program bindings state state "MM0:Vector" _ _
    vector_is_data_constructor _ (by decide)
  have last := evaluated_argument_returns program bindings state state state .data
    (.expression [.symbol "+", .var "size", .grounded (.int 1)]) (natural (size + 1))
    (vectorValue handle (size + 1)) [] [.symbol "MM0:Vector", handleValue handle] 2 rfl
    increment (data_arguments_values_return program bindings state _ 3)
  have spaceReturns : PureReturns program bindings state (.var "space") state (handleValue handle) := by
    simpa [bindings, environment, applySubst, Subst.lookup] using
      variable_returns program bindings state "space"
  have rest := evaluated_argument_returns program bindings state state state .data (.var "space")
    (handleValue handle) _ _ [.symbol "MM0:Vector"] 1 rfl spaceReturns last
  exact evaluated_argument_returns program bindings state state state .data (.symbol "MM0:Vector")
    (.symbol "MM0:Vector") _ _ [] 0 rfl (symbol_returns program bindings state "MM0:Vector") rest

theorem publication_body_returns (before after : State) (handle : Handle) (size : Nat) (value : Atom)
    (inserted : SourcePrimitives.insert before handle (row (size, value)) = some after) :
    PureReturns program (environment handle size value) before vectorSnocEquation.body after
      (vectorValue handle (size + 1)) := by
  let bindings := environment handle size value
  let bound := ("done", boolean true) :: bindings
  rw [body_shape]
  apply let_returns program bindings bound before after after (.var "done") _ _ (boolean true) _
  · apply call_returns program bindings before after "add-atom" _ _ (by decide) _ (by decide)
    have insertedPath := native_function_arguments_return program bindings before after "add-atom"
      [handleValue handle, row (size, value)] 2 (boolean true) (by decide) (by decide)
      (by simp [SourcePrimitives.apply, inserted])
    have last := raw_argument_answers program bindings before after "add-atom"
      (.expression [.var "size", .var "value"]) [] [handleValue handle] 1 [boolean true]
      (by decide) (by simpa [bindings, environment, row, applySubst, applySubst.applySubstList,
        Subst.lookup] using insertedPath)
    have spaceReturns : PureReturns program bindings before (.var "space") before (handleValue handle) := by
      simpa [bindings, environment, applySubst, Subst.lookup] using
        variable_returns program bindings before "space"
    exact evaluated_argument_returns program bindings before before after (.function "add-atom")
      (.var "space") (handleValue handle) _ _ [] 0 (by decide) spaceReturns last
  · simp [SourceProgram.matchValue, matchAtom, bindings, environment, Subst.lookup, bound]
  · exact incremented_vector_returns after handle size value

theorem publication_returns (bindings : Subst) (before after : State) (handle : Handle)
    (size : Nat) (value : Atom) (vectorName valueName : String)
    (inserted : SourcePrimitives.insert before handle (row (size, value)) = some after)
    (vectorCaptured : applySubst bindings (.var vectorName) = vectorValue handle size)
    (valueCaptured : applySubst bindings (.var valueName) = value) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var valueName]) after
      (vectorValue handle (size + 1)) := by
  apply authored_variable_call_returns program bindings (environment handle size value) before after
    "mm0:vector-snoc" [vectorName, valueName] vectorSnocEquation.body _
    (by decide) (by decide) (by decide) _
    (publication_body_returns before after handle size value inserted) (by decide)
  simpa [vectorCaptured, valueCaptured] using publication_clause handle size value

/-- The source operation and the concrete private-store postcondition agree.
The incoming row's logical authorization is not inferred from its storage. -/
theorem publication_preserves_tables (bindings : Subst) (before after : State) (handle : Handle)
    (entries : List (Nat × Atom)) (size : Nat) (value : Atom) (vectorName valueName : String)
    (represented : Store.Represents before handle entries)
    (inserted : SourcePrimitives.insert before handle (row (size, value)) = some after)
    (vectorCaptured : applySubst bindings (.var vectorName) = vectorValue handle size)
    (valueCaptured : applySubst bindings (.var valueName) = value) :
    PureReturns program bindings before
        (.expression [.symbol "mm0:vector-snoc", .var vectorName, .var valueName]) after
        (vectorValue handle (size + 1)) ∧
      Store.Represents after handle (entries ++ [(size, value)]) ∧
      (∀ other, other ≠ handle → after.read other = before.read other) ∧
      after.cells = before.cells := by
  exact ⟨publication_returns bindings before after handle size value vectorName valueName
      inserted vectorCaptured valueCaptured,
    Store.publish_preserves_representation represented inserted,
    fun _ different => SourcePrimitives.insert_read_other inserted different,
    SourcePrimitives.insert_preserves_cells inserted⟩

theorem publication_preserves_dense_prefix {before after : State} {handle : Handle}
    {values : List Atom} {value : Atom}
    (represented : Store.Represents before handle (Store.enumerate values))
    (inserted : SourcePrimitives.insert before handle (row (values.length, value)) = some after) :
    Store.Represents after handle (Store.enumerate (values ++ [value])) := by
  rw [Store.enumerate_append_one]
  exact Store.publish_preserves_representation represented inserted

end Mettapedia.Languages.MM0.MeTTa.VectorPublication
