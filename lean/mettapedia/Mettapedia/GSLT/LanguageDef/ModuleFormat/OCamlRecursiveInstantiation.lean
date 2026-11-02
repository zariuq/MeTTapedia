import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlFunctionInstantiation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlPatternPool

/-! Recursive dispatch retains the source group and slot. Generated rows
refer to the actual lambda in that slot and rebuild the same recursive
environment as the independent source machine.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax Match

def recursiveRow (group slot body : OCaml.Code) (patternCode : Pattern)
    (definitions : List OCaml.Code) : RewriteRule :=
  rule ("ml-recursive:" ++ toString group ++ ":" ++ toString slot)
    (node "MlApply" [node "MlClosure" [node "MlRecursiveFunction" [code group, code slot], hole "environment"],
      hole "argument", hole "continuation"])
    (node "MlMatchOne" [patternCode, hole "argument", code body,
      recursiveEnvironment group definitions (hole "environment"), hole "continuation"])

def recursiveEntry? (program : OCaml.Program) (pool : List OCaml.MatchPattern) (group : OCaml.Code)
    (definitions : List OCaml.Code) (entry : OCaml.Code × Nat) : Option RewriteRule := do
  let some (.lambda parameter body) := program.instruction? entry.1 | none
  pure (recursiveRow group entry.2 body (← patternReference? pool parameter) definitions)

theorem recursive_rows (program : OCaml.Program) (pool : List OCaml.MatchPattern) (group body : OCaml.Code)
    (definitions : List OCaml.Code) :
    functionRules? program pool group (.letRecursive definitions body) =
      definitions.zipIdx.mapM (recursiveEntry? program pool group definitions) := rfl

theorem recursive_entry_readback (program : OCaml.Program) (pool : List OCaml.MatchPattern) (group : OCaml.Code)
    (definitions : List OCaml.Code) (entry : OCaml.Code × Nat) (row : RewriteRule)
    (compiled : recursiveEntry? program pool group definitions entry = some row) :
    ∃ parameter body patternCode,
      program.instruction? entry.1 = some (.lambda parameter body) ∧
      patternReference? pool parameter = some patternCode ∧
      row = recursiveRow group entry.2 body patternCode definitions := by
  unfold recursiveEntry? at compiled
  cases found : program.instruction? entry.1 with
  | none => simp [found] at compiled
  | some instruction =>
      cases instruction with
      | lambda parameter body =>
          cases referenced : patternReference? pool parameter with
          | none => simp [found, referenced] at compiled
          | some patternCode =>
              have same : recursiveRow group entry.2 body patternCode definitions = row := by
                simpa [found, referenced] using compiled
              exact ⟨parameter, body, patternCode, rfl, referenced, same.symm⟩
      | _ => simp [found] at compiled

theorem option_mapM_member {α β : Type} (items : List α) (emit : α → Option β) (outputs : List β)
    (compiled : items.mapM emit = some outputs) (output : β) (member : output ∈ outputs) :
    ∃ item ∈ items, emit item = some output := by
  induction items generalizing outputs with
  | nil => simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at compiled; subst outputs; cases member
  | cons first rest ih =>
      cases head : emit first with
      | none => simp [List.mapM_cons, head] at compiled
      | some emitted =>
          cases tail : rest.mapM emit with
          | none => simp [List.mapM_cons, head, tail] at compiled
          | some remaining =>
              have same : emitted :: remaining = outputs := by simpa [List.mapM_cons, head, tail] using compiled
              subst outputs
              rcases List.mem_cons.mp member with rfl | later
              · exact ⟨first, List.mem_cons_self, head⟩
              · obtain ⟨item, present, emitted⟩ := ih remaining tail later
                exact ⟨item, List.mem_cons_of_mem first present, emitted⟩

theorem recursive_rule_origin (program : OCaml.Program) (pool : List OCaml.MatchPattern) (group body : OCaml.Code)
    (definitions : List OCaml.Code) (rows : List RewriteRule) (row : RewriteRule)
    (compiled : functionRules? program pool group (.letRecursive definitions body) = some rows)
    (member : row ∈ rows) :
    ∃ slot reference parameter functionBody patternCode,
      definitions[slot]? = some reference ∧ program.instruction? reference = some (.lambda parameter functionBody) ∧
      patternReference? pool parameter = some patternCode ∧
      row = recursiveRow group slot functionBody patternCode definitions := by
  rw [recursive_rows] at compiled
  obtain ⟨⟨reference, slot⟩, present, emitted⟩ := option_mapM_member _ _ _ compiled row member
  have indexed := List.mk_mem_zipIdx_iff_getElem?.mp present
  obtain ⟨parameter, functionBody, patternCode, found, referenced, same⟩ :=
    recursive_entry_readback program pool group definitions (reference, slot) row emitted
  exact ⟨slot, reference, parameter, functionBody, patternCode, indexed, found, referenced, same⟩

theorem recursive_row_instance (group slot body : OCaml.Code) {parameter : OCaml.MatchPattern}
    {pool : List OCaml.MatchPattern} {patternCode : Pattern} (definitions : List OCaml.Code)
    (resolved : patternReference? pool parameter = some patternCode)
    (captured : OCaml.Environment) (argument : OCaml.Value) (continuation : Pattern) :
    applyBindings (functionBindings captured argument continuation) (recursiveRow group slot body patternCode definitions).left =
      node "MlApply" [value (.closure (.recursive group slot) captured), value argument, continuation] ∧
    applyBindings (functionBindings captured argument continuation) (recursiveRow group slot body patternCode definitions).right =
      node "MlMatchOne" [patternCode, value argument, code body,
        environment (OCaml.recursiveEnvironment group definitions captured), continuation] := by
  constructor
  · simp only [recursiveRow, rule, apply_node, List.map_cons, List.map_nil, apply_code]
    simp [functionBindings, hole, applyBindings, value]
  · simp only [recursiveRow, rule, apply_node, List.map_cons, List.map_nil, apply_code,
      patternReference?_fixed _ resolved, apply_recursiveEnvironment]
    simp [functionBindings, hole, applyBindings]
    rw [recursive_environment]

theorem recursive_source_success (program : OCaml.Program) (group slot reference body : OCaml.Code)
    (definitions : List OCaml.Code) (groupBody : OCaml.Code) (parameter : OCaml.MatchPattern)
    (captured : OCaml.Environment) (argument : OCaml.Value) (bindings : List OCaml.Value)
    (continuation : OCaml.Continuation)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned (.closure (.recursive group slot) captured) (.function argument :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend (OCaml.recursiveEnvironment group definitions captured) bindings) continuation)) := by
  simp only [OCaml.machineStep, OCaml.returnValue, OCaml.applyClosure, declaredGroup, declaredSlot,
    declaredFunction, OCaml.enterBody, matched, Except.map]
  rfl

theorem option_mapM_exists {α β : Type} (items : List α) (emit : α → Option β)
    (complete : ∀ item ∈ items, ∃ output, emit item = some output) :
    ∃ outputs, items.mapM emit = some outputs := by
  induction items with
  | nil => exact ⟨[], rfl⟩
  | cons first rest ih =>
      obtain ⟨head, headFound⟩ := complete first List.mem_cons_self
      obtain ⟨tail, tailFound⟩ := ih (fun item member => complete item (List.mem_cons_of_mem first member))
      exact ⟨head :: tail, by simp [List.mapM_cons, headFound, tailFound]⟩

theorem option_mapM_member_complete {α β : Type} (items : List α) (emit : α → Option β) (outputs : List β)
    (compiled : items.mapM emit = some outputs) (item : α) (member : item ∈ items) (output : β)
    (emitted : emit item = some output) : output ∈ outputs := by
  induction items generalizing outputs with
  | nil => cases member
  | cons first rest ih =>
      cases head : emit first with
      | none => simp [List.mapM_cons, head] at compiled
      | some emittedHead =>
          cases tail : rest.mapM emit with
          | none => simp [List.mapM_cons, head, tail] at compiled
          | some remaining =>
              have same : emittedHead :: remaining = outputs := by simpa [List.mapM_cons, head, tail] using compiled
              subst outputs
              rcases List.mem_cons.mp member with rfl | later
              · have equal := Option.some.inj (head.symm.trans emitted)
                exact equal ▸ List.mem_cons_self
              · exact List.mem_cons_of_mem _ (ih remaining tail later)

theorem recursive_rules_complete (program : OCaml.Program) (group groupBody : OCaml.Code)
    (definitions : List OCaml.Code)
    (functions : ∀ reference ∈ definitions, ∃ parameter body,
      program.instruction? reference = some (.lambda parameter body)) :
    ∃ rows, functionRules? program (patterns program) group (.letRecursive definitions groupBody) = some rows := by
  rw [recursive_rows]
  apply option_mapM_exists
  intro entry present
  obtain ⟨parameter, body, declared⟩ := functions entry.1 (List.fst_mem_of_mem_zipIdx present)
  obtain ⟨patternCode, resolved⟩ := patternReference?_exists (lambda_pattern_member declared)
  refine ⟨recursiveRow group entry.2 body patternCode definitions, ?_⟩
  simp only [recursiveEntry?, declared, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem recursive_selected_row (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (group groupBody slot reference body : OCaml.Code) (definitions : List OCaml.Code)
    (parameter : OCaml.MatchPattern) (patternCode : Pattern) (rows : List RewriteRule)
    (compiled : functionRules? program pool group (.letRecursive definitions groupBody) = some rows)
    (indexed : definitions[slot]? = some reference)
    (declared : program.instruction? reference = some (.lambda parameter body))
    (resolved : patternReference? pool parameter = some patternCode) :
    recursiveRow group slot body patternCode definitions ∈ rows := by
  rw [recursive_rows] at compiled
  apply option_mapM_member_complete definitions.zipIdx _ rows compiled (reference, slot)
    (List.mk_mem_zipIdx_iff_getElem?.mpr indexed)
  simp only [recursiveEntry?, declared, resolved, Option.bind_eq_bind, Option.bind_some, Option.pure_def]

theorem recursive_pattern_lowering (program : OCaml.Program) (pool : List OCaml.MatchPattern)
    (group groupBody slot reference body index : OCaml.Code) (definitions : List OCaml.Code)
    (parameter : OCaml.MatchPattern) (captured : OCaml.Environment) (argument : OCaml.Value)
    (bindings : List OCaml.Value) (continuation : OCaml.Continuation) (encodedContinuation : Pattern)
    (rows : List RewriteRule)
    (compiled : functionRules? program pool group (.letRecursive definitions groupBody) = some rows)
    (declaredGroup : program.instruction? group = some (.letRecursive definitions groupBody))
    (declaredSlot : definitions[slot]? = some reference)
    (declaredFunction : program.instruction? reference = some (.lambda parameter body))
    (parameterResolved : patternReference? pool parameter = some (patternId index))
    (continuationResolved : continuation? pool continuation = some encodedContinuation)
    (matched : OCaml.matchPattern parameter argument = some bindings) :
    OCaml.machineStep program (.returned (.closure (.recursive group slot) captured) (.function argument :: continuation)) =
      .ok (some (.evaluate body (OCaml.extend (OCaml.recursiveEnvironment group definitions captured) bindings) continuation)) ∧
    ∃ functionRow assignment, functionRow ∈ rows ∧
      applyBindings (functionBindings captured argument encodedContinuation) functionRow.left =
        node "MlApply" [value (.closure (.recursive group slot) captured), value argument, encodedContinuation] ∧
      applyBindings (functionBindings captured argument encodedContinuation) functionRow.right =
        applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).left ∧
      state? pool (.evaluate body (OCaml.extend (OCaml.recursiveEnvironment group definitions captured) bindings) continuation) =
        some (applyBindings assignment ((patternRules index parameter)[0]'(by simp [patternRules])).right) := by
  refine ⟨recursive_source_success program group slot reference body definitions groupBody parameter captured argument
    bindings continuation declaredGroup declaredSlot declaredFunction matched, ?_⟩
  have present := recursive_selected_row program pool group groupBody slot reference body definitions parameter
    (patternId index) rows compiled declaredSlot declaredFunction parameterResolved
  obtain ⟨input, request⟩ := recursive_row_instance group slot body definitions parameterResolved captured argument encodedContinuation
  obtain ⟨assignment, patternInput, patternOutput⟩ := match_one_rule_complete parameter index argument bindings body
    (OCaml.recursiveEnvironment group definitions captured) encodedContinuation matched
  refine ⟨recursiveRow group slot body (patternId index) definitions, assignment, present, input,
    request.trans patternInput.symm, ?_⟩
  rw [patternOutput]
  simpa only [OCaml.enterBody, matched] using enter_body_encoding body
    (OCaml.recursiveEnvironment group definitions captured) continuation continuationResolved matched

#print axioms recursive_rule_origin
#print axioms recursive_row_instance
#print axioms recursive_source_success
#print axioms recursive_rules_complete
#print axioms recursive_selected_row
#print axioms recursive_pattern_lowering

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlCompilation
