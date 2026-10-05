import Mettapedia.Languages.MM0.MeTTa.Data
import Mettapedia.Languages.MM0.ServiceInferenceCache

/-!
# Declaration lookup in the retained MM0 source

Private tables store ordinary indexed rows. The source distinguishes no
match, one match and repeated matches; equal repeated values remain repeated
observations. Lookup is read-only and does not itself authorize a declaration.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.TableAccess

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State handleValue)
open NamedSpaces (Handle)
open Store (natural indexedQuery)

def tableValue (handle : Handle) : Atom :=
  .expression [.symbol "MM0:Table", handleValue handle]

theorem table_literal (handle : Handle) : SourceProgram.Literal (tableValue handle) := by
  apply SourceProgram.Literal.constructor "MM0:Table" [handleValue handle] (by decide)
  have literal : SourceProgram.Literal (handleValue handle) := by
    cases handle with
    | self => exact .symbol _
    | privateSpace index => exact .grounded _
  simpa using literal

def declarationRows (entries : List ServiceInferenceCache.Row) : List Atom :=
  Store.rows (entries.map fun entry => (entry.1, Data.declaration entry.2))

theorem query_declaration_rows (entries : List ServiceInferenceCache.Row) (index : Nat) :
    indexedQuery (declarationRows entries) index =
      ((entries.filter fun entry => entry.1 = index).map fun entry => Data.declaration entry.2) := by
  rw [declarationRows, Store.query_indexed_rows]
  simp [List.filter_map, Function.comp_def, beq_eq_decide]

def queryAnswer : List Atom → Atom
  | [] => .symbol "None"
  | [value] => ListAccess.optionValue (some value)
  | _ :: _ :: _ => .symbol "MM0:Malformed"

private def environment (handle : Handle) (index : Nat) : Subst :=
  [("key", natural index), ("table", tableValue handle)]

private def tableEnvironment (handle : Handle) (index : Nat) : Subst :=
  ("space", handleValue handle) :: environment handle index

private def equation : SourceProgram.Equation := dataSource.program.equations[5]'(by decide)

private def declarationEquation : SourceProgram.Equation :=
  dataSource.program.equations[7]'(by decide)

private theorem unique :
    program.equations.filter (fun entry => entry.head == "mm0:nat-table-get") = [equation] := by decide

private theorem declaration_unique :
    program.equations.filter (fun entry => entry.head == "mm0:declaration") =
      [declarationEquation] := by decide

private theorem formals : equation.arguments = [.var "table", .var "key"] := by decide

private theorem declaration_formals :
    declarationEquation.arguments = [.var "table", .var "index"] := by decide

private def cases : SourceProgram.Cases :=
  match equation.body with
  | .expression [_, _, .expression entries] => (readCases entries).getD []
  | _ => []

private def tableBody : Atom := (cases[0]'(by decide)).2
private def listBody : Atom := (cases[1]'(by decide)).2

private def foundBody : Atom :=
  match tableBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def foundCases : SourceProgram.Cases :=
  match foundBody with
  | .expression [_, _, .expression entries] => (readCases entries).getD []
  | _ => []

private theorem body_shape :
    equation.body = .expression [.symbol "case", .var "table",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [.symbol "MM0:Table", .var "space"], tableBody),
      (.expression [.symbol "MM0:L", .var "entries"], listBody)] := by decide

private theorem table_body_shape :
    tableBody = .expression [.symbol "let", .var "found",
      .expression [.symbol "collapse", .expression [.symbol "match", .var "space",
        .expression [.var "key", .var "value"], .var "value"]], foundBody] := by decide

private theorem found_body_shape :
    foundBody = .expression [.symbol "case", .var "found",
      .expression (foundCases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem found_cases_shape :
    foundCases = [(.expression [], .symbol "None"),
      (.expression [.var "value"], .expression [.symbol "Some", .var "value"]),
      (.var "duplicates", .symbol "MM0:Malformed")] := by decide

private theorem declaration_body_shape :
    declarationEquation.body =
      .expression [.symbol "mm0:nat-table-get", .var "table", .var "index"] := by decide

theorem table_clause (handle : Handle) (index : Nat) :
    clauses program "mm0:nat-table-get" [tableValue handle, natural index] =
      [.evaluate (environment handle index) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem found_body_returns (state : State) (handle : Handle) (index : Nat)
    (answers : List Atom) :
    PureReturns program (("found", .expression answers) :: tableEnvironment handle index)
      state foundBody state (queryAnswer answers) := by
  let bindings := ("found", .expression answers) :: tableEnvironment handle index
  rw [found_body_shape]
  cases answers with
  | nil =>
      apply case_returns program bindings bindings state state state (.var "found")
        (.expression []) (.symbol "None") _ _ foundCases (read_cases_encoded foundCases)
      · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
      · simp [found_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
          SourceProgram.matchValue.matchValues]
      · exact symbol_returns program bindings state "None"
  | cons first rest =>
      cases rest with
      | nil =>
          let bound := ("value", first) :: bindings
          apply case_returns program bindings bound state state state (.var "found")
            (.expression [first]) (.expression [.symbol "Some", .var "value"]) _ _ foundCases
            (read_cases_encoded foundCases)
          · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
          · simp [found_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
              SourceProgram.matchValue.matchValues, matchAtom, bindings, tableEnvironment,
              environment, Subst.lookup, bound]
          · simpa [bound, applySubst, Subst.lookup, queryAnswer, ListAccess.optionValue] using
              unary_constructor_returns program bound state "Some" "value" some_is_data_constructor (by decide)
      | cons second rest =>
          let bound := ("duplicates", .expression (first :: second :: rest)) :: bindings
          apply case_returns program bindings bound state state state (.var "found")
            (.expression (first :: second :: rest)) (.symbol "MM0:Malformed") _ _ foundCases
            (read_cases_encoded foundCases)
          · simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "found"
          · simp [found_cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
              SourceProgram.matchValue.matchValues, matchAtom, bindings, tableEnvironment,
              environment, Subst.lookup, bound]
          · exact symbol_returns program bound state "MM0:Malformed"

theorem table_body_returns (state : State) (handle : Handle) (entries : List Atom) (index : Nat)
    (allocated : state.read handle = some entries) :
    PureReturns program (environment handle index) state equation.body state
      (queryAnswer (indexedQuery entries index)) := by
  rw [body_shape]
  apply case_returns program (environment handle index) (tableEnvironment handle index)
    state state state (.var "table") (tableValue handle) tableBody _ _ cases (read_cases_encoded cases)
  · simpa [environment, applySubst, Subst.lookup] using
      variable_returns program (environment handle index) state "table"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, tableValue, environment,
      tableEnvironment, Subst.lookup]
  · rw [table_body_shape]
    apply let_returns program (tableEnvironment handle index)
      (("found", .expression (indexedQuery entries index)) :: tableEnvironment handle index)
      state state state (.var "found") _ _ (.expression (indexedQuery entries index)) _
    · apply match_collapse_returns program (tableEnvironment handle index) state state "space" _ _
        (indexedQuery entries index)
      simp [tableEnvironment, environment, applySubst, applySubst.applySubstList,
        Subst.lookup, SourcePrimitives.apply, allocated, Store.indexedQuery]
    · simp [SourceProgram.matchValue, matchAtom, tableEnvironment, environment, Subst.lookup]
    · exact found_body_returns state handle index (indexedQuery entries index)

theorem table_captured_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List Atom) (index : Nat) (tableName indexName : String)
    (allocated : state.read handle = some entries)
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-table-get", .var tableName, .var indexName])
      state (queryAnswer (indexedQuery entries index)) := by
  apply authored_variable_call_returns program bindings (environment handle index) state state
    "mm0:nat-table-get" [tableName, indexName] equation.body _ (by decide) (by decide) (by decide)
    _ (table_body_returns state handle entries index allocated) (by decide)
  simpa [tableCaptured, indexCaptured] using table_clause handle index

theorem declaration_captured_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List Atom) (index : Nat) (tableName indexName : String)
    (allocated : state.read handle = some entries)
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:declaration", .var tableName, .var indexName])
      state (queryAnswer (indexedQuery entries index)) := by
  let callee : Subst := [("index", natural index), ("table", tableValue handle)]
  have called : clauses program "mm0:declaration" [tableValue handle, natural index] =
      [.evaluate callee declarationEquation.body] := by
    rw [clauses_use_only_the_named_equations, declaration_unique]
    simp [declaration_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, Subst.lookup, callee]
  apply authored_variable_call_returns program bindings callee state state "mm0:declaration"
    [tableName, indexName] declarationEquation.body _ (by decide) (by decide) (by decide) _ _ (by decide)
  · simpa [tableCaptured, indexCaptured] using called
  · rw [declaration_body_shape]
    exact table_captured_returns callee state handle entries index "table" "index" allocated
      (by simp [callee, applySubst, Subst.lookup]) (by simp [callee, applySubst, Subst.lookup])

/-- On the unique indexed rows of an admitted theory, the source lookup is
the signature lookup used by the independent kernel. -/
theorem declaration_signature_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List ServiceInferenceCache.Row) (index : Nat) (tableName indexName : String)
    (unique : ServiceInferenceCache.Unique entries)
    (allocated : state.read handle = some (declarationRows entries))
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:declaration", .var tableName, .var indexName]) state
      (ListAccess.optionValue
        ((Presentation.ComputationalTyping.signatureOf entries index).map Data.declaration)) := by
  have source := declaration_captured_returns bindings state handle (declarationRows entries) index
    tableName indexName allocated tableCaptured indexCaptured
  have bounded := unique index
  rw [query_declaration_rows] at source
  cases filtered : entries.filter (fun entry => entry.1 = index) with
  | nil =>
      have absent := ServiceInferenceCache.signatureOf_of_filter_nil index entries filtered
      simpa [filtered, absent, queryAnswer, ListAccess.optionValue] using source
  | cons first rest =>
      cases rest with
      | nil =>
          have present := ServiceInferenceCache.signatureOf_of_filter_single index entries first filtered
          simpa [filtered, present, queryAnswer, ListAccess.optionValue] using source
      | cons second rest => simp [filtered] at bounded

/-- The same table operation reads term, definition and theorem payloads.
The row invariant, rather than a guest lookup primitive, supplies uniqueness. -/
theorem indexed_rows_returns {Value : Type} (encode : Value → Atom)
    (bindings : Subst) (state : State) (handle : Handle)
    (entries : List (Nat × Value)) (index : Nat) (tableName indexName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (Store.rows (entries.map fun entry => (entry.1, encode entry.2))))
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-table-get", .var tableName, .var indexName]) state
      (ListAccess.optionValue ((entries.find? fun entry => entry.1 = index).map fun entry => encode entry.2)) := by
  have returned := table_captured_returns bindings state handle _ index tableName indexName
    allocated tableCaptured indexCaptured
  rw [Store.query_indexed_rows] at returned
  have filtered : ((entries.map fun entry => (entry.1, encode entry.2)).filter
      (fun entry => entry.1 == index)).map Prod.snd =
      (entries.filter fun entry => entry.1 = index).map (fun entry => encode entry.2) := by
    simp [List.filter_map, List.map_map, Function.comp_def, beq_eq_decide]
  have bounded := unique index
  rw [filtered] at returned
  rw [← List.head?_filter (l := entries) (p := fun entry => decide (entry.1 = index))]
  cases found : entries.filter (fun entry => entry.1 = index) with
  | nil => simpa [found, queryAnswer, ListAccess.optionValue] using returned
  | cons entry rest =>
      cases rest with
      | nil => simpa [found, queryAnswer, ListAccess.optionValue] using returned
      | cons other rest => simp [found] at bounded

/-- The independent kernel reads the same association list with `lookup`.
This identity concerns first lookup, not the native duplicate-admission check. -/
theorem lookup_eq_find {Value : Type} (entries : List (Nat × Value)) (index : Nat) :
    entries.lookup index = (entries.find? fun entry => entry.1 = index).map Prod.snd := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      rcases entry with ⟨key, value⟩
      by_cases same : index = key <;>
        simp [List.lookup, List.find?, beq_eq_decide, eq_comm, ih, same]

/-- A unique native table returns the independent kernel's association lookup. -/
theorem indexed_lookup_returns {Value : Type} (encode : Value → Atom)
    (bindings : Subst) (state : State) (handle : Handle)
    (entries : List (Nat × Value)) (index : Nat) (tableName indexName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (Store.rows (entries.map fun entry => (entry.1, encode entry.2))))
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle)
    (indexCaptured : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:nat-table-get", .var tableName, .var indexName]) state
      (ListAccess.optionValue ((entries.lookup index).map encode)) := by
  rw [lookup_eq_find, Option.map_map]
  exact indexed_rows_returns encode bindings state handle entries index tableName indexName unique allocated tableCaptured indexCaptured

theorem missing_row_is_refused (state : State) (handle : Handle) (index : Nat)
    (allocated : state.read handle = some []) :
    PureReturns program [("table", tableValue handle), ("key", natural index)] state
      (.expression [.symbol "mm0:nat-table-get", .var "table", .var "key"])
      state (.symbol "None") :=
  table_captured_returns _ state handle [] index "table" "key" allocated rfl rfl

theorem duplicate_rows_are_malformed (state : State) (handle : Handle) (index : Nat) (value : Atom)
    (allocated : state.read handle = some (Store.rows [(index, value), (index, value)])) :
    PureReturns program [("table", tableValue handle), ("key", natural index)] state
      (.expression [.symbol "mm0:nat-table-get", .var "table", .var "key"])
      state (.symbol "MM0:Malformed") := by
  simpa [Store.duplicate_rows_are_visible, queryAnswer] using
    table_captured_returns _ state handle (Store.rows [(index, value), (index, value)]) index
      "table" "key" allocated rfl rfl

end Mettapedia.Languages.MM0.MeTTa.TableAccess
