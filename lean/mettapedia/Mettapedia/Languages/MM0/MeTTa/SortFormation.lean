import Mettapedia.Languages.MM0.MeTTa.TableAccess
import Mettapedia.Languages.MM0.Kernel.DeclarationAdmission

/-!
# Sort uses in the retained MM0 source

Formation reads declared sort profiles. Bound parameters exclude strict sorts,
results exclude pure sorts, statements require provability, and fresh dummies
exclude both strict and free sorts. Lookup does not authorize a declaration.
The source computes these flags without changing the sort table or any cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SortFormation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean)
open NamedSpaces (Handle)
open Kernel (SortInfo)
open ListAccess (listValue optionValue)
open Store (natural)
open TableAccess (tableValue)

def sortValue (info : SortInfo) : Atom :=
  listValue [.symbol "MM0:Sort", boolean info.pure, boolean info.strict, boolean info.provable, boolean info.free]

inductive Use where
  | bound | regular | result | statement | dummy

def useValue : Use → Atom
  | .bound => .symbol "Bound"
  | .regular => .symbol "Regular"
  | .result => .symbol "Result"
  | .statement => .symbol "Statement"
  | .dummy => .symbol "Dummy"

def flag (value : Option SortInfo) (use : Use) : Bool :=
  match value with
  | none => false
  | some info => match use with
    | .bound => !info.strict
    | .regular => true
    | .result => !info.pure
    | .statement => info.provable
    | .dummy => !info.strict && !info.free

def rows (entries : List (Nat × SortInfo)) : List Atom :=
  Store.rows (entries.map fun entry => (entry.1, sortValue entry.2))

def signature (entries : List (Nat × SortInfo)) : Kernel.SortSignature := fun index => entries.lookup index

private def notEquation : SourceProgram.Equation := (kernelSource.program.equations.take 85)[84]'(by decide)
private def andEquation : SourceProgram.Equation := (kernelSource.program.equations.take 86)[85]'(by decide)
private def sortEquation : SourceProgram.Equation := (kernelSource.program.equations.take 92)[91]'(by decide)
private def infoEquation : SourceProgram.Equation := (kernelSource.program.equations.take 93)[92]'(by decide)

private def casesOf (body : Atom) : SourceProgram.Cases :=
  match body with
  | .expression [_, _, .expression cases] => (readCases cases).getD []
  | _ => []
private def notCases := casesOf notEquation.body
private def andCases := casesOf andEquation.body
private def infoCases := casesOf infoEquation.body
private def dummyBody : Atom := (infoCases[5]'(by decide)).2

private def infoEnvironment (info : Option SortInfo) (use : Use) : Subst :=
  [("useInput", useValue use), ("valueInput", optionValue (info.map sortValue))]

private def flagsEnvironment (info : SortInfo) (use : Use) : Subst :=
  [("free", boolean info.free), ("provable", boolean info.provable),
   ("strict", boolean info.strict), ("pure", boolean info.pure)] ++ infoEnvironment (some info) use

private def sortEnvironment (handle : Handle) (index : Nat) (use : Use) : Subst :=
  [("use", useValue use), ("sort", natural index), ("sorts", tableValue handle)]

private theorem not_unique : program.equations.filter (fun e => e.head == "mm0:form-not") = [notEquation] := by decide
private theorem and_unique : program.equations.filter (fun e => e.head == "mm0:form-and") = [andEquation] := by decide
private theorem info_unique : program.equations.filter (fun e => e.head == "mm0:form-sort-info") = [infoEquation] := by decide
private theorem sort_unique : program.equations.filter (fun e => e.head == "mm0:form-sort") = [sortEquation] := by decide
private theorem not_formals : notEquation.arguments = [.var "conditionInput"] := by decide
private theorem and_formals : andEquation.arguments = [.var "conditionInput", .var "right"] := by decide
private theorem info_formals : infoEquation.arguments = [.var "valueInput", .var "useInput"] := by decide
private theorem sort_formals : sortEquation.arguments = [.var "sorts", .var "sort", .var "use"] := by decide

private theorem not_shape : notEquation.body =
    .expression [.symbol "case", .expression [.var "conditionInput"],
      .expression (notCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem not_cases : notCases =
    [(.expression [boolean true], boolean false), (.expression [boolean false], boolean true), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem and_shape : andEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (andCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem and_cases : andCases =
    [(boolean true, .var "right"), (boolean false, boolean false), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

theorem not_returns (bindings : Subst) (state : State) (value : Bool) (name : String)
    (captured : applySubst bindings (.var name) = boolean value) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-not", .var name]) state (boolean (!value)) := by
  let callee : Subst := [("conditionInput", boolean value)]
  have body : PureReturns program callee state notEquation.body state (boolean (!value)) := by
    rw [not_shape]
    have input : PureReturns program callee state (.expression [.var "conditionInput"]) state (.expression [boolean value]) := by
      simpa [callee, applySubst, Subst.lookup] using tuple_variables_return program callee state ["conditionInput"]
    cases value with
    | false =>
        apply case_returns program callee callee state state state _ _ (boolean true) _ _ notCases (read_cases_encoded _) input
        · simp [not_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, boolean]
        · exact grounded_returns program callee state (.bool true)
    | true =>
        apply case_returns program callee callee state state state _ _ (boolean false) _ _ notCases (read_cases_encoded _) input
        · simp [not_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, boolean]
        · exact grounded_returns program callee state (.bool false)
  apply authored_variable_call_returns program bindings callee state state "mm0:form-not" [name] notEquation.body _
    (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, not_unique]
  simp [captured, not_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, callee]

theorem and_returns (bindings : Subst) (state : State) (left right : Bool) (leftName rightName : String)
    (capturedLeft : applySubst bindings (.var leftName) = boolean left)
    (capturedRight : applySubst bindings (.var rightName) = boolean right) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-and", .var leftName, .var rightName]) state (boolean (left && right)) := by
  let callee : Subst := [("right", boolean right), ("conditionInput", boolean left)]
  have body : PureReturns program callee state andEquation.body state (boolean (left && right)) := by
    rw [and_shape]
    have input : PureReturns program callee state (.var "conditionInput") state (boolean left) := by
      simpa [callee, applySubst, Subst.lookup] using variable_returns program callee state "conditionInput"
    cases left with
    | false =>
        apply case_returns program callee callee state state state _ _ (boolean false) _ _ andCases (read_cases_encoded _) input
        · simp [and_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
        · exact grounded_returns program callee state (.bool false)
    | true =>
        apply case_returns program callee callee state state state _ _ (.var "right") _ _ andCases (read_cases_encoded _) input
        · simp [and_cases, SourceProgram.selectCase, SourceProgram.matchValue, matchAtom, boolean]
        · simpa [callee, applySubst, Subst.lookup, boolean] using variable_returns program callee state "right"
  apply authored_variable_call_returns program bindings callee state state "mm0:form-and" [leftName, rightName] andEquation.body _
    (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, and_unique]
  simp [capturedLeft, capturedRight, and_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, callee]

private def sortPattern : Atom :=
  .expression [.symbol "Some", listValue [.symbol "MM0:Sort", .var "pure", .var "strict", .var "provable", .var "free"]]

private theorem info_shape : infoEquation.body =
    .expression [.symbol "case", .expression [.var "valueInput", .var "useInput"],
      .expression (infoCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem info_cases : infoCases =
    [(.expression [.symbol "None", .var "use"], boolean false),
     (.expression [sortPattern, useValue .bound], .expression [.symbol "mm0:form-not", .var "strict"]),
     (.expression [sortPattern, useValue .regular], boolean true),
     (.expression [sortPattern, useValue .result], .expression [.symbol "mm0:form-not", .var "pure"]),
     (.expression [sortPattern, useValue .statement], .var "provable"),
     (.expression [sortPattern, useValue .dummy], dummyBody), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem dummy_shape : dummyBody =
    .expression [.symbol "let", .var "formNotResult", .expression [.symbol "mm0:form-not", .var "strict"],
      .expression [.symbol "let", .var "formNotResult2", .expression [.symbol "mm0:form-not", .var "free"],
        .expression [.symbol "mm0:form-and", .var "formNotResult", .var "formNotResult2"]]] := by decide

private theorem dummy_returns (info : SortInfo) (state : State) :
    PureReturns program (flagsEnvironment info .dummy) state dummyBody state (boolean (!info.strict && !info.free)) := by
  rw [dummy_shape]
  let bindings := flagsEnvironment info .dummy
  let withStrict := ("formNotResult", boolean (!info.strict)) :: bindings
  let withFree := ("formNotResult2", boolean (!info.free)) :: withStrict
  apply let_returns program bindings withStrict state state state (.var "formNotResult") _ _ (boolean (!info.strict)) _
  · apply not_returns; simp [bindings, flagsEnvironment, applySubst, Subst.lookup]
  · simp [SourceProgram.matchValue, matchAtom, bindings, withStrict, flagsEnvironment, infoEnvironment, Subst.lookup]
  · apply let_returns program withStrict withFree state state state (.var "formNotResult2") _ _ (boolean (!info.free)) _
    · apply not_returns; simp [withStrict, bindings, flagsEnvironment, applySubst, Subst.lookup]
    · simp [SourceProgram.matchValue, matchAtom, withFree, withStrict, bindings, flagsEnvironment, infoEnvironment, Subst.lookup]
    · exact and_returns withFree state (!info.strict) (!info.free) "formNotResult" "formNotResult2" rfl rfl

theorem info_body_returns (info : Option SortInfo) (use : Use) (state : State) :
    PureReturns program (infoEnvironment info use) state infoEquation.body state (boolean (flag info use)) := by
  rw [info_shape]
  have input : PureReturns program (infoEnvironment info use) state (.expression [.var "valueInput", .var "useInput"]) state
      (.expression [optionValue (info.map sortValue), useValue use]) := by
    simpa [infoEnvironment, applySubst, Subst.lookup] using tuple_variables_return program (infoEnvironment info use) state ["valueInput", "useInput"]
  cases info with
  | none =>
      let bindings := infoEnvironment none use
      let bound := ("use", useValue use) :: bindings
      apply case_returns program bindings bound state state state _ _ (boolean false) _ _ infoCases (read_cases_encoded _) input
      · simp [info_cases, SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
          matchAtom, bindings, bound, infoEnvironment, optionValue, Subst.lookup]
      · exact grounded_returns program bound state (.bool false)
  | some info =>
      cases use with
      | bound =>
          apply case_returns program _ (flagsEnvironment info .bound) state state state _ _
            (.expression [.symbol "mm0:form-not", .var "strict"]) _ _ infoCases (read_cases_encoded _) input
          · simp [info_cases, sortPattern, sortValue, listValue, optionValue, useValue, flagsEnvironment, infoEnvironment,
              SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup]
          · apply not_returns; simp [flagsEnvironment, applySubst, Subst.lookup]
      | regular =>
          apply case_returns program _ (flagsEnvironment info .regular) state state state _ _ (boolean true) _ _ infoCases (read_cases_encoded _) input
          · simp [info_cases, sortPattern, sortValue, listValue, optionValue, useValue, flagsEnvironment, infoEnvironment,
              SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup]
          · exact grounded_returns program _ state (.bool true)
      | result =>
          apply case_returns program _ (flagsEnvironment info .result) state state state _ _
            (.expression [.symbol "mm0:form-not", .var "pure"]) _ _ infoCases (read_cases_encoded _) input
          · simp [info_cases, sortPattern, sortValue, listValue, optionValue, useValue, flagsEnvironment, infoEnvironment,
              SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup]
          · apply not_returns; simp [flagsEnvironment, applySubst, Subst.lookup]
      | statement =>
          apply case_returns program _ (flagsEnvironment info .statement) state state state _ _ (.var "provable") _ _ infoCases (read_cases_encoded _) input
          · simp [info_cases, sortPattern, sortValue, listValue, optionValue, useValue, flagsEnvironment, infoEnvironment,
              SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup]
          · simpa [flagsEnvironment, applySubst, Subst.lookup, flag] using variable_returns program (flagsEnvironment info .statement) state "provable"
      | dummy =>
          apply case_returns program _ (flagsEnvironment info .dummy) state state state _ _ dummyBody _ _ infoCases (read_cases_encoded _) input
          · simp [info_cases, sortPattern, sortValue, listValue, optionValue, useValue, flagsEnvironment, infoEnvironment,
              SourceProgram.selectCase, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup]
          · exact dummy_returns info state

theorem info_captured_returns (bindings : Subst) (state : State) (info : Option SortInfo) (use : Use)
    (valueName useName : String)
    (capturedValue : applySubst bindings (.var valueName) = optionValue (info.map sortValue))
    (capturedUse : applySubst bindings (.var useName) = useValue use) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-sort-info", .var valueName, .var useName]) state (boolean (flag info use)) := by
  apply authored_variable_call_returns program bindings (infoEnvironment info use) state state "mm0:form-sort-info"
    [valueName, useName] infoEquation.body _ (by decide) (by decide) (by decide) _ (info_body_returns info use state) (by decide)
  rw [clauses_use_only_the_named_equations, info_unique]
  simp [capturedValue, capturedUse, info_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, infoEnvironment]

private theorem sort_shape : sortEquation.body =
    .expression [.symbol "let", .var "declaration", .expression [.symbol "mm0:nat-table-get", .var "sorts", .var "sort"],
      .expression [.symbol "mm0:form-sort-info", .var "declaration", .var "use"]] := by decide

theorem sort_body_returns (handle : Handle) (entries : List (Nat × SortInfo)) (index : Nat) (use : Use) (state : State)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (rows entries)) :
    PureReturns program (sortEnvironment handle index use) state sortEquation.body state (boolean (flag (signature entries index) use)) := by
  rw [sort_shape]
  let bindings := sortEnvironment handle index use
  let bound := ("declaration", optionValue ((entries.lookup index).map sortValue)) :: bindings
  apply let_returns program bindings bound state state state (.var "declaration") _ _ (optionValue ((entries.lookup index).map sortValue)) _
  · exact TableAccess.indexed_lookup_returns sortValue bindings state handle entries index "sorts" "sort" unique allocated
      (by simp [bindings, sortEnvironment, applySubst, Subst.lookup]) (by simp [bindings, sortEnvironment, applySubst, Subst.lookup])
  · simp [SourceProgram.matchValue, matchAtom, bound, bindings, sortEnvironment, Subst.lookup]
  · exact info_captured_returns bound state (entries.lookup index) use "declaration" "use" rfl rfl

theorem sort_captured_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List (Nat × SortInfo)) (index : Nat) (use : Use) (tableName indexName useName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (rows entries))
    (capturedTable : applySubst bindings (.var tableName) = tableValue handle)
    (capturedIndex : applySubst bindings (.var indexName) = natural index)
    (capturedUse : applySubst bindings (.var useName) = useValue use) :
    PureReturns program bindings state (.expression [.symbol "mm0:form-sort", .var tableName, .var indexName, .var useName]) state
      (boolean (flag (signature entries index) use)) := by
  apply authored_variable_call_returns program bindings (sortEnvironment handle index use) state state "mm0:form-sort"
    [tableName, indexName, useName] sortEquation.body _ (by decide) (by decide) (by decide) _
    (sort_body_returns handle entries index use state unique allocated) (by decide)
  rw [clauses_use_only_the_named_equations, sort_unique]
  simp [capturedTable, capturedIndex, capturedUse, sort_formals, SourceProgram.matchValue,
    SourceProgram.matchValue.matchValues, matchAtom, Subst.lookup, sortEnvironment]

theorem sort_use_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × SortInfo))
    (index : Nat) (use : Use) (sortsName indexName : String)
    (unique : ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1)
    (allocated : state.read handle = some (rows entries))
    (capturedSorts : applySubst bindings (.var sortsName) = tableValue handle)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:form-sort", .var sortsName, .var indexName, useValue use]) state
      (boolean (flag (signature entries index) use)) := by
  apply call_returns program bindings state state "mm0:form-sort" _ _ (by decide) _ (by decide)
  apply variable_prefix_arguments_return program bindings state state (.function "mm0:form-sort")
    [sortsName, indexName] [useValue use] [] 0 _
  apply raw_arguments_return program bindings state state "mm0:form-sort" [useValue use] _ 2 _
  · intro offset bounded
    have zero : offset = 0 := by simpa using bounded
    subst offset
    decide
  · apply authored_function_arguments_return program bindings (sortEnvironment handle index use) state state "mm0:form-sort"
      _ 3 sortEquation.body _ (by decide) (by decide) _ (sort_body_returns handle entries index use state unique allocated)
    rw [clauses_use_only_the_named_equations, sort_unique]
    have useCaptured : applySubst bindings (useValue use) = useValue use := by cases use <;> rfl
    simp [capturedSorts, capturedIndex, useCaptured, sort_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
      matchAtom, Subst.lookup, sortEnvironment]

theorem dummy_flag (sorts : Kernel.SortSignature) (index : Nat) :
    flag (sorts index) .dummy = Kernel.Definition.dummySortAllowed sorts index := by
  cases known : sorts index <;> simp [flag, Kernel.Definition.dummySortAllowed, known]

theorem bound_flag (sorts : Kernel.SortSignature) (context : Kernel.Context) (index : Nat) :
    flag (sorts index) .bound = Kernel.Context.checkBinder sorts context (.bound index) := by
  cases known : sorts index <;> simp [flag, Kernel.Context.checkBinder, known]

theorem bound_flag_iff (sorts : Kernel.SortSignature) (context : Kernel.Context) (index : Nat) :
    flag (sorts index) .bound = true ↔ Kernel.Context.AdmitsBinder sorts context (.bound index) := by
  rw [bound_flag]
  exact Kernel.Context.checkBinder_iff sorts context (.bound index)

theorem regular_flag_iff (sorts : Kernel.SortSignature) (index : Nat) :
    flag (sorts index) .regular = true ↔ ∃ info, sorts index = some info := by
  cases known : sorts index <;> simp [flag]

theorem result_flag_iff (sorts : Kernel.SortSignature) (index : Nat) :
    flag (sorts index) .result = true ↔ ∃ info, sorts index = some info ∧ info.pure = false := by
  cases known : sorts index <;> simp [flag]

theorem statement_flag_iff (sorts : Kernel.SortSignature) (index : Nat) :
    flag (sorts index) .statement = true ↔ ∃ info, sorts index = some info ∧ info.provable = true := by
  cases known : sorts index <;> simp [flag]

theorem dummy_flag_iff (sorts : Kernel.SortSignature) (index : Nat) :
    flag (sorts index) .dummy = true ↔
      ∃ info, sorts index = some info ∧ info.strict = false ∧ info.free = false := by
  rw [dummy_flag]
  exact Kernel.Definition.dummySortAllowed_iff sorts index

end Mettapedia.Languages.MM0.MeTTa.SortFormation
