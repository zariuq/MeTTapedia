import Mettapedia.Languages.MM0.MeTTa.Admission.SessionInitialization
import Mettapedia.Languages.MM0.MeTTa.Formation.TheoremFormation
import Mettapedia.Languages.MM0.MeTTa.Formation.TermFormation
import Mettapedia.Languages.MM0.MeTTa.Formation.BodyFormation
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission

/-!
# Admission checks in the retained MM0 program

The native tables retain chronological row order, while the kernel inserts
new declarations at the front of an association list. Their contents are
related by reversal. Unique keys derive lookup agreement; no lookup grants
authorization. Formation and supplied-proof calls follow the source's eager
order, including checks performed after an earlier Boolean refusal.

Specification matching and publication are separate operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.AdmissionChecks

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Theory Admission TermDecl TheoremDecl SortInfo)
open Store (natural)
open ListAccess (listValue optionValue)
open TableAccess (tableValue declarationRows)
open Presentation.ComputationalTyping (signatureOf)
open SessionInitialization (Spaces theoryValue)

/-- Native duplicate detection requires at most one row for each key. -/
def UniqueKeys {Value : Type} (entries : List (Nat × Value)) : Prop :=
  ∀ key, (entries.filter fun entry => entry.1 = key).length ≤ 1

theorem uniqueKeys_reverse {Value : Type} {entries : List (Nat × Value)}
    (unique : UniqueKeys entries) : UniqueKeys entries.reverse := by
  intro key
  simpa only [List.filter_reverse, List.length_reverse] using unique key

/-- Reversing a unique table preserves its association lookup. -/
theorem lookup_reverse {Value : Type} (entries : List (Nat × Value))
    (unique : UniqueKeys entries) (index : Nat) :
    entries.reverse.lookup index = entries.lookup index := by
  rw [TableAccess.lookup_eq_find, TableAccess.lookup_eq_find,
    ← List.head?_filter, ← List.head?_filter, List.filter_reverse]
  have bounded := unique index
  cases filtered : entries.filter (fun entry => entry.1 = index) with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest => simp [filtered] at bounded

/-- Physical ownership and unique row contents, before logical admission. -/
structure TableReady (spaces : Spaces) (theory : Theory) (state : State) : Prop where
  sorts : state.read spaces.sorts = some (SortFormation.rows theory.sorts.reverse)
  terms : state.read spaces.terms = some (declarationRows theory.terms.reverse)
  definitions : state.read spaces.definitions = some (Unfolding.definitionRows theory.definitions.reverse)
  theorems : state.read spaces.theorems = some (Proof.theoremRows theory.theorems.reverse)
  uniqueSorts : UniqueKeys theory.sorts
  uniqueTerms : UniqueKeys theory.terms
  uniqueDefinitions : UniqueKeys theory.definitions
  uniqueTheorems : UniqueKeys theory.theorems
  separate : spaces.handles.Nodup

/-- Cache observations belong to the current preceding declaration scope. -/
structure Ready (spaces : Spaces) (theory : Theory) (state : State) : Prop
    extends TableReady spaces theory state where
  cache : InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache state

theorem TableReady.separate_sort {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : spaces.sorts ≠ spaces.cache := by
  have absent := (List.nodup_cons.mp ready.separate).1
  intro same
  exact absent (by simp [same])

theorem TableReady.separate_term {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : spaces.terms ≠ spaces.cache := by
  have absent := (List.nodup_cons.mp ready.separate).1
  intro same
  exact absent (by simp [same])

theorem TableReady.separate_definition {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : spaces.definitions ≠ spaces.cache := by
  have absent := (List.nodup_cons.mp ready.separate).1
  intro same
  exact absent (by simp [same])

theorem TableReady.separate_theorem {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : spaces.theorems ≠ spaces.cache := by
  have absent := (List.nodup_cons.mp ready.separate).1
  intro same
  exact absent (by simp [same])

theorem TableReady.separate_proof {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : spaces.proofs ≠ spaces.cache := by
  have absent := (List.nodup_cons.mp ready.separate).1
  intro same
  exact absent (by simp [same])

theorem TableReady.sort_signature {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) :
    SortFormation.signature theory.sorts.reverse = theory.sortSignature := by
  funext index
  exact lookup_reverse theory.sorts ready.uniqueSorts index

theorem TableReady.term_signature {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) : signatureOf theory.terms.reverse = theory.termSignature := by
  funext index
  rw [Presentation.ComputationalTyping.signatureOf_eq_lookup]
  exact lookup_reverse theory.terms ready.uniqueTerms index

theorem TableReady.definition_signature {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) :
    Unfolding.definitionSignature theory.definitions.reverse = theory.definitionSignature := by
  funext index
  unfold Unfolding.definitionSignature
  rw [← TableAccess.lookup_eq_find]
  exact lookup_reverse theory.definitions ready.uniqueDefinitions index

theorem TableReady.theorem_signature {spaces : Spaces} {theory : Theory} {state : State}
    (ready : TableReady spaces theory state) :
    Proof.theoremSignature theory.theorems.reverse = theory.theoremSignature := by
  funext index
  unfold Proof.theoremSignature
  rw [← TableAccess.lookup_eq_find]
  exact lookup_reverse theory.theorems ready.uniqueTheorems index

/-- Resetting or extending the cache leaves the declaration tables intact. -/
theorem TableReady.after_reads {spaces : Spaces} {theory : Theory} {before after : State}
    (ready : TableReady spaces theory before)
    (reads : ∀ handle, handle ≠ spaces.cache → after.read handle = before.read handle) :
    TableReady spaces theory after := by
  refine ⟨?_, ?_, ?_, ?_, ready.uniqueSorts, ready.uniqueTerms, ready.uniqueDefinitions,
    ready.uniqueTheorems, ready.separate⟩
  · rw [reads spaces.sorts ready.separate_sort]; exact ready.sorts
  · rw [reads spaces.terms ready.separate_term]; exact ready.terms
  · rw [reads spaces.definitions ready.separate_definition]; exact ready.definitions
  · rw [reads spaces.theorems ready.separate_theorem]; exact ready.theorems

theorem Ready.after_frame {spaces : Spaces} {theory : Theory} {before after : State}
    {bound : Nat} (ready : Ready spaces theory before)
    (frame : InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after)
    (cache : InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after) :
    Ready spaces theory after := by
  exact ⟨ready.toTableReady.after_reads frame.other, cache⟩

/-- The actual start operation earns the empty native-table and cache premises. -/
theorem start_ready (before : State) (specification : Atom) :
    Ready (SessionInitialization.allocatedSpaces before) ({} : Theory)
      (SessionInitialization.startState before specification) := by
  let spaces := SessionInitialization.allocatedSpaces before
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, SessionInitialization.allocated_spaces_distinct before⟩, ?_⟩
  · exact SessionInitialization.start_sort_table before specification
  · simpa [declarationRows, Store.rows] using SessionInitialization.allocated_spaces_empty before specification spaces.terms
      (by simp [spaces, SessionInitialization.Spaces.handles])
  · simpa [Unfolding.definitionRows, Store.rows] using SessionInitialization.allocated_spaces_empty before specification spaces.definitions
      (by simp [spaces, SessionInitialization.Spaces.handles])
  · simpa [Proof.theoremRows, Store.rows] using SessionInitialization.allocated_spaces_empty before specification spaces.theorems
      (by simp [spaces, SessionInitialization.Spaces.handles])
  · intro key; simp
  · intro key; simp
  · intro key; simp
  · intro key; simp
  · refine ⟨(SessionInitialization.start_owns_cells before specification).1, [], ?_, InferenceCache.empty_valid _ _⟩
    exact SessionInitialization.allocated_spaces_empty before specification spaces.cache
      (by simp [spaces, SessionInitialization.Spaces.handles])

/-- Encoding of the supplied declaration; this performs no checking. -/
def admissionValue : Admission → Atom
  | .sort index info => listValue [.symbol "MM0:AdmitSort", natural index, SortFormation.sortValue info]
  | .term index declaration => listValue [.symbol "MM0:AdmitTerm", natural index, Data.declaration declaration]
  | .definition index declaration body =>
      listValue [.symbol "MM0:AdmitDefinition", natural index, Data.declaration declaration, Unfolding.bodyValue body]
  | .axiomDecl index declaration =>
      listValue [.symbol "MM0:AdmitAxiom", natural index, TheoremInstantiation.declarationValue declaration]
  | .theoremDecl index declaration dummies proof =>
      listValue [.symbol "MM0:AdmitTheorem", natural index, TheoremInstantiation.declarationValue declaration,
        Support.indicesValue dummies, Proof.witnessValue proof]

private def freshEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 115)[114]'(by decide)
private def missingEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 116)[115]'(by decide)
private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 117)[116]'(by decide)
private def proofEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 118)[117]'(by decide)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def missingCases := casesOf missingEquation.body
private def cases := casesOf equation.body
private def sortBody := (cases[0]'(by decide)).2
private def termBody := (cases[1]'(by decide)).2
private def definitionBody := (cases[2]'(by decide)).2
private def axiomBody := (cases[3]'(by decide)).2
private def theoremBody := (cases[4]'(by decide)).2
private def branch : Admission → Atom
  | .sort _ _ => sortBody
  | .term _ _ => termBody
  | .definition _ _ _ => definitionBody
  | .axiomDecl _ _ => axiomBody
  | .theoremDecl _ _ _ _ => theoremBody

private def environment (spaces : Spaces) (admission : Admission) : Subst :=
  [("valueInputValue", admissionValue admission), ("valueInput", theoryValue spaces)]

private def fields : Admission → Subst
  | .sort index info => [("info", SortFormation.sortValue info), ("index", natural index)]
  | .term index declaration => [("declaration", Data.declaration declaration), ("index", natural index)]
  | .definition index declaration body =>
      [("body", Unfolding.bodyValue body), ("declaration", Data.declaration declaration), ("index", natural index)]
  | .axiomDecl index declaration =>
      [("declaration", TheoremInstantiation.declarationValue declaration), ("index", natural index)]
  | .theoremDecl index declaration dummies proof =>
      [("proof", Proof.witnessValue proof), ("dummies", Support.indicesValue dummies),
        ("declaration", TheoremInstantiation.declarationValue declaration), ("index", natural index)]

private def boundEnvironment (spaces : Spaces) (admission : Admission) : Subst :=
  fields admission ++ [("theorems", tableValue spaces.theorems), ("definitions", tableValue spaces.definitions),
    ("terms", tableValue spaces.terms), ("sorts", tableValue spaces.sorts)] ++ environment spaces admission

private theorem fresh_unique :
    program.equations.filter (fun row => row.head == "mm0:admission-fresh") = [freshEquation] := by decide +kernel
private theorem missing_unique :
    program.equations.filter (fun row => row.head == "mm0:admission-missing") = [missingEquation] := by decide +kernel
private theorem unique :
    program.equations.filter (fun row => row.head == "mm0:admission-check") = [equation] := by decide +kernel
private theorem proof_unique :
    program.equations.filter (fun row => row.head == "mm0:admission-proof") = [proofEquation] := by decide +kernel
private theorem fresh_formals : freshEquation.arguments = [.var "table", .var "index"] := by decide +kernel
private theorem missing_formals : missingEquation.arguments = [.var "valueInput"] := by decide +kernel
private theorem formals : equation.arguments = [.var "valueInput", .var "valueInputValue"] := by decide +kernel
private theorem fresh_shape : freshEquation.body = .expression [.symbol "let", .var "declaration",
    .expression [.symbol "mm0:nat-table-get", .var "table", .var "index"],
    .expression [.symbol "mm0:admission-missing", .var "declaration"]] := by decide +kernel
private theorem missing_shape : missingEquation.body = .expression [.symbol "case", .expression [.var "valueInput"],
    .expression (missingCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem missing_cases : missingCases = [(.expression [.symbol "None"], boolean true),
    (.expression [.expression [.symbol "Some", .var "entry"]], boolean false),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "valueInput", .var "valueInputValue"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem cases_shape : cases = [
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitSort", .var "index", .var "info"]], sortBody),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitTerm", .var "index", .var "declaration"]], termBody),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitDefinition", .var "index", .var "declaration", .var "body"]],
      definitionBody),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitAxiom", .var "index", .var "declaration"]], axiomBody),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitTheorem", .var "index", .var "declaration", .var "dummies", .var "proof"]],
      theoremBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private theorem missing_body_returns (value : Option Atom) (state : State) :
    PureReturns program [("valueInput", optionValue value)] state missingEquation.body state (boolean value.isNone) := by
  rw [missing_shape]
  let bindings : Subst := [("valueInput", optionValue value)]
  cases value with
  | none =>
      apply case_returns program bindings bindings state state state (.expression [.var "valueInput"])
        (.expression [.symbol "None"]) (boolean true) _ _ missingCases (read_cases_encoded _)
      · simpa [bindings, optionValue, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [missing_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, bindings]
      · exact grounded_returns program bindings state (.bool true)
  | some value =>
      let bound := ("entry", value) :: bindings
      apply case_returns program bindings bound state state state (.expression [.var "valueInput"])
        (.expression [.expression [.symbol "Some", value]]) (boolean false) _ _ missingCases (read_cases_encoded _)
      · simpa [bindings, optionValue, applySubst, Subst.lookup] using tuple_variables_return program bindings state ["valueInput"]
      · simp [missing_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, bindings, bound, Subst.lookup]
      · exact grounded_returns program bound state (.bool false)

private theorem missing_captured_returns (bindings : Subst) (state : State) (value : Option Atom)
    (name : String) (captured : applySubst bindings (.var name) = optionValue value) :
    PureReturns program bindings state (.expression [.symbol "mm0:admission-missing", .var name])
      state (boolean value.isNone) := by
  apply authored_variable_call_returns program bindings [("valueInput", optionValue value)] state state
    "mm0:admission-missing" [name] missingEquation.body _ (by decide) (by decide) (by decide) _
    (missing_body_returns value state) (by decide)
  rw [clauses_use_only_the_named_equations, missing_unique]
  simp [captured, missing_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

/-- The source's freshness test reads all matching rows before deciding absence. -/
theorem fresh_captured_returns {Value : Type} (encode : Value → Atom)
    (bindings : Subst) (state : State) (handle : Handle) (entries : List (Nat × Value))
    (index : Nat) (tableName indexName : String) (uniqueKeys : UniqueKeys entries)
    (allocated : state.read handle = some (Store.rows (entries.map fun entry => (entry.1, encode entry.2))))
    (capturedTable : applySubst bindings (.var tableName) = tableValue handle)
    (capturedIndex : applySubst bindings (.var indexName) = natural index) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:admission-fresh", .var tableName, .var indexName]) state
      (boolean (entries.lookup index).isNone) := by
  let callBindings : Subst := [("index", natural index), ("table", tableValue handle)]
  have body : PureReturns program callBindings state freshEquation.body state
      (boolean (entries.lookup index).isNone) := by
    rw [fresh_shape]
    let value := (entries.lookup index).map encode
    let bound := ("declaration", optionValue value) :: callBindings
    apply let_returns program callBindings bound state state state (.var "declaration") _ _ (optionValue value) _
    · exact TableAccess.indexed_lookup_returns encode callBindings state handle entries index "table" "index"
        uniqueKeys allocated rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, bound, callBindings, Subst.lookup]
    · simpa only [value, Option.isNone_map] using missing_captured_returns bound state value "declaration" rfl
  apply authored_variable_call_returns program bindings callBindings state state
    "mm0:admission-fresh" [tableName, indexName] freshEquation.body _ (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, fresh_unique]
  simp [capturedTable, capturedIndex, fresh_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, callBindings]

private theorem selected_branch (spaces : Spaces) (admission : Admission) :
    SpaceSemantics.selectCase (environment spaces admission)
      (.expression [theoryValue spaces, admissionValue admission]) cases =
      some (boundEnvironment spaces admission, branch admission) := by
  cases admission <;>
    simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, theoryValue, admissionValue,
      listValue, environment, boundEnvironment, fields, branch, Subst.lookup]

private theorem sort_shape (index : Nat) (info : SortInfo) : branch (.sort index info) =
    .expression [.symbol "mm0:admission-fresh", .var "sorts", .var "index"] := by
  change sortBody = _
  decide +kernel

private theorem term_shape (index : Nat) (declaration : TermDecl) : branch (.term index declaration) =
    .expression [.symbol "let", .var "admissionFreshResult",
      .expression [.symbol "mm0:admission-fresh", .var "terms", .var "index"],
      .expression [.symbol "let", .var "formTermResult",
        .expression [.symbol "mm0:form-term", .var "sorts", .var "declaration"],
        .expression [.symbol "mm0:form-and", .var "admissionFreshResult", .var "formTermResult"]]] := by
  change termBody = _
  decide +kernel

private theorem axiom_shape (index : Nat) (declaration : TheoremDecl) : branch (.axiomDecl index declaration) =
    .expression [.symbol "let", .var "admissionFreshResult4",
      .expression [.symbol "mm0:admission-fresh", .var "theorems", .var "index"],
      .expression [.symbol "let", .var "formTheoremResult",
        .expression [.symbol "mm0:form-theorem", .var "sorts", .var "terms", .var "declaration"],
        .expression [.symbol "mm0:form-and", .var "admissionFreshResult4", .var "formTheoremResult"]]] := by
  change axiomBody = _
  decide +kernel

/-- Calls use the actual handle-bearing theory value and supplied payload. -/
def Call (spaces : Spaces) (admission : Admission) (before after : State) (answer : Bool) : Prop :=
  ∀ bindings theoryName admissionName,
    applySubst bindings (.var theoryName) = theoryValue spaces →
    applySubst bindings (.var admissionName) = admissionValue admission →
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-check", .var theoryName, .var admissionName]) after
      (boolean answer)

private theorem call_from_branch (spaces : Spaces) (admission : Admission) (before after : State) (answer : Bool)
    (computed : PureReturns program (boundEnvironment spaces admission) before (branch admission) after (boolean answer)) :
    Call spaces admission before after answer := by
  have body : PureReturns program (environment spaces admission) before equation.body after (boolean answer) := by
    rw [shape]
    apply case_returns program (environment spaces admission) (boundEnvironment spaces admission)
      before before after (.expression [.var "valueInput", .var "valueInputValue"])
      (.expression [theoryValue spaces, admissionValue admission]) (branch admission) _ _ cases (read_cases_encoded _)
    · simpa [environment, applySubst, Subst.lookup] using tuple_variables_return program (environment spaces admission) before
        ["valueInput", "valueInputValue"]
    · exact selected_branch spaces admission
    · exact computed
  intro bindings theoryName admissionName capturedTheory capturedAdmission
  apply authored_variable_call_returns program bindings (environment spaces admission) before after
    "mm0:admission-check" [theoryName, admissionName] equation.body _ (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, unique]
  simp [capturedTheory, capturedAdmission, formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

theorem sort_captured_returns (spaces : Spaces) (theory : Theory) (index : Nat) (info : SortInfo)
    (before : State) (ready : Ready spaces theory before) :
    Call spaces (.sort index info) before before (Admission.check theory (.sort index info)) := by
  apply call_from_branch
  rw [sort_shape]
  have returned := fresh_captured_returns SortFormation.sortValue
    (boundEnvironment spaces (.sort index info)) before spaces.sorts theory.sorts.reverse index
    "sorts" "index" (uniqueKeys_reverse ready.uniqueSorts) ready.sorts rfl rfl
  simpa only [Admission.check, Theory.sortSignature, lookup_reverse theory.sorts ready.uniqueSorts] using returned

theorem term_captured_returns (spaces : Spaces) (theory : Theory) (index : Nat) (declaration : TermDecl)
    (before : State) (ready : Ready spaces theory before) :
    Call spaces (.term index declaration) before before (Admission.check theory (.term index declaration)) := by
  apply call_from_branch
  rw [term_shape]
  let bindings := boundEnvironment spaces (.term index declaration)
  let fresh := (theory.termSignature index).isNone
  let formed := TermDecl.check theory.sortSignature declaration
  let withFresh := ("admissionFreshResult", boolean fresh) :: bindings
  let withForm := ("formTermResult", boolean formed) :: withFresh
  apply let_returns program bindings withFresh before before before (.var "admissionFreshResult") _ _ (boolean fresh) _
  · have returned := fresh_captured_returns Data.declaration bindings before spaces.terms theory.terms.reverse index
      "terms" "index" (uniqueKeys_reverse ready.uniqueTerms) ready.terms rfl rfl
    simpa only [fresh, Theory.termSignature, lookup_reverse theory.terms ready.uniqueTerms] using returned
  · simp [SpaceSemantics.matchValue, matchAtom, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program withFresh withForm before before before (.var "formTermResult") _ _ (boolean formed) _
    · have returned := TermFormation.captured_returns withFresh before spaces.sorts theory.sorts.reverse declaration
        "sorts" "declaration" (uniqueKeys_reverse ready.uniqueSorts) ready.sorts rfl rfl
      simpa only [ready.sort_signature, formed] using returned
    · simp [SpaceSemantics.matchValue, matchAtom, withForm, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · exact SortFormation.and_returns withForm before fresh formed "admissionFreshResult" "formTermResult" rfl rfl

theorem axiom_captured_returns (spaces : Spaces) (theory : Theory) (index : Nat) (declaration : TheoremDecl)
    (before : State) (ready : Ready spaces theory before) :
    ∃ after,
      Call spaces (.axiomDecl index declaration) before after (Admission.check theory (.axiomDecl index declaration)) ∧
      Ready spaces theory after ∧
      InferenceCache.Frame spaces.cache (tableValue spaces.terms)
        (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) before after := by
  obtain ⟨after, formedReturned, cacheAfter, frame⟩ := TheoremFormation.captured_returns spaces.sorts spaces.terms spaces.cache
    theory.sorts.reverse theory.terms.reverse (uniqueKeys_reverse ready.uniqueSorts) (uniqueKeys_reverse ready.uniqueTerms)
    ready.separate_sort ready.separate_term declaration before ready.sorts ready.terms
    (by simpa only [ready.term_signature] using ready.cache)
  refine ⟨after, ?_, ready.after_frame frame (by simpa only [ready.term_signature] using cacheAfter), frame⟩
  apply call_from_branch
  rw [axiom_shape]
  let bindings := boundEnvironment spaces (.axiomDecl index declaration)
  let fresh := (theory.theoremSignature index).isNone
  let formed := TheoremDecl.check theory.sortSignature theory.termSignature declaration
  let withFresh := ("admissionFreshResult4", boolean fresh) :: bindings
  let withForm := ("formTheoremResult", boolean formed) :: withFresh
  apply let_returns program bindings withFresh before before after (.var "admissionFreshResult4") _ _ (boolean fresh) _
  · have returned := fresh_captured_returns TheoremInstantiation.declarationValue bindings before spaces.theorems
      theory.theorems.reverse index "theorems" "index" (uniqueKeys_reverse ready.uniqueTheorems) ready.theorems rfl rfl
    simpa only [fresh, Theory.theoremSignature, lookup_reverse theory.theorems ready.uniqueTheorems] using returned
  · simp [SpaceSemantics.matchValue, matchAtom, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program withFresh withForm before after after (.var "formTheoremResult") _ _ (boolean formed) _
    · simpa only [ready.sort_signature, ready.term_signature, formed] using
        formedReturned withFresh "sorts" "terms" "declaration" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withForm, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · exact SortFormation.and_returns withForm after fresh formed "admissionFreshResult4" "formTheoremResult" rfl rfl

/-- Admission passes hypotheses inline; no saved hypothesis vector is assumed. -/
def proofTables {before : State} (spaces : Spaces) (theory : Theory) (values : List Kernel.Preterm)
    (ready : Ready spaces theory before) : Proof.Tables :=
  { terms := spaces.terms
    definitions := spaces.definitions
    theorems := spaces.theorems
    hypotheses := spaces.proofs
    cache := spaces.cache
    entries := theory.terms.reverse
    bodies := theory.definitions.reverse
    declarations := theory.theorems.reverse
    values := values
    storage := .inline
    uniqueTerms := uniqueKeys_reverse ready.uniqueTerms
    uniqueDefinitions := uniqueKeys_reverse ready.uniqueDefinitions
    uniqueTheorems := uniqueKeys_reverse ready.uniqueTheorems
    separateTerms := ready.separate_term
    separateDefinitions := ready.separate_definition
    separateTheorems := ready.separate_theorem
    separateHypotheses := ready.separate_proof }

theorem proof_tables_ready {before : State} (spaces : Spaces) (theory : Theory)
    (values : List Kernel.Preterm) (ready : Ready spaces theory before) :
    Proof.Ready (proofTables spaces theory values ready) before := by
  apply Proof.Ready.of_inline _ before rfl ready.terms ready.definitions ready.theorems
  simpa only [proofTables, ready.term_signature] using ready.cache

private def proofCases := casesOf proofEquation.body
private def proofBody := (proofCases[0]'(by decide)).2
private def proofEnvironment (spaces : Spaces) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : Kernel.ProofWitness) : Subst :=
  [("proof", Proof.witnessValue proof), ("dummies", Support.indicesValue dummies),
    ("valueInput", TheoremInstantiation.declarationValue declaration),
    ("theorems", tableValue spaces.theorems), ("definitions", tableValue spaces.definitions),
    ("terms", tableValue spaces.terms)]
private def proofBoundEnvironment (spaces : Spaces) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : Kernel.ProofWitness) : Subst :=
  [("conclusion", Data.preterm declaration.conclusion),
    ("hypotheses", ListSubstitution.expressionsValue declaration.hypotheses),
    ("context", Data.context declaration.arguments)] ++ proofEnvironment spaces declaration dummies proof

private theorem proof_formals : proofEquation.arguments =
    [.var "terms", .var "definitions", .var "theorems", .var "valueInput", .var "dummies", .var "proof"] := by decide +kernel
private theorem proof_shape : proofEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (proofCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem proof_cases : proofCases =
    [(listValue [.symbol "MM0:Theorem", .var "context", .var "hypotheses", .var "conclusion"], proofBody),
      (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem proof_body_shape : proofBody = .expression [.symbol "let", .var "combined",
    .expression [.symbol "let", .var "dummyContextResult",
      .expression [.symbol "mm0:dummy-context", .var "dummies"],
      .expression [.symbol "mm0:list-append", .var "context", .var "dummyContextResult"]],
    .expression [.symbol "mm0:check-proof", .var "terms", .var "definitions", .var "theorems", .var "combined",
      .var "hypotheses", .var "proof", .var "conclusion"]] := by decide +kernel

def ProofCall (spaces : Spaces) (declaration : TheoremDecl) (dummies : List Nat)
    (proof : Kernel.ProofWitness) (before after : State) (answer : Bool) : Prop :=
  ∀ bindings termsName definitionsName theoremsName declarationName dummiesName proofName,
    applySubst bindings (.var termsName) = tableValue spaces.terms →
    applySubst bindings (.var definitionsName) = tableValue spaces.definitions →
    applySubst bindings (.var theoremsName) = tableValue spaces.theorems →
    applySubst bindings (.var declarationName) = TheoremInstantiation.declarationValue declaration →
    applySubst bindings (.var dummiesName) = Support.indicesValue dummies →
    applySubst bindings (.var proofName) = Proof.witnessValue proof →
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-proof", .var termsName, .var definitionsName, .var theoremsName,
        .var declarationName, .var dummiesName, .var proofName]) after (boolean answer)

theorem proof_captured_returns (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : Kernel.ProofWitness) (before : State) (ready : Ready spaces theory before) :
    ∃ after bound,
      ProofCall spaces declaration dummies proof before after
        (Kernel.ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
          (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  let tables := proofTables spaces theory declaration.hypotheses ready
  let context := Admission.proofContext declaration dummies
  obtain ⟨after, bound, checked, proofReady, frame⟩ := Proof.check_returns tables context proof declaration.conclusion before
    (proof_tables_ready spaces theory declaration.hypotheses ready)
  refine ⟨after, bound, ?_, ready.after_frame frame ?_, frame⟩
  · let answer := Kernel.ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
      context declaration.hypotheses proof declaration.conclusion
    have body : PureReturns program (proofEnvironment spaces declaration dummies proof) before proofEquation.body
        after (boolean answer) := by
      rw [proof_shape]
      let bindings := proofEnvironment spaces declaration dummies proof
      let boundBindings := proofBoundEnvironment spaces declaration dummies proof
      apply case_returns program bindings boundBindings before before after (.var "valueInput")
        (TheoremInstantiation.declarationValue declaration) proofBody _ _ proofCases (read_cases_encoded _)
      · exact variable_returns program bindings before "valueInput"
      · simp [proof_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, TheoremInstantiation.declarationValue,
          listValue, boundBindings, bindings, proofBoundEnvironment, proofEnvironment, Subst.lookup]
      · rw [proof_body_shape]
        let combined := ("combined", Data.context context) :: boundBindings
        apply let_returns program boundBindings combined before before after (.var "combined") _ _ (Data.context context) _
        · let withDummies := ("dummyContextResult", Data.context (dummies.map Kernel.Binder.bound)) :: boundBindings
          apply let_returns program boundBindings withDummies before before before (.var "dummyContextResult") _ _
            (Data.context (dummies.map Kernel.Binder.bound)) _
          · exact BodyFormation.DummyContext.captured_returns boundBindings before dummies "dummies" rfl
          · simp [SpaceSemantics.matchValue, matchAtom, withDummies, boundBindings,
              proofBoundEnvironment, proofEnvironment, Subst.lookup]
          · simpa [context, Admission.proofContext, Data.context] using
              ListAccess.append_captured_returns withDummies before (declaration.arguments.map Data.binder)
                ((dummies.map Kernel.Binder.bound).map Data.binder) "context" "dummyContextResult" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, combined, boundBindings,
            proofBoundEnvironment, proofEnvironment, Subst.lookup]
        · have returned := checked combined "terms" "definitions" "theorems" "combined" "hypotheses" "proof" "conclusion"
            rfl rfl rfl rfl (by simp [tables, proofTables, Proof.hypothesesValue, Hypothesis.value,
              ListSubstitution.expressionsValue, combined, boundBindings,
              proofBoundEnvironment, proofEnvironment, applySubst, Subst.lookup]) rfl rfl
          simpa only [tables, proofTables, ready.term_signature, ready.definition_signature,
            ready.theorem_signature, answer] using returned
    intro bindings termsName definitionsName theoremsName declarationName dummiesName proofName ct cd cth cc cdu cp
    apply authored_variable_call_returns program bindings (proofEnvironment spaces declaration dummies proof)
      before after "mm0:admission-proof" [termsName, definitionsName, theoremsName, declarationName, dummiesName, proofName]
      proofEquation.body _ (by decide) (by decide) (by decide) _ body (by decide)
    rw [clauses_use_only_the_named_equations, proof_unique]
    simp [ct, cd, cth, cc, cdu, cp, proof_formals, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, proofEnvironment]
  · simpa only [tables, proofTables, ready.term_signature] using proofReady.cache

private theorem theorem_shape (index : Nat) (declaration : TheoremDecl) (dummies : List Nat)
    (proof : Kernel.ProofWitness) : branch (.theoremDecl index declaration dummies proof) =
    .expression [.symbol "let", .var "formAndResult3",
      .expression [.symbol "let", .var "formAndResult4",
        .expression [.symbol "let", .var "admissionFreshResult5",
          .expression [.symbol "mm0:admission-fresh", .var "theorems", .var "index"],
          .expression [.symbol "let", .var "formTheoremResult2",
            .expression [.symbol "mm0:form-theorem", .var "sorts", .var "terms", .var "declaration"],
            .expression [.symbol "mm0:form-and", .var "admissionFreshResult5", .var "formTheoremResult2"]]],
        .expression [.symbol "let", .var "formDummiesResult",
          .expression [.symbol "mm0:form-dummies", .var "sorts", .var "dummies"],
          .expression [.symbol "mm0:form-and", .var "formAndResult4", .var "formDummiesResult"]]],
      .expression [.symbol "let", .var "admissionProofResult",
        .expression [.symbol "mm0:admission-proof", .var "terms", .var "definitions", .var "theorems",
          .var "declaration", .var "dummies", .var "proof"],
        .expression [.symbol "mm0:form-and", .var "formAndResult3", .var "admissionProofResult"]]] := by
  change theoremBody = _
  decide +kernel

/-- All theorem checks execute in source order, even after a false freshness,
formation or dummy-sort result. Only the scoped inference cache may change. -/
theorem theorem_captured_returns (spaces : Spaces) (theory : Theory) (index : Nat) (declaration : TheoremDecl)
    (dummies : List Nat) (proof : Kernel.ProofWitness) (before : State) (ready : Ready spaces theory before) :
    ∃ after bound,
      Call spaces (.theoremDecl index declaration dummies proof) before after
        (Admission.check theory (.theoremDecl index declaration dummies proof)) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨middle, formedReturned, cacheMiddle, formationFrame⟩ := TheoremFormation.captured_returns
    spaces.sorts spaces.terms spaces.cache theory.sorts.reverse theory.terms.reverse
    (uniqueKeys_reverse ready.uniqueSorts) (uniqueKeys_reverse ready.uniqueTerms)
    ready.separate_sort ready.separate_term declaration before ready.sorts ready.terms
    (by simpa only [ready.term_signature] using ready.cache)
  have readyMiddle := ready.after_frame formationFrame (by simpa only [ready.term_signature] using cacheMiddle)
  obtain ⟨after, proofBound, proofReturned, readyAfter, proofFrame⟩ :=
    proof_captured_returns spaces theory declaration dummies proof middle readyMiddle
  let bound := max (max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion)) proofBound
  refine ⟨after, bound, ?_, readyAfter,
    (formationFrame.weaken (Nat.le_max_left _ _)).trans (proofFrame.weaken (Nat.le_max_right _ _))⟩
  apply call_from_branch
  rw [theorem_shape]
  let bindings := boundEnvironment spaces (.theoremDecl index declaration dummies proof)
  let fresh := (theory.theoremSignature index).isNone
  let formed := TheoremDecl.check theory.sortSignature theory.termSignature declaration
  let dummyAllowed := Kernel.Definition.checkDummySorts theory.sortSignature dummies
  let proofAccepted := Kernel.ProofWitness.check theory.termSignature theory.definitionSignature theory.theoremSignature
    (Admission.proofContext declaration dummies) declaration.hypotheses proof declaration.conclusion
  let withPrefix := ("formAndResult3", boolean ((fresh && formed) && dummyAllowed)) :: bindings
  let withProof := ("admissionProofResult", boolean proofAccepted) :: withPrefix
  apply let_returns program bindings withPrefix before middle after (.var "formAndResult3") _ _
    (boolean ((fresh && formed) && dummyAllowed)) _
  · let withFormation := ("formAndResult4", boolean (fresh && formed)) :: bindings
    let withDummies := ("formDummiesResult", boolean dummyAllowed) :: withFormation
    apply let_returns program bindings withFormation before middle middle (.var "formAndResult4") _ _
      (boolean (fresh && formed)) _
    · let withFresh := ("admissionFreshResult5", boolean fresh) :: bindings
      let withForm := ("formTheoremResult2", boolean formed) :: withFresh
      apply let_returns program bindings withFresh before before middle (.var "admissionFreshResult5") _ _ (boolean fresh) _
      · have returned := fresh_captured_returns TheoremInstantiation.declarationValue bindings before spaces.theorems
          theory.theorems.reverse index "theorems" "index" (uniqueKeys_reverse ready.uniqueTheorems) ready.theorems rfl rfl
        simpa only [fresh, Theory.theoremSignature, lookup_reverse theory.theorems ready.uniqueTheorems] using returned
      · simp [SpaceSemantics.matchValue, matchAtom, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
      · apply let_returns program withFresh withForm before middle middle (.var "formTheoremResult2") _ _ (boolean formed) _
        · simpa only [ready.sort_signature, ready.term_signature, formed] using
            formedReturned withFresh "sorts" "terms" "declaration" rfl rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, withForm, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
        · exact SortFormation.and_returns withForm middle fresh formed "admissionFreshResult5" "formTheoremResult2" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withFormation, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · apply let_returns program withFormation withDummies middle middle middle (.var "formDummiesResult") _ _ (boolean dummyAllowed) _
      · have returned := DummyFormation.captured_returns withFormation middle spaces.sorts theory.sorts.reverse dummies
          "sorts" "dummies" (uniqueKeys_reverse ready.uniqueSorts) readyMiddle.sorts rfl rfl
        simpa only [ready.sort_signature, dummyAllowed] using returned
      · simp [SpaceSemantics.matchValue, matchAtom, withDummies, withFormation, bindings, boundEnvironment, fields, environment, Subst.lookup]
      · exact SortFormation.and_returns withDummies middle (fresh && formed) dummyAllowed "formAndResult4" "formDummiesResult" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, withPrefix, bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program withPrefix withProof middle after after (.var "admissionProofResult") _ _ (boolean proofAccepted) _
    · exact proofReturned withPrefix "terms" "definitions" "theorems" "declaration" "dummies" "proof" rfl rfl rfl rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withProof, withPrefix, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · exact SortFormation.and_returns withProof after ((fresh && formed) && dummyAllowed) proofAccepted
        "formAndResult3" "admissionProofResult" rfl rfl

private theorem definition_shape (index : Nat) (declaration : TermDecl) (body : Kernel.Definition.Body) :
    branch (.definition index declaration body) =
    .expression [.symbol "let", .var "formAndResult",
      .expression [.symbol "let", .var "formAndResult2",
        .expression [.symbol "let", .var "admissionFreshResult2",
          .expression [.symbol "mm0:admission-fresh", .var "terms", .var "index"],
          .expression [.symbol "let", .var "admissionFreshResult3",
            .expression [.symbol "mm0:admission-fresh", .var "definitions", .var "index"],
            .expression [.symbol "mm0:form-and", .var "admissionFreshResult2", .var "admissionFreshResult3"]]],
        .expression [.symbol "let", .var "formTermResult2",
          .expression [.symbol "mm0:form-term", .var "sorts", .var "declaration"],
          .expression [.symbol "mm0:form-and", .var "formAndResult2", .var "formTermResult2"]]],
      .expression [.symbol "let", .var "formBodyResult",
        .expression [.symbol "mm0:form-body", .var "sorts", .var "terms", .var "declaration", .var "body"],
        .expression [.symbol "mm0:form-and", .var "formAndResult", .var "formBodyResult"]]] := by
  change definitionBody = _
  decide +kernel

theorem definition_captured_returns (spaces : Spaces) (theory : Theory) (index : Nat) (declaration : TermDecl)
    (body : Kernel.Definition.Body) (before : State) (ready : Ready spaces theory before) :
    ∃ after,
      Call spaces (.definition index declaration body) before after (Admission.check theory (.definition index declaration body)) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms)
        (sizeOf body.expression + 1) before after := by
  obtain ⟨after, bodyReturned, cacheAfter, frame⟩ := BodyFormation.returns spaces.sorts spaces.terms spaces.cache
    theory.sorts.reverse theory.terms.reverse declaration body before
    (uniqueKeys_reverse ready.uniqueSorts) (uniqueKeys_reverse ready.uniqueTerms) ready.separate_term ready.sorts ready.terms
    (by simpa only [ready.term_signature] using ready.cache)
  refine ⟨after, ?_, ready.after_frame frame (by simpa only [ready.term_signature] using cacheAfter), frame⟩
  apply call_from_branch
  rw [definition_shape]
  let bindings := boundEnvironment spaces (.definition index declaration body)
  let freshTerm := (theory.termSignature index).isNone
  let freshDefinition := (theory.definitionSignature index).isNone
  let formed := TermDecl.check theory.sortSignature declaration
  let validBody := Kernel.Definition.checkBody theory.sortSignature theory.termSignature declaration body
  let withPrefix := ("formAndResult", boolean ((freshTerm && freshDefinition) && formed)) :: bindings
  let withBody := ("formBodyResult", boolean validBody) :: withPrefix
  apply let_returns program bindings withPrefix before before after (.var "formAndResult") _ _
    (boolean ((freshTerm && freshDefinition) && formed)) _
  · let withFresh := ("formAndResult2", boolean (freshTerm && freshDefinition)) :: bindings
    let withForm := ("formTermResult2", boolean formed) :: withFresh
    apply let_returns program bindings withFresh before before before (.var "formAndResult2") _ _
      (boolean (freshTerm && freshDefinition)) _
    · let withTerm := ("admissionFreshResult2", boolean freshTerm) :: bindings
      let withDefinition := ("admissionFreshResult3", boolean freshDefinition) :: withTerm
      apply let_returns program bindings withTerm before before before (.var "admissionFreshResult2") _ _ (boolean freshTerm) _
      · have returned := fresh_captured_returns Data.declaration bindings before spaces.terms theory.terms.reverse index
          "terms" "index" (uniqueKeys_reverse ready.uniqueTerms) ready.terms rfl rfl
        simpa only [freshTerm, Theory.termSignature, lookup_reverse theory.terms ready.uniqueTerms] using returned
      · simp [SpaceSemantics.matchValue, matchAtom, withTerm, bindings, boundEnvironment, fields, environment, Subst.lookup]
      · apply let_returns program withTerm withDefinition before before before (.var "admissionFreshResult3") _ _
          (boolean freshDefinition) _
        · have returned := fresh_captured_returns Unfolding.bodyValue withTerm before spaces.definitions
            theory.definitions.reverse index "definitions" "index" (uniqueKeys_reverse ready.uniqueDefinitions) ready.definitions rfl rfl
          simpa only [freshDefinition, Theory.definitionSignature, lookup_reverse theory.definitions ready.uniqueDefinitions] using returned
        · simp [SpaceSemantics.matchValue, matchAtom, withDefinition, withTerm, bindings, boundEnvironment, fields, environment, Subst.lookup]
        · exact SortFormation.and_returns withDefinition before freshTerm freshDefinition
            "admissionFreshResult2" "admissionFreshResult3" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · apply let_returns program withFresh withForm before before before (.var "formTermResult2") _ _ (boolean formed) _
      · have returned := TermFormation.captured_returns withFresh before spaces.sorts theory.sorts.reverse declaration
          "sorts" "declaration" (uniqueKeys_reverse ready.uniqueSorts) ready.sorts rfl rfl
        simpa only [ready.sort_signature, formed] using returned
      · simp [SpaceSemantics.matchValue, matchAtom, withForm, withFresh, bindings, boundEnvironment, fields, environment, Subst.lookup]
      · exact SortFormation.and_returns withForm before (freshTerm && freshDefinition) formed
          "formAndResult2" "formTermResult2" rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, withPrefix, bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program withPrefix withBody before after after (.var "formBodyResult") _ _ (boolean validBody) _
    · simpa only [ready.sort_signature, ready.term_signature, validBody] using
        bodyReturned withPrefix "sorts" "terms" "declaration" "body" rfl rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withBody, withPrefix, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · exact SortFormation.and_returns withBody after ((freshTerm && freshDefinition) && formed) validBody
        "formAndResult" "formBodyResult" rfl rfl

/-- Correspondence for every supplied admission constructor. The kernel's
Boolean judgment is independent of the source equations quoted above. -/
theorem captured_returns (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    ∃ after bound,
      Call spaces admission before after (Admission.check theory admission) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  cases admission with
  | sort index info =>
      exact ⟨before, 0, sort_captured_returns spaces theory index info before ready,
        ready, InferenceCache.Frame.refl _ _ _ _⟩
  | term index declaration =>
      exact ⟨before, 0, term_captured_returns spaces theory index declaration before ready,
        ready, InferenceCache.Frame.refl _ _ _ _⟩
  | definition index declaration body =>
      obtain ⟨after, computed, readyAfter, frame⟩ := definition_captured_returns spaces theory index declaration body before ready
      exact ⟨after, sizeOf body.expression + 1, computed, readyAfter, frame⟩
  | axiomDecl index declaration =>
      obtain ⟨after, computed, readyAfter, frame⟩ := axiom_captured_returns spaces theory index declaration before ready
      exact ⟨after, max (sizeOf declaration.hypotheses) (sizeOf declaration.conclusion), computed, readyAfter, frame⟩
  | theoremDecl index declaration dummies proof =>
      exact theorem_captured_returns spaces theory index declaration dummies proof before ready

def requestConfiguration (state : State) (spaces : Spaces) (admission : Admission) : Configuration :=
  { state, control := .evaluate (environment spaces admission)
      (.expression [.symbol "mm0:admission-check", .var "valueInput", .var "valueInputValue"]) }

theorem sufficient_fuel (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    ∃ after bound fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces admission) =
        .complete after [boolean (Admission.check theory admission)] [] []) ∧
      Ready spaces theory after ∧ InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨after, bound, returned, readyAfter, frame⟩ := captured_returns spaces theory admission before ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment spaces admission) before after _ _
    (returned _ "valueInput" "valueInputValue" rfl rfl)
  exact ⟨after, bound, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, readyAfter, frame⟩

theorem result_iff_source_returns (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) (answer : Bool) :
    Admission.check theory admission = answer ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) = .complete after [boolean answer] [] [] := by
  obtain ⟨reference, _, referenceFuel, completed, _, _⟩ := sufficient_fuel spaces theory admission before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro same
    exact ⟨reference, referenceFuel, by simpa only [same] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have values := List.singleton_inj.mp same.2.1
    simpa [boolean] using values

theorem authorized_iff_source_accepts (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Admission.Authorized theory admission ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) = .complete after [boolean true] [] [] :=
  (Admission.check_iff theory admission).symm.trans (result_iff_source_returns spaces theory admission before ready true)

theorem refused_iff_source_refuses (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    (¬ Admission.Authorized theory admission) ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces admission) = .complete after [boolean false] [] [] := by
  rw [← Admission.check_iff]
  exact Bool.eq_false_iff.symm.trans (result_iff_source_returns spaces theory admission before ready false)

theorem authorized_iff_gslt_path (spaces : Spaces) (kernelTheory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces kernelTheory before) :
    Admission.Authorized kernelTheory admission ↔
      ∃ after, (theory program).MultiStep (requestConfiguration before spaces admission) (finished after [boolean true] [] []) := by
  rw [authorized_iff_source_accepts spaces kernelTheory admission before ready]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem authorized_iff_judgment (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) :
    Admission.Authorized theory admission ↔
      ∃ after, DeclarativeSpec.Runs program (requestConfiguration before spaces admission)
        (.complete after [boolean true] [] []) := by
  rw [authorized_iff_source_accepts spaces theory admission before ready]
  exact exists_congr fun after => completed_run_iff_derivation program _ after _ [] []

theorem completed_frame (spaces : Spaces) (theory : Theory) (admission : Admission)
    (before : State) (ready : Ready spaces theory before) (after : State) (fuel : Nat) (answers : List Atom)
    (returned : run program fuel (requestConfiguration before spaces admission) = .complete after answers [] []) :
    Ready spaces theory after ∧ ∃ bound, InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after := by
  obtain ⟨reference, bound, referenceFuel, completed, readyReference, frame⟩ := sufficient_fuel spaces theory admission before ready
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
  rw [← same.1]
  exact ⟨readyReference, bound, frame⟩

namespace Controls

private def spaces : Spaces :=
  ⟨.privateSpace 0, .privateSpace 1, .privateSpace 2, .privateSpace 3, .privateSpace 4, .privateSpace 5⟩
private def info : SortInfo := { provable := true }
private def declarations : Theory := { sorts := [(0, info)] }
private def initial : State :=
  { core := []
    next := 6
    spaces := fun index => if index = 2 then SortFormation.rows declarations.sorts.reverse else []
    cells := fun name => if name = InferenceCache.cell then some (Effects.handleValue spaces.cache) else none }
private def declaration : TheoremDecl :=
  { arguments := [.bound 0], hypotheses := [.var 0], conclusion := .var 0 }

private theorem ready : Ready spaces declarations initial := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide⟩, ?_⟩
  · simp [initial, spaces, NamedSpaces.Store.read]
  · simp [initial, spaces, declarations, declarationRows, Store.rows, NamedSpaces.Store.read]
  · simp [initial, spaces, declarations, Unfolding.definitionRows, Store.rows, NamedSpaces.Store.read]
  · simp [initial, spaces, declarations, Proof.theoremRows, Store.rows, NamedSpaces.Store.read]
  · intro key; by_cases same : 0 = key <;> simp [declarations, same]
  · intro key; simp [declarations]
  · intro key; simp [declarations]
  · intro key; simp [declarations]
  · refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;>
      simp [initial, spaces, NamedSpaces.Store.read]

/-- Start permits an independently fresh sort identifier in the actual checker. -/
theorem empty_sort_source_accepts (before : State) (specification : Atom) (index : Nat) (sort : SortInfo) :
    ∃ after fuel, run program fuel
      (requestConfiguration (SessionInitialization.startState before specification)
        (SessionInitialization.allocatedSpaces before) (.sort index sort)) = .complete after [boolean true] [] [] := by
  apply (result_iff_source_returns _ ({} : Theory) _ _ (start_ready before specification) true).mp
  rfl

/-- Reusing a sort identifier is a completed refusal, not fuel exhaustion. -/
theorem duplicate_sort_source_refuses :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces (.sort 0 info)) =
      .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns spaces declarations _ initial ready false).mp
  decide +kernel

/-- The admission path consumes inline hypotheses through the same proof recursion. -/
theorem inline_hypothesis_source_accepts :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces (.theoremDecl 7 declaration [] (.hyp 0))) =
      .complete after [boolean true] [] [] := by
  apply (result_iff_source_returns spaces declarations _ initial ready true).mp
  decide +kernel

/-- A missing inline hypothesis cannot be repaired by valid theorem formation. -/
theorem missing_inline_hypothesis_source_refuses :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces (.theoremDecl 7 declaration [] (.hyp 1))) =
      .complete after [boolean false] [] [] := by
  apply (result_iff_source_returns spaces declarations _ initial ready false).mp
  decide +kernel

end Controls

end Mettapedia.Languages.MM0.MeTTa.AdmissionChecks
