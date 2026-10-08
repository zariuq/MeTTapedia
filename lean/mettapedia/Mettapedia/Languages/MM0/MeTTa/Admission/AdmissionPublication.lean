import Mettapedia.Languages.MM0.MeTTa.Admission.AdmissionChecks

/-!
# Publication in the retained MM0 admission source

Publication executes the five retained branches and records their actual
native insertions. Rows appear in chronological order, the reverse of the
independent kernel's front-inserted association lists. Freshness is supplied
by a separate authorization proof; the publication function itself permits
duplicates. Cells, the proof space and the preceding cache scope are preserved.
A new term signature obtains its own cache scope at the next driver reset.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.AdmissionPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Kernel (Theory Admission SortInfo TermDecl TheoremDecl)
open Store (natural)
open ListAccess (listValue optionValue)
open TableAccess (tableValue)
open SessionInitialization (Spaces theoryValue)
open AdmissionChecks (admissionValue TableReady Ready UniqueKeys)

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 121)[120]'(by decide +kernel)

private def cases : SpaceSemantics.Cases :=
  match equation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def branch : Admission → Atom
  | .sort _ _ => (cases[0]'(by decide)).2
  | .term _ _ => (cases[1]'(by decide)).2
  | .definition _ _ _ => (cases[2]'(by decide)).2
  | .axiomDecl _ _ => (cases[3]'(by decide)).2
  | .theoremDecl _ _ _ _ => (cases[4]'(by decide)).2

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

private theorem unique :
    program.equations.filter (fun row => row.head == "mm0:admission-publish") = [equation] := by decide +kernel

private theorem formals : equation.arguments = [.var "valueInput", .var "valueInputValue"] := by decide +kernel

private theorem shape : equation.body = .expression [.symbol "case",
    .expression [.var "valueInput", .var "valueInputValue"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem cases_shape : cases = [
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitSort", .var "index", .var "info"]], branch (.sort 0 {})),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitTerm", .var "index", .var "declaration"]], branch (.term 0 ⟨[], 0, ∅⟩)),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitDefinition", .var "index", .var "declaration", .var "body"]],
      branch (.definition 0 ⟨[], 0, ∅⟩ ⟨[], .var 0⟩)),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitAxiom", .var "index", .var "declaration"]], branch (.axiomDecl 0 ⟨[], [], .var 0⟩)),
    (.expression [listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "theorems"],
      listValue [.symbol "MM0:AdmitTheorem", .var "index", .var "declaration", .var "dummies", .var "proof"]],
      branch (.theoremDecl 0 ⟨[], [], .var 0⟩ [] (.hyp 0))),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide +kernel

private theorem selected_branch (spaces : Spaces) (admission : Admission) :
    SpaceSemantics.selectCase (environment spaces admission)
      (.expression [theoryValue spaces, admissionValue admission]) cases =
      some (boundEnvironment spaces admission, branch admission) := by
  cases admission <;>
    simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment,
      boundEnvironment, fields, admissionValue, theoryValue, listValue] <;> rfl

private theorem sort_shape (index : Nat) (info : SortInfo) :
    branch (.sort index info) =
      .expression [.symbol "let", .var "items", .expression [.symbol "let", .var "extended", .expression [.symbol "let", .var "items2", .expression [.symbol "MM0:L", .expression [.var "index", .var "info"]], .expression [.symbol "mm0:list-cons", .var "items2", .var "sorts"]], .expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var "extended", .var "terms", .var "definitions", .var "theorems"]]], .expression [.symbol "Some", .var "items"]] := by simp only [branch]; decide +kernel

private theorem term_shape (index : Nat) (declaration : TermDecl) :
    branch (.term index declaration) =
      .expression [.symbol "let", .var "items3", .expression [.symbol "let", .var "extended2", .expression [.symbol "let", .var "items4", .expression [.symbol "MM0:L", .expression [.var "index", .var "declaration"]], .expression [.symbol "mm0:list-cons", .var "items4", .var "terms"]], .expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var "sorts", .var "extended2", .var "definitions", .var "theorems"]]], .expression [.symbol "Some", .var "items3"]] := by simp only [branch]; decide +kernel

private theorem definition_shape (index : Nat) (declaration : TermDecl) (body : Kernel.Definition.Body) :
    branch (.definition index declaration body) =
      .expression [.symbol "let", .var "items5", .expression [.symbol "let", .var "extended3", .expression [.symbol "let", .var "items6", .expression [.symbol "MM0:L", .expression [.var "index", .var "declaration"]], .expression [.symbol "mm0:list-cons", .var "items6", .var "terms"]], .expression [.symbol "let", .var "extended4", .expression [.symbol "let", .var "items7", .expression [.symbol "MM0:L", .expression [.var "index", .var "body"]], .expression [.symbol "mm0:list-cons", .var "items7", .var "definitions"]], .expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var "sorts", .var "extended3", .var "extended4", .var "theorems"]]]], .expression [.symbol "Some", .var "items5"]] := by simp only [branch]; decide +kernel

private theorem axiom_shape (index : Nat) (declaration : TheoremDecl) :
    branch (.axiomDecl index declaration) =
      .expression [.symbol "let", .var "items8", .expression [.symbol "let", .var "extended5", .expression [.symbol "let", .var "items9", .expression [.symbol "MM0:L", .expression [.var "index", .var "declaration"]], .expression [.symbol "mm0:list-cons", .var "items9", .var "theorems"]], .expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "extended5"]]], .expression [.symbol "Some", .var "items8"]] := by simp only [branch]; decide +kernel

private theorem theorem_shape (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : Kernel.ProofWitness) :
    branch (.theoremDecl index declaration dummies proof) =
      .expression [.symbol "let", .var "items10", .expression [.symbol "let", .var "extended6", .expression [.symbol "let", .var "items11", .expression [.symbol "MM0:L", .expression [.var "index", .var "declaration"]], .expression [.symbol "mm0:list-cons", .var "items11", .var "theorems"]], .expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "definitions", .var "extended6"]]], .expression [.symbol "Some", .var "items10"]] := by simp only [branch]; decide +kernel

/-- The actual native insertion trace. It contains no validity or freshness
condition and introduces no alternative store operation. -/
def Writes (spaces : Spaces) (admission : Admission) (before after : State) : Prop :=
  match admission with
  | .sort index info => Effects.insert before spaces.sorts (Store.row (index, SortFormation.sortValue info)) = some after
  | .term index declaration => Effects.insert before spaces.terms (Store.row (index, Data.declaration declaration)) = some after
  | .definition index declaration body =>
      ∃ middle, Effects.insert before spaces.terms (Store.row (index, Data.declaration declaration)) = some middle ∧
        Effects.insert middle spaces.definitions (Store.row (index, Unfolding.bodyValue body)) = some after
  | .axiomDecl index declaration =>
      Effects.insert before spaces.theorems (Store.row (index, TheoremInstantiation.declarationValue declaration)) = some after
  | .theoremDecl index declaration _ _ =>
      Effects.insert before spaces.theorems (Store.row (index, TheoremInstantiation.declarationValue declaration)) = some after

private theorem lookup_cons_ne (bindings : Subst) (key name : String) (value : Atom)
    (different : key ≠ name) :
    Subst.lookup ((key, value) :: bindings) name = Subst.lookup bindings name := by
  unfold Subst.lookup
  simp only [List.find?_cons]
  rw [beq_eq_false_iff_ne.mpr different]

private theorem capture_cons_ne (bindings : Subst) (key name : String) (value : Atom)
    (different : key ≠ name) :
    applySubst ((key, value) :: bindings) (.var name) = applySubst bindings (.var name) := by
  simp only [applySubst, lookup_cons_ne bindings key name value different]

private theorem match_fresh (bindings : Subst) (name : String) (value : Atom)
    (fresh : Subst.lookup bindings name = none) :
    SpaceSemantics.matchValue bindings (.var name) value = some ((name, value) :: bindings) := by
  simp [SpaceSemantics.matchValue, matchAtom, fresh]

private theorem row_constructor_returns (bindings : Subst) (state : State)
    (index : Nat) (payload : Atom) (payloadName : String)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (payloadCaptured : applySubst bindings (.var payloadName) = payload) :
    PureReturns program bindings state
      (.expression [.symbol "MM0:L", .expression [.var "index", .var payloadName]]) state
      (listValue [natural index, payload]) := by
  apply unary_constructor_of_returns program bindings state state "MM0:L" _ _
    list_is_data_constructor (by decide)
  simpa [indexCaptured, payloadCaptured, listValue] using tuple_variables_return program bindings state ["index", payloadName]

private theorem row_let_returns (bindings : Subst) (before after : State)
    (handle : Handle) (index : Nat) (payload : Atom) (payloadName tableName rowName : String)
    (inserted : Effects.insert before handle (Store.row (index, payload)) = some after)
    (fresh : Subst.lookup bindings rowName = none) (separate : rowName ≠ tableName)
    (indexCaptured : applySubst bindings (.var "index") = natural index)
    (payloadCaptured : applySubst bindings (.var payloadName) = payload)
    (tableCaptured : applySubst bindings (.var tableName) = tableValue handle) :
    PureReturns program bindings before
      (.expression [.symbol "let", .var rowName,
        .expression [.symbol "MM0:L", .expression [.var "index", .var payloadName]],
        .expression [.symbol "mm0:list-cons", .var rowName, .var tableName]]) after (tableValue handle) := by
  let bound := (rowName, listValue [natural index, payload]) :: bindings
  apply let_returns program bindings bound before before after (.var rowName) _ _ _ _
    (row_constructor_returns bindings before index payload payloadName indexCaptured payloadCaptured)
    (match_fresh bindings rowName _ fresh)
  apply TableAccess.publish_captured_returns bound before after handle index payload rowName tableName inserted
  · simp [bound, applySubst, Subst.lookup]
  · rw [capture_cons_ne bindings rowName tableName _ separate]
    exact tableCaptured

private theorem theory_constructor_returns (bindings : Subst) (state : State) (spaces : Spaces)
    (sortName termName definitionName theoremName : String)
    (sortCaptured : applySubst bindings (.var sortName) = tableValue spaces.sorts)
    (termCaptured : applySubst bindings (.var termName) = tableValue spaces.terms)
    (definitionCaptured : applySubst bindings (.var definitionName) = tableValue spaces.definitions)
    (theoremCaptured : applySubst bindings (.var theoremName) = tableValue spaces.theorems) :
    PureReturns program bindings state
      (.expression [.symbol "MM0:L", .expression [.symbol "MM0:Theory", .var sortName,
        .var termName, .var definitionName, .var theoremName]]) state (theoryValue spaces) := by
  apply unary_constructor_of_returns program bindings state state "MM0:L" _ _
    list_is_data_constructor (by decide)
  simpa [theoryValue, listValue, sortCaptured, termCaptured, definitionCaptured, theoremCaptured] using
    constructor_variables_return program bindings state "MM0:Theory"
      [sortName, termName, definitionName, theoremName] (by decide +kernel) (by decide)

private theorem some_let_returns (bindings : Subst) (before after : State)
    (name : String) (expression value : Atom)
    (fresh : Subst.lookup bindings name = none)
    (computed : PureReturns program bindings before expression after value) :
    PureReturns program bindings before (.expression [.symbol "let", .var name, expression,
      .expression [.symbol "Some", .var name]]) after (optionValue (some value)) := by
  let bound := (name, value) :: bindings
  apply let_returns program bindings bound before after after (.var name) _ _ value _ computed
    (match_fresh bindings name value fresh)
  simpa [bound, applySubst, Subst.lookup, optionValue] using
    unary_constructor_returns program bound after "Some" name some_is_data_constructor (by decide)

private theorem sort_branch_returns (spaces : Spaces) (index : Nat) (info : SortInfo)
    (before after : State) (written : Writes spaces (.sort index info) before after) :
    PureReturns program (boundEnvironment spaces (.sort index info)) before (branch (.sort index info)) after
      (optionValue (some (theoryValue spaces))) := by
  let bindings := boundEnvironment spaces (.sort index info)
  change PureReturns program bindings before (branch (.sort index info)) after _
  rw [sort_shape]
  apply some_let_returns bindings before after "items" _ (theoryValue spaces)
  · simp [bindings, boundEnvironment, fields, environment, Subst.lookup]
  · let extended := ("extended", tableValue spaces.sorts) :: bindings
    apply let_returns program bindings extended before after after (.var "extended") _ _ (tableValue spaces.sorts) _
    · apply row_let_returns bindings before after spaces.sorts index (SortFormation.sortValue info)
        "info" "sorts" "items2"
        written (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
      all_goals simp [bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
    · exact match_fresh bindings "extended" _ (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
    · apply theory_constructor_returns extended after spaces "extended" "terms" "definitions" "theorems"
      all_goals simp [extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]

private theorem term_branch_returns (spaces : Spaces) (index : Nat) (declaration : TermDecl)
    (before after : State) (written : Writes spaces (.term index declaration) before after) :
    PureReturns program (boundEnvironment spaces (.term index declaration)) before (branch (.term index declaration)) after
      (optionValue (some (theoryValue spaces))) := by
  let bindings := boundEnvironment spaces (.term index declaration)
  change PureReturns program bindings before (branch (.term index declaration)) after _
  rw [term_shape]
  apply some_let_returns bindings before after "items3" _ (theoryValue spaces)
  · simp [bindings, boundEnvironment, fields, environment, Subst.lookup]
  · let extended := ("extended2", tableValue spaces.terms) :: bindings
    apply let_returns program bindings extended before after after (.var "extended2") _ _ (tableValue spaces.terms) _
    · apply row_let_returns bindings before after spaces.terms index (Data.declaration declaration)
        "declaration" "terms" "items4"
        written (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
      all_goals simp [bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
    · exact match_fresh bindings "extended2" _ (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
    · apply theory_constructor_returns extended after spaces "sorts" "extended2" "definitions" "theorems"
      all_goals simp [extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]

private theorem axiom_branch_returns (spaces : Spaces) (index : Nat) (declaration : TheoremDecl)
    (before after : State) (written : Writes spaces (.axiomDecl index declaration) before after) :
    PureReturns program (boundEnvironment spaces (.axiomDecl index declaration)) before (branch (.axiomDecl index declaration)) after
      (optionValue (some (theoryValue spaces))) := by
  let bindings := boundEnvironment spaces (.axiomDecl index declaration)
  change PureReturns program bindings before (branch (.axiomDecl index declaration)) after _
  rw [axiom_shape]
  apply some_let_returns bindings before after "items8" _ (theoryValue spaces)
  · simp [bindings, boundEnvironment, fields, environment, Subst.lookup]
  · let extended := ("extended5", tableValue spaces.theorems) :: bindings
    apply let_returns program bindings extended before after after (.var "extended5") _ _ (tableValue spaces.theorems) _
    · apply row_let_returns bindings before after spaces.theorems index (TheoremInstantiation.declarationValue declaration)
        "declaration" "theorems" "items9"
        written (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
      all_goals simp [bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
    · exact match_fresh bindings "extended5" _ (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
    · apply theory_constructor_returns extended after spaces "sorts" "terms" "definitions" "extended5"
      all_goals simp [extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]

private theorem theorem_branch_returns (spaces : Spaces) (index : Nat) (declaration : TheoremDecl) (dummies : List Nat) (proof : Kernel.ProofWitness)
    (before after : State) (written : Writes spaces (.theoremDecl index declaration dummies proof) before after) :
    PureReturns program (boundEnvironment spaces (.theoremDecl index declaration dummies proof)) before (branch (.theoremDecl index declaration dummies proof)) after
      (optionValue (some (theoryValue spaces))) := by
  let bindings := boundEnvironment spaces (.theoremDecl index declaration dummies proof)
  change PureReturns program bindings before (branch (.theoremDecl index declaration dummies proof)) after _
  rw [theorem_shape]
  apply some_let_returns bindings before after "items10" _ (theoryValue spaces)
  · simp [bindings, boundEnvironment, fields, environment, Subst.lookup]
  · let extended := ("extended6", tableValue spaces.theorems) :: bindings
    apply let_returns program bindings extended before after after (.var "extended6") _ _ (tableValue spaces.theorems) _
    · apply row_let_returns bindings before after spaces.theorems index (TheoremInstantiation.declarationValue declaration)
        "declaration" "theorems" "items11"
        written (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
      all_goals simp [bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
    · exact match_fresh bindings "extended6" _ (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
    · apply theory_constructor_returns extended after spaces "sorts" "terms" "definitions" "extended6"
      all_goals simp [extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]

private theorem definition_branch_returns (spaces : Spaces) (index : Nat) (declaration : TermDecl)
    (body : Kernel.Definition.Body) (before after : State)
    (written : Writes spaces (.definition index declaration body) before after) :
    PureReturns program (boundEnvironment spaces (.definition index declaration body)) before
      (branch (.definition index declaration body)) after (optionValue (some (theoryValue spaces))) := by
  obtain ⟨middle, termWritten, bodyWritten⟩ := written
  let bindings := boundEnvironment spaces (.definition index declaration body)
  let extended := ("extended3", tableValue spaces.terms) :: bindings
  let both := ("extended4", tableValue spaces.definitions) :: extended
  change PureReturns program bindings before (branch (.definition index declaration body)) after _
  rw [definition_shape]
  apply some_let_returns bindings before after "items5" _ (theoryValue spaces)
  · simp [bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program bindings extended before middle after (.var "extended3") _ _
      (tableValue spaces.terms) _
    · apply row_let_returns bindings before middle spaces.terms index (Data.declaration declaration)
        "declaration" "terms" "items6" termWritten
        (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
      all_goals simp [bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
    · exact match_fresh bindings "extended3" _ (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
    · apply let_returns program extended both middle after after (.var "extended4") _ _
        (tableValue spaces.definitions) _
      · apply row_let_returns extended middle after spaces.definitions index (Unfolding.bodyValue body)
          "body" "definitions" "items7" bodyWritten
          (by simp [extended, bindings, boundEnvironment, fields, environment, Subst.lookup]) (by decide)
        all_goals simp [extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]
      · exact match_fresh extended "extended4" _
          (by simp [extended, bindings, boundEnvironment, fields, environment, Subst.lookup])
      · apply theory_constructor_returns both after spaces "sorts" "extended3" "extended4" "theorems"
        all_goals simp [both, extended, bindings, boundEnvironment, fields, environment, applySubst, Subst.lookup]

private theorem body_returns (spaces : Spaces) (admission : Admission) (before after : State)
    (written : Writes spaces admission before after) :
    PureReturns program (environment spaces admission) before equation.body after
      (optionValue (some (theoryValue spaces))) := by
  rw [shape]
  apply case_returns program (environment spaces admission) (boundEnvironment spaces admission)
    before before after (.expression [.var "valueInput", .var "valueInputValue"])
    (.expression [theoryValue spaces, admissionValue admission]) (branch admission) _ _ cases (read_cases_encoded _)
  · simpa [environment, applySubst, Subst.lookup] using tuple_variables_return program (environment spaces admission) before
      ["valueInput", "valueInputValue"]
  · exact selected_branch spaces admission
  · cases admission with
    | sort index info => exact sort_branch_returns spaces index info before after written
    | term index declaration => exact term_branch_returns spaces index declaration before after written
    | definition index declaration body => exact definition_branch_returns spaces index declaration body before after written
    | axiomDecl index declaration => exact axiom_branch_returns spaces index declaration before after written
    | theoremDecl index declaration dummies proof =>
        exact theorem_branch_returns spaces index declaration dummies proof before after written

/-- The source returns the same four table capabilities after its native writes. -/
theorem captured_returns (spaces : Spaces) (admission : Admission) (before after : State)
    (written : Writes spaces admission before after) (bindings : Subst) (theoryName admissionName : String)
    (capturedTheory : applySubst bindings (.var theoryName) = theoryValue spaces)
    (capturedAdmission : applySubst bindings (.var admissionName) = admissionValue admission) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-publish", .var theoryName, .var admissionName]) after
      (optionValue (some (theoryValue spaces))) := by
  apply authored_variable_call_returns program bindings (environment spaces admission) before after
    "mm0:admission-publish" [theoryName, admissionName] equation.body _
    (by decide +kernel) (by decide +kernel) (by decide +kernel) _
    (body_returns spaces admission before after written) (by decide +kernel)
  rw [clauses_use_only_the_named_equations, unique]
  simp [capturedTheory, capturedAdmission, formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

/-- Raw captured arguments also admit constructed table-capability expressions.
This uses the same retained source body and the same physical publication trace. -/
theorem atom_captured_returns (spaces : Spaces) (admission : Admission) (before after : State)
    (written : Writes spaces admission before after) (bindings : Subst) (theoryExpr admissionExpr : Atom)
    (capturedTheory : applySubst bindings theoryExpr = theoryValue spaces)
    (capturedAdmission : applySubst bindings admissionExpr = admissionValue admission) :
    PureReturns program bindings before
      (.expression [.symbol "mm0:admission-publish", theoryExpr, admissionExpr]) after
      (optionValue (some (theoryValue spaces))) := by
  apply raw_call_returns program bindings before after "mm0:admission-publish" [theoryExpr, admissionExpr] _
    (by decide +kernel) _ _ (by decide +kernel)
  · intro index bounded
    have small : index < 2 := by simpa using bounded
    interval_cases index <;> decide +kernel
  · have selected : clauses program "mm0:admission-publish" [theoryValue spaces, admissionValue admission] =
        [.evaluate (environment spaces admission) equation.body] := by
      rw [clauses_use_only_the_named_equations, unique]
      simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
        matchAtom, Subst.lookup, environment]
    simpa [capturedTheory, capturedAdmission] using
      authored_function_arguments_return program bindings (environment spaces admission) before after
        "mm0:admission-publish" [theoryValue spaces, admissionValue admission] 2 equation.body _
        (by decide +kernel) (by decide +kernel) selected (body_returns spaces admission before after written)

private theorem table_separation {spaces : Spaces} {theory : Theory} {before : State}
    (ready : TableReady spaces theory before) :
    spaces.sorts ≠ spaces.terms ∧ spaces.sorts ≠ spaces.definitions ∧ spaces.sorts ≠ spaces.theorems ∧
      spaces.terms ≠ spaces.definitions ∧ spaces.terms ≠ spaces.theorems ∧ spaces.definitions ≠ spaces.theorems := by
  have separated := ready.separate
  simp [Spaces.handles] at separated
  tauto

/-- Each publication completes whenever the four tables are owned. No
logical admission condition is imposed by the store operation. -/
theorem writes_exists (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : TableReady spaces theory before) : ∃ after, Writes spaces admission before after := by
  cases admission with
  | sort index info => exact Effects.insert_exists_of_read_some ready.sorts _
  | term index declaration => exact Effects.insert_exists_of_read_some ready.terms _
  | definition index declaration body =>
      obtain ⟨middle, termWritten⟩ := Effects.insert_exists_of_read_some ready.terms
        (Store.row (index, Data.declaration declaration))
      have allocated : middle.read spaces.definitions = some (Unfolding.definitionRows theory.definitions.reverse) := by
        rw [Effects.insert_read_other termWritten (Ne.symm (table_separation ready).2.2.2.1)]
        exact ready.definitions
      obtain ⟨after, bodyWritten⟩ := Effects.insert_exists_of_read_some allocated
        (Store.row (index, Unfolding.bodyValue body))
      exact ⟨after, middle, termWritten, bodyWritten⟩
  | axiomDecl index declaration => exact Effects.insert_exists_of_read_some ready.theorems _
  | theoremDecl index declaration dummies proof => exact Effects.insert_exists_of_read_some ready.theorems _

/-- A universal source execution, retaining the native effect trace needed
for physical invariants. Authorization remains a separate theorem premise. -/
theorem returns (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : TableReady spaces theory before) :
    ∃ after,
      (∀ bindings theoryName admissionName,
        applySubst bindings (.var theoryName) = theoryValue spaces →
        applySubst bindings (.var admissionName) = admissionValue admission →
        PureReturns program bindings before
          (.expression [.symbol "mm0:admission-publish", .var theoryName, .var admissionName]) after
          (optionValue (some (theoryValue spaces)))) ∧ Writes spaces admission before after := by
  obtain ⟨after, written⟩ := writes_exists spaces theory admission before ready
  exact ⟨after, fun bindings theoryName admissionName capturedTheory capturedAdmission =>
    captured_returns spaces admission before after written bindings theoryName admissionName
      capturedTheory capturedAdmission, written⟩

/-- The table capabilities affected by this declaration's publication. -/
def targets (spaces : Spaces) : Admission → List Handle
  | .sort _ _ => [spaces.sorts]
  | .term _ _ => [spaces.terms]
  | .definition _ _ _ => [spaces.terms, spaces.definitions]
  | .axiomDecl _ _ => [spaces.theorems]
  | .theoremDecl _ _ _ _ => [spaces.theorems]

theorem Writes.cells {spaces : Spaces} {admission : Admission} {before after : State}
    (written : Writes spaces admission before after) : after.cells = before.cells := by
  cases admission with
  | sort index info => exact Effects.insert_preserves_cells written
  | term index declaration => exact Effects.insert_preserves_cells written
  | definition index declaration body =>
      obtain ⟨middle, first, second⟩ := written
      exact (Effects.insert_preserves_cells second).trans (Effects.insert_preserves_cells first)
  | axiomDecl index declaration => exact Effects.insert_preserves_cells written
  | theoremDecl index declaration dummies proof => exact Effects.insert_preserves_cells written

theorem Writes.read_other {spaces : Spaces} {admission : Admission} {before after : State}
    (written : Writes spaces admission before after) (other : Handle)
    (untouched : other ∉ targets spaces admission) : after.read other = before.read other := by
  cases admission with
  | sort index info => exact Effects.insert_read_other written (by simpa [targets] using untouched)
  | term index declaration => exact Effects.insert_read_other written (by simpa [targets] using untouched)
  | definition index declaration body =>
      obtain ⟨middle, first, second⟩ := written
      have separated : other ≠ spaces.terms ∧ other ≠ spaces.definitions := by simpa [targets] using untouched
      exact (Effects.insert_read_other second separated.2).trans (Effects.insert_read_other first separated.1)
  | axiomDecl index declaration => exact Effects.insert_read_other written (by simpa [targets] using untouched)
  | theoremDecl index declaration dummies proof => exact Effects.insert_read_other written (by simpa [targets] using untouched)

private theorem cache_untouched {spaces : Spaces} {theory : Theory} {before : State}
    (ready : TableReady spaces theory before) (admission : Admission) :
    spaces.cache ∉ targets spaces admission := by
  have separate := ready.separate
  simp [Spaces.handles] at separate
  cases admission <;> simp only [targets, List.mem_cons, List.mem_nil_iff, or_false, not_or] <;> tauto

private theorem proofs_untouched {spaces : Spaces} {theory : Theory} {before : State}
    (ready : TableReady spaces theory before) (admission : Admission) :
    spaces.proofs ∉ targets spaces admission := by
  have separate := ready.separate
  simp [Spaces.handles] at separate
  cases admission <;> simp only [targets, List.mem_cons, List.mem_nil_iff, or_false, not_or] <;> tauto

/-- Both non-table spaces and all named cells retain their exact contents. -/
theorem writes_frame (spaces : Spaces) (theory : Theory) (admission : Admission) (before after : State)
    (ready : TableReady spaces theory before) (written : Writes spaces admission before after) :
    after.cells = before.cells ∧ after.read spaces.cache = before.read spaces.cache ∧
      after.read spaces.proofs = before.read spaces.proofs ∧
      (∀ other, other ∉ targets spaces admission → after.read other = before.read other) :=
  ⟨written.cells, written.read_other spaces.cache (cache_untouched ready admission),
    written.read_other spaces.proofs (proofs_untouched ready admission), written.read_other⟩

private theorem insert_rows_back {before after : State} {handle : Handle} {rows : List Atom} {row : Atom}
    (allocated : before.read handle = some rows) (inserted : Effects.insert before handle row = some after) :
    after.read handle = some (rows ++ [row]) := by
  obtain ⟨stored, readBefore, readAfter⟩ := Effects.insert_reads_back inserted
  have same : stored = rows := Option.some.inj (readBefore.symm.trans allocated)
  subst stored
  exact readAfter

/-- The four physical reads agree with the kernel's candidate insertion,
including the two sequential writes of a definition. This requires no fresh
identifier and therefore does not claim unique lookup. -/
theorem writes_contents (spaces : Spaces) (theory : Theory) (admission : Admission) (before after : State)
    (ready : TableReady spaces theory before) (written : Writes spaces admission before after) :
    after.read spaces.sorts = some (SortFormation.rows (admission.insert theory).sorts.reverse) ∧
      after.read spaces.terms = some (TableAccess.declarationRows (admission.insert theory).terms.reverse) ∧
      after.read spaces.definitions = some (Unfolding.definitionRows (admission.insert theory).definitions.reverse) ∧
      after.read spaces.theorems = some (Proof.theoremRows (admission.insert theory).theorems.reverse) := by
  rcases table_separation ready with ⟨sortTerm, sortDefinition, sortTheorem, termDefinition, termTheorem, definitionTheorem⟩
  cases admission with
  | sort index info =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Admission.insert, SortFormation.rows, Store.rows, Store.row] using insert_rows_back ready.sorts written
      · simpa [Admission.insert] using (Effects.insert_read_other written (Ne.symm sortTerm)).trans ready.terms
      · simpa [Admission.insert] using (Effects.insert_read_other written (Ne.symm sortDefinition)).trans ready.definitions
      · simpa [Admission.insert] using (Effects.insert_read_other written (Ne.symm sortTheorem)).trans ready.theorems
  | term index declaration =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Admission.insert] using (Effects.insert_read_other written sortTerm).trans ready.sorts
      · simpa [Admission.insert, TableAccess.declarationRows, Store.rows, Store.row] using insert_rows_back ready.terms written
      · simpa [Admission.insert] using (Effects.insert_read_other written (Ne.symm termDefinition)).trans ready.definitions
      · simpa [Admission.insert] using (Effects.insert_read_other written (Ne.symm termTheorem)).trans ready.theorems
  | definition index declaration body =>
      obtain ⟨middle, first, second⟩ := written
      have bodyBefore : middle.read spaces.definitions = some (Unfolding.definitionRows theory.definitions.reverse) :=
        (Effects.insert_read_other first (Ne.symm termDefinition)).trans ready.definitions
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Admission.insert] using (Effects.insert_read_other second sortDefinition).trans
          ((Effects.insert_read_other first sortTerm).trans ready.sorts)
      · simpa [Admission.insert, TableAccess.declarationRows, Store.rows, Store.row] using
          (Effects.insert_read_other second termDefinition).trans (insert_rows_back ready.terms first)
      · simpa [Admission.insert, Unfolding.definitionRows, Store.rows, Store.row] using insert_rows_back bodyBefore second
      · simpa [Admission.insert] using (Effects.insert_read_other second (Ne.symm definitionTheorem)).trans
          ((Effects.insert_read_other first (Ne.symm termTheorem)).trans ready.theorems)
  | axiomDecl index declaration =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Admission.insert] using (Effects.insert_read_other written sortTheorem).trans ready.sorts
      · simpa [Admission.insert] using (Effects.insert_read_other written termTheorem).trans ready.terms
      · simpa [Admission.insert] using (Effects.insert_read_other written definitionTheorem).trans ready.definitions
      · simpa [Admission.insert, Proof.theoremRows, Store.rows, Store.row] using insert_rows_back ready.theorems written
  | theoremDecl index declaration dummies proof =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Admission.insert] using (Effects.insert_read_other written sortTheorem).trans ready.sorts
      · simpa [Admission.insert] using (Effects.insert_read_other written termTheorem).trans ready.terms
      · simpa [Admission.insert] using (Effects.insert_read_other written definitionTheorem).trans ready.definitions
      · simpa [Admission.insert, Proof.theoremRows, Store.rows, Store.row] using insert_rows_back ready.theorems written

private theorem uniqueKeys_cons {Value : Type} (entries : List (Nat × Value)) (index : Nat) (value : Value)
    (unique : UniqueKeys entries) (fresh : entries.lookup index = none) : UniqueKeys ((index, value) :: entries) := by
  have absent : entries.filter (fun entry => entry.1 = index) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro entry member
    have different := (List.lookup_eq_none_iff.mp fresh) entry member
    have unequal : index ≠ entry.1 := by
      intro same
      simp [same] at different
    simpa only [decide_eq_true_eq] using Ne.symm unequal
  intro key
  by_cases same : index = key
  · subst key
    simp [absent]
  · simpa [same] using unique key

/-- Unique row keys are earned from the separate admission judgment's fresh
identifier premises, rather than assumed of the publication operation. -/
theorem authorized_unique (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : TableReady spaces theory before) (authorized : Admission.Authorized theory admission) :
    UniqueKeys (admission.insert theory).sorts ∧ UniqueKeys (admission.insert theory).terms ∧
      UniqueKeys (admission.insert theory).definitions ∧ UniqueKeys (admission.insert theory).theorems := by
  cases authorized with
  | sort fresh =>
      exact ⟨uniqueKeys_cons theory.sorts _ _ ready.uniqueSorts fresh,
        ready.uniqueTerms, ready.uniqueDefinitions, ready.uniqueTheorems⟩
  | term fresh valid =>
      exact ⟨ready.uniqueSorts, uniqueKeys_cons theory.terms _ _ ready.uniqueTerms fresh,
        ready.uniqueDefinitions, ready.uniqueTheorems⟩
  | definition fresh freshBody valid body =>
      exact ⟨ready.uniqueSorts, uniqueKeys_cons theory.terms _ _ ready.uniqueTerms fresh,
        uniqueKeys_cons theory.definitions _ _ ready.uniqueDefinitions freshBody, ready.uniqueTheorems⟩
  | axiomDecl fresh valid =>
      exact ⟨ready.uniqueSorts, ready.uniqueTerms, ready.uniqueDefinitions,
        uniqueKeys_cons theory.theorems _ _ ready.uniqueTheorems fresh⟩
  | theoremDecl fresh valid dummies proof =>
      exact ⟨ready.uniqueSorts, ready.uniqueTerms, ready.uniqueDefinitions,
        uniqueKeys_cons theory.theorems _ _ ready.uniqueTheorems fresh⟩

/-- Actual native publication establishes the next theory's table invariant
when the preceding theory independently authorizes the declaration. -/
theorem writes_tables (spaces : Spaces) (theory : Theory) (admission : Admission) (before after : State)
    (ready : TableReady spaces theory before) (authorized : Admission.Authorized theory admission)
    (written : Writes spaces admission before after) : TableReady spaces (admission.insert theory) after := by
  rcases writes_contents spaces theory admission before after ready written with ⟨sorts, terms, definitions, theorems⟩
  rcases authorized_unique spaces theory admission before ready authorized with ⟨uniqueSorts, uniqueTerms, uniqueDefinitions, uniqueTheorems⟩
  exact ⟨sorts, terms, definitions, theorems, uniqueSorts, uniqueTerms, uniqueDefinitions, uniqueTheorems, ready.separate⟩

/-- The physical cache and its old frozen-signature observations survive.
This is deliberately not a cache invariant for the extended term signature. -/
theorem writes_frozen_cache (spaces : Spaces) (theory : Theory) (admission : Admission) (before after : State)
    (ready : Ready spaces theory before) (written : Writes spaces admission before after) :
    InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after := by
  obtain ⟨owned, stored, allocated, valid⟩ := ready.cache
  refine ⟨?_, stored, ?_, valid⟩
  · rw [written.cells]; exact owned
  · rw [written.read_other spaces.cache (cache_untouched ready.toTableReady admission)]
    exact allocated

/-- Authorized source publication completes and derives both chronological
row ownership and the exact unchanged cache, proof-space and cell frame. -/
theorem authorized_returns (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : Ready spaces theory before) (authorized : Admission.Authorized theory admission) :
    ∃ after,
      (∀ bindings theoryName admissionName,
        applySubst bindings (.var theoryName) = theoryValue spaces →
        applySubst bindings (.var admissionName) = admissionValue admission →
        PureReturns program bindings before
          (.expression [.symbol "mm0:admission-publish", .var theoryName, .var admissionName]) after
          (optionValue (some (theoryValue spaces)))) ∧
      TableReady spaces (admission.insert theory) after ∧
      InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.cache = before.read spaces.cache ∧
      after.read spaces.proofs = before.read spaces.proofs ∧
      (∀ other, other ∉ targets spaces admission → after.read other = before.read other) := by
  obtain ⟨after, returned, written⟩ := returns spaces theory admission before ready.toTableReady
  exact ⟨after, returned, writes_tables spaces theory admission before after ready.toTableReady authorized written,
    writes_frozen_cache spaces theory admission before after ready written,
    writes_frame spaces theory admission before after ready.toTableReady written⟩

def requestConfiguration (before : State) (spaces : Spaces) (admission : Admission) : Configuration :=
  { state := before, control := .evaluate (environment spaces admission)
      (.expression [.symbol "mm0:admission-publish", .var "valueInput", .var "valueInputValue"]) }

/-- Every typed publication has enough fuel; completion is stable under
increasing the budget and retains the actual native insertion trace. -/
theorem sufficient_fuel (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : TableReady spaces theory before) :
    ∃ after fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces admission) =
        .complete after [optionValue (some (theoryValue spaces))] [] []) ∧
      Writes spaces admission before after := by
  obtain ⟨after, returned, written⟩ := returns spaces theory admission before ready
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment spaces admission)
    before after _ _ (returned _ "valueInput" "valueInputValue" rfl rfl)
  exact ⟨after, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed, written⟩

/-- The publication run is a path of the consolidated PeTTa GSLT. The
separate authorization judgment earns the next physical table invariant. -/
theorem authorized_path_and_tables (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : Ready spaces theory before) (authorized : Admission.Authorized theory admission) :
    ∃ after, (Eval.theory program).MultiStep (requestConfiguration before spaces admission)
        (finished after [optionValue (some (theoryValue spaces))] [] []) ∧
      TableReady spaces (admission.insert theory) after ∧
      InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.cache = before.read spaces.cache ∧
      after.read spaces.proofs = before.read spaces.proofs := by
  obtain ⟨after, returned, tables, frozen, cells, cache, proofs, _⟩ :=
    authorized_returns spaces theory admission before ready authorized
  exact ⟨after, returned _ "valueInput" "valueInputValue" rfl rfl, tables, frozen, cells, cache, proofs⟩

/-- Any observed completed source publication has the same native writes
and observations as the constructed derivation. -/
theorem completed_writes (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : TableReady spaces theory before) (fuel : Nat) (after : State) (answers input output : List Atom)
    (completed : run program fuel (requestConfiguration before spaces admission) =
      .complete after answers input output) :
    answers = [optionValue (some (theoryValue spaces))] ∧ input = [] ∧ output = [] ∧
      Writes spaces admission before after := by
  obtain ⟨referenceAfter, referenceFuel, reference, written⟩ := sufficient_fuel spaces theory admission before ready
  have same := completed_result_unique program fuel referenceFuel _ after referenceAfter answers input output
    [optionValue (some (theoryValue spaces))] [] [] completed (by simpa using reference 0)
  refine ⟨same.2.1, same.2.2.1, same.2.2.2, ?_⟩
  rw [same.1]
  exact written

/-- Driver consumers can derive table readiness and exact cells/cache/proof
frames from an observed completed publication, without supplying its writes. -/
theorem completed_tables_and_frame (spaces : Spaces) (theory : Theory) (admission : Admission) (before : State)
    (ready : Ready spaces theory before) (authorized : Admission.Authorized theory admission)
    (fuel : Nat) (after : State) (answers input output : List Atom)
    (completed : run program fuel (requestConfiguration before spaces admission) =
      .complete after answers input output) :
    answers = [optionValue (some (theoryValue spaces))] ∧ input = [] ∧ output = [] ∧
      TableReady spaces (admission.insert theory) after ∧
      InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.cache = before.read spaces.cache ∧
      after.read spaces.proofs = before.read spaces.proofs ∧
      (∀ other, other ∉ targets spaces admission → after.read other = before.read other) := by
  obtain ⟨answers, input, output, written⟩ := completed_writes spaces theory admission before
    ready.toTableReady fuel after answers input output completed
  exact ⟨answers, input, output, writes_tables spaces theory admission before after ready.toTableReady authorized written,
    writes_frozen_cache spaces theory admission before after ready written,
    writes_frame spaces theory admission before after ready.toTableReady written⟩

/-- A fresh sort request obtains the next native table along an actual
publication path. Sort admission requires precisely identifier freshness. -/
theorem fresh_sort_path_and_tables (spaces : Spaces) (theory : Theory) (index : Nat) (info : SortInfo)
    (before : State) (ready : Ready spaces theory before) (fresh : theory.sortSignature index = none) :
    ∃ after, (Eval.theory program).MultiStep (requestConfiguration before spaces (.sort index info))
        (finished after [optionValue (some (theoryValue spaces))] [] []) ∧
      TableReady spaces (Admission.insert theory (.sort index info)) after ∧
      InferenceCache.Ready theory.termSignature (tableValue spaces.terms) spaces.cache after ∧
      after.cells = before.cells ∧ after.read spaces.cache = before.read spaces.cache ∧
      after.read spaces.proofs = before.read spaces.proofs :=
  authorized_path_and_tables spaces theory (.sort index info) before ready (.sort fresh)

/-- The preceding source check refuses a duplicate sort. A direct publication
call still appends it, demonstrating why publication grants no authorization. -/
theorem duplicate_sort_check_refuses (spaces : Spaces) (theory : Theory) (index : Nat) (oldInfo info : SortInfo)
    (before : State) (ready : Ready spaces theory before) (present : theory.sortSignature index = some oldInfo) :
    AdmissionChecks.Call spaces (.sort index info) before before false ∧
      ¬ Admission.Authorized theory (.sort index info) ∧
      ∃ after, (Eval.theory program).MultiStep (requestConfiguration before spaces (.sort index info))
          (finished after [optionValue (some (theoryValue spaces))] [] []) ∧
        Writes spaces (.sort index info) before after := by
  have refused : Admission.check theory (.sort index info) = false := by simp [Admission.check, present]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [refused] using AdmissionChecks.sort_captured_returns spaces theory index info before ready
  · intro authorized
    have accepted := (Admission.check_iff theory (.sort index info)).mpr authorized
    simp [refused] at accepted
  · obtain ⟨after, returned, written⟩ := returns spaces theory (.sort index info) before ready.toTableReady
    exact ⟨after, returned _ "valueInput" "valueInputValue" rfl rfl, written⟩

end Mettapedia.Languages.MM0.MeTTa.AdmissionPublication
