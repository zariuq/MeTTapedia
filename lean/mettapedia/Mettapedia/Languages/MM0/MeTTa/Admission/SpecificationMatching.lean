import Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement
import Mettapedia.Languages.MM0.Kernel.SpecificationAdmission
import Mettapedia.Languages.MM0.MeTTa.Admission.AdmissionChecks
import Mettapedia.Languages.MM0.MeTTa.Formation.SortFormation
import Mettapedia.Languages.MM0.MeTTa.Kernel.Unfolding
import Mettapedia.Languages.MM0.MeTTa.Kernel.TheoremInstantiation

/-!
# Specification matching in the retained MM0 program

Specification declarations and proof declarations have different roles.
Public declarations must match the next specification entry; auxiliary
definitions and proved theorems consume no entry. A missing specification
body permits an admitted body, whereas a supplied body must agree exactly.
The computations below use the bodies read from the pinned program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SpecificationMatching

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (SpecificationEntry Admission TermDecl TheoremDecl SortInfo)
open Store (natural)
open ListAccess (listValue optionValue)

/-- Source encoding of an already resolved specification entry. -/
def entryValue : SpecificationEntry → Atom
  | .sort index info => listValue [.symbol "MM0:SpecSort", natural index, SortFormation.sortValue info]
  | .term index declaration => listValue [.symbol "MM0:SpecTerm", natural index, Data.declaration declaration]
  | .definition index declaration body =>
      listValue [.symbol "MM0:SpecDefinition", natural index, Data.declaration declaration,
        optionValue (body.map Unfolding.bodyValue)]
  | .axiomDecl index declaration =>
      listValue [.symbol "MM0:SpecAxiom", natural index, TheoremInstantiation.declarationValue declaration]
  | .theoremDecl index declaration =>
      listValue [.symbol "MM0:SpecTheorem", natural index, TheoremInstantiation.declarationValue declaration]

def declarationValue (declaration : Kernel.ProofDeclaration) : Atom :=
  listValue [.symbol "MM0:ProofDeclaration", boolean declaration.isLocal,
    AdmissionChecks.admissionValue declaration.admission]

def pendingValue (entries : List SpecificationEntry) : Atom := listValue (entries.map entryValue)

private theorem boolean_injective : Function.Injective boolean := by
  intro first second same
  simpa [boolean] using same

theorem sortValue_injective : Function.Injective SortFormation.sortValue := by
  intro first second same
  have parts : boolean first.pure = boolean second.pure ∧
      boolean first.strict = boolean second.strict ∧
      boolean first.provable = boolean second.provable ∧
      boolean first.free = boolean second.free := by
    simpa [SortFormation.sortValue, listValue] using same
  cases first; cases second
  simp_all only [boolean_injective.eq_iff]

theorem declarationValue_injective : Function.Injective Data.declaration := by
  intro first second same
  have parts : Data.context first.arguments = Data.context second.arguments ∧
      natural first.resultSort = natural second.resultSort ∧
      Data.dependencies first.dependencies = Data.dependencies second.dependencies := by
    simpa [Data.declaration, listValue] using same
  cases first; cases second
  simp_all only [Data.context_injective.eq_iff, Data.natural_injective.eq_iff,
    Data.dependencies_injective.eq_iff]

theorem bodyValue_injective : Function.Injective Unfolding.bodyValue := by
  intro first second same
  have parts : Support.indicesValue first.dummies = Support.indicesValue second.dummies ∧
      Data.preterm first.expression = Data.preterm second.expression := by
    simpa [Unfolding.bodyValue, listValue] using same
  have dummies : first.dummies = second.dummies :=
    List.map_injective_iff.mpr Data.natural_injective (by
      simpa [Support.indicesValue, listValue] using parts.1)
  have expression := Data.preterm_injective parts.2
  cases first; cases second
  simp_all

theorem theoremValue_injective : Function.Injective TheoremInstantiation.declarationValue := by
  intro first second same
  have parts : Data.context first.arguments = Data.context second.arguments ∧
      ListSubstitution.expressionsValue first.hypotheses = ListSubstitution.expressionsValue second.hypotheses ∧
      Data.preterm first.conclusion = Data.preterm second.conclusion := by
    simpa [TheoremInstantiation.declarationValue, listValue] using same
  have hypotheses : first.hypotheses = second.hypotheses :=
    List.map_injective_iff.mpr Data.preterm_injective (by
      simpa [ListSubstitution.expressionsValue, listValue] using parts.2.1)
  have context := Data.context_injective parts.1
  have conclusion := Data.preterm_injective parts.2.2
  cases first; cases second
  simp_all

private def bodyEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 123)[122]'(by decide +kernel)
private def guardEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 126)[125]'(by decide +kernel)

private def casesOf (body : Atom) : SpaceSemantics.Cases :=
  match body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def bodyCases := casesOf bodyEquation.body
private def guardCases := casesOf guardEquation.body

private theorem body_unique :
    program.equations.filter (fun row => row.head == "mm0:spec-body") = [bodyEquation] := by decide
private theorem guard_unique :
    program.equations.filter (fun row => row.head == "mm0:spec-guard") = [guardEquation] := by decide
private theorem body_formals : bodyEquation.arguments = [.var "valueInput", .var "body"] := by decide
private theorem guard_formals : guardEquation.arguments = [.var "conditionInput", .var "pending"] := by decide
private theorem body_shape : bodyEquation.body =
    .expression [.symbol "case", .var "valueInput", .expression (bodyCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem guard_shape : guardEquation.body =
    .expression [.symbol "case", .var "conditionInput", .expression (guardCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem body_cases : bodyCases = [(.symbol "None", boolean true),
    (.expression [.symbol "Some", .var "expected"],
      .expression [.symbol "mm0:data-eq", .var "expected", .var "body"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem guard_cases : guardCases = [(boolean false, .symbol "None"),
    (boolean true, .expression [.symbol "Some", .var "pending"]),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

private theorem body_returns (state : State) (expected : Option Kernel.Definition.Body)
    (actual : Kernel.Definition.Body) :
    PureReturns program [("body", Unfolding.bodyValue actual),
      ("valueInput", optionValue (expected.map Unfolding.bodyValue))] state bodyEquation.body state
      (boolean (decide (expected = none ∨ expected = some actual))) := by
  rw [body_shape]
  let bindings : Subst := [("body", Unfolding.bodyValue actual),
    ("valueInput", optionValue (expected.map Unfolding.bodyValue))]
  have input : PureReturns program bindings state (.var "valueInput") state
      (optionValue (expected.map Unfolding.bodyValue)) := by
    simpa [bindings, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  cases expected with
  | none =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "None") (boolean true) _ _ bodyCases (read_cases_encoded _) input
      · simp [body_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings state (.bool true)
  | some expected =>
      let bound := ("expected", Unfolding.bodyValue expected) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (optionValue (some (Unfolding.bodyValue expected)))
        (.expression [.symbol "mm0:data-eq", .var "expected", .var "body"]) _ _ bodyCases (read_cases_encoded _) input
      · simp [body_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, optionValue, bindings, bound, Subst.lookup]
      · simpa only [Option.some.injEq, reduceCtorEq, false_or,
          bodyValue_injective.eq_iff] using Scalar.data_equality_captured_returns bound state
          (Unfolding.bodyValue expected) (Unfolding.bodyValue actual) "expected" "body" rfl rfl

theorem body_captured_returns (bindings : Subst) (state : State)
    (expected : Option Kernel.Definition.Body) (actual : Kernel.Definition.Body)
    (expectedName actualName : String)
    (capturedExpected : applySubst bindings (.var expectedName) = optionValue (expected.map Unfolding.bodyValue))
    (capturedActual : applySubst bindings (.var actualName) = Unfolding.bodyValue actual) :
    PureReturns program bindings state (.expression [.symbol "mm0:spec-body", .var expectedName, .var actualName])
      state (boolean (decide (expected = none ∨ expected = some actual))) := by
  apply authored_variable_call_returns program bindings
    [("body", Unfolding.bodyValue actual), ("valueInput", optionValue (expected.map Unfolding.bodyValue))]
    state state "mm0:spec-body" [expectedName, actualName] bodyEquation.body _
    (by decide) (by decide) (by decide) _ (body_returns state expected actual) (by decide)
  rw [clauses_use_only_the_named_equations, body_unique]
  simp [capturedExpected, capturedActual, body_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup]

theorem guard_captured_returns (bindings : Subst) (state : State) (allowed : Bool) (pending : Atom)
    (allowedName pendingName : String)
    (capturedAllowed : applySubst bindings (.var allowedName) = boolean allowed)
    (capturedPending : applySubst bindings (.var pendingName) = pending) :
    PureReturns program bindings state (.expression [.symbol "mm0:spec-guard", .var allowedName, .var pendingName])
      state (optionValue (if allowed then some pending else none)) := by
  let callee : Subst := [("pending", pending), ("conditionInput", boolean allowed)]
  have body : PureReturns program callee state guardEquation.body state
      (optionValue (if allowed then some pending else none)) := by
    rw [guard_shape]
    have input : PureReturns program callee state (.var "conditionInput") state (boolean allowed) := by
      simpa [callee, applySubst, Subst.lookup] using variable_returns program callee state "conditionInput"
    cases allowed with
    | false =>
        apply case_returns program callee callee state state state _ _ (.symbol "None") _ _
          guardCases (read_cases_encoded _) input
        · simp [guard_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
        · exact symbol_returns program callee state "None"
    | true =>
        apply case_returns program callee callee state state state _ _
          (.expression [.symbol "Some", .var "pending"]) _ _ guardCases (read_cases_encoded _) input
        · simp [guard_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
        · simpa [optionValue, callee, applySubst, Subst.lookup] using
            unary_constructor_returns program callee state "Some" "pending" some_is_data_constructor (by decide)
  apply authored_variable_call_returns program bindings callee state state "mm0:spec-guard"
    [allowedName, pendingName] guardEquation.body _ (by decide) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, guard_unique]
  simp [capturedAllowed, capturedPending, guard_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, callee]

private def payloadBody (leftName rightName : String) : Atom :=
  .expression [.symbol "let", .var leftName, listValue [.var "index", .var "payload"],
    .expression [.symbol "let", .var rightName, listValue [.var "actual", .var "stored"],
      .expression [.symbol "mm0:data-eq", .var leftName, .var rightName]]]

private theorem payload_returns (bindings : Subst) (state : State) (index actual : Nat)
    (payload stored : Atom) (leftName rightName : String)
    (leftFresh : Subst.lookup bindings leftName = none)
    (rightFresh : Subst.lookup bindings rightName = none)
    (different : leftName ≠ rightName) (leftNotActual : leftName ≠ "actual")
    (leftNotStored : leftName ≠ "stored")
    (capturedIndex : applySubst bindings (.var "index") = natural index)
    (capturedPayload : applySubst bindings (.var "payload") = payload)
    (capturedActual : applySubst bindings (.var "actual") = natural actual)
    (capturedStored : applySubst bindings (.var "stored") = stored) :
    PureReturns program bindings state (payloadBody leftName rightName) state
      (boolean (decide (index = actual ∧ payload = stored))) := by
  let left := listValue [natural index, payload]
  let right := listValue [natural actual, stored]
  let withLeft := (leftName, left) :: bindings
  let withBoth := (rightName, right) :: withLeft
  have absentRight : (bindings.find? fun row => row.1 == rightName).map Prod.snd = none := rightFresh
  unfold payloadBody
  apply let_returns program bindings withLeft state state state (.var leftName) _ _ left _
  · simpa [left, listValue, capturedIndex, capturedPayload] using
      ListAccess.list_variables_return bindings state ["index", "payload"]
  · simp [SpaceSemantics.matchValue, matchAtom, leftFresh, withLeft]
  · apply let_returns program withLeft withBoth state state state (.var rightName) _ _ right _
    · have actualAfter : applySubst withLeft (.var "actual") = natural actual := by
        simpa [withLeft, applySubst, Subst.lookup, leftNotActual] using capturedActual
      have storedAfter : applySubst withLeft (.var "stored") = stored := by
        simpa [withLeft, applySubst, Subst.lookup, leftNotStored] using capturedStored
      simpa [right, listValue, actualAfter, storedAfter] using
        ListAccess.list_variables_return withLeft state ["actual", "stored"]
    · simp [SpaceSemantics.matchValue, matchAtom, withLeft, withBoth,
        Subst.lookup, absentRight, different]
    · have capturedLeft : applySubst withBoth (.var leftName) = left := by
        simp [withBoth, withLeft, applySubst, Subst.lookup, Ne.symm different]
      have capturedRight : applySubst withBoth (.var rightName) = right := by
        simp [withBoth, applySubst, Subst.lookup]
      simpa [left, right, listValue, Data.natural_injective.eq_iff] using
        Scalar.data_equality_captured_returns withBoth state left right leftName rightName
          capturedLeft capturedRight

private def equation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 122)[121]'(by decide +kernel)
private def cases := casesOf equation.body
private def arm (index : Nat) : Atom := (cases[index]?.map Prod.snd).getD (.symbol "MM0:Malformed")
private def environment (entry : SpecificationEntry) (admission : Admission) : Subst :=
  [("admissionInput", AdmissionChecks.admissionValue admission), ("entryInput", entryValue entry)]
private def branch : SpecificationEntry → Admission → Atom
  | .sort .., .sort .. => arm 0
  | .term .., .term .. => arm 1
  | .definition .., .definition .. => arm 2
  | .axiomDecl .., .axiomDecl .. => arm 3
  | .theoremDecl .., .theoremDecl .. => arm 4
  | _, _ => boolean false
private def fields : SpecificationEntry → Admission → Subst
  | .sort index info, .sort actual stored =>
      [("stored", SortFormation.sortValue stored), ("actual", natural actual),
        ("payload", SortFormation.sortValue info), ("index", natural index)]
  | .term index declaration, .term actual stored =>
      [("stored", Data.declaration stored), ("actual", natural actual),
        ("payload", Data.declaration declaration), ("index", natural index)]
  | .definition index declaration expected, .definition actual stored body =>
      [("body", Unfolding.bodyValue body), ("stored", Data.declaration stored), ("actual", natural actual),
        ("expected", optionValue (expected.map Unfolding.bodyValue)),
        ("payload", Data.declaration declaration), ("index", natural index)]
  | .axiomDecl index declaration, .axiomDecl actual stored =>
      [("stored", TheoremInstantiation.declarationValue stored), ("actual", natural actual),
        ("payload", TheoremInstantiation.declarationValue declaration), ("index", natural index)]
  | .theoremDecl index declaration, .theoremDecl actual stored dummies proof =>
      [("proof", Proof.witnessValue proof), ("dummies", Support.indicesValue dummies),
        ("stored", TheoremInstantiation.declarationValue stored), ("actual", natural actual),
        ("payload", TheoremInstantiation.declarationValue declaration), ("index", natural index)]
  | entry, admission => [("admission", AdmissionChecks.admissionValue admission), ("entry", entryValue entry)]
private def boundEnvironment (entry : SpecificationEntry) (admission : Admission) : Subst :=
  fields entry admission ++ environment entry admission

private theorem unique : program.equations.filter (fun row => row.head == "mm0:spec-match") = [equation] := by decide
private theorem formals : equation.arguments = [.var "entryInput", .var "admissionInput"] := by decide
private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "entryInput", .var "admissionInput"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide
private theorem cases_shape : cases = [
    (.expression [listValue [.symbol "MM0:SpecSort", .var "index", .var "payload"],
      listValue [.symbol "MM0:AdmitSort", .var "actual", .var "stored"]], arm 0),
    (.expression [listValue [.symbol "MM0:SpecTerm", .var "index", .var "payload"],
      listValue [.symbol "MM0:AdmitTerm", .var "actual", .var "stored"]], arm 1),
    (.expression [listValue [.symbol "MM0:SpecDefinition", .var "index", .var "payload", .var "expected"],
      listValue [.symbol "MM0:AdmitDefinition", .var "actual", .var "stored", .var "body"]], arm 2),
    (.expression [listValue [.symbol "MM0:SpecAxiom", .var "index", .var "payload"],
      listValue [.symbol "MM0:AdmitAxiom", .var "actual", .var "stored"]], arm 3),
    (.expression [listValue [.symbol "MM0:SpecTheorem", .var "index", .var "payload"],
      listValue [.symbol "MM0:AdmitTheorem", .var "actual", .var "stored", .var "dummies", .var "proof"]], arm 4),
    (.expression [.var "entry", .var "admission"], boolean false),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem selected (entry : SpecificationEntry) (admission : Admission) :
    SpaceSemantics.selectCase (environment entry admission)
      (.expression [entryValue entry, AdmissionChecks.admissionValue admission]) cases =
      some (boundEnvironment entry admission, branch entry admission) := by
  cases entry <;> cases admission <;>
    simp [cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
      SpaceSemantics.matchValue.matchValues, matchAtom, entryValue, AdmissionChecks.admissionValue,
      listValue, boundEnvironment, fields, environment, branch, Subst.lookup]

private theorem sort_shape (index actual : Nat) (info stored : SortInfo) :
    branch (.sort index info) (.sort actual stored) = payloadBody "items" "items2" := by
  change arm 0 = payloadBody "items" "items2"
  decide
private theorem term_shape (index actual : Nat) (declaration stored : TermDecl) :
    branch (.term index declaration) (.term actual stored) = payloadBody "items3" "items4" := by
  change arm 1 = payloadBody "items3" "items4"
  decide
private theorem axiom_shape (index actual : Nat) (declaration stored : TheoremDecl) :
    branch (.axiomDecl index declaration) (.axiomDecl actual stored) = payloadBody "items7" "items8" := by
  change arm 3 = payloadBody "items7" "items8"
  decide
private theorem theorem_shape (index actual : Nat) (declaration stored : TheoremDecl)
    (dummies : List Nat) (proof : Kernel.ProofWitness) :
    branch (.theoremDecl index declaration) (.theoremDecl actual stored dummies proof) =
      payloadBody "items9" "items10" := by
  change arm 4 = payloadBody "items9" "items10"
  decide
private theorem definition_shape (index actual : Nat) (declaration stored : TermDecl)
    (expected : Option Kernel.Definition.Body) (body : Kernel.Definition.Body) :
    branch (.definition index declaration expected) (.definition actual stored body) =
      .expression [.symbol "let", .var "equal", payloadBody "items5" "items6",
        .expression [.symbol "let", .var "specBodyResult",
          .expression [.symbol "mm0:spec-body", .var "expected", .var "body"],
          .expression [.symbol "mm0:form-and", .var "equal", .var "specBodyResult"]]] := by
  change arm 2 = .expression [.symbol "let", .var "equal", payloadBody "items5" "items6",
    .expression [.symbol "let", .var "specBodyResult",
      .expression [.symbol "mm0:spec-body", .var "expected", .var "body"],
      .expression [.symbol "mm0:form-and", .var "equal", .var "specBodyResult"]]]
  decide

private theorem definition_returns (state : State) (index actual : Nat) (declaration stored : TermDecl)
    (expected : Option Kernel.Definition.Body) (body : Kernel.Definition.Body) :
    PureReturns program (boundEnvironment (.definition index declaration expected) (.definition actual stored body)) state
      (branch (.definition index declaration expected) (.definition actual stored body)) state
      (boolean (SpecificationEntry.checkMatch (.definition index declaration expected) (.definition actual stored body))) := by
  let bindings := boundEnvironment (.definition index declaration expected) (.definition actual stored body)
  let equal := decide (index = actual ∧ Data.declaration declaration = Data.declaration stored)
  let bodyMatches := decide (expected = none ∨ expected = some body)
  let withEqual := ("equal", boolean equal) :: bindings
  let withBoth := ("specBodyResult", boolean bodyMatches) :: withEqual
  have result : (equal && bodyMatches) = SpecificationEntry.checkMatch
      (.definition index declaration expected) (.definition actual stored body) := by
    simp [equal, bodyMatches, SpecificationEntry.checkMatch, declarationValue_injective.eq_iff,
      Bool.and_assoc]
  rw [definition_shape, ← result]
  apply let_returns program bindings withEqual state state state (.var "equal") _ _ (boolean equal) _
  · apply payload_returns bindings state index actual (Data.declaration declaration) (Data.declaration stored) "items5" "items6"
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by decide) (by decide) (by decide) rfl rfl rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, withEqual, bindings, boundEnvironment, fields, environment, Subst.lookup]
  · apply let_returns program withEqual withBoth state state state (.var "specBodyResult") _ _ (boolean bodyMatches) _
    · exact body_captured_returns withEqual state expected body "expected" "body" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, withBoth, withEqual, bindings, boundEnvironment, fields, environment, Subst.lookup]
    · exact SortFormation.and_returns withBoth state equal bodyMatches "equal" "specBodyResult" rfl rfl

private theorem branch_returns (state : State) (entry : SpecificationEntry) (admission : Admission) :
    PureReturns program (boundEnvironment entry admission) state (branch entry admission) state
      (boolean (SpecificationEntry.checkMatch entry admission)) := by
  cases entry <;> cases admission
  all_goals try exact grounded_returns program _ state (.bool false)
  case definition.definition index declaration expected actual stored body =>
    exact definition_returns state index actual declaration stored expected body
  case sort.sort index declaration actual stored =>
    let bindings := boundEnvironment (.sort index declaration) (.sort actual stored)
    rw [sort_shape]
    have returned := payload_returns bindings state index actual (SortFormation.sortValue declaration) (SortFormation.sortValue stored)
      "items" "items2"
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by decide) (by decide) (by decide) rfl rfl rfl rfl
    simpa only [SpecificationEntry.checkMatch, sortValue_injective.eq_iff] using returned
  case term.term index declaration actual stored =>
    let bindings := boundEnvironment (.term index declaration) (.term actual stored)
    rw [term_shape]
    have returned := payload_returns bindings state index actual (Data.declaration declaration) (Data.declaration stored)
      "items3" "items4"
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by decide) (by decide) (by decide) rfl rfl rfl rfl
    simpa only [SpecificationEntry.checkMatch, declarationValue_injective.eq_iff] using returned
  case axiomDecl.axiomDecl index declaration actual stored =>
    let bindings := boundEnvironment (.axiomDecl index declaration) (.axiomDecl actual stored)
    rw [axiom_shape]
    have returned := payload_returns bindings state index actual (TheoremInstantiation.declarationValue declaration) (TheoremInstantiation.declarationValue stored)
      "items7" "items8"
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by decide) (by decide) (by decide) rfl rfl rfl rfl
    simpa only [SpecificationEntry.checkMatch, theoremValue_injective.eq_iff] using returned
  case theoremDecl.theoremDecl index declaration actual stored dummies proof =>
    let bindings := boundEnvironment (.theoremDecl index declaration) (.theoremDecl actual stored dummies proof)
    rw [theorem_shape]
    have returned := payload_returns bindings state index actual (TheoremInstantiation.declarationValue declaration) (TheoremInstantiation.declarationValue stored)
      "items9" "items10"
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by simp [bindings, boundEnvironment, fields, environment, Subst.lookup])
      (by decide) (by decide) (by decide) rfl rfl rfl rfl
    simpa only [SpecificationEntry.checkMatch, theoremValue_injective.eq_iff] using returned

theorem match_captured_returns (bindings : Subst) (state : State) (entry : SpecificationEntry) (admission : Admission)
    (entryName admissionName : String)
    (capturedEntry : applySubst bindings (.var entryName) = entryValue entry)
    (capturedAdmission : applySubst bindings (.var admissionName) = AdmissionChecks.admissionValue admission) :
    PureReturns program bindings state (.expression [.symbol "mm0:spec-match", .var entryName, .var admissionName])
      state (boolean (SpecificationEntry.checkMatch entry admission)) := by
  have body : PureReturns program (environment entry admission) state equation.body state
      (boolean (SpecificationEntry.checkMatch entry admission)) := by
    rw [shape]
    apply case_returns program (environment entry admission) (boundEnvironment entry admission) state state state
      (.expression [.var "entryInput", .var "admissionInput"])
      (.expression [entryValue entry, AdmissionChecks.admissionValue admission])
      (branch entry admission) _ _ cases (read_cases_encoded _)
    · simpa [environment, applySubst, Subst.lookup] using tuple_variables_return program (environment entry admission) state ["entryInput", "admissionInput"]
    · exact selected entry admission
    · exact branch_returns state entry admission
  apply authored_variable_call_returns program bindings (environment entry admission) state state
    "mm0:spec-match" [entryName, admissionName] equation.body _ (by decide +kernel) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, unique]
  simp [capturedEntry, capturedAdmission, formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, environment]

private def auxiliaryEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 124)[123]'(by decide +kernel)
private def auxiliaryCases := casesOf auxiliaryEquation.body
private def auxiliaryEnvironment (admission : Admission) : Subst :=
  [("admissionInput", AdmissionChecks.admissionValue admission)]
private def auxiliaryFields : Admission → Subst
  | .definition index declaration body => [("body", Unfolding.bodyValue body),
      ("payload", Data.declaration declaration), ("index", natural index)]
  | .theoremDecl index declaration dummies proof => [("proof", Proof.witnessValue proof),
      ("dummies", Support.indicesValue dummies), ("payload", TheoremInstantiation.declarationValue declaration),
      ("index", natural index)]
  | admission => [("admission", AdmissionChecks.admissionValue admission)]
private theorem auxiliary_unique :
    program.equations.filter (fun row => row.head == "mm0:spec-auxiliary") = [auxiliaryEquation] := by decide
private theorem auxiliary_formals : auxiliaryEquation.arguments = [.var "admissionInput"] := by decide
private theorem auxiliary_shape : auxiliaryEquation.body = .expression [.symbol "case", .expression [.var "admissionInput"],
    .expression (auxiliaryCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem auxiliary_cases : auxiliaryCases = [
    (.expression [listValue [.symbol "MM0:AdmitDefinition", .var "index", .var "payload", .var "body"]], boolean true),
    (.expression [listValue [.symbol "MM0:AdmitTheorem", .var "index", .var "payload", .var "dummies", .var "proof"]], boolean true),
    (.expression [.var "admission"], boolean false), (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide

theorem auxiliary_captured_returns (bindings : Subst) (state : State) (admission : Admission) (name : String)
    (captured : applySubst bindings (.var name) = AdmissionChecks.admissionValue admission) :
    PureReturns program bindings state (.expression [.symbol "mm0:spec-auxiliary", .var name]) state
      (boolean (Kernel.ProofDeclaration.auxiliary admission)) := by
  let callee := auxiliaryEnvironment admission
  let bound := auxiliaryFields admission ++ callee
  have body : PureReturns program callee state auxiliaryEquation.body state
      (boolean (Kernel.ProofDeclaration.auxiliary admission)) := by
    rw [auxiliary_shape]
    apply case_returns program callee bound state state state (.expression [.var "admissionInput"])
      (.expression [AdmissionChecks.admissionValue admission])
      (boolean (Kernel.ProofDeclaration.auxiliary admission)) _ _ auxiliaryCases (read_cases_encoded _)
    · simpa [callee, auxiliaryEnvironment, applySubst, Subst.lookup] using
        tuple_variables_return program callee state ["admissionInput"]
    · cases admission <;> simp [auxiliary_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, AdmissionChecks.admissionValue, listValue,
        bound, callee, auxiliaryEnvironment, auxiliaryFields, Subst.lookup, Kernel.ProofDeclaration.auxiliary]
    · exact grounded_returns program bound state (.bool (Kernel.ProofDeclaration.auxiliary admission))
  apply authored_variable_call_returns program bindings callee state state "mm0:spec-auxiliary" [name]
    auxiliaryEquation.body _ (by decide +kernel) (by decide) (by decide) _ body (by decide)
  rw [clauses_use_only_the_named_equations, auxiliary_unique]
  simp [captured, auxiliary_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, callee, auxiliaryEnvironment]

private def publicEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 127)[126]'(by decide +kernel)
private def publicCases := casesOf publicEquation.body
private def publicConsBody : Atom := (publicCases[1]'(by decide)).2
private def publicEnvironment (entries : List SpecificationEntry) (admission : Admission) : Subst :=
  [("admission", AdmissionChecks.admissionValue admission),
    ("valueInput", ListAccess.viewValue (entries.map entryValue))]
private theorem public_unique :
    program.equations.filter (fun row => row.head == "mm0:spec-public") = [publicEquation] := by decide
private theorem public_formals : publicEquation.arguments = [.var "valueInput", .var "admission"] := by decide
private theorem public_shape : publicEquation.body = .expression [.symbol "case", .var "valueInput",
    .expression (publicCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem public_cases : publicCases = [(.symbol "List:Nil", .symbol "None"),
    (.expression [.symbol "List:Cons", .var "entry", .var "pending"], publicConsBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem public_cons_shape : publicConsBody = .expression [.symbol "let", .var "specMatchResult",
    .expression [.symbol "mm0:spec-match", .var "entry", .var "admission"],
    .expression [.symbol "mm0:spec-guard", .var "specMatchResult", .var "pending"]] := by decide

private theorem public_body_returns (state : State) (entries : List SpecificationEntry) (admission : Admission) :
    PureReturns program (publicEnvironment entries admission) state publicEquation.body state
      (optionValue ((Kernel.SpecificationAdmission.pending? entries ⟨admission, false⟩).map pendingValue)) := by
  let bindings := publicEnvironment entries admission
  rw [public_shape]
  have input : PureReturns program bindings state (.var "valueInput") state
      (ListAccess.viewValue (entries.map entryValue)) := by
    simpa [bindings, publicEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "valueInput"
  cases entries with
  | nil =>
      apply case_returns program bindings bindings state state state (.var "valueInput")
        (.symbol "List:Nil") (.symbol "None") _ _ publicCases (read_cases_encoded _) input
      · simp [public_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact symbol_returns program bindings state "None"
  | cons entry remaining =>
      let bound := ("pending", pendingValue remaining) :: ("entry", entryValue entry) :: bindings
      apply case_returns program bindings bound state state state (.var "valueInput")
        (ListAccess.viewValue ((entry :: remaining).map entryValue)) publicConsBody _ _
        publicCases (read_cases_encoded _) input
      · simp [public_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, ListAccess.viewValue, pendingValue,
          bound, bindings, publicEnvironment, Subst.lookup]
      · rw [public_cons_shape]
        let checked := ("specMatchResult", boolean (entry.checkMatch admission)) :: bound
        apply let_returns program bound checked state state state (.var "specMatchResult") _ _
          (boolean (entry.checkMatch admission)) _
        · exact match_captured_returns bound state entry admission "entry" "admission" rfl rfl
        · simp [SpaceSemantics.matchValue, matchAtom, checked, bound, bindings, publicEnvironment, Subst.lookup]
        · simpa [Kernel.SpecificationAdmission.pending?] using
            guard_captured_returns checked state (entry.checkMatch admission) (pendingValue remaining)
              "specMatchResult" "pending" rfl rfl

theorem public_captured_returns (bindings : Subst) (state : State) (entries : List SpecificationEntry)
    (admission : Admission) (viewName admissionName : String)
    (capturedView : applySubst bindings (.var viewName) = ListAccess.viewValue (entries.map entryValue))
    (capturedAdmission : applySubst bindings (.var admissionName) = AdmissionChecks.admissionValue admission) :
    PureReturns program bindings state (.expression [.symbol "mm0:spec-public", .var viewName, .var admissionName]) state
      (optionValue ((Kernel.SpecificationAdmission.pending? entries ⟨admission, false⟩).map pendingValue)) := by
  apply authored_variable_call_returns program bindings (publicEnvironment entries admission) state state
    "mm0:spec-public" [viewName, admissionName] publicEquation.body _
    (by decide +kernel) (by decide) (by decide) _ (public_body_returns state entries admission) (by decide)
  rw [clauses_use_only_the_named_equations, public_unique]
  simp [capturedView, capturedAdmission, public_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, publicEnvironment]

private def pendingEquation : SpaceSemantics.Equation :=
  (kernelSource.program.equations.take 125)[124]'(by decide +kernel)
private def pendingCases := casesOf pendingEquation.body
private def localBody : Atom := (pendingCases[0]'(by decide)).2
private def publicBody : Atom := (pendingCases[1]'(by decide)).2
private def pendingEnvironment (entries : List SpecificationEntry) (declaration : Kernel.ProofDeclaration) : Subst :=
  [("admission", AdmissionChecks.admissionValue declaration.admission), ("pending", pendingValue entries),
    ("conditionInput", boolean declaration.isLocal)]
private theorem pending_unique :
    program.equations.filter (fun row => row.head == "mm0:spec-pending") = [pendingEquation] := by decide
private theorem pending_formals : pendingEquation.arguments = [.var "conditionInput", .var "pending", .var "admission"] := by decide
private theorem pending_shape : pendingEquation.body = .expression [.symbol "case", .var "conditionInput",
    .expression (pendingCases.map fun row => .expression [row.1, row.2])] := by decide
private theorem pending_cases : pendingCases = [(boolean true, localBody), (boolean false, publicBody),
    (.var "mm0Malformed", .symbol "MM0:Malformed")] := by decide
private theorem local_shape : localBody = .expression [.symbol "let", .var "specAuxiliaryResult",
    .expression [.symbol "mm0:spec-auxiliary", .var "admission"],
    .expression [.symbol "mm0:spec-guard", .var "specAuxiliaryResult", .var "pending"]] := by decide
private theorem public_body_shape : publicBody = .expression [.symbol "let", .var "view",
    .expression [.symbol "mm0:list-view", .var "pending"],
    .expression [.symbol "mm0:spec-public", .var "view", .var "admission"]] := by decide

private theorem pending_body_returns (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) :
    PureReturns program (pendingEnvironment entries declaration) state pendingEquation.body state
      (optionValue ((Kernel.SpecificationAdmission.pending? entries declaration).map pendingValue)) := by
  let bindings := pendingEnvironment entries declaration
  rw [pending_shape]
  have input : PureReturns program bindings state (.var "conditionInput") state (boolean declaration.isLocal) := by
    simpa [bindings, pendingEnvironment, applySubst, Subst.lookup] using variable_returns program bindings state "conditionInput"
  rcases declaration with ⟨admission, localFlag⟩
  cases localFlag with
  | true =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean true)
        localBody _ _ pendingCases (read_cases_encoded _) input
      · simp [pending_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [local_shape]
        let checked := ("specAuxiliaryResult", boolean (Kernel.ProofDeclaration.auxiliary admission)) :: bindings
        apply let_returns program bindings checked state state state (.var "specAuxiliaryResult") _ _
          (boolean (Kernel.ProofDeclaration.auxiliary admission)) _
        · exact auxiliary_captured_returns bindings state admission "admission" rfl
        · simp [SpaceSemantics.matchValue, matchAtom, checked, bindings, pendingEnvironment, Subst.lookup]
        · simpa [Kernel.SpecificationAdmission.pending?] using
            guard_captured_returns checked state (Kernel.ProofDeclaration.auxiliary admission) (pendingValue entries)
              "specAuxiliaryResult" "pending" rfl rfl
  | false =>
      apply case_returns program bindings bindings state state state (.var "conditionInput") (boolean false)
        publicBody _ _ pendingCases (read_cases_encoded _) input
      · simp [pending_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, boolean]
      · rw [public_body_shape]
        let viewed := ("view", ListAccess.viewValue (entries.map entryValue)) :: bindings
        apply let_returns program bindings viewed state state state (.var "view") _ _
          (ListAccess.viewValue (entries.map entryValue)) _
        · exact ListAccess.view_captured_returns bindings state "pending" (entries.map entryValue) rfl
        · simp [SpaceSemantics.matchValue, matchAtom, viewed, bindings, pendingEnvironment, Subst.lookup]
        · exact public_captured_returns viewed state entries admission "view" "admission" rfl rfl

theorem pending_captured_returns (bindings : Subst) (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) (localName pendingName admissionName : String)
    (capturedLocal : applySubst bindings (.var localName) = boolean declaration.isLocal)
    (capturedPending : applySubst bindings (.var pendingName) = pendingValue entries)
    (capturedAdmission : applySubst bindings (.var admissionName) = AdmissionChecks.admissionValue declaration.admission) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:spec-pending", .var localName, .var pendingName, .var admissionName]) state
      (optionValue ((Kernel.SpecificationAdmission.pending? entries declaration).map pendingValue)) := by
  apply authored_variable_call_returns program bindings (pendingEnvironment entries declaration) state state
    "mm0:spec-pending" [localName, pendingName, admissionName] pendingEquation.body _
    (by decide +kernel) (by decide) (by decide) _ (pending_body_returns state entries declaration) (by decide)
  rw [clauses_use_only_the_named_equations, pending_unique]
  simp [capturedLocal, capturedPending, capturedAdmission, pending_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, pendingEnvironment]

theorem optionalBodyValue_injective : Function.Injective
    (fun body : Option Kernel.Definition.Body => optionValue (body.map Unfolding.bodyValue)) := by
  intro first second same
  cases first <;> cases second <;> simp_all [optionValue, bodyValue_injective.eq_iff]

theorem entryValue_injective : Function.Injective entryValue := by
  intro first second same
  cases first <;> cases second <;>
    simp_all [entryValue, listValue, Data.natural_injective.eq_iff,
      sortValue_injective.eq_iff, declarationValue_injective.eq_iff,
      optionalBodyValue_injective.eq_iff, theoremValue_injective.eq_iff]

theorem pendingValue_injective : Function.Injective pendingValue := by
  intro first second same
  apply List.map_injective_iff.mpr entryValue_injective
  simpa [pendingValue, listValue] using same

private theorem pendingResult_injective : Function.Injective
    (fun entries : Option (List SpecificationEntry) => optionValue (entries.map pendingValue)) := by
  intro first second same
  cases first <;> cases second <;> simp_all [optionValue, pendingValue_injective.eq_iff]

def matchRequestConfiguration (state : State) (entry : SpecificationEntry) (admission : Admission) : Configuration :=
  { state, control := .evaluate (environment entry admission)
      (.expression [.symbol "mm0:spec-match", .var "entryInput", .var "admissionInput"]) }

def pendingRequestConfiguration (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) : Configuration :=
  { state, control := .evaluate (pendingEnvironment entries declaration)
      (.expression [.symbol "mm0:spec-pending", .var "conditionInput", .var "pending", .var "admission"]) }

theorem match_sufficient_fuel (state : State) (entry : SpecificationEntry) (admission : Admission) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (matchRequestConfiguration state entry admission) =
      .complete state [boolean (entry.checkMatch admission)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment entry admission) state state _ _
    (match_captured_returns (environment entry admission) state entry admission "entryInput" "admissionInput" rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem match_result_iff (state : State) (entry : SpecificationEntry) (admission : Admission) (answer : Bool) :
    entry.checkMatch admission = answer ↔
      ∃ after fuel, run program fuel (matchRequestConfiguration state entry admission) = .complete after [boolean answer] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := match_sufficient_fuel state entry admission
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same; exact ⟨state, referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] reference returned
    exact boolean_injective (List.singleton_inj.mp same.2.1)

theorem matched_iff_source_accepts (state : State) (entry : SpecificationEntry) (admission : Admission) :
    entry.Matches admission ↔
      ∃ after fuel, run program fuel (matchRequestConfiguration state entry admission) = .complete after [boolean true] [] [] :=
  (SpecificationEntry.checkMatch_iff entry admission).symm.trans (match_result_iff state entry admission true)

theorem matched_iff_gslt_path (state : State) (entry : SpecificationEntry) (admission : Admission) :
    entry.Matches admission ↔
      ∃ after, (theory program).MultiStep (matchRequestConfiguration state entry admission) (finished after [boolean true] [] []) := by
  rw [matched_iff_source_accepts]
  exact exists_congr fun after => completed_run_iff_path program _ after _ [] []

theorem pending_sufficient_fuel (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) :
    ∃ fuel, ∀ extra, run program (fuel + extra) (pendingRequestConfiguration state entries declaration) =
      .complete state [optionValue ((Kernel.SpecificationAdmission.pending? entries declaration).map pendingValue)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (pendingEnvironment entries declaration) state state _ _
    (pending_captured_returns (pendingEnvironment entries declaration) state entries declaration
      "conditionInput" "pending" "admission" rfl rfl rfl)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ state _ [] [] completed⟩

theorem pending_result_iff (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) (answer : Option (List SpecificationEntry)) :
    Kernel.SpecificationAdmission.pending? entries declaration = answer ↔
      ∃ after fuel, run program fuel (pendingRequestConfiguration state entries declaration) =
        .complete after [optionValue (answer.map pendingValue)] [] [] := by
  obtain ⟨referenceFuel, completed⟩ := pending_sufficient_fuel state entries declaration
  have reference := completed 0
  simp only [Nat.add_zero] at reference
  constructor
  · intro same; exact ⟨state, referenceFuel, by simpa only [same] using reference⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] _ [] [] reference returned
    exact pendingResult_injective (List.singleton_inj.mp same.2.1)

theorem permitted_iff_source_pending (state : State) (entries remaining : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) :
    Kernel.SpecificationAdmission.pending? entries declaration = some remaining ↔
      ∃ after fuel, run program fuel (pendingRequestConfiguration state entries declaration) =
        .complete after [optionValue (some (pendingValue remaining))] [] [] :=
  pending_result_iff state entries declaration (some remaining)

theorem pending_refused_iff_source_none (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) :
    Kernel.SpecificationAdmission.pending? entries declaration = none ↔
      ∃ after fuel, run program fuel (pendingRequestConfiguration state entries declaration) = .complete after [.symbol "None"] [] [] :=
  pending_result_iff state entries declaration none

theorem pending_result_iff_judgment (state : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) (answer : Option (List SpecificationEntry)) :
    Kernel.SpecificationAdmission.pending? entries declaration = answer ↔
      ∃ after, DeclarativeSpec.Runs program (pendingRequestConfiguration state entries declaration)
        (.complete after [optionValue (answer.map pendingValue)] [] []) := by
  rw [pending_result_iff]
  exact exists_congr fun after => completed_run_iff_derivation program _ after _ [] []

theorem completed_pending_preserves_store (state after : State) (entries : List SpecificationEntry)
    (declaration : Kernel.ProofDeclaration) (fuel : Nat) (answers printed input : List Atom)
    (completed : run program fuel (pendingRequestConfiguration state entries declaration) = .complete after answers printed input) :
    after = state ∧ answers = [optionValue ((Kernel.SpecificationAdmission.pending? entries declaration).map pendingValue)] ∧
      printed = [] ∧ input = [] := by
  obtain ⟨referenceFuel, returns⟩ := pending_sufficient_fuel state entries declaration
  have reference := returns 0
  simp only [Nat.add_zero] at reference
  have same := completed_result_unique program referenceFuel fuel _ state after _ [] [] answers printed input reference completed
  exact ⟨same.1.symm, same.2.1.symm, same.2.2.1.symm, same.2.2.2.symm⟩

/-! ## Specification boundary controls on the source machine -/

private def controlDeclaration : TermDecl := ⟨[], 0, ∅⟩
private def controlBody : Kernel.Definition.Body := ⟨[], .term 0⟩

theorem omitted_body_source_accepts :
    UpstreamAgreement.answersOf (run program 400 (matchRequestConfiguration Effects.empty
      (.definition 0 controlDeclaration none) (.definition 0 controlDeclaration controlBody))) =
      some [boolean true] := by decide +kernel

theorem different_body_source_refuses :
    UpstreamAgreement.answersOf (run program 400 (matchRequestConfiguration Effects.empty
      (.definition 0 controlDeclaration (some controlBody)) (.definition 0 controlDeclaration ⟨[], .var 0⟩))) =
      some [boolean false] := by decide +kernel

theorem local_definition_preserves_empty_specification :
    UpstreamAgreement.answersOf (run program 400 (pendingRequestConfiguration Effects.empty []
      ⟨.definition 0 controlDeclaration controlBody, true⟩)) =
      some [optionValue (some (pendingValue []))] := by decide +kernel

theorem local_axiom_source_refuses :
    UpstreamAgreement.answersOf (run program 400 (pendingRequestConfiguration Effects.empty []
      ⟨.axiomDecl 0 ⟨[], [], .term 0⟩, true⟩)) =
      some [.symbol "None"] := by decide +kernel

theorem public_declaration_requires_an_entry :
    UpstreamAgreement.answersOf (run program 400 (pendingRequestConfiguration Effects.empty [] ⟨.sort 0 {}, false⟩)) =
      some [.symbol "None"] := by decide +kernel

end Mettapedia.Languages.MM0.MeTTa.SpecificationMatching
