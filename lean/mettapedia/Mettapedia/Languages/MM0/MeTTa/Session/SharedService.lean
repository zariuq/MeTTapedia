import Mettapedia.Languages.MM0.MeTTa.Admission.SpecificationStep
import Mettapedia.Languages.MM0.MeTTa.Session.Sharing
import Mettapedia.Languages.MM0.Kernel.SharedAdmission

/-!
# Fixed shared-theorem submissions in the retained MM0 service

The service checks the supplied initializer witnesses in chronological order,
including each optional expected conclusion, then checks the supplied root.
Specification permission and independent theorem formation precede this
execution. Publication follows only a successful fixed submission. Cut supplies
ordinary logical evidence separately; it never replaces the submitted root.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.SharedService

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open NamedSpaces (Handle)
open Kernel (Theory Admission TheoremDecl ProofWitness SpecificationEntry ProofDeclaration)
open SessionInitialization (Spaces theoryValue stateValue)
open SpecificationMatching (pendingValue)
open AdmissionChecks (admissionValue Ready TableReady)
open TableAccess (tableValue)
open ListAccess (listValue optionValue)
open Store (natural)

/-- The command submitted by the frontend, including an empty saved list. -/
structure Command where
  isLocal : Bool
  index : Nat
  declaration : TheoremDecl
  dummies : List Nat
  saved : List Sharing.Entry
  root : ProofWitness

def Command.admission (command : Command) : Admission :=
  .theoremDecl command.index command.declaration command.dummies command.root

def Command.proofDeclaration (command : Command) : ProofDeclaration :=
  ⟨command.admission, command.isLocal⟩

def commandValue (command : Command) : Atom :=
  .expression [.symbol "MM0:SharedTheorem", boolean command.isLocal, natural command.index,
    TheoremInstantiation.declarationValue command.declaration, Support.indicesValue command.dummies,
    listValue (command.saved.map Sharing.entryValue), Proof.witnessValue command.root]

/-- Shared checking uses the existing vector implementation, with the same
preceding logical signatures as ordinary admission. -/
def tables {before : State} (spaces : Spaces) (theory : Theory) (declaration : TheoremDecl)
    (ready : Ready spaces theory before) : Proof.Tables :=
  { AdmissionChecks.proofTables spaces theory declaration.hypotheses ready with storage := .vector }

def Accepted {before : State} (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (ready : Ready spaces logical.theory before) : Prop :=
  (∃ remaining, Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining) ∧
    Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
    Sharing.Checked (Admission.proofContext command.declaration command.dummies)
      command.root command.declaration.conclusion (tables spaces logical.theory command.declaration ready) command.saved

/-- This is physical input evidence, without any assumption about the saved
values left from an earlier proof check. The vector initializer replaces them. -/
structure Input (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State) (before : State) : Prop where
  ready : Ready spaces logical.theory before
  proofCell : before.cells "mm0-proof-store" = some (Effects.handleValue spaces.proofs)
  proofRows : ∃ rows, before.read spaces.proofs = some rows ∧ Effects.RowsHaveArity 2 rows

/-- The native result contains capabilities; this frame supplies the logical
snapshot they actually represent and the private stores needed by the driver. -/
structure EffectFrame (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before after : State) (result : Option Kernel.SpecificationAdmission.State) : Prop where
  tables : TableReady spaces (result.getD logical).theory after
  cache : InferenceCache.Ready logical.theory.termSignature (tableValue spaces.terms) spaces.cache after
  cacheRows : ∃ rows, after.read spaces.cache = some rows ∧ Effects.RowsHaveArity 4 rows
  proofCell : after.cells "mm0-proof-store" = some (Effects.handleValue spaces.proofs)
  proofRows : ∃ rows, after.read spaces.proofs = some rows ∧ Effects.RowsHaveArity 2 rows
  cells : after.cells = before.cells
  other : ∀ handle, handle ≠ spaces.cache → handle ≠ spaces.proofs → handle ≠ spaces.theorems →
    after.read handle = before.read handle
  refused : result = none → after.read spaces.theorems = before.read spaces.theorems
  pendingRefused : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = none →
    after = before

private def casesOf (expression : Atom) : SpaceSemantics.Cases :=
  match expression with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def letBody (expression : Atom) : Atom :=
  match expression with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def yesBody (expression : Atom) : Atom :=
  match expression with
  | .expression [_, _, yes, _] => yes
  | _ => .expression []

private def equation : SpaceSemantics.Equation := serviceSource.program.equations[2]'(by decide +kernel)
private def cases := casesOf equation.body
private def body := (cases[0]'(by decide +kernel)).2
private def shapeBody := letBody body
private def nextBody := letBody shapeBody
private def nextCases := casesOf nextBody
private def permittedBody := (nextCases[0]'(by decide +kernel)).2
private def formedBody := yesBody permittedBody
private def dummiesBody := yesBody formedBody
private def sharingBody := yesBody dummiesBody
private def contextBody := letBody sharingBody
private def checkedBody := letBody contextBody
private def publishedBody := yesBody checkedBody

private def environment (spaces : Spaces) (pending : List SpecificationEntry) (command : Command) : Subst :=
  [("command", commandValue command), ("state", stateValue spaces (pendingValue pending))]

private def boundEnvironment (spaces : Spaces) (pending : List SpecificationEntry) (command : Command) : Subst :=
  [("root", Proof.witnessValue command.root), ("saved", listValue (command.saved.map Sharing.entryValue)),
    ("dummies", Support.indicesValue command.dummies), ("claim", Data.preterm command.declaration.conclusion),
    ("hyps", ListSubstitution.expressionsValue command.declaration.hypotheses),
    ("args", Data.context command.declaration.arguments), ("index", natural command.index),
    ("local", boolean command.isLocal), ("pending", pendingValue pending),
    ("thms", tableValue spaces.theorems), ("defs", tableValue spaces.definitions),
    ("terms", tableValue spaces.terms), ("sorts", tableValue spaces.sorts)] ++ environment spaces pending command

private def shapedEnvironment (spaces : Spaces) (pending : List SpecificationEntry) (command : Command) : Subst :=
  ("shape", admissionValue command.admission) :: boundEnvironment spaces pending command

private def permittedEnvironment (spaces : Spaces) (pending remaining : List SpecificationEntry)
    (command : Command) : Subst :=
  ("remaining", pendingValue remaining) :: ("next", optionValue (some (pendingValue remaining))) ::
    shapedEnvironment spaces pending command

private def declarationExpression : Atom :=
  listValue [.symbol "MM0:Theorem", .var "args", .var "hyps", .var "claim"]

private def theoryExpression : Atom :=
  listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "defs", .var "thms"]

private def admissionExpression : Atom :=
  listValue [.symbol "MM0:AdmitTheorem", .var "index", declarationExpression, .var "dummies", .var "root"]

private theorem unique : program.equations.filter (fun row => row.head == "mm0:service-step") = [equation] := by
  decide +kernel

private theorem formals : equation.arguments = [.var "state", .var "command"] := by decide +kernel

private theorem shape : equation.body = .expression [.symbol "case", .expression [.var "state", .var "command"],
    .expression (cases.map fun row => .expression [row.1, row.2])] := by decide +kernel

private theorem cases_shape : cases = [
    (.expression [listValue [.symbol "MM0:SpecificationState", theoryExpression, .var "pending"],
      .expression [.symbol "MM0:SharedTheorem", .var "local", .var "index", declarationExpression,
        .var "dummies", .var "saved", .var "root"]], body),
    (.expression [.var "other", .var "ordinary"],
      .expression [.symbol "mm0:spec-step", .var "other", .var "ordinary"])] := by decide +kernel

private theorem selected (spaces : Spaces) (pending : List SpecificationEntry) (command : Command) :
    SpaceSemantics.selectCase (environment spaces pending command)
      (.expression [stateValue spaces (pendingValue pending), commandValue command]) cases =
      some (boundEnvironment spaces pending command, body) := by
  simp [cases_shape, theoryExpression, declarationExpression, SpaceSemantics.selectCase,
    SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
    environment, boundEnvironment, stateValue, theoryValue, commandValue, listValue,
    TheoremInstantiation.declarationValue]

private theorem body_shape : body = .expression [.symbol "let", .var "shape", admissionExpression, shapeBody] := by
  decide +kernel
private theorem shape_body_shape : shapeBody = .expression [.symbol "let", .var "next",
    .expression [.symbol "mm0:spec-pending", .var "local", .var "pending", .var "shape"], nextBody] := by
  decide +kernel
private theorem next_body_shape : nextBody = .expression [.symbol "case", .var "next",
    .expression (nextCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem next_cases_shape : nextCases =
    [(.expression [.symbol "Some", .var "remaining"], permittedBody), (.symbol "None", .symbol "None"),
      (.var "malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem permitted_shape : permittedBody = .expression [.symbol "if",
    .expression [.symbol "mm0:admission-fresh", .var "thms", .var "index"], formedBody, .symbol "None"] := by
  decide +kernel
private theorem formed_shape : formedBody = .expression [.symbol "if",
    .expression [.symbol "mm0:form-theorem", .var "sorts", .var "terms", declarationExpression],
    dummiesBody, .symbol "None"] := by decide +kernel
private theorem dummies_shape : dummiesBody = .expression [.symbol "if",
    .expression [.symbol "mm0:form-dummies", .var "sorts", .var "dummies"], sharingBody, .symbol "None"] := by
  decide +kernel
private theorem sharing_shape : sharingBody = .expression [.symbol "let", .var "extra",
    .expression [.symbol "mm0:dummy-context", .var "dummies"], contextBody] := by decide +kernel
private theorem context_shape : contextBody = .expression [.symbol "let", .var "ctx",
    .expression [.symbol "mm0:list-append", .var "args", .var "extra"], checkedBody] := by decide +kernel
private theorem checked_shape : checkedBody = .expression [.symbol "if",
    .expression [.symbol "mm0:shared-proof", .var "terms", .var "defs", .var "thms", .var "ctx",
      .var "hyps", .var "saved", .var "root", .var "claim"], publishedBody, .symbol "None"] := by decide +kernel
private theorem published_shape : publishedBody = .expression [.symbol "let", .var "published",
    .expression [.symbol "mm0:admission-publish", theoryExpression, .var "shape"],
    .expression [.symbol "mm0:spec-admitted", .var "published", .var "remaining"]] := by decide +kernel

private theorem declaration_constructor_returns (bindings : Subst) (before : State) (declaration : TheoremDecl)
    (args : applySubst bindings (.var "args") = Data.context declaration.arguments)
    (hyps : applySubst bindings (.var "hyps") = ListSubstitution.expressionsValue declaration.hypotheses)
    (claim : applySubst bindings (.var "claim") = Data.preterm declaration.conclusion) :
    PureReturns program bindings before declarationExpression before
      (TheoremInstantiation.declarationValue declaration) := by
  apply unary_constructor_of_returns program bindings before before "MM0:L" _ _ list_is_data_constructor (by decide)
  simpa [declarationExpression, TheoremInstantiation.declarationValue, args, hyps, claim, listValue] using
    constructor_variables_return program bindings before "MM0:Theorem" ["args", "hyps", "claim"]
      (by decide +kernel) (by decide)

private theorem admission_constructor_returns (spaces : Spaces) (pending : List SpecificationEntry)
    (command : Command) (before : State) :
    PureReturns program (boundEnvironment spaces pending command) before admissionExpression before
      (admissionValue command.admission) := by
  let bindings := boundEnvironment spaces pending command
  apply unary_constructor_of_returns program bindings before before "MM0:L" _ _ list_is_data_constructor (by decide)
  apply data_call_returns program bindings before before "MM0:AdmitTheorem"
    [.var "index", declarationExpression, .var "dummies", .var "root"] _ (by decide +kernel) _ (by decide)
  apply evaluated_argument_returns program bindings before before before .data (.symbol "MM0:AdmitTheorem")
    (.symbol "MM0:AdmitTheorem") _ _ [] 0 rfl (symbol_returns program bindings before _)
  apply evaluated_argument_returns program bindings before before before .data (.var "index")
    (natural command.index) _ _ _ 1 rfl (variable_returns program bindings before _)
  apply evaluated_argument_returns program bindings before before before .data declarationExpression
    (TheoremInstantiation.declarationValue command.declaration) _ _ _ 2 rfl
    (declaration_constructor_returns bindings before command.declaration rfl rfl rfl)
  apply evaluated_argument_returns program bindings before before before .data (.var "dummies")
    (Support.indicesValue command.dummies) _ _ _ 3 rfl (variable_returns program bindings before _)
  apply evaluated_argument_returns program bindings before before before .data (.var "root")
    (Proof.witnessValue command.root) _ _ _ 4 rfl (variable_returns program bindings before _)
  simpa [bindings, admissionValue, Command.admission, listValue] using
    data_arguments_values_return program bindings before
      [.symbol "MM0:AdmitTheorem", natural command.index, TheoremInstantiation.declarationValue command.declaration,
        Support.indicesValue command.dummies, Proof.witnessValue command.root] 5

private theorem clause (spaces : Spaces) (pending : List SpecificationEntry) (command : Command) :
    clauses program "mm0:service-step" [stateValue spaces (pendingValue pending), commandValue command] =
      [.evaluate (environment spaces pending command) equation.body] := by
  rw [clauses_use_only_the_named_equations, unique]
  simp [formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, matchAtom,
    Subst.lookup, environment]

def Call (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State) (command : Command)
    (before after : State) (result : Option Kernel.SpecificationAdmission.State) : Prop :=
  ∀ bindings stateName commandName,
    applySubst bindings (.var stateName) = stateValue spaces (pendingValue logical.pending) →
    applySubst bindings (.var commandName) = commandValue command →
    PureReturns program bindings before (.expression [.symbol "mm0:service-step", .var stateName, .var commandName])
      after (SpecificationStep.resultValue spaces result)

private theorem call_of_body (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State) (command : Command)
    (before after : State) (result : Option Kernel.SpecificationAdmission.State)
    (computed : PureReturns program (boundEnvironment spaces logical.pending command) before body after
      (SpecificationStep.resultValue spaces result)) : Call spaces logical command before after result := by
  have top : PureReturns program (environment spaces logical.pending command) before equation.body after
      (SpecificationStep.resultValue spaces result) := by
    rw [shape]
    let bindings := environment spaces logical.pending command
    apply case_returns program bindings (boundEnvironment spaces logical.pending command) before before after
      (.expression [.var "state", .var "command"]) (.expression [stateValue spaces (pendingValue logical.pending),
        commandValue command]) body _ _ cases (read_cases_encoded _) _ (selected spaces logical.pending command) computed
    simpa [bindings, environment, applySubst, Subst.lookup] using tuple_variables_return program bindings before ["state", "command"]
  intro bindings stateName commandName capturedState capturedCommand
  apply authored_variable_call_returns program bindings (environment spaces logical.pending command) before after
    "mm0:service-step" [stateName, commandName] equation.body _ (by decide) (by decide) (by decide +kernel) _ top (by decide)
  simpa [capturedState, capturedCommand] using clause spaces logical.pending command


private theorem proof_independent {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before : State} (input : Input spaces logical before) (declaration : TheoremDecl) :
    ProofStore.Independent (tables spaces logical.theory declaration input.ready) := by
  have separated := input.ready.separate
  simp [Spaces.handles] at separated
  refine ⟨?_, ?_, ?_, rfl⟩ <;>
    simp only [tables, AdmissionChecks.proofTables] <;> tauto

private theorem sharing_input {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before : State} (input : Input spaces logical before) (declaration : TheoremDecl) :
    Sharing.Input (tables spaces logical.theory declaration input.ready) before := by
  refine ⟨input.ready.terms, input.ready.definitions, input.ready.theorems, ?_,
    input.proofCell, input.proofRows, proof_independent input declaration⟩
  simpa only [tables, AdmissionChecks.proofTables, input.ready.term_signature] using input.ready.cache

private theorem cache_rows {spaces : Spaces} {theory : Theory} {before : State}
    (ready : Ready spaces theory before) :
    ∃ rows, before.read spaces.cache = some rows ∧ Effects.RowsHaveArity 4 rows := by
  obtain ⟨_, rows, allocated, valid⟩ := ready.cache
  exact ⟨rows, allocated, valid.rows⟩

private theorem Input.after_frame {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before after : State} {bound : Nat} (input : Input spaces logical before)
    (frame : InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before after)
    (cache : InferenceCache.Ready logical.theory.termSignature (tableValue spaces.terms) spaces.cache after) :
    Input spaces logical after := by
  refine ⟨input.ready.after_frame frame cache, ?_, ?_⟩
  · rw [frame.cells]; exact input.proofCell
  · obtain ⟨rows, allocated, shaped⟩ := input.proofRows
    exact ⟨rows, (frame.other spaces.proofs input.ready.separate_proof).trans allocated, shaped⟩

private theorem Input.after_sharing {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before after : State} {declaration : TheoremDecl} {values : List Kernel.Preterm}
    (input : Input spaces logical before)
    (ready : Proof.Ready { tables spaces logical.theory declaration input.ready with values := values } after)
    (others : ∀ handle, handle ≠ spaces.cache → handle ≠ spaces.proofs → after.read handle = before.read handle)
    (cells : after.cells = before.cells) : Input spaces logical after := by
  have separated := input.ready.separate
  simp [Spaces.handles] at separated
  have tableReady : TableReady spaces logical.theory after := by
    refine ⟨?_, ready.terms, ready.definitions, ready.theorems, input.ready.uniqueSorts,
      input.ready.uniqueTerms, input.ready.uniqueDefinitions, input.ready.uniqueTheorems, input.ready.separate⟩
    rw [others spaces.sorts input.ready.separate_sort (by tauto)]
    exact input.ready.sorts
  refine ⟨⟨tableReady, ?_⟩, ?_, ?_⟩
  · simpa only [tables, AdmissionChecks.proofTables, input.ready.term_signature] using ready.cache
  · rw [cells]; exact input.proofCell
  · exact ⟨Store.rows (Store.enumerate (values.map Data.preterm)), ready.vector_hypotheses rfl,
      Store.rows_have_arity _⟩

private theorem refused_frame {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State} {command : Command}
    {before after : State} (input : Input spaces logical after) (cells : after.cells = before.cells)
    (others : ∀ handle, handle ≠ spaces.cache → handle ≠ spaces.proofs → after.read handle = before.read handle)
    (pendingRefused : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = none → after = before) :
    EffectFrame spaces logical command before after none := by
  have separated := input.ready.separate
  simp [Spaces.handles] at separated
  exact ⟨input.ready.toTableReady, input.ready.cache, cache_rows input.ready, input.proofCell, input.proofRows,
    cells, fun handle notCache notProofs _ => others handle notCache notProofs,
    fun _ => others spaces.theorems input.ready.separate_theorem (by tauto), pendingRefused⟩

/-- Accepted sharing retains every submitted initializer witness and the same
root. Computed saved conclusions respect the supplied optional expectations. -/
theorem checked_retains_shared {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before : State} (ready : Ready spaces logical.theory before)
    (checked : Sharing.Checked (Admission.proofContext command.declaration command.dummies)
      command.root command.declaration.conclusion (tables spaces logical.theory command.declaration ready) command.saved) :
    ∃ saved,
      Kernel.SharedProof.Checks logical.theory command.declaration command.dummies ⟨saved, command.root⟩ ∧
      List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
        (entry.expected = none ∨ entry.expected = some pair.1)) command.saved saved := by
  obtain ⟨saved, initializers, root, retained⟩ := checked.retains_witnesses
  refine ⟨saved, ⟨?_, ?_⟩, retained⟩
  · simpa only [tables, AdmissionChecks.proofTables, ready.term_signature, ready.definition_signature,
      ready.theorem_signature] using initializers
  · apply (Kernel.ProofWitness.check_iff _ _ _ _ _ _ _).mpr
    simpa only [tables, AdmissionChecks.proofTables, ready.term_signature, ready.definition_signature,
      ready.theorem_signature] using root

/-- Cut yields ordinary admission evidence only after the actual submitted
shared evidence has been checked. The runtime does not replace its root. -/
theorem checked_authorizes {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before : State} (ready : Ready spaces logical.theory before)
    (formed : Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies)
    (checked : Sharing.Checked (Admission.proofContext command.declaration command.dummies)
      command.root command.declaration.conclusion (tables spaces logical.theory command.declaration ready) command.saved) :
    ∃ ordinary, Admission.Authorized logical.theory
      (.theoremDecl command.index command.declaration command.dummies ordinary) := by
  obtain ⟨saved, given, _⟩ := checked_retains_shared ready checked
  exact formed.authorizes given

private theorem result_none_frame {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State} {command : Command}
    {before : State} (input : Input spaces logical before) : EffectFrame spaces logical command before before none :=
  refused_frame input rfl (fun _ _ _ => rfl) (fun _ => rfl)


def admittedState (logical : Kernel.SpecificationAdmission.State) (command : Command)
    (remaining : List SpecificationEntry) : Kernel.SpecificationAdmission.State :=
  ⟨Kernel.SharedProof.published logical.theory command.index command.declaration, remaining⟩

private def outcome (logical : Kernel.SpecificationAdmission.State) (command : Command)
    (remaining : List SpecificationEntry) (answer : Bool) : Option Kernel.SpecificationAdmission.State :=
  if answer then some (admittedState logical command remaining) else none

private def checkingEnvironment (spaces : Spaces) (pending remaining : List SpecificationEntry)
    (command : Command) : Subst :=
  ("ctx", Data.context (Admission.proofContext command.declaration command.dummies)) ::
    ("extra", Data.context (command.dummies.map Kernel.Binder.bound)) ::
      permittedEnvironment spaces pending remaining command

private theorem sharing_body_of_paths {before checked after : State} {spaces : Spaces}
    {logical : Kernel.SpecificationAdmission.State} {command : Command} {remaining : List SpecificationEntry}
    {ready : Ready spaces logical.theory before} {answer : Bool} {result : Atom}
    (shared : Sharing.Call (tables spaces logical.theory command.declaration ready)
      (Admission.proofContext command.declaration command.dummies) command.saved command.root
      command.declaration.conclusion before checked answer)
    (handled : PureReturns program (checkingEnvironment spaces logical.pending remaining command) checked
      (if answer then publishedBody else .symbol "None") after result) :
    PureReturns program (permittedEnvironment spaces logical.pending remaining command) before sharingBody after result := by
  rw [sharing_shape]
  let bindings := permittedEnvironment spaces logical.pending remaining command
  let extra := ("extra", Data.context (command.dummies.map Kernel.Binder.bound)) :: bindings
  let context := checkingEnvironment spaces logical.pending remaining command
  apply let_returns program bindings extra before before after (.var "extra") _ _
    (Data.context (command.dummies.map Kernel.Binder.bound)) _
  · exact BodyFormation.DummyContext.captured_returns bindings before command.dummies "dummies" rfl
  · simp [SpaceSemantics.matchValue, matchAtom, extra, bindings, permittedEnvironment,
      shapedEnvironment, boundEnvironment, environment, Subst.lookup]
  · rw [context_shape]
    apply let_returns program extra context before before after (.var "ctx") _ _
      (Data.context (Admission.proofContext command.declaration command.dummies)) _
    · simpa only [Data.context, Admission.proofContext, List.map_append, listValue] using
        ListAccess.append_captured_returns extra before (command.declaration.arguments.map Data.binder)
          ((command.dummies.map Kernel.Binder.bound).map Data.binder) "args" "extra" rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, context, checkingEnvironment, extra, bindings,
        permittedEnvironment, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
    · rw [checked_shape]
      apply if_returns program context before checked after _ (boolean answer) _ _ result
      · exact shared context "terms" "defs" "thms" "ctx" "hyps" "saved" "root" "claim"
          rfl rfl rfl rfl rfl rfl rfl rfl
      · cases answer <;> simpa [boolean, context] using handled

private theorem publication_body_of_paths {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {remaining : List SpecificationEntry} {before after : State}
    (written : AdmissionPublication.Writes spaces command.admission before after) :
    PureReturns program (checkingEnvironment spaces logical.pending remaining command) before publishedBody after
      (SpecificationStep.resultValue spaces (some (admittedState logical command remaining))) := by
  rw [published_shape]
  let bindings := checkingEnvironment spaces logical.pending remaining command
  let published := ("published", optionValue (some (theoryValue spaces))) :: bindings
  apply let_returns program bindings published before after after (.var "published") _ _
    (optionValue (some (theoryValue spaces))) _
  · exact AdmissionPublication.atom_captured_returns spaces command.admission before after written bindings
      theoryExpression (.var "shape") rfl rfl
  · simp [SpaceSemantics.matchValue, matchAtom, published, bindings, checkingEnvironment,
      permittedEnvironment, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
  · simpa only [admittedState, Option.map_some] using
      SpecificationStep.admitted_captured_returns published after spaces
        (some (Kernel.SharedProof.published logical.theory command.index command.declaration)) remaining
        "published" "remaining" rfl rfl

private theorem formation_iff {theory : Theory} {command : Command} :
    Kernel.SharedProof.Formation theory command.index command.declaration command.dummies ↔
      (theory.theoremSignature command.index).isNone = true ∧
      Kernel.TheoremDecl.check theory.sortSignature theory.termSignature command.declaration = true ∧
      Kernel.Definition.checkDummySorts theory.sortSignature command.dummies = true := by
  simp only [Option.isNone_iff_eq_none, Kernel.TheoremDecl.check_iff, Kernel.Definition.checkDummySorts_iff]
  exact ⟨fun formed => ⟨formed.fresh, formed.statement, formed.dummySorts⟩,
    fun given => ⟨given.1, given.2.1, given.2.2⟩⟩

private theorem prepend_frame {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before middle after : State} {bound : Nat}
    {remaining : List SpecificationEntry} {result : Option Kernel.SpecificationAdmission.State}
    (permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining)
    (first : InferenceCache.Frame spaces.cache (tableValue spaces.terms) bound before middle)
    (last : EffectFrame spaces logical command middle after result)
    (notCache : spaces.theorems ≠ spaces.cache) :
    EffectFrame spaces logical command before after result := by
  exact ⟨last.tables, last.cache, last.cacheRows, last.proofCell, last.proofRows,
    last.cells.trans first.cells,
    fun handle nc np nt => (last.other handle nc np nt).trans (first.other handle nc),
    fun refused => (last.refused refused).trans (first.other spaces.theorems notCache),
    fun noPending => by rw [permitted] at noPending; cases noPending⟩

private theorem publication_frame {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before after : State} {remaining : List SpecificationEntry}
    (input : Input spaces logical before)
    (permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining)
    (formed : Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies)
    (checked : Sharing.Checked (Admission.proofContext command.declaration command.dummies)
      command.root command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved)
    (written : AdmissionPublication.Writes spaces command.admission before after) :
    EffectFrame spaces logical command before after (some (admittedState logical command remaining)) := by
  obtain ⟨ordinary, authorized⟩ := checked_authorizes input.ready formed checked
  let admission := Admission.theoremDecl command.index command.declaration command.dummies ordinary
  have transported : AdmissionPublication.Writes spaces admission before after := by
    simpa only [admission, Command.admission, AdmissionPublication.Writes] using written
  have newTables := AdmissionPublication.writes_tables spaces logical.theory admission before after
    input.ready.toTableReady authorized transported
  have frozen := AdmissionPublication.writes_frozen_cache spaces logical.theory command.admission before after input.ready written
  obtain ⟨cells, cacheRead, proofRead, others⟩ := AdmissionPublication.writes_frame spaces logical.theory
    command.admission before after input.ready.toTableReady written
  obtain ⟨cacheEntries, cacheAllocated, cacheShaped⟩ := cache_rows input.ready
  obtain ⟨proofEntries, proofAllocated, proofShaped⟩ := input.proofRows
  refine ⟨?_, frozen, ⟨cacheEntries, cacheRead.trans cacheAllocated, cacheShaped⟩, ?_,
    ⟨proofEntries, proofRead.trans proofAllocated, proofShaped⟩, cells, ?_, ?_, ?_⟩
  · simpa only [Option.getD_some, admittedState, admission, Admission.insert, Kernel.SharedProof.published] using newTables
  · rw [cells]; exact input.proofCell
  · intro handle _ _ notTheorems
    exact others handle (by simpa only [Command.admission, AdmissionPublication.targets,
      List.mem_singleton] using notTheorems)
  · intro impossible; cases impossible
  · intro noPending; rw [permitted] at noPending; cases noPending


private theorem sharing_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (remaining : List SpecificationEntry) (before : State) (input : Input spaces logical before)
    (permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining)
    (formed : Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies) :
    ∃ after answer,
      PureReturns program (permittedEnvironment spaces logical.pending remaining command) before sharingBody after
        (SpecificationStep.resultValue spaces (outcome logical command remaining answer)) ∧
      (Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
        command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved ↔
          answer = true) ∧
      EffectFrame spaces logical command before after (outcome logical command remaining answer) := by
  let proofTables := tables spaces logical.theory command.declaration input.ready
  let proofContext := Admission.proofContext command.declaration command.dummies
  have sharingInput := sharing_input input command.declaration
  obtain ⟨stored, allocated, shaped⟩ := sharingInput.allocated
  obtain ⟨checked, values, answer, called, proofReady, justified, others, cells⟩ :=
    Sharing.returns proofTables proofContext command.saved command.root command.declaration.conclusion
      before stored sharingInput.terms sharingInput.definitions sharingInput.theorems sharingInput.cache
      sharingInput.current allocated shaped sharingInput.independent
  have checkedInput : Input spaces logical checked := Input.after_sharing input proofReady others cells
  cases answer with
  | false =>
      refine ⟨checked, false, ?_, justified, ?_⟩
      · exact sharing_body_of_paths called (symbol_returns program _ checked "None")
      · exact refused_frame checkedInput cells others
          (fun noPending => by rw [permitted] at noPending; cases noPending)
  | true =>
      have checkedEvidence := justified.mpr rfl
      obtain ⟨after, _, written⟩ := AdmissionPublication.returns spaces logical.theory command.admission checked
        checkedInput.ready.toTableReady
      have frame := publication_frame checkedInput permitted formed checkedEvidence written
      refine ⟨after, true, ?_, justified, ?_⟩
      · exact sharing_body_of_paths called (publication_body_of_paths written)
      · refine ⟨frame.tables, frame.cache, frame.cacheRows, frame.proofCell, frame.proofRows,
          frame.cells.trans cells, ?_, ?_, ?_⟩
        · intro handle notCache notProofs notTheorems
          exact (frame.other handle notCache notProofs notTheorems).trans (others handle notCache notProofs)
        · intro impossible; cases impossible
        · intro noPending; rw [permitted] at noPending; cases noPending

private theorem permitted_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (remaining : List SpecificationEntry) (before : State) (input : Input spaces logical before)
    (permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining) :
    ∃ after answer,
      PureReturns program (permittedEnvironment spaces logical.pending remaining command) before permittedBody after
        (SpecificationStep.resultValue spaces (outcome logical command remaining answer)) ∧
      (Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
        Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
          command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved ↔
            answer = true) ∧
      EffectFrame spaces logical command before after (outcome logical command remaining answer) := by
  let bindings := permittedEnvironment spaces logical.pending remaining command
  have freshness : PureReturns program bindings before
      (.expression [.symbol "mm0:admission-fresh", .var "thms", .var "index"]) before
      (boolean (logical.theory.theoremSignature command.index).isNone) := by
    have computed := AdmissionChecks.fresh_captured_returns TheoremInstantiation.declarationValue bindings before
      spaces.theorems logical.theory.theorems.reverse command.index "thms" "index"
      (AdmissionChecks.uniqueKeys_reverse input.ready.uniqueTheorems) input.ready.theorems rfl rfl
    simpa only [AdmissionChecks.lookup_reverse _ input.ready.uniqueTheorems, Theory.theoremSignature] using computed
  cases fresh : (logical.theory.theoremSignature command.index).isNone with
  | false =>
      refine ⟨before, false, ?_, ?_, result_none_frame input⟩
      · rw [permitted_shape]
        apply if_returns program bindings before before before _ (boolean false) _ _ _
        · simpa only [fresh] using freshness
        · exact symbol_returns program bindings before "None"
      · simp [formation_iff, fresh]
  | true =>
      obtain ⟨formed, formationCall, cacheFormed, frameFormed⟩ := TheoremFormation.atom_captured_returns
        spaces.sorts spaces.terms spaces.cache logical.theory.sorts.reverse logical.theory.terms.reverse
        (AdmissionChecks.uniqueKeys_reverse input.ready.uniqueSorts) (AdmissionChecks.uniqueKeys_reverse input.ready.uniqueTerms)
        input.ready.separate_sort input.ready.separate_term command.declaration before input.ready.sorts input.ready.terms
        (by simpa only [input.ready.term_signature] using input.ready.cache)
      have cacheFormedCurrent : InferenceCache.Ready logical.theory.termSignature (tableValue spaces.terms) spaces.cache formed := by
        simpa only [input.ready.term_signature] using cacheFormed
      have formedInput := input.after_frame frameFormed cacheFormedCurrent
      have formation : PureReturns program bindings before
          (.expression [.symbol "mm0:form-theorem", .var "sorts", .var "terms", declarationExpression]) formed
          (boolean (Kernel.TheoremDecl.check logical.theory.sortSignature logical.theory.termSignature command.declaration)) := by
        have computed := formationCall bindings (.var "sorts") (.var "terms") declarationExpression rfl rfl rfl
        simpa only [input.ready.sort_signature, input.ready.term_signature] using computed
      cases statement : Kernel.TheoremDecl.check logical.theory.sortSignature logical.theory.termSignature command.declaration with
      | false =>
          refine ⟨formed, false, ?_, ?_, ?_⟩
          · rw [permitted_shape]
            apply if_returns program bindings before before formed _ (boolean true) _ _ _
            · simpa only [fresh] using freshness
            · rw [formed_shape]
              apply if_returns program bindings before formed formed _ (boolean false) _ _ _
              · simpa only [statement] using formation
              · exact symbol_returns program bindings formed "None"
          · simp [formation_iff, statement]
          · exact prepend_frame permitted frameFormed (result_none_frame formedInput) input.ready.separate_theorem
      | true =>
          have dummy : PureReturns program bindings formed
              (.expression [.symbol "mm0:form-dummies", .var "sorts", .var "dummies"]) formed
              (boolean (Kernel.Definition.checkDummySorts logical.theory.sortSignature command.dummies)) := by
            have computed := DummyFormation.captured_returns bindings formed spaces.sorts logical.theory.sorts.reverse
              command.dummies "sorts" "dummies" (AdmissionChecks.uniqueKeys_reverse input.ready.uniqueSorts)
              formedInput.ready.sorts rfl rfl
            simpa only [input.ready.sort_signature] using computed
          cases dummies : Kernel.Definition.checkDummySorts logical.theory.sortSignature command.dummies with
          | false =>
              refine ⟨formed, false, ?_, ?_, ?_⟩
              · rw [permitted_shape]
                apply if_returns program bindings before before formed _ (boolean true) _ _ _
                · simpa only [fresh] using freshness
                · rw [formed_shape]
                  apply if_returns program bindings before formed formed _ (boolean true) _ _ _
                  · simpa only [statement] using formation
                  · rw [dummies_shape]
                    apply if_returns program bindings formed formed formed _ (boolean false) _ _ _
                    · simpa only [dummies] using dummy
                    · exact symbol_returns program bindings formed "None"
              · simp [formation_iff, dummies]
              · exact prepend_frame permitted frameFormed (result_none_frame formedInput) input.ready.separate_theorem
          | true =>
              have formedEvidence : Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies :=
                formation_iff.mpr ⟨fresh, statement, dummies⟩
              obtain ⟨after, answer, shared, justified, frame⟩ := sharing_returns spaces logical command remaining formed
                formedInput permitted formedEvidence
              refine ⟨after, answer, ?_, ?_, prepend_frame permitted frameFormed frame input.ready.separate_theorem⟩
              · rw [permitted_shape]
                apply if_returns program bindings before before after _ (boolean true) _ _ _
                · simpa only [fresh] using freshness
                · rw [formed_shape]
                  apply if_returns program bindings before formed after _ (boolean true) _ _ _
                  · simpa only [statement] using formation
                  · rw [dummies_shape]
                    apply if_returns program bindings formed formed after _ (boolean true) _ _ _
                    · simpa only [dummies] using dummy
                    · exact shared
              · exact ⟨fun given => justified.mp given.2, fun given => ⟨formedEvidence, justified.mpr given⟩⟩


private theorem pending_none_body_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State)
    (refused : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = none) :
    PureReturns program (boundEnvironment spaces logical.pending command) before body before (.symbol "None") := by
  rw [body_shape]
  let bindings := boundEnvironment spaces logical.pending command
  let shaped := shapedEnvironment spaces logical.pending command
  let next := ("next", .symbol "None") :: shaped
  apply let_returns program bindings shaped before before before (.var "shape") _ _ (admissionValue command.admission) _
  · exact admission_constructor_returns spaces logical.pending command before
  · simp [SpaceSemantics.matchValue, matchAtom, shaped, bindings, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
  · rw [shape_body_shape]
    apply let_returns program shaped next before before before (.var "next") _ _ (.symbol "None") _
    · simpa only [refused, Option.map_none, optionValue] using
        SpecificationMatching.pending_captured_returns shaped before logical.pending command.proofDeclaration
          "local" "pending" "shape" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, next, shaped, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
    · rw [next_body_shape]
      apply case_returns program next next before before before (.var "next") (.symbol "None") (.symbol "None") _ _
        nextCases (read_cases_encoded _) (variable_returns program next before "next") _
        (symbol_returns program next before "None")
      simp [next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom, next,
        shaped, shapedEnvironment, boundEnvironment, environment]

private theorem pending_some_body_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (remaining : List SpecificationEntry) (before after : State) (result : Atom)
    (permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining)
    (continued : PureReturns program (permittedEnvironment spaces logical.pending remaining command)
      before permittedBody after result) :
    PureReturns program (boundEnvironment spaces logical.pending command) before body after result := by
  rw [body_shape]
  let bindings := boundEnvironment spaces logical.pending command
  let shaped := shapedEnvironment spaces logical.pending command
  let next := ("next", optionValue (some (pendingValue remaining))) :: shaped
  apply let_returns program bindings shaped before before after (.var "shape") _ _ (admissionValue command.admission) _
  · exact admission_constructor_returns spaces logical.pending command before
  · simp [SpaceSemantics.matchValue, matchAtom, shaped, bindings, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
  · rw [shape_body_shape]
    apply let_returns program shaped next before before after (.var "next") _ _ (optionValue (some (pendingValue remaining))) _
    · simpa only [permitted, Option.map_some] using
        SpecificationMatching.pending_captured_returns shaped before logical.pending command.proofDeclaration
          "local" "pending" "shape" rfl rfl rfl
    · simp [SpaceSemantics.matchValue, matchAtom, next, shaped, shapedEnvironment, boundEnvironment, environment, Subst.lookup]
    · rw [next_body_shape]
      apply case_returns program next (permittedEnvironment spaces logical.pending remaining command)
        before before after (.var "next") (optionValue (some (pendingValue remaining))) permittedBody _ _
        nextCases (read_cases_encoded _) (variable_returns program next before "next") _ continued
      simp [next_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, next, shaped, permittedEnvironment,
        shapedEnvironment, boundEnvironment, environment, Subst.lookup, optionValue]

/-- Every fixed submitted command completes with either its checked publication
or a refusal. The Boolean is obtained from the source execution, not another
saved-proof traversal. All private-store obligations are earned postconditions. -/
theorem captured_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (input : Input spaces logical before) :
    ∃ after result,
      Call spaces logical command before after result ∧ EffectFrame spaces logical command before after result ∧
      (∀ next, result = some next ↔
        ∃ remaining, next = admittedState logical command remaining ∧
          Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
          Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
          Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
            command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved) ∧
      (result = none ↔ ¬ Accepted spaces logical command input.ready) := by
  cases permitted : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration with
  | none =>
      refine ⟨before, none, call_of_body spaces logical command before before none
        (pending_none_body_returns spaces logical command before permitted), result_none_frame input, ?_, ?_⟩
      · intro next
        constructor
        · intro impossible; cases impossible
        · rintro ⟨_, _, impossible, _, _⟩; cases impossible
      · simp [Accepted, permitted]
  | some remaining =>
      obtain ⟨after, answer, continued, justified, frame⟩ := permitted_returns spaces logical command remaining before input permitted
      refine ⟨after, outcome logical command remaining answer,
        call_of_body spaces logical command before after _
          (pending_some_body_returns spaces logical command remaining before after _ permitted continued), frame, ?_, ?_⟩
      · intro next
        cases answer with
        | false =>
            simp only [outcome, Bool.false_eq_true, ↓reduceIte]
            constructor
            · intro impossible; cases impossible
            · rintro ⟨_, _, _, formed, checked⟩
              have impossible := justified.mp ⟨formed, checked⟩
              cases impossible
        | true =>
            simp only [outcome, ↓reduceIte, Option.some.injEq]
            constructor
            · intro same
              subst next
              exact ⟨remaining, rfl, rfl, (justified.mpr rfl).1, (justified.mpr rfl).2⟩
            · rintro ⟨claimed, same, pending, _, _⟩
              subst claimed
              exact same.symm
      · have acceptance : Accepted spaces logical command input.ready ↔ answer = true := by
          exact ⟨fun given => justified.mp ⟨given.2.1, given.2.2⟩,
            fun given => ⟨⟨remaining, permitted⟩, (justified.mpr given).1, (justified.mpr given).2⟩⟩
        cases answer <;> simp_all [outcome]



def requestConfiguration (before : State) (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) : Configuration :=
  { state := before, control := .evaluate (environment spaces logical.pending command)
      (.expression [.symbol "mm0:service-step", .var "state", .var "command"]) }

/-- More fuel preserves the complete response and every earned private-store
and table invariant for this same fixed submission. -/
theorem sufficient_fuel (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (input : Input spaces logical before) :
    ∃ after result fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before spaces logical command) =
        .complete after [SpecificationStep.resultValue spaces result] [] []) ∧
      EffectFrame spaces logical command before after result ∧
      (∀ next, result = some next ↔
        ∃ remaining, next = admittedState logical command remaining ∧
          Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
          Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
          Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
            command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved) ∧
      (result = none ↔ ¬ Accepted spaces logical command input.ready) := by
  obtain ⟨after, result, called, frame, successful, refused⟩ := captured_returns spaces logical command before input
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program (environment spaces logical.pending command)
    before after _ _ (called (environment spaces logical.pending command) "state" "command" rfl rfl)
  exact ⟨after, result, fuel, fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed,
    frame, successful, refused⟩

private theorem outcome_value_injective (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (first second : List SpecificationEntry) :
    SpecificationStep.resultValue spaces (some (admittedState logical command first)) =
      SpecificationStep.resultValue spaces (some (admittedState logical command second)) ↔ first = second := by
  simp [SpecificationStep.resultValue, admittedState, optionValue, stateValue, listValue,
    SpecificationMatching.pendingValue_injective.eq_iff]

/-- Exact acceptance for a particular pending result. Native table capabilities
are paired with the independent logical publication, rather than interpreted
as arbitrary theory snapshots. -/
theorem source_advances_iff (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (remaining : List SpecificationEntry) (before : State) (input : Input spaces logical before) :
    (∃ after fuel, run program fuel (requestConfiguration before spaces logical command) =
      .complete after [SpecificationStep.resultValue spaces (some (admittedState logical command remaining))] [] []) ↔
      Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
      Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
        command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved := by
  obtain ⟨reference, result, referenceFuel, completed, _, successful, _⟩ := sufficient_fuel spaces logical command before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have sameAnswer := List.singleton_inj.mp same.2.1
    cases result with
    | none => simp [SpecificationStep.resultValue, optionValue] at sameAnswer
    | some next =>
        obtain ⟨actual, nextSame, pending, formed, shared⟩ := (successful next).mp rfl
        subst next
        have equal := (outcome_value_injective spaces logical command actual remaining).mp sameAnswer
        subst actual
        exact ⟨pending, formed, shared⟩
  · rintro ⟨pending, formed, shared⟩
    have answer := (successful (admittedState logical command remaining)).mpr ⟨remaining, rfl, pending, formed, shared⟩
    exact ⟨reference, referenceFuel, by simpa only [answer] using referenceCompleted⟩

/-- The actual shared service advances exactly for the permitted, independently
formed, fixed submitted sharing judgment. -/
theorem accepted_iff_source_advances (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (input : Input spaces logical before) :
    Accepted spaces logical command input.ready ↔
      ∃ after remaining fuel, run program fuel (requestConfiguration before spaces logical command) =
        .complete after [SpecificationStep.resultValue spaces (some (admittedState logical command remaining))] [] [] := by
  constructor
  · rintro ⟨⟨remaining, pending⟩, formed, shared⟩
    obtain ⟨after, fuel, completed⟩ := (source_advances_iff spaces logical command remaining before input).mpr ⟨pending, formed, shared⟩
    exact ⟨after, remaining, fuel, completed⟩
  · rintro ⟨after, remaining, fuel, completed⟩
    obtain ⟨pending, formed, shared⟩ := (source_advances_iff spaces logical command remaining before input).mp ⟨after, fuel, completed⟩
    exact ⟨⟨remaining, pending⟩, formed, shared⟩

/-- A different proof of the theorem never repairs a refused submitted shared
root, initializer, or expected conclusion. -/
theorem refused_iff_source_none (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (input : Input spaces logical before) :
    ¬ Accepted spaces logical command input.ready ↔
      ∃ after fuel, run program fuel (requestConfiguration before spaces logical command) = .complete after [.symbol "None"] [] [] := by
  obtain ⟨reference, result, referenceFuel, completed, _, _, refused⟩ := sufficient_fuel spaces logical command before input
  have referenceCompleted := completed 0
  simp only [Nat.add_zero] at referenceCompleted
  constructor
  · intro rejected
    exact ⟨reference, referenceFuel, by simpa only [refused.mpr rejected, SpecificationStep.resultValue, Option.map_none, optionValue] using referenceCompleted⟩
  · rintro ⟨after, fuel, returned⟩
    have same := completed_result_unique program referenceFuel fuel _ reference after _ [] [] _ [] [] referenceCompleted returned
    have sameAnswer := List.singleton_inj.mp same.2.1
    apply refused.mp
    cases result with
    | none => rfl
    | some next => simp [SpecificationStep.resultValue, optionValue] at sameAnswer

theorem accepted_iff_gslt_path (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (input : Input spaces logical before) :
    Accepted spaces logical command input.ready ↔
      ∃ after remaining, (theory program).MultiStep (requestConfiguration before spaces logical command)
        (finished after [SpecificationStep.resultValue spaces (some (admittedState logical command remaining))] [] []) := by
  rw [accepted_iff_source_advances spaces logical command before input]
  constructor
  · rintro ⟨after, remaining, fuel, completed⟩
    exact ⟨after, remaining, (completed_run_iff_path program _ after _ [] []).mp ⟨fuel, completed⟩⟩
  · rintro ⟨after, remaining, path⟩
    obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ after _ [] []).mpr path
    exact ⟨after, remaining, fuel, completed⟩

/-- Frames describe any observed complete service run, not just the execution
constructed by the universal correspondence proof. -/
theorem completed_frame (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before after : State) (input : Input spaces logical before)
    (fuel : Nat) (answers unread printed : List Atom)
    (completed : run program fuel (requestConfiguration before spaces logical command) = .complete after answers unread printed) :
    ∃ result, answers = [SpecificationStep.resultValue spaces result] ∧ unread = [] ∧ printed = [] ∧
      EffectFrame spaces logical command before after result ∧ (result = none ↔ ¬ Accepted spaces logical command input.ready) ∧
      (∀ next, result = some next ↔
        ∃ remaining, next = admittedState logical command remaining ∧
          Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
          Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
          Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
            command.declaration.conclusion (tables spaces logical.theory command.declaration input.ready) command.saved) := by
  obtain ⟨reference, result, referenceFuel, returned, frame, successful, refused⟩ := sufficient_fuel spaces logical command before input
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    reference after _ [] [] answers unread printed referenceCompleted completed
  subst after
  exact ⟨result, sameAnswers.symm, sameUnread.symm, samePrinted.symm, frame, refused, successful⟩

private theorem pending_witness_irrelevant (pending : List SpecificationEntry) (command : Command) (ordinary : ProofWitness) :
    Kernel.SpecificationAdmission.pending? pending command.proofDeclaration =
      Kernel.SpecificationAdmission.pending? pending
        ⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩ := by
  cases localFlag : command.isLocal <;> cases pending with
  | nil => simp [Kernel.SpecificationAdmission.pending?, Command.proofDeclaration, Command.admission,
      localFlag, Kernel.ProofDeclaration.auxiliary]
  | cons expected rest =>
      cases expected <;> simp [Kernel.SpecificationAdmission.pending?, Command.proofDeclaration, Command.admission,
        localFlag, Kernel.ProofDeclaration.auxiliary, Kernel.SpecificationEntry.checkMatch]

/-- An accepted fixed sharing submission produces an ordinary logical history
step by cut. The existential witness is history evidence, not the runtime's
submitted root and not a condition used to accept the source command. -/
theorem Accepted.specification_step {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before : State} (ready : Ready spaces logical.theory before)
    (accepted : Accepted spaces logical command ready) :
    ∃ ordinary remaining,
      Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
      Kernel.SpecificationAdmission.Step logical
        ⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩
        (admittedState logical command remaining) := by
  obtain ⟨⟨remaining, pending⟩, formed, shared⟩ := accepted
  obtain ⟨ordinary, authorized⟩ := checked_authorizes ready formed shared
  refine ⟨ordinary, remaining, pending, (Kernel.SpecificationAdmission.step_eq_some_iff _ _ _).mp ?_⟩
  have permitted : Kernel.SpecificationAdmission.pending? logical.pending
      ⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩ = some remaining :=
    (pending_witness_irrelevant logical.pending command ordinary).symm.trans pending
  simp [Kernel.SpecificationAdmission.step?, permitted, Kernel.Theory.step?,
    (Admission.check_iff _ _).mpr authorized, Admission.insert, admittedState, Kernel.SharedProof.published]

/-- With no saved initializers, the service checks the same supplied ordinary
witness while retaining all specification and formation requirements. -/
theorem empty_saved_iff {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : Command} {before : State} (ready : Ready spaces logical.theory before) (empty : command.saved = []) :
    Accepted spaces logical command ready ↔
      (∃ remaining, Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining) ∧
      Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      Kernel.ProofWitness.Checks logical.theory.termSignature logical.theory.definitionSignature logical.theory.theoremSignature
        (Admission.proofContext command.declaration command.dummies) command.declaration.hypotheses command.root command.declaration.conclusion := by
  simp only [Accepted, empty, Sharing.checked_nil_iff, tables, AdmissionChecks.proofTables,
    ready.term_signature, ready.definition_signature, ready.theorem_signature]

/-- Every completed advancing source command retains its submitted witnesses,
optional expectations and root in the existing kernel sharing judgment. -/
theorem source_acceptance_retains_shared (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (remaining : List SpecificationEntry) (before after : State)
    (input : Input spaces logical before) (fuel : Nat)
    (accepted : run program fuel (requestConfiguration before spaces logical command) =
      .complete after [SpecificationStep.resultValue spaces (some (admittedState logical command remaining))] [] []) :
    Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      ∃ saved,
        Kernel.SharedProof.Checks logical.theory command.declaration command.dummies ⟨saved, command.root⟩ ∧
        List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
          (entry.expected = none ∨ entry.expected = some pair.1)) command.saved saved := by
  obtain ⟨_, formed, checked⟩ := (source_advances_iff spaces logical command remaining before input).mp ⟨after, fuel, accepted⟩
  exact ⟨formed, checked_retains_shared input.ready checked⟩


/-- Refused specification permission stops before freshness, formation or
vector initialization, even when those private spaces are not allocated. -/
theorem pending_refusal_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : Command) (before : State)
    (refused : Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = none) :
    Call spaces logical command before before none :=
  call_of_body spaces logical command before before none
    (pending_none_body_returns spaces logical command before refused)

namespace Controls

open Kernel

private def spaces : Spaces :=
  ⟨.privateSpace 0, .privateSpace 1, .privateSpace 2, .privateSpace 3, .privateSpace 4, .privateSpace 5⟩
private def info : SortInfo := { provable := true }
private def primitive : TermDecl := ⟨[], 0, ∅⟩
private def statement : TheoremDecl := ⟨[], [], .term 1⟩
private def declarations : Theory :=
  { sorts := [(0, info)], terms := [(2, primitive), (1, primitive)], theorems := [(10, statement)] }
private def logical : Kernel.SpecificationAdmission.State :=
  ⟨declarations, [.theoremDecl 12 statement]⟩
private def obsoleteRows : List Atom := Store.rows [(99, .symbol "obsolete")]
private def initial : State :=
  { core := []
    next := 6
    spaces := fun index =>
      if index = 1 then obsoleteRows
      else if index = 2 then SortFormation.rows declarations.sorts.reverse
      else if index = 3 then TableAccess.declarationRows declarations.terms.reverse
      else if index = 5 then Proof.theoremRows declarations.theorems.reverse
      else []
    cells := fun name =>
      if name = InferenceCache.cell then some (Effects.handleValue spaces.cache)
      else if name = "mm0-proof-store" then some (Effects.handleValue spaces.proofs)
      else if name = "mm0-session" then some (optionValue (some (stateValue spaces (pendingValue logical.pending))))
      else none }

private theorem input : Input spaces logical initial := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide +kernel⟩, ?_⟩, ?_, ?_⟩
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, declarations, Unfolding.definitionRows, Store.rows, NamedSpaces.Store.read]
  · simp [initial, spaces, logical, NamedSpaces.Store.read]
  · intro key; by_cases same : 0 = key <;> simp [logical, declarations, same]
  · intro key
    by_cases two : 2 = key
    · subst key; decide +kernel
    · by_cases one : 1 = key
      · subst key; decide +kernel
      · simp [logical, declarations, two, one]
  · intro key; simp [logical, declarations]
  · intro key; by_cases same : 10 = key <;> simp [logical, declarations, same]
  · refine ⟨?_, [], ?_, InferenceCache.empty_valid _ _⟩ <;> simp [initial, spaces, NamedSpaces.Store.read]
  · simp [initial, spaces, InferenceCache.cell]
  · exact ⟨obsoleteRows, rfl, Store.rows_have_arity _⟩

private def submitted : Command :=
  ⟨false, 12, statement, [],
    [⟨some (.term 1), .theoremApp 10 [] []⟩, ⟨none, .hyp 0⟩], .hyp 1⟩

private theorem submitted_checked : Sharing.Checked (Admission.proofContext submitted.declaration submitted.dummies)
    submitted.root submitted.declaration.conclusion (tables spaces logical.theory submitted.declaration input.ready) submitted.saved := by
  apply Sharing.Checked.save (actual := .term 1)
  · apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
    decide +kernel
  · exact Or.inr rfl
  · apply Sharing.Checked.save (actual := .term 1)
    · apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
      decide +kernel
    · exact Or.inl rfl
    · apply Sharing.Checked.root
      apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
      decide +kernel

/-- The submitted root is invalid by itself in the original empty hypothesis
scope; its acceptance requires the actual checked saved prefix. -/
theorem submitted_root_needs_saved_prefix :
    ProofWitness.proof? declarations.termSignature declarations.definitionSignature declarations.theoremSignature
      [] [] submitted.root = none := by decide +kernel

/-- Two supplied initializers, including an absent expectation, are checked in
order and the actual root reuses the second materialized vector entry. -/
theorem nonempty_saved_source_accepts :
    ∃ after fuel, run program fuel (requestConfiguration initial spaces logical submitted) =
      .complete after [SpecificationStep.resultValue spaces (some (admittedState logical submitted []))] [] [] := by
  apply (source_advances_iff spaces logical submitted [] initial input).mpr
  refine ⟨rfl, formation_iff.mpr ⟨?_, ?_, ?_⟩, submitted_checked⟩
  all_goals decide +kernel

/-- The same frontend command form accepts an empty saved list and directly
checks its unchanged ordinary root. -/
theorem empty_saved_source_accepts :
    let ordinary : Command := { submitted with saved := [], root := .theoremApp 10 [] [] }
    ∃ after fuel, run program fuel (requestConfiguration initial spaces logical ordinary) =
      .complete after [SpecificationStep.resultValue spaces (some (admittedState logical ordinary []))] [] [] := by
  dsimp only
  apply (source_advances_iff spaces logical _ [] initial input).mpr
  refine ⟨rfl, formation_iff.mpr ⟨?_, ?_, ?_⟩, Sharing.Checked.root ?_⟩
  all_goals first
    | decide +kernel
    | (apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp; decide +kernel)

/-- A valid initializer cannot satisfy a different supplied expected conclusion,
even though the requested theorem itself has an available logical proof. -/
theorem wrong_expected_source_refuses :
    let wrong : Command := { submitted with saved := [⟨some (.term 2), .theoremApp 10 [] []⟩], root := .hyp 0 }
    ∃ after fuel, run program fuel (requestConfiguration initial spaces logical wrong) = .complete after [.symbol "None"] [] [] := by
  dsimp only
  apply (refused_iff_source_none spaces logical _ initial input).mp
  rintro ⟨_, _, checked⟩
  have acceptedPrefix := (Sharing.checked_cons_iff _ _ _ _ ⟨some (.term 2), .theoremApp 10 [] []⟩ [] (.term 1)
    (by decide +kernel)).mp checked
  have impossible : ¬ ((some (Preterm.term 2)) = none ∨ some (Preterm.term 2) = some (.term 1)) := by decide +kernel
  exact impossible acceptedPrefix.1

/-- The first saved initializer cannot reference its own future vector slot.
Absence of an expected conclusion still checks the supplied witness. -/
theorem future_reference_source_refuses :
    let future : Command := { submitted with saved := [⟨none, .hyp 0⟩], root := .hyp 0 }
    ∃ after fuel, run program fuel (requestConfiguration initial spaces logical future) = .complete after [.symbol "None"] [] [] := by
  dsimp only
  apply (refused_iff_source_none spaces logical _ initial input).mp
  rintro ⟨_, _, checked⟩
  exact Sharing.checked_cons_refused _ _ _ _ ⟨none, .hyp 0⟩ [] (by decide +kernel) checked

end Controls

end Mettapedia.Languages.MM0.MeTTa.SharedService
