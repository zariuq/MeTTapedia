import Mettapedia.Languages.MM0.MeTTa.Admission.SpecificationStep
import Mettapedia.Languages.MM0.MeTTa.Session.DeclarationScope
import Mettapedia.Languages.MM0.Upstream.Lean3ProofAdmission
import Mettapedia.Languages.MeTTa.PeTTa.UpstreamAgreement

/-!
# Physical session invariants and the retained MM0 driver

The driver owns six spaces and three state cells. Between declarations the
cache need only retain its four-field physical shape: the actual submit reset
earns coherence for the current theory before any declaration check. A failed
submit stores `None`; later submits and completion cannot reopen it.

The ordinary command branch below composes the existing specification checker.
Shared commands retain their separate supplied evidence and use the shared
service branch. Completion observes pending specification consumption without
changing the session cell.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SessionDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Kernel (Theory ProofDeclaration SpecificationEntry)
open SessionInitialization (Spaces stateValue theoryValue)
open SpecificationMatching (pendingValue declarationValue)
open AdmissionChecks (TableReady Ready)
open ListAccess (optionValue listValue)
open TableAccess (tableValue)

/-- A physical invariant between submissions. It does not assert that an
old cache remains coherent after publishing a new term declaration. -/
structure Live (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (store : State) : Prop where
  tables : TableReady spaces logical.theory store
  cacheCell : store.cells InferenceCache.cell = some (handleValue spaces.cache)
  proofCell : store.cells "mm0-proof-store" = some (handleValue spaces.proofs)
  sessionCell : store.cells "mm0-session" =
    some (SpecificationStep.resultValue spaces (some logical))
  cacheRows : ∃ rows, store.read spaces.cache = some rows ∧ Effects.RowsHaveArity 4 rows
  proofRows : ∃ rows, store.read spaces.proofs = some rows ∧ Effects.RowsHaveArity 2 rows

/-- Native session representation uses the already checked logical state;
the stopped case carries the actual sticky failure cell. -/
inductive Stored (spaces : Spaces) : Option Kernel.SpecificationAdmission.State → State → Prop where
  | active {logical : Kernel.SpecificationAdmission.State} {store : State} :
      Live spaces logical store → Stored spaces (some logical) store
  | stopped {store : State} :
      store.cells "mm0-session" = some (.symbol "None") → Stored spaces none store

theorem start_live (before : State) (specification : List SpecificationEntry) :
    Live (SessionInitialization.allocatedSpaces before) ⟨{}, specification⟩
      (SessionInitialization.startState before (pendingValue specification)) := by
  let spaces := SessionInitialization.allocatedSpaces before
  have cells := SessionInitialization.start_owns_cells before (pendingValue specification)
  refine ⟨(AdmissionChecks.start_ready before (pendingValue specification)).toTableReady,
    cells.1, cells.2.1, ?_, ?_, ?_⟩
  · simpa [SpecificationStep.resultValue, optionValue, SessionInitialization.sessionValue] using cells.2.2
  · refine ⟨[], ?_, ?_⟩
    · exact SessionInitialization.allocated_spaces_empty before (pendingValue specification) spaces.cache
        (by simp [spaces, SessionInitialization.Spaces.handles])
    · intro row impossible; cases impossible
  · refine ⟨[], ?_, ?_⟩
    · exact SessionInitialization.allocated_spaces_empty before (pendingValue specification) spaces.proofs
        (by simp [spaces, SessionInitialization.Spaces.handles])
    · intro row impossible; cases impossible

/-- Only reset emptiness and unchanged native tables are used to enter the
new checking scope. Validity of the preceding cache values is unnecessary. -/
theorem Live.ready_after_reset {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before checking : State} (live : Live spaces logical before)
    (empty : checking.read spaces.cache = some [])
    (others : ∀ handle, handle ≠ spaces.cache → checking.read handle = before.read handle)
    (cells : checking.cells = before.cells) : Ready spaces logical.theory checking := by
  refine ⟨live.tables.after_reads others, ?_⟩
  exact ⟨by rw [cells]; exact live.cacheCell, [], empty, InferenceCache.empty_valid _ _⟩

private def serviceEquation : SpaceSemantics.Equation :=
  serviceSource.program.equations[2]'(by decide +kernel)
private def serviceEnvironment (state command : Atom) : Subst := [("command", command), ("state", state)]
private def serviceCases : SpaceSemantics.Cases :=
  match serviceEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def sharedPattern : Atom := (serviceCases[0]'(by decide +kernel)).1

private theorem service_shape : serviceEquation.body =
    .expression [.symbol "case", .expression [.var "state", .var "command"],
      .expression (serviceCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem service_cases_shape : serviceCases =
    [(sharedPattern, (serviceCases[0]'(by decide +kernel)).2),
      (.expression [.var "other", .var "ordinary"],
        .expression [.symbol "mm0:spec-step", .var "other", .var "ordinary"])] := by decide +kernel
private theorem shared_pattern_shape : sharedPattern =
    .expression [listValue [.symbol "MM0:SpecificationState",
      listValue [.symbol "MM0:Theory", .var "sorts", .var "terms", .var "defs", .var "thms"], .var "pending"],
      .expression [.symbol "MM0:SharedTheorem", .var "local", .var "index",
        listValue [.symbol "MM0:Theorem", .var "args", .var "hyps", .var "claim"],
        .var "dummies", .var "saved", .var "root"]] := by decide +kernel
private theorem service_unique : program.equations.filter (fun row => row.head == "mm0:service-step") =
    [serviceEquation] := by decide +kernel
private theorem service_formals : serviceEquation.arguments = [.var "state", .var "command"] := by decide +kernel

private theorem ordinary_body_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before after : State)
    (computed : SpecificationStep.Call spaces logical declaration before after
      (Kernel.SpecificationAdmission.step? logical declaration)) :
    PureReturns program (serviceEnvironment (stateValue spaces (pendingValue logical.pending))
      (declarationValue declaration)) before serviceEquation.body after
      (SpecificationStep.resultValue spaces (Kernel.SpecificationAdmission.step? logical declaration)) := by
  rw [service_shape]
  let source := stateValue spaces (pendingValue logical.pending)
  let command := declarationValue declaration
  let bindings := serviceEnvironment source command
  let bound := ("ordinary", command) :: ("other", source) :: bindings
  apply case_returns program bindings bound before before after
    (.expression [.var "state", .var "command"]) (.expression [source, command])
    (.expression [.symbol "mm0:spec-step", .var "other", .var "ordinary"]) _ _
    serviceCases (read_cases_encoded _)
  · simpa [bindings, serviceEnvironment, applySubst, Subst.lookup, source, command] using
      tuple_variables_return program bindings before ["state", "command"]
  · rw [service_cases_shape, shared_pattern_shape]
    rcases declaration with ⟨admission, localFlag⟩
    cases admission <;>
      simp [source, command, declarationValue, stateValue, theoryValue, listValue,
        AdmissionChecks.admissionValue, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
        SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, bindings,
        serviceEnvironment, bound]
  · exact computed bound "other" "ordinary" rfl rfl

/-- The actual service's ordinary fallback reaches the existing specification
step, and supplies that child's physical publication/cache frame. -/
theorem ordinary_service_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (before : State) (ready : Ready spaces logical.theory before) :
    ∃ after, (∀ (bindings : Subst) (stateName commandName : String),
      applySubst bindings (.var stateName) = stateValue spaces (pendingValue logical.pending) →
      applySubst bindings (.var commandName) = declarationValue declaration →
      PureReturns program bindings before
        (.expression [.symbol "mm0:service-step", .var stateName, .var commandName]) after
        (SpecificationStep.resultValue spaces (Kernel.SpecificationAdmission.step? logical declaration))) ∧
      SpecificationStep.EffectFrame spaces logical declaration before after := by
  obtain ⟨after, computed, frame⟩ := SpecificationStep.captured_returns spaces logical declaration before ready
  refine ⟨after, ?_, frame⟩
  intro bindings stateName commandName capturedState capturedCommand
  apply authored_variable_call_returns program bindings
    (serviceEnvironment (stateValue spaces (pendingValue logical.pending)) (declarationValue declaration))
    before after "mm0:service-step" [stateName, commandName] serviceEquation.body _
    (by decide) (by decide) (by decide +kernel) _
    (ordinary_body_returns spaces logical declaration before after computed) (by decide)
  rw [clauses_use_only_the_named_equations, service_unique]
  simp [capturedState, capturedCommand, service_formals, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, serviceEnvironment]

private theorem tables_after_cell {spaces : Spaces} {logicalTheory : Theory} {store : State}
    (tables : TableReady spaces logicalTheory store) (name : String) (value : Atom) :
    TableReady spaces logicalTheory (store.putCell name value) :=
  tables.after_reads (fun _ _ => NamedSpaces.Store.cell_preserves_spaces _ _ _ _)

/-- A checked child's table/ownership/shape frame yields the driver's next
session representation after recording that exact returned option. -/
theorem stored_after_result {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    (result : Option Kernel.SpecificationAdmission.State) (checked : State)
    (tables : TableReady spaces (result.getD logical).theory checked)
    (cacheCell : checked.cells InferenceCache.cell = some (handleValue spaces.cache))
    (proofCell : checked.cells "mm0-proof-store" = some (handleValue spaces.proofs))
    (cacheRows : ∃ rows, checked.read spaces.cache = some rows ∧ Effects.RowsHaveArity 4 rows)
    (proofRows : ∃ rows, checked.read spaces.proofs = some rows ∧ Effects.RowsHaveArity 2 rows) :
    Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) := by
  cases result with
  | none =>
      apply Stored.stopped
      simp [SpecificationStep.resultValue, optionValue]
  | some next =>
      apply Stored.active
      refine ⟨tables_after_cell tables _ _, ?_, ?_, by simp, ?_, ?_⟩
      · simpa [NamedSpaces.Store.putCell, InferenceCache.cell] using cacheCell
      · simpa [NamedSpaces.Store.putCell] using proofCell
      · obtain ⟨rows, readRows, shaped⟩ := cacheRows
        exact ⟨rows, by simpa using readRows, shaped⟩
      · obtain ⟨rows, readRows, shaped⟩ := proofRows
        exact ⟨rows, by simpa using readRows, shaped⟩

private theorem live_after_step {spaces : Spaces} {logical next : Kernel.SpecificationAdmission.State}
    {declaration : ProofDeclaration} {before checking checked : State}
    (live : Live spaces logical before)
    (checkingCells : checking.cells = before.cells)
    (checkingOthers : ∀ handle, handle ≠ spaces.cache → checking.read handle = before.read handle)
    (frame : SpecificationStep.EffectFrame spaces logical declaration checking checked)
    (stepped : Kernel.SpecificationAdmission.step? logical declaration = some next) :
    Live spaces next (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces (some next))) := by
  refine ⟨tables_after_cell (frame.tables_of_step stepped) _ _, ?_, ?_, by simp, ?_, ?_⟩
  · simpa [NamedSpaces.Store.putCell, InferenceCache.cell] using frame.cache.1
  · have owned : checked.cells "mm0-proof-store" = some (handleValue spaces.proofs) := by
      rw [frame.cells, checkingCells]; exact live.proofCell
    simpa [NamedSpaces.Store.putCell] using owned
  · obtain ⟨rows, readRows, valid⟩ := frame.cache.2
    exact ⟨rows, by simpa using readRows, valid.rows⟩
  · obtain ⟨rows, readRows, shaped⟩ := live.proofRows
    refine ⟨rows, ?_, shaped⟩
    simp only [NamedSpaces.Store.cell_preserves_spaces]
    rw [frame.proofs, checkingOthers spaces.proofs live.tables.separate_proof]
    exact readRows

/-- Ordinary submissions derive the checking premises from the actual reset;
publication then yields the next physical session representation. -/
theorem ordinary_submit_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (bindings : Subst) (name : String) (before : State)
    (live : Live spaces logical before)
    (captured : applySubst bindings (.var name) = declarationValue declaration) :
    ∃ after, PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
      after (boolean (Kernel.SpecificationAdmission.step? logical declaration).isSome) ∧
      Stored spaces (Kernel.SpecificationAdmission.step? logical declaration) after := by
  let next := Kernel.SpecificationAdmission.step? logical declaration
  let answer := next.map fun state => stateValue spaces (pendingValue state.pending)
  obtain ⟨rows, allocated, shaped⟩ := live.cacheRows
  obtain ⟨checking, checked, returned, frame, empty, others, cells⟩ :=
    DeclarationScope.submit_returns_with_frame bindings before spaces.cache rows
      (stateValue spaces (pendingValue logical.pending)) (declarationValue declaration) answer name
      captured (by simpa [SpecificationStep.resultValue, optionValue] using live.sessionCell)
      live.cacheCell allocated shaped (SpecificationStep.EffectFrame spaces logical declaration) (by
        intro checking empty others cells
        obtain ⟨checked, computed, frame⟩ := ordinary_service_returns spaces logical declaration checking
          (live.ready_after_reset empty others cells)
        refine ⟨checked, ?_, frame⟩
        exact computed (DeclarationScope.declarationEnvironment spaces.cache
          (stateValue spaces (pendingValue logical.pending)) (declarationValue declaration)) "state" "command"
          rfl rfl)
  refine ⟨checked.putCell "mm0-session" (optionValue answer), ?_, ?_⟩
  · simpa [answer, next] using returned
  · cases stepped : Kernel.SpecificationAdmission.step? logical declaration with
    | none =>
        apply Stored.stopped
        simp [answer, next, stepped, optionValue]
    | some nextState =>
        apply Stored.active
        simpa [answer, next, stepped, SpecificationStep.resultValue] using
          live_after_step live cells others frame stepped

private def finishEquation : SpaceSemantics.Equation :=
  serviceSource.program.equations[5]'(by decide +kernel)
private def finishBody : Atom :=
  match finishEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []
private def finishCases : SpaceSemantics.Cases :=
  match finishBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []
private def activeFinish : Atom := (finishCases[0]'(by decide +kernel)).2
private def finishAnswerBody : Atom :=
  match activeFinish with
  | .expression [_, _, _, body] => body
  | _ => .expression []
private def finishAnswerCases : SpaceSemantics.Cases :=
  match finishAnswerBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private theorem finish_shape : finishEquation.body =
    .expression [.symbol "let", .var "current",
      .expression [.symbol "get-state", .symbol "mm0-session"], finishBody] := by decide +kernel
private theorem finish_case_shape : finishBody =
    .expression [.symbol "case", .var "current",
      .expression (finishCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem finish_cases_shape : finishCases =
    [(.expression [.symbol "Some", .var "state"], activeFinish),
      (.symbol "None", boolean false), (.var "malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem active_finish_shape : activeFinish =
    .expression [.symbol "let", .var "answer", .expression [.symbol "mm0:spec-finish", .var "current"],
      finishAnswerBody] := by decide +kernel
private theorem answer_case_shape : finishAnswerBody =
    .expression [.symbol "case", .var "answer",
      .expression (finishAnswerCases.map fun row => .expression [row.1, row.2])] := by decide +kernel
private theorem answer_cases_shape : finishAnswerCases =
    [(.expression [.symbol "Some", .var "theory"], boolean true),
      (.symbol "None", boolean false), (.var "malformed", .symbol "MM0:Malformed")] := by decide +kernel
private theorem finish_unique : program.equations.filter (fun row => row.head == "mm0:finish") =
    [finishEquation] := by decide +kernel
private theorem finish_formals : finishEquation.arguments = [] := by decide +kernel

private theorem finish_answer_returns (bindings : Subst) (before : State) (answer : Option Atom)
    (captured : applySubst bindings (.var "answer") = optionValue answer)
    (fresh : Subst.lookup bindings "theory" = none) :
    PureReturns program bindings before finishAnswerBody before (boolean answer.isSome) := by
  rw [answer_case_shape]
  cases answer with
  | none =>
      apply case_returns program bindings bindings before before before (.var "answer") (.symbol "None")
        (boolean false) _ _ finishAnswerCases (read_cases_encoded _)
      · simpa [captured, optionValue] using variable_returns program bindings before "answer"
      · simp [answer_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue, matchAtom]
      · exact grounded_returns program bindings before (.bool false)
  | some value =>
      let bound := ("theory", value) :: bindings
      have freshLookup := fresh
      unfold Subst.lookup at freshLookup
      apply case_returns program bindings bound before before before (.var "answer")
        (.expression [.symbol "Some", value]) (boolean true) _ _ finishAnswerCases (read_cases_encoded _)
      · simpa [captured, optionValue] using variable_returns program bindings before "answer"
      · simp [answer_cases_shape, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, freshLookup, bound]
      · exact grounded_returns program bound before (.bool true)

/-- Completion observes the independent specification result. A leftover
entry gives `False` without writing the session cell or any native space. -/
theorem active_finish_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (before : State) (bindings : Subst)
    (session : before.cells "mm0-session" = some (SpecificationStep.resultValue spaces (some logical))) :
    PureReturns program bindings before (.expression [.symbol "mm0:finish"]) before
      (boolean logical.pending.isEmpty) := by
  let current := SpecificationStep.resultValue spaces (some logical)
  let source := stateValue spaces (pendingValue logical.pending)
  let outer : Subst := [("current", current)]
  let active := ("state", source) :: outer
  let answer : Option Atom := if logical.pending.isEmpty then some (theoryValue spaces) else none
  have child : PureReturns program active before (.expression [.symbol "mm0:spec-finish", .var "current"])
      before (optionValue answer) := by
    have computed := SpecificationStep.finish_captured_returns active before spaces (some logical) "current"
      (by simp [active, outer, applySubst, Subst.lookup, current])
    cases pending : logical.pending <;>
      simpa [answer, pending, AdmissionStep.resultValue, optionValue] using computed
  have tail : PureReturns program active before activeFinish before (boolean logical.pending.isEmpty) := by
    rw [active_finish_shape]
    let bound := ("answer", optionValue answer) :: active
    apply let_returns program active bound before before before (.var "answer") _ _ (optionValue answer) _ child
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, bound, active, outer]
    · have returned := finish_answer_returns bound before answer
        (by simp [bound, applySubst, Subst.lookup])
        (by simp [bound, active, outer, Subst.lookup])
      cases pending : logical.pending <;> simpa [answer, pending] using returned
  have body : PureReturns program [] before finishEquation.body before (boolean logical.pending.isEmpty) := by
    rw [finish_shape]
    apply let_returns program [] outer before before before (.var "current") _ _ current _
      (DeclarationScope.cell_returns before [] "mm0-session" current session)
    · simp [SpaceSemantics.matchValue, matchAtom, Subst.lookup, outer]
    · rw [finish_case_shape]
      apply case_returns program outer active before before before (.var "current") current activeFinish _ _
        finishCases (read_cases_encoded _)
      · simpa [outer, applySubst, Subst.lookup] using variable_returns program outer before "current"
      · simp [finish_cases_shape, current, source, SpecificationStep.resultValue, optionValue,
          SpaceSemantics.selectCase, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues,
          matchAtom, Subst.lookup, outer, active]
      · exact tail
  apply authored_variable_call_returns program bindings [] before before "mm0:finish" []
    finishEquation.body _ (by decide) (by decide) (by decide +kernel) _ body (by decide)
  rw [clauses_use_only_the_named_equations, finish_unique]
  simp [finish_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues]

/-- Later ordinary submissions observe an already stored failure without
executing their declaration. Successful active submissions use the same
driver, reset and publication theorem as above. -/
theorem submit_returns (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (declaration : ProofDeclaration) (bindings : Subst) (name : String) (before : State)
    (represented : Stored spaces logical before)
    (captured : applySubst bindings (.var name) = declarationValue declaration) :
    ∃ after, PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name]) after
      (boolean (logical.bind fun state => Kernel.SpecificationAdmission.step? state declaration).isSome) ∧
      Stored spaces (logical.bind fun state => Kernel.SpecificationAdmission.step? state declaration) after := by
  cases represented with
  | active live =>
      simpa only [Option.bind_some] using ordinary_submit_returns spaces _ declaration bindings name before live captured
  | stopped failed =>
      exact ⟨before, DeclarationScope.refused_submit_returns bindings before _ name captured failed,
        Stored.stopped failed⟩

/-- EOF completion observes the existing pending-entry condition. In
particular a false finish on a live session leaves that session live. -/
theorem finish_returns (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (before : State) (bindings : Subst) (represented : Stored spaces logical before) :
    PureReturns program bindings before (.expression [.symbol "mm0:finish"]) before
      (boolean (logical.bind fun state =>
        if state.pending.isEmpty then some state.theory else none).isSome) := by
  cases logical with
  | none =>
      cases represented with
      | stopped failed => exact DeclarationScope.refused_finish_returns bindings before failed
  | some state =>
      cases represented with
      | active live =>
          have returned := active_finish_returns spaces state before bindings live.sessionCell
          cases pending : state.pending <;> simpa [pending] using returned

/-- Native controls for already resolved ordinary declarations. This is
input data for the existing PeTTa machine, not a second session semantics. -/
def submissionControls (declarations : List ProofDeclaration) : List Control :=
  declarations.map fun declaration => .evaluate [("command", declarationValue declaration)]
    (.expression [.symbol "mm0:submit", .var "command"])

/-- The existing source sequencer produces one Boolean per submission and
retains the independent kernel's exact logical result. Once stopped, all
remaining controls return false. -/
theorem ordinary_run_returns (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (declarations : List ProofDeclaration) (before : State) (represented : Stored spaces logical before)
    (collected : List Atom) :
    ∃ after answers, (theory program).MultiStep
        { state := before, control := .sequence (submissionControls declarations) collected }
        (finished after (collected ++ answers) [] []) ∧
      Stored spaces (logical.bind fun state => Kernel.SpecificationAdmission.run? state declarations) after ∧
      answers.length = declarations.length ∧
      ((logical.bind fun state => Kernel.SpecificationAdmission.run? state declarations).isSome = true ↔
        logical.isSome = true ∧ answers = List.replicate declarations.length (boolean true)) := by
  induction declarations generalizing logical before collected with
  | nil =>
      refine ⟨before, [], ?_, ?_, rfl, ?_⟩
      · simpa only [submissionControls, List.map_nil, List.append_nil] using
          (show (theory program).MultiStep { state := before, control := .sequence [] collected }
            (finished before collected [] []) from .step (step_transition rfl) (.refl _))
      · cases logical <;> simpa [Kernel.SpecificationAdmission.run?] using represented
      · simp [Kernel.SpecificationAdmission.run?]
  | cons declaration remaining ih =>
      obtain ⟨middle, returned, stored⟩ := submit_returns spaces logical declaration
        [("command", declarationValue declaration)] "command" before represented rfl
      let next := logical.bind fun state => Kernel.SpecificationAdmission.step? state declaration
      obtain ⟨after, answers, rest, representedAfter, length, accepted⟩ :=
        ih next middle stored (collected ++ [boolean next.isSome])
      have same : logical.bind (fun state => Kernel.SpecificationAdmission.run? state (declaration :: remaining)) =
          next.bind (fun state => Kernel.SpecificationAdmission.run? state remaining) := by
        cases logical <;> rfl
      refine ⟨after, boolean next.isSome :: answers, ?_, ?_, by simp [length], ?_⟩
      · simpa only [submissionControls, List.map_cons, List.append_assoc, List.singleton_append] using
          sequence_cons_answers program before middle after
            (.evaluate [("command", declarationValue declaration)]
              (.expression [.symbol "mm0:submit", .var "command"]))
            (submissionControls remaining) collected [boolean next.isSome] (collected ++ [boolean next.isSome] ++ answers)
            returned rest
      · rw [same]; exact representedAfter
      · rw [same, accepted]
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq, boolean]
        cases original : logical with
        | none => simp [next, original]
        | some state =>
            cases stepped : Kernel.SpecificationAdmission.step? state declaration <;> simp [next, original, stepped]

/-- The submitted sequence followed by the actual finish control. Every
answer occurrence is retained; the final answer checks pending consumption. -/
theorem ordinary_run_and_finish_returns (spaces : Spaces)
    (logical : Option Kernel.SpecificationAdmission.State) (declarations : List ProofDeclaration)
    (before : State) (represented : Stored spaces logical before) (collected : List Atom) :
    ∃ after answers, (theory program).MultiStep
        { state := before, control := .sequence
            (submissionControls declarations ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) collected }
        (finished after (collected ++ answers ++
          [boolean ((logical.bind fun state => Kernel.SpecificationAdmission.run? state declarations).bind fun state =>
            if state.pending.isEmpty then some state.theory else none).isSome]) [] []) ∧
      Stored spaces (logical.bind fun state => Kernel.SpecificationAdmission.run? state declarations) after ∧
      answers.length = declarations.length ∧
      ((logical.bind fun state => Kernel.SpecificationAdmission.run? state declarations).isSome = true ↔
        logical.isSome = true ∧ answers = List.replicate declarations.length (boolean true)) := by
  induction declarations generalizing logical before collected with
  | nil =>
      refine ⟨before, [], ?_, ?_, rfl, ?_⟩
      · have returned := finish_returns spaces logical before [] represented
        have path := sequence_cons_answers program before before before
          (.evaluate [] (.expression [.symbol "mm0:finish"])) [] collected
          [boolean (logical.bind fun state => if state.pending.isEmpty then some state.theory else none).isSome]
          (collected ++ [boolean (logical.bind fun state =>
            if state.pending.isEmpty then some state.theory else none).isSome]) returned
          (.step (step_transition rfl) (.refl _))
        cases logical <;> simpa [submissionControls, Kernel.SpecificationAdmission.run?] using path
      · cases logical <;> simpa [Kernel.SpecificationAdmission.run?] using represented
      · simp [Kernel.SpecificationAdmission.run?]
  | cons declaration remaining ih =>
      obtain ⟨middle, returned, stored⟩ := submit_returns spaces logical declaration
        [("command", declarationValue declaration)] "command" before represented rfl
      let next := logical.bind fun state => Kernel.SpecificationAdmission.step? state declaration
      obtain ⟨after, answers, rest, representedAfter, length, accepted⟩ :=
        ih next middle stored (collected ++ [boolean next.isSome])
      have same : logical.bind (fun state => Kernel.SpecificationAdmission.run? state (declaration :: remaining)) =
          next.bind (fun state => Kernel.SpecificationAdmission.run? state remaining) := by
        cases logical <;> rfl
      refine ⟨after, boolean next.isSome :: answers, ?_, ?_, by simp [length], ?_⟩
      · rw [same]
        have composed := sequence_cons_answers program before middle after
            (.evaluate [("command", declarationValue declaration)]
              (.expression [.symbol "mm0:submit", .var "command"]))
            (submissionControls remaining ++ [.evaluate [] (.expression [.symbol "mm0:finish"])])
            collected [boolean next.isSome] _ returned rest
        simpa only [submissionControls, List.map_cons, List.cons_append, List.append_assoc,
          List.nil_append, List.singleton_append] using composed
      · rw [same]; exact representedAfter
      · rw [same, accepted]
        simp only [List.length_cons, List.replicate_succ, List.cons.injEq, boolean]
        cases original : logical with
        | none => simp [next, original]
        | some state =>
            cases stepped : Kernel.SpecificationAdmission.step? state declaration <;> simp [next, original, stepped]

def ordinaryProtocolControls (specification : List SpecificationEntry) (declarations : List ProofDeclaration) : List Control :=
  .evaluate [("spec", pendingValue specification)] (.expression [.symbol "mm0:start", .var "spec"]) ::
    submissionControls declarations ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]

def ordinaryProtocolConfiguration (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) : Configuration :=
  { state := before, control := .sequence (ordinaryProtocolControls specification declarations) [] }

/-- The resolved ordinary protocol earns its native table, cache and cell
premises by executing `start`, then every real `submit`, then `finish`.
Acceptance is the independent verifier's acceptance, including exact public
specification consumption. The frontend's shared commands have their own
fixed-evidence correspondence and are not silently treated as ordinary data. -/
theorem ordinary_protocol_returns (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    ∃ after answers, (theory program).MultiStep (ordinaryProtocolConfiguration before specification declarations)
        (finished after answers [] []) ∧
      Stored (SessionInitialization.allocatedSpaces before)
        (Kernel.SpecificationAdmission.run? ⟨{}, specification⟩ declarations) after ∧
      answers.length = declarations.length + 2 ∧
      (answers = List.replicate (declarations.length + 2) (boolean true) ↔
        (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true) := by
  let spaces := SessionInitialization.allocatedSpaces before
  let initial := SessionInitialization.startState before (pendingValue specification)
  let logical : Kernel.SpecificationAdmission.State := ⟨{}, specification⟩
  obtain ⟨after, submitted, rest, represented, length, accepted⟩ :=
    ordinary_run_and_finish_returns spaces (some logical) declarations initial
      (Stored.active (start_live before specification)) [boolean true]
  let last := boolean (Kernel.SpecificationAdmission.verify? specification declarations).isSome
  refine ⟨after, boolean true :: submitted ++ [last], ?_, ?_, by simp [length], ?_⟩
  · have start := SessionInitialization.returns [("spec", pendingValue specification)] before
      (pendingValue specification) "spec" rfl
    have same : ((some logical).bind fun state => Kernel.SpecificationAdmission.run? state declarations).bind
        (fun state => if state.pending.isEmpty then some state.theory else none) =
        Kernel.SpecificationAdmission.verify? specification declarations := rfl
    rw [same] at rest
    have composed := sequence_cons_answers program before initial after
        (.evaluate [("spec", pendingValue specification)] (.expression [.symbol "mm0:start", .var "spec"]))
        (submissionControls declarations ++ [.evaluate [] (.expression [.symbol "mm0:finish"])])
        [] [boolean true] _ start rest
    simpa only [ordinaryProtocolConfiguration, ordinaryProtocolControls, initial, last,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append] using composed
  · exact represented
  · have submissionAccepted : (Kernel.SpecificationAdmission.run? logical declarations).isSome = true ↔
        submitted = List.replicate declarations.length (boolean true) := by
      simpa only [Option.bind_some, Option.isSome_some, true_and] using accepted
    constructor
    · intro allTrue
      have finalAnswer : last = boolean true := by
        exact (List.eq_replicate_iff.mp allTrue).2 last (by simp)
      simpa [last, boolean] using finalAnswer
    · intro verified
      have running : (Kernel.SpecificationAdmission.run? logical declarations).isSome = true := by
        cases result : Kernel.SpecificationAdmission.run? logical declarations with
        | none => simp [Kernel.SpecificationAdmission.verify?, logical, result] at verified
        | some state => rfl
      rw [submissionAccepted.mp running]
      have replicate : boolean true :: (List.replicate declarations.length (boolean true) ++ [boolean true]) =
          List.replicate (declarations.length + 2) (boolean true) := by
        rw [show declarations.length + 2 = (declarations.length + 1) + 1 by omega,
          List.replicate_succ]
        congr 1
        exact (List.replicate_add declarations.length 1 (boolean true)).symm
      simpa only [last, verified, List.cons_append] using replicate

/-- The complete ordinary protocol has enough fuel and retains its exact
response sequence and physical session representation under fuel extension. -/
theorem ordinary_protocol_sufficient_fuel (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    ∃ after answers fuel,
      (∀ extra, run program (fuel + extra) (ordinaryProtocolConfiguration before specification declarations) =
        .complete after answers [] []) ∧
      Stored (SessionInitialization.allocatedSpaces before)
        (Kernel.SpecificationAdmission.run? ⟨{}, specification⟩ declarations) after ∧
      answers.length = declarations.length + 2 ∧
      (answers = List.replicate (declarations.length + 2) (boolean true) ↔
        (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true) := by
  obtain ⟨after, answers, path, stored, length, accepted⟩ := ordinary_protocol_returns before specification declarations
  obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ after answers [] []).mpr path
  exact ⟨after, answers, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ _ _ [] [] completed,
    stored, length, accepted⟩

/-- Every completed observation inherits the protocol's earned invariants.
Exhaustion is not converted into an accepting or refusing response. -/
theorem ordinary_protocol_completed_frame (before after : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (fuel : Nat) (answers unread printed : List Atom)
    (completed : run program fuel (ordinaryProtocolConfiguration before specification declarations) =
      .complete after answers unread printed) :
    Stored (SessionInitialization.allocatedSpaces before)
      (Kernel.SpecificationAdmission.run? ⟨{}, specification⟩ declarations) after ∧
      answers.length = declarations.length + 2 ∧ unread = [] ∧ printed = [] ∧
      (answers = List.replicate (declarations.length + 2) (boolean true) ↔
        (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true) := by
  obtain ⟨reference, expected, referenceFuel, returned, stored, length, accepted⟩ :=
    ordinary_protocol_sufficient_fuel before specification declarations
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    reference after expected [] [] answers unread printed referenceCompleted completed
  subst after
  subst answers
  exact ⟨stored, length, sameUnread.symm, samePrinted.symm, accepted⟩

/-- The retained source driver accepts this resolved ordinary stream exactly
when the independent specification/admission checker accepts it. -/
theorem ordinary_protocol_accepts_iff (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    (∃ after fuel, run program fuel (ordinaryProtocolConfiguration before specification declarations) =
      .complete after (List.replicate (declarations.length + 2) (boolean true)) [] []) ↔
      (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true := by
  constructor
  · rintro ⟨after, fuel, completed⟩
    exact (ordinary_protocol_completed_frame before after specification declarations fuel _ [] [] completed).2.2.2.2.mp rfl
  · intro verified
    obtain ⟨after, answers, fuel, returned, _, _, accepted⟩ := ordinary_protocol_sufficient_fuel before specification declarations
    have allTrue := accepted.mpr verified
    exact ⟨after, fuel, by simpa only [Nat.add_zero, allTrue] using returned 0⟩

/-- The same acceptance theorem ranges over the one PeTTa whole-run judgment. -/
theorem ordinary_protocol_judgment_iff (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    (∃ after, DeclarativeSpec.Runs program (ordinaryProtocolConfiguration before specification declarations)
      (.complete after (List.replicate (declarations.length + 2) (boolean true)) [] [])) ↔
      (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true := by
  rw [← ordinary_protocol_accepts_iff before specification declarations]
  constructor
  · rintro ⟨after, derivation⟩
    obtain ⟨fuel, completed⟩ := (completed_run_iff_derivation program _ after _ [] []).mpr derivation
    exact ⟨after, fuel, completed⟩
  · rintro ⟨after, fuel, completed⟩
    exact ⟨after, (completed_run_iff_derivation program _ after _ [] []).mp ⟨fuel, completed⟩⟩

/-- These are actual paths in the judgment-generated PeTTa GSLT. -/
theorem ordinary_protocol_gslt_iff (before : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) :
    (∃ after, (theory program).MultiStep (ordinaryProtocolConfiguration before specification declarations)
      (finished after (List.replicate (declarations.length + 2) (boolean true)) [] [])) ↔
      (Kernel.SpecificationAdmission.verify? specification declarations).isSome = true := by
  rw [← ordinary_protocol_accepts_iff before specification declarations]
  constructor
  · rintro ⟨after, path⟩
    obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ after _ [] []).mpr path
    exact ⟨after, fuel, completed⟩
  · rintro ⟨after, fuel, completed⟩
    exact ⟨after, (completed_run_iff_path program _ after _ [] []).mp ⟨fuel, completed⟩⟩

/-- An accepted observed protocol constructs the independently checked
specification history, its exact authorized axioms, and the specified source
extension. The history is a conclusion of execution, not a driver premise. -/
theorem ordinary_protocol_specified_history (before after : State) (specification : List SpecificationEntry)
    (declarations : List ProofDeclaration) (fuel : Nat)
    (accepted : run program fuel (ordinaryProtocolConfiguration before specification declarations) =
      .complete after (List.replicate (declarations.length + 2) (boolean true)) [] []) :
    ∃ logicalTheory,
      Kernel.SpecificationAdmission.verify? specification declarations = some logicalTheory ∧
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨logicalTheory, []⟩ ∧
      Kernel.Theory.WellFormed logicalTheory ∧
      Kernel.SpecificationAdmission.declarationAxioms declarations =
        Kernel.SpecificationAdmission.specificationAxioms specification ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedExtends
        (specification.map Upstream.Lean3ProofAdmission.projectSpecification)
        (Upstream.Lean3Typing.projectRun (declarations.map ProofDeclaration.admission)) := by
  have verified := (ordinary_protocol_accepts_iff before specification declarations).mp ⟨after, fuel, accepted⟩
  cases result : Kernel.SpecificationAdmission.verify? specification declarations with
  | none => simp [result] at verified
  | some logicalTheory =>
      exact ⟨logicalTheory, rfl, (Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mp result,
        Kernel.SpecificationAdmission.verified_wellFormed result,
        Kernel.SpecificationAdmission.verified_axioms_exact result,
        Upstream.Lean3ProofAdmission.checked_specification_extension result⟩

namespace Controls

private def info : Kernel.SortInfo := { provable := true }
private def specification : List SpecificationEntry := [.sort 0 info]
private def good : ProofDeclaration := ⟨.sort 0 info, false⟩
private def wrong : ProofDeclaration := ⟨.sort 1 info, false⟩

/-- The empty resolved specification completes with start and finish true. -/
theorem empty_protocol_accepts :
    UpstreamAgreement.answersOf (run program 4000
      (ordinaryProtocolConfiguration (Effects.loaded program) [] [])) = some [boolean true, boolean true] := by
  decide +kernel

/-- Startup earns the store premises of a matching public declaration. -/
theorem matching_sort_protocol_accepts :
    UpstreamAgreement.answersOf (run program 8000
      (ordinaryProtocolConfiguration (Effects.loaded program) specification [good])) =
        some [boolean true, boolean true, boolean true] := by
  decide +kernel

/-- An unfinished specification yields a completed false finish response. -/
theorem missing_declaration_protocol_refuses :
    UpstreamAgreement.answersOf (run program 4000
      (ordinaryProtocolConfiguration (Effects.loaded program) specification [])) =
        some [boolean true, boolean false] := by
  decide +kernel

/-- A mismatch stops the session; a later matching declaration cannot reopen
it, and finish remains false. -/
theorem wrong_then_matching_protocol_stays_refused :
    UpstreamAgreement.answersOf (run program 8000
      (ordinaryProtocolConfiguration (Effects.loaded program) specification [wrong, good])) =
        some [boolean true, boolean false, boolean false, boolean false] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MM0.MeTTa.SessionDriver
