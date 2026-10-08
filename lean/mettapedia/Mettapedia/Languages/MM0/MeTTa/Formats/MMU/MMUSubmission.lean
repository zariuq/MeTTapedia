import Mettapedia.Languages.MM0.MeTTa.Formats.MMU.MMUResolution
import Mettapedia.Languages.MM0.MeTTa.Session.SessionProtocol
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# MMU submission through the existing admission session

The retained frontend submits its resolved commands in source order and stops
at the first False verdict. These paths use the existing session receipts;
they introduce no admission checker or replacement shared-proof witness.
Finishing the specification remains a separate authorization condition.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.MMUSubmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open ListAccess (listValue)
open SessionInitialization (Spaces)
open SessionDriver (Stored)
open SessionProtocol (Command Trace)
open MMUResolution (resolverSource)

private def submissionEquation : SpaceSemantics.Equation :=
  resolverSource.program.equations[60]'(by decide)

private def submissionCases : SpaceSemantics.Cases :=
  match submissionEquation.body with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def nonemptyBody : Atom := (submissionCases[1]'(by decide)).2

private def verdictCases : SpaceSemantics.Cases :=
  match nonemptyBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def submissionEnvironment (commands : List Command) : Subst :=
  [("commands", .expression (commands.map SessionProtocol.commandValue))]

private theorem submission_unique :
    MMUResolution.program.equations.filter (fun equation => equation.head == "mm0:mmu:submit-commands") =
      [submissionEquation] := by decide

private theorem submission_formals : submissionEquation.arguments =
    [.expression [.symbol "MM0:L", .var "commands"]] := by decide

private theorem submission_shape : submissionEquation.body =
    .expression [.symbol "case", .var "commands",
      .expression (submissionCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem submission_cases : submissionCases =
    [(.expression [], boolean true),
      (.expression [.symbol "cons", .var "first", .var "rest"], nonemptyBody),
      (.var "bad", .symbol "MM0:Malformed")] := by decide

private theorem nonempty_shape : nonemptyBody =
    .expression [.symbol "case", .expression [.symbol "mm0:submit", .var "first"],
      .expression (verdictCases.map fun row => .expression [row.1, row.2])] := by decide

private theorem verdict_cases : verdictCases =
    [(boolean true, .expression [.symbol "mm0:mmu:submit-commands",
        .expression [.symbol "MM0:L", .var "rest"]]),
      (boolean false, boolean false), (.var "bad", .symbol "MM0:Malformed")] := by decide

private theorem submission_clause (commands : List Command) :
    clauses MMUResolution.program "mm0:mmu:submit-commands"
      [listValue (commands.map SessionProtocol.commandValue)] =
      [.evaluate (submissionEnvironment commands) submissionEquation.body] := by
  rw [clauses_use_only_the_named_equations, submission_unique]
  simp [submission_formals, listValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, submissionEnvironment]

private theorem submission_raw_returns (bindings : Subst) (before after : State)
    (commands : List Command) (argument answer : Atom)
    (captured : applySubst bindings argument = listValue (commands.map SessionProtocol.commandValue))
    (body : PureReturns MMUResolution.program (submissionEnvironment commands) before submissionEquation.body after answer) :
    PureReturns MMUResolution.program bindings before
      (.expression [.symbol "mm0:mmu:submit-commands", argument]) after answer := by
  apply call_returns MMUResolution.program bindings before after "mm0:mmu:submit-commands" _ answer
    (by decide) _ (by decide)
  apply raw_arguments_return MMUResolution.program bindings before after "mm0:mmu:submit-commands" _ [] 0 answer
  · intro offset bounded
    have zero : offset = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst offset
    decide
  · simpa [captured] using authored_function_arguments_return MMUResolution.program bindings
      (submissionEnvironment commands) before after "mm0:mmu:submit-commands"
      [listValue (commands.map SessionProtocol.commandValue)] 1 submissionEquation.body answer
      (by decide) (by decide) (submission_clause commands) body

/-- A rejected session is inert on every remaining receipt. This also accounts
for the suffix that the frontend skips after its first False verdict. -/
theorem stopped_trace {spaces : Spaces} {logical terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after) (stopped : logical = none) :
    terminal = none ∧ after = before := by
  revert stopped
  induction trace with
  | nil logical before => intro stopped; exact ⟨stopped, rfl⟩
  | @cons logical next terminal before middle after command commands answers receipt tail ih =>
      intro stopped
      subst logical
      obtain ⟨nextStopped, sameState⟩ := receipt.stopped
      obtain ⟨terminalStopped, sameTail⟩ := ih nextStopped
      exact ⟨terminalStopped, sameTail.trans sameState⟩

private theorem receipt_returns {spaces : Spaces}
    {logical next : Option Kernel.SpecificationAdmission.State} {command : Command} {before middle : State}
    (receipt : SessionProtocol.Receipt spaces logical command before middle next)
    (bindings : Subst) (name : String)
    (captured : applySubst bindings (.var name) = SessionProtocol.commandValue command) :
    PureReturns MMUResolution.program bindings before
      (.expression [.symbol "mm0:submit", .var name]) middle (boolean next.isSome) := by
  have checked := MMUResolution.checker_captured_returns (by decide +kernel) receipt.returned
  apply raw_unary_capture_returns MMUResolution.program
    [("command", SessionProtocol.commandValue command)] bindings before middle "mm0:submit"
    (.var "command") (.var name) (boolean next.isSome) (by decide) (by decide) (by decide) _ checked
  change SessionProtocol.commandValue command = applySubst bindings (.var name)
  exact captured.symm

/-- The actual recursive source body computes the conjunction of the existing
receipt verdicts. On rejection its skipped suffix already has the same store. -/
private theorem submission_body_returns {spaces : Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after) :
    PureReturns MMUResolution.program (submissionEnvironment commands) before submissionEquation.body
      after (boolean (answers.all id)) := by
  induction trace with
  | nil logical before =>
      rw [submission_shape]
      apply case_returns MMUResolution.program (submissionEnvironment []) (submissionEnvironment [])
        before before before (.var "commands") (.expression []) (boolean true) _ _ submissionCases
        (read_cases_encoded _)
      · simpa [submissionEnvironment, applySubst, Subst.lookup] using
          variable_returns MMUResolution.program (submissionEnvironment []) before "commands"
      · simp [submission_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues]
      · exact grounded_returns MMUResolution.program _ before (.bool true)
  | @cons logical next terminal before middle after command commands answers receipt tail ih =>
      let outer := submissionEnvironment (command :: commands)
      let bound : Subst := ("rest", .expression (commands.map SessionProtocol.commandValue)) ::
        ("first", SessionProtocol.commandValue command) :: outer
      rw [submission_shape]
      apply case_returns MMUResolution.program outer bound before before after
        (.var "commands") (.expression ((command :: commands).map SessionProtocol.commandValue))
        nonemptyBody _ _ submissionCases (read_cases_encoded _)
      · simpa [outer, submissionEnvironment, applySubst, Subst.lookup] using
          variable_returns MMUResolution.program outer before "commands"
      · simp [submission_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
          SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup,
          outer, bound, submissionEnvironment]
      · rw [nonempty_shape]
        cases next with
        | none =>
            have sameAfter := (stopped_trace tail rfl).2
            subst after
            simp only [Option.isSome_none, List.all_cons, id_eq, Bool.false_and]
            apply case_returns MMUResolution.program bound bound before middle middle
              (.expression [.symbol "mm0:submit", .var "first"]) (boolean false)
              (boolean false) _ _ verdictCases (read_cases_encoded _)
            · exact receipt_returns receipt bound "first"
                (by simp [bound, applySubst, Subst.lookup])
            · simp [verdict_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, boolean]
            · exact grounded_returns MMUResolution.program bound middle (.bool false)
        | some state =>
            simp only [Option.isSome_some, List.all_cons, id_eq, Bool.true_and]
            apply case_returns MMUResolution.program bound bound before middle after
              (.expression [.symbol "mm0:submit", .var "first"]) (boolean true)
              (.expression [.symbol "mm0:mmu:submit-commands", .expression [.symbol "MM0:L", .var "rest"]])
              _ _ verdictCases (read_cases_encoded _)
            · exact receipt_returns receipt bound "first"
                (by simp [bound, applySubst, Subst.lookup])
            · simp [verdict_cases, SpaceSemantics.selectCase, SpaceSemantics.matchValue,
                matchAtom, boolean]
            · exact submission_raw_returns bound middle after commands _ _
                (by simp [bound, applySubst, applySubst.applySubstList, Subst.lookup, listValue]) ih

theorem submit_commands_captured_returns {spaces : Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after)
    (bindings : Subst) (name : String)
    (captured : applySubst bindings (.var name) = listValue (commands.map SessionProtocol.commandValue)) :
    PureReturns MMUResolution.program bindings before
      (.expression [.symbol "mm0:mmu:submit-commands", .var name]) after (boolean (answers.all id)) :=
  submission_raw_returns bindings before after commands _ _ captured (submission_body_returns trace)

theorem submit_commands_sufficient_fuel {spaces : Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after)
    (bindings : Subst) (name : String)
    (captured : applySubst bindings (.var name) = listValue (commands.map SessionProtocol.commandValue)) :
    ∃ fuel, ∀ extra, run MMUResolution.program (fuel + extra)
      { state := before, control := .evaluate bindings
          (.expression [.symbol "mm0:mmu:submit-commands", .var name]) } =
      .complete after [boolean (answers.all id)] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel MMUResolution.program bindings before after _ _
    (submit_commands_captured_returns trace bindings name captured)
  exact ⟨fuel, fun extra => completed_run_more_fuel MMUResolution.program fuel extra _
    after [boolean (answers.all id)] [] [] completed⟩

/-- The retained resolver constructor keeps its metadata and fixed commands.
Submission reads only the command field; it cannot change the specification. -/
def resolvedProgramValue (profile resolverState : Atom) (commands : List Command)
    (extensions source : Atom) : Atom :=
  .expression [.symbol "MM0:MMUProgram", profile, resolverState,
    listValue (commands.map SessionProtocol.commandValue), extensions, source]

private def programEquation : SpaceSemantics.Equation :=
  resolverSource.program.equations[59]'(by decide)

private def programEnvironment (profile resolverState : Atom) (commands : List Command)
    (extensions source : Atom) : Subst :=
  [("source", source), ("extensions", extensions),
    ("commands", listValue (commands.map SessionProtocol.commandValue)),
    ("state", resolverState), ("profile", profile)]

private theorem program_unique :
    MMUResolution.program.equations.filter (fun equation => equation.head == "mm0:mmu:submit-program") =
      [programEquation] := by decide

private theorem program_formals : programEquation.arguments =
    [.expression [.symbol "MM0:MMUProgram", .var "profile", .var "state",
      .var "commands", .var "extensions", .var "source"]] := by decide

private theorem program_body : programEquation.body =
    .expression [.symbol "mm0:mmu:submit-commands", .var "commands"] := by decide

private theorem program_clause (profile resolverState : Atom) (commands : List Command)
    (extensions source : Atom) :
    clauses MMUResolution.program "mm0:mmu:submit-program"
      [resolvedProgramValue profile resolverState commands extensions source] =
      [.evaluate (programEnvironment profile resolverState commands extensions source) programEquation.body] := by
  rw [clauses_use_only_the_named_equations, program_unique]
  simp [program_formals, resolvedProgramValue, SpaceSemantics.matchValue,
    SpaceSemantics.matchValue.matchValues, matchAtom, Subst.lookup, programEnvironment]

theorem submit_program_captured_returns {spaces : Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after)
    (bindings : Subst) (name : String) (profile resolverState extensions source : Atom)
    (captured : applySubst bindings (.var name) =
      resolvedProgramValue profile resolverState commands extensions source) :
    PureReturns MMUResolution.program bindings before
      (.expression [.symbol "mm0:mmu:submit-program", .var name]) after (boolean (answers.all id)) := by
  apply call_returns MMUResolution.program bindings before after "mm0:mmu:submit-program" _ _
    (by decide) _ (by decide)
  apply raw_arguments_return MMUResolution.program bindings before after "mm0:mmu:submit-program" _ [] 0 _
  · intro offset bounded
    have zero : offset = 0 := by simp only [List.length_cons, List.length_nil] at bounded; omega
    subst offset
    decide
  · have body := submit_commands_captured_returns trace
      (programEnvironment profile resolverState commands extensions source) "commands"
      (by simp [programEnvironment, applySubst, Subst.lookup])
    rw [← program_body] at body
    simpa [captured] using authored_function_arguments_return MMUResolution.program bindings
      (programEnvironment profile resolverState commands extensions source) before after "mm0:mmu:submit-program"
      [resolvedProgramValue profile resolverState commands extensions source] 1 programEquation.body _
      (by decide) (by decide) (program_clause profile resolverState commands extensions source) body

theorem submit_program_exists (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (commands : List Command) (before : State) (represented : Stored spaces logical before)
    (bindings : Subst) (name : String) (profile resolverState extensions source : Atom)
    (captured : applySubst bindings (.var name) =
      resolvedProgramValue profile resolverState commands extensions source) :
    ∃ after answers terminal,
      PureReturns MMUResolution.program bindings before
        (.expression [.symbol "mm0:mmu:submit-program", .var name]) after (boolean (answers.all id)) ∧
      Trace spaces logical before commands answers terminal after ∧ Stored spaces terminal after := by
  obtain ⟨after, answers, terminal, trace, stored⟩ :=
    SessionProtocol.trace_exists spaces logical commands before represented
  exact ⟨after, answers, terminal,
    submit_program_captured_returns trace bindings name profile resolverState extensions source captured,
    trace, stored⟩

/-- The read-only finish call still checks the independent pending entries,
even when the frontend's empty command fold returned True. -/
theorem finish_captured_returns (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (before : State) (bindings : Subst) (represented : Stored spaces logical before) :
    PureReturns MMUResolution.program bindings before (.expression [.symbol "mm0:finish"]) before
      (boolean (SessionProtocol.finishedStatus logical)) :=
  MMUResolution.checker_captured_returns (by decide +kernel)
    (SessionDriver.finish_returns spaces logical before bindings represented)

theorem finished_status_iff_consumed (logical : Option Kernel.SpecificationAdmission.State) :
    SessionProtocol.finishedStatus logical = true ↔ ∃ finalTheory, logical = some ⟨finalTheory, []⟩ := by
  cases logical with
  | none => simp [SessionProtocol.finishedStatus]
  | some state =>
      rcases state with ⟨theory, pending⟩
      cases pending <;> simp [SessionProtocol.finishedStatus]

/-- The source entry points are invoked in their actual start/submit/finish
order. This view does not add a source equation or a session implementation. -/
def protocolConfiguration (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom) : Configuration :=
  { state := before, control := .sequence
      [.evaluate [("spec", SpecificationMatching.pendingValue specification)]
          (.expression [.symbol "mm0:start", .var "spec"]),
       .evaluate [("resolved", resolvedProgramValue profile resolverState commands extensions source)]
          (.expression [.symbol "mm0:mmu:submit-program", .var "resolved"]),
       .evaluate [] (.expression [.symbol "mm0:finish"])] [] }

theorem protocol_returns (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom) :
    ∃ after answers terminal,
      (theory MMUResolution.program).MultiStep
        (protocolConfiguration before specification profile resolverState commands extensions source)
        (finished after [boolean true, boolean (answers.all id),
          boolean (SessionProtocol.finishedStatus terminal)] [] []) ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      ([boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] =
        List.replicate 3 (boolean true) ↔ ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  let spaces := SessionInitialization.allocatedSpaces before
  let initial := SessionInitialization.startState before (SpecificationMatching.pendingValue specification)
  obtain ⟨after, answers, terminal, trace, stored⟩ :=
    SessionProtocol.trace_exists spaces (some ⟨{}, specification⟩) commands initial
      (.active (SessionDriver.start_live before specification))
  have start := MMUResolution.checker_captured_returns (by decide +kernel)
    (SessionInitialization.returns [("spec", SpecificationMatching.pendingValue specification)] before
      (SpecificationMatching.pendingValue specification) "spec" rfl)
  have submitted := submit_program_captured_returns trace
    [("resolved", resolvedProgramValue profile resolverState commands extensions source)] "resolved"
    profile resolverState extensions source rfl
  have finished := finish_captured_returns spaces terminal after [] stored
  have last := sequence_cons_answers MMUResolution.program after after after
    (.evaluate [] (.expression [.symbol "mm0:finish"])) []
    [boolean true, boolean (answers.all id)] [boolean (SessionProtocol.finishedStatus terminal)]
    [boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] finished
    (.step (step_transition rfl) (.refl _))
  have rest := sequence_cons_answers MMUResolution.program initial after after _ _ [boolean true]
    [boolean (answers.all id)] _ submitted
    (by simpa using last)
  have combined := sequence_cons_answers MMUResolution.program before initial after _ _ []
    [boolean true] _ start (by simpa using rest)
  refine ⟨after, answers, terminal, ?_, trace, stored, ?_⟩
  · simpa [protocolConfiguration] using combined
  · constructor
    · intro accepted
      have finalAnswer : boolean (SessionProtocol.finishedStatus terminal) = boolean true :=
        (List.eq_replicate_iff.mp accepted).2 _ (by simp)
      have status : SessionProtocol.finishedStatus terminal = true := by
        simpa [boolean] using finalAnswer
      exact (finished_status_iff_consumed terminal).mp status
    · rintro ⟨finalTheory, rfl⟩
      have accepted := (trace.advances.mp rfl).2
      simp [accepted, SessionProtocol.finishedStatus]

theorem sufficient_fuel (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom) :
    ∃ after answers terminal fuel,
      (∀ extra, run MMUResolution.program (fuel + extra)
        (protocolConfiguration before specification profile resolverState commands extensions source) =
        .complete after [boolean true, boolean (answers.all id),
          boolean (SessionProtocol.finishedStatus terminal)] [] []) ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      ([boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] =
        List.replicate 3 (boolean true) ↔ ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, path, trace, stored, gate⟩ :=
    protocol_returns before specification profile resolverState commands extensions source
  obtain ⟨fuel, completed⟩ := (completed_run_iff_path MMUResolution.program _ after _ [] []).mpr path
  exact ⟨after, answers, terminal, fuel,
    fun extra => completed_run_more_fuel MMUResolution.program fuel extra _ after _ [] [] completed,
    trace, stored, gate⟩

/-- Every completed source observation inherits the same earned receipts and
store. No fuel-dependent alternative can acquire declaration authorization. -/
theorem completed_protocol (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom)
    (after : State) (fuel : Nat) (outputs unread printed : List Atom)
    (completed : run MMUResolution.program fuel
      (protocolConfiguration before specification profile resolverState commands extensions source) =
      .complete after outputs unread printed) :
    ∃ answers terminal,
      outputs = [boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] ∧
      unread = [] ∧ printed = [] ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      (outputs = List.replicate 3 (boolean true) ↔ ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨reference, answers, terminal, referenceFuel, returned, trace, stored, gate⟩ :=
    sufficient_fuel before specification profile resolverState commands extensions source
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ :=
    completed_result_unique MMUResolution.program referenceFuel fuel _ reference after _ [] []
      outputs unread printed referenceCompleted completed
  subst after
  refine ⟨answers, terminal, sameAnswers.symm, sameUnread.symm, samePrinted.symm, trace, stored, ?_⟩
  rw [← sameAnswers]
  exact gate

/-- The frontend's observed all-True completion consumes the independent
specification and earns its exact axioms and specified declaration history.
The extracted sharing witness never replaces an input command. -/
theorem accepted_consumes_specification (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom)
    (after : State) (fuel : Nat)
    (accepted : run MMUResolution.program fuel
      (protocolConfiguration before specification profile resolverState commands extensions source) =
      .complete after (List.replicate 3 (boolean true)) [] []) :
    ∃ finalTheory declarations answers,
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers (some ⟨finalTheory, []⟩) after ∧
      SessionDriver.Live (SessionInitialization.allocatedSpaces before) ⟨finalTheory, []⟩ after ∧
      List.Forall₂ SessionProtocol.HistoryImage commands declarations ∧
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨finalTheory, []⟩ ∧
      Kernel.SpecificationAdmission.verify? specification declarations = some finalTheory ∧
      Kernel.SpecificationAdmission.declarationAxioms (commands.map SessionProtocol.inputDeclaration) =
        Kernel.SpecificationAdmission.specificationAxioms specification ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedExtends
        (specification.map Upstream.Lean3ProofAdmission.projectSpecification)
        (Upstream.Lean3Typing.projectRun
          ((commands.map SessionProtocol.inputDeclaration).map Kernel.ProofDeclaration.admission)) := by
  obtain ⟨answers, terminal, _, _, _, trace, stored, gate⟩ :=
    completed_protocol before specification profile resolverState commands extensions source
      after fuel _ [] [] accepted
  obtain ⟨finalTheory, same⟩ := gate.mp rfl
  obtain ⟨declarations, images, history, verified, axioms, specified⟩ :=
    trace.consumed_specification finalTheory same
  rw [same] at trace stored
  cases stored with
  | active live => exact ⟨finalTheory, declarations, answers, trace, live, images, history, verified, axioms, specified⟩

theorem accepted_shared_preceding_proof (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom)
    (after : State) (fuel : Nat)
    (accepted : run MMUResolution.program fuel
      (protocolConfiguration before specification profile resolverState commands extensions source) =
      .complete after (List.replicate 3 (boolean true)) [] [])
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map Kernel.ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨finalTheory, declarations, answers, trace, _, _, _, _, _, _⟩ :=
    accepted_consumes_specification before specification profile resolverState commands extensions source after fuel accepted
  exact trace.shared_preceding_proof ⟨{}, specification⟩ ⟨finalTheory, []⟩ rfl rfl
    specification [] (.nil _) command belongs

theorem empty_commands_return_true (spaces : Spaces)
    (logical : Option Kernel.SpecificationAdmission.State) (before : State) :
    PureReturns MMUResolution.program [("commands", listValue [])] before
      (.expression [.symbol "mm0:mmu:submit-commands", .var "commands"]) before (boolean true) := by
  simpa using submit_commands_captured_returns (Trace.nil (spaces := spaces) logical before)
    [("commands", listValue [])] "commands" rfl

theorem unfinished_specification_still_refused (before : State) (specification : List Kernel.SpecificationEntry)
    (pending : specification ≠ []) :
    PureReturns MMUResolution.program []
      (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
      (.expression [.symbol "mm0:finish"])
      (SessionInitialization.startState before (SpecificationMatching.pendingValue specification)) (boolean false) := by
  have returned := finish_captured_returns (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
    (SessionInitialization.startState before (SpecificationMatching.pendingValue specification)) []
    (.active (SessionDriver.start_live before specification))
  cases specification with
  | nil => exact False.elim (pending rfl)
  | cons entry rest => simpa [SessionProtocol.finishedStatus] using returned

theorem protocol_derivation_returns (before : State) (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom) :
    ∃ after answers terminal,
      DeclarativeSpec.Runs MMUResolution.program
        (protocolConfiguration before specification profile resolverState commands extensions source)
        (.complete after [boolean true, boolean (answers.all id),
          boolean (SessionProtocol.finishedStatus terminal)] [] []) ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧ Stored (SessionInitialization.allocatedSpaces before) terminal after := by
  obtain ⟨after, answers, terminal, path, trace, stored, _⟩ :=
    protocol_returns before specification profile resolverState commands extensions source
  exact ⟨after, answers, terminal,
    (completed_derivation_iff_path MMUResolution.program _ after _ [] []).mpr path, trace, stored⟩

/-- Loading earns both store-encoding premises. The actual configuration
language represents the complete ordered observations and retained receipts. -/
theorem loaded_protocol_generated_path (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom) :
    ∃ after answers terminal target,
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing
        (ConfigurationLanguageDef.relationEnv MMUResolution.program) ConfigurationLanguageDef.language).MultiStep
        (ConfigurationEncoding.encode
          (protocolConfiguration (Effects.loaded MMUResolution.program) specification
            profile resolverState commands extensions source) []) target ∧
      ConfigurationEncoding.decode target = some (finished after
        [boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] [] []) ∧
      Trace (SessionInitialization.allocatedSpaces (Effects.loaded MMUResolution.program))
        (some ⟨{}, specification⟩)
        (SessionInitialization.startState (Effects.loaded MMUResolution.program)
          (SpecificationMatching.pendingValue specification)) commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces (Effects.loaded MMUResolution.program)) terminal after ∧
      ([boolean true, boolean (answers.all id), boolean (SessionProtocol.finishedStatus terminal)] =
        List.replicate 3 (boolean true) ↔ ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, path, trace, stored, gate⟩ :=
    protocol_returns (Effects.loaded MMUResolution.program) specification profile resolverState commands extensions source
  obtain ⟨names, generated, vacant, covers⟩ :=
    ConfigurationLanguageDef.path_realized MMUResolution.program _ _ []
      (Effects.loaded_empty_tail _) (fun _ _ => rfl) path
  exact ⟨after, answers, terminal, _, generated,
    ConfigurationEncoding.decode_encode _ names vacant covers, trace, stored, gate⟩

/-- Authorization observed through the generated language still supplies
the independent specification history, without caller-supplied store support. -/
theorem loaded_generated_acceptance (specification : List Kernel.SpecificationEntry)
    (profile resolverState : Atom) (commands : List Command) (extensions source : Atom)
    (after : State) (target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (generated : (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing
      (ConfigurationLanguageDef.relationEnv MMUResolution.program) ConfigurationLanguageDef.language).MultiStep
      (ConfigurationEncoding.encode
        (protocolConfiguration (Effects.loaded MMUResolution.program) specification
          profile resolverState commands extensions source) []) target)
    (decoded : ConfigurationEncoding.decode target =
      some (finished after (List.replicate 3 (boolean true)) [] [])) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedExtends
      (specification.map Upstream.Lean3ProofAdmission.projectSpecification)
      (Upstream.Lean3Typing.projectRun
        ((commands.map SessionProtocol.inputDeclaration).map Kernel.ProofDeclaration.admission)) := by
  obtain ⟨fuel, completed⟩ := (ConfigurationLanguageDef.completed_run_iff_generated_path
    MMUResolution.program _ [] (Effects.loaded_empty_tail _) (fun _ _ => rfl) after _ [] []).mpr
    ⟨target, generated, decoded⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, specified⟩ :=
    accepted_consumes_specification (Effects.loaded MMUResolution.program) specification
      profile resolverState commands extensions source after fuel completed
  exact specified

end Mettapedia.Languages.MM0.MeTTa.MMUSubmission
