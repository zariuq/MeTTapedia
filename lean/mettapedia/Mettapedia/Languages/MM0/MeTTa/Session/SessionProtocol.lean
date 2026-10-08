import Mettapedia.Languages.MM0.MeTTa.Session.SharedSessionDriver

/-!
# The resolved MM0 start, submission and finish protocol

Ordinary declarations and fixed shared-theorem commands remain separate input
data. A trace records the actual source submission receipts and their observed
options. It adds no checker: logical specification history is obtained from
accepted receipts, with cut used only for the history of checked sharing.

The controls here use already resolved constructor data. The frontend's
per-request term-pool `let*` construction and parsed-line stream are separate
source interfaces.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.SessionProtocol

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (ProofDeclaration SpecificationEntry)
open SessionInitialization (Spaces)
open SessionDriver (Stored)
open SpecificationMatching (pendingValue declarationValue)

/-- Input alternatives, using the existing payloads and fixed sharing plan. -/
abbrev Command := ProofDeclaration ⊕ SharedService.Command

def commandValue : Command → Atom
  | .inl declaration => declarationValue declaration
  | .inr command => SharedService.commandValue command

def inputDeclaration : Command → ProofDeclaration
  | .inl declaration => declaration
  | .inr command => command.proofDeclaration

/-- An extracted logical declaration retains the input's public/local flag
and payload. Only a shared theorem's cut witness may differ in this history. -/
def HistoryImage : Command → ProofDeclaration → Prop
  | .inl original, declaration => declaration = original
  | .inr command, declaration => ∃ ordinary,
      declaration = ⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩

def submissionControl (command : Command) : Control :=
  .evaluate [("command", commandValue command)]
    (.expression [.symbol "mm0:submit", .var "command"])

def submissionControls (commands : List Command) : List Control := commands.map submissionControl

/-- Child evidence about a completed real submit, including stopped sessions.
The sharing case retains the existing child receipt and the original command. -/
structure Receipt (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (command : Command) (before after : State) (result : Option Kernel.SpecificationAdmission.State) : Prop where
  returned : PureReturns program [("command", commandValue command)] before
    (.expression [.symbol "mm0:submit", .var "command"]) after (boolean result.isSome)
  stored : Stored spaces result after
  evidence : match logical, command with
    | none, _ => result = none ∧ after = before
    | some current, .inl declaration => result = Kernel.SpecificationAdmission.step? current declaration
    | some current, .inr submitted => ∃ checking checked,
        after = checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result) ∧
        SharedSessionDriver.Receipt spaces current submitted before checking checked result

/-- One invocation uses exactly the existing driver branch, or its stored
failure branch. No proof witness is substituted into the source request. -/
theorem submit_returns (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (command : Command) (before : State) (represented : Stored spaces logical before) :
    ∃ after result, Receipt spaces logical command before after result := by
  cases represented with
  | stopped failed =>
      refine ⟨before, none, ?_⟩
      exact ⟨DeclarationScope.refused_submit_returns [("command", commandValue command)] before
        (commandValue command) "command" rfl failed, .stopped failed, rfl, rfl⟩
  | active live =>
      cases command with
      | inl declaration =>
          obtain ⟨after, returned, stored⟩ := SessionDriver.ordinary_submit_returns spaces _ declaration
            [("command", declarationValue declaration)] "command" before live rfl
          exact ⟨after, _, returned, stored, rfl⟩
      | inr submitted =>
          obtain ⟨checking, checked, result, returned, receipt, stored⟩ :=
            SharedSessionDriver.captured_returns spaces _ submitted
              [("command", SharedService.commandValue submitted)] "command" before live rfl
          exact ⟨_, result, returned, stored, checking, checked, rfl, receipt⟩

theorem Receipt.stopped {spaces : Spaces} {command : Command} {before after : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces none command before after result) : result = none ∧ after = before :=
  receipt.evidence

theorem Receipt.advances_from_live {spaces : Spaces} {logical result : Option Kernel.SpecificationAdmission.State}
    {command : Command} {before after : State} (receipt : Receipt spaces logical command before after result)
    (advanced : result.isSome = true) : logical.isSome = true := by
  cases logical with
  | none => rw [receipt.stopped.1] at advanced; cases advanced
  | some current => rfl

/-- Accepted source evidence supplies the independently checked logical step.
The sharing witness here is extracted only after the fixed source check. -/
theorem Receipt.step {spaces : Spaces} {logical next : Kernel.SpecificationAdmission.State}
    {result : Option Kernel.SpecificationAdmission.State} {command : Command} {before after : State}
    (receipt : Receipt spaces (some logical) command before after result) (advanced : result = some next) :
    ∃ declaration, HistoryImage command declaration ∧ Kernel.SpecificationAdmission.Step logical declaration next := by
  cases command with
  | inl declaration =>
      exact ⟨declaration, rfl, (Kernel.SpecificationAdmission.step_eq_some_iff _ _ _).mp
        (receipt.evidence.symm.trans advanced)⟩
  | inr submitted =>
      obtain ⟨checking, checked, _, shared⟩ := receipt.evidence
      obtain ⟨ordinary, step⟩ := shared.specification_step advanced
      exact ⟨⟨.theoremDecl submitted.index submitted.declaration submitted.dummies ordinary, submitted.isLocal⟩,
        ⟨ordinary, rfl⟩, step⟩

/-- A list of actual checked receipts, not a second operational semantics. -/
inductive Trace (spaces : Spaces) : Option Kernel.SpecificationAdmission.State → State →
    List Command → List Bool → Option Kernel.SpecificationAdmission.State → State → Prop where
  | nil (logical : Option Kernel.SpecificationAdmission.State) (before : State) :
      Trace spaces logical before [] [] logical before
  | cons {logical next terminal : Option Kernel.SpecificationAdmission.State}
      {before middle after : State} {command : Command} {commands : List Command} {answers : List Bool} :
      Receipt spaces logical command before middle next →
      Trace spaces next middle commands answers terminal after →
      Trace spaces logical before (command :: commands) (next.isSome :: answers) terminal after

/-- The source driver constructs receipts for every resolved input list,
including the suffix after a refused command. -/
theorem trace_exists (spaces : Spaces) (logical : Option Kernel.SpecificationAdmission.State)
    (commands : List Command) (before : State) (represented : Stored spaces logical before) :
    ∃ after answers terminal, Trace spaces logical before commands answers terminal after ∧ Stored spaces terminal after := by
  induction commands generalizing logical before with
  | nil => exact ⟨before, [], logical, .nil _ _, represented⟩
  | cons command commands ih =>
      obtain ⟨middle, next, receipt⟩ := submit_returns spaces logical command before represented
      obtain ⟨after, answers, terminal, rest, stored⟩ := ih next middle receipt.stored
      exact ⟨after, next.isSome :: answers, terminal, .cons receipt rest, stored⟩

theorem Trace.length {spaces : Spaces} {logical terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after) : answers.length = commands.length := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simp only [List.length_cons, ih]

theorem Trace.append {spaces : Spaces} {logical middle terminal : Option Kernel.SpecificationAdmission.State}
    {before checking after : State} {first second : List Command} {left right : List Bool}
    (one : Trace spaces logical before first left middle checking)
    (two : Trace spaces middle checking second right terminal after) :
    Trace spaces logical before (first ++ second) (left ++ right) terminal after := by
  induction one with
  | nil => exact two
  | cons receipt rest ih => exact .cons receipt (ih two)

theorem Trace.advances {spaces : Spaces} {logical terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after) :
    terminal.isSome = true ↔ logical.isSome = true ∧ answers = List.replicate commands.length true := by
  induction trace with
  | nil => simp
  | @cons logical next terminal before middle after command commands answers receipt rest ih =>
      rw [ih]
      simp only [List.length_cons, List.replicate_succ, List.cons.injEq]
      exact ⟨fun given => ⟨receipt.advances_from_live given.1, given.1, given.2⟩,
        fun given => ⟨given.2.1, given.2.2⟩⟩

/-- The existing source sequencer retains every Boolean occurrence. -/
theorem Trace.path {spaces : Spaces} {logical terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after) (collected : List Atom) :
    (theory program).MultiStep
      { state := before, control := .sequence (submissionControls commands) collected }
      (finished after (collected ++ answers.map boolean) [] []) := by
  induction trace generalizing collected with
  | nil =>
      simpa only [submissionControls, List.map_nil, List.append_nil] using
        (show (theory program).MultiStep { state := _, control := .sequence [] collected }
          (finished _ collected [] []) from .step (step_transition rfl) (.refl _))
  | @cons logical next terminal before middle after command commands answers receipt rest ih =>
      simpa only [submissionControls, List.map_cons, List.append_assoc, List.singleton_append] using
        sequence_cons_answers program before middle after (submissionControl command) (submissionControls commands)
          collected [boolean next.isSome] (collected ++ [boolean next.isSome] ++ answers.map boolean)
          receipt.returned (ih (collected ++ [boolean next.isSome]))

def finishedStatus (logical : Option Kernel.SpecificationAdmission.State) : Bool :=
  (logical.bind fun state => if state.pending.isEmpty then some state.theory else none).isSome

theorem Trace.finish_path {spaces : Spaces} {logical terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces logical before commands answers terminal after)
    (stored : Stored spaces terminal after) (collected : List Atom) :
    (theory program).MultiStep
      { state := before, control := .sequence
          (submissionControls commands ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) collected }
      (finished after (collected ++ answers.map boolean ++ [boolean (finishedStatus terminal)]) [] []) := by
  induction trace generalizing collected with
  | nil =>
      simpa only [submissionControls, List.map_nil, List.nil_append, List.append_nil] using
        sequence_cons_answers program _ _ _ (.evaluate [] (.expression [.symbol "mm0:finish"])) [] collected
          [boolean (finishedStatus _)] (collected ++ [boolean (finishedStatus _)])
          (SessionDriver.finish_returns spaces _ _ [] stored) (.step (step_transition rfl) (.refl _))
  | @cons logical next terminal before middle after command commands answers receipt rest ih =>
      have composed := sequence_cons_answers program before middle after (submissionControl command)
          (submissionControls commands ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) collected
          [boolean next.isSome] _ receipt.returned (ih stored (collected ++ [boolean next.isSome]))
      simpa only [submissionControls, List.map_cons, List.cons_append, List.append_assoc,
        List.singleton_append, List.nil_append] using composed

/-- Logical history is obtained from the accepted original receipt trace.
Its extracted witness is never used as a replacement source command. -/
theorem Trace.history {spaces : Spaces} {initial terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces initial before commands answers terminal after)
    (logical next : Kernel.SpecificationAdmission.State) (started : initial = some logical) (advanced : terminal = some next) :
    ∃ declarations, List.Forall₂ HistoryImage commands declarations ∧
      Kernel.SpecificationAdmission.Runs logical declarations next := by
  induction trace generalizing logical next with
  | nil state before =>
      have same : logical = next := Option.some.inj (started.symm.trans advanced)
      exact ⟨[], .nil, same ▸ .nil logical⟩
  | @cons initial middle terminal before checking after command commands answers receipt rest ih =>
      have live : middle.isSome = true := ((rest.advances).mp (by rw [advanced]; rfl)).1
      cases middle with
      | none => cases live
      | some state =>
          obtain ⟨declaration, image, step⟩ := Receipt.step (by simpa only [started] using receipt) rfl
          obtain ⟨declarations, images, history⟩ := ih state next rfl advanced
          exact ⟨declaration :: declarations, .cons image images, .cons step history⟩

theorem HistoryImage.axioms {command : Command} {declaration : ProofDeclaration}
    (image : HistoryImage command declaration) :
    Kernel.SpecificationAdmission.declarationAxioms [inputDeclaration command] =
      Kernel.SpecificationAdmission.declarationAxioms [declaration] := by
  cases command with
  | inl original => cases image; rfl
  | inr submitted => obtain ⟨ordinary, rfl⟩ := image; rfl

theorem history_axioms {commands : List Command} {declarations : List ProofDeclaration}
    (images : List.Forall₂ HistoryImage commands declarations) :
    Kernel.SpecificationAdmission.declarationAxioms (commands.map inputDeclaration) =
      Kernel.SpecificationAdmission.declarationAxioms declarations := by
  induction images with
  | nil => rfl
  | @cons command declaration commands declarations image rest ih =>
      cases command with
      | inl original =>
          have same : declaration = original := image
          subst declaration
          rcases original with ⟨admission, flag⟩
          cases admission <;> simpa [inputDeclaration, Kernel.SpecificationAdmission.declarationAxioms] using ih
      | inr submitted =>
          obtain ⟨ordinary, rfl⟩ := image
          simpa [inputDeclaration, SharedService.Command.proofDeclaration, SharedService.Command.admission,
            Kernel.SpecificationAdmission.declarationAxioms] using ih

def protocolControls (specification : List SpecificationEntry) (commands : List Command) : List Control :=
  .evaluate [("spec", pendingValue specification)] (.expression [.symbol "mm0:start", .var "spec"]) ::
    submissionControls commands ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]

def protocolConfiguration (before : State) (specification : List SpecificationEntry) (commands : List Command) : Configuration :=
  { state := before, control := .sequence (protocolControls specification commands) [] }

theorem Trace.protocol_path (before : State) (specification : List SpecificationEntry)
    {commands : List Command} {answers : List Bool} {terminal : Option Kernel.SpecificationAdmission.State} {after : State}
    (trace : Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
      (SessionInitialization.startState before (pendingValue specification)) commands answers terminal after)
    (stored : Stored (SessionInitialization.allocatedSpaces before) terminal after) :
    (theory program).MultiStep (protocolConfiguration before specification commands)
      (finished after (boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)]) [] []) := by
  have start := SessionInitialization.returns [("spec", pendingValue specification)] before
    (pendingValue specification) "spec" rfl
  have rest := trace.finish_path stored [boolean true]
  have composed := sequence_cons_answers program before (SessionInitialization.startState before (pendingValue specification)) after
    (.evaluate [("spec", pendingValue specification)] (.expression [.symbol "mm0:start", .var "spec"]))
    (submissionControls commands ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) [] [boolean true] _ start rest
  simpa only [protocolConfiguration, protocolControls, List.nil_append, List.singleton_append,
    List.cons_append] using composed

/-- Start earns all physical premises. The existing sequencer then runs every
original command and the read-only finish condition, including stopped suffixes. -/
theorem protocol_returns (before : State) (specification : List SpecificationEntry) (commands : List Command) :
    ∃ after answers terminal,
      (theory program).MultiStep (protocolConfiguration before specification commands)
        (finished after (boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)]) [] []) ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (pendingValue specification)) commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      answers.length = commands.length ∧
      ((boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)]) =
        List.replicate (commands.length + 2) (boolean true) ↔
          ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  let spaces := SessionInitialization.allocatedSpaces before
  let initial := SessionInitialization.startState before (pendingValue specification)
  obtain ⟨after, answers, terminal, trace, stored⟩ := trace_exists spaces (some ⟨{}, specification⟩)
    commands initial (.active (SessionDriver.start_live before specification))
  have length := trace.length
  refine ⟨after, answers, terminal, ?_, trace, stored, length, ?_⟩
  · exact trace.protocol_path before specification stored
  · constructor
    · intro allTrue
      have finalAnswer : boolean (finishedStatus terminal) = boolean true :=
        (List.eq_replicate_iff.mp allTrue).2 _ (by simp)
      cases terminal with
      | none => simp [finishedStatus, boolean] at finalAnswer
      | some logical =>
          cases pending : logical.pending with
          | nil => exact ⟨logical.theory, by cases logical; simpa using pending⟩
          | cons entry rest => simp [finishedStatus, pending, boolean] at finalAnswer
    · rintro ⟨finalTheory, rfl⟩
      have accepted : answers = List.replicate commands.length true :=
        ((trace.advances).mp rfl).2
      rw [accepted]
      simp only [List.map_replicate, finishedStatus, Option.bind_some, List.isEmpty_nil, ↓reduceIte,
        Option.isSome_some]
      rw [show commands.length + 2 = (commands.length + 1) + 1 by omega, List.replicate_succ]
      simpa only [List.cons_append, List.replicate_succ, List.replicate_zero, List.nil_append] using congrArg (List.cons (boolean true))
        (List.replicate_add commands.length 1 (boolean true)).symm

theorem HistoryImage.project {command : Command} {declaration : ProofDeclaration}
    (image : HistoryImage command declaration) :
    Upstream.Lean3Typing.projectAdmission declaration.admission =
      Upstream.Lean3Typing.projectAdmission (inputDeclaration command).admission := by
  cases command with
  | inl original => cases image; rfl
  | inr submitted => obtain ⟨ordinary, rfl⟩ := image; rfl

/-- Mario's declaration projection forgets proof witnesses. Its logical
history therefore has exactly the original commands' projected payloads. -/
theorem history_projection {commands : List Command} {declarations : List ProofDeclaration}
    (images : List.Forall₂ HistoryImage commands declarations) :
    Upstream.Lean3Typing.projectRun (declarations.map ProofDeclaration.admission) =
      Upstream.Lean3Typing.projectRun ((commands.map inputDeclaration).map ProofDeclaration.admission) := by
  induction images with
  | nil => rfl
  | @cons command declaration commands declarations image rest ih =>
      have same := congrArg (List.cons (Upstream.Lean3Typing.projectAdmission declaration.admission)) ih
      simpa only [Upstream.Lean3Typing.projectRun, List.map_cons, image.project] using same

/-- A terminal consumed specification earns the independent verifier, the
exact axiom basis and the specified structural extension from actual receipts. -/
theorem Trace.consumed_specification {spaces : Spaces} {specification : List SpecificationEntry}
    {terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List Command} {answers : List Bool}
    (trace : Trace spaces (some ⟨{}, specification⟩) before commands answers terminal after)
    (finalTheory : Kernel.Theory) (finished : terminal = some ⟨finalTheory, []⟩) :
    ∃ declarations,
      List.Forall₂ HistoryImage commands declarations ∧
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨finalTheory, []⟩ ∧
      Kernel.SpecificationAdmission.verify? specification declarations = some finalTheory ∧
      Kernel.SpecificationAdmission.declarationAxioms (commands.map inputDeclaration) =
        Kernel.SpecificationAdmission.specificationAxioms specification ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedExtends
        (specification.map Upstream.Lean3ProofAdmission.projectSpecification)
        (Upstream.Lean3Typing.projectRun ((commands.map inputDeclaration).map ProofDeclaration.admission)) := by
  obtain ⟨declarations, images, history⟩ := trace.history ⟨{}, specification⟩ ⟨finalTheory, []⟩ rfl finished
  have verified := (Kernel.SpecificationAdmission.verify_eq_some_iff _ _ _).mpr history
  refine ⟨declarations, images, history, verified,
    (history_axioms images).trans (Kernel.SpecificationAdmission.verified_axioms_exact verified), ?_⟩
  rw [← history_projection images]
  exact Upstream.Lean3ProofAdmission.checked_specification_extension verified

/-- A fixed shared source receipt provides its Mario proof in the actual
preceding history, before the submitted theorem is published. -/
theorem Receipt.preceding_shared_proof {spaces : Spaces} {logical next : Kernel.SpecificationAdmission.State}
    {result : Option Kernel.SpecificationAdmission.State} {command : SharedService.Command}
    {before after : State}
    (receipt : Receipt spaces (some logical) (.inr command) before after result) (advanced : result = some next)
    (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (history.map ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
      (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨checking, checked, _, shared⟩ := receipt.evidence
  exact shared.preceding_specified_proof advanced specification history preceding

private theorem history_snoc {before middle after : Kernel.SpecificationAdmission.State}
    {history : List ProofDeclaration} {declaration : ProofDeclaration}
    (checked : Kernel.SpecificationAdmission.Runs before history middle)
    (step : Kernel.SpecificationAdmission.Step middle declaration after) :
    Kernel.SpecificationAdmission.Runs before (history ++ [declaration]) after := by
  induction checked with
  | nil => exact .cons step (.nil _)
  | cons first rest ih => exact .cons first (ih step)

/-- Every shared command in an advancing trace has a specified proof in an
earned preceding prefix. This is derived from its fixed receipt, not from a
substituted ordinary witness in the input command list. -/
theorem Trace.shared_preceding_proof {spaces : Spaces} {initial terminal : Option Kernel.SpecificationAdmission.State}
    {before after : State} {commands : List Command} {answers : List Bool}
    (trace : Trace spaces initial before commands answers terminal after)
    (logical next : Kernel.SpecificationAdmission.State) (started : initial = some logical) (advanced : terminal = some next)
    (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical)
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  induction trace generalizing logical next history with
  | nil => cases belongs
  | @cons initial middle terminal before checking after head commands answers receipt rest ih =>
      have live : middle.isSome = true := ((rest.advances).mp (by rw [advanced]; rfl)).1
      cases middle with
      | none => cases live
      | some state =>
          have actual : Receipt spaces (some logical) head before checking (some state) := by
            simpa only [started] using receipt
          rcases List.mem_cons.mp belongs with same | later
          · subst head
            exact ⟨history, logical, preceding,
              actual.preceding_shared_proof rfl specification history preceding⟩
          · obtain ⟨declaration, _, step⟩ := actual.step rfl
            exact ih state next rfl advanced (history ++ [declaration]) (history_snoc preceding step) later

/-- Completed execution is stable under added fuel for the whole protocol,
with its original command trace and stored logical option retained. -/
theorem sufficient_fuel (before : State) (specification : List SpecificationEntry) (commands : List Command) :
    ∃ after answers terminal fuel,
      (∀ extra, run program (fuel + extra) (protocolConfiguration before specification commands) =
        .complete after (boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)]) [] []) ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (pendingValue specification)) commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      answers.length = commands.length ∧
      ((boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)]) =
        List.replicate (commands.length + 2) (boolean true) ↔
          ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, path, trace, stored, length, accepted⟩ := protocol_returns before specification commands
  obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ after _ [] []).mpr path
  exact ⟨after, answers, terminal, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed,
    trace, stored, length, accepted⟩

/-- Any observed completed protocol has the same Boolean occurrence list,
length and earned session trace as the constructed source execution. -/
theorem completed_protocol (before : State) (specification : List SpecificationEntry) (commands : List Command)
    (after : State) (fuel : Nat) (outputs unread printed : List Atom)
    (completed : run program fuel (protocolConfiguration before specification commands) = .complete after outputs unread printed) :
    ∃ answers terminal,
      outputs = boolean true :: answers.map boolean ++ [boolean (finishedStatus terminal)] ∧
      unread = [] ∧ printed = [] ∧
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (pendingValue specification)) commands answers terminal after ∧
      Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      outputs.length = commands.length + 2 ∧
      (outputs = List.replicate (commands.length + 2) (boolean true) ↔
        ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨reference, answers, terminal, referenceFuel, returned, trace, stored, length, accepted⟩ :=
    sufficient_fuel before specification commands
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    reference after _ [] [] outputs unread printed referenceCompleted completed
  subst after
  refine ⟨answers, terminal, sameAnswers.symm, sameUnread.symm, samePrinted.symm, trace, stored, ?_, ?_⟩
  · rw [← sameAnswers]; simp [length]
  · rw [← sameAnswers]; exact accepted

/-- An all-true observed source completion consumes the independently supplied
specification, earns its exact axiom basis and its Mario structural extension.
The input commands and fixed sharing receipts remain unchanged. -/
theorem accepted_consumes_specification (before : State) (specification : List SpecificationEntry)
    (commands : List Command) (after : State) (fuel : Nat)
    (accepted : run program fuel (protocolConfiguration before specification commands) =
      .complete after (List.replicate (commands.length + 2) (boolean true)) [] []) :
    ∃ finalTheory declarations answers,
      Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (pendingValue specification)) commands answers (some ⟨finalTheory, []⟩) after ∧
      SessionDriver.Live (SessionInitialization.allocatedSpaces before) ⟨finalTheory, []⟩ after ∧
      List.Forall₂ HistoryImage commands declarations ∧
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ declarations ⟨finalTheory, []⟩ ∧
      Kernel.SpecificationAdmission.verify? specification declarations = some finalTheory ∧
      Kernel.SpecificationAdmission.declarationAxioms (commands.map inputDeclaration) =
        Kernel.SpecificationAdmission.specificationAxioms specification ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedExtends
        (specification.map Upstream.Lean3ProofAdmission.projectSpecification)
        (Upstream.Lean3Typing.projectRun ((commands.map inputDeclaration).map ProofDeclaration.admission)) := by
  obtain ⟨answers, terminal, _, _, _, trace, stored, _, gate⟩ :=
    completed_protocol before specification commands after fuel _ [] [] accepted
  obtain ⟨finalTheory, same⟩ := gate.mp rfl
  obtain ⟨declarations, images, history, verified, axioms, specified⟩ := trace.consumed_specification finalTheory same
  rw [same] at trace stored
  cases stored with
  | active live => exact ⟨finalTheory, declarations, answers, trace, live, images, history, verified, axioms, specified⟩

/-- Every shared theorem in an all-true observed protocol has a Mario proof in
its actual preceding specification prefix, independent of its new table row. -/
theorem accepted_shared_preceding_proof (before : State) (specification : List SpecificationEntry)
    (commands : List Command) (after : State) (fuel : Nat)
    (accepted : run program fuel (protocolConfiguration before specification commands) =
      .complete after (List.replicate (commands.length + 2) (boolean true)) [] [])
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨finalTheory, declarations, answers, trace, _, _, _, _, _, _⟩ :=
    accepted_consumes_specification before specification commands after fuel accepted
  exact trace.shared_preceding_proof ⟨{}, specification⟩ ⟨finalTheory, []⟩ rfl rfl specification [] (.nil _) command belongs

namespace Controls

open Kernel

private def info : SortInfo := { provable := true }
private def primitive : TermDecl := ⟨[], 0, ∅⟩
private def statement : TheoremDecl := ⟨[], [], .term 1⟩
private def sortInput : ProofDeclaration := ⟨.sort 0 info, false⟩
private def termInput : ProofDeclaration := ⟨.term 1 primitive, false⟩
private def axiomInput : ProofDeclaration := ⟨.axiomDecl 10 statement, false⟩
private def prefixCommands : List Command := [.inl sortInput, .inl termInput, .inl axiomInput]
private def specification : List SpecificationEntry :=
  [.sort 0 info, .term 1 primitive, .axiomDecl 10 statement, .theoremDecl 12 statement]
private def sorted : Kernel.SpecificationAdmission.State :=
  ⟨{ sorts := [(0, info)] }, [.term 1 primitive, .axiomDecl 10 statement, .theoremDecl 12 statement]⟩
private def typed : Kernel.SpecificationAdmission.State :=
  ⟨{ sorts := [(0, info)], terms := [(1, primitive)] }, [.axiomDecl 10 statement, .theoremDecl 12 statement]⟩
private def axiomatized : Kernel.SpecificationAdmission.State :=
  ⟨{ sorts := [(0, info)], terms := [(1, primitive)], theorems := [(10, statement)] }, [.theoremDecl 12 statement]⟩
private def submitted : SharedService.Command :=
  ⟨false, 12, statement, [],
    [⟨some (.term 1), .theoremApp 10 [] []⟩, ⟨none, .hyp 0⟩], .hyp 1⟩

private theorem prefix_trace (before : State) :
    ∃ after, Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
      (SessionInitialization.startState before (pendingValue specification)) prefixCommands [true, true, true]
      (some axiomatized) after ∧ Stored (SessionInitialization.allocatedSpaces before) (some axiomatized) after := by
  let spaces := SessionInitialization.allocatedSpaces before
  let initial := SessionInitialization.startState before (pendingValue specification)
  obtain ⟨first, r₁, s₁⟩ := SessionDriver.ordinary_submit_returns spaces ⟨{}, specification⟩ sortInput
    [("command", declarationValue sortInput)] "command" initial (SessionDriver.start_live before specification) rfl
  change Stored spaces (some sorted) first at s₁
  let p₁ : Receipt spaces (some ⟨{}, specification⟩) (.inl sortInput) initial first (some sorted) := ⟨r₁, s₁, rfl⟩
  cases s₁ with
  | active live₁ =>
      obtain ⟨second, r₂, s₂⟩ := SessionDriver.ordinary_submit_returns spaces sorted termInput
        [("command", declarationValue termInput)] "command" first live₁ rfl
      change Stored spaces (some typed) second at s₂
      let p₂ : Receipt spaces (some sorted) (.inl termInput) first second (some typed) := ⟨r₂, s₂, rfl⟩
      cases s₂ with
      | active live₂ =>
          obtain ⟨third, r₃, s₃⟩ := SessionDriver.ordinary_submit_returns spaces typed axiomInput
            [("command", declarationValue axiomInput)] "command" second live₂ rfl
          change Stored spaces (some axiomatized) third at s₃
          let p₃ : Receipt spaces (some typed) (.inl axiomInput) second third (some axiomatized) := ⟨r₃, s₃, rfl⟩
          exact ⟨third, .cons p₁ (.cons p₂ (.cons p₃ (.nil _ _))), s₃⟩

private theorem formed : SharedProof.Formation axiomatized.theory submitted.index submitted.declaration submitted.dummies := by
  refine ⟨rfl, (TheoremDecl.check_iff _ _ _).mp ?_, ?_⟩
  · decide +kernel
  · intro sort impossible; cases impossible

private theorem checked {spaces : Spaces} {before : State}
    (ready : AdmissionChecks.Ready spaces axiomatized.theory before) :
    Sharing.Checked (Admission.proofContext submitted.declaration submitted.dummies) submitted.root
      submitted.declaration.conclusion (SharedService.tables spaces axiomatized.theory submitted.declaration ready) submitted.saved := by
  apply Sharing.Checked.save (actual := .term 1)
  · apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
    simp only [SharedService.tables, AdmissionChecks.proofTables]
    decide +kernel
  · exact Or.inr rfl
  · apply Sharing.Checked.save (actual := .term 1)
    · apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
      simp only [ProofStore.extend, SharedService.tables, AdmissionChecks.proofTables]
      decide +kernel
    · exact Or.inl rfl
    · apply Sharing.Checked.root
      apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
      simp only [ProofStore.extend, SharedService.tables, AdmissionChecks.proofTables]
      decide +kernel

/-- Startup, three ordinary declarations, a nonempty sharing plan and EOF
produce six true occurrences from any initial native state. -/
theorem full_mixed_source_accepts (before : State) :
    ∃ after fuel, run program fuel
      (protocolConfiguration before specification (prefixCommands ++ [.inr submitted])) =
        .complete after (List.replicate 6 (boolean true)) [] [] := by
  obtain ⟨middle, prior, stored⟩ := prefix_trace before
  cases stored with
  | active live =>
      obtain ⟨checking, checkedState, result, returned, child, represented⟩ := SharedSessionDriver.captured_returns
        (SessionInitialization.allocatedSpaces before) axiomatized submitted
        [("command", SharedService.commandValue submitted)] "command" middle live rfl
      have same : result = some (SharedService.admittedState axiomatized submitted []) :=
        (child.successful _).mpr ⟨[], rfl, rfl, formed, checked child.input.ready⟩
      subst result
      let receipt : Receipt (SessionInitialization.allocatedSpaces before) (some axiomatized) (.inr submitted) middle
          (checkedState.putCell "mm0-session" (SpecificationStep.resultValue _ (some (SharedService.admittedState axiomatized submitted []))))
          (some (SharedService.admittedState axiomatized submitted [])) :=
        ⟨returned, represented, checking, checkedState, rfl, child⟩
      have full := prior.append (.cons receipt (.nil _ _))
      have path := full.protocol_path before specification represented
      obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ _ _ [] []).mpr path
      exact ⟨_, fuel, by simpa [finishedStatus, SharedService.admittedState] using completed⟩

/-- This available ordinary proof does not repair a refused shared initializer. -/
theorem available_root_checks :
    ProofWitness.check axiomatized.theory.termSignature axiomatized.theory.definitionSignature
      axiomatized.theory.theoremSignature [] [] (.theoremApp 10 [] []) statement.conclusion = true := by decide +kernel

private def repaired : SharedService.Command := { submitted with saved := [], root := .theoremApp 10 [] [] }
private def badRoot : SharedService.Command := { submitted with saved := [], root := .hyp 0 }
private def badInitializer : SharedService.Command := { repaired with saved := [⟨none, .hyp 0⟩] }

private theorem refused_root {spaces : Spaces} {before : State}
    (ready : AdmissionChecks.Ready spaces axiomatized.theory before) :
    ¬ SharedService.Accepted spaces axiomatized badRoot ready := by
  rintro ⟨_, _, sharing⟩
  have original := (Sharing.checked_nil_iff _ _ _ _).mp sharing
  have computed := original.eval
  simp [SharedService.tables, AdmissionChecks.proofTables, badRoot, submitted,
    statement, ProofWitness.proof?] at computed

private theorem refused_initializer {spaces : Spaces} {before : State}
    (ready : AdmissionChecks.Ready spaces axiomatized.theory before) :
    ¬ SharedService.Accepted spaces axiomatized badInitializer ready := by
  rintro ⟨_, _, sharing⟩
  exact Sharing.checked_cons_refused _ _ _ _ ⟨none, .hyp 0⟩ []
    (by
      simp only [SharedService.tables, AdmissionChecks.proofTables]
      decide +kernel) sharing

private theorem refused_protocol (before : State) (command : SharedService.Command)
    (refused : ∀ (spaces : Spaces) (checking : State) (ready : AdmissionChecks.Ready spaces axiomatized.theory checking),
      ¬ SharedService.Accepted spaces axiomatized command ready) :
    ∃ after fuel, run program fuel
      (protocolConfiguration before specification (prefixCommands ++ [.inr command, .inr repaired])) =
        .complete after [boolean true, boolean true, boolean true, boolean true,
          boolean false, boolean false, boolean false] [] [] := by
  obtain ⟨middle, prior, stored⟩ := prefix_trace before
  cases stored with
  | active live =>
      obtain ⟨checking, checkedState, result, returned, child, represented⟩ := SharedSessionDriver.captured_returns
        (SessionInitialization.allocatedSpaces before) axiomatized command
        [("command", SharedService.commandValue command)] "command" middle live rfl
      have same : result = none := child.refused.mpr (refused _ _ child.input.ready)
      subst result
      let receipt : Receipt (SessionInitialization.allocatedSpaces before) (some axiomatized) (.inr command) middle
          (checkedState.putCell "mm0-session" (SpecificationStep.resultValue _ none)) none :=
        ⟨returned, represented, checking, checkedState, rfl, child⟩
      obtain ⟨later, result, stopped⟩ := submit_returns _ none (.inr repaired) _ represented
      obtain ⟨sameResult, sameState⟩ := stopped.stopped
      subst result
      subst later
      have full := prior.append (.cons receipt (.cons stopped (.nil _ _)))
      have path := full.protocol_path before specification stopped.stored
      obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ _ _ [] []).mpr path
      exact ⟨_, fuel, by simpa [finishedStatus] using completed⟩

/-- A bad supplied root stops the protocol; a later valid root for the same
theorem cannot reopen it or turn any refused occurrence into true. -/
theorem full_bad_root_is_sticky (before : State) :
    ∃ after fuel, run program fuel
      (protocolConfiguration before specification (prefixCommands ++ [.inr badRoot, .inr repaired])) =
        .complete after [boolean true, boolean true, boolean true, boolean true,
          boolean false, boolean false, boolean false] [] [] :=
  refused_protocol before badRoot (fun _ _ ready => refused_root ready)

/-- An initializer's future reference is refused even with a valid ordinary
root and a later repaired submission. Absence of an expectation checks it. -/
theorem full_future_initializer_is_sticky (before : State) :
    ∃ after fuel, run program fuel
      (protocolConfiguration before specification (prefixCommands ++ [.inr badInitializer, .inr repaired])) =
        .complete after [boolean true, boolean true, boolean true, boolean true,
          boolean false, boolean false, boolean false] [] [] :=
  refused_protocol before badInitializer (fun _ _ ready => refused_initializer ready)

end Controls

end Mettapedia.Languages.MM0.MeTTa.SessionProtocol
