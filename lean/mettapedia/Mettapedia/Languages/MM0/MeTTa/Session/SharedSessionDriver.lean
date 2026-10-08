import Mettapedia.Languages.MM0.MeTTa.Session.SharedService
import Mettapedia.Languages.MM0.MeTTa.Session.SessionDriver
import Mettapedia.Languages.MM0.MeTTa.Session.SessionProof

/-!
# Shared theorem submissions in the retained session driver

The actual submit reset earns the current cache scope, then the shared
service checks the supplied saved initializers and root. The driver stores
the observed service option and returns its Boolean status. Logical cut and
specification history are consequences of checked sharing; they never replace
a refused submitted initializer or root.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.SharedSessionDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean handleValue)
open NamedSpaces (Handle)
open Kernel (Admission Theory ProofWitness ProofDeclaration SpecificationEntry)
open SessionInitialization (Spaces stateValue)
open SpecificationMatching (pendingValue)
open SessionDriver (Live Stored)
open ListAccess (optionValue)

/-- Old proof-vector values need only have their physical row shape. The
shared initializer rebuilds their contents in the new checking scope. -/
theorem input_after_reset {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {before checking : State} (live : Live spaces logical before)
    (empty : checking.read spaces.cache = some [])
    (others : ∀ handle, handle ≠ spaces.cache → checking.read handle = before.read handle)
    (cells : checking.cells = before.cells) : SharedService.Input spaces logical checking := by
  refine ⟨live.ready_after_reset empty others cells, ?_, ?_⟩
  · rw [cells]; exact live.proofCell
  · obtain ⟨rows, allocated, shaped⟩ := live.proofRows
    exact ⟨rows, (others spaces.proofs live.tables.separate_proof).trans allocated, shaped⟩

/-- A receipt records the real reset, child execution, physical frame and
fixed submitted evidence. -/
structure Receipt (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before checking checked : State)
    (result : Option Kernel.SpecificationAdmission.State) : Prop where
  input : SharedService.Input spaces logical checking
  empty : checking.read spaces.cache = some []
  otherReads : ∀ handle, handle ≠ spaces.cache → checking.read handle = before.read handle
  cells : checking.cells = before.cells
  called : SharedService.Call spaces logical command checking checked result
  frame : SharedService.EffectFrame spaces logical command checking checked result
  successful : ∀ next, result = some next ↔
    ∃ remaining, next = SharedService.admittedState logical command remaining ∧
      Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
      Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
        command.declaration.conclusion (SharedService.tables spaces logical.theory command.declaration input.ready)
        command.saved
  refused : result = none ↔ ¬ SharedService.Accepted spaces logical command input.ready

/-- Recording the same source result earns the next physical session state. -/
theorem Receipt.stored {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result) :
    Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) :=
  SessionDriver.stored_after_result result checked receipt.frame.tables receipt.frame.cache.1
    receipt.frame.proofCell receipt.frame.cacheRows receipt.frame.proofRows

theorem Receipt.other_reads {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    (handle : Handle) (notCache : handle ≠ spaces.cache) (notProofs : handle ≠ spaces.proofs)
    (notTheorems : handle ≠ spaces.theorems) :
    (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)).read handle = before.read handle := by
  rw [NamedSpaces.Store.cell_preserves_spaces, receipt.frame.other handle notCache notProofs notTheorems]
  exact receipt.otherReads handle notCache

theorem Receipt.other_cell {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    (name : String) (different : name ≠ "mm0-session") :
    (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)).cells name = before.cells name := by
  rw [NamedSpaces.Store.cell_read_other _ _ _ _ different, receipt.frame.cells, receipt.cells]

/-- The observed Boolean reflects this same command's fixed sharing gates. -/
theorem Receipt.accepted_iff {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result) :
    result.isSome = true ↔ SharedService.Accepted spaces logical command receipt.input.ready := by
  constructor
  · intro accepted
    cases result with
    | none => cases accepted
    | some next =>
        obtain ⟨remaining, _, pending, formed, sharing⟩ := (receipt.successful next).mp rfl
        exact ⟨⟨remaining, pending⟩, formed, sharing⟩
  · intro accepted
    cases result with
    | none => exact False.elim ((receipt.refused.mp rfl) accepted)
    | some next => rfl

/-- The retained submit body supplies its reset facts to the child, stores
that child's observed option, and retains its exact fixed-sharing gates. -/
theorem captured_returns (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (bindings : Subst) (name : String) (before : State)
    (live : Live spaces logical before)
    (captured : applySubst bindings (.var name) = SharedService.commandValue command) :
    ∃ checking checked result,
      PureReturns program bindings before (.expression [.symbol "mm0:submit", .var name])
        (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) (boolean result.isSome) ∧
      Receipt spaces logical command before checking checked result ∧
      Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) := by
  let retained (checking checked : State) (answer : Option Atom) : Prop :=
    ∃ (result : Option Kernel.SpecificationAdmission.State) (input : SharedService.Input spaces logical checking),
      answer = result.map (fun next => stateValue spaces (pendingValue next.pending)) ∧
      SharedService.Call spaces logical command checking checked result ∧
      SharedService.EffectFrame spaces logical command checking checked result ∧
      (∀ next, result = some next ↔
        ∃ remaining, next = SharedService.admittedState logical command remaining ∧
          Kernel.SpecificationAdmission.pending? logical.pending command.proofDeclaration = some remaining ∧
          Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
          Sharing.Checked (Admission.proofContext command.declaration command.dummies) command.root
            command.declaration.conclusion (SharedService.tables spaces logical.theory command.declaration input.ready)
            command.saved) ∧
      (result = none ↔ ¬ SharedService.Accepted spaces logical command input.ready)
  obtain ⟨rows, allocated, shaped⟩ := live.cacheRows
  obtain ⟨checking, checked, answer, returned, observed, empty, others, cells⟩ :=
    DeclarationScope.submit_returns_with_result bindings before spaces.cache rows
      (stateValue spaces (pendingValue logical.pending)) (SharedService.commandValue command) name captured
      (by simpa [SpecificationStep.resultValue, optionValue] using live.sessionCell)
      live.cacheCell allocated shaped retained (by
        intro checking empty others cells
        let input := input_after_reset live empty others cells
        obtain ⟨checked, result, called, frame, successful, refused⟩ :=
          SharedService.captured_returns spaces logical command checking input
        refine ⟨checked, result.map (fun next => stateValue spaces (pendingValue next.pending)),
          ?_, result, input, rfl, called, frame, successful, refused⟩
        exact called (DeclarationScope.declarationEnvironment spaces.cache
          (stateValue spaces (pendingValue logical.pending)) (SharedService.commandValue command))
          "state" "command" rfl rfl)
  obtain ⟨result, input, sameAnswer, called, frame, successful, refused⟩ := observed
  subst answer
  let receipt : Receipt spaces logical command before checking checked result :=
    ⟨input, empty, others, cells, called, frame, successful, refused⟩
  exact ⟨checking, checked, result, by simpa [SpecificationStep.resultValue] using returned,
    receipt, receipt.stored⟩

def requestConfiguration (before : State) (command : SharedService.Command) : Configuration :=
  { state := before, control := .evaluate [("command", SharedService.commandValue command)]
      (.expression [.symbol "mm0:submit", .var "command"]) }

/-- Fuel extension preserves the exact response, logical result, reset scope
and private-store invariants of this fixed submitted command. -/
theorem sufficient_fuel (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before : State) (live : Live spaces logical before) :
    ∃ checking checked result fuel,
      (∀ extra, run program (fuel + extra) (requestConfiguration before command) =
        .complete (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result))
          [boolean result.isSome] [] []) ∧
      Receipt spaces logical command before checking checked result ∧
      Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) := by
  obtain ⟨checking, checked, result, returned, receipt, stored⟩ :=
    captured_returns spaces logical command [("command", SharedService.commandValue command)] "command" before live rfl
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program
    [("command", SharedService.commandValue command)] before
    (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) _ _ returned
  exact ⟨checking, checked, result, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ _ _ [] [] completed, receipt, stored⟩

theorem judgment (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before : State) (live : Live spaces logical before) :
    ∃ checking checked result,
      DeclarativeSpec.Runs program (requestConfiguration before command)
        (.complete (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result))
          [boolean result.isSome] [] []) ∧
      Receipt spaces logical command before checking checked result ∧
      Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) := by
  obtain ⟨checking, checked, result, fuel, completed, receipt, stored⟩ :=
    sufficient_fuel spaces logical command before live
  refine ⟨checking, checked, result, ?_, receipt, stored⟩
  apply (completed_run_iff_derivation program _ _ _ [] []).mp
  exact ⟨fuel, by simpa only [Nat.add_zero] using completed 0⟩

theorem gslt_path (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before : State) (live : Live spaces logical before) :
    ∃ checking checked result,
      (theory program).MultiStep (requestConfiguration before command)
        (finished (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result))
          [boolean result.isSome] [] []) ∧
      Receipt spaces logical command before checking checked result ∧
      Stored spaces result (checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)) := by
  obtain ⟨checking, checked, result, fuel, completed, receipt, stored⟩ :=
    sufficient_fuel spaces logical command before live
  refine ⟨checking, checked, result, ?_, receipt, stored⟩
  apply (completed_run_iff_path program _ _ _ [] []).mp
  exact ⟨fuel, by simpa only [Nat.add_zero] using completed 0⟩

/-- Every complete observed submit has the same earned receipt and stored
result, including completed refusal. No initial cache coherence is assumed. -/
theorem completed_frame (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (answers unread printed : List Atom)
    (completed : run program fuel (requestConfiguration before command) = .complete after answers unread printed) :
    ∃ checking checked result,
      after = checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result) ∧
      Receipt spaces logical command before checking checked result ∧
      answers = [boolean result.isSome] ∧ unread = [] ∧ printed = [] ∧ Stored spaces result after := by
  obtain ⟨checking, checked, result, referenceFuel, returned, receipt, stored⟩ :=
    sufficient_fuel spaces logical command before live
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    _ after _ [] [] answers unread printed referenceCompleted completed
  exact ⟨checking, checked, result, sameState.symm, receipt, sameAnswers.symm,
    sameUnread.symm, samePrinted.symm, sameState ▸ stored⟩

/-- A complete True response advances the same represented source session. -/
theorem source_acceptance_receipt (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (accepted : run program fuel (requestConfiguration before command) =
      .complete after [boolean true] [] []) :
    ∃ checking checked next,
      after = checked.putCell "mm0-session" (SpecificationStep.resultValue spaces (some next)) ∧
      Receipt spaces logical command before checking checked (some next) ∧ Live spaces next after := by
  obtain ⟨checking, checked, result, same, receipt, answers, _, _, stored⟩ :=
    completed_frame spaces logical command before after live fuel _ _ _ accepted
  cases result with
  | none => simp [boolean] at answers
  | some next =>
      cases stored with
      | active nextLive => exact ⟨checking, checked, next, same, receipt, nextLive⟩

/-- Complete False stores failure even if the claim has some other valid
logical proof. Its submitted sharing gates remain those in the receipt. -/
theorem source_refusal_receipt (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (refused : run program fuel (requestConfiguration before command) =
      .complete after [boolean false] [] []) :
    ∃ checking checked,
      after = checked.putCell "mm0-session" (SpecificationStep.resultValue spaces none) ∧
      Receipt spaces logical command before checking checked none ∧ Stored spaces none after := by
  obtain ⟨checking, checked, result, same, receipt, answers, _, _, stored⟩ :=
    completed_frame spaces logical command before after live fuel _ _ _ refused
  cases result with
  | none => exact ⟨checking, checked, same, receipt, stored⟩
  | some next => simp [boolean] at answers

/-- Advancing receipts retain the initializer witnesses, optional expectations
and original root in the existing kernel sharing judgment. -/
theorem Receipt.retains_shared {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    {next : Kernel.SpecificationAdmission.State} (advanced : result = some next) :
    Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      ∃ saved,
        Kernel.SharedProof.Checks logical.theory command.declaration command.dummies ⟨saved, command.root⟩ ∧
        List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
          (entry.expected = none ∨ entry.expected = some pair.1)) command.saved saved := by
  obtain ⟨_, _, _, formed, sharing⟩ := (receipt.successful next).mp advanced
  exact ⟨formed, SharedService.checked_retains_shared receipt.input.ready sharing⟩

/-- Cut discharges the checked saved prefix in the original hypothesis scope.
This logical result is not used to accept the supplied source command. -/
theorem Receipt.preceding_derives {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    {next : Kernel.SpecificationAdmission.State} (advanced : result = some next) :
    Kernel.Derives logical.theory.termSignature logical.theory.definitionSignature logical.theory.theoremSignature
      (Admission.proofContext command.declaration command.dummies) command.declaration.hypotheses
      command.declaration.conclusion := by
  obtain ⟨_, saved, sharing, _⟩ := receipt.retains_shared advanced
  exact sharing.derives

theorem Receipt.specification_step {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    {next : Kernel.SpecificationAdmission.State} (advanced : result = some next) :
    ∃ ordinary, Kernel.SpecificationAdmission.Step logical
      ⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩ next := by
  obtain ⟨remaining, nextSame, pending, formed, sharing⟩ := (receipt.successful next).mp advanced
  obtain ⟨ordinary, actual, actualPending, step⟩ := SharedService.Accepted.specification_step receipt.input.ready
    ⟨⟨remaining, pending⟩, formed, sharing⟩
  have same : actual = remaining := Option.some.inj (actualPending.symm.trans pending)
  subst actual
  exact ⟨ordinary, nextSame.symm ▸ step⟩

private theorem history_snoc {before middle after : Kernel.SpecificationAdmission.State}
    {history : List ProofDeclaration} {declaration : ProofDeclaration}
    (checked : Kernel.SpecificationAdmission.Runs before history middle)
    (step : Kernel.SpecificationAdmission.Step middle declaration after) :
    Kernel.SpecificationAdmission.Runs before (history ++ [declaration]) after := by
  induction checked with
  | nil state => exact .cons step (.nil _)
  | cons first rest ih => exact .cons first (ih step)

/-- Only accepted fixed sharing extends the independently checked history.
The ordinary witness here is cut evidence for that logical history. -/
theorem Receipt.extends_history {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    {next : Kernel.SpecificationAdmission.State} (advanced : result = some next)
    (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical) :
    ∃ ordinary, Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩
      (history ++ [⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩]) next := by
  obtain ⟨ordinary, step⟩ := receipt.specification_step advanced
  exact ⟨ordinary, history_snoc preceding step⟩

theorem Receipt.preceding_specified_proof {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result)
    {next : Kernel.SpecificationAdmission.State} (advanced : result = some next)
    (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (history.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext (Admission.proofContext command.declaration command.dummies))
      (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  have admitted : Kernel.Theory.run? {} (history.map Kernel.ProofDeclaration.admission) = some logical.theory :=
    (Kernel.Theory.run_eq_some_iff _ _ _).mpr preceding.theory_run
  exact (Upstream.Lean3ProofAdmission.checked_run_proof_iff admitted
    (Admission.proofContext command.declaration command.dummies) command.declaration.hypotheses
    command.declaration.conclusion).mpr (receipt.preceding_derives advanced)

theorem source_acceptance_retains_shared (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (accepted : run program fuel (requestConfiguration before command) =
      .complete after [boolean true] [] []) :
    Kernel.SharedProof.Formation logical.theory command.index command.declaration command.dummies ∧
      ∃ saved,
        Kernel.SharedProof.Checks logical.theory command.declaration command.dummies ⟨saved, command.root⟩ ∧
        List.Forall₂ (fun entry pair => entry.witness = pair.2 ∧
          (entry.expected = none ∨ entry.expected = some pair.1)) command.saved saved := by
  obtain ⟨_, _, next, _, receipt, _⟩ := source_acceptance_receipt spaces logical command before after live fuel accepted
  exact receipt.retains_shared (next := next) rfl

/-- The independent specification prefix is a separate history premise. The
submitted source proof is checked before its cut evidence extends that history. -/
theorem source_acceptance_extends_history (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (accepted : run program fuel (requestConfiguration before command) =
      .complete after [boolean true] [] []) (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical) :
    ∃ next ordinary, Live spaces next after ∧ Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩
      (history ++ [⟨.theoremDecl command.index command.declaration command.dummies ordinary, command.isLocal⟩]) next := by
  obtain ⟨_, _, next, _, receipt, nextLive⟩ := source_acceptance_receipt spaces logical command before after live fuel accepted
  obtain ⟨ordinary, extended⟩ := receipt.extends_history (next := next) rfl specification history preceding
  exact ⟨next, ordinary, nextLive, extended⟩

theorem source_acceptance_has_specified_preceding_proof (spaces : Spaces) (logical : Kernel.SpecificationAdmission.State)
    (command : SharedService.Command) (before after : State) (live : Live spaces logical before)
    (fuel : Nat) (accepted : run program fuel (requestConfiguration before command) =
      .complete after [boolean true] [] []) (specification : List SpecificationEntry) (history : List ProofDeclaration)
    (preceding : Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ history logical) :
    Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
      (Upstream.Lean3Typing.projectRun (history.map Kernel.ProofDeclaration.admission))
      (Upstream.Lean3Typing.Reference.ofContext (Admission.proofContext command.declaration command.dummies))
      (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
      (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨_, _, next, _, receipt, _⟩ := source_acceptance_receipt spaces logical command before after live fuel accepted
  exact receipt.preceding_specified_proof (next := next) rfl specification history preceding

/-- The stopped result from this observed submit cannot be reopened by a
later submission or finish. Both later operations preserve its exact store. -/
theorem Receipt.refusal_is_sticky {spaces : Spaces} {logical : Kernel.SpecificationAdmission.State}
    {command : SharedService.Command} {before checking checked : State}
    {result : Option Kernel.SpecificationAdmission.State}
    (receipt : Receipt spaces logical command before checking checked result) (refused : result = none)
    (bindings : Subst) (laterCommand : Atom) (name : String)
    (captured : applySubst bindings (.var name) = laterCommand) :
    let after := checked.putCell "mm0-session" (SpecificationStep.resultValue spaces result)
    PureReturns program bindings after (.expression [.symbol "mm0:submit", .var name]) after (boolean false) ∧
      PureReturns program bindings after (.expression [.symbol "mm0:finish"]) after (boolean false) := by
  have represented := receipt.stored
  rw [refused] at represented ⊢
  cases represented with
  | stopped failed =>
      exact ⟨DeclarationScope.refused_submit_returns bindings _ laterCommand name captured failed,
        DeclarationScope.refused_finish_returns bindings _ failed⟩

namespace Controls

open Kernel

private def spaces : Spaces :=
  ⟨.privateSpace 0, .privateSpace 1, .privateSpace 2, .privateSpace 3, .privateSpace 4, .privateSpace 5⟩
private def info : SortInfo := { provable := true }
private def primitive : TermDecl := ⟨[], 0, ∅⟩
private def statement : TheoremDecl := ⟨[], [], .term 1⟩
private def declarations : Theory :=
  { sorts := [(0, info)], terms := [(2, primitive), (1, primitive)], theorems := [(10, statement)] }
private def logical : Kernel.SpecificationAdmission.State := ⟨declarations, [.theoremDecl 12 statement]⟩
private def staleRows : List Atom :=
  [InferenceCache.row (TableAccess.tableValue spaces.terms) (Data.context [])
    (Data.preterm (.term 1)) (Data.inferred none)]
private def obsoleteProofRows : List Atom := Store.rows [(0, Data.preterm (.term 2))]
private def initial : State :=
  { core := [], next := 6
    spaces := fun index =>
      if index = 0 then staleRows
      else if index = 1 then obsoleteProofRows
      else if index = 2 then SortFormation.rows declarations.sorts.reverse
      else if index = 3 then TableAccess.declarationRows declarations.terms.reverse
      else if index = 5 then Proof.theoremRows declarations.theorems.reverse
      else []
    cells := fun name =>
      if name = InferenceCache.cell then some (handleValue spaces.cache)
      else if name = "mm0-proof-store" then some (handleValue spaces.proofs)
      else if name = "mm0-session" then some (SpecificationStep.resultValue spaces (some logical))
      else none }

private theorem live : Live spaces logical initial := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by decide +kernel⟩, rfl, rfl, rfl,
    ⟨staleRows, rfl, ?_⟩, ⟨obsoleteProofRows, rfl, Store.rows_have_arity _⟩⟩
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
  · intro row member
    have same : row = InferenceCache.row (TableAccess.tableValue spaces.terms) (Data.context [])
        (Data.preterm (.term 1)) (Data.inferred none) := by simpa [staleRows] using member
    subst row
    exact ⟨_, rfl, rfl⟩

private def submitted : SharedService.Command :=
  ⟨false, 12, statement, [], [⟨none, .theoremApp 10 [] []⟩], .hyp 0⟩

private theorem formed : SharedProof.Formation logical.theory submitted.index submitted.declaration submitted.dummies := by
  refine ⟨by decide +kernel, (TheoremDecl.check_iff _ _ _).mp (by decide +kernel), ?_⟩
  intro sort absent
  cases absent

private theorem checked {checking : State} (input : SharedService.Input spaces logical checking) :
    Sharing.Checked (Admission.proofContext submitted.declaration submitted.dummies) submitted.root
      submitted.declaration.conclusion (SharedService.tables spaces logical.theory submitted.declaration input.ready)
      submitted.saved := by
  apply Sharing.Checked.save (actual := .term 1)
  · apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
    change ProofWitness.proof? (Presentation.ComputationalTyping.signatureOf declarations.terms.reverse)
      (Unfolding.definitionSignature declarations.definitions.reverse) (Proof.theoremSignature declarations.theorems.reverse)
      [] [] (.theoremApp 10 [] []) = some (.term 1)
    decide +kernel
  · exact Or.inl rfl
  · apply Sharing.Checked.root
    apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
    change ProofWitness.proof? (Presentation.ComputationalTyping.signatureOf declarations.terms.reverse)
      (Unfolding.definitionSignature declarations.definitions.reverse) (Proof.theoremSignature declarations.theorems.reverse)
      [] [.term 1] (.hyp 0) = some (.term 1)
    decide +kernel

/-- The inherited row records refusal for a term that the current signature
types successfully. Driver input deliberately asserts only its physical shape. -/
theorem stale_cache_answer_is_wrong :
    InferenceCache.keyQuery staleRows (TableAccess.tableValue spaces.terms) ([], .term 1) = [Data.inferred none] ∧
      Data.inferred (Preterm.infer declarations.termSignature [] (.term 1)) ≠ Data.inferred none := by
  constructor <;> decide +kernel

/-- The real submit clears that wrong cache, rebuilds the old vector, checks
the same saved initializer and root, then publishes and stores the next state. -/
theorem nonempty_saved_submit_accepts :
    ∃ after fuel, run program fuel (requestConfiguration initial submitted) =
      .complete after [boolean true] [] [] ∧ Live spaces (SharedService.admittedState logical submitted []) after := by
  obtain ⟨checking, checkedState, result, fuel, completed, receipt, represented⟩ :=
    sufficient_fuel spaces logical submitted initial live
  have advanced : result = some (SharedService.admittedState logical submitted []) :=
    (receipt.successful _).mpr ⟨[], rfl, rfl, formed, checked receipt.input⟩
  refine ⟨checkedState.putCell "mm0-session"
    (SpecificationStep.resultValue spaces (some (SharedService.admittedState logical submitted []))), fuel, ?_, ?_⟩
  · simpa [advanced] using completed 0
  · rw [advanced] at represented
    cases represented with
    | active nextLive => exact nextLive

/-- The frontend's empty sharing form checks the unchanged ordinary root
through the same reset, vector initialization and session-cell update. -/
theorem empty_saved_submit_accepts :
    let ordinary : SharedService.Command := { submitted with saved := [], root := .theoremApp 10 [] [] }
    ∃ after fuel, run program fuel (requestConfiguration initial ordinary) =
      .complete after [boolean true] [] [] ∧ Live spaces (SharedService.admittedState logical ordinary []) after := by
  dsimp only
  let ordinary : SharedService.Command := { submitted with saved := [], root := .theoremApp 10 [] [] }
  obtain ⟨checking, checkedState, result, fuel, completed, receipt, represented⟩ :=
    sufficient_fuel spaces logical ordinary initial live
  have shared : Sharing.Checked (Admission.proofContext ordinary.declaration ordinary.dummies)
      ordinary.root ordinary.declaration.conclusion
      (SharedService.tables spaces logical.theory ordinary.declaration receipt.input.ready) ordinary.saved := by
    apply Sharing.Checked.root
    apply (ProofWitness.proof_eq_some_iff _ _ _ _ _ _ _).mp
    change ProofWitness.proof? (Presentation.ComputationalTyping.signatureOf declarations.terms.reverse)
      (Unfolding.definitionSignature declarations.definitions.reverse) (Proof.theoremSignature declarations.theorems.reverse)
      [] [] (.theoremApp 10 [] []) = some (.term 1)
    decide +kernel
  have advanced : result = some (SharedService.admittedState logical ordinary []) :=
    (receipt.successful _).mpr ⟨[], rfl, rfl, formed, shared⟩
  refine ⟨checkedState.putCell "mm0-session"
    (SpecificationStep.resultValue spaces (some (SharedService.admittedState logical ordinary []))), fuel, ?_, ?_⟩
  · simpa [advanced] using completed 0
  · rw [advanced] at represented
    cases represented with
    | active nextLive => exact nextLive

theorem refused_initializer_has_valid_ordinary_root :
    ProofWitness.proof? declarations.termSignature declarations.definitionSignature declarations.theoremSignature
      [] [] (.theoremApp 10 [] []) = some statement.conclusion := by decide +kernel

/-- An absent expectation still refuses an initializer that refers to its own
future slot, despite an available valid ordinary root and old vector contents. -/
theorem invalid_initializer_submit_refuses :
    let invalid : SharedService.Command := { submitted with saved := [⟨none, .hyp 0⟩], root := .theoremApp 10 [] [] }
    ∃ after fuel, run program fuel (requestConfiguration initial invalid) =
      .complete after [boolean false] [] [] ∧ Stored spaces none after := by
  dsimp only
  let invalid : SharedService.Command := { submitted with saved := [⟨none, .hyp 0⟩], root := .theoremApp 10 [] [] }
  obtain ⟨checking, checkedState, result, fuel, completed, receipt, represented⟩ :=
    sufficient_fuel spaces logical invalid initial live
  have rejected : ¬ SharedService.Accepted spaces logical invalid receipt.input.ready := by
    rintro ⟨_, _, shared⟩
    apply Sharing.checked_cons_refused _ _ _ _ ⟨none, .hyp 0⟩ [] _ shared
    change ProofWitness.proof? (Presentation.ComputationalTyping.signatureOf declarations.terms.reverse)
      (Unfolding.definitionSignature declarations.definitions.reverse) (Proof.theoremSignature declarations.theorems.reverse)
      [] [] (.hyp 0) = none
    decide +kernel
  have refused : result = none := receipt.refused.mpr rejected
  refine ⟨checkedState.putCell "mm0-session" (SpecificationStep.resultValue spaces none), fuel, ?_, ?_⟩
  · simpa [refused] using completed 0
  · simpa only [refused] using represented

end Controls

end Mettapedia.Languages.MM0.MeTTa.SharedSessionDriver
