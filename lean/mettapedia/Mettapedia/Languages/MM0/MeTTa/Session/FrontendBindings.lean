import Mettapedia.Languages.MM0.MeTTa.Session.SessionProtocol
import Std.Data.String.ToNat

/-!
# Finite frontend input bindings

The frontend emits fresh `mm0InputN` bindings in child-before-parent order.
The data here records those actual constructor calls. Its evidence checks
references against their preceding prefix and relates request templates to the
existing MM0 data codec. It does not implement the Python term-pool algorithm.

Materialization uses the retained make-var, make-term and make-app source
equations and the existing PeTTa sequential-binding judgment. Constructor
binding preserves the whole native state; declaration checking remains in the
existing drivers.
-/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Mettapedia.Languages.MM0.MeTTa.FrontendBindings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Kernel (Preterm)

def inputName (index : Nat) : String := "mm0Input" ++ Nat.repr index

theorem input_name_injective : Function.Injective inputName := by
  intro first second same
  apply Nat.repr_injective
  exact (String.append_right_inj "mm0Input").mp same

/-- The three source calls used by a finite frontend binding plan. -/
inductive Constructor where
  | variable (index : Nat)
  | term (index : Nat)
  | application (function argument : Nat)

def Constructor.expression : Constructor → Atom
  | .variable index => .expression [.symbol "mm0:make-var", Store.natural index]
  | .term index => .expression [.symbol "mm0:make-term", Store.natural index]
  | .application function argument =>
      .expression [.symbol "mm0:make-app", .var (inputName function), .var (inputName argument)]

/-- Application references must be in the already materialized prefix. -/
inductive Constructs (preceding : List Preterm) : Constructor → Preterm → Prop where
  | variable (index : Nat) : Constructs preceding (.variable index) (.var index)
  | term (index : Nat) : Constructs preceding (.term index) (.term index)
  | application {function argument : Nat} {left right : Preterm}
      (functionFound : preceding[function]? = some left)
      (argumentFound : preceding[argument]? = some right) :
      Constructs preceding (.application function argument) (.app left right)

/-- Evidence about the supplied finite plan, without a binding-plan evaluator. -/
inductive Materializes : List Preterm → List Constructor → List Preterm → Prop where
  | nil (preceding : List Preterm) : Materializes preceding [] preceding
  | cons {preceding final : List Preterm} {constructor : Constructor}
      {remaining : List Constructor} {value : Preterm} :
      Constructs preceding constructor value →
      Materializes (preceding ++ [value]) remaining final →
      Materializes preceding (constructor :: remaining) final

theorem Constructs.application_bounds {preceding : List Preterm} {function argument : Nat}
    {value : Preterm} (constructed : Constructs preceding (.application function argument) value) :
    function < preceding.length ∧ argument < preceding.length := by
  cases constructed with
  | application first second =>
      exact ⟨(List.getElem?_eq_some_iff.mp first).1, (List.getElem?_eq_some_iff.mp second).1⟩

theorem Materializes.length {preceding final : List Preterm} {constructors : List Constructor}
    (materialized : Materializes preceding constructors final) :
    final.length = preceding.length + constructors.length := by
  induction materialized with
  | nil => simp
  | cons _ _ ih => simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

/-- Captures of prior values and freshness of all later input names. -/
structure Environment (values : List Preterm) (bindings : Subst) : Prop where
  captured : ∀ (index : Nat) (value : Preterm), values[index]? = some value →
    Subst.lookup bindings (inputName index) = some (Data.preterm value)
  fresh : ∀ (index : Nat), values.length ≤ index → Subst.lookup bindings (inputName index) = none

theorem Environment.empty : Environment [] [] := by
  refine ⟨?_, ?_⟩
  · intro index value impossible; simp at impossible
  · intro index _; rfl

private theorem lookup_cons_ne (bindings : Subst) (name other : String) (value : Atom)
    (different : name ≠ other) :
    Subst.lookup ((name, value) :: bindings) other = Subst.lookup bindings other := by
  simp [Subst.lookup, different]

theorem Environment.extend {values : List Preterm} {bindings : Subst}
    (captured : Environment values bindings) (value : Preterm) :
    Environment (values ++ [value]) ((inputName values.length, Data.preterm value) :: bindings) := by
  refine ⟨?_, ?_⟩
  · intro index result found
    by_cases old : index < values.length
    · have names : inputName values.length ≠ inputName index :=
        fun same => (Nat.ne_of_gt old) (input_name_injective same)
      rw [lookup_cons_ne bindings _ _ _ names]
      exact captured.captured index result (by simpa only [List.getElem?_append_left old] using found)
    · rw [List.getElem?_append_right (by omega)] at found
      cases distance : index - values.length with
      | zero =>
          have sameIndex : index = values.length := by omega
          subst index
          have sameValue : result = value := by simpa using found.symm
          subst result
          simp [Subst.lookup]
      | succ distance => simp [distance] at found
  · intro index future
    have later : values.length < index := by
      simp only [List.length_append, List.length_singleton] at future
      omega
    have names : inputName values.length ≠ inputName index :=
      fun same => (Nat.ne_of_lt later) (input_name_injective same)
    rw [lookup_cons_ne bindings _ _ _ names]
    exact captured.fresh index (by omega)

theorem Environment.variable {values : List Preterm} {bindings : Subst}
    (captured : Environment values bindings) (index : Nat) (value : Preterm)
    (found : values[index]? = some value) :
    applySubst bindings (.var (inputName index)) = Data.preterm value := by
  simp only [applySubst, captured.captured index value found, Option.getD_some]

theorem Constructs.returns {values : List Preterm} {bindings : Subst}
    {constructor : Constructor} {value : Preterm}
    (constructed : Constructs values constructor value) (captured : Environment values bindings)
    (before : State) :
    PureReturns program bindings before constructor.expression before (Data.preterm value) := by
  cases constructed with
  | «variable» index => exact Data.make_var_returns bindings before index
  | term index => exact Data.make_term_returns bindings before index
  | application first second =>
      exact Data.make_app_captured_returns bindings before _ _ _ _
        (captured.variable _ _ first) (captured.variable _ _ second)

def pairs : Nat → List Constructor → List Atom
  | _, [] => []
  | index, constructor :: remaining =>
      .expression [.var (inputName index), constructor.expression] :: pairs (index + 1) remaining

/-- The frontend omits let* for an empty pool. -/
def wrap (constructors : List Constructor) (body : Atom) : Atom :=
  match constructors with
  | [] => body
  | _ :: _ => .expression [.symbol "let*", .expression (pairs 0 constructors), body]

/-- Actual nested binding materializes all values without changing the state.
The continuation is evaluated in the earned final capture environment. -/
theorem Materializes.nested_returns {values final : List Preterm} {constructors : List Constructor}
    (materialized : Materializes values constructors final) (bindings : Subst)
    (captured : Environment values bindings) (before : State) :
    ∃ bound, Environment final bound ∧
      ∀ (body : Atom) (after : State) (answer : Atom),
        PureReturns program bound before body after answer →
        ∃ nested, nestedLets (pairs values.length constructors) body = some nested ∧
          PureReturns program bindings before nested after answer := by
  induction materialized generalizing bindings with
  | nil => exact ⟨bindings, captured, fun body after answer returned => ⟨body, rfl, returned⟩⟩
  | @cons values final constructor remaining value constructed rest ih =>
      let next := (inputName values.length, Data.preterm value) :: bindings
      obtain ⟨bound, finalCaptured, continuation⟩ := ih next (captured.extend value)
      refine ⟨bound, finalCaptured, ?_⟩
      intro body after answer returned
      obtain ⟨nested, expanded, computed⟩ := continuation body after answer returned
      simp only [List.length_append, List.length_singleton] at expanded
      refine ⟨.expression [.symbol "let", .var (inputName values.length), constructor.expression, nested], ?_, ?_⟩
      · simp only [pairs, nestedLets, expanded]
        rfl
      · apply let_returns program bindings next before before after (.var (inputName values.length))
          constructor.expression nested (Data.preterm value) answer (constructed.returns captured before) _ computed
        simp [SpaceSemantics.matchValue, matchAtom, captured.fresh values.length (by omega), next]

theorem Materializes.wrapper_returns {final : List Preterm} {constructors : List Constructor}
    (materialized : Materializes [] constructors final) (before : State) :
    ∃ bound, Environment final bound ∧
      ∀ (body : Atom) (after : State) (answer : Atom),
        PureReturns program bound before body after answer →
        PureReturns program [] before (wrap constructors body) after answer := by
  obtain ⟨bound, captured, nestedReturned⟩ := materialized.nested_returns [] Environment.empty before
  refine ⟨bound, captured, ?_⟩
  intro body after answer returned
  obtain ⟨nested, expanded, computed⟩ := nestedReturned body after answer returned
  cases constructors with
  | nil =>
      have same : nested = body := Option.some.inj expanded.symm
      simpa only [same, wrap] using computed
  | cons first remaining =>
      exact let_star_returns program [] before after _ body nested answer expanded computed

/-- Request syntax with preterm references into a materialized input pool.
The targets are the existing constructor atoms, not a second term carrier. -/
inductive Template (values : List Preterm) : Atom → Atom → Prop where
  | symbol (name : String) : Template values (.symbol name) (.symbol name)
  | grounded (value : GroundedValue) : Template values (.grounded value) (.grounded value)
  | reference {index : Nat} {value : Preterm} (found : values[index]? = some value) :
      Template values (.var (inputName index)) (Data.preterm value)
  | expression {sources targets : List Atom}
      (items : List.Forall₂ (Template values) sources targets) :
      Template values (.expression sources) (.expression targets)

mutual

theorem Template.substitutes {values : List Preterm} {bindings : Subst} {source target : Atom}
    (image : Template values source target) (captured : Environment values bindings) :
    applySubst bindings source = target := by
  cases image with
  | symbol => rfl
  | grounded => rfl
  | reference found => exact captured.variable _ _ found
  | expression items =>
      exact congrArg Atom.expression (template_list_substitutes items captured)
termination_by sizeOf source

private theorem template_list_substitutes {values : List Preterm} {bindings : Subst}
    {sources targets : List Atom} (images : List.Forall₂ (Template values) sources targets)
    (captured : Environment values bindings) :
    applySubst.applySubstList bindings sources = targets := by
  cases images with
  | nil => rfl
  | cons image rest =>
      exact congrArg₂ List.cons (image.substitutes captured) (template_list_substitutes rest captured)
termination_by sizeOf sources

end

private theorem template_self {values : List Preterm} {items : List Atom}
    (members : ∀ item ∈ items, Template values item item) :
    List.Forall₂ (Template values) items items := by
  induction items with
  | nil => exact .nil
  | cons item remaining ih =>
      exact .cons (members item (by simp)) (ih (fun next found => members next (by simp [found])))

/-- Closed literal constructor data needs no pool binding. -/
theorem Template.literal (values : List Preterm) {value : Atom} (literal : SpaceSemantics.Literal value) :
    Template values value value := by
  induction literal with
  | symbol name => exact .symbol name
  | grounded value => exact .grounded value
  | expression items _ _ ih => exact .expression (template_self ih)

theorem Template.list_value {values : List Preterm} {sources targets : List Atom}
    (items : List.Forall₂ (Template values) sources targets) :
    Template values (ListAccess.listValue sources) (ListAccess.listValue targets) :=
  .expression (.cons (.symbol "MM0:L") (.cons (.expression items) .nil))

theorem Template.empty_not_variable {source target : Atom} (image : Template [] source target) (name : String) :
    source ≠ .var name := by
  cases image with
  | symbol => simp
  | grounded => simp
  | reference found => simp at found
  | expression => simp

structure Request where
  constructors : List Constructor
  values : List Preterm
  argument : Atom

def Request.Encodes (request : Request) (target : Atom) : Prop :=
  Materializes [] request.constructors request.values ∧ Template request.values request.argument target

def Request.body (request : Request) (head : String) : Atom :=
  wrap request.constructors (.expression [.symbol head, request.argument])

def Request.control (request : Request) (head : String) : Control :=
  .evaluate [] (request.body head)

/-- Binding constructs the exact raw argument before the retained callee
runs. The whole final state and answer are those of the original callee. -/
theorem Request.returns (request : Request) (value : Atom) (encoded : request.Encodes value)
    (before after : State) (head : String) (first : Subst) (one answer : Atom)
    (dispatch : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = true)
    (raw : argumentIsRaw program head 0 = true)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote"])
    (capturedOne : applySubst first one = value)
    (returned : PureReturns program first before (.expression [.symbol head, one]) after answer) :
    PureReturns program [] before (request.body head) after answer := by
  obtain ⟨bound, captured, wrapped⟩ := encoded.1.wrapper_returns before
  apply wrapped _ after answer
  exact raw_unary_capture_returns program first bound before after head one request.argument answer
    dispatch raw ordinary (capturedOne.trans (encoded.2.substitutes captured).symm) returned

theorem Request.start_returns (request : Request) (specification : List Kernel.SpecificationEntry)
    (encoded : request.Encodes (SpecificationMatching.pendingValue specification)) (before : State) :
    PureReturns program [] before (request.body "mm0:start")
      (SessionInitialization.startState before (SpecificationMatching.pendingValue specification)) (boolean true) := by
  exact request.returns _ encoded before _ "mm0:start"
    [("spec", SpecificationMatching.pendingValue specification)] (.var "spec") (boolean true)
    (by decide) (by decide) (by decide) rfl
    (SessionInitialization.returns _ before _ "spec" rfl)

/-- A fixed canonical submission receipt survives the actual input wrapper.
Neither its command nor its submitted sharing evidence is replaced. -/
theorem Request.submit_receipt_returns (request : Request) {spaces : SessionInitialization.Spaces}
    {logical result : Option Kernel.SpecificationAdmission.State} {command : SessionProtocol.Command}
    {before after : State}
    (encoded : request.Encodes (SessionProtocol.commandValue command))
    (receipt : SessionProtocol.Receipt spaces logical command before after result) :
    PureReturns program [] before (request.body "mm0:submit") after (boolean result.isSome) := by
  exact request.returns _ encoded before after "mm0:submit"
    [("command", SessionProtocol.commandValue command)] (.var "command") (boolean result.isSome)
    (by decide) (by decide) (by decide) rfl receipt.returned

theorem Request.submit_returns (request : Request) (spaces : SessionInitialization.Spaces)
    (logical : Option Kernel.SpecificationAdmission.State) (command : SessionProtocol.Command) (before : State)
    (encoded : request.Encodes (SessionProtocol.commandValue command))
    (represented : SessionDriver.Stored spaces logical before) :
    ∃ after result,
      PureReturns program [] before (request.body "mm0:submit") after (boolean result.isSome) ∧
      SessionProtocol.Receipt spaces logical command before after result := by
  obtain ⟨after, result, receipt⟩ := SessionProtocol.submit_returns spaces logical command before represented
  exact ⟨after, result, request.submit_receipt_returns encoded receipt, receipt⟩

def submissionControls (requests : List Request) : List Control :=
  requests.map (·.control "mm0:submit")

/-- The existing receipt trace lifts to the supplied encoded request list.
Every constructor wrapper preserves the intervening physical states. -/
theorem frontend_finish_path {spaces : SessionInitialization.Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List SessionProtocol.Command} {answers : List Bool}
    (trace : SessionProtocol.Trace spaces logical before commands answers terminal after)
    (requests : List Request)
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests)
    (stored : SessionDriver.Stored spaces terminal after) (collected : List Atom) :
    (theory program).MultiStep
      { state := before, control := .sequence
          (submissionControls requests ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) collected }
      (finished after (collected ++ answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) [] []) := by
  induction trace generalizing requests collected with
  | nil =>
      cases encoded with
      | nil =>
          simpa only [submissionControls, List.map_nil, List.nil_append, List.append_nil] using
            sequence_cons_answers program _ _ _ (.evaluate [] (.expression [.symbol "mm0:finish"])) [] collected
              [boolean (SessionProtocol.finishedStatus _)] (collected ++ [boolean (SessionProtocol.finishedStatus _)])
              (SessionDriver.finish_returns spaces _ _ [] stored) (.step (step_transition rfl) (.refl _))
  | @cons logical next terminal before middle after command commands answers receipt rest ih =>
      cases encoded with
      | @cons _ request _ requests firstEncoded remainingEncoded =>
          have composed := sequence_cons_answers program before middle after (request.control "mm0:submit")
            (submissionControls requests ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) collected
            [boolean next.isSome] _ (request.submit_receipt_returns firstEncoded receipt)
            (ih requests remainingEncoded stored (collected ++ [boolean next.isSome]))
          simpa only [submissionControls, List.map_cons, List.cons_append, List.append_assoc,
            List.singleton_append, List.nil_append] using composed

def protocolControls (start : Request) (requests : List Request) : List Control :=
  start.control "mm0:start" :: submissionControls requests ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]

def protocolConfiguration (before : State) (start : Request) (requests : List Request) : Configuration :=
  { state := before, control := .sequence (protocolControls start requests) [] }

/-- Exact finite frontend wrappers compose with the existing mixed protocol.
All original commands and source receipts are retained in the result. -/
theorem protocol_returns (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : Request) (requests : List Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests) :
    ∃ after answers terminal,
      (theory program).MultiStep (protocolConfiguration before start requests)
        (finished after (boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) [] []) ∧
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      SessionDriver.Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      answers.length = commands.length ∧
      ((boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) =
        List.replicate (commands.length + 2) (boolean true) ↔
          ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, _, trace, stored, length, accepted⟩ :=
    SessionProtocol.protocol_returns before specification commands
  refine ⟨after, answers, terminal, ?_, trace, stored, length, accepted⟩
  have rest := frontend_finish_path trace requests encoded stored [boolean true]
  have composed := sequence_cons_answers program before
    (SessionInitialization.startState before (SpecificationMatching.pendingValue specification)) after
    (start.control "mm0:start")
    (submissionControls requests ++ [.evaluate [] (.expression [.symbol "mm0:finish"])]) [] [boolean true] _
    (start.start_returns specification startEncoded before) rest
  simpa only [protocolConfiguration, protocolControls, List.nil_append, List.singleton_append,
    List.cons_append] using composed

theorem sufficient_fuel (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : Request) (requests : List Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests) :
    ∃ after answers terminal fuel,
      (∀ extra, run program (fuel + extra) (protocolConfiguration before start requests) =
        .complete after (boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) [] []) ∧
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      SessionDriver.Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      answers.length = commands.length ∧
      ((boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) =
        List.replicate (commands.length + 2) (boolean true) ↔
          ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, path, trace, stored, length, accepted⟩ :=
    protocol_returns before specification commands start requests startEncoded encoded
  obtain ⟨fuel, completed⟩ := (completed_run_iff_path program _ after _ [] []).mpr path
  exact ⟨after, answers, terminal, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ after _ [] [] completed,
    trace, stored, length, accepted⟩

/-- Any completed emitted-request sequence retains the original fixed input
trace, exact response occurrences, stored option and finish gate. -/
theorem completed_protocol (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : Request) (requests : List Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests)
    (after : State) (fuel : Nat) (outputs unread printed : List Atom)
    (completed : run program fuel (protocolConfiguration before start requests) = .complete after outputs unread printed) :
    ∃ answers terminal,
      outputs = boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)] ∧
      unread = [] ∧ printed = [] ∧
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      SessionDriver.Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      outputs.length = commands.length + 2 ∧
      (outputs = List.replicate (commands.length + 2) (boolean true) ↔
        ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨reference, answers, terminal, referenceFuel, returned, trace, stored, length, accepted⟩ :=
    sufficient_fuel before specification commands start requests startEncoded encoded
  have referenceCompleted := returned 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameAnswers, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    reference after _ [] [] outputs unread printed referenceCompleted completed
  subst after
  refine ⟨answers, terminal, sameAnswers.symm, sameUnread.symm, samePrinted.symm, trace, stored, ?_, ?_⟩
  · rw [← sameAnswers]; simp [length]
  · rw [← sameAnswers]; exact accepted

/-- Actual frontend wrappers preserve independently checked consumption,
the exact authorized axiom basis and Mario's specified structural extension. -/
theorem accepted_consumes_specification (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : Request) (requests : List Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests)
    (after : State) (fuel : Nat)
    (accepted : run program fuel (protocolConfiguration before start requests) =
      .complete after (List.replicate (commands.length + 2) (boolean true)) [] []) :
    ∃ finalTheory declarations answers,
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
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
        (Upstream.Lean3Typing.projectRun ((commands.map SessionProtocol.inputDeclaration).map Kernel.ProofDeclaration.admission)) := by
  obtain ⟨answers, terminal, _, _, _, trace, stored, _, gate⟩ :=
    completed_protocol before specification commands start requests startEncoded encoded after fuel _ [] [] accepted
  obtain ⟨finalTheory, same⟩ := gate.mp rfl
  obtain ⟨declarations, images, history, verified, axioms, specified⟩ := trace.consumed_specification finalTheory same
  rw [same] at trace stored
  cases stored with
  | active live => exact ⟨finalTheory, declarations, answers, trace, live, images, history, verified, axioms, specified⟩

/-- The root and saved initializers of the original frontend command remain
fixed when its Mario proof is derived in the actual preceding history. -/
theorem accepted_shared_preceding_proof (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : Request) (requests : List Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands requests)
    (after : State) (fuel : Nat)
    (accepted : run program fuel (protocolConfiguration before start requests) =
      .complete after (List.replicate (commands.length + 2) (boolean true)) [] [])
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map Kernel.ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨finalTheory, declarations, answers, trace, _, _, _, _, _, _⟩ :=
    accepted_consumes_specification before specification commands start requests startEncoded encoded after fuel accepted
  exact trace.shared_preceding_proof ⟨{}, specification⟩ ⟨finalTheory, []⟩ rfl rfl specification [] (.nil _) command belongs

/-- An earned input binding is returned inertly, including shared children,
without any mutation or extra answer occurrence. -/
theorem Materializes.pool_value_returns {constructors : List Constructor} {values : List Preterm}
    (materialized : Materializes [] constructors values) (before : State) (index : Nat) (value : Preterm)
    (found : values[index]? = some value) :
    PureReturns program [] before (wrap constructors (.var (inputName index))) before (Data.preterm value) := by
  obtain ⟨bound, captured, wrapped⟩ := materialized.wrapper_returns before
  apply wrapped _ before (Data.preterm value)
  simpa only [captured.variable index value found] using variable_returns program bound before (inputName index)

namespace Controls

private def leaf : Preterm := .term 7
private def repeated : Preterm := .app leaf leaf
private def doubled : Preterm := .app repeated repeated
private def sharedPlan : List Constructor := [.term 7, .application 0 0, .application 1 1]
private def sharedValues : List Preterm := [leaf, repeated, doubled]

private theorem shared_plan_materializes : Materializes [] sharedPlan sharedValues := by
  exact .cons (.term 7)
    (.cons (.application rfl rfl) (.cons (.application rfl rfl) (.nil _)))

/-- Both applications reuse their preceding child twice. The actual let*
wrapper returns the final existing preterm encoding with the whole state fixed. -/
theorem repeated_child_returns (before : State) :
    PureReturns program [] before (wrap sharedPlan (.var (inputName 2))) before (Data.preterm doubled) :=
  shared_plan_materializes.pool_value_returns before 2 doubled rfl

theorem repeated_child_sufficient_fuel (before : State) :
    ∃ fuel, ∀ extra, run program (fuel + extra)
      { state := before, control := .evaluate [] (wrap sharedPlan (.var (inputName 2))) } =
        .complete before [Data.preterm doubled] [] [] := by
  obtain ⟨fuel, completed⟩ := pure_returns_has_sufficient_fuel program [] before before _ _ (repeated_child_returns before)
  exact ⟨fuel, fun extra => completed_run_more_fuel program fuel extra _ before _ [] [] completed⟩

private def startupDeclaration : Kernel.TheoremDecl := ⟨[], [], doubled⟩
private def startupSpecification : List Kernel.SpecificationEntry := [.axiomDecl 10 startupDeclaration]
private def startupRequest : Request :=
  ⟨sharedPlan, sharedValues, ListAccess.listValue [ListAccess.listValue
    [.symbol "MM0:SpecAxiom", Store.natural 10, ListAccess.listValue
      [.symbol "MM0:Theorem", Data.context [], ListAccess.listValue [], .var (inputName 2)]]]⟩

private theorem startup_encoded :
    startupRequest.Encodes (SpecificationMatching.pendingValue startupSpecification) := by
  refine ⟨shared_plan_materializes, ?_⟩
  have declarationImage : Template sharedValues
      (ListAccess.listValue [.symbol "MM0:Theorem", Data.context [], ListAccess.listValue [], .var (inputName 2)])
      (ListAccess.listValue [.symbol "MM0:Theorem", Data.context [], ListAccess.listValue [], Data.preterm doubled]) :=
    .list_value (.cons (.symbol "MM0:Theorem") (.cons (.literal _ (Data.context_literal []))
      (.cons (.list_value .nil) (.cons (.reference rfl) .nil))))
  have entryImage : Template sharedValues
      (ListAccess.listValue [.symbol "MM0:SpecAxiom", Store.natural 10,
        ListAccess.listValue [.symbol "MM0:Theorem", Data.context [], ListAccess.listValue [], .var (inputName 2)]])
      (ListAccess.listValue [.symbol "MM0:SpecAxiom", Store.natural 10,
        ListAccess.listValue [.symbol "MM0:Theorem", Data.context [], ListAccess.listValue [], Data.preterm doubled]]) :=
    .list_value (.cons (.symbol "MM0:SpecAxiom") (.cons (.literal _ (Data.natural_literal 10)) (.cons declarationImage .nil)))
  simpa only [startupRequest, startupSpecification, startupDeclaration, SpecificationMatching.pendingValue,
    SpecificationMatching.entryValue, TheoremInstantiation.declarationValue, ListSubstitution.expressionsValue,
    List.map_cons, List.map_nil] using Template.list_value (.cons entryImage .nil)

/-- The emitted child-before-parent pool is used inside an actual start
request. Startup receives the fully resolved specification and allocates its
ordinary session state; constructor binding adds no separate store effects. -/
theorem repeated_child_start_returns (before : State) :
    PureReturns program [] before (startupRequest.body "mm0:start")
      (SessionInitialization.startState before (SpecificationMatching.pendingValue startupSpecification)) (boolean true) :=
  startupRequest.start_returns startupSpecification startup_encoded before

/-- A forward reference cannot be certified as a materialized input value.
The constructor itself remains a data operation; this is prefix validity. -/
theorem forward_reference_invalid (remaining : List Constructor) (values : List Preterm) :
    ¬ Materializes [] (.application 0 0 :: remaining) values := by
  intro materialized
  cases materialized with
  | cons constructed _ =>
      have impossible := constructed.application_bounds
      simp at impossible

/-- Missing input names do not turn into canonical preterm captures. -/
theorem forward_reference_not_encoded (value : Preterm) :
    ¬ Template [] (.var (inputName 0)) (Data.preterm value) := by
  intro image
  exact image.empty_not_variable (inputName 0) rfl

end Controls


/-! ## Input and output preservation for encoded request syntax -/

private theorem template_symbol_target {values : List Preterm} {source target : Atom}
    (image : Template values source target) (head : String) (symbol : source = .symbol head) :
    target = .symbol head := by
  cases image with
  | symbol => exact symbol
  | grounded => cases symbol
  | reference => cases symbol
  | expression => cases symbol

private def headSafe (excluded : List String) : List Atom → Bool
  | .symbol head :: _ => !InputOutput.blocked excluded head
  | _ => true

private theorem template_head_safe {values : List Preterm} {sources targets : List Atom}
    (images : List.Forall₂ (Template values) sources targets) (excluded : List String)
    (safe : headSafe excluded targets = true) :
    headSafe excluded sources = true := by
  cases images with
  | nil => rfl
  | cons image rest =>
      rename_i source target sources targets
      cases source with
      | symbol head =>
          have same := template_symbol_target image head rfl
          subst target
          exact safe
      | grounded => rfl
      | var => rfl
      | expression => rfl

mutual

theorem Template.code_safe {values : List Preterm} {source target : Atom}
    (image : Template values source target) (excluded : List String)
    (safe : InputOutput.codeSafe excluded target = true) :
    InputOutput.codeSafe excluded source = true := by
  cases image with
  | symbol => exact safe
  | grounded => exact safe
  | reference => simp [InputOutput.codeSafe, SpaceSemantics.patternHeads]
  | expression items =>
      rw [InputOutput.expression_safe] at safe ⊢
      change (headSafe excluded _ && _) = true at safe ⊢
      simp only [Bool.and_eq_true] at safe ⊢
      exact ⟨template_head_safe items excluded safe.1,
        template_list_safe items excluded safe.2⟩
termination_by sizeOf source

private theorem template_list_safe {values : List Preterm} {sources targets : List Atom}
    (images : List.Forall₂ (Template values) sources targets) (excluded : List String)
    (safe : targets.all (InputOutput.codeSafe excluded) = true) :
    sources.all (InputOutput.codeSafe excluded) = true := by
  cases images with
  | nil => rfl
  | cons image rest =>
      simp only [List.all_cons, Bool.and_eq_true] at safe ⊢
      exact ⟨image.code_safe excluded safe.1,
        template_list_safe rest excluded safe.2⟩
termination_by sizeOf sources

end

theorem Constructor.code_safe (constructor : Constructor) :
    InputOutput.codeSafe ["mm0:stream"] constructor.expression = true := by
  cases constructor <;>
    simp [Constructor.expression, InputOutput.codeSafe, SpaceSemantics.patternHeads,
      SpaceSemantics.patternHeads.nested, InputOutput.blocked, ioHead, Store.natural]

theorem pairs_code_safe (index : Nat) (constructors : List Constructor) :
    (pairs index constructors).all (InputOutput.codeSafe ["mm0:stream"]) = true := by
  induction constructors generalizing index with
  | nil => rfl
  | cons constructor remaining ih =>
      simp only [pairs, List.all_cons, Bool.and_eq_true]
      refine ⟨?_, ih (index + 1)⟩
      rw [InputOutput.expression_safe]
      have variableSafe : InputOutput.codeSafe ["mm0:stream"] (.var (inputName index)) = true := by
        simp [InputOutput.codeSafe, SpaceSemantics.patternHeads]
      simp only [List.all_cons, List.all_nil, variableSafe, constructor.code_safe,
        Bool.and_true]

theorem wrap_code_safe (constructors : List Constructor) (body : Atom)
    (safe : InputOutput.codeSafe ["mm0:stream"] body = true) :
    InputOutput.codeSafe ["mm0:stream"] (wrap constructors body) = true := by
  cases constructors with
  | nil => exact safe
  | cons first remaining =>
      have paired := pairs_code_safe 0 (first :: remaining)
      have containerSafe : InputOutput.codeSafe ["mm0:stream"] (.expression (pairs 0 (first :: remaining))) = true := by
        rw [InputOutput.expression_safe]
        change (true && _) = true
        simpa only [Bool.true_and] using paired
      change InputOutput.codeSafe ["mm0:stream"]
        (.expression [.symbol "let*", .expression (pairs 0 (first :: remaining)), body]) = true
      rw [InputOutput.expression_safe]
      have symbolSafe : InputOutput.codeSafe ["mm0:stream"] (.symbol "let*") = true := by
        simp [InputOutput.codeSafe, SpaceSemantics.patternHeads]
      have headSafe : InputOutput.blocked ["mm0:stream"] "let*" = false := by decide
      simp only [List.all_cons, List.all_nil, containerSafe, safe, symbolSafe, headSafe,
        Bool.not_false, Bool.and_true]

theorem Request.body_code_safe (request : Request) (value : Atom) (head : String)
    (encoded : request.Encodes value) (headSafe : InputOutput.blocked ["mm0:stream"] head = false)
    (safe : InputOutput.codeSafe ["mm0:stream"] value = true) :
    InputOutput.codeSafe ["mm0:stream"] (request.body head) = true := by
  apply wrap_code_safe
  have argumentSafe := encoded.2.code_safe ["mm0:stream"] safe
  rw [InputOutput.expression_safe]
  have symbolSafe : InputOutput.codeSafe ["mm0:stream"] (.symbol head) = true := by
    simp [InputOutput.codeSafe, SpaceSemantics.patternHeads]
  simp only [List.all_cons, List.all_nil, headSafe, argumentSafe, symbolSafe,
    Bool.not_false, Bool.and_true]


namespace Controls

/-- A repeated-child binding wrapper introduces no input or output operation. -/
theorem repeated_child_binding_code_safe :
    InputOutput.codeSafe ["mm0:stream"] (wrap sharedPlan (.var (inputName 2))) = true := by
  apply wrap_code_safe
  simp [InputOutput.codeSafe, SpaceSemantics.patternHeads]

/-- Wrapping an output operation never makes it eligible for read-only framing. -/
theorem print_body_not_safe (constructors : List Constructor) :
    InputOutput.codeSafe ["mm0:stream"]
      (wrap constructors (.expression [.symbol "println!", .symbol "answer"])) = false := by
  have printed : InputOutput.codeSafe ["mm0:stream"]
      (.expression [.symbol "println!", .symbol "answer"]) = false := by
    simp [InputOutput.codeSafe, SpaceSemantics.patternHeads, SpaceSemantics.patternHeads.nested,
      InputOutput.blocked, ioHead]
  cases constructors with
  | nil => exact printed
  | cons first remaining =>
      change InputOutput.codeSafe ["mm0:stream"]
        (.expression [.symbol "let*", .expression (pairs 0 (first :: remaining)),
          .expression [.symbol "println!", .symbol "answer"]]) = false
      rw [InputOutput.expression_safe]
      simp only [List.all_cons, List.all_nil, printed, Bool.false_and, Bool.and_false]

end Controls

end Mettapedia.Languages.MM0.MeTTa.FrontendBindings
