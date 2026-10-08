import Mettapedia.Languages.MM0.MeTTa.Session.FrontendBindings
import Mettapedia.Languages.MeTTa.PeTTa.ConfigurationLanguageDef

/-!
# The retained parsed-request stream

The stream reads each request, executes it through the existing PeTTa machine,
and prints its observed answer. Its final returned atom is an EOF observation;
specification acceptance depends on the preceding Boolean response sequence.
Raw line reading and native rendering remain separate interfaces.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000

namespace Mettapedia.Languages.MM0.MeTTa.StreamProtocol

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval Eval.InputOutput
open Effects (State boolean)

private def excluded : List String := ["mm0:stream"]

private theorem checker_closed : Closed program excluded := by
  have inventory : program.equations.all (fun equation =>
      blocked excluded equation.head || codeSafe excluded equation.body) = true := by decide +kernel
  intro equation member allowed
  have included := (List.all_eq_true.mp inventory) equation member
  simpa only [allowed, Bool.false_or] using included

private theorem let_allowed : blocked excluded "let" = false := by decide

private def streamEquation : SpaceSemantics.Equation := streamSource.program.equations[0]'(by decide)
private def streamBody : Atom := streamEquation.body
private def streamRows : List Atom :=
  match streamBody with
  | .expression [_, _, _, .expression [_, _, .expression rows]] => rows
  | _ => []
private def loopBody : Atom :=
  match streamRows with
  | [_, .expression [_, body]] => body
  | _ => .expression []

def call : Atom := .expression [.symbol "mm0:stream"]
def endMarker : Atom := .symbol "MM0:End"

private theorem stream_shape : streamBody =
    .expression [.symbol "let", .var "request", .expression [.symbol "readln!"],
      .expression [.symbol "case", .var "request", .expression streamRows]] := by decide
private theorem loop_shape : loopBody =
    .expression [.symbol "let", .var "answer", .expression [.symbol "eval", .var "call"],
      .expression [.symbol "let", .var "printed", .expression [.symbol "println!", .var "answer"], call]] := by decide
private theorem stream_rows : readCases streamRows =
    some [(.symbol "end_of_file", endMarker), (.var "call", loopBody)] := by decide
private theorem stream_unique :
    program.equations.filter (fun equation => equation.head == "mm0:stream") = [streamEquation] := by decide +kernel
private theorem stream_formals : streamEquation.arguments = [] := by decide +kernel
private theorem stream_clauses : clauses program "mm0:stream" [] = [.evaluate [] streamBody] := by
  rw [clauses_use_only_the_named_equations, stream_unique]
  simp [stream_formals, SpaceSemantics.matchValue, SpaceSemantics.matchValue.matchValues, streamBody]

private theorem stream_call_returns (bindings : Subst) (before after : State)
    (input output remaining printed : List Atom)
    (body : PureReturnsIO program [] before streamBody after endMarker input output remaining printed) :
    PureReturnsIO program bindings before call after endMarker input output remaining printed := by
  apply call_io_returns program bindings before after "mm0:stream" [] endMarker
    input output remaining printed (by decide) (by decide)
  have dispatch : step program
      { state := before, control := .arguments bindings (.function "mm0:stream") [] [] 0, input, output } =
      some { state := before, control := .sequence [.evaluate [] streamBody] [], input, output } := by
    simp [step, ioHead, show StdLib.known "mm0:stream" = false by decide, stream_clauses]
  exact .step (step_transition dispatch)
    (single_sequence_io program before after (.evaluate [] streamBody) [] [endMarker] input output remaining printed body)

private def requestEnvironment (request : Atom) : Subst := [("request", request)]
private def callEnvironment (request : Atom) : Subst := ("call", request) :: requestEnvironment request
private def answerEnvironment (request answer : Atom) : Subst := ("answer", answer) :: callEnvironment request
private def printedEnvironment (request answer : Atom) : Subst :=
  ("printed", boolean true) :: answerEnvironment request answer

private theorem match_fresh (bindings : Subst) (name : String) (value : Atom)
    (fresh : Subst.lookup bindings name = none) :
    SpaceSemantics.matchValue bindings (.var name) value = some ((name, value) :: bindings) := by
  cases value <;> simp [SpaceSemantics.matchValue, Mettapedia.Languages.ProcessCalculi.MORK.matchAtom, fresh]

theorem eof_returns (state : State) (output : List Atom) :
    PureReturnsIO program [] state call state endMarker [] output [] output := by
  apply stream_call_returns
  rw [stream_shape]
  apply let_io_returns program [] (requestEnvironment (.symbol "end_of_file")) state state state
    (.var "request") (.expression [.symbol "readln!"]) _ (.symbol "end_of_file") endMarker
    [] output [] output [] output
  · exact read_end_io_returns program [] state output
  · exact match_fresh [] "request" _ rfl
  · apply case_io_returns program (requestEnvironment (.symbol "end_of_file"))
      (requestEnvironment (.symbol "end_of_file")) state state state
      (.var "request") (.symbol "end_of_file") endMarker endMarker streamRows _
      [] output [] output [] output stream_rows
    · exact variable_io_returns program _ state "request" [] output
    · simp [SpaceSemantics.selectCase,
        SpaceSemantics.matchValue_literal (SpaceSemantics.Literal.symbol "end_of_file")]
    · exact symbol_io_returns program _ state "MM0:End" [] output

/-- One source iteration prints the actual child answer, then uses the
remaining input through the same retained stream equation. -/
theorem request_returns (before middle after : State) (request answer : Atom)
    (remaining output printed : List Atom) (notEnd : request ≠ .symbol "end_of_file")
    (computed : PureReturnsIO program [] before request middle answer remaining output remaining output)
    (continued : PureReturnsIO program [] middle call after endMarker
      remaining (output ++ [answer]) [] printed) :
    PureReturnsIO program [] before call after endMarker (request :: remaining) output [] printed := by
  apply stream_call_returns
  rw [stream_shape]
  apply let_io_returns program [] (requestEnvironment request) before before after
    (.var "request") (.expression [.symbol "readln!"]) _ request endMarker
    (request :: remaining) output remaining output [] printed
  · exact read_line_io_returns program [] before request remaining output
  · exact match_fresh [] "request" _ rfl
  · apply case_io_returns program (requestEnvironment request) (callEnvironment request)
      before before after (.var "request") request loopBody endMarker streamRows _
      remaining output remaining output [] printed stream_rows
    · exact variable_io_returns program _ before "request" remaining output
    · simp only [SpaceSemantics.selectCase,
        SpaceSemantics.matchValue_literal (SpaceSemantics.Literal.symbol "end_of_file"),
        Ne.symm notEnd, ↓reduceIte]
      rw [match_fresh _ "call" request (by simp [requestEnvironment, Subst.lookup])]
      rfl
    · rw [loop_shape]
      apply let_io_returns program (callEnvironment request) (answerEnvironment request answer)
        before middle after (.var "answer") (.expression [.symbol "eval", .var "call"]) _ answer endMarker
        remaining output remaining output [] printed
      · exact eval_variable_io_returns program _ before middle "call" request answer
          remaining output remaining output (by decide) rfl computed
      · exact match_fresh _ "answer" answer (by simp [callEnvironment, requestEnvironment, Subst.lookup])
      · apply let_io_returns program (answerEnvironment request answer) (printedEnvironment request answer)
          middle middle after (.var "printed") (.expression [.symbol "println!", .var "answer"]) call
          (boolean true) endMarker remaining output remaining (output ++ [answer]) [] printed
        · exact println_variable_io_returns program _ middle "answer" answer remaining output (by decide) rfl
        · exact match_fresh _ "printed" _ (by simp [answerEnvironment, callEnvironment, requestEnvironment, Subst.lookup])
        · exact nullary_capture_io_returns program [] _ middle after "mm0:stream" endMarker
            remaining (output ++ [answer]) [] printed (by decide) (by decide) continued

private theorem symbol_safe (name : String) : codeSafe excluded (.symbol name) = true := by simp [codeSafe, SpaceSemantics.patternHeads]
private theorem natural_safe (index : Nat) : codeSafe excluded (Store.natural index) = true := by simp [Store.natural, codeSafe, SpaceSemantics.patternHeads]
private theorem boolean_safe (value : Bool) : codeSafe excluded (boolean value) = true := by simp [boolean, codeSafe, SpaceSemantics.patternHeads]

private theorem constructor_safe (head : String) (items : List Atom)
    (allowed : blocked excluded head = false) (safe : ∀ item ∈ items, codeSafe excluded item = true) :
    codeSafe excluded (.expression (.symbol head :: items)) = true := by
  rw [expression_safe]
  simp only [allowed, Bool.not_false, List.all_cons, symbol_safe, Bool.true_and]
  exact List.all_eq_true.mpr safe

private theorem container_safe (items : List Atom) (safe : codeSafe excluded (.expression items) = true) :
    codeSafe excluded (ListAccess.listValue items) = true := by
  apply constructor_safe "MM0:L" [.expression items] (by decide)
  intro item member
  obtain rfl := List.mem_singleton.mp member
  exact safe

private theorem tagged_safe (head : String) (items : List Atom)
    (allowed : blocked excluded head = false) (safe : ∀ item ∈ items, codeSafe excluded item = true) :
    codeSafe excluded (ListAccess.listValue (.symbol head :: items)) = true :=
  container_safe _ (constructor_safe head items allowed safe)

private theorem mapped_safe {Value : Type} (encode : Value → Atom) (values : List Value)
    (safe : ∀ value ∈ values, codeSafe excluded (encode value) = true)
    (nonSymbol : ∀ value name, encode value ≠ .symbol name) :
    codeSafe excluded (ListAccess.listValue (values.map encode)) = true := by
  apply container_safe
  rw [expression_safe]
  have members : (values.map encode).all (codeSafe excluded) = true := by
    apply List.all_eq_true.mpr
    intro item member
    obtain ⟨value, belongs, rfl⟩ := List.mem_map.mp member
    exact safe value belongs
  rw [members, Bool.and_true]
  cases values with
  | nil => rfl
  | cons first rest =>
      simp only [List.map_cons]
      cases observed : encode first with
      | symbol name => exact False.elim (nonSymbol first name observed)
      | var | grounded | expression => rfl

private theorem preterm_safe (value : Kernel.Preterm) : codeSafe excluded (Data.preterm value) = true := by
  induction value with
  | var index => exact constructor_safe "MM0:Var" _ (by decide) (by simpa using natural_safe index)
  | term index => exact constructor_safe "MM0:Term" _ (by decide) (by simpa using natural_safe index)
  | app function argument first second =>
      apply constructor_safe "MM0:App" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact first
      · exact second

private theorem indices_safe (values : List Nat) : codeSafe excluded (Support.indicesValue values) = true :=
  mapped_safe Store.natural values (fun index _ => natural_safe index) (by intro index name; simp [Store.natural])

private theorem dependencies_safe (values : Finset Nat) : codeSafe excluded (Data.dependencies values) = true :=
  mapped_safe Store.natural _ (fun index _ => natural_safe index) (by intro index name; simp [Store.natural])

private theorem binder_safe (value : Kernel.Binder) : codeSafe excluded (Data.binder value) = true := by
  cases value with
  | bound sort =>
      exact tagged_safe "MM0:Bound" _ (by decide) (by simpa using natural_safe sort)
  | regular sort values =>
      apply tagged_safe "MM0:Regular" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe sort
      · exact dependencies_safe values

private theorem context_safe (values : Kernel.Context) : codeSafe excluded (Data.context values) = true :=
  mapped_safe Data.binder values (fun value _ => binder_safe value) (by intro value name; cases value <;> simp [Data.binder, ListAccess.listValue])

private theorem expressions_safe (values : List Kernel.Preterm) :
    codeSafe excluded (ListSubstitution.expressionsValue values) = true :=
  mapped_safe Data.preterm values (fun value _ => preterm_safe value) (by intro value name; cases value <;> simp [Data.preterm])

private theorem term_declaration_safe (value : Kernel.TermDecl) : codeSafe excluded (Data.declaration value) = true := by
  apply tagged_safe "MM0:TermDecl" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact context_safe value.arguments
  · exact natural_safe value.resultSort
  · exact dependencies_safe value.dependencies

private theorem theorem_declaration_safe (value : Kernel.TheoremDecl) :
    codeSafe excluded (TheoremInstantiation.declarationValue value) = true := by
  apply tagged_safe "MM0:Theorem" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact context_safe value.arguments
  · exact expressions_safe value.hypotheses
  · exact preterm_safe value.conclusion

private theorem body_safe (value : Kernel.Definition.Body) : codeSafe excluded (Unfolding.bodyValue value) = true := by
  apply tagged_safe "MM0:Definition" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact indices_safe value.dummies
  · exact preterm_safe value.expression

private theorem sort_safe (value : Kernel.SortInfo) : codeSafe excluded (SortFormation.sortValue value) = true := by
  apply tagged_safe "MM0:Sort" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact boolean_safe _

private theorem option_safe (value : Option Atom) (safe : ∀ item, value = some item → codeSafe excluded item = true) :
    codeSafe excluded (ListAccess.optionValue value) = true := by
  cases value with
  | none => exact symbol_safe "None"
  | some item => exact constructor_safe "Some" _ (by decide) (by simpa using safe item rfl)

private theorem conversion_safe (witness : Kernel.ConvWitness) :
    codeSafe excluded (Conversion.witnessValue witness) = true := by
  cases witness with
  | refl expression =>
      simp only [Conversion.witnessValue]
      exact tagged_safe "MM0:ConvRefl" _ (by decide) (by simpa using preterm_safe expression)
  | symm child =>
      simp only [Conversion.witnessValue]
      exact tagged_safe "MM0:ConvSymm" _ (by decide) (by simpa using conversion_safe child)
  | trans first second =>
      simp only [Conversion.witnessValue]
      apply tagged_safe "MM0:ConvTrans" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact conversion_safe first
      · exact conversion_safe second
  | congruence index children =>
      simp only [Conversion.witnessValue]
      apply tagged_safe "MM0:ConvCongruence" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact mapped_safe Conversion.witnessValue children (fun child _ => conversion_safe child)
          (by intro child name; cases child <;> simp [Conversion.witnessValue, ListAccess.listValue])
  | unfold index arguments images =>
      simp only [Conversion.witnessValue]
      apply tagged_safe "MM0:ConvUnfold" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact natural_safe index
      · exact expressions_safe arguments
      · exact indices_safe images
termination_by sizeOf witness

private theorem proof_safe (witness : Kernel.ProofWitness) : codeSafe excluded (Proof.witnessValue witness) = true := by
  cases witness with
  | hyp index =>
      simp only [Proof.witnessValue, Hypothesis.witness]
      exact tagged_safe "MM0:Hyp" _ (by decide) (by simpa using natural_safe index)
  | theoremApp index arguments children =>
      simp only [Proof.witnessValue]
      apply tagged_safe "MM0:TheoremApp" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact natural_safe index
      · exact expressions_safe arguments
      · exact mapped_safe Proof.witnessValue children (fun child _ => proof_safe child)
          (by intro child name; cases child <;> simp [Proof.witnessValue, Hypothesis.witness, ListAccess.listValue])
  | conversion witness child =>
      simp only [Proof.witnessValue]
      apply tagged_safe "MM0:Conversion" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact conversion_safe witness
      · exact proof_safe child
termination_by sizeOf witness

private theorem option_preterm_safe (value : Option Kernel.Preterm) :
    codeSafe excluded (ProofResults.resultValue value) = true := by
  apply option_safe
  intro item found
  obtain ⟨expression, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact preterm_safe expression

private theorem option_body_safe (value : Option Kernel.Definition.Body) :
    codeSafe excluded (ListAccess.optionValue (value.map Unfolding.bodyValue)) = true := by
  apply option_safe
  intro item found
  obtain ⟨body, _, rfl⟩ := Option.map_eq_some_iff.mp found
  exact body_safe body

private theorem entry_safe (value : Kernel.SpecificationEntry) :
    codeSafe excluded (SpecificationMatching.entryValue value) = true := by
  cases value with
  | sort index info =>
      apply tagged_safe "MM0:SpecSort" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact sort_safe info
  | term index declaration =>
      apply tagged_safe "MM0:SpecTerm" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact term_declaration_safe declaration
  | definition index declaration body =>
      apply tagged_safe "MM0:SpecDefinition" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact natural_safe index
      · exact term_declaration_safe declaration
      · exact option_body_safe body
  | axiomDecl index declaration =>
      apply tagged_safe "MM0:SpecAxiom" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact theorem_declaration_safe declaration
  | theoremDecl index declaration =>
      apply tagged_safe "MM0:SpecTheorem" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact theorem_declaration_safe declaration

theorem pending_code_safe (entries : List Kernel.SpecificationEntry) :
    codeSafe excluded (SpecificationMatching.pendingValue entries) = true :=
  mapped_safe SpecificationMatching.entryValue entries (fun entry _ => entry_safe entry)
    (by intro entry name; cases entry <;> simp [SpecificationMatching.entryValue, ListAccess.listValue])

private theorem admission_safe (value : Kernel.Admission) : codeSafe excluded (AdmissionChecks.admissionValue value) = true := by
  cases value with
  | sort index info =>
      apply tagged_safe "MM0:AdmitSort" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact sort_safe info
  | term index declaration =>
      apply tagged_safe "MM0:AdmitTerm" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact term_declaration_safe declaration
  | definition index declaration body =>
      apply tagged_safe "MM0:AdmitDefinition" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact natural_safe index
      · exact term_declaration_safe declaration
      · exact body_safe body
  | axiomDecl index declaration =>
      apply tagged_safe "MM0:AdmitAxiom" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact natural_safe index
      · exact theorem_declaration_safe declaration
  | theoremDecl index declaration dummies proof =>
      apply tagged_safe "MM0:AdmitTheorem" _ (by decide)
      intro item member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact natural_safe index
      · exact theorem_declaration_safe declaration
      · exact indices_safe dummies
      · exact proof_safe proof

private theorem declaration_safe (value : Kernel.ProofDeclaration) :
    codeSafe excluded (SpecificationMatching.declarationValue value) = true := by
  apply tagged_safe "MM0:ProofDeclaration" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact boolean_safe value.isLocal
  · exact admission_safe value.admission

private theorem saved_safe (value : Sharing.Entry) : codeSafe excluded (Sharing.entryValue value) = true := by
  apply constructor_safe "MM0:Saved" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact option_preterm_safe value.expected
  · exact proof_safe value.witness

private theorem shared_command_safe (value : SharedService.Command) :
    codeSafe excluded (SharedService.commandValue value) = true := by
  apply constructor_safe "MM0:SharedTheorem" _ (by decide)
  intro item member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact boolean_safe value.isLocal
  · exact natural_safe value.index
  · exact theorem_declaration_safe value.declaration
  · exact indices_safe value.dummies
  · exact mapped_safe Sharing.entryValue value.saved (fun entry _ => saved_safe entry)
      (by intro entry name; simp [Sharing.entryValue])
  · exact proof_safe value.root

theorem command_code_safe (value : SessionProtocol.Command) : codeSafe excluded (SessionProtocol.commandValue value) = true := by
  cases value with
  | inl declaration => exact declaration_safe declaration
  | inr shared => exact shared_command_safe shared


def finishRequest : Atom := .expression [.symbol "mm0:finish"]

def requests (start : FrontendBindings.Request) (submissions : List FrontendBindings.Request) : List Atom :=
  start.body "mm0:start" :: submissions.map (·.body "mm0:submit") ++ [finishRequest]

def configuration (before : State) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request) : Configuration :=
  { state := before, control := .evaluate [] call, input := requests start submissions }

/-- The service loop is the retained program's sole executable initializer. -/
theorem retained_initializer : program.initializers = [call] := by decide +kernel

private theorem finish_safe : codeSafe excluded finishRequest = true :=
  constructor_safe "mm0:finish" [] (by decide) (by simp)

private theorem body_not_end (request : FrontendBindings.Request) (head : String) :
    request.body head ≠ .symbol "end_of_file" := by
  cases shape : request.constructors <;> simp [FrontendBindings.Request.body, FrontendBindings.wrap, shape]

/-- Every supplied wrapper is executed with the existing receipt's result.
The stream prints all occurrences, including false responses after refusal. -/
theorem trace_returns {spaces : SessionInitialization.Spaces}
    {logical terminal : Option Kernel.SpecificationAdmission.State} {before after : State}
    {commands : List SessionProtocol.Command} {answers : List Bool}
    (trace : SessionProtocol.Trace spaces logical before commands answers terminal after)
    (submissions : List FrontendBindings.Request)
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (stored : SessionDriver.Stored spaces terminal after) (output : List Atom) :
    PureReturnsIO program [] before call after endMarker
      (submissions.map (·.body "mm0:submit") ++ [finishRequest]) output []
      (output ++ answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) := by
  induction trace generalizing submissions output with
  | nil logical before =>
      cases encoded with
      | nil =>
          simpa only [List.map_nil, List.nil_append, List.append_nil] using
            request_returns before before before finishRequest (boolean (SessionProtocol.finishedStatus logical))
              [] output (output ++ [boolean (SessionProtocol.finishedStatus logical)]) (by simp [finishRequest])
              (returns_with_io program excluded checker_closed let_allowed [] before before finishRequest
                [boolean (SessionProtocol.finishedStatus logical)] [] output finish_safe
                (SessionDriver.finish_returns spaces logical before [] stored))
              (eof_returns before (output ++ [boolean (SessionProtocol.finishedStatus logical)]))
  | @cons logical next terminal before middle after command commands answers receipt rest ih =>
      cases encoded with
      | @cons _ request _ submissions firstEncoded remainingEncoded =>
          have computed := returns_with_io program excluded checker_closed let_allowed [] before middle
            (request.body "mm0:submit") [boolean next.isSome]
            (submissions.map (·.body "mm0:submit") ++ [finishRequest]) output
            (request.body_code_safe _ "mm0:submit" firstEncoded (by decide) (command_code_safe command))
            (request.submit_receipt_returns firstEncoded receipt)
          have continued := ih submissions remainingEncoded stored (output ++ [boolean next.isSome])
          have combined := request_returns before middle after (request.body "mm0:submit") (boolean next.isSome)
            (submissions.map (·.body "mm0:submit") ++ [finishRequest]) output _
            (body_not_end request _) computed continued
          simpa only [List.map_cons, List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using combined

/-- Exact constructor-wrapped input runs through the actual pinned stream.
The marker is returned, while the complete Boolean response trace is printed. -/
theorem protocol_returns (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions) :
    ∃ after answers terminal,
      (theory program).MultiStep (configuration before start submissions)
        (finished after [endMarker] [] (boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)])) ∧
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
  have computed := returns_with_io program excluded checker_closed let_allowed [] before
    (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
    (start.body "mm0:start") [boolean true]
    (submissions.map (·.body "mm0:submit") ++ [finishRequest]) []
    (start.body_code_safe _ "mm0:start" startEncoded (by decide) (pending_code_safe specification))
    (start.start_returns specification startEncoded before)
  have continued := trace_returns trace submissions encoded stored [boolean true]
  simpa only [configuration, requests, List.nil_append, List.singleton_append, List.cons_append] using
    request_returns before _ after (start.body "mm0:start") (boolean true)
      (submissions.map (·.body "mm0:submit") ++ [finishRequest]) [] _
      (body_not_end start _) computed continued

theorem sufficient_fuel (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions) :
    ∃ after answers terminal fuel,
      (∀ extra, run program (fuel + extra) (configuration before start submissions) =
        .complete after [endMarker] [] (boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)])) ∧
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      SessionDriver.Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      answers.length = commands.length ∧
      ((boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) =
        List.replicate (commands.length + 2) (boolean true) ↔
          ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨after, answers, terminal, path, trace, stored, length, accepted⟩ :=
    protocol_returns before specification commands start submissions startEncoded encoded
  obtain ⟨fuel, completed⟩ := path_has_sufficient_fuel program _ after [endMarker] [] _ path
  exact ⟨after, answers, terminal, fuel,
    fun extra => completed_run_more_fuel program fuel extra _ after [endMarker] [] _ completed,
    trace, stored, length, accepted⟩

/-- Any completed stream observation has exactly the response trace derived
from its original requests. Completion supplies no extra authorization. -/
theorem completed_protocol (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (after : State) (fuel : Nat) (result unread printed : List Atom)
    (completed : run program fuel (configuration before start submissions) = .complete after result unread printed) :
    ∃ answers terminal,
      result = [endMarker] ∧ unread = [] ∧
      printed = (boolean true :: answers.map boolean ++ [boolean (SessionProtocol.finishedStatus terminal)]) ∧
      SessionProtocol.Trace (SessionInitialization.allocatedSpaces before) (some ⟨{}, specification⟩)
        (SessionInitialization.startState before (SpecificationMatching.pendingValue specification))
        commands answers terminal after ∧
      SessionDriver.Stored (SessionInitialization.allocatedSpaces before) terminal after ∧
      printed.length = commands.length + 2 ∧
      (printed = List.replicate (commands.length + 2) (boolean true) ↔
        ∃ finalTheory, terminal = some ⟨finalTheory, []⟩) := by
  obtain ⟨reference, answers, terminal, referenceFuel, enough, trace, stored, length, gate⟩ :=
    sufficient_fuel before specification commands start submissions startEncoded encoded
  have referenceCompleted := enough 0
  simp only [Nat.add_zero] at referenceCompleted
  obtain ⟨sameState, sameResult, sameUnread, samePrinted⟩ := completed_result_unique program referenceFuel fuel _
    reference after _ [] _ result unread printed referenceCompleted completed
  subst after
  refine ⟨answers, terminal, sameResult.symm, sameUnread.symm, samePrinted.symm, trace, stored, ?_, ?_⟩
  · rw [← samePrinted]; simp [length]
  · rw [← samePrinted]; exact gate

/-- All printed responses are true only after the independently supplied
specification has been consumed with its exact authorized axiom basis. -/
theorem accepted_consumes_specification (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (after : State) (fuel : Nat)
    (accepted : run program fuel (configuration before start submissions) =
      .complete after [endMarker] [] (List.replicate (commands.length + 2) (boolean true))) :
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
    completed_protocol before specification commands start submissions startEncoded encoded after fuel _ [] _ accepted
  obtain ⟨finalTheory, same⟩ := gate.mp rfl
  obtain ⟨declarations, images, history, verified, axioms, specified⟩ := trace.consumed_specification finalTheory same
  rw [same] at trace stored
  cases stored with
  | active live => exact ⟨finalTheory, declarations, answers, trace, live, images, history, verified, axioms, specified⟩

/-- Each original shared command has a specified proof in its actual
preceding checked history; it is not justified by its later publication. -/
theorem accepted_shared_preceding_proof (before : State) (specification : List Kernel.SpecificationEntry)
    (commands : List SessionProtocol.Command) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request => request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (after : State) (fuel : Nat)
    (accepted : run program fuel (configuration before start submissions) =
      .complete after [endMarker] [] (List.replicate (commands.length + 2) (boolean true)))
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map Kernel.ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨finalTheory, _, answers, trace, _, _, _, _, _, _⟩ :=
    accepted_consumes_specification before specification commands start submissions startEncoded encoded after fuel accepted
  exact trace.shared_preceding_proof ⟨{}, specification⟩ ⟨finalTheory, []⟩ rfl rfl specification [] (.nil _) command belongs

/-- The accepted stream observation is exactly a path in the existing
judgment-generated PeTTa GSLT. -/
theorem accepted_iff_gslt_path (before after : State) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request) (count : Nat) :
    (∃ fuel, run program fuel (configuration before start submissions) =
      .complete after [endMarker] [] (List.replicate count (boolean true))) ↔
      (theory program).MultiStep (configuration before start submissions)
        (finished after [endMarker] [] (List.replicate count (boolean true))) :=
  completed_run_iff_path program _ after [endMarker] [] _

/-- The same accepted observation has a derivation in the existing
whole-program transition judgment. -/
theorem accepted_iff_petta_judgment (before after : State) (start : FrontendBindings.Request)
    (submissions : List FrontendBindings.Request) (count : Nat) :
    (∃ fuel, run program fuel (configuration before start submissions) =
      .complete after [endMarker] [] (List.replicate count (boolean true))) ↔
      DeclarativeSpec.Runs program (configuration before start submissions)
        (.complete after [endMarker] [] (List.replicate count (boolean true))) :=
  completed_run_iff_derivation program _ after [endMarker] [] _

/-- The accepted stream observation is exactly a path in the authored configuration language. -/
theorem accepted_iff_language_path (before after : State) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (start : FrontendBindings.Request) (submissions : List FrontendBindings.Request)
    (count : Nat) :
    (∃ fuel, run program fuel (configuration before start submissions) =
      .complete after [endMarker] [] (List.replicate count (boolean true))) ↔
      ∃ target,
        (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
          ConfigurationLanguageDef.language).MultiStep
          (ConfigurationEncoding.encode (configuration before start submissions) names) target ∧
        ConfigurationEncoding.decode target =
          some (finished after [endMarker] [] (List.replicate count (boolean true))) :=
  ConfigurationLanguageDef.completed_run_iff_generated_path program _ names vacant covers
    after [endMarker] [] _

/-- Accepted generated paths retain the actual independently authorized specification history. -/
theorem language_path_consumes_specification (before : State)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (specification : List Kernel.SpecificationEntry) (commands : List SessionProtocol.Command)
    (start : FrontendBindings.Request) (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request =>
      request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (after : State) (target : Pattern)
    (path : (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
      ConfigurationLanguageDef.language).MultiStep
      (ConfigurationEncoding.encode (configuration before start submissions) names) target)
    (completed : ConfigurationEncoding.decode target =
      some (finished after [endMarker] []
        (List.replicate (commands.length + 2) (boolean true)))) :
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
        (Upstream.Lean3Typing.projectRun
          ((commands.map SessionProtocol.inputDeclaration).map Kernel.ProofDeclaration.admission)) := by
  obtain ⟨fuel, accepted⟩ :=
    (accepted_iff_language_path before after names vacant covers start submissions _).mpr
      ⟨target, path, completed⟩
  exact accepted_consumes_specification before specification commands start submissions
    startEncoded encoded after fuel accepted

/-- Shared proofs are justified in the checked history preceding their generated path occurrence. -/
theorem language_path_shared_preceding_proof (before : State)
    (names : List String) (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (specification : List Kernel.SpecificationEntry) (commands : List SessionProtocol.Command)
    (start : FrontendBindings.Request) (submissions : List FrontendBindings.Request)
    (startEncoded : start.Encodes (SpecificationMatching.pendingValue specification))
    (encoded : List.Forall₂ (fun command request =>
      request.Encodes (SessionProtocol.commandValue command)) commands submissions)
    (after : State) (target : Pattern)
    (path : (langGSLTUsing (ConfigurationLanguageDef.relationEnv program)
      ConfigurationLanguageDef.language).MultiStep
      (ConfigurationEncoding.encode (configuration before start submissions) names) target)
    (completed : ConfigurationEncoding.decode target =
      some (finished after [endMarker] []
        (List.replicate (commands.length + 2) (boolean true))))
    (command : SharedService.Command) (belongs : Sum.inr command ∈ commands) :
    ∃ precedingHistory current,
      Kernel.SpecificationAdmission.Runs ⟨{}, specification⟩ precedingHistory current ∧
      Upstream.Lean3ProofAdmission.Reference.SpecifiedProof
        (Upstream.Lean3Typing.projectRun (precedingHistory.map Kernel.ProofDeclaration.admission))
        (Upstream.Lean3Typing.Reference.ofContext
          (Kernel.Admission.proofContext command.declaration command.dummies))
        (Upstream.Lean3ProofAdmission.sourceHypotheses command.declaration.hypotheses)
        (Upstream.Lean3Typing.Reference.SExpr.ofKernel command.declaration.conclusion) := by
  obtain ⟨fuel, accepted⟩ :=
    (accepted_iff_language_path before after names vacant covers start submissions _).mpr
      ⟨target, path, completed⟩
  exact accepted_shared_preceding_proof before specification commands start submissions
    startEncoded encoded after fuel accepted command belongs

namespace Controls

open FrontendBindings

private def resolved (value : Atom) : Request := ⟨[], [], value⟩

private def info : Kernel.SortInfo := { provable := true }
private def primitive : Kernel.TermDecl := ⟨[], 0, ∅⟩
private def sourceStatement : Atom := ListAccess.listValue
  [.symbol "MM0:Theorem", Data.context [], ListSubstitution.expressionsValue [], .var (inputName 0)]
private def fixtureStart : Request := ⟨[.term 1], [.term 1], ListAccess.listValue
  [SpecificationMatching.entryValue (.sort 0 info), SpecificationMatching.entryValue (.term 1 primitive),
    ListAccess.listValue [.symbol "MM0:SpecAxiom", Store.natural 10, sourceStatement],
    ListAccess.listValue [.symbol "MM0:SpecTheorem", Store.natural 12, sourceStatement]]⟩
private def sortRequest : Request := resolved (SpecificationMatching.declarationValue ⟨.sort 0 info, false⟩)
private def termRequest : Request := resolved (SpecificationMatching.declarationValue ⟨.term 1 primitive, false⟩)
private def axiomRequest : Request := ⟨[.term 1], [.term 1], ListAccess.listValue
  [.symbol "MM0:ProofDeclaration", boolean false,
    ListAccess.listValue [.symbol "MM0:AdmitAxiom", Store.natural 10, sourceStatement]]⟩
private def theoremRequest (saved : List Atom) (root : Kernel.ProofWitness) : Request :=
  ⟨[.term 1], [.term 1], .expression [.symbol "MM0:SharedTheorem", boolean false, Store.natural 12,
    sourceStatement, Support.indicesValue [], ListAccess.listValue saved, Proof.witnessValue root]⟩
private def initializer : Atom := .expression [.symbol "MM0:Saved", .expression [.symbol "Some", .var (inputName 0)],
  Proof.witnessValue (.theoremApp 10 [] [])]
private def validRequest : Request := theoremRequest [initializer] (.hyp 0)
private def prefixRequests : List Request := [sortRequest, termRequest, axiomRequest]

private def observation : Outcome → Option (List Atom × List Atom × List Atom)
  | .complete _ result unread output => some (result, unread, output)
  | _ => none

/-- A finite constructor-wrapped stream admits real declarations and a
nonempty saved proof, then prints six true responses before returning EOF. -/
theorem nonempty_shared_stream_accepts :
    observation (run program 20000 (configuration (Effects.loaded program) fixtureStart (prefixRequests ++ [validRequest]))) =
      some ([endMarker], [], List.replicate 6 (boolean true)) := by decide +kernel

/-- An available valid proof cannot rescue the original submitted bad root;
the repaired request and finish both retain the failed session. -/
theorem bad_root_stream_stays_refused :
    observation (run program 20000 (configuration (Effects.loaded program) fixtureStart
      (prefixRequests ++ [theoremRequest [initializer] (.hyp 1), validRequest]))) =
      some ([endMarker], [], List.replicate 4 (boolean true) ++ List.replicate 3 (boolean false)) := by decide +kernel

/-- A future saved slot is checked even without an expected conclusion.
The valid ordinary root cannot bypass that failed initializer. -/
theorem future_initializer_stream_stays_refused :
    observation (run program 20000 (configuration (Effects.loaded program) fixtureStart
      (prefixRequests ++ [theoremRequest [.expression [.symbol "MM0:Saved", .symbol "None", Proof.witnessValue (.hyp 0)]]
        (.theoremApp 10 [] []), validRequest]))) =
      some ([endMarker], [], List.replicate 4 (boolean true) ++ List.replicate 3 (boolean false)) := by decide +kernel

/-- EOF with an unfinished specification is an observation, not acceptance. -/
theorem unfinished_specification_prints_false :
    observation (run program 2000 (configuration (Effects.loaded program) fixtureStart [])) =
      some ([endMarker], [], [boolean true, boolean false]) := by decide +kernel

/-- Empty input returns the marker without any successful checker response. -/
theorem marker_alone_has_no_responses (state : State) :
    ∃ fuel, run program fuel { state, control := .evaluate [] call } =
      .complete state [endMarker] [] [] :=
  path_has_sufficient_fuel program _ state [endMarker] [] [] (eof_returns state [])

end Controls

end Mettapedia.Languages.MM0.MeTTa.StreamProtocol
