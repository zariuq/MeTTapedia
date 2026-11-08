import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
import Mettapedia.Languages.MeTTa.PeTTa.EagerDFSProducer
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.Machines.Cursor.OwnedLifecycle
import Mettapedia.Machines.CMemory.EffectStatements
import Mettapedia.Machines.CMemory.Tactic
import Mettapedia.Machines.CMemory.ProductiveBlocks
import Mettapedia.GSLT.LanguageDef.NativeOpsCLexSegments
import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement

/-!
# Streaming source execution through labelled finite runs

The existing eager depth-first source machine instantiates the existing
productive-block run interface. A root answer is an ordered occurrence;
steps producing no root answer are silent to this observer. Output, input,
store, bindings, alternatives and caller frames remain in the saved source
configuration. Faults and malformed stopped configurations are handoffs
retaining that configuration, rather than successful exhaustion.

The adapter's readback is the actual source runner, and its event list is
exactly the extension of the source answer history. Budget splitting, prefix
growth and account splitting then use the generic labelled-run laws. No
global productivity rank, equivalence with the batch evaluator, native C
refinement or validity of a changed shared world is asserted by that adapter.

`NativePull` and `NativeGoals` then connect selected actual C blocks and
physical retained records to the shared run interface and the independent
destination component. They preserve whole child binding records, native
goal identities, older storage and the original output slot. The physical
ABI, native atom/binding reader, allocation and primitive services remain
explicit component boundaries. ARGUMENT_RETURN retains its saved height,
interpreted as a saved continuation delimiter; native choice and
collection completion are not consequences of these local squares.

The module and namespace were formerly named
`Mettapedia.Languages.MeTTa.PeTTa.CettaDFSStreaming`. The current name records
that this is a streaming adapter for the pure-Lean eager DFS machine, while
CeTTa-specific native obligations remain in separately named modules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Configuration := EagerDFS.Configuration
abbrev Barrier := EagerDFSProducer.Barrier

/-- Select the existing eager evaluator or the retained finite Destination
component explicitly. The default retains historical eager collection behavior. -/
inductive ExecutionProfile : Type 1 where
  | eager
  | scopedDestination (Context : Type) (policy : EagerDFS.Destination.Policy)

namespace ExecutionProfile

abbrev State : ExecutionProfile → Type
  | .eager => Configuration
  | .scopedDestination context _ => EagerDFS.Destination.ScopedCursor context

abbrev Event : ExecutionProfile → Type
  | .eager => Atom
  | .scopedDestination _ _ => EagerDFS.Destination.CollectedAnswer

abbrev Request : ExecutionProfile → Type
  | .eager => Barrier
  | .scopedDestination _ _ => EagerDFS.Destination.ScopeBoundary

end ExecutionProfile

/-- One existing driver supplies budgeting and resumption for both explicit
profiles. The scoped case retains allocator authority and every source scope;
it does not identify its component admission with the default eager language. -/
def machine (program : Program) (profile : ExecutionProfile := .eager) :
    Machine profile.State profile.Event profile.State profile.Request :=
  match profile with
  | .eager => {
    step configuration := some <|
      match EagerDFS.step program configuration with
      | some next =>
          match EagerDFSProducer.emission configuration with
          | [] => .silent next
          | values => .publish values next
      | none =>
          if EagerDFS.completed configuration then .finish configuration
          else match EagerDFS.fault configuration with
            | some reason => .call (.fault reason) configuration
            | none => .call .stopped configuration }
  | .scopedDestination _ policy => {
    step source := some (EagerDFS.Destination.scopeStep policy program source) }

/-- Read back every retained or completed configuration. A generic faulted
outcome has no configuration; this adapter never produces that outcome. -/
def readback : Outcome Configuration Configuration Barrier → Option Configuration
  | .finished configuration | .stuck configuration | .exhausted configuration =>
      some configuration
  | .suspended _ configuration => some configuration
  | .faulted => none

/-- Readback of any finite labelled run is the independently executable
source runner, including its world and complete control state. -/
theorem run_readback (program : Program) (fuel : Nat) (source : Configuration) :
    readback ((machine program).run fuel source).2 =
      some (EagerDFS.advance program fuel source) := by
  induction fuel generalizing source with
  | zero => rfl
  | succ fuel ih =>
      cases stepped : EagerDFS.step program source with
      | none =>
          by_cases finished : EagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, readback, EagerDFS.advance]
          · cases failed : EagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, readback,
                EagerDFS.advance]
      | some next =>
          cases emitted : EagerDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, EagerDFS.advance] using ih next
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, EagerDFS.advance] using ih next

/-- The observed prefix is exactly the new source answer occurrences. Equal
values at different positions remain different list entries. -/
theorem run_answer_history (program : Program) (fuel : Nat) (source : Configuration)
    (valid : EagerDFS.ScopesValid source.scopes) :
    EagerDFS.answers (EagerDFS.advance program fuel source) =
      EagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  induction fuel generalizing source with
  | zero => simp [EagerDFS.advance, Machine.run]
  | succ fuel ih =>
      cases stepped : EagerDFS.step program source with
      | none =>
          by_cases finished : EagerDFS.completed source = true
          · simp [Machine.run, machine, stepped, finished, EagerDFS.advance]
          · cases failed : EagerDFS.fault source <;>
              simp [Machine.run, machine, stepped, finished, failed, EagerDFS.advance]
      | some next =>
          have transition := EagerDFS.step_transition stepped
          have retained := EagerDFS.transition_scopes_valid transition valid
          have appended := EagerDFSProducer.transition_answers transition valid
          have later := ih next retained
          cases emitted : EagerDFSProducer.emission source with
          | nil =>
              simpa [Machine.run, machine, stepped, emitted, EagerDFS.advance,
                appended] using later
          | cons value rest =>
              simpa [Machine.run, machine, stepped, emitted, EagerDFS.advance,
                appended, List.append_assoc] using later

/-- Every bounded prefix has a genuine path in the independent source rules,
with at most one source transition per scheduler inspection. -/
theorem run_source (program : Program) (fuel : Nat) (source : Configuration)
    (valid : EagerDFS.ScopesValid source.scopes) :
    ∃ target count, count ≤ fuel ∧
      readback ((machine program).run fuel source).2 = some target ∧
      EagerDFS.SourceRun program count source target ∧
      EagerDFS.ScopesValid target.scopes ∧
      EagerDFS.answers target =
        EagerDFS.answers source ++ ((machine program).run fuel source).1 := by
  obtain ⟨count, bound, path⟩ := EagerDFS.advance_has_source_run program fuel source
  exact ⟨_, count, bound, run_readback program fuel source, path,
    EagerDFS.advance_scopes_valid program fuel source valid,
    run_answer_history program fuel source valid⟩

/-- The owned producer log and the labelled run observe the same actual
source prefix. Capture and admission microsteps need not have the same count
as source transitions; the earned source path supplies the matching budget. -/
theorem producer_log_correspondence {Stored Context Output : Type} {clients : Nat}
    (program : Program) (capture : Atom → Option Stored) (capacity : Stored → Bool)
    (compatible : Context → Bool) (ticks : Nat)
    (packet : EagerDFSProducer.Packet Stored Context Output clients)
    (execution : Mettapedia.Machines.Cursor.ProducerOccurrenceLog.Execution
      Configuration Atom Empty Barrier)
    (attached : packet.execution = some execution)
    (valid : EagerDFS.ScopesValid execution.producer.scopes) :
    let result := Mettapedia.Machines.Cursor.ProducerOccurrenceLog.run
      (EagerDFSProducer.step program) capture capacity compatible ticks packet
    ∃ next sourceSteps, result.2.execution = some next ∧
      EagerDFS.SourceRun program sourceSteps execution.producer next.producer ∧
      readback ((machine program).run sourceSteps execution.producer).2 = some next.producer ∧
      ((machine program).run sourceSteps execution.producer).1 =
        result.1.flatMap Mettapedia.Machines.Cursor.ProducerOccurrenceLog.returned := by
  dsimp only
  obtain ⟨next, count, retained, path, _, answers⟩ :=
    EagerDFSProducer.run_source capture capacity compatible ticks packet execution attached valid
  have advances := EagerDFS.source_run_advances path
  have observed := run_answer_history program count execution.producer valid
  rw [advances] at observed
  refine ⟨next, count, retained, path, ?_, ?_⟩
  · rw [run_readback, advances]
  · exact List.append_cancel_left (observed.symm.trans answers)

/-- The generic resumption law applies to the actual streaming evaluator,
preserving established occurrences and the complete saved configuration. -/
theorem resume_after_prefix (program : Program) (first second : Nat)
    (source residual : Configuration) (events : List Atom)
    (paused : (machine program).run first source = (events, .exhausted residual)) :
    (machine program).run (first + second) source =
      (events ++ ((machine program).run second residual).1,
        ((machine program).run second residual).2) :=
  (machine program).established_and_pending first second source residual events paused

/-- Longer budgets extend the ordered answer prefix without revising a final
status. Changing the strategy or source is not covered by this law. -/
theorem observation_prefix (program : Program) (first second : Nat)
    (source : Configuration) :
    ((machine program).observe first source).Prefix
      ((machine program).observe (first + second) source) :=
  (machine program).observe_prefix first second source

/-- A supplied price account splits at the exact saved state. Its physical
meaning and bounds require separate implementation evidence. -/
theorem account_split (program : Program) (price : Configuration → Nat)
    (first second : Nat) (source : Configuration) :
    (machine program).spent price (first + second) source =
      (machine program).spent price first source +
        (machine program).spentAfter price second ((machine program).run first source).2 :=
  (machine program).spent_add price first second source

namespace Controls

open EagerDFSProducer.Controls (program ready a b printReady)

def firstAnswer : Configuration :=
  EagerDFS.advance program 1 ready

theorem pause_after_one_answer :
    (machine program).run 1 ready = ([a], .exhausted firstAnswer) := rfl

theorem resume_keeps_both_remaining_occurrences :
    (machine program).run 2 firstAnswer =
      ([a, b], .exhausted (EagerDFS.advance program 3 ready)) := rfl

theorem split_after_an_observed_answer :
    (machine program).run 3 ready =
      ([a] ++ ((machine program).run 2 firstAnswer).1,
        ((machine program).run 2 firstAnswer).2) :=
  resume_after_prefix program 1 2 ready firstAnswer [a] pause_after_one_answer

/-- Restarting the initial computation repeats the established occurrence. -/
theorem restarting_repeats_an_answer :
    [a] ++ ((machine program).run 3 ready).1 ≠ ((machine program).run 3 ready).1 := by
  decide

theorem performed_output_survives_pause :
    (EagerDFS.advance program 1 printReady).world.output = [a] ∧
      ((machine program).run 1 printReady).1 = [] := ⟨rfl, rfl⟩

theorem resumption_does_not_repeat_output :
    (EagerDFS.advance program 2
      (EagerDFS.advance program 1 printReady)).world.output = [a] := rfl

theorem stopped_fault_is_not_completion (reason : Effects.Fault) :
    let source : Configuration :=
      ⟨ready.world, [{frontier := [⟨.fault reason, []⟩]}]⟩
    (machine program).run 1 source = ([], .suspended (.fault reason) source) := rfl

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming

/-! ## Native retained child and goal-array components -/

set_option maxRecDepth 12000
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativePull

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/- The selected PettaPullFrame fields are logical typed C cells. The embedded
Bindings record is copied in full; its byte layout and its interpretation as
a source substitution are separate obligations. No source step is used by
the memory operations. -/
def pullLayout : ReadExpressions.Layout := fun name =>
  if name = "machine".toList then some ⟨0, .pointer⟩
  else if name = "requested_child".toList then some ⟨1, .pointer⟩
  else if name = "completed_child".toList then some ⟨2, .pointer⟩
  else if name = "answer".toList then some ⟨3, .pointer⟩
  else if name = "step".toList then some ⟨4, .word⟩
  else if name = "environment".toList then some ⟨5, .embedded⟩
  else none

def ident (name : String) : CExpr := .identifier name.toList
def field (owner name : String) : CExpr := .field (ident owner) name.toList true

def requestBody : List CStatement :=
  [.assign (field "frame" "requested_child") (ident "child")]

def handoffBody : List CStatement :=
  [.assign (field "parent" "completed_child") (ident "child"),
   .assign (field "parent" "answer") (ident "result"),
   .assign (field "parent" "environment") (ident "bindings"),
   .assign (field "parent" "step") (ident "step")]

def consumeBody : List CStatement :=
  [.assign (.unary .dereference (ident "answer")) (field "frame" "answer"),
   .assign (.unary .dereference (ident "environment")) (field "frame" "environment"),
   .effect (.call "bindings_init".toList
     [.unary .address (field "frame" "environment")]),
   .assign (field "frame" "answer") .null,
   .assign (field "frame" "completed_child") .null]

def requestSource : String := "{ frame->requested_child = child; }"
def handoffSource : String := "{ parent->completed_child = child; parent->answer = result; parent->environment = bindings; parent->step = step; }"
def consumeSource : String := "{ *answer = frame->answer; *environment = frame->environment; bindings_init(&frame->environment); frame->answer = NULL; frame->completed_child = NULL; }"

def requestTokens : List Token := [.punctuation "{".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "requested_child".toList, .punctuation "=".toList, .identifier "child".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem request_lex : lex requestSource.toList = .ok requestTokens := by
  apply lex_of_completed
  decide +kernel
theorem request_parsed : blockText? [] requestSource.toList = some requestBody :=
  block_text_of_parts [] _ requestTokens _ request_lex (by rfl)
def handoffTokens : List Token := [.punctuation "{".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "completed_child".toList, .punctuation "=".toList, .identifier "child".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "result".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation "=".toList, .identifier "bindings".toList, .punctuation ";".toList, .identifier "parent".toList, .punctuation "->".toList, .identifier "step".toList, .punctuation "=".toList, .identifier "step".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem handoff_lex : lex handoffSource.toList = .ok handoffTokens := by
  apply lex_of_completed
  decide +kernel
theorem handoff_parsed : blockText? [] handoffSource.toList = some handoffBody :=
  block_text_of_parts [] _ handoffTokens _ handoff_lex (by rfl)
def consumeTokens : List Token := [.punctuation "{".toList, .punctuation "*".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation ";".toList, .punctuation "*".toList, .identifier "environment".toList, .punctuation "=".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation ";".toList, .identifier "bindings_init".toList, .punctuation "(".toList, .punctuation "&".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "environment".toList, .punctuation ")".toList, .punctuation ";".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "answer".toList, .punctuation "=".toList, .identifier "NULL".toList, .punctuation ";".toList, .identifier "frame".toList, .punctuation "->".toList, .identifier "completed_child".toList, .punctuation "=".toList, .identifier "NULL".toList, .punctuation ";".toList, .punctuation "}".toList]
theorem consume_lex : lex consumeSource.toList = .ok consumeTokens := by
  apply lex_of_completed
  decide +kernel
theorem consume_parsed : blockText? [] consumeSource.toList = some consumeBody :=
  block_text_of_parts [] _ consumeTokens _ consume_lex (by rfl)

def requestEnvironment (frame child : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "frame".toList then some (.ptr (some frame))
  else if name = "child".toList then some (.ptr (some child)) else none

def handoffEnvironment (parent child : Ptr) (answer : Option Ptr) (step : UInt32) :
    ReadExpressions.Environment := fun name =>
  if name = "parent".toList then some (.ptr (some parent))
  else if name = "child".toList then some (.ptr (some child))
  else if name = "result".toList then some (.ptr answer)
  else if name = "step".toList then some (.u32 step) else none

def consumeEnvironment (frame answer environment : Ptr) : ReadExpressions.Environment := fun name =>
  if name = "frame".toList then some (.ptr (some frame))
  else if name = "answer".toList then some (.ptr (some answer))
  else if name = "environment".toList then some (.ptr (some environment)) else none

/- C's aggregate assignment is a copy of the supplied whole embedded record,
not a read of an invented pointer-valued environment field. Scalar statements
continue through the existing field assignment interpreter. -/
def handoffAssignment (bindingSource : Ptr) (bindingWidth : Nat) : StatementBlock.Assignment :=
  fun layout environment statement =>
    match statement with
    | .assign (.field owner name true) (.identifier source) =>
      if name = "environment".toList ∧ source = "bindings".toList then do
        let actual ← ReadExpressions.expression layout environment owner
        let destination ← ReadExpressions.fieldAddress layout actual name
        CProg.copyCells bindingSource destination bindingWidth
        pure environment
      else StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement
    | _ => StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement

def consumeAssignment (bindingWidth : Nat) : StatementBlock.Assignment :=
  fun layout environment statement =>
    match statement with
    | .assign (.unary .dereference (.identifier destination))
        (.field owner name true) => do
      let address ← ReadExpressions.resolved (environment destination) >>= ReadExpressions.pointer
      match address with
      | none => CProg.undefined
      | some address =>
        if name = "environment".toList then do
          let actual ← ReadExpressions.expression layout environment owner
          let source ← ReadExpressions.fieldAddress layout actual name
          CProg.copyCells source address bindingWidth
          pure environment
        else do
          let value ← ReadExpressions.expression layout environment (.field owner name true)
          CProg.store address value
          pure environment
    | _ => StatementBlock.fieldAssignment ReadExpressions.expression layout environment statement

def bindingInitializer (empty : List CVal) : StatementBlock.Effect :=
  fun layout environment expression =>
    match expression with
    | .call name [address] =>
      if name = "bindings_init".toList then do
        let actual ← ReadExpressions.expression layout environment address >>= ReadExpressions.pointer
        match actual with
        | some destination => CProg.initializeCells destination empty
        | none => CProg.undefined
      else CProg.undefined
    | _ => CProg.undefined

def requestProgram (frame child : Ptr) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith {} (StatementBlock.fieldAssignment ReadExpressions.expression)
    pullLayout 0 2 (requestEnvironment frame child) requestBody

def handoffProgram (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (bindingWidth : Nat) : CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith {} (handoffAssignment bindingSource bindingWidth)
    pullLayout 0 5 (handoffEnvironment parent child answer step) handoffBody

def consumeProgram (frame answer environment : Ptr) (empty : List CVal) :
    CProg CVal ReadBlock.Result :=
  StatementBlock.executeWith { effect := bindingInitializer empty }
    (consumeAssignment empty.length) pullLayout 0 6
    (consumeEnvironment frame answer environment) consumeBody

def requestOperations (frame child : Ptr) : CProg CVal ReadBlock.Result := do
  CProg.store (frame + 1) (.ptr (some child))
  pure (.finished (.next (requestEnvironment frame child)))

def handoffOperations (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (bindingWidth : Nat) : CProg CVal ReadBlock.Result := do
  CProg.store (parent + 2) (.ptr (some child))
  CProg.store (parent + 3) (.ptr answer)
  CProg.copyCells bindingSource (parent + 5) bindingWidth
  CProg.store (parent + 4) (.u32 step)
  pure (.finished (.next (handoffEnvironment parent child answer step)))

def consumeOperations (frame answer environment : Ptr) (empty : List CVal) :
    CProg CVal ReadBlock.Result := do
  let value ← CProg.loadPtr (frame + 3)
  CProg.store answer (.ptr value)
  CProg.copyCells (frame + 5) environment empty.length
  CProg.initializeCells (frame + 5) empty
  CProg.store (frame + 3) (.ptr none)
  CProg.store (frame + 2) (.ptr none)
  pure (.finished (.next (consumeEnvironment frame answer environment)))

theorem request_uses_memory (frame child : Ptr) :
    requestProgram frame child = requestOperations frame child := by
  simp [requestProgram, requestBody, ident, field, requestEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.valueKind, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, requestOperations]

theorem handoff_uses_memory (parent child bindingSource : Ptr) (answer : Option Ptr)
    (step : UInt32) (width : Nat) :
    handoffProgram parent child bindingSource answer step width =
      handoffOperations parent child bindingSource answer step width := by
  simp [handoffProgram, handoffBody, ident, field, handoffEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, handoffAssignment, StatementBlock.fieldAssignment,
    ReadExpressions.expression, ReadExpressions.expressionWith,
    ReadExpressions.expressionWithNames,
    ReadExpressions.storeField, ReadExpressions.pointer, ReadExpressions.resolved,
    ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.valueKind, Prog.bind_eq, Prog.pure_eq, Prog.ret_bind,
    Prog.bind_assoc, handoffOperations]

theorem consume_uses_memory (frame answer environment : Ptr) (empty : List CVal) :
    consumeProgram frame answer environment empty =
      consumeOperations frame answer environment empty := by
  simp [consumeProgram, consumeBody, ident, field, consumeEnvironment,
    StatementBlock.executeWith, StatementBlock.executeScopedWith,
    StatementBlock.Services.scoped, consumeAssignment, bindingInitializer,
    StatementBlock.fieldAssignment, ReadExpressions.expression,
    ReadExpressions.expressionWith, ReadExpressions.expressionWithNames,
    ReadExpressions.field, ReadExpressions.storeField, ReadExpressions.pointer,
    ReadExpressions.resolved, ReadExpressions.fieldAddress, pullLayout,
    ReadExpressions.ObjectReads.fieldLayout, ReadExpressions.valueKind,
    Prog.bind_eq, Prog.pure_eq, Prog.ret_bind, Prog.bind_assoc, consumeOperations]

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem request_owned (frame child : Ptr) (prior : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + 1) (.ptr prior) ∗ rest) (requestProgram frame child)
      (fun result heap => result = .finished (.next (requestEnvironment frame child)) ∧
        (PointsTo (frame + 1) (.ptr (some child)) ∗ rest) heap) := by
  rw [request_uses_memory]
  cmem_start heap held
  unfold requestOperations
  cmem_vcgen
  cmem_exact

theorem handoff_owned (parent child bindingSource : Ptr) (answer oldChild oldAnswer : Option Ptr)
    (step oldStep : UInt32) (bindings : List CVal) (old : List (Option CVal))
    (width : old.length = bindings.length) (rest : Heap L → Prop) :
    CTriple (PointsTo (parent + 2) (.ptr oldChild) ∗
      PointsTo (parent + 3) (.ptr oldAnswer) ∗ PointsTo (parent + 4) (.u32 oldStep) ∗
      Cells bindingSource (bindings.map some) ∗ Cells (parent + 5) old ∗ rest)
      (handoffProgram parent child bindingSource answer step bindings.length)
      (fun result heap => result = .finished (.next (handoffEnvironment parent child answer step)) ∧
        (PointsTo (parent + 2) (.ptr (some child)) ∗
          PointsTo (parent + 3) (.ptr answer) ∗ PointsTo (parent + 4) (.u32 step) ∗
          Cells bindingSource (bindings.map some) ∗
          Cells (parent + 5) (bindings.map some) ∗ rest) heap) := by
  rw [handoff_uses_memory]
  cmem_start heap held
  unfold handoffOperations
  cmem_vcgen
  cmem_call copy_cells bindingSource (parent + 5) old bindings width
  rintro _ heap copied
  cmem_vcgen
  cmem_exact

theorem consume_owned (frame answer environment : Ptr) (value child oldAnswer : Option Ptr)
    (bindings empty : List CVal) (old : List (Option CVal))
    (width : empty.length = bindings.length) (destinationWidth : old.length = bindings.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo (frame + 3) (.ptr value) ∗ PointsTo (frame + 2) (.ptr child) ∗
      PointsTo answer (.ptr oldAnswer) ∗ Cells (frame + 5) (bindings.map some) ∗
      Cells environment old ∗ rest) (consumeProgram frame answer environment empty)
      (fun result heap => result = .finished (.next (consumeEnvironment frame answer environment)) ∧
        (PointsTo (frame + 3) (.ptr none) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo answer (.ptr value) ∗ Cells (frame + 5) (empty.map some) ∗
          Cells environment (bindings.map some) ∗ rest) heap) := by
  rw [consume_uses_memory]
  cmem_start heap held
  unfold consumeOperations
  simp only [CProg.loadPtr, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  rw [width]
  cmem_call copy_cells (frame + 5) environment old bindings destinationWidth
  rintro _ heap copied
  cmem_call initialize_cells (frame + 5) (bindings.map some) empty
    (by simpa using width.symm)
  rintro _ heap initialized
  cmem_vcgen
  cmem_exact

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativePull

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativePull

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

/-- The actual public status tags. A private child request shares the suspended
status tag but is distinguished by the native `requested` field. -/
inductive StepTag where
  | answer | exhausted | declined | invalidated | stack | capacity | hostError | suspended
  deriving DecidableEq, Repr

def StepTag.encode : StepTag → UInt32
  | .answer => 0 | .exhausted => 1 | .declined => 2 | .invalidated => 3
  | .stack => 4 | .capacity => 5 | .hostError => 6 | .suspended => 7

def StepTag.decode : UInt32 → Option StepTag
  | 0 => some .answer | 1 => some .exhausted | 2 => some .declined
  | 3 => some .invalidated | 4 => some .stack | 5 => some .capacity
  | 6 => some .hostError | 7 => some .suspended | _ => none

theorem StepTag.decode_encode (tag : StepTag) : StepTag.decode tag.encode = some tag := by
  cases tag <;> decide +kernel

structure Reply where
  step : UInt32
  requested : Bool
  deriving DecidableEq, Repr

/-- The selected valid-parent branch of `petta_machine_pull_child`. The parsed
transfer and request blocks are used verbatim. Initial invalid pointer checks,
C byte layout and the allocator's object identities remain admission boundaries.
The equality test here is object identity, not equality of child results. -/
def pull (frame child answer environment : Ptr) (empty : List CVal) : CProg CVal Reply := do
  CProg.store answer (.ptr none)
  let completed ← CProg.loadPtr (frame + 2)
  match completed with
  | none =>
      let _ ← requestProgram frame child
      pure ⟨7, true⟩
  | some completed =>
      if completed = child then
        let _ ← consumeProgram frame answer environment empty
        let step ← CProg.loadU32 (frame + 4)
        pure ⟨step, false⟩
      else
        CProg.initializeCells environment empty
        pure ⟨5, false⟩

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem pull_requested (frame child answer environment : Ptr) (empty : List CVal)
    (oldAnswer oldRequest : Option Ptr) (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr none) ∗
      PointsTo (frame + 1) (.ptr oldRequest) ∗ rest)
      (pull frame child answer environment empty)
      (fun result heap => result = ⟨7, true⟩ ∧
        (PointsTo answer (.ptr none) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo (frame + 1) (.ptr (some child)) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  rw [request_uses_memory]
  unfold requestOperations
  cmem_vcgen
  cmem_exact

theorem pull_completed (frame child answer environment : Ptr) (value oldAnswer : Option Ptr)
    (step : UInt32) (bindings empty : List CVal) (old : List (Option CVal))
    (width : empty.length = bindings.length) (destinationWidth : old.length = bindings.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr (some child)) ∗
      PointsTo (frame + 3) (.ptr value) ∗ PointsTo (frame + 4) (.u32 step) ∗
      Cells (frame + 5) (bindings.map some) ∗ Cells environment old ∗ rest)
      (pull frame child answer environment empty)
      (fun result heap => result = ⟨step, false⟩ ∧
        (PointsTo answer (.ptr value) ∗ PointsTo (frame + 2) (.ptr none) ∗
          PointsTo (frame + 3) (.ptr none) ∗ PointsTo (frame + 4) (.u32 step) ∗
          Cells (frame + 5) (empty.map some) ∗
          Cells environment (bindings.map some) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  cmem_vcgen
  cmem_call consume_owned frame answer environment value (some child) none
    bindings empty old width destinationWidth (PointsTo (frame + 4) (.u32 step) ∗ rest)
  rintro _ heap ⟨rfl, copied⟩
  cmem_vcgen
  cmem_exact

theorem pull_wrong_child (frame expected actual answer environment : Ptr)
    (different : actual ≠ expected) (empty : List CVal) (oldAnswer : Option Ptr)
    (old : List (Option CVal)) (width : old.length = empty.length)
    (rest : Heap L → Prop) :
    CTriple (PointsTo answer (.ptr oldAnswer) ∗ PointsTo (frame + 2) (.ptr (some actual)) ∗
      Cells environment old ∗ rest)
      (pull frame expected answer environment empty)
      (fun result heap => result = ⟨5, false⟩ ∧
        (PointsTo answer (.ptr none) ∗ PointsTo (frame + 2) (.ptr (some actual)) ∗
          Cells environment (empty.map some) ∗ rest) heap) := by
  cmem_start heap held
  unfold pull
  cmem_vcgen
  simp only [if_neg different]
  cmem_call initialize_cells environment old empty width
  rintro _ heap cleared
  cmem_exact

/-! Executable controls use the existing finite-storage primitive interpreter.
The extra cell represents already performed shared work; transfer does not undo
or repeat it. The child evaluator remains a separate source obligation. -/
namespace Controls
open ExecutableStorage
open Mettapedia.GSLT.Distinction.ProductiveBlocks

def frame : Ptr := ⟨1, 0⟩
def child : Ptr := ⟨2, 0⟩
def answer : Ptr := ⟨3, 0⟩
def environment : Ptr := ⟨4, 0⟩
def value : Ptr := ⟨5, 0⟩
def world : Ptr := ⟨6, 0⟩
def empty : List CVal := [.ptr none, .u32 0, .ptr none]
def bindings : List CVal := [.ptr (some ⟨7, 0⟩), .u32 2, .ptr (some ⟨8, 0⟩)]

def saved (tag : StepTag := .answer) : Storage CVal :=
  [(1, ⟨true, ([(CVal.ptr (some ⟨9, 0⟩)), .ptr none, .ptr (some child),
      .ptr (if tag = .answer then some value else none), .u32 tag.encode] ++
        (if tag = .answer then bindings else empty)).map some⟩),
   (2, ⟨true, [some (.u32 1)]⟩), (3, ⟨true, [some (.ptr none)]⟩),
   (4, ⟨true, empty.map some⟩), (5, ⟨true, [some (.u32 42)]⟩),
   (6, ⟨true, [some (.u32 1)]⟩)]

def completed? (fuel : Nat) (program : CProg CVal Reply) (storage : Storage CVal) :
    Option (Reply × Storage CVal) :=
  match (ProductiveBlocks.machine.run fuel ⟨program, storage, []⟩).2 with
  | .finished (.returned result) => some (result.answer, result.storage)
  | _ => none

def observation (result : Option (Reply × Storage CVal)) :
    Option (Reply × Option CVal × Option CVal × List (Option CVal) × Option CVal) := do
  let (reply, store) ← result
  pure (reply, load store answer, load store (frame + 2),
    (List.range 3).map (fun index => load store (environment + index)), load store world)

theorem completed_row_preserves_bindings_and_world :
    observation (completed? 40 (pull frame child answer environment empty) saved) =
      some (⟨0, false⟩, some (.ptr (some value)), some (.ptr none),
        bindings.map some, some (.u32 1)) := by rfl

theorem completed_pause_is_not_a_private_request :
    observation (completed? 40 (pull frame child answer environment empty) (saved .suspended)) =
      some (⟨7, false⟩, some (.ptr none), some (.ptr none),
        empty.map some, some (.u32 1)) := by rfl

theorem wrong_child_does_not_consume :
    observation (completed? 40 (pull frame ⟨20, 0⟩ answer environment empty) saved) =
      some (⟨5, false⟩, some (.ptr none), some (.ptr (some child)),
        empty.map some, some (.u32 1)) := by rfl

def twice : CProg CVal Reply := do
  let _ ← pull frame child answer environment empty
  pull frame child answer environment empty

theorem consumed_row_cannot_replay :
    observation (completed? 80 twice saved) =
      some (⟨7, true⟩, some (.ptr none), some (.ptr none),
        bindings.map some, some (.u32 1)) := by rfl

theorem unfinished_transfer_is_pending :
    match (ProductiveBlocks.machine.run 3
        ⟨pull frame child answer environment empty, saved, []⟩).2 with
    | .exhausted _ => True
    | _ => False := by trivial

/-- Arbitrary scheduler cuts retain the unfinished primitive program and exact
chronological receipts. Resumption does not invoke a child producer. -/
theorem resume_transfer (first second : Nat) (initial savedState :
    ProductiveBlocks.State CVal Reply) (receipts : List (ProductiveBlocks.Receipt CVal))
    (paused : ProductiveBlocks.machine.run first initial = (receipts, .exhausted savedState)) :
    ProductiveBlocks.machine.run (first + second) initial =
      (receipts ++ (ProductiveBlocks.machine.run second savedState).1,
        (ProductiveBlocks.machine.run second savedState).2) :=
  ProductiveBlocks.resume_after_prefix first second initial savedState receipts paused

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativePull

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- Logical cell offsets for the selected PettaGoal fields. The opaque suffix
contains every remaining plan, scope, activation and control field. Native byte
layout is an explicit representation boundary, not this cell enumeration. -/
structure Row where
  kind : UInt32
  barrier : UInt32
  instanceId : UInt64
  first : Option Ptr
  second : Option Ptr
  third : Option Ptr
  fourth : Option Ptr
  suffix : List CVal
  deriving Repr, DecidableEq

def Row.cells (row : Row) : List CVal :=
  [.u32 row.kind, .u32 row.barrier, .u64 row.instanceId,
    .ptr row.first, .ptr row.second, .ptr row.third, .ptr row.fourth] ++ row.suffix

/-- Source-facing requests retain their destination. They are not complete
source evaluations, and no eager or relational policy is selected here. -/
inductive Request where
  | solve (expression destination : Atom)
  | unify (left right : Atom)
  | callReady (invocation destination : Atom)
  | argumentReturn (value destination : Atom) (returnHeight : UInt64)
  deriving DecidableEq, Repr

/-- The actual enum tags read from petta_search_machine.c. An unsupported kind
is refused by this component rather than interpreted as a solver step. -/
def Row.request (atoms : Ptr → Option Atom) (row : Row) : Option Request := do
  let first ← row.first >>= atoms
  let second ← row.second >>= atoms
  if row.kind = 0 then some (.solve first second)
  else if row.kind = 4 then some (.callReady first second)
  else if row.kind = 25 then some (.unify first second)
  else if row.kind = 23 then
    match (row.suffix[6]? : Option CVal) with
    | some (CVal.u64 height) => some (.argumentReturn first second height)
    | _ => none
  else none

structure Occurrence where
  identity : UInt64
  barrier : UInt32
  request : Request
  deriving DecidableEq, Repr

def Row.observe (atoms : Ptr → Option Atom) (row : Row) : Option Occurrence := do
  pure ⟨row.instanceId, row.barrier, ← row.request atoms⟩

/-- The native array's live prefix is bottom-to-top; the source continuation
front is its reverse. Rows outside the live prefix remain protected by the
choice/overwrite trail, a separate part of the machine representation. -/
def readback (atoms : Ptr → Option Atom) (active : List Row) : Option (List Occurrence) :=
  active.reverse.mapM (Row.observe atoms)

theorem readback_push (atoms : Ptr → Option Atom) (active : List Row) (row : Row) :
    readback atoms (active ++ [row]) = (do
      let nextOccurrence ← row.observe atoms
      let older ← readback atoms active
      pure (nextOccurrence :: older)) := by
  simp [readback, List.reverse_append]

theorem readback_push_iff (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (nextOccurrence : Occurrence) (older : List Occurrence) :
    row.observe atoms = some nextOccurrence →
    (readback atoms (active ++ [row]) = some (nextOccurrence :: older) ↔ readback atoms active = some older) := by
  intro selected
  rw [readback_push, selected]
  cases readback atoms active <;> simp

/-- The aggregate-copy portion of the admitted native push: reserve, protected
slot logging and epoch retention have already succeeded. The store increments
the live length before copying, exactly as the C post-increment does. -/
def push (length source base : Ptr) (width : Nat) : CProg CVal Unit := do
  let index ← CProg.loadU64 length
  CProg.store length (.u64 (index + 1))
  CProg.copyCells source (base + index.toNat * width) width

/-- The scheduler removes a live top row before dispatch. An empty live prefix
is not read; the native scheduler treats it as completion before this block. -/
def pop (length base : Ptr) (width : Nat) : CProg CVal (List CVal) := do
  let index ← CProg.loadU64 length
  if index = 0 then CProg.undefined else do
    let prior := index - 1
    CProg.store length (.u64 prior)
    CProg.loadCells (base + prior.toNat * width) width

universe u
variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

theorem push_preserves_older (length source base : Ptr) (index : UInt64)
    (priorCells row : List CVal) (old : List (Option CVal))
    (position : index.toNat * row.length = priorCells.length)
    (width : old.length = row.length) (rest : Heap L → Prop) :
    CTriple (PointsTo length (.u64 index) ∗ Cells source (row.map some) ∗
      Cells base (priorCells.map some ++ old) ∗ rest)
      (push length source base row.length)
      (fun _ => PointsTo length (.u64 (index + 1)) ∗ Cells source (row.map some) ∗
        Cells base ((priorCells ++ row).map some) ∗ rest) := by
  cmem_start heap held
  simp only [cells_append, List.length_map] at held
  unfold push
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  rw [position]
  cmem_call copy_cells source (base + priorCells.length) old row width
  rintro _ heap copied
  simp only [List.map_append, cells_append, List.length_map]
  cmem_exact

theorem pop_preserves_older (length base : Ptr) (index : UInt64)
    (nonempty : index ≠ 0) (priorCells row : List CVal)
    (position : (index - 1).toNat * row.length = priorCells.length) (rest : Heap L → Prop) :
    CTriple (PointsTo length (.u64 index) ∗ Cells base ((priorCells ++ row).map some) ∗ rest)
      (pop length base row.length)
      (fun result heap => result = row ∧
        (PointsTo length (.u64 (index - 1)) ∗
          Cells base ((priorCells ++ row).map some) ∗ rest) heap) := by
  cmem_start heap held
  simp only [List.map_append, cells_append, List.length_map] at held
  unfold pop
  simp only [CProg.loadU64, Prog.bind_eq, Prog.bind_assoc]
  cmem_vcgen
  simp only [if_neg nonempty]
  cmem_vcgen
  rw [position]
  cmem_call load_cells (base + priorCells.length) row
  rintro _ heap ⟨rfl, loaded⟩
  simp only [List.map_append, cells_append, List.length_map]
  exact ⟨trivial, by cmem_exact⟩

/-- The two independently written boundaries compose: actual aggregate push
preserves the physical prefix, and the source-facing readback adds exactly one
occurrence with its original destination and barrier. -/
theorem pushed_occurrence_readback (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (occurrence : Occurrence) (older : List Occurrence)
    (selected : row.observe atoms = some occurrence) (prior : readback atoms active = some older) :
    readback atoms (active ++ [row]) = some (occurrence :: older) := by
  exact (readback_push_iff atoms active row occurrence older selected).mpr prior

/-! Source-independent scheduling data from the actual admitted control branch.
The branch policy is explicit. Execution of these destination-bearing requests
requires the relational source service; it is not identified with eager DFS. -/
inductive BindingPolicy where
  | eagerValue | relationalLeft | relationalRight
  deriving DecidableEq, Repr

/-- Authored local schedules retain the intermediate destination and final
body destination. This is an admission judgment for control construction. -/
inductive LetSchedule : BindingPolicy → Atom → Atom → Atom → Atom → Atom → List Request → Prop where
  | eager (pattern producer body output hole : Atom) :
      LetSchedule .eagerValue pattern producer body output hole
        [.solve producer hole, .unify pattern hole, .solve body output]
  | relationalLeft (pattern producer body output hole : Atom) :
      LetSchedule .relationalLeft pattern producer body output hole
        [.solve pattern hole, .solve producer hole, .solve body output]
  | relationalRight (pattern producer body output hole : Atom) :
      LetSchedule .relationalRight pattern producer body output hole
        [.solve producer hole, .solve pattern hole, .solve body output]

/-- This is the actual order of pushes in each selected C branch. It is
independent of the source judgment and of the array readback. -/
def letPushes (policy : BindingPolicy) (pattern producer body output hole : Atom) : List Request :=
  match policy with
  | .eagerValue => [.solve body output, .unify pattern hole, .solve producer hole]
  | .relationalLeft => [.solve body output, .solve producer hole, .solve pattern hole]
  | .relationalRight => [.solve body output, .solve pattern hole, .solve producer hole]

theorem let_schedule_iff (policy : BindingPolicy) (pattern producer body output hole : Atom)
    (requests : List Request) :
    LetSchedule policy pattern producer body output hole requests ↔
      (letPushes policy pattern producer body output hole).reverse = requests := by
  constructor
  · intro source
    cases source <;> rfl
  · intro selected
    subst requests
    cases policy
    · exact .eager _ _ _ _ _
    · exact .relationalLeft _ _ _ _ _
    · exact .relationalRight _ _ _ _ _

/-- The existing scalar source has precisely the eager producer-first entry.
This theorem does not turn a relational scheduling witness into that entry. -/
theorem eager_source_entry (program : SpaceSemantics.Program) (world : EagerDFS.World)
    (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
    (pattern producer body : Atom) (older : List EagerDFS.Frame) :
    EagerDFS.LocalTransition program world
      ⟨.evaluate bindings (.expression [.symbol "let", pattern, producer, body]), older⟩ world
      (.next ⟨.evaluate bindings producer, .bind bindings pattern body :: older⟩) :=
  .let_enter

/-- Actual argument rows retain the producer syntax, its fresh result slot,
the native evaluation flag and the error-control test. The latter decides
whether a return-height guard is pushed; it never changes the producer order. -/
structure Argument where
  expression : Atom
  destination : Atom
  evaluate : Bool
  knownError : Bool
  deriving DecidableEq, Repr

def argumentRowPushes (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (argument : Argument) : List Request :=
  (if eagerFaults && (argument.evaluate || argument.knownError) then
    [.argumentReturn argument.destination output height] else []) ++
  (if argument.evaluate then [.solve argument.expression argument.destination] else [])

/-- Direct translation of the native descending index loop, following the
already-pushed final call/data/unification row. -/
def argumentPushes (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) : List Request :=
  arguments.reverse.flatMap (argumentRowPushes eagerFaults output height)

def argumentExecution (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) : List Request :=
  arguments.flatMap fun argument =>
    (if argument.evaluate then [.solve argument.expression argument.destination] else []) ++
    (if eagerFaults && (argument.evaluate || argument.knownError) then
      [.argumentReturn argument.destination output height] else [])

/-- Reversing the actual goal-array pushes gives left-to-right producer
execution, with each enabled fault guard immediately after its producer.
Every guard retains the same older-frame boundary, rather than an inferred
boundary based on the current number of answers. -/
theorem argument_order (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    (argumentPushes eagerFaults output height arguments).reverse =
      argumentExecution eagerFaults output height arguments := by
  induction arguments with
  | nil => simp [argumentPushes, argumentExecution]
  | cons argument arguments ih =>
      simp only [argumentPushes, List.reverse_cons, List.flatMap_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, List.reverse_append,
        argumentExecution, List.flatMap_cons]
      rw [show (List.flatMap (argumentRowPushes eagerFaults output height) arguments.reverse).reverse =
        argumentExecution eagerFaults output height arguments from ih]
      simp only [argumentRowPushes, List.reverse_append]
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;> rfl

namespace Controls

def atoms : Ptr → Option Atom := fun pointer => some (.symbol (toString pointer.block))
def row (identity : UInt64) (tag : UInt32 := 0) : Row :=
  ⟨tag, 17, identity, some ⟨1, 0⟩, some ⟨2, 0⟩, none, none, [.bool false]⟩

theorem two_equal_payloads_keep_occurrences :
    readback atoms [row 10, row 11] = some
      [⟨11, 17, .solve (.symbol "1") (.symbol "2")⟩,
       ⟨10, 17, .solve (.symbol "1") (.symbol "2")⟩] := by decide +kernel

theorem unsupported_tag_not_a_solve : (row 10 77).request atoms = none := by decide +kernel

theorem eager_and_relational_keep_different_requests :
    letPushes .eagerValue (.symbol "A") (.symbol "effect") (.symbol "C") (.var "out") (.var "join") ≠
    letPushes .relationalLeft (.symbol "A") (.symbol "effect") (.symbol "C") (.var "out") (.var "join") := by
  decide +kernel


theorem call_ready_keeps_original_destination :
    (row 21 4).observe atoms = some
      ⟨21, 17, .callReady (.symbol "1") (.symbol "2")⟩ := by decide +kernel

theorem argument_return_requires_saved_height :
    (row 22 23).request atoms = none := by decide +kernel

theorem argument_return_retains_height :
    ({ row 22 23 with suffix := List.replicate 6 (CVal.ptr none) ++ [CVal.u64 5] }).request atoms =
      some (.argumentReturn (.symbol "1") (.symbol "2") 5) := by decide +kernel

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

open Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
open Mettapedia.Machines.CMemory
open Mettapedia.GSLT.Logic.AbstractSeparationLogic

private def id (name : String) : CExpr := .identifier name.toList
private def sourceElement (index : CExpr) : CExpr :=
  .index (.field (.field (id "expression") "expr".toList true) "elems".toList false) index
private def barrier : CExpr := .field (id "goal") "barrier".toList true
private def planChild (index : CExpr) : CExpr :=
  .call "petta_plan_child".toList [id "plan", index]

def solveCall (index destination : CExpr) : CExpr :=
  .call "petta_push_solve_planned".toList
    [id "machine", sourceElement (match index with | .unsignedInteger n => .decimal n | other => other), destination, barrier, planChild index]

def unifyCall : CExpr :=
  .call "petta_push_unify".toList
    [id "machine", sourceElement (id "binder_index"), id "value", barrier]

def eagerFailure : CExpr := .binary .or
  (.binary .or (.binary .or (.unary .not (id "value"))
    (.unary .not (solveCall (.unsignedInteger 3) (id "expected"))))
    (.unary .not unifyCall))
  (.unary .not (solveCall (id "source_index") (id "value")))

def relationalLeftFailure : CExpr := .binary .or
  (.unary .not (solveCall (.unsignedInteger 2) (id "joined")))
  (.unary .not (solveCall (.unsignedInteger 1) (id "joined")))

def relationalRightFailure : CExpr := .binary .or
  (.unary .not (solveCall (.unsignedInteger 1) (id "joined")))
  (.unary .not (solveCall (.unsignedInteger 2) (id "joined")))

def eagerFailureSource : String := "!value || !petta_push_solve_planned(machine, expression->expr.elems[3], expected, goal->barrier, petta_plan_child(plan, 3u)) || !petta_push_unify(machine, expression->expr.elems[binder_index], value, goal->barrier) || !petta_push_solve_planned(machine, expression->expr.elems[source_index], value, goal->barrier, petta_plan_child(plan, source_index))"
def eagerFailureTokens : List Token := [.punctuation "!".toList, .identifier "value".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "3".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "expected".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "3u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_unify".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .identifier "binder_index".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "value".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .identifier "source_index".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "value".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .identifier "source_index".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem eagerFailure_lex : lex eagerFailureSource.toList = .ok eagerFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem eagerFailure_parsed : expressionText? [] eagerFailureSource.toList = some eagerFailure := by
  unfold expressionText?
  rw [eagerFailure_lex]
  rfl

def relationalLeftFailureSource : String := "!petta_push_solve_planned(machine, expression->expr.elems[2], joined, goal->barrier, petta_plan_child(plan, 2u)) || !petta_push_solve_planned(machine, expression->expr.elems[1], joined, goal->barrier, petta_plan_child(plan, 1u))"
def relationalLeftFailureTokens : List Token := [.punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "2".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "2u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "1".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem relationalLeftFailure_lex : lex relationalLeftFailureSource.toList = .ok relationalLeftFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem relationalLeftFailure_parsed : expressionText? [] relationalLeftFailureSource.toList = some relationalLeftFailure := by
  unfold expressionText?
  rw [relationalLeftFailure_lex]
  rfl

def relationalRightFailureSource : String := "!petta_push_solve_planned(machine, expression->expr.elems[1], joined, goal->barrier, petta_plan_child(plan, 1u)) || !petta_push_solve_planned(machine, expression->expr.elems[2], joined, goal->barrier, petta_plan_child(plan, 2u))"
def relationalRightFailureTokens : List Token := [.punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "1".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "1u".toList, .punctuation ")".toList, .punctuation ")".toList, .punctuation "||".toList, .punctuation "!".toList, .identifier "petta_push_solve_planned".toList, .punctuation "(".toList, .identifier "machine".toList, .punctuation ",".toList, .identifier "expression".toList, .punctuation "->".toList, .identifier "expr".toList, .punctuation ".".toList, .identifier "elems".toList, .punctuation "[".toList, .number "2".toList, .punctuation "]".toList, .punctuation ",".toList, .identifier "joined".toList, .punctuation ",".toList, .identifier "goal".toList, .punctuation "->".toList, .identifier "barrier".toList, .punctuation ",".toList, .identifier "petta_plan_child".toList, .punctuation "(".toList, .identifier "plan".toList, .punctuation ",".toList, .number "2u".toList, .punctuation ")".toList, .punctuation ")".toList]
theorem relationalRightFailure_lex : lex relationalRightFailureSource.toList = .ok relationalRightFailureTokens := by
  apply lex_of_completed
  decide +kernel
theorem relationalRightFailure_parsed : expressionText? [] relationalRightFailureSource.toList = some relationalRightFailure := by
  unfold expressionText?
  rw [relationalRightFailure_lex]
  rfl


structure PushOperands where
  kind : UInt32
  expression : CExpr
  destination : CExpr
  barrier : CExpr
  plan : Option CExpr
  deriving Repr

/-- Extract only the two admitted native helper calls. The machine receiver,
arity and full operand syntax are checked. Execution remains the C call service. -/
def pushOperands? : CExpr → Option PushOperands
  | .call name [.identifier machine, expression, destination, barrier, plan] =>
      if name = "petta_push_solve_planned".toList ∧ machine = "machine".toList then
        some ⟨0, expression, destination, barrier, some plan⟩
      else none
  | .call name [.identifier machine, expression, destination, barrier] =>
      if name = "petta_push_unify".toList ∧ machine = "machine".toList then
        some ⟨25, expression, destination, barrier, none⟩
      else none
  | _ => none

/-- Potential calls are listed in their C short-circuit order. The pointer
allocation guard contributes no call. A failed prefix does not execute the
remaining list; that execution fact is proved below using the C interpreter. -/
def constructionCalls? : CExpr → Option (List PushOperands)
  | .binary .or left right => do
      pure ((← constructionCalls? left) ++ (← constructionCalls? right))
  | .unary .not (.identifier name) =>
      if name = "value".toList then some [] else none
  | .unary .not call => (pushOperands? call).map List.singleton
  | _ => none

theorem eager_call_operands : constructionCalls? eagerFailure = some
    [⟨0, sourceElement (.decimal 3), id "expected", barrier,
       some (planChild (.unsignedInteger 3))⟩,
     ⟨25, sourceElement (id "binder_index"), id "value", barrier, none⟩,
     ⟨0, sourceElement (id "source_index"), id "value", barrier,
       some (planChild (id "source_index"))⟩] := by rfl

theorem relational_left_call_operands : constructionCalls? relationalLeftFailure = some
    [⟨0, sourceElement (.decimal 2), id "joined", barrier,
       some (planChild (.unsignedInteger 2))⟩,
     ⟨0, sourceElement (.decimal 1), id "joined", barrier,
       some (planChild (.unsignedInteger 1))⟩] := by rfl

theorem relational_right_call_operands : constructionCalls? relationalRightFailure = some
    [⟨0, sourceElement (.decimal 1), id "joined", barrier,
       some (planChild (.unsignedInteger 1))⟩,
     ⟨0, sourceElement (.decimal 2), id "joined", barrier,
       some (planChild (.unsignedInteger 2))⟩] := by rfl

/-- Negation and short-circuiting retain the actual physical CProg effects. -/
def failureOf (operation : CProg CVal CVal) : CProg CVal CVal := do
  let value ← operation
  let succeeded ← ReadExpressions.truth value
  pure (.bool (!succeeded))

def eitherFailure (left right : CProg CVal CVal) : CProg CVal CVal := do
  let value ← left
  let failed ← ReadExpressions.truth value
  if failed then pure (.bool true) else do
    let value ← right
    let failed ← ReadExpressions.truth value
    pure (.bool failed)

theorem relational_left_executes_actual_calls (names : ReadExpressions.NameReads)
    (calls : ReadExpressions.Calls) (layout : ReadExpressions.Layout)
    (objects : ReadExpressions.ObjectReads := {}) :
    ReadExpressions.expressionWithNames names calls layout relationalLeftFailure objects =
      eitherFailure
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 2) (id "joined")) objects))
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 1) (id "joined")) objects)) := by rfl

theorem relational_right_executes_actual_calls (names : ReadExpressions.NameReads)
    (calls : ReadExpressions.Calls) (layout : ReadExpressions.Layout)
    (objects : ReadExpressions.ObjectReads := {}) :
    ReadExpressions.expressionWithNames names calls layout relationalRightFailure objects =
      eitherFailure
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 1) (id "joined")) objects))
        (failureOf (ReadExpressions.expressionWithNames names calls layout
          (solveCall (.unsignedInteger 2) (id "joined")) objects)) := by rfl

theorem successful_pushes_keep_order (first second : CProg CVal Unit) :
    eitherFailure
      (failureOf (first >>= fun _ => pure (.bool true)))
      (failureOf (second >>= fun _ => pure (.bool true))) =
      (first >>= fun _ => second >>= fun _ => pure (.bool false)) := by
  simp [eitherFailure, failureOf, ReadExpressions.truth,
    Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]

theorem failed_push_keeps_prefix (first : CProg CVal Unit) (second : CProg CVal CVal) :
    eitherFailure (failureOf (first >>= fun _ => pure (.bool false))) second =
      (first >>= fun _ => pure (.bool true)) := by
  simp [eitherFailure, failureOf, ReadExpressions.truth,
    Prog.bind_eq, Prog.pure_eq, Prog.bind_assoc, Prog.ret_bind]

/-- Once the body has been pushed, the admitted relational-left C branch
executes producer-push before binder-push. The reverse live-array readback
therefore places the binder first, retaining their one shared destination. -/
theorem relational_left_physical_sequence (body producer binder : CProg CVal Unit) :
    (do body
        eitherFailure (failureOf (producer >>= fun _ => pure (.bool true)))
          (failureOf (binder >>= fun _ => pure (.bool true)))) =
      (body >>= fun _ => producer >>= fun _ => binder >>= fun _ => pure (.bool false)) := by
  rw [successful_pushes_keep_order]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

open Mettapedia.Machines.CMemory
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

/-- Understood native phases enter the independently stated destination
component. An argument return retains its saved continuation delimiter; the
source step separately validates that the designated caller suffix exists. -/
def Request.goal : Request → Option Goal
  | .solve expression destination => some (.evaluate expression destination)
  | .unify value destination => some (.equate value destination)
  | .callReady (.expression (.symbol head :: arguments)) destination =>
      some (.invoke head arguments destination)
  | .argumentReturn value destination height =>
      some (.argumentReturn value destination height.toNat)
  | .callReady _ _ => none

def sourceGoals (occurrences : List Occurrence) : Option (List Goal) :=
  occurrences.mapM (fun occurrence => occurrence.request.goal)

def rowsToGoals (atoms : Ptr → Option Atom) (active : List Row) : Option (List Goal) := do
  sourceGoals (← readback atoms active)

theorem rowsToGoals_push (atoms : Ptr → Option Atom) (active : List Row) (row : Row)
    (occurrence : Occurrence) (goal : Goal)
    (decoded : row.observe atoms = some occurrence) (understood : occurrence.request.goal = some goal) :
    rowsToGoals atoms (active ++ [row]) = (goal :: ·) <$> rowsToGoals atoms active := by
  simp only [rowsToGoals, readback_push, decoded]
  cases old : readback atoms active with
  | none => rfl
  | some occurrences =>
      cases pending : sourceGoals occurrences <;> simp_all [sourceGoals]

/-- The raw native checkpoint retains the complete binding record, all goal
fields, occurrence identities and enclosing scope state. A supplied scalar/
atom representation reads values; it is not a native-unifier adequacy premise. -/
structure Saved (Context : Type) where
  bindings : List CVal
  active : List Row
  output : Ptr
  world : EagerDFS.World
  enclosing : Context
  reserved : Finset String := ∅
  /-- Logical delimiter carried by this view. Decoding the native choice
  boundary is an independent representation obligation. -/
  cutBoundary : Nat := 0

/-- The binding reader must account for the actual current-value authority of
SearchContext (including contextual frame slots), not reinterpret historical
Binding entries as simultaneous assignments. Its correctness is a separate
representation obligation. These control squares do not assume it. -/
def Saved.readback {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context) :
    Option (Cursor Context) := do
  let bindings ← readBindings saved.bindings
  let goals ← rowsToGoals atoms saved.active
  let destination ← atoms saved.output
  pure ⟨saved.world, ⟨bindings, goals, destination, saved.reserved,saved.cutBoundary⟩,
    saved.enclosing⟩

/-- The admitted native view makes the finite structural boundary testable.
A missing atom/phase/binding representation or an unsupported scalar retains
the native checkpoint; it does not authorize a source completion. -/
def Saved.readbackFinite {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context) :
    Option (Cursor Context) := do
  let cursor ← saved.readback atoms readBindings
  if cursor.control.finiteStructural then some cursor else none

theorem readbackFinite_iff {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context)
    (cursor : Cursor Context) :
    saved.readbackFinite atoms readBindings = some cursor ↔
      saved.readback atoms readBindings = some cursor ∧
        FiniteStructuralAdmission cursor.control := by
  simp only [Saved.readbackFinite, FiniteStructuralAdmission]
  cases read : saved.readback atoms readBindings with
  | none => simp
  | some actual =>
      change (if actual.control.finiteStructural then some actual else none) = some cursor ↔
        some actual = some cursor ∧ cursor.control.finiteStructural = true
      split <;> simp_all
      all_goals
        intro same
        cases same
        assumption

/-- Adding a goal changes only the continuation. The reached binding record,
world, original destination and older scope are read from the same checkpoint. -/
theorem saved_push_readback {Context : Type} (atoms : Ptr → Option Atom)
    (readBindings : List CVal → Option Equations) (saved : Saved Context)
    (row : Row) (occurrence : Occurrence) (goal : Goal)
    (bindings : Equations) (goals : List Goal) (destination : Atom)
    (bound : readBindings saved.bindings = some bindings)
    (before : rowsToGoals atoms saved.active = some goals)
    (output : atoms saved.output = some destination)
    (decoded : row.observe atoms = some occurrence) (understood : occurrence.request.goal = some goal) :
    ({ saved with active := saved.active ++ [row] }).readback atoms readBindings =
      some ⟨saved.world, ⟨bindings, goal :: goals, destination, saved.reserved,saved.cutBoundary⟩,
        saved.enclosing⟩ := by
  simp [Saved.readback, bound, rowsToGoals_push atoms saved.active row occurrence goal decoded understood,
    before, output]

def requestGoals (requests : List Request) : Option (List Goal) := requests.mapM Request.goal

/-- Exact push-order interpretation of the actual native let alternatives.
These use the source profile's reached bindings through `Control`; they do not
identify the default relational branch with eager value binding. -/
theorem relational_left_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .relationalLeft pattern producer body output joined).reverse) =
      some [.evaluate pattern joined, .evaluate producer joined, .evaluate body output] := by rfl

theorem relational_right_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .relationalRight pattern producer body output joined).reverse) =
      some [.evaluate producer joined, .evaluate pattern joined, .evaluate body output] := by rfl

theorem eager_value_goals (pattern producer body output joined : Atom) :
    requestGoals ((letPushes .eagerValue pattern producer body output joined).reverse) =
      some [.evaluate producer joined, .equate pattern joined, .evaluate body output] := by rfl

/-- The complete relational let continuation, including arbitrary older
requests, is the source continuation selected by the corresponding native
branch. Native plan/rigidity admission is the condition selecting that branch. -/
theorem let_goals_square (program : SpaceSemantics.Program) (policy : Policy)
    (pattern producer body output joined : Atom) :
    requestGoals ((letPushes
      (match policy with
       | .eagerValue => .eagerValue
       | .relational => if rigid program producer && !rigid program pattern
           then .relationalRight else .relationalLeft)
      pattern producer body output joined).reverse) =
      some (letGoals policy program pattern producer body output joined) := by
  cases policy with
  | eagerValue => rfl
  | relational =>
      simp only [letGoals]
      split <;> rfl

/-- This composed local square includes the reached bindings, world, outer
output and arbitrary older requests. The parsed C branches above determine
`letPushes`; the source branch computes its own destination continuation. -/
theorem let_cursor_square {Context : Type} (program : SpaceSemantics.Program)
    (policy : Policy) (cursor : Cursor Context) (pattern producer body output : Atom)
    (older : List Goal)
    (atLet : cursor.control.goals =
      .evaluate (.expression [.symbol "let", pattern, producer, body]) output :: older)
    (work : List Goal)
    (nativeGoals : requestGoals ((letPushes
      (match policy with
       | .eagerValue => .eagerValue
       | .relational => if rigid program producer && !rigid program pattern
           then .relationalRight else .relationalLeft)
      pattern producer body output (.var (freshName cursor.control 0))).reverse) = some work) :
    (EagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with goals := work ++ older } }) := by
  have exactWork := (let_goals_square program policy pattern producer body output
    (.var (freshName cursor.control 0))).symm.trans nativeGoals
  have same := Option.some.inj exactWork
  subst work
  simp [EagerDFS.Destination.machine, atLet, prepare, replace]

/-- Exact instruction request map for an ordinary prepared native call. The
ready argument cells and the original destination remain shared with all of
its pending producer goals. -/
theorem callReady_source (head : String) (arguments : List Atom) (destination : Atom) :
    (Request.callReady (.expression (.symbol head :: arguments)) destination).goal =
      some (.invoke head arguments destination) := rfl

/-- Every decoded goal occurrence remains at its original position. Equal
values and equal request syntax are not evidence for identifying occurrences. -/
theorem decoded_occurrence_count (occurrences : List Occurrence) (goals : List Goal)
    (decoded : sourceGoals occurrences = some goals) : goals.length = occurrences.length := by
  induction occurrences generalizing goals with
  | nil => simp [sourceGoals] at decoded; subst goals; rfl
  | cons occurrence rest ih =>
      simp only [sourceGoals, List.mapM_cons] at decoded
      cases first : occurrence.request.goal with
      | none => simp [first] at decoded
      | some goal =>
          cases later : sourceGoals rest with
          | none =>
              simp only [sourceGoals] at later
              simp [first, later] at decoded
          | some tail =>
              simp only [sourceGoals] at later
              simp [first, later] at decoded
              subst goals
              simpa using ih tail later

namespace Controls

open EagerDFS.Destination.Controls (program world)

def callAtoms : Ptr → Option Atom
  | ⟨1, 0⟩ => some (.expression [.symbol "f", .var "slot", .var "slot"])
  | ⟨2, 0⟩ => some (.var "result")
  | _ => none

theorem call_retains_argument_sharing_and_destination :
    rowsToGoals callAtoms [row 27 4] = some
      [.invoke "f" [.var "slot", .var "slot"] (.var "result")] := by decide +kernel

theorem height_guard_preserves_delimiter :
    Request.goal (.argumentReturn (.symbol "A") (.var "out") 5) =
      some (.argumentReturn (.symbol "A") (.var "out") 5) := by rfl

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals

/-! ## Finite current-store presentation and retained destination returns

The source destination machine remains independently stated. A whole
scope-checked contextual store snapshot constructs one finite substitution
for the return, output destination and older operand positions. Globals are
declared explicitly; unlisted private names do not gain shared identity.
The local accepted/refused square and saved-cursor laws do not assert a
bisimulation of arbitrary future primitives or whole default-PeTTa coverage.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- A successful source return consumes exactly its current equate goal.
All later work executes from the reached cursor, with its world and context. -/
theorem accepted_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (after : Equations) (accepted : Refinement cursor.control.bindings value destination (some after))
    (later : Nat) :
    (EagerDFS.Destination.machine policy program).run (later + 1) cursor =
      (EagerDFS.Destination.machine policy program).run later
        { cursor with control := { cursor.control with bindings := after, goals := older } } :=
  (EagerDFS.Destination.machine policy program).run_succ_silent
    ((return_square policy program cursor value destination older atReturn after).mp accepted)

/-- The selected presentation is consumed by the existing source machine.
This is an earned return square, not another transition implementation. -/
theorem certified_accepted_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)]))) (later : Nat) :
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      (EagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } } := by
  apply (EagerDFS.Destination.machine policy program).run_succ_silent
  apply (certified_return_step policy program cursor certified record value destination older atReturn).mp
  apply (return_square policy program cursor value destination older atReturn _).mp
  simpa only [record] using accepted

/-- A scheduler cut immediately after return keeps the complete resulting
cursor; no later goal is rerun, dropped or published as already completed. -/
theorem certified_return_pause {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)]))) :
    (EagerDFS.Destination.machine policy program).run 1 (cursor.readout table) =
      ([], .exhausted
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }) :=
  certified_accepted_run policy program cursor certified record value destination older atReturn accepted 0

/-- Actual earlier work is retained. The certified return and remaining
budget compose after the saved cursor, without restarting its prefix. -/
theorem certified_return_after_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement (bindingAtomEquations bindings) value destination
      (some (bindingAtomEquations bindings ++ [(value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (EagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout table))) :
    (EagerDFS.Destination.machine policy program).run (first + (later + 1)) source =
      (events ++ ((EagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }).1,
        ((EagerDFS.Destination.machine policy program).run later
        { cursor.readout table with control := { (cursor.readout table).control with
          bindings := bindingAtomEquations bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }).2) := by
  rw [EagerDFS.Destination.resume policy program first (later + 1)
    source (cursor.readout table) events paused]
  rw [certified_accepted_run policy program cursor certified record value destination older atReturn accepted]

/-- Refusal completes the current branch with its reached world and cursor.
It is deliberately distinct from budget exhaustion and operation handoff. -/
theorem certified_refused_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (cursor : Cursor Context) {bindings : Bindings} {table : TypeSubst}
    (certified : ReadoutCertificate bindings table)
    (record : cursor.control.bindings = bindingAtomEquations bindings)
    (value destination : Atom) (older : List Goal)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (refused : Refinement (bindingAtomEquations bindings) value destination none) (later : Nat) :
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .finished (.noValue cursor.control.bindings, cursor.readout table)) := by
  apply (EagerDFS.Destination.machine policy program).run_succ_finish
  apply (certified_refused_step policy program cursor certified record value destination older atReturn).mp
  apply (refused_return_square policy program cursor value destination older atReturn).mp
  simpa only [record] using refused

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

/-- The complete contextual request is read with one computed table. The
output destination, older goals and further caller operands keep their order
and repeated occurrences. The retained slot snapshot is obtained by actual
scope-checked preparation with explicitly declared global names, not by a
callback supplying an expected equation record. -/
theorem current_store_live_readout
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    (value destination output : Atom) (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands =
      some (snapshot, value :: destination :: output :: older.flatMap Goal.atoms ++ contextual)) :
    CurrentStore.readout? image operands =
      some (let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
        table.apply value :: table.apply destination :: table.apply output ::
          (older.map (Goal.readout table)).flatMap Goal.atoms ++ contextual.map table.apply) := by
  rw [CurrentStore.readout?_prepared (CurrentStore.prepareScoped?_success prepared)]
  simp only [goals_readout_atoms, List.map_cons, List.map_append]

/-- Actual scope-checked whole-store preparation and strict finite dependency rank earn the
return simulation and its reflection. The independent destination machine
retains its original world, caller context and raw equation record. -/
theorem current_store_return_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := cursor.control.bindings ++ [(value, destination)], goals := older } }) ↔
    (EagerDFS.Destination.machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  simpa only [record] using certified_return_step policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn

/-- Failure is transported through the same computed readout. It finishes the
current branch with the reached world; it neither exhausts a budget nor asks
for an unsupported service. -/
theorem current_store_refused_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).step cursor =
        some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (EagerDFS.Destination.machine policy program).step (cursor.readout table) =
        some (.finish (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_refused_step policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn

/-- Actual source resolution constructs the corresponding presented solution.
One residual permutation compares the entire live continuation tuple. The
ranked profile is finite first-order substitution, not cyclic PeTTa values. -/
theorem current_store_return_resolves
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination output : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: output :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    {environment : Environment}
    (resolved : resolve (bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩ ++
      [(value, destination)]) = some environment) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    ∃ presented, resolve (bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩ ++
        [(table.apply value, table.apply destination)]) = some presented ∧
      ∃ permutation : Equiv.Perm String,
        (table.apply output :: (older.map (Goal.readout table)).flatMap Goal.atoms ++
          contextual.map table.apply).map (read presented) =
        ((output :: older.flatMap Goal.atoms ++ contextual).map (read environment)).map
          (renameTypeVars permutation) := by
  simpa only [List.map_cons, List.map_append, goals_readout_atoms] using
    certified_return_resolve (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked)
      value destination resolved (output :: older.flatMap Goal.atoms ++ contextual)

/-- A successful prepared return has an exact one-step saved cursor. The
snapshot certificate is constructed here from the current logical store. -/
theorem current_store_return_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination
      (some (cursor.control.bindings ++ [(value, destination)]))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run 1 (cursor.readout table) =
      ([], .exhausted { cursor.readout table with
        control := { (cursor.readout table).control with
          bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
          goals := older.map (Goal.readout table) } }) := by
  simpa only [record] using certified_return_pause policy program cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn
    (by simpa only [record] using accepted)

/-- Earlier work is consumed once. A pause at the actual prepared return
resumes from its full reached cursor, including its already performed effects. -/
theorem current_store_return_after_prefix {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (source cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (accepted : Refinement cursor.control.bindings value destination
      (some (cursor.control.bindings ++ [(value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (EagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout
        (CurrentStore.normalize (CurrentStore.assignments snapshot))))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    let reached := { cursor.readout table with control := { (cursor.readout table).control with
      bindings := cursor.control.bindings ++ [(table.apply value, table.apply destination)],
      goals := older.map (Goal.readout table) } }
    (EagerDFS.Destination.machine policy program).run (first + (later + 1)) source =
      (events ++ ((EagerDFS.Destination.machine policy program).run later reached).1,
        ((EagerDFS.Destination.machine policy program).run later reached).2) := by
  simpa only [record] using certified_return_after_prefix policy program source cursor
    (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked) record value destination older atReturn
    (by simpa only [record] using accepted) first later events paused

/-- Inconsistent equations reject the prepared return at any positive budget,
while retaining the reached state. No current-store failure is reinterpreted
as a successful empty result. -/
theorem current_store_refused_run {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .equate value destination :: older)
    (refused : Refinement cursor.control.bindings value destination none) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .finished (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_refused_run policy program cursor (CurrentStore.prepare?_certified (CurrentStore.prepareScoped?_success prepared) ranked)
    record value destination older atReturn (by simpa only [record] using refused) later

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 600000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.PresentationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Logic.LP

private def bindings : Bindings := ⟨[], [("x", "y")]⟩
private def table : TypeSubst := [("x", .var "y")]

private theorem certified : ReadoutCertificate bindings table := by
  apply ReadoutCertificate.of_fold
  change EquationListPresentationRel [(.var "x", .var "y")] [] [("x", .var "y")]
  refine .cons (.ordinary (TypeSubst.apply_empty _) (TypeSubst.apply_empty _) ?_) (.nil _)
  simpa [TypeSubst.bind, TypeSubst.erase] using
    (AppliedReducedTypeMatchRel.bindLeft (substitution := []) (name := "x")
      (right := .var "y") (by decide))

def pair (first second : Atom) : Atom := .expression [.symbol "Pair", first, second]
def program : SpaceSemantics.Program := { equations := [], declarations := [] }
def world : World := ⟨Effects.empty, [], [.symbol "earlier"]⟩
def older : List Goal := [.invoke "println!" [pair (.var "x") (.var "x")] (.var "unit")]
def cursor : Cursor String :=
  ⟨world,
    { bindings := bindingAtomEquations bindings
      goals := .equate (.symbol "A") (.var "x") :: older
      destination := pair (.var "x") (.var "x")
      reserved := {"sibling"} },
    "outer-caller"⟩
def afterReturn : Cursor String :=
  { cursor.readout table with control := { (cursor.readout table).control with
    bindings := bindingAtomEquations bindings ++ [(.symbol "A", .var "y")],
    goals := older.map (Goal.readout table) } }

private theorem accepted : Refinement (bindingAtomEquations bindings) (.symbol "A") (.var "x")
    (some (bindingAtomEquations bindings ++ [(.symbol "A", .var "x")])) := by
  let environment : Environment := fun name =>
    if name = "x" ∨ name = "y" then encode (.symbol "A") else .var name
  refine .accepted environment ?_ ?_
  · simp [Solves, bindings, bindingAtomEquations, read, environment, decode, encode, Subst.applyTerm]
  · simp [read, environment, decode, encode, Subst.applyTerm]

theorem repeated_variable_readout :
    (cursor.readout table).control.destination = pair (.var "y") (.var "y") := by
  simp [cursor, Cursor.readout, table, pair, TypeSubst.apply, TypeSubst.lookup]

theorem independent_variables_are_not_shared_readout :
    (cursor.readout table).control.destination ≠ pair (.var "y") (.var "z") := by
  rw [repeated_variable_readout]
  decide

theorem return_pause_keeps_full_cursor :
    (machine .relational program).run 1 (cursor.readout table) = ([], .exhausted afterReturn) := by
  simpa [afterReturn, table, TypeSubst.apply, TypeSubst.lookup] using
    certified_return_pause .relational program cursor certified rfl
      (.symbol "A") (.var "x") older rfl accepted

theorem return_keeps_world_and_outer_work :
    afterReturn.world = world ∧ afterReturn.context = "outer-caller" ∧
      afterReturn.control.reserved = {"sibling"} ∧
      afterReturn.control.goals = [.invoke "println!" [pair (.var "y") (.var "y")] (.var "unit")] := by
  simp [afterReturn, cursor, Cursor.readout, older, Goal.readout, table,
    TypeSubst.apply, TypeSubst.lookup, pair]

def printed (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option (List Atom) :=
  (observed result).map (fun state => state.1.output)

def value (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome (Cursor String) (Result × Cursor String) Boundary) : Option Atom :=
  match result with
  | .finished (.value atom _, _) => some atom
  | _ => none

def resumeAfterEffect : Option (List Atom) := do
  match ((machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved => printed ((machine .relational program).run 2 saved).2
  | _ => none

def restartAfterEffect : Option (List Atom) := do
  match ((machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved =>
      let restarted := { cursor.readout table with world := saved.world }
      printed ((machine .relational program).run 4 restarted).2
  | _ => none

/- Executable controls use the actual total unifier and retained machine. -/
#guard value ((machine .relational program).run 4 (cursor.readout table)).2 ==
  some (pair (.symbol "A") (.symbol "A"))
#guard resumeAfterEffect == some [.symbol "earlier", pair (.symbol "A") (.symbol "A")]
#guard restartAfterEffect == some [.symbol "earlier", pair (.symbol "A") (.symbol "A"),
  pair (.symbol "A") (.symbol "A")]

private theorem incompatible : Refinement (bindingAtomEquations bindings)
    (.symbol "A") (.symbol "B") none := by
  apply Refinement.refused
  rintro ⟨environment, _, impossible⟩
  simp only [read_eq_applyTypeValuation, applyTypeValuation] at impossible
  exact (by decide : Atom.symbol "A" ≠ .symbol "B") impossible

def refusedCursor : Cursor String :=
  { cursor with control := { cursor.control with
      goals := .equate (.symbol "A") (.symbol "B") :: older } }

theorem inconsistent_equation_refuses_and_keeps_world :
    (machine .relational program).run 8 (refusedCursor.readout table) =
      ([], .finished (.noValue (bindingAtomEquations bindings), refusedCursor.readout table)) := by
  exact certified_refused_run .relational program refusedCursor certified rfl
    (.symbol "A") (.symbol "B") older rfl incompatible 7

theorem refused_return_is_not_budget_exhaustion :
    ((machine .relational program).run 8 (refusedCursor.readout table)).2 ≠
      .exhausted (refusedCursor.readout table) := by
  rw [inconsistent_equation_refuses_and_keeps_world]
  intro impossible
  cases impossible

theorem refusal_does_not_execute_the_pending_print :
    printed ((machine .relational program).run 8 (refusedCursor.readout table)).2 =
      some [.symbol "earlier"] := by
  rw [inconsistent_equation_refuses_and_keeps_world]
  rfl

/-- Structural readout of written syntax does not invoke it. -/
theorem readout_does_not_force_written_call :
    table.apply (.expression [.symbol "println!", .var "x"]) =
      .expression [.symbol "println!", .var "y"] := by
  simp [table, TypeSubst.apply, TypeSubst.lookup]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFS.Destination.PresentationControls


set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.CurrentStoreControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared
open Mettapedia.Logic.LP

private def caller : Token := ⟨0, 3⟩
private def child : Token := ⟨1, 8⟩
private def callerName : String := CurrentStore.referenceName (caller.ref 0)
private def childName : String := CurrentStore.referenceName (child.ref 0)
private def unitName : String := CurrentStore.referenceName (child.ref 1)
private def pair (first second : Atom) : Atom := .expression [.symbol "pair", first, second]
private def image : ImageOf CurrentStore.ContextualOperand :=
  ⟨#[some (EntryOf.initial 3 ["x"] (fun _ => some (child, .var "x"))),
     some (EntryOf.initial 8 ["x", "unit"] (fun _ => none))], 11⟩
attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.readout? CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  MetavariableFrameStore.Snapshot.rows MetavariableFrameStore.Snapshot.entryRows MetavariableFrameStore.Snapshot.Row.ofEntry EntryOf.initial entryEnv
  MetavariableFrameStore.Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  caller child callerName childName unitName image pair

private def snapshot : List CurrentStore.Row := (CurrentStore.contextualRows? image).get (by decide)
attribute [local simp] snapshot

private def table : TypeSubst := CurrentStore.normalize (CurrentStore.assignments snapshot)
private def older : List Goal :=
  [.invoke "println!" [pair (.var callerName) (.var callerName)] (.var unitName)]
private def operands : List CurrentStore.ContextualOperand :=
  [(caller, .symbol "A"), (caller, .var "x"),
    (caller, pair (.var "x") (.var "x")), (child, .var "unit"),
    (caller, pair (.var "x") (.var "x"))]
private def world : EagerDFS.World := ⟨Effects.empty, [], [.symbol "earlier"]⟩
private def program : SpaceSemantics.Program := { equations := [], declarations := [] }
private def cursor : Cursor String :=
  ⟨world,
    { bindings := bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩
      goals := .equate (.symbol "A") (.var callerName) :: older
      destination := pair (.var callerName) (.var callerName)
      reserved := {"sibling"} },
    "outer-caller"⟩

private theorem actual_assignments :
    CurrentStore.assignments snapshot = [(callerName, .var childName)] := by simp

private def rank (name : String) : Nat := if name = callerName then 1 else 0

private theorem ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot) := by
  rw [actual_assignments]
  intro name value member
  simp only [List.mem_singleton, Prod.mk.injEq] at member
  rcases member with ⟨rfl, rfl⟩
  intro varName occurs
  simp only [TypeSubst.typeVars, List.mem_singleton] at occurs
  subst varName
  simp [rank]

private theorem actual_table : table = [(callerName, .var childName)] := by simp [table]

private theorem prepared : CurrentStore.prepareScoped? [] image operands = some
    (snapshot, .symbol "A" :: .var callerName :: cursor.control.destination ::
      older.flatMap Goal.atoms ++ []) := by simp [operands, cursor, older, Goal.atoms]

private theorem accepted : Refinement cursor.control.bindings (.symbol "A") (.var callerName)
    (some (cursor.control.bindings ++ [(.symbol "A", .var callerName)])) := by
  let environment : Environment := fun _ => encode (.symbol "A")
  refine .accepted environment ?_ ?_
  · simp [cursor, bindingAtomEquations, Solves, EagerDFS.Destination.read,
      environment, encode, decode, Subst.applyTerm]
  · simp [EagerDFS.Destination.read, environment, encode, decode, Subst.applyTerm]

/-- Two authored x names in distinct live frames retain distinct references;
the alias is an explicit current assignment rather than a spelling collision. -/
theorem authored_names_keep_context :
    CurrentStore.qualify? image (caller, .var "x") = some (.var callerName) ∧
      CurrentStore.qualify? image (child, .var "x") = some (.var childName) ∧
      callerName ≠ childName := by simp

theorem actual_joint_preparation :
    CurrentStore.readout? image operands = some
      [.symbol "A", .var childName, pair (.var childName) (.var childName),
        .var unitName, pair (.var childName) (.var childName)] := by
  have result := current_store_live_readout (.symbol "A") (.var callerName)
    cursor.control.destination older [] [] prepared
  simpa [cursor, older, Goal.readout, Goal.atoms] using result

/-- The open target is a live slot, while an old incarnation is not a free variable. -/
theorem open_and_stale_are_not_interchanged :
    (MetavariableFrameStore.Snapshot.readRow? image (child.ref 0)).map (fun row => row.observed.value) = some none ∧
      CurrentStore.prepare? image [(⟨1, 9⟩, .var "x")] = none := by decide

/-- Equal undeclared spellings in different frames do not create a global variable. -/
theorem undeclared_private_name_refused :
    CurrentStore.prepareScoped? [] image
      [(caller, .var "private"), (child, .var "private")] = none := by
  simp

/-- Shared external identity is available only when the source context declares it. -/
theorem declared_global_name_shared :
    (CurrentStore.prepareScoped? ["ambient"] image
      [(caller, .var "ambient"), (child, .var "ambient")]).isSome = true ∧
    CurrentStore.readout? image [(caller, .var "ambient"), (child, .var "ambient")] =
      some [.var (CurrentStore.freeName "ambient"), .var (CurrentStore.freeName "ambient")] := by
  simp
  decide +kernel

theorem current_store_pause_preserves_parent :
    (EagerDFS.Destination.machine .relational program).run 1 (cursor.readout table) =
      ([], .exhausted { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(table.apply (.symbol "A"), table.apply (.var callerName))],
        goals := older.map (Goal.readout table) } }) :=
  current_store_return_pause .relational program cursor (.symbol "A") (.var callerName)
    older [] [] prepared ranked rfl rfl accepted

private def printed (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Cursor String) (Result × Cursor String) Boundary) : Option (List Atom) :=
  (observed result).map (fun state => state.1.output)

private def answer (result : Mettapedia.GSLT.Distinction.ProductiveBlocks.Outcome
    (Cursor String) (Result × Cursor String) Boundary) : Option Atom :=
  match result with
  | .finished (.value atom _, _) => some atom
  | _ => none

private def resumeAfterPrint : Option (List Atom) := do
  match ((EagerDFS.Destination.machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved => printed ((EagerDFS.Destination.machine .relational program).run 2 saved).2
  | _ => none

private def restartAfterPrint : Option (List Atom) := do
  match ((EagerDFS.Destination.machine .relational program).run 2 (cursor.readout table)).2 with
  | .exhausted saved =>
      let restarted := { cursor.readout table with world := saved.world }
      printed ((EagerDFS.Destination.machine .relational program).run 4 restarted).2
  | _ => none

#guard answer ((EagerDFS.Destination.machine .relational program).run 4
  (cursor.readout table)).2 == some (pair (.symbol "A") (.symbol "A"))
#guard resumeAfterPrint == some [.symbol "earlier", pair (.symbol "A") (.symbol "A")]
#guard restartAfterPrint == some [.symbol "earlier", pair (.symbol "A") (.symbol "A"),
  pair (.symbol "A") (.symbol "A")]

private def badCursor : Cursor String :=
  { cursor with control := { cursor.control with
      goals := .equate (.symbol "A") (.symbol "B") :: older } }
private def badOperands : List CurrentStore.ContextualOperand :=
  [(caller, .symbol "A"), (caller, .symbol "B"),
    (caller, pair (.var "x") (.var "x")), (child, .var "unit"),
    (caller, pair (.var "x") (.var "x"))]
private theorem badPrepared : CurrentStore.prepareScoped? [] image badOperands = some
    (snapshot, .symbol "A" :: .symbol "B" :: badCursor.control.destination ::
      older.flatMap Goal.atoms ++ []) := by simp [badOperands, badCursor, cursor, older, Goal.atoms]
private theorem incompatible : Refinement badCursor.control.bindings (.symbol "A") (.symbol "B") none := by
  apply Refinement.refused
  rintro ⟨environment, _, impossible⟩
  simp only [read_eq_applyTypeValuation, applyTypeValuation] at impossible
  exact (by decide : Atom.symbol "A" ≠ .symbol "B") impossible

theorem actual_inconsistent_return_refused :
    (EagerDFS.Destination.machine .relational program).run 8 (badCursor.readout table) =
      ([], .finished (.noValue badCursor.control.bindings, badCursor.readout table)) :=
  current_store_refused_run .relational program badCursor (.symbol "A") (.symbol "B")
    older [] [] badPrepared ranked rfl rfl incompatible 7

theorem refused_preserves_world_and_pending_occurrence :
    printed ((EagerDFS.Destination.machine .relational program).run 8
      (badCursor.readout table)).2 = some [.symbol "earlier"] ∧
      (badCursor.readout table).context = "outer-caller" ∧
      (badCursor.readout table).control.goals.length = 2 := by
  rw [actual_inconsistent_return_refused]
  simp [printed, observed, badCursor, cursor, Cursor.readout, older, world]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.CurrentStoreControls

/-! ## Retained invocation and argument-return boundaries -/


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination

/-- The admitted argument plan schedules a producer followed by its optional
error delimiter. The Boolean flags are the existing argument-plan boundary;
this list does not claim to classify every typed or specialized operation. -/
def argumentWork (eagerFaults : Bool) (output : Atom) (callerDepth : Nat)
    (arguments : List Argument) : List Goal :=
  arguments.flatMap fun argument =>
    (if argument.evaluate then [.evaluate argument.expression argument.destination] else []) ++
    (if eagerFaults && (argument.evaluate || argument.knownError) then
      [.argumentReturn argument.destination output callerDepth] else [])

theorem argumentExecution_source (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    requestGoals (argumentExecution eagerFaults output height arguments) =
      some (argumentWork eagerFaults output height.toNat arguments) := by
  induction arguments with
  | nil => rfl
  | cons argument rest ih =>
      simp only [argumentExecution, argumentWork, List.flatMap_cons] at ih ⊢
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;>
        simp_all [requestGoals, Request.goal]

/-- This composes the actual descending push order with the source goal map.
Repeated identical argument requests remain repeated positions. -/
theorem argumentPushes_source (eagerFaults : Bool) (output : Atom) (height : UInt64)
    (arguments : List Argument) :
    requestGoals ((argumentPushes eagerFaults output height arguments).reverse) =
      some (argumentWork eagerFaults output height.toNat arguments) := by
  rw [argument_order]
  exact argumentExecution_source eagerFaults output height arguments

/-- All argument guards share the caller delimiter. The final invocation is
younger than that delimiter, so a reached error also bypasses the invocation. -/
theorem argumentWork_wellDelimited (eagerFaults : Bool) (output : Atom) (depth : Nat)
    (arguments : List Argument) (following : List Goal)
    (bound : depth ≤ following.length) (valid : WellDelimited following) :
    WellDelimited (argumentWork eagerFaults output depth arguments ++ following) := by
  induction arguments with
  | nil => exact valid
  | cons argument rest ih =>
      have larger : depth ≤ (argumentWork eagerFaults output depth rest ++ following).length := by
        simp only [List.length_append]
        omega
      simp only [argumentWork, List.flatMap_cons, List.append_assoc]
      cases eagerFaults <;> cases argument.evaluate <;> cases argument.knownError <;>
        simp_all only [Bool.false_and, Bool.true_and,
          Bool.or_false, Bool.or_true, Bool.false_eq_true, ↓reduceIte,
          List.nil_append, List.cons_append, WellDelimited]
      all_goals first | exact ih | exact ⟨larger, ih⟩

/-- A saved native height is one representation of the source delimiter.
The exact source schedule proves the represented state well formed. -/
theorem prepared_call_wellDelimited (eagerFaults : Bool) (head : String)
    (arguments : List Argument) (ready : List Atom) (output : Atom) (height : UInt64)
    (older : List Goal) (delimiter : height.toNat = older.length)
    (valid : WellDelimited older) :
    WellDelimited (argumentWork eagerFaults output height.toNat arguments ++
      (.invoke head ready output :: older)) := by
  apply argumentWork_wellDelimited
  · simp only [delimiter, List.length_cons]; omega
  · exact valid

/-- For an ordinary prepared call the actual goal map preserves every
argument occurrence and the final invocation before the older caller suffix. -/
theorem prepared_call_goals (eagerFaults : Bool) (head : String)
    (arguments : List Argument) (ready : List Atom) (output : Atom) (height : UInt64) :
    requestGoals ((argumentPushes eagerFaults output height arguments).reverse ++
      [.callReady (.expression (.symbol head :: ready)) output]) =
      some (argumentWork eagerFaults output height.toNat arguments ++ [.invoke head ready output]) := by
  have mapped := argumentPushes_source eagerFaults output height arguments
  unfold requestGoals at mapped ⊢
  rw [List.mapM_append, mapped]
  rfl

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.NativeGoals


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The actual current-store snapshot supplies one table for the produced
value, outer destination, complete younger/older continuation and context. -/
theorem current_store_argument_return_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).step cursor = some (.silent
      { cursor with control := { cursor.control with
        bindings := cursor.control.bindings ++ [(read environment value, destination)], goals := older } }) ↔
    (EagerDFS.Destination.machine policy program).step (cursor.readout table) = some (.silent
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) :=
  certified_argumentReturn_propagated policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
    atReturn resolved error

/-- Post-binding refusal is transported by the same table as success. The
reached world remains available at the terminal branch result. -/
theorem current_store_argument_refused_square {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).step cursor = some (.finish (.noValue cursor.control.bindings, cursor)) ↔
    (EagerDFS.Destination.machine policy program).step (cursor.readout table) =
      some (.finish (.noValue cursor.control.bindings, cursor.readout table)) :=
  certified_argumentReturn_refused policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
    atReturn resolved error

/-- A normal return resumes the exact pending caller work for every later
budget. No child or prior effect is restarted. -/
theorem current_store_argument_normal_run {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (normal : (read environment value).isError = false) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      (EagerDFS.Destination.machine policy program).run later
        ({ cursor with control := replace cursor.control (younger ++ older) }.readout table) :=
  (EagerDFS.Destination.machine policy program).run_succ_silent
    (certified_argumentReturn_ordinary policy program cursor
      (CurrentStore.prepareScoped?_certified prepared ranked) record value destination younger older
      atReturn resolved normal)

/-- Successful error delivery pauses after the constraint was added and the
younger work was removed. Its parent world/context and older suffix are exact. -/
theorem current_store_argument_error_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true)
    (accepted : Refinement cursor.control.bindings (read environment value) destination
      (some (cursor.control.bindings ++ [(read environment value, destination)]))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run 1 (cursor.readout table) = ([], .exhausted
      { cursor.readout table with control := { (cursor.readout table).control with
        bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
        goals := older.map (Goal.readout table) } }) := by
  apply (EagerDFS.Destination.machine policy program).run_succ_silent (fuel := 0)
  apply (current_store_argument_return_square policy program cursor value destination younger older
    globals contextual prepared ranked record atReturn resolved error).mp
  exact (argumentReturn_propagated_square policy program cursor value destination younger older
    atReturn resolved error _).mp accepted

/-- An arbitrary already-executed prefix composes with the retained error
return. This preserves the reached world, even when the prefix performed IO. -/
theorem current_store_argument_after_prefix {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (source cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (value destination : Atom) (younger older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      value :: destination :: cursor.control.destination :: (younger ++ older).flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atReturn : cursor.control.goals = .argumentReturn value destination older.length :: (younger ++ older))
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (error : (read environment value).isError = true)
    (accepted : Refinement cursor.control.bindings (read environment value) destination
      (some (cursor.control.bindings ++ [(read environment value, destination)])))
    (first later : Nat) (events : List Empty)
    (paused : (EagerDFS.Destination.machine policy program).run first source =
      (events, .exhausted (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))))) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    let reached := { cursor.readout table with control := { (cursor.readout table).control with
      bindings := cursor.control.bindings ++ [(read environment value, table.apply destination)],
      goals := older.map (Goal.readout table) } }
    (EagerDFS.Destination.machine policy program).run (first + 1 + later) source =
      (events ++ ((EagerDFS.Destination.machine policy program).run later reached).1,
        ((EagerDFS.Destination.machine policy program).run later reached).2) := by
  dsimp only
  rw [Nat.add_assoc, EagerDFS.Destination.resume policy program first (1 + later)
    source _ events paused]
  rw [(EagerDFS.Destination.machine policy program).run_add 1 later,
    current_store_argument_error_pause policy program cursor value destination younger older
      globals contextual prepared ranked record atReturn resolved error accepted]
  rfl

/-- A real print operation reads its argument through the certified reached
store and appends exactly one output before its pending return check. -/
theorem current_store_print_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (argument destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      argument :: destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atPrint : cursor.control.goals = .invoke "println!" [argument] destination :: older)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run 1 (cursor.readout table) = ([], .exhausted
      ({ cursor with
        world := { cursor.world with output := cursor.world.output ++ [read environment argument] }
        control := replace cursor.control (.equate (Effects.boolean true) destination :: older) }.readout table)) :=
  certified_print_resume policy program cursor
    (CurrentStore.prepareScoped?_certified prepared ranked) record argument destination older atPrint resolved 0

/-- Calls not handled by this local component retain their actual resolved
argument occurrences and the whole saved continuation. The theorem does not
count an unserved request as an executed equation or primitive. -/
theorem current_store_invocation_request {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (notPrint : head ≠ "println!") {environment : Environment}
    (resolved : resolve cursor.control.bindings = some environment) (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke head (arguments.map (read environment)) (table.apply destination))
        (cursor.readout table)) :=
  (EagerDFS.Destination.machine policy program).run_succ_call
    (certified_invoke_request_step policy program cursor
      (CurrentStore.prepareScoped?_certified prepared ranked) record head arguments destination older
      atCall notPrint resolved)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.CurrentStoreControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open MetavariableFrameStore.Shared
open Mettapedia.Logic.LP

attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.readout? CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  MetavariableFrameStore.Snapshot.rows MetavariableFrameStore.Snapshot.entryRows MetavariableFrameStore.Snapshot.Row.ofEntry EntryOf.initial entryEnv
  MetavariableFrameStore.Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  caller child callerName childName unitName image pair snapshot

private def argumentError : Atom := .expression [.symbol "Error", pair (.var callerName) (.var callerName)]
private def argumentOlder : List Goal :=
  [.invoke "later" [pair (.var callerName) (.var callerName)] (.symbol "ok")]
private def argumentYounger : List Goal :=
  [.invoke "println!" [.symbol "skipped"] (.var unitName)]
private def argumentCursor : Cursor String :=
  {cursor with control := {cursor.control with goals :=
      (.argumentReturn argumentError (.var unitName) argumentOlder.length ::
        (argumentYounger ++ argumentOlder))}}
private def argumentOperands : List CurrentStore.ContextualOperand :=
  [(caller, .expression [.symbol "Error", pair (.var "x") (.var "x")]),
   (child, .var "unit"), (caller, pair (.var "x") (.var "x")),
   (child, .var "unit"), (caller, .symbol "skipped"),
   (caller, .symbol "ok"), (caller, pair (.var "x") (.var "x"))]

private theorem argumentPrepared : CurrentStore.prepareScoped? [] image argumentOperands = some
    (snapshot, argumentError :: .var unitName :: argumentCursor.control.destination ::
      (argumentYounger ++ argumentOlder).flatMap Goal.atoms ++ []) := by
  simp [argumentOperands, argumentCursor, cursor, argumentError, argumentOlder, argumentYounger, Goal.atoms]

private def argumentEnvironment : Environment :=
  Subst.single callerName (encode (.var childName))
private theorem argumentResolved : resolve argumentCursor.control.bindings = some argumentEnvironment := by
  simp [argumentCursor, cursor, bindingAtomEquations, argumentEnvironment, resolve, equations,
    encode, unifyTotal, Subst.applyEqs, Subst.comp_id_left]
private theorem argumentIsError : (EagerDFS.Destination.read argumentEnvironment argumentError).isError = true := by
  simp [argumentEnvironment, argumentError, EagerDFS.Destination.read, encode, decode,
    Subst.single, Atom.isError]
private theorem argumentAccepted : Refinement argumentCursor.control.bindings
    (EagerDFS.Destination.read argumentEnvironment argumentError) (.var unitName)
    (some (argumentCursor.control.bindings ++
      [(EagerDFS.Destination.read argumentEnvironment argumentError, .var unitName)])) := by
  apply (refinement_iff _ _ _ _).mpr
  simp [argumentCursor, cursor, argumentEnvironment, argumentError, bindingAtomEquations,
    EagerDFS.Destination.read, refine, resolve, equations, encode, decode, unifyTotal,
    Subst.applyEqs, Subst.single, Subst.applyTerm, Term.occursIn, Fin.exists_fin_succ]

/-- The actual two-frame alias snapshot prepares and executes the error guard.
Its full older continuation shares the same qualified open variable twice. -/
theorem scoped_argument_pause_keeps_open_correlation :
    (EagerDFS.Destination.machine .relational program).run 1 (argumentCursor.readout table) =
      ([], .exhausted { argumentCursor.readout table with
        control := { (argumentCursor.readout table).control with
          bindings := argumentCursor.control.bindings ++
            [(EagerDFS.Destination.read argumentEnvironment argumentError, table.apply (.var unitName))],
          goals := argumentOlder.map (Goal.readout table) } }) :=
  current_store_argument_error_pause .relational program argumentCursor argumentError (.var unitName)
    argumentYounger argumentOlder [] [] argumentPrepared ranked rfl rfl argumentResolved argumentIsError argumentAccepted

theorem scoped_argument_readout_keeps_correlation :
    table.apply argumentError = .expression [.symbol "Error", pair (.var childName) (.var childName)] ∧
      argumentOlder.map (Goal.readout table) =
        [.invoke "later" [pair (.var childName) (.var childName)] (.symbol "ok")] := by
  simp [table, argumentError, argumentOlder, Goal.readout]

theorem scoped_guard_keeps_parent_and_effect_prefix :
    (argumentCursor.readout table).context = "outer-caller" ∧
      (argumentCursor.readout table).control.reserved = {"sibling"} ∧
      (argumentCursor.readout table).world.output = [.symbol "earlier"] := by
  exact ⟨rfl, rfl, rfl⟩

private def cyclicArgumentCursor : Cursor String :=
  {argumentCursor with control := {argumentCursor.control with goals :=
      (.argumentReturn argumentError (.var callerName) argumentOlder.length ::
        (argumentYounger ++ argumentOlder))}}
private def cyclicArgumentOperands : List CurrentStore.ContextualOperand :=
  [(caller, .expression [.symbol "Error", pair (.var "x") (.var "x")]),
   (caller, .var "x"), (caller, pair (.var "x") (.var "x")),
   (child, .var "unit"), (caller, .symbol "skipped"),
   (caller, .symbol "ok"), (caller, pair (.var "x") (.var "x"))]
private theorem cyclicArgumentPrepared : CurrentStore.prepareScoped? [] image cyclicArgumentOperands = some
    (snapshot, argumentError :: .var callerName :: cyclicArgumentCursor.control.destination ::
      (argumentYounger ++ argumentOlder).flatMap Goal.atoms ++ []) := by
  simp [cyclicArgumentOperands, cyclicArgumentCursor, argumentCursor, cursor, argumentError,
    argumentOlder, argumentYounger, Goal.atoms]

/-- Binding the returned error to its own open argument is refused after the
reached alias equations. Refusal retains the already performed world. -/
theorem scoped_argument_occurs_refusal :
    (EagerDFS.Destination.machine .relational program).run 1 (cyclicArgumentCursor.readout table) =
      ([], .finished (.noValue cyclicArgumentCursor.control.bindings, cyclicArgumentCursor.readout table)) := by
  apply (EagerDFS.Destination.machine .relational program).run_succ_finish (fuel := 0)
  apply (current_store_argument_refused_square .relational program cyclicArgumentCursor argumentError
    (.var callerName) argumentYounger argumentOlder [] [] cyclicArgumentPrepared ranked rfl rfl
    argumentResolved argumentIsError).mp
  apply (argumentReturn_refused_square .relational program cyclicArgumentCursor argumentError
    (.var callerName) argumentYounger argumentOlder rfl argumentResolved argumentIsError).mp
  apply (refinement_iff _ _ _ _).mpr
  simp [cyclicArgumentCursor, argumentCursor, cursor, argumentEnvironment, argumentError,
    bindingAtomEquations, EagerDFS.Destination.read, refine, resolve, equations,
    encode, decode, unifyTotal, Subst.applyEqs, Subst.single, Subst.applyTerm,
    Term.occursIn, Fin.exists_fin_succ]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.CurrentStoreControls


set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS.Destination
open EagerDFS.Destination.ClauseChoice

/-- A scope-checked complete current-store tuple reaches the existing
invocation request. Each actually computed source-equation occurrence earns
its fresh body, a solvable reached constraint store, and one later readout
for all pending observations. Body execution remains saved work. -/
theorem current_store_clause_selection {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program) (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (atCall : cursor.control.goals = .invoke head arguments destination :: older)
    (ordinary : Eval.ioHead head = false ∧ StdLib.known head = false)
    {environment : Environment} (resolved : resolve cursor.control.bindings = some environment)
    (occurrence : Nat) (next : Control)
    (selected : (occurrence, next) ∈ choices program
      (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))).control head
      (arguments.map (read environment))
      ((CurrentStore.normalize (CurrentStore.assignments snapshot)).apply destination)
      (older.map (Goal.readout (CurrentStore.normalize (CurrentStore.assignments snapshot)))))
    (later : Nat) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    (EagerDFS.Destination.machine policy program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke head (arguments.map (read environment)) (table.apply destination))
        (cursor.readout table)) ∧
    ∃ equation reached,
      program.equations[occurrence]? = some equation ∧
      Selection program (cursor.readout table).control head (arguments.map (read environment))
        (table.apply destination) (older.map (Goal.readout table)) occurrence
        (freshPattern (cursor.readout table).control occurrence equation)
        (freshBody (cursor.readout table).control occurrence equation) next ∧
      resolve next.bindings = some reached ∧
      (∀ pending : List Atom,
        (pending.map table.apply).map (read reached) = pending.map (read reached)) ∧
      ({cursor with control := next} : Cursor Context).world = cursor.world ∧
      ({cursor with control := next} : Cursor Context).context = cursor.context := by
  dsimp only
  have notPrint : head ≠ "println!" := by
    intro same
    subst head
    simpa [Eval.ioHead] using ordinary.1
  refine ⟨current_store_invocation_request policy program cursor head arguments destination older
    globals contextual prepared ranked record atCall notPrint resolved later, ?_⟩
  obtain ⟨equation, row, source⟩ := (choices_source_iff _ _ _ _ _ _ _ _).mp selected
  obtain ⟨reached, solved⟩ := selected_resolves source
  refine ⟨equation, reached, row, source, solved, ?_, rfl, rfl⟩
  exact selected_pending_absorbed
    (control := (cursor.readout (CurrentStore.normalize (CurrentStore.assignments snapshot))).control)
    (CurrentStore.prepareScoped?_certified prepared ranked)
    record source solved

/-- The same occurrence can be refused after earlier constraints are reached.
Presenting all operands through the prepared table cannot turn that refusal
into acceptance. The old world and pending alternatives are not rolled back. -/
theorem current_store_clause_refusal {Context : Type}
    (cursor : Cursor Context)
    {image : ImageOf CurrentStore.ContextualOperand}
    {operands : List CurrentStore.ContextualOperand} {snapshot : List CurrentStore.Row}
    {rank : String → Nat} (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal) (globals : List String) (contextual : List Atom)
    (prepared : CurrentStore.prepareScoped? globals image operands = some (snapshot,
      arguments ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ contextual))
    (ranked : CurrentStore.Ranked rank (CurrentStore.assignments snapshot))
    (record : cursor.control.bindings = bindingAtomEquations ⟨CurrentStore.assignments snapshot, []⟩)
    (occurrence : Nat) (equation : SpaceSemantics.Equation) (sameHead : equation.head = head) :
    let table := CurrentStore.normalize (CurrentStore.assignments snapshot)
    attempt cursor.control head arguments destination older occurrence equation = none ↔
      refine cursor.control.bindings (table.apply (.expression (.symbol head :: arguments)))
        (table.apply (freshPattern cursor.control occurrence equation)) = none :=
  presented_refusal_iff cursor.control head arguments destination older occurrence equation sameHead
    (CurrentStore.prepareScoped?_certified prepared ranked) record

/-- Once this selected branch has actually run to a scheduler cut, resumption
uses its reached cursor. No equation re-selection or world replay occurs. -/
theorem current_store_selected_pause {Context : Type}
    (policy : Policy) (program : SpaceSemantics.Program)
    (cursor residual : Cursor Context) (next : Control) (first second : Nat)
    (events : List Empty)
    (paused : (EagerDFS.Destination.machine policy program).run first
      {cursor with control := next} = (events, .exhausted residual)) :
    (EagerDFS.Destination.machine policy program).run (first + second)
      {cursor with control := next} =
      (events ++ ((EagerDFS.Destination.machine policy program).run second residual).1,
        ((EagerDFS.Destination.machine policy program).run second residual).2) :=
  selected_resume policy program cursor residual next first second events paused

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 10000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.ChoiceStoreControls
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.MetavariableFrameStore
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open EagerDFS.Destination
open EagerDFS.Destination.ClauseChoice
open Mettapedia.Logic.LP

private def pair (x y : Atom) : Atom := .expression [.symbol "Pair", x, y]
private def argument := Atom.var (CurrentStore.referenceName CurrentStore.Controls.callerX)
private def destination := Atom.var (CurrentStore.referenceName CurrentStore.Controls.callerOpen)
private def equation : SpaceSemantics.Equation := ⟨"f", [.var "x"], pair (.var "x") (.var "x")⟩
private def program : SpaceSemantics.Program := {equations := [equation, equation], declarations := []}
private def older : List Goal := [.invoke "println!" [pair argument argument] (Effects.boolean true)]
private def cursor : Cursor String :=
  { world := ⟨Effects.empty, [], [.symbol "earlier-effect"]⟩
    control :=
      { bindings := bindingAtomEquations ⟨CurrentStore.assignments CurrentStore.Controls.snapshot, []⟩
        goals := .invoke "f" [argument] destination :: older
        destination := destination
        reserved := {"older-sibling"} }
    context := "parent" }
private def table := CurrentStore.normalize (CurrentStore.assignments CurrentStore.Controls.snapshot)
private def operands : List CurrentStore.ContextualOperand :=
  [(CurrentStore.Controls.caller, .var "x"), (CurrentStore.Controls.caller, .var "open"),
   (CurrentStore.Controls.caller, .var "open"), (CurrentStore.Controls.caller, Effects.boolean true),
   (CurrentStore.Controls.caller, pair (.var "x") (.var "x"))]

attribute [local simp] CurrentStore.prepareScoped? CurrentStore.operandScope
  TypeSubst.typeVars TypeSubst.typeVarsList CurrentStore.prepare? CurrentStore.contextualRows?
  CurrentStore.qualifyRowsFrom? CurrentStore.qualifyRow? CurrentStore.qualify?
  Snapshot.rows Snapshot.entryRows Snapshot.Row.ofEntry EntryOf.initial entryEnv
  Snapshot.image_frameAt List.range_succ List.ofFn_succ CurrentStore.assignments
  CurrentStore.normalize CurrentStore.normalizeFrom TypeSubst.bind TypeSubst.apply
  TypeSubst.applyAssignment TypeSubst.lookup TypeSubst.erase renameTypeVars CurrentStore.nameIn
  MetavariableFrame.indexOf CurrentStore.referenceName CurrentStore.freeName Token.ref
  CurrentStore.Controls.caller CurrentStore.Controls.child CurrentStore.Controls.callerX
  CurrentStore.Controls.callerOpen CurrentStore.Controls.childX CurrentStore.Controls.image
  CurrentStore.Controls.snapshot

private theorem prepared : CurrentStore.prepareScoped? [] CurrentStore.Controls.image operands =
    some (CurrentStore.Controls.snapshot,
      [argument] ++ destination :: cursor.control.destination :: older.flatMap Goal.atoms ++ []) := by
  simp [operands, argument, destination, cursor, older, pair, Goal.atoms, Effects.boolean]

private def environment := (resolve cursor.control.bindings).getD (Subst.id signature)
private theorem resolved : resolve cursor.control.bindings = some environment := by
  obtain ⟨actual, result⟩ := certified_resolves CurrentStore.Controls.actual_certificate
  change resolve cursor.control.bindings = some actual at result
  simp [environment, result]

private def alternatives := choices program (cursor.readout table).control "f"
  ([argument].map (EagerDFS.Destination.read environment)) (table.apply destination)
  (older.map (Goal.readout table))
private def first := (alternatives.head?.map Prod.snd).getD cursor.control
private def execution (budget : Nat) :=
  (EagerDFS.Destination.machine .relational program).run budget {cursor with control := first}
private def answer := match (execution 48).2 with
  | .finished (.value value _, _) => some value
  | _ => none
private def output := ((observed (execution 48).2).map fun (state : EagerDFS.World × Control) => state.1.output)
private def resumedOutput := match (execution 5).2 with
  | .exhausted saved => ((observed
      ((EagerDFS.Destination.machine .relational program).run 43 saved).2).map fun (state : EagerDFS.World × Control) => state.1.output)
  | _ => none

#guard alternatives.map Prod.fst == [0, 1]
#guard answer == some (pair (.symbol "A") (.symbol "A"))
#guard output == some [.symbol "earlier-effect", pair (.symbol "A") (.symbol "A")]
#guard resumedOutput == output
#guard first.reserved == cursor.control.reserved
#guard CurrentStore.prepareScoped? [] CurrentStore.Controls.image
  [(⟨0, 4⟩, .var "x")] == none

theorem actual_scoped_invocation_request (later : Nat) :
    (EagerDFS.Destination.machine .relational program).run (later + 1) (cursor.readout table) =
      ([], .suspended (.invoke "f" ([argument].map (EagerDFS.Destination.read environment))
        (table.apply destination)) (cursor.readout table)) :=
  current_store_invocation_request .relational program cursor "f" [argument] destination older [] []
    prepared CurrentStore.Controls.actual_rank rfl rfl (by decide) resolved later

theorem every_actual_occurrence_has_joint_source_readout (occurrence : Nat) (next : Control)
    (selected : (occurrence, next) ∈ alternatives) :
    ∃ reached, resolve next.bindings = some reached ∧
      ∀ pending : List Atom,
        (pending.map table.apply).map (EagerDFS.Destination.read reached) =
          pending.map (EagerDFS.Destination.read reached) := by
  obtain ⟨_, equation, reached, _row, _source, solved, absorbed, _world, _context⟩ :=
    current_store_clause_selection .relational program cursor "f" [argument] destination older [] []
      prepared CurrentStore.Controls.actual_rank rfl rfl (by decide) resolved occurrence next selected 0
  exact ⟨reached, solved, absorbed⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.DestinationReturn.ChoiceStoreControls



set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Inspection keeps the complete saved allocator/scope pair. Source control
faults are suspended requests, never an erased `faulted` configuration. -/
def readback {Context : Type} : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary →
    Option (ScopedCursor Context)
  | .finished cursor | .exhausted cursor | .stuck cursor | .suspended _ cursor => some cursor
  | .faulted => none

/-- This compatibility equation identifies the unchanged historical profile.
It does not validate its old open-answer collection behavior. -/
theorem eager_step_unchanged (program : SpaceSemantics.Program) (source : EagerDFS.Configuration) :
    (EagerDFSStreaming.machine program .eager).step source = some (
      match EagerDFS.step program source with
      | some next => match EagerDFSProducer.emission source with
        | [] => .silent next
        | values => .publish values next
      | none => if EagerDFS.completed source then .finish source
        else match EagerDFS.fault source with
          | some reason => .call (.fault reason) source
          | none => .call .stopped source) := rfl

/-- The scheduler inspection is the constructed scope operation, with all
children and primitive requests retained by the one existing driver. -/
theorem step_scope {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step source =
      some (scopeStep policy program source) := rfl

/-- A budget split resumes the entire reached source cursor. Allocation,
collected occurrences, world updates and older scopes are not restarted. -/
theorem resume {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (first second : Nat) (source saved : ScopedCursor Context) (events : List CollectedAnswer)
    (paused : (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run first source =
      (events, .exhausted saved)) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (first + second) source =
      (events ++ ((EagerDFSStreaming.machine program (.scopedDestination Context policy)).run second saved).1,
        ((EagerDFSStreaming.machine program (.scopedDestination Context policy)).run second saved).2) :=
  (EagerDFSStreaming.machine program (.scopedDestination Context policy)).established_and_pending
    first second source saved events paused

/-- Completion of an empty root is distinct from an exhausted budget. The
already collected answer history and reached world remain in the verdict. -/
theorem empty_root_finishes {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (answers : List CollectedAnswer) (fuel : Nat) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, [⟨[], answers, none⟩]⟩) =
      ([], .finished (allocator, ⟨world, [⟨[], answers, none⟩]⟩)) := rfl

/-- A refused return consumes one alternative while retaining every older
choice. The premise is independent joint satisfiability, not a target result. -/
theorem refused_return {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (head : control.goals = .equate value destination :: older) :
    Refinement control.bindings value destination none ↔
      (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 1
        (allocator, ⟨world, scope :: parents⟩) =
        ([], .exhausted (allocator, ⟨world, {scope with frontier := pending} :: parents⟩)) := by
  rw [scope_refused_return_iff policy program allocator world scope parents control context origins
    pending value destination older frontier head]
  constructor
  · intro actual
    simp only [Machine.run, step_scope, actual]
  · intro actual
    cases refined : refine control.bindings value destination with
    | none =>
      exact scope_refused_return policy program allocator world scope parents control context origins
        pending value destination older frontier head ((refinement_iff _ _ _ _).mpr refined)
    | some bindings =>
      have stepped := scope_accepted_return policy program allocator world scope parents control context
        origins pending value destination older bindings frontier head ((refinement_iff _ _ _ _).mpr refined)
      simp only [Machine.run, step_scope, stepped] at actual
      have sizes := congrArg (fun result => readback result.2 |>.map fun next =>
        next.2.scopes.head?.map (fun (current : CollectionScope Context) => current.frontier.length)) actual
      simp [readback] at sizes

/-- A primitive source fault suspends at the exact reached world and control;
it cannot publish a partially collected list or skip a younger continuation. -/
theorem primitive_fault {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (environment : Environment) (reason : Effects.Fault) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke head arguments destination :: older)
    (resolved : resolve control.bindings = some environment) (known : StdLib.known head = true)
    (failed : StdLib.apply world.state head (arguments.map (read environment)) = .error reason) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .suspended (.fault reason) (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_primitive_fault policy program allocator world scope parents control context origins pending
      head arguments destination older environment reason frontier atCall resolved known failed]

/-- Every budget at an unresolved attached-work boundary retains that work,
all completed rows and the caller; it is not successful empty search. -/
theorem associated_work_retained {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (answers : List CollectedAnswer)
    (caller : CollectionCaller Context) (parent : CollectionScope Context)
    (parents : List (CollectionScope Context)) (answer : CollectedAnswer)
    (member : answer ∈ answers) (pending : answer.associated ≠ []) (fuel : Nat) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩) =
      ([], .suspended .associatedWork (allocator, ⟨world, ⟨[], answers, some caller⟩ :: parent :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scopeStep_pending_associated policy program allocator world answers caller parent parents answer member pending]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World ScopesValid)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Every finite prefix retains a properly nested source configuration. A
fault or request still has that exact saved configuration; no state is erased. -/
theorem run_scopes_valid {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes) :
    ∃ reached, readback ((EagerDFSStreaming.machine program
      (.scopedDestination Context policy)).run fuel source).2 = some reached ∧
      ScopesValid reached.2.scopes := by
  induction fuel generalizing source with
  | zero => exact ⟨source, rfl, valid⟩
  | succ fuel ih =>
    have kept := scopeStep_scopes_valid policy program source valid
    cases stepped : scopeStep policy program source with
    | silent next =>
      rw [stepped] at kept
      simpa only [Machine.run, step_scope, stepped] using ih next kept
    | publish events next =>
      rw [stepped] at kept
      simpa only [Machine.run, step_scope, stepped] using ih next kept
    | finish next =>
      rw [stepped] at kept
      exact ⟨next, by simp only [Machine.run, step_scope, stepped, readback], kept⟩
    | call request next =>
      rw [stepped] at kept
      exact ⟨next, by simp only [Machine.run, step_scope, stepped, readback], kept⟩
    | fail events =>
      rw [stepped] at kept
      exact False.elim kept

/-- Every published occurrence retains an independently satisfiable reached
constraint record. This follows the executed source branches over the whole
prefix, rather than asking a completion service for a certified answer. -/
theorem run_answer_models {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes)
    (answer : CollectedAnswer) (published : answer ∈
      ((EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel source).1) :
    ∃ environment, Solves environment answer.bindings := by
  induction fuel generalizing source with
  | zero => cases published
  | succ fuel ih =>
    have kept := scopeStep_scopes_valid policy program source valid
    cases stepped : scopeStep policy program source with
    | silent next =>
      rw [stepped] at kept
      exact ih next kept (by simpa only [Machine.run, step_scope, stepped] using published)
    | publish events next =>
      rw [stepped] at kept
      simp only [Machine.run, step_scope, stepped, List.mem_append] at published
      rcases published with here | later
      · obtain ⟨value, bindings, origins, environment, eventsEq, solved⟩ :=
          scope_published_source_model policy program source next events stepped
        rw [eventsEq] at here
        cases List.mem_singleton.mp here
        exact ⟨environment, solved⟩
      · exact ih next kept later
    | finish next => simp only [Machine.run, step_scope, stepped, List.not_mem_nil] at published
    | call request next => simp only [Machine.run, step_scope, stepped, List.not_mem_nil] at published
    | fail events =>
      rw [stepped] at kept
      exact False.elim kept

/-- Actual loading supplies the scope invariant for every later run prefix.
The loader and scheduler construct children; no completed child is an input. -/
theorem loaded_run {policy : Policy} (program : SpaceSemantics.Program)
    (allocator : Allocator) (core : List Atom) (cells : List (String × Atom))
    (input : List Atom) (control : Control) (context : List Atom)
    (source : ScopedCursor (Token × List Atom)) (fuel : Nat)
    (loaded : loadScoped? allocator core cells input control context = some source) :
    (∃ reached, readback ((EagerDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) policy)).run fuel source).2 = some reached ∧
      ScopesValid reached.2.scopes) ∧
    (∀ answer ∈ ((EagerDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) policy)).run fuel source).1,
      ∃ environment, Solves environment answer.bindings) := by
  have valid := loadScoped_scopes_valid allocator core cells input control context source loaded
  exact ⟨run_scopes_valid policy program fuel source valid,
    fun answer present => run_answer_models policy program fuel source valid answer present⟩

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped


set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 12000

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def program : SpaceSemantics.Program := {equations := [], declarations := []}
private def x : Atom := .var "x"
private def a : Atom := .var "a"
private def b : Atom := .var "b"
private def quote (atom : Atom) : Atom := .expression [.symbol "quote", atom]
private def collapse (atom : Atom) : Atom := .expression [.symbol "collapse", atom]
private def superpose (atoms : List Atom) : Atom := .expression [.symbol "superpose", .expression atoms]
private def pair (one two : Atom) : Atom := .expression [.symbol "Pair", one, two]
private def letE (pattern value body : Atom) : Atom := .expression [.symbol "let", pattern, value, body]
private def equality (one two : Atom) : Atom := .expression [.symbol "==", one, two]
private def seed (expression : Atom) : Control :=
  {bindings := [(.var "caller", .symbol "retained")]
   goals := [.evaluate expression (.var "out")]
   destination := .var "out"}
private def loaded (expression : Atom) (capacity : Nat := 12) :=
  loadScoped? (Allocator.empty capacity 3) [] [("remember", pair x x)] [] (seed expression) [x, x]
private def execute (expression : Atom) (fuel : Nat := 150) (capacity : Nat := 12) :=
  (loaded expression capacity).map fun state =>
    (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel state
private def answers (expression : Atom) (fuel : Nat := 150) :=
  (execute expression fuel).map fun result => result.1.map CollectedAnswer.value
private def saved (expression : Atom) (fuel : Nat) :=
  (execute expression fuel).bind fun result => Scoped.readback result.2
private def output (expression : Atom) (fuel : Nat := 150) :=
  (saved expression fuel).map fun state => state.2.world.output
private def finished (expression : Atom) :=
  (execute expression).map fun result => match result.2 with
    | .finished _ => true
    | _ => false

private def comparison := letE (.expression [a, b]) (collapse (superpose [x, x])) (equality a b)
#guard answers comparison == some [Effects.boolean false]
#guard finished comparison == some true

private def sharing := letE (.expression [pair a b]) (collapse (quote (pair x x))) (equality a b)
#guard answers sharing == some [Effects.boolean true]

private def nested := collapse (collapse (quote (pair x x)))
#guard (answers nested).map (fun values => match values with
  | [.expression [.expression [.expression [.symbol "Pair", .var one, .var two]]]] => one == two
  | _ => false) == some true

private def printEffect : Atom := .expression [.symbol "println!", .symbol "effect"]
private def effectful := collapse (letE (.var "unit") printEffect (quote (pair x x)))
#guard output effectful 8 == some [.symbol "effect"]
#guard output effectful 150 == some [.symbol "effect"]
private def resumedOutput : Option (List Atom) := do
  let paused ← execute effectful 8
  match paused.2 with
  | .exhausted state =>
    (Scoped.readback ((EagerDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) .relational)).run 142 state).2).map fun final => final.2.world.output
  | _ => none
#guard resumedOutput == some [.symbol "effect"]

private def refusedAfterEffect := collapse (superpose [
  letE (.var "unit") printEffect (letE (.symbol "A") (.symbol "B") (.symbol "unreachable")),
  quote (.symbol "survivor")])
#guard answers refusedAfterEffect == some [.expression [.symbol "survivor"]]
#guard output refusedAfterEffect == some [.symbol "effect"]
private def emptyCollection := collapse (superpose [])
#guard answers emptyCollection == some [.expression []]
private def literalError := collapse (quote (.expression [.symbol "Error", .symbol "data", .symbol "message"]))
#guard answers literalError == some [.expression [.expression [.symbol "Error", .symbol "data", .symbol "message"]]]
private def partialFault := collapse (superpose [quote (.symbol "first"),
  .expression [.symbol "%", .grounded (.int 1), .grounded (.int 0)]])
#guard (execute partialFault).map (fun result => (result.1.length, match result.2 with
  | .suspended (.fault .zeroDivisor) _ => true
  | _ => false)) == some (0, true)
#guard (saved partialFault 150).map (fun state => state.2.scopes.head?.map fun scope =>
  scope.collected.map CollectedAnswer.value) == some (some [.symbol "first"])
#guard (execute (collapse (quote x)) 30 1).map (fun result => match result.2 with
  | .suspended .allocation _ => true
  | _ => false) == some true

/-- A restarted child repeats its output; exact saved-cursor resumption above does not. -/
private def replayedOutput : Option (List Atom) := do
  let initial ← loaded effectful
  let reached ← saved effectful 8
  let replay := (initial.1, {initial.2 with world := reached.2.world})
  (Scoped.readback ((EagerDFSStreaming.machine program
    (.scopedDestination (Token × List Atom) .relational)).run 8 replay).2).map fun final => final.2.world.output
#guard replayedOutput == some [.symbol "effect", .symbol "effect"]
#guard output effectful 7 == some []

private def remembered := letE (.expression [a]) (collapse (quote x))
  (letE (pair b b) (.expression [.symbol "get-state", .symbol "remember"]) (equality a b))
#guard answers remembered == some [Effects.boolean false]
private def syntaxAndString := collapse (quote (pair x (.grounded (.string "slot:6"))))
#guard (answers syntaxAndString).map (fun values => match values with
  | [.expression [.expression [.symbol "Pair", .var _, .grounded (.string text)]]] => text == "slot:6"
  | _ => false) == some true

private def row : SpaceSemantics.Equation := ⟨"f", [x], pair x x⟩
private def repeatedProgram : SpaceSemantics.Program := {equations := [row, row], declarations := []}
private def repeatedRun := (loaded (.expression [.symbol "f", .symbol "B"])).map fun initial =>
  (EagerDFSStreaming.machine repeatedProgram (.scopedDestination (Token × List Atom) .relational)).run 60 initial
#guard repeatedRun.map (fun result => result.1.map CollectedAnswer.value) ==
  some [pair (.symbol "B") (.symbol "B"), pair (.symbol "B") (.symbol "B")]
#guard repeatedRun.map (fun result => result.1.map CollectedAnswer.occurrences) == some [[0], [1]]

private def delayed : ScopedCursor Unit := (Allocator.empty 4 3,
  ⟨⟨NamedSpaces.Store.new [] [], [], [.symbol "before"]⟩,
    [⟨[], [⟨x, [], [2], [pair x x]⟩], some (seed x, a, (), [1])⟩,
      ⟨[(seed (.symbol "older"), (), [0])], [], none⟩]⟩)
#guard match (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 20 delayed with
  | ([], .suspended .associatedWork saved) => saved.1 == delayed.1 &&
      saved.2.scopes.head?.map (fun scope => scope.collected.map CollectedAnswer.associated) == some [[pair x x]]
  | _ => false
#guard (execute comparison 0).map (fun result => match result.2 with
  | .exhausted _ => result.1.isEmpty
  | _ => false) == some true

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Controls

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The actual parse allocation consumes one transition. Every later budget
starts from its retained return constraint, so it cannot repeat the parser
or allocate another identity for the same result. -/
theorem parsed_return_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator next : Allocator) (token : Token) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text value destination : Atom) (older : List Goal) (environment : Environment) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (loaded : EagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) =
      .ok (some (next, token, value))) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel
        (next, ⟨world,
          {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩) := by
  simp only [Machine.run, step_scope,
    scope_parse_success policy program allocator next token world scope parents control context origins pending
      text value destination older environment frontier atCall resolved loaded]

/-- A named parse's one actual allocation remains in the saved cursor. The
next budget resumes the ordinary constraint-return path, not the parser. -/
theorem parsed_return_pending {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator next : Allocator) (token : Token) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text value destination : Atom) (older : List Goal) (environment : Environment)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (loaded : EagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) =
      .ok (some (next, token, value))) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 1
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .exhausted (next, ⟨world,
        {scope with frontier := primitiveWork control context origins destination older [value] ++ pending} :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_parse_success policy program allocator next token world scope parents control context origins pending
      text value destination older environment frontier atCall resolved loaded]

/-- Refusing an allocation retains the exact reached request, bindings, older
frontier and world at every positive budget. No partial parse result appears. -/
theorem parse_allocation_retained {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (text destination : Atom) (older : List Goal) (environment : Environment) (fuel : Nat)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atCall : control.goals = .invoke "parse" [text] destination :: older)
    (resolved : resolve control.bindings = some environment)
    (unserved : EagerDFS.Collection.SyntaxLoading.loadParsed? allocator
      (collectionSupport ⟨world, scope :: parents⟩) (read environment text) = .ok none) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run (fuel + 1)
      (allocator, ⟨world, scope :: parents⟩) =
      ([], .suspended .allocation (allocator, ⟨world, scope :: parents⟩)) := by
  simp only [Machine.run, step_scope,
    scope_parse_unserved policy program allocator world scope parents control context origins pending
      text destination older environment frontier atCall resolved unserved]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.NamedParseControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def program : SpaceSemantics.Program := {equations := [], declarations := []}
private def a : Atom := .var "a"
private def b : Atom := .var "b"
private def c : Atom := .var "c"
private def d : Atom := .var "d"
private def parse (text : String) : Atom := .expression [.symbol "parse", .grounded (.string text)]
private def letE (pattern value body : Atom) : Atom := .expression [.symbol "let", pattern, value, body]
private def equality (one two : Atom) : Atom := .expression [.symbol "==", one, two]
private def pair (one two : Atom) : Atom := .expression [.symbol "Pair", one, two]
private def seed (expression : Atom) : Control :=
  {bindings := [(.var "caller", .symbol "retained")], goals := [.evaluate expression (.var "out")], destination := .var "out"}
private def loaded (expression : Atom) (capacity : Nat := 12) :=
  loadScoped? (Allocator.empty capacity 4) [] [("remember", .symbol "initial")] [] (seed expression) []
private def execute (expression : Atom) (fuel : Nat := 180) (capacity : Nat := 12) := do
  let initial ← loaded expression capacity
  pure ((EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run fuel initial)
private def answers (expression : Atom) :=
  (execute expression).map fun result => result.1.map CollectedAnswer.value
private def saved (expression : Atom) (fuel : Nat) (capacity : Nat := 12) :=
  (execute expression fuel capacity).bind fun result => Scoped.readback result.2
private def output (expression : Atom) (fuel : Nat := 180) :=
  (saved expression fuel).map fun state => state.2.world.output
private def separate := letE a (parse "$x") (letE b (parse "$x") (equality a b))
#guard answers separate == some [Effects.boolean false]
#guard (execute separate).map (fun result => match result.2 with | .finished _ => true | _ => false) == some true
private def authored := letE a (parse "$x") (equality a (.var "x"))
#guard answers authored == some [Effects.boolean false]
private def within := letE (.var "parsed") (parse "(Pair $x $x)")
  (letE (pair a b) (.var "parsed") (equality a b))
#guard answers within == some [Effects.boolean true]
private def twoPairs := letE (.var "p") (parse "(Pair $x $x)")
  (letE (.var "q") (parse "(Pair $x $x)")
    (letE (pair a b) (.var "p")
      (letE (pair c d) (.var "q")
        (.expression [.symbol "Checks", equality a b, equality c d, equality a c]))))
#guard answers twoPairs == some [.expression [.symbol "Checks", Effects.boolean true, Effects.boolean true, Effects.boolean false]]
private def boundOne := letE a (parse "$x") (letE b (parse "$x")
  (letE a (.symbol "A") (equality a b)))
#guard answers boundOne == some [Effects.boolean false]
private def sharedBinding := letE (.var "p") (parse "(Pair $x $x)")
  (letE (pair a b) (.var "p") (letE a (.symbol "A") (equality b (.symbol "A"))))
#guard answers sharedBinding == some [Effects.boolean true]
private def rawSpelling := letE a (parse "$slot:0") (equality a (.var "slot:0"))
#guard answers rawSpelling == some [Effects.boolean false]
private def strings := letE (.var "p") (parse "(Pair $x \"$x\")")
  (letE (pair a b) (.var "p") (equality a b))
#guard answers strings == some [Effects.boolean false]
private def quotedSyntax := letE (.var "p") (parse "(quote $x)")
  (letE (.expression [.symbol "quote", a]) (.var "p") (equality a (.var "x")))
#guard answers quotedSyntax == some [Effects.boolean false]

private def printEffect : Atom := .expression [.symbol "println!", .symbol "effect"]
private def effectful := letE (.var "unit") printEffect separate
#guard output effectful 8 == some [.symbol "effect"]
#guard output effectful == some [.symbol "effect"]
private def resumed : Option (List Atom × List Atom) := do
  let paused ← execute effectful 8
  match paused.2 with
  | .exhausted state =>
    let completed := (EagerDFSStreaming.machine program
      (.scopedDestination (Token × List Atom) .relational)).run 172 state
    let final ← Scoped.readback completed.2
    pure ((paused.1 ++ completed.1).map CollectedAnswer.value, final.2.world.output)
  | _ => none
#guard resumed == some ([Effects.boolean false], [.symbol "effect"])

private def collected := letE (.expression [a, b])
  (.expression [.symbol "collapse", .expression [.symbol "superpose",
    .expression [parse "$x", parse "$x"]]]) (equality a b)
#guard answers collected == some [Effects.boolean false]
private def stored := letE a (parse "$x")
  (letE (.var "unit") (.expression [.symbol "change-state!", .symbol "remember", a])
    (letE b (parse "$x")
      (letE c (.expression [.symbol "get-state", .symbol "remember"]) (equality b c))))
#guard answers stored == some [Effects.boolean false]

private def noCapacity := execute effectful 180 1
#guard noCapacity.map (fun result => match result.2 with
  | .suspended .allocation state => (result.1.isEmpty, state.2.world.output)
  | _ => (false, [])) == some (true, [.symbol "effect"])
#guard noCapacity.map (fun result => match result.2 with
  | .suspended .allocation state =>
    match (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 20 state with
    | ([], .suspended .allocation same) =>
      same.1 == state.1 && same.2.world.output == state.2.world.output &&
        same.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1)) ==
          state.2.scopes.map (fun scope => scope.frontier.map (fun work => work.1))
    | _ => false
  | _ => false) == some true

private def malformed := letE (.var "unit") printEffect (parse "(")
#guard (execute malformed).map (fun result => match result.2 with
  | .suspended (.fault (.invalidArguments "parse")) state => (result.1.isEmpty, state.2.world.output)
  | _ => (false, [])) == some (true, [.symbol "effect"])

/- Anonymous source occurrences remain independent through actual parsing,
owned loading, pattern binding and the retained caller. -/
private def anonymous := letE (.var "p") (parse "(Pair $_ $_)")
  (letE (pair a b) (.var "p") (equality a b))
#guard answers anonymous == some [Effects.boolean false]
private def anonymousBinding := letE (.var "p") (parse "(Pair $_ $_)")
  (letE (pair a b) (.var "p") (letE a (.symbol "A") (equality b (.symbol "A"))))
#guard answers anonymousBinding == some [Effects.boolean false]

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.NamedParseControls


namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.OrderedCallControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private def pair (left right : Atom) : Atom := call "Pair" [left, right]
private def a : Atom := .symbol "A"
private def b : Atom := .symbol "B"
private def c : Atom := .symbol "C"
private def left : Atom := .symbol "Left"
private def right : Atom := .symbol "Right"
private def x : Atom := .var "x"
private def y : Atom := .var "y"
private def out : Atom := .var "out"
private def program : SpaceSemantics.Program :=
  {equations := [
    {head := "route", arguments := [a], body := left},
    {head := "other", arguments := [a], body := .symbol "Skipped"},
    {head := "route", arguments := [b], body := right},
    {head := "route", arguments := [a], body := left}], declarations := []}
private def control : Control :=
  {bindings := [(x, y)], goals := [.invoke "route" [x] out], destination := pair x out}
private def world : World := ⟨Effects.loaded program, [], []⟩
private def initial (allocator : Allocator) : ScopedCursor Unit :=
  (allocator, ⟨world, [⟨[(control, (), [])], [], none⟩]⟩)
private def execute (fuel : Nat) (source : ScopedCursor Unit) :=
  (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run fuel source


private def allocator : Allocator := Allocator.empty 0 0

#guard ((execute 14 (initial allocator)).1.map CollectedAnswer.value) ==
  [pair a left, pair b right, pair a left]
#guard ((execute 14 (initial allocator)).1.map CollectedAnswer.occurrences) == [[0], [2], [3]]
#guard (match (execute 14 (initial allocator)).2 with | .finished _ => true | _ => false)
#guard ((execute 14 (initial allocator)).1.map CollectedAnswer.value).length != 2

#guard ((execute 5 (initial allocator)).1.map CollectedAnswer.occurrences) == [[0]]
#guard ((Scoped.readback (execute 5 (initial allocator)).2).map fun saved =>
  saved.2.scopes.head?.map fun scope => scope.frontier.map (fun work => work.2.2)) ==
    some (some [[2], [3]])

private def older : ScopedCursor Unit :=
  (allocator, ⟨world, [⟨[(control, (), []),
    ({bindings := [], goals := [], destination := .symbol "Older"}, (), [99])], [], none⟩]⟩)
#guard ((execute 16 older).1.map CollectedAnswer.value) ==
  [pair a left, pair b right, pair a left, .symbol "Older"]

private def impossible : ScopedCursor Unit :=
  (allocator, ⟨world, [⟨[({control with bindings := [(x, c)]}, (), [])], [], none⟩]⟩)
#guard (execute 2 impossible).1.isEmpty
#guard (match (execute 2 impossible).2 with | .finished _ => true | _ => false)

private def collected : ScopedCursor Unit :=
  (Allocator.empty 8 1, ⟨world, [⟨[({control with
    goals := [.evaluate (call "collapse" [call "route" [x]]) out]}, (), [])], [], none⟩]⟩)
#guard (match (execute 30 collected).1.map CollectedAnswer.value with
  | [.expression [.symbol "Pair", .var _, .expression values]] => values == [left, right, left]
  | _ => false)
#guard (match (execute 30 collected).2 with | .finished _ => true | _ => false)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.OrderedCallControls

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Every finite budget leaves the recursive head active. No later answer is
published, no empty completion is invented, and saved scopes remain intact. -/
theorem dfs_loop_every_budget {Context : Type} (policy : Policy)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (pending : List (CollectionWork Context))
    (destination : Atom) (older : List Goal) (fuel : Nat) (source : ScopedCursor Context)
    (active : DFSLoop.Active allocator world scope parents pending destination older source) :
    ∃ saved,
      (EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Context policy)).run fuel source =
        ([], .exhausted saved) ∧
      DFSLoop.Active allocator world scope parents pending destination older saved := by
  induction fuel generalizing source with
  | zero => exact ⟨source, rfl, active⟩
  | succ fuel ih =>
      obtain ⟨next, stepped, nextActive⟩ :=
        DFSLoop.progress policy allocator world scope parents pending destination older source active
      obtain ⟨saved, resumed, stillActive⟩ := ih next nextActive
      refine ⟨saved, ?_, stillActive⟩
      have actual :
          (EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Context policy)).step source =
            some (.silent next) := by
        rw [step_scope, stepped]
      exact ((EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Context policy)).run_succ_silent actual).trans resumed

namespace DFSControls

/-- The same answer is immediately publishable when no recursive head blocks
it. This control has arbitrary payload, allocator and reached world. -/
theorem ready_answer_publishes (allocator : Allocator) (world : World) (value : Atom) :
    let control : Control := {bindings := [], goals := [], destination := value}
    let scope : CollectionScope Unit := ⟨[(control, (), [1])], [], none⟩
    let answer : CollectedAnswer := ⟨value, [], [1], []⟩
    scopeStep .relational DFSLoop.program (allocator, ⟨world, [scope]⟩) =
      .publish [answer] (allocator, ⟨world, [EagerDFS.Scope.record scope [] answer]⟩) := by
  dsimp only
  have resolved : resolve [] = some (Mettapedia.Logic.LP.Subst.id signature) := by
    simp [resolve, equations, Mettapedia.Logic.LP.unifyTotal]
  simpa only [EagerDFS.Scope.record, Option.isNone_none, ↓reduceIte, EagerDFS.Destination.read,
    Mettapedia.Logic.LP.Subst.applyTerm_id, decode_encode] using
    scope_terminal_value .relational DFSLoop.program allocator world
      (⟨[({bindings := [], goals := [], destination := value}, (), [1])], [], none⟩ : CollectionScope Unit)
      [] {bindings := [], goals := [], destination := value} () [1] []
      (Mettapedia.Logic.LP.Subst.id signature) rfl rfl resolved

/-- DFS is not fairness: a ready second alternative remains saved behind the
recursive first clause for every budget. The enclosing world and collection
rows are preserved, rather than the later alternative being discarded. -/
theorem ready_answer_starved (allocator : Allocator) (world : World) (value : Atom) (fuel : Nat) :
    let first : Control := {bindings := [], goals := [.invoke "dfs-loop" [] (.var "out")], destination := .var "out"}
    let later : CollectionWork Unit := ({bindings := [], goals := [], destination := value}, (), [1])
    let scope : CollectionScope Unit := ⟨[], [], none⟩
    let source : ScopedCursor Unit := (allocator, ⟨world, [{scope with frontier := [(first, (), [0]), later]}]⟩)
    ∃ saved,
      (EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Unit .relational)).run fuel source =
        ([], .exhausted saved) ∧
      DFSLoop.Active allocator world scope [] [later] (.var "out") [] saved := by
  dsimp only
  apply dfs_loop_every_budget .relational allocator world _ [] _ (.var "out") [] fuel _
  refine ⟨_, (), [0], rfl, ⟨[],Or.inl rfl⟩, Mettapedia.Logic.LP.Subst.id signature, ?_⟩
  intro pair present
  cases present

private def choice (value : Atom) : Atom := .expression [.symbol "superpose",
  .expression [DFSLoop.term, .expression [.symbol "quote", value]]]
private def choiceControl (value : Atom) : Control :=
  {bindings := [], goals := [.evaluate (choice value) (.var "out")], destination := .var "out"}
private def choiceStart (allocator : Allocator) (world : World) (value : Atom) : ScopedCursor Unit :=
  (allocator, ⟨world, [⟨[(choiceControl value, (), [])], [], none⟩]⟩)
private def firstControl (value : Atom) : Control :=
  {choiceControl value with goals := [.evaluate DFSLoop.term (.var "out")]}
private def laterWork (value : Atom) : CollectionWork Unit :=
  ({choiceControl value with goals := [.evaluate (.expression [.symbol "quote", value]) (.var "out")]}, (), [1])
private def choiceEntered (allocator : Allocator) (world : World) (value : Atom) : ScopedCursor Unit :=
  (allocator, ⟨world, [⟨[(firstControl value, (), [0]), laterWork value], [], none⟩]⟩)

/-- The authored source choice reaches the invariant through the actual
superpose rule, rather than starting from an assumed compiled frontier. -/
theorem authored_choice_diverges (allocator : Allocator) (world : World) (value : Atom) (fuel : Nat) :
    ∃ saved,
      (EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Unit .relational)).run fuel
        (choiceStart allocator world value) = ([], .exhausted saved) := by
  cases fuel with
  | zero => exact ⟨_, rfl⟩
  | succ fuel =>
      have entered : scopeStep .relational DFSLoop.program (choiceStart allocator world value) =
          .silent (choiceEntered allocator world value) := by
        simpa [choiceStart, choiceEntered, firstControl, laterWork, superposeWork] using
          scope_superpose_entry .relational DFSLoop.program allocator world
            (⟨[(choiceControl value, (), [])], [], none⟩ : CollectionScope Unit)
            [] (choiceControl value) () [] [] [DFSLoop.term, .expression [.symbol "quote", value]]
            (.var "out") [] rfl rfl
      have active : DFSLoop.Active allocator world (⟨[], [], none⟩ : CollectionScope Unit) []
          [laterWork value] (.var "out") [] (choiceEntered allocator world value) := by
        refine ⟨firstControl value, (), [0], rfl, ⟨[],Or.inr rfl⟩, Mettapedia.Logic.LP.Subst.id signature, ?_⟩
        intro pair present
        cases present
      obtain ⟨saved, following, _⟩ := dfs_loop_every_budget .relational allocator world _ []
        [laterWork value] (.var "out") [] fuel _ active
      refine ⟨saved, ?_⟩
      have actual : (EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Unit .relational)).step
          (choiceStart allocator world value) = some (.silent (choiceEntered allocator world value)) := by
        rw [step_scope, entered]
      exact ((EagerDFSStreaming.machine DFSLoop.program (.scopedDestination Unit .relational)).run_succ_silent actual).trans following

end DFSControls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped



/-!
## Independent scoped source derivations

The scoped source judgment supplies local syntax, complete equation coverage,
refinement and generative collection evidence. The common derivation algebra
composes these rules through arbitrary finite prefixes and recursive scopes.
There is no second executable evaluator or assumed whole-run source reply.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World ScopesValid)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- The independent scoped rules enable an actual source transition. Proper
source configurations have no rule for an absent machine transition. -/
def sourceRule {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (transition : Option (Source.ScopeAction Allocator Context)) : Prop :=
  ∃ action, transition = some action ∧ Source.ScopedStep Source.FreshOperations.owned policy program source action

theorem source_rule_execution {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (source : ScopedCursor Context) (transition : Option (Source.ScopeAction Allocator Context))
    (evidence : sourceRule policy program source transition) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step source = transition := by
  obtain ⟨action, rfl, evidence⟩ := evidence
  exact congrArg some evidence.execution

/-- Whole finite-prefix correspondence, with arbitrary nested collection,
open constraints, source occurrences, the reached world and saved requests.
It is constructed from local source laws and the existing scope invariant. -/
theorem source_run_iff_derivation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source : ScopedCursor Context) (valid : ScopesValid source.2.scopes)
    (events : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel source = (events, outcome) ↔
      Derivation (sourceRule policy program) fuel source events outcome := by
  refine Machine.run_iff_derivation
    (EagerDFSStreaming.machine program (.scopedDestination Context policy))
    (sourceRule policy program) (fun state => ScopesValid state.2.scopes)
    (source_rule_execution policy program) ?_ ?_ ?_ fuel source valid events outcome
  · intro state wellformed
    change sourceRule policy program state (some (scopeStep policy program state))
    exact ⟨_, rfl, (Source.scoped_step_iff_source policy program state wellformed _).mp rfl⟩
  · intro state next wellformed stepped
    have kept := scopeStep_scopes_valid policy program state wellformed
    have actual : scopeStep policy program state = .silent next := Option.some.inj stepped
    rw [actual] at kept
    exact kept
  · intro state events next wellformed stepped
    have kept := scopeStep_scopes_valid policy program state wellformed
    have actual : scopeStep policy program state = .publish events next := Option.some.inj stepped
    rw [actual] at kept
    exact kept

/-- Completed search uses the same derivation relation as prefixes and
requests. Completion is not inferred from absence of a result in a prefix. -/
theorem completed_iff_source {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (fuel : Nat) (source reached : ScopedCursor Context) (valid : ScopesValid source.2.scopes)
    (events : List CollectedAnswer) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel source =
      (events, .finished reached) ↔
    Derivation (sourceRule policy program) fuel source events (.finished reached) :=
  source_run_iff_derivation policy program fuel source valid events (.finished reached)

/-- Completed source searches agree even when their finite budgets differ.
The comparison includes ordered answer occurrences and the entire reached
configuration, rather than result membership or printed variable spellings. -/
theorem completed_results_unique {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    {first second : Nat} {source firstEnd secondEnd : ScopedCursor Context}
    {events other : List CollectedAnswer} (valid : ScopesValid source.2.scopes)
    (left : Derivation (sourceRule policy program) first source events (.finished firstEnd))
    (right : Derivation (sourceRule policy program) second source other (.finished secondEnd)) :
    events = other ∧ firstEnd = secondEnd := by
  let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
  have firstRun : interpreter.run first source = (events, .finished firstEnd) :=
    (completed_iff_source policy program first source firstEnd valid events).mpr left
  have secondRun : interpreter.run second source = (other, .finished secondEnd) :=
    (completed_iff_source policy program second source secondEnd valid other).mpr right
  have firstTotal : interpreter.run (first + second) source = (events, .finished firstEnd) :=
    (interpreter.run_stable first second source (by simp [firstRun])).trans firstRun
  have secondTotal : interpreter.run (first + second) source = (other, .finished secondEnd) := by
    simpa only [Nat.add_comm] using
      (interpreter.run_stable second first source (by simp [secondRun])).trans secondRun
  have same := firstTotal.symm.trans secondTotal
  exact ⟨congrArg Prod.fst same, Outcome.finished.inj (congrArg Prod.snd same)⟩

namespace DFSControls

/-- The source derivation itself denies completed failure or success behind
the divergent first alternative, even though the second answer is retained. -/
theorem source_choice_no_completion (allocator : Allocator) (world : World) (value : Atom) (fuel : Nat) :
    ¬∃ events reached, Derivation (sourceRule .relational DFSLoop.program) fuel
      (choiceStart allocator world value) events (.finished reached) := by
  rintro ⟨events, reached, completed⟩
  have valid : ScopesValid (choiceStart allocator world value).2.scopes := .root _ _
  have actual := (completed_iff_source .relational DFSLoop.program fuel _ reached valid events).mpr completed
  obtain ⟨saved, pending⟩ := authored_choice_diverges allocator world value fuel
  rw [pending] at actual
  cases actual

end DFSControls
end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Once a first child answer reaches its commit/restore boundary, three
inspections discard exactly the younger alternatives, restore the delimiter
and record the answer. No execution or termination premise concerns either
discarded siblings or older alternatives. Root scopes publish immediately;
collection scopes retain the answer internally. The whole reached world and
allocator are unchanged. -/
theorem commit_first_answer {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (younger kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (environment : Environment)
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept)
    (atGoal : control.goals = [.commit,.restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length)
    (resolved : resolve control.bindings = some environment) :
    let answer : CollectedAnswer := ⟨read environment control.destination, control.bindings, origins, []⟩
    let after : ScopedCursor Context := (allocator,⟨world,EagerDFS.Scope.record scope kept answer :: parents⟩)
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run 3
      (allocator,⟨world,scope :: parents⟩) =
      (if scope.caller.isNone then [answer] else [], .exhausted after) := by
  let stopped : Control := {control with goals := [.restoreCommit previousBoundary]}
  let returned : Control := {control with goals := [],cutBoundary := previousBoundary}
  let scope₁ := {scope with frontier := (stopped,context,origins) :: kept}
  let scope₂ := {scope with frontier := (returned,context,origins) :: kept}
  have committed : scopeStep policy program (allocator,⟨world,scope :: parents⟩) =
      .silent (allocator,⟨world,scope₁ :: parents⟩) :=
    scope_commit_split policy program allocator world scope parents control context origins younger kept
      [.restoreCommit previousBoundary] frontier atGoal boundary
  have restored : scopeStep policy program (allocator,⟨world,scope₁ :: parents⟩) =
      .silent (allocator,⟨world,scope₂ :: parents⟩) := by
    simp [scopeStep,scope₁,scope₂,stopped,returned,enterCollapse?,enterSuperpose?,
      EagerDFS.Destination.machine,installChild,retainChild]
  have published : scopeStep policy program (allocator,⟨world,scope₂ :: parents⟩) =
      (let answer : CollectedAnswer := ⟨read environment control.destination,control.bindings,origins,[]⟩
       let after : ScopedCursor Context := (allocator,⟨world,EagerDFS.Scope.record scope kept answer :: parents⟩)
       if scope.caller.isNone then .publish [answer] after else .silent after) := by
    simp [scopeStep,scope₂,returned,enterCollapse?,enterSuperpose?,
      EagerDFS.Destination.machine,resolved,installChild,EagerDFS.Scope.record]
  have first : (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step
      (allocator,⟨world,scope :: parents⟩) = some (.silent (allocator,⟨world,scope₁ :: parents⟩)) := by
    rw [step_scope,committed]
  have second : (EagerDFSStreaming.machine program (.scopedDestination Context policy)).step
      (allocator,⟨world,scope₁ :: parents⟩) = some (.silent (allocator,⟨world,scope₂ :: parents⟩)) := by
    rw [step_scope,restored]
  rw [(EagerDFSStreaming.machine program (.scopedDestination Context policy)).run_succ_silent first,
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run_succ_silent second]
  cases caller : scope.caller <;>
    simp [EagerDFSStreaming.machine,Machine.run,published,caller]

/-- The bounded commit prefix has an independent scoped source derivation
from every properly nested input. It needs no completion evidence for the
discarded child frontier or the retained outer frontier. -/
theorem commit_first_answer_source {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (younger kept : List (CollectionWork Context)) (previousBoundary : Nat)
    (environment : Environment)
    (valid : EagerDFS.ScopesValid (scope :: parents))
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept)
    (atGoal : control.goals = [.commit,.restoreCommit previousBoundary])
    (boundary : control.cutBoundary = kept.length)
    (resolved : resolve control.bindings = some environment) :
    let answer : CollectedAnswer := ⟨read environment control.destination, control.bindings, origins, []⟩
    let after : ScopedCursor Context := (allocator,⟨world,EagerDFS.Scope.record scope kept answer :: parents⟩)
    Derivation (sourceRule policy program) 3 (allocator,⟨world,scope :: parents⟩)
      (if scope.caller.isNone then [answer] else []) (.exhausted after) :=
  (source_run_iff_derivation policy program 3 _ valid _ _).mp
    (commit_first_answer policy program allocator world scope parents control context origins younger kept
      previousBoundary environment frontier atGoal boundary resolved)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.CommitControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks

private def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
private def quote (value : Atom) : Atom := call "quote" [value]
private def choice (values : List Atom) : Atom := call "superpose" [.expression values]
private def once (value : Atom) : Atom := call "once" [value]
private def bind (pattern value body : Atom) : Atom := call "let" [pattern,value,body]
private def a : Atom := .symbol "A"
private def b : Atom := .symbol "B"
private def c : Atom := .symbol "C"
private def outer : Atom := .symbol "Outer"
private def cut : Atom := call "cut" []
private def program : SpaceSemantics.Program :=
  {equations := [
    {head := "f",arguments := [],body := bind (.var "ignored") cut (quote a)},
    {head := "f",arguments := [],body := quote b},
    {head := "g",arguments := [],body := once (choice [quote a,quote b])},
    {head := "g",arguments := [],body := quote c},
    {head := "h",arguments := [],body := bind (.var "ignored") cut (call "empty" [])},
    {head := "h",arguments := [],body := quote b},
    {head := "dfs-loop",arguments := [],body := call "dfs-loop" []}],declarations := []}
private def loaded (expression : Atom) :=
  loadScoped? (Allocator.empty 8 2) [] [] []
    {bindings := [],goals := [.evaluate expression (.var "out")],destination := .var "out"} []
private def execute (expression : Atom) (policy : Policy := .relational) (fuel : Nat := 80) :=
  (loaded expression).map fun source =>
    (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) policy)).run fuel source
private def answers (expression : Atom) (policy : Policy := .relational) :=
  (execute expression policy).map fun result => result.1.map CollectedAnswer.value
private def finished (expression : Atom) (policy : Policy := .relational) :=
  (execute expression policy).map fun result => match result.2 with | .finished _ => true | _ => false
private def reachedOutput (expression : Atom) (fuel : Nat := 80) :=
  (execute expression .relational fuel).bind fun result =>
    (Scoped.readback result.2).map fun saved => saved.2.world.output

-- Inner commitment leaves the older outer choice intact.
private def nested := choice [once (choice [quote a,quote b]),quote outer]
#guard answers nested == some [a,outer]
#guard answers nested .eagerValue == some [a,outer]
#guard finished nested == some true
#guard answers nested != some [a]

-- A predicate cut removes that predicate's later clauses, not its caller.
#guard answers (choice [call "f" [],quote outer]) == some [a,outer]
#guard answers (choice [call "f" [],quote outer]) .eagerValue == some [a,outer]
#guard answers (call "g" []) == some [a,c]
#guard answers (call "h" []) == some []
#guard finished (call "h" []) == some true
#guard answers (choice [once (call "empty" []),quote outer]) == some [outer]

private def correlated := bind (call "Pair" [.var "left",.var "right"])
  (once (choice [quote (call "Pair" [.var "x",.var "x"]),quote (call "Pair" [.var "y",.var "z"])]))
  (call "==" [.var "left",.var "right"])
#guard answers correlated == some [Effects.boolean true]

-- A cut under quotation is ordinary data; collection has its own delimiter.
#guard answers (choice [quote cut,quote outer]) == some [cut,outer]
#guard answers (choice [call "collapse" [choice [bind (.var "ignored") cut (quote a),quote b]],quote outer]) ==
  some [.expression [a],outer]

-- Once need not exhaust the alternatives after its first success.
private def valueThenLoop := choice [quote a,call "dfs-loop" []]
#guard answers (once valueThenLoop) == some [a]
#guard finished (once valueThenLoop) == some true
#guard finished (call "collapse" [valueThenLoop]) == some false

private def effectful := once (bind (.var "ignored") (call "println!" [.symbol "committed"])
  (choice [quote a,quote b]))
#guard answers effectful == some [a]
#guard reachedOutput effectful == some [.symbol "committed"]

private def effectPause := (execute effectful .relational 9).bind fun result => Scoped.readback result.2
private def effectResume := effectPause.map fun saved =>
  (EagerDFSStreaming.machine program (.scopedDestination (Token × List Atom) .relational)).run 80 saved
#guard reachedOutput effectful 9 == some [.symbol "committed"]
#guard (execute effectful .relational 9).map (fun result => match result.2 with
  | .exhausted _ => true | _ => false) == some true
#guard effectResume.map (fun result => result.1.map CollectedAnswer.value) == some [a]
#guard (effectResume.bind fun result => Scoped.readback result.2).map
  (fun saved => saved.2.world.output) == some [.symbol "committed"]

private def cutProbe (retained : Nat) : ScopedCursor Unit :=
  (Allocator.empty 0 0,⟨⟨Effects.empty,[],[]⟩,
    [⟨[({bindings := [],goals := [.commit,.restoreCommit 0],destination := a,cutBoundary := retained},(),[0]),
       ({bindings := [],goals := [],destination := outer},(),[1])],[],none⟩]⟩)
private def answerA : CollectedAnswer := ⟨a,[],[0],[]⟩
private def answerOuter : CollectedAnswer := ⟨outer,[],[1],[]⟩
private def cutFinished (answers : List CollectedAnswer) : ScopedCursor Unit :=
  (Allocator.empty 0 0,⟨⟨Effects.empty,[],[]⟩,[⟨[],answers,none⟩]⟩)

private theorem cut_run_exact (protectOuter : Bool) :
    (EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 5
        (cutProbe (if protectOuter then 1 else 0)) =
      (answerA :: (if protectOuter then [answerOuter] else []),
        .finished (cutFinished (answerA :: (if protectOuter then [answerOuter] else [])))) := by
  cases protectOuter <;>
    simp [EagerDFSStreaming.machine,Machine.run,scopeStep,enterCollapse?,enterSuperpose?,
      EagerDFS.Destination.machine,installChild,retainChild,cutProbe,cutFinished,EagerDFS.Scope.record,
      resolve,equations,Mettapedia.Logic.LP.unifyTotal,EagerDFS.Destination.read,encode,decode,
      Mettapedia.Logic.LP.Subst.applyTerm,Mettapedia.Logic.LP.Subst.id,answerA,answerOuter,a,outer]

/-- The independent source derivation retains the older outer occurrence. -/
theorem protected_cut_source :
    Derivation (sourceRule .relational program) 5 (cutProbe 1) [answerA,answerOuter]
      (.finished (cutFinished [answerA,answerOuter])) := by
  apply (completed_iff_source .relational program 5 _ _ (.root _ _) _).mp
  exact cut_run_exact true

/-- The same current operands may instead be inside the delimiter. -/
theorem local_cut_source :
    Derivation (sourceRule .relational program) 5 (cutProbe 0) [answerA]
      (.finished (cutFinished [answerA])) := by
  apply (completed_iff_source .relational program 5 _ _ (.root _ _) _).mp
  exact cut_run_exact false

/-- Forgetting the delimiter changes public answer occurrences, not just
internal representation. -/
theorem delimiter_changes_observation :
    ((EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 5 (cutProbe 0)).1 ≠
      ((EagerDFSStreaming.machine program (.scopedDestination Unit .relational)).run 5 (cutProbe 1)).1 := by
  rw [(completed_iff_source .relational program 5 _ _ (.root _ _) _).mpr local_cut_source,
    (completed_iff_source .relational program 5 _ _ (.root _ _) _).mpr protected_cut_source]
  intro same
  have lengths := congrArg List.length same
  simp only [List.length_cons,List.length_nil] at lengths
  omega

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.CommitControls

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ProtectedContinuation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Adding an older continuation increases the saved argument-return suffix
length. Choice-stack delimiters count alternatives and are unchanged. -/
def shift (extra : Nat) : Goal → Goal
  | .argumentReturn value destination depth => .argumentReturn value destination (depth + extra)
  | goal => goal

@[simp] theorem shift_atoms (extra : Nat) (goal : Goal) :
    (shift extra goal).atoms = goal.atoms := by
  cases goal <;> rfl

/-- The finite support of a saved goal suffix, including all its destinations. -/
def names (goals : List Goal) : Finset String :=
  (goals.flatMap Goal.atoms).foldl (fun found atom => found ∪ (encode atom).freeVars) ∅

/-- Attach source work without replacing reached equations, root destination,
reserved caller names, or the predicate's choice delimiter. -/
def attach (suffix : List Goal) (control : Control) : Control :=
  {control with goals := control.goals.map (shift suffix.length) ++ suffix}

private theorem fold_names (atoms : List Atom) (initial : Finset String) :
    atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) initial =
      initial ∪ atoms.foldl (fun found atom => found ∪ (encode atom).freeVars) ∅ := by
  induction atoms generalizing initial with
  | nil => simp
  | cons atom atoms ih =>
      rw [List.foldl_cons, ih]
      conv_rhs => rw [List.foldl_cons, Finset.empty_union, ih]
      exact Finset.union_assoc _ _ _

@[simp] theorem shift_atoms_list (extra : Nat) (goals : List Goal) :
    (goals.map (shift extra)).flatMap Goal.atoms = goals.flatMap Goal.atoms := by
  simp only [List.flatMap_map, shift_atoms]

theorem attach_support (suffix : List Goal) (control : Control) :
    (attach suffix control).support = control.support ∪ names suffix := by
  simp only [attach, Control.support, List.flatMap_append, shift_atoms_list,
    List.foldl_append, names]
  rw [fold_names]
  ac_rfl

/-- Protecting the suffix at the root makes its later attachment invisible to
the allocator. It remains present as actual pending source work. -/
theorem attach_support_eq (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) :
    (attach suffix control).support = control.support := by
  rw [attach_support, Finset.union_eq_left]
  exact protectedNames.trans Finset.subset_union_left

theorem attach_freshName (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (index : Nat) :
    freshName (attach suffix control) index = freshName control index := by
  simp only [freshName, attach_support_eq suffix control protectedNames]

theorem attach_freshSlots (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (count : Nat) :
    freshSlots (attach suffix control) count = freshSlots control count := by
  simp only [freshSlots, attach_freshName suffix control protectedNames]

@[simp] theorem attach_replace (suffix : List Goal) (control : Control) (goals : List Goal) :
    attach suffix (replace control goals) =
      replace (attach suffix control) (goals.map (shift suffix.length) ++ suffix) := rfl

@[simp] theorem attach_bindings (suffix : List Goal) (control : Control) :
    (attach suffix control).bindings = control.bindings := rfl

@[simp] theorem attach_destination (suffix : List Goal) (control : Control) :
    (attach suffix control).destination = control.destination := rfl

@[simp] theorem attach_reserved (suffix : List Goal) (control : Control) :
    (attach suffix control).reserved = control.reserved := rfl

theorem attach_injective (suffix : List Goal) : Function.Injective (attach suffix) := by
  intro first second same
  cases first with
  | mk firstBindings firstGoals firstDestination firstReserved firstBoundary =>
      cases second with
      | mk secondBindings secondGoals secondDestination secondReserved secondBoundary =>
          simp only [attach, Control.mk.injEq, List.append_cancel_right_eq] at same
          obtain ⟨bindings, goals, destination, reserved, boundary⟩ := same
          have shifted : Function.Injective (shift suffix.length) := by
            intro left right same
            cases left <;> cases right <;> simp_all [shift]
          have goalEq := List.map_injective_iff.mpr shifted goals
          cases bindings
          cases goalEq
          cases destination
          cases reserved
          cases boundary
          rfl

/-- A return delimiter still selects exactly the original older suffix,
followed by the newly attached continuation. Repeated goals stay repeated. -/
theorem shifted_caller_suffix (suffix younger older : List Goal) :
    callerSuffix? (older.length + suffix.length)
        ((younger ++ older).map (shift suffix.length) ++ suffix) =
      some (older.map (shift suffix.length) ++ suffix) := by
  rw [List.map_append, List.append_assoc]
  simpa only [List.length_append, List.length_map] using
    callerSuffix?_split (younger.map (shift suffix.length))
      (older.map (shift suffix.length) ++ suffix)

theorem shift_letGoals (extra : Nat) (policy : Policy)
    (program : SpaceSemantics.Program) (pattern producer body output joined : Atom) :
    (letGoals policy program pattern producer body output joined).map (shift extra) =
      letGoals policy program pattern producer body output joined := by
  cases policy with
  | eagerValue => rfl
  | relational => simp only [letGoals]; split <;> rfl

theorem shift_dataGoals (extra : Nat) (policy : Policy)
    (children slots : List Atom) (destination : Atom) :
    (dataGoals policy children slots destination).map (shift extra) =
      dataGoals policy children slots destination := by
  cases policy <;> simp only [dataGoals, List.map_cons, List.map_append, List.map_map,
    Function.comp_def, shift, List.map_nil]

theorem shift_callArguments (extra : Nat) (program : SpaceSemantics.Program)
    (head : String) (arguments slots : List Atom) :
    ((callArguments program head arguments slots).1).map (shift extra) =
      (callArguments program head arguments slots).1 := by
  unfold callArguments
  generalize (arguments.zip slots).zipIdx = work
  have invariant : ∀ (work : List ((Atom × Atom) × Nat)) (pending : List Goal) (ready : List Atom),
      pending.map (shift extra) = pending →
      ((work.foldl (fun (pending, ready) ((argument, slot), index) =>
        if Eval.argumentIsRaw program head index then (pending, ready ++ [argument])
        else (pending ++ [.evaluate argument slot], ready ++ [slot])) (pending, ready)).1).map (shift extra) =
        (work.foldl (fun (pending, ready) ((argument, slot), index) =>
          if Eval.argumentIsRaw program head index then (pending, ready ++ [argument])
          else (pending ++ [.evaluate argument slot], ready ++ [slot])) (pending, ready)).1 := by
    intro work
    induction work with
    | nil => intro pending ready fixed; exact fixed
    | cons row work ih =>
        intro pending ready fixed
        rcases row with ⟨⟨argument, slot⟩, index⟩
        simp only [List.foldl_cons]
        split
        · exact ih _ _ fixed
        · apply ih
          simp only [List.map_append, fixed, List.map_cons, List.map_nil, shift]
  exact invariant work [] [] rfl

/-- Independent source expansion commutes with an already protected caller
suffix. This covers every payload shape at once and preserves the actual
reached equation record. -/
theorem prepared_attach {policy : Policy} {program : SpaceSemantics.Program}
    {control next : Control} {destination expression : Atom} {older : List Goal}
    (source : Source.Prepared policy program control destination older expression next)
    (suffix : List Goal) (protectedNames : names suffix ⊆ control.reserved) :
    Source.Prepared policy program (attach suffix control) destination
      (older.map (shift suffix.length) ++ suffix) expression (attach suffix next) := by
  have fresh := attach_freshName suffix control protectedNames 0
  have slots := attach_freshSlots suffix control protectedNames
  cases source with
  | variableValue name => exact .variableValue name
  | symbol name => exact .symbol name
  | grounded value => exact .grounded value
  | quotation value => exact .quotation value
  | binding pattern producer body =>
      simpa only [attach_replace, List.map_append, shift_letGoals, fresh, List.append_assoc] using
        (Source.Prepared.binding (policy := policy) (program := program) (control := attach suffix control)
          (destination := destination) (older := older.map (shift suffix.length) ++ suffix) pattern producer body)
  | cut => exact .cut
  | once child => exact .once child
  | conditional condition yes no =>
      simpa only [attach_replace, List.map_cons, shift, fresh, List.cons_append] using
        (Source.Prepared.conditional (policy := policy) (program := program) (control := attach suffix control)
          (destination := destination) (older := older.map (shift suffix.length) ++ suffix) condition yes no)
  | conditionalWithoutElse condition yes =>
      simpa only [attach_replace, List.map_cons, shift, fresh, List.cons_append] using
        (Source.Prepared.conditionalWithoutElse (policy := policy) (program := program) (control := attach suffix control)
          (destination := destination) (older := older.map (shift suffix.length) ++ suffix) condition yes)
  | application head arguments ordinary declared =>
      simpa only [attach_replace, List.map_append, shift_callArguments, List.map_cons,
        List.map_nil, shift, slots, List.append_assoc] using
        (Source.Prepared.application (policy := policy) (program := program) (control := attach suffix control)
          (destination := destination) (older := older.map (shift suffix.length) ++ suffix)
          head arguments ordinary declared)
  | construction head arguments ordinary data =>
      cases policy with
      | relational =>
          simpa only [attach_replace, List.map_cons, List.map_append, List.map_map,
            Function.comp_def, shift, slots, List.map_nil, List.append_assoc] using
            (Source.Prepared.construction (policy := .relational) (program := program) (control := attach suffix control)
              (destination := destination) (older := older.map (shift suffix.length) ++ suffix)
              head arguments ordinary data)
      | eagerValue =>
          simpa only [attach_replace, List.map_cons, List.map_append, List.map_map,
            Function.comp_def, shift, slots, List.map_nil, List.append_assoc] using
            (Source.Prepared.construction (policy := .eagerValue) (program := program) (control := attach suffix control)
              (destination := destination) (older := older.map (shift suffix.length) ++ suffix)
              head arguments ordinary data)
  | tuple children noHead =>
      simpa only [attach_replace, List.map_append, shift_dataGoals, slots, List.append_assoc] using
        (Source.Prepared.tuple (policy := policy) (program := program) (control := attach suffix control)
          (destination := destination) (older := older.map (shift suffix.length) ++ suffix) children noHead)

theorem attach_freshPattern (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (occurrence : Nat)
    (equation : SpaceSemantics.Equation) :
    ClauseChoice.freshPattern (attach suffix control) occurrence equation =
      ClauseChoice.freshPattern control occurrence equation := by
  have renamer : ClauseChoice.rename (attach suffix control) occurrence (ClauseChoice.clauseAtoms equation) =
      ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation) := by
    funext name
    exact attach_freshName suffix control protectedNames _
  exact congrArg (fun rename => HE.Spec.Type.RuntimeRefinement.renameTypeVars rename (ClauseChoice.pattern equation)) renamer

theorem attach_freshBody (suffix : List Goal) (control : Control)
    (protectedNames : names suffix ⊆ control.reserved) (occurrence : Nat)
    (equation : SpaceSemantics.Equation) :
    ClauseChoice.freshBody (attach suffix control) occurrence equation =
      ClauseChoice.freshBody control occurrence equation := by
  have renamer : ClauseChoice.rename (attach suffix control) occurrence (ClauseChoice.clauseAtoms equation) =
      ClauseChoice.rename control occurrence (ClauseChoice.clauseAtoms equation) := by
    funext name
    exact attach_freshName suffix control protectedNames _
  exact congrArg (fun rename => HE.Spec.Type.RuntimeRefinement.renameTypeVars rename equation.body) renamer

/-- Each source position makes the same match/refusal decision. The accepted
branch keeps its reached equations and receives the complete caller suffix. -/
theorem decision_attach {program : SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {occurrence : Nat} {result : Option Control}
    (source : ClauseChoice.Decision program control head arguments destination older occurrence result)
    (suffix : List Goal) (protectedNames : names suffix ⊆ control.reserved) :
    ClauseChoice.Decision program (attach suffix control) head arguments destination
      (older.map (shift suffix.length) ++ suffix) occurrence (result.map (attach suffix)) := by
  cases source with
  | other equation row different => exact .other equation row different
  | refused equation row sameHead incompatible =>
      apply ClauseChoice.Decision.refused equation row sameHead
      simpa only [attach_bindings, attach_freshPattern suffix control protectedNames] using incompatible
  | selected equation bindings row sameHead compatible =>
      have refined : Refinement (attach suffix control).bindings
          (.expression (.symbol head :: arguments))
          (ClauseChoice.freshPattern (attach suffix control) occurrence equation) (some bindings) := by
        simpa only [attach_bindings, attach_freshPattern suffix control protectedNames] using compatible
      have selected := (ClauseChoice.Decision.selected (program := program) (control := attach suffix control)
          (head := head) (arguments := arguments) (destination := destination)
          (older := older.map (shift suffix.length) ++ suffix) equation bindings row sameHead refined)
      rw [attach_freshBody suffix control protectedNames] at selected
      simpa only [Option.map_some, attach, List.map_cons, shift, List.cons_append] using selected

/-- Transport a complete source scan, including every omitted position's
refusal. This is list transport, so duplicate accepted occurrences survive. -/
theorem frontier_attach {program : SpaceSemantics.Program} {control : Control}
    {head : String} {arguments : List Atom} {destination : Atom} {older : List Goal}
    {positions : List Nat} {answers : List (Nat × Control)}
    (source : ClauseChoice.Frontier program control head arguments destination older positions answers)
    (suffix : List Goal) (protectedNames : names suffix ⊆ control.reserved) :
    ClauseChoice.Frontier program (attach suffix control) head arguments destination
      (older.map (shift suffix.length) ++ suffix) positions
      (answers.map fun row => (row.1, attach suffix row.2)) := by
  induction source with
  | nil => exact .nil
  | skip decision _ ih => exact .skip (decision_attach decision suffix protectedNames) ih
  | keep decision _ ih => exact .keep (decision_attach decision suffix protectedNames) ih

/-- Full scans reflect as well as preserve. No source position may disappear
merely because the caller continuation was represented outside its body. -/
theorem frontier_attach_iff (program : SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
    (positions : List Nat) (valid : ∀ occurrence ∈ positions, occurrence < program.equations.length)
    (answers : List (Nat × Control)) (suffix : List Goal)
    (protectedNames : names suffix ⊆ control.reserved) :
    ClauseChoice.Frontier program (attach suffix control) head arguments destination
        (older.map (shift suffix.length) ++ suffix) positions
        (answers.map fun row => (row.1, attach suffix row.2)) ↔
      ClauseChoice.Frontier program control head arguments destination older positions answers := by
  constructor
  · intro target
    let original := positions.filterMap fun occurrence =>
      (ClauseChoice.trial program control head arguments destination older occurrence).map (occurrence, ·)
    have originalSource : ClauseChoice.Frontier program control head arguments destination older positions original :=
      (ClauseChoice.frontier_iff_scan program control head arguments destination older positions valid original).mpr rfl
    have mapped := frontier_attach originalSource suffix protectedNames
    have same := ClauseChoice.Frontier.unique valid mapped target
    have injective : Function.Injective (fun row : Nat × Control => (row.1, attach suffix row.2)) := by
      intro first second same
      rcases first with ⟨firstIndex, firstControl⟩
      rcases second with ⟨secondIndex, secondControl⟩
      change (firstIndex, attach suffix firstControl) = (secondIndex, attach suffix secondControl) at same
      obtain ⟨rfl, controls⟩ := Prod.mk.inj same
      exact Prod.ext rfl (attach_injective suffix controls)
    have equal := List.map_injective_iff.mpr injective same
    exact equal ▸ originalSource
  · intro source
    exact frontier_attach source suffix protectedNames

/-- Source occurrence paths and reached records remain positional under the
whole scan transport; identical clauses are not identified. -/
theorem attached_frontier_observations (answers : List (Nat × Control)) (suffix : List Goal) :
    (answers.map fun row => (row.1, attach suffix row.2)).map Prod.fst = answers.map Prod.fst ∧
      (answers.map fun row => (row.1, attach suffix row.2)).map (fun row => row.2.bindings) =
        answers.map (fun row => row.2.bindings) := by
  constructor <;> simp only [List.map_map, Function.comp_def, attach_bindings]

theorem choices_attach (program : SpaceSemantics.Program) (control : Control)
    (head : String) (arguments : List Atom) (destination : Atom) (older suffix : List Goal)
    (protectedNames : names suffix ⊆ control.reserved) :
    ClauseChoice.choices program (attach suffix control) head arguments destination
        (older.map (shift suffix.length) ++ suffix) =
      (ClauseChoice.choices program control head arguments destination older).map
        (fun row => (row.1, attach suffix row.2)) := by
  apply ClauseChoice.Frontier.unique (fun _ member => List.mem_range.mp member)
    ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)
  exact frontier_attach ((ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mp rfl)
    suffix protectedNames

@[simp] theorem attach_protectControl (suffix : List Goal) (control : Control) (boundary : Finset String) :
    attach suffix (protectControl control boundary) = protectControl (attach suffix control) boundary := rfl

/-- An entered body is nonempty. Its predicate delimiter stays immediately
after that body and keeps its old choice boundary under suffix attachment. -/
theorem predicateEntry_attach (suffix : List Goal) (control : Control)
    (goal : Goal) (older : List Goal) (atBody : control.goals = goal :: older) (retained : Nat) :
    predicateEntry retained (attach suffix control) = attach suffix (predicateEntry retained control) := by
  simp only [attach, atBody, List.map_cons, List.cons_append, predicateEntry, shift]

def attachWork {Context : Type} (suffix : List Goal) (work : CollectionWork Context) : CollectionWork Context :=
  (attach suffix work.1, work.2)

/-- Complete ordinary equation entry transports all source occurrences and
their restored predicate boundaries. Every selected body carries its own
reached constraints into the same protected older continuation. -/
theorem equationWork_attach {Context : Type} (program : SpaceSemantics.Program)
    (control : Control) (boundary : Finset String) (context : Context) (origins : List Nat)
    (head : String) (arguments : List Atom) (destination : Atom) (older suffix : List Goal)
    (retained : Nat) (protectedNames : names suffix ⊆ control.reserved) :
    equationWork program (attach suffix control) boundary context origins head arguments destination
        (older.map (shift suffix.length) ++ suffix) retained =
      (equationWork program control boundary context origins head arguments destination older retained).map
        (attachWork suffix) := by
  have protectedMore : names suffix ⊆ (protectControl control boundary).reserved :=
    protectedNames.trans Finset.subset_union_left
  simp only [equationWork, ← attach_protectControl,
    choices_attach program (protectControl control boundary) head arguments destination older suffix protectedMore,
    List.map_map]
  apply List.map_congr_left
  intro row present
  rcases row with ⟨occurrence, selected⟩
  obtain ⟨equation, row, chosen⟩ := (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp present
  have caller := ClauseChoice.attempt_preserves_caller
    (protectControl control boundary) head arguments destination older occurrence equation selected chosen
  simp only [Function.comp_def, attachWork, predicateEntry_attach suffix selected
    (.evaluate (ClauseChoice.freshBody (protectControl control boundary) occurrence equation) destination)
    older caller.2.2.1 retained]

theorem attached_work_observations {Context : Type} (work : List (CollectionWork Context)) (suffix : List Goal) :
    (work.map (attachWork suffix)).map (fun row => (row.1.bindings, row.2)) =
      work.map (fun row => (row.1.bindings, row.2)) := by
  simp only [List.map_map, Function.comp_def, attachWork, attach_bindings]

def attachCursor {Context : Type} (suffix : List Goal) (cursor : Cursor Context) : Cursor Context :=
  {cursor with control := attach suffix cursor.control}

theorem attachCursor_injective {Context : Type} (suffix : List Goal) :
    Function.Injective (attachCursor (Context := Context) suffix) := by
  intro first second same
  have worlds := congrArg Cursor.world same
  have controls := attach_injective suffix (congrArg Cursor.control same)
  have contexts := congrArg Cursor.context same
  cases first
  cases second
  cases worlds
  cases controls
  cases contexts
  rfl

/-- A normal return preserves the whole pending continuation; an error
returns only to its saved delimiter. Both directions retain the reached
binding record, including open caller aliases. -/
theorem argumentReturn_attach_silent_iff {Context : Type} (cursor after : Cursor Context)
    (value destination : Atom) (younger older suffix : List Goal) :
    ArgumentReturn (attachCursor suffix cursor) value destination
        (younger.map (shift suffix.length)) (older.map (shift suffix.length) ++ suffix)
        (.silent (attachCursor suffix after)) ↔
      ArgumentReturn cursor value destination younger older (.silent after) := by
  constructor
  · intro source
    generalize actionEq : Transition.silent (attachCursor suffix after) = action at source
    cases source with
    | ordinary environment resolved normal =>
        have same : attachCursor suffix after = attachCursor suffix
            {cursor with control := replace cursor.control (younger ++ older)} := by
          simpa only [attachCursor, attach, replace, List.map_append, List.append_assoc] using
            Transition.silent.inj actionEq
        have afterEq := attachCursor_injective suffix same
        rw [afterEq]
        exact .ordinary environment resolved normal
    | propagated environment resolved error bindings accepted =>
        have same : attachCursor suffix after = attachCursor suffix
            {cursor with control := {cursor.control with bindings := bindings, goals := older}} :=
          Transition.silent.inj actionEq
        have afterEq := attachCursor_injective suffix same
        rw [afterEq]
        exact .propagated (cursor := cursor) environment resolved error bindings accepted
    | refused => cases actionEq
    | invalid => cases actionEq
  · intro source
    cases source with
    | ordinary environment resolved normal =>
        simpa only [attachCursor, attach, replace, List.map_append, List.append_assoc] using
          (ArgumentReturn.ordinary (cursor := attachCursor suffix cursor)
            (value := value) (destination := destination)
            (younger := younger.map (shift suffix.length))
            (older := older.map (shift suffix.length) ++ suffix) environment resolved normal)
    | propagated environment resolved error bindings accepted =>
        exact .propagated (cursor := attachCursor suffix cursor) environment resolved error bindings accepted

/-- Continuing source work retains the same root-name protection. This is
derived from the source cases, including both ordinary and error returns. -/
theorem step_reserved {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (source : Source.Step policy program before (.silent after)) :
    after.control.reserved = before.control.reserved := by
  cases source with
  | restoring => rfl
  | expanded _ _ _ _ _ _ prepared => exact prepared.retains_frame.2.2
  | accepted => rfl
  | conditional => rfl
  | printed => rfl
  | argument _ _ _ _ _ _ returned => cases returned <;> rfl

/-- An ordinary continuing source transition commutes with a protected older
suffix. Boundaries that would finish the original child are deliberately not
identified with completion of the still-pending caller. -/
theorem step_attach {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (source : Source.Step policy program before (.silent after))
    (suffix : List Goal) (protectedNames : names suffix ⊆ before.control.reserved) :
    Source.Step policy program (attachCursor suffix before) (.silent (attachCursor suffix after)) := by
  cases source with
  | restoring boundary older atGoal =>
      apply Source.Step.restoring boundary (older.map (shift suffix.length) ++ suffix)
      simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
  | expanded expression destination older next atGoal ordinary prepared =>
      apply Source.Step.expanded expression destination (older.map (shift suffix.length) ++ suffix)
        (attach suffix next)
      · simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
      · exact ordinary
      · exact prepared_attach prepared suffix protectedNames
  | accepted value destination older bindings atGoal refined =>
      apply Source.Step.accepted value destination (older.map (shift suffix.length) ++ suffix) bindings
      · simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
      · exact refined
  | conditional condition yes no destination older environment atGoal resolved =>
      apply Source.Step.conditional condition yes no destination (older.map (shift suffix.length) ++ suffix) environment
      · simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
      · exact resolved
  | printed arguments destination older environment value atGoal resolved readout =>
      apply Source.Step.printed arguments destination (older.map (shift suffix.length) ++ suffix)
        environment value
      · simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
      · exact resolved
      · exact readout
  | argument value destination younger older action atGoal returned =>
      apply Source.Step.argument value destination (younger.map (shift suffix.length))
        (older.map (shift suffix.length) ++ suffix)
      · simp only [attachCursor, attach, atGoal, List.map_cons, List.map_append,
          List.length_append, List.length_map, shift, List.cons_append, List.append_assoc]
      · exact (argumentReturn_attach_silent_iff before after value destination younger older suffix).mpr returned

theorem refused_attach {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : Cursor Context} {bindings : Equations}
    (source : Source.Step policy program before (.finish (.noValue bindings, after)))
    (suffix : List Goal) :
    Source.Step policy program (attachCursor suffix before)
      (.finish (.noValue bindings, attachCursor suffix after)) := by
  cases source with
  | refused value destination older atGoal incompatible =>
      apply Source.Step.refused value destination (older.map (shift suffix.length) ++ suffix)
      · simp only [attachCursor, attach, atGoal, List.map_cons, shift, List.cons_append]
      · exact incompatible
  | argument value destination younger older action atGoal returned =>
      cases returned with
      | refused environment resolved error incompatible =>
          apply Source.Step.argument value destination (younger.map (shift suffix.length))
            (older.map (shift suffix.length) ++ suffix)
          · simp only [attachCursor, attach, atGoal, List.map_cons, List.map_append,
              List.length_append, List.length_map, shift, List.cons_append, List.append_assoc]
          · exact ArgumentReturn.refused environment resolved error incompatible

def attachScope {Context : Type} (suffix : List Goal) (scope : CollectionScope Context) :
    CollectionScope Context :=
  {scope with frontier := scope.frontier.map (attachWork suffix)}

/-- Only the current child's alternatives receive its caller continuation.
Outer scopes and already collected occurrences remain exactly as reached. -/
def attachState {Context : Type} (suffix : List Goal) (state : ScopedCursor Context) : ScopedCursor Context :=
  (state.1, {state.2 with scopes := match state.2.scopes with
    | [] => []
    | scope :: parents => attachScope suffix scope :: parents})

theorem attachState_scopes_valid {Context : Type} (suffix : List Goal) (state : ScopedCursor Context)
    (valid : EagerDFS.ScopesValid state.2.scopes) :
    EagerDFS.ScopesValid (attachState suffix state).2.scopes := by
  cases scopes : state.2.scopes with
  | nil => exact False.elim (valid.nonempty scopes)
  | cons scope parents =>
      have headValid : EagerDFS.ScopesValid (scope :: parents) := scopes ▸ valid
      simpa only [attachState, scopes, attachScope] using
        headValid.replace_head (scope.frontier.map (attachWork suffix)) scope.collected

/-- At the child's terminal cut, the saved suffix starts in the child's
reached frame. Every other occurrence receives the same continuation without
changing its bindings, context, origin or position in the frontier. -/
theorem terminal_attach_frontier {Context : Type} (suffix : List Goal)
    (supply : MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atEnd : control.goals = []) :
    attachState suffix (supply, ⟨world, scope :: parents⟩) =
      (supply, ⟨world, {scope with frontier :=
        (replace control suffix, context, origins) :: pending.map (attachWork suffix)} :: parents⟩) := by
  simp only [attachState, attachScope, frontier, List.map_cons, attachWork,
    attach, atEnd, List.map_nil, List.nil_append, replace]

/-- At an actual argument-return goal the full scoped action is exactly one
of the independent local return rules installed in the retained frontier.
The decomposition includes refused and inconsistent branches, not only
successful ordinary returns. -/
theorem argumentReturn_scoped_iff {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (supply : MetavariableFrameStore.Shared.Allocator)
    (world : EagerDFS.World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (younger older : List Goal)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReturn : control.goals = .argumentReturn value destination older.length :: younger ++ older)
    (action : Source.ScopeAction MetavariableFrameStore.Shared.Allocator Context) :
    Source.ScopedStep Source.FreshOperations.owned policy program
        (supply, ⟨world, scope :: parents⟩) action ↔
      ∃ localAction, ArgumentReturn (⟨world, control, context⟩ : Cursor Context)
          value destination younger older localAction ∧
        action = installChild program (supply, ⟨world, scope :: parents⟩)
          scope parents origins pending localAction := by
  constructor
  · intro source
    obtain ⟨localAction, localSource, actual⟩ := Source.step_has_source policy program
      (⟨world, control, context⟩ : Cursor Context)
      (.argument value destination older.length (younger ++ older) atReturn)
    have returned := argumentReturn_step_source policy program
      (⟨world, control, context⟩ : Cursor Context) value destination younger older atReturn actual
    exact ⟨localAction, returned, source.execution.symm.trans
      (Source.source_step_scope policy program supply world scope parents control context origins pending
        frontier localAction localSource)⟩
  · rintro ⟨localAction, returned, rfl⟩
    have localSource := Source.Step.argument (policy := policy) (program := program)
      value destination younger older localAction atReturn returned
    cases returned with
    | ordinary environment resolved normal =>
        exact .active supply world scope parents control context origins pending _ frontier
          (.next _ localSource)
    | propagated environment resolved error bindings accepted =>
        exact .active supply world scope parents control context origins pending _ frontier
          (.next _ localSource)
    | refused environment resolved error incompatible =>
        exact .active supply world scope parents control context origins pending _ frontier
          (.refused _ _ localSource)
    | invalid inconsistent =>
        exact .active supply world scope parents control context origins pending _ frontier
          (.boundary .invalidEnvironment _ localSource (by intros; simp) (by intros; simp) (by simp) (by intros; simp))

/-- Crossing an earned continuing return consumes one step, then runs the
saved siblings on the returned cursor. Finite execution reflects to source
evidence for every endpoint, preserving all later duplicate occurrences. -/
theorem argumentReturn_silent_run_iff {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (supply : MetavariableFrameStore.Shared.Allocator)
    (world : EagerDFS.World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (control : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (value destination : Atom) (younger older : List Goal) (reached : Cursor Context)
    (valid : EagerDFS.ScopesValid (scope :: parents))
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (atReturn : control.goals = .argumentReturn value destination older.length :: younger ++ older)
    (returned : ArgumentReturn (⟨world, control, context⟩ : Cursor Context)
      value destination younger older (.silent reached))
    (fuel : Nat) (events : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run
        (fuel + 1) (supply, ⟨world, scope :: parents⟩) = (events, outcome) ↔
      Derivation (sourceRule policy program) fuel
        (supply, ⟨reached.world, retainChild scope pending origins reached :: parents⟩) events outcome := by
  have source : Source.ScopedStep Source.FreshOperations.owned policy program
      (supply, ⟨world, scope :: parents⟩)
      (.silent (supply, ⟨reached.world, retainChild scope pending origins reached :: parents⟩)) :=
    (argumentReturn_scoped_iff policy program supply world scope parents control context origins pending
      value destination younger older frontier atReturn _).mpr ⟨.silent reached, returned, rfl⟩
  have retained := scopeStep_scopes_valid policy program
    (supply, ⟨world, scope :: parents⟩) valid
  rw [source.execution] at retained
  rw [(EagerDFSStreaming.machine program (.scopedDestination Context policy)).run_succ_silent
    (congrArg some source.execution)]
  exact source_run_iff_derivation policy program fuel _ retained events outcome

/-- The source name invariant concerns pending operands, not the result of a
future execution. It can be established once when a caller saves its suffix. -/
def Protected {Context : Type} (suffix : List Goal) (state : ScopedCursor Context) : Prop :=
  match state.2.scopes with
  | [] => True
  | scope :: _ => ∀ work ∈ scope.frontier, names suffix ⊆ work.1.reserved

theorem attachScope_support {Context : Type} (suffix : List Goal) (scope : CollectionScope Context)
    (protectedNames : ∀ work ∈ scope.frontier, names suffix ⊆ work.1.reserved) :
    (attachScope suffix scope).support = scope.support := by
  have front : ∀ work : List (CollectionWork Context),
      (∀ item ∈ work, names suffix ⊆ item.1.reserved) →
      (work.map (attachWork suffix)).foldr (fun item found => item.1.support ∪ found) ∅ =
        work.foldr (fun item found => item.1.support ∪ found) ∅ := by
    intro work
    induction work with
    | nil => intro _; rfl
    | cons work rest ih =>
        intro protectedWork
        simp only [List.map_cons, List.foldr_cons, attachWork,
          attach_support_eq suffix work.1 (protectedWork work (by simp))]
        rw [ih (fun item member => protectedWork item (List.mem_cons_of_mem _ member))]
  exact congrArg (fun found => found ∪
    scope.collected.foldr (fun answer found => answer.support ∪ found) ∅ ∪
    (scope.caller.map fun caller => caller.1.support ∪ (encode caller.2.1).freeVars).getD ∅)
    (front scope.frontier protectedNames)

theorem attachState_support {Context : Type} (suffix : List Goal) (state : ScopedCursor Context)
    (protectedNames : Protected suffix state) :
    collectionSupport (attachState suffix state).2 = collectionSupport state.2 := by
  cases scopes : state.2.scopes with
  | nil => simp only [attachState, scopes, collectionSupport, List.foldr_nil]
  | cons scope parents =>
      have protectedScope : ∀ work ∈ scope.frontier, names suffix ⊆ work.1.reserved := by
        simpa only [Protected, scopes] using protectedNames
      simp only [attachState, scopes, collectionSupport, List.foldr_cons,
        attachScope_support suffix scope protectedScope]

/-- Ordinary pre-return search uses the existing source transition cases.
Equation entry carries complete coverage, including explicit rejected rows.
There is no publication, cut, collection or external primitive-invocation
constructor. Local source output steps may occur and retain their reached
world. The judgment stops before the child hands its answer to its caller. -/
inductive PreReturnStep {Context : Type} (policy : Policy) (program : SpaceSemantics.Program) :
    ScopedCursor Context → ScopedCursor Context → Prop where
  | continuing (supply : MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
      (scope : CollectionScope Context) (parents : List (CollectionScope Context))
      (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
      (reached : Cursor Context)
      (frontier : scope.frontier = (control, context, origins) :: pending)
      (source : Source.Step policy program ⟨world, control, context⟩ (.silent reached)) :
      PreReturnStep policy program (supply, ⟨world, scope :: parents⟩)
        (supply, ⟨reached.world, retainChild scope pending origins reached :: parents⟩)
  | refused (supply : MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
      (scope : CollectionScope Context) (parents : List (CollectionScope Context))
      (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
      (bindings : Equations) (reached : Cursor Context)
      (frontier : scope.frontier = (control, context, origins) :: pending)
      (source : Source.Step policy program ⟨world, control, context⟩ (.finish (.noValue bindings, reached))) :
      PreReturnStep policy program (supply, ⟨world, scope :: parents⟩)
        (supply, ⟨reached.world, {scope with frontier := pending} :: parents⟩)
  | equations (supply : MetavariableFrameStore.Shared.Allocator) (world : EagerDFS.World)
      (scope : CollectionScope Context) (parents : List (CollectionScope Context))
      (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
      (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal)
      (environment : Environment) (selected : List (Nat × Control))
      (frontier : scope.frontier = (control, context, origins) :: pending)
      (atCall : control.goals = .invoke head arguments destination :: older)
      (resolved : resolve control.bindings = some environment)
      (ordinary : head ≠ "parse") (unknown : StdLib.known head = false)
      (notIO : Eval.ioHead head = false)
      (declared : program.equations.any (·.head == head) = true)
      (coverage : ClauseChoice.Frontier program
        (protectControl control (collectionSupport ⟨world, scope :: parents⟩)) head
        (arguments.map (read environment)) destination older (List.range program.equations.length) selected) :
      PreReturnStep policy program (supply, ⟨world, scope :: parents⟩)
        (supply, ⟨world, {scope with frontier := (selected.map (fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])) ++ pending)} :: parents⟩)

/-- Every admitted pre-return step is an actual independent scoped source
step. The profile introduces neither an evaluator nor a source reply oracle. -/
theorem PreReturnStep.source {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : ScopedCursor Context} (source : PreReturnStep policy program before after) :
    Source.ScopedStep Source.FreshOperations.owned policy program before (.silent after) := by
  cases source with
  | continuing supply world scope parents control context origins pending reached frontier localStep =>
      exact .active supply world scope parents control context origins pending _ frontier (.next reached localStep)
  | refused supply world scope parents control context origins pending bindings reached frontier localStep =>
      exact .active supply world scope parents control context origins pending _ frontier (.refused bindings reached localStep)
  | equations supply world scope parents control context origins pending head arguments destination older
      environment selected frontier atCall resolved ordinary unknown notIO declared coverage =>
      refine .active supply world scope parents control context origins pending _ frontier
        (.invocation head arguments destination older environment _ atCall resolved ?_
          (.equations selected ordinary unknown notIO declared coverage))
      intro value printing
      subst head
      simp [Eval.ioHead] at notIO

theorem PreReturnStep.protected {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : ScopedCursor Context} (source : PreReturnStep policy program before after)
    (suffix : List Goal) (protectedNames : Protected suffix before) : Protected suffix after := by
  cases source with
  | continuing supply world scope parents control context origins pending reached frontier localStep =>
      have before : ∀ work ∈ (control, context, origins) :: pending, names suffix ⊆ work.1.reserved := by
        simpa only [Protected, frontier] using protectedNames
      intro work member
      simp only [retainChild, List.mem_cons] at member
      rcases member with rfl | member
      · simpa only [step_reserved localStep] using before (control, context, origins) (by simp)
      · exact before work (List.mem_cons_of_mem _ member)
  | refused supply world scope parents control context origins pending bindings reached frontier localStep =>
      intro work member
      exact protectedNames work (frontier ▸ List.mem_cons_of_mem _ member)
  | equations supply world scope parents control context origins pending head arguments destination older
      environment selected frontier atCall resolved ordinary unknown notIO declared coverage =>
      have before : ∀ work ∈ (control, context, origins) :: pending, names suffix ⊆ work.1.reserved := by
        simpa only [Protected, frontier] using protectedNames
      have selectedEq := (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr coverage
      intro work member
      rcases List.mem_append.mp member with child | pendingMember
      · obtain ⟨⟨occurrence, result⟩, present, rfl⟩ := List.mem_map.mp child
        obtain ⟨equation, row, accepted⟩ :=
          (ClauseChoice.mem_choices_iff _ _ _ _ _ _ _ _).mp (selectedEq ▸ present)
        have fields := ClauseChoice.attempt_preserves_caller _ _ _ _ _ _ _ _ accepted
        simpa only [predicateEntry, fields.2.1, protectControl] using
          (before (control, context, origins) (by simp)).trans Finset.subset_union_left
      · exact before work (List.mem_cons_of_mem _ pendingMember)

/-- The pre-return recursion really executes in the same source machine.
Entire equation frontiers are transported; recursive calls are not treated
as an assumed child answer or as a single selected path. -/
theorem PreReturnStep.attach_source {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : ScopedCursor Context} (source : PreReturnStep policy program before after)
    (suffix : List Goal) (protectedNames : Protected suffix before) :
    Source.ScopedStep Source.FreshOperations.owned policy program
      (attachState suffix before) (.silent (attachState suffix after)) := by
  cases source with
  | continuing supply world scope parents control context origins pending reached frontier localStep =>
      have protectedControl : names suffix ⊆ control.reserved :=
        protectedNames (control, context, origins) (frontier ▸ List.mem_cons_self)
      have targetFrontier : (attachScope suffix scope).frontier =
          (attach suffix control, context, origins) :: pending.map (attachWork suffix) := by
        simp only [attachScope, frontier, List.map_cons, attachWork]
      have targetLocal := step_attach localStep suffix protectedControl
      have actual := Source.ScopedStep.active (fresh := Source.FreshOperations.owned) (policy := policy) supply world (attachScope suffix scope) parents
        (attach suffix control) context origins (pending.map (attachWork suffix)) _ targetFrontier
        (.next (attachCursor suffix reached) targetLocal)
      simpa only [attachState, attachScope, retainChild, List.map_cons, attachWork, attachCursor] using actual
  | refused supply world scope parents control context origins pending bindings reached frontier localStep =>
      have targetFrontier : (attachScope suffix scope).frontier =
          (attach suffix control, context, origins) :: pending.map (attachWork suffix) := by
        simp only [attachScope, frontier, List.map_cons, attachWork]
      have actual := Source.ScopedStep.active (fresh := Source.FreshOperations.owned) (policy := policy) supply world (attachScope suffix scope) parents
        (attach suffix control) context origins (pending.map (attachWork suffix)) _ targetFrontier
        (.refused bindings (attachCursor suffix reached) (refused_attach localStep suffix))
      simpa only [attachState, attachScope, attachCursor] using actual
  | equations supply world scope parents control context origins pending head arguments destination older
      environment selected frontier atCall resolved ordinary unknown notIO declared coverage =>
      let boundary := collectionSupport (⟨world, scope :: parents⟩ : CollectionConfiguration Context)
      have protectedControl : names suffix ⊆ control.reserved :=
        protectedNames (control, context, origins) (frontier ▸ List.mem_cons_self)
      have targetSupport : collectionSupport
          (⟨world, attachScope suffix scope :: parents⟩ : CollectionConfiguration Context) = boundary :=
        attachState_support suffix (supply, ⟨world, scope :: parents⟩) protectedNames
      have targetFrontier : (attachScope suffix scope).frontier =
          (attach suffix control, context, origins) :: pending.map (attachWork suffix) := by
        simp only [attachScope, frontier, List.map_cons, attachWork]
      have selectedEq : ClauseChoice.choices program (protectControl control boundary) head
          (arguments.map (read environment)) destination older = selected :=
        (ClauseChoice.choices_iff_frontier _ _ _ _ _ _ _).mpr coverage
      have mappedCoverage := frontier_attach coverage suffix
        (protectedControl.trans Finset.subset_union_left)
      have targetCoverage : ClauseChoice.Frontier program
          (protectControl (attach suffix control)
            (collectionSupport (⟨world, attachScope suffix scope :: parents⟩ : CollectionConfiguration Context))) head
          (arguments.map (read environment)) destination (older.map (shift suffix.length) ++ suffix)
          (List.range program.equations.length) (selected.map fun row => (row.1, attach suffix row.2)) := by
        simpa only [targetSupport, attach_protectControl] using mappedCoverage
      have targetCall : (attach suffix control).goals = .invoke head arguments destination ::
          (older.map (shift suffix.length) ++ suffix) := by
        simp only [attach, atCall, List.map_cons, shift, List.cons_append]
      have actual := Source.ScopedStep.active (fresh := Source.FreshOperations.owned) (policy := policy) supply world (attachScope suffix scope) parents
        (attach suffix control) context origins (pending.map (attachWork suffix)) _ targetFrontier
        (Source.ActiveStep.invocation head arguments destination (older.map (shift suffix.length) ++ suffix)
          environment _ targetCall resolved (by intro value printing; subst head; simp [Eval.ioHead] at notIO)
          (.equations (selected.map fun row => (row.1, attach suffix row.2))
            ordinary unknown notIO declared targetCoverage))
      have branchMap :
          (selected.map fun row => (predicateEntry (pending.map (attachWork suffix)).length
              (attach suffix row.2), context, origins ++ [row.1])) =
            (selected.map fun row => (predicateEntry pending.length row.2, context, origins ++ [row.1])).map
              (attachWork suffix) := by
        rw [← selectedEq]
        have joined := equationWork_attach program control boundary context origins head
          (arguments.map (read environment)) destination older suffix pending.length protectedControl
        simp only [equationWork, ← attach_protectControl,
          choices_attach program (protectControl control boundary) head (arguments.map (read environment))
            destination older suffix (protectedControl.trans Finset.subset_union_left),
          List.map_map, Function.comp_def, List.length_map] at joined ⊢
        exact joined
      have branchMap' := branchMap
      simp only [List.length_map, List.map_map, Function.comp_def] at branchMap'
      simp only [attachState, attachScope, List.map_append, List.map_map, Function.comp_def,
        List.length_map] at actual ⊢
      rw [branchMap'] at actual
      exact actual

/-- The profile is a relation of independently licensed source steps, not a
new evaluator. Its only continuing action is the reached silent state. -/
def preReturnRule {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (before : ScopedCursor Context) (action : Option (Source.ScopeAction MetavariableFrameStore.Shared.Allocator Context)) : Prop :=
  ∃ after, action = some (.silent after) ∧ PreReturnStep policy program before after

/-- An arbitrary finite pre-return source derivation expands to actual scoped
source evidence, with precisely its original finite budget and endpoint. -/
theorem preReturn_derivation_source {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {fuel : Nat} {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after)) :
    Derivation (sourceRule policy program) fuel before events (.exhausted after) := by
  induction fuel generalizing before events with
  | zero => cases source; exact .pause _
  | succ fuel ih =>
      cases source with
      | silent step rest =>
          obtain ⟨_, same, step⟩ := step
          cases Option.some.inj same
          exact .silent ⟨_, rfl, step.source⟩ (ih rest)
      | published step rest => obtain ⟨_, same, _⟩ := step; cases same

/-- Attaching a protected caller commutes with arbitrary finite ordinary
recursive search before its first return. Each installed equation occurrence
retains its reached constraints; failed alternatives are still exhausted by
their actual source refusals. The endpoint remains a pause, never a completed
answer bag or a claim that the attached caller has finished. -/
theorem preReturn_derivation_attach {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {fuel : Nat} {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (suffix : List Goal) (protectedNames : Protected suffix before) :
    Protected suffix after ∧
      Derivation (sourceRule policy program) fuel (attachState suffix before) events
        (.exhausted (attachState suffix after)) := by
  induction fuel generalizing before events with
  | zero => cases source; exact ⟨protectedNames, .pause _⟩
  | succ fuel ih =>
      cases source with
      | silent step rest =>
          obtain ⟨_, same, step⟩ := step
          cases Option.some.inj same
          obtain ⟨kept, lifted⟩ := ih rest (step.protected suffix protectedNames)
          exact ⟨kept, .silent ⟨_, rfl, step.attach_source suffix protectedNames⟩ lifted⟩
      | published step rest => obtain ⟨_, same, _⟩ := step; cases same

/-- Source-prefix transport is realized by the maintained driver, at the same
budget and actual reached world. The pending caller is not reloaded. -/
theorem preReturn_attached_run {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {fuel : Nat} {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (suffix : List Goal) (protectedNames : Protected suffix before) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel
        (attachState suffix before) = (events, .exhausted (attachState suffix after)) :=
  ((preReturn_derivation_attach source suffix protectedNames).2).sound
    (EagerDFSStreaming.machine program (.scopedDestination Context policy))
    (source_rule_execution policy program)

/-- After arbitrary finite recursive head work, the actual caller runs on
that head occurrence's reached equations, world and retained alternatives.
Earlier source steps and effects are not repeated. -/
theorem preReturn_continuation_run {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {fuel : Nat} {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (suffix : List Goal) (protectedNames : Protected suffix before) (later : Nat) :
    let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
    interpreter.run (fuel + later) (attachState suffix before) =
      (events ++ (interpreter.run later (attachState suffix after)).1,
        (interpreter.run later (attachState suffix after)).2) :=
  (EagerDFSStreaming.machine program (.scopedDestination Context policy)).established_and_pending
    fuel later (attachState suffix before) (attachState suffix after) events
    (preReturn_attached_run source suffix protectedNames)

theorem preReturn_derivation_scopes_valid {Context : Type} {policy : Policy}
    {program : SpaceSemantics.Program} {fuel : Nat}
    {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (valid : EagerDFS.ScopesValid before.2.scopes) :
    EagerDFS.ScopesValid after.2.scopes := by
  induction fuel generalizing before events with
  | zero => cases source; exact valid
  | succ fuel ih =>
      cases source with
      | silent step rest =>
          obtain ⟨_, same, step⟩ := step
          cases Option.some.inj same
          have retained := scopeStep_scopes_valid policy program before valid
          rw [step.source.execution] at retained
          exact ih rest retained
      | published step rest => obtain ⟨_, same, _⟩ := step; cases same

/-- The saved continuation is both sufficient and necessary for a longer
finite run. Reflection reconstructs its independent source derivation at
the actual reached world; a completed child is never used as a reply oracle. -/
theorem preReturn_continuation_iff {Context : Type} {policy : Policy}
    {program : SpaceSemantics.Program} {fuel : Nat}
    {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (suffix : List Goal) (protectedNames : Protected suffix before)
    (valid : EagerDFS.ScopesValid before.2.scopes) (later : Nat)
    (published : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run
        (fuel + later) (attachState suffix before) = (events ++ published, outcome) ↔
      Derivation (sourceRule policy program) later (attachState suffix after) published outcome := by
  rw [preReturn_continuation_run source suffix protectedNames later]
  have reachedValid := attachState_scopes_valid suffix after
    (preReturn_derivation_scopes_valid source valid)
  rw [← source_run_iff_derivation policy program later (attachState suffix after)
    reachedValid published outcome]
  simp only [Prod.mk.injEq, List.append_cancel_left_eq]
  constructor
  · rintro ⟨eventsEq, outcomeEq⟩
    exact Prod.ext eventsEq outcomeEq
  · intro same
    exact ⟨congrArg Prod.fst same, congrArg Prod.snd same⟩

/-- A source head return initializes all saved sibling work with its own
reached equations and world. The terminal readout is earned by the local
source rule; the continuation may finish, pause, refuse or request a service.
No condition requires the child's result or caller variables to be closed. -/
theorem preReturn_return_continuation_iff {Context : Type} {policy : Policy}
    {program : SpaceSemantics.Program} {fuel : Nat}
    {before after : ScopedCursor Context} {events : List CollectedAnswer}
    (source : Derivation (preReturnRule policy program) fuel before events (.exhausted after))
    (suffix : List Goal) (protectedNames : Protected suffix before)
    (valid : EagerDFS.ScopesValid before.2.scopes)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context))
    (scopes : after.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (value : Atom) (bindings : Equations) (returned : Cursor Context)
    (headReturn : Source.Step policy program ⟨after.2.world, control, context⟩
      (.finish (.value value bindings, returned)))
    (later : Nat) (published : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    returned = ⟨after.2.world, control, context⟩ ∧ bindings = control.bindings ∧
      (∃ environment, resolve bindings = some environment ∧ read environment control.destination = value) ∧
      ((EagerDFSStreaming.machine program (.scopedDestination Context policy)).run
          (fuel + later) (attachState suffix before) = (events ++ published, outcome) ↔
        Derivation (sourceRule policy program) later
          (after.1, ⟨after.2.world, {scope with frontier :=
            (replace control suffix, context, origins) :: pending.map (attachWork suffix)} :: parents⟩)
          published outcome) := by
  obtain ⟨same, bindingEq, atEnd, environment, resolved, readout⟩ :=
    (Source.Step.returned_iff policy program _ returned value bindings).mp headReturn
  refine ⟨same, bindingEq, ⟨environment, bindingEq ▸ resolved, readout⟩, ?_⟩
  have reached : after = (after.1, ⟨after.2.world, scope :: parents⟩) := by
    cases after with
    | mk supply configuration =>
        cases configuration
        simp_all
  have endpoint := terminal_attach_frontier suffix after.1 after.2.world scope parents
    control context origins pending frontier atEnd
  rw [← reached] at endpoint
  rw [← endpoint]
  exact preReturn_continuation_iff source suffix protectedNames valid later published outcome

namespace Controls

open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared

private def program : SpaceSemantics.Program :=
  {equations := [⟨"outer", [], .expression [.symbol "inner"]⟩,
    ⟨"inner", [], .symbol "B"⟩, ⟨"inner", [], .symbol "B"⟩], declarations := []}
private def world : EagerDFS.World := ⟨Effects.empty, [], []⟩
private def suffix : List Goal := [.equate (.var "public") (.var "result")]
private def control : Control :=
  {bindings := [], goals := [.invoke "outer" [] (.var "result")],
    destination := .var "result", reserved := {"public", "result"}}
private def initial : ScopedCursor Unit := (Allocator.empty 0 1, ⟨world, [⟨[(control, (), [])], [], none⟩]⟩)
private def outerSelected : Control :=
  {protectControl control (collectionSupport initial.2) with
    bindings := [(.expression [.symbol "outer"], .expression [.symbol "outer"])],
    goals := [.evaluate (.expression [.symbol "inner"]) (.var "result")]}
private def firstControl : Control := predicateEntry 0 outerSelected
private def firstWork : List (CollectionWork Unit) := [(firstControl, (), [0])]
private def expanded : Control :=
  {firstControl with goals := [.invoke "inner" [] (.var "result"), .restoreCommit 0]}
private def middle : ScopedCursor Unit := (initial.1, ⟨world, [⟨[(expanded, (), [0])], [], none⟩]⟩)
private def innerSelected : Control :=
  {protectControl expanded (collectionSupport middle.2) with
    bindings := expanded.bindings ++ [(.expression [.symbol "inner"], .expression [.symbol "inner"])],
    goals := [.evaluate (.symbol "B") (.var "result"), .restoreCommit 0]}
private def finalWork : List (CollectionWork Unit) :=
  [(predicateEntry 0 innerSelected, (), [0, 1]), (predicateEntry 0 innerSelected, (), [0, 2])]
private def reached : ScopedCursor Unit := (initial.1, ⟨world, [⟨finalWork, [], none⟩]⟩)

theorem recursive_duplicate_prefix :
    Derivation (preReturnRule .eagerValue program) 3 initial [] (.exhausted reached) := by
  let identity : Environment := Mettapedia.Logic.LP.Subst.id signature
  have outerModels : Solves identity control.bindings := by
    intro pair present
    cases present
  obtain ⟨outerEnvironment, outerResolved⟩ := resolve_complete ⟨identity, outerModels⟩
  have outerCoverage : ClauseChoice.Frontier program (protectControl control (collectionSupport initial.2))
      "outer" [] (.var "result") [] [0, 1, 2] [(0, outerSelected)] := by
    apply ClauseChoice.Frontier.keep
    · simpa only [outerSelected, ClauseChoice.freshPattern, ClauseChoice.freshBody,
        ClauseChoice.pattern, HE.Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil,
        protectControl, control, List.nil_append] using
        (ClauseChoice.Decision.selected (program := program)
          (control := protectControl control (collectionSupport initial.2))
          (head := "outer") (arguments := []) (destination := .var "result") (older := []) (occurrence := 0)
          ⟨"outer", [], .expression [.symbol "inner"]⟩ _ rfl rfl
          (Refinement.accepted identity outerModels (by
            simp only [ClauseChoice.freshPattern, ClauseChoice.pattern,
              HE.Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil])))
    · exact .skip (.other ⟨"inner", [], .symbol "B"⟩ rfl (by decide))
        (.skip (.other ⟨"inner", [], .symbol "B"⟩ rfl (by decide)) .nil)
  have outerStep : PreReturnStep .eagerValue program initial
      (initial.1, ⟨world, [⟨firstWork, [], none⟩]⟩) := by
    simpa only [initial, firstWork, firstControl, List.length_nil,
      List.map_nil, List.map_cons, List.nil_append, List.append_nil] using
      (PreReturnStep.equations (policy := .eagerValue) (program := program)
      initial.1 world ⟨[(control, (), [])], [], none⟩ [] control () [] [] "outer" []
      (.var "result") [] outerEnvironment [(0, outerSelected)] rfl rfl outerResolved (by decide) (by decide)
      (by decide) (by decide) outerCoverage)
  have expandStep : PreReturnStep .eagerValue program
      (initial.1, ⟨world, [⟨firstWork, [], none⟩]⟩) middle := by
    apply PreReturnStep.continuing initial.1 world ⟨firstWork, [], none⟩ [] firstControl () [0] []
      ⟨world, expanded, ()⟩
    · rfl
    · exact .expanded (.expression [.symbol "inner"]) (.var "result") [.restoreCommit 0]
        expanded rfl (by decide) (.application "inner" [] (by decide) (by decide))
  have innerModels : Solves identity expanded.bindings := by
    intro pair present
    change pair ∈ [(.expression [.symbol "outer"], .expression [.symbol "outer"])] at present
    rcases List.mem_singleton.mp present with rfl
    rfl
  obtain ⟨innerEnvironment, innerResolved⟩ := resolve_complete ⟨identity, innerModels⟩
  have innerCoverage : ClauseChoice.Frontier program (protectControl expanded (collectionSupport middle.2))
      "inner" [] (.var "result") [.restoreCommit 0] [0, 1, 2] [(1, innerSelected), (2, innerSelected)] := by
    have selected (index : Nat)
        (row : program.equations[index]? = some ⟨"inner", [], .symbol "B"⟩) :
        ClauseChoice.Decision program (protectControl expanded (collectionSupport middle.2))
          "inner" [] (.var "result") [.restoreCommit 0] index (some innerSelected) := by
      simpa only [innerSelected, ClauseChoice.freshPattern, ClauseChoice.freshBody,
        ClauseChoice.pattern, HE.Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil,
        protectControl] using
        (ClauseChoice.Decision.selected (program := program)
          (control := protectControl expanded (collectionSupport middle.2))
          (head := "inner") (arguments := []) (destination := .var "result")
          (older := [.restoreCommit 0]) (occurrence := index)
          ⟨"inner", [], .symbol "B"⟩ _ row rfl (Refinement.accepted identity innerModels (by
            simp only [ClauseChoice.freshPattern, ClauseChoice.pattern,
              HE.Spec.Type.RuntimeRefinement.renameTypeVars, List.map_cons, List.map_nil])))
    exact .skip (.other ⟨"outer", [], .expression [.symbol "inner"]⟩ rfl (by decide))
      (.keep (selected 1 rfl) (.keep (selected 2 rfl) .nil))
  have innerStep : PreReturnStep .eagerValue program middle reached := by
    simpa only [middle, reached, finalWork, List.length_nil,
      List.map_nil, List.map_cons, List.append_nil, List.cons_append, List.nil_append] using
      (PreReturnStep.equations (policy := .eagerValue) (program := program)
      initial.1 world ⟨[(expanded, (), [0])], [], none⟩ [] expanded () [0] [] "inner" []
      (.var "result") [.restoreCommit 0] innerEnvironment [(1, innerSelected), (2, innerSelected)] rfl rfl innerResolved
      (by decide) (by decide) (by decide) (by decide)
      innerCoverage)
  exact .silent ⟨_, rfl, outerStep⟩ (.silent ⟨_, rfl, expandStep⟩ (.silent ⟨_, rfl, innerStep⟩ (.pause _)))

theorem protected_recursive_duplicate_prefix :
    Derivation (sourceRule .eagerValue program) 3 (attachState suffix initial) []
      (.exhausted (attachState suffix reached)) ∧
      ((attachState suffix reached).2.scopes.head?.map fun scope =>
        scope.frontier.map (fun work => work.2.2)) = some [[0, 1], [0, 2]] := by
  refine ⟨(preReturn_derivation_attach recursive_duplicate_prefix suffix ?_).2, ?_⟩
  · simp [Protected, initial, control, suffix, names, Goal.atoms, encode, Mettapedia.Logic.LP.Term.freeVars]
  · rfl

/-- Omitting root protection changes the actual allocator, even though the
same suffix is eventually attached. It is not a harmless premise to drop. -/
theorem unprotected_suffix_changes_freshName :
    freshName (attach [.equate (.var "a-long-caller-name") (.symbol "A")]
      {bindings := [], goals := [], destination := .symbol "result"}) 0 ≠
    freshName {bindings := [], goals := [], destination := .symbol "result"} 0 := by
  intro same
  have lengths := congrArg String.length same
  simp [freshName, attach, Control.support, Goal.atoms, encode,
    Mettapedia.Logic.LP.Term.freeVars] at lengths

/-- A saved return depth must grow with its older suffix. Keeping the old
number silently selects a different continuation. -/
theorem unshifted_depth_loses_caller :
    callerSuffix? 0 suffix ≠ some suffix := by
  decide

private def returnedControl (forget : Bool) : Control :=
  {bindings := if forget then [] else [(.var "caller", .var "result"), (.var "result", .symbol "B")]
   goals := []
   destination := .expression [.symbol "Pair", .var "caller", .var "result"]
   reserved := {"caller", "result", "outer"}}
private def returnedSuffix : List Goal :=
  [.argumentReturn (.var "result") (.var "outer") 1, .equate (.var "caller") (.symbol "B")]
private def returnedWorld : EagerDFS.World := ⟨Effects.empty, [], [.symbol "prior-effect"]⟩
private def returnedScope : CollectionScope String :=
  ⟨[(returnedControl false, "caller-context", [3, 0]),
      (returnedControl false, "caller-context", [3, 1])], [], none⟩
private def returnedStart : ScopedCursor String :=
  attachState returnedSuffix (MetavariableFrameStore.Shared.Allocator.empty 0 0,
    ⟨returnedWorld, [returnedScope]⟩)

/-- Two saved source occurrences keep their shared open caller alias and the
world reached before the return. The actual step is earned by a source rule. -/
theorem returned_aliases_and_duplicate_occurrences :
    ∃ after, (EagerDFSStreaming.machine ({equations := [], declarations := []} : SpaceSemantics.Program)
        (.scopedDestination String .eagerValue)).run 1 returnedStart = ([], .exhausted after) ∧
      after.2.world.output = [.symbol "prior-effect"] ∧
      (after.2.scopes.head?.map fun scope => scope.frontier.map fun work =>
        (work.1.bindings, work.2.1, work.2.2)) =
        some [((returnedControl false).bindings, "caller-context", [3, 0]),
          ((returnedControl false).bindings, "caller-context", [3, 1])] := by
  let model : Environment := fun _ => encode (.symbol "B")
  have models : Solves model (returnedControl false).bindings := by
    intro pair member
    simp only [returnedControl, Bool.false_eq_true, ↓reduceIte, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [EagerDFS.Destination.read, model, encode, decode,
        Mettapedia.Logic.LP.Subst.applyTerm]
  obtain ⟨environment, resolved⟩ := resolve_complete ⟨model, models⟩
  have output := resolve_sound resolved (.var "result", .symbol "B") (by simp [returnedControl])
  have scalar : read environment (.symbol "B") = .symbol "B" := by
    simp [EagerDFS.Destination.read, encode, decode]
  have normal : (read environment (.var "result")).isError = false := by
    rw [output, scalar]
    rfl
  let beforeScope := attachScope returnedSuffix returnedScope
  let beforeControl := attach returnedSuffix (returnedControl false)
  let pending : List (CollectionWork String) :=
    [(beforeControl, "caller-context", [3, 1])]
  let reached : Cursor String := ⟨returnedWorld,
    replace beforeControl [.equate (.var "caller") (.symbol "B")], "caller-context"⟩
  let after : ScopedCursor String := (MetavariableFrameStore.Shared.Allocator.empty 0 0,
    ⟨returnedWorld, [retainChild beforeScope pending [3, 0] reached]⟩)
  refine ⟨after, ?_, rfl, rfl⟩
  exact (argumentReturn_silent_run_iff .eagerValue {equations := [], declarations := []}
    (MetavariableFrameStore.Shared.Allocator.empty 0 0) returnedWorld beforeScope []
    beforeControl "caller-context" [3, 0] pending (.var "result") (.var "outer") []
    [.equate (.var "caller") (.symbol "B")] reached (.root _ _) rfl rfl
    (.ordinary (cursor := (⟨returnedWorld, beforeControl, "caller-context"⟩ : Cursor String))
      environment resolved normal) 0 [] (.exhausted after)).mpr (.pause after)

/-- Resetting the head's reached equations severs the caller/result alias.
The source cannot then return the same materialized public tuple. -/
theorem resetting_returned_bindings_changes_answers :
    ¬Source.Step .eagerValue ({equations := [], declarations := []} : SpaceSemantics.Program)
      (⟨returnedWorld, returnedControl true, "caller-context"⟩ : Cursor String)
      (.finish (.value (.expression [.symbol "Pair", .symbol "B", .symbol "B"]) [],
        ⟨returnedWorld, returnedControl true, "caller-context"⟩)) := by
  intro source
  obtain ⟨_, _, _, environment, resolved, output⟩ :=
    (Source.Step.returned_iff _ _ _ _ _ _).mp source
  have emptyResolved : resolve [] = some (Mettapedia.Logic.LP.Subst.id signature) := by
    simp [resolve, equations, Mettapedia.Logic.LP.unifyTotal]
  have same := Option.some.inj (emptyResolved.symm.trans resolved)
  rw [← same] at output
  simp [EagerDFS.Destination.read, returnedControl,
    Mettapedia.Logic.LP.Subst.applyTerm_id, decode_encode] at output

end Controls

#print axioms frontier_attach_iff
#print axioms equationWork_attach
#print axioms PreReturnStep.attach_source
#print axioms preReturn_derivation_attach
#print axioms preReturn_attached_run
#print axioms preReturn_continuation_run
#print axioms attachCursor_injective
#print axioms argumentReturn_attach_silent_iff
#print axioms Source.Step.returned_iff
#print axioms attachState_scopes_valid
#print axioms terminal_attach_frontier
#print axioms argumentReturn_scoped_iff
#print axioms argumentReturn_silent_run_iff
#print axioms preReturn_derivation_scopes_valid
#print axioms preReturn_continuation_iff
#print axioms preReturn_return_continuation_iff
#print axioms Controls.protected_recursive_duplicate_prefix
#print axioms Controls.unprotected_suffix_changes_freshName
#print axioms Controls.unshifted_depth_loses_caller
#print axioms Controls.returned_aliases_and_duplicate_occurrences
#print axioms Controls.resetting_returned_bindings_changes_answers

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ProtectedContinuation

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Lifecycle

open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor

variable {Owner Address Value : Type} [DecidableEq Owner] [DecidableEq Address]

/-- Context owners in a live scope include its saved collection caller.
Published results and foreign callers have their own external pins; this is
not a decoder of all strong roots in a native runtime. -/
def scopeContexts (scope : CollectionScope Owner) : List Owner :=
  scope.frontier.map (fun work => work.2.1) ++
    scope.caller.toList.map (fun caller => caller.2.2.1)

def contextSupport (state : ScopedCursor Owner) : Finset Owner :=
  (state.2.scopes.flatMap scopeContexts).toFinset

/-- A dropped occurrence does not retire a context still used by surviving
work, a saved caller, or an external pin. Occurrence order is left in the
machine state, separately from this finite ownership inventory. -/
def retiredContexts (before after : ScopedCursor Owner) (external : Finset Owner) : Finset Owner :=
  contextSupport before \ (contextSupport after ∪ external)

/-- The actual delimiter step changes context support by precisely its
younger frontier; arbitrary parent scopes and collection callers survive. -/
theorem commit_context_support (allocator : Allocator) (world : World)
    (scope : CollectionScope Owner) (parents : List (CollectionScope Owner))
    (control : Control) (context : Owner) (origins : List Nat)
    (younger kept : List (CollectionWork Owner)) (older : List Goal)
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept) :
    contextSupport (allocator,⟨world,scope :: parents⟩) =
      (younger.map (fun work => work.2.1)).toFinset ∪
        contextSupport (allocator,⟨world,{scope with frontier :=
          ({control with goals := older},context,origins) :: kept} :: parents⟩) := by
  ext owner
  simp only [contextSupport, List.flatMap_cons, scopeContexts, frontier,
    List.map_cons, List.map_append, List.mem_toFinset, List.mem_append,
    List.mem_cons, Finset.mem_union]
  tauto

/-- This inventory comes from the actual reached states, not from all
occurrences of a context in the discarded prefix. -/
theorem commit_retired_contexts (allocator : Allocator) (world : World)
    (scope : CollectionScope Owner) (parents : List (CollectionScope Owner))
    (control : Control) (context : Owner) (origins : List Nat)
    (younger kept : List (CollectionWork Owner)) (older : List Goal) (external : Finset Owner)
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept) :
    retiredContexts (allocator,⟨world,scope :: parents⟩)
        (allocator,⟨world,{scope with frontier :=
          ({control with goals := older},context,origins) :: kept} :: parents⟩) external =
      (younger.map (fun work => work.2.1)).toFinset \ (contextSupport
        (allocator,⟨world,{scope with frontier :=
          ({control with goals := older},context,origins) :: kept} :: parents⟩) ∪ external) := by
  unfold retiredContexts
  rw [commit_context_support allocator world scope parents control context origins younger kept older frontier]
  ext owner
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- A licensed machine cut composes with the existing resource lifecycle.
It preserves every cell reachable through a surviving context, including
shared descendants and cycles. Root discovery and authority for external
job cancellation are separate from this local semantic-interface law. -/
theorem commit_lifecycle_square (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Owner)
    (parents : List (CollectionScope Owner)) (control : Control) (context : Owner)
    (origins : List Nat) (younger kept : List (CollectionWork Owner)) (older : List Goal)
    (external : Finset Owner) (heap : Heap Address Value) (roots : Roots Owner Address)
    (valid : EagerDFS.ScopesValid (scope :: parents))
    (frontier : scope.frontier = (control,context,origins) :: younger ++ kept)
    (atGoal : control.goals = .commit :: older) (boundary : control.cutBoundary = kept.length) :
    let before : ScopedCursor Owner := (allocator,⟨world,scope :: parents⟩)
    let after : ScopedCursor Owner := (allocator,⟨world,{scope with frontier :=
      ({control with goals := older},context,origins) :: kept} :: parents⟩)
    let session : OwnedLifecycle.Session Owner Address Value World := ⟨heap,roots,world⟩
    Derivation (sourceRule policy program) 1 before [] (.exhausted after) ∧
      (OwnedLifecycle.closeScope session (retiredContexts before after external)).world = world ∧
      ∀ owner ∈ contextSupport after ∪ external, ∀ address,
        Live heap (roots.filter (fun pair => pair.1 = owner)) address →
          (OwnedLifecycle.closeScope session (retiredContexts before after external)).heap.lookup address =
            heap.lookup address := by
  dsimp only
  refine ⟨?_,rfl,?_⟩
  · apply (source_run_iff_derivation policy program 1 _ valid [] _).mp
    have actual := scope_commit_split policy program allocator world scope parents control context origins
      younger kept older frontier atGoal boundary
    have step := step_scope policy program (allocator,⟨world,scope :: parents⟩)
    rw [actual] at step
    rw [(EagerDFSStreaming.machine program (.scopedDestination Owner policy)).run_succ_silent step]
    rfl
  · intro owner surviving address live
    apply lookup_collect_of_live
    apply live_cancel_other_owner heap roots _ owner ?_ live
    intro retired
    exact (Finset.mem_sdiff.mp retired).2 surviving

namespace Controls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def control : Control :=
  {bindings := [],goals := [.commit],destination := .symbol "answer",cutBoundary := 2}

private def work (owner : Nat) : CollectionWork Nat := (control,owner,[])
private def younger : List (CollectionWork Nat) := [work 7,work 8,work 9]
private def kept : List (CollectionWork Nat) := [work 7,work 7]
private def world : World := ⟨Effects.empty,[],[.symbol "already committed"]⟩
private def allocator : Allocator := Allocator.empty 0 0
private def caller : CollectionCaller Nat := (control,.symbol "collected",11,[])
private def scope : CollectionScope Nat := ⟨work 10 :: younger ++ kept,[],some caller⟩
private def parent : CollectionScope Nat := ⟨[work 12],[],none⟩
private def before : ScopedCursor Nat := (allocator,⟨world,[scope,parent]⟩)
private def after : ScopedCursor Nat :=
  (allocator,⟨world,[{scope with frontier := ({control with goals := []},10,[]) :: kept},parent]⟩)

/-- An actual cut drops three younger occurrences, but retires only their
unshared, unpinned context. The saved collection caller and parent survive. -/
theorem shared_and_pinned_contexts_survive_actual_cut :
    (EagerDFSStreaming.machine {equations := [],declarations := []}
      (.scopedDestination Nat .relational)).run 1 before = ([],.exhausted after) ∧
      retiredContexts before after {8} = {9} ∧
      contextSupport after = {7,10,11,12} ∧
      after.2.scopes.head?.map (fun scope => scope.frontier.map (fun row => row.2.1)) = some [10,7,7] ∧
      after.2.world.output = [.symbol "already committed"] := by
  refine ⟨?_,by decide,by decide,rfl,rfl⟩
  have actual := scope_commit_split .relational {equations := [],declarations := []}
    allocator world scope [parent] control 10 [] younger kept [] rfl rfl rfl
  have step := step_scope .relational {equations := [],declarations := []} before
  rw [show scopeStep .relational {equations := [],declarations := []} before = .silent after from actual] at step
  rw [(EagerDFSStreaming.machine {equations := [],declarations := []}
    (.scopedDestination Nat .relational)).run_succ_silent step]
  rfl

/-- Cancelling every owner mentioned by a dropped occurrence would revoke
the retained alternative and the external pin. Such cancellation is not the
licensed delimiter partition. -/
theorem discarded_occurrences_do_not_authorize_whole_context_cancellation :
    (younger.map (fun row => row.2.1)).toFinset ≠ retiredContexts before after {8} ∧
      7 ∈ contextSupport after ∧ 7 ∉ retiredContexts before after {8} ∧
      8 ∉ retiredContexts before after {8} := by decide

private def roots : Roots Nat (Fin 3) := {(7,0),(8,1),(9,0)}
private def resources : OwnedLifecycle.Session Nat (Fin 3) Nat World :=
  ⟨Examples.cyclicHeap,roots,world⟩

/-- The surviving alternative and discarded alternative share the same
cyclic graph. Releasing the discarded context retains every complete cell,
not only the shared top node. -/
theorem actual_cut_keeps_shared_cyclic_graph (address : Fin 3) :
    (OwnedLifecycle.closeScope resources (retiredContexts before after {8})).heap.lookup address =
      Examples.cyclicHeap.lookup address := by
  have square := commit_lifecycle_square .relational {equations := [],declarations := []}
    allocator world scope [parent] control 10 [] younger kept [] {8} Examples.cyclicHeap roots
    (.nested _ _ _ (.root _ _)) rfl rfl rfl
  apply square.2.2 7 (by decide) address
  apply (mem_census_iff_live Examples.cyclicHeap (roots.filter (fun pair => pair.1 = 7)) ?_ address).mp
  · fin_cases address <;> decide
  · intro pair _
    exact Finset.mem_univ pair.2

/-- Releasing every context in the younger prefix destroys the same live
graph. Sharing must be considered before invoking resource collection. -/
theorem cancelling_whole_discarded_contexts_loses_shared_graph :
    (OwnedLifecycle.closeScope resources (younger.map (fun row => row.2.1)).toFinset).heap.lookup 0 ≠
      Examples.cyclicHeap.lookup 0 := by
  have empty : cancel roots (younger.map (fun row => row.2.1)).toFinset = ∅ := by decide
  change (collect Examples.cyclicHeap (cancel roots _)).lookup 0 ≠ Examples.cyclicHeap.lookup 0
  rw [empty,lookup_collect_of_not_live Examples.cyclicHeap ∅ (not_live_empty Examples.cyclicHeap 0)]
  simp [Examples.cyclicHeap]

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Lifecycle

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Scheduler

open EagerDFS (ScopesValid)
open EagerDFS.Destination
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ProductiveCoreAdapters

/-- The shared scheduler retains the existing first-order scope cursor,
including its allocator, choice delimiters, bindings, callers and world.
Only the declared machine transition is executed on each provider visit. -/
def visit {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (fuel : Nat) (source : ScopedCursor Context) :
    Nat × EventCursor.Result (EagerDFSStreaming.machine program (.scopedDestination Context policy)) :=
  let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
  Machines.Cursor.advance (EventCursor.provider interpreter) EventCursor.client (EventCursor.charge interpreter price)
    fuel (EventCursor.packet interpreter ([], .exhausted source))

theorem visit_read {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (fuel : Nat) (source : ScopedCursor Context) :
    EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Context policy))
        (visit policy program price fuel source).2 =
      (EagerDFSStreaming.machine program (.scopedDestination Context policy)).run fuel source := by
  simpa only [visit, List.nil_append] using
    (EventCursor.advance_run (EagerDFSStreaming.machine program (.scopedDestination Context policy))
      price fuel source []).2

theorem visit_account {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (fuel : Nat) (source : ScopedCursor Context) :
    (visit policy program price fuel source).1 =
      (EagerDFSStreaming.machine program (.scopedDestination Context policy)).spent price fuel source :=
  (EventCursor.advance_run (EagerDFSStreaming.machine program (.scopedDestination Context policy))
    price fuel source []).1

/-- The cursor's public execution is licensed in both directions by the
independent source rules, with the same finite budget and complete outcome.
An exhausted or requested source configuration is not a completed search. -/
theorem visit_source_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (fuel : Nat) (source : ScopedCursor Context)
    (valid : ScopesValid source.2.scopes) (events : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Context policy))
        (visit policy program price fuel source).2 = (events, outcome) ↔
      Derivation (sourceRule policy program) fuel source events outcome := by
  rw [visit_read]
  exact source_run_iff_derivation policy program fuel source valid events outcome

/-- This is equality of actual shared-protocol residuals and accounts, not
only of completed answer lists. The saved world is used again unchanged;
replacing it by a newer world requires a separate validation law. -/
theorem visit_split {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (earlier later : Nat) (source : ScopedCursor Context) :
    let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
    visit policy program price (earlier + later) source =
      Machines.Cursor.resume (EventCursor.provider interpreter) EventCursor.client (EventCursor.charge interpreter price)
        later (visit policy program price earlier source) :=
  EventCursor.advance_split _ _ _ _ _ _

theorem resumed_source_iff {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (earlier later : Nat) (source : ScopedCursor Context)
    (valid : ScopesValid source.2.scopes) (events : List CollectedAnswer)
    (outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary) :
    let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
    EventCursor.read interpreter
        (Machines.Cursor.resume (EventCursor.provider interpreter) EventCursor.client (EventCursor.charge interpreter price)
          later (visit policy program price earlier source)).2 = (events, outcome) ↔
      Derivation (sourceRule policy program) (earlier + later) source events outcome := by
  dsimp only
  rw [← visit_split]
  exact visit_source_iff policy program price (earlier + later) source valid events outcome

/-- A reached independent source prefix determines the exact next live
configuration. Resuming the scheduler keeps its previously reached world,
collected occurrences and pending work instead of reloading the original call. -/
theorem resume_source_cut {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (price : ScopedCursor Context → Nat) (earlier later : Nat) (source saved : ScopedCursor Context)
    (valid : ScopesValid source.2.scopes) (published : List CollectedAnswer)
    (cut : Derivation (sourceRule policy program) earlier source published (.exhausted saved)) :
    let interpreter := EagerDFSStreaming.machine program (.scopedDestination Context policy)
    EventCursor.read interpreter
        (Machines.Cursor.resume (EventCursor.provider interpreter) EventCursor.client (EventCursor.charge interpreter price)
          later (visit policy program price earlier source)).2 =
      (published ++ (interpreter.run later saved).1, (interpreter.run later saved).2) := by
  dsimp only
  rw [← visit_split, visit_read]
  exact Scoped.resume policy program earlier later source saved published
    ((source_run_iff_derivation policy program earlier source valid published (.exhausted saved)).mpr cut)

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Scheduler

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.CommitControls

open Mettapedia.Machines.ProductiveCoreAdapters

/-- The shared cursor realizes the independently proved source delimiter
control; the older outer occurrence survives the committed child. -/
theorem protected_cut_cursor :
    EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Unit .relational))
        (Scheduler.visit .relational program (fun _ => 1) 5 (cutProbe 1)).2 =
      ([answerA, answerOuter], .finished (cutFinished [answerA, answerOuter])) :=
  (Scheduler.visit_source_iff .relational program (fun _ => 1) 5 (cutProbe 1)
    (.root _ _) _ _).mpr protected_cut_source

/-- The same adapter retains the counterexample: omitting the delimiter
changes observable occurrences even though all current operands agree. -/
theorem delimiter_changes_cursor_observation :
    (EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Unit .relational))
      (Scheduler.visit .relational program (fun _ => 1) 5 (cutProbe 0)).2).1 ≠
    (EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Unit .relational))
      (Scheduler.visit .relational program (fun _ => 1) 5 (cutProbe 1)).2).1 := by
  rw [Scheduler.visit_read, Scheduler.visit_read]
  exact delimiter_changes_observation

end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.CommitControls

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ComponentRealization

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS (World)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ProductiveCoreAdapters.ComponentRealization
open ProtectedContinuation

abbrev StoreView := List Equations × List Equations
abbrev ControlView := List (List Goal) × List (List Goal)
abbrev SelectionView (Context : Type) :=
  List (Context × List Nat) × List (Context × List Nat)
abbrev PublicationView := List CollectedAnswer

private def headAndParents {Context Item : Type}
    (read : CollectionScope Context → List Item) (state : ScopedCursor Context) :
    List Item × List Item :=
  match state.2.scopes with
  | [] => ([], [])
  | scope :: parents => (read scope, parents.flatMap read)

def storeView {Context : Type} (state : ScopedCursor Context) : StoreView :=
  headAndParents (fun scope => scope.frontier.map fun work => work.1.bindings) state

def controlView {Context : Type} (state : ScopedCursor Context) : ControlView :=
  headAndParents (fun scope => scope.frontier.map fun work => work.1.goals) state

def selectionView {Context : Type} (state : ScopedCursor Context) : SelectionView Context :=
  headAndParents (fun scope => scope.frontier.map fun work => (work.2.1, work.2.2)) state

def publicationView {Context : Type} (state : ScopedCursor Context) : PublicationView :=
  state.2.scopes.flatMap fun scope => scope.collected

def projection {Context : Type} :
    ComponentProjection (ScopedCursor Context) StoreView ControlView
      (SelectionView Context) World PublicationView where
  store := storeView
  control := controlView
  selection := selectionView
  world := fun state => state.2.world
  publication := publicationView

/-- The protected suffix transformation expected of the active scope's
continuations; parent controls remain unchanged. -/
def ControlRel (suffix : List Goal) (logical impl : ControlView) : Prop :=
  impl.1 = logical.1.map (fun goals => goals.map (shift suffix.length) ++ suffix) ∧
    impl.2 = logical.2

/-- A concrete attached state, including the source-side name protection that
licenses future freshening. -/
def Attached {Context : Type} (suffix : List Goal)
    (logical impl : ScopedCursor Context) : Prop :=
  Protected suffix logical ∧ impl = attachState suffix logical

def relation {Context : Type} (suffix : List Goal) :
    FiveComponentRel (projection (Context := Context)) (projection (Context := Context)) where
  storeRel := Eq
  controlRel := ControlRel suffix
  selectionRel := Eq
  worldRel := Eq
  publicationRel := Eq
  coherent := Attached suffix

/-- Attachment changes only active goals; stores, occurrence identities,
world, retained publications and all parent controls remain exact. -/
theorem storeView_attachState {Context : Type} (suffix : List Goal)
    (state : ScopedCursor Context) :
    storeView (attachState suffix state) = storeView state := by
  rcases state with ⟨allocator, world, scopes⟩
  cases scopes <;> simp [storeView, headAndParents, attachState, attachScope,
    attachWork, attach]

theorem controlView_attachState {Context : Type} (suffix : List Goal)
    (state : ScopedCursor Context) :
    ControlRel suffix (controlView state) (controlView (attachState suffix state)) := by
  rcases state with ⟨allocator, world, scopes⟩
  cases scopes <;> simp [ControlRel, controlView, headAndParents, attachState,
    attachScope, attachWork, attach, List.map_map, Function.comp_def]

theorem selectionView_attachState {Context : Type} (suffix : List Goal)
    (state : ScopedCursor Context) :
    selectionView (attachState suffix state) = selectionView state := by
  rcases state with ⟨allocator, world, scopes⟩
  cases scopes <;> simp [selectionView, headAndParents, attachState, attachScope,
    attachWork, attach]

theorem publicationView_attachState {Context : Type} (suffix : List Goal)
    (state : ScopedCursor Context) :
    publicationView (attachState suffix state) = publicationView state := by
  rcases state with ⟨allocator, world, scopes⟩
  cases scopes <;> simp [publicationView, attachState, attachScope]

theorem attached_components {Context : Type} (suffix : List Goal)
    (state : ScopedCursor Context) (admitted : Protected suffix state) :
    (relation suffix).Holds state (attachState suffix state) := by
  refine ⟨(storeView_attachState suffix state).symm,
    controlView_attachState suffix state,
    (selectionView_attachState suffix state).symm, rfl,
    (publicationView_attachState suffix state).symm, admitted, rfl⟩

structure Input (Context : Type) (suffix : List Goal) where
  state : ScopedCursor Context
  admitted : Protected suffix state

def Input.logical {Context : Type} {suffix : List Goal}
    (input : Input Context suffix) : ScopedCursor Context := input.state

def Input.implementation {Context : Type} {suffix : List Goal}
    (input : Input Context suffix) : ScopedCursor Context := attachState suffix input.state

def readStores (stores : StoreView) (atoms : List Atom) :
    List (Option (List Atom)) × List (Option (List Atom)) :=
  let readOne := fun equations => (resolve equations).map fun environment => atoms.map (read environment)
  (stores.1.map readOne, stores.2.map readOne)

def normalizeControl (suffix : List Goal) (control : ControlView) : ControlView :=
  (control.1.map (fun goals => goals.map (shift suffix.length) ++ suffix), control.2)

def futureRead {Context : Type} (state : ScopedCursor Context) (atoms : List Atom) :=
  readStores (storeView state) atoms

/-- A one-inspection pre-return derivation can only pause at its reached
silent state and cannot publish or finish. -/
theorem preReturn_one_exhausted {Context : Type} {policy : Policy}
    {program : SpaceSemantics.Program} {before : ScopedCursor Context}
    {events : List CollectedAnswer}
    {outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary}
    (path : Derivation (preReturnRule policy program) 1 before events outcome) :
    ∃ after, events = [] ∧ outcome = .exhausted after ∧
      Derivation (preReturnRule policy program) 1 before [] (.exhausted after) := by
  cases path with
  | silent step rest =>
      cases rest
      exact ⟨_, rfl, rfl, .silent step (.pause _)⟩
  | published step _ => obtain ⟨after, impossible, _⟩ := step; cases impossible
  | finished step => obtain ⟨after, impossible, _⟩ := step; cases impossible
  | faulted step => obtain ⟨after, impossible, _⟩ := step; cases impossible
  | requested step => obtain ⟨after, impossible, _⟩ := step; cases impossible
  | stuck step => obtain ⟨after, impossible, _⟩ := step; cases impossible

/-- One pre-return source inspection becomes one actual scoped source
inspection under the protected continuation. -/
theorem attached_productive_block {Context : Type} (policy : Policy)
    (program : SpaceSemantics.Program) (suffix : List Goal) :
    ProductiveLocalBlock (preReturnRule policy program) (sourceRule policy program)
      (relation suffix).Holds
      ({ event := fun event => [event], verdict := id, request := id } :
        ExecutionReadout CollectedAnswer (ScopedCursor Context) ScopeBoundary
          CollectedAnswer (ScopedCursor Context) ScopeBoundary)
      ({ event := fun event => [event], verdict := id, request := id } :
        ExecutionReadout CollectedAnswer (ScopedCursor Context) ScopeBoundary
          CollectedAnswer (ScopedCursor Context) ScopeBoundary) := by
  refine ⟨?_⟩
  intro before actual events outcome related path
  have attached := related.2.2.2.2.2
  rcases attached with ⟨protectedBefore, rfl⟩
  obtain ⟨after, rfl, rfl, one⟩ := preReturn_one_exhausted path
  obtain ⟨protectedAfter, lifted⟩ :=
    preReturn_derivation_attach one suffix protectedBefore
  exact ⟨1, by omega, [], .exhausted (attachState suffix after), lifted, rfl,
    .exhausted (attached_components suffix after protectedAfter)⟩

/-- The protected-continuation PeTTa component profile discharges M1--M7. -/
def realization {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (suffix : List Goal) :
    ModularMachineAdequacy
      (Input.logical (Context := Context) (suffix := suffix))
      (Input.implementation (Context := Context) (suffix := suffix))
      (projection (Context := Context)) (projection (Context := Context)) (relation suffix)
      (preReturnRule policy program) (sourceRule policy program)
      ({ event := fun event => [event], verdict := id, request := id } :
        ExecutionReadout CollectedAnswer (ScopedCursor Context) ScopeBoundary
          CollectedAnswer (ScopedCursor Context) ScopeBoundary)
      ({ event := fun event => [event], verdict := id, request := id } :
        ExecutionReadout CollectedAnswer (ScopedCursor Context) ScopeBoundary
          CollectedAnswer (ScopedCursor Context) ScopeBoundary)
      (SelectionView Context) (List Atom)
      (List (Option (List Atom)) × List (Option (List Atom))) World ControlView
      PublicationView (List Atom)
      (List (Option (List Atom)) × List (Option (List Atom))) where
  m1_load input := attached_components suffix input.state input.admitted
  observeLogicalSelection := id
  observeImplSelection := id
  m2_selection related := related.2.2.1
  readLogicalStore := readStores
  readImplStore := readStores
  m3_store_read related query := congrArg (fun stores => readStores stores query) related.1
  m4_control := attached_productive_block policy program suffix
  observeLogicalWorld := id
  observeImplWorld := id
  m5_world related := related.2.2.2.1
  observeLogicalControl := normalizeControl suffix
  observeImplControl := id
  m6_retained_control related := by
    exact Prod.ext related.2.1.1.symm related.2.1.2.symm
  observeLogicalPublication := id
  observeImplPublication := id
  m7_publication related := related.2.2.2.2.1
  observeLogicalFuture := futureRead
  observeImplFuture := futureRead
  m7_future related query := congrArg (fun stores => readStores stores query) related.1

/-- Principal PeTTa M8 retained-run theorem before the child return. -/
theorem retained_run {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (suffix : List Goal) (input : Input Context suffix)
    {first second : Nat} {saved : ScopedCursor Context}
    {events later : List CollectedAnswer}
    {outcome : Outcome (ScopedCursor Context) (ScopedCursor Context) ScopeBoundary}
    (initial : Derivation (preReturnRule policy program) first input.logical events (.exhausted saved))
    (continued : Derivation (preReturnRule policy program) second saved later outcome) :
    ∃ first' second' saved' events' later' outcome',
      Derivation (sourceRule policy program) first' input.implementation events' (.exhausted saved') ∧
      Derivation (sourceRule policy program) second' saved' later' outcome' ∧
      (relation suffix).Holds saved saved' ∧
      (realization policy program suffix).ObservationsAgree saved saved' ∧
      events'.flatMap (fun event => [event]) = events.flatMap (fun event => [event]) ∧
      later'.flatMap (fun event => [event]) = later.flatMap (fun event => [event]) ∧
      OutcomeRel (relation suffix).Holds outcome outcome' ∧
      Derivation (sourceRule policy program) (first' + second') input.implementation
        (events' ++ later') outcome' := by
  simpa only [Outcome.relabel_id] using
    (realization policy program suffix).loaded_retained_run input initial continued


end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ComponentRealization

namespace Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Lifecycle

open EagerDFS (World ScopesValid)
open EagerDFS.Destination
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.Machines.ResourceOwnership
open Mettapedia.Machines.Cursor
open Mettapedia.Machines.ProductiveCoreAdapters

variable {Owner Address Value : Type} [DecidableEq Owner] [DecidableEq Address]

/-- A licensed cut, resource retirement, and scheduler resumption share the
same reached scoped configuration. The delimiter emits no public answer, so
the suffix contains only newly produced occurrences; live shared resources
remain readable. -/
theorem composed_cut_retention_adequacy (policy : Policy)
    (program : SpaceSemantics.Program) (price : ScopedCursor Owner → Nat)
    (allocator : Allocator) (world : World) (scope : CollectionScope Owner)
    (parents : List (CollectionScope Owner)) (control : Control) (context : Owner)
    (origins : List Nat) (younger kept : List (CollectionWork Owner))
    (older : List Goal) (external : Finset Owner) (heap : Heap Address Value)
    (roots : Roots Owner Address) (later : Nat)
    (valid : ScopesValid (scope :: parents))
    (frontier : scope.frontier = (control, context, origins) :: younger ++ kept)
    (atGoal : control.goals = .commit :: older)
    (boundary : control.cutBoundary = kept.length) :
    let before : ScopedCursor Owner := (allocator, ⟨world, scope :: parents⟩)
    let after : ScopedCursor Owner :=
      (allocator, ⟨world, {scope with frontier :=
        ({control with goals := older}, context, origins) :: kept} :: parents⟩)
    let session : OwnedLifecycle.Session Owner Address Value World := ⟨heap, roots, world⟩
    Derivation (sourceRule policy program) 1 before [] (.exhausted after) ∧
      EventCursor.read (EagerDFSStreaming.machine program (.scopedDestination Owner policy))
        (Mettapedia.Machines.Cursor.resume
          (EventCursor.provider
            (EagerDFSStreaming.machine program (.scopedDestination Owner policy)))
          EventCursor.client
          (EventCursor.charge
            (EagerDFSStreaming.machine program (.scopedDestination Owner policy)) price)
          later (Scheduler.visit policy program price 1 before)).2 =
        (EagerDFSStreaming.machine program (.scopedDestination Owner policy)).run later after ∧
      (OwnedLifecycle.closeScope session (retiredContexts before after external)).world = world ∧
      ∀ owner ∈ contextSupport after ∪ external, ∀ address,
        Live heap (roots.filter (fun pair => pair.1 = owner)) address →
          (OwnedLifecycle.closeScope session (retiredContexts before after external)).heap.lookup address =
            heap.lookup address := by
  dsimp only
  have square := commit_lifecycle_square policy program allocator world scope parents control
    context origins younger kept older external heap roots valid frontier atGoal boundary
  have resumed := Scheduler.resume_source_cut policy program price 1 later
    (allocator, ⟨world, scope :: parents⟩)
    (allocator, ⟨world, {scope with frontier :=
      ({control with goals := older}, context, origins) :: kept} :: parents⟩)
    valid [] square.1
  exact ⟨square.1, by simpa using resumed, square.2.1, square.2.2⟩


end Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Lifecycle

#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.ComponentRealization.retained_run
#print axioms Mettapedia.Languages.MeTTa.PeTTa.EagerDFSStreaming.Scoped.Lifecycle.composed_cut_retention_adequacy
