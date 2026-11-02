import Mettapedia.Computability.StackMachineComposition
import Mettapedia.Computability.StackMachinePortTime
import Mettapedia.Computability.StackMachineCompositionReflection
import Mettapedia.Computability.StackMachineOutputRelay
import Mettapedia.Computability.StackMachineContextCall
import Mettapedia.Computability.NaturalWordMachine
import Mettapedia.Computability.FramedHeadCall
import Mettapedia.Computability.FramedFieldAssembly
import Mettapedia.Machines.FiniteStackWorker
import Mettapedia.Machines.FiniteCompiledMachine
import Mettapedia.Machines.ConditionalSourceMachine
import Mettapedia.Machines.ICSourceCalls
import Mettapedia.Machines.ICConditionalCalls
import Mettapedia.Examples.Compression.PhysicalCheckControls
import Mettapedia.Examples.Compression.PreparedSourceControls
import Mettapedia.Examples.Compression.E2EntryControls
import Mettapedia.Machines.HierarchicalSourceTime
import Mettapedia.Logic.KernelFoundationManifest

/-!
# Original-time, physical-port and retained-worker controls

In-place output and dirty halts are real counterexamples to missing premises.
The output relay runs actual source, transfer and copy transitions. A second
physical program negates every bit, preserving order and duplicate positions;
its original source times feed a two-call retained-path witness.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

namespace Mettapedia.Examples.Compression.FeatureMachineTimeControls

open Turing StateTransition KolmogorovComplexity
open Mettapedia.Computability
open Mettapedia.Machines

attribute [local implicit_reducible] Turing.idComputer StackMachineOutputRelay.machine
  StackMachineOutputRelay.copy WordHomomorphismMachine.machine StackMachineComposition.machine

abbrev identity : FinTM2 := Turing.idComputer Bool

abbrev identityFinite : Fintype (identity.Γ identity.k₁) := inferInstanceAs (Fintype Bool)
abbrev identityInhabited : Inhabited (identity.Γ identity.k₁) := inferInstanceAs (Inhabited Bool)

attribute [local instance] identityFinite identityInhabited

def payload : List Bool := [true, false, true]

theorem in_place_output_has_no_uniform_time_factor (factor : Nat) :
    ∃ word : List Bool, Nonempty (TM2OutputsInTime identity word (some word) 1) ∧
      factor * 1 < word.length :=
  StackMachinePortTime.Controls.in_place_output_refutes_every_uniform_time_factor factor

theorem identity_halts_cleanly (input : List Bool) (state : identity.Cfg)
    (path : Reaches identity.step (initList identity input) state)
    (stopped : state.l = none) : ∃ output : List Bool, state = haltList identity output := by
  have halted : identity.step state = none := by
    cases state with
    | mk label registers contents =>
        dsimp only at stopped
        subst label
        rfl
  have actual : state ∈ StateTransition.eval identity.step (initList identity input) :=
    StateTransition.mem_eval.mpr ⟨path, halted⟩
  have original := StackMachinePortTime.Controls.identityRun input
  have expected : haltList identity input ∈
      StateTransition.eval identity.step (initList identity input) :=
    StateTransition.mem_eval.mpr ⟨StackMachineComposition.execution_reaches original.toEvalsTo, by rfl⟩
  exact ⟨input, Part.mem_unique actual expected⟩

abbrev first : FinTM2 := StackMachineOutputRelay.machine identity
abbrev second : FinTM2 := WordHomomorphismMachine.machine (fun bit : Bool => [!bit])

abbrev firstFinite : Fintype (first.Γ first.k₁) := inferInstanceAs (Fintype Bool)
abbrev firstInhabited : Inhabited (first.Γ first.k₁) := inferInstanceAs (Inhabited Bool)
abbrev firstEquality : DecidableEq (first.Γ first.k₁) := inferInstanceAs (DecidableEq Bool)

attribute [local instance] firstFinite firstInhabited firstEquality

def firstRun (input : List Bool) : TM2OutputsInTime first input (some input) (1 + 6 * input.length + 4) :=
  StackMachineOutputRelay.outputs identity (StackMachinePortTime.Controls.identityRun input)

theorem first_has_separate_ports : first.k₀ ≠ first.k₁ :=
  StackMachineOutputRelay.distinct_ports identity

theorem first_halts_cleanly (input : List Bool) (state : first.Cfg)
    (path : Reaches first.step (initList first input) state) (stopped : state.l = none) :
    ∃ output : List Bool, state = haltList first output :=
  StackMachineOutputRelay.clean_halts identity identity_halts_cleanly input state path stopped

theorem relay_needs_its_last_copy_transition :
    ((FiniteStackWorker.worker first (fun _word => payload)).searcher []).result 22 = none := by decide

theorem relay_copies_in_order_and_preserves_duplicates :
    ((FiniteStackWorker.worker first (fun _word => payload)).searcher []).result 23 = some payload := by decide

theorem a_halted_readout_keeps_the_same_budget :
    ((FiniteStackWorker.worker first (fun _word => payload)).searcher []).result 40 = some payload := by decide

theorem relay_ports_charge_its_actual_io :
    payload.length ≤ StackMachinePortTime.machinePopBound first * 23 ∧
      payload.length ≤ StackMachineSpaceGrowth.machinePushBound first * 23 :=
  FiniteStackWorker.readout_port_bounds first first_has_separate_ports first_halts_cleanly
    (fun _word => payload) [] payload 23 relay_copies_in_order_and_preserves_duplicates

theorem relay_readout_reflects_to_the_original_identity :
    Nonempty (TM2OutputsInTime identity payload (some payload) 23) := by
  obtain ⟨readRun⟩ := FiniteStackWorker.sound first first_halts_cleanly (fun _word => payload)
    [] payload 23 relay_copies_in_order_and_preserves_duplicates
  exact StackMachineOutputRelay.reflects_outputs identity identity_halts_cleanly readRun

theorem negate_word (input : List Bool) : input.flatMap (fun bit => [!bit]) = input.map Bool.not := by
  induction input with
  | nil => rfl
  | cons head tail ih => simp only [List.flatMap_cons, ih, List.singleton_append, List.map_cons]

def secondRun (input : List Bool) :
    TM2OutputsInTime second input (some (input.map Bool.not)) (4 * input.length + 2) := by
  have raw := WordHomomorphismMachine.outputs (fun bit : Bool => [!bit]) input
  have same : TM2OutputsInTime second input (some (input.map Bool.not))
      (2 * input.length + 2 * (input.map Bool.not).length + 2) :=
    Eq.mp (congrArg (fun output : List Bool => TM2OutputsInTime second input (some output)
      (2 * input.length + 2 * output.length + 2)) (negate_word input)) raw
  exact ⟨same.toEvalsTo, same.steps_le_m.trans (by simp only [List.length_map]; omega)⟩

abbrev combined : FinTM2 := StackMachineComposition.machine first second (Equiv.refl Bool)

abbrev combinedEquality : DecidableEq (combined.Γ combined.k₁) := inferInstanceAs (DecidableEq Bool)
attribute [local instance] combinedEquality

theorem composite_is_not_done_at_44 :
    ((FiniteStackWorker.worker combined (fun _word => payload)).searcher []).result 44 = none := by decide

theorem composite_negates_at_45 :
    ((FiniteStackWorker.worker combined (fun _word => payload)).searcher []).result 45 = some [false, true, false] := by decide

theorem source_machine_push_constant_is_computed : StackMachineSpaceGrowth.machinePushBound first = 1 := by decide

def callOne : HierarchicalSourceTime.Call first second := ⟨[true], payload, payload.map Bool.not, 23, 14⟩
def callTwo : HierarchicalSourceTime.Call first second := ⟨[true], payload.map Bool.not, payload, 23, 14⟩

theorem linear_source_budget_is_85 :
    HierarchicalSourceTime.sourceTime callOne = 85 ∧ HierarchicalSourceTime.sourceTime callTwo = 85 := by decide

def contextInput (context : List Bool) (_word : BinString) : List Bool := context
def nextInput (_context output : List Bool) : List Bool := output

theorem two_call_path_has_original_execution_witnesses :
    HierarchicalSourceTime.SourcePath first second (Equiv.refl Bool) contextInput nextInput
      payload [callOne, callTwo] := by
  refine .cons callOne ?_ ?_ (.cons callTwo ?_ ?_ (.nil payload))
  · simpa [contextInput, nextInput, callOne, payload] using firstRun payload
  · change TM2OutputsInTime second payload (some (payload.map Bool.not)) 14
    simpa [payload] using secondRun payload
  · simpa [contextInput, nextInput, callOne, callTwo, payload] using firstRun (payload.map Bool.not)
  · change TM2OutputsInTime second (payload.map Bool.not) (some payload) 14
    simpa [payload] using secondRun (payload.map Bool.not)

theorem original_times_feed_real_retained_workers :
    HierarchicalPrefixSearch.TimedPath
      (fun context => FiniteStackWorker.worker combined (contextInput context)) nextInput payload
      ([callOne, callTwo].map (HierarchicalSourceTime.timed (first := first) (second := second))) :=
  HierarchicalSourceTime.sourcePath_to_timed first second (Equiv.refl Bool) first_has_separate_ports
    contextInput nextInput two_call_path_has_original_execution_witnesses

theorem source_path_pays_both_cumulative_levels :
    HierarchicalPrefixSearch.nestedBound ([callOne, callTwo].map HierarchicalSourceTime.timed) = 23392 := by decide

abbrev dirty : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _key := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _label := .push true (fun _state => false) .halt

abbrev dirtyEquality : DecidableEq (dirty.Γ dirty.k₁) := inferInstanceAs (DecidableEq Bool)
attribute [local instance] dirtyEquality

theorem halted_word_reading_does_not_supply_clean_halts :
    ((FiniteStackWorker.worker dirty (fun _word => [true])).searcher []).result 1 = some [false] := by decide

theorem dirty_halt_refutes_the_clean_halt_contract :
    ¬ (∀ (input : List Bool) (state : dirty.Cfg), Reaches dirty.step (initList dirty input) state →
      state.l = none → ∃ output : List Bool, state = haltList dirty output) := by
  intro clean
  let final := Turing.TM2.stepAux (dirty.m ()) () (initList dirty [true]).stk
  have advanced : dirty.step (initList dirty [true]) = some final := rfl
  obtain ⟨output, same⟩ := clean [true] final (Relation.ReflTransGen.single advanced) rfl
  have contents := congrArg (fun state : dirty.Cfg => state.stk false) same
  simp [final, dirty, Turing.TM2.stepAux, initList, haltList] at contents

namespace ContextCalls

attribute [local implicit_reducible] StackMachineContextCall.machine

abbrev identityInputInhabited : Inhabited (identity.Γ identity.k₀) := inferInstanceAs (Inhabited Bool)
attribute [local instance] identityInputInhabited

abbrev identityCall : FinTM2 := StackMachineContextCall.machine identity
abbrev identityCallEquality : DecidableEq (identityCall.Γ identityCall.k₁) :=
  inferInstanceAs (DecidableEq (Option (Bool ⊕ Bool)))
attribute [local instance] identityCallEquality

theorem caller_needs_its_last_context_transition :
    ((FiniteStackWorker.worker identityCall (fun _word => payload)).searcher []).result 20 = none := by decide

theorem caller_retains_the_argument_and_result_in_order :
    ((FiniteStackWorker.worker identityCall (fun _word => payload)).searcher []).result 21 =
      some [some (.inl true), some (.inl false), some (.inl true), none,
        some (.inr true), some (.inr false), some (.inr true)] := by decide

theorem empty_arguments_and_results_keep_the_delimiter :
    ((FiniteStackWorker.worker identityCall (fun _word => [])).searcher []).result 6 = some [none] := by decide

theorem an_empty_call_still_pays_its_last_transition :
    ((FiniteStackWorker.worker identityCall (fun _word => [])).searcher []).result 5 = none := by decide

theorem wrong_context_is_not_the_returned_packet :
    ((FiniteStackWorker.worker identityCall (fun _word => payload)).searcher []).result 21 ≠
      some (StackMachineContextCall.packet identity [false, true, false] payload) := by decide

theorem identity_call_halts_cleanly (input : List Bool) (state : identityCall.Cfg)
    (path : Reaches identityCall.step (initList identityCall input) state) (stopped : state.l = none) :
    ∃ output : List (Option (Bool ⊕ Bool)), state = haltList identityCall output :=
  StackMachineContextCall.clean_halts identity identity_halts_cleanly input state path stopped

theorem caller_readout_recovers_an_original_counted_execution :
    ∃ output : List Bool, StackMachineContextCall.packet identity payload output =
        StackMachineContextCall.packet identity payload payload ∧
      Nonempty (TM2OutputsInTime identity payload (some output) 21) := by
  have published : ((FiniteStackWorker.worker identityCall (fun _word => payload)).searcher []).result 21 =
      some (StackMachineContextCall.packet identity payload payload) := caller_retains_the_argument_and_result_in_order
  obtain ⟨called⟩ := FiniteStackWorker.sound identityCall identity_call_halts_cleanly (fun _word => payload)
    [] (StackMachineContextCall.packet identity payload payload) 21 published
  exact StackMachineContextCall.reflects_outputs identity identity_halts_cleanly called

def counted_identity_call (input : List Bool) :
    TM2OutputsInTime identityCall input (some (StackMachineContextCall.packet identity input input))
      (1 + 5 * input.length + 5) :=
  StackMachineContextCall.outputs_with_input_charge identity (StackMachinePortTime.Controls.identityRun input)

abbrev secondInputInhabited : Inhabited (second.Γ second.k₀) := inferInstanceAs (Inhabited Bool)
abbrev secondFinite : Fintype (second.Γ second.k₁) := inferInstanceAs (Fintype Bool)
abbrev secondInhabited : Inhabited (second.Γ second.k₁) := inferInstanceAs (Inhabited Bool)
attribute [local instance] secondInputInhabited secondFinite secondInhabited

abbrev negateCall : FinTM2 := StackMachineContextCall.machine second
abbrev negateCallEquality : DecidableEq (negateCall.Γ negateCall.k₁) :=
  inferInstanceAs (DecidableEq (Option (Bool ⊕ Bool)))
attribute [local instance] negateCallEquality

theorem a_source_that_changes_the_word_does_not_change_its_saved_argument :
    ((FiniteStackWorker.worker negateCall (fun _word => payload)).searcher []).result 34 =
      some (StackMachineContextCall.packet second payload [false, true, false]) := by decide

def counted_negating_call :
    TM2OutputsInTime negateCall payload
      (some (StackMachineContextCall.packet second payload (payload.map Bool.not))) 34 := by
  have called := StackMachineContextCall.outputs second (secondRun payload)
  exact ⟨called.toEvalsTo, called.steps_le_m.trans (by decide)⟩

abbrev eraser : FinTM2 := WordHomomorphismMachine.machine (fun _bit : Bool => ([] : List Bool))
abbrev eraserFinite : Fintype (eraser.Γ eraser.k₁) := inferInstanceAs (Fintype Bool)
abbrev eraserInhabited : Inhabited (eraser.Γ eraser.k₁) := inferInstanceAs (Inhabited Bool)
abbrev eraserInputInhabited : Inhabited (eraser.Γ eraser.k₀) := inferInstanceAs (Inhabited Bool)
attribute [local instance] eraserFinite eraserInhabited eraserInputInhabited

abbrev eraseCall : FinTM2 := StackMachineContextCall.machine eraser
abbrev eraseCallEquality : DecidableEq (eraseCall.Γ eraseCall.k₁) :=
  inferInstanceAs (DecidableEq (Option (Bool ⊕ Bool)))
attribute [local instance] eraseCallEquality

theorem an_empty_source_result_does_not_erase_the_saved_argument :
    ((FiniteStackWorker.worker eraseCall (fun _word => payload)).searcher []).result 22 =
      some (StackMachineContextCall.packet eraser payload []) := by decide

abbrev loop : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ _key := Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m _label := .goto (fun _state => ())

abbrev loopFinite : Fintype (loop.Γ loop.k₁) := inferInstanceAs (Fintype Bool)
abbrev loopInhabited : Inhabited (loop.Γ loop.k₁) := inferInstanceAs (Inhabited Bool)
attribute [local instance] loopFinite loopInhabited

theorem loop_source_reaches_only_its_initial_configuration (input : List Bool) (state : loop.Cfg)
    (path : Reaches loop.step (initList loop input) state) : state = initList loop input := by
  induction path with
  | refl => rfl
  | @tail middle final previous advanced ih =>
      rw [ih] at advanced
      exact (Option.some.inj (Option.mem_def.mp advanced)).symm

abbrev loopCall : FinTM2 := StackMachineContextCall.machine loop
abbrev loopCallEquality : DecidableEq (loopCall.Γ loopCall.k₁) :=
  inferInstanceAs (DecidableEq (Option (Bool ⊕ Bool)))
attribute [local instance] loopCallEquality

theorem a_divergent_source_never_becomes_a_completed_context_call
    (input : List Bool) (budget : Nat) (state : loopCall.Cfg)
    (executed : EvalsToInTime loopCall.step (initList loopCall input) (some state) budget) : state.l ≠ none := by
  intro stopped
  obtain ⟨after, halted, ⟨original⟩⟩ := StackMachineContextCall.terminal_source_halts loop executed stopped
  have same := loop_source_reaches_only_its_initial_configuration input after
    (StackMachineComposition.execution_reaches original.toEvalsTo)
  rw [same] at halted
  cases halted

theorem a_divergent_source_still_runs_after_100_slots :
    ((FiniteStackWorker.worker loopCall (fun _word => payload)).searcher []).result 100 = none := by decide

abbrev dirtyFinite : Fintype (dirty.Γ dirty.k₁) := inferInstanceAs (Fintype Bool)
abbrev dirtyInhabited : Inhabited (dirty.Γ dirty.k₁) := inferInstanceAs (Inhabited Bool)
attribute [local instance] dirtyFinite dirtyInhabited

abbrev dirtyCall : FinTM2 := StackMachineContextCall.machine dirty
abbrev dirtyInputEquality : DecidableEq (dirtyCall.Γ (.inl false)) := inferInstanceAs (DecidableEq Bool)
attribute [local instance] dirtyInputEquality

theorem dirty_source_garbage_is_not_hidden_by_packet_readout :
    let final := Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.runFor dirtyCall.step 11 (initList dirtyCall [true])
    final.l = none ∧ final.stk (.inl false) = [true] ∧
      final ≠ haltList dirtyCall (StackMachineContextCall.packet dirty [true] [false]) := by
  dsimp only
  refine ⟨by decide, by decide, ?_⟩
  intro same
  have retained := congrArg (fun state : dirtyCall.Cfg => state.stk (.inl false)) same
  have original : (Mettapedia.UniversalAI.TimeBoundedAIXI.StepCounting.runFor dirtyCall.step 11
      (initList dirtyCall [true])).stk (.inl false) = [true] := by decide
  have canonical : (haltList dirtyCall (StackMachineContextCall.packet dirty [true] [false])).stk (.inl false) = [] := rfl
  rw [original, canonical] at retained
  cases retained

end ContextCalls

namespace CompiledCalls

open Turing.PartrecToTM2
open Mettapedia.UniversalAI.TimeBoundedAIXI

attribute [local implicit_reducible] FiniteCompiledMachine.machine FiniteSupportMachine.machine
  FiniteCompiledMachine.contextMachine StackMachineContextCall.machine

def raw_successor_run : EvalsToInTime (TM2.step tr) (init ToPartrec.Code.succ [0]) (some (halt [1])) 9 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 9 (init ToPartrec.Code.succ [0])
  have final : StepCounting.runFor (TM2.step tr) 9 (init ToPartrec.Code.succ [0]) = halt [1] := by
    let state := StepCounting.runFor (TM2.step tr) 9 (init ToPartrec.Code.succ [0])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [1]) [] [] [] := by
      funext key
      cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [1] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

abbrev successor : FinTM2 := FiniteCompiledMachine.machine ToPartrec.Code.succ
abbrev successorEquality : DecidableEq (successor.Γ successor.k₁) := inferInstanceAs (DecidableEq Γ')
attribute [local instance] successorEquality

theorem finite_package_is_not_done_at_eight :
    ((FiniteStackWorker.worker successor (fun _word => trList [0])).searcher []).result 8 = none := by decide

theorem finite_package_uses_the_original_nine_transitions :
    ((FiniteStackWorker.worker successor (fun _word => trList [0])).searcher []).result 9 = some (trList [1]) := by decide

def packaged_successor_run : TM2OutputsInTime successor (trList [0]) (some (trList [1])) 9 :=
  FiniteCompiledMachine.outputs ToPartrec.Code.succ raw_successor_run

def recovered_original_run : EvalsToInTime (TM2.step tr) (init ToPartrec.Code.succ [0]) (some (halt [1])) 9 :=
  FiniteCompiledMachine.reflects_outputs ToPartrec.Code.succ packaged_successor_run

attribute [local instance] FiniteCompiledMachine.inputInhabited FiniteCompiledMachine.outputFinite
  FiniteCompiledMachine.outputInhabited

abbrev successorCall : FinTM2 := FiniteCompiledMachine.contextMachine ToPartrec.Code.succ
abbrev successorCallEquality : DecidableEq (successorCall.Γ successorCall.k₁) :=
  inferInstanceAs (DecidableEq (Option (Γ' ⊕ Γ')))
attribute [local instance] successorCallEquality

theorem compiled_call_keeps_the_original_encoded_argument :
    ((FiniteStackWorker.worker successorCall (fun _word => trList [0])).searcher []).result 21 =
      some [some (.inl .cons), none, some (.inr .bit1), some (.inr .cons)] := by decide

theorem compiled_call_does_not_publish_an_unfinished_packet :
    ((FiniteStackWorker.worker successorCall (fun _word => trList [0])).searcher []).result 20 = none := by decide

def counted_compiled_context_call :
    TM2OutputsInTime successorCall (trList [0])
      (some (StackMachineContextCall.packet successor (trList [0]) (trList [1]))) 21 := by
  have called := FiniteCompiledMachine.context_outputs ToPartrec.Code.succ raw_successor_run
  exact ⟨called.toEvalsTo, called.steps_le_m.trans (by decide)⟩

theorem completed_compiled_packet_recovers_an_actual_source_run :
    ∃ output : List Nat,
      StackMachineContextCall.packet successor (trList [0]) (trList output) =
        StackMachineContextCall.packet successor (trList [0]) (trList [1]) ∧
      Nonempty (EvalsToInTime (TM2.step tr) (init ToPartrec.Code.succ [0]) (some (halt output)) 21) :=
  FiniteCompiledMachine.context_reflects_outputs ToPartrec.Code.succ counted_compiled_context_call

theorem observed_compiled_packet_recovers_an_actual_source_run :
    ∃ output : List Nat,
      StackMachineContextCall.packet successor (trList [0]) (trList output) =
        StackMachineContextCall.packet successor (trList [0]) (trList [1]) ∧
      Nonempty (EvalsToInTime (TM2.step tr) (init ToPartrec.Code.succ [0]) (some (halt output)) 21) := by
  have observed : ((FiniteStackWorker.worker successorCall (fun _word => trList [0])).searcher []).result 21 =
      some (StackMachineContextCall.packet successor (trList [0]) (trList [1])) :=
    compiled_call_keeps_the_original_encoded_argument
  obtain ⟨counted⟩ := FiniteStackWorker.sound_at successorCall (fun _word => trList [0]) []
    (FiniteCompiledMachine.context_clean_halts_at_encoded_input ToPartrec.Code.succ [0])
    (StackMachineContextCall.packet successor (trList [0]) (trList [1])) 21 observed
  exact FiniteCompiledMachine.context_reflects_outputs ToPartrec.Code.succ counted

def omittedTarget (_label : Nat) : TM2.Stmt (fun _key : Unit => Bool) Nat Unit :=
  .goto (fun _state => 1)

theorem omitting_a_reachable_label_refutes_support_closure :
    ¬ (∀ label ∈ ({0} : Finset Nat), TM2.SupportsStmt {0} (omittedTarget label)) := by
  intro closed
  have target := closed 0 (by simp) ()
  simp at target

theorem out_of_support_fallback_does_not_establish_source_correspondence :
    (FiniteSupportMachine.select ({0} : Finset Nat) ⟨0, by simp⟩ 1).val = 0 ∧
      ¬ TM2.SupportsStmt ({0} : Finset Nat) (omittedTarget 0) := by
  constructor
  · decide
  · intro supported
    have impossible := supported ()
    simp at impossible

end CompiledCalls

namespace ConditionalSources

open Turing.PartrecToTM2

attribute [local implicit_reducible] FiniteCompiledMachine.machine FiniteSupportMachine.machine

abbrev secondFieldMachine : FinTM2 := FiniteCompiledMachine.machine ToPartrec.Code.tail
abbrev secondFieldEquality : DecidableEq (secondFieldMachine.Γ secondFieldMachine.k₁) :=
  inferInstanceAs (DecidableEq Γ')
attribute [local instance] secondFieldEquality

def programSource (codec : NaturalWordCodec) :
    ConditionalSourceMachine.Presentation codec (fun program _condition => Part.some program) where
  code := ToPartrec.Code.head
  correct program condition := by simp

def conditionSource (codec : NaturalWordCodec) :
    ConditionalSourceMachine.Presentation codec (fun _program condition => Part.some condition) where
  code := ToPartrec.Code.tail
  correct program condition := by rfl

theorem canonical_query_retains_two_different_fields :
    ConditionalSourceMachine.readQuery (trList [7, 42]) = some (7, 42) := by decide

theorem zero_fields_remain_two_fields :
    ConditionalSourceMachine.readQuery [Γ'.cons, Γ'.cons] = some (0, 0) := by decide

theorem missing_argument_is_not_a_query :
    ConditionalSourceMachine.readQuery (trList [7]) = none := by decide

theorem extra_argument_is_not_a_query :
    ConditionalSourceMachine.readQuery (trList [7, 42, 3]) = none := by decide

theorem unterminated_argument_is_not_a_query :
    ConditionalSourceMachine.readQuery (trNat 7 ++ Γ'.cons :: [Γ'.bit1]) = none := by decide

theorem noncanonical_first_number_is_not_a_query :
    ConditionalSourceMachine.readQuery (Γ'.bit0 :: Γ'.cons :: trList [42]) = none := by decide

theorem field_roles_are_not_interchanged (program condition : Nat) :
    ToPartrec.Code.head.eval [program, condition] = Part.some [program] ∧
      ToPartrec.Code.tail.eval [program, condition] = Part.some [condition] := by simp

theorem distinct_field_order_is_observable :
    ConditionalSourceMachine.readQuery (trList [42, 7]) ≠ some (7, 42) := by decide

theorem condition_field_is_selected_by_the_actual_fixed_machine :
    ((FiniteStackWorker.worker secondFieldMachine (fun _word => trList [7, 42])).searcher []).result 128 =
      some (trList [42]) := by decide

theorem changing_only_the_program_field_does_not_change_this_condition_projection :
    ((FiniteStackWorker.worker secondFieldMachine (fun _word => trList [999, 42])).searcher []).result 128 =
      some (trList [42]) := by decide

theorem swapping_fields_changes_the_actual_source_answer :
    ((FiniteStackWorker.worker secondFieldMachine (fun _word => trList [42, 7])).searcher []).result 128 =
      some (trList [7]) := by decide

end ConditionalSources

namespace NaturalWords

open Turing.PartrecToTM2
open Mettapedia.UniversalAI.TimeBoundedAIXI

attribute [local implicit_reducible] NaturalWordMachine.machine

abbrev outputEquality : DecidableEq (NaturalWordMachine.machine.Γ NaturalWordMachine.machine.k₁) :=
  inferInstanceAs (DecidableEq Γ')
abbrev resultEquality : DecidableEq (NaturalWordMachine.machine.Γ NaturalWordMachine.Stack.result) :=
  inferInstanceAs (DecidableEq Γ')
attribute [local instance] outputEquality resultEquality

theorem empty_word_has_a_complete_zero_field :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => [])).searcher []).result 2 =
      some [Γ'.cons] := by decide

theorem empty_word_still_needs_the_restoration_exit :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => [])).searcher []).result 1 = none := by decide

theorem leading_zero_words_do_not_collapse :
    NaturalWordEncoding.encode [] = 0 ∧ NaturalWordEncoding.encode [false] = 1 ∧
      NaturalWordEncoding.encode [false, false] = 3 ∧ NaturalWordEncoding.encode [true] = 2 := by decide

theorem physical_conversion_matches_the_exact_codec :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => payload)).searcher []).result 9 =
      some [Γ'.bit0, Γ'.bit0, Γ'.bit1, Γ'.bit1, Γ'.cons] := by decide

theorem conversion_is_not_finished_before_its_last_transition :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => payload)).searcher []).result 8 = none := by decide

theorem borrowed_high_sentinel_is_not_emitted_as_a_spurious_zero :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => [false, false, false])).searcher []).result 8 =
      some [Γ'.bit1, Γ'.bit1, Γ'.bit1, Γ'.cons] := by decide

theorem conversion_depends_on_bit_length_not_natural_magnitude :
    ((FiniteStackWorker.worker NaturalWordMachine.machine (fun _word => List.replicate 64 false)).searcher []).result 130 =
      some (List.replicate 64 Γ'.bit1 ++ [Γ'.cons]) := by decide

theorem existing_suffix_is_retained_without_reencoding :
    let initial := NaturalWordMachine.config (some false) true none payload [] [Γ'.consₗ, Γ'.bit0]
    let final := StepCounting.runFor NaturalWordMachine.machine.step 9 initial
    final.l = none ∧ final.stk .result =
      [Γ'.bit0, Γ'.bit0, Γ'.bit1, Γ'.bit1, Γ'.cons, Γ'.consₗ, Γ'.bit0] := by decide

theorem two_field_query_is_prepared_with_the_existing_condition :
    let initial := NaturalWordMachine.config (some false) true none payload []
      (trList [NaturalWordEncoding.encode [false, false]])
    let final := StepCounting.runFor NaturalWordMachine.machine.step 9 initial
    final.l = none ∧ final.stk .result =
      ConditionalSourceMachine.query NaturalWordEncoding.codec payload [false, false] := by decide

theorem codec_and_compiler_field_roundtrip_keep_the_word :
    NaturalWordEncoding.decode (NaturalWordEncoding.encode payload) = payload ∧
      ConditionalSourceMachine.readQuery (ConditionalSourceMachine.query NaturalWordEncoding.codec payload [false]) =
        some (NaturalWordEncoding.encode payload, NaturalWordEncoding.encode [false]) := by
  constructor
  · exact NaturalWordEncoding.decode_encode payload
  · exact ConditionalSourceMachine.query_fields NaturalWordEncoding.codec payload [false]

end NaturalWords

namespace FramedCalls

open WordTemplateMachine

attribute [local instance] ContextCalls.identityInputInhabited

attribute [local implicit_reducible] FramedHeadCall.machine FramedFieldAssembly.machine
  ICSourceCalls.machine ICSourceCalls.invocation ICSourceCalls.firstStage ICSourceCalls.secondStage
  ICSourceCalls.prepareFirst ICSourceCalls.prepareSecond

abbrev identityHead : FinTM2 := FramedHeadCall.machine identity (Equiv.refl Bool)
abbrev identityHeadEquality : DecidableEq (identityHead.Γ identityHead.k₁) :=
  inferInstanceAs (DecidableEq (Option Bool))
attribute [local instance] identityHeadEquality

def metadata : List (Option Bool) := Indexed.frame [[false], [], [true, false], [true, false]]

theorem a_head_call_preserves_empty_fields_order_and_duplicate_metadata :
    ((FiniteStackWorker.worker identityHead (fun _word => Indexed.frame [[true, false]] ++ metadata)).searcher []).result 33 =
      some (Indexed.frame [[true, false]] ++ metadata) := by decide

theorem a_head_call_needs_its_last_transfer :
    ((FiniteStackWorker.worker identityHead (fun _word => Indexed.frame [[true, false]] ++ metadata)).searcher []).result 32 =
      none := by decide

theorem empty_heads_and_tails_remain_distinct_framed_fields :
    ((FiniteStackWorker.worker identityHead (fun _word => Indexed.frame [[], [], [], [true]])).searcher []).result 15 =
      some (Indexed.frame [[], [], [], [true]]) := by decide

theorem a_missing_first_delimiter_is_not_an_empty_head :
    ((FiniteStackWorker.worker identityHead (fun _word => [some true, some false])).searcher []).result 100 = none := by decide

theorem a_completed_head_recovers_a_counted_source_call :
    ∃ output : List Bool,
      output.map some ++ none :: metadata = Indexed.frame [[true, false]] ++ metadata ∧
      Nonempty (TM2OutputsInTime identity [true, false] (some output) 33) := by
  have called := FramedHeadCall.outputs identity (Equiv.refl Bool) metadata
    (StackMachinePortTime.Controls.identityRun [true, false])
  exact FramedHeadCall.reflects_outputs_at identity (Equiv.refl Bool)
    (identity_halts_cleanly [true, false]) metadata called

abbrev loopHead : FinTM2 := FramedHeadCall.machine ContextCalls.loop (Equiv.refl Bool)

theorem a_divergent_source_never_completes_its_framed_call
    (input : List Bool) (tail : List (Option Bool)) (budget : Nat) (state : loopHead.Cfg)
    (executed : EvalsToInTime loopHead.step
      (initList loopHead (input.map some ++ none :: tail)) (some state) budget) : state.l ≠ none := by
  intro stopped
  obtain ⟨after, halted, ⟨original⟩⟩ := FramedHeadCall.terminal_source_halts
    ContextCalls.loop (Equiv.refl Bool) tail executed stopped
  have same := ContextCalls.loop_source_reaches_only_its_initial_configuration input after
    (StackMachineComposition.execution_reaches original.toEvalsTo)
  rw [same] at halted
  cases halted

def groups : List (List (Fin 3)) := [[2, 0], [1], [], [2, 2]]
abbrev grouped : FinTM2 := FramedFieldAssembly.machine (Γ := Bool) groups

noncomputable def grouped_run : TM2OutputsInTime grouped
    (Indexed.frame [payload, [], [false]])
    (some (Indexed.frame [[false, true, false, true], [], [], [false, false]])) 384 := by
  have run := FramedFieldAssembly.outputs (Γ := Bool) groups
    (![payload, [], [false]] : Fin 3 → List Bool)
  simpa [grouped, groups, payload, Indexed.argumentWire, ← List.ofFn_eq_map, List.ofFn_succ,
    Indexed.frame] using run

theorem grouped_assembly_executes_concatenation_reordering_empty_and_repeated_fields :
    ((FiniteStackWorker.worker grouped (fun _word => Indexed.frame [payload, [], [false]])).searcher []).result 384 =
      some (Indexed.frame [[false, true, false, true], [], [], [false, false]]) :=
  FiniteStackWorker.complete grouped (fun _word => Indexed.frame [payload, [], [false]]) [] _ _ grouped_run

end FramedCalls

namespace DependentCalls

open Turing.PartrecToTM2 WordTemplateMachine
open Mettapedia.UniversalAI.TimeBoundedAIXI

attribute [local implicit_reducible] FiniteCompiledMachine.machine FiniteSupportMachine.machine
  ICSourceCalls.machine ICSourceCalls.invocation ICSourceCalls.firstStage ICSourceCalls.secondStage
  ICSourceCalls.prepareFirst ICSourceCalls.prepareSecond FramedHeadCall.machine FramedFieldAssembly.machine
attribute [local instance] FiniteCompiledMachine.inputInhabited FiniteCompiledMachine.outputFinite
  FiniteCompiledMachine.outputInhabited

/-- The compiled source increments the second argument and ignores the first. -/
def code : ToPartrec.Code := .comp .succ .tail
abbrev source : FinTM2 := FiniteCompiledMachine.machine code
abbrev pipeline : FinTM2 := ICSourceCalls.machine source (Equiv.refl Γ')

def extract_run : EvalsToInTime (TM2.step tr) (init code [1, 3]) (some (halt [4])) 64 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 64 (init code [1, 3])
  have final : StepCounting.runFor (TM2.step tr) 64 (init code [1, 3]) = halt [4] := by
    let state := StepCounting.runFor (TM2.step tr) 64 (init code [1, 3])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [4]) [] [] [] := by
      funext key
      cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [4] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

def reconstruct_run : EvalsToInTime (TM2.step tr) (init code [7, 4]) (some (halt [5])) 64 := by
  have counted := FiniteStackWorker.executionWithin (TM2.step tr) 64 (init code [7, 4])
  have final : StepCounting.runFor (TM2.step tr) 64 (init code [7, 4]) = halt [5] := by
    let state := StepCounting.runFor (TM2.step tr) 64 (init code [7, 4])
    have label : state.l = none := by decide
    have registers : state.var = none := by decide
    have contents : state.stk = K'.elim (trList [5]) [] [] [] := by
      funext key
      cases key <;> decide
    calc state = TM2.Cfg.mk state.l state.var state.stk := rfl
      _ = halt [5] := by rw [label, registers, contents]; rfl
  simpa only [final] using counted

def query : List (Option Γ') := Indexed.frame [trList [1], trList [7], trList [3]]
def expected : List (Option Γ') := Indexed.frame [trList [5], trList [7], trList [4], trList [3]]

noncomputable def pipeline_run : TM2OutputsInTime pipeline query (some expected) 4096 := by
  have extracted := FiniteCompiledMachine.outputs code extract_run
  have reconstructed := FiniteCompiledMachine.outputs code reconstruct_run
  have calls := ICSourceCalls.outputs source (Equiv.refl Γ') (trList [1]) (trList [7]) (trList [3])
    (trList [4]) (trList [5]) 64 64 extracted (by
      change TM2OutputsInTime source (trList [7] ++ (trList [4]).map id) _ _
      simpa only [source, List.map_id, trList, List.append_assoc, List.append_nil,
        List.singleton_append] using reconstructed)
  change TM2OutputsInTime pipeline query
    (some (Indexed.frame [(trList [5]).map id, trList [7], (trList [4]).map id, trList [3]])) _ at calls
  simp only [List.map_id] at calls
  exact ⟨calls.toEvalsTo, calls.steps_le_m.trans (by decide)⟩

theorem the_second_call_uses_the_first_calls_residual :
    ((FiniteStackWorker.worker pipeline (fun _word => query)).searcher []).result 4096 = some expected :=
  FiniteStackWorker.complete pipeline (fun _word => query) [] expected 4096 pipeline_run

theorem reusing_the_original_in_place_of_the_residual_changes_the_result :
    ((FiniteStackWorker.worker pipeline (fun _word => query)).searcher []).result 4096 ≠
      some (Indexed.frame [trList [4], trList [7], trList [4], trList [3]]) := by
  rw [the_second_call_uses_the_first_calls_residual]
  decide

theorem source_call_completion_does_not_establish_reconstruction : trList [5] ≠ trList [3] := by decide

def incrementCondition (_program condition : BinString) : Part BinString :=
  Part.some (NaturalWordEncoding.decode (NaturalWordEncoding.encode condition + 1))

def presentation : ConditionalSourceMachine.Presentation NaturalWordEncoding.codec incrementCondition where
  code := code
  correct _program _condition := by
    simp [code, incrementCondition, NaturalWordEncoding.codec, NaturalWordEncoding.encode_decode]

def conditional_extract : TM2OutputsInTime (ConditionalSourceMachine.machine presentation)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec
      (NaturalWordEncoding.decode 1) (NaturalWordEncoding.decode 3))
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec (NaturalWordEncoding.decode 4))) 64 := by
  simpa only [ConditionalSourceMachine.machine, presentation, ConditionalSourceMachine.query,
    ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode_decode] using
    FiniteCompiledMachine.outputs code extract_run

def conditional_reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine presentation)
    (ConditionalSourceMachine.query NaturalWordEncoding.codec
      (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 4))
    (some (ConditionalSourceMachine.answer NaturalWordEncoding.codec (NaturalWordEncoding.decode 5))) 64 := by
  simpa only [ConditionalSourceMachine.machine, presentation, ConditionalSourceMachine.query,
    ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode_decode] using
    FiniteCompiledMachine.outputs code reconstruct_run

theorem physical_calls_have_both_declared_conditional_meanings :
    NaturalWordEncoding.decode 4 ∈ incrementCondition (NaturalWordEncoding.decode 1) (NaturalWordEncoding.decode 3) ∧
      NaturalWordEncoding.decode 5 ∈ incrementCondition (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 4) :=
  ICConditionalCalls.source_meanings presentation conditional_extract conditional_reconstruct

theorem conditional_pipeline_returns_the_same_ordered_packet :
    ((FiniteStackWorker.worker (ICConditionalCalls.machine presentation)
      (fun _word => ICConditionalCalls.input NaturalWordEncoding.codec
        (NaturalWordEncoding.decode 1) (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 3))).searcher []).result 4096 =
      some (ICConditionalCalls.result NaturalWordEncoding.codec
        (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 3)
        (NaturalWordEncoding.decode 4) (NaturalWordEncoding.decode 5)) := by
  have run := ICConditionalCalls.outputs presentation conditional_extract conditional_reconstruct
  have bounded : TM2OutputsInTime (ICConditionalCalls.machine presentation)
      (ICConditionalCalls.input NaturalWordEncoding.codec
        (NaturalWordEncoding.decode 1) (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 3))
      (some (ICConditionalCalls.result NaturalWordEncoding.codec
        (NaturalWordEncoding.decode 7) (NaturalWordEncoding.decode 3)
        (NaturalWordEncoding.decode 4) (NaturalWordEncoding.decode 5))) 4096 :=
    ⟨run.toEvalsTo, run.steps_le_m.trans (by
      simp only [ICConditionalCalls.overhead, ICConditionalCalls.input, ICConditionalCalls.field,
        ConditionalSourceMachine.answer, NaturalWordEncoding.codec, NaturalWordEncoding.encode_decode]
      decide)⟩
  exact FiniteStackWorker.complete _ _ [] _ _ bounded

end DependentCalls

end Mettapedia.Examples.Compression.FeatureMachineTimeControls

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Mettapedia.Computability.StackMachineComposition,
    `Mettapedia.Computability.StackMachinePortTime, `Mettapedia.Computability.StackMachineCompositionReflection,
    `Mettapedia.Computability.StackMachineOutputRelay, `Mettapedia.Computability.StackMachineContextCall,
    `Mettapedia.Computability.FiniteSupportMachine, `Mettapedia.Machines.FiniteCompiledMachine,
    `Mettapedia.Machines.ConditionalSourceMachine,
    `Mettapedia.Computability.KolmogorovComplexity.NaturalWordEncoding,
    `Mettapedia.Computability.NaturalWordMachine,
    `Mettapedia.Computability.FramedHeadCall,
    `Mettapedia.Computability.FramedFieldAssembly,
    `Mettapedia.Machines.ICSourceCalls,
    `Mettapedia.Machines.ICConditionalCalls,
    `Mettapedia.Computability.StackMachineCompositionTail,
    `Mettapedia.Computability.WordDropLastMachine,
    `Mettapedia.Computability.NaturalWordDecodingMachine,
    `Mettapedia.Computability.FramedCompressionCheck,
    `Mettapedia.Machines.ICPhysicalCheck,
    `Mettapedia.Examples.Compression.PhysicalCheckControls,
    `Mettapedia.Computability.BinaryCountdownMachine,
    `Mettapedia.Machines.ICPreparedCheck,
    `Mettapedia.Machines.ICSourceClock,
    `Mettapedia.Machines.PreparedICSearch,
    `Mettapedia.Examples.Compression.PreparedSourceControls,
    `Mettapedia.Computability.E2PairMachine,
    `Mettapedia.Machines.ICEntryCheck,
    `Mettapedia.Examples.Compression.E2EntryControls,
    `Mettapedia.Machines.FiniteStackWorker,
    `Mettapedia.Machines.HierarchicalSourceTime]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut names : Array Name := #[]
  let mut regular : NameSet := {}
  let mut seen : NameSet := {}
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName | throwError "missing source-time module {moduleName}"
    let data := env.header.moduleData[index]!
    names := names ++ data.constNames ++ data.extraConstNames
    for name in data.constNames do regular := regular.insert name
  for (name, _) in env.constants.toList do
    let publicName := (privateToUserName? name).getD name
    if (`Mettapedia.Examples.Compression.FeatureMachineTimeControls).isPrefixOf publicName then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  let mut compilerImplementations : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | do
      if regular.contains name then throwError "missing source-time declaration {name}"
      continue
    if info.isUnsafe || info.isPartial then
      let some owner := Mettapedia.Logic.KernelFoundationManifest.runtimeCounterpart? env name
        | throwError "unmatched source-time compiler declaration {name}"
      let some ownerInfo := env.checked.get.find? owner | throwError "missing source-time logical owner {owner}"
      if ownerInfo.isUnsafe || ownerInfo.isPartial then throwError "nonlogical source-time owner {owner}"
      compilerImplementations := compilerImplementations.push
        (Json.mkObj [("name", toJson name.toString), ("logicalOwner", toJson owner.toString),
          ("matchingTypeLevelsAndOwner", toJson true)])
      continue
    if info matches .axiomInfo _ then throwError "new source-time axiom {name}"
    let mut references := info.type.getUsedConstants
    if let some body := info.value? (allowOpaque := true) then references := references ++ body.getUsedConstants
    for reference in references do
      if let some referencedInfo := env.checked.get.find? reference then
        if referencedInfo.isUnsafe || referencedInfo.isPartial then throwError "nonlogical source-time reference {name}: {reference}"
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unpermitted source-time dependency {name}: {dependency}"
    safe := safe + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
      audited := audited.push (Json.mkObj [("name", toJson name.toString),
        ("axioms", toJson (dependencies.map Name.toString))])
  liftIO <| IO.println (Json.mkObj [("sourceMachineTimeDeclarations", toJson safe),
    ("theorems", toJson theorems), ("auditedTheorems", toJson audited),
    ("separateCompilerImplementations", toJson compilerImplementations.size),
    ("compilerImplementations", toJson compilerImplementations)]).compress
