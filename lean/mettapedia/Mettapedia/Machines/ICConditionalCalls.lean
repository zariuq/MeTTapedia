import Mettapedia.Machines.ICSourceCalls
import Mettapedia.Computability.NaturalWordMachine

/-!
# Dependent calls to one fixed conditional interpreter

An encoded task retains its descriptive program, feature and original word.
The physical pipeline calls the unchanged interpreter twice, using the first
call's residual as the second call's auxiliary input. All field assembly,
handoff and copying is charged. The interface starts with encoded input;
encoding preparation is not hidden in the source clock.

The returned packet is not an acceptance certificate. Reconstructed equality
and strict shortening are subsequent checks, not hypotheses of call completion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICConditionalCalls

open Turing KolmogorovComplexity
open Turing.PartrecToTM2
open Mettapedia.Computability WordTemplateMachine

attribute [local implicit_reducible] ConditionalSourceMachine.machine FiniteCompiledMachine.machine
  FiniteSupportMachine.machine ICSourceCalls.machine ICSourceCalls.invocation ICSourceCalls.firstStage
  ICSourceCalls.secondStage ICSourceCalls.prepareFirst ICSourceCalls.prepareSecond
attribute [local instance] FiniteCompiledMachine.inputInhabited FiniteCompiledMachine.outputFinite
  FiniteCompiledMachine.outputInhabited

def field (codec : NaturalWordCodec) (word : BinString) : List Γ' :=
  ConditionalSourceMachine.answer codec word

theorem query_assembly (codec : NaturalWordCodec) (program condition : BinString) :
    field codec program ++ field codec condition = ConditionalSourceMachine.query codec program condition := by
  simp [field, ConditionalSourceMachine.answer, ConditionalSourceMachine.query, trList, List.append_assoc]

def input (codec : NaturalWordCodec) (descriptive feature original : BinString) : List (Option Γ') :=
  Indexed.frame [field codec descriptive, field codec feature, field codec original]

def result (codec : NaturalWordCodec) (feature original residual rebuilt : BinString) : List (Option Γ') :=
  Indexed.frame [field codec rebuilt, field codec feature, field codec residual, field codec original]

def overhead (codec : NaturalWordCodec) (descriptive feature original residual rebuilt : BinString) : Nat :=
  128 * ((input codec descriptive feature original).length +
    (field codec residual).length + (field codec rebuilt).length + 1)

variable {codec : NaturalWordCodec} {algorithm : ConditionalAlgorithm}

local instance (source : ConditionalSourceMachine.Presentation codec algorithm) :
    Inhabited ((ConditionalSourceMachine.machine source).Γ (ConditionalSourceMachine.machine source).k₀) :=
  inferInstanceAs (Inhabited Γ')
local instance (source : ConditionalSourceMachine.Presentation codec algorithm) :
    Fintype ((ConditionalSourceMachine.machine source).Γ (ConditionalSourceMachine.machine source).k₁) :=
  inferInstanceAs (Fintype Γ')
local instance (source : ConditionalSourceMachine.Presentation codec algorithm) :
    Inhabited ((ConditionalSourceMachine.machine source).Γ (ConditionalSourceMachine.machine source).k₁) :=
  inferInstanceAs (Inhabited Γ')

def machine (source : ConditionalSourceMachine.Presentation codec algorithm) : FinTM2 :=
  ICSourceCalls.machine (ConditionalSourceMachine.machine source) (Equiv.refl Γ')

attribute [local implicit_reducible] machine

/-- This clock uses the two actual source executions, with an explicit physical
overhead. Neither effectiveness nor compiler correctness supplies a speed law. -/
noncomputable def outputs (source : ConditionalSourceMachine.Presentation codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query codec descriptive original)
      (some (ConditionalSourceMachine.answer codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query codec feature residual)
      (some (ConditionalSourceMachine.answer codec rebuilt)) secondTime) :
    TM2OutputsInTime (machine source) (input codec descriptive feature original)
      (some (result codec feature original residual rebuilt))
      (firstTime + secondTime + overhead codec descriptive feature original residual rebuilt) := by
  have extracted : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (field codec descriptive ++ field codec original) (some (field codec residual)) firstTime := by
    rw [query_assembly]
    exact extract
  have reconstructed : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (field codec feature ++ (field codec residual).map (Equiv.refl Γ'))
      (some (field codec rebuilt)) secondTime := by
    change TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (field codec feature ++ (field codec residual).map id) _ _
    rw [List.map_id, query_assembly]
    exact reconstruct
  have called := ICSourceCalls.outputs (ConditionalSourceMachine.machine source) (Equiv.refl Γ')
    (field codec descriptive) (field codec feature) (field codec original)
    (field codec residual) (field codec rebuilt) firstTime secondTime extracted reconstructed
  change TM2OutputsInTime (machine source) (input codec descriptive feature original)
    (some (Indexed.frame [(field codec rebuilt).map id, field codec feature,
      (field codec residual).map id, field codec original])) _ at called
  simpa only [List.map_id, overhead, ICSourceCalls.input, input, result] using called

/-- The meaning of both counted source calls comes from the fixed compiler
presentation, not from treating the first output as a reconstruction proof. -/
theorem source_meanings (source : ConditionalSourceMachine.Presentation codec algorithm)
    {descriptive feature original residual rebuilt : BinString} {firstTime secondTime : Nat}
    (extract : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query codec descriptive original)
      (some (ConditionalSourceMachine.answer codec residual)) firstTime)
    (reconstruct : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query codec feature residual)
      (some (ConditionalSourceMachine.answer codec rebuilt)) secondTime) :
    residual ∈ algorithm descriptive original ∧ rebuilt ∈ algorithm feature residual :=
  ⟨ConditionalSourceMachine.sound source extract, ConditionalSourceMachine.sound source reconstruct⟩

theorem eventually_outputs (source : ConditionalSourceMachine.Presentation codec algorithm)
    {descriptive feature original residual rebuilt : BinString}
    (extract : residual ∈ algorithm descriptive original)
    (reconstruct : rebuilt ∈ algorithm feature residual) :
    ∃ firstTime secondTime, Nonempty (TM2OutputsInTime (machine source)
      (input codec descriptive feature original) (some (result codec feature original residual rebuilt))
      (firstTime + secondTime + overhead codec descriptive feature original residual rebuilt)) := by
  obtain ⟨firstTime, ⟨firstRun⟩⟩ := ConditionalSourceMachine.complete source extract
  obtain ⟨secondTime, ⟨secondRun⟩⟩ := ConditionalSourceMachine.complete source reconstruct
  exact ⟨firstTime, secondTime, ⟨outputs source firstRun secondRun⟩⟩

/-- One source code is chosen before all task words and both invocations.
This is the plain universal interpreter, without a prefix-domain assertion. -/
theorem fixed_universal_pipeline (codec : NaturalWordCodec) :
    ∃ source : ConditionalSourceMachine.Presentation codec universalConditionalAlgorithm,
      ∀ descriptive feature original residual rebuilt : BinString,
        residual ∈ universalConditionalAlgorithm descriptive original →
        rebuilt ∈ universalConditionalAlgorithm feature residual →
        ∃ firstTime secondTime, Nonempty (TM2OutputsInTime (machine source)
          (input codec descriptive feature original) (some (result codec feature original residual rebuilt))
          (firstTime + secondTime + overhead codec descriptive feature original residual rebuilt)) := by
  obtain ⟨source⟩ := ConditionalSourceMachine.universal_has_fixed_source codec
  exact ⟨source, fun _descriptive _feature _original _residual _rebuilt extract reconstruct =>
    eventually_outputs source extract reconstruct⟩

/-- Completion of the physical pipeline implies completion of both dependent
conditional computations. The underlying interpreter need not be total. -/
theorem terminal_computations (source : ConditionalSourceMachine.Presentation codec algorithm)
    {descriptive feature original : BinString} {final : (machine source).Cfg} {time : Nat}
    (executed : StateTransition.EvalsToInTime (machine source).step
      (initList (machine source) (input codec descriptive feature original)) (some final) time)
    (stopped : final.l = none) :
    ∃ residual rebuilt : BinString, residual ∈ algorithm descriptive original ∧ rebuilt ∈ algorithm feature residual ∧
      Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
        (ConditionalSourceMachine.query codec descriptive original) (some (field codec residual)) time) ∧
      Nonempty (TM2OutputsInTime (ConditionalSourceMachine.machine source)
        (ConditionalSourceMachine.query codec feature residual) (some (field codec rebuilt)) time) := by
  have cleanFirst : ∀ state : (ConditionalSourceMachine.machine source).Cfg,
      StateTransition.Reaches (ConditionalSourceMachine.machine source).step
        (initList (ConditionalSourceMachine.machine source) (field codec descriptive ++ field codec original)) state →
      state.l = none → ∃ output, state = haltList (ConditionalSourceMachine.machine source) output := by
    intro state path halted
    rw [query_assembly] at path
    obtain ⟨numbers, canonical⟩ := FiniteCompiledMachine.clean_halts_at_encoded_input source.code
      [codec.encode descriptive, codec.encode original] state path halted
    exact ⟨trList numbers, canonical⟩
  obtain ⟨physicalResidual, ⟨firstRun⟩, secondState, secondStopped, ⟨secondRun⟩⟩ :=
    ICSourceCalls.terminal_calls (ConditionalSourceMachine.machine source) (Equiv.refl Γ')
      (field codec descriptive) (field codec feature) (field codec original) cleanFirst executed stopped
  have firstQuery : TM2OutputsInTime (ConditionalSourceMachine.machine source)
      (ConditionalSourceMachine.query codec descriptive original) (some physicalResidual) time := by
    exact Eq.mp (congrArg (fun word : List Γ' =>
      TM2OutputsInTime (ConditionalSourceMachine.machine source) word (some physicalResidual) time)
      (query_assembly codec descriptive original)) firstRun
  obtain ⟨residual, extracts, firstCanonical, firstCounted⟩ :=
    ConditionalSourceMachine.terminal_meaning source firstQuery rfl
  have sameResidual : physicalResidual = field codec residual := by
    have read := congrArg (fun state : (ConditionalSourceMachine.machine source).Cfg =>
      state.stk (ConditionalSourceMachine.machine source).k₁) firstCanonical
    simpa [field, haltList] using read
  subst physicalResidual
  change StateTransition.EvalsToInTime (ConditionalSourceMachine.machine source).step
    (initList (ConditionalSourceMachine.machine source) (field codec feature ++ (field codec residual).map id))
    (some secondState) time at secondRun
  rw [List.map_id, query_assembly] at secondRun
  obtain ⟨rebuilt, reconstructs, _secondCanonical, secondCounted⟩ :=
    ConditionalSourceMachine.terminal_meaning source secondRun secondStopped
  exact ⟨residual, rebuilt, extracts, reconstructs, firstCounted, secondCounted⟩

/-- The constant is uniform before all program strings. The dense codec bounds
physical cells by word bits; it does not bound source computation by bit length. -/
theorem dense_overhead_bound (descriptive feature original residual rebuilt : BinString) :
    overhead NaturalWordEncoding.codec descriptive feature original residual rebuilt ≤
      128 * (descriptive.length + feature.length + original.length + residual.length + rebuilt.length + 14) := by
  have g := (NaturalWordMachine.field_length_bounds descriptive).2
  have f := (NaturalWordMachine.field_length_bounds feature).2
  have x := (NaturalWordMachine.field_length_bounds original).2
  have r := (NaturalWordMachine.field_length_bounds residual).2
  have y := (NaturalWordMachine.field_length_bounds rebuilt).2
  simp only [overhead, input, Indexed.frame, List.flatMap_cons, List.flatMap_nil,
    List.length_append, List.length_map, List.length_cons, List.length_nil]
  simp only [field, ConditionalSourceMachine.answer, NaturalWordEncoding.codec]
  omega

end Mettapedia.Machines.ICConditionalCalls
