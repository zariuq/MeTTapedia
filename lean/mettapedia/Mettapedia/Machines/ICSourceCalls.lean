import Mettapedia.Computability.FramedHeadCall
import Mettapedia.Computability.FramedFieldAssembly
import Mettapedia.Computability.StackMachineCompositionTail

/-!
# Physical dependent source calls for a checked autoencoder

Fixed field templates retain the feature and original source around the
extraction call, then construct the reconstruction query from the returned
residual. Both invocations use the same unchanged source program. Physical
assembly, call setup, collection, metadata copying and handoff are charged.

The returned four-field frame is deliberately unchecked: reconstruction
equality and strict shortening remain the subsequent checker stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Machines.ICSourceCalls

open Turing StateTransition
open Mettapedia.Computability
open WordTemplateMachine

def firstGroups : List (List (Fin 3)) := [[0, 2], [1], [2]]
def secondGroups : List (List (Fin 3)) := [[1, 0], [1], [0], [2]]

variable (source : FinTM2) [Inhabited (source.Γ source.k₀)]
  [Fintype (source.Γ source.k₁)] [Inhabited (source.Γ source.k₁)]
  (bridge : source.Γ source.k₁ ≃ source.Γ source.k₀)

local instance : Fintype (source.Γ source.k₀) := source.Γk₀Fin

def prepareFirst : FinTM2 := FramedFieldAssembly.machine (Γ := source.Γ source.k₀) firstGroups
def prepareSecond : FinTM2 := FramedFieldAssembly.machine (Γ := source.Γ source.k₀) secondGroups
def invocation : FinTM2 := FramedHeadCall.machine source bridge

local instance : Fintype ((prepareFirst source).Γ (prepareFirst source).k₁) :=
  inferInstanceAs (Fintype (Option (source.Γ source.k₀)))
local instance : Inhabited ((prepareFirst source).Γ (prepareFirst source).k₁) :=
  inferInstanceAs (Inhabited (Option (source.Γ source.k₀)))
local instance : Fintype ((prepareSecond source).Γ (prepareSecond source).k₁) :=
  inferInstanceAs (Fintype (Option (source.Γ source.k₀)))
local instance : Inhabited ((prepareSecond source).Γ (prepareSecond source).k₁) :=
  inferInstanceAs (Inhabited (Option (source.Γ source.k₀)))
local instance : Fintype ((invocation source bridge).Γ (invocation source bridge).k₁) :=
  inferInstanceAs (Fintype (Option (source.Γ source.k₀)))
local instance : Inhabited ((invocation source bridge).Γ (invocation source bridge).k₁) :=
  inferInstanceAs (Inhabited (Option (source.Γ source.k₀)))

def firstStage : FinTM2 := StackMachineComposition.machine (prepareFirst source) (invocation source bridge)
  (Equiv.refl (Option (source.Γ source.k₀)))

local instance : Fintype ((firstStage source bridge).Γ (firstStage source bridge).k₁) :=
  inferInstanceAs (Fintype (Option (source.Γ source.k₀)))
local instance : Inhabited ((firstStage source bridge).Γ (firstStage source bridge).k₁) :=
  inferInstanceAs (Inhabited (Option (source.Γ source.k₀)))

def secondStage : FinTM2 := StackMachineComposition.machine (firstStage source bridge) (prepareSecond source)
  (Equiv.refl (Option (source.Γ source.k₀)))

local instance : Fintype ((secondStage source bridge).Γ (secondStage source bridge).k₁) :=
  inferInstanceAs (Fintype (Option (source.Γ source.k₀)))
local instance : Inhabited ((secondStage source bridge).Γ (secondStage source bridge).k₁) :=
  inferInstanceAs (Inhabited (Option (source.Γ source.k₀)))

def machine : FinTM2 := StackMachineComposition.machine (secondStage source bridge) (invocation source bridge)
  (Equiv.refl (Option (source.Γ source.k₀)))

attribute [local implicit_reducible] prepareFirst prepareSecond invocation firstStage secondStage machine

def input (descriptive feature original : List (source.Γ source.k₀)) : List (Option (source.Γ source.k₀)) :=
  Indexed.frame [descriptive, feature, original]

def result (feature original : List (source.Γ source.k₀)) (residual rebuilt : List (source.Γ source.k₁)) :
    List (Option (source.Γ source.k₀)) :=
  Indexed.frame [rebuilt.map bridge, feature, residual.map bridge, original]

noncomputable def first_preparation (descriptive feature original : List (source.Γ source.k₀)) :
    TM2OutputsInTime (prepareFirst source) (input source descriptive feature original)
      (some (Indexed.frame [descriptive ++ original, feature, original]))
      (40 * ((input source descriptive feature original).length + 1)) := by
  have run := FramedFieldAssembly.outputs (Γ := source.Γ source.k₀) firstGroups
    (![descriptive, feature, original] : Fin 3 → List (source.Γ source.k₀))
  simpa [prepareFirst, firstGroups, input, Indexed.argumentWire,
    ← List.ofFn_eq_map, List.ofFn_succ, List.append_assoc] using run

noncomputable def second_preparation (feature original : List (source.Γ source.k₀))
    (residual : List (source.Γ source.k₁)) :
    TM2OutputsInTime (prepareSecond source) (Indexed.frame [residual.map bridge, feature, original])
      (some (Indexed.frame [feature ++ residual.map bridge, feature, residual.map bridge, original]))
      (48 * ((Indexed.frame [residual.map bridge, feature, original]).length + 1)) := by
  have run := FramedFieldAssembly.outputs (Γ := source.Γ source.k₀) secondGroups
    (![residual.map bridge, feature, original] : Fin 3 → List (source.Γ source.k₀))
  simpa [prepareSecond, secondGroups, Indexed.argumentWire,
    ← List.ofFn_eq_map, List.ofFn_succ, List.append_assoc] using run

def prefixClock (descriptive feature original : List (source.Γ source.k₀))
    (residual : List (source.Γ source.k₁)) (firstTime : Nat) : Nat :=
  40 * ((input source descriptive feature original).length + 1) +
    2 * (Indexed.frame [descriptive ++ original, feature, original]).length + 2 +
    (firstTime + 2 * (descriptive ++ original).length + 2 * residual.length +
      2 * (Indexed.frame [feature, original]).length + 6) +
    2 * (Indexed.frame [residual.map bridge, feature, original]).length + 2 +
    48 * ((Indexed.frame [residual.map bridge, feature, original]).length + 1)

noncomputable def secondStage_outputs (descriptive feature original : List (source.Γ source.k₀))
    (residual : List (source.Γ source.k₁)) (firstTime : Nat)
    (extract : TM2OutputsInTime source (descriptive ++ original) (some residual) firstTime) :
    TM2OutputsInTime (secondStage source bridge) (input source descriptive feature original)
      (some (Indexed.frame [feature ++ residual.map bridge, feature, residual.map bridge, original]))
      (prefixClock source bridge descriptive feature original residual firstTime) := by
  let firstPacket := Indexed.frame [descriptive ++ original, feature, original]
  let afterFirst := Indexed.frame [residual.map bridge, feature, original]
  let secondPacket := Indexed.frame [feature ++ residual.map bridge, feature, residual.map bridge, original]
  have prepared := first_preparation source descriptive feature original
  let firstCallTime := firstTime + 2 * (descriptive ++ original).length +
    2 * residual.length + 2 * (Indexed.frame [feature, original]).length + 6
  have called : TM2OutputsInTime (invocation source bridge) firstPacket (some afterFirst) firstCallTime := by
    have run := FramedHeadCall.outputs source bridge (Indexed.frame [feature, original]) extract
    simpa [invocation, firstPacket, afterFirst, firstCallTime, Indexed.frame, List.map_map,
      Function.comp_def, List.append_assoc] using run
  have first := StackMachineComposition.outputs (prepareFirst source) (invocation source bridge)
    (Equiv.refl (Option (source.Γ source.k₀))) (input source descriptive feature original)
    firstPacket afterFirst _ firstCallTime prepared (by
      change TM2OutputsInTime (invocation source bridge) (firstPacket.map id) _ _
      simpa only [List.map_id] using called)
  have secondPrepared := second_preparation source bridge feature original residual
  have second := StackMachineComposition.outputs (firstStage source bridge) (prepareSecond source)
    (Equiv.refl (Option (source.Γ source.k₀))) (input source descriptive feature original) afterFirst secondPacket
    _ _ first (by
      change TM2OutputsInTime (prepareSecond source) (afterFirst.map id) _ _
      simpa only [List.map_id] using secondPrepared)
  exact second

/-- The original source times are joined to the actual physical two-call
pipeline. The returned frame retains all information needed by its checker.
The constant is fixed before every candidate and source occurrence. -/
noncomputable def outputs (descriptive feature original : List (source.Γ source.k₀))
    (residual rebuilt : List (source.Γ source.k₁)) (firstTime secondTime : Nat)
    (extract : TM2OutputsInTime source (descriptive ++ original) (some residual) firstTime)
    (reconstruct : TM2OutputsInTime source (feature ++ residual.map bridge) (some rebuilt) secondTime) :
    TM2OutputsInTime (machine source bridge) (input source descriptive feature original)
      (some (result source bridge feature original residual rebuilt))
      (firstTime + secondTime + 128 * ((input source descriptive feature original).length +
        residual.length + rebuilt.length + 1)) := by
  let secondPacket := Indexed.frame [feature ++ residual.map bridge, feature, residual.map bridge, original]
  have second := secondStage_outputs source bridge descriptive feature original residual firstTime extract
  let secondCallTime := secondTime + 2 * (feature ++ residual.map bridge).length +
    2 * rebuilt.length + 2 * (Indexed.frame [feature, residual.map bridge, original]).length + 6
  have reconstructed : TM2OutputsInTime (invocation source bridge) secondPacket
      (some (result source bridge feature original residual rebuilt)) secondCallTime := by
    have run := FramedHeadCall.outputs source bridge (Indexed.frame [feature, residual.map bridge, original]) reconstruct
    simpa [invocation, secondPacket, result, secondCallTime, Indexed.frame, List.map_map,
      Function.comp_def, List.append_assoc] using run
  have joined := StackMachineComposition.outputs (secondStage source bridge) (invocation source bridge)
    (Equiv.refl (Option (source.Γ source.k₀))) (input source descriptive feature original) secondPacket
    (result source bridge feature original residual rebuilt) _ secondCallTime second
    (by
      change TM2OutputsInTime (invocation source bridge) (secondPacket.map id) _ _
      simpa only [List.map_id] using reconstructed)
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  simp only [prefixClock, secondCallTime, input,
    secondPacket, Indexed.frame, List.length_append, List.length_map,
    List.length_cons, List.length_nil, List.flatMap_cons, List.flatMap_nil]
  omega

/-- A completed pipeline contains both genuine source halts. Clean halting is
needed only at the first admitted query to construct the dependent second one;
termination of neither invocation is assumed in advance. -/
theorem terminal_calls (descriptive feature original : List (source.Γ source.k₀))
    (cleanFirst : ∀ state : source.Cfg, Reaches source.step (initList source (descriptive ++ original)) state →
      state.l = none → ∃ residual, state = haltList source residual)
    {final : (machine source bridge).Cfg} {time : Nat}
    (executed : EvalsToInTime (machine source bridge).step
      (initList (machine source bridge) (input source descriptive feature original)) (some final) time)
    (stopped : final.l = none) :
    ∃ residual : List (source.Γ source.k₁),
      Nonempty (TM2OutputsInTime source (descriptive ++ original) (some residual) time) ∧
      ∃ rebuilt : source.Cfg, rebuilt.l = none ∧
        Nonempty (EvalsToInTime source.step (initList source (feature ++ residual.map bridge)) (some rebuilt) time) := by
  obtain ⟨stageTwo, stoppedTwo, ⟨ranTwo⟩⟩ := StackMachineComposition.terminal_first_halts
    (secondStage source bridge) (invocation source bridge) (Equiv.refl (Option (source.Γ source.k₀))) executed stopped
  obtain ⟨stageOne, stoppedOne, ⟨ranOne⟩⟩ := StackMachineComposition.terminal_first_halts
    (firstStage source bridge) (prepareSecond source) (Equiv.refl (Option (source.Γ source.k₀))) ranTwo stoppedTwo
  have prepared := first_preparation source descriptive feature original
  obtain ⟨headOne, embeddedOne, ⟨headRunOne⟩⟩ := StackMachineComposition.terminal_after_known_first
    (prepareFirst source) (invocation source bridge) (Equiv.refl (Option (source.Γ source.k₀)))
    prepared ranOne stoppedOne
  have headStoppedOne : headOne.l = none :=
    (StackMachineComposition.secondConfig_halted_iff (prepareFirst source) (invocation source bridge)
      (Equiv.refl (Option (source.Γ source.k₀))) headOne).mp (by rw [embeddedOne]; exact stoppedOne)
  change EvalsToInTime (invocation source bridge).step
    (initList (invocation source bridge) ((Indexed.frame [descriptive ++ original, feature, original]).map id))
    (some headOne) time at headRunOne
  have firstHead : EvalsToInTime (FramedHeadCall.machine source bridge).step
      (initList (FramedHeadCall.machine source bridge)
        ((descriptive ++ original).map some ++ none :: Indexed.frame [feature, original])) (some headOne) time := by
    simpa [invocation, Indexed.frame, List.append_assoc] using headRunOne
  obtain ⟨sourceOne, sourceStoppedOne, ⟨sourceRunOne⟩⟩ := FramedHeadCall.terminal_source_halts
    source bridge (Indexed.frame [feature, original]) firstHead headStoppedOne
  obtain ⟨residual, sourceSame⟩ := cleanFirst sourceOne
    (StackMachineComposition.execution_reaches sourceRunOne.toEvalsTo) sourceStoppedOne
  have firstCall : TM2OutputsInTime source (descriptive ++ original) (some residual) time := by
    simpa only [sourceSame, TM2OutputsInTime, Option.map_some] using sourceRunOne
  have prefixRun := secondStage_outputs source bridge descriptive feature original residual time firstCall
  obtain ⟨headTwo, embeddedTwo, ⟨headRunTwo⟩⟩ := StackMachineComposition.terminal_after_known_first
    (secondStage source bridge) (invocation source bridge) (Equiv.refl (Option (source.Γ source.k₀)))
    prefixRun executed stopped
  have headStoppedTwo : headTwo.l = none :=
    (StackMachineComposition.secondConfig_halted_iff (secondStage source bridge) (invocation source bridge)
      (Equiv.refl (Option (source.Γ source.k₀))) headTwo).mp (by rw [embeddedTwo]; exact stopped)
  change EvalsToInTime (invocation source bridge).step
    (initList (invocation source bridge)
      ((Indexed.frame [feature ++ residual.map bridge, feature, residual.map bridge, original]).map id))
    (some headTwo) time at headRunTwo
  have secondHead : EvalsToInTime (FramedHeadCall.machine source bridge).step
      (initList (FramedHeadCall.machine source bridge)
        ((feature ++ residual.map bridge).map some ++ none :: Indexed.frame [feature, residual.map bridge, original]))
      (some headTwo) time := by
    simpa [invocation, Indexed.frame, List.append_assoc] using headRunTwo
  obtain ⟨rebuilt, sourceStoppedTwo, sourceRunTwo⟩ := FramedHeadCall.terminal_source_halts
    source bridge (Indexed.frame [feature, residual.map bridge, original]) secondHead headStoppedTwo
  exact ⟨residual, ⟨firstCall⟩, rebuilt, sourceStoppedTwo, sourceRunTwo⟩

end Mettapedia.Machines.ICSourceCalls
