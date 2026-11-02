import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoRunnerAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution

/-! Successful shared emission realizes source Peano equation paths in the
MeTTa run entry at every budget. Completed runs have the exact source normal
form. Scope and commit readiness follow from the checked emission and source
typing, rather than being supplied as semantic assumptions. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoEmission

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Eval (PureReturns)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open WireKit
open Mettapedia.GSLT.LanguageDef.WellSorted
open PeanoProducer

def spec (context : Maude.VariableContext) : CompleteEmission.Spec :=
  ⟨compiledPlan context, [], .base "Nat", .canonical⟩

theorem explored_eq (context : Maude.VariableContext) (source : Maude.Term) (work : Nat) :
    CompleteEmission.explored (spec context) (encode source) work =
      Complete.Explore.explore (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical)
        (encode source) work := by
  change Complete.Explore.explore (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical)
    (Complete.Normalized.commit (compiledPlan context) .canonical (encode source)) work = _
  rw [PeanoRunner.commit_encode]

theorem emitted_source_run {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (spec context) name .classes = .ok emitted)
    (state : State) (source : Maude.Term)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") (ticks quantum : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (.expression (.symbol (CompleteEmission.runHead name) ::
        [CompleteExecution.patternValue (encode source), number ticks, number quantum])) state
      (encoded (CompleteExecution.classTraceTerm (compiledPlan context) (PeanoRunner.run context source ticks quantum))) ∧
    (∃ result, (PeanoRunner.run context source ticks quantum).state = encode result ∧
      Maude.EquationPath Maude.Examples.peano context "Nat" source result) ∧
    ((PeanoRunner.run context source ticks quantum).phase = .done →
      (PeanoRunner.run context source ticks quantum).state = encode (Maude.PeanoNormalization.reduce source)) := by
  have emittedFacts := (CompleteEmission.emit?_ok ok).2
  have footprinted : CompleteEmission.Footprinted (spec context) :=
    CompleteEmission.footprinted_of_compiled emittedFacts
  have sorted := source_typed context source typed
  have checked : Complete.Classes.Checked (compiledPlan context) [] (.base "Nat") (encode source) :=
    (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr sorted
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked (compiledPlan context) (mode := .canonical)
    (CompleteEmission.table_for (spec context)) checked
  obtain ⟨_, runs, _⟩ := CompleteEmission.emitted_complete ok footprinted state (encode source) inside ready
  exact ⟨runs ticks quantum, PeanoRunner.run_source_path context source ticks quantum typed,
    PeanoRunner.done_value context source ticks quantum typed⟩

theorem emitted_source_explore {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (spec context) name .classes = .ok emitted)
    (state : State) {source target : Maude.Term}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (path : Maude.EquationPath Maude.Examples.peano context "Nat" source target) :
    ∃ work, encode target ∈ (CompleteEmission.explored (spec context) (encode source) work).nodes.map (·.state) ∧
      PureReturns (CompleteEmission.runtime.append emitted) [] state
        (.expression (.symbol (CompleteEmission.exploreHead name) :: [CompleteExecution.patternValue (encode source), number work]))
        state (CompleteExecution.patternsValue
          ((CompleteEmission.explored (spec context) (encode source) work).nodes.map (·.state))) := by
  have emittedFacts := (CompleteEmission.emit?_ok ok).2
  have footprinted : CompleteEmission.Footprinted (spec context) :=
    CompleteEmission.footprinted_of_compiled emittedFacts
  have sorted := source_typed context source typed
  have checked : Complete.Classes.Checked (compiledPlan context) [] (.base "Nat") (encode source) :=
    (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr sorted
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked (compiledPlan context) (mode := .canonical)
    (CompleteEmission.table_for (spec context)) checked
  obtain ⟨_, _, explores⟩ := CompleteEmission.emitted_complete ok footprinted state (encode source) inside ready
  obtain ⟨work, node, member, reached⟩ := PeanoRunner.source_path_explored path
  refine ⟨work, ?_, explores work⟩
  rw [explored_eq]
  exact List.mem_map.mpr ⟨node, member, reached⟩

theorem emitted_explore_source_sound {context : Maude.VariableContext} {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? (spec context) name .classes = .ok emitted)
    (state : State) (source : Maude.Term)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") (work : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (.expression (.symbol (CompleteEmission.exploreHead name) :: [CompleteExecution.patternValue (encode source), number work]))
      state (CompleteExecution.patternsValue
        ((CompleteEmission.explored (spec context) (encode source) work).nodes.map (·.state))) ∧
    ∀ target ∈ (CompleteEmission.explored (spec context) (encode source) work).nodes.map (·.state),
      ∃ result, target = encode result ∧ Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  have emittedFacts := (CompleteEmission.emit?_ok ok).2
  have footprinted : CompleteEmission.Footprinted (spec context) :=
    CompleteEmission.footprinted_of_compiled emittedFacts
  have sorted := source_typed context source typed
  have checked : Complete.Classes.Checked (compiledPlan context) [] (.base "Nat") (encode source) :=
    (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr sorted
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked (compiledPlan context) (mode := .canonical)
    (CompleteEmission.table_for (spec context)) checked
  obtain ⟨_, _, explores⟩ := CompleteEmission.emitted_complete ok footprinted state (encode source) inside ready
  refine ⟨explores work, ?_⟩
  intro target member
  obtain ⟨node, nodeMember, rfl⟩ := List.mem_map.mp member
  rw [explored_eq] at nodeMember
  exact PeanoRunner.explored_node_source typed work nodeMember

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoEmission
