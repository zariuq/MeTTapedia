import Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailboxRunnerAgreement
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution

/-! The emitted mailbox entry implements the same canonical class runner
used by the queue-operation readback. Source results are supplied by the
independent queue theorems, not by evaluating a program during emission. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Emission

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL
open Mettapedia.Languages.MeTTa.PeTTa.Eval (PureReturns)
open Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics (Program)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef CettaWire
open WireKit

def spec : CompleteEmission.Spec := ⟨plan, [], .base "ErMailboxConfig", .canonical⟩

theorem emitted_source_run {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state : State) (source answer : Pattern)
    (canonical : CanonicalBags.canon source = source) (typed : Model.Sorted source)
    (settles : Settles Runner.base source answer) (ticks quantum : Nat) :
    PureReturns (CompleteEmission.runtime.append emitted) [] state
      (.expression (.symbol (CompleteEmission.runHead name) ::
        [CompleteExecution.patternValue source, number ticks, number quantum])) state
      (encoded (CompleteExecution.classTraceTerm plan (Runner.run source ticks quantum))) ∧
    Path Runner.base source (Runner.run source ticks quantum).state ∧
    ((Runner.run source ticks quantum).phase = .done → (Runner.run source ticks quantum).state = answer) := by
  have emittedFacts := (CompleteEmission.emit?_ok ok).2
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled emittedFacts
  have checked : Complete.Classes.Checked plan [] (.base "ErMailboxConfig") source :=
    (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr typed
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked plan (mode := .canonical)
    (CompleteEmission.table_for spec) checked
  obtain ⟨_, runs, _⟩ := CompleteEmission.emitted_complete ok footprinted state source inside ready
  exact ⟨runs ticks quantum, (Runner.run_source_path source ticks quantum canonical typed).1,
    Runner.done_value settles canonical typed ticks quantum⟩

/-- Any completed target evaluation of the public run entry returns exactly
its shared-machine trace. The observation is not assumed to decode as a
valid source queue or a valid trace in advance. -/
theorem completed_trace_readback {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state after : State) (source answer : Pattern)
    (canonical : CanonicalBags.canon source = source) (typed : Model.Sorted source)
    (settles : Settles Runner.base source answer) (ticks quantum : Nat) (observed : Term)
    (read : Mettapedia.Languages.MeTTa.PeTTa.DeclarativeSpec.Runs (CompleteEmission.runtime.append emitted)
      {state := state, control := .evaluate []
        (.expression (.symbol (CompleteEmission.runHead name) ::
          [CompleteExecution.patternValue source, number ticks, number quantum]))}
      (.complete after [encoded observed] [] [])) :
    observed = CompleteExecution.classTraceTerm plan (Runner.run source ticks quantum) := by
  have actual := (emitted_source_run ok state source answer canonical typed settles ticks quantum).1
  have values := (Mettapedia.Languages.MeTTa.PeTTa.Eval.pure_returns_derivation_iff
    (CompleteEmission.runtime.append emitted) [] state state _ _ actual after _ [] []).mp read |>.2.1
  exact CettaWireAtom.encode_injective _ _ (List.cons.inj values).1

theorem explored_eq (source : Pattern) (work : Nat) (canonical : CanonicalBags.canon source = source) :
    CompleteEmission.explored spec source work =
      Complete.Explore.explore (Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical) source work := by
  change Complete.Explore.explore (Complete.Normalized.search plan [] (.base "ErMailboxConfig") .canonical)
    (Complete.Normalized.commit plan .canonical source) work = _
  rw [Runner.commit_fixed canonical]

theorem emitted_answer_explored {name : String} {emitted : Program}
    (ok : CompleteEmission.emit? spec name .classes = .ok emitted)
    (state : State) {source answer : Pattern}
    (canonical : CanonicalBags.canon source = source) (typed : Model.Sorted source)
    (settles : Settles Runner.base source answer) :
    ∃ work, answer ∈ (CompleteEmission.explored spec source work).nodes.map (·.state) ∧
      PureReturns (CompleteEmission.runtime.append emitted) [] state
        (.expression (.symbol (CompleteEmission.exploreHead name) :: [CompleteExecution.patternValue source, number work]))
        state (CompleteExecution.patternsValue ((CompleteEmission.explored spec source work).nodes.map (·.state))) := by
  have emittedFacts := (CompleteEmission.emit?_ok ok).2
  have footprinted : CompleteEmission.Footprinted spec := CompleteEmission.footprinted_of_compiled emittedFacts
  have checked : Complete.Classes.Checked plan [] (.base "ErMailboxConfig") source :=
    (checkOpenPatternWellSorted_eq_true_iff _ _ _ _ _).mpr typed
  have inside := Complete.Footprint.sorted_within footprinted.scope.declared checked
  have ready := CompleteExecution.commitReady_of_checked plan (mode := .canonical)
    (CompleteEmission.table_for spec) checked
  obtain ⟨_, _, explores⟩ := CompleteEmission.emitted_complete ok footprinted state source inside ready
  obtain ⟨work, node, member, reached⟩ := (Runner.source_path_explored canonical typed settles.reached).1
  refine ⟨work, ?_, explores work⟩
  rw [explored_eq source work canonical]
  exact List.mem_map.mpr ⟨node, member, reached⟩

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ErlangMailbox.Execution.Emission
