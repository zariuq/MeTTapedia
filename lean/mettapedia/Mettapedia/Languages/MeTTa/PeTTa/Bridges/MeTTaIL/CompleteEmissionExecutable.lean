import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution
import Mettapedia.Languages.MeTTa.PeTTa.ExecutableOnTheStep

/-!
# Executing emitted GSLT explorers on Transform rules

For a language admitted by the emitter's class profile, run its generated
explorer on the compiled PeTTa rule program. There is a fuel budget at
which this computation returns the explorer's states, and its completed
runs have exactly that result. The target runner uses the finite program
and its named built-in data operations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (declaredFootprint)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open SpaceSemantics (Program)
open WireKit

variable {spec : Spec}

/-- A completed run of the executable Transform hosting is exactly the
authored explorer's result. Completion is possible with sufficient fuel. -/
theorem explored_executable {name : String} {emitted : Program}
    (ok : emit? spec name .classes = .ok emitted) (footprinted : Footprinted spec)
    (state : State) (cells : List String) (vacant : NamedSpaces.Store.EmptyTail state [])
    (covers : ∀ c, c ∉ cells → state.cells c = none)
    (source : Pattern) (inside : ∀ n ∈ source.freeFvarNames, n ∈ declaredFootprint spec.plan)
    (ready : CompleteExecution.CommitReady spec.mode (table spec) source) (work : Nat)
    (after : State) (answers : List Atom) :
    (∃ fuel, ExecutableOnTheStep.run (runtime.append emitted) fuel
      (ConfigurationEncoding.encode
        (Eval.start state
          (.expression [.symbol (exploreHead name), CompleteExecution.patternValue source, number work]))
        cells) = some (.complete after answers [] [])) ↔
      after = state ∧
        answers = [CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))] := by
  obtain ⟨_, _, explores⟩ := emitted_complete ok footprinted state source inside ready
  let initial := Eval.start state
    (.expression [.symbol (exploreHead name), CompleteExecution.patternValue source, number work])
  have executes (fuel : ℕ) :=
    ExecutableOnTheStep.run_eq (runtime.append emitted) fuel initial cells vacant covers
  change (∃ fuel, ExecutableOnTheStep.run (runtime.append emitted) fuel
    (ConfigurationEncoding.encode initial cells) = some (.complete after answers [] [])) ↔ _
  have same : (∃ fuel, ExecutableOnTheStep.run (runtime.append emitted) fuel
      (ConfigurationEncoding.encode initial cells) = some (.complete after answers [] [])) ↔
      ∃ fuel, Eval.run (runtime.append emitted) fuel initial = .complete after answers [] [] :=
    exists_congr fun fuel => by rw [executes fuel, Option.some.injEq]
  refine same.trans ?_
  let expected : Atom := CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))
  have path : (Eval.theory (runtime.append emitted)).MultiStep initial (Eval.finished state [expected] [] []) :=
    explores work
  simpa [expected] using
    Eval.path_completed_iff (runtime.append emitted) initial state [expected] [] [] path after answers [] []

#print axioms explored_executable

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
