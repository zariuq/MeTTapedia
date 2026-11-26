import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmissionExecution
import Mettapedia.Languages.MeTTa.PeTTa.EvalOnTheStep

/-!
# An emitted language, through PeTTa, on the transform step

The emitter takes an admitted plan to a PeTTa module, and `EvalOnTheStep` takes PeTTa's
evaluator to the transform step. This is the composite.

* `explored_on_the_step`: from a state that shows the call of an emitted module's
  explore entry, some run of firings reads the explorer's answer, and every finished
  configuration that any run reads is that answer and no other.
* `exists_start`: every such call is shown by a state, so the theorem is about something.

The plan is any one the emitter accepts in the class profile. Nothing here is proved
per language.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.MeTTaIL.Complete.Footprint (Scope declaredFootprint)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (rowState rowState_reads)
open SpaceSemantics (Program)
open WireKit

/-- Runs of a deterministic system to terminal states end at one state. -/
theorem terminal_unique {S : GSLT} (deterministic : ∀ {a b c : S.Term}, S.Step a b → S.Step a c → b = c) :
    ∀ {start first second : S.Term}, S.MultiStep start first → S.MultiStep start second →
      (∀ next, ¬ S.Step first next) → (∀ next, ¬ S.Step second next) → first = second
  | _, _, _, .refl _, .refl _, _, _ => rfl
  | _, _, _, .refl _, .step stepped _, stopped, _ => absurd stepped (stopped _)
  | _, _, _, .step stepped _, .refl _, _, stopped => absurd stepped (stopped _)
  | _, _, _, .step left leftRest, .step right rightRest, firstStopped, secondStopped => by
      obtain rfl := deterministic left right
      exact terminal_unique deterministic leftRest rightRest firstStopped secondStopped

/-- A finished configuration has no transition. -/
theorem finished_stopped (program : Program) (state : State) (answers : List Atom) (next : Eval.Configuration) :
    ¬ (Eval.theory program).Step (Eval.finished state answers [] []) next := by
  intro stepped
  have computed := (Eval.theory_step_iff program _ next).mp stepped
  simp [Eval.step, Eval.finished] at computed

/-- Every call from a store with an empty tail and finitely many cells is shown by a state. -/
theorem exists_start (state : State) (vacant : NamedSpaces.Store.EmptyTail state []) (cells : List String)
    (covers : ∀ name, name ∉ cells → state.cells name = none) (expression : Atom) :
    ∃ start : SState ℕ,
      EvalOnTheStep.Shows { state, control := .evaluate [] expression } start :=
  ⟨rowState _, cells, vacant, covers, rowState_reads _⟩

variable {spec : Spec}

/-- **An admitted language, through PeTTa, on transform**: some run of firings reads the
explorer's answer, and no run reads another finished answer. -/
theorem explored_on_the_step {O : Type} [DecidableEq O] [Infinite O] {name : String} {emitted : Program}
    (ok : emit? spec name .classes = .ok emitted) (footprinted : Footprinted spec) (state : State)
    (source : Pattern) (inside : ∀ name ∈ source.freeFvarNames, name ∈ declaredFootprint spec.plan)
    (ready : CompleteExecution.CommitReady spec.mode (table spec) source) (work : Nat) {start : SState O}
    (shown : EvalOnTheStep.Shows
      { state
        control := .evaluate []
          (.expression [.symbol (exploreHead name), CompleteExecution.patternValue source, number work]) }
      start)
    (after : State) (answers : List Atom) :
    (∃ final, (EvalOnTheStep.stepSystem O (runtime.append emitted)).MultiStep start final ∧
        EvalOnTheStep.Shows (Eval.finished after answers [] []) final) ↔
      after = state ∧
        answers = [CompleteExecution.patternsValue ((explored spec source work).nodes.map (·.state))] := by
  obtain ⟨-, -, explores⟩ := emitted_complete ok footprinted state source inside ready
  refine (EvalOnTheStep.returns_on_the_step (runtime.append emitted) [] state after _ answers shown).symm.trans
    ⟨fun returned => ?_, ?_⟩
  · have same := terminal_unique (S := Eval.theory (runtime.append emitted))
      (fun left right => Eval.step_deterministic _ _ _ _ left right) returned (explores work)
      (finished_stopped _ _ _) (finished_stopped _ _ _)
    exact ⟨congrArg Eval.Configuration.state same,
      Eval.Control.returned.inj (congrArg Eval.Configuration.control same)⟩
  · rintro ⟨rfl, rfl⟩
    exact explores work

#print axioms exists_start
#print axioms explored_on_the_step

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission
