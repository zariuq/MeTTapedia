import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedMachineEpisodes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedCopyObservation

/-!
# Behavioral observation at source-instruction boundaries

The source span uses the independently specified instruction relation.
The target span uses actual start/copy/commit episodes between represented
running states. No target edge is defined by decoding into a source edge.
The proved episode comparison supplies the event map and outgoing lifting.
Native modal transport then applies to source predicates and future-only
formulas with positive fixed-point bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedInstructionObservation

open Mettapedia.Machines.BranchLocalNeed
open CallTimeChoice (Program Store)
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.GSLT.ObservationSpans
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary

structure RunningState where
  world : NeedMachine.World
  next : Nat
  stores : Nat → Store
  control : NeedControl.Control Nat
  valid : NeedMachine.Running world next stores control

def RunningState.decode (state : RunningState) : CallTimeChoiceInstructions.Control :=
  state.control.decode state.stores

structure SourceEdge (program : Program) where
  before : CallTimeChoiceInstructions.Control
  after : CallTimeChoiceInstructions.Control
  instruction : CallTimeChoiceInstructions.Instruction program before after

structure EpisodeEdge (program : Program) where
  before : RunningState
  after : RunningState
  episode : NeedMachine.Episode program before.world after.world

def sourceSpan (program : Program) : ReductionSpan CallTimeChoiceInstructions.Control where
  Edge := SourceEdge program
  source := SourceEdge.before
  target := SourceEdge.after

def episodeSpan (program : Program) : ReductionSpan RunningState where
  Edge := EpisodeEdge program
  source := EpisodeEdge.before
  target := EpisodeEdge.after

theorem EpisodeEdge.instruction {program : Program} (edge : EpisodeEdge program) :
    CallTimeChoiceInstructions.Instruction program edge.before.decode edge.after.decode := by
  obtain ⟨next,stores,control,valid,instruction⟩ := edge.episode.source_instruction edge.before.valid
  have same := (NeedMachine.Witness.running (program := program) next stores control valid).agrees_running edge.after.valid
  change control.decode stores = edge.after.decode at same
  rw [same] at instruction
  exact instruction

def projection (program : Program) : SpanMap (episodeSpan program) (sourceSpan program) where
  states := RunningState.decode
  events edge := ⟨edge.before.decode,edge.after.decode,edge.instruction⟩
  source_comm _ := rfl
  target_comm _ := rfl

/-- Every source instruction from an observed running state is realized
by a genuine ordinary episode with the exact observed successor. -/
theorem projection_source_lifts (program : Program) : (projection program).SourceLifts := by
  intro before event starts
  have instruction := event.instruction
  change event.before = before.decode at starts
  rw [starts] at instruction
  obtain ⟨world,episode,next,stores,control,valid,decoded⟩ := before.valid.realize_episode event.after instruction
  let after : RunningState := ⟨world,next,stores,control,valid⟩
  exact ⟨⟨before,after,episode⟩,rfl,decoded⟩

theorem possibility_iff (program : Program) (predicate : CallTimeChoiceInstructions.Control → Prop)
    (state : RunningState) :
    derivedDiamond (sourceSpan program) predicate state.decode ↔
      derivedDiamond (episodeSpan program) (fun target => predicate target.decode) state :=
  (projection program).diamond_pullback (projection_source_lifts program) predicate state

/-- The exact additional condition for every predecessor-box observation.
Outgoing completeness alone does not discharge this condition. -/
theorem incoming_box_transport_iff (program : Program) :
    (projection program).TargetLifts ↔
      ∀ (predicate : CallTimeChoiceInstructions.Control → Prop) (state : RunningState),
        derivedBox (sourceSpan program) predicate state.decode ↔
          derivedBox (episodeSpan program) (fun predecessor => predicate predecessor.decode) state :=
  (projection program).targetLifts_iff_box

/-- The observation is explicitly at instruction boundaries. Source
predicates do not inspect private heap allocation or intermediate control
rows, and this theorem does not assert spatial or predecessor coverage. -/
theorem future_formula_iff (program : Program) {n : Nat} (formula : Formula Traversal n)
    (future : NeedCopyObservation.FutureOnly formula) (positive : fixedPointsPositive formula = true)
    (environment : Env CallTimeChoiceInstructions.Control n) (state : RunningState) :
    satisfies (transitionSystem (sourceSpan program)) environment formula state.decode ↔
      satisfies (transitionSystem (episodeSpan program))
        (pullEnvironment (projection program).states environment) formula state :=
  satisfies_pullback (projection program) formula
    (NeedCopyObservation.future_coverage_of_lifts (projection program) (projection_source_lifts program) formula future)
    positive environment state

/-- Source reachability is the actual finite instruction path relation. -/
theorem source_reaches_iff (program : Program) (predicate : CallTimeChoiceInstructions.Control → Prop)
    (state : CallTimeChoiceInstructions.Control) :
    Reaches (sourceSpan program) predicate state ↔
      ∃ target, CallTimeChoiceInstructions.Path program state target ∧ predicate target := by
  constructor
  · intro reaches
    induction reaches with
    | goal holds => exact ⟨_,.refl,holds⟩
    | step event _ ih =>
        obtain ⟨target,path,holds⟩ := ih
        exact ⟨target,(Relation.ReflTransGen.single event.instruction).trans path,holds⟩
  · rintro ⟨target,path,holds⟩
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact Reaches.goal holds
    | @head first middle instruction rest ih =>
        exact Reaches.step (span := sourceSpan program) ⟨first,middle,instruction⟩ ih

/-- Native reachability at instruction boundaries agrees with a physical
ordinary path ending at a represented running state. Private allocation
histories are not added to the source predicate. -/
theorem reachability_iff_physical_path (program : Program) (predicate : CallTimeChoiceInstructions.Control → Prop)
    (state : RunningState) :
    satisfies (transitionSystem (episodeSpan program))
      (pullEnvironment (projection program).states (fun _ : Fin 1 => {target | predicate target})) reachFormula state ↔
      ∃ after next stores control, NeedMachine.Path program state.world after ∧
        NeedMachine.Running after next stores control ∧ predicate (control.decode stores) := by
  let environment : Env CallTimeChoiceInstructions.Control 1 := fun _ => {target | predicate target}
  refine (future_formula_iff program reachFormula (by simp [NeedCopyObservation.FutureOnly,reachFormula])
    (fixedPointsPositive_of_existential reachFormula reachFormula_existential) environment state).symm.trans ?_
  refine (satisfies_reach_iff (sourceSpan program) environment state.decode).trans ?_
  change Reaches (sourceSpan program) predicate state.decode ↔ _
  refine (source_reaches_iff program predicate state.decode).trans ?_
  constructor
  · rintro ⟨target,path,holds⟩
    obtain ⟨after,next,stores,control,actual,running,decoded⟩ :=
      (state.valid.source_path_iff target).mp path
    exact ⟨after,next,stores,control,actual,running,decoded.symm ▸ holds⟩
  · rintro ⟨after,next,stores,control,actual,running,holds⟩
    exact ⟨control.decode stores,(state.valid.source_path_iff _).mpr
      ⟨after,next,stores,control,actual,running,rfl⟩,holds⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NeedInstructionObservation
