import Mettapedia.GSLT.Core.TerminatingStreamingClassifierLowering

/-!
# Reified rows for terminating streaming GSLT lowerings

`TerminatingStreaming` gives the semantic GSLT-to-GSLT lowering of one
source occurrence into a classified target occurrence followed by dispatch.
This module supplies the adjacent reified artifact transform: it emits the
ordered target-row occurrences needed to run that lowering in a target
machine.

The emitted stream is not a verdict and it does not erase a stopping input.
Each event retains its source state, item, position, and unconsumed suffix.
At a terminal source decision the triggering event is emitted once and the
suffix remains only in the terminal endpoint.  Thus a source parser or
proof-reader can produce ordinary target data without pre-running a later
proof or theorem checker.

The semantic realization and the reified row emission stay distinct on
purpose: the former proves the GSLT path correspondence, while the latter is
the inspectable data artifact that a standalone implementation may produce.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming
open Mettapedia.OSLF.Framework.IndexedModalFunctor

universe u v

/-- One emitted target-row occurrence.  The payload is obtained only from the
supplied stage; source position and suffix are retained explicitly, so equal
rows at different occurrences never collapse. -/
structure Event
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) where
  position : Nat
  state : State
  item : Item
  remaining : List Item

namespace Event

variable {State Item Stop Class Row : Type u}
variable {stage : Stage State Item Stop Class Row}

/-- The target-owned classification selected for this source occurrence. -/
def classification (event : Event stage) : Class :=
  stage.classify event.state event.item

/-- The exact reified target row selected for this source occurrence. -/
def row (event : Event stage) : Row :=
  stage.row event.state event.item event.classification

/-- The target state reached by the classifier half of the lowering. -/
def classifiedTerm (event : Event stage) :
    TargetTerm State Item Stop Class Row :=
  .classified event.state event.item event.remaining event.classification event.row

/-- Every emitted event has the target classifier step dictated by the same
stage.  This is independent of a particular target runtime. -/
def classificationStep (event : Event stage) :
    TargetStep stage
      (.pending event.state (event.item :: event.remaining))
      event.classifiedTerm :=
  .classify event.state event.item event.remaining

theorem classifiedTerm_row_exact (event : Event stage) :
    event.classifiedTerm =
      .classified event.state event.item event.remaining
        (stage.classify event.state event.item)
        (stage.row event.state event.item (stage.classify event.state event.item)) :=
  rfl

end Event

/-- A finite source-relative row artifact together with its exact source
endpoint.  `endpoint` records either clean finish or the first stopping
occurrence; it is not supplied by the caller. -/
structure Artifact
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) where
  events : List (Event stage)
  endpoint : SourceTerm State Item Stop

/-- Construct one source occurrence event without consulting its outcome. -/
def eventAt
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (position : Nat) (state : State) (item : Item) (remaining : List Item) :
    Event stage :=
  { position, state, item, remaining }

/-- A reified row artifact together with the source and target paths that
justify it.  This extends the existing whole-stream realization by inspectable
output data; it does not introduce a second source semantics. -/
structure Run
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (remaining : List Item) where
  artifact : Artifact stage
  sourcePath : ExecutionPath (sourceGSLT stage) (.running state remaining)
    artifact.endpoint
  targetPath : ExecutionPath (targetGSLT stage) (.pending state remaining)
    (mapTerm (Class := Class) (Row := Row) artifact.endpoint)
  map_exact : (realization stage).mapRoute sourcePath = targetPath

/-- Reify the target classifier rows for the supplied finite source stream.
The source operation decides continuation or stopping; this transformation
does not inspect any external artifact identity or expected result. -/
def run
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    (position : Nat) -> (state : State) -> (remaining : List Item) ->
      Run stage state remaining
  | _, state, [] =>
      { artifact :=
          { events := []
            endpoint := .finished state }
        sourcePath := .cons ⟨SourceStep.finish state⟩ (.refl _)
        targetPath := finishPath stage state
        map_exact := by
          change (finishPath stage state).append (.refl _) = finishPath stage state
          exact Route.append_refl _ }
  | position, state, item :: remaining =>
      let event := eventAt stage position state item remaining
      match decided : stage.authoredRun state item with
      | .continue nextState =>
          let suffix := run stage (position + 1) nextState remaining
          { artifact :=
              { events := event :: suffix.artifact.events
                endpoint := suffix.artifact.endpoint }
            sourcePath :=
              .cons ⟨SourceStep.consume state item remaining nextState decided⟩
                suffix.sourcePath
            targetPath :=
              (consumePath stage state item remaining nextState
                ((stage.dispatch_correct state item).trans decided)).append
                suffix.targetPath
            map_exact := by
              change
                (consumePath stage state item remaining nextState
                  ((stage.dispatch_correct state item).trans decided)).append
                  ((realization stage).mapRoute suffix.sourcePath) =
                (consumePath stage state item remaining nextState
                  ((stage.dispatch_correct state item).trans decided)).append
                  suffix.targetPath
              rw [suffix.map_exact]
              rfl }
      | .stop reason =>
          { artifact :=
              { events := [event]
                endpoint := .stopped state item remaining reason }
            sourcePath :=
              .cons ⟨SourceStep.stop state item remaining reason decided⟩ (.refl _)
            targetPath := stopPath stage state item remaining reason
              ((stage.dispatch_correct state item).trans decided)
            map_exact := by
              change
                (stopPath stage state item remaining reason
                  ((stage.dispatch_correct state item).trans decided)).append
                  (.refl _) =
                stopPath stage state item remaining reason
                  ((stage.dispatch_correct state item).trans decided)
              exact Route.append_refl _ }

/-- The inspectable output component of the certified row-emission run. -/
def emit
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (position : Nat) (state : State) (remaining : List Item) : Artifact stage :=
  (run stage position state remaining).artifact

/-! ## Row encoders

The semantic target row and its concrete target-data encoding are deliberately
separate.  An encoder can therefore be implemented in another runtime without
changing the source GSLT or treating a rendered artifact as semantic evidence.
-/

/-- One encoded target-data occurrence, retaining its complete source event.
The output is determined by `encodeEvent`; this structure is not an authority
for arbitrary caller-provided target data. -/
structure EncodedEvent
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (Output : Type v) where
  source : Event stage
  output : Output

/-- An encoded artifact preserves the exact source endpoint while replacing
only the target-row representation. -/
structure EncodedArtifact
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (Output : Type v) where
  events : List (EncodedEvent stage Output)
  endpoint : SourceTerm State Item Stop

/-- Encode one semantic target row while retaining its source occurrence. -/
def encodeEvent
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (event : Event stage) : EncodedEvent stage Output :=
  { source := event
    output := encoder event.row }

/-- Encode every row emitted from a source-relative artifact.  The source
endpoint is copied exactly; this operation cannot turn a terminal stop into an
acceptance or consume its retained suffix. -/
def encodeArtifact
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (artifact : Artifact stage) :
    EncodedArtifact stage Output :=
  { events := artifact.events.map (encodeEvent encoder)
    endpoint := artifact.endpoint }

theorem encodeEvent_source_position
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (event : Event stage) :
    (encodeEvent encoder event).source.position = event.position :=
  rfl

theorem encodeEvent_output_exact
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (event : Event stage) :
    (encodeEvent encoder event).output = encoder event.row :=
  rfl

theorem encodeArtifact_endpoint_exact
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (artifact : Artifact stage) :
    (encodeArtifact encoder artifact).endpoint = artifact.endpoint :=
  rfl

theorem encodeArtifact_event_count
    {State Item Stop Class Row : Type u} {Output : Type v}
    {stage : Stage State Item Stop Class Row}
    (encoder : Row -> Output) (artifact : Artifact stage) :
    (encodeArtifact encoder artifact).events.length = artifact.events.length := by
  simp [encodeArtifact]

theorem emit_empty
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (position : Nat) (state : State) :
    emit stage position state [] =
      { events := []
        endpoint := .finished state } :=
  rfl

/-- The source execution carried by an emitted artifact is a real GSLT path,
not a separately asserted endpoint. -/
def runSourcePath
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (position : Nat) (state : State) (remaining : List Item) :
    ExecutionPath (sourceGSLT stage) (.running state remaining)
      (emit stage position state remaining).endpoint :=
  (run stage position state remaining).sourcePath

/-- The target execution carried by the same artifact consists of the
classification/dispatch lowering, with the exact emitted endpoint. -/
def runTargetPath
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (position : Nat) (state : State) (remaining : List Item) :
    ExecutionPath (targetGSLT stage) (.pending state remaining)
      (mapTerm (Class := Class) (Row := Row)
        (emit stage position state remaining).endpoint) :=
  (run stage position state remaining).targetPath

/-- Reified emission preserves the exact path-valued GSLT lowering, rather
than merely agreeing on a terminal observation. -/
theorem run_maps_exact
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (position : Nat) (state : State) (remaining : List Item) :
    (realization stage).mapRoute (runSourcePath stage position state remaining) =
      runTargetPath stage position state remaining :=
  (run stage position state remaining).map_exact

/-- Every reified row-emission transform is observed through the OSLF-derived
native modal transport of the exact underlying GSLT realization.  The emitted
artifact does not bypass this semantic arrow. -/
def reachabilityNTT
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (targetGSLT stage).closure)
      (oslfForwardModalObject (sourceGSLT stage).closure) :=
  (realization stage).closureOSLFPullback

/-- The NTT transport named by row emission is exactly the one obtained by
running OSLF over its path-valued GSLT realization. -/
theorem reachabilityNTT_exact
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    reachabilityNTT stage =
      (realization stage).closureOSLFPullback :=
  rfl

/-! ## Small positive and negative controls -/

namespace Canary

def stage : Stage Nat Bool Unit Bool Nat where
  authoredRun := fun state item =>
    if item then .continue (state + 1) else .stop ()
  classify := fun _ item => item
  dispatch := fun state _ item =>
    if item then .continue (state + 1) else .stop ()
  row := fun state _ item => if item then state + 100 else state
  dispatch_correct := by
    intro state item
    cases item <;> rfl

def positive : Artifact stage := emit stage 0 0 [true]
def stopping : Artifact stage := emit stage 4 0 [true, false, true]
def stoppingRun : Run stage 0 [true, false, true] :=
  run stage 4 0 [true, false, true]

/-- The positive example emits one row and reaches normal end of input. -/
theorem positive_events : positive.events.length = 1 := by
  rfl

theorem positive_endpoint : positive.endpoint = .finished 1 := by
  rfl

/-- The stopping example emits the failed occurrence but not the suffix. -/
theorem stopping_events : stopping.events.length = 2 := by
  rfl

theorem stopping_endpoint :
    stopping.endpoint = .stopped 1 false [true] () := by
  rfl

/-- The second event retains its real source position and the unconsumed tail.
This rejects a transform that silently treats a set of equal rows as ordered
input. -/
theorem stopping_second_event :
    stopping.events[1]? =
      some (eventAt stage 5 1 false [true]) := by
  rfl

theorem stoppingRun_artifact : stoppingRun.artifact = stopping :=
  rfl

theorem stoppingRun_source_length : stoppingRun.sourcePath.length = 2 := by
  rfl

theorem stoppingRun_target_length : stoppingRun.targetPath.length = 4 := by
  rfl

theorem stoppingRun_maps_exact :
    (realization stage).mapRoute stoppingRun.sourcePath = stoppingRun.targetPath :=
  stoppingRun.map_exact

end Canary

#print axioms Event.classificationStep
#print axioms Event.classifiedTerm_row_exact
#print axioms encodeEvent_source_position
#print axioms encodeEvent_output_exact
#print axioms encodeArtifact_endpoint_exact
#print axioms encodeArtifact_event_count
#print axioms runSourcePath
#print axioms runTargetPath
#print axioms run_maps_exact
#print axioms reachabilityNTT
#print axioms reachabilityNTT_exact
#print axioms Canary.positive_events
#print axioms Canary.positive_endpoint
#print axioms Canary.stopping_events
#print axioms Canary.stopping_endpoint
#print axioms Canary.stopping_second_event
#print axioms Canary.stoppingRun_artifact
#print axioms Canary.stoppingRun_source_length
#print axioms Canary.stoppingRun_target_length
#print axioms Canary.stoppingRun_maps_exact

end Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.RowEmission
