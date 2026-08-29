import Mettapedia.GSLT.Core.TerminatingStreamingClassifierLowering

/-!
# Composing a terminating stream with an explicit finalizer

Many finite input machines have two distinct kinds of terminal work:

* a stream item can stop at its own occurrence with a retained suffix; and
* after ordinary input is exhausted, a finalizer can accept the final state or
  report an end-of-input fault.

This construction composes those two authored machines without folding the
finalizer into a fake last input item.  Each stream item and the finalizer
retain the ordinary classifier-then-dispatch target path.  The result is a
single path-valued GSLT realization, so it composes through the existing
`OperationalRealization` category and closure OSLF construction.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite

universe u

abbrev StreamStage
    (State Item Stop Class Row : Type u) :=
  Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Stage
    State Item Stop Class Row

abbrev FinalizerStage
    (State FinalOutcome FinalClass FinalRow : Type u) :=
  Mettapedia.GSLT.ClassifierLowering.Stage
    State FinalOutcome FinalClass FinalRow

/-- A stream fault retains its exact input fibre; ordinary exhaustion retains
the finalizer's state and semantic result. -/
inductive Terminal
    (State Item Stop FinalOutcome : Type u) where
  | stopped (state : State) (item : Item) (remaining : List Item)
      (reason : Stop)
  | finalized (state : State) (outcome : FinalOutcome)

/-- The source machine runs the input stream until an item fault or until the
explicit finalizer is invoked at an empty suffix. -/
inductive SourceTerm
    (State Item Stop FinalOutcome : Type u) where
  | running (state : State) (remaining : List Item)
  | terminal (result : Terminal State Item Stop FinalOutcome)

/-- The target retains a classified row for both ordinary items and the
distinct finalization event. -/
inductive TargetTerm
    (State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u) where
  | pending (state : State) (remaining : List Item)
  | classified (state : State) (item : Item) (remaining : List Item)
      (classification : StreamClass) (row : StreamRow)
  | finalClassified (state : State) (classification : FinalClass) (row : FinalRow)
  | terminal (result : Terminal State Item Stop FinalOutcome)

/-- The authored composite machine has one semantic transition per stream
item, plus one distinct semantic finalization transition after exhaustion. -/
inductive SourceStep
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) :
    SourceTerm State Item Stop FinalOutcome ->
      SourceTerm State Item Stop FinalOutcome -> Prop where
  | consume (state : State) (item : Item) (remaining : List Item)
      (nextState : State)
      (accepted : stream.authoredRun state item = .continue nextState) :
      SourceStep stream finalizer
        (.running state (item :: remaining))
        (.running nextState remaining)
  | stop (state : State) (item : Item) (remaining : List Item) (reason : Stop)
      (stopped : stream.authoredRun state item = .stop reason) :
      SourceStep stream finalizer
        (.running state (item :: remaining))
        (.terminal (.stopped state item remaining reason))
  | finish (state : State) :
      SourceStep stream finalizer (.running state [])
        (.terminal (.finalized state (finalizer.authoredRun state)))

/-- The target keeps classifier and dispatcher steps explicit for both the
stream and the end-of-input finalizer. -/
inductive TargetStep
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) :
    TargetTerm State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow ->
      TargetTerm State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow -> Prop where
  | classify (state : State) (item : Item) (remaining : List Item) :
      TargetStep stream finalizer
        (.pending state (item :: remaining))
        (.classified state item remaining
          (stream.classify state item)
          (stream.row state item (stream.classify state item)))
  | consume (state : State) (item : Item) (remaining : List Item)
      (nextState : State)
      (accepted : stream.dispatch state item (stream.classify state item) =
        .continue nextState) :
      TargetStep stream finalizer
        (.classified state item remaining
          (stream.classify state item)
          (stream.row state item (stream.classify state item)))
        (.pending nextState remaining)
  | stop (state : State) (item : Item) (remaining : List Item) (reason : Stop)
      (stopped : stream.dispatch state item (stream.classify state item) =
        .stop reason) :
      TargetStep stream finalizer
        (.classified state item remaining
          (stream.classify state item)
          (stream.row state item (stream.classify state item)))
        (.terminal (.stopped state item remaining reason))
  | finishClassify (state : State) :
      TargetStep stream finalizer (.pending state [])
        (.finalClassified state (finalizer.classify state)
          (finalizer.row state (finalizer.classify state)))
  | finishDispatch (state : State) :
      TargetStep stream finalizer
        (.finalClassified state (finalizer.classify state)
          (finalizer.row state (finalizer.classify state)))
        (.terminal (.finalized state
          (finalizer.dispatch state (finalizer.classify state))) )

def sourceGSLT
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) : GSLT where
  Term := SourceTerm State Item Stop FinalOutcome
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceStep stream finalizer
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def targetGSLT
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) : GSLT where
  Term := TargetTerm State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep stream finalizer
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def mapTerm
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u} :
    SourceTerm State Item Stop FinalOutcome ->
      TargetTerm State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow
  | .running state remaining => .pending state remaining
  | .terminal result => .terminal result

def consumePath
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (item : Item) (remaining : List Item) (nextState : State)
    (accepted : stream.dispatch state item (stream.classify state item) =
      .continue nextState) :
    ExecutionPath (targetGSLT stream finalizer)
      (.pending state (item :: remaining)) (.pending nextState remaining) :=
  .cons ⟨TargetStep.classify state item remaining⟩
    (.cons ⟨TargetStep.consume state item remaining nextState accepted⟩ (.refl _))

def stopPath
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (item : Item) (remaining : List Item) (reason : Stop)
    (stopped : stream.dispatch state item (stream.classify state item) =
      .stop reason) :
    ExecutionPath (targetGSLT stream finalizer)
      (.pending state (item :: remaining))
      (.terminal (.stopped state item remaining reason)) :=
  .cons ⟨TargetStep.classify state item remaining⟩
    (.cons ⟨TargetStep.stop state item remaining reason stopped⟩ (.refl _))

def dispatchedFinishPath
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) :
    ExecutionPath (targetGSLT stream finalizer) (.pending state [])
      (.terminal (.finalized state
        (finalizer.dispatch state (finalizer.classify state)))) :=
  .cons ⟨TargetStep.finishClassify state⟩
    (.cons ⟨TargetStep.finishDispatch state⟩ (.refl _))

/-- Reindex the dispatch endpoint through the independently supplied
finalizer adequacy equality without erasing either target transition. -/
def finishPath
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) :
    ExecutionPath (targetGSLT stream finalizer) (.pending state [])
      (.terminal (.finalized state (finalizer.authoredRun state))) :=
  Mettapedia.GSLT.ClassifierLowering.transportTarget
    (congrArg (fun outcome => TargetTerm.terminal (.finalized state outcome))
      (finalizer.dispatch_correct state))
    (dispatchedFinishPath stream finalizer state)

def lowerStep
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    {source target : SourceTerm State Item Stop FinalOutcome}
    (step : SourceStep stream finalizer source target) :
    ExecutionPath (targetGSLT stream finalizer) (mapTerm source) (mapTerm target) := by
  cases source with
  | running state remaining =>
      cases remaining with
      | nil =>
          have targetEqual :
              target = .terminal (.finalized state (finalizer.authoredRun state)) := by
            cases step
            rfl
          subst target
          exact finishPath stream finalizer state
      | cons item remaining =>
          cases target with
          | running nextState targetRemaining =>
              have remainingEqual : targetRemaining = remaining := by
                cases step
                rfl
              subst targetRemaining
              have accepted : stream.authoredRun state item = .continue nextState := by
                cases step
                assumption
              exact consumePath stream finalizer state item remaining nextState
                ((stream.dispatch_correct state item).trans accepted)
          | terminal terminal =>
              cases terminal with
              | stopped targetState targetItem targetRemaining reason =>
                  have stateEqual : targetState = state := by
                    cases step
                    rfl
                  subst targetState
                  have itemEqual : targetItem = item := by
                    cases step
                    rfl
                  subst targetItem
                  have remainingEqual : targetRemaining = remaining := by
                    cases step
                    rfl
                  subst targetRemaining
                  have stopped : stream.authoredRun state item = .stop reason := by
                    cases step
                    assumption
                  exact stopPath stream finalizer state item remaining reason
                    ((stream.dispatch_correct state item).trans stopped)
              | finalized targetState outcome =>
                  exact False.elim (by cases step)
  | terminal terminal =>
      exact False.elim (by cases step)

def realization
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) :
    OperationalRealization (sourceGSLT stream finalizer) (targetGSLT stream finalizer) where
  mapTerm := mapTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := lowerStep stream finalizer

/-! ## Whole finite stream/finalizer runs -/

/-- A complete finite run of a terminating stream followed, only after
ordinary exhaustion, by its explicit finalizer.  The source and target routes
are retained together and related by the reusable path-valued realization.
An early stream stop preserves its triggering occurrence and untouched suffix;
it never invokes the finalizer. -/
structure Run
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (remaining : List Item) where
  endpoint : SourceTerm State Item Stop FinalOutcome
  sourcePath : ExecutionPath (sourceGSLT stream finalizer)
    (.running state remaining) endpoint
  targetPath : ExecutionPath (targetGSLT stream finalizer)
    (.pending state remaining)
    (mapTerm (StreamClass := StreamClass) (StreamRow := StreamRow)
      (FinalClass := FinalClass) (FinalRow := FinalRow) endpoint)
  map_exact : (realization stream finalizer).mapRoute sourcePath = targetPath

/-- Thread a finite input through the authored stream operation.  Continuing
items take their classifier/dispatch target paths; a stopping item terminates
at its own occurrence; and the distinct finalizer is invoked precisely at an
empty suffix.  This constructs routes rather than a decompressed instruction
list. -/
def run
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) :
    (state : State) -> (remaining : List Item) -> Run stream finalizer state remaining
  | state, [] =>
      { endpoint := .terminal (.finalized state (finalizer.authoredRun state))
        sourcePath := .cons ⟨SourceStep.finish state⟩ (.refl _)
        targetPath := finishPath stream finalizer state
        map_exact := by
          change (finishPath stream finalizer state).append (.refl _) =
            finishPath stream finalizer state
          exact Route.append_refl _ }
  | state, item :: remaining =>
      match decided : stream.authoredRun state item with
      | .continue nextState =>
          let suffix := run stream finalizer nextState remaining
          { endpoint := suffix.endpoint
            sourcePath :=
              .cons ⟨SourceStep.consume state item remaining nextState decided⟩
                suffix.sourcePath
            targetPath :=
              (consumePath stream finalizer state item remaining nextState
                ((stream.dispatch_correct state item).trans decided)).append
                suffix.targetPath
            map_exact := by
              change
                (consumePath stream finalizer state item remaining nextState
                  ((stream.dispatch_correct state item).trans decided)).append
                    ((realization stream finalizer).mapRoute suffix.sourcePath) =
                  (consumePath stream finalizer state item remaining nextState
                    ((stream.dispatch_correct state item).trans decided)).append
                    suffix.targetPath
              rw [suffix.map_exact]
              rfl }
      | .stop reason =>
          { endpoint := .terminal (.stopped state item remaining reason)
            sourcePath :=
              .cons ⟨SourceStep.stop state item remaining reason decided⟩ (.refl _)
            targetPath := stopPath stream finalizer state item remaining reason
              ((stream.dispatch_correct state item).trans decided)
            map_exact := by
              change
                (stopPath stream finalizer state item remaining reason
                  ((stream.dispatch_correct state item).trans decided)).append
                    (.refl _) =
                  stopPath stream finalizer state item remaining reason
                    ((stream.dispatch_correct state item).trans decided)
              exact Route.append_refl _ }

/-- The whole finite route is exactly the route obtained by mapping its
source execution through the composed GSLT realization. -/
theorem run_maps_exact
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (remaining : List Item) :
    (realization stream finalizer).mapRoute
      (run stream finalizer state remaining).sourcePath =
      (run stream finalizer state remaining).targetPath :=
  (run stream finalizer state remaining).map_exact

/-- The combined stage is observed by OSLF at the finite macro-step scale.
The realization itself remains in source-to-target execution order. -/
def reachabilityNTT
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow) :=
  (realization stream finalizer).closureOSLFPullback

theorem consumePath_length
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (item : Item) (remaining : List Item) (nextState : State)
    (accepted : stream.dispatch state item (stream.classify state item) =
      .continue nextState) :
    (consumePath stream finalizer state item remaining nextState accepted).length = 2 :=
  rfl

theorem stopPath_length
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) (item : Item) (remaining : List Item) (reason : Stop)
    (stopped : stream.dispatch state item (stream.classify state item) =
      .stop reason) :
    (stopPath stream finalizer state item remaining reason stopped).length = 2 :=
  rfl

theorem finishPath_length
    {State Item Stop FinalOutcome StreamClass StreamRow FinalClass FinalRow : Type u}
    (stream : StreamStage State Item Stop StreamClass StreamRow)
    (finalizer : FinalizerStage State FinalOutcome FinalClass FinalRow)
    (state : State) :
    (finishPath stream finalizer state).length = 2 := by
  unfold finishPath
  rw [Mettapedia.GSLT.ClassifierLowering.transportTarget_length]
  rfl

#print axioms realization
#print axioms Run
#print axioms run
#print axioms run_maps_exact
#print axioms reachabilityNTT
#print axioms consumePath_length
#print axioms stopPath_length
#print axioms finishPath_length

end Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming.Finalization
