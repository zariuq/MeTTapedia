import Mettapedia.GSLT.Core.ClassifierLowering

/-!
# Terminating streaming classifier lowerings

`StreamingClassifierLowering` models a stream which is known to consume every
input occurrence.  Verifiers and parsers also need the adjacent case: an
occurrence may produce a terminal fault or rejection, and the remaining input
must stay unconsumed.  This module makes that boundary explicit.

Each consumed source occurrence still lowers to two target transitions:
classification into an inspectable row, followed by dispatch.  A terminating
dispatch ends in a target terminal state carrying the exact triggering item,
unconsumed suffix, and stop reason.  No source-side pre-expansion is involved.

The construction is deliberately a small extension of the existing
path-valued `OperationalRealization` and closure OSLF interfaces.  It is not a
second transformation category.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.OSLF.Framework.IndexedModalFunctor

universe u

/-- A source operation either supplies the next state or stops at its current
input occurrence with an explicit reason. -/
inductive Decision (State Stop : Type u) where
  | continue (nextState : State) : Decision State Stop
  | stop (reason : Stop) : Decision State Stop
deriving DecidableEq, Repr

/-- An independently authored terminating operation and its target-owned
classification/dispatch realization.  `dispatch_correct` is the only semantic
bridge: neither target operation is defined in terms of the authored one. -/
structure Stage (State Item Stop Class Row : Type u) where
  authoredRun : State -> Item -> Decision State Stop
  classify : State -> Item -> Class
  dispatch : State -> Item -> Class -> Decision State Stop
  row : State -> Item -> Class -> Row
  dispatch_correct : forall state item,
    dispatch state item (classify state item) = authoredRun state item

/-- A source stream either continues, finishes at end of input, or stops at
the exact offending occurrence.  The unconsumed tail is retained at a stop. -/
inductive SourceTerm (State Item Stop : Type u) where
  | running (state : State) (remaining : List Item)
  | finished (state : State)
  | stopped (state : State) (item : Item) (remaining : List Item)
      (reason : Stop)

/-- Target streams retain a classified row between classification and dispatch.
Terminal target states retain the same occurrence fibre as their source
counterparts. -/
inductive TargetTerm (State Item Stop Class Row : Type u) where
  | pending (state : State) (remaining : List Item)
  | classified (state : State) (item : Item) (remaining : List Item)
      (classification : Class) (row : Row)
  | finished (state : State)
  | stopped (state : State) (item : Item) (remaining : List Item)
      (reason : Stop)

/-- One authored source transition consumes an item or stops at it; finishing
an empty stream is explicit. -/
inductive SourceStep
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    SourceTerm State Item Stop -> SourceTerm State Item Stop -> Prop where
  | consume (state : State) (item : Item) (remaining : List Item)
      (nextState : State)
      (accepted : stage.authoredRun state item = .continue nextState) :
      SourceStep stage
        (.running state (item :: remaining))
        (.running nextState remaining)
  | stop (state : State) (item : Item) (remaining : List Item)
      (reason : Stop)
      (stopped : stage.authoredRun state item = .stop reason) :
      SourceStep stage
        (.running state (item :: remaining))
        (.stopped state item remaining reason)
  | finish (state : State) :
      SourceStep stage (.running state []) (.finished state)

/-- Target execution separates classification from the two possible dispatch
outcomes. -/
inductive TargetStep
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    TargetTerm State Item Stop Class Row ->
      TargetTerm State Item Stop Class Row -> Prop where
  | classify (state : State) (item : Item) (remaining : List Item) :
      TargetStep stage
        (.pending state (item :: remaining))
        (.classified state item remaining
          (stage.classify state item)
          (stage.row state item (stage.classify state item)))
  | consume (state : State) (item : Item) (remaining : List Item)
      (nextState : State)
      (accepted :
        stage.dispatch state item (stage.classify state item) =
          .continue nextState) :
      TargetStep stage
        (.classified state item remaining
          (stage.classify state item)
          (stage.row state item (stage.classify state item)))
        (.pending nextState remaining)
  | stop (state : State) (item : Item) (remaining : List Item)
      (reason : Stop)
      (stopped :
        stage.dispatch state item (stage.classify state item) = .stop reason) :
      TargetStep stage
        (.classified state item remaining
          (stage.classify state item)
          (stage.row state item (stage.classify state item)))
        (.stopped state item remaining reason)
  | finish (state : State) :
      TargetStep stage (.pending state []) (.finished state)

def sourceGSLT
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) : GSLT where
  Term := SourceTerm State Item Stop
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := SourceStep stage
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def targetGSLT
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) : GSLT where
  Term := TargetTerm State Item Stop Class Row
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := TargetStep stage
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

/-- Public source states map to their corresponding target states; only the
classified intermediate state is target-administrative. -/
def mapTerm
    {State Item Stop Class Row : Type u} :
    SourceTerm State Item Stop -> TargetTerm State Item Stop Class Row
  | .running state remaining => .pending state remaining
  | .finished state => .finished state
  | .stopped state item remaining reason => .stopped state item remaining reason

/-- A continuing source item retains classifier then dispatch. -/
def consumePath
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (item : Item) (remaining : List Item) (nextState : State)
    (accepted : stage.dispatch state item (stage.classify state item) =
      .continue nextState) :
    ExecutionPath (targetGSLT stage)
      (.pending state (item :: remaining)) (.pending nextState remaining) :=
  .cons ⟨TargetStep.classify state item remaining⟩
    (.cons ⟨TargetStep.consume state item remaining nextState accepted⟩
      (.refl _))

/-- A stopping source item retains the same classifier and then lands in an
occurrence-preserving terminal target state. -/
def stopPath
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (item : Item) (remaining : List Item) (reason : Stop)
    (stopped : stage.dispatch state item (stage.classify state item) =
      .stop reason) :
    ExecutionPath (targetGSLT stage)
      (.pending state (item :: remaining))
      (.stopped state item remaining reason) :=
  .cons ⟨TargetStep.classify state item remaining⟩
    (.cons ⟨TargetStep.stop state item remaining reason stopped⟩ (.refl _))

def finishPath
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (state : State) :
    ExecutionPath (targetGSLT stage) (.pending state []) (.finished state) :=
  .cons ⟨TargetStep.finish state⟩ (.refl _)

theorem consumePath_length
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (item : Item) (remaining : List Item) (nextState : State)
    (accepted : stage.dispatch state item (stage.classify state item) =
      .continue nextState) :
    (consumePath stage state item remaining nextState accepted).length = 2 :=
  rfl

theorem stopPath_length
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (item : Item) (remaining : List Item) (reason : Stop)
    (stopped : stage.dispatch state item (stage.classify state item) =
      .stop reason) :
    (stopPath stage state item remaining reason stopped).length = 2 :=
  rfl

theorem finishPath_length
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (state : State) :
    (finishPath stage state).length = 1 :=
  rfl

/-- Lower a source transition using only its endpoint equality and the stage's
independent adequacy law. -/
def lowerStep
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    {source target : SourceTerm State Item Stop}
    (step : SourceStep stage source target) :
    ExecutionPath (targetGSLT stage) (mapTerm source) (mapTerm target) := by
  cases source with
  | running state remaining =>
      cases remaining with
      | nil =>
          have targetEqual : target = .finished state := by
            cases target with
            | running _ _ => cases step
            | finished targetState =>
                cases step
                rfl
            | stopped _ _ _ _ => cases step
          subst target
          exact finishPath stage state
      | cons item remaining =>
          cases target with
          | running nextState targetRemaining =>
              have remainingEqual : targetRemaining = remaining := by
                cases step
                rfl
              subst targetRemaining
              have accepted : stage.authoredRun state item = .continue nextState := by
                cases step
                assumption
              exact consumePath stage state item remaining nextState
                ((stage.dispatch_correct state item).trans accepted)
          | finished targetState =>
              exact False.elim (by cases step)
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
              have stopped : stage.authoredRun state item = .stop reason := by
                cases step
                assumption
              exact stopPath stage state item remaining reason
                ((stage.dispatch_correct state item).trans stopped)
  | finished state =>
      exact False.elim (by cases step)
  | stopped state item remaining reason =>
      exact False.elim (by cases step)

def realization
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    OperationalRealization (sourceGSLT stage) (targetGSLT stage) where
  mapTerm := mapTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := lowerStep stage

/-! ## Whole finite streams -/

/-- A complete finite source run together with an independently assembled
target route to the mapped endpoint.  Keeping the endpoint existential avoids
equating a proof-relevant route with a separately re-evaluated dependent
program while retaining the exact source and target executions. -/
structure StreamRun
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (remaining : List Item) where
  endpoint : SourceTerm State Item Stop
  sourcePath : ExecutionPath (sourceGSLT stage) (.running state remaining) endpoint
  targetPath : ExecutionPath (targetGSLT stage) (.pending state remaining)
    (mapTerm (Class := Class) (Row := Row) endpoint)
  map_exact : (realization stage).mapRoute sourcePath = targetPath

/-- Construct a whole finite stream run by composing independently authored
source transitions with the corresponding classifier/dispatch paths.  A stop
retains its triggering item and leaves the suffix unconsumed. -/
def runStream
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    (state : State) -> (remaining : List Item) -> StreamRun stage state remaining
  | state, [] =>
      { endpoint := .finished state
        sourcePath := .cons ⟨SourceStep.finish state⟩ (.refl _)
        targetPath := finishPath stage state
        map_exact := by
          change (finishPath stage state).append (.refl _) = finishPath stage state
          exact Route.append_refl _ }
  | state, item :: remaining =>
      match decided : stage.authoredRun state item with
      | .continue nextState =>
          let suffix := runStream stage nextState remaining
          { endpoint := suffix.endpoint
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
          { endpoint := .stopped state item remaining reason
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

/-- The constructed whole-stream target path is exactly the path produced by
the reusable GSLT realization, not merely an endpoint-equivalent route. -/
theorem runStream_map_exact
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) (state : State)
    (remaining : List Item) :
    (realization stage).mapRoute (runStream stage state remaining).sourcePath =
      (runStream stage state remaining).targetPath :=
  (runStream stage state remaining).map_exact

/-- OSLF observes the terminating lowering at closure scale.  Primitive target
classification remains visible rather than being identified with one source
transition. -/
def reachabilityNTT
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (targetGSLT stage).closure)
      (oslfForwardModalObject (sourceGSLT stage).closure) :=
  (realization stage).closureOSLFPullback

/-- A classifier followed by a continuing dispatcher reflects one unique
authored source consumption step. -/
theorem classify_dispatch_reflects_consume
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    {state : State} {item : Item} {remaining : List Item}
    {middle : TargetTerm State Item Stop Class Row} {nextState : State}
    (classified : TargetStep stage (.pending state (item :: remaining)) middle)
    (dispatched : TargetStep stage middle (.pending nextState remaining)) :
    SourceStep stage (.running state (item :: remaining))
      (.running nextState remaining) := by
  cases classified
  case classify =>
    cases dispatched
    case consume accepted =>
      exact .consume state item remaining nextState
        ((stage.dispatch_correct state item).symm.trans accepted)

/-- The analogous reflection theorem for a stopping target dispatch. -/
theorem classify_dispatch_reflects_stop
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    {state : State} {item : Item} {remaining : List Item}
    {middle : TargetTerm State Item Stop Class Row} {reason : Stop}
    (classified : TargetStep stage (.pending state (item :: remaining)) middle)
    (dispatched : TargetStep stage middle
      (.stopped state item remaining reason)) :
    SourceStep stage (.running state (item :: remaining))
      (.stopped state item remaining reason) := by
  cases classified
  case classify =>
    cases dispatched
    case stop accepted =>
      exact .stop state item remaining reason
        ((stage.dispatch_correct state item).symm.trans accepted)

/-- No nonempty target pending state can skip the retained classified row. -/
theorem nonempty_pending_to_pending_not_targetStep
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state nextState : State) (item : Item)
    (remaining nextRemaining : List Item) :
    Not (TargetStep stage (.pending state (item :: remaining))
      (.pending nextState nextRemaining)) := by
  intro step
  cases step

/-- Nor can a nonempty target pending state jump straight to a stop without a
classified target row. -/
theorem nonempty_pending_to_stopped_not_targetStep
    {State Item Stop Class Row : Type u}
    (stage : Stage State Item Stop Class Row)
    (state : State) (item : Item) (remaining : List Item) (reason : Stop) :
    Not (TargetStep stage (.pending state (item :: remaining))
      (.stopped state item remaining reason)) := by
  intro step
  cases step

/-! ## Small controls -/

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

/-- One continuing item and one stopping item form a finite authored route
whose terminal state retains the triggering occurrence and unconsumed suffix. -/
def sourceRoute :
    ExecutionPath (sourceGSLT stage) (.running 0 [true, false, true])
      (.stopped 1 false [true] ()) :=
  .cons ⟨SourceStep.consume 0 true [false, true] 1 (by rfl)⟩
    (.cons ⟨SourceStep.stop 1 false [true] () (by rfl)⟩ (.refl _))

/-- The independently assembled target route keeps classification before both
the continue and stop dispatches. -/
def targetRoute :
    ExecutionPath (targetGSLT stage) (.pending 0 [true, false, true])
      (.stopped 1 false [true] ()) :=
  (consumePath stage 0 true [false, true] 1 (by rfl)).append
    (stopPath stage 1 false [true] () (by rfl))

theorem sourceRoute_length : sourceRoute.length = 2 := by
  rfl

theorem targetRoute_length : targetRoute.length = 4 := by
  rfl

/-- The actual path-valued realization has the same four target transitions
for the mixed route. -/
theorem mapped_sourceRoute_length :
    ((realization stage).mapRoute sourceRoute).length = 4 := by
  rfl

/-- The generic finite-stream construction retains the first stopping item and
the unconsumed suffix for the mixed canary stream. -/
def streamedRun : StreamRun stage 0 [true, false, true] :=
  runStream stage 0 [true, false, true]

theorem streamedRun_endpoint :
    streamedRun.endpoint = .stopped 1 false [true] () := by
  rfl

theorem streamedRun_source_length : streamedRun.sourcePath.length = 2 := by
  rfl

theorem streamedRun_target_length : streamedRun.targetPath.length = 4 := by
  rfl

theorem streamedRun_maps_exact :
    (realization stage).mapRoute streamedRun.sourcePath = streamedRun.targetPath :=
  streamedRun.map_exact

end Canary

#print axioms consumePath_length
#print axioms stopPath_length
#print axioms finishPath_length
#print axioms realization
#print axioms runStream_map_exact
#print axioms reachabilityNTT
#print axioms classify_dispatch_reflects_consume
#print axioms classify_dispatch_reflects_stop
#print axioms nonempty_pending_to_pending_not_targetStep
#print axioms nonempty_pending_to_stopped_not_targetStep
#print axioms Canary.sourceRoute_length
#print axioms Canary.targetRoute_length
#print axioms Canary.mapped_sourceRoute_length
#print axioms Canary.streamedRun_endpoint
#print axioms Canary.streamedRun_source_length
#print axioms Canary.streamedRun_target_length
#print axioms Canary.streamedRun_maps_exact

end Mettapedia.GSLT.ClassifierLowering.TerminatingStreaming
