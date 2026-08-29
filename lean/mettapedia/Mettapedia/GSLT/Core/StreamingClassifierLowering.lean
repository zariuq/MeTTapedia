import Mettapedia.GSLT.Core.ClassifierLowering

/-!
# Streaming classifier lowerings

`ClassifierLowering.Stage` describes one authored operation lowered to an
explicit target classification followed by dispatch.  This module is the
reusable finite-stream construction: it threads the authored state through a
list of input occurrences, retains every classified target row, and gives the
whole stream one path-valued GSLT realization.

The construction is deliberately not a list-producing source translation.
Each source item remains pending until its own classifier and dispatcher run
in the target machine.  Consequently a stream with `n` items has exactly
`2 * n + 1` target transitions: two for every supplied item and one explicit
end-of-stream transition.

This is repeated use of one compatible classifier stage.  Composition between
different stages remains the existing `OperationalRealization.comp` when their
GSLT boundaries agree, or the presentation-sensitive transformation interface
when a real compiled artifact mediates the boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ClassifierLowering.Streaming

open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.IndexedModalFunctor
open Mettapedia.GSLT.Ultrainfinite

universe u

/-- A source stream retains both its threaded state and all unconsumed input
occurrences.  Completion is distinct from an empty pending stream. -/
inductive SourceTerm (State : Type u) (Item : Type u) where
  | running (state : State) (remaining : List Item)
  | finished (state : State)

/-- The target stream retains one classified input occurrence and its
target-owned row between classification and dispatch. -/
inductive TargetTerm
    (State : Type u) (Item : Type u) (Class : Type u) (Row : Type u) where
  | pending (state : State) (remaining : List Item)
  | classified (state : State) (item : Item) (remaining : List Item)
      (classification : Class) (row : Row)
  | finished (state : State)

/-- The source consumes exactly one input occurrence, or explicitly reaches
its end-of-stream state. -/
inductive SourceStep
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    SourceTerm State Item -> SourceTerm State Item -> Prop where
  | consume (state : State) (item : Item) (remaining : List Item) :
      SourceStep stage
        (.running state (item :: remaining))
        (.running (stage.authoredRun (state, item)) remaining)
  | finish (state : State) :
      SourceStep stage (.running state []) (.finished state)

/-- The target cannot consume an item atomically: it first records its class
and row, then dispatches that retained classification. -/
inductive TargetStep
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    TargetTerm State Item Class Row -> TargetTerm State Item Class Row -> Prop where
  | classify (state : State) (item : Item) (remaining : List Item) :
      TargetStep stage
        (.pending state (item :: remaining))
        (.classified state item remaining
          (stage.classify (state, item))
          (stage.row (state, item) (stage.classify (state, item))))
  | dispatch (state : State) (item : Item) (remaining : List Item) :
      TargetStep stage
        (.classified state item remaining
          (stage.classify (state, item))
          (stage.row (state, item) (stage.classify (state, item))))
        (.pending
          (stage.dispatch (state, item) (stage.classify (state, item)))
          remaining)
  | finish (state : State) :
      TargetStep stage (.pending state []) (.finished state)

/-- The GSLT of the authored state-threaded stream. -/
def sourceGSLT
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) : GSLT where
  Term := SourceTerm State Item
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

/-- The target GSLT of classified, row-retaining stream execution. -/
def targetGSLT
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) : GSLT where
  Term := TargetTerm State Item Class Row
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

/-- Embed a source stream state into the corresponding externally observable
target stream state. -/
def mapTerm
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u} :
    SourceTerm State Item -> TargetTerm State Item Class Row
  | .running state remaining => .pending state remaining
  | .finished state => .finished state

/-- The two primitive target steps for one supplied stream occurrence before
reindexing the endpoint through semantic adequacy. -/
def consumePath
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (item : Item) (remaining : List Item) :
    ExecutionPath (targetGSLT stage)
      (.pending state (item :: remaining))
      (.pending
        (stage.dispatch (state, item) (stage.classify (state, item)))
        remaining) :=
  .cons ⟨TargetStep.classify state item remaining⟩
    (.cons ⟨TargetStep.dispatch state item remaining⟩ (.refl _))

/-- Reindex the two-step target path to the independently authored successor
state without hiding either administrative target transition. -/
def consumePathAtAuthored
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (item : Item) (remaining : List Item) :
    ExecutionPath (targetGSLT stage)
      (.pending state (item :: remaining))
      (.pending (stage.authoredRun (state, item)) remaining) :=
  Mettapedia.GSLT.ClassifierLowering.transportTarget
    (congrArg (fun nextState => TargetTerm.pending nextState remaining)
      (stage.dispatch_correct (state, item)))
    (consumePath stage state item remaining)

/-- One input occurrence always retains exactly classifier then dispatcher. -/
theorem consumePathAtAuthored_length
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (item : Item) (remaining : List Item) :
    (consumePathAtAuthored stage state item remaining).length = 2 := by
  unfold consumePathAtAuthored
  rw [Mettapedia.GSLT.ClassifierLowering.transportTarget_length]
  rfl

/-- End-of-stream is a separately retained target transition. -/
def finishPath
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) (state : State) :
    ExecutionPath (targetGSLT stage) (.pending state []) (.finished state) :=
  .cons ⟨TargetStep.finish state⟩ (.refl _)

theorem finishPath_length
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) (state : State) :
    (finishPath stage state).length = 1 :=
  rfl

/-- Lower a proposition-valued authored stream step to independently
constructed target path evidence.  As in the one-step core, source evidence
is used only to recover the endpoint propositionally; it never manufactures
target execution data. -/
def lowerStep
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    {source target : SourceTerm State Item}
    (step : SourceStep stage source target) :
    ExecutionPath (targetGSLT stage) (mapTerm source) (mapTerm target) := by
  cases source with
  | running state remaining =>
      cases remaining with
      | nil =>
          have targetEqual : target = .finished state := by
            cases step
            rfl
          subst target
          exact finishPath stage state
      | cons item remaining =>
          have targetEqual :
              target = .running (stage.authoredRun (state, item)) remaining := by
            cases step
            rfl
          subst target
          exact consumePathAtAuthored stage state item remaining
  | finished state =>
      exact False.elim (by cases step)

/-- The state-threaded stream is a path-valued GSLT-to-GSLT realization. -/
def realization
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    OperationalRealization (sourceGSLT stage) (targetGSLT stage) where
  mapTerm := mapTerm
  mapEquiv := by
    intro left right equal
    subst right
    rfl
  mapStep := lowerStep stage

/-- A target classifier/dispatcher pair cannot invent a stream consumption:
when its two retained target steps begin at a pending source occurrence and
return to the matching tail, they reconstruct the unique authored source
transition. -/
theorem classify_dispatch_reflects_source
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    {state : State} {item : Item} {remaining : List Item}
    {middle : TargetTerm State Item Class Row} {nextState : State}
    (classified : TargetStep stage (.pending state (item :: remaining)) middle)
    (dispatched : TargetStep stage middle (.pending nextState remaining)) :
    SourceStep stage (.running state (item :: remaining))
      (.running nextState remaining) := by
  cases classified
  cases dispatched
  rw [stage.dispatch_correct]
  exact SourceStep.consume state item remaining

/-- OSLF sees the finite stream lowering at reachability scale.  This is not
an identification with the target's primitive one-step native theory. -/
def reachabilityNTT
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    ForwardModalPredicateTheory.Hom
      (oslfForwardModalObject (targetGSLT stage).closure)
      (oslfForwardModalObject (sourceGSLT stage).closure) :=
  (realization stage).closureOSLFPullback

/-- Thread the independently authored state transition through a finite input
stream without producing a decompressed instruction list. -/
def runState
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    State -> List Item -> State
  | state, [] => state
  | state, item :: remaining =>
      runState stage (stage.authoredRun (state, item)) remaining

/-- The authored stream route retains every source occurrence plus an explicit
end-of-stream transition. -/
def sourceRunPath
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    (state : State) -> (items : List Item) ->
      ExecutionPath (sourceGSLT stage)
        (.running state items) (.finished (runState stage state items))
  | state, [] => .cons ⟨SourceStep.finish state⟩ (.refl _)
  | state, item :: remaining =>
      .cons ⟨SourceStep.consume state item remaining⟩
        (sourceRunPath stage (stage.authoredRun (state, item)) remaining)

/-- The independently constructed target route makes every classification row
visible and threads exactly the authored successor state to the next item. -/
def targetRunPath
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row) :
    (state : State) -> (items : List Item) ->
      ExecutionPath (targetGSLT stage)
        (.pending state items) (.finished (runState stage state items))
  | state, [] => finishPath stage state
  | state, item :: remaining =>
      (consumePathAtAuthored stage state item remaining).append
        (targetRunPath stage (stage.authoredRun (state, item)) remaining)

/-- The compiled route is exactly the target route assembled occurrence by
occurrence; no target step is supplied by a source proof witness. -/
theorem realization_maps_sourceRunPath
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (items : List Item) :
    (realization stage).mapRoute (sourceRunPath stage state items) =
      targetRunPath stage state items := by
  induction items generalizing state with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      change
        (consumePathAtAuthored stage state item remaining).append
            ((realization stage).mapRoute
              (sourceRunPath stage (stage.authoredRun (state, item)) remaining)) =
          (consumePathAtAuthored stage state item remaining).append
            (targetRunPath stage (stage.authoredRun (state, item)) remaining)
      rw [inductionHypothesis]
      rfl

/-- The source route has one transition per input occurrence plus its explicit
end marker. -/
theorem sourceRunPath_length
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (items : List Item) :
    (sourceRunPath stage state items).length = items.length + 1 := by
  induction items generalizing state with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [sourceRunPath, Route.length, List.length_cons]
      exact congrArg (fun length => length + 1)
        (inductionHypothesis (stage.authoredRun (state, item)))

/-- A finite stream takes exactly two target transitions per occurrence and
one target end transition.  This is a semantic step bound, not an expansion
of the stream into normal proof labels. -/
theorem targetRunPath_length
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state : State) (items : List Item) :
    (targetRunPath stage state items).length = 2 * items.length + 1 := by
  induction items generalizing state with
  | nil => rfl
  | cons item remaining inductionHypothesis =>
      simp only [targetRunPath, Route.length_append, List.length_cons]
      rw [consumePathAtAuthored_length]
      calc
        2 + (targetRunPath stage
            (stage.authoredRun (state, item)) remaining).length =
            2 + (2 * remaining.length + 1) :=
          congrArg (fun length => 2 + length)
            (inductionHypothesis (stage.authoredRun (state, item)))
        _ = 2 * (remaining.length + 1) + 1 := by omega

/-- Equal classified target states retain the same input occurrence. -/
theorem classified_item_injective
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    {stateLeft stateRight : State} {left right : Item}
    {remainingLeft remainingRight : List Item}
    {classLeft classRight : Class} {rowLeft rowRight : Row}
    (equal :
      @TargetTerm.classified State Item Class Row stateLeft left remainingLeft
        classLeft rowLeft =
      @TargetTerm.classified State Item Class Row stateRight right remainingRight
        classRight rowRight) :
    left = right := by
  injection equal

/-- Negative control: a nonempty source stream cannot skip its classified
target row by taking a primitive pending-to-pending transition. -/
theorem nonempty_pending_to_pending_not_targetStep
    {State : Type u} {Item : Type u} {Class : Type u} {Row : Type u}
    (stage : Stage (State × Item) State Class Row)
    (state nextState : State) (item : Item)
    (remaining nextRemaining : List Item) :
    Not (TargetStep stage (.pending state (item :: remaining))
      (.pending nextState nextRemaining)) := by
  intro step
  cases step

/-! ## Small concrete controls -/

namespace Canary

def stage : Stage (Nat × Bool) Nat Bool Nat where
  authoredRun := fun (state, item) => if item then state + 1 else state
  classify := fun (_, item) => item
  dispatch := fun (state, _) item => if item then state + 1 else state
  row := fun (state, _) item => if item then state + 100 else state
  dispatch_correct := by
    intro input
    rcases input with ⟨state, item⟩
    cases item <;> rfl

/-- Two input occurrences retain four classifier/dispatch transitions and one
explicit end transition. -/
theorem two_items_have_five_target_steps :
    (targetRunPath stage 0 [true, false]).length = 5 := by
  exact targetRunPath_length stage 0 [true, false]

/-- The final state is the one obtained by sequentially threading the
authored operation, not a source-side list compilation result. -/
theorem two_items_thread_authored_state :
    runState stage 0 [true, false] = 1 := by
  rfl

end Canary

#print axioms consumePathAtAuthored_length
#print axioms lowerStep
#print axioms realization
#print axioms classify_dispatch_reflects_source
#print axioms reachabilityNTT
#print axioms realization_maps_sourceRunPath
#print axioms sourceRunPath_length
#print axioms targetRunPath_length
#print axioms classified_item_injective
#print axioms nonempty_pending_to_pending_not_targetStep
#print axioms Canary.two_items_have_five_target_steps
#print axioms Canary.two_items_thread_authored_state

end Mettapedia.GSLT.ClassifierLowering.Streaming
