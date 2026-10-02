import Mettapedia.Machines.ScopedCommit

/-!
# Ordered pure guards inside effectful calls

This is an algebra of the existing `ScopedCommit` controls, not another query
interpreter. A qualified pure guard supplies its complete ordered list of
refined local states. The caller's success and failure continuations retain
the performed world, so a consumer's effects are not rolled back between
answers. Unqualified, suspended or faulting services must use their ordinary
query continuations; they do not supply such a list merely by timing out.

Singleton fusion removes a choice without discarding its refinement. Pipeline
composition preserves ordered occurrences, including duplicates. These laws
justify replacing only the guard boundary; argument execution, body execution
and result publication remain the existing caller's continuations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedGuardPipeline

open ScopedCommit

variable {Local World Result : Type}

abbrev Guard (Local : Type) := Local → List Local

def guard (answers : Guard Local) (next : Body Local World) : Body Local World :=
  .choose (fun state _ => answers state) next

def pipeline : List (Guard Local) → Body Local World → Body Local World
  | [], next => next
  | stage :: stages, next => guard stage (pipeline stages next)

/-- The pure ordered refinement algebra; it does not execute a body. -/
def refinements : List (Guard Local) → Local → List Local
  | [], state => [state]
  | stage :: stages, state => (stage state).flatMap (refinements stages)

theorem pipeline_append (first later : List (Guard Local))
    (next : Body Local World) :
    pipeline (first ++ later) next = pipeline first (pipeline later next) := by
  induction first with
  | nil => rfl
  | cons stage stages ih => simp only [List.cons_append, pipeline, ih]

theorem refinements_append (first later : List (Guard Local)) (state : Local) :
    refinements (first ++ later) state =
      (refinements first state).flatMap (refinements later) := by
  induction first generalizing state with
  | nil => simp [refinements]
  | cons stage stages ih =>
      simp only [List.cons_append, refinements, List.flatMap_assoc]
      exact congrArg (fun next => (stage state).flatMap next) (funext ih)

/-- Replacing a provider's ordered states preserves arbitrary effectful
continuations. Equality of a set of states would not suffice here. -/
theorem guard_congr (first second : Guard Local) (next : Body Local World)
    (state : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World)
    (same : first state = second state) :
    eval (guard first next) state success failure saved world =
      eval (guard second next) state success failure saved world := by
  simp only [guard, eval, same]

/-- A singleton direct step retains the actual refined state. The statement
quantifies over both continuations, including the saved outer alternative. -/
theorem singleton_fusion (answers : Guard Local) (refine : Local → Local)
    (next : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) (single : answers state = [refine state]) :
    eval (guard answers next) state success failure saved world =
      eval (.effect (fun state world => (refine state, world)) next)
        state success failure saved world := by
  simp [guard, eval, single]

theorem identity_fusion (next : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (guard (fun state => [state]) next) state success failure saved world =
      eval next state success failure saved world := by
  simp [guard, eval]

theorem rejection_fusion (next : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (guard (fun _ => []) next) state success failure saved world =
      failure world := rfl

/-- The direct conditional still publishes the successful binding refinement. -/
theorem decision_fusion (test : Local → Bool) (refine : Local → Local)
    (next : Body Local World) (state : Local)
    (success : Success Local World Result) (failure saved : Failure World Result)
    (world : World) :
    eval (guard (fun state => if test state then [refine state] else []) next)
        state success failure saved world =
      eval (.branch (fun state _ => test state)
        (.effect (fun state world => (refine state, world)) next) .fail)
        state success failure saved world := by
  cases h : test state <;> simp [guard, eval, h]

/-- Two adjacent pure guards can share one refinement computation. No body
effects move across this boundary. -/
theorem adjacent_guards (first second : Guard Local) (next : Body Local World)
    (state : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (guard first (guard second next)) state success failure saved world =
      eval (guard (fun state => (first state).flatMap second) next)
        state success failure saved world := by
  simp only [guard, eval]
  have folded : ∀ states : List Local,
      (states.foldr (fun state rest => fun world =>
        ((second state).foldr (fun refined pending => fun world =>
          eval next refined success pending saved world) rest) world) failure) =
      ((states.flatMap second).foldr (fun refined pending => fun world =>
        eval next refined success pending saved world) failure) := by
    intro states
    induction states with
    | nil => rfl
    | cons state states ih =>
        simp only [List.foldr_cons, List.flatMap_cons, List.foldr_append, ih]
  exact congrFun (folded (first state)) world

/-- The complete guard pipeline, not only one successful branch, refines to
one ordered provider before the existing body continuation. -/
theorem pipeline_fusion (stages : List (Guard Local)) (next : Body Local World)
    (state : Local) (success : Success Local World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (pipeline stages next) state success failure saved world =
      eval (guard (refinements stages) next) state success failure saved world := by
  induction stages generalizing state success failure saved world with
  | nil => simp [pipeline, refinements, guard, eval]
  | cons stage stages ih =>
      simp only [pipeline, guard, eval]
      have folded : ∀ states : List Local,
          (states.foldr (fun state rest => fun world =>
            eval (pipeline stages next) state success rest saved world) failure) =
          (states.foldr (fun state rest => fun world =>
            eval (guard (refinements stages) next) state success rest saved world) failure) := by
        intro states
        induction states with
        | nil => rfl
        | cons state states ihStates =>
            simp only [List.foldr_cons, ihStates]
            funext world
            exact ih state success _ saved world
      rw [folded]
      exact adjacent_guards stage (refinements stages) next state
        success failure saved world

theorem guard_readout (answers : Guard Local) (state : Local) (world : World) :
    run (guard answers .done) state world = (answers state, world) := by
  have collectList : ∀ states : List Local,
      (states.foldr (fun state rest => fun world => collect state rest world) finish) world =
        (states, world) := by
    intro states
    induction states with
    | nil => rfl
    | cons state states ih =>
        exact congrArg (fun rest : Observation Local World => (state :: rest.1, rest.2)) ih
  exact collectList (answers state)

/-- Erasing a pure guard for all continuation consumers requires exactly one
answer carrying the original state. Merely binding a previously fresh type
variable, or producing two identical witnesses, does not meet this law. -/
theorem guard_erasure_iff (answers : Guard Local) (state : Local) (world : World) :
    (∀ (success : Success Local World (Observation Local World)) failure saved,
      eval (guard answers .done) state success failure saved world =
        eval .done state success failure saved world) ↔ answers state = [state] := by
  constructor
  · intro erased
    have readout := erased collect finish finish
    change run (guard answers .done) state world = ([state], world) at readout
    rw [guard_readout] at readout
    exact congrArg Prod.fst readout
  · intro unchanged success failure saved
    simp [guard, eval, unchanged]

namespace Controls

def duplicated : Guard Nat := fun state => [state + 1, state + 1]
def binding : Guard Nat := fun _ => [7]

theorem duplicate_bindings_remain_occurrences :
    refinements [duplicated, binding] 0 = [7, 7] := rfl

theorem discarding_a_refinement_changes_the_result :
    (run (guard binding .done) 0 ()).1 ≠
      (run (guard (fun state => [state]) .done) 0 ()).1 := by decide

def touchingBody : Body Nat Nat := .effect (fun state world => (state, world + 1)) .done

theorem consumers_share_the_performed_world :
    run (guard duplicated touchingBody) 0 0 = ([1, 1], 2) := rfl

theorem failed_result_check_keeps_the_body_effect :
    run (.effect (fun state world => (state, world + 1))
      (guard (fun _ => []) .done)) 0 0 = ([], 1) := rfl

theorem moving_a_result_check_before_the_body_loses_effects :
    run (.effect (fun state world => (state, world + 1))
      (guard (fun _ => []) .done)) 0 0 ≠
      run (guard (fun _ => []) touchingBody) 0 0 := by decide

end Controls

end Mettapedia.Machines.OrderedGuardPipeline
