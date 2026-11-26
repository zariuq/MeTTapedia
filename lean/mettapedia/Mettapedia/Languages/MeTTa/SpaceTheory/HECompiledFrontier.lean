import Mettapedia.Languages.MeTTa.SpaceTheory.HEFrontierTransport
import Mettapedia.Languages.MeTTa.SpaceTheory.EvaluationObservations

/-!
# HE snapshot compilation with relocated occurrence evidence

An invocation can reuse a complete frontier from another snapshot
when it has an ordered alignment for this query. Only ordinals are
relocated. Rejected insertions and removals produce no work. If no
alignment is supplied the invocation reads the live frontier.

Reuse is installed at the existing Transform invocation ports.
Selection, scoped typing, grounded operations, return, and publication
use the original rules and reached world. The theorem preserves all
seven observations of that same rule program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledFrontier

open Mettapedia.GSLT (GSLT)
open Mettapedia.GSLT.Contracts.OccurrenceObservers (Demand)
open Mettapedia.GSLT.Contracts.OccurrenceExecution (completed readCompleted reports ofTerm)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (NonGroundedCallRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (WorldConfiguration)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
open HEInvocationEntry (Input Mode Request Reply Licensed)
open HEFrontierTransport (Alignment relabel)
open HENativeOnTransform (Presentation)
open EvaluationObservations (heView heEmit)

variable {Context World : Type}

/-- A per-call witness; calls outside its supported reads may fall
back without invalidating a different call's saved compilation. -/
abbrev Plans (env : WorldEnvironment Context World) (snapshot : World → Context → Space) :=
  (world : World) → (scope : Context) → (input : Input) → (mode : Mode) →
    Option (Alignment (mode.protect input.live) input.value.erase input.frame.bindings
      (snapshot world scope).atoms (env.view world scope).atoms)

def selectedFrontier (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : Plans env snapshot) (world : World) (scope : Context) (input : Input) (mode : Mode)
    (work : List EquationWork) : Prop :=
  match plans world scope input mode with
  | none =>
    EquationFrontierRel (env.view world scope) (mode.protect input.live) input.value.erase input.frame.bindings work
  | some route =>
    ∃ previous, EquationFrontierRel (snapshot world scope) (mode.protect input.live) input.value.erase
        input.frame.bindings previous ∧
      relabel (route.pairing 0 0) previous = some work

theorem selected_frontier_exact (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : Plans env snapshot) (world : World) (scope : Context) (input : Input) (mode : Mode)
    (work : List EquationWork) :
    selectedFrontier env snapshot plans world scope input mode work ↔
      EquationFrontierRel (env.view world scope) (mode.protect input.live) input.value.erase input.frame.bindings work := by
  unfold selectedFrontier
  split
  · rfl
  · exact (HEFrontierTransport.frontier_iff_relabel ‹_› work).symm

def authorize (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : Plans env snapshot) (policy : Policy) (world : World) (scope : Context)
    (request : Request) (reply : Reply) (next : World) : Prop :=
  match request, reply with
  | .invoke input mode, .query work =>
    next = world ∧ mode.mayInvoke input ∧ NonGroundedCallRel env.dispatch input.value.erase ∧
      selectedFrontier env snapshot plans world scope input mode work
  | _, _ => Licensed env policy world scope request reply next

theorem authorize_exact (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : Plans env snapshot) (policy : Policy) (world : World) (scope : Context)
    (request : Request) (reply : Reply) (next : World) :
    authorize env snapshot plans policy world scope request reply next ↔
      Licensed env policy world scope request reply next := by
  cases request with
  | retained => cases reply <;> rfl
  | invoke input mode =>
    cases reply <;> try rfl
    case query work =>
      simp only [authorize, Licensed, selected_frontier_exact]

def operations (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (plans : Plans env snapshot) (policy : Policy) : Relations :=
  fun port args result =>
    if 9 ≤ port ∧ port < 12 then
      HEInvocationOnTransform.operationsFrom code env.dispatch policy
        (authorize env snapshot plans policy) port args result
    else HEControlOnTransform.operations code env policy port args result

theorem operations_exact (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (plans : Plans env snapshot) (policy : Policy) :
    operations code env snapshot plans policy = HEControlOnTransform.operations code env policy := by
  have auth : authorize env snapshot plans policy = Licensed env policy := by
    funext world scope request reply next
    exact propext (authorize_exact env snapshot plans policy world scope request reply next)
  funext name args result
  unfold operations
  by_cases invocation : 9 ≤ name ∧ name < 12
  · have notNative : name ≠ 0 := by omega
    have notContext : ¬ name < 3 := by omega
    have notTyped : ¬ name < 9 := by omega
    simp only [if_pos invocation, auth, HEControlOnTransform.operations, if_neg notNative,
      if_neg notContext, if_neg notTyped, if_pos invocation.2, HEInvocationOnTransform.operations]
  · exact if_neg invocation

def theory (O : Type) [DecidableEq O] (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (plans : Plans env snapshot) (policy : Policy) : GSLT :=
  programSystem O (specialized rows (relationGraph (operations code env snapshot plans policy))
    {rule | rule ∈ HEControlOnTransform.rules})

theorem theory_exact (O : Type) [DecidableEq O] (code : Presentation Context World)
    (env : WorldEnvironment Context World) (snapshot : World → Context → Space)
    (plans : Plans env snapshot) (policy : Policy) :
    theory O code env snapshot plans policy = HEControlOnTransform.theory O code env policy := by
  unfold theory
  rw [operations_exact]
  rfl

theorem compiled_reports_iff {O : Type} [DecidableEq O] [Infinite O]
    (code : Presentation Context World) (env : WorldEnvironment Context World)
    (snapshot : World → Context → Space) (plans : Plans env snapshot) (policy : Policy)
    {source : WorldConfiguration Context World} {start : SState O}
    (shown : HEControlOnTransform.Shows code source start)
    (demand : Demand) (answer : Mettapedia.GSLT.Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEControlOnTransform.source env policy) heView (·.finished = true) heEmit source)
      demand answer ↔
    reports (readCompleted (sys := theory O code env snapshot plans policy)
      (ofTerm (HEControlOnTransform.Shows code) heView) (·.finished = true) heEmit start) demand answer := by
  let observe (ops : Relations) :=
    reports (readCompleted (sys := programSystem O
      (specialized rows (relationGraph ops) {rule | rule ∈ HEControlOnTransform.rules}))
      (ofTerm (HEControlOnTransform.Shows code) heView) (·.finished = true) heEmit start) demand answer
  change _ ↔ observe (operations code env snapshot plans policy)
  rw [operations_exact]
  exact EvaluationObservations.he_reports_iff env policy code shown demand answer

/-- An example that never uses the fallback, including for the first
matching definition after the insertion. -/
def prependedPlans (env : WorldEnvironment Context World) (note : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (irrelevant : ∀ lhs rhs, note ≠ .expression [.symbol "=", lhs, rhs]) :
    Plans {env with view := fun world scope => ⟨note :: (env.view world scope).atoms⟩} env.view :=
  fun world scope _ _ =>
    some (.insert (fun ordinal => .irrelevant ordinal note irrelevant) (.stay (env.view world scope).atoms))

end Mettapedia.Languages.MeTTa.SpaceTheory.HECompiledFrontier
