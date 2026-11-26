import Mettapedia.Languages.MeTTa.SpaceTheory.HEObservationReplacement
import Mettapedia.Languages.MeTTa.SpaceTheory.EquationalLookupProtection

/-!
# Snapshot replacement for an equation-aware HE call

The ready request has two distinct read supports: its equation class,
and the complete frontier at each member that can be used. After entry,
the saved alternatives and the ordinary reached-world rules decide
the rest. Preserving both supports retains full timed observations,
without demanding that unrelated classes or definitions stay fixed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalReplacement

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result WorldEnvironment)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationRowResultsRel EquationWork)
open Mettapedia.GSLT.Contracts.OccurrenceObservers (Demand)
open Mettapedia.GSLT.Contracts.OccurrenceExecution (completed completed_iff_chain readCompleted reports ofTerm reports_congr)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Presentation.Schematic (SState)
open HEEquationalExecution (State Request Transition MayEnter Shows)
open EvaluationObservations (heEquationalView heEmit)
open EquationalLookupProtection (SameClass ClosedClass class_append_iff)

variable {Context World : Type}

def UnchangedBySuffix (before after : Space) (request : Request Context World) : Prop :=
  ∃ added, after = Space.ofList (before.atoms ++ added) ∧
    ClosedClass before.atoms added request.input.value.erase ∧
    ∀ representative, AtomEquations.Equivalent before.atoms request.input.value.erase representative →
      ∀ declaration ∈ added, ∀ ordinal,
        EquationRowResultsRel (request.expected :: request.input.live) representative
          request.input.frame.bindings ordinal declaration []

private theorem entry_append_iff (env : WorldEnvironment Context World) (other : World → Context → Space)
    (request : Request Context World) (same : UnchangedBySuffix (env.view request.world request.scope)
      (other request.world request.scope) request) (representative : Atom) (work : List EquationWork) :
    MayEnter env request representative work ↔ MayEnter {env with view := other} request representative work := by
  let before := env.view request.world request.scope
  let after := other request.world request.scope
  change UnchangedBySuffix before after request at same
  obtain ⟨added, appended, closed, rejected⟩ := same
  have equivalences : SameClass before.atoms after.atoms request.input.value.erase := by
    rw [appended]
    exact (class_append_iff before.atoms added request.input.value.erase).mpr closed
  have first := HEEquationEntry.entry_exact before env.dispatch request.expected request.input.live request.input.frame
    request.input.value.erase representative work
  have second := HEEquationEntry.entry_exact after env.dispatch request.expected request.input.live request.input.frame
    request.input.value.erase representative work
  refine first.trans (Iff.trans ?_ second.symm)
  constructor
  · rintro ⟨eqn, good, ordinary, frontier, nonempty⟩
    refine ⟨(equivalences _).mp eqn, good, ordinary, ?_, nonempty⟩
    rw [appended]
    exact (HEObservationReplacement.frontier_append_iff before added _ _ _ (rejected _ eqn) work).mpr frontier
  · rintro ⟨eqn, good, ordinary, frontier, nonempty⟩
    have was := (equivalences _).mpr eqn
    rw [appended] at frontier
    exact ⟨was, good, ordinary,
      (HEObservationReplacement.frontier_append_iff before added _ _ _ (rejected _ was) work).mp frontier, nonempty⟩

def PendingAgreement (before after : Space) (request : Request Context World) : Prop :=
  ∃ common : Space, UnchangedBySuffix common before request ∧ UnchangedBySuffix common after request

theorem entry_iff (env : WorldEnvironment Context World) (other : World → Context → Space)
    (request : Request Context World) (same : PendingAgreement (env.view request.world request.scope)
      (other request.world request.scope) request) (representative : Atom) (work : List EquationWork) :
    MayEnter env request representative work ↔ MayEnter {env with view := other} request representative work := by
  obtain ⟨common, first, second⟩ := same
  let prefixEnv : WorldEnvironment Context World := {env with view := fun _ _ => common}
  exact (entry_append_iff prefixEnv env.view request first representative work).symm.trans
    (entry_append_iff prefixEnv other request second representative work)

def AtPhase (env : WorldEnvironment Context World) (other : World → Context → Space) (policy : Policy) :
    State Context World → Prop
  | .pending request => PendingAgreement (env.view request.world request.scope) (other request.world request.scope) request
  | .running current => HEObservationReplacement.ProtectedAt env other policy current

theorem protected_step (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy)
    {before after : State Context World} (same : AtPhase env other p before) :
    (HEEquationalExecution.source env p).Step before after ↔
      (HEEquationalExecution.source {env with view := other} p).Step before after := by
  let pinned : WorldEnvironment Context World := {env with view := other}
  change Transition env p before after ↔ Transition pinned p before after
  constructor
  · intro step
    cases step with
    | select found => exact .select ((entry_iff env other _ same _ _).mp found)
    | ordinary step =>
      exact .ordinary ((HEControlOnTransform.source_step_iff pinned p _ _).mp
        ((HEObservationReplacement.protected_step env other p same).mp
          ((HEControlOnTransform.source_step_iff env p _ _).mpr step)))
  · intro step
    cases step with
    | select found => exact .select ((entry_iff env other _ same _ _).mpr found)
    | ordinary step =>
      exact .ordinary ((HEControlOnTransform.source_step_iff env p _ _).mp
        ((HEObservationReplacement.protected_step env other p same).mpr
          ((HEControlOnTransform.source_step_iff pinned p _ _).mpr step)))

private theorem protected_chain (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy)
    (current : State Context World) (tail : List (State Context World))
    (same : ∀ reached, (HEEquationalExecution.source {env with view := other} p).MultiStep current reached →
      AtPhase env other p reached) :
    (current :: tail).IsChain (Transition env p) ↔
      (current :: tail).IsChain (Transition {env with view := other} p) := by
  induction tail generalizing current with
  | nil => simp
  | cons next tail ih =>
    simp only [List.isChain_cons_cons]
    have first : Transition env p current next ↔ Transition {env with view := other} p current next :=
      protected_step env other p (after := next) (same current (.refl _))
    rw [first]
    apply and_congr_right
    intro agreed
    exact ih next (fun reached remaining => same reached (.step agreed remaining))

theorem protected_reports_on_transform {O : Type} [DecidableEq O] [Infinite O]
    (env : WorldEnvironment Context World) (other : World → Context → Space) (p : Policy)
    (code : HENativeOnTransform.Presentation Context World) {current : State Context World} {start : SState O}
    (shown : Shows code current start)
    (same : ∀ reached, (HEEquationalExecution.source {env with view := other} p).MultiStep current reached →
      AtPhase env other p reached)
    (demand : Demand) (answer : Mettapedia.GSLT.Contracts.OccurrenceObservers.Result Result demand) :
    reports (completed (sys := HEEquationalExecution.source env p) heEquationalView (·.finished = true) heEmit current)
      demand answer ↔
    reports (readCompleted (sys := HEEquationalExecution.theory O code {env with view := other} p)
      (ofTerm (Shows code) heEquationalView) (·.finished = true) heEmit start) demand answer := by
  refine Iff.trans ?_ (EvaluationObservations.he_equational_reports_iff {env with view := other} p code shown demand answer)
  apply reports_congr
  intro trace
  refine (completed_iff_chain (sys := HEEquationalExecution.source env p)
    heEquationalView _ heEmit current trace).trans (Iff.trans ?_
      (completed_iff_chain (sys := HEEquationalExecution.source {env with view := other} p)
        heEquationalView _ heEmit current trace).symm)
  constructor
  · rintro ⟨tail, finish, chain, last, done, batches⟩
    exact ⟨tail, finish, (protected_chain env other p current tail same).mp chain, last, done, batches⟩
  · rintro ⟨tail, finish, chain, last, done, batches⟩
    exact ⟨tail, finish, (protected_chain env other p current tail same).mpr chain, last, done, batches⟩

end Mettapedia.Languages.MeTTa.SpaceTheory.HEEquationalReplacement
