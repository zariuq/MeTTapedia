import Mettapedia.Logic.LP.PrivateVariableUnification
import Mettapedia.Machines.OrderedGuardPipeline

/-!
# Private variables in intrinsic type guards

The base PeTTa candidate clause `get_type_candidate(X, _) :- var(X), !`
has one anonymous output variable. With a resolved variable subject, its
private head match accepts the incoming requirement and leaves public caller
observations unchanged. The cut makes this candidate complete within the
intrinsic candidate relation. Authored get-type clauses are outside that cut,
so this law does not erase their alternatives or effects.

For constructor-shaped requirements, a separate ordered row traversal proves
that fresh field aliases can be replaced by the incoming fields. Each child
query receives the same resolved subject and requirement, and actual LP
unification preserves shared caller variables in all surviving branches.

The projection proof comes from the actual LP unifier; the continuation proof
uses the ordered effect-sensitive guard algebra. Native identities, fresh
allocation, resolution of incoming bindings and classifier exclusion require
the corresponding C adapter and ownership checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.VariableTypeGuard

open Mettapedia.Logic.LP
open Mettapedia.Machines ScopedCommit OrderedGuardPipeline

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols] {World Result : Type}

/-- The private clause-head substitution disappears under the caller's
projection before its ordinary effectful consumer is invoked. -/
theorem intrinsic_variable_guard_erasure (privateVar : σ.vars) (required : Term σ)
    (observations : List (Term σ))
    (requiredFresh : required.occursIn privateVar = false)
    (observationsFresh : ∀ term ∈ observations, term.occursIn privateVar = false)
    (next : Body (List (Term σ)) World)
    (success : Success (List (Term σ)) World Result)
    (failure saved : Failure World Result) (world : World) :
    eval (guard (fun state => privateVariableAnswers privateVar required state) next)
      observations success failure saved world =
    eval next observations success failure saved world := by
  rw [guard_congr (fun state => privateVariableAnswers privateVar required state)
    (fun state => [state]) next observations success failure saved world
    (private_variable_answers_identity privateVar required observations
      requiredFresh observationsFresh)]
  exact identity_fusion next observations success failure saved world

namespace BoundRow

/-- One admitted intrinsic child query, given its resolved subject and actual
requirement. Answers are resolved terms in the caller's namespace; freshly
introduced variables must not capture private row identifiers. This service
boundary excludes authored classifier effects and the enclosing fallback. -/
abbrev Query (σ : LPSignature) := Term σ → Term σ → List (Term σ)

/-- The intrinsic variable-subject clause commits without refining the
requirement. Other subjects query that actual requirement, then match each
ordered answer using the LP unifier. Failure drops only that answer. -/
def childRefinements (query : Query σ) (fuel : Nat)
    (subject required : Term σ) : List (Subst σ) :=
  match subject with
  | .var _ => [Subst.id σ]
  | _ => (query subject required).flatMap
      (fun answer => (unifyFuel fuel [(answer, required)]).toList)

/-- The native row loop's binding-store presentation: resolve the next
subject and requirement on entry, retain each refinement in its own branch,
and publish the row and public observations after all children succeed. -/
def withStore (query : Query σ) (fuel : Nat) :
    List (Term σ × Term σ) → Term σ → List (Term σ) → Subst σ →
      List (Term σ × List (Term σ))
  | [], row, observations, store =>
      [(store.applyTerm row, observations.map store.applyTerm)]
  | (subject, required) :: pending, row, observations, store =>
      (childRefinements query fuel (store.applyTerm subject)
        (store.applyTerm required)).flatMap fun refinement =>
          withStore query fuel pending row observations (refinement ∘ₛ store)

/-- A separate resolved-term presentation of the same row protocol. Each
answer substitutes the remaining subjects and requirements together, which
preserves variables shared across subject and type positions. -/
def resolved (query : Query σ) (fuel : Nat) :
    List (Term σ × Term σ) → Term σ → List (Term σ) →
      List (Term σ × List (Term σ))
  | [], row, observations => [(row, observations)]
  | (subject, required) :: pending, row, observations =>
      (childRefinements query fuel subject required).flatMap fun refinement =>
        resolved query fuel
          (pending.map (fun pair =>
            (refinement.applyTerm pair.1, refinement.applyTerm pair.2)))
          (refinement.applyTerm row) (observations.map refinement.applyTerm)
termination_by pending => pending.length
decreasing_by simp_wf

/-- Every recursive query receives the same resolved subject and requirement
in the two presentations. The induction preserves the full ordered answer
list, including duplicates and failed trials between successful answers. -/
theorem withStore_eq_resolved (query : Query σ) (fuel : Nat)
    (pending : List (Term σ × Term σ)) (row : Term σ)
    (observations : List (Term σ)) (store : Subst σ) :
    withStore query fuel pending row observations store =
      resolved query fuel
        (pending.map (fun pair => (store.applyTerm pair.1, store.applyTerm pair.2)))
        (store.applyTerm row) (observations.map store.applyTerm) := by
  induction pending generalizing row observations store with
  | nil => simp only [withStore, List.map_nil, resolved]
  | cons pair pending ih =>
      rcases pair with ⟨subject, required⟩
      simp only [withStore, List.map_cons, resolved]
      apply congrArg (fun next =>
        (childRefinements query fuel (store.applyTerm subject)
          (store.applyTerm required)).flatMap next)
      funext refinement
      rw [ih]
      simp only [List.map_map, Subst.applyTerm_comp, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro term _
      exact Subst.applyTerm_comp refinement store term

/-- Eliminate the initial private row aliases for any row width. The left
side uses the actual constructor unifier's substitution; the right starts
with the required row and an empty store. All later queries and matching
remain in place, with no restriction on public variable sharing. -/
theorem eliminate_private_row (query : Query σ) (fuel : Nat)
    (function : σ.functionSymbols)
    (names : Fin (σ.functionArity function) → σ.vars)
    (subjects required : Fin (σ.functionArity function) → Term σ)
    (observations : List (Term σ))
    (distinct : Function.Injective names)
    (requiredFresh : ∀ i j, (required j).occursIn (names i) = false)
    (subjectsFresh : ∀ i j, (subjects j).occursIn (names i) = false)
    (observationsFresh : ∀ term ∈ observations, ∀ i,
      term.occursIn (names i) = false) :
    withStore query fuel
      ((List.finRange (σ.functionArity function)).map
        (fun i => (subjects i, .var (names i))))
      (.app function (fun i => .var (names i))) observations
      (privateFieldSubstitution
        ((List.finRange (σ.functionArity function)).map
          (fun i => (names i, required i)))) =
    withStore query fuel
      ((List.finRange (σ.functionArity function)).map
        (fun i => (subjects i, required i)))
      (.app function required) observations (Subst.id σ) := by
  let fields := (List.finRange (σ.functionArity function)).map
    (fun i => (names i, required i))
  let store := privateFieldSubstitution fields
  have keepsPublic (term : Term σ) (fresh : ∀ i, term.occursIn (names i) = false) :
      store.applyTerm term = term := by
    apply private_fields_keep_public_term
    intro fieldId member
    obtain ⟨pair, pairMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp pairMember
    exact fresh i
  have rowProjection : store.applyTerm (.app function (fun i => .var (names i))) =
      .app function required :=
    private_constructor_projects function names required distinct requiredFresh
  have fieldProjection : ∀ i, store.applyTerm (.var (names i)) = required i := by
    have same := rowProjection
    simp only [Subst.applyTerm_app, Term.app.injEq, heq_eq_eq, true_and] at same
    exact fun i => congrFun same i
  rw [withStore_eq_resolved, withStore_eq_resolved]
  change resolved query fuel _ _ (observations.map store.applyTerm) = _
  rw [rowProjection]
  have pairs :
      ((List.finRange (σ.functionArity function)).map
        (fun i => (subjects i, Term.var (names i)))).map
          (fun pair => (store.applyTerm pair.1, store.applyTerm pair.2)) =
      (List.finRange (σ.functionArity function)).map
        (fun i => (subjects i, required i)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, fieldProjection,
      keepsPublic (subjects i) (fun j => subjectsFresh j i)]
  have visible : observations.map store.applyTerm = observations := by
    calc
      observations.map store.applyTerm = observations.map id := by
        apply List.map_congr_left
        intro term member
        exact keepsPublic term (observationsFresh term member)
      _ = observations := List.map_id observations
  rw [pairs, visible]
  have identity : (Subst.id σ).applyTerm = id := by
    funext term
    exact Subst.applyTerm_id term
  simp only [identity, id_eq, List.map_map, List.map_id, Function.comp_def]

/-- Starting from the actual constructor-unification call gives the same
ordered row results as using the incoming fields directly. The proof removes
only the fresh alias match; every child query and unification still runs. -/
theorem eliminate_initial_row_match (query : Query σ) (fuel : Nat)
    (function : σ.functionSymbols)
    (names : Fin (σ.functionArity function) → σ.vars)
    (subjects required : Fin (σ.functionArity function) → Term σ)
    (observations : List (Term σ))
    (distinct : Function.Injective names)
    (requiredFresh : ∀ i j, (required j).occursIn (names i) = false)
    (subjectsFresh : ∀ i j, (subjects j).occursIn (names i) = false)
    (observationsFresh : ∀ term ∈ observations, ∀ i,
      term.occursIn (names i) = false) :
    (unifyFuel (σ.functionArity function + 2)
      [(.app function (fun i => .var (names i)), .app function required)]).toList.flatMap
      (fun store => withStore query fuel
        ((List.finRange (σ.functionArity function)).map
          (fun i => (subjects i, .var (names i))))
        (.app function (fun i => .var (names i))) observations store) =
    withStore query fuel
      ((List.finRange (σ.functionArity function)).map
        (fun i => (subjects i, required i)))
      (.app function required) observations (Subst.id σ) := by
  rw [unify_private_constructor function names required distinct requiredFresh]
  simpa only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    using eliminate_private_row query fuel function names subjects required observations
      distinct requiredFresh subjectsFresh observationsFresh

end BoundRow

namespace Controls

open PrivateVariableControls

/-- Three declaration answers in the first position, including a duplicate;
other positions return their resolved subject as the matching candidate. -/
def sharedBranchQuery : BoundRow.Query rowSignature
  | .const 100, _ => [.const 6, .const 7, .const 6]
  | subject, _ => [subject]

/-- The first requirement shares a variable with the next subject. Resolving
that subject in each branch rejects the middle candidate while preserving
the two surviving equal answers and their caller binding. -/
theorem shared_subject_requirement_branching :
    BoundRow.withStore sharedBranchQuery 3
      [(.const 100, .var 4), (.var 4, .const 6)]
      (.app 2 (fun _ => .var 4)) [.var 4] (Subst.id rowSignature) =
      [(.app 2 (fun _ => .const 6), [.const 6]),
       (.app 2 (fun _ => .const 6), [.const 6])] := by
  rfl

/-- Treating the second subject as its original unbound variable would skip
its check and retain all three branches. That changes multiplicity. -/
theorem ignoring_shared_subject_refinement_changes_answers :
    (BoundRow.withStore sharedBranchQuery 3
      [(.const 100, .var 4), (.var 4, .const 6)]
      (.app 2 (fun _ => .var 4)) [.var 4] (Subst.id rowSignature)).length ≠ 3 := by
  rw [shared_subject_requirement_branching]
  decide


/-- Adding a second classifier answer repeats the consuming body. Even
identical public states are two ordered occurrences. -/
theorem authored_alternative_prevents_erasure :
    run (guard (fun state : Nat => [state, state])
      (.effect (fun state world => (state, world + 1)) .done)) 0 0 = ([0, 0], 2) := rfl

theorem duplicated_guard_differs_from_erasure :
    run (guard (fun state : Nat => [state, state])
      (.effect (fun state world => (state, world + 1)) .done)) 0 0 ≠
    run (.effect (fun state : Nat => fun world : Nat => (state, world + 1)) .done) 0 0 := by
  decide

end Controls
end Mettapedia.Languages.MeTTa.PeTTa.VariableTypeGuard
