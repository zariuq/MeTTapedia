import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mettapedia.GSLT.Core.BoundedSelection
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Flatten
import Mathlib.Logic.Relation

/-!
# Weighted branching coalgebras as free resumptions

A transition either returns an answer or exposes an ordered finite family of
successor occurrences and coefficients. The operation response is its physical
list position, not the value of the successor. Equal successors therefore do
not become one alternative.

The free unfolding and the direct weighted frontier recursion are independent
algorithms. Their comparison theorem preserves both returned answers and open
states. Its resumption law keeps the accumulated coefficient in execution order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.WeightedBranchingResumption

open ResumptionAlgebra WeightedResumption

universe uState uAnswer uValue

variable {State : Type uState} {Answer : Type uAnswer} {V : Type uValue}

abbrev Operation (State : Type uState) (V : Type uValue) := List (State × V)
abbrev Response (alternatives : Operation State V) := Fin alternatives.length
abbrev Coalgebra (State : Type uState) (Answer : Type uAnswer) (V : Type uValue) :=
  State → Answer ⊕ Operation State V

/-- Every physical response occurs once, even if states or coefficients repeat. -/
def catalogue (alternatives : Operation State V) :
    Contributions (Response alternatives) V :=
  List.ofFn fun index => (index, alternatives[index].2)

def observe (source : Coalgebra State Answer V) (state : State) :
    View (Operation State V) Response Answer State :=
  match source state with
  | .inl answer => .returned answer
  | .inr alternatives => .request alternatives (fun index => alternatives[index].1)

def cut (source : Coalgebra State Answer V) (fuel : Nat) (state : State) :
    Computation (Operation State V) Response (Answer ⊕ State) :=
  unfold (observe source) fuel state

/-- Execute the weighted frontier directly, without constructing a free tree. -/
def contributions [Monoid V] (source : Coalgebra State Answer V) :
    Nat → State → Contributions (Answer ⊕ State) V
  | 0, state => [(.inr state, 1)]
  | fuel + 1, state =>
      match source state with
      | .inl answer => [(.inl answer, 1)]
      | .inr alternatives => sequence alternatives (contributions source fuel)

/-- A coefficient-preserving one-step comparison transports the entire
finite execution, including duplicate occurrences and suspended states. -/
theorem contributions_reindex [Monoid V] {OtherState OtherAnswer : Type*}
    (source : Coalgebra State Answer V)
    (target : Coalgebra OtherState OtherAnswer V)
    (stateMap : State → OtherState) (answerMap : Answer → OtherAnswer)
    (comparison : ∀ state, target (stateMap state) =
      match source state with
      | .inl answer => .inl (answerMap answer)
      | .inr alternatives =>
          .inr (alternatives.map fun next => (stateMap next.1, next.2)))
    (fuel : Nat) (state : State) :
    contributions target fuel (stateMap state) =
      (contributions source fuel state).map fun leaf =>
        (Sum.map answerMap stateMap leaf.1, leaf.2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [contributions, comparison]
      cases inspected : source state with
      | inl answer => rfl
      | inr alternatives =>
          simp only [WeightedResumption.sequence, List.flatMap_map, List.map_flatMap]
          apply List.flatMap_congr
          intro next member
          rw [ih]
          simp only [List.map_map]
          rfl

/-- A declared coefficient-admission policy filters candidate occurrences
before their continuations execute. It preserves the source order and does not
merge equal states or coefficients. This is distinct from recording a zero
coefficient and filtering completed answers after their bodies have run. -/
def admittingSource (source : Coalgebra State Answer V) (admit : V → Bool) :
    Coalgebra State Answer V :=
  fun state => match source state with
    | .inl answer => .inl answer
    | .inr alternatives => .inr (alternatives.filter fun next => admit next.2)

@[simp] theorem admittingSource_true (source : Coalgebra State Answer V) :
    admittingSource source (fun _ => true) = source := by
  funext state
  cases inspected : source state <;> simp [admittingSource, inspected]

theorem admittingSource_return_iff (source : Coalgebra State Answer V)
    (admit : V → Bool) (state : State) (answer : Answer) :
    admittingSource source admit state = .inl answer ↔ source state = .inl answer := by
  cases inspected : source state <;> simp [admittingSource, inspected]

/-- Membership is exactly original authorization together with the declared
admission test. An accepted duplicate occurrence is never deduplicated. -/
theorem admittingSource_successor_iff (source : Coalgebra State Answer V)
    (admit : V → Bool) (state : State) (next : State × V) :
    (∃ selected, admittingSource source admit state = .inr selected ∧ next ∈ selected) ↔
      ∃ original, source state = .inr original ∧ next ∈ original ∧
        admit next.2 = true := by
  cases inspected : source state <;> simp [admittingSource, inspected]

/-- A one-step sublist comparison preserves whole surviving contributions
at every finite budget, including order, multiplicity and residual state. -/
theorem contributions_sublist [Monoid V]
    (source selected : Coalgebra State Answer V)
    (comparison : ∀ state, match source state with
      | .inl answer => selected state = .inl answer
      | .inr alternatives => ∃ kept, selected state = .inr kept ∧ kept.Sublist alternatives) :
    ∀ (fuel : Nat) (state : State),
      List.Sublist (contributions selected fuel state)
        (contributions source fuel state)
  | 0, _ => .refl _
  | fuel + 1, state => by
      have compared := comparison state
      cases inspected : source state with
      | inl answer =>
          simp only [inspected] at compared
          simp only [contributions, inspected, compared]
          exact .refl _
      | inr alternatives =>
          simp only [inspected] at compared
          obtain ⟨kept, same, sublist⟩ := compared
          simp only [contributions, inspected, same]
          unfold WeightedResumption.sequence
          apply List.Sublist.trans
            (sublist.flatMap _)
          apply List.Sublist.flatMap_right
          intro next _
          exact (contributions_sublist source selected comparison fuel next.1).map _

/-- Admission can only remove complete contribution occurrences. It cannot
rewrite their coefficients or replace their retained worlds. -/
theorem admitting_contributions_sublist [Monoid V]
    (source : Coalgebra State Answer V) (admit : V → Bool)
    (fuel : Nat) (state : State) :
    List.Sublist (contributions (admittingSource source admit) fuel state)
      (contributions source fuel state) := by
  apply contributions_sublist source (admittingSource source admit) ?_ fuel state
  intro before
  cases inspected : source before with
  | inl answer => simp [admittingSource, inspected]
  | inr alternatives =>
      exact ⟨alternatives.filter (fun next => admit next.2),
        by simp [admittingSource, inspected], List.filter_sublist⟩

/-- Enable coefficient filtering only at a declared observation boundary.
An unselected administrative transition retains its source authorization. -/
def admittingSourceAt (source : Coalgebra State Answer V)
    (boundary : State → Bool) (admit : V → Bool) : Coalgebra State Answer V :=
  fun state => if boundary state then admittingSource source admit state else source state

theorem admittingAt_contributions_sublist [Monoid V]
    (source : Coalgebra State Answer V) (boundary : State → Bool) (admit : V → Bool)
    (fuel : Nat) (state : State) :
    List.Sublist (contributions (admittingSourceAt source boundary admit) fuel state)
      (contributions source fuel state) := by
  apply contributions_sublist source (admittingSourceAt source boundary admit) ?_ fuel state
  intro before
  cases selected : boundary before <;> cases inspected : source before <;>
    simp only [admittingSourceAt, selected, Bool.false_eq_true, ↓reduceIte,
      admittingSource, inspected]
  · exact ⟨_, rfl, .refl _⟩
  · exact ⟨_, rfl, List.filter_sublist⟩

theorem catalogue_length (alternatives : Operation State V) :
    (catalogue alternatives).length = alternatives.length := by simp [catalogue]

/-- Position-indexed response handling agrees with an ordinary list traversal. -/
theorem catalogue_sequence [Mul V] {Result : Type*}
    (alternatives : Operation State V) (next : State → Contributions Result V) :
    sequence (catalogue alternatives) (fun index => next alternatives[index].1) =
      sequence alternatives next := by
  unfold WeightedResumption.sequence catalogue
  simp only [List.flatMap_def, List.map_ofFn]
  change (List.ofFn (fun index : Fin alternatives.length =>
    (next alternatives[index].1).map
      (fun result => (result.1, alternatives[index].2 * result.2)))).flatten = _
  exact congrArg List.flatten (List.ofFn_getElem_eq_map alternatives
    (fun first => (next first.1).map fun result => (result.1, first.2 * result.2)))

/-- Actual handler interpretation equals the separately defined frontier run. -/
theorem interpret_cut [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (state : State) :
    interpret catalogue (cut source fuel state) = contributions source fuel state := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      simp only [cut, unfold, observe, contributions]
      cases inspected : source state with
      | inl answer => rfl
      | inr alternatives =>
          change sequence (catalogue alternatives)
            (fun index => interpret catalogue (cut source fuel alternatives[index].1)) =
            sequence alternatives (contributions source fuel)
          simp only [ih]
          exact catalogue_sequence alternatives _

theorem cut_add (source : Coalgebra State Answer V)
    (first second : Nat) (state : State) :
    cut source (first + second) state =
      bind (cut source first state) (resume (observe source) second) :=
  unfold_add _ _ _ _

/-- A second slice interprets each retained state without losing earlier weights. -/
theorem contributions_add [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (state : State) :
    contributions source (first + second) state =
      sequence (contributions source first state)
        (fun leaf => match leaf with
          | .inl answer => [(.inl answer, 1)]
          | .inr pending => contributions source second pending) := by
  rw [← interpret_cut, cut_add, interpret_bind, interpret_cut]
  apply congrArg (sequence (contributions source first state))
  funext leaf
  cases leaf with
  | inl answer => rfl
  | inr pending => exact interpret_cut source second pending

/-- Returned contributions retain their coefficients and producing answers.
A budget-cut state is not an answer. -/
def returnedContributions (leaves : Contributions (Answer ⊕ State) V) :
    Contributions Answer V :=
  leaves.filterMap fun leaf => match leaf.1 with
    | .inl answer => some (answer, leaf.2)
    | .inr _ => none

/-- Continuing a finite cut can add answers, but never removes, reorders or
reweights those already returned. Returned answers take no further source
instruction; only cut states are passed to the source again. -/
theorem returned_sublist_continue [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (leaves : Contributions (Answer ⊕ State) V) :
    (returnedContributions leaves).Sublist
      (returnedContributions (sequence leaves fun leaf => match leaf with
        | .inl answer => [(.inl answer, 1)]
        | .inr pending => contributions source fuel pending)) := by
  induction leaves with
  | nil => exact List.Sublist.refl []
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl answer =>
          simpa only [returnedContributions, List.filterMap_cons, sequence_cons,
            List.map_cons, List.map_nil, mul_one, List.singleton_append,
            List.filterMap_cons] using List.Sublist.cons_cons (answer, value) ih
      | inr pending =>
          simpa only [returnedContributions, List.filterMap_cons, sequence_cons,
            List.filterMap_append] using List.sublist_append_of_sublist_right ih

/-- A cut with only returned leaves takes no more source instructions. This
includes parked grade results: not polling them leaves their work unchanged,
but does not turn them into completed body answers. -/
theorem continue_without_pending [Monoid V] (source : Coalgebra State Answer V)
    (fuel : Nat) (leaves : Contributions (Answer ⊕ State) V)
    (returned : leaves.all (fun leaf => leaf.1.isLeft) = true) :
    sequence leaves (fun leaf => match leaf with
      | .inl answer => [(.inl answer, 1)]
      | .inr pending => contributions source fuel pending) = leaves := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl answer =>
          have restReturned : rest.all (fun leaf => leaf.1.isLeft) = true := by
            simpa using returned
          simp only [sequence_cons, List.map_cons, List.map_nil, mul_one,
            List.singleton_append, ih restReturned]
      | inr pending => simp at returned

/-- The source's independent finite-cut algorithm has the same preservation
law. This includes parked results when they inhabit the returned-answer type. -/
theorem returned_sublist_add [Monoid V] (source : Coalgebra State Answer V)
    (first second : Nat) (initial : State) :
    (returnedContributions (contributions source first initial)).Sublist
      (returnedContributions (contributions source (first + second) initial)) := by
  rw [contributions_add]
  exact returned_sublist_continue source second _

/-- An invariant of actual successor occurrences survives the handler's
ordered multiplication, including zero or cancelling coefficients. Returned
and suspended leaves keep their different obligations. -/
theorem contributions_invariant [Monoid V] (source : Coalgebra State Answer V)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (returns : ∀ state answer, stateValid state → source state = .inl answer → answerValid answer)
    (successors : ∀ state alternatives, stateValid state → source state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1) :
    ∀ (fuel : Nat) (state : State), stateValid state →
      ∀ leaf ∈ contributions source fuel state,
        Sum.elim answerValid stateValid leaf.1
  | 0, state, valid, leaf, member => by
      simp only [contributions, List.mem_singleton] at member
      subst leaf
      exact valid
  | fuel + 1, state, valid, leaf, member => by
      cases inspected : source state with
      | inl answer =>
          simp only [contributions, inspected, List.mem_singleton] at member
          subst leaf
          exact returns state answer valid inspected
      | inr alternatives =>
          simp only [contributions, inspected, WeightedResumption.sequence, List.mem_flatMap] at member
          obtain ⟨next, nextMember, leafMember⟩ := member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp leafMember
          have inherited := contributions_invariant source stateValid answerValid returns
            successors fuel next.1 (successors state alternatives valid inspected next nextMember)
            child childMember
          cases same
          exact inherited

/-- A nondecreasing meter charged at most once per source quantum bounds
returned and suspended leaves alike. Coefficients do not reset the meter. -/
theorem contributions_meter_bounds [Monoid V] (source : Coalgebra State Answer V)
    (stateMeter : State → Nat) (answerMeter : Answer → Nat)
    (returns : ∀ state answer, source state = .inl answer → answerMeter answer = stateMeter state)
    (successors : ∀ state alternatives, source state = .inr alternatives →
      ∀ next ∈ alternatives,
        stateMeter state ≤ stateMeter next.1 ∧ stateMeter next.1 ≤ stateMeter state + 1) :
    ∀ (fuel : Nat) (state : State) (leaf : (Answer ⊕ State) × V),
      leaf ∈ contributions source fuel state →
        stateMeter state ≤ Sum.elim answerMeter stateMeter leaf.1 ∧
        Sum.elim answerMeter stateMeter leaf.1 ≤ stateMeter state + fuel
  | 0, state, leaf, member => by
      simp only [contributions, List.mem_singleton] at member
      subst leaf
      exact ⟨le_rfl, by simp⟩
  | fuel + 1, state, leaf, member => by
      cases inspected : source state with
      | inl answer =>
          simp only [contributions, inspected, List.mem_singleton] at member
          subst leaf
          change stateMeter state ≤ answerMeter answer ∧
            answerMeter answer ≤ stateMeter state + (fuel + 1)
          rw [returns state answer inspected]
          exact ⟨le_rfl, Nat.le_add_right _ _⟩
      | inr alternatives =>
          simp only [contributions, inspected, WeightedResumption.sequence, List.mem_flatMap] at member
          obtain ⟨next, nextMember, leafMember⟩ := member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp leafMember
          have stepBound := successors state alternatives inspected next nextMember
          have childBound := contributions_meter_bounds source stateMeter answerMeter returns
            successors fuel next.1 child childMember
          cases same
          exact ⟨stepBound.1.trans childBound.1,
            childBound.2.trans (by omega)⟩

/-- Every finite path of actual successor occurrences ending in a return is
present in a sufficiently deep cut. Coefficients remain contributions even
when their product is zero; this is not a nonzero-support theorem. -/
theorem contributions_return_of_reachable [Monoid V]
    (source : Coalgebra State Answer V) (step : State → State → Prop)
    (admitted : ∀ before after, step before after →
      ∃ alternatives value, source before = .inr alternatives ∧
        (after, value) ∈ alternatives)
    {before after : State} (reachable : Relation.ReflTransGen step before after)
    (answer : Answer) (returned : source after = .inl answer) :
    ∃ fuel value, (.inl answer, value) ∈ contributions source fuel before := by
  induction reachable using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨1, 1, by simp [contributions, returned]⟩
  | @head before next edge _ ih =>
      obtain ⟨fuel, value, present⟩ := ih
      obtain ⟨alternatives, factor, inspected, member⟩ := admitted before next edge
      refine ⟨fuel + 1, factor * value, ?_⟩
      simp only [contributions, inspected, WeightedResumption.sequence, List.mem_flatMap]
      exact ⟨(next, factor), member, List.mem_map.mpr ⟨(.inl answer, value), present, rfl⟩⟩

/-- Open leaves are not answered leaves, even if the observation budget is zero. -/
theorem zero_cut_retains_state [Monoid V] (source : Coalgebra State Answer V)
    (state : State) : contributions source 0 state = [(.inr state, 1)] := rfl

section PendingCoefficients

variable {Job Grade : Type*}

/-- An admitted successor is retained while its coefficient is computed.
The body has no instruction to execute until that computation returns. -/
abbrev PendingState (State Job : Type*) := State ⊕ (State × Job)

/-- A coefficient result outside the declared algebra retains the authorized
body and the actual result. It is distinct from a completed body answer. -/
abbrev PendingAnswer (State Answer Grade : Type*) := Answer ⊕ (State × Grade)

def pendingBody : PendingState State Job → State := Sum.elim id Prod.fst

/-- Compose actual body and coefficient computations through the existing
weighted handler. Administrative steps have unit coefficient. A settled
coefficient is multiplied once, when its retained body becomes executable. -/
def pendingSource [One V] (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Job → Grade ⊕ List Job) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) :
    Coalgebra (PendingState State Job) (PendingAnswer State Answer Grade) V
  | .inl state =>
      match body state with
      | .inl answer => .inl (.inl answer)
      | .inr alternatives =>
          .inr (alternatives.map fun next => match next.2 with
            | .inl value => (.inl next.1, value)
            | .inr job => (.inr (next.1, job), 1))
  | .inr (state, job) =>
      match grade job with
      | .inl result =>
          match readout result with
          | some value => .inr [(.inl (resumeBody state result), value)]
          | none => .inl (.inr (state, result))
      | .inr alternatives =>
          .inr (alternatives.map fun next => (.inr (state, next), 1))

/-- Nested coefficient work retains the body and every suspended parent
coefficient continuation. Forcing graded work while computing a coefficient
therefore does not move its contribution outside the weighted account. -/
abbrev NestedPendingState (State Job : Type*) := State ⊕ (State × Job × List Job)

/-- Uninterpreted nested results retain the whole continuation stack. -/
abbrev NestedPendingAnswer (State Answer Job Grade : Type*) :=
  Answer ⊕ (State × Grade × List Job)

/-- Body and coefficient admissions share the same weighted handler. A new
coefficient suspends its parent; its result resumes that exact continuation
and contributes its coefficient once, before the parent can execute again. -/
def nestedPendingSource [One V] (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job) :
    Coalgebra (NestedPendingState State Job)
      (NestedPendingAnswer State Answer Job Grade) V
  | .inl state =>
      match body state with
      | .inl answer => .inl (.inl answer)
      | .inr alternatives =>
          .inr (alternatives.map fun next => match next.2 with
            | .inl value => (.inl next.1, value)
            | .inr job => (.inr (next.1, job, []), 1))
  | .inr (state, job, parents) =>
      match grade job with
      | .inl result =>
          match readout result with
          | none => .inl (.inr (state, result, parents))
          | some value =>
              match parents with
              | [] => .inr [(.inl (resumeBody state result), value)]
              | parent :: rest =>
                  .inr [(.inr (state, resumeGrade parent result, rest), value)]
      | .inr alternatives =>
          .inr (alternatives.map fun next => match next.2 with
            | .inl value => (.inr (state, next.1, parents), value)
            | .inr child => (.inr (state, child, next.1 :: parents), 1))

/-- Completed body contributions retain their values, physical multiplicity
and accumulated factors. A returned but uninterpreted grade is excluded. -/
def nestedAnswers {Answer Parked Pending : Type*}
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    Contributions Answer V :=
  leaves.filterMap fun leaf => match leaf.1 with
    | .inl (.inl answer) => some (answer, leaf.2)
    | _ => none

/-- Outstanding contributions retain their original order and coefficient.
A parked result owns its body and parent stack; a pending state owns the
instructions which may be resumed. Neither is an emitted body answer. -/
def nestedObligations {Answer Parked Pending : Type*}
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    Contributions (Parked ⊕ Pending) V :=
  leaves.filterMap fun leaf => match leaf.1 with
    | .inl (.inl _) => none
    | .inl (.inr parked) => some (.inl parked, leaf.2)
    | .inr pending => some (.inr pending, leaf.2)

/-- Parked returns are not runnable instructions. Their complete result and
continuations remain in the residual until a declared interpretation changes. -/
def parkedGrades {Parked Pending : Type*}
    (obligations : Contributions (Parked ⊕ Pending) V) : Contributions Parked V :=
  obligations.filterMap fun leaf => match leaf.1 with
    | .inl parked => some (parked, leaf.2)
    | .inr _ => none

def pendingInstructions {Parked Pending : Type*}
    (obligations : Contributions (Parked ⊕ Pending) V) : Contributions Pending V :=
  obligations.filterMap fun leaf => match leaf.1 with
    | .inl _ => none
    | .inr pending => some (pending, leaf.2)

/-- Every occurrence is either a completed body or an outstanding obligation;
this census does not inspect, normalize or sum semantic coefficients. -/
theorem nested_answers_obligations_count {State Answer Job Grade : Type*}
    (leaves : Contributions
      (NestedPendingAnswer State Answer Job Grade ⊕ NestedPendingState State Job) V) :
    (nestedAnswers leaves).length + (nestedObligations leaves).length = leaves.length := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl result => cases result <;> simp [nestedAnswers, nestedObligations] at * <;> omega
      | inr pending => simp [nestedAnswers, nestedObligations] at *; omega

theorem parked_pending_count {State Job Grade : Type*}
    (obligations : Contributions ((State × Grade × List Job) ⊕
      NestedPendingState State Job) V) :
    (parkedGrades obligations).length + (pendingInstructions obligations).length =
      obligations.length := by
  induction obligations with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf <;> simp [parkedGrades, pendingInstructions] at * <;> omega

/-- The parked census is a declared readout of the actual returned grade
occurrences, rather than a second execution algorithm. -/
theorem parked_grades_returned_view {State Answer Job Grade : Type*}
    (leaves : Contributions
      (NestedPendingAnswer State Answer Job Grade ⊕ NestedPendingState State Job) V) :
    parkedGrades (nestedObligations leaves) =
      (returnedContributions leaves).filterMap (fun leaf => match leaf.1 with
        | .inl _ => none
        | .inr parked => some (parked, leaf.2)) := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl result => cases result <;>
          simpa [parkedGrades, nestedObligations, returnedContributions] using ih
      | inr pending =>
          simpa [parkedGrades, nestedObligations, returnedContributions] using ih

/-- Resuming a cut retains each already parked grade with the same body,
result, parent frames and accumulated coefficient. New pending work may add
other parked occurrences; equality of values never merges either occurrence. -/
theorem nested_parked_sublist_add [Monoid V] {Job Grade : Type*}
    (source : Coalgebra (NestedPendingState State Job)
      (NestedPendingAnswer State Answer Job Grade) V)
    (first second : Nat) (initial : NestedPendingState State Job) :
    (parkedGrades (nestedObligations (contributions source first initial))).Sublist
      (parkedGrades (nestedObligations (contributions source (first + second) initial))) := by
  rw [parked_grades_returned_view, parked_grades_returned_view]
  exact (returned_sublist_add source first second initial).filterMap _

/-- Empty runnable work proves closure only when the parked residual is also
empty. This tests the whole obligation census, independently of priorities. -/
theorem obligations_empty_iff {State Job Grade : Type*}
    (obligations : Contributions ((State × Grade × List Job) ⊕
      NestedPendingState State Job) V) :
    obligations = [] ↔
      parkedGrades obligations = [] ∧ pendingInstructions obligations = [] := by
  have counts := parked_pending_count obligations
  constructor
  · intro empty; subst obligations; exact ⟨rfl, rfl⟩
  · rintro ⟨parked, pending⟩
    rw [parked, pending] at counts
    have emptyLength : obligations.length = 0 := by simpa using counts.symm
    exact List.length_eq_zero_iff.mp emptyLength

/-- Count only the completed answers selected by the declared observation.
Zero coefficients and repeated equal answers remain occurrences. Other
completed returns are still available in `nestedAnswers`. -/
def nestedSelected {Answer Parked Pending Selected : Type*}
    (select : Answer → Option Selected)
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    Contributions Selected V :=
  (nestedAnswers leaves).filterMap fun leaf =>
    (select leaf.1).map fun selected => (selected, leaf.2)

/-- Use the common three-outcome contract. The closure bit includes parked
results, whereas the requested count uses the declared completed readout. -/
def nestedSelectionOutcome {Answer Parked Pending Selected : Type*}
    (select : Answer → Option Selected) (requested : Nat)
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    Mettapedia.GSLT.Core.BoundedSelection.SelectOutcome :=
  Mettapedia.GSLT.Core.BoundedSelection.outcomeFromCounts requested
    (nestedSelected select leaves).length (nestedObligations leaves).isEmpty

theorem nested_selection_established_iff {State Answer Job Grade Selected : Type*}
    (select : Answer → Option Selected) (requested : Nat)
    (leaves : Contributions
      (NestedPendingAnswer State Answer Job Grade ⊕ NestedPendingState State Job) V) :
    nestedSelectionOutcome select requested leaves = .established ↔
      requested ≤ (nestedSelected select leaves).length :=
  Mettapedia.GSLT.Core.BoundedSelection.outcomeFromCounts_established_iff _ _ _

theorem nested_selection_saturated_iff {State Answer Job Grade Selected : Type*}
    (select : Answer → Option Selected) (requested : Nat)
    (leaves : Contributions
      (NestedPendingAnswer State Answer Job Grade ⊕ NestedPendingState State Job) V) :
    nestedSelectionOutcome select requested leaves = .saturated ↔
      (nestedSelected select leaves).length < requested ∧
        parkedGrades (nestedObligations leaves) = [] ∧
        pendingInstructions (nestedObligations leaves) = [] := by
  rw [nestedSelectionOutcome,
    Mettapedia.GSLT.Core.BoundedSelection.outcomeFromCounts_saturated_iff]
  simp only [List.isEmpty_iff, obligations_empty_iff]

theorem nested_selection_incomplete_iff {State Answer Job Grade Selected : Type*}
    (select : Answer → Option Selected) (requested : Nat)
    (leaves : Contributions
      (NestedPendingAnswer State Answer Job Grade ⊕ NestedPendingState State Job) V) :
    nestedSelectionOutcome select requested leaves = .incomplete ↔
      (nestedSelected select leaves).length < requested ∧
        (parkedGrades (nestedObligations leaves) ≠ [] ∨
          pendingInstructions (nestedObligations leaves) ≠ []) := by
  rw [nestedSelectionOutcome,
    Mettapedia.GSLT.Core.BoundedSelection.outcomeFromCounts_incomplete_iff]
  simp only [List.isEmpty_eq_false_iff, ne_eq, obligations_empty_iff, not_and_or]

/-- All suspended frames remain in the owned account while their child runs. -/
def nestedStateMeter (stateMeter : State → Nat) (jobMeter : Job → Nat) :
    NestedPendingState State Job → Nat
  | .inl state => stateMeter state
  | .inr (state, job, parents) =>
      stateMeter state + jobMeter job + (parents.map jobMeter).sum

def nestedAnswerMeter (answerMeter : Answer → Nat) (stateMeter : State → Nat)
    (gradeMeter : Grade → Nat) (jobMeter : Job → Nat) :
    NestedPendingAnswer State Answer Job Grade → Nat
  | .inl answer => answerMeter answer
  | .inr (state, result, parents) =>
      stateMeter state + gradeMeter result + (parents.map jobMeter).sum

/-- Child work is transferred once into its caller when it returns. Starting
a fresh child is free in this instruction metric; both actual instruction
sources charge one unit. The theorem keeps those metric assumptions explicit. -/
theorem nested_contributions_meter_bounds [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Coalgebra Job Grade (V ⊕ Job))
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (resumeGrade : Job → Grade → Job)
    (stateMeter : State → Nat) (answerMeter : Answer → Nat)
    (jobMeter : Job → Nat) (gradeMeter : Grade → Nat)
    (bodyReturns : ∀ state answer, body state = .inl answer →
      answerMeter answer = stateMeter state)
    (bodySteps : ∀ state alternatives, body state = .inr alternatives →
      ∀ next ∈ alternatives, stateMeter next.1 = stateMeter state + 1 ∧
        Sum.elim (fun _ => True) (fun child => jobMeter child = 0) next.2)
    (gradeReturns : ∀ job result, grade job = .inl result → gradeMeter result = jobMeter job)
    (gradeSteps : ∀ job alternatives, grade job = .inr alternatives →
      ∀ next ∈ alternatives, jobMeter next.1 = jobMeter job + 1 ∧
        Sum.elim (fun _ => True) (fun child => jobMeter child = 0) next.2)
    (bodyResumes : ∀ state result, stateMeter (resumeBody state result) =
      stateMeter state + gradeMeter result)
    (gradeResumes : ∀ parent result, jobMeter (resumeGrade parent result) =
      jobMeter parent + gradeMeter result)
    (fuel : Nat) (initial : NestedPendingState State Job) :
    ∀ leaf ∈ contributions (nestedPendingSource body grade readout resumeBody resumeGrade)
      fuel initial,
      nestedStateMeter stateMeter jobMeter initial ≤
        Sum.elim (nestedAnswerMeter answerMeter stateMeter gradeMeter jobMeter)
          (nestedStateMeter stateMeter jobMeter) leaf.1 ∧
      Sum.elim (nestedAnswerMeter answerMeter stateMeter gradeMeter jobMeter)
          (nestedStateMeter stateMeter jobMeter) leaf.1 ≤
        nestedStateMeter stateMeter jobMeter initial + fuel := by
  apply contributions_meter_bounds (nestedPendingSource body grade readout resumeBody resumeGrade)
    (nestedStateMeter stateMeter jobMeter)
    (nestedAnswerMeter answerMeter stateMeter gradeMeter jobMeter) ?_ ?_ fuel initial
  · intro pending answer returned
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result =>
            simp only [nestedPendingSource, inspected, Sum.inl.injEq] at returned
            subst answer
            exact bodyReturns state result inspected
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        cases inspected : grade job with
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
        | inl result =>
            cases decoded : readout result with
            | some value =>
                cases parents <;> simp [nestedPendingSource, inspected, decoded] at returned
            | none =>
                simp only [nestedPendingSource, inspected, decoded, Sum.inl.injEq] at returned
                subst answer
                simp only [nestedAnswerMeter, nestedStateMeter, gradeReturns job result inspected]
  · intro pending alternatives requested next member
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result => simp [nestedPendingSource, inspected] at requested
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨spent, fresh⟩ := bodySteps state children inspected (child, coefficient) present
            cases coefficient with
            | inl value =>
                cases same
                simp only [nestedStateMeter, spent]
                exact ⟨Nat.le_add_right _ _, le_rfl⟩
            | inr job =>
                cases same
                change jobMeter job = 0 at fresh
                simp only [nestedStateMeter, spent, fresh, List.map_nil, List.sum_nil,
                  Nat.add_zero]
                exact ⟨Nat.le_add_right _ _, le_rfl⟩
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        cases inspected : grade job with
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨spent, fresh⟩ := gradeSteps job children inspected (child, coefficient) present
            cases coefficient with
            | inl value =>
                cases same
                simp only [nestedStateMeter, spent]
                omega
            | inr inner =>
                cases same
                change jobMeter inner = 0 at fresh
                simp only [nestedStateMeter, fresh, spent, List.map_cons, List.sum_cons,
                  Nat.add_zero]
                omega
        | inl result =>
            cases decoded : readout result with
            | none => simp [nestedPendingSource, inspected, decoded] at requested
            | some value =>
                have spent := gradeReturns job result inspected
                cases parents with
                | nil =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    simp only [nestedStateMeter, bodyResumes, spent, List.map_nil,
                      List.sum_nil, Nat.add_zero]
                    exact ⟨le_rfl, Nat.le_add_right _ _⟩
                | cons parent rest =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    have same := List.mem_singleton.mp member
                    subst next
                    simp only [nestedStateMeter, gradeResumes, spent, List.map_cons,
                      List.sum_cons]
                    omega

/-- A settled child contributes once and restores its retained parent.
Completion order never selects a different continuation. -/
theorem nested_coefficient_resumes_parent [One V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (state : State) (job parent : Job) (parents : List Job) (result : Grade) (value : V)
    (returned : grade job = .inl result) (decoded : readout result = some value) :
    nestedPendingSource body grade readout resumeBody resumeGrade
      (.inr (state, job, parent :: parents)) =
      .inr [(.inr (state, resumeGrade parent result, parents), value)] := by
  simp [nestedPendingSource, returned, decoded]

theorem nested_coefficient_resumes_body [One V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (state : State) (job : Job) (result : Grade) (value : V)
    (returned : grade job = .inl result) (decoded : readout result = some value) :
    nestedPendingSource body grade readout resumeBody resumeGrade
      (.inr (state, job, [])) = .inr [(.inl (resumeBody state result), value)] := by
  simp [nestedPendingSource, returned, decoded]

/-- An unknown interpretation cannot discard the original body or any
parent coefficient frame, and does not execute any of those continuations. -/
theorem nested_uninterpreted_retains_stack [One V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (state : State) (job : Job) (parents : List Job) (result : Grade)
    (returned : grade job = .inl result) (unknown : readout result = none) :
    nestedPendingSource body grade readout resumeBody resumeGrade
      (.inr (state, job, parents)) = .inl (.inr (state, result, parents)) := by
  simp [nestedPendingSource, returned, unknown]

def settledBody (body : Coalgebra State Answer V) : Coalgebra State Answer (V ⊕ Job) :=
  fun state => match body state with
    | .inl answer => .inl answer
    | .inr alternatives => .inr (alternatives.map fun next => (next.1, .inl next.2))

def settledLeaf (leaf : Answer ⊕ State) :
    PendingAnswer State Answer Grade ⊕ PendingState State Job :=
  Sum.map Sum.inl Sum.inl leaf

/-- The nested stack adds no administrative quantum when there is no
coefficient job. The independently executed original frontier is unchanged. -/
theorem nested_pending_settled_agrees [Monoid V] (body : Coalgebra State Answer V)
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (fuel : Nat) (state : State) :
    contributions (nestedPendingSource (settledBody body) grade readout resumeBody resumeGrade)
      fuel (.inl state) =
      (contributions body fuel state).map (fun leaf =>
        (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  apply contributions_reindex body
    (nestedPendingSource (settledBody body) grade readout resumeBody resumeGrade)
    Sum.inl Sum.inl ?_ fuel state
  intro before
  cases inspected : body before <;>
    simp [nestedPendingSource, settledBody, inspected, List.map_map]

/-- Settled annotations and admission share the original execution budget.
Admission is applied at the same candidate boundary in both algorithms;
neither version starts a coefficient job. -/
theorem admitting_nested_pending_settled_agrees [Monoid V]
    (body : Coalgebra State Answer V) (grade : Coalgebra Job Grade (V ⊕ Job))
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (resumeGrade : Job → Grade → Job) (admit : V → Bool)
    (fuel : Nat) (state : State) :
    contributions
        (admittingSource
          (nestedPendingSource (settledBody body) grade readout resumeBody resumeGrade) admit)
        fuel (.inl state) =
      (contributions (admittingSource body admit) fuel state).map
        (fun leaf => (Sum.map Sum.inl Sum.inl leaf.1, leaf.2)) := by
  apply contributions_reindex (admittingSource body admit)
    (admittingSource
      (nestedPendingSource (settledBody body) grade readout resumeBody resumeGrade) admit)
    Sum.inl Sum.inl ?_ fuel state
  intro before
  cases inspected : body before <;>
    simp [admittingSource, nestedPendingSource, settledBody, inspected,
      List.filter_map, List.map_map, Function.comp_def]

/-- Settled one-level annotations use the same admission boundary. -/
theorem admitting_pending_settled_agrees [Monoid V] (body : Coalgebra State Answer V)
    (grade : Job → Grade ⊕ List Job) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (admit : V → Bool)
    (fuel : Nat) (state : State) :
    contributions
        (admittingSource (pendingSource (settledBody body) grade readout resumeBody) admit)
        fuel (.inl state) =
      (contributions (admittingSource body admit) fuel state).map
        (fun leaf => (settledLeaf leaf.1, leaf.2)) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases inspected : body state with
      | inl answer =>
          simp [contributions, admittingSource, pendingSource, settledBody, inspected, settledLeaf]
      | inr alternatives =>
          simp only [contributions, admittingSource, pendingSource, settledBody, inspected,
            WeightedResumption.sequence, List.filter_map, List.map_map,
            List.flatMap_map, List.map_flatMap]
          apply List.flatMap_congr
          intro next member
          dsimp only [Function.comp_apply]
          rw [ih]
          simp only [List.map_map]
          apply List.map_congr_left
          intro child present
          rfl

/-- Programs with settled coefficients use exactly the original frontier and
budget. No coefficient job or extra execution quantum is introduced. -/
theorem pending_settled_agrees [Monoid V] (body : Coalgebra State Answer V)
    (grade : Job → Grade ⊕ List Job) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (fuel : Nat) (state : State) :
    contributions (pendingSource (settledBody body) grade readout resumeBody) fuel (.inl state) =
      (contributions body fuel state).map (fun leaf => (settledLeaf leaf.1, leaf.2)) := by
  simpa only [admittingSource_true] using
    admitting_pending_settled_agrees body grade readout resumeBody (fun _ => true) fuel state

/-- Validity of the authorized body survives coefficient execution, including
uninterpreted coefficient results. This uses the same invariant theorem as
settled weighted execution. -/
theorem pending_contributions_invariant [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Job → Grade ⊕ List Job)
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (returns : ∀ state answer, stateValid state → body state = .inl answer → answerValid answer)
    (successors : ∀ state alternatives, stateValid state → body state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1)
    (resumes : ∀ state result value, stateValid state → readout result = some value →
      stateValid (resumeBody state result))
    (fuel : Nat) (initial : PendingState State Job) (valid : stateValid (pendingBody initial)) :
    ∀ leaf ∈ contributions (pendingSource body grade readout resumeBody) fuel initial,
      Sum.elim (Sum.elim answerValid (fun result => stateValid result.1))
        (fun pending => stateValid (pendingBody pending)) leaf.1 := by
  apply contributions_invariant (pendingSource body grade readout resumeBody)
    (fun pending => stateValid (pendingBody pending))
    (Sum.elim answerValid (fun result => stateValid result.1))
    ?_ ?_ fuel initial valid
  · intro pending answer inherited returned
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result =>
            simp only [pendingSource, inspected, Sum.inl.injEq] at returned
            subst answer
            exact returns state result inherited inspected
        | inr alternatives => simp [pendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨state, job⟩
        cases inspected : grade job with
        | inr alternatives => simp [pendingSource, inspected] at returned
        | inl result =>
            cases decoded : readout result with
            | some value => simp [pendingSource, inspected, decoded] at returned
            | none =>
                simp only [pendingSource, inspected, decoded, Sum.inl.injEq] at returned
                subst answer
                exact inherited
  · intro pending alternatives inherited requested next member
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl answer => simp [pendingSource, inspected] at requested
        | inr children =>
            simp only [pendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            have childValid := successors state children inherited inspected
              (child, coefficient) present
            cases coefficient with
            | inl value => cases same; exact childValid
            | inr job => cases same; exact childValid
    | inr held =>
        rcases held with ⟨state, job⟩
        cases inspected : grade job with
        | inr children =>
            simp only [pendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨child, _, rfl⟩ := List.mem_map.mp member
            exact inherited
        | inl result =>
            cases decoded : readout result with
            | none => simp [pendingSource, inspected, decoded] at requested
            | some value =>
                simp only [pendingSource, inspected, decoded, Sum.inr.injEq] at requested
                subst alternatives
                have same := List.mem_singleton.mp member
                subst next
                exact resumes state result value inherited decoded

theorem pending_settled_once [Monoid V] (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Job → Grade ⊕ List Job) (readout : Grade → Option V)
    (resumeBody : State → Grade → State)
    (state : State) (job : Job) (result : Grade) (value : V)
    (returned : grade job = .inl result) (decoded : readout result = some value) :
    contributions (pendingSource body grade readout resumeBody) 1 (.inr (state, job)) =
      [(.inr (.inl (resumeBody state result)), value)] := by
  simp [contributions, pendingSource, returned, decoded, WeightedResumption.sequence]

theorem pending_uninterpreted_retains_body [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Job → Grade ⊕ List Job) (readout : Grade → Option V)
    (resumeBody : State → Grade → State)
    (state : State) (job : Job) (result : Grade)
    (returned : grade job = .inl result) (unknown : readout result = none) :
    contributions (pendingSource body grade readout resumeBody) 1 (.inr (state, job)) =
      [(.inl (.inr (state, result)), 1)] := by
  simp [contributions, pendingSource, returned, unknown]

/-- Coefficient computations with no returned result cannot produce any body
answer. Every remaining occurrence still owns the same authorized body. -/
theorem pending_nonreturning_retains_body [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Job → Grade ⊕ List Job)
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (nonreturning : ∀ job, ∃ children, grade job = .inr children)
    (state : State) (job : Job) (fuel : Nat) :
    ∀ leaf ∈ contributions (pendingSource body grade readout resumeBody) fuel (.inr (state, job)),
      ∃ next, leaf.1 = .inr (.inr (state, next)) := by
  have retained := contributions_invariant (pendingSource body grade readout resumeBody)
    (fun pending => match pending with
      | .inl _ => False
      | .inr held => held.1 = state)
    (fun _ => False) ?_ ?_ fuel (.inr (state, job)) rfl
  · intro leaf member
    have valid := retained leaf member
    cases leaf with
    | mk outcome value =>
        cases outcome with
        | inl answer => exact False.elim valid
        | inr pending =>
            cases pending with
            | inl bodyState => exact False.elim valid
            | inr held =>
                rcases held with ⟨bodyState, next⟩
                change bodyState = state at valid
                subst bodyState
                exact ⟨next, rfl⟩
  · intro pending answer valid returned
    cases pending with
    | inl bodyState => exact False.elim valid
    | inr held =>
        obtain ⟨children, inspected⟩ := nonreturning held.2
        simp [pendingSource, inspected] at returned
  · intro pending alternatives valid requested next member
    cases pending with
    | inl bodyState => exact False.elim valid
    | inr held =>
        obtain ⟨children, inspected⟩ := nonreturning held.2
        simp only [pendingSource, inspected, Sum.inr.injEq] at requested
        subst alternatives
        obtain ⟨child, _, rfl⟩ := List.mem_map.mp member
        exact valid

end PendingCoefficients

end Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
