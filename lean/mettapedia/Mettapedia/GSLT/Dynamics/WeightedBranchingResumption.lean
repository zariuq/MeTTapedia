import Mettapedia.GSLT.Dynamics.WeightedResumption
import Mettapedia.GSLT.Core.BoundedSelection
import Mettapedia.GSLT.Core.InferenceControl
import Mettapedia.GSLT.Core.WeightOrderedSelection
import Mettapedia.GSLT.Causality.OccurrenceMachineHistory
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.Group.Hom.Defs
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

/-- Every coefficient actually exposed by a source satisfies the given law.
Returned answers impose no coefficient obligation. This quantifies over the
source transitions, not merely over expressions scanned by an implementation. -/
def CoefficientsSatisfy (source : Coalgebra State Answer V) (holds : V → Prop) : Prop :=
  ∀ state alternatives, source state = .inr alternatives →
    ∀ next ∈ alternatives, holds next.2

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


/-- Restrict the state type to a proved invariant without filtering any
successor occurrence or changing its coefficient. The witnesses are erased
proofs, not a runtime search or an admission oracle. -/
def invariantSource (source : Coalgebra State Answer V)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (returns : ∀ state answer, stateValid state → source state = .inl answer → answerValid answer)
    (successors : ∀ state alternatives, stateValid state → source state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1) :
    Coalgebra {state // stateValid state} {answer // answerValid answer} V :=
  fun state => match inspected : source state.val with
    | .inl answer => .inl ⟨answer, returns state.val answer state.property inspected⟩
    | .inr alternatives => .inr (alternatives.attach.map fun next =>
        (⟨next.val.1, successors state.val alternatives state.property inspected
          next.val next.property⟩, next.val.2))

theorem invariantSource_forget (source : Coalgebra State Answer V)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (returns : ∀ state answer, stateValid state → source state = .inl answer → answerValid answer)
    (successors : ∀ state alternatives, stateValid state → source state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1)
    (state : {state // stateValid state}) :
    source state.val = match invariantSource source stateValid answerValid returns successors state with
      | .inl answer => .inl answer.val
      | .inr alternatives => .inr (alternatives.map fun next => (next.1.val, next.2)) := by
  unfold invariantSource
  split
  · rename_i answer captured
    split at captured
    · cases Sum.inl.inj captured
      assumption
    · contradiction
  · rename_i alternatives captured
    split at captured
    · contradiction
    · rename_i original actual
      cases Sum.inr.inj captured
      simp only [List.map_map]
      change source state.val = .inr (original.attach.map Subtype.val)
      rw [List.attach_map_subtype_val]
      assumption

/-- Forgetting invariant witnesses recovers all original bounded work,
including returned answers, suspended states, order and multiplicity. -/
theorem invariantSource_contributions [Monoid V] (source : Coalgebra State Answer V)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (returns : ∀ state answer, stateValid state → source state = .inl answer → answerValid answer)
    (successors : ∀ state alternatives, stateValid state → source state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1)
    (fuel : Nat) (state : {state // stateValid state}) :
    contributions source fuel state.val =
      (contributions (invariantSource source stateValid answerValid returns successors) fuel state).map
        (fun leaf => (Sum.map Subtype.val Subtype.val leaf.1, leaf.2)) :=
  contributions_reindex (invariantSource source stateValid answerValid returns successors) source
    (fun held : {state // stateValid state} => held.val)
    (fun held : {answer // answerValid answer} => held.val)
    (fun held => by
      have checked := invariantSource_forget source stateValid answerValid returns successors held
      cases inspected : invariantSource source stateValid answerValid returns successors held <;>
        simpa only [inspected] using checked)
    fuel state

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

/-- An actual pending occurrence can be continued without losing its prior
coefficient. The two factors retain their execution order, even when either
is zero. This is membership in the full contribution list, not its support. -/
theorem contributions_continue [Monoid V] (source : Coalgebra State Answer V)
    {first second : Nat} {before pending : State} {priorWeight : V}
    {leaf : (Answer ⊕ State) × V}
    (reached : (.inr pending, priorWeight) ∈ contributions source first before)
    (continued : leaf ∈ contributions source second pending) :
    (leaf.1, priorWeight * leaf.2) ∈ contributions source (first + second) before := by
  rw [contributions_add]
  exact List.mem_flatMap.mpr
    ⟨(.inr pending, priorWeight), reached, List.mem_map.mpr ⟨leaf, continued, rfl⟩⟩

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

/-! ## Global scheduling of weighted resumptions -/

namespace Scheduled

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

/-- The ordinary inference controller carries the accumulated coefficient
with each complete source state. It multiplies on the right at an actual
successor, retains every list occurrence, and never filters zero weights.
Source states may themselves retain occurrence paths and pending handlers. -/
def system [Mul V] (source : Coalgebra State Answer V) :
    BranchingSystem (State × V) (Answer × V) where
  emit node := match source node.1 with
    | .inl answer => some (answer, node.2)
    | .inr _ => none
  successors node := match source node.1 with
    | .inl _ => []
    | .inr alternatives =>
        alternatives.map fun next => (next.1, node.2 * next.2)

/-- The actual carried coefficient realizes a superior combination only when
that combination agrees with the source's multiplication. This supplies a
stopping licence for qualifying algebras, not for every weight family. -/
theorem system_realized [Mul V] [Preorder V] (source : Coalgebra State Answer V)
    (superior : WeightOrderedSelection.Superior V)
    (combines : ∀ left right, superior.combine left right = left * right) :
    WeightOrderedSelection.Realized (system source) superior Prod.snd where
  accumulated parent child member := by
    cases inspected : source parent.1 with
    | inl answer => simp [system, inspected] at member
    | inr alternatives =>
        simp only [system, inspected, List.mem_map] at member
        obtain ⟨next, _, equal⟩ := member
        subst child
        exact ⟨next.2, (combines parent.2 next.2).symm⟩

/-- A coefficient-domain law is lifted through the actual successor list and
right multiplication. The order used for stopping may differ from the
coefficient carrier's order, as for descending confidence products. -/
theorem system_stepBound [Mul V] {W : Type*} [Preorder W]
    (source : Coalgebra State Answer V) (weight : V → W) (domain : V → Prop)
    (steps : ∀ state alternatives, source state = .inr alternatives →
      ∀ next ∈ alternatives, ∀ incoming, domain incoming →
        domain (incoming * next.2) ∧ weight incoming ≤ weight (incoming * next.2)) :
    WeightOrderedSelection.StepBound (system source)
      (fun node => weight node.2) (fun node => domain node.2) := by
  have step : ∀ parent child, domain parent.2 → child ∈ (system source).successors parent →
      domain child.2 ∧ weight parent.2 ≤ weight child.2 := by
    intro parent child valid member
    cases inspected : source parent.1 with
    | inl answer => simp [system, inspected] at member
    | inr alternatives =>
        simp only [system, inspected, List.mem_map] at member
        obtain ⟨next, nextMember, equal⟩ := member
        subst child
        exact steps parent.1 alternatives inspected next nextMember parent.2 valid
  exact ⟨fun parent child valid member => (step parent child valid member).1,
    fun parent child valid member => (step parent child valid member).2⟩

/-- Unit-interval factors preserve descending bounds for every nonnegative
carried coefficient, including starting coefficients greater than one.
The coefficient carrier itself need not admit a superior multiplication. -/
theorem product_stepBound {R : Type*} [Semiring R] [PartialOrder R] [IsOrderedRing R]
    (source : Coalgebra State Answer R)
    (factors : CoefficientsSatisfy source (fun factor => 0 ≤ factor ∧ factor ≤ 1)) :
    WeightOrderedSelection.StepBound (system source)
      (fun node => OrderDual.toDual node.2) (fun node => 0 ≤ node.2) := by
  apply system_stepBound source OrderDual.toDual (fun value => 0 ≤ value)
  intro state alternatives inspected next member incoming nonnegative
  obtain ⟨factorNonnegative, factorBound⟩ := factors state alternatives inspected next member
  refine ⟨mul_nonneg nonnegative factorNonnegative, ?_⟩
  change incoming * next.2 ≤ incoming
  simpa only [mul_one] using mul_le_mul_of_nonneg_left factorBound nonnegative

/-- Nonnegative additive increments preserve ascending bounds even when the
starting value is signed. `Multiplicative` uses the existing weighted machine
with addition as its composition; this changes no successor occurrences. -/
theorem sum_stepBound {R : Type*} [AddCommMonoid R] [PartialOrder R]
    [IsOrderedAddMonoid R] (source : Coalgebra State Answer (Multiplicative R))
    (factors : CoefficientsSatisfy source (fun factor => 0 ≤ Multiplicative.toAdd factor)) :
    WeightOrderedSelection.StepBound (system source)
      (fun node => Multiplicative.toAdd node.2) (fun _ => True) := by
  apply system_stepBound source Multiplicative.toAdd (fun _ => True)
  intro state alternatives inspected next member incoming _
  refine ⟨True.intro, ?_⟩
  change Multiplicative.toAdd incoming ≤
    Multiplicative.toAdd incoming + Multiplicative.toAdd next.2
  exact le_add_of_nonneg_right (factors state alternatives inspected next member)

/-- Read a temporal snapshot through the existing contribution observations:
emitted results in emission order, followed by the complete live frontier in
agenda order. This readout forgets event origins; the full snapshot retains
them. It is not the depth-first ordering of a synchronous unfolding cut. -/
def observeSnapshot
    (snapshot : BranchingTemporal.Snapshot (State × V) (Answer × V)) :
    Contributions (Answer ⊕ State) V :=
  snapshot.events.map (fun event => (.inl event.value.1, event.value.2)) ++
    snapshot.frontier.map (fun node => (.inr node.1, node.2))

/-- The observation never drops a returned or pending occurrence. -/
theorem observed_length
    (snapshot : BranchingTemporal.Snapshot (State × V) (Answer × V)) :
    (observeSnapshot snapshot).length =
      snapshot.events.length + snapshot.frontier.length := by
  simp [observeSnapshot]

/-- A snapshot has no pending contribution exactly when its agenda is empty.
Returned parked obligations are still results of the source's answer type;
their classification belongs to the existing nested-result readout. -/
theorem observed_no_pending_iff
    (snapshot : BranchingTemporal.Snapshot (State × V) (Answer × V)) :
    (observeSnapshot snapshot).all (fun leaf => leaf.1.isLeft) = true ↔
      snapshot.frontier = [] := by
  cases frontier : snapshot.frontier <;>
    simp [observeSnapshot, frontier, List.all_map, Function.comp_def]

/-- A returned contribution is produced by a generated node; a pending
contribution is that generated node itself. The coefficient remains data. -/
def Authorized [Mul V] (source : Coalgebra State Answer V)
    (roots : List (State × V)) (leaf : (Answer ⊕ State) × V) : Prop :=
  match leaf.1 with
  | .inl answer => ∃ node, Generated (system source) roots node ∧
      (system source).emit node = some (answer, leaf.2)
  | .inr pending => Generated (system source) roots (pending, leaf.2)

/-- The independent depth-cut algorithm can be realized by the existing
global scheduler. A depth bound is not a count of selected scheduler nodes. -/
theorem contribution_authorized [Monoid V] (source : Coalgebra State Answer V)
    (roots : List (State × V)) :
    ∀ (depth : Nat) (before : State) (carried : V),
      Generated (system source) roots (before, carried) →
      ∀ leaf ∈ contributions source depth before,
        Authorized source roots (leaf.1, carried * leaf.2)
  | 0, before, carried, generated, leaf, member => by
      simp only [contributions, List.mem_singleton] at member
      subst leaf
      simpa only [Authorized, mul_one] using generated
  | depth + 1, before, carried, generated, leaf, member => by
      cases inspected : source before with
      | inl answer =>
          simp only [contributions, inspected, List.mem_singleton] at member
          subst leaf
          exact ⟨(before, carried), generated, by simp [system, inspected]⟩
      | inr alternatives =>
          simp only [contributions, inspected, WeightedResumption.sequence,
            List.mem_flatMap] at member
          obtain ⟨next, nextMember, leafMember⟩ := member
          obtain ⟨child, childMember, same⟩ := List.mem_map.mp leafMember
          cases same
          have childGenerated : Generated (system source) roots
              (next.1, carried * next.2) :=
            .successor generated (by
              simp only [system, inspected]
              exact List.mem_map.mpr ⟨next, nextMember, rfl⟩)
          simpa only [mul_assoc] using
            contribution_authorized source roots depth next.1
              (carried * next.2) childGenerated child childMember

/-- Every generated weighted state occurs in an independently computed cut.
There is no nonzero-support assumption and no cancellation of coefficients. -/
theorem generated_pending [Monoid V] (source : Coalgebra State Answer V)
    (initial : State) {node : State × V}
    (generated : Generated (system source) [(initial, 1)] node) :
    ∃ depth, (.inr node.1, node.2) ∈ contributions source depth initial := by
  induction generated with
  | @root found member =>
      simp only [List.mem_singleton] at member
      subst found
      exact ⟨0, by simp [contributions]⟩
  | @successor parent child _ member ih =>
      cases inspected : source parent.1 with
      | inl answer => simp [system, inspected] at member
      | inr alternatives =>
          simp only [system, inspected] at member
          obtain ⟨next, nextMember, same⟩ := List.mem_map.mp member
          subst child
          obtain ⟨depth, reached⟩ := ih
          refine ⟨depth + 1, ?_⟩
          apply contributions_continue source (second := 1)
            (leaf := (.inr next.1, next.2)) reached
          simp only [contributions, inspected, WeightedResumption.sequence,
            List.mem_flatMap]
          refine ⟨next, nextMember, ?_⟩
          simp

/-- Membership correspondence for the full weighted pending state. Source
occurrence identities, when present in `State`, are retained by both sides. -/
theorem generated_iff_pending [Monoid V] (source : Coalgebra State Answer V)
    (initial : State) (node : State × V) :
    Generated (system source) [(initial, 1)] node ↔
      ∃ depth, (.inr node.1, node.2) ∈ contributions source depth initial := by
  constructor
  · exact generated_pending source initial
  · rintro ⟨depth, member⟩
    have authorized := contribution_authorized source [(initial, 1)] depth initial 1
      (.root (by simp)) _ member
    simpa only [Authorized, one_mul] using authorized

/-- Emissions of the scheduled machine reflect to the actual weighted source
algorithm. Equality of answer values alone is not the premise. -/
theorem event_contribution [Monoid V] (source : Coalgebra State Answer V)
    (initial : State) {event : Emission (State × V) (Answer × V)}
    (valid : EventValid (system source) [(initial, 1)] event) :
    ∃ depth, (.inl event.value.1, event.value.2) ∈
      contributions source depth initial := by
  obtain ⟨generated, emitted⟩ := valid
  obtain ⟨depth, reached⟩ := generated_pending source initial generated
  cases inspected : source event.origin.1 with
  | inr alternatives => simp [system, inspected] at emitted
  | inl answer =>
      have same : (answer, event.origin.2) = event.value := by
        simpa only [system, inspected, Option.some.injEq] using emitted
      refine ⟨depth + 1, ?_⟩
      have continued := contributions_continue source reached
        (show (.inl answer, (1 : V)) ∈ contributions source 1 event.origin.1 by
          simp [contributions, inspected])
      simpa only [mul_one, ← same] using continued

/-- The existing controller's soundness now covers semantic coefficients and
the complete retained source state, under any lawful agenda. -/
theorem run_events_authorized [Monoid V] (source : Coalgebra State Answer V)
    {Memory : Type*} (controller : Controller (State × V) (Answer × V) Memory)
    (initial : State) (fuel : Nat) {event : Emission (State × V) (Answer × V)}
    (member : event ∈
      (InferenceControl.Snapshot.run (system source) controller fuel
        (InferenceControl.Snapshot.initial controller [(initial, 1)])).search.events) :
    ∃ depth, (.inl event.value.1, event.value.2) ∈
      contributions source depth initial := by
  apply event_contribution source initial
  exact (InferenceControl.Snapshot.sound_run (system source) controller
    (initial_sound (system source) [(initial, 1)]) fuel).2 event member

/-- The common contribution observation reflects both emitted results and
every remaining weighted state to the independent source semantics. -/
theorem observed_run_contribution [Monoid V] (source : Coalgebra State Answer V)
    {Memory : Type*} (controller : Controller (State × V) (Answer × V) Memory)
    (initial : State) (fuel : Nat) {leaf : (Answer ⊕ State) × V}
    (member : leaf ∈ observeSnapshot
      (InferenceControl.Snapshot.run (system source) controller fuel
        (InferenceControl.Snapshot.initial controller [(initial, 1)])).search) :
    ∃ depth, leaf ∈ contributions source depth initial := by
  rcases List.mem_append.mp member with emitted | pending
  · obtain ⟨event, present, same⟩ := List.mem_map.mp emitted
    subst leaf
    exact run_events_authorized source controller initial fuel present
  · obtain ⟨node, present, same⟩ := List.mem_map.mp pending
    subst leaf
    apply generated_pending source initial
    exact (InferenceControl.Snapshot.sound_run (system source) controller
      (initial_sound (system source) [(initial, 1)]) fuel).1 node present

/-- Completeness consumes fairness, unlike finite-run soundness. Even a zero
coefficient contribution is eventually emitted. The resulting scheduler
budget need not equal the independent unfolding depth. -/
theorem fair_emits_contribution [Monoid V] (source : Coalgebra State Answer V)
    {Memory : Type*} (controller : Controller (State × V) (Answer × V) Memory)
    (initial : State)
    (fair : InferenceControl.Snapshot.FairFrom (system source) controller [(initial, 1)])
    (depth : Nat) (answer : Answer) (value : V)
    (member : (.inl answer, value) ∈ contributions source depth initial) :
    ∃ fuel node, (⟨node, (answer, value)⟩ : Emission (State × V) (Answer × V)) ∈
      (InferenceControl.Snapshot.run (system source) controller fuel
        (InferenceControl.Snapshot.initial controller [(initial, 1)])).search.events := by
  have authorized := contribution_authorized source [(initial, 1)] depth initial 1
    (.root (by simp)) _ member
  simp only [Authorized, one_mul] at authorized
  obtain ⟨node, generated, emitted⟩ := authorized
  obtain ⟨fuel, present⟩ := InferenceControl.Snapshot.fair_emits_reachable
    (system source) controller [(initial, 1)] fair generated emitted
  exact ⟨fuel, node, present⟩

/-! Finite cuts can also be enumerated by a global agenda. A depth-zero
node emits a *pending* leaf of the cut, never a completed source answer.
Completing this enumeration therefore does not claim that the source closes. -/

def cutSystem [Mul V] (source : Coalgebra State Answer V) :
    BranchingSystem (Nat × State × V) ((Answer ⊕ State) × V) where
  emit node := match node.1 with
    | 0 => some (.inr node.2.1, node.2.2)
    | _ + 1 => match source node.2.1 with
        | .inl answer => some (.inl answer, node.2.2)
        | .inr _ => none
  successors node := match node.1 with
    | 0 => []
    | depth + 1 => match source node.2.1 with
        | .inl _ => []
        | .inr alternatives =>
            alternatives.map fun next => (depth, next.1, node.2.2 * next.2)

/-- An independently specified cut account: the earlier ordered frontier
algorithm, with the incoming coefficient prepended to each leaf. -/
def cutValue [Monoid V] (source : Coalgebra State Answer V)
    (node : Nat × State × V) : Multiset ((Answer ⊕ State) × V) :=
  ((contributions source node.1 node.2.1).map fun leaf =>
    (leaf.1, node.2.2 * leaf.2) : List ((Answer ⊕ State) × V))

/-- Local conservation follows from the independent frontier algorithm and
associativity. It requires neither addition nor commutative multiplication. -/
def cutDenotation [Monoid V] (source : Coalgebra State Answer V) :
    AdditiveDenotation (cutSystem source) where
  value := cutValue source
  unfold node := by
    rcases node with ⟨depth, state, carried⟩
    cases depth with
    | zero => simp [cutValue, contributions, cutSystem, optionBag, foldValues]
    | succ depth =>
        cases inspected : source state with
        | inl answer =>
            simp [cutValue, contributions, cutSystem, inspected, optionBag, foldValues]
        | inr alternatives =>
            simp only [cutValue, contributions, cutSystem, inspected, optionBag, zero_add]
            clear inspected
            induction alternatives with
            | nil => simp [WeightedResumption.sequence, foldValues]
            | cons next rest ih =>
                simpa [WeightedResumption.sequence, foldValues, cutValue,
                  List.map_flatMap, List.map_map, Function.comp_def, mul_assoc] using
                  congrArg (fun tail =>
                    (cutValue source (depth, next.1, carried * next.2)) + tail) ih

/-- Exact selected-node count for enumerating the cut. This counts source
inspections and pending cut leaves, not native firings or host CPU work. -/
def cutWork (source : Coalgebra State Answer V) : Nat → State → Nat
  | 0, _ => 1
  | depth + 1, state => match source state with
      | .inl _ => 1
      | .inr alternatives =>
          1 + (alternatives.map fun next => cutWork source depth next.1).sum

def cutDescent [Mul V] (source : Coalgebra State Answer V) :
    DescentCertificate (cutSystem source) where
  rank node := cutWork source node.1 node.2.1
  unfold node := by
    rcases node with ⟨depth, state, carried⟩
    cases depth with
    | zero => rfl
    | succ depth =>
        cases inspected : source state with
        | inl answer => simp [cutWork, cutSystem, inspected, foldRanks]
        | inr alternatives =>
            simp only [cutWork, cutSystem, inspected]
            clear inspected
            congr 1
            induction alternatives with
            | nil => rfl
            | cons next rest ih => simp [foldRanks, ih]

/-- Every lawful agenda completes the finite cut enumeration at its actual
node count. It may require far more selections than the unfolding depth. -/
theorem cut_run_complete [Monoid V] (source : Coalgebra State Answer V)
    {Memory : Type*}
    (controller : Controller (Nat × State × V) ((Answer ⊕ State) × V) Memory)
    (depth : Nat) (initial : State) :
    (InferenceControl.Snapshot.run (cutSystem source) controller
      (cutWork source depth initial)
      (InferenceControl.Snapshot.initial controller [(depth, initial, 1)])).search.frontier =
      [] := by
  simpa only [InferenceControl.Snapshot.initial, BranchingTemporal.initial,
    cutDescent, foldRanks, Nat.add_zero] using
    InferenceControl.Snapshot.run_completes_at_rank (cutSystem source) controller
      (cutDescent source)
      (InferenceControl.Snapshot.initial controller [(depth, initial, 1)])

/-- Exact multiplicities and coefficients agree with the independently
computed cut. Only agenda order is forgotten by this bag observation;
returned answers and complete pending states remain different leaves. -/
theorem cut_run_contributions [Monoid V] (source : Coalgebra State Answer V)
    {Memory : Type*}
    (controller : Controller (Nat × State × V) ((Answer ⊕ State) × V) Memory)
    (depth : Nat) (initial : State) :
    eventBag (InferenceControl.Snapshot.run (cutSystem source) controller
      (cutWork source depth initial)
      (InferenceControl.Snapshot.initial controller [(depth, initial, 1)])).search.events =
      (contributions source depth initial : Multiset ((Answer ⊕ State) × V)) := by
  have accounted := InferenceControl.Snapshot.completed_run_denotation
    (cutSystem source) controller (cutDenotation source) [(depth, initial, 1)]
    (cutWork source depth initial) (cut_run_complete source controller depth initial)
  simpa [cutDenotation, foldValues, cutValue] using accounted

section Replay

open Mettapedia.Machines
open Mettapedia.GSLT.Causality.OccurrenceMachineHistory
open Mettapedia.OSLF.Binding

variable {Code Result Coefficient : Type} [Monoid Coefficient]

/-- The scheduled source uses the existing executable occurrence machine.
Its state includes the complete source continuation and accumulated weight. -/
def pathMachine (source : Coalgebra Code Result Coefficient) :
    OccurrenceMachineCore Code (Code × Coefficient) (Result × Coefficient) where
  load code := (code, 1)
  next := (system source).successors
  answer := (system source).emit
  answer_final node result returned := by
    cases inspected : source node.1 <;> simp [system, inspected] at returned ⊢

/-- Decorating the common agenda is exactly the existing machine-occurrence
construction, including its physical successor positions. -/
theorem occurrence_system (source : Coalgebra Code Result Coefficient) :
    WorkOccurrence.system (pathMachine source) = WorkOccurrence.lift (system source) := rfl

/-- Read the coefficient at a selected physical source position. The default
is used only off a valid path; the history theorem establishes that every
actual step selects an existing source alternative. -/
def edgeCoefficient (source : Coalgebra Code Result Coefficient)
    (before : Code) (index : Nat) : Coefficient :=
  match source before with
  | .inl _ => 1
  | .inr alternatives => (alternatives[index]?.map Prod.snd).getD 1

theorem successor_coefficient (source : Coalgebra Code Result Coefficient)
    {before after : Code × Coefficient} {index : Nat}
    (selected : ((pathMachine source).next before)[index]? = some after) :
    after.2 = before.2 * edgeCoefficient source before.1 index := by
  cases inspected : source before.1 with
  | inl result => simp [pathMachine, system, inspected] at selected
  | inr alternatives =>
      simp only [pathMachine, system, inspected, List.getElem?_map] at selected
      cases located : alternatives[index]? with
      | none => simp [located] at selected
      | some edge =>
          simp only [located, Option.map_some, Option.some.injEq] at selected
          subst after
          simp [edgeCoefficient, inspected, located]

/-- A replayable history carries precisely the chronological product of its
actual source coefficients. No division, cancellation or commutation is used,
so this remains valid for zero coefficients and noncommutative algebras. -/
theorem history_coefficient (source : Coalgebra Code Result Coefficient)
    {before after : RewriteEventHistory.State
      (Mettapedia.GSLT.Causality.OccurrenceMachineHistory.system (pathMachine source))}
    (history : RewriteEventHistory.History
      (Mettapedia.GSLT.Causality.OccurrenceMachineHistory.system (pathMachine source))
      before after) :
    after.term.2 = before.term.2 *
      (eventAccount (pathMachine source)
        (fun state _ index => edgeCoefficient source state.1 index)).of history := by
  induction history with
  | nil =>
      change _ = _ * (1 : Coefficient)
      exact (mul_one _).symm
  | @cons middle target past event ih =>
      rw [eventAccount_cons]
      rw [successor_coefficient source event.property, ih, mul_assoc]

end Replay

end Scheduled

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

/-- Nested jobs may expose factors from the body, from another grade job, or
from a completed grade readout. Covering only body annotations omits two of
these cases. Administrative suspensions expose the multiplicative unit. -/
theorem nested_coefficients_satisfy [One V]
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Coalgebra Job Grade (V ⊕ Job))
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (resumeGrade : Job → Grade → Job) (holds : V → Prop) (unit : holds 1)
    (bodyFactors : CoefficientsSatisfy body (Sum.elim holds (fun _ => True)))
    (gradeFactors : CoefficientsSatisfy grade (Sum.elim holds (fun _ => True)))
    (returnedFactors : ∀ result value, readout result = some value → holds value) :
    CoefficientsSatisfy (nestedPendingSource body grade readout resumeBody resumeGrade) holds := by
  intro work alternatives inspected next member
  cases work with
  | inl state =>
      cases bodyStep : body state with
      | inl answer => simp [nestedPendingSource, bodyStep] at inspected
      | inr offered =>
          simp only [nestedPendingSource, bodyStep, Sum.inr.injEq] at inspected
          subst alternatives
          obtain ⟨candidate, candidateMember, rfl⟩ := List.mem_map.mp member
          have valid := bodyFactors state offered bodyStep candidate candidateMember
          cases coefficient : candidate.2 <;> simp_all
  | inr held =>
      rcases held with ⟨state, job, parents⟩
      cases gradeStep : grade job with
      | inl result =>
          cases decoded : readout result with
          | none => simp [nestedPendingSource, gradeStep, decoded] at inspected
          | some value =>
              have valid := returnedFactors result value decoded
              cases parents <;>
                simp only [nestedPendingSource, gradeStep, decoded, Sum.inr.injEq] at inspected <;>
                subst alternatives <;>
                obtain rfl := List.mem_singleton.mp member <;>
                exact valid
      | inr offered =>
          simp only [nestedPendingSource, gradeStep, Sum.inr.injEq] at inspected
          subst alternatives
          obtain ⟨candidate, candidateMember, rfl⟩ := List.mem_map.mp member
          have valid := gradeFactors job offered gradeStep candidate candidateMember
          cases coefficient : candidate.2 <;> simp_all

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

theorem parked_pending_count {Parked Pending : Type*}
    (obligations : Contributions (Parked ⊕ Pending) V) :
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
theorem obligations_empty_iff {Parked Pending : Type*}
    (obligations : Contributions (Parked ⊕ Pending) V) :
    obligations = [] ↔
      parkedGrades obligations = [] ∧ pendingInstructions obligations = [] := by
  have counts := parked_pending_count obligations
  constructor
  · intro empty; subst obligations; exact ⟨rfl, rfl⟩
  · rintro ⟨parked, pending⟩
    rw [parked, pending] at counts
    have emptyLength : obligations.length = 0 := by simpa using counts.symm
    exact List.length_eq_zero_iff.mp emptyLength

namespace Scheduled

/-- The pending part of a scheduled observation is exactly the retained
frontier, in order and with its original coefficients. Returned parked
results cannot become runnable instructions through this readout. -/
theorem nested_pending_exact {Parked : Type*}
    (snapshot : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot
      (State × V) ((Answer ⊕ Parked) × V)) :
    pendingInstructions (nestedObligations (observeSnapshot snapshot)) = snapshot.frontier := by
  rcases snapshot with ⟨events, frontier⟩
  induction events with
  | nil =>
      induction frontier with
      | nil => rfl
      | cons node rest ih =>
          simp [observeSnapshot, nestedObligations, pendingInstructions] at ih ⊢
  | cons event rest ih =>
      cases valueEq : event.value.1 <;>
        simpa [observeSnapshot, nestedObligations, pendingInstructions, valueEq] using ih

/-- Every returned parked occurrence appears once in the parked residual;
the runnable frontier contributes none of these records. -/
theorem nested_parked_exact {Parked : Type*}
    (snapshot : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot
      (State × V) ((Answer ⊕ Parked) × V)) :
    parkedGrades (nestedObligations (observeSnapshot snapshot)) =
      snapshot.events.filterMap (fun event => match event.value.1 with
        | .inl _ => none
        | .inr parked => some (parked, event.value.2)) := by
  rcases snapshot with ⟨events, frontier⟩
  induction events with
  | nil =>
      induction frontier with
      | nil => rfl
      | cons node rest ih =>
          simp [observeSnapshot, nestedObligations, parkedGrades] at ih ⊢
  | cons event rest ih =>
      cases valueEq : event.value.1 <;>
        simp_all [observeSnapshot, nestedObligations, parkedGrades]

/-- Closure requires both no runnable instruction and no parked return.
This is a readout of the actual event/frontier snapshot, not an additional
closure bit supplied by a scheduler. -/
theorem nested_closed_iff {Parked : Type*}
    (snapshot : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot
      (State × V) ((Answer ⊕ Parked) × V)) :
    nestedObligations (observeSnapshot snapshot) = [] ↔
      (snapshot.events.filterMap (fun event => match event.value.1 with
        | .inl _ => none
        | .inr parked => some (parked, event.value.2))) = [] ∧
      snapshot.frontier = [] := by
  rw [obligations_empty_iff, nested_pending_exact, nested_parked_exact]

end Scheduled

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

namespace Scheduled

/-- The common bounded-selection readout declares shortage only after both
the actual runnable frontier and returned parked obligations are empty. -/
theorem nested_saturated_iff {Parked Selected : Type*}
    (select : Answer → Option Selected) (requested : Nat)
    (snapshot : Mettapedia.GSLT.Core.BranchingTemporal.Snapshot
      (State × V) ((Answer ⊕ Parked) × V)) :
    nestedSelectionOutcome select requested (observeSnapshot snapshot) = .saturated ↔
      (nestedSelected select (observeSnapshot snapshot)).length < requested ∧
      (snapshot.events.filterMap (fun event => match event.value.1 with
        | .inl _ => none
        | .inr parked => some (parked, event.value.2))) = [] ∧
      snapshot.frontier = [] := by
  rw [nestedSelectionOutcome,
    Mettapedia.GSLT.Core.BoundedSelection.outcomeFromCounts_saturated_iff]
  simp only [List.isEmpty_iff, nested_closed_iff]

end Scheduled

/-- Each retained job's captured caller agrees with the exact suspended
state below it. This is caller-state agreement, not occurrence identity or
permission to merge equal states. The handler retains the full occurrences. -/
def nestedCallerAgreement {Owner : Type*} (stateView : State → Owner)
    (jobView capturedCaller : Job → Owner) (state : State) : Job → List Job → Prop
  | job, [] => capturedCaller job = stateView state
  | job, parent :: parents =>
      capturedCaller job = jobView parent ∧
        nestedCallerAgreement stateView jobView capturedCaller state parent parents

theorem nested_caller_agreement_replace {Owner : Type*} (stateView : State → Owner)
    (jobView capturedCaller : Job → Owner) (state : State) (before after : Job)
    (parents : List Job) (same : capturedCaller after = capturedCaller before)
    (agreement : nestedCallerAgreement stateView jobView capturedCaller state before parents) :
    nestedCallerAgreement stateView jobView capturedCaller state after parents := by
  cases parents with
  | nil => exact same.trans agreement
  | cons parent rest => exact ⟨same.trans agreement.1, agreement.2⟩

def nestedWorkCallerAgreement {Owner : Type*} (stateView : State → Owner)
    (jobView capturedCaller : Job → Owner) : NestedPendingState State Job → Prop :=
  Sum.elim (fun _ => True) (fun held =>
    nestedCallerAgreement stateView jobView capturedCaller held.1 held.2.1 held.2.2)

def nestedResultCallerAgreement {Owner : Type*} (stateView : State → Owner)
    (jobView capturedCaller : Job → Owner) :
    NestedPendingAnswer State Answer Job Job → Prop :=
  Sum.elim (fun _ => True) (fun held =>
    nestedCallerAgreement stateView jobView capturedCaller held.1 held.2.1 held.2.2)

/-- Actual fresh captures, origin-preserving steps and restoration of the
retained parent establish caller agreement throughout every finite cut.
Uninterpreted returns preserve that same caller stack. -/
theorem nested_contributions_caller_agreement [Monoid V] {Owner : Type*}
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Coalgebra Job Job (V ⊕ Job))
    (readout : Job → Option V) (resumeBody : State → Job → State)
    (resumeGrade : Job → Job → Job) (stateView : State → Owner)
    (jobView capturedCaller : Job → Owner)
    (bodyCaptures : ∀ state alternatives, body state = .inr alternatives →
      ∀ next ∈ alternatives, ∀ job, next.2 = .inr job →
        capturedCaller job = stateView next.1)
    (gradeReturns : ∀ job result, grade job = .inl result →
      capturedCaller result = capturedCaller job)
    (gradeSteps : ∀ job alternatives, grade job = .inr alternatives →
      ∀ next ∈ alternatives,
        capturedCaller next.1 = capturedCaller job ∧
        Sum.elim (fun _ => True)
          (fun child => capturedCaller child = jobView next.1) next.2)
    (resumes : ∀ parent result,
      capturedCaller (resumeGrade parent result) = capturedCaller parent)
    (fuel : Nat) (initial : NestedPendingState State Job)
    (valid : nestedWorkCallerAgreement stateView jobView capturedCaller initial) :
    ∀ leaf ∈ contributions (nestedPendingSource body grade readout resumeBody resumeGrade)
      fuel initial,
      Sum.elim (nestedResultCallerAgreement stateView jobView capturedCaller)
        (nestedWorkCallerAgreement stateView jobView capturedCaller) leaf.1 := by
  apply contributions_invariant (nestedPendingSource body grade readout resumeBody resumeGrade)
    (nestedWorkCallerAgreement stateView jobView capturedCaller)
    (nestedResultCallerAgreement stateView jobView capturedCaller) ?_ ?_ fuel initial valid
  · intro pending answer inherited returned
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result =>
            simp only [nestedPendingSource, inspected, Sum.inl.injEq] at returned
            subst answer
            exact True.intro
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        change nestedCallerAgreement stateView jobView capturedCaller state job parents at inherited
        cases inspected : grade job with
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
        | inl result =>
            cases decoded : readout result with
            | some value =>
                cases parents <;> simp [nestedPendingSource, inspected, decoded] at returned
            | none =>
                simp only [nestedPendingSource, inspected, decoded, Sum.inl.injEq] at returned
                subst answer
                exact nested_caller_agreement_replace stateView jobView capturedCaller
                  state job result parents (gradeReturns job result inspected) inherited
  · intro pending alternatives inherited requested next member
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result => simp [nestedPendingSource, inspected] at requested
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            cases coefficient with
            | inl value =>
                cases same
                exact True.intro
            | inr job =>
                cases same
                exact bodyCaptures state children inspected (child, .inr job) present job rfl
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        change nestedCallerAgreement stateView jobView capturedCaller state job parents at inherited
        cases inspected : grade job with
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨unchanged, capture⟩ := gradeSteps job children inspected (child, coefficient) present
            have childAgreement := nested_caller_agreement_replace stateView jobView
              capturedCaller state job child parents unchanged inherited
            cases coefficient with
            | inl value =>
                cases same
                exact childAgreement
            | inr inner =>
                cases same
                exact ⟨capture, childAgreement⟩
        | inl result =>
            cases decoded : readout result with
            | none => simp [nestedPendingSource, inspected, decoded] at requested
            | some value =>
                cases parents with
                | nil =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    obtain rfl := List.mem_singleton.mp member
                    exact True.intro
                | cons parent rest =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    obtain rfl := List.mem_singleton.mp member
                    exact nested_caller_agreement_replace stateView jobView capturedCaller
                      state parent (resumeGrade parent result) rest (resumes parent result)
                      inherited.2

/-- All suspended frames remain in the owned account while their child runs. -/
def nestedStateMeter (stateMeter : State → Nat) (jobMeter : Job → Nat) :
    NestedPendingState State Job → Nat
  | .inl state => stateMeter state
  | .inr (state, job, parents) =>
      stateMeter state + jobMeter job + (parents.map jobMeter).sum

/-- An on-request view of every owned account, in caller-to-parent order. -/
def nestedStateAccounts (stateMeter : State → Nat) (jobMeter : Job → Nat) :
    NestedPendingState State Job → List Nat
  | .inl state => [stateMeter state]
  | .inr (state, job, parents) =>
      stateMeter state :: jobMeter job :: parents.map jobMeter

theorem nested_state_accounts_sum (stateMeter : State → Nat) (jobMeter : Job → Nat)
    (pending : NestedPendingState State Job) :
    (nestedStateAccounts stateMeter jobMeter pending).sum =
      nestedStateMeter stateMeter jobMeter pending := by
  cases pending with
  | inl state => simp [nestedStateAccounts, nestedStateMeter]
  | inr held =>
      rcases held with ⟨state, job, parents⟩
      simp [nestedStateAccounts, nestedStateMeter, Nat.add_assoc]

def nestedAnswerMeter (answerMeter : Answer → Nat) (stateMeter : State → Nat)
    (gradeMeter : Grade → Nat) (jobMeter : Job → Nat) :
    NestedPendingAnswer State Answer Job Grade → Nat
  | .inl answer => answerMeter answer
  | .inr (state, result, parents) =>
      stateMeter state + gradeMeter result + (parents.map jobMeter).sum

/-- Child work is transferred once into its caller when it returns. Both
instruction sources charge at most one unit, and fresh child accounts start
at zero. Administrative phase changes may charge no actual instruction. -/
theorem nested_contributions_meter_bounds_le [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job)) (grade : Coalgebra Job Grade (V ⊕ Job))
    (readout : Grade → Option V) (resumeBody : State → Grade → State)
    (resumeGrade : Job → Grade → Job)
    (stateMeter : State → Nat) (answerMeter : Answer → Nat)
    (jobMeter : Job → Nat) (gradeMeter : Grade → Nat)
    (bodyReturns : ∀ state answer, body state = .inl answer →
      answerMeter answer = stateMeter state)
    (bodySteps : ∀ state alternatives, body state = .inr alternatives →
      ∀ next ∈ alternatives, stateMeter state ≤ stateMeter next.1 ∧
        stateMeter next.1 ≤ stateMeter state + 1 ∧
        Sum.elim (fun _ => True) (fun child => jobMeter child = 0) next.2)
    (gradeReturns : ∀ job result, grade job = .inl result → gradeMeter result = jobMeter job)
    (gradeSteps : ∀ job alternatives, grade job = .inr alternatives →
      ∀ next ∈ alternatives, jobMeter job ≤ jobMeter next.1 ∧
        jobMeter next.1 ≤ jobMeter job + 1 ∧
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
            obtain ⟨lower, upper, fresh⟩ := bodySteps state children inspected (child, coefficient) present
            dsimp only at lower upper
            cases coefficient with
            | inl value =>
                cases same
                simp only [nestedStateMeter]
                omega
            | inr job =>
                cases same
                change jobMeter job = 0 at fresh
                simp only [nestedStateMeter, fresh, List.map_nil, List.sum_nil,
                  Nat.add_zero]
                omega
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        cases inspected : grade job with
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨lower, upper, fresh⟩ := gradeSteps job children inspected (child, coefficient) present
            dsimp only at lower upper
            cases coefficient with
            | inl value =>
                cases same
                simp only [nestedStateMeter]
                omega
            | inr inner =>
                cases same
                change jobMeter inner = 0 at fresh
                simp only [nestedStateMeter, fresh, List.map_cons, List.sum_cons,
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

/-- Exact-unit specialization of the shared nested instruction bound.
Returning a child transfers its expenditure once; fresh children start at zero. -/
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
  apply nested_contributions_meter_bounds_le body grade readout resumeBody resumeGrade
    stateMeter answerMeter jobMeter gradeMeter bodyReturns ?_ gradeReturns ?_
    bodyResumes gradeResumes fuel initial
  · intro state alternatives requested next member
    obtain ⟨spent, fresh⟩ := bodySteps state alternatives requested next member
    exact ⟨by omega, by omega, fresh⟩
  · intro job alternatives requested next member
    obtain ⟨spent, fresh⟩ := gradeSteps job alternatives requested next member
    exact ⟨by omega, by omega, fresh⟩

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

/-- Component invariants include every suspended parent, even while an inner
job is the only active computation. -/
def nestedWorkHolds (stateValid : State → Prop) (jobValid : Job → Prop) :
    NestedPendingState State Job → Prop
  | .inl state => stateValid state
  | .inr (state, job, parents) =>
      stateValid state ∧ jobValid job ∧ ∀ parent ∈ parents, jobValid parent

def nestedResultHolds (stateValid : State → Prop) (answerValid : Answer → Prop)
    (jobValid : Job → Prop) (gradeValid : Grade → Prop) :
    NestedPendingAnswer State Answer Job Grade → Prop
  | .inl answer => answerValid answer
  | .inr (state, result, parents) =>
      stateValid state ∧ gradeValid result ∧ ∀ parent ∈ parents, jobValid parent

/-- Actual nested transitions preserve component invariants across fresh
jobs, completed jobs, unknown readouts and restoration of suspended parents. -/
theorem nested_source_preserves [One V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (jobValid : Job → Prop) (gradeValid : Grade → Prop)
    (bodyReturns : ∀ state answer, stateValid state →
      body state = .inl answer → answerValid answer)
    (bodySteps : ∀ state alternatives, stateValid state → body state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1 ∧
        ∀ child, next.2 = .inr child → jobValid child)
    (gradeReturns : ∀ job result, jobValid job → grade job = .inl result → gradeValid result)
    (gradeSteps : ∀ job alternatives, jobValid job → grade job = .inr alternatives →
      ∀ next ∈ alternatives, jobValid next.1 ∧
        ∀ child, next.2 = .inr child → jobValid child)
    (resumeBodyValid : ∀ state result, stateValid state → gradeValid result →
      stateValid (resumeBody state result))
    (resumeGradeValid : ∀ parent result, jobValid parent → gradeValid result →
      jobValid (resumeGrade parent result)) :
    (∀ pending answer, nestedWorkHolds stateValid jobValid pending →
      nestedPendingSource body grade readout resumeBody resumeGrade pending = .inl answer →
      nestedResultHolds stateValid answerValid jobValid gradeValid answer) ∧
    (∀ pending alternatives, nestedWorkHolds stateValid jobValid pending →
      nestedPendingSource body grade readout resumeBody resumeGrade pending = .inr alternatives →
      ∀ next ∈ alternatives, nestedWorkHolds stateValid jobValid next.1) := by
  constructor
  · intro pending answer inherited returned
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result =>
            simp only [nestedPendingSource, inspected, Sum.inl.injEq] at returned
            subst answer
            exact bodyReturns state result inherited inspected
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        rcases inherited with ⟨stateOk, jobOk, parentsOk⟩
        cases inspected : grade job with
        | inr alternatives => simp [nestedPendingSource, inspected] at returned
        | inl result =>
            cases decoded : readout result with
            | some value =>
                cases parents <;> simp [nestedPendingSource, inspected, decoded] at returned
            | none =>
                simp only [nestedPendingSource, inspected, decoded, Sum.inl.injEq] at returned
                subst answer
                exact ⟨stateOk, gradeReturns job result jobOk inspected, parentsOk⟩
  · intro pending alternatives inherited requested next member
    cases pending with
    | inl state =>
        cases inspected : body state with
        | inl result => simp [nestedPendingSource, inspected] at requested
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨childOk, captures⟩ := bodySteps state children inherited inspected
              (child, coefficient) present
            cases coefficient with
            | inl value => cases same; exact childOk
            | inr job =>
                cases same
                exact ⟨childOk, captures job rfl, by simp⟩
    | inr held =>
        rcases held with ⟨state, job, parents⟩
        rcases inherited with ⟨stateOk, jobOk, parentsOk⟩
        cases inspected : grade job with
        | inr children =>
            simp only [nestedPendingSource, inspected, Sum.inr.injEq] at requested
            subst alternatives
            obtain ⟨⟨child, coefficient⟩, present, same⟩ := List.mem_map.mp member
            obtain ⟨childOk, captures⟩ := gradeSteps job children jobOk inspected
              (child, coefficient) present
            cases coefficient with
            | inl value =>
                cases same
                exact ⟨stateOk, childOk, parentsOk⟩
            | inr inner =>
                cases same
                refine ⟨stateOk, captures inner rfl, ?_⟩
                intro parent member
                rcases List.mem_cons.mp member with rfl | later
                · exact childOk
                · exact parentsOk parent later
        | inl result =>
            have resultOk := gradeReturns job result jobOk inspected
            cases decoded : readout result with
            | none => simp [nestedPendingSource, inspected, decoded] at requested
            | some value =>
                cases parents with
                | nil =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    obtain rfl := List.mem_singleton.mp member
                    exact resumeBodyValid state result stateOk resultOk
                | cons parent rest =>
                    simp only [nestedPendingSource, inspected, decoded, Sum.inr.injEq] at requested
                    subst alternatives
                    obtain rfl := List.mem_singleton.mp member
                    exact ⟨stateOk, resumeGradeValid parent result
                      (parentsOk parent (List.mem_cons_self)) resultOk,
                      fun held member => parentsOk held (List.mem_cons_of_mem _ member)⟩

theorem nested_contributions_invariant [Monoid V]
    (body : Coalgebra State Answer (V ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job)) (readout : Grade → Option V)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (stateValid : State → Prop) (answerValid : Answer → Prop)
    (jobValid : Job → Prop) (gradeValid : Grade → Prop)
    (bodyReturns : ∀ state answer, stateValid state →
      body state = .inl answer → answerValid answer)
    (bodySteps : ∀ state alternatives, stateValid state → body state = .inr alternatives →
      ∀ next ∈ alternatives, stateValid next.1 ∧
        ∀ child, next.2 = .inr child → jobValid child)
    (gradeReturns : ∀ job result, jobValid job → grade job = .inl result → gradeValid result)
    (gradeSteps : ∀ job alternatives, jobValid job → grade job = .inr alternatives →
      ∀ next ∈ alternatives, jobValid next.1 ∧
        ∀ child, next.2 = .inr child → jobValid child)
    (resumeBodyValid : ∀ state result, stateValid state → gradeValid result →
      stateValid (resumeBody state result))
    (resumeGradeValid : ∀ parent result, jobValid parent → gradeValid result →
      jobValid (resumeGrade parent result))
    (fuel : Nat) (initial : NestedPendingState State Job)
    (valid : nestedWorkHolds stateValid jobValid initial) :
    ∀ leaf ∈ contributions (nestedPendingSource body grade readout resumeBody resumeGrade)
      fuel initial,
      Sum.elim (nestedResultHolds stateValid answerValid jobValid gradeValid)
        (nestedWorkHolds stateValid jobValid) leaf.1 := by
  obtain ⟨returns, successors⟩ := nested_source_preserves body grade readout resumeBody resumeGrade
    stateValid answerValid jobValid gradeValid bodyReturns bodySteps gradeReturns gradeSteps
    resumeBodyValid resumeGradeValid
  exact contributions_invariant _ _ _ returns successors fuel initial valid

end PendingCoefficients

/-! ## Lawful coefficient changes

A monoid homomorphism transports the finite execution and every retained nested
grade frame. Admission additionally needs its own intertwining law; preserving
coefficients alone never grants permission to filter contributions. Completed
selection and the whole obligation census commute with coefficient-only maps.
-/

section CoefficientChanges

universe uOther
variable {W : Type uOther}

theorem contributions_change_coefficients [Monoid V] [Monoid W]
    (change : V →* W) (source : Coalgebra State Answer V)
    (target : Coalgebra State Answer W)
    (comparison : ∀ state, target state = match source state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives))
    (fuel : Nat) (state : State) :
    contributions target fuel state = mapCoefficients change (contributions source fuel state) := by
  induction fuel generalizing state with
  | zero => simp [contributions, mapCoefficients]
  | succ fuel ih =>
      simp only [contributions, comparison]
      cases inspected : source state with
      | inl answer => simp [mapCoefficients]
      | inr alternatives =>
          rw [mapCoefficients_sequence change change.map_mul]
          apply congrArg (sequence (mapCoefficients change alternatives))
          funext next
          exact ih next

theorem admitting_source_change_coefficients [Monoid V] [Monoid W]
    (change : V →* W) (source : Coalgebra State Answer V)
    (target : Coalgebra State Answer W)
    (comparison : ∀ state, target state = match source state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives))
    (admitSource : V → Bool) (admitTarget : W → Bool)
    (admits : ∀ value, admitTarget (change value) = admitSource value)
    (state : State) :
    admittingSource target admitTarget state =
      match admittingSource source admitSource state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives) := by
  simp only [admittingSource, comparison]
  cases inspected : source state with
  | inl answer => rfl
  | inr alternatives =>
      simp [mapCoefficients, List.filter_map, Function.comp_def, admits]

/-- A coefficient change preserves selected admission boundaries only when
the declared tests agree on every coefficient. Administrative steps are unchanged. -/
theorem admitting_at_source_change_coefficients [Monoid V] [Monoid W]
    (change : V →* W) (source : Coalgebra State Answer V)
    (target : Coalgebra State Answer W)
    (comparison : ∀ state, target state = match source state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives))
    (boundary : State → Bool) (admitSource : V → Bool) (admitTarget : W → Bool)
    (admits : ∀ value, admitTarget (change value) = admitSource value)
    (state : State) :
    admittingSourceAt target boundary admitTarget state =
      match admittingSourceAt source boundary admitSource state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives) := by
  unfold admittingSourceAt
  cases selected : boundary state with
  | false => simpa using comparison state
  | true => exact (admitting_source_change_coefficients change source target
      comparison admitSource admitTarget admits state)

/-- The admission comparison preserves each complete surviving contribution
at every finite cut, including retained state, coefficient order and duplicates. -/
theorem admitting_at_contributions_change_coefficients [Monoid V] [Monoid W]
    (change : V →* W) (source : Coalgebra State Answer V)
    (target : Coalgebra State Answer W)
    (comparison : ∀ state, target state = match source state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives))
    (boundary : State → Bool) (admitSource : V → Bool) (admitTarget : W → Bool)
    (admits : ∀ value, admitTarget (change value) = admitSource value)
    (fuel : Nat) (state : State) :
    contributions (admittingSourceAt target boundary admitTarget) fuel state =
      mapCoefficients change
        (contributions (admittingSourceAt source boundary admitSource) fuel state) := by
  apply contributions_change_coefficients change _ _ ?_ fuel state
  exact admitting_at_source_change_coefficients change source target comparison
    boundary admitSource admitTarget admits

theorem nested_pending_change_coefficients [Monoid V] [Monoid W]
    {Job Grade : Type*} (change : V →* W)
    (body : Coalgebra State Answer (V ⊕ Job))
    (targetBody : Coalgebra State Answer (W ⊕ Job))
    (grade : Coalgebra Job Grade (V ⊕ Job))
    (targetGrade : Coalgebra Job Grade (W ⊕ Job))
    (bodyComparison : ∀ state, targetBody state = match body state with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (alternatives.map fun next =>
          (next.1, Sum.map change id next.2)))
    (gradeComparison : ∀ job, targetGrade job = match grade job with
      | .inl result => .inl result
      | .inr alternatives => .inr (alternatives.map fun next =>
          (next.1, Sum.map change id next.2)))
    (readout : Grade → Option V) (targetReadout : Grade → Option W)
    (readoutComparison : ∀ result, targetReadout result = (readout result).map change)
    (resumeBody : State → Grade → State) (resumeGrade : Job → Grade → Job)
    (pending : NestedPendingState State Job) :
    nestedPendingSource targetBody targetGrade targetReadout resumeBody resumeGrade pending =
      match nestedPendingSource body grade readout resumeBody resumeGrade pending with
      | .inl answer => .inl answer
      | .inr alternatives => .inr (mapCoefficients change alternatives) := by
  cases pending with
  | inl state =>
      simp only [nestedPendingSource, bodyComparison]
      cases inspected : body state with
      | inl answer => rfl
      | inr alternatives =>
          simp only [mapCoefficients, List.map_map]
          apply congrArg Sum.inr
          apply List.map_congr_left
          rintro ⟨next, choice⟩ _
          cases choice <;> simp [map_one]
  | inr held =>
      rcases held with ⟨state, job, parents⟩
      simp only [nestedPendingSource, gradeComparison]
      cases inspected : grade job with
      | inl result =>
          simp only []
          rw [readoutComparison]
          cases decoded : readout result with
          | none => rfl
          | some value => cases parents <;> rfl
      | inr alternatives =>
          simp only [mapCoefficients, List.map_map]
          apply congrArg Sum.inr
          apply List.map_congr_left
          rintro ⟨next, choice⟩ _
          cases choice <;> simp [map_one]

theorem nested_selected_change_coefficients {Parked Pending Selected : Type*}
    (change : V → W) (select : Answer → Option Selected)
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    nestedSelected select (mapCoefficients change leaves) =
      mapCoefficients change (nestedSelected select leaves) := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl result =>
          cases result with
          | inl answer =>
              cases selected : select answer with
              | none =>
                  simpa [nestedSelected, nestedAnswers, mapCoefficients, selected] using ih
              | some item =>
                  simpa [nestedSelected, nestedAnswers, mapCoefficients, selected] using
                    congrArg (List.cons (item, change value)) ih
          | inr parked =>
              simpa [nestedSelected, nestedAnswers, mapCoefficients] using ih
      | inr pending => simpa [nestedSelected, nestedAnswers, mapCoefficients] using ih

theorem nested_obligations_change_coefficients {Parked Pending : Type*}
    (change : V → W) (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    nestedObligations (mapCoefficients change leaves) =
      mapCoefficients change (nestedObligations leaves) := by
  induction leaves with
  | nil => rfl
  | cons leaf rest ih =>
      rcases leaf with ⟨leaf, value⟩
      cases leaf with
      | inl result =>
          cases result with
          | inl answer => simpa [nestedObligations, mapCoefficients] using ih
          | inr parked =>
              simpa [nestedObligations, mapCoefficients] using
                congrArg (List.cons (Sum.inl parked, change value)) ih
      | inr pending =>
          simpa [nestedObligations, mapCoefficients] using
            congrArg (List.cons (Sum.inr pending, change value)) ih

theorem nested_selection_change_coefficients {Parked Pending Selected : Type*}
    (change : V → W) (select : Answer → Option Selected) (requested : Nat)
    (leaves : Contributions ((Answer ⊕ Parked) ⊕ Pending) V) :
    nestedSelectionOutcome select requested (mapCoefficients change leaves) =
      nestedSelectionOutcome select requested leaves := by
  simp only [nestedSelectionOutcome]
  rw [nested_selected_change_coefficients, nested_obligations_change_coefficients]
  simp [mapCoefficients]

end CoefficientChanges

end Mettapedia.GSLT.Dynamics.WeightedBranchingResumption
