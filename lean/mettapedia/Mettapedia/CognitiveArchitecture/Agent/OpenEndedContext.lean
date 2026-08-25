import Mathlib.Data.Fintype.Card
import Mettapedia.CognitiveArchitecture.Agent.WorldState
import Mettapedia.Cybernetics.ObservedVariety

/-!
# Open-ended context through weakest sufficient views

Source provenance: integrated from GödelClaw/MeTTapedia commit
`4d846be21841a1aec5d99bd80ec58b7d56078c57`; the original theorem bundle is
retained, with observer-variety and fibre-factorization bridges added for the
live general theory.

A permanent lossy context cannot remain sufficient for an open-ended family
of queries whose accumulated distinctions identify the recoverable evidence
state.  This file supplies the constructive counterpart to that obstruction:
at each epoch, retain exactly the answer vector for the finite active query
set, while keeping the evidence state available for certified refresh.

The active answer vector is canonical in a precise sense.  It identifies two
states exactly when all active answers agree, preserves every active query,
and factors through every other active-query-preserving view.  Thus it is the
coarsest, or weakest, sufficient view in the factorization preorder.  Its
cardinality is bounded by `|Answer| ^ |active|`, independently of the size of
the recoverable state space.

The permanent-view no-go and the dynamic construction have deliberately
different premises:

* open-endedness constrains the union of queries encountered across epochs;
* boundedness constrains each finite active set separately;
* recoverability keeps the evidence state outside the lossy context view.

No fixed action policy or compaction algorithm is installed here.
-/

set_option autoImplicit false

namespace Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext

open Mettapedia.CognitiveArchitecture.Agent.WorldState
open Mettapedia.Cybernetics

universe uState uEpoch uQuery uAnswer uView uCoarse

variable {State : Type uState} {Epoch : Type uEpoch}
  {Query : Type uQuery} {Answer : Type uAnswer}

/-! ## Finite active-query views -/

/-- The answer vector indexed by one finite active query set. -/
abbrev ActiveQueryView (active : Finset Query) (Answer : Type uAnswer) :
    Type (max uQuery uAnswer) :=
  active → Answer

/-- Project a recoverable state to exactly its active answer vector. -/
def activeProjection [DecidableEq Query]
    (answer : State → Query → Answer) (active : Finset Query) :
    State → ActiveQueryView active Answer :=
  fun state query => answer state query.1

/-- Equality of canonical active views is exactly agreement on every active
query.  The view contains neither less nor more state distinction than that
contract names. -/
theorem activeProjection_eq_iff [DecidableEq Query]
    (answer : State → Query → Answer) (active : Finset Query)
    (left right : State) :
    activeProjection answer active left = activeProjection answer active right ↔
      ∀ query, query ∈ active → answer left query = answer right query := by
  constructor
  · intro same query member
    exact congrFun same ⟨query, member⟩
  · intro agrees
    funext query
    exact agrees query.1 query.2

/-- The active projection as an observer.  This connects agent context to the
general observer-indexed variety theory without identifying its entire
codomain with the views that evidence states actually realize. -/
def activeObserver [DecidableEq Query]
    (answer : State → Query → Answer) (active : Finset Query) :
    Observer State (ActiveQueryView active Answer) where
  observe := activeProjection answer active

/-- The canonical active observer distinguishes exactly the state pairs that
some active query distinguishes. -/
theorem activeObserver_distinguishes_iff [DecidableEq Query]
    (answer : State → Query → Answer) (active : Finset Query)
    (left right : State) :
    (activeObserver answer active).Distinguishes left right ↔
      ∃ query, query ∈ active ∧
        answer left query ≠ answer right query := by
  classical
  constructor
  · intro distinguished
    change activeProjection answer active left ≠
      activeProjection answer active right at distinguished
    by_contra noWitness
    exact distinguished
      ((activeProjection_eq_iff answer active left right).2 (by
        intro query member
        by_contra differs
        exact noWitness ⟨query, member, differs⟩))
  · rintro ⟨query, member, differs⟩ equal
    change activeProjection answer active left =
      activeProjection answer active right at equal
    exact differs
      ((activeProjection_eq_iff answer active left right).1 equal
        query member)

/-- `fine` refines `coarse` when the coarse view can be obtained by forgetting
information from the fine view. -/
def Refines {Fine : Type uView} {Coarse : Type uCoarse}
    (fine : State → Fine) (coarse : State → Coarse) : Prop :=
  ∃ forget : Fine → Coarse, ∀ state, forget (fine state) = coarse state

theorem Refines.refl {View : Type uView} (view : State → View) :
    Refines view view := by
  exact ⟨id, fun _ => rfl⟩

theorem Refines.trans
    {Fine : Type uView} {Middle : Type*} {Coarse : Type uCoarse}
    {fine : State → Fine} {middle : State → Middle} {coarse : State → Coarse}
    (fineRefines : Refines fine middle)
    (middleRefines : Refines middle coarse) :
    Refines fine coarse := by
  obtain ⟨forgetFine, fineCommutes⟩ := fineRefines
  obtain ⟨forgetMiddle, middleCommutes⟩ := middleRefines
  refine ⟨forgetMiddle ∘ forgetFine, ?_⟩
  intro state
  simp only [Function.comp_apply, fineCommutes, middleCommutes]

/-- Executable refinement implies Mathlib's fibre-invariance notion.  The
converse needs a way to choose values outside the image and is intentionally
not assumed. -/
theorem Refines.factorsThrough
    {Fine : Type uView} {Coarse : Type uCoarse}
    {fine : State → Fine} {coarse : State → Coarse}
    (refines : Refines fine coarse) :
    Function.FactorsThrough coarse fine := by
  obtain ⟨forget, commutes⟩ := refines
  intro left right sameFine
  rw [← commutes left, ← commutes right, sameFine]

/-- Any view satisfying the existing relevant-query contract refines the
canonical active answer vector.  This is the weakest-sufficient-view theorem:
every sufficient view contains at least the distinctions in the canonical
one. -/
theorem preservesRelevant_refines_activeProjection [DecidableEq Query]
    {View : Type uView}
    (answer : State → Query → Answer) (active : Finset Query)
    (view : State → View)
    (preserves :
      PreservesRelevantQueries (fun query => query ∈ active) answer view) :
    Refines view (activeProjection answer active) := by
  obtain ⟨answerFromView, recovers⟩ := preserves
  refine ⟨fun visible query => answerFromView visible query.1, ?_⟩
  intro state
  funext query
  exact recovers state query.1 query.2

/-- The canonical active view itself satisfies the existing relevant-query
contract.  An inhabitant is needed only to totalize the decoder on irrelevant
queries; no theorem depends on those arbitrary values. -/
theorem activeProjection_preservesRelevant [DecidableEq Query]
    [Inhabited Answer]
    (answer : State → Query → Answer) (active : Finset Query) :
    PreservesRelevantQueries (fun query => query ∈ active) answer
      (activeProjection answer active) := by
  let decode : ActiveQueryView active Answer → Query → Answer :=
    fun visible query =>
      if member : query ∈ active then visible ⟨query, member⟩ else default
  refine ⟨decode, ?_⟩
  intro state query member
  simp only [decode, dif_pos member, activeProjection]

/-- The canonical view is sufficient and no more informative than any other
sufficient view. -/
theorem activeProjection_is_weakest_sufficient [DecidableEq Query]
    [Inhabited Answer]
    (answer : State → Query → Answer) (active : Finset Query) :
    PreservesRelevantQueries (fun query => query ∈ active) answer
        (activeProjection answer active) ∧
      ∀ {View : Type uView} (view : State → View),
        PreservesRelevantQueries (fun query => query ∈ active) answer view →
          Refines view (activeProjection answer active) := by
  constructor
  · exact activeProjection_preservesRelevant answer active
  · intro View view preserves
    exact preservesRelevant_refines_activeProjection answer active view preserves

/-- Finite active sets yield a bounded view even when `State` and `Query` are
not finite. -/
theorem card_activeQueryView [DecidableEq Query] [Fintype Answer]
    (active : Finset Query) :
    Fintype.card (ActiveQueryView active Answer) =
      Fintype.card Answer ^ active.card := by
  simp [ActiveQueryView]

/-- The informative observed variety is bounded by the full answer-vector
codomain.  Unlike `card_activeQueryView`, this counts only views realized by
some evidence state. -/
theorem natCard_activeObservedVariety_le [DecidableEq Query]
    [Fintype Answer]
    (answer : State → Query → Answer) (active : Finset Query) :
    Nat.card (activeObserver answer active).Variety ≤
      Fintype.card Answer ^ active.card := by
  calc
    Nat.card (activeObserver answer active).Variety ≤
        Nat.card (ActiveQueryView active Answer) :=
      Nat.card_le_card_of_injective
        (fun observed : (activeObserver answer active).Variety => observed.1)
        (fun _ _ equal => Subtype.ext equal)
    _ = Fintype.card (ActiveQueryView active Answer) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card Answer ^ active.card :=
      card_activeQueryView active

/-- The observed-variety bound is exact when every active answer vector is
realized by an evidence state.  Surjectivity is the missing premise behind
identifying the codomain count with realized variety. -/
theorem natCard_activeObservedVariety_eq [DecidableEq Query]
    [Fintype Answer]
    (answer : State → Query → Answer) (active : Finset Query)
    (realizesEveryVector :
      Function.Surjective (activeProjection answer active)) :
    Nat.card (activeObserver answer active).Variety =
      Fintype.card Answer ^ active.card := by
  calc
    Nat.card (activeObserver answer active).Variety =
        Nat.card (ActiveQueryView active Answer) := by
      apply Nat.card_eq_of_bijective
        (fun observed : (activeObserver answer active).Variety => observed.1)
      constructor
      · intro left right equal
        exact Subtype.ext equal
      · intro view
        obtain ⟨state, realizes⟩ := realizesEveryVector view
        exact ⟨⟨view, ⟨state, realizes⟩⟩, rfl⟩
    _ = Fintype.card (ActiveQueryView active Answer) :=
      Nat.card_eq_fintype_card
    _ = Fintype.card Answer ^ active.card :=
      card_activeQueryView active

/-! ## Open-ended schedules rule out a permanent lossy sufficient view -/

/-- Across the schedule, the encountered finite query sets distinguish every
pair of recoverable states.  Individual epochs may remain very small. -/
def ScheduleSeparating [DecidableEq Query]
    (answer : State → Query → Answer)
    (schedule : Epoch → Finset Query) : Prop :=
  ∀ ⦃left right : State⦄,
    (∀ epoch (query : schedule epoch),
      answer left query.1 = answer right query.1) →
      left = right

/-- One permanent view is complete throughout the schedule if each epoch may
decode its active answers from that same view.  Allowing a different decoder
at every epoch makes the no-go theorem maximally permissive. -/
def PermanentlyComplete [DecidableEq Query]
    (answer : State → Query → Answer)
    (schedule : Epoch → Finset Query)
    {View : Type uView} (view : State → View) : Prop :=
  ∃ decode : ∀ epoch, View → ActiveQueryView (schedule epoch) Answer,
    ∀ epoch state, decode epoch (view state) =
      activeProjection answer (schedule epoch) state

/-- A permanent context sufficient for an open-ended, state-separating
schedule must retain the entire state's distinctions. -/
theorem permanentlyComplete_injective [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    {View : Type uView} {view : State → View}
    (separating : ScheduleSeparating answer schedule)
    (complete : PermanentlyComplete answer schedule view) :
    Function.Injective view := by
  obtain ⟨decode, recovers⟩ := complete
  intro left right sameView
  apply separating
  intro epoch query
  calc
    answer left query.1 = decode epoch (view left) query :=
      (congrFun (recovers epoch left) query).symm
    _ = decode epoch (view right) query := by rw [sameView]
    _ = answer right query.1 := congrFun (recovers epoch right) query

/-- Consequently, no genuinely lossy permanent view can remain sufficient as
the separating query schedule unfolds. -/
theorem no_permanently_sufficient_lossy_context [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    {View : Type uView} {view : State → View}
    (separating : ScheduleSeparating answer schedule)
    (lossy : ¬ Function.Injective view) :
    ¬ PermanentlyComplete answer schedule view := by
  intro complete
  exact lossy (permanentlyComplete_injective separating complete)

/-- In the finite case, a permanently sufficient open-ended view cannot have
strictly smaller cardinality than the recoverable state. -/
theorem no_smaller_permanently_sufficient_context [DecidableEq Query]
    {View : Type uView} [Fintype State] [Fintype View]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    {view : State → View}
    (separating : ScheduleSeparating answer schedule)
    (smaller : Fintype.card View < Fintype.card State) :
    ¬ PermanentlyComplete answer schedule view := by
  intro complete
  have injective : Function.Injective view :=
    permanentlyComplete_injective separating complete
  have cardLe : Fintype.card State ≤ Fintype.card View :=
    Fintype.card_le_of_injective view injective
  exact (Nat.not_le_of_gt smaller) cardLe

/-! ## Recoverable evidence and certified refresh -/

/-- A bounded model-visible context paired with the exact evidence state from
which it was certified.  Refresh replaces only the view and epoch. -/
structure RecoverableContext [DecidableEq Query]
    (answer : State → Query → Answer)
    (schedule : Epoch → Finset Query) where
  evidence : State
  epoch : Epoch
  view : ActiveQueryView (schedule epoch) Answer
  certified : view = activeProjection answer (schedule epoch) evidence

/-- Construct the certified weakest view for one evidence state and epoch. -/
def RecoverableContext.ofEvidence [DecidableEq Query]
    (answer : State → Query → Answer)
    (schedule : Epoch → Finset Query)
    (evidence : State) (epoch : Epoch) :
    RecoverableContext answer schedule where
  evidence := evidence
  epoch := epoch
  view := activeProjection answer (schedule epoch) evidence
  certified := rfl

/-- Refresh a bounded context from its retained evidence when the active query
set changes. -/
def RecoverableContext.refresh [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    (context : RecoverableContext answer schedule) (next : Epoch) :
    RecoverableContext answer schedule :=
  RecoverableContext.ofEvidence answer schedule context.evidence next

@[simp] theorem RecoverableContext.refresh_evidence [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    (context : RecoverableContext answer schedule) (next : Epoch) :
    (context.refresh next).evidence = context.evidence := by
  rfl

@[simp] theorem RecoverableContext.refresh_epoch [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    (context : RecoverableContext answer schedule) (next : Epoch) :
    (context.refresh next).epoch = next := by
  rfl

/-- Every refreshed context is certified against the retained evidence; no
summary is recursively summarized. -/
theorem RecoverableContext.refresh_certified [DecidableEq Query]
    {answer : State → Query → Answer}
    {schedule : Epoch → Finset Query}
    (context : RecoverableContext answer schedule) (next : Epoch) :
    (context.refresh next).view =
      activeProjection answer (schedule next) context.evidence := by
  rfl

/-! ## Infinite-state canary -/

namespace InfiniteStateCanary

/-- Query `q` asks whether the recoverable natural-number state is `q`. -/
def answer (state query : Nat) : Bool :=
  decide (state = query)

/-- Epoch `n` activates only query `n`. -/
def schedule (epoch : Nat) : Finset Nat :=
  {epoch}

/-- Although every epoch contains only one Boolean query, the accumulated
schedule distinguishes all natural-number evidence states. -/
theorem scheduleSeparating : ScheduleSeparating answer schedule := by
  intro left right agrees
  by_contra distinct
  have atLeft := agrees left ⟨left, by simp [schedule]⟩
  simp [answer] at atLeft
  exact distinct atLeft.symm

/-- Every epoch's canonical view has exactly two possible values. -/
theorem epochView_card (epoch : Nat) :
    Fintype.card (ActiveQueryView (schedule epoch) Bool) = 2 := by
  simpa [schedule] using
    (card_activeQueryView (Answer := Bool) (schedule epoch))

/-- The constant view is genuinely lossy on natural-number evidence. -/
theorem constantView_lossy :
    ¬ Function.Injective (fun _state : Nat => ()) := by
  intro injective
  have impossible : (0 : Nat) = 1 := injective rfl
  omega

/-- No constant permanent context can answer the unfolding one-query epochs,
even though every individual certified context needs only two values. -/
theorem constantView_not_permanentlyComplete :
    ¬ PermanentlyComplete answer schedule (fun _state : Nat => ()) :=
  no_permanently_sufficient_lossy_context scheduleSeparating constantView_lossy

end InfiniteStateCanary

end Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext

#print axioms Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext.activeProjection_is_weakest_sufficient
#print axioms Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext.natCard_activeObservedVariety_eq
#print axioms Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext.no_permanently_sufficient_lossy_context
#print axioms Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext.RecoverableContext.refresh_certified
#print axioms Mettapedia.CognitiveArchitecture.Agent.OpenEndedContext.InfiniteStateCanary.constantView_not_permanentlyComplete
