import Mettapedia.Logic.ConstraintTypes.Semantics
import Mathlib.Order.FixedPoints
import Mathlib.Order.WellFounded
import Mathlib.Data.Set.Lattice

/-!
# Quiescent propagation is independent of wake-up order

Propagators are monotone, contracting functions on an approximation order.
Every finite run retains all common fixed points below its initial state.
Consequently any two quiescent runs from that state have the same result.
Well-founded strict refinement additionally guarantees a quiescent run exists.
None of these hypotheses is asserted across arbitrary program edits.

This is the order-theoretic store/propagator interpretation of deterministic
constraint propagation, not a semantics for effects or committed search.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ConstraintTypes.Saturation

universe u v w

structure Propagator (State : Type u) [PartialOrder State] where
  step : State → State
  monotone : Monotone step
  contracting : ∀ state, step state ≤ state

variable {State : Type u} [PartialOrder State] {Index : Type v}

def run (family : Index → Propagator State) : List Index → State → State
  | [], initial => initial
  | index :: schedule, initial => run family schedule ((family index).step initial)

def Quiescent (family : Index → Propagator State) (state : State) : Prop :=
  ∀ index, (family index).step state = state

theorem run_contracts (family : Index → Propagator State) (schedule : List Index)
    (initial : State) : run family schedule initial ≤ initial := by
  induction schedule generalizing initial with
  | nil => exact le_rfl
  | cons index rest ih => exact le_trans (ih _) ((family index).contracting initial)

/-- Every possible solution at a common fixed point remains below every stage
of a run, independently of its wake-up order or duplicate firings. -/
theorem run_retains_fixed_lower_bounds (family : Index → Propagator State)
    (schedule : List Index) (initial fixed : State)
    (stable : Quiescent family fixed) (below : fixed ≤ initial) :
    fixed ≤ run family schedule initial := by
  induction schedule generalizing initial with
  | nil => exact below
  | cons index rest ih =>
      apply ih _
      calc
        fixed = (family index).step fixed := (stable index).symm
        _ ≤ (family index).step initial := (family index).monotone below

theorem quiescent_result_greatest (family : Index → Propagator State)
    (schedule : List Index) (initial : State)
    (finished : Quiescent family (run family schedule initial)) :
    Quiescent family (run family schedule initial) ∧
      run family schedule initial ≤ initial ∧
      ∀ fixed, Quiescent family fixed → fixed ≤ initial → fixed ≤ run family schedule initial :=
  ⟨finished, run_contracts family schedule initial,
    fun fixed stable below => run_retains_fixed_lower_bounds family schedule initial fixed stable below⟩

/-- General finite-run order independence requires quiescence, not pairwise
commutation of the individual propagators. -/
theorem quiescent_runs_agree (family : Index → Propagator State)
    (left right : List Index) (initial : State)
    (leftFinished : Quiescent family (run family left initial))
    (rightFinished : Quiescent family (run family right initial)) :
    run family left initial = run family right initial := by
  apply le_antisymm
  · exact run_retains_fixed_lower_bounds family right initial _ leftFinished
      (run_contracts family left initial)
  · exact run_retains_fixed_lower_bounds family left initial _ rightFinished
      (run_contracts family right initial)

/-- Finite-height approximation domains are instances. The proof only fires a
rule when it changes the state; it does not assume that unfair arbitrary runs
terminate. -/
theorem exists_quiescent_run
    (refinementWellFounded : WellFounded ((· < ·) : State → State → Prop))
    (family : Index → Propagator State) (initial : State) :
    ∃ schedule, Quiescent family (run family schedule initial) := by
  classical
  refine refinementWellFounded.induction
    (C := fun state => ∃ schedule, Quiescent family (run family schedule state)) initial ?_
  intro initial ih
  by_cases stable : Quiescent family initial
  · exact ⟨[], stable⟩
  · obtain ⟨index, changed⟩ := not_forall.mp stable
    have strict : (family index).step initial < initial :=
      lt_of_le_of_ne ((family index).contracting initial) changed
    obtain ⟨schedule, done⟩ := ih ((family index).step initial) strict
    exact ⟨index :: schedule, done⟩

/-- Flat predicate contracts instantiate the approximation order with sets of
valuations. Simultaneous checks intersect; overload alternatives form a union
inside one such check. -/
def predicatePropagator {Value : Type w} (predicate : Set Value) : Propagator (Set Value) where
  step solutions := solutions ∩ predicate
  monotone _ _ below _ member := ⟨below member.1, member.2⟩
  contracting _ _ member := member.1

theorem predicate_fixed_iff {Value : Type w} (predicate solutions : Set Value) :
    (predicatePropagator predicate).step solutions = solutions ↔ solutions ⊆ predicate := by
  simp [predicatePropagator, Set.inter_eq_left]

/-- Exact solution-set semantics for an arbitrary finite firing sequence. -/
theorem predicate_run_membership {Value : Type w} (predicates : Index → Set Value)
    (schedule : List Index) (initial : Set Value) (value : Value) :
    value ∈ run (fun index => predicatePropagator (predicates index)) schedule initial ↔
      value ∈ initial ∧ ∀ index ∈ schedule, value ∈ predicates index := by
  induction schedule generalizing initial with
  | nil => simp [run]
  | cons index rest ih =>
      rw [run, ih]
      simp only [predicatePropagator, Set.mem_inter_iff, List.mem_cons, forall_eq_or_imp]
      exact ⟨fun ⟨⟨hi, hp⟩, hr⟩ => ⟨hi, hp, hr⟩,
        fun ⟨hi, hp, hr⟩ => ⟨⟨hi, hp⟩, hr⟩⟩

/-- For pure predicates one complete sweep is quiescent even when the value
universe is infinite. No finite-height or termination hypothesis is needed. -/
theorem predicate_complete_sweep {Value : Type w} (predicates : Index → Set Value)
    (schedule : List Index) (covers : ∀ index, index ∈ schedule) (initial : Set Value) :
    Quiescent (fun index => predicatePropagator (predicates index))
      (run (fun index => predicatePropagator (predicates index)) schedule initial) := by
  intro index
  apply (predicate_fixed_iff _ _).2
  intro value accepted
  exact ((predicate_run_membership predicates schedule initial value).1 accepted).2 index (covers index)

end Mettapedia.Logic.ConstraintTypes.Saturation

namespace Mettapedia.Logic.ConstraintTypes.Semantics

theorem hiding_galois_connection {X Y : Type} (map : X → Y) :
    GaloisConnection (image map) (reindex map) :=
  fun source target => image_reindex_adjunction map source target

end Mettapedia.Logic.ConstraintTypes.Semantics

namespace Mettapedia.Logic.ConstraintTypes.Grammar

variable {Q S : Type} {arity : S → Nat}

/-- The standard monotone production operator on sets of grammar states. -/
def productionOperator (grammar : Grammar Q S arity) : Set Q →o Set Q where
  toFun states q := ∃ s fields, fields ∈ grammar.productions q s ∧ ∀ i, states (fields i)
  monotone' _ _ below _ witness := by
    obtain ⟨s, fields, rule, children⟩ := witness
    exact ⟨s, fields, rule, fun i => below (children i)⟩

/-- Constructor inhabitation is the least fixed point of the production
operator, using mathlib's fixed-point construction. -/
theorem productive_eq_lfp (grammar : Grammar Q S arity) :
    {q | grammar.Productive q} = (grammar.productionOperator).lfp := by
  apply le_antisymm
  · apply grammar.productive_least
    intro q s fields rule children
    have generated : grammar.productionOperator grammar.productionOperator.lfp q :=
      ⟨s, fields, rule, children⟩
    rwa [OrderHom.map_lfp] at generated
  · apply OrderHom.lfp_le
    rintro q ⟨s, fields, rule, children⟩
    exact grammar.productive_closed q s fields rule children

end Mettapedia.Logic.ConstraintTypes.Grammar
