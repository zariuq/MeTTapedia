import Mettapedia.MachineLearning.NeuralNetworks.LocalLearning.WeightedGSLTBehavioralAdequacy
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Finite recurrent-class admission for local learning

For a finite support graph, the states visited infinitely often by a fair run
form a reachable bottom strongly connected class.  Consequently, checking that
every reachable bottom class satisfies a behavioral gate is sound for every
fair run.  The converse requires an explicit realizability condition saying
that every reachable bottom class occurs as the recurrent set of some fair
run; under that condition the graph certificate and fair-run reliability are
equivalent.

The fairness condition used by the admission theorem is support fairness:
every supported successor of an infinitely recurring state also recurs
infinitely often.  A stronger edge-fairness condition implies it.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
namespace WeightedGSLTFiniteAdmission

/-- States occurring infinitely often along a run. -/
def infOftenSet {State : Type*} (run : ℕ → State) : Set State :=
  { state | Set.Infinite { n | run n = state } }

/-- An infinite run starts at `initial` and follows the support relation. -/
structure SupportRun {State : Type*} (step : State → State → Prop)
    (initial : State) (run : ℕ → State) : Prop where
  start : run 0 = initial
  follows : ∀ n, step (run n) (run (n + 1))

/-- Fairness at the state-support level. -/
def SupportFair {State : Type*} (step : State → State → Prop)
    (run : ℕ → State) : Prop :=
  ∀ ⦃source target⦄,
    step source target → source ∈ infOftenSet run → target ∈ infOftenSet run

/-- Strong edge fairness: if a source recurs infinitely often, each supported
outgoing edge is taken infinitely often. -/
def EdgeFair {State : Type*} (step : State → State → Prop)
    (run : ℕ → State) : Prop :=
  ∀ ⦃source target⦄,
    step source target →
    Set.Infinite { n | run n = source } →
    Set.Infinite { n | run n = source ∧ run (n + 1) = target }

/-- A bottom class is nonempty, internally strongly connected, and closed
under every supported transition. -/
structure BottomClass {State : Type*} (step : State → State → Prop)
    (carrier : Set State) : Prop where
  nonempty : carrier.Nonempty
  stronglyConnected :
    ∀ ⦃source⦄, source ∈ carrier → ∀ ⦃target⦄, target ∈ carrier →
      Relation.ReflTransGen step source target
  closed : ∀ ⦃source⦄, source ∈ carrier →
    ∀ ⦃target⦄, step source target → target ∈ carrier

def ReachableFrom {State : Type*} (step : State → State → Prop)
    (initial state : State) : Prop :=
  Relation.ReflTransGen step initial state

def ReachableClass {State : Type*} (step : State → State → Prop)
    (initial : State) (carrier : Set State) : Prop :=
  ∃ state, state ∈ carrier ∧ ReachableFrom step initial state

/-- All recurrent behavior satisfies `good`.  Transient states are deliberately
irrelevant to this stable-success predicate. -/
def RecurrentlySatisfies {State : Type*} (good : State → Prop)
    (run : ℕ → State) : Prop :=
  ∀ ⦃state⦄, state ∈ infOftenSet run → good state

/-- Reliability over every support-fair run. -/
def FairlyReliable {State : Type*} (step : State → State → Prop)
    (initial : State) (good : State → Prop) : Prop :=
  ∀ run, SupportRun step initial run → SupportFair step run →
    RecurrentlySatisfies good run

/-- The finite graph admission condition. -/
def BottomAdmissible {State : Type*} (step : State → State → Prop)
    (initial : State) (good : State → Prop) : Prop :=
  ∀ carrier, BottomClass step carrier → ReachableClass step initial carrier →
    ∀ ⦃state⦄, state ∈ carrier → good state

/-- Completeness requires each reachable bottom class to be realizable as the
recurrent set of a fair run. -/
def BottomRealizable {State : Type*} (step : State → State → Prop)
    (initial : State) : Prop :=
  ∀ carrier, BottomClass step carrier → ReachableClass step initial carrier →
    ∃ run, SupportRun step initial run ∧ SupportFair step run ∧
      infOftenSet run = carrier

theorem edgeFair_supportFair {State : Type*} {step : State → State → Prop}
    {run : ℕ → State} (hfair : EdgeFair step run) : SupportFair step run := by
  intro source target hstep hsource
  change Set.Infinite { n | run n = source } at hsource
  have hedge : Set.Infinite { n | run n = source ∧ run (n + 1) = target } :=
    hfair hstep hsource
  have himage : Set.Infinite (Nat.succ '' { n | run n = source ∧ run (n + 1) = target }) :=
    hedge.image Nat.succ_injective.injOn
  change Set.Infinite { n | run n = target }
  refine himage.mono ?_
  intro index hindex
  rcases hindex with ⟨n, hn, rfl⟩
  exact hn.2

theorem run_reachable_of_le {State : Type*} {step : State → State → Prop}
    {run : ℕ → State} (hfollows : ∀ n, step (run n) (run (n + 1)))
    {m n : ℕ} (hmn : m ≤ n) :
    Relation.ReflTransGen step (run m) (run n) := by
  induction n, hmn using Nat.le_induction with
  | base => exact Relation.ReflTransGen.refl
  | succ n _ ih =>
      exact Relation.ReflTransGen.tail ih (hfollows n)

theorem infOftenSet_nonempty {State : Type*} [Finite State]
    (run : ℕ → State) : (infOftenSet run).Nonempty := by
  obtain ⟨state, hstate⟩ := Finite.exists_infinite_fiber run
  refine ⟨state, ?_⟩
  change Set.Infinite { n | run n = state }
  have hfiber : run ⁻¹' ({state} : Set State) = { n | run n = state } := by
    ext n
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [hfiber] at hstate
  exact Set.infinite_coe_iff.mp hstate

theorem infOften_reachable {State : Type*} {step : State → State → Prop}
    {run : ℕ → State} (hfollows : ∀ n, step (run n) (run (n + 1)))
    {source target : State}
    (hsource : source ∈ infOftenSet run) (htarget : target ∈ infOftenSet run) :
    Relation.ReflTransGen step source target := by
  change Set.Infinite { n | run n = source } at hsource
  change Set.Infinite { n | run n = target } at htarget
  rcases hsource.nonempty with ⟨m, hm⟩
  rcases htarget.exists_gt m with ⟨n, hn, hmn⟩
  have hreach := run_reachable_of_le hfollows (Nat.le_of_lt hmn)
  change run m = source at hm
  change run n = target at hn
  simpa only [hm, hn] using hreach

theorem infOften_is_bottomClass {State : Type*} [Finite State]
    {step : State → State → Prop} {run : ℕ → State}
    (hrun : ∀ n, step (run n) (run (n + 1)))
    (hfair : SupportFair step run) :
    BottomClass step (infOftenSet run) := by
  refine ⟨infOftenSet_nonempty run, ?_, ?_⟩
  · intro source hsource target htarget
    exact infOften_reachable hrun hsource htarget
  · intro source hsource target hstep
    exact hfair hstep hsource

theorem infOften_is_reachableClass {State : Type*} [Finite State]
    {step : State → State → Prop} {initial : State} {run : ℕ → State}
    (hrun : SupportRun step initial run) :
    ReachableClass step initial (infOftenSet run) := by
  rcases infOftenSet_nonempty run with ⟨state, hstate⟩
  change Set.Infinite { n | run n = state } at hstate
  rcases hstate.nonempty with ⟨n, hn⟩
  refine ⟨state, ?_, ?_⟩
  · change Set.Infinite { m | run m = state }
    exact hstate
  · have hreach := run_reachable_of_le hrun.follows (Nat.zero_le n)
    change run n = state at hn
    change Relation.ReflTransGen step initial state
    simpa only [hrun.start, hn] using hreach

/-- Checking every reachable bottom class is sound for all support-fair runs. -/
theorem bottomAdmissible_implies_fairlyReliable {State : Type*} [Finite State]
    {step : State → State → Prop} {initial : State} {good : State → Prop}
    (hadmit : BottomAdmissible step initial good) :
    FairlyReliable step initial good := by
  intro run hrun hfair state hstate
  exact hadmit (infOftenSet run)
    (infOften_is_bottomClass hrun.follows hfair)
    (infOften_is_reachableClass hrun) hstate

/-- With explicit bottom-class realizability, the finite graph admission test
is also complete. -/
theorem bottomAdmissible_iff_fairlyReliable_of_realizable
    {State : Type*} [Finite State]
    {step : State → State → Prop} {initial : State} {good : State → Prop}
    (hrealizable : BottomRealizable step initial) :
    BottomAdmissible step initial good ↔ FairlyReliable step initial good := by
  constructor
  · exact bottomAdmissible_implies_fairlyReliable
  · intro hreliable carrier hbottom hreachable state hstate
    rcases hrealizable carrier hbottom hreachable with
      ⟨run, hrun, hfair, hlimit⟩
    have hstable := hreliable run hrun hfair
    apply hstable
    rw [hlimit]
    exact hstate

/-! ## Positive and negative finite examples -/

inductive BranchState where
  | start
  | good
  | bad
deriving DecidableEq, Fintype

inductive BranchStep : BranchState → BranchState → Prop where
  | toGood : BranchStep .start .good
  | toBad : BranchStep .start .bad
  | stayGood : BranchStep .good .good
  | stayBad : BranchStep .bad .bad

theorem BranchStep.reachable_from_good_eq_good {target : BranchState}
    (hreach : Relation.ReflTransGen BranchStep .good target) : target = .good := by
  induction hreach with
  | refl => rfl
  | tail _ last ih =>
      subst_vars
      cases last
      rfl

def badClass : Set BranchState := {BranchState.bad}

theorem badClass_bottom : BottomClass BranchStep badClass := by
  refine ⟨⟨.bad, rfl⟩, ?_, ?_⟩
  · intro source hsource target htarget
    simp only [badClass, Set.mem_singleton_iff] at hsource htarget
    subst source
    subst target
    exact Relation.ReflTransGen.refl
  · intro source hsource target hstep
    simp only [badClass, Set.mem_singleton_iff] at hsource ⊢
    subst source
    cases hstep
    rfl

theorem badClass_reachable : ReachableClass BranchStep .start badClass := by
  exact ⟨.bad, rfl, Relation.ReflTransGen.single BranchStep.toBad⟩

def goodOnly : BranchState → Prop := fun state => state = .good

/-- Negative example: the reachable bad sink defeats the bottom-class gate. -/
theorem branch_not_bottomAdmissible :
    ¬ BottomAdmissible BranchStep .start goodOnly := by
  intro hadmit
  have hgood := hadmit badClass badClass_bottom badClass_reachable
    (state := BranchState.bad) rfl
  cases hgood

/-- Positive example: accepting both recurrent sinks makes every reachable
bottom class good, while the transient start state need not be accepted. -/
def recurrentSink : BranchState → Prop
  | .start => False
  | .good => True
  | .bad => True

theorem branch_bottomAdmissible_recurrentSinks :
    BottomAdmissible BranchStep .start recurrentSink := by
  intro carrier hbottom _ state hstate
  cases state with
  | start =>
      have hclosedGood := hbottom.closed hstate BranchStep.toGood
      have hclosedBad := hbottom.closed hstate BranchStep.toBad
      have hreach := hbottom.stronglyConnected hclosedGood hclosedBad
      have himpossible := BranchStep.reachable_from_good_eq_good hreach
      cases himpossible
  | good => trivial
  | bad => trivial

#print axioms edgeFair_supportFair
#print axioms infOften_is_bottomClass
#print axioms infOften_is_reachableClass
#print axioms bottomAdmissible_implies_fairlyReliable
#print axioms bottomAdmissible_iff_fairlyReliable_of_realizable
#print axioms branch_not_bottomAdmissible
#print axioms branch_bottomAdmissible_recurrentSinks

end WeightedGSLTFiniteAdmission
end Mettapedia.MachineLearning.NeuralNetworks.LocalLearning
