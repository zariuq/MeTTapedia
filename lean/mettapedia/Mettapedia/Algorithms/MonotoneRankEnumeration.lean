import Mettapedia.GSLT.Core.BoundedPublication
import Mathlib.Data.List.Dedup
import Mettapedia.Machines.ResumableRegion

/-!
# Lazy enumeration of monotone rank graphs

Only root candidates are admitted initially.  Popping a minimum admits its
previously unseen immediate neighbors.  This is the rank-vector mechanism
used for lazy Cartesian derivation extraction: different paths to the same
rank vector are one candidate, while different vectors and edge identities
remain distinct derivations.

The source is independently defined graph reachability.  The algorithm does
not enumerate that source before selecting its first result.  A local cost
law proves each published rank minimum among every remaining source rank.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.MonotoneRankEnumeration

open Mettapedia.GSLT.Core.BranchingTemporal

variable {Node : Type} [DecidableEq Node]

structure Graph (Node : Type*) where
  neighbors : Node → List Node
  cost : Node → Nat

def Graph.system (graph : Graph Node) : BranchingSystem Node Node :=
  ⟨some, graph.neighbors⟩

def Source (graph : Graph Node) (roots : List Node) (node : Node) : Prop :=
  Generated graph.system roots node

def Monotone (graph : Graph Node) : Prop :=
  ∀ parent child, child ∈ graph.neighbors parent → graph.cost parent ≤ graph.cost child

structure State (Node : Type*) where
  published : List Node
  frontier : List Node
  deriving Repr, DecidableEq

def admitted (state : State Node) : List Node := state.published ++ state.frontier

def initial (roots : List Node) : State Node := ⟨[], roots.dedup⟩

def fresh (graph : Graph Node) (state : State Node) (node : Node) : List Node :=
  ((graph.neighbors node).filter (fun child => decide (child ∉ admitted state))).dedup

def consume (graph : Graph Node) (state : State Node) (node : Node) : State Node :=
  ⟨state.published ++ [node], state.frontier.erase node ++ fresh graph state node⟩

def tick (graph : Graph Node) (state : State Node) : State Node :=
  match CertifiedFiniteChoice.chooseBest (fun node => -(graph.cost node : Rat)) state.frontier with
  | none => state
  | some node => consume graph state node

def run (graph : Graph Node) : Nat → State Node → State Node
  | 0, state => state
  | fuel + 1, state => tick graph (run graph fuel state)

theorem run_add (graph : Graph Node) (first second : Nat) (state : State Node) :
    run graph (first + second) state = run graph second (run graph first state) := by
  induction second with
  | zero => simp [run]
  | succ second ih => simp [run, ih]

theorem tick_closed (graph : Graph Node) (state : State Node)
    (closed : state.frontier = []) : tick graph state = state := by
  simp [tick, closed, CertifiedFiniteChoice.chooseBest]

theorem tick_publishes_one (graph : Graph Node) (state : State Node)
    (live : state.frontier ≠ []) :
    (tick graph state).published.length = state.published.length + 1 := by
  cases selected : CertifiedFiniteChoice.chooseBest
      (fun node => -(graph.cost node : Rat)) state.frontier with
  | none =>
      exact False.elim (live ((CertifiedFiniteChoice.chooseBest_eq_none_iff _ _).mp selected))
  | some node => simp [tick, selected, consume]

/-- Demand is a stopping predicate on the same retained rank state. -/
def demandMachine (graph : Graph Node) (requested : Nat) :
    Mettapedia.Machines.MachineCore (List Node) where
  State := State Node
  load := initial
  step state := if state.published.length < requested ∧ state.frontier ≠ []
    then some (tick graph state) else none

theorem demand_pause_resume (graph : Graph Node) (requested first second : Nat)
    (state : State Node) :
    (demandMachine graph requested).runSlice (first + second) state =
      let earlier := (demandMachine graph requested).runSlice first state
      let later := (demandMachine graph requested).runSlice second earlier.1
      (later.1, earlier.2 + later.2) :=
  Mettapedia.Machines.MachineCore.runSlice_add (demandMachine graph requested)
    first second state

theorem demand_is_prefix (graph : Graph Node) (requested fuel : Nat) (state : State Node) :
    (demandMachine graph requested).runSlice fuel state =
      (run graph ((demandMachine graph requested).runSlice fuel state).2 state,
        ((demandMachine graph requested).runSlice fuel state).2) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases progresses : state.published.length < requested ∧ state.frontier ≠ []
      · simp only [Mettapedia.Machines.MachineCore.runSlice, demandMachine, if_pos progresses]
        have projection := congrArg Prod.fst (ih (tick graph state))
        simp only at projection
        apply Prod.ext
        · change ((demandMachine graph requested).runSlice fuel (tick graph state)).1 =
            run graph (((demandMachine graph requested).runSlice fuel (tick graph state)).2 + 1)
              state
          rw [projection]
          rw [Nat.add_comm, run_add]
          rfl
        · rfl
      · simp [Mettapedia.Machines.MachineCore.runSlice, demandMachine, progresses, run]

theorem demand_no_overshoot (graph : Graph Node) (requested fuel : Nat) (state : State Node)
    (within : state.published.length ≤ requested) :
    ((demandMachine graph requested).runSlice fuel state).1.published.length ≤ requested := by
  induction fuel generalizing state with
  | zero => exact within
  | succ fuel ih =>
      by_cases progresses : state.published.length < requested ∧ state.frontier ≠ []
      · simp only [Mettapedia.Machines.MachineCore.runSlice, demandMachine, if_pos progresses]
        apply ih
        rw [tick_publishes_one graph state progresses.2]
        omega
      · simpa [Mettapedia.Machines.MachineCore.runSlice, demandMachine, progresses] using within

/-- One successful rank step publishes one candidate. An allowance of k
therefore suffices for a fresh k-prefix, without computing the cardinality of
the whole independent source. -/
theorem demand_allowance_suffices (graph : Graph Node) (requested fuel : Nat)
    (state : State Node) (within : state.published.length ≤ requested)
    (enough : requested ≤ state.published.length + fuel) :
    ((demandMachine graph requested).runSlice fuel state).1.published.length = requested ∨
      ((demandMachine graph requested).runSlice fuel state).1.frontier = [] := by
  induction fuel generalizing state with
  | zero => left; change state.published.length = requested; omega
  | succ fuel ih =>
      by_cases progresses : state.published.length < requested ∧ state.frontier ≠ []
      · simp only [Mettapedia.Machines.MachineCore.runSlice, demandMachine,
          if_pos progresses]
        have count := tick_publishes_one graph state progresses.2
        apply ih
        · omega
        · omega
      · have stopped : (demandMachine graph requested).runSlice (fuel + 1) state =
            (state, 0) := by
          simp [Mettapedia.Machines.MachineCore.runSlice, demandMachine, progresses]
        rw [stopped]
        by_cases live : state.frontier = []
        · exact Or.inr live
        · left
          have fulfilled : requested ≤ state.published.length := by
            by_contra smaller
            exact progresses ⟨by omega, live⟩
          exact Nat.le_antisymm within fulfilled

/-- A live, unsatisfied residual has spent its whole allowance.  The stopped
case cannot conceal either closure or a satisfied request. -/
theorem demand_open_unsatisfied_spent (graph : Graph Node) (requested fuel : Nat)
    (state : State Node)
    (live : ((demandMachine graph requested).runSlice fuel state).1.frontier ≠ [])
    (unsatisfied : ((demandMachine graph requested).runSlice fuel state).1.published.length <
      requested) :
    ((demandMachine graph requested).runSlice fuel state).2 = fuel := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      by_cases progresses : state.published.length < requested ∧ state.frontier ≠ []
      · simp only [Mettapedia.Machines.MachineCore.runSlice, demandMachine,
          if_pos progresses] at live unsatisfied ⊢
        have earlier := ih (tick graph state) live unsatisfied
        change ((demandMachine graph requested).runSlice fuel (tick graph state)).2 + 1 = _
        omega
      · have stopped : (demandMachine graph requested).runSlice (fuel + 1) state =
            (state, 0) := by
          simp [Mettapedia.Machines.MachineCore.runSlice, demandMachine, progresses]
        rw [stopped] at live unsatisfied
        exact False.elim (progresses ⟨unsatisfied, live⟩)

structure Invariant (graph : Graph Node) (roots : List Node) (state : State Node) : Prop where
  distinct : (admitted state).Nodup
  sound : ∀ node ∈ admitted state, Source graph roots node
  roots : ∀ node ∈ roots, node ∈ admitted state
  processed : ∀ parent ∈ state.published, ∀ child ∈ graph.neighbors parent,
    child ∈ admitted state

theorem initial_invariant (graph : Graph Node) (roots : List Node) :
    Invariant graph roots (initial roots) := by
  constructor
  · simpa only [admitted, initial, List.nil_append] using List.nodup_dedup roots
  · intro node member
    exact .root (by simpa [admitted, initial] using member)
  · intro node member
    simpa [admitted, initial] using member
  · simp [initial]

theorem mem_fresh (graph : Graph Node) (state : State Node) (node child : Node) :
    child ∈ fresh graph state node ↔
      child ∈ graph.neighbors node ∧ child ∉ admitted state := by
  simp [fresh]

theorem consume_admitted_perm (graph : Graph Node) (state : State Node) (node : Node)
    (member : node ∈ state.frontier) :
    (admitted (consume graph state node)).Perm
      (admitted state ++ fresh graph state node) := by
  simpa [consume, admitted, List.append_assoc] using
    ((List.perm_cons_erase member).symm.append_left state.published).append_right
      (fresh graph state node)

theorem mem_consume_admitted (graph : Graph Node) (state : State Node) (node child : Node)
    (member : node ∈ state.frontier) :
    child ∈ admitted (consume graph state node) ↔
      child ∈ admitted state ∨ child ∈ graph.neighbors node := by
  rw [(consume_admitted_perm graph state node member).mem_iff]
  simp only [List.mem_append, mem_fresh]
  tauto

theorem consume_invariant (graph : Graph Node) (roots : List Node) (state : State Node)
    (valid : Invariant graph roots state) (node : Node) (member : node ∈ state.frontier) :
    Invariant graph roots (consume graph state node) := by
  have source : Source graph roots node := valid.sound node
    (List.mem_append.mpr (Or.inr member))
  constructor
  · apply (consume_admitted_perm graph state node member).nodup_iff.mpr
    apply List.nodup_append.mpr
    refine ⟨valid.distinct, List.nodup_dedup _, ?_⟩
    intro old oldMember new newMember equal
    have absent := (mem_fresh graph state node new).mp newMember
    exact absent.2 (equal ▸ oldMember)
  · intro child included
    rcases (mem_consume_admitted graph state node child member).mp included with old | next
    · exact valid.sound child old
    · exact .successor source next
  · intro root included
    exact (mem_consume_admitted graph state node root member).mpr
      (Or.inl (valid.roots root included))
  · intro parent included child neighbor
    have casesPublished : parent ∈ state.published ∨ parent = node := by
      simpa [consume] using included
    apply (mem_consume_admitted graph state node child member).mpr
    rcases casesPublished with prior | same
    · exact Or.inl (valid.processed parent prior child neighbor)
    · exact Or.inr (same ▸ neighbor)

theorem tick_invariant (graph : Graph Node) (roots : List Node) (state : State Node)
    (valid : Invariant graph roots state) : Invariant graph roots (tick graph state) := by
  cases selected : CertifiedFiniteChoice.chooseBest
      (fun node => -(graph.cost node : Rat)) state.frontier with
  | none => simpa [tick, selected] using valid
  | some node =>
      have member := (CertifiedFiniteChoice.chooseBest_correct _ _ node selected).1
      simpa [tick, selected] using consume_invariant graph roots state valid node member

theorem run_invariant (graph : Graph Node) (roots : List Node) (fuel : Nat)
    (state : State Node) (valid : Invariant graph roots state) :
    Invariant graph roots (run graph fuel state) := by
  induction fuel with
  | zero => exact valid
  | succ fuel ih => exact tick_invariant graph roots _ ih

omit [DecidableEq Node] in
theorem published_bound (graph : Graph Node) (roots : List Node) (state : State Node)
    (valid : Invariant graph roots state) (domain : Finset Node)
    (bounded : ∀ node, Source graph roots node → node ∈ domain) :
    state.published.length ≤ domain.card := by
  have included : ∀ node ∈ admitted state, node ∈ domain.toList := by
    intro node member
    exact Finset.mem_toList.mpr (bounded node (valid.sound node member))
  have lengthBound := valid.distinct.length_le_of_subset included
  have firstLength : state.published.length ≤ (admitted state).length := by
    simp [admitted]
  exact firstLength.trans (by simpa using lengthBound)

theorem open_run_spent (graph : Graph Node) (fuel : Nat) (state : State Node)
    (live : (run graph fuel state).frontier ≠ []) :
    fuel + state.published.length ≤ (run graph fuel state).published.length := by
  induction fuel with
  | zero => simp [run]
  | succ fuel ih =>
      have priorLive : (run graph fuel state).frontier ≠ [] := by
        intro closed
        exact live (by simpa [run, tick_closed graph _ closed] using closed)
      have earlier := ih priorLive
      change _ ≤ (tick graph (run graph fuel state)).published.length
      rw [tick_publishes_one graph _ priorLive]
      omega

/-- A finite source domain suffices for exhaustion.  The domain is only a
proof bound: the implementation never puts its complete list in the queue. -/
theorem finite_exhaustion (graph : Graph Node) (roots : List Node) (domain : Finset Node)
    (bounded : ∀ node, Source graph roots node → node ∈ domain) :
    (run graph (domain.card + 1) (initial roots)).frontier = [] := by
  by_contra live
  have spent := open_run_spent graph (domain.card + 1) (initial roots) live
  have boundedPublished := published_bound graph roots _
    (run_invariant graph roots (domain.card + 1) _ (initial_invariant graph roots)) domain bounded
  change domain.card + 1 + 0 ≤
    (run graph (domain.card + 1) (initial roots)).published.length at spent
  omega

/-- Finite demand returns enough witnesses or a genuinely closed source.
The complete domain is a proof bound, never a prefilled frontier. -/
theorem finite_demand_stops (graph : Graph Node) (roots : List Node)
    (domain : Finset Node) (bounded : ∀ node, Source graph roots node → node ∈ domain)
    (requested : Nat) :
    let result := ((demandMachine graph requested).runSlice (domain.card + 1)
      (initial roots)).1
    result.published.length = requested ∨ result.frontier = [] := by
  intro result
  by_cases closed : result.frontier = []
  · exact Or.inr closed
  · left
    have within := demand_no_overshoot graph requested (domain.card + 1)
      (initial roots) (by simp [initial])
    change result.published.length ≤ requested at within
    by_contra different
    have unsatisfied : result.published.length < requested := by omega
    have spent := demand_open_unsatisfied_spent graph requested (domain.card + 1)
      (initial roots) closed unsatisfied
    have projection := congrArg Prod.fst
      (demand_is_prefix graph requested (domain.card + 1) (initial roots))
    rw [spent] at projection
    change result = run graph (domain.card + 1) (initial roots) at projection
    apply closed
    rw [projection]
    exact finite_exhaustion graph roots domain bounded

omit [DecidableEq Node] in
/-- Every unobserved source rank has an admitted predecessor no more costly
than itself.  This is a consequence of actual neighbor admission. -/
theorem frontier_lower_bound (graph : Graph Node) (monotone : Monotone graph)
    (roots : List Node) (state : State Node) (valid : Invariant graph roots state)
    {node : Node} (source : Source graph roots node) :
    node ∈ state.published ∨
      ∃ ancestor ∈ state.frontier, graph.cost ancestor ≤ graph.cost node := by
  induction source with
  | @root node member =>
      rcases List.mem_append.mp (valid.roots node member) with published | frontier
      · exact Or.inl published
      · exact Or.inr ⟨node, frontier, le_rfl⟩
  | @successor parent child previous next ih =>
      rcases ih with published | ⟨ancestor, frontier, bound⟩
      · rcases List.mem_append.mp (valid.processed parent published child next) with
          publishedChild | frontierChild
        · exact Or.inl publishedChild
        · exact Or.inr ⟨child, frontierChild, le_rfl⟩
      · exact Or.inr ⟨ancestor, frontier, bound.trans (monotone parent child next)⟩

omit [DecidableEq Node] in
theorem selected_minimum (graph : Graph Node) (monotone : Monotone graph)
    (roots : List Node) (state : State Node) (valid : Invariant graph roots state)
    (node : Node) (selected : CertifiedFiniteChoice.chooseBest
      (fun node => -(graph.cost node : Rat)) state.frontier = some node) :
    Source graph roots node ∧ node ∉ state.published ∧
      ∀ other, Source graph roots other → other ∉ state.published →
        graph.cost node ≤ graph.cost other := by
  obtain ⟨member, minimal⟩ := CertifiedFiniteChoice.chooseBest_correct _ _ node selected
  have separation := (List.nodup_append.mp valid.distinct).2.2
  refine ⟨valid.sound node (List.mem_append.mpr (Or.inr member)), ?_, ?_⟩
  · intro published
    exact separation node published node member rfl
  · intro other source remaining
    rcases frontier_lower_bound graph monotone roots state valid source with
      published | ⟨ancestor, frontier, bound⟩
    · exact False.elim (remaining published)
    · have comparison := minimal ancestor frontier
      have rational : (graph.cost node : Rat) ≤ graph.cost ancestor := by linarith
      exact (by exact_mod_cast rational : graph.cost node ≤ graph.cost ancestor).trans bound

def BestPrefix (graph : Graph Node) (roots : List Node) (published : List Node) : Prop :=
  published.Pairwise (fun first second => graph.cost first ≤ graph.cost second) ∧
    ∀ first ∈ published, ∀ other, Source graph roots other → other ∉ published →
      graph.cost first ≤ graph.cost other

theorem initial_best (graph : Graph Node) (roots : List Node) :
    BestPrefix graph roots (initial roots).published := by simp [BestPrefix, initial]

theorem tick_best (graph : Graph Node) (monotone : Monotone graph) (roots : List Node)
    (state : State Node) (valid : Invariant graph roots state)
    (best : BestPrefix graph roots state.published) :
    BestPrefix graph roots (tick graph state).published := by
  cases selected : CertifiedFiniteChoice.chooseBest
      (fun node => -(graph.cost node : Rat)) state.frontier with
  | none => simpa [tick, selected] using best
  | some node =>
      obtain ⟨source, absent, minimal⟩ :=
        selected_minimum graph monotone roots state valid node selected
      simp only [tick, selected, consume, BestPrefix, List.pairwise_append,
        List.pairwise_singleton, List.mem_singleton, true_and]
      refine ⟨⟨best.1, ?_⟩, ?_⟩
      · intro old member chosen equal
        subst chosen
        exact best.2 old member node source absent
      · intro answer member other otherSource remaining
        have oldRemaining : other ∉ state.published := by
          intro prior
          exact remaining (List.mem_append.mpr (Or.inl prior))
        rcases List.mem_append.mp member with old | latest
        · exact best.2 answer old other otherSource oldRemaining
        · have equal : answer = node := by simpa using latest
          subst answer
          exact minimal other otherSource oldRemaining

theorem run_best (graph : Graph Node) (monotone : Monotone graph) (roots : List Node)
    (fuel : Nat) : BestPrefix graph roots (run graph fuel (initial roots)).published := by
  induction fuel with
  | zero => exact initial_best graph roots
  | succ fuel ih =>
      exact tick_best graph monotone roots _
        (run_invariant graph roots fuel _ (initial_invariant graph roots)) ih

/-- Best-first is fair when the actual source occurrences below each cost
are finite.  Finite keys alone would not provide this occurrence bound. -/
theorem finite_sublevel_reached (graph : Graph Node) (monotone : Monotone graph)
    (roots : List Node) (target : Node) (source : Source graph roots target)
    (domain : Finset Node)
    (bounded : ∀ node, Source graph roots node → graph.cost node ≤ graph.cost target →
      node ∈ domain) :
    target ∈ (run graph (domain.card + 1) (initial roots)).published := by
  let result := run graph (domain.card + 1) (initial roots)
  have valid := run_invariant graph roots (domain.card + 1) (initial roots)
    (initial_invariant graph roots)
  have best := run_best graph monotone roots (domain.card + 1)
  by_contra absent
  have live : result.frontier ≠ [] := by
    intro closed
    rcases frontier_lower_bound graph monotone roots result valid source with
      present | ⟨ancestor, member, _⟩
    · exact absent present
    · simp [closed] at member
  have included : ∀ node ∈ result.published, node ∈ domain.toList := by
    intro node member
    exact Finset.mem_toList.mpr (bounded node
      (valid.sound node (List.mem_append.mpr (Or.inl member)))
      (best.2 node member target source absent))
  have lengthBound := (List.nodup_append.mp valid.distinct).1.length_le_of_subset included
  have spent := open_run_spent graph (domain.card + 1) (initial roots) live
  change domain.card + 1 + 0 ≤ result.published.length at spent
  have finiteLength : result.published.length ≤ domain.card := by
    simpa only [Finset.length_toList] using lengthBound
  omega

omit [DecidableEq Node] in
/-- Closure certifies the complete source rank family, independent of costs. -/
theorem closed_complete (graph : Graph Node) (monotone : Monotone graph)
    (roots : List Node) (state : State Node) (valid : Invariant graph roots state)
    (closed : state.frontier = []) (node : Node) :
    node ∈ state.published ↔ Source graph roots node := by
  constructor
  · intro member
    exact valid.sound node (List.mem_append.mpr (Or.inl member))
  · intro source
    rcases frontier_lower_bound graph monotone roots state valid source with
      published | ⟨ancestor, frontier, _⟩
    · exact published
    · simp [closed] at frontier

namespace Controls

def diamond : Graph Nat where
  neighbors
    | 0 => [1, 2]
    | 1 => [3]
    | 2 => [3]
    | _ => []
  cost := id

theorem diamond_monotone : Monotone diamond := by
  intro parent child member
  rcases parent with _ | _ | _ | parent <;> simp_all [diamond]

example : (run diamond 4 (initial [0])).published = [0, 1, 2, 3] := by decide
example : (run diamond 4 (initial [0])).frontier = [] := by decide

/-- A cheaper descendant violates the needed local law. -/
def nonmonotone : Graph Nat where
  neighbors
    | 0 => [1]
    | _ => []
  cost
    | 0 => 8
    | _ => 2

example : ¬ Monotone nonmonotone := by
  intro monotone
  have impossible := monotone 0 1 (by simp [nonmonotone])
  simp [nonmonotone] at impossible

end Controls

end Mettapedia.Algorithms.MonotoneRankEnumeration
