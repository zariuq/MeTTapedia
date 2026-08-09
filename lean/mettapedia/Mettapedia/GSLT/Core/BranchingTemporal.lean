import Mettapedia.GSLT.Core.GSLT
import Mathlib.Data.Multiset.AddSub
import Mathlib.Tactic

/-!
# Branching processes, scheduler streams, and finite shadows

A nondeterministic process and a stream of its observations are different
objects.  `BranchingSystem` presents the branching coalgebra.  `Scheduler`
chooses a linear traversal without changing the live frontier.  `Snapshot`
records the finite stream prefix and the still-live frontier.

The central invariant is `account_tick`: whenever a branching system admits an
additive completed denotation, one scheduler step preserves the sum of answers
already emitted and answers still latent in the frontier.  Consequently all
completed scheduler runs agree at bag level even when their streams disagree.

The file also separates two infinitary phenomena.

* A fair scheduler eventually emits every reachable answer
  (`fair_emits_reachable`).
* A legal depth-first scheduler can starve an answer behind a silent loop
  (`depthFirst_starves_answer`).

Finally, `no_finite_denotation_productiveLoop` proves that a productive infinite
stream has no finite multiset denotation satisfying the additive unfolding law.
This is the precise boundary between a resumable temporal observation and a
completed finite answer shadow.
-/

namespace Mettapedia.GSLT.Core.BranchingTemporal

/-! ## A finitely presented branching coalgebra -/

/-- One node may emit at most one answer and expose finitely many successor
nodes.  Cycles are allowed, so the generated process may still be infinite. -/
structure BranchingSystem (Node Answer : Type*) where
  emit : Node → Option Answer
  successors : Node → List Node

/-- A scheduler has two independent choices: it may reorder the current
frontier before selecting its head, and it may interleave generated successors
with the pending frontier.  Both operations preserve occurrences exactly. -/
structure Scheduler (Node : Type*) where
  reorder : List Node → List Node
  reorder_complete : ∀ frontier, (reorder frontier).Perm frontier
  integrate : List Node → List Node → List Node
  integrate_complete : ∀ pending generated,
    (integrate pending generated).Perm (pending ++ generated)

namespace Scheduler

variable {Node : Type*}

def breadthFirst : Scheduler Node where
  reorder frontier := frontier
  reorder_complete _ := .refl _
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := .refl _

def depthFirst : Scheduler Node where
  reorder frontier := frontier
  reorder_complete _ := .refl _
  integrate pending generated := generated ++ pending
  integrate_complete _ _ := List.perm_append_comm

def reverseBreadthFirst : Scheduler Node where
  reorder frontier := frontier.reverse
  reorder_complete frontier := frontier.reverse_perm
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := .refl _

theorem mem_reorder_iff (scheduler : Scheduler Node)
    {frontier : List Node} {node : Node} :
    node ∈ scheduler.reorder frontier ↔ node ∈ frontier :=
  (scheduler.reorder_complete frontier).mem_iff

theorem mem_integrate_iff (scheduler : Scheduler Node)
    {pending generated : List Node} {node : Node} :
    node ∈ scheduler.integrate pending generated ↔
      node ∈ pending ∨ node ∈ generated := by
  rw [(scheduler.integrate_complete pending generated).mem_iff]
  simp

end Scheduler

/-- One occurrence in the linear observation stream, retaining its producing
node rather than confusing stream position with semantic origin. -/
structure Emission (Node Answer : Type*) where
  origin : Node
  value : Answer
deriving DecidableEq, Repr

/-- A finite observation consists of what has been emitted and what remains
live.  An empty frontier is completion; a nonempty frontier is an open run. -/
structure Snapshot (Node Answer : Type*) where
  events : List (Emission Node Answer)
  frontier : List Node
deriving DecidableEq, Repr

def initial {Node Answer : Type*} (roots : List Node) : Snapshot Node Answer :=
  ⟨[], roots⟩

def selected {Node : Type*} (scheduler : Scheduler Node)
    (frontier : List Node) : Option Node :=
  (scheduler.reorder frontier).head?

private def eventFor {Node Answer : Type*} (node : Node) :
    Option Answer → List (Emission Node Answer)
  | none => []
  | some answer => [⟨node, answer⟩]

/-- One temporal step: select one live node, append its possible event, and
replace it by its successors.  Exhausted snapshots remain unchanged. -/
def tick {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (snapshot : Snapshot Node Answer) :
    Snapshot Node Answer :=
  match scheduler.reorder snapshot.frontier with
  | [] => snapshot
  | node :: pending =>
      { events := snapshot.events ++ eventFor node (system.emit node)
        frontier := scheduler.integrate pending (system.successors node) }

/-- Observe `fuel` scheduler steps. -/
def run {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) : Nat → Snapshot Node Answer → Snapshot Node Answer
  | 0, snapshot => snapshot
  | fuel + 1, snapshot => tick system scheduler (run system scheduler fuel snapshot)

theorem events_prefix_tick {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) :
    snapshot.events.IsPrefix (tick system scheduler snapshot).events := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simp [tick, ordered]
  | cons node pending =>
      cases emitted : system.emit node with
      | none => simp [tick, ordered, emitted]
      | some answer => simp [tick, ordered, emitted, eventFor]

/-- Resumption only extends the event stream; it never rewrites an earlier
prefix. -/
theorem events_prefix_run {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (fuel : Nat) (snapshot : Snapshot Node Answer) :
    snapshot.events.IsPrefix (run system scheduler fuel snapshot).events := by
  induction fuel with
  | zero => exact List.prefix_rfl
  | succ fuel ih =>
      exact ih.trans (events_prefix_tick system scheduler _)

private theorem reorder_nil {Node : Type*} (scheduler : Scheduler Node) :
    scheduler.reorder [] = [] := by
  have lengthZero : (scheduler.reorder []).length = 0 := by
    simpa using (scheduler.reorder_complete []).length_eq
  exact List.length_eq_zero_iff.mp lengthZero

theorem tick_eq_self_of_frontier_nil {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) (empty : snapshot.frontier = []) :
    tick system scheduler snapshot = snapshot := by
  have reordered : scheduler.reorder snapshot.frontier = [] := by
    rw [empty, reorder_nil]
  simp [tick, reordered]

theorem run_eq_self_of_frontier_nil {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) (empty : snapshot.frontier = [])
    (fuel : Nat) :
    run system scheduler fuel snapshot = snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
      simp only [run, ih]
      exact tick_eq_self_of_frontier_nil system scheduler snapshot empty

/-- Once completion has genuinely been reached, a larger observation budget
cannot retract it. -/
theorem completion_persists {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) (small extra : Nat)
    (complete : (run system scheduler small snapshot).frontier = []) :
    (run system scheduler extra (run system scheduler small snapshot)).frontier = [] := by
  rw [run_eq_self_of_frontier_nil system scheduler _ complete extra]
  exact complete

/-! ## Reachability and scheduler soundness -/

/-- Nodes generated from an initial frontier by finitely many successor steps. -/
inductive Generated {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (roots : List Node) : Node → Prop where
  | root {node} : node ∈ roots → Generated system roots node
  | successor {parent child} :
      Generated system roots parent →
      child ∈ system.successors parent →
      Generated system roots child

def EventValid {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (roots : List Node) (event : Emission Node Answer) : Prop :=
  Generated system roots event.origin ∧
    system.emit event.origin = some event.value

def Snapshot.Sound {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (roots : List Node) (snapshot : Snapshot Node Answer) : Prop :=
  (∀ node ∈ snapshot.frontier, Generated system roots node) ∧
    (∀ event ∈ snapshot.events, EventValid system roots event)

theorem initial_sound {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (roots : List Node) :
    (initial roots : Snapshot Node Answer).Sound system roots := by
  constructor
  · exact fun _ member => .root member
  · simp [initial]

theorem sound_tick {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    {roots : List Node} {snapshot : Snapshot Node Answer}
    (sound : snapshot.Sound system roots) :
    (tick system scheduler snapshot).Sound system roots := by
  obtain ⟨frontierSound, eventSound⟩ := sound
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil =>
      simpa [Snapshot.Sound, tick, ordered] using
        And.intro frontierSound eventSound
  | cons node pending =>
      have nodeMemberOrdered : node ∈ scheduler.reorder snapshot.frontier := by
        simp [ordered]
      have nodeGenerated : Generated system roots node :=
        frontierSound node ((scheduler.mem_reorder_iff).mp nodeMemberOrdered)
      constructor
      · intro next member
        have split := (scheduler.mem_integrate_iff).mp (by
          simpa [tick, ordered] using member)
        rcases split with pendingMember | generatedMember
        · apply frontierSound next
          apply (scheduler.mem_reorder_iff).mp
          simp [ordered, pendingMember]
        · exact .successor nodeGenerated generatedMember
      · intro event member
        cases emitted : system.emit node with
        | none =>
            apply eventSound event
            simpa [tick, ordered, emitted, eventFor] using member
        | some answer =>
            have split : event ∈ snapshot.events ∨ event = ⟨node, answer⟩ := by
              simpa [tick, ordered, emitted, eventFor] using member
            rcases split with old | new
            · exact eventSound event old
            · subst new
              exact ⟨nodeGenerated, emitted⟩

theorem sound_run {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    {roots : List Node} {snapshot : Snapshot Node Answer}
    (sound : snapshot.Sound system roots) (fuel : Nat) :
    (run system scheduler fuel snapshot).Sound system roots := by
  induction fuel with
  | zero => exact sound
  | succ fuel ih => exact sound_tick system scheduler ih

/-! ## Completed answer shadows and the accounting invariant -/

def optionBag {Answer : Type*} : Option Answer → Multiset Answer
  | none => 0
  | some answer => {answer}

def foldValues {Node Answer : Type*} (value : Node → Multiset Answer) :
    List Node → Multiset Answer
  | [] => 0
  | node :: rest => value node + foldValues value rest

@[simp] theorem foldValues_append {Node Answer : Type*}
    (value : Node → Multiset Answer) (left right : List Node) :
    foldValues value (left ++ right) =
      foldValues value left + foldValues value right := by
  induction left with
  | nil => simp [foldValues]
  | cons node rest ih => simp [foldValues, ih, add_assoc]

theorem foldValues_perm {Node Answer : Type*} (value : Node → Multiset Answer)
    {left right : List Node} (reordered : left.Perm right) :
    foldValues value left = foldValues value right := by
  induction reordered with
  | nil => rfl
  | cons _ _ ih => simp [foldValues, ih]
  | swap first second rest =>
      simp [foldValues, add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A completed bag denotation is an algebra for one coalgebra step: the value
of a node is its immediate emission plus the values of all successors.  Such a
finite algebra need not exist for a productive infinite process. -/
structure AdditiveDenotation {Node Answer : Type*}
    (system : BranchingSystem Node Answer) where
  value : Node → Multiset Answer
  unfold : ∀ node,
    value node = optionBag (system.emit node) +
      foldValues value (system.successors node)

def eventBag {Node Answer : Type*}
    (events : List (Emission Node Answer)) : Multiset Answer :=
  (events.map Emission.value : Multiset Answer)

@[simp] theorem eventBag_append {Node Answer : Type*}
    (left right : List (Emission Node Answer)) :
    eventBag (left ++ right) = eventBag left + eventBag right := by
  simp [eventBag, Multiset.coe_add]

@[simp] private theorem eventBag_eventFor {Node Answer : Type*}
    (node : Node) (answer : Option Answer) :
    eventBag (eventFor node answer) = optionBag answer := by
  cases answer <;> simp [eventFor, eventBag, optionBag]

def account {Node Answer : Type*} {system : BranchingSystem Node Answer}
    (denotation : AdditiveDenotation system) (snapshot : Snapshot Node Answer) :
    Multiset Answer :=
  eventBag snapshot.events + foldValues denotation.value snapshot.frontier

/-- **Branching-temporal factorization.**  A scheduler step may change the
stream and frontier order, but it preserves the completed bag represented by
the emitted prefix plus the live frontier. -/
theorem account_tick {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (snapshot : Snapshot Node Answer) :
    account denotation (tick system scheduler snapshot) = account denotation snapshot := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simp [tick, ordered]
  | cons node pending =>
      have reorderValue :
          foldValues denotation.value (scheduler.reorder snapshot.frontier) =
            foldValues denotation.value snapshot.frontier :=
        foldValues_perm denotation.value (scheduler.reorder_complete _)
      have integrateValue :
          foldValues denotation.value
              (scheduler.integrate pending (system.successors node)) =
            foldValues denotation.value (pending ++ system.successors node) :=
        foldValues_perm denotation.value (scheduler.integrate_complete _ _)
      have accountOriginal :
          account denotation snapshot =
            eventBag snapshot.events +
              foldValues denotation.value (node :: pending) := by
        rw [account, ← reorderValue, ordered]
      rw [accountOriginal, show
        account denotation (tick system scheduler snapshot) =
          eventBag (snapshot.events ++ eventFor node (system.emit node)) +
            foldValues denotation.value
              (scheduler.integrate pending (system.successors node)) by
          simp [account, tick, ordered]]
      rw [eventBag_append, eventBag_eventFor, integrateValue]
      rw [foldValues_append]
      simp only [foldValues]
      rw [denotation.unfold]
      ac_rfl

theorem account_run {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (fuel : Nat)
    (snapshot : Snapshot Node Answer) :
    account denotation (run system scheduler fuel snapshot) =
      account denotation snapshot := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => exact (account_tick system scheduler denotation _).trans ih

/-- Any completed run emits exactly the additive denotation of its initial
frontier, regardless of scheduler order. -/
theorem completed_run_denotation {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system) (roots : List Node) (fuel : Nat)
    (complete : (run system scheduler fuel (initial roots)).frontier = []) :
    eventBag (run system scheduler fuel (initial roots)).events =
      foldValues denotation.value roots := by
  have preserved := account_run system scheduler denotation fuel (initial roots)
  change (run system scheduler fuel
      { events := [], frontier := roots }).frontier = [] at complete
  change eventBag (run system scheduler fuel
      { events := [], frontier := roots }).events =
        foldValues denotation.value roots
  simp only [account, initial] at preserved
  rw [complete] at preserved
  simpa [foldValues, eventBag] using preserved

/-- Two completed scheduler streams may differ in order, but their bag
projections agree. -/
theorem completed_schedulers_bag_agree {Node Answer : Type*}
    (system : BranchingSystem Node Answer)
    (first second : Scheduler Node) (denotation : AdditiveDenotation system)
    (roots : List Node) (firstFuel secondFuel : Nat)
    (firstComplete : (run system first firstFuel (initial roots)).frontier = [])
    (secondComplete : (run system second secondFuel (initial roots)).frontier = []) :
    eventBag (run system first firstFuel (initial roots)).events =
      eventBag (run system second secondFuel (initial roots)).events := by
  rw [completed_run_denotation system first denotation roots firstFuel firstComplete,
    completed_run_denotation system second denotation roots secondFuel secondComplete]

/-! ## Fairness as a property of the traversal, not the branching object -/

/-- A generated successor is live immediately after its parent is selected. -/
theorem successor_mem_tick_of_selected {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) {parent child : Node}
    (selection : selected scheduler snapshot.frontier = some parent)
    (childMember : child ∈ system.successors parent) :
    child ∈ (tick system scheduler snapshot).frontier := by
  unfold selected at selection
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simp [ordered] at selection
  | cons node pending =>
      simp only [ordered, List.head?_cons, Option.some.injEq] at selection
      subst node
      simpa [tick, ordered] using
        (scheduler.mem_integrate_iff).mpr (Or.inr childMember)

/-- Selecting an emitting node appends the corresponding certified-origin
event to the next prefix. -/
theorem event_mem_tick_of_selected {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) {node : Node} {answer : Answer}
    (selection : selected scheduler snapshot.frontier = some node)
    (emits : system.emit node = some answer) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (tick system scheduler snapshot).events := by
  unfold selected at selection
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil => simp [ordered] at selection
  | cons selectedNode pending =>
      simp only [ordered, List.head?_cons, Option.some.injEq] at selection
      subst selectedNode
      simp [tick, ordered, emits, eventFor]

/-- A scheduler is fair from an initial frontier when every node that ever
appears live is eventually selected.  This is intentionally a scheduler/run
property, not a field of `BranchingSystem`. -/
def FairFrom {Node Answer : Type*} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (roots : List Node) : Prop :=
  ∀ node,
    (∃ fuel, node ∈ (run system scheduler fuel (initial roots)).frontier) →
    ∃ fuel,
      selected scheduler (run system scheduler fuel (initial roots)).frontier =
        some node

/-- Fairness reaches every finitely generated node, not just roots that were
present initially. -/
theorem fair_selects_generated {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (fair : FairFrom system scheduler roots)
    {node : Node} (generated : Generated system roots node) :
    ∃ fuel,
      selected scheduler (run system scheduler fuel (initial roots)).frontier =
        some node := by
  induction generated with
  | root member =>
      apply fair
      exact ⟨0, by simpa [run, initial] using member⟩
  | successor parentGenerated childMember ih =>
      obtain ⟨fuel, parentSelected⟩ := ih
      apply fair
      refine ⟨fuel + 1, ?_⟩
      change _ ∈ (tick system scheduler
        (run system scheduler fuel (initial roots))).frontier
      exact successor_mem_tick_of_selected system scheduler _
        parentSelected childMember

/-- **Fairness adequacy.**  Every reachable emitting node eventually occurs in
the stream.  A mere silent prefix is insufficient; the fairness hypothesis is
the evidence that turns reachability into eventual observation. -/
theorem fair_emits_reachable {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (roots : List Node) (fair : FairFrom system scheduler roots)
    {node : Node} {answer : Answer} (generated : Generated system roots node)
    (emits : system.emit node = some answer) :
    ∃ fuel,
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system scheduler fuel (initial roots)).events := by
  obtain ⟨fuel, selection⟩ :=
    fair_selects_generated system scheduler roots fair generated
  refine ⟨fuel + 1, ?_⟩
  change _ ∈ (tick system scheduler
    (run system scheduler fuel (initial roots))).events
  exact event_mem_tick_of_selected system scheduler _ selection emits

/-! ## Finite descent certificates force completion -/

def foldRanks {Node : Type*} (rank : Node → Nat) : List Node → Nat
  | [] => 0
  | node :: rest => rank node + foldRanks rank rest

@[simp] theorem foldRanks_append {Node : Type*} (rank : Node → Nat)
    (left right : List Node) :
    foldRanks rank (left ++ right) = foldRanks rank left + foldRanks rank right := by
  induction left with
  | nil => simp [foldRanks]
  | cons node rest ih => simp [foldRanks, ih, Nat.add_assoc]

theorem foldRanks_perm {Node : Type*} (rank : Node → Nat)
    {left right : List Node} (reordered : left.Perm right) :
    foldRanks rank left = foldRanks rank right := by
  induction reordered with
  | nil => rfl
  | cons _ _ ih => simp [foldRanks, ih]
  | swap first second rest => simp [foldRanks, Nat.add_left_comm]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- A finite certificate assigning one unit to the node itself and the rest to
all of its generated subwork.  Each scheduler tick therefore spends exactly
one unit, independently of traversal order. -/
structure DescentCertificate {Node Answer : Type*}
    (system : BranchingSystem Node Answer) where
  rank : Node → Nat
  unfold : ∀ node,
    rank node = 1 + foldRanks rank (system.successors node)

namespace DescentCertificate

variable {Node Answer : Type*} {system : BranchingSystem Node Answer}

theorem rank_positive (certificate : DescentCertificate system) (node : Node) :
    0 < certificate.rank node := by
  rw [certificate.unfold]
  omega

theorem foldRanks_eq_zero_iff (certificate : DescentCertificate system)
    (frontier : List Node) :
    foldRanks certificate.rank frontier = 0 ↔ frontier = [] := by
  constructor
  · intro zero
    cases frontier with
    | nil => rfl
    | cons node rest =>
        have positive := certificate.rank_positive node
        simp only [foldRanks] at zero
        omega
  · rintro rfl
    rfl

end DescentCertificate

/-- Every tick consumes exactly one rank unit while work remains. -/
theorem foldRanks_tick {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (certificate : DescentCertificate system) (snapshot : Snapshot Node Answer) :
    foldRanks certificate.rank (tick system scheduler snapshot).frontier =
      foldRanks certificate.rank snapshot.frontier - 1 := by
  cases ordered : scheduler.reorder snapshot.frontier with
  | nil =>
      have reorderedRank :=
        foldRanks_perm certificate.rank (scheduler.reorder_complete snapshot.frontier)
      have oldZero : foldRanks certificate.rank snapshot.frontier = 0 := by
        rw [← reorderedRank, ordered]
        rfl
      simp [tick, ordered, oldZero]
  | cons node pending =>
      have reorderedRank :=
        foldRanks_perm certificate.rank (scheduler.reorder_complete snapshot.frontier)
      have integratedRank :=
        foldRanks_perm certificate.rank
          (scheduler.integrate_complete pending (system.successors node))
      rw [show (tick system scheduler snapshot).frontier =
          scheduler.integrate pending (system.successors node) by
        simp [tick, ordered]]
      rw [integratedRank, foldRanks_append, ← reorderedRank, ordered]
      simp only [foldRanks]
      rw [certificate.unfold]
      omega

theorem foldRanks_run {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (certificate : DescentCertificate system) (fuel : Nat)
    (snapshot : Snapshot Node Answer) :
    foldRanks certificate.rank (run system scheduler fuel snapshot).frontier =
      foldRanks certificate.rank snapshot.frontier - fuel := by
  induction fuel with
  | zero => simp [run]
  | succ fuel ih =>
      rw [run, foldRanks_tick, ih]
      omega

/-- A descent certificate converts the finite rank into an exact sufficient
observation budget, for every occurrence-preserving scheduler. -/
theorem run_completes_at_rank {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (certificate : DescentCertificate system) (snapshot : Snapshot Node Answer) :
    (run system scheduler (foldRanks certificate.rank snapshot.frontier) snapshot).frontier =
      [] := by
  apply (certificate.foldRanks_eq_zero_iff _).mp
  rw [foldRanks_run]
  omega

/-- Finite descent plus additive unfolding yields scheduler-independent
enumeration of the full answer bag. -/
theorem finite_run_emits_denotation {Node Answer : Type*}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (denotation : AdditiveDenotation system)
    (certificate : DescentCertificate system) (roots : List Node) :
    eventBag
        (run system scheduler (foldRanks certificate.rank roots) (initial roots)).events =
      foldValues denotation.value roots := by
  apply completed_run_denotation
  exact run_completes_at_rank system scheduler certificate (initial roots)

/-! ## A concrete finite search tree -/

inductive FiniteSearch (Answer : Type*) where
  | zero
  | answer (value : Answer)
  | delay (next : FiniteSearch Answer)
  | choice (left right : FiniteSearch Answer)
deriving DecidableEq, Repr

namespace FiniteSearch

variable {Answer : Type*}

def system : BranchingSystem (FiniteSearch Answer) Answer where
  emit
    | .answer value => some value
    | _ => none
  successors
    | .zero => []
    | .answer _ => []
    | .delay next => [next]
    | .choice left right => [left, right]

def denote : FiniteSearch Answer → Multiset Answer
  | .zero => 0
  | .answer value => {value}
  | .delay next => denote next
  | .choice left right => denote left + denote right

def additiveDenotation : AdditiveDenotation (system (Answer := Answer)) where
  value := denote
  unfold node := by
    cases node <;> simp [denote, system, optionBag, foldValues]

def nodeCount : FiniteSearch Answer → Nat
  | .zero => 1
  | .answer _ => 1
  | .delay next => 1 + nodeCount next
  | .choice left right => 1 + nodeCount left + nodeCount right

def descentCertificate : DescentCertificate (system (Answer := Answer)) where
  rank := nodeCount
  unfold node := by
    cases node <;> simp [nodeCount, system, foldRanks, Nat.add_assoc]

theorem every_scheduler_completes (scheduler : Scheduler (FiniteSearch Answer))
    (root : FiniteSearch Answer) :
    (run system scheduler (nodeCount root) (initial [root])).frontier = [] := by
  have completed :=
    run_completes_at_rank system scheduler descentCertificate (initial [root])
  change (run system scheduler (nodeCount root) (initial [root])).frontier = [] at completed
  exact completed

theorem every_scheduler_emits_denotation
    (scheduler : Scheduler (FiniteSearch Answer)) (root : FiniteSearch Answer) :
    eventBag (run system scheduler (nodeCount root) (initial [root])).events =
      denote root := by
  simpa [descentCertificate, additiveDenotation, foldRanks, foldValues] using
    finite_run_emits_denotation system scheduler additiveDenotation
      descentCertificate [root]

def twoAnswers : FiniteSearch Bool :=
  .choice (.answer false) (.answer true)

/-- Breadth-first left-to-right traversal exposes one sequence. -/
theorem breadthFirst_twoAnswers_stream :
    (run system Scheduler.breadthFirst 3 (initial [twoAnswers])).events.map
        Emission.value = [false, true] := by
  decide

/-- A legal reversing scheduler exposes the opposite sequence. -/
theorem reverse_twoAnswers_stream :
    (run system Scheduler.reverseBreadthFirst 3 (initial [twoAnswers])).events.map
        Emission.value = [true, false] := by
  decide

/-- Stream equality is strictly finer than the completed bag shadow. -/
theorem twoAnswers_streams_differ_bags_agree :
    (run system Scheduler.breadthFirst 3 (initial [twoAnswers])).events.map
          Emission.value ≠
        (run system Scheduler.reverseBreadthFirst 3
          (initial [twoAnswers])).events.map Emission.value ∧
      eventBag (run system Scheduler.breadthFirst 3
          (initial [twoAnswers])).events =
        eventBag (run system Scheduler.reverseBreadthFirst 3
          (initial [twoAnswers])).events := by
  decide

end FiniteSearch

/-! ## The fairness hypotheses bite: a starvation witness -/

namespace Starvation

inductive Node where
  | loop
  | answer
deriving DecidableEq, Repr

def system : BranchingSystem Node Nat where
  emit
    | .loop => none
    | .answer => some 42
  successors
    | .loop => [.loop]
    | .answer => []

def roots : List Node := [.loop, .answer]

theorem depthFirst_tick_fixed :
    tick system Scheduler.depthFirst (initial roots) = initial roots := by
  rfl

theorem depthFirst_run_fixed (fuel : Nat) :
    run system Scheduler.depthFirst fuel (initial roots) = initial roots := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp [run, ih, depthFirst_tick_fixed]

/-- A legal depth-first traversal can remain on the silent self-loop forever
although an answer is live in the frontier. -/
theorem depthFirst_starves_answer (fuel : Nat) :
    (⟨.answer, 42⟩ : Emission Node Nat) ∉
      (run system Scheduler.depthFirst fuel (initial roots)).events := by
  rw [depthFirst_run_fixed]
  simp [initial]

theorem answer_is_generated : Generated system roots .answer := by
  exact .root (by simp [roots])

theorem depthFirst_not_fair :
    ¬ FairFrom system Scheduler.depthFirst roots := by
  intro fair
  obtain ⟨fuel, selectedAnswer⟩ := fair .answer ⟨0, by simp [run, initial, roots]⟩
  rw [depthFirst_run_fixed] at selectedAnswer
  simp [selected, Scheduler.depthFirst, initial, roots] at selectedAnswer

/-- Breadth-first traversal exposes the same live answer after two ticks. -/
theorem breadthFirst_emits_answer :
    (⟨.answer, 42⟩ : Emission Node Nat) ∈
      (run system Scheduler.breadthFirst 2 (initial roots)).events := by
  decide

end Starvation

/-! ## Productive infinity has no completed finite bag -/

def productiveLoopSystem {Answer : Type*} (answer : Answer) :
    BranchingSystem Unit Answer where
  emit _ := some answer
  successors _ := [()]

/-- A node that emits once and recreates itself would require a finite multiset
equal to itself plus one occurrence.  Therefore no finite additive denotation
exists, even though every finite stream prefix is meaningful. -/
theorem no_finite_denotation_productiveLoop {Answer : Type*} (answer : Answer) :
    ¬ Nonempty (AdditiveDenotation (productiveLoopSystem answer)) := by
  rintro ⟨denotation⟩
  have unfolds := denotation.unfold ()
  have cardinality := congrArg Multiset.card unfolds
  simp [productiveLoopSystem, optionBag, foldValues] at cardinality

/-! ## Connection to GSLT rewrite paths -/

/-- A finitely branching presentation of a GSLT enumerates exactly its legal
one-step successors and selects which terms emit answers. -/
structure GSLTBranchingPresentation (S : GSLT) (Answer : Type*) where
  emit : S.Term → Option Answer
  successors : S.Term → List S.Term
  step_iff_mem : ∀ source target,
    target ∈ successors source ↔ S.Step source target

def GSLTBranchingPresentation.toSystem {S : GSLT} {Answer : Type*}
    (presentation : GSLTBranchingPresentation S Answer) :
    BranchingSystem S.Term Answer where
  emit := presentation.emit
  successors := presentation.successors

private theorem multistep_tail {S : GSLT} {first middle last : S.Term}
    (path : S.MultiStep first middle) (lastStep : S.Step middle last) :
    S.MultiStep first last := by
  induction path with
  | refl _ => exact .step lastStep (.refl _)
  | step firstStep rest ih => exact .step firstStep (ih lastStep)

/-- Generated work in an exact finite presentation is genuine GSLT
reachability. -/
theorem generated_has_gslt_multistep {S : GSLT} {Answer : Type*}
    (presentation : GSLTBranchingPresentation S Answer)
    {root node : S.Term}
    (generated : Generated presentation.toSystem [root] node) :
    S.MultiStep root node := by
  induction generated with
  | root member =>
      simp only [List.mem_singleton] at member
      subst member
      exact .refl _
  | successor parentGenerated childMember ih =>
      apply multistep_tail ih
      exact (presentation.step_iff_mem _ _).mp childMember

/-- **Scheduler soundness for GSLTs.**  Every emitted stream occurrence has a
finite GSLT rewrite derivation from the root, independently of traversal
policy. -/
theorem scheduled_event_has_gslt_path {S : GSLT} {Answer : Type*}
    (presentation : GSLTBranchingPresentation S Answer)
    (scheduler : Scheduler S.Term) (root : S.Term) (fuel : Nat)
    {event : Emission S.Term Answer}
    (member : event ∈
      (run presentation.toSystem scheduler fuel (initial [root])).events) :
    S.MultiStep root event.origin ∧
      presentation.emit event.origin = some event.value := by
  have sound := sound_run presentation.toSystem scheduler
    (initial_sound presentation.toSystem [root]) fuel
  have valid := sound.2 event member
  exact ⟨generated_has_gslt_multistep presentation valid.1, valid.2⟩

end Mettapedia.GSLT.Core.BranchingTemporal
