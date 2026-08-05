import Mathlib.Tactic

/-!
# Bounded-stale coordinate epochs

FabricPC proposes staged asynchronous execution for predictive-coding graphs:
coordinate updates may read a boundedly stale state while communication
overlaps computation.  This file isolates a finite semantic certificate for
that design.

An update packet records the coordinate it overwrites, the certified norm of
the stale snapshot used to compute it, and its proposed value.  A packet is
admissible when its stale norm is below the current epoch budget and its value
contracts that stale norm by a declared factor.  If one epoch covers every
coordinate, its output contracts coordinatewise.  Repeating certified epochs
therefore gives a geometric error bound.

The coverage and stale-budget hypotheses are essential.  A two-coordinate
fixture shows that an unfair schedule can leave one coordinate unchanged, and
a one-coordinate fixture shows that an out-of-budget stale packet can expand
the state.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace BoundedStaleEpoch

universe u

variable {Vertex : Type u} [DecidableEq Vertex]

abbrev CoordinateState (Vertex : Type u) :=
  Vertex → ℝ

/-- One coordinate overwrite computed from a possibly stale snapshot. -/
structure Packet (Vertex : Type u) where
  coordinate : Vertex
  staleNorm : ℝ
  value : ℝ

/-- Overwrite the packet's coordinate. -/
def applyPacket
    (packet : Packet Vertex)
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  fun vertex =>
    if vertex = packet.coordinate then packet.value else state vertex

@[simp] theorem applyPacket_same
    (packet : Packet Vertex)
    (state : CoordinateState Vertex) :
    applyPacket packet state packet.coordinate = packet.value := by
  simp [applyPacket]

theorem applyPacket_other
    (packet : Packet Vertex)
    (state : CoordinateState Vertex)
    {vertex : Vertex}
    (different : vertex ≠ packet.coordinate) :
    applyPacket packet state vertex = state vertex := by
  simp [applyPacket, different]

/-- Execute a finite packet schedule in order. -/
def runPackets :
    List (Packet Vertex) →
      CoordinateState Vertex →
      CoordinateState Vertex
  | [], state => state
  | packet :: packets, state =>
      runPackets packets (applyPacket packet state)

@[simp] theorem runPackets_nil
    (state : CoordinateState Vertex) :
    runPackets [] state = state :=
  rfl

@[simp] theorem runPackets_cons
    (packet : Packet Vertex)
    (packets : List (Packet Vertex))
    (state : CoordinateState Vertex) :
    runPackets (packet :: packets) state =
      runPackets packets (applyPacket packet state) :=
  rfl

/-- A coordinate absent from the packet list is unchanged. -/
theorem runPackets_eq_of_not_mem
    (packets : List (Packet Vertex))
    (state : CoordinateState Vertex)
    {vertex : Vertex}
    (absent : vertex ∉ packets.map Packet.coordinate) :
    runPackets packets state vertex = state vertex := by
  induction packets generalizing state with
  | nil =>
      rfl
  | cons packet packets induction =>
      have different : vertex ≠ packet.coordinate := by
        intro same
        apply absent
        simp [same]
      have absentTail : vertex ∉ packets.map Packet.coordinate := by
        intro member
        apply absent
        simp [member]
      rw [runPackets_cons]
      rw [induction (state := applyPacket packet state) absentTail]
      exact applyPacket_other packet state different

/-- Once a coordinate occurs in a schedule, its final value is bounded by the
common bound on packet values, regardless of later overwrites. -/
theorem abs_runPackets_le_of_mem
    (packets : List (Packet Vertex))
    (state : CoordinateState Vertex)
    {vertex : Vertex}
    {bound : ℝ}
    (packetBound :
      ∀ packet ∈ packets, |packet.value| ≤ bound)
    (present : vertex ∈ packets.map Packet.coordinate) :
    |runPackets packets state vertex| ≤ bound := by
  induction packets generalizing state with
  | nil =>
      simp at present
  | cons packet packets induction =>
      have tailBound :
          ∀ tailPacket ∈ packets, |tailPacket.value| ≤ bound := by
        intro tailPacket member
        exact packetBound tailPacket (by simp [member])
      by_cases later : vertex ∈ packets.map Packet.coordinate
      · rw [runPackets_cons]
        exact induction
          (state := applyPacket packet state)
          tailBound
          later
      · have same : vertex = packet.coordinate := by
          simpa [later] using present
        subst vertex
        rw [runPackets_cons]
        rw [runPackets_eq_of_not_mem
          packets (applyPacket packet state) later]
        rw [applyPacket_same]
        exact packetBound packet (by simp)

/-- The local certificate attached to one stale update packet. -/
def Packet.Admissible
    (packet : Packet Vertex)
    (contraction epochBound : ℝ) : Prop :=
  0 ≤ packet.staleNorm ∧
    packet.staleNorm ≤ epochBound ∧
    |packet.value| ≤ contraction * packet.staleNorm

/-- An epoch is fair when it overwrites every coordinate at least once. -/
def Covers
    (packets : List (Packet Vertex)) : Prop :=
  ∀ vertex, vertex ∈ packets.map Packet.coordinate

omit [DecidableEq Vertex] in
theorem Packet.abs_value_le_epoch
    {packet : Packet Vertex}
    {contraction epochBound : ℝ}
    (contractionNonnegative : 0 ≤ contraction)
    (admissible : packet.Admissible contraction epochBound) :
    |packet.value| ≤ contraction * epochBound := by
  exact admissible.2.2.trans
    (mul_le_mul_of_nonneg_left admissible.2.1 contractionNonnegative)

/-- A fair epoch of admissible stale packets contracts every coordinate. -/
theorem fair_epoch_contracts
    {contraction epochBound : ℝ}
    (contractionNonnegative : 0 ≤ contraction)
    (packets : List (Packet Vertex))
    (admissible :
      ∀ packet ∈ packets,
        packet.Admissible contraction epochBound)
    (covers : Covers packets)
    (state : CoordinateState Vertex)
    (vertex : Vertex) :
    |runPackets packets state vertex| ≤ contraction * epochBound := by
  apply abs_runPackets_le_of_mem
    (packets := packets)
    (state := state)
  · intro packet member
    exact Packet.abs_value_le_epoch
      contractionNonnegative
      (admissible packet member)
  · exact covers vertex

/-- Even an incomplete admissible epoch is nonexpansive when the contraction
factor is at most one and the input already satisfies the epoch budget. -/
theorem partial_epoch_nonexpansive
    {contraction epochBound : ℝ}
    (contractionNonnegative : 0 ≤ contraction)
    (contractionAtMostOne : contraction ≤ 1)
    (epochBoundNonnegative : 0 ≤ epochBound)
    (packets : List (Packet Vertex))
    (admissible :
      ∀ packet ∈ packets,
        packet.Admissible contraction epochBound)
    (state : CoordinateState Vertex)
    (stateBound : ∀ vertex, |state vertex| ≤ epochBound)
    (vertex : Vertex) :
    |runPackets packets state vertex| ≤ epochBound := by
  by_cases present : vertex ∈ packets.map Packet.coordinate
  · refine (abs_runPackets_le_of_mem
      (packets := packets)
      (state := state)
      (bound := contraction * epochBound)
      ?_
      present).trans ?_
    · intro packet member
      exact Packet.abs_value_le_epoch
        contractionNonnegative
        (admissible packet member)
    · exact mul_le_of_le_one_left epochBoundNonnegative contractionAtMostOne
  · rw [runPackets_eq_of_not_mem packets state present]
    exact stateBound vertex

/-- A state-dependent packet scheduler. -/
abbrev Scheduler (Vertex : Type u) :=
  CoordinateState Vertex → List (Packet Vertex)

/-- Execute one scheduler epoch. -/
def scheduledStep
    (scheduler : Scheduler Vertex)
    (state : CoordinateState Vertex) :
    CoordinateState Vertex :=
  runPackets (scheduler state) state

/-- The executable premise for a uniformly contractive bounded-stale
scheduler. -/
def IsCertifiedScheduler
    (scheduler : Scheduler Vertex)
    (contraction : ℝ) : Prop :=
  ∀ state epochBound,
    0 ≤ epochBound →
    (∀ vertex, |state vertex| ≤ epochBound) →
      (∀ packet ∈ scheduler state,
        packet.Admissible contraction epochBound) ∧
      Covers (scheduler state)

theorem scheduledStep_contracts
    {scheduler : Scheduler Vertex}
    {contraction epochBound : ℝ}
    (contractionNonnegative : 0 ≤ contraction)
    (certified : IsCertifiedScheduler scheduler contraction)
    (state : CoordinateState Vertex)
    (epochBoundNonnegative : 0 ≤ epochBound)
    (stateBound : ∀ vertex, |state vertex| ≤ epochBound)
    (vertex : Vertex) :
    |scheduledStep scheduler state vertex| ≤
      contraction * epochBound := by
  rcases certified state epochBound epochBoundNonnegative stateBound with
    ⟨admissible, covers⟩
  exact fair_epoch_contracts
    contractionNonnegative
    (scheduler state)
    admissible
    covers
    state
    vertex

/-- Iterate a state-dependent packet scheduler. -/
def iterateScheduledStep
    (scheduler : Scheduler Vertex) :
    ℕ → CoordinateState Vertex → CoordinateState Vertex
  | 0, state => state
  | steps + 1, state =>
      scheduledStep scheduler (iterateScheduledStep scheduler steps state)

/-- Repeated certified epochs have the expected geometric coordinatewise
error bound. -/
theorem iterateScheduledStep_abs_le
    {scheduler : Scheduler Vertex}
    {contraction initialBound : ℝ}
    (contractionNonnegative : 0 ≤ contraction)
    (initialBoundNonnegative : 0 ≤ initialBound)
    (certified : IsCertifiedScheduler scheduler contraction)
    (initial : CoordinateState Vertex)
    (initialBounded : ∀ vertex, |initial vertex| ≤ initialBound)
    (steps : ℕ)
    (vertex : Vertex) :
    |iterateScheduledStep scheduler steps initial vertex| ≤
      contraction ^ steps * initialBound := by
  induction steps generalizing vertex with
  | zero =>
      simpa [iterateScheduledStep] using initialBounded vertex
  | succ steps induction =>
      rw [iterateScheduledStep]
      have boundNonnegative :
          0 ≤ contraction ^ steps * initialBound :=
        mul_nonneg (pow_nonneg contractionNonnegative steps)
          initialBoundNonnegative
      have nextBound := scheduledStep_contracts
        contractionNonnegative
        certified
        (iterateScheduledStep scheduler steps initial)
        boundNonnegative
        induction
        vertex
      calc
        |scheduledStep scheduler
            (iterateScheduledStep scheduler steps initial) vertex| ≤
            contraction * (contraction ^ steps * initialBound) :=
          nextBound
        _ = contraction ^ (steps + 1) * initialBound := by ring

/-! ## Positive and negative executable fixtures -/

/-- A one-coordinate scheduler whose packets use the current norm and halve
the coordinate. -/
noncomputable def halfScheduler : Scheduler Unit :=
  fun state =>
    [{
      coordinate := ()
      staleNorm := |state ()|
      value := state () / 2
    }]

theorem halfScheduler_certified :
    IsCertifiedScheduler halfScheduler (1 / 2) := by
  intro state epochBound epochBoundNonnegative stateBound
  constructor
  · intro packet member
    simp only [halfScheduler, List.mem_singleton] at member
    subst packet
    refine ⟨abs_nonneg _, stateBound (), ?_⟩
    rw [abs_div]
    norm_num
    ring_nf
    exact le_rfl
  · intro vertex
    simp [halfScheduler]

theorem halfScheduler_geometric
    (initial : CoordinateState Unit)
    (initialBound : ℝ)
    (initialBoundNonnegative : 0 ≤ initialBound)
    (bounded : |initial ()| ≤ initialBound)
    (steps : ℕ) :
    |iterateScheduledStep halfScheduler steps initial ()| ≤
      (1 / 2 : ℝ) ^ steps * initialBound := by
  apply iterateScheduledStep_abs_le
  · norm_num
  · exact initialBoundNonnegative
  · exact halfScheduler_certified
  · intro vertex
    simpa using bounded

/-- An unfair two-coordinate schedule updates only `false`. -/
def unfairPackets : List (Packet Bool) :=
  [{
    coordinate := false
    staleNorm := 1
    value := 0
  }]

def unfairInitial : CoordinateState Bool :=
  fun _ => 1

theorem unfairPackets_admissible :
    ∀ packet ∈ unfairPackets,
      packet.Admissible (1 / 2) 1 := by
  intro packet member
  simp only [unfairPackets, List.mem_singleton] at member
  subst packet
  norm_num [Packet.Admissible]

theorem unfairPackets_do_not_contract_true :
    |runPackets unfairPackets unfairInitial true| = 1 := by
  norm_num [unfairPackets, unfairInitial, runPackets, applyPacket]

theorem unfairPackets_not_covering :
    ¬ Covers unfairPackets := by
  intro covers
  have := covers true
  simp [unfairPackets] at this

/-- A packet computed from a stale norm outside the declared epoch budget. -/
def outOfBudgetPacket : Packet Unit where
  coordinate := ()
  staleNorm := 4
  value := 2

theorem outOfBudgetPacket_expands :
    |applyPacket outOfBudgetPacket (fun _ => 1) ()| = 2 := by
  norm_num [outOfBudgetPacket, applyPacket]

theorem outOfBudgetPacket_not_admissible :
    ¬ outOfBudgetPacket.Admissible (1 / 2) 1 := by
  norm_num [outOfBudgetPacket, Packet.Admissible]

#print axioms fair_epoch_contracts
#print axioms partial_epoch_nonexpansive
#print axioms scheduledStep_contracts
#print axioms iterateScheduledStep_abs_le
#print axioms halfScheduler_geometric
#print axioms unfairPackets_not_covering
#print axioms outOfBudgetPacket_not_admissible

end BoundedStaleEpoch

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
