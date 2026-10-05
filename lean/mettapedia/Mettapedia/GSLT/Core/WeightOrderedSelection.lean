import Mettapedia.GSLT.Core.AgeProtectedSchedule
import Mettapedia.GSLT.Core.BranchingTemporal
import Mettapedia.GSLT.Core.InferenceControl
import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.Interval.Set.Instances
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Best-first selection by accumulated weight

Best-first selection orders the live frontier by a total weight order and
otherwise preserves occurrences. Stopping bounds need only a preorder and
one-sided growth on a preserved domain. A superior combination is one
sufficient instance: it is monotone and never below either argument.

An emitted answer is a lightest latent answer.  If only finitely many
generated items are at most as heavy as a live target, and a selected item
of that class does not return, best-first selection reaches the target.
Finiteness of that class alone does not yield fairness: a returning
weight-zero item is a finite class and is selected forever.  An infinite
weight-zero chain starves a heavier neighbour for the same reason.  A
portfolio with an age lane still selects that neighbour when the weights
themselves decrease.

Breadth-first and depth-first queue updates append or prepend.  They do not
sort by weight.  The weight order is the scheduler reorder, an insertion
sort, and that reorder is a permutation, so grades do not drop occurrences.

Nonnegative costs under addition, and coefficients in the unit interval under
multiplication read with larger coefficients as better, are superior; a
factor above one is not. A superior law is sufficient for a stopping
certificate; the certificate itself needs only one-sided growth along
successors within a preserved domain. When no live frontier item is better
than a bound, no node any scheduler has not yet chosen is better than it
either, since every such node is still reachable from that frontier. The
certificate holds for every scheduler, including stateful controllers and
portfolios with an age lane. Retained unaccepted results also need a bound.
Without the step law a strictly better answer can still be pending.
-/

namespace Mettapedia.GSLT.Core.WeightOrderedSelection

open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.AgeProtectedSchedule
open Mettapedia.GSLT.Core.WeightedOccurrenceControl

/-! ## Superior combinations -/

/-- A superior combination on a preorder is monotone in each argument and
lies above both arguments. -/
structure Superior (W : Type _) [Preorder W] where
  combine : W → W → W
  mono_left : ∀ {a a' b : W}, a ≤ a' → combine a b ≤ combine a' b
  mono_right : ∀ {a b b' : W}, b ≤ b' → combine a b ≤ combine a b'
  left_le : ∀ a b, a ≤ combine a b
  right_le : ∀ a b, b ≤ combine a b

theorem Superior.mono {W : Type _} [Preorder W] (s : Superior W) {a a' b b' : W}
    (ha : a ≤ a') (hb : b ≤ b') : s.combine a b ≤ s.combine a' b' :=
  le_trans (s.mono_left ha) (s.mono_right hb)

/-- Addition of natural numbers is superior. -/
def natAdd : Superior Nat where
  combine := (· + ·)
  mono_left := fun h => Nat.add_le_add_right h _
  mono_right := fun h => Nat.add_le_add_left h _
  left_le := fun a b => Nat.le_add_right a b
  right_le := fun a b => Nat.le_add_left b a

theorem intAdd_not_left_le : ¬ ((0 : Int) ≤ 0 + (-1)) := by
  decide

/-- Integer addition is not a superior function: a negative summand drops
below its other argument. -/
theorem intAdd_not_superior : ¬ ∃ s : Superior Int, s.combine = (· + ·) := by
  intro ⟨s, hcombine⟩
  have hle := s.left_le (0 : Int) (-1)
  simp [hcombine] at hle

/-- Addition in a canonically ordered additive monoid is superior: the law of
nonnegative costs, for example nonnegative rationals under addition. -/
def canonicalAdd (W : Type _) [AddCommMonoid W] [PartialOrder W]
    [IsOrderedAddMonoid W] [CanonicallyOrderedAdd W] : Superior W where
  combine := (· + ·)
  mono_left := fun h => add_le_add h le_rfl
  mono_right := fun h => add_le_add le_rfl h
  left_le := fun _ _ => le_self_add
  right_le := fun _ _ => le_add_self

/-- Coefficients in the unit interval under multiplication, with larger
coefficients better: in the order dual, where lighter means larger, the
product is superior. -/
def unitIntervalMul (R : Type _) [Semiring R] [PartialOrder R] [IsOrderedRing R] :
    Superior (Set.Icc (0 : R) 1)ᵒᵈ where
  combine a b := OrderDual.toDual (OrderDual.ofDual a * OrderDual.ofDual b)
  mono_left := fun {a a' b} h => by
    change OrderDual.ofDual a' * OrderDual.ofDual b ≤ OrderDual.ofDual a * OrderDual.ofDual b
    have h' : ((OrderDual.ofDual a' : Set.Icc (0 : R) 1) : R) ≤ OrderDual.ofDual a := h
    exact Subtype.coe_le_coe.mp (by
      simpa using mul_le_mul_of_nonneg_right h' (OrderDual.ofDual b).2.1)
  mono_right := fun {a b b'} h => by
    change OrderDual.ofDual a * OrderDual.ofDual b' ≤ OrderDual.ofDual a * OrderDual.ofDual b
    have h' : ((OrderDual.ofDual b' : Set.Icc (0 : R) 1) : R) ≤ OrderDual.ofDual b := h
    exact Subtype.coe_le_coe.mp (by
      simpa using mul_le_mul_of_nonneg_left h' (OrderDual.ofDual a).2.1)
  left_le := fun _ _ => Set.Icc.mul_le_left
  right_le := fun _ _ => Set.Icc.mul_le_right

/-- Outside the unit interval the product is not superior: a factor of
twenty moves a coefficient of one up, so it is not below its argument in the
larger-is-better order. -/
theorem rat_mul_not_superior :
    ¬ ∃ s : Superior ℚᵒᵈ, ∀ a b,
      s.combine a b = OrderDual.toDual (OrderDual.ofDual a * OrderDual.ofDual b) := by
  rintro ⟨s, hs⟩
  have h := s.left_le (OrderDual.toDual 1) (OrderDual.toDual 20)
  rw [hs] at h
  change (1 : ℚ) * 20 ≤ 1 at h
  norm_num at h

/-- A weight is accumulated when every successor's weight is the superior
combination of its parent's weight with some edge weight. -/
structure Realized {W Node Answer : Type _} [Preorder W]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W) : Prop where
  accumulated : ∀ parent child, child ∈ system.successors parent →
    ∃ edge, weight child = s.combine (weight parent) edge

theorem realized_monotone {W Node Answer : Type _} [Preorder W]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W)
    (h : Realized system s weight) :
    ∀ parent child, child ∈ system.successors parent → weight parent ≤ weight child := by
  intro parent child hmem
  obtain ⟨edge, heq⟩ := h.accumulated parent child hmem
  simpa [heq] using s.left_le (weight parent) edge

/-- A stopping bound needs only one-sided growth on a preserved domain of
states. It does not require an order on individual factors or a superior
combination on the entire coefficient carrier. -/
structure StepBound {W Node Answer : Type*} [Preorder W]
    (system : BranchingSystem Node Answer) (weight : Node → W)
    (domain : Node → Prop) : Prop where
  preserves : ∀ parent child, domain parent → child ∈ system.successors parent → domain child
  bounds : ∀ parent child, domain parent → child ∈ system.successors parent →
    weight parent ≤ weight child

/-- A superior realization supplies the unrestricted instance of the weaker
step law. The growth proof uses its actual successor realization. -/
theorem Realized.stepBound {W Node Answer : Type*} [Preorder W]
    {system : BranchingSystem Node Answer} {s : Superior W} {weight : Node → W}
    (realized : Realized system s weight) : StepBound system weight (fun _ => True) where
  preserves := fun _ _ _ _ => True.intro
  bounds := fun parent child _ member =>
    realized_monotone system s weight realized parent child member

/-- Both domain membership and the frontier bound survive every finite
source path. No total order, factor commutation or fairness is needed. -/
theorem StepBound.generated {W Node Answer : Type*} [Preorder W]
    {system : BranchingSystem Node Answer} {weight : Node → W} {domain : Node → Prop}
    (law : StepBound system weight domain) {frontier : List Node} {bound : W}
    (frontierDomain : ∀ item ∈ frontier, domain item)
    (certificate : ∀ item ∈ frontier, bound ≤ weight item) {node : Node}
    (reachable : Generated system frontier node) : domain node ∧ bound ≤ weight node := by
  induction reachable with
  | root member => exact ⟨frontierDomain _ member, certificate _ member⟩
  | successor _ childMember inductionHypothesis =>
      exact ⟨law.preserves _ _ inductionHypothesis.1 childMember,
        inductionHypothesis.2.trans (law.bounds _ _ inductionHypothesis.1 childMember)⟩

/-! ## Best-first frontiers -/

/-- Order the frontier by `rank` and append generated work behind what is
already waiting.  `rank` affects order only. -/
def orderScheduler {Node : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank] : Scheduler Node where
  reorder frontier := frontier.insertionSort rank
  reorder_complete frontier := List.perm_insertionSort rank frontier
  integrate pending generated := pending ++ generated
  integrate_complete _ _ := List.Perm.refl _

theorem frontier_after_choice {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (snapshot : Snapshot Node Answer)
    {node : Node} {pending : List Node}
    (horder : (orderScheduler rank).reorder snapshot.frontier = node :: pending) :
    (tick system (orderScheduler rank) snapshot).frontier =
      pending ++ system.successors node := by
  simp only [tick]
  rw [horder]
  simp [orderScheduler]

theorem reorder_pair_le {Node : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    {a b : Node} (hle : rank a b) :
    (orderScheduler rank).reorder [a, b] = [a, b] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hle]
  simp

theorem reorder_pair_not {Node : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    {a b : Node} (hnot : ¬ rank a b) :
    (orderScheduler rank).reorder [a, b] = [b, a] := by
  simp only [orderScheduler, List.insertionSort_cons, List.insertionSort_nil,
    List.orderedInsert_cons, List.orderedInsert_nil, hnot]
  simp

def choiceAt {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (index : Nat) : Option Node :=
  ((orderScheduler rank).reorder
    (run system (orderScheduler rank) index (initial roots)).frontier).head?

def choiceList {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (steps : Nat) : List Node :=
  (List.range steps).filterMap (choiceAt rank system roots)

theorem choiceList_succ {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (steps : Nat) {node : Node}
    (hchosen : choiceAt rank system roots steps = some node) :
    choiceList rank system roots (steps + 1) =
      choiceList rank system roots steps ++ [node] := by
  simp [choiceList, List.range_succ, List.filterMap_append, hchosen,
    List.filterMap_cons_some]

theorem cons_of_head? {Node : Type _} {nodes : List Node} {node : Node}
    (h : nodes.head? = some node) : ∃ pending, nodes = node :: pending := by
  cases nodes with
  | nil => simp at h
  | cons head tail =>
      simp at h
      exact ⟨tail, by simp [h]⟩

theorem chosen_least {Node : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (frontier : List Node) {node : Node} {pending : List Node}
    (horder : (orderScheduler rank).reorder frontier = node :: pending) :
    ∀ item ∈ frontier, rank node item := by
  intro item hitem
  have hsorted : List.insertionSort rank frontier = node :: pending := by
    simpa [orderScheduler] using horder
  have hpair := List.pairwise_insertionSort rank frontier
  have hmem : item ∈ node :: pending := by
    rw [← hsorted]
    exact (List.mem_insertionSort rank).mpr hitem
  rw [hsorted] at hpair
  rcases List.mem_cons.mp hmem with hhead | htail
  · rw [← hhead]
    exact (Std.Total.total (r := rank) item item).elim id id
  · exact (List.pairwise_cons.mp hpair).1 item htail

private theorem exists_mem_split {α : Type _} {a : α} {l : List α} (h : a ∈ l) :
    ∃ s t, l = s ++ a :: t := by
  induction l with
  | nil => cases h
  | cons head tail ih =>
      cases h with
      | head => exact ⟨[], tail, rfl⟩
      | tail _ htail =>
          obtain ⟨s, t, rfl⟩ := ih htail
          exact ⟨head :: s, t, rfl⟩

theorem length_le_of_nodup_mem {α : Type _} [DecidableEq α] {l t : List α}
    (hl : l.Nodup) (hmem : ∀ x ∈ l, x ∈ t) : l.length ≤ t.length := by
  induction l generalizing t with
  | nil => simp
  | cons a rest ih =>
      obtain ⟨hnot, hrest⟩ := List.nodup_cons.mp hl
      have ha : a ∈ t := hmem a (List.mem_cons.mpr (Or.inl rfl))
      obtain ⟨s, u, rfl⟩ := exists_mem_split ha
      have hrestmem : ∀ x ∈ rest, x ∈ s ++ u := by
        intro x hx
        have hxAll := hmem x (List.mem_cons.mpr (Or.inr hx))
        have xne : x ≠ a := by
          intro heq
          exact hnot (heq ▸ hx)
        rcases List.mem_append.mp hxAll with hs | hu
        · exact List.mem_append_left _ hs
        · rcases List.mem_cons.mp hu with heq | hu
          · exact absurd heq xne
          · exact List.mem_append_right _ hu
      have ihlen := ih hrest hrestmem
      simp only [List.length_cons, List.length_append] at ihlen ⊢
      omega

theorem mem_of_same_length {α : Type _} [DecidableEq α] {l t : List α}
    (hl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ t) (hlen : l.length = t.length)
    {x : α} (hx : x ∈ t) : x ∈ l := by
  by_cases hxl : x ∈ l
  · exact hxl
  · have hsub' : ∀ y ∈ l, y ∈ t.erase x := by
      intro y hy
      have hym := hsub y hy
      have yne : y ≠ x := by
        intro heq
        exact hxl (heq ▸ hy)
      exact (List.mem_erase_of_ne yne).2 hym
    have hlenLe := length_le_of_nodup_mem hl hsub'
    have herase := List.length_erase_of_mem hx
    have hne : t ≠ [] := List.ne_nil_of_mem hx
    have hpos : 0 < t.length :=
      Nat.pos_of_ne_zero (fun hzero => hne (List.length_eq_zero_iff.mp hzero))
    rw [herase] at hlenLe
    have : t.length < t.length := by omega
    exact absurd this (lt_irrefl _)

/-! ## Latent answers are accounted for by the frontier -/

theorem reorder_nil_iff {Node : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank] (frontier : List Node) :
    (orderScheduler rank).reorder frontier = [] ↔ frontier = [] := by
  constructor
  · intro hnil
    have hperm := (orderScheduler rank).reorder_complete frontier
    rw [hnil] at hperm
    exact List.perm_nil.mp hperm.symm
  · intro hnil
    simp [orderScheduler, hnil]

theorem choice_some_of_mem {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (index : Nat)
    {target : Node}
    (hlive : target ∈ (run system (orderScheduler rank) index (initial roots)).frontier) :
    ∃ node, choiceAt rank system roots index = some node := by
  cases horder : (orderScheduler rank).reorder
      (run system (orderScheduler rank) index (initial roots)).frontier with
  | nil =>
      have hempty := (reorder_nil_iff rank _).mp horder
      simp [hempty] at hlive
  | cons node pending =>
      exact ⟨node, by simp [choiceAt, horder]⟩

theorem from_entry {Node Answer : Type _} [DecidableEq Node] (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (start extra : Nat)
    {node : Node}
    (henter : node ∈ (run system (orderScheduler rank) start (initial roots)).frontier) :
    node ∈ choiceList rank system roots (start + extra) ∨
      node ∈ (run system (orderScheduler rank) (start + extra) (initial roots)).frontier := by
  induction extra with
  | zero => exact Or.inr (by simpa using henter)
  | succ extra ih =>
      rcases ih with hselected | hlive
      · left
        have hmono : node ∈ choiceList rank system roots (start + extra + 1) := by
          simp only [choiceList, List.mem_filterMap, List.mem_range] at hselected ⊢
          obtain ⟨index, hindex, hchoice⟩ := hselected
          exact ⟨index, Nat.lt_trans hindex (Nat.lt_succ_self _), hchoice⟩
        simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hmono
      · cases horder : (orderScheduler rank).reorder
            (run system (orderScheduler rank) (start + extra) (initial roots)).frontier with
        | nil =>
            have hempty := (reorder_nil_iff rank _).mp horder
            simp [hempty] at hlive
        | cons head pending =>
            by_cases hhead : head = node
            · left
              have hchoice : choiceAt rank system roots (start + extra) = some node := by
                simp [choiceAt, horder, hhead]
              have hmem : node ∈ choiceList rank system roots (start + extra + 1) := by
                rw [choiceList_succ rank system roots (start + extra) hchoice]
                exact List.mem_append_right _ (by simp)
              simpa [Nat.add_assoc] using hmem
            · right
              have hmemOrdered : node ∈ head :: pending := by
                have hperm := (orderScheduler rank).reorder_complete
                  (run system (orderScheduler rank) (start + extra) (initial roots)).frontier
                rw [horder] at hperm
                exact hperm.mem_iff.mpr hlive
              have hpending : node ∈ pending := by
                rcases List.mem_cons.mp hmemOrdered with rfl | hpending
                · exact absurd rfl hhead
                · exact hpending
              have hfront := frontier_after_choice rank system
                (run system (orderScheduler rank) (start + extra) (initial roots)) horder
              have hfuel : start + (extra + 1) = Nat.succ (start + extra) := by
                rw [← Nat.add_assoc]
              have hstep :
                  run system (orderScheduler rank) (Nat.succ (start + extra)) (initial roots) =
                    tick system (orderScheduler rank)
                      (run system (orderScheduler rank) (start + extra) (initial roots)) := rfl
              rw [hfuel, hstep]
              exact hfront.symm ▸ List.mem_append_left _ hpending

theorem successor_enters {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (index : Nat)
    {parent child : Node}
    (hchoice : choiceAt rank system roots index = some parent)
    (hchild : child ∈ system.successors parent) :
    child ∈ (run system (orderScheduler rank) (index + 1) (initial roots)).frontier := by
  obtain ⟨pending, horder⟩ := cons_of_head? (by simpa [choiceAt] using hchoice)
  simp only [run]
  rw [frontier_after_choice rank system _ horder]
  exact List.mem_append_right _ hchild

/-- Every generated node has been selected, or is still reachable from the
live frontier. -/
theorem generated_accounted {Node Answer : Type _} [DecidableEq Node]
    (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat) {node : Node}
    (hgen : Generated system roots node) :
    node ∈ choiceList rank system roots fuel ∨
      Generated system (run system (orderScheduler rank) fuel (initial roots)).frontier node := by
  have covered := InferenceControl.Snapshot.generated_selected_or_reachable system
    (InferenceControl.Controller.fixed (orderScheduler rank))
    { search := initial roots, memory := () } fuel hgen
  rcases covered with ⟨index, beforeEnd, selection⟩ | reachable
  · left
    simp only [choiceList, List.mem_filterMap, List.mem_range]
    refine ⟨index, beforeEnd, ?_⟩
    change ((orderScheduler rank).reorder
      (InferenceControl.Snapshot.run system
        (InferenceControl.Controller.fixed (orderScheduler rank)) index
        { search := initial roots, memory := () }).search.frontier).head? = some node at selection
    simpa only [InferenceControl.Snapshot.fixed_run_search, choiceAt] using selection
  · exact Or.inr (by
      simpa only [InferenceControl.Snapshot.fixed_run_search] using reachable)

/-- One scheduler step appends no event, or exactly the selected emission. -/
private theorem tick_events {Node Answer : Type _}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node)
    (snapshot : Snapshot Node Answer) :
    (tick system scheduler snapshot).events =
      snapshot.events ++
        match scheduler.reorder snapshot.frontier with
        | [] => []
        | node :: _ =>
            match system.emit node with
            | none => []
            | some answer => [⟨node, answer⟩] := by
  cases h : scheduler.reorder snapshot.frontier with
  | nil => simp [tick, h]
  | cons node pending =>
      cases e : system.emit node with
      | none =>
          simp [tick, h, e]
          rfl
      | some answer =>
          simp [tick, h, e]
          rfl

theorem tick_records {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (snapshot : Snapshot Node Answer)
    {node : Node} {answer : Answer} {pending : List Node}
    (horder : (orderScheduler rank).reorder snapshot.frontier = node :: pending)
    (hemits : system.emit node = some answer) :
    (tick system (orderScheduler rank) snapshot).events =
      snapshot.events ++ [⟨node, answer⟩] := by
  simp [tick, horder, hemits]
  rfl

theorem chosen_emission {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat)
    {node : Node} {answer : Answer}
    (hemits : system.emit node = some answer)
    (hselected : node ∈ choiceList rank system roots fuel) :
    (⟨node, answer⟩ : Emission Node Answer) ∈
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  simp only [choiceList, List.mem_filterMap, List.mem_range] at hselected
  obtain ⟨index, hindex, hchoice⟩ := hselected
  obtain ⟨pending, horder⟩ := cons_of_head? (by simpa [choiceAt] using hchoice)
  have htick := tick_records rank system
    (run system (orderScheduler rank) index (initial roots)) horder hemits
  have hmem :
      (⟨node, answer⟩ : Emission Node Answer) ∈
        (run system (orderScheduler rank) (index + 1) (initial roots)).events := by
    have hstep :
        run system (orderScheduler rank) (index + 1) (initial roots) =
          tick system (orderScheduler rank)
            (run system (orderScheduler rank) index (initial roots)) := rfl
    rw [hstep, htick]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  obtain ⟨extra, heq⟩ := Nat.le.dest (Nat.succ_le_of_lt hindex)
  have hprefix :
      (run system (orderScheduler rank) (index + 1) (initial roots)).events.IsPrefix
        (run system (orderScheduler rank) fuel (initial roots)).events := by
    have hfuel :
        run system (orderScheduler rank) fuel (initial roots) =
          run system (orderScheduler rank) extra
            (run system (orderScheduler rank) (index + 1) (initial roots)) := by
      have hadd := run_add system (orderScheduler rank) (index + 1) extra (initial roots)
      simpa [heq] using hadd
    rw [hfuel]
    exact events_prefix_run system (orderScheduler rank) extra _
  exact List.IsPrefix.mem hmem hprefix

theorem unemitted_reaches {Node Answer : Type _} [DecidableEq Node]
    (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) (fuel : Nat)
    {node : Node} {answer : Answer}
    (hgen : Generated system roots node) (hemits : system.emit node = some answer)
    (hnot : (⟨node, answer⟩ : Emission Node Answer) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events) :
    Generated system (run system (orderScheduler rank) fuel (initial roots)).frontier node := by
  rcases generated_accounted rank system roots fuel hgen with hselected | hreach
  · exact absurd (chosen_emission rank system roots fuel hemits hselected) hnot
  · exact hreach

theorem reaches_ranked {Node Answer : Type _} (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer)
    (mono : ∀ parent child, child ∈ system.successors parent → rank parent child)
    {frontier : List Node} {head : Node}
    (hleast : ∀ item ∈ frontier, rank head item) {node : Node}
    (hreaches : Generated system frontier node) : rank head node := by
  induction hreaches with
  | root hmem => exact hleast _ hmem
  | successor _ hchild ih => exact trans_of rank ih (mono _ _ hchild)

/-- When best-first emits an answer, no generated answer that is still
unemitted is strictly better in `rank`. -/
theorem best_first_lightest {Node Answer : Type _} [DecidableEq Node]
    (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node)
    (mono : ∀ parent child, child ∈ system.successors parent → rank parent child)
    (fuel : Nat) {node : Node} {answer : Answer}
    (hnew : (⟨node, answer⟩ : Emission Node Answer) ∈
      (run system (orderScheduler rank) (fuel + 1) (initial roots)).events)
    (hold : (⟨node, answer⟩ : Emission Node Answer) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events)
    {later : Node} {laterAnswer : Answer}
    (hgen : Generated system roots later) (hlater : system.emit later = some laterAnswer)
    (hnot : (⟨later, laterAnswer⟩ : Emission Node Answer) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events) :
    rank node later := by
  have htick := tick_events system (orderScheduler rank)
    (run system (orderScheduler rank) fuel (initial roots))
  have hstep :
      run system (orderScheduler rank) (fuel + 1) (initial roots) =
        tick system (orderScheduler rank)
          (run system (orderScheduler rank) fuel (initial roots)) := rfl
  rw [hstep, htick] at hnew
  rcases List.mem_append.mp hnew with halready | hfresh
  · exact absurd halready hold
  · cases horder : (orderScheduler rank).reorder
        (run system (orderScheduler rank) fuel (initial roots)).frontier with
    | nil => simp [horder] at hfresh
    | cons head pending =>
        cases hemits : system.emit head with
        | none => simp [horder, hemits] at hfresh
        | some value =>
            rw [horder] at hfresh
            simp [hemits] at hfresh
            obtain ⟨horigin, _hvalue⟩ := hfresh
            rw [horigin]
            have hreach := unemitted_reaches rank system roots fuel hgen hlater hnot
            have hleast := chosen_least rank _ horder
            exact reaches_ranked rank system mono hleast hreach

/-! ## Finite down-sets and no return -/

/-- If every generated item ranked at least as good as a live root belongs to
a finite bucket, and a selected bucket item never returns, best-first
selection reaches that root. -/
theorem least_first_selects {Node Answer : Type _} [DecidableEq Node]
    (rank : Node → Node → Prop)
    [DecidableRel rank] [IsTrans Node rank] [Std.Total rank]
    (system : BranchingSystem Node Answer) (roots : List Node) {target : Node}
    (hroot : target ∈ roots) (bucket : List Node)
    (bucket_complete : ∀ node, Generated system roots node → rank node target → node ∈ bucket)
    (noreturn : ∀ index node, choiceAt rank system roots index = some node → node ∈ bucket →
      ∀ extra, node ∉ (run system (orderScheduler rank) (index + 1 + extra) (initial roots)).frontier) :
    ∃ fuel, choiceAt rank system roots fuel = some target := by
  suffices ∀ remaining steps,
      steps + remaining = bucket.length →
      (∀ index, index < steps → choiceAt rank system roots index ≠ some target) →
      target ∈ (run system (orderScheduler rank) steps (initial roots)).frontier →
      (choiceList rank system roots steps).Nodup →
      (choiceList rank system roots steps).length = steps →
      (∀ item ∈ choiceList rank system roots steps, item ∈ bucket) →
      ∃ fuel, choiceAt rank system roots (steps + fuel) = some target by
    simpa using this bucket.length 0 (by simp) (by intro index hindex; cases hindex)
      (by simp [run, initial, hroot]) (by simp [choiceList]) (by simp [choiceList])
      (by intro item hitem; simp [choiceList] at hitem)
  intro remaining
  induction remaining with
  | zero =>
      intro steps hsum hinv hstay hlistNodup hlen hsub
      have hsteps : steps = bucket.length := by omega
      have htarget : target ∈ bucket :=
        bucket_complete target (Generated.root hroot)
          ((Std.Total.total (r := rank) target target).elim id id)
      have hnot : target ∉ choiceList rank system roots steps := by
        intro hmem
        simp only [choiceList, List.mem_filterMap, List.mem_range] at hmem
        obtain ⟨index, hindex, hchoice⟩ := hmem
        exact hinv index hindex hchoice
      have hcover := mem_of_same_length hlistNodup hsub (by simpa [hsteps] using hlen) htarget
      exact absurd hcover hnot
  | succ remaining ih =>
      intro steps hsum hinv hstay hlistNodup hlen hsub
      obtain ⟨node, hchoice⟩ := choice_some_of_mem rank system roots steps hstay
      by_cases htarget : node = target
      · exact ⟨0, by simp [hchoice, htarget]⟩
      · have horderPair := cons_of_head? (by simpa [choiceAt] using hchoice)
        obtain ⟨pending, horder⟩ := horderPair
        have hleast := chosen_least rank _ horder
        have hrank : rank node target := hleast target hstay
        have hsound := sound_run system (orderScheduler rank)
          (initial_sound system roots) steps
        have hgenerated : Generated system roots node := by
          have hfront : node ∈
              (run system (orderScheduler rank) steps (initial roots)).frontier := by
            have hperm := (orderScheduler rank).reorder_complete
              (run system (orderScheduler rank) steps (initial roots)).frontier
            rw [horder] at hperm
            exact hperm.mem_iff.mp (by simp)
          exact hsound.1 node hfront
        have hinBucket : node ∈ bucket := bucket_complete node hgenerated hrank
        have hfresh : node ∉ choiceList rank system roots steps := by
          intro hmem
          simp only [choiceList, List.mem_filterMap, List.mem_range] at hmem
          obtain ⟨index, hindex, hprev⟩ := hmem
          have hback := noreturn index node hprev hinBucket (steps - (index + 1))
          have hindexFuel : index + 1 + (steps - (index + 1)) = steps := by
            omega
          rw [hindexFuel] at hback
          have hliveNode : node ∈
              (run system (orderScheduler rank) steps (initial roots)).frontier := by
            have hperm := (orderScheduler rank).reorder_complete
              (run system (orderScheduler rank) steps (initial roots)).frontier
            rw [horder] at hperm
            exact hperm.mem_iff.mp (by simp)
          exact hback hliveNode
        have hlist := choiceList_succ rank system roots steps hchoice
        have hnodup' : (choiceList rank system roots (steps + 1)).Nodup := by
          rw [hlist, List.nodup_append]
          refine ⟨hlistNodup, by simp, ?_⟩
          intro left hleft right hright heq
          simp only [List.mem_singleton] at hright
          subst hright
          subst heq
          exact hfresh hleft
        have hlen' : (choiceList rank system roots (steps + 1)).length = steps + 1 := by
          rw [hlist]
          simp [hlen]
        have hsub' : ∀ item ∈ choiceList rank system roots (steps + 1), item ∈ bucket := by
          intro item hitem
          rw [hlist] at hitem
          rcases List.mem_append.mp hitem with hitem | hitem
          · exact hsub item hitem
          · simp only [List.mem_singleton] at hitem
            simpa [hitem] using hinBucket
        have hstay' : target ∈
            (run system (orderScheduler rank) (steps + 1) (initial roots)).frontier := by
          have hpending : target ∈ pending := by
            have hmemOrdered : target ∈ node :: pending := by
              have hperm := (orderScheduler rank).reorder_complete
                (run system (orderScheduler rank) steps (initial roots)).frontier
              rw [horder] at hperm
              exact hperm.mem_iff.mpr hstay
            rcases List.mem_cons.mp hmemOrdered with rfl | hpending
            · exact absurd rfl htarget
            · exact hpending
          have hfront := frontier_after_choice rank system
            (run system (orderScheduler rank) steps (initial roots)) horder
          have hstep :
              run system (orderScheduler rank) (steps + 1) (initial roots) =
                tick system (orderScheduler rank)
                  (run system (orderScheduler rank) steps (initial roots)) := rfl
          rw [hstep]
          exact hfront.symm ▸ List.mem_append_left _ hpending
        have hinv' : ∀ index, index < steps + 1 →
            choiceAt rank system roots index ≠ some target := by
          intro index hindex
          cases Nat.eq_or_lt_of_le (Nat.lt_succ_iff.mp hindex) with
          | inl heq =>
              intro hbad
              rw [heq] at hbad
              have : node = target := by
                simpa [hchoice] using hbad
              exact htarget this
          | inr hlt => exact hinv index hlt
        have hsum' : (steps + 1) + remaining = bucket.length := by omega
        obtain ⟨fuel, hfuel⟩ := ih (steps + 1) hsum' hinv' hstay' hnodup' hlen' hsub'
        exact ⟨fuel + 1, by simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hfuel⟩

/-! ## The stopping certificate under any scheduler -/

/-- The node a scheduler selects at a step. -/
def chosenAt {Node Answer : Type _} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (roots : List Node) (index : Nat) : Option Node :=
  selected scheduler (run system scheduler index (initial roots)).frontier

theorem chosen_successor_enters {Node Answer : Type _} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (roots : List Node) (index : Nat) {parent child : Node}
    (hchoice : chosenAt system scheduler roots index = some parent)
    (hchild : child ∈ system.successors parent) :
    child ∈ (run system scheduler (index + 1) (initial roots)).frontier := by
  exact BranchingTemporal.successor_mem_tick_of_selected system scheduler _ hchoice hchild

/-- A node on the frontier is later chosen, or is still on the frontier. -/
theorem entry_chosen_or_live {Node Answer : Type _} (system : BranchingSystem Node Answer)
    (scheduler : Scheduler Node) (roots : List Node) (start extra : Nat) {node : Node}
    (henter : node ∈ (run system scheduler start (initial roots)).frontier) :
    (∃ index, index < start + extra ∧ chosenAt system scheduler roots index = some node) ∨
      node ∈ (run system scheduler (start + extra) (initial roots)).frontier := by
  have starts : node ∈ (InferenceControl.Snapshot.run system
      (InferenceControl.Controller.fixed scheduler) start
      { search := initial roots, memory := () }).search.frontier := by
    rw [InferenceControl.Snapshot.fixed_run_search]
    exact henter
  have covered := InferenceControl.Snapshot.entry_selected_or_live system
    (InferenceControl.Controller.fixed scheduler)
    { search := initial roots, memory := () } start extra starts
  rcases covered with ⟨index, _, beforeEnd, choice⟩ | live
  · refine Or.inl ⟨index, beforeEnd, ?_⟩
    change selected scheduler (InferenceControl.Snapshot.run system
      (InferenceControl.Controller.fixed scheduler) index
      { search := initial roots, memory := () }).search.frontier = some node at choice
    simpa only [InferenceControl.Snapshot.fixed_run_search, chosenAt] using choice
  · exact Or.inr (by
      simpa only [InferenceControl.Snapshot.fixed_run_search] using live)

/-- Under any scheduler, every generated node has been chosen, or is still
reachable from the live frontier. -/
theorem generated_chosen_or_reachable {Node Answer : Type _}
    (system : BranchingSystem Node Answer) (scheduler : Scheduler Node) (roots : List Node)
    (fuel : Nat) {node : Node} (hgen : Generated system roots node) :
    (∃ index, index < fuel ∧ chosenAt system scheduler roots index = some node) ∨
      Generated system (run system scheduler fuel (initial roots)).frontier node := by
  have covered := InferenceControl.Snapshot.generated_selected_or_reachable system
    (InferenceControl.Controller.fixed scheduler)
    { search := initial roots, memory := () } fuel hgen
  change (∃ index, index < fuel ∧ selected scheduler
    (InferenceControl.Snapshot.run system (InferenceControl.Controller.fixed scheduler)
      index { search := initial roots, memory := () }).search.frontier = some node) ∨
    Generated system
      (InferenceControl.Snapshot.run system (InferenceControl.Controller.fixed scheduler)
        fuel { search := initial roots, memory := () }).search.frontier node at covered
  simpa only [InferenceControl.Snapshot.fixed_run_search, chosenAt] using covered

/-- Under a superior law, a weight no worse than every live frontier item's
bounds every node still reachable from that frontier. -/
theorem bound_reaches {W Node Answer : Type _} [Preorder W]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W)
    (law : Realized system s weight) {frontier : List Node} {bound : W}
    (certificate : ∀ item ∈ frontier, bound ≤ weight item) {node : Node}
    (hreach : Generated system frontier node) : bound ≤ weight node := by
  exact (law.stepBound.generated (fun _ _ => True.intro) certificate hreach).2

namespace Controlled

open Mettapedia.GSLT.Core.InferenceControl

/-- The frontier bound applies to unselected descendants under any stateful
controller, starting from an arbitrary captured snapshot. -/
theorem certificate_bounds_unchosen {W Node Answer Memory : Type*} [Preorder W]
    (system : BranchingSystem Node Answer) (weight : Node → W) (domain : Node → Prop)
    (law : StepBound system weight domain) (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      domain item) {bound : W}
    (certificate : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      bound ≤ weight item)
    {node : Node} (generated : Generated system snapshot.search.frontier node)
    (unchosen : ∀ index, index < fuel → InferenceControl.Snapshot.selected controller
      (InferenceControl.Snapshot.run system controller index snapshot) ≠ some node) :
    bound ≤ weight node := by
  rcases InferenceControl.Snapshot.generated_selected_or_reachable system controller
    snapshot fuel generated with ⟨index, beforeEnd, selection⟩ | reachable
  · exact absurd selection (unchosen index beforeEnd)
  · exact (law.generated frontierDomain certificate reachable).2

/-- An emitting node not yet represented in the event stream is bounded by
the live frontier, even after arbitrary controller-memory changes. -/
theorem certificate_bounds_unemitted {W Node Answer Memory : Type*} [Preorder W]
    (system : BranchingSystem Node Answer) (weight : Node → W) (domain : Node → Prop)
    (law : StepBound system weight domain) (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      domain item) {bound : W}
    (certificate : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      bound ≤ weight item)
    {node : Node} {answer : Answer}
    (generated : Generated system snapshot.search.frontier node)
    (emits : system.emit node = some answer)
    (unemitted : (⟨node, answer⟩ : Emission Node Answer) ∉
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.events) :
    bound ≤ weight node := by
  rcases InferenceControl.Snapshot.generated_emitted_or_reachable system controller
    snapshot fuel generated emits with emitted | reachable
  · exact absurd emitted unemitted
  · exact (law.generated frontierDomain certificate reachable).2

/-- A selected/unselected answer observation needs bounds on both forms of
residual: reachable frontier work and retained, unaccepted events. In
particular a parked result is not discharged by an empty runnable frontier.
The bound concerns this fixed system; revising a parked result's meaning
requires a separate preservation law. -/
theorem certificate_bounds_unaccepted {W Node Answer Memory : Type*} [Preorder W]
    (system : BranchingSystem Node Answer) (weight : Node → W) (domain : Node → Prop)
    (law : StepBound system weight domain) (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      domain item) {bound : W}
    (accepted : Emission Node Answer → Prop)
    (frontierBound : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      bound ≤ weight item)
    (retainedBound : ∀ event ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.events,
      ¬ accepted event → bound ≤ weight event.origin)
    {node : Node} {answer : Answer}
    (generated : Generated system snapshot.search.frontier node)
    (emits : system.emit node = some answer)
    (unaccepted : ¬ accepted ⟨node, answer⟩) :
    bound ≤ weight node := by
  rcases InferenceControl.Snapshot.generated_emitted_or_reachable system controller
    snapshot fuel generated emits with emitted | reachable
  · exact retainedBound _ emitted unaccepted
  · exact (law.generated frontierDomain frontierBound reachable).2

/-- A finite selected batch is no worse than any unaccepted emitting node
when both residual bounds hold. Occurrence identities belong in `Node` and
`accepted`; this theorem neither deduplicates answers nor supplies the
requested batch size. -/
theorem early_stop_selects_best {W Node Answer Memory : Type*} [Preorder W]
    (system : BranchingSystem Node Answer) (weight : Node → W) (domain : Node → Prop)
    (law : StepBound system weight domain) (controller : Controller Node Answer Memory)
    (snapshot : InferenceControl.Snapshot Node Answer Memory) (fuel : Nat)
    (frontierDomain : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      domain item) {bound : W}
    (accepted : Emission Node Answer → Prop)
    (frontierBound : ∀ item ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.frontier,
      bound ≤ weight item)
    (retainedBound : ∀ event ∈
      (InferenceControl.Snapshot.run system controller fuel snapshot).search.events,
      ¬ accepted event → bound ≤ weight event.origin)
    {selections : List Node} (selectedBound : ∀ chosen ∈ selections, weight chosen ≤ bound)
    {node : Node} {answer : Answer}
    (generated : Generated system snapshot.search.frontier node)
    (emits : system.emit node = some answer)
    (unaccepted : ¬ accepted ⟨node, answer⟩) :
    ∀ chosen ∈ selections, weight chosen ≤ weight node := fun chosen member =>
  le_trans (selectedBound chosen member)
    (certificate_bounds_unaccepted system weight domain law controller snapshot fuel
      frontierDomain accepted frontierBound retainedBound generated emits unaccepted)

end Controlled

/-- The stopping certificate.  Under a superior law and any scheduler, when no
live frontier item is lighter than `bound`, no generated node that has not
yet been chosen is lighter than `bound` either. -/
theorem certificate_bounds_unchosen {W Node Answer : Type _} [Preorder W]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W)
    (law : Realized system s weight) (scheduler : Scheduler Node) (roots : List Node)
    (fuel : Nat) {bound : W}
    (certificate : ∀ item ∈ (run system scheduler fuel (initial roots)).frontier,
      bound ≤ weight item)
    {node : Node} (hgen : Generated system roots node)
    (hunchosen : ∀ index, index < fuel → chosenAt system scheduler roots index ≠ some node) :
    bound ≤ weight node := by
  rcases generated_chosen_or_reachable system scheduler roots fuel hgen with
    ⟨index, hindex, hchoice⟩ | hreach
  · exact absurd hchoice (hunchosen index hindex)
  · exact bound_reaches system s weight law certificate hreach

/-- Early best-k is sound: selections no heavier than the certified bound
are no heavier than any node, answer or not, the search has yet to choose. -/
theorem early_stop_selects_best {W Node Answer : Type _} [Preorder W]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W)
    (law : Realized system s weight) (scheduler : Scheduler Node) (roots : List Node)
    (fuel : Nat) {bound : W}
    (certificate : ∀ item ∈ (run system scheduler fuel (initial roots)).frontier,
      bound ≤ weight item)
    {selections : List Node} (hselected : ∀ chosen ∈ selections, weight chosen ≤ bound)
    {node : Node} (hgen : Generated system roots node)
    (hunchosen : ∀ index, index < fuel → chosenAt system scheduler roots index ≠ some node) :
    ∀ chosen ∈ selections, weight chosen ≤ weight node := fun chosen hmem =>
  le_trans (hselected chosen hmem)
    (certificate_bounds_unchosen system s weight law scheduler roots fuel certificate hgen hunchosen)

/-- Order nodes by their accumulated weight. -/
def byWeight {W Node : Type _} [LinearOrder W] (weight : Node → W) (left right : Node) : Prop :=
  weight left ≤ weight right

instance {W Node : Type _} [LinearOrder W] (weight : Node → W) :
    DecidableRel (byWeight weight) := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance {W Node : Type _} [LinearOrder W] (weight : Node → W) :
    IsTrans Node (byWeight weight) := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance {W Node : Type _} [LinearOrder W] (weight : Node → W) :
    Std.Total (byWeight weight) := ⟨fun left right => le_total (weight left) (weight right)⟩

/-- Under a superior law, best-first by accumulated weight emits a best
answer first: no generated answer still unemitted is lighter. -/
theorem best_first_best_under_law {W Node Answer : Type _} [LinearOrder W] [DecidableEq Node]
    (system : BranchingSystem Node Answer) (s : Superior W) (weight : Node → W)
    (law : Realized system s weight) (roots : List Node) (fuel : Nat)
    {node : Node} {answer : Answer}
    (hnew : (⟨node, answer⟩ : Emission Node Answer) ∈
      (run system (orderScheduler (byWeight weight)) (fuel + 1) (initial roots)).events)
    (hold : (⟨node, answer⟩ : Emission Node Answer) ∉
      (run system (orderScheduler (byWeight weight)) fuel (initial roots)).events)
    {later : Node} {laterAnswer : Answer}
    (hgen : Generated system roots later) (hlater : system.emit later = some laterAnswer)
    (hnot : (⟨later, laterAnswer⟩ : Emission Node Answer) ∉
      (run system (orderScheduler (byWeight weight)) fuel (initial roots)).events) :
    weight node ≤ weight later :=
  best_first_lightest (byWeight weight) system roots
    (fun parent child hchild => realized_monotone system s weight law parent child hchild)
    fuel hnew hold hgen hlater hnot

/-! ## Positive control: the lighter answer is emitted first -/

namespace LightFirst

inductive Node where
  | root
  | light
  | heavy
deriving DecidableEq, Repr

def weight : Node → Nat
  | .root => 0
  | .light => 1
  | .heavy => 5

def system : BranchingSystem Node Nat where
  emit
    | .root => none
    | .light => some 1
    | .heavy => some 5
  successors
    | .root => [.heavy, .light]
    | .light => []
    | .heavy => []

def rank (left right : Node) : Prop := weight left ≤ weight right

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance : Std.Total rank := ⟨fun left right => le_total (weight left) (weight right)⟩

theorem realized : Realized system natAdd weight where
  accumulated parent child hmem := by
    cases parent with
    | root =>
        simp [system] at hmem
        rcases hmem with rfl | rfl
        · exact ⟨5, by simp [weight, natAdd]⟩
        · exact ⟨1, by simp [weight, natAdd]⟩
    | light => simp [system] at hmem
    | heavy => simp [system] at hmem

/-- The successor list names the heavier node first.  Best-first still emits
the lighter answer first. -/
theorem emits_light_before_heavy :
    (run system (orderScheduler rank) 2 (initial [.root])).events = [⟨.light, 1⟩] := by
  decide

/-- The policy changes after each selected occurrence. It is not a fixed
best-first scheduler: the first expansion uses FIFO and the next uses the
reverse frontier. -/
def adaptive : InferenceControl.Controller Node Nat Bool where
  initialMemory := false
  scheduler changed := if changed then Scheduler.reverseBreadthFirst else Scheduler.breadthFirst
  advance changed _ _ _ := !changed

def adaptiveRun (fuel : Nat) :=
  InferenceControl.Snapshot.run system adaptive fuel
    (InferenceControl.Snapshot.initial adaptive [.root])

theorem adaptive_prefix_keeps_heavy_pending :
    (adaptiveRun 2).search.events = [⟨.light, 1⟩] ∧
      (adaptiveRun 2).search.frontier = [.heavy] ∧
      (adaptiveRun 1).memory = true ∧ (adaptiveRun 2).memory = false := by
  decide

/-- The certificate applies after resuming with the changed policy memory,
and bounds every generated emitting node still absent from the event stream. -/
theorem resumed_bound {node : Node} {answer : Nat}
    (generated : Generated system (adaptiveRun 1).search.frontier node)
    (emits : system.emit node = some answer)
    (unemitted : (⟨node, answer⟩ : Emission Node Nat) ∉ (adaptiveRun 2).search.events) :
    1 ≤ weight node := by
  have resumed : InferenceControl.Snapshot.run system adaptive 1 (adaptiveRun 1) =
      adaptiveRun 2 := (InferenceControl.Snapshot.run_add system adaptive 1 1 _).symm
  refine Controlled.certificate_bounds_unemitted system weight (fun _ => True)
    realized.stepBound adaptive (adaptiveRun 1) 1 (fun _ _ => True.intro)
    (bound := 1) ?_ generated emits ?_
  · rw [resumed, adaptive_prefix_keeps_heavy_pending.2.1]
    intro item member
    have same := List.mem_singleton.mp member
    subst item
    decide
  · simpa only [resumed] using unemitted

/-- Empty runnable work does not bound already retained, unaccepted results.
Here all transitions satisfy the superior law, but accepting only the heavy
answer cannot justify discarding the lighter retained occurrence. -/
theorem frontier_only_misses_retained_answer :
    (∀ item ∈ (adaptiveRun 3).search.frontier, 5 ≤ weight item) ∧
      ∃ event ∈ (adaptiveRun 3).search.events,
        event.origin ≠ .heavy ∧ ¬ 5 ≤ weight event.origin := by
  constructor
  · intro item member
    change item ∈ ([] : List Node) at member
    simp at member
  · exact ⟨⟨.light, 1⟩, by decide, by decide, by decide⟩

end LightFirst

/-! ## Negative control: a non-superior weight emits a heavier answer first -/

namespace Suboptimal

inductive Node where
  | root
  | heavy
  | mid
  | light
deriving DecidableEq, Repr

def weight : Node → Int
  | .root => 0
  | .heavy => 2
  | .mid => 3
  | .light => 0

def system : BranchingSystem Node Int where
  emit
    | .heavy => some 2
    | .light => some 0
    | _ => none
  successors
    | .root => [.heavy, .mid]
    | .mid => [.light]
    | _ => []

def rank (left right : Node) : Prop := weight left ≤ weight right

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance : Std.Total rank := ⟨fun left right => le_total (weight left) (weight right)⟩

theorem not_monotone :
    ¬ ∀ parent child, child ∈ system.successors parent → weight parent ≤ weight child := by
  intro hmono
  have hle := hmono .mid .light (by simp [system])
  simp [weight] at hle

theorem light_generated : Generated system [.root] .light := by
  refine Generated.successor (parent := .mid) ?_ ?_
  · refine Generated.successor (parent := .root) ?_ ?_
    · exact Generated.root (by simp)
    · simp [system]
  · simp [system]

/-- Best-first emits the heavier answer while a lighter generated answer
remains outstanding. -/
theorem emits_heavy_first :
    (run system (orderScheduler rank) 2 (initial [.root])).events = [⟨.heavy, 2⟩] ∧
      weight .light < weight .heavy := by
  refine ⟨?_, by decide⟩
  · decide

end Suboptimal

/-! ## Negative control: without the law the certificate misses the best answer

Coefficients under multiplication, larger is better, with one factor above
one.  After three best-first steps rain (27/50) is emitted and the only live
item weighs 1/10, so the certificate holds; the sprinkler derivation it
leads to weighs 1/10 * 20 = 2 and is strictly better. -/

namespace LawBroken

inductive Node where
  | root
  | sprinklerStep
  | rainStep
  | sprinkler
  | rain
deriving DecidableEq, Repr

def coefficient : Node → ℚ
  | .root => 1
  | .sprinklerStep => 1 / 10
  | .rainStep => 9 / 10
  | .sprinkler => 1 / 10 * 20
  | .rain => 9 / 10 * (6 / 10)

def system : BranchingSystem Node Unit where
  emit
    | .sprinkler => some ()
    | .rain => some ()
    | _ => none
  successors
    | .root => [.sprinklerStep, .rainStep]
    | .sprinklerStep => [.sprinkler]
    | .rainStep => [.rain]
    | _ => []

/-- Larger coefficients first. -/
def rank (left right : Node) : Prop := coefficient right ≤ coefficient left

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (coefficient right ≤ coefficient left))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hright hleft⟩

instance : Std.Total rank := ⟨fun left right => le_total (coefficient right) (coefficient left)⟩

theorem run_three :
    run system (orderScheduler rank) 3 (initial [.root]) =
      ⟨[⟨.rain, ()⟩], [.sprinklerStep]⟩ := by
  decide +kernel

/-- No live item beats the emitted rain answer. -/
theorem certificate_holds :
    ∀ item ∈ (run system (orderScheduler rank) 3 (initial [.root])).frontier,
      coefficient item ≤ coefficient .rain := by
  rw [run_three]
  intro item hitem
  simp only [List.mem_singleton] at hitem
  subst hitem
  norm_num [coefficient]

theorem sprinkler_generated : Generated system [.root] .sprinkler :=
  Generated.successor (parent := .sprinklerStep)
    (Generated.successor (parent := .root) (Generated.root (by simp)) (by simp [system]))
    (by simp [system])

theorem sprinkler_better : coefficient .rain < coefficient .sprinkler := by
  norm_num [coefficient]

/-- The law fails at the factor above one: that step raises the coefficient. -/
theorem not_monotone :
    ¬ ∀ parent child, child ∈ system.successors parent →
      coefficient child ≤ coefficient parent := by
  intro hmono
  have h := hmono .sprinklerStep .sprinkler (by simp [system])
  norm_num [coefficient] at h

end LawBroken

/-! ## Negative control: one returning weight-zero item starves a neighbour -/

namespace ReturningZero

inductive Node where
  | loop
  | goal
deriving DecidableEq, Repr

def weight : Node → Nat
  | .loop => 0
  | .goal => 1

def system : BranchingSystem Node Nat where
  emit
    | .loop => none
    | .goal => some 1
  successors
    | .loop => [.loop]
    | .goal => []

def roots : List Node := [.loop, .goal]

def rank (left right : Node) : Prop := weight left ≤ weight right

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance : Std.Total rank := ⟨fun left right => le_total (weight left) (weight right)⟩

/-- The goal is at most as heavy as itself, and the loop is lighter, so the
class of nodes no heavier than the goal is this finite node set.  Selection
still fails because the selected loop returns. -/
theorem both_nodes_are_light (node : Node) : weight node ≤ weight .goal := by
  cases node <;> decide

theorem sort_goal_loop :
    (orderScheduler rank).reorder [.goal, .loop] = [.loop, .goal] :=
  reorder_pair_not rank (by simp [rank, weight])

theorem sort_loop_goal :
    (orderScheduler rank).reorder [.loop, .goal] = [.loop, .goal] :=
  reorder_pair_le rank (by simp [rank, weight])

theorem step_from_zero :
    run system (orderScheduler rank) 1 (initial roots) = ⟨[], [.goal, .loop]⟩ := by
  have hstart : run system (orderScheduler rank) 0 (initial roots) =
      (⟨[], [.loop, .goal]⟩ : Snapshot Node Nat) := by
    simp [run, initial, roots]
  rw [run, hstart]
  simp only [tick]
  rw [sort_loop_goal]
  simp [system, orderScheduler]
  rfl

theorem step_stable (fuel : Nat)
    (hprev : run system (orderScheduler rank) fuel (initial roots) = ⟨[], [.goal, .loop]⟩) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) = ⟨[], [.goal, .loop]⟩ := by
  rw [run, hprev]
  simp only [tick]
  rw [sort_goal_loop]
  simp [system, orderScheduler]
  rfl

theorem silent_after (fuel : Nat) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) = ⟨[], [.goal, .loop]⟩ := by
  induction fuel with
  | zero => exact step_from_zero
  | succ fuel ih => exact step_stable (fuel + 1) ih

/-- The light class is finite, but the selected light item returns, so the
heavier goal is never emitted. -/
theorem goal_starves (fuel : Nat) :
    (⟨.goal, 1⟩ : Emission Node Nat) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel =>
      simp [silent_after fuel]

end ReturningZero

/-! ## Negative control: an infinite weight-zero chain -/

namespace ZeroChain

inductive Node where
  | zero : Nat → Node
  | target
deriving DecidableEq, Repr

def weight : Node → Nat
  | .zero _ => 0
  | .target => 1

def system : BranchingSystem Node Nat where
  emit
    | .zero _ => none
    | .target => some 1
  successors
    | .zero n => [.zero (n + 1)]
    | .target => []

def roots : List Node := [.zero 0, .target]

def rank (left right : Node) : Prop := weight left ≤ weight right

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance : Std.Total rank := ⟨fun left right => le_total (weight left) (weight right)⟩

theorem zero_generated (n : Nat) : Generated system roots (.zero n) := by
  induction n with
  | zero => exact Generated.root (by simp [roots])
  | succ n ih => exact Generated.successor ih (by simp [system])

theorem sort_target_zero (n : Nat) :
    (orderScheduler rank).reorder [.target, .zero n] = [.zero n, .target] :=
  reorder_pair_not rank (by simp [rank, weight])

theorem sort_zero_target (n : Nat) :
    (orderScheduler rank).reorder [.zero n, .target] = [.zero n, .target] :=
  reorder_pair_le rank (by simp [rank, weight])

theorem step_from_zero :
    run system (orderScheduler rank) 1 (initial roots) = ⟨[], [.target, .zero 1]⟩ := by
  have hstart : run system (orderScheduler rank) 0 (initial roots) =
      (⟨[], [.zero 0, .target]⟩ : Snapshot Node Nat) := by
    simp [run, initial, roots]
  rw [run, hstart]
  simp only [tick]
  rw [sort_zero_target 0]
  simp [system, orderScheduler]
  rfl

theorem step_stable (fuel : Nat)
    (hprev : run system (orderScheduler rank) fuel (initial roots) =
      ⟨[], [.target, .zero fuel]⟩) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.target, .zero (fuel + 1)]⟩ := by
  rw [run, hprev]
  simp only [tick]
  rw [sort_target_zero fuel]
  simp [system, orderScheduler]
  rfl

theorem silent_after (fuel : Nat) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.target, .zero (fuel + 1)]⟩ := by
  induction fuel with
  | zero => exact step_from_zero
  | succ fuel ih => exact step_stable (fuel + 1) ih

theorem target_starves (fuel : Nat) :
    (⟨.target, 1⟩ : Emission Node Nat) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel => simp [silent_after fuel]

/-- No finite bucket contains every generated weight-zero item. -/
theorem no_finite_light_bucket (bucket : List Node) :
    ¬ (∀ node, Generated system roots node → weight node ≤ weight .target → node ∈ bucket) := by
  intro hcomplete
  let counted := (List.range (bucket.length + 1)).map Node.zero
  have hnodup : counted.Nodup :=
    List.Nodup.map (fun left right h => by
      cases h
      rfl) (List.nodup_range (n := bucket.length + 1))
  have hsub : ∀ node ∈ counted, node ∈ bucket := by
    intro node hmem
    simp only [counted, List.mem_map, List.mem_range] at hmem
    obtain ⟨index, -, rfl⟩ := hmem
    exact hcomplete (.zero index) (zero_generated index) (by simp [weight])
  have hlen := length_le_of_nodup_mem hnodup hsub
  simp [counted, List.length_map, List.length_range] at hlen

end ZeroChain

/-! ## Decreasing weights starve; an age lane does not -/

namespace Descending

inductive Node where
  | nest : Nat → Node
  | goal
deriving DecidableEq, Repr

def weight : Node → Int
  | .nest n => -(n : Int)
  | .goal => 1

def system : BranchingSystem Node Nat where
  emit
    | .nest _ => none
    | .goal => some 1
  successors
    | .nest n => [.nest (n + 1)]
    | .goal => []

def roots : List Node := [.nest 0, .goal]

def rank (left right : Node) : Prop := weight left ≤ weight right

instance : DecidableRel rank := fun left right =>
  inferInstanceAs (Decidable (weight left ≤ weight right))

instance : IsTrans Node rank := ⟨fun _ _ _ hleft hright => le_trans hleft hright⟩

instance : Std.Total rank := ⟨fun left right => le_total (weight left) (weight right)⟩

theorem child_is_lighter (n : Nat) :
    weight (.nest (n + 1)) < weight (.nest n) := by
  simp [weight]

theorem not_goal_before_nest (n : Nat) : ¬ rank .goal (.nest n) := by
  simp [rank, weight]
  omega

theorem nest_before_goal (n : Nat) : rank (.nest n) .goal := by
  simp [rank, weight]

theorem sort_goal_nest (n : Nat) :
    (orderScheduler rank).reorder [.goal, .nest n] = [.nest n, .goal] :=
  reorder_pair_not rank (not_goal_before_nest n)

theorem sort_nest_goal (n : Nat) :
    (orderScheduler rank).reorder [.nest n, .goal] = [.nest n, .goal] :=
  reorder_pair_le rank (nest_before_goal n)

theorem step_from_zero :
    run system (orderScheduler rank) 1 (initial roots) = ⟨[], [.goal, .nest 1]⟩ := by
  have hstart : run system (orderScheduler rank) 0 (initial roots) =
      (⟨[], [.nest 0, .goal]⟩ : Snapshot Node Nat) := by
    simp [run, initial, roots]
  rw [run, hstart]
  simp only [tick]
  rw [sort_nest_goal 0]
  simp [system, orderScheduler]
  rfl

theorem step_stable (fuel : Nat)
    (hprev : run system (orderScheduler rank) fuel (initial roots) =
      ⟨[], [.goal, .nest fuel]⟩) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.goal, .nest (fuel + 1)]⟩ := by
  rw [run, hprev]
  simp only [tick]
  rw [sort_goal_nest fuel]
  simp [system, orderScheduler]
  rfl

theorem silent_after (fuel : Nat) :
    run system (orderScheduler rank) (fuel + 1) (initial roots) =
      ⟨[], [.goal, .nest (fuel + 1)]⟩ := by
  induction fuel with
  | zero => exact step_from_zero
  | succ fuel ih => exact step_stable (fuel + 1) ih

theorem goal_starves (fuel : Nat) :
    (⟨.goal, 1⟩ : Emission Node Nat) ∉
      (run system (orderScheduler rank) fuel (initial roots)).events := by
  cases fuel with
  | zero => simp [run, initial]
  | succ fuel => simp [silent_after fuel]

/-- The same goal is selected by a portfolio whose age lane is breadth-first,
even though these weights decrease and so are not superior. -/
theorem age_lane_selects_goal :
    ∃ fuel,
      Node.goal ∈
        (PortfolioSnapshot.run system
          (withPriorityShare 1 QueueDiscipline.depthFirst).disciplines fuel
          ((withPriorityShare (Node := Node) 1 QueueDiscipline.depthFirst).initial
            (Answer := Nat) roots 0)).selections :=
  (withPriorityShare (Node := Node) 1 QueueDiscipline.depthFirst).eventually_selects_root
    system roots 0 (by simp [roots])

end Descending

end Mettapedia.GSLT.Core.WeightOrderedSelection
