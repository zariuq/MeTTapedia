import Mettapedia.TypeTheory.MaterialSets.Hypersets.Bisimulation
import Mathlib.Logic.Equiv.Basic

/-!
# The finite graphs that separate the axioms

Five pictures carry the comparisons.

* The one-node loop. Its unfolding is an infinite chain. It is strongly extensional.
* The two-node cycle. Each node has the other as its only child. The two unfoldings are
  chains, and the two pointed graphs are isomorphic, but the two nodes have different children.
* The Scott pair. One node is a loop; the other has both nodes as children. The nodes are
  bisimilar, and their unfoldings are not isomorphic: the roots have one and two children.
* The Finsler triple. Node `n0` has only `n1` as a child; `n1` has `n0` and `n2`; `n2` has
  `n0` and `n1`. The unfoldings of `n1` and `n2` are isomorphic. No two pointed downsets are.
* The nest. A childless node and a node whose children are that node and itself. The two
  nodes are not bisimilar.

Membership chains are written as inductive paths, so an isomorphism of unfoldings is a
bijection of those paths sending a one-step extension to a one-step extension.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

open Mettapedia.TypeTheory.MaterialSets.Hypersets

inductive Loop where
  | node
  deriving DecidableEq

def loopEdge : Loop → Loop → Prop
  | .node, .node => True

inductive Cycle where
  | l
  | r
  deriving DecidableEq

def cycleEdge : Cycle → Cycle → Prop
  | .l, .r => True
  | .r, .l => True
  | _, _ => False

inductive Scott where
  | s0
  | s1
  deriving DecidableEq

/-- `s0` is a loop. `s1` has both nodes as children. `s1` is not a child of `s0`. -/
def scottEdge : Scott → Scott → Prop
  | .s0, .s0 => True
  | .s1, .s0 => True
  | .s1, .s1 => True
  | .s0, .s1 => False

inductive Fin3 where
  | n0
  | n1
  | n2
  deriving DecidableEq

/-- `n0` has child `n1`; `n1` has children `n0` and `n2`; `n2` has children `n0` and `n1`. -/
def finEdge : Fin3 → Fin3 → Prop
  | .n0, .n1 => True
  | .n1, .n0 => True
  | .n1, .n2 => True
  | .n2, .n0 => True
  | .n2, .n1 => True
  | _, _ => False

inductive Nest where
  | blank
  | point
  deriving DecidableEq

def nestEdge : Nest → Nest → Prop
  | .point, .blank => True
  | .point, .point => True
  | _, _ => False

inductive EmptyG where
  | node
  deriving DecidableEq

def emptyEdge : EmptyG → EmptyG → Prop
  | _, _ => False

/-! ## Paths -/

inductive PathLoop where
  | here
  | step : PathLoop → PathLoop

inductive PathS0 where
  | here
  | step : PathS0 → PathS0

/-- Paths from `s1`: one step to the loop, or one step back to `s1`. -/
inductive PathS1 where
  | here
  | to0 : PathS0 → PathS1
  | to1 : PathS1 → PathS1

mutual
  inductive PathL where
    | here
    | toR : PathR → PathL
  inductive PathR where
    | here
    | toL : PathL → PathR
end

mutual
  inductive FinPath0 where
    | here
    | to1 : FinPath1 → FinPath0
  inductive FinPath1 where
    | here
    | to0 : FinPath0 → FinPath1
    | to2 : FinPath2 → FinPath1
  inductive FinPath2 where
    | here
    | to0 : FinPath0 → FinPath2
    | to1 : FinPath1 → FinPath2
end

def s0ToLoop : PathS0 → PathLoop
  | .here => .here
  | .step p => .step (s0ToLoop p)

def loopToS0 : PathLoop → PathS0
  | .here => .here
  | .step p => .step (loopToS0 p)

theorem loopToS0_s0ToLoop (p : PathS0) : loopToS0 (s0ToLoop p) = p := by
  induction p with
  | here => rfl
  | step p ih => exact congrArg PathS0.step ih

theorem s0ToLoop_loopToS0 (p : PathLoop) : s0ToLoop (loopToS0 p) = p := by
  induction p with
  | here => rfl
  | step p ih => exact congrArg PathLoop.step ih

mutual
  def lenL : PathL → Nat
    | .here => 0
    | .toR p => lenR p + 1
  def lenR : PathR → Nat
    | .here => 0
    | .toL p => lenL p + 1
end

mutual
  def ofNatL : Nat → PathL
    | 0 => .here
    | n + 1 => .toR (ofNatR n)
  def ofNatR : Nat → PathR
    | 0 => .here
    | n + 1 => .toL (ofNatL n)
end

theorem len_ofNat (n : Nat) : lenL (ofNatL n) = n ∧ lenR (ofNatR n) = n := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    constructor
    · show lenR (ofNatR n) + 1 = n + 1
      rw [ih.2]
    · show lenL (ofNatL n) + 1 = n + 1
      rw [ih.1]

theorem lenL_ofNatL (n : Nat) : lenL (ofNatL n) = n := (len_ofNat n).1

theorem lenR_ofNatR (n : Nat) : lenR (ofNatR n) = n := (len_ofNat n).2

/-- Each cycle path is the chain of its length. Proved together, by induction on that length. -/
theorem ofNat_len :
    (∀ p : PathL, ofNatL (lenL p) = p) ∧ (∀ p : PathR, ofNatR (lenR p) = p) := by
  suffices h : ∀ n,
      (∀ p : PathL, lenL p ≤ n → ofNatL (lenL p) = p) ∧
      (∀ p : PathR, lenR p ≤ n → ofNatR (lenR p) = p) by
    exact ⟨fun p => (h (lenL p)).1 p (Nat.le_refl _),
      fun p => (h (lenR p)).2 p (Nat.le_refl _)⟩
  intro n
  induction n with
  | zero =>
    constructor
    · intro p hp
      cases p with
      | here => rfl
      | toR q => exact absurd hp (Nat.not_succ_le_zero (lenR q))
    · intro p hp
      cases p with
      | here => rfl
      | toL q => exact absurd hp (Nat.not_succ_le_zero (lenL q))
  | succ n ih =>
    constructor
    · intro p hp
      cases p with
      | here => rfl
      | toR q =>
        exact congrArg PathL.toR (ih.2 q (Nat.le_of_succ_le_succ hp))
    · intro p hp
      cases p with
      | here => rfl
      | toL q =>
        exact congrArg PathR.toL (ih.1 q (Nat.le_of_succ_le_succ hp))

theorem ofNatL_lenL (p : PathL) : ofNatL (lenL p) = p := (ofNat_len).1 p

theorem ofNatR_lenR (p : PathR) : ofNatR (lenR p) = p := (ofNat_len).2 p

/-- The two cycle nodes have isomorphic unfoldings: both path trees are the chain of lengths. -/
def cycleUnfoldLtoR (p : PathL) : PathR :=
  ofNatR (lenL p)

def cycleUnfoldRtoL (p : PathR) : PathL :=
  ofNatL (lenR p)

theorem cycleUnfold_left_right (p : PathL) : cycleUnfoldRtoL (cycleUnfoldLtoR p) = p := by
  unfold cycleUnfoldRtoL cycleUnfoldLtoR
  rw [lenR_ofNatR, ofNatL_lenL]

theorem cycleUnfold_right_left (p : PathR) : cycleUnfoldLtoR (cycleUnfoldRtoL p) = p := by
  unfold cycleUnfoldLtoR cycleUnfoldRtoL
  rw [lenL_ofNatL, ofNatR_lenR]

/-- Roots go to roots, and the single one-step extension goes to the single one-step extension. -/
theorem cycleUnfold_root : cycleUnfoldLtoR PathL.here = PathR.here := rfl

theorem cycleUnfold_step :
    cycleUnfoldLtoR (PathL.toR PathR.here) = PathR.toL PathL.here := rfl

mutual
  /-- Unfoldings of the Finsler nodes n1 and n2. The step through n0 is shared.
  The other step swaps the two nodes. -/
  def f12 : FinPath1 → FinPath2
    | .here => .here
    | .to0 p => .to0 p
    | .to2 q => .to1 (f21 q)
  def f21 : FinPath2 → FinPath1
    | .here => .here
    | .to0 p => .to0 p
    | .to1 r => .to2 (f12 r)
end

mutual
  def depth1 : FinPath1 → Nat
    | .here => 0
    | .to0 _ => 0
    | .to2 q => depth2 q + 1
  def depth2 : FinPath2 → Nat
    | .here => 0
    | .to0 _ => 0
    | .to1 r => depth1 r + 1
end

/-- The two Finsler unfoldings are inverse. Proved together, by induction on the swap depth. -/
theorem f_round :
    (∀ p : FinPath1, f21 (f12 p) = p) ∧ (∀ q : FinPath2, f12 (f21 q) = q) := by
  suffices h : ∀ n,
      (∀ p : FinPath1, depth1 p ≤ n → f21 (f12 p) = p) ∧
      (∀ q : FinPath2, depth2 q ≤ n → f12 (f21 q) = q) by
    exact ⟨fun p => (h (depth1 p)).1 p (Nat.le_refl _),
      fun q => (h (depth2 q)).2 q (Nat.le_refl _)⟩
  intro n
  induction n with
  | zero =>
    constructor
    · intro p hp
      cases p with
      | here => rfl
      | to0 _ => rfl
      | to2 q => exact absurd hp (Nat.not_succ_le_zero (depth2 q))
    · intro q hp
      cases q with
      | here => rfl
      | to0 _ => rfl
      | to1 r => exact absurd hp (Nat.not_succ_le_zero (depth1 r))
  | succ n ih =>
    constructor
    · intro p hp
      cases p with
      | here => rfl
      | to0 _ => rfl
      | to2 q =>
        exact congrArg FinPath1.to2 (ih.2 q (Nat.le_of_succ_le_succ hp))
    · intro q hp
      cases q with
      | here => rfl
      | to0 _ => rfl
      | to1 r =>
        exact congrArg FinPath2.to1 (ih.1 r (Nat.le_of_succ_le_succ hp))

theorem f21_f12 (p : FinPath1) : f21 (f12 p) = p := (f_round).1 p

theorem f12_f21 (q : FinPath2) : f12 (f21 q) = q := (f_round).2 q

theorem f12_root : f12 FinPath1.here = FinPath2.here := rfl

theorem f12_to0 (p : FinPath0) : f12 (FinPath1.to0 p) = FinPath2.to0 p := rfl

theorem f12_to2 (q : FinPath2) : f12 (FinPath1.to2 q) = FinPath2.to1 (f21 q) := rfl

/-- `s0` has one path of length one. `s1` has two, and they are distinct. -/
theorem pathS1_children_distinct : PathS1.to0 .here ≠ PathS1.to1 .here := by
  intro h
  exact PathS1.noConfusion h

theorem not_scott_unfolding_iso :
    ¬ ∃ f : PathS0 → PathS1,
      f .here = .here ∧
      (∃ p, f p = .to0 .here) ∧
      (∃ p, f p = .to1 .here) ∧
      (∀ p, f p = .to0 .here ∨ f p = .to1 .here → p = .step .here) := by
  intro ⟨f, _, ⟨p0, hp0⟩, ⟨p1, hp1⟩, only⟩
  have h0 : p0 = .step .here := only p0 (Or.inl hp0)
  have h1 : p1 = .step .here := only p1 (Or.inr hp1)
  have same : f p0 = f p1 := by rw [h0, h1]
  rw [hp0, hp1] at same
  exact pathS1_children_distinct same

/-! ## Downsets of the Finsler triple -/

/-- `x` lies in the downset of `root` when a membership chain runs from `x` up to `root`. -/
inductive InDownset {α : Type} (edge : α → α → Prop) : α → α → Prop where
  | refl (a : α) : InDownset edge a a
  | step {child parent root : α} : edge parent child → InDownset edge parent root →
      InDownset edge child root

theorem finEdge_n0_n1 : finEdge Fin3.n0 Fin3.n1 := trivial
theorem finEdge_n1_n0 : finEdge Fin3.n1 Fin3.n0 := trivial
theorem finEdge_n1_n2 : finEdge Fin3.n1 Fin3.n2 := trivial
theorem finEdge_n2_n0 : finEdge Fin3.n2 Fin3.n0 := trivial
theorem finEdge_n2_n1 : finEdge Fin3.n2 Fin3.n1 := trivial

theorem fin_inDownset (x root : Fin3) : InDownset finEdge x root :=
  match x, root with
  | .n0, .n0 => InDownset.refl Fin3.n0
  | .n0, .n1 =>
      InDownset.step (child := Fin3.n0) (parent := Fin3.n1) (root := Fin3.n1)
        finEdge_n1_n0 (InDownset.refl Fin3.n1)
  | .n0, .n2 =>
      InDownset.step (child := Fin3.n0) (parent := Fin3.n2) (root := Fin3.n2)
        finEdge_n2_n0 (InDownset.refl Fin3.n2)
  | .n1, .n0 =>
      InDownset.step (child := Fin3.n1) (parent := Fin3.n0) (root := Fin3.n0)
        finEdge_n0_n1 (InDownset.refl Fin3.n0)
  | .n1, .n1 => InDownset.refl Fin3.n1
  | .n1, .n2 =>
      InDownset.step (child := Fin3.n1) (parent := Fin3.n2) (root := Fin3.n2)
        finEdge_n2_n1 (InDownset.refl Fin3.n2)
  | .n2, .n0 =>
      InDownset.step (child := Fin3.n2) (parent := Fin3.n1) (root := Fin3.n0) finEdge_n1_n2
        (InDownset.step (child := Fin3.n1) (parent := Fin3.n0) (root := Fin3.n0)
          finEdge_n0_n1 (InDownset.refl Fin3.n0))
  | .n2, .n1 =>
      InDownset.step (child := Fin3.n2) (parent := Fin3.n1) (root := Fin3.n1)
        finEdge_n1_n2 (InDownset.refl Fin3.n1)
  | .n2, .n2 => InDownset.refl Fin3.n2

theorem fin_unique_child_n0 : ∃! b, finEdge .n0 b :=
  ⟨.n1, trivial, fun b hb => by
    cases b with
    | n0 => exact hb.elim
    | n1 => rfl
    | n2 => exact hb.elim⟩

theorem fin_not_unique_child_n1 : ¬ ∃! b, finEdge .n1 b := by
  intro ⟨b, _, only⟩
  have h0 : .n0 = b := only .n0 trivial
  have h2 : .n2 = b := only .n2 trivial
  cases h0.trans h2.symm

theorem fin_not_unique_child_n2 : ¬ ∃! b, finEdge .n2 b := by
  intro ⟨b, _, only⟩
  have h0 : .n0 = b := only .n0 trivial
  have h1 : .n1 = b := only .n1 trivial
  cases h0.trans h1.symm

/-- A bijection of carriers preserving the child relation and the distinguished node. -/
structure PointedIso {α β : Type} (edge : α → α → Prop) (edge' : β → β → Prop)
    (a : α) (b : β) where
  equiv : α ≃ β
  point : equiv a = b
  preserve : ∀ x y, edge x y ↔ edge' (equiv x) (equiv y)

theorem not_finsler_iso_n1_n2 : ¬ Nonempty (PointedIso finEdge finEdge Fin3.n1 Fin3.n2) := by
  intro ⟨e⟩
  have unique0 : ∃! b, finEdge (e.equiv .n0) b := by
    obtain ⟨b, hb, only⟩ := fin_unique_child_n0
    refine ⟨e.equiv b, (e.preserve .n0 b).mp hb, ?_⟩
    intro c hc
    have : e.equiv.symm c = b := only _ ((e.preserve .n0 (e.equiv.symm c)).mpr
      (by rw [e.equiv.apply_symm_apply]; exact hc))
    have := congrArg e.equiv this
    rw [e.equiv.apply_symm_apply] at this
    exact this
  have en0 : e.equiv .n0 = .n0 := by
    cases h : e.equiv .n0 with
    | n0 => rfl
    | n1 => exact (fin_not_unique_child_n1 (h ▸ unique0)).elim
    | n2 => exact (fin_not_unique_child_n2 (h ▸ unique0)).elim
  have en2 : e.equiv .n2 = .n1 := by
    cases h : e.equiv .n2 with
    | n0 =>
      have : e.equiv .n2 = e.equiv .n0 := h.trans en0.symm
      cases e.equiv.injective this
    | n1 => rfl
    | n2 =>
      have : e.equiv .n2 = e.equiv .n1 := h.trans e.point.symm
      cases e.equiv.injective this
  have moved : finEdge (e.equiv .n0) (e.equiv .n1) := (e.preserve .n0 .n1).mp trivial
  rw [en0, e.point] at moved
  exact moved.elim

/-! ## Bisimulations -/

theorem scott_total_bisim : IsBisimulation scottEdge scottEdge (fun _ _ => True) := by
  intro a b _
  constructor
  · intro a' ha
    cases a with
    | s0 =>
      cases a' with
      | s0 =>
        cases b with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s0, trivial, trivial⟩
      | s1 => exact ha.elim
    | s1 =>
      cases a' with
      | s0 =>
        cases b with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s0, trivial, trivial⟩
      | s1 =>
        cases b with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s1, trivial, trivial⟩
  · intro b' hb
    cases b with
    | s0 =>
      cases b' with
      | s0 =>
        cases a with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s0, trivial, trivial⟩
      | s1 => exact hb.elim
    | s1 =>
      cases b' with
      | s0 =>
        cases a with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s0, trivial, trivial⟩
      | s1 =>
        cases a with
        | s0 => exact ⟨.s0, trivial, trivial⟩
        | s1 => exact ⟨.s1, trivial, trivial⟩

theorem scott_s0_bisim_s1 : Bisimilar scottEdge scottEdge .s0 .s1 :=
  scott_total_bisim.bisimilar trivial

theorem cycle_total_bisim : IsBisimulation cycleEdge cycleEdge (fun _ _ => True) := by
  intro a b _
  constructor
  · intro a' ha
    cases a with
    | l =>
      cases a' with
      | l => exact ha.elim
      | r =>
        cases b with
        | l => exact ⟨.r, trivial, trivial⟩
        | r => exact ⟨.l, trivial, trivial⟩
    | r =>
      cases a' with
      | l =>
        cases b with
        | l => exact ⟨.r, trivial, trivial⟩
        | r => exact ⟨.l, trivial, trivial⟩
      | r => exact ha.elim
  · intro b' hb
    cases b with
    | l =>
      cases b' with
      | l => exact hb.elim
      | r =>
        cases a with
        | l => exact ⟨.r, trivial, trivial⟩
        | r => exact ⟨.l, trivial, trivial⟩
    | r =>
      cases b' with
      | l =>
        cases a with
        | l => exact ⟨.r, trivial, trivial⟩
        | r => exact ⟨.l, trivial, trivial⟩
      | r => exact hb.elim

theorem cycle_l_bisim_r : Bisimilar cycleEdge cycleEdge .l .r :=
  cycle_total_bisim.bisimilar trivial

def finRelate : Fin3 → Fin3 → Prop
  | .n0, .n0 => True
  | .n1, .n1 => True
  | .n2, .n2 => True
  | .n1, .n2 => True
  | .n2, .n1 => True
  | _, _ => False

private theorem finRelate_symm {a b : Fin3} (h : finRelate a b) : finRelate b a := by
  cases a <;> cases b <;> exact h

private theorem fin_forth (a b a' : Fin3) (hab : finRelate a b) (ha : finEdge a a') :
    ∃ b', finEdge b b' ∧ finRelate a' b' := by
  cases a with
  | n0 =>
    cases b with
    | n0 =>
      cases a' with
      | n0 => exact ha.elim
      | n1 => exact ⟨.n1, trivial, trivial⟩
      | n2 => exact ha.elim
    | n1 => exact hab.elim
    | n2 => exact hab.elim
  | n1 =>
    cases b with
    | n0 => exact hab.elim
    | n1 =>
      cases a' with
      | n0 => exact ⟨.n0, trivial, trivial⟩
      | n1 => exact ha.elim
      | n2 => exact ⟨.n2, trivial, trivial⟩
    | n2 =>
      cases a' with
      | n0 => exact ⟨.n0, trivial, trivial⟩
      | n1 => exact ha.elim
      | n2 => exact ⟨.n1, trivial, trivial⟩
  | n2 =>
    cases b with
    | n0 => exact hab.elim
    | n1 =>
      cases a' with
      | n0 => exact ⟨.n0, trivial, trivial⟩
      | n1 => exact ⟨.n2, trivial, trivial⟩
      | n2 => exact ha.elim
    | n2 =>
      cases a' with
      | n0 => exact ⟨.n0, trivial, trivial⟩
      | n1 => exact ⟨.n1, trivial, trivial⟩
      | n2 => exact ha.elim

private theorem fin_back (a b b' : Fin3) (hab : finRelate a b) (hb : finEdge b b') :
    ∃ a', finEdge a a' ∧ finRelate a' b' := by
  obtain ⟨a', ha, hrel⟩ := fin_forth b a b' (finRelate_symm hab) hb
  exact ⟨a', ha, finRelate_symm hrel⟩

theorem fin_bisim : IsBisimulation finEdge finEdge finRelate :=
  fun a b hab => ⟨fun a' ha => fin_forth a b a' hab ha, fun b' hb => fin_back a b b' hab hb⟩

theorem fin_n1_bisim_n2 : Bisimilar finEdge finEdge .n1 .n2 :=
  fin_bisim.bisimilar trivial

theorem nest_point_not_bisim_blank : ¬ Bisimilar nestEdge nestEdge Nest.point Nest.blank :=
  not_bisimilar_of_child (a := Nest.point) (a' := Nest.blank) (b := Nest.blank) trivial
    fun b' hb => by cases b' <;> exact hb.elim

/-- The two cycle nodes, with the child relation, are isomorphic pointed graphs. -/
def cycleSwap : PointedIso cycleEdge cycleEdge .l .r where
  equiv := {
    toFun := fun
      | .l => .r
      | .r => .l
    invFun := fun
      | .l => .r
      | .r => .l
    left_inv := fun
      | .l => rfl
      | .r => rfl
    right_inv := fun
      | .l => rfl
      | .r => rfl
  }
  point := rfl
  preserve := by
    intro a b
    cases a <;> cases b
    · constructor
      · intro h; exact h.elim
      · intro h; exact h.elim
    · constructor
      · intro _; exact trivial
      · intro _; exact trivial
    · constructor
      · intro _; exact trivial
      · intro _; exact trivial
    · constructor
      · intro h; exact h.elim
      · intro h; exact h.elim

theorem cycle_not_same_children :
    ¬ (∀ c, cycleEdge .l c ↔ cycleEdge .r c) := by
  intro h
  exact (h .r).mp trivial |>.elim

theorem fin_total_bisim : IsBisimulation finEdge finEdge (fun _ _ => True) := by
  intro a b _
  constructor
  · intro _ _
    cases b with
    | n0 => exact ⟨.n1, trivial, trivial⟩
    | n1 => exact ⟨.n0, trivial, trivial⟩
    | n2 => exact ⟨.n0, trivial, trivial⟩
  · intro _ _
    cases a with
    | n0 => exact ⟨.n1, trivial, trivial⟩
    | n1 => exact ⟨.n0, trivial, trivial⟩
    | n2 => exact ⟨.n0, trivial, trivial⟩

theorem loop_has_child (a : Loop) : ∃ b, loopEdge a b :=
  ⟨.node, trivial⟩

theorem cycle_has_child (a : Cycle) : ∃ b, cycleEdge a b := by
  cases a with
  | l => exact ⟨.r, trivial⟩
  | r => exact ⟨.l, trivial⟩

theorem scott_has_child (a : Scott) : ∃ b, scottEdge a b := by
  cases a with
  | s0 => exact ⟨.s0, trivial⟩
  | s1 => exact ⟨.s0, trivial⟩

theorem fin_has_child (a : Fin3) : ∃ b, finEdge a b := by
  cases a with
  | n0 => exact ⟨.n1, trivial⟩
  | n1 => exact ⟨.n0, trivial⟩
  | n2 => exact ⟨.n0, trivial⟩

end Mettapedia.SetTheory.AntiFoundation
