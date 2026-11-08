import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Causal cells: the dependent confusion-free race identity

A **cell system** has events, each in one cell, with real weights, and at every configuration (a
finite set of fired events) a finite set of enabled cells (`CellSystem`). The **candidates** at a
configuration are the events of its enabled cells, and the **race total** is the sum of their
weights (`total_eq_sum_candidates`). The jump chain fires a candidate with its weight over the race
total (`pathProb`). A cell is a choice point (a race over its events); a cell enabled by several
earlier events is a join.

## Histories and their linearizations

A **history** is a finite set `X` of events. A **linearization** of `X` from a configuration `x` is
a run of the jump chain from `x`, firing at each move a candidate not yet fired, that ends at `X`
(`IsLin`). The linearizations form a finite set (`lins`, `mem_lins`).

## The race identity

`History X` asks four things of `X`:
* **conflict freedom**: no two events of `X` share a cell;
* **maximality**: nothing is enabled at `X`;
* **persistence**: along `X`, a cell enabled at a configuration stays enabled when an event of
  another cell fires;
* **positivity**: the cells enabled along `X` have positive totals.

**Move to front** (`History.reach_insert`): if `X` is reachable from `x`, it is reachable from `x`
with any candidate of `X` fired first. The enabled cells along `X` are in bijection with the
candidates of `X` there (`History.exists_of_enabled`, `History.total_eq`): every enabled cell
fires in `X`, exactly once.

**The identity** (`History.race_identity`): summed over the linearizations of a reachable history,
the jump-chain likelihood is the product, over the events of the history, of each event's weight
over its cell's total. Normalization inside cells is exact on histories whenever every enabled
cell persists until it fires, cells enabled by joins included. The independent case is R103's
`CausalHistories.sum_shuffles` (`CausalCellsShuffles`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalCells

universe u v

/-- **A cell system**: events in cells, with weights, and the cells enabled at each
configuration. -/
structure CellSystem (E : Type u) (C : Type v) where
  /-- The cell of an event. -/
  cell : E → C
  /-- The events of a cell: the candidates of its race. -/
  members : C → Finset E
  cell_of_mem : ∀ {e : E} {c : C}, e ∈ members c → cell e = c
  /-- The weight (rate) of an event. -/
  weight : E → ℝ
  /-- The cells enabled at a configuration. -/
  enabled : Finset E → Finset C

namespace CellSystem

variable {E : Type u} {C : Type v} [DecidableEq E] (K : CellSystem E C)

/-- The total weight of a cell. -/
def cellTotal (c : C) : ℝ := ∑ e ∈ K.members c, K.weight e

/-- The candidates at a configuration: the events of its enabled cells. -/
def candidates (x : Finset E) : Finset E := (K.enabled x).biUnion K.members

/-- **The race total** at a configuration: the sum of its enabled cells' totals. -/
def total (x : Finset E) : ℝ := ∑ c ∈ K.enabled x, K.cellTotal c

/-- **The jump-chain likelihood of a word** from a configuration: each move's weight over the race
total of the configuration it leaves. -/
def pathProb : Finset E → List E → ℝ
  | _, [] => 1
  | x, e :: l => K.weight e / K.total x * pathProb (insert e x) l

theorem mem_candidates {x : Finset E} {e : E} :
    e ∈ K.candidates x ↔ K.cell e ∈ K.enabled x ∧ e ∈ K.members (K.cell e) := by
  unfold candidates
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨c, hc, he⟩
    obtain rfl := K.cell_of_mem he
    exact ⟨hc, he⟩
  · rintro ⟨hc, he⟩
    exact ⟨_, hc, he⟩

/-- **The race total is the sum of the candidates' weights**: cells are disjoint. -/
theorem total_eq_sum_candidates (x : Finset E) :
    K.total x = ∑ e ∈ K.candidates x, K.weight e := by
  have disjoint : ((K.enabled x : Set C)).PairwiseDisjoint K.members := by
    intro c _ c' _ different
    show Disjoint (K.members c) (K.members c')
    rw [Finset.disjoint_left]
    intro e inC inC'
    exact different ((K.cell_of_mem inC).symm.trans (K.cell_of_mem inC'))
  unfold total candidates cellTotal
  rw [Finset.sum_biUnion disjoint]

/-! ## Linearizations -/

/-- **A linearization of the history `X` from `x`**: a run of the jump chain that fires, at each
move, a candidate not yet fired, and ends at `X`. -/
inductive IsLin (X : Finset E) : Finset E → List E → Prop
  | nil : IsLin X X []
  | cons {x : Finset E} {e : E} {l : List E} :
      e ∈ K.candidates x → e ∉ x → IsLin X (insert e x) l → IsLin X x (e :: l)

/-- `X` is reachable from `x`: it has a linearization from `x`. -/
def Reach (X x : Finset E) : Prop := ∃ l, K.IsLin X x l

variable {K}

theorem IsLin.subset {X x : Finset E} {l : List E} (lin : K.IsLin X x l) : x ⊆ X := by
  induction lin with
  | nil => exact Finset.Subset.refl _
  | cons _ _ _ ih => exact (Finset.subset_insert _ _).trans ih

theorem IsLin.mem {X x : Finset E} {e : E} {l : List E} (lin : K.IsLin X x (e :: l)) : e ∈ X := by
  cases lin with
  | cons _ _ rest => exact rest.subset (Finset.mem_insert_self _ _)

variable (K)

/-- The candidates of `X` at `x` that `X` has not fired yet. -/
def onHistory (X x : Finset E) : Finset E := (X \ x).filter (· ∈ K.candidates x)

/-- The linearizations of `X` from `x` within `n` moves. -/
def linsN (X : Finset E) : ℕ → Finset E → Finset (List E)
  | 0, x => if x = X then {[]} else ∅
  | n + 1, x => (K.onHistory X x).biUnion fun e => (linsN X n (insert e x)).image (List.cons e)

/-- **The linearizations of `X` from `x`**, as a finite set. -/
def lins (X x : Finset E) : Finset (List E) := K.linsN X (X \ x).card x

/-- The product, over the events of `X` not in `x`, of each event's weight over its cell's
total. -/
def cellProduct (X x : Finset E) : ℝ := ∏ e ∈ X \ x, K.weight e / K.cellTotal (K.cell e)

theorem card_sdiff_insert {X x : Finset E} {e : E} (member : e ∈ X \ x) :
    (X \ insert e x).card = (X \ x).card - 1 := by
  rw [Finset.sdiff_insert, Finset.card_erase_of_mem member]

theorem mem_linsN (X : Finset E) :
    ∀ (n : ℕ) (x : Finset E), (X \ x).card = n → ∀ l, l ∈ K.linsN X n x ↔ K.IsLin X x l
  | 0, x, card, l => by
      simp only [linsN]
      constructor
      · intro member
        split_ifs at member with same
        · rw [Finset.mem_singleton] at member
          subst member
          subst same
          exact IsLin.nil
        · simp at member
      · intro lin
        cases lin with
        | nil => simp
        | cons _ fresh rest =>
            exfalso
            have inside := Finset.mem_sdiff.mpr ⟨rest.subset (Finset.mem_insert_self _ _), fresh⟩
            rw [Finset.card_eq_zero] at card
            rw [card] at inside
            simp at inside
  | n + 1, x, card, l => by
      simp only [linsN, Finset.mem_biUnion, Finset.mem_image]
      constructor
      · rintro ⟨e, he, l', hl', rfl⟩
        have he' := Finset.mem_filter.mp he
        have card' : (X \ insert e x).card = n := by
          rw [card_sdiff_insert he'.1, card]
          rfl
        exact IsLin.cons he'.2 (Finset.mem_sdiff.mp he'.1).2
          ((mem_linsN X n _ card' l').mp hl')
      · intro lin
        cases lin with
        | nil => simp at card
        | @cons _ e l' cand fresh rest =>
            have inX : e ∈ X := rest.subset (Finset.mem_insert_self _ _)
            have he : e ∈ K.onHistory X x :=
              Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨inX, fresh⟩, cand⟩
            have card' : (X \ insert e x).card = n := by
              rw [card_sdiff_insert (Finset.mem_sdiff.mpr ⟨inX, fresh⟩), card]
              rfl
            exact ⟨e, he, l', (mem_linsN X n _ card' l').mpr rest, rfl⟩

/-- **The linearizations are exactly the runs of the jump chain from `x` that end at `X`.** -/
theorem mem_lins (X x : Finset E) (l : List E) : l ∈ K.lins X x ↔ K.IsLin X x l :=
  K.mem_linsN X _ x rfl l

/-- The first-move decomposition of the sum over linearizations. -/
theorem sum_linsN_succ (X : Finset E) (n : ℕ) (x : Finset E) :
    ∑ l ∈ K.linsN X (n + 1) x, K.pathProb x l =
      ∑ e ∈ K.onHistory X x,
        K.weight e / K.total x * ∑ l ∈ K.linsN X n (insert e x), K.pathProb (insert e x) l := by
  simp only [linsN]
  have disjoint : ((K.onHistory X x : Set E)).PairwiseDisjoint
      fun e => (K.linsN X n (insert e x)).image (List.cons e) := by
    intro e _ e' _ different
    show Disjoint ((K.linsN X n (insert e x)).image (List.cons e))
      ((K.linsN X n (insert e' x)).image (List.cons e'))
    rw [Finset.disjoint_left]
    intro l inE inE'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp inE
    obtain ⟨_, _, same⟩ := Finset.mem_image.mp inE'
    exact different (List.cons.inj same).1.symm
  rw [Finset.sum_biUnion disjoint]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_image (fun _ _ _ _ same => List.cons_injective same), Finset.mul_sum]
  rfl

/-- At `X` itself the only linearization is the empty one. -/
theorem lins_self (X : Finset E) : K.lins X X = {[]} := by
  ext l
  rw [mem_lins, Finset.mem_singleton]
  constructor
  · intro lin
    cases lin with
    | nil => rfl
    | cons _ fresh rest => exact absurd (rest.subset (Finset.mem_insert_self _ _)) fresh
  · rintro rfl
    exact IsLin.nil

/-- **Linearizations split by their first move**, away from `X`. -/
theorem lins_eq_biUnion {X x : Finset E} (away : x ≠ X) :
    K.lins X x =
      (K.onHistory X x).biUnion fun e => (K.lins X (insert e x)).image (List.cons e) := by
  ext l
  simp only [Finset.mem_biUnion, Finset.mem_image, mem_lins]
  constructor
  · intro lin
    cases lin with
    | nil => exact absurd rfl away
    | @cons _ e l' cand fresh rest =>
        exact ⟨e, Finset.mem_filter.mpr
          ⟨Finset.mem_sdiff.mpr ⟨rest.subset (Finset.mem_insert_self _ _), fresh⟩, cand⟩,
          l', rest, rfl⟩
  · rintro ⟨e, he, l', lin, rfl⟩
    have he' := Finset.mem_filter.mp he
    exact IsLin.cons he'.2 (Finset.mem_sdiff.mp he'.1).2 lin

/-- The first-move decomposition of the sum over linearizations, away from `X`. -/
theorem sum_lins_of_ne {X x : Finset E} (away : x ≠ X) :
    ∑ l ∈ K.lins X x, K.pathProb x l =
      ∑ e ∈ K.onHistory X x,
        K.weight e / K.total x * ∑ l ∈ K.lins X (insert e x), K.pathProb (insert e x) l := by
  rw [K.lins_eq_biUnion away]
  have disjoint : ((K.onHistory X x : Set E)).PairwiseDisjoint
      fun e => (K.lins X (insert e x)).image (List.cons e) := by
    intro e _ e' _ different
    show Disjoint ((K.lins X (insert e x)).image (List.cons e))
      ((K.lins X (insert e' x)).image (List.cons e'))
    rw [Finset.disjoint_left]
    intro l inE inE'
    obtain ⟨_, _, rfl⟩ := Finset.mem_image.mp inE
    obtain ⟨_, _, same⟩ := Finset.mem_image.mp inE'
    exact different (List.cons.inj same).1.symm
  rw [Finset.sum_biUnion disjoint]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.sum_image (fun _ _ _ _ same => List.cons_injective same), Finset.mul_sum]
  rfl

/-- One event of `X \ x` splits off the cell product. -/
theorem cellProduct_insert {X x : Finset E} {e : E} (member : e ∈ X \ x) :
    K.cellProduct X x = K.weight e / K.cellTotal (K.cell e) * K.cellProduct X (insert e x) := by
  unfold cellProduct
  rw [Finset.sdiff_insert]
  exact (Finset.mul_prod_erase (X \ x) (fun e => K.weight e / K.cellTotal (K.cell e)) member).symm

/-! ## Histories -/

/-- **A history on which normalization inside cells is exact**: conflict-free, maximal,
persistent and positive along itself. -/
structure History (X : Finset E) : Prop where
  conflictFree : ∀ ⦃e : E⦄, e ∈ X → ∀ ⦃e' : E⦄, e' ∈ X → K.cell e = K.cell e' → e = e'
  maximal : K.enabled X = ∅
  persistent : ∀ ⦃x : Finset E⦄, x ⊆ X → ∀ ⦃c : C⦄ ⦃e : E⦄, c ∈ K.enabled x →
    e ∈ K.candidates x → e ∈ X → e ∉ x → K.cell e ≠ c → c ∈ K.enabled (insert e x)
  positive : ∀ ⦃x : Finset E⦄, x ⊆ X → ∀ ⦃c : C⦄, c ∈ K.enabled x → 0 < K.cellTotal c

variable {K} {X : Finset E}

/-- **Move to front**: if `X` is reachable from `x`, then it is reachable after any candidate of
`X` not yet fired. -/
theorem History.reach_insert (H : K.History X) {x : Finset E} {l : List E}
    (lin : K.IsLin X x l) : ∀ {e : E}, e ∈ K.candidates x → e ∈ X → e ∉ x →
      K.Reach X (insert e x) := by
  induction lin with
  | nil =>
      intro e _ inX fresh
      exact absurd inX fresh
  | @cons x e' l cand' fresh' rest ih =>
      intro e cand inX fresh
      by_cases same : e = e'
      · subst same
        exact ⟨l, rest⟩
      · have sub : x ⊆ X := (Finset.subset_insert _ _).trans rest.subset
        have inX' : e' ∈ X := rest.subset (Finset.mem_insert_self _ _)
        have cells : K.cell e ≠ K.cell e' := fun h => same (H.conflictFree inX inX' h)
        have candE : e ∈ K.candidates (insert e' x) := by
          have parts := K.mem_candidates.mp cand
          exact K.mem_candidates.mpr
            ⟨H.persistent sub parts.1 cand' inX' fresh' (Ne.symm cells), parts.2⟩
        have freshE : e ∉ insert e' x := by
          rw [Finset.mem_insert, not_or]
          exact ⟨same, fresh⟩
        obtain ⟨l', lin'⟩ := ih candE inX freshE
        have candE' : e' ∈ K.candidates (insert e x) := by
          have parts := K.mem_candidates.mp cand'
          exact K.mem_candidates.mpr ⟨H.persistent sub parts.1 cand inX fresh cells, parts.2⟩
        have freshE' : e' ∉ insert e x := by
          rw [Finset.mem_insert, not_or]
          exact ⟨Ne.symm same, fresh'⟩
        refine ⟨e' :: l', IsLin.cons candE' freshE' ?_⟩
        rw [Finset.insert_comm]
        exact lin'

/-- **Every cell enabled along `X` fires in `X`**, with a candidate not yet fired. -/
theorem History.exists_of_enabled (H : K.History X) {x : Finset E} {l : List E}
    (lin : K.IsLin X x l) : ∀ {c : C}, c ∈ K.enabled x →
      ∃ e ∈ X, e ∉ x ∧ e ∈ K.candidates x ∧ K.cell e = c := by
  induction lin with
  | nil =>
      intro c enabled
      rw [H.maximal] at enabled
      simp at enabled
  | @cons x e' l cand' fresh' rest ih =>
      intro c enabled
      have inX' : e' ∈ X := rest.subset (Finset.mem_insert_self _ _)
      by_cases same : K.cell e' = c
      · exact ⟨e', inX', fresh', cand', same⟩
      · have sub : x ⊆ X := (Finset.subset_insert _ _).trans rest.subset
        obtain ⟨e, inX, notIn, candE, cellE⟩ := ih (H.persistent sub enabled cand' inX' fresh' same)
        refine ⟨e, inX, fun h => notIn (Finset.mem_insert_of_mem h), ?_, cellE⟩
        rw [K.mem_candidates]
        exact ⟨cellE ▸ enabled, (K.mem_candidates.mp candE).2⟩

theorem History.total_pos (H : K.History X) {x : Finset E} {e : E} {l : List E}
    (lin : K.IsLin X x (e :: l)) : 0 < K.total x := by
  cases lin with
  | cons cand _ rest =>
      have sub : x ⊆ X := (Finset.subset_insert _ _).trans rest.subset
      unfold total
      exact Finset.sum_pos (fun c enabled => H.positive sub enabled)
        ⟨_, (K.mem_candidates.mp cand).1⟩

variable [DecidableEq C]

/-- **The race total along `X` is the sum of the cell totals of `X`'s candidates there.** -/
theorem History.total_eq (H : K.History X) {x : Finset E} {l : List E} (lin : K.IsLin X x l) :
    ∑ e ∈ K.onHistory X x, K.cellTotal (K.cell e) = K.total x := by
  have image : (K.onHistory X x).image K.cell = K.enabled x := by
    ext c
    simp only [Finset.mem_image, onHistory, Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨e, ⟨_, cand⟩, rfl⟩
      exact (K.mem_candidates.mp cand).1
    · intro enabled
      obtain ⟨e, inX, notIn, cand, rfl⟩ := H.exists_of_enabled lin enabled
      exact ⟨e, ⟨⟨inX, notIn⟩, cand⟩, rfl⟩
  unfold total
  conv_rhs => rw [← image]
  rw [Finset.sum_image]
  intro e he e' he' same
  exact H.conflictFree (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_coe.mp he)).1).1
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp (Finset.mem_coe.mp he')).1).1 same

theorem History.sum_linsN (H : K.History X) :
    ∀ (n : ℕ) (x : Finset E), (X \ x).card = n → K.Reach X x →
      ∑ l ∈ K.linsN X n x, K.pathProb x l = K.cellProduct X x
  | 0, x, card, ⟨_, lin⟩ => by
      have same : x = X := by
        apply Finset.Subset.antisymm lin.subset
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at card
        exact card
      subst same
      simp [linsN, cellProduct, pathProb]
  | n + 1, x, card, ⟨l, lin⟩ => by
      rw [K.sum_linsN_succ]
      have later : ∀ e ∈ K.onHistory X x,
          ∑ l ∈ K.linsN X n (insert e x), K.pathProb (insert e x) l =
            K.cellProduct X (insert e x) := by
        intro e he
        have he' := Finset.mem_filter.mp he
        apply H.sum_linsN n
        · rw [card_sdiff_insert he'.1, card]
          rfl
        · exact H.reach_insert lin he'.2 (Finset.mem_sdiff.mp he'.1).1
            (Finset.mem_sdiff.mp he'.1).2
      have totalPos : 0 < K.total x := by
        cases lin with
        | nil => simp at card
        | cons cand fresh rest => exact H.total_pos (IsLin.cons cand fresh rest)
      rw [Finset.sum_congr rfl fun e he => by rw [later e he]]
      calc ∑ e ∈ K.onHistory X x, K.weight e / K.total x * K.cellProduct X (insert e x)
          = ∑ e ∈ K.onHistory X x, K.cellTotal (K.cell e) / K.total x * K.cellProduct X x := by
            refine Finset.sum_congr rfl fun e he => ?_
            have he' := Finset.mem_filter.mp he
            have cellPos : 0 < K.cellTotal (K.cell e) :=
              H.positive lin.subset (K.mem_candidates.mp he'.2).1
            rw [K.cellProduct_insert he'.1, ← mul_assoc, div_mul_div_comm,
              mul_comm (K.cellTotal _) (K.weight e), mul_div_mul_right _ _ cellPos.ne']
        _ = (∑ e ∈ K.onHistory X x, K.cellTotal (K.cell e)) / K.total x * K.cellProduct X x := by
            rw [Finset.sum_div, Finset.sum_mul]
        _ = K.cellProduct X x := by
            rw [H.total_eq lin, div_self totalPos.ne', one_mul]

/-- The race identity from any configuration from which `X` is reachable. -/
theorem History.sum_lins (H : K.History X) {x : Finset E} (reach : K.Reach X x) :
    ∑ l ∈ K.lins X x, K.pathProb x l = K.cellProduct X x :=
  H.sum_linsN _ x rfl reach

/-- **The dependent confusion-free race identity.** Summed over its linearizations, the jump-chain
likelihood of a reachable history is the product of its events' weights over their cells'
totals. -/
theorem History.race_identity (H : K.History X) (reach : K.Reach X ∅) :
    ∑ l ∈ K.lins X ∅, K.pathProb ∅ l = ∏ e ∈ X, K.weight e / K.cellTotal (K.cell e) := by
  rw [H.sum_lins reach]
  simp [cellProduct]

end CellSystem

#print axioms CellSystem.total_eq_sum_candidates
#print axioms CellSystem.mem_lins
#print axioms CellSystem.sum_linsN_succ
#print axioms CellSystem.lins_self
#print axioms CellSystem.lins_eq_biUnion
#print axioms CellSystem.sum_lins_of_ne
#print axioms CellSystem.History.reach_insert
#print axioms CellSystem.History.exists_of_enabled
#print axioms CellSystem.History.total_eq
#print axioms CellSystem.History.sum_lins
#print axioms CellSystem.History.race_identity

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CausalCells

end
