import Mathlib

-- Linter configuration: silence warnings pending systematic cleanup
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open scoped BigOperators
open Classical

noncomputable section

namespace FourColor

/-- Scalar field `𝔽₂`. -/
abbrev F2 := ZMod 2

/-- The color group `G = F₂ × F₂` used to encode edge colors. -/
abbrev Color :=
  F2 × F2

/-
Auxiliary algebra for Lemma 4.5.

We gather the small “zero chain” facts, support lemmas, and finite-sum
rewrite rules in one place so the facial-basis proof can cite them without
repeating the underlying `simp` gymnastics.
-/
@[simp] lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  classical
  fin_cases x <;> decide

/-- In F₂×F₂, every color added to itself gives zero (self-inverse property). -/
@[simp] lemma color_add_self (c : Color) : c + c = (0,0) := by
  ext <;> simp [zmod2_add_self]

/-- The constant zero chain. -/
def zeroChain {E : Type*} [DecidableEq E] : E → Color := fun _ => (0,0)

@[simp] lemma zeroChain_eq_zero {E : Type*} [DecidableEq E] :
    zeroChain = (0 : E → Color) := rfl

/-- Support of a chain: the set of edges where the colour is non-zero. -/
def support {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  (Finset.univ.filter fun e => x e ≠ (0,0))

lemma mem_support_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} :
    e ∈ support x ↔ x e ≠ (0,0) := by
  classical
  unfold support
  simp

lemma support_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support (zeroChain (E := E)) = ∅ := by
  classical
  ext e; simp [support, zeroChain]

lemma support_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support x = ∅ ↔ ∀ e, x e = (0,0) := by
  classical
  constructor
  · intro h e
    have : e ∉ support x := by simpa [h]
    simpa [support] using this
  · intro h
    ext e; simp [support, h e]

lemma eq_zero_of_support_eq_empty {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} (h : support x = ∅) :
    x = zeroChain (E := E) := by
  classical
  funext e
  simpa [zeroChain] using (support_eq_empty_iff.mp h e)

/-- γ-coordinate support: edges where the first coordinate (γ = (1,0) projection) is nonzero.
This is used in the leaf-peel induction to avoid circular dependencies. -/
def support₁ {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  (Finset.univ.filter fun e => (x e).fst ≠ 0)

@[simp] lemma mem_support₁ {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} :
    e ∈ support₁ x ↔ (x e).fst ≠ 0 := by
  classical
  unfold support₁; simp

lemma support₁_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support₁ (zeroChain (E := E)) = ∅ := by
  classical
  ext e; simp [support₁, zeroChain]

lemma support₁_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support₁ x = ∅ ↔ ∀ e, (x e).fst = 0 := by
  classical
  constructor
  · intro h e
    have : e ∉ support₁ x := by simpa [h]
    simpa [support₁] using this
  · intro h
    ext e; simp [support₁, h e]

/-- γ₂-coordinate support: edges where the second coordinate (γ = (0,1) projection) is nonzero. -/
def support₂ {E : Type*} [Fintype E] [DecidableEq E] (x : E → Color) : Finset E :=
  (Finset.univ.filter fun e => (x e).snd ≠ 0)

@[simp] lemma mem_support₂ {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {e : E} :
    e ∈ support₂ x ↔ (x e).snd ≠ 0 := by
  classical
  unfold support₂; simp

lemma support₂_zeroChain {E : Type*} [Fintype E] [DecidableEq E] :
    support₂ (zeroChain (E := E)) = ∅ := by
  classical
  ext e; simp [support₂, zeroChain]

lemma support₂_eq_empty_iff {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} :
    support₂ x = ∅ ↔ ∀ e, (x e).snd = 0 := by
  classical
  constructor
  · intro h e
    have : e ∉ support₂ x := by simpa [h]
    simpa [support₂] using this
  · intro h
    ext e; simp [support₂, h e]

namespace Color

variable (u v : Color)

/-- Dot product on `G = F₂ × F₂`, taken coordinatewise and summed in `F₂`. -/
def dot (u v : Color) : ZMod 2 :=
  u.1 * v.1 + u.2 * v.2

instance instOfNatColorZero : OfNat Color 0 where
  ofNat := (0, 0)

lemma zero_eq_pair : (0 : Color) = (0, 0) := rfl

@[simp] lemma dot_mk (u₁ u₂ v₁ v₂ : ZMod 2) :
    dot (u := (u₁, u₂)) (v := (v₁, v₂)) = u₁ * v₁ + u₂ * v₂ :=
  rfl

@[simp] lemma dot_zero_right (u : Color) : dot u ((0, 0) : Color) = 0 := by
  rcases u with ⟨u₁, u₂⟩
  simp [dot]

@[simp] lemma dot_zero_right' (u : Color) : dot u (0 : Color) = 0 := by
  rcases u with ⟨u₁, u₂⟩
  simp [dot]

@[simp] lemma dot_zero_left (v : Color) : dot ((0, 0) : Color) v = 0 := by
  rcases v with ⟨v₁, v₂⟩
  simp [dot]

@[simp] lemma dot_comm (u v : Color) : dot u v = dot v u := by
  cases u with
  | mk u₁ u₂ =>
    cases v with
    | mk v₁ v₂ =>
      change u₁ * v₁ + u₂ * v₂ = v₁ * u₁ + v₂ * u₂
      simp [mul_comm]

@[simp] lemma dot_add_right (u v w : Color) : dot u (v + w) = dot u v + dot u w := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rcases w with ⟨w₁, w₂⟩
  simp [dot, mul_add, add_comm, add_left_comm, add_assoc]

@[simp] lemma dot_add_left (u v w : Color) : dot (u + v) w = dot u w + dot v w := by
  rcases u with ⟨u₁, u₂⟩
  rcases v with ⟨v₁, v₂⟩
  rcases w with ⟨w₁, w₂⟩
  simp [dot, add_mul, add_comm, add_left_comm, add_assoc]

variable {u}

/-- Lemma 4.1(a): for any non-zero color `u`, there exists `v` with `dot u v = 1`. -/
lemma exists_dot_one_of_ne_zero (u : Color) (h : u ≠ 0) :
    ∃ v : Color, dot u v = 1 := by
  classical
  rcases u with ⟨u₁, u₂⟩
  have hcoords : u₁ ≠ 0 ∨ u₂ ≠ 0 := by
    by_contra hnot
    push Not at hnot
    rcases hnot with ⟨h₁, h₂⟩
    have : (u₁, u₂) = ((0, 0) : Color) := by simpa [h₁, h₂]
    exact h this
  cases hcoords with
  | inl h₁ =>
      refine ⟨(u₁⁻¹, 0), ?_⟩
      have h₁' : u₁ ≠ 0 := h₁
      simp [dot, h₁']
  | inr h₂ =>
      refine ⟨(0, u₂⁻¹), ?_⟩
      have h₂' : u₂ ≠ 0 := h₂
      simp [dot, h₂']

/-- Chains are functions from edges to colors. -/
abbrev Chain (ι : Type*) := ι → Color

/-- Dot product aggregated over all edges (Definition 4.1). -/
def chainDot {ι : Type*} [Fintype ι] (y z : Chain ι) : F2 :=
  ∑ e : ι, dot (y e) (z e)

@[simp] lemma chainDot_zero_right {ι : Type*} [Fintype ι]
    (y : Chain ι) : chainDot y (fun _ => 0) = 0 := by
  classical
  unfold chainDot
  refine Finset.sum_eq_zero ?_
  intro e _
  simp [dot]

@[simp] lemma chainDot_add_right {ι : Type*} [Fintype ι]
    (y x z : Chain ι) : chainDot y (x + z) = chainDot y x + chainDot y z := by
  classical
  unfold chainDot
  simpa [dot_add_right, Finset.sum_add_distrib]

@[simp] lemma chainDot_add_left {ι : Type*} [Fintype ι]
    (y x z : Chain ι) : chainDot (y + x) z = chainDot y z + chainDot x z := by
  classical
  unfold chainDot
  simpa [dot_add_left, Finset.sum_add_distrib]

/-- Lemma 4.1(b): a non-zero chain admits a witness with dot `1`. -/
lemma exists_chain_dot_one {ι : Type*} [Fintype ι]
    {y : Chain ι} (hy : ∃ e, y e ≠ 0) :
    ∃ z : Chain ι, chainDot y z = 1 := by
  classical
  obtain ⟨e₀, he₀⟩ := hy
  obtain ⟨w, hw⟩ := exists_dot_one_of_ne_zero (u := y e₀) he₀
  let z : Chain ι := fun e => if e = e₀ then w else 0
  have hsum :
      chainDot y z = dot (y e₀) w := by
    classical
    unfold chainDot
    have hrewrite :
        ∑ e : ι, dot (y e) (z e) =
          ∑ e : ι, (if e = e₀ then dot (y e) w else 0) := by
      refine Finset.sum_congr rfl ?_
      intro e _
      by_cases h : e = e₀
      · subst h; simp [z]
      · simp [z, h, dot_zero_right']
    have hcalc :
        ∑ e : ι, (if e = e₀ then dot (y e) w else 0)
          = dot (y e₀) w := by
      classical
      simpa using
        Finset.sum_ite (s := (Finset.univ : Finset ι)) (p := fun e => e = e₀)
          (f := fun e => dot (y e) w) (g := fun _ => (0 : F2))
    exact (hrewrite.trans hcalc)
  refine ⟨z, ?_⟩
  simpa [hsum] using hw

/-- Swap two distinguished colors, leaving any other color unchanged. -/
def swap (α β x : Color) : Color :=
  if x = α then β else if x = β then α else x

@[simp] lemma swap_eq_left (α β : Color) : swap α β α = β := by
  simp [swap]

@[simp] lemma swap_eq_right (α β : Color) : swap α β β = α := by
  simp [swap]

@[simp] lemma swap_ne (α β x : Color) (hα : x ≠ α) (hβ : x ≠ β) :
    swap α β x = x := by
  simp [swap, hα, hβ]

/-- Helper: In ZMod 2, adding to itself gives zero. -/
lemma F2_add_self (a : F2) : a + a = 0 := by
  -- Use decidability of ZMod 2
  fin_cases a <;> decide

/-- Helper: In ZMod 2, doubling gives zero. -/
lemma F2_two_mul (a : F2) : 2 * a = 0 := by
  rw [two_mul]
  exact F2_add_self a

/-- Delta for swap: add α+β on {α,β}, else add 0. -/
def delta (α β x : Color) : Color :=
  if x = α ∨ x = β then α + β else (0, 0)

/-- Key algebraic identity: swap equals addition by delta.
    This is the foundation of the even-incidence swap principle. -/
lemma swap_eq_add_delta (α β x : Color) :
    swap α β x = x + delta α β x := by
  unfold swap delta
  by_cases hα : x = α
  · rw [if_pos hα, if_pos (Or.inl hα), hα]
    -- β = α + (α + β) in F₂²
    ext
    · show β.1 = α.1 + (α.1 + β.1)
      rw [← add_assoc, F2_add_self, zero_add]
    · show β.2 = α.2 + (α.2 + β.2)
      rw [← add_assoc, F2_add_self, zero_add]
  · by_cases hβ : x = β
    · rw [if_neg hα, if_pos hβ, if_pos (Or.inr hβ), hβ]
      -- α = β + (α + β) in F₂²
      ext
      · show α.1 = β.1 + (α.1 + β.1)
        rw [add_comm α.1, ← add_assoc, F2_add_self, zero_add]
      · show α.2 = β.2 + (α.2 + β.2)
        rw [add_comm α.2, ← add_assoc, F2_add_self, zero_add]
    · rw [if_neg hα, if_neg hβ, if_neg]
      simp
      intro h; cases h <;> contradiction

/-- In F₂², summing a value an even number of times gives zero. -/
lemma nsmul_even_eq_zero {c : Color} {n : ℕ} (h : Even n) :
    n • c = (0, 0) := by
  rcases h with ⟨k, rfl⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    show (k + 1 + (k + 1)) • c = (0, 0)
    -- Simplify: (k+1 + (k+1)) = (k+k) + 2
    have : k + 1 + (k + 1) = k + k + 2 := by omega
    rw [this, add_nsmul, ih]
    ext <;> simp [F2_two_mul]

/-- Sum of constant over a finset equals card • constant. -/
lemma sum_const {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset E) (c : Color) :
    ∑ _e ∈ S, c = S.card • c := by
  induction S using Finset.induction with
  | empty => simp
  | insert e S he ih =>
    rw [Finset.sum_insert he, ih, Finset.card_insert_of_notMem he]
    show c + S.card • c = (S.card + 1) • c
    rw [add_comm (c : Color), add_nsmul, one_nsmul, add_comm]

/-- Sum at a vertex is preserved if the swap set has even αβ-incidence.
    This is the key lemma for Kempe chain switches. -/
lemma swap_preserves_vertex_sum
    {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V]
    (incident : V → Finset E)
    (x : E → Color) (C : Finset E) (α β : Color)
    (even_at : ∀ v : V, Even ((C ∩ incident v).filter (fun e => x e = α ∨ x e = β)).card) :
  ∀ v, ∑ e ∈ incident v, x e
      = ∑ e ∈ incident v, (if e ∈ C then swap α β (x e) else x e) := by
  intro v
  let S := (C ∩ incident v).filter (fun e => x e = α ∨ x e = β)

  -- Each swapped term equals original + conditional delta
  have h_swap : ∀ e, (if e ∈ C then swap α β (x e) else x e)
                   = x e + (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0)) := by
    intro e
    by_cases he : e ∈ C
    · simp [he, swap_eq_add_delta, delta]
    · simp [he]

  calc
    ∑ e ∈ incident v, x e
      = (∑ e ∈ incident v, x e) + (0, 0) := by
          simp
    _ = (∑ e ∈ incident v, x e) + S.card • (α + β) := by
          rw [nsmul_even_eq_zero (even_at v)]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ S, (α + β)) := by
          rw [sum_const]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ incident v, (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          congr 1
          -- S = (C ∩ incident v).filter (fun e => x e = α ∨ x e = β)
          -- Need to show: ∑ e ∈ S, (α + β) = ∑ e ∈ incident v, if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else 0
          -- The key insight: the RHS sums only over elements where the condition holds,
          -- which is exactly the set S
          have h_eq : ∑ e ∈ incident v, (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))
                    = ∑ e ∈ S, (α + β) := by
            -- Rewrite if-then-else with explicit zero
            have : (fun e => if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))
                 = (fun e => if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else 0) := by
              funext e; split_ifs <;> rfl
            rw [this]
            -- Use Finset.sum_filter
            rw [← Finset.sum_filter]
            -- Now show the filtered set equals S
            congr 1
            -- filter (incident v) (fun e => e ∈ C ∧ (x e = α ∨ x e = β)) = S
            -- S = (C ∩ incident v).filter (fun e => x e = α ∨ x e = β)
            ext e
            simp only [Finset.mem_filter, Finset.mem_inter, S]
            tauto
          rw [h_eq]
    _ = ∑ e ∈ incident v, (x e + (if e ∈ C ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ e ∈ incident v, (if e ∈ C then swap α β (x e) else x e) := by
          congr 1; funext e; exact (h_swap e).symm

/-- Predicate version of swap_preserves_vertex_sum.

    Takes a predicate `p : E → Prop` instead of a Finset `C`. The proof structure
    is identical, but uses `p e` instead of `e ∈ C`.

    This eliminates the need to filter on non-decidable predicates!
-/
lemma swap_preserves_vertex_sum_pred
    {E V : Type*} [Fintype E] [DecidableEq E] [Fintype V]
    (incident : V → Finset E)
    (x : E → Color) (p : E → Prop) [DecidablePred p] (α β : Color)
    (even_at : ∀ v : V, Even ((incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))).card) :
  ∀ v, ∑ e ∈ incident v, x e
      = ∑ e ∈ incident v, (if p e then swap α β (x e) else x e) := by
  intro v
  let S := (incident v).filter (fun e => p e ∧ (x e = α ∨ x e = β))

  -- Each swapped term equals original + conditional delta
  have h_swap : ∀ e, (if p e then swap α β (x e) else x e)
                   = x e + (if p e ∧ (x e = α ∨ x e = β) then α + β else (0, 0)) := by
    intro e
    by_cases he : p e
    · simp [he, swap_eq_add_delta, delta]
    · simp [he]

  calc
    ∑ e ∈ incident v, x e
      = (∑ e ∈ incident v, x e) + (0, 0) := by simp
    _ = (∑ e ∈ incident v, x e) + S.card • (α + β) := by
          rw [nsmul_even_eq_zero (even_at v)]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ S, (α + β)) := by
          rw [sum_const]
    _ = (∑ e ∈ incident v, x e) + (∑ e ∈ incident v, (if p e ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          congr 1
          have h_eq : ∑ e ∈ incident v, (if p e ∧ (x e = α ∨ x e = β) then α + β else (0, 0))
                    = ∑ e ∈ S, (α + β) := by
            have : (fun e => if p e ∧ (x e = α ∨ x e = β) then α + β else (0, 0))
                 = (fun e => if p e ∧ (x e = α ∨ x e = β) then α + β else 0) := by
              funext e; split_ifs <;> rfl
            rw [this, ← Finset.sum_filter]
          rw [h_eq]
    _ = ∑ e ∈ incident v, (x e + (if p e ∧ (x e = α ∨ x e = β) then α + β else (0, 0))) := by
          rw [Finset.sum_add_distrib]
    _ = ∑ e ∈ incident v, (if p e then swap α β (x e) else x e) := by
          congr 1; funext e; exact (h_swap e).symm

end Color

/-- Convenient shorthand for the two-element set `{α, β}`. -/
def twoColor (α β : Color) : Set Color :=
  {c | c = α ∨ c = β}

namespace Color

@[simp] lemma swap_mem_twoColor_iff (α β x : Color) :
    swap α β x ∈ twoColor α β ↔ x ∈ twoColor α β := by
  classical
  unfold twoColor
  by_cases hα : x = α
  · subst hα
    simp [swap]
  · by_cases hβ : x = β
    · subst hβ
      simp [swap]
    · simp [swap, hα, hβ]

end Color

/-- Apply a Kempe switch that toggles colors `α` and `β` on the edge set `D`. -/
def switch {ι : Type*} (α β : Color) (D : Set ι) (C : ι → Color) :
    ι → Color :=
  fun e => if e ∈ D then Color.swap α β (C e) else C e

@[simp] lemma switch_of_not_mem {ι : Type*} (α β : Color) (D : Set ι)
    (C : ι → Color) {e : ι} (he : e ∉ D) :
    switch α β D C e = C e := by
  simpa [switch, he]

@[simp] lemma switch_of_mem {ι : Type*} (α β : Color) (D : Set ι)
    (C : ι → Color) {e : ι} (he : e ∈ D) :
    switch α β D C e = Color.swap α β (C e) := by
  simpa [switch, he]

lemma switch_mem_twoColor_iff {ι : Type*} (α β : Color) (D : Set ι)
    (C : ι → Color) (e : ι) :
    switch α β D C e ∈ twoColor α β ↔ C e ∈ twoColor α β := by
  classical
  by_cases he : e ∈ D
  · simp [switch_of_mem, he, Color.swap_mem_twoColor_iff]
  · simp [switch_of_not_mem, he]

def twoColorSupport {ι : Type*} (C : ι → Color) (α β : Color) : Set ι :=
  {e | C e ∈ twoColor α β}

/-- **Lemma 4.2 (Run invariance under cycle switches).**
Swapping colors `α` and `β` along a Kempe cycle leaves the `αβ` support
unchanged, and hence the maximal runs on any boundary are preserved. -/
lemma twoColorSupport_switch {ι : Type*} (α β : Color) (D : Set ι)
    (C : ι → Color) :
    twoColorSupport (switch α β D C) α β =
      twoColorSupport C α β := by
  classical
  ext e
  simpa [twoColorSupport] using
    (switch_mem_twoColor_iff (α := α) (β := β) (D := D) (C := C) e)

/-- Chain indicating membership in a finite set, coloured by `γ`. -/
def indicatorChain {ι : Type*} [DecidableEq ι] (γ : Color) (S : Finset ι) :
    ι → Color :=
  fun e => if e ∈ S then γ else 0

@[simp] lemma indicatorChain_of_mem {ι : Type*} [DecidableEq ι]
    (γ : Color) {S : Finset ι} {e : ι} (he : e ∈ S) :
    indicatorChain γ S e = γ := by
  classical
  simp [indicatorChain, he]

@[simp] lemma indicatorChain_of_not_mem {ι : Type*} [DecidableEq ι]
    (γ : Color) {S : Finset ι} {e : ι} (he : e ∉ S) :
    indicatorChain γ S e = 0 := by
  classical
  simp [indicatorChain, he]

/-- Pointwise “XOR” of two chains, implemented as subtraction. In characteristic two
this coincides with addition, but phrasing it as subtraction avoids any extra
algebraic prerequisites in the intermediate lemmas. -/
def chainXor {ι : Type*} (x y : ι → Color) : ι → Color :=
  fun e => x e + (-y e)

@[simp] lemma chainXor_apply {ι : Type*} (x y : ι → Color) (e : ι) :
    chainXor x y e = x e + (-y e) := rfl

lemma chainXor_add_right_cancel {ι : Type*} (x y z : ι → Color) :
    chainXor (x + z) (y + z) = chainXor x y := by
  funext e
  simp [chainXor, add_comm, add_assoc]

/-- **Lemma 4.3 (Per-run purification, pointwise form).** If two chains agree
off a distinguished run `R`, and differ by `γ` on `R`, then their `XOR`
restricts precisely to the indicator of `R`. This isolates the combinatorial
heart of the per-run argument; the geometric hypotheses will later supply the
pointwise equalities. -/
lemma perRunPurification_pointwise {ι : Type*} [DecidableEq ι]
    (γ : Color) (R : Finset ι) {X Y : ι → Color}
    (h_off : ∀ e, e ∉ R → X e = Y e)
    (h_on  : ∀ e ∈ R, chainXor X Y e = γ) :
    chainXor X Y = indicatorChain γ R := by
  classical
  refine funext ?_
  intro e
  by_cases he : e ∈ R
  ·
    have hind : indicatorChain γ R e = γ := by
      simp [indicatorChain, he]
    exact (h_on e he).trans hind.symm
  · have hXY : X e = Y e := h_off e he
    have hzero : chainXor X Y e = 0 := by
      simp [chainXor, hXY]
    have hind : indicatorChain γ R e = 0 := by
      simp [indicatorChain, he]
    exact hzero.trans hind.symm

/-- Aggregate face generator obtained by choosing, for every run, a completion set.
This models the quantity `X_f^{αβ}` from Goertzel's formulation. -/
def faceGenerator {ι : Type*} [DecidableEq ι]
    (γ : Color) (runs : Finset (Finset ι)) (assign : Finset ι → Finset ι) :
    ι → Color :=
  ∑ R ∈ runs, indicatorChain γ (assign R)

/-- **Lemma 4.3 (Per-run purification, aggregated form).** If two assignments agree
on every run except a distinguished `R`, and their associated chains differ there by
`γ · 1_R`, then the difference of the face generators is exactly `γ · 1_R`. -/
lemma perRunPurification_face {ι : Type*} [DecidableEq ι]
    (γ : Color) (runs : Finset (Finset ι))
    (R : Finset ι) (assign assign' : Finset ι → Finset ι)
    (hR : R ∈ runs)
    (h_off : ∀ S ∈ runs, S ≠ R → assign S = assign' S)
    (h_run :
      chainXor (indicatorChain γ (assign R)) (indicatorChain γ (assign' R))
        = indicatorChain γ R) :
    chainXor (faceGenerator γ runs assign)
      (faceGenerator γ runs assign') = indicatorChain γ R := by
  classical
  have hsum_assign :=
    Finset.add_sum_erase (s := runs)
      (f := fun S : Finset ι => indicatorChain γ (assign S)) hR
  have hsum_assign' :=
    Finset.add_sum_erase (s := runs)
      (f := fun S : Finset ι => indicatorChain γ (assign' S)) hR
  set rest :=
    ∑ S ∈ runs.erase R, indicatorChain γ (assign S) with hrest_def
  set rest' :=
    ∑ S ∈ runs.erase R, indicatorChain γ (assign' S) with hrest'_def
  have hrest_eq : rest = rest' := by
    have hsum :
        ∑ S ∈ runs.erase R, indicatorChain γ (assign S) =
          ∑ S ∈ runs.erase R, indicatorChain γ (assign' S) := by
      refine Finset.sum_congr rfl ?_
      intro S hS
      obtain ⟨hS_ne, hS_runs⟩ := Finset.mem_erase.mp hS
      have hassign := h_off S hS_runs hS_ne
      simpa [indicatorChain, hassign]
    simpa [rest, rest', hrest_def, hrest'_def] using hsum
  have hface_assign :
      indicatorChain γ (assign R) + rest =
        faceGenerator γ runs assign := by
    simpa [faceGenerator, rest, hrest_def] using hsum_assign
  have hface_assign' :
      indicatorChain γ (assign' R) + rest' =
        faceGenerator γ runs assign' := by
    simpa [faceGenerator, rest', hrest'_def] using hsum_assign'
  calc
    chainXor (faceGenerator γ runs assign) (faceGenerator γ runs assign')
        = chainXor (indicatorChain γ (assign R) + rest)
            (indicatorChain γ (assign' R) + rest') := by
              simp [hface_assign.symm, hface_assign'.symm]
    _ = chainXor (indicatorChain γ (assign R) + rest)
            (indicatorChain γ (assign' R) + rest) := by
              simpa [hrest_eq]
    _ = chainXor (indicatorChain γ (assign R))
            (indicatorChain γ (assign' R)) :=
              chainXor_add_right_cancel _ _ _
    _ = indicatorChain γ R := h_run

/-- Summing the `γ`-indicator chains over a partition of `boundary` recovers the
indicator of the whole boundary. This is the algebraic heart of Lemma 4.4. -/
lemma indicatorChain_of_partition {ι : Type*} [DecidableEq ι]
    (γ : Color) (runs : Finset (Finset ι)) (boundary : Finset ι)
    (h_subset : ∀ R ∈ runs, R ⊆ boundary)
    (h_cover : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R) :
    faceGenerator γ runs (fun R => R) = indicatorChain γ boundary := by
  classical
  refine funext ?_
  intro e
  by_cases he : e ∈ boundary
  · rcases h_cover e he with ⟨R₀, hR₀P, huniq⟩
    rcases hR₀P with ⟨hR₀_runs, heR₀⟩
    have hsum :=
      Finset.add_sum_erase (s := runs)
        (f := fun S : Finset ι => if e ∈ S then γ else 0) hR₀_runs
    have hrest_zero :
        ∑ S ∈ runs.erase R₀, (if e ∈ S then γ else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      obtain ⟨hSr, hS_runs⟩ := Finset.mem_erase.mp hS
      have : e ∉ S := by
        by_contra heS
        have hmatch : S = R₀ :=
          huniq S ⟨hS_runs, heS⟩
        exact hSr hmatch
      simp [this]
    have hsum_eval :
        ∑ S ∈ runs, (if e ∈ S then γ else 0) = γ := by
      have := hsum.symm
      -- `hsum` gives the equation `(if e ∈ R₀ then γ else 0) + rest = total`.
      -- After simplifying we deduce `∑ ... = γ`.
      simpa [heR₀, hrest_zero] using this
    simpa [faceGenerator, indicatorChain, he]
      using hsum_eval
  · have : ∀ R ∈ runs, e ∉ R := by
      intro R hR
      exact fun heR => he ((h_subset R hR) heR)
    have hsum_zero :
        ∑ S ∈ runs, (if e ∈ S then γ else 0) = 0 := by
      refine Finset.sum_eq_zero ?_
      intro S hS
      have : e ∉ S := this S hS
      simp [this]
    simpa [faceGenerator, indicatorChain, he] using hsum_zero

/-- **Lemma 4.4 (Face-level purification, algebraic form).** If the αβ-runs on a
face partition its boundary, then the XOR (i.e. sum) of their per-run
purification contributions equals the boundary indicator. -/
lemma faceLevelPurification {ι : Type*} [DecidableEq ι]
    (γ : Color) (runs : Finset (Finset ι)) (boundary : Finset ι)
    (X : ι → Color) (Y : Finset ι → ι → Color)
    (h_run : ∀ R ∈ runs, chainXor X (Y R) = indicatorChain γ R)
    (h_subset : ∀ R ∈ runs, R ⊆ boundary)
    (h_cover : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R) :
    ∑ R ∈ runs, chainXor X (Y R) = indicatorChain γ boundary := by
  classical
  have hrewrite :
      ∑ R ∈ runs, chainXor X (Y R)
        = ∑ R ∈ runs, indicatorChain γ R := by
    refine Finset.sum_congr rfl ?_
    intro R hR
    simpa using h_run R hR
  have hpartition :=
    indicatorChain_of_partition (γ := γ) (runs := runs) (boundary := boundary)
      h_subset h_cover
  calc
    ∑ R ∈ runs, chainXor X (Y R)
        = ∑ R ∈ runs, indicatorChain γ R := hrewrite
    _ = faceGenerator γ runs (fun R => R) := rfl
    _ = indicatorChain γ boundary := hpartition

/-- Data needed to instantiate Lemma 4.4 in the concrete geometric setting:
the runs give a partition of the boundary, each run has an associated Kempe
completion, and the per-run XOR reduces to the run indicator. -/
structure FaceRunPurificationData (ι : Type*) [DecidableEq ι] where
  γ : Color
  runs : Finset (Finset ι)
  boundary : Finset ι
  base : ι → Color
  switched : Finset ι → ι → Color
  run_chain : ∀ R ∈ runs, chainXor base (switched R) = indicatorChain γ R
  subset_boundary : ∀ R ∈ runs, R ⊆ boundary
  cover_boundary : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R

namespace FaceRunPurificationData

/-- The aggregated per-run purification equals the boundary indicator (Lemma 4.4). -/
lemma boundary_indicator {ι : Type*} [DecidableEq ι]
    (D : FaceRunPurificationData ι) :
    ∑ R ∈ D.runs, chainXor D.base (D.switched R)
        = indicatorChain D.γ D.boundary :=
  faceLevelPurification (γ := D.γ) (runs := D.runs)
    (boundary := D.boundary) (X := D.base) (Y := D.switched)
    D.run_chain D.subset_boundary D.cover_boundary

end FaceRunPurificationData

/-!
The following records package the combinatorial data that arise from
partitioning a face boundary into αβ-runs and providing a Kempe completion
for each such run.  They serve as the geometric bridge to the algebraic
lemma `FaceRunPurificationData.boundary_indicator`.
-/

/-- A combinatorial description of a face boundary decomposed into finite runs. -/
structure FaceRunPartition (ι : Type*) [DecidableEq ι] where
  runs : Finset (Finset ι)
  boundary : Finset ι
  subset_boundary : ∀ R ∈ runs, R ⊆ boundary
  cover_boundary : ∀ e ∈ boundary, ∃! R, R ∈ runs ∧ e ∈ R

namespace FaceRunPartition

variable {ι : Type*} [DecidableEq ι]

/-- Construct a `FaceRunPurificationData` once the base colouring and per-run
switched colourings are supplied for a face run partition. -/
structure SwitchData (P : FaceRunPartition ι) where
  γ : Color
  base : ι → Color
  switched : ∀ ⦃R⦄, R ∈ P.runs → (ι → Color)
  run_chain :
    ∀ {R} (hR : R ∈ P.runs),
      chainXor base (switched hR) = indicatorChain γ R

namespace SwitchData

variable {P : FaceRunPartition ι} (S : SwitchData P)

/-- Switched colouring that sends runs outside `P.runs` to the zero chain. -/
def switchedTotal : Finset ι → ι → Color :=
  fun R =>
    if hR : R ∈ P.runs then S.switched hR else fun _ => (0,0)

lemma switchedTotal_apply_of_mem {R : Finset ι} (hR : R ∈ P.runs) :
    S.switchedTotal R = S.switched hR := by
  funext e; unfold switchedTotal; simp [hR]

lemma switchedTotal_apply_of_not_mem {R : Finset ι} (hR : R ∉ P.runs) :
    S.switchedTotal R = fun _ => (0,0) := by
  funext e; unfold switchedTotal; simp [hR]

lemma run_chain_total {R : Finset ι} (hR : R ∈ P.runs) :
    chainXor S.base (S.switchedTotal R) = indicatorChain S.γ R := by
  classical
  simpa [switchedTotal_apply_of_mem (S := S) hR] using S.run_chain (P := P) hR

/-- Assemble a `FaceRunPurificationData` from partition data and per-run switches. -/
def toPurificationData : FaceRunPurificationData ι where
  γ := S.γ
  runs := P.runs
  boundary := P.boundary
  base := S.base
  switched := S.switchedTotal
  run_chain := by
    intro R hR
    exact S.run_chain_total (P := P) hR
  subset_boundary := P.subset_boundary
  cover_boundary := P.cover_boundary

end SwitchData

end FaceRunPartition

/-
## Facial basis scaffolding (towards Lemma 4.5)

We prepare lightweight containers for the zero-boundary condition and the
dual-forest hypotheses.  The actual inductive proof will be added in a later
pass once the geometric data is available.
-/

section FacialBasis

variable {V E : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

structure ZeroBoundaryData (V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  incident : V → Finset E
  boundaryEdges : Finset E

namespace ZeroBoundaryData

variable (D : ZeroBoundaryData V E)

def isZeroBoundary (x : E → Color) : Prop :=
  ∀ v : V, ∑ e ∈ D.incident v, x e = (0,0)

/-- Chains that vanish on every vertex and on the distinguished boundary. -/
def zeroBoundarySet : Set (E → Color) :=
  {x | D.isZeroBoundary x ∧ ∀ e ∈ D.boundaryEdges, x e = (0,0)}

lemma zeroChain_isZeroBoundary {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (D : ZeroBoundaryData V E) :
    D.isZeroBoundary (zeroChain (E := E)) := by
  intro v
  simp [ZeroBoundaryData.isZeroBoundary, zeroChain]

lemma zeroChain_mem_zeroBoundarySet {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (D : ZeroBoundaryData V E) :
    zeroChain (E := E) ∈ D.zeroBoundarySet := by
  refine ⟨zeroChain_isZeroBoundary (E := E) D, ?_⟩
  intro e he
  rfl

lemma isZeroBoundary_add (D : ZeroBoundaryData V E)
    {x y : E → Color}
    (hx : D.isZeroBoundary x) (hy : D.isZeroBoundary y) :
    D.isZeroBoundary (x + y) := by
  intro v
  -- ∑ (x + y) = ∑ x + ∑ y = 0
  simpa [Pi.add_apply, Finset.sum_add_distrib, hx v, hy v]

lemma mem_zero_add (D : ZeroBoundaryData V E)
    {x y : E → Color}
    (hx : x ∈ D.zeroBoundarySet) (hy : y ∈ D.zeroBoundarySet) :
    x + y ∈ D.zeroBoundarySet := by
  rcases hx with ⟨hxV, hxB⟩
  rcases hy with ⟨hyV, hyB⟩
  refine ⟨D.isZeroBoundary_add hxV hyV, ?_⟩
  intro e he
  -- boundary values: (x + y) e = 0 + 0
  simp [hxB e he, hyB e he]

lemma sum_mem_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ZeroBoundaryData V E)
    (S : Finset ι) (f : ι → E → Color)
    (h : ∀ i ∈ S, f i ∈ D.zeroBoundarySet) :
    (∑ i ∈ S, f i) ∈ D.zeroBoundarySet := by
  classical
  induction' S using Finset.induction with i S hi ih
  · simpa using D.zeroChain_mem_zeroBoundarySet
  · have hi' : f i ∈ D.zeroBoundarySet := h i (Finset.mem_insert_self _ _)
    have hS : ∀ j ∈ S, f j ∈ D.zeroBoundarySet :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    simpa [Finset.sum_insert hi] using
      D.mem_zero_add hi' (ih hS)

end ZeroBoundaryData


/-- Chain attached to the boundary of a face, coloured by `γ`. -/
def faceBoundaryChain (γ : Color) (f : Finset E) : E → Color :=
  indicatorChain γ f

/-- Toggling a face at γ=(1,0) flips exactly the first coordinate on edges of `f`. -/
lemma support₁_toggle_symmDiff {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) :
    support₁ (faceBoundaryChain (γ := (1,0)) f) = f := by
  classical
  ext e
  by_cases he : e ∈ f
  · simp [faceBoundaryChain, indicatorChain, he]
  · simp [faceBoundaryChain, indicatorChain, he]

/-- When adding a face boundary at γ=(1,0), the γ-support changes via symmetric difference. -/
lemma support₁_after_toggle {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {f : Finset E} :
    support₁ (x + faceBoundaryChain (γ := (1,0)) f)
      = (support₁ x \ f) ∪ (f \ support₁ x) := by
  classical
  ext e
  by_cases he : e ∈ f
  · -- first coordinate flips on f
    have hγ : (faceBoundaryChain (γ := (1,0)) f e).fst = 1 := by
      simp [faceBoundaryChain, indicatorChain, he]
    -- In F₂: 0+1=1≠0 and 1+1=0, so (x e).fst + 1 ≠ 0 ↔ (x e).fst = 0
    have : (x e).fst = 0 ∨ (x e).fst = 1 := by
      rcases (x e).fst with ⟨v, hv⟩
      interval_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases this with h0 | h1
    · simp [he, hγ, h0, Finset.mem_union, Finset.mem_sdiff]
    · simp [he, hγ, h1, Finset.mem_union, Finset.mem_sdiff]
  · -- off f, first coordinate unchanged
    have hγ : (faceBoundaryChain (γ := (1,0)) f e).fst = 0 := by
      simp [faceBoundaryChain, indicatorChain, he]
    simp [he, hγ, Finset.mem_union, Finset.mem_sdiff]

/-- Toggling a face at γ=(0,1) flips exactly the second coordinate on edges of `f`. -/
lemma support₂_toggle_symmDiff {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) :
    support₂ (faceBoundaryChain (γ := (0,1)) f) = f := by
  classical
  ext e
  by_cases he : e ∈ f
  · simp [faceBoundaryChain, indicatorChain, he]
  · simp [faceBoundaryChain, indicatorChain, he]

/-- When adding a face boundary at γ=(0,1), the γ₂-support changes via symmetric difference. -/
lemma support₂_after_toggle {E : Type*} [Fintype E] [DecidableEq E]
    {x : E → Color} {f : Finset E} :
    support₂ (x + faceBoundaryChain (γ := (0,1)) f)
      = (support₂ x \ f) ∪ (f \ support₂ x) := by
  classical
  ext e
  by_cases he : e ∈ f
  · -- second coordinate flips on f
    have hγ : (faceBoundaryChain (γ := (0,1)) f e).snd = 1 := by
      simp [faceBoundaryChain, indicatorChain, he]
    have : (x e).snd = 0 ∨ (x e).snd = 1 := by
      rcases (x e).snd with ⟨v, hv⟩
      interval_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases this with h0 | h1
    · simp [he, hγ, h0, Finset.mem_union, Finset.mem_sdiff]
    · simp [he, hγ, h1, Finset.mem_union, Finset.mem_sdiff]
  · -- off f, second coordinate unchanged
    have hγ : (faceBoundaryChain (γ := (0,1)) f e).snd = 0 := by
      simp [faceBoundaryChain, indicatorChain, he]
    simp [he, hγ, Finset.mem_union, Finset.mem_sdiff]

/-- Fold symmetric difference over a list of faces, tracking support changes across multiple toggles.
This helper is useful for analyzing how support evolves when toggling multiple faces sequentially. -/
def symmDiffFold {E : Type*} [DecidableEq E]
    (initial : Finset E) (faces : List (Finset E)) : Finset E :=
  faces.foldl (fun acc f => (acc \ f) ∪ (f \ acc)) initial

@[simp] lemma symmDiffFold_nil {E : Type*} [DecidableEq E] (initial : Finset E) :
    symmDiffFold initial [] = initial := by
  unfold symmDiffFold
  rfl

lemma symmDiffFold_cons {E : Type*} [DecidableEq E]
    (initial : Finset E) (f : Finset E) (faces : List (Finset E)) :
    symmDiffFold initial (f :: faces) =
      symmDiffFold ((initial \ f) ∪ (f \ initial)) faces := by
  unfold symmDiffFold
  simp [List.foldl]

-- First-coordinate pointwise evaluation for a single face boundary at γ=(1,0).
@[simp] lemma fst_faceBoundary_at {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) (e : E) :
    (faceBoundaryChain (γ := (1,0)) f e).fst
      = (if e ∈ f then (1 : ZMod 2) else 0) := by
  classical
  by_cases he : e ∈ f
  · simp [faceBoundaryChain, indicatorChain, he]
  · simp [faceBoundaryChain, indicatorChain, he]

-- Second-coordinate pointwise evaluation for a single face boundary at γ=(0,1).
@[simp] lemma snd_faceBoundary_at {E : Type*} [Fintype E] [DecidableEq E]
    (f : Finset E) (e : E) :
    (faceBoundaryChain (γ := (0,1)) f e).snd
      = (if e ∈ f then (1 : ZMod 2) else 0) := by
  classical
  by_cases he : e ∈ f
  · simp [faceBoundaryChain, indicatorChain, he]
  · simp [faceBoundaryChain, indicatorChain, he]

/-- γ=(1,0): the first coordinate of the finite sum at edge `e` is
the Z₂-sum of membership indicators `(e ∈ f)` over `f ∈ S`. -/
lemma fst_sum_faceBoundary_at {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) (e : E) :
    ((∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) e).fst
      = ∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0) := by
  classical
  revert e
  refine Finset.induction_on S ?base ?step
  · intro e; simp
  · intro a S ha ih e
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Pi.add_apply]
    -- Goal: (faceBoundaryChain (1,0) a e + (∑ x ∈ S, faceBoundaryChain (1,0) x) e).fst = ...
    -- .fst distributes over +
    show (faceBoundaryChain (1, 0) a e + (∑ x ∈ S, faceBoundaryChain (1, 0) x) e).fst =
      (if e ∈ a then 1 else 0) + ∑ f ∈ S, if e ∈ f then 1 else 0
    simp only [Prod.fst_add, fst_faceBoundary_at]
    congr 1
    exact ih e

/-- γ=(0,1): the second coordinate of the finite sum at edge `e` is
the Z₂-sum of membership indicators `(e ∈ f)` over `f ∈ S`. -/
lemma snd_sum_faceBoundary_at {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) (e : E) :
    ((∑ f ∈ S, faceBoundaryChain (γ := (0,1)) f) e).snd
      = ∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0) := by
  classical
  revert e
  refine Finset.induction_on S ?base ?step
  · intro e; simp
  · intro a S ha ih e
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Pi.add_apply]
    -- Goal: (faceBoundaryChain (0,1) a e + (∑ x ∈ S, faceBoundaryChain (0,1) x) e).snd = ...
    -- .snd distributes over +
    show (faceBoundaryChain (0, 1) a e + (∑ x ∈ S, faceBoundaryChain (0, 1) x) e).snd =
      (if e ∈ a then 1 else 0) + ∑ f ∈ S, if e ∈ f then 1 else 0
    simp only [Prod.snd_add, snd_faceBoundary_at]
    congr 1
    exact ih e

/-- Edges toggled by the sum of face boundaries at γ=(1,0) are exactly those
with odd incidence across the summation set. -/
def oddOn {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) : Finset E :=
  Finset.univ.filter (fun e =>
    (∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0)) ≠ 0)

-- Clean parity identity for γ = (1,0): support₁ of the sum equals the odd-incidence set.
lemma support₁_sum_faceBoundary_gamma10_eq_oddOn {E : Type*}
    [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) :
    support₁ (∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) = oddOn S := by
  classical
  ext e
  -- pointwise at e; keep simp minimal so we don't trigger card-of-filter lemmas:
  have hfst : ((∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) e).fst
               = ∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0) :=
    fst_sum_faceBoundary_at S e
  have hsum_odd : (∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0)) ≠ 0
          ↔ e ∈ oddOn S := by
    -- literal def of oddOn
    simp only [oddOn, Finset.mem_filter, Finset.mem_univ, true_and]
  -- LHS membership is "fst ≠ 0" by def of support₁
  have hlhs : e ∈ support₁ (∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f)
          ↔ ((∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0)) ≠ 0) := by
    -- def of support₁ + rewrite at e via hfst
    simp only [support₁, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfst]
  -- done
  rw [hlhs, hsum_odd]

lemma support₁_sum_faceBoundary_of_zero {E : Type*} [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) :
    support₁ (∑ f ∈ S, faceBoundaryChain (γ := (1,0)) f) = oddOn S :=
  support₁_sum_faceBoundary_gamma10_eq_oddOn S

-- Symmetric (0,1) parity lemma: support₂ of the sum equals the odd-incidence set.
lemma support₂_sum_faceBoundary_gamma01_eq_oddOn {E : Type*}
    [Fintype E] [DecidableEq E]
    (S : Finset (Finset E)) :
    support₂ (∑ f ∈ S, faceBoundaryChain (γ := (0,1)) f) = oddOn S := by
  classical
  ext e
  have hsnd : ((∑ f ∈ S, faceBoundaryChain (γ := (0,1)) f) e).snd
               = ∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0) :=
    snd_sum_faceBoundary_at S e
  have hsum_odd : (∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0)) ≠ 0
          ↔ e ∈ oddOn S := by
    simp only [oddOn, Finset.mem_filter, Finset.mem_univ, true_and]
  have hlhs : e ∈ support₂ (∑ f ∈ S, faceBoundaryChain (γ := (0,1)) f)
          ↔ ((∑ f ∈ S, (if e ∈ f then (1 : ZMod 2) else 0)) ≠ 0) := by
    simp only [support₂, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsnd]
  rw [hlhs, hsum_odd]

/-- "Span" of face boundary chains: all finite XOR-sums of the given face
boundaries, coloured by `γ`.  We encode the span concretely via `Finset` sums so
that we remain within the current function-based formalisation of chains. -/
def faceBoundarySpan (γ : Color) (faces : Finset (Finset E)) : Set (E → Color) :=
  {x | ∃ S ⊆ faces, x = ∑ f ∈ S, faceBoundaryChain (γ := γ) f}
section FaceBoundaryHelpers

variable {V E : Type*} [Fintype V] [DecidableEq V]
variable [Fintype E] [DecidableEq E]

lemma mem_faceBoundarySpan_of_subset {γ : Color}
    {faces S : Finset (Finset E)} (hS : S ⊆ faces) :
    (∑ f ∈ S, faceBoundaryChain (γ := γ) f) ∈ faceBoundarySpan γ faces := by
  refine ⟨S, hS, rfl⟩

lemma faceBoundarySpan_mono {γ : Color} {faces faces' : Finset (Finset E)}
    (hfaces : faces ⊆ faces') :
    faceBoundarySpan γ faces ⊆ faceBoundarySpan γ faces' := by
  intro x hx
  rcases hx with ⟨S, hS, hsum⟩
  exact ⟨S, hS.trans hfaces, hsum⟩

/-- Over `𝔽₂ × 𝔽₂`, a face boundary added to itself is the zero chain. -/
lemma faceBoundaryChain_add_self {γ : Color} (f : Finset E) :
    faceBoundaryChain (γ := γ) f + faceBoundaryChain (γ := γ) f
      = zeroChain (E := E) := by
  classical
  funext e
  by_cases he : e ∈ f
  · rcases γ with ⟨γ₁, γ₂⟩
    ext <;> simp [faceBoundaryChain, zeroChain, he, zmod2_add_self]
  · ext <;> simp [faceBoundaryChain, zeroChain, he]

/-
Linearity of `chainDot` over finite sums of face boundaries, used to push
orthogonality from generators to their finite XOR-sums.
-/
-- (reserved for future: orthogonality propagation to spans)

/-- Summation helper: adding a fresh face toggles its boundary chain. -/
lemma sum_faceBoundary_insert {γ : Color} {faces : Finset (Finset E)} {face : Finset E}
    (hface : face ∉ faces) :
    (∑ f ∈ insert face faces, faceBoundaryChain (γ := γ) f)
        = faceBoundaryChain (γ := γ) face
            + ∑ f ∈ faces, faceBoundaryChain (γ := γ) f := by
  classical
  simpa using
    (Finset.sum_insert (s := faces) (a := face)
      (f := fun f => faceBoundaryChain (γ := γ) f)
      (by simpa using hface))

lemma sum_faceBoundary_face_plus_erase_eq {γ : Color}
    {faces : Finset (Finset E)} {face : Finset E}
    (hface : face ∈ faces) :
    faceBoundaryChain (γ := γ) face
      + ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f
        = ∑ f ∈ faces, faceBoundaryChain (γ := γ) f := by
  classical
  have hnot : face ∉ faces.erase face := Finset.notMem_erase _ _
  have hperm : insert face (faces.erase face) = faces := Finset.insert_erase hface
  have hsum :
      ∑ f ∈ insert face (faces.erase face), faceBoundaryChain (γ := γ) f =
        faceBoundaryChain (γ := γ) face
          + ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f := by
    simpa using
      (Finset.sum_insert (s := faces.erase face) (a := face)
        (f := fun f => faceBoundaryChain (γ := γ) f)
        (by simpa using hnot))
  calc
    faceBoundaryChain (γ := γ) face
        + ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f
        = ∑ f ∈ insert face (faces.erase face), faceBoundaryChain (γ := γ) f := by
            simpa [add_comm] using hsum.symm
    _ = ∑ f ∈ faces, faceBoundaryChain (γ := γ) f := by
            simpa [hperm]

/-- Summation helper: removing a face toggles its boundary chain. -/
lemma sum_faceBoundary_erase {γ : Color} {faces : Finset (Finset E)} {face : Finset E}
    (hface : face ∈ faces) :
    (∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f)
        = faceBoundaryChain (γ := γ) face
            + ∑ f ∈ faces, faceBoundaryChain (γ := γ) f := by
  classical
  have hsum :=
    sum_faceBoundary_face_plus_erase_eq (γ := γ) (faces := faces) (face := face) hface
  calc
    ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f
        = zeroChain (E := E) +
            ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f := by simp [zeroChain]
    _ = (faceBoundaryChain (γ := γ) face + faceBoundaryChain (γ := γ) face)
            + ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f := by
              simp [faceBoundaryChain_add_self, add_comm, add_left_comm, add_assoc]
    _ = faceBoundaryChain (γ := γ) face
            + (faceBoundaryChain (γ := γ) face
                + ∑ f ∈ faces.erase face, faceBoundaryChain (γ := γ) f) := by
              simp [add_comm, add_left_comm, add_assoc]
    _ = faceBoundaryChain (γ := γ) face
            + ∑ f ∈ faces, faceBoundaryChain (γ := γ) f := by
              simpa [hsum, add_comm, add_left_comm, add_assoc]

end FaceBoundaryHelpers

/-- **LEGACY**: Data for leaf-peeling induction with single-face peels.

**Prefer `LeafPeelSumData`** for new code. The aggregated multi-face approach in `LeafPeelSumData`
directly matches Goertzel v3 (§4.2, Lemma 4.8) and avoids the need to factorize aggregated
toggles into strict single-face cuts. This structure is retained for compatibility and
alternative proof strategies, but the main proof pipeline uses `LeafPeelSumData.peel_sum`.

See `LeafPeelSumData` for the preferred aggregated-peel approach. -/

structure LeafPeelData (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := (1,0)
  internalFaces : Finset (Finset E)
  boundary_mem_zero :
    ∀ {f}, f ∈ internalFaces →
      faceBoundaryChain (γ := gamma) f ∈ zero.zeroBoundarySet
  /-- Tightness: chains with empty γ-support are zero. This holds for planar disks
  where interior edges form a basis, or can be proven by iterating over γ=(0,1). -/
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain (E := E)
  /-- **Cardinality decrease version**: the induction only needs `card (support₁ x') < card (support₁ x)`. -/
  peel :
    ∀ {x},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ f ∈ internalFaces, ∃ x',
        x' ∈ zero.zeroBoundarySet ∧
        x = x' + faceBoundaryChain (γ := gamma) f ∧
        Finset.card (support₁ x') < Finset.card (support₁ x)

/-- Data for leaf-peeling induction using **multi-face aggregated peels** (Option A from LEAF_CUT_SWITCH.md).

This structure directly implements the paper's approach from §4.2 (Lemma 4.8, Theorem 4.9).
Unlike `LeafPeelData` which returns a single face, this returns a set of faces S₀ (a leaf-subtree)
and uses the aggregated toggle B̃_αβ(S₀) = ⊕_{f ∈ S₀} B^f_αβ.

The `peel_sum` field is **directly provable** using the cut-parity and orthogonality arguments
from the paper, whereas the single-face strict cut in `LeafPeelData.peel` requires an extra
factorization step that may be challenging to formalize. -/
structure LeafPeelSumData (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] where
  zero : ZeroBoundaryData V E
  gamma : Color := (1,0)
  internalFaces : Finset (Finset E)
  boundary_mem_zero_sum :
    ∀ {S}, S ⊆ internalFaces →
      (∑ f ∈ S, faceBoundaryChain (γ := gamma) f) ∈ zero.zeroBoundarySet
  tight :
    ∀ {x}, x ∈ zero.zeroBoundarySet → support₁ x = ∅ → x = zeroChain (E := E)
  /-- **Multi-face peel**: Returns a nonempty set S₀ ⊆ internalFaces (leaf-subtree) such that
  toggling the aggregated sum strictly decreases support₁. This is the formulation
  that directly matches Lemma 4.8 in the paper. -/
  peel_sum :
    ∀ {x},
      x ∈ zero.zeroBoundarySet →
      support₁ x ≠ ∅ →
      ∃ (S₀ : Finset (Finset E)),
        S₀.Nonempty ∧
        S₀ ⊆ internalFaces ∧
        ∃ x',
          x' ∈ zero.zeroBoundarySet ∧
          x = x' + (∑ f ∈ S₀, faceBoundaryChain (γ := gamma) f) ∧
          Finset.card (support₁ x') < Finset.card (support₁ x)

/-- Lemma 4.5: zero-boundary chains lie in the span of the face boundaries. -/
theorem LeafPeelData.facialBasis_zeroBoundary_in_span
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (dual : LeafPeelData V E) :
    dual.zero.zeroBoundarySet ⊆ faceBoundarySpan dual.gamma dual.internalFaces := by
  classical
  -- Strong induction on γ-coordinate support size.
  have peel_induction :
      ∀ n {x}, x ∈ dual.zero.zeroBoundarySet →
        Finset.card (support₁ x) ≤ n →
        ∃ S ⊆ dual.internalFaces,
          x = ∑ f ∈ S, faceBoundaryChain (γ := dual.gamma) f := by
    intro n
    induction' n with n ih
    · intro x hx hcard
      have hsupp : support₁ x = ∅ := by
        have : Finset.card (support₁ x) = 0 :=
          Nat.le_antisymm hcard (Nat.zero_le _)
        exact Finset.card_eq_zero.mp this
      -- When γ=(1,0), if support₁ is empty, all first coordinates are zero
      have h_fst_zero : ∀ e, (x e).fst = 0 := support₁_eq_empty_iff.mp hsupp
      -- We want to show x = ∑_{f∈∅} faceBoundaryChain γ f = 0
      -- Strategy: Since faceBoundaryChain γ f only affects first coordinate,
      -- and x has all first coords zero, we need x to be the zero chain.
      -- For the 4CT, we'd need to handle the second coordinate using γ=(0,1).
      -- Here we make the simplifying assumption that the zero-boundary data
      -- is "γ-tight": chains with γ-support empty are actually zero.
      -- This holds for typical planar graph constructions where edges form a basis.
      -- Full generality would require iterating over both γ=(1,0) and γ=(0,1).
      have hx_zero : x = zeroChain (E := E) :=
        -- Use tightness hypothesis: support₁ empty ⇒ x = 0
        dual.tight hx hsupp
      subst hx_zero
      exact ⟨∅, by simp, by simp [faceBoundaryChain, zeroChain]⟩
    · intro x hx hcard
      by_cases hzero : support₁ x = ∅
      · -- Same as base case: use tightness
        have hx_zero : x = zeroChain (E := E) :=
          dual.tight hx hzero
        subst hx_zero
        exact ⟨∅, by simp, by simp [faceBoundaryChain, zeroChain]⟩
      · obtain ⟨f, hf, x', hx', hx_eq, hlt⟩ :=
          dual.peel hx (by simpa using hzero)
        have hcard' : Finset.card (support₁ x') ≤ n :=
          (Nat.lt_succ_iff).1 (lt_of_lt_of_le hlt hcard)
        obtain ⟨S, hSsubset, hx'S⟩ := ih hx' hcard'
        by_cases hfS : f ∈ S
        · have hx_sum :=
            sum_faceBoundary_face_plus_erase_eq (γ := dual.gamma)
              (faces := S) (face := f) hfS
          refine ⟨S.erase f, ?_, ?_⟩
          · intro g hg
            exact hSsubset (Finset.mem_of_mem_erase hg)
          · calc
              x = x' + faceBoundaryChain (γ := dual.gamma) f := hx_eq
              _ = ∑ g ∈ S, faceBoundaryChain (γ := dual.gamma) g
                    + faceBoundaryChain (γ := dual.gamma) f := by
                        simp [hx'S, add_comm, add_left_comm, add_assoc]
              _ = faceBoundaryChain (γ := dual.gamma) f
                    + (faceBoundaryChain (γ := dual.gamma) f
                        + ∑ g ∈ S.erase f, faceBoundaryChain (γ := dual.gamma) g) := by
                        simpa [hx_sum, add_comm, add_left_comm, add_assoc]
              _ = (faceBoundaryChain (γ := dual.gamma) f
                    + faceBoundaryChain (γ := dual.gamma) f)
                        + ∑ g ∈ S.erase f, faceBoundaryChain (γ := dual.gamma) g := by
                        simp [add_comm, add_left_comm, add_assoc]
              _ = ∑ g ∈ S.erase f, faceBoundaryChain (γ := dual.gamma) g := by
                        simp [faceBoundaryChain_add_self, zeroChain, add_comm, add_left_comm, add_assoc]
        · have hx_sum :=
            sum_faceBoundary_insert (γ := dual.gamma)
              (faces := S) (face := f) (by simpa using hfS)
          refine ⟨insert f S, ?_, ?_⟩
          · intro g hg
            rcases Finset.mem_insert.mp hg with rfl | hg'
            · simpa using hf
            · exact hSsubset hg'
          · calc
              x = x' + faceBoundaryChain (γ := dual.gamma) f := hx_eq
              _ = ∑ g ∈ S, faceBoundaryChain (γ := dual.gamma) g
                    + faceBoundaryChain (γ := dual.gamma) f := by
                        simp [hx'S, add_comm, add_left_comm, add_assoc]
              _ = faceBoundaryChain (γ := dual.gamma) f
                    + ∑ g ∈ S, faceBoundaryChain (γ := dual.gamma) g := by
                        simp [add_comm, add_left_comm, add_assoc]
              _ = ∑ g ∈ insert f S, faceBoundaryChain (γ := dual.gamma) g := by
                        simpa [hx_sum, add_comm, add_left_comm, add_assoc]
  intro x hx
  obtain ⟨S, hSsubset, hxS⟩ :=
    peel_induction (Finset.card (support₁ x)) hx (le_rfl)
  exact ⟨S, hSsubset, hxS⟩

/-- Convenience wrapper avoiding namespace qualification. -/
lemma facialBasis_zeroBoundary_in_span
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (dual : LeafPeelData V E) :
    dual.zero.zeroBoundarySet ⊆ faceBoundarySpan dual.gamma dual.internalFaces :=
  dual.facialBasis_zeroBoundary_in_span
