import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.LinearAlgebra.Finsupp.LSum

/-!
# Single-species Behr–Krivine rule algebra with read and exhaust structure

A single-species interaction rule `(take, keep, make, exhaust)` consumes `take`
distinct occurrences, inspects `keep` distinct surviving occurrences, mints
`make` fresh occurrences, and—when `exhaust = true`—requires that zero
unmatched occurrences remain outside `take + keep`.

Notice how `exhaust = true` unifies the non-monotone full-read primitives of
the reactive interaction basis into a single closed invariant:
* `take = 0, keep = 0, exhaust = true` requires `x = 0` (pure absence);
* `take = 0, keep = 1, exhaust = true` requires `x = 1` (unique read);
* `take = 1, keep = 0, exhaust = true` consumes the unique occurrence;
* `take = n, keep = 0, exhaust = true` consumes all `n` occurrences.

We construct:
1. Overlap composition `compose1 r₂ r₁ : SingleRule →₀ ℕ` with exact integral
   multiplicity `Overlap1.mult` and transported `exhaust` guards.
2. The standard uncolored bag representation `rho1` (`binom x take * binom (x - take) keep`).
3. The enriched 3-color occurrence-tracked representation `occRho1` over
   `(untouched, read, new) : ℕ × ℕ × ℕ`, which is proved **injective (faithful)**
   and a **homomorphism** (`occRho1_mul`), intertwined with `rho1` via the
   color-forgetting projection `forgetColors`.
4. Exact associativity `(A * B) * C = A * (B * C)` and `Semiring SingleRuleAlgebra`,
   deduced conceptually from faithfulness of `occRho1`.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RuleAlgebra

open scoped BigOperators

/-- A single-species interaction rule with consumption (`take`), read-arc
inspection (`keep`), production (`make`), and zero-residual guard (`exhaust`). -/
structure SingleRule where
  take : ℕ
  keep : ℕ
  make : ℕ
  exhaust : Bool
  deriving DecidableEq, Repr

namespace SingleRule

/-- The trivial identity rule: takes nothing, keeps nothing, makes nothing, no exhaust guard. -/
def id : SingleRule := ⟨0, 0, 0, false⟩

/-- Pure absence guard: requires count `0` without consuming or producing. -/
def pureAbsent : SingleRule := ⟨0, 0, 0, true⟩

/-- Pure pattern-count observable rule: inspects `k` distinct occurrences. -/
def keepOnly (k : ℕ) : SingleRule := ⟨0, k, 0, false⟩

/-- Number of occurrence-subset matches of `r` on a bag of size `x`. -/
def matchesCount (r : SingleRule) (x : ℕ) : ℕ :=
  if r.exhaust && decide (x ≠ r.take + r.keep) then 0
  else Nat.choose x r.take * Nat.choose (x - r.take) r.keep

@[simp]
theorem id_matchesCount (x : ℕ) : SingleRule.id.matchesCount x = 1 := by
  simp [SingleRule.id, matchesCount]

theorem matchesCount_eq_zero_of_lt (r : SingleRule) {x : ℕ} (hx : x < r.take + r.keep) :
    r.matchesCount x = 0 := by
  unfold matchesCount
  split_ifs with h
  · rfl
  · by_cases ht : x < r.take
    · simp [Nat.choose_eq_zero_of_lt ht]
    · have hk : x - r.take < r.keep := by omega
      simp [Nat.choose_eq_zero_of_lt hk]

end SingleRule

/-- An overlap specification between a first rule `r₁` and a second rule `r₂`:
* `u`: tokens minted by `r₁` that `r₂` consumes (`take`);
* `v`: tokens kept by `r₁` that `r₂` consumes (`take`);
* `w`: surviving minted tokens of `r₁` that `r₂` inspects (`keep`);
* `z`: surviving kept tokens of `r₁` that `r₂` also inspects (`keep`). -/
structure Overlap1 where
  u : ℕ
  v : ℕ
  w : ℕ
  z : ℕ
  deriving DecidableEq, Repr

namespace Overlap1

/-- Validity of an overlap `ov` for `r₁` followed by `r₂`, including transported
residual-exhaustion compatibility. -/
def Valid (r₂ r₁ : SingleRule) (ov : Overlap1) : Prop :=
  ov.u + ov.w ≤ r₁.make ∧
  ov.v + ov.z ≤ r₁.keep ∧
  ov.u + ov.v ≤ r₂.take ∧
  ov.w + ov.z ≤ r₂.keep ∧
  (r₁.exhaust = true → r₂.take = ov.u + ov.v ∧ r₂.keep = ov.w + ov.z) ∧
  (r₂.exhaust = true → r₁.make = ov.u + ov.w ∧ r₁.keep = ov.v + ov.z)

instance (r₂ r₁ : SingleRule) (ov : Overlap1) : Decidable (Valid r₂ r₁ ov) := by
  unfold Valid
  infer_instance

/-- Finite bounding box containing all valid overlaps for `r₁` followed by `r₂`. -/
def candidates (r₂ r₁ : SingleRule) : Finset Overlap1 :=
  (((Finset.range (r₁.make + 1) ×ˢ Finset.range (r₁.keep + 1)) ×ˢ
      Finset.range (r₁.make + 1)) ×ˢ Finset.range (r₁.keep + 1)).map
    ⟨fun p => ⟨p.1.1.1, p.1.1.2, p.1.2, p.2⟩, by
      intro a b h
      cases a; cases b
      simp only [Overlap1.mk.injEq] at h
      ext <;> simp [h]⟩ |>.filter (fun ov => Valid r₂ r₁ ov)

theorem mem_candidates_iff (r₂ r₁ : SingleRule) (ov : Overlap1) :
    ov ∈ candidates r₂ r₁ ↔ Valid r₂ r₁ ov := by
  simp only [candidates, Finset.mem_filter, Finset.mem_map, Finset.mem_product,
    Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hv
    refine ⟨⟨(((ov.u, ov.v), ov.w), ov.z), ?_, rfl⟩, hv⟩
    rcases hv with ⟨h1, h2, _, _, _, _⟩
    dsimp only
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> omega

/-- Composite single-species rule produced along overlap `ov`. -/
def composedRule (r₂ r₁ : SingleRule) (ov : Overlap1) : SingleRule where
  take := r₁.take + (r₂.take - ov.u)
  keep := (r₁.keep - ov.v) + (r₂.keep - ov.w - ov.z)
  make := (r₁.make - ov.u) + r₂.make
  exhaust := r₁.exhaust || r₂.exhaust

/-- Integral combinatorial multiplicity of overlap `ov` in `r₂ ⋆ r₁`. -/
def mult (r₂ r₁ : SingleRule) (ov : Overlap1) : ℕ :=
  let T' := r₁.take + (r₂.take - ov.u)
  let K' := (r₁.keep - ov.v) + (r₂.keep - ov.w - ov.z)
  Nat.choose r₁.make ov.u *
    Nat.choose (r₁.make - ov.u) ov.w *
    Nat.choose T' r₁.take *
    Nat.choose (r₂.take - ov.u) ov.v *
    Nat.choose K' (r₁.keep - ov.v) *
    Nat.choose (r₁.keep - ov.v) ov.z

end Overlap1

/-- Formal-sum Behr–Krivine composition `r₂ ⋆₁ r₁` of two single-species rules. -/
noncomputable def compose1 (r₂ r₁ : SingleRule) : SingleRule →₀ ℕ :=
  (Overlap1.candidates r₂ r₁).sum fun ov =>
    Finsupp.single (Overlap1.composedRule r₂ r₁ ov) (Overlap1.mult r₂ r₁ ov)

/-- Bilinear extension of `compose1` to `SingleRule →₀ ℕ`. -/
noncomputable def mul1 (A B : SingleRule →₀ ℕ) : SingleRule →₀ ℕ :=
  A.sum fun r₂ c₂ => B.sum fun r₁ c₁ => (c₂ * c₁) • compose1 r₂ r₁

@[simp]
theorem mul1_zero_left (B : SingleRule →₀ ℕ) : mul1 0 B = 0 := by
  simp [mul1]

@[simp]
theorem mul1_zero_right (A : SingleRule →₀ ℕ) : mul1 A 0 = 0 := by
  simp [mul1]

theorem mul1_add_left (A₁ A₂ B : SingleRule →₀ ℕ) :
    mul1 (A₁ + A₂) B = mul1 A₁ B + mul1 A₂ B := by
  unfold mul1
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₂ a₁ a₂
    rw [← Finsupp.sum_add]
    congr 1; ext r₁ c₁
    rw [Nat.add_mul, add_smul]

theorem mul1_add_right (A B₁ B₂ : SingleRule →₀ ℕ) :
    mul1 A (B₁ + B₂) = mul1 A B₁ + mul1 A B₂ := by
  unfold mul1
  rw [← Finsupp.sum_add]
  congr 1; ext r₂ c₂
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₁ b₁ b₂
    rw [Nat.mul_add, add_smul]

theorem mul1_single_single (r₂ r₁ : SingleRule) :
    mul1 (Finsupp.single r₂ 1) (Finsupp.single r₁ 1) = compose1 r₂ r₁ := by
  simp [mul1]

theorem mul1_smul_single_single (c₂ c₁ : ℕ) (r₂ r₁ : SingleRule) :
    mul1 (Finsupp.single r₂ c₂) (Finsupp.single r₁ c₁) = (c₂ * c₁) • compose1 r₂ r₁ := by
  simp [mul1]

theorem compose1_id_right (r : SingleRule) :
    compose1 r SingleRule.id = Finsupp.single r 1 := by
  have hcand : Overlap1.candidates r SingleRule.id = {⟨0, 0, 0, 0⟩} := by
    ext ov
    rw [Overlap1.mem_candidates_iff, Finset.mem_singleton]
    rcases ov with ⟨u, v, w, z⟩
    simp only [Overlap1.Valid, SingleRule.id, Overlap1.mk.injEq]
    constructor
    · rintro ⟨h1, h2, _, _, _, _⟩; omega
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
      · intro h; cases h
      · intro _; exact ⟨rfl, rfl⟩
  simp only [compose1, hcand, Finset.sum_singleton]
  have hrule : Overlap1.composedRule r SingleRule.id ⟨0, 0, 0, 0⟩ = r := by
    cases r; simp [Overlap1.composedRule, SingleRule.id]
  have hmult : Overlap1.mult r SingleRule.id ⟨0, 0, 0, 0⟩ = 1 := by
    simp [Overlap1.mult, SingleRule.id]
  rw [hrule, hmult]

theorem compose1_id_left (r : SingleRule) :
    compose1 SingleRule.id r = Finsupp.single r 1 := by
  have hcand : Overlap1.candidates SingleRule.id r = {⟨0, 0, 0, 0⟩} := by
    ext ov
    rw [Overlap1.mem_candidates_iff, Finset.mem_singleton]
    rcases ov with ⟨u, v, w, z⟩
    simp only [Overlap1.Valid, SingleRule.id, Overlap1.mk.injEq]
    constructor
    · rintro ⟨_, _, h3, h4, _, _⟩; omega
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
      · intro _; exact ⟨rfl, rfl⟩
      · intro h; cases h
  simp only [compose1, hcand, Finset.sum_singleton]
  have hrule : Overlap1.composedRule SingleRule.id r ⟨0, 0, 0, 0⟩ = r := by
    cases r; simp [Overlap1.composedRule, SingleRule.id]
  have hmult : Overlap1.mult SingleRule.id r ⟨0, 0, 0, 0⟩ = 1 := by
    simp [Overlap1.mult, SingleRule.id]
  rw [hrule, hmult]

private theorem nat_smul_single_one {α : Type*} (c : ℕ) (a : α) :
    c • Finsupp.single a (1 : ℕ) = Finsupp.single a c := by
  ext x
  by_cases h : a = x <;> simp [h]

theorem mul1_id_right (A : SingleRule →₀ ℕ) :
    mul1 A (Finsupp.single SingleRule.id 1) = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mul1_add_left, hx, hy]) ?_
  intro r c
  rw [mul1_smul_single_single, compose1_id_right, Nat.mul_one, nat_smul_single_one]

theorem mul1_id_left (A : SingleRule →₀ ℕ) :
    mul1 (Finsupp.single SingleRule.id 1) A = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mul1_add_right, hx, hy]) ?_
  intro r c
  rw [mul1_smul_single_single, compose1_id_left, Nat.one_mul, nat_smul_single_one]

/-! ## Uncolored and 3-color concrete occurrence representations -/

/-- Action of a single rule on an uncolored bag-count basis ket `|x⟩`.
Note that when `x < r.take + r.keep`, `r.matchesCount x = 0`, so this evaluates to `0`. -/
noncomputable def rhoRule1 (r : SingleRule) (x : ℕ) : ℕ →₀ ℕ :=
  Finsupp.single (x - r.take + r.make) (r.matchesCount x)

/-- Linear operator `ρ₁(A)` on the free `ℕ`-module `ℕ →₀ ℕ` of bag counts. -/
noncomputable def rho1 (A : SingleRule →₀ ℕ) : (ℕ →₀ ℕ) →ₗ[ℕ] (ℕ →₀ ℕ) :=
  A.sum fun r c => c • Finsupp.lsum ℕ (fun x =>
    (Finsupp.lsingle (x - r.take + r.make)).comp (LinearMap.mulLeft ℕ (r.matchesCount x)))

@[simp]
theorem rho1_zero : rho1 0 = 0 := by simp [rho1]

theorem rho1_add (A B : SingleRule →₀ ℕ) : rho1 (A + B) = rho1 A + rho1 B := by
  unfold rho1
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]

theorem rho1_smul (c : ℕ) (A : SingleRule →₀ ℕ) : rho1 (c • A) = c • rho1 A := by
  unfold rho1
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext r
  rw [smul_eq_mul, mul_smul]

theorem rho1_single_apply (r : SingleRule) (x : ℕ) :
    rho1 (Finsupp.single r 1) (Finsupp.single x 1) = rhoRule1 r x := by
  simp [rho1, rhoRule1]

/-- 3-color occurrence counts `(untouched_initial, read_initial, new_minted)`. -/
abbrev OccCount := ℕ × ℕ × ℕ

/-- Color-forgetting linear projection `|(u, r_c, n)⟩ ↦ |(u + r_c + n)⟩`. -/
noncomputable def forgetColors : (OccCount →₀ ℕ) →ₗ[ℕ] (ℕ →₀ ℕ) :=
  Finsupp.lsum ℕ fun c => Finsupp.lsingle (c.1 + c.2.1 + c.2.2)

@[simp]
theorem forgetColors_single (c : OccCount) (v : ℕ) :
    forgetColors (Finsupp.single c v) = Finsupp.single (c.1 + c.2.1 + c.2.2) v := by
  simp [forgetColors]

/-- Concrete occurrence-subset firings `(T, K)` of `r` on a finite token set `X`. -/
def firingsOn (r : SingleRule) (X : Finset ℕ) : Finset (Finset ℕ × Finset ℕ) :=
  (((X.powersetCard r.take).sigma fun T => (X \ T).powersetCard r.keep).map
    ⟨fun s => (s.1, s.2), fun a b h => by
      cases a; cases b
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl⟩).filter fun p => !r.exhaust || decide (p.1 ∪ p.2 = X)

theorem mem_firingsOn {r : SingleRule} {X : Finset ℕ} {p : Finset ℕ × Finset ℕ} :
    p ∈ firingsOn r X ↔
      p.1 ⊆ X ∧ p.1.card = r.take ∧ p.2 ⊆ X \ p.1 ∧ p.2.card = r.keep ∧
        (r.exhaust = true → p.1 ∪ p.2 = X) := by
  rcases p with ⟨T, K⟩
  simp only [firingsOn, Finset.mem_filter, Finset.mem_map, Finset.mem_sigma,
    Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨⟨T', K'⟩, ⟨⟨hT1, hT2⟩, ⟨hK1, hK2⟩⟩, hEq⟩, hex⟩
    rcases Prod.mk.inj hEq with ⟨rfl, rfl⟩
    refine ⟨hT1, hT2, hK1, hK2, ?_⟩
    intro he
    simpa [he] using hex
  · rintro ⟨hT1, hT2, hK1, hK2, hex⟩
    refine ⟨⟨⟨T, K⟩, ⟨⟨hT1, hT2⟩, ⟨hK1, hK2⟩⟩, rfl⟩, ?_⟩
    cases he : r.exhaust
    · simp
    · simp [hex he]

theorem card_firingsOn (r : SingleRule) (X : Finset ℕ) :
    (firingsOn r X).card = r.matchesCount X.card := by
  unfold SingleRule.matchesCount
  by_cases hbad : (r.exhaust && decide (X.card ≠ r.take + r.keep)) = true
  · rw [if_pos hbad]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbad
    rcases hbad with ⟨he, hne⟩
    suffices firingsOn r X = ∅ by simp [this]
    ext p
    simp only [Finset.notMem_empty, iff_false]
    rw [mem_firingsOn]
    rintro ⟨_, hTc, hKsub, hKc, hex⟩
    have hdisj : Disjoint p.1 p.2 := disjoint_sdiff_self_right.mono_right hKsub
    have hcard : (p.1 ∪ p.2).card = r.take + r.keep := by
      rw [Finset.card_union_of_disjoint hdisj, hTc, hKc]
    rw [hex he] at hcard
    exact hne hcard
  · rw [if_neg hbad]
    have hfilter : firingsOn r X =
        (((X.powersetCard r.take).sigma fun T => (X \ T).powersetCard r.keep).map
          ⟨fun s => (s.1, s.2), fun a b h => by
            cases a; cases b; simp only [Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl⟩) := by
      apply Finset.filter_true_of_mem
      intro p hp
      simp only [Finset.mem_map, Finset.mem_sigma, Finset.mem_powersetCard] at hp
      rcases hp with ⟨⟨T, K⟩, ⟨⟨hT1, hT2⟩, ⟨hK1, hK2⟩⟩, hEq⟩
      have hp_eq : p = (T, K) := hEq.symm
      subst hp_eq
      cases he : r.exhaust
      · simp
      · simp only [he, Bool.true_and, decide_eq_true_eq, not_not] at hbad
        have hdisj : Disjoint T K := disjoint_sdiff_self_right.mono_right hK1
        have hsub : T ∪ K ⊆ X := Finset.union_subset hT1 (hK1.trans Finset.sdiff_subset)
        have hcard : (T ∪ K).card = X.card := by
          rw [Finset.card_union_of_disjoint hdisj, hT2, hK2, hbad]
        have hEqX : T ∪ K = X := Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
        simp [hEqX]
    rw [hfilter, Finset.card_map, Finset.card_sigma]
    by_cases hlt : X.card < r.take
    · have hemp : X.powersetCard r.take = ∅ := by
        rw [← Finset.card_eq_zero, Finset.card_powersetCard]
        exact Nat.choose_eq_zero_of_lt hlt
      simp [hemp, Nat.choose_eq_zero_of_lt hlt]
    · have hconst : ∀ T ∈ X.powersetCard r.take,
          ((X \ T).powersetCard r.keep).card = (X.card - r.take).choose r.keep := by
        intro T hT
        rw [Finset.mem_powersetCard] at hT
        rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hT.1, hT.2]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_powersetCard, smul_eq_mul]

/-- Output 3-color occurrence counts when `r` fires via `(T, K)` on disjoint `(U, R, N)`. -/
def outCount (r : SingleRule) (U R N T K : Finset ℕ) : OccCount :=
  ((U \ (T ∪ K)).card, ((R \ T) ∪ (U ∩ K)).card, (N \ T).card + r.make)

/-- Concrete occurrence step of `r` on disjoint token sets `(U, R, N)`. -/
noncomputable def occStepOn (r : SingleRule) (U R N : Finset ℕ) : OccCount →₀ ℕ :=
  (firingsOn r (U ∪ R ∪ N)).sum fun p => Finsupp.single (outCount r U R N p.1 p.2) 1

/-- Canonical untouched initial interval `[0, u)`. -/
def canonU (u : ℕ) : Finset ℕ := Finset.Ico 0 u
/-- Canonical read initial interval `[u, u + rc)`. -/
def canonR (u rc : ℕ) : Finset ℕ := Finset.Ico u (u + rc)
/-- Canonical minted interval `[u + rc, u + rc + n)`. -/
def canonN (u rc n : ℕ) : Finset ℕ := Finset.Ico (u + rc) (u + rc + n)

theorem canon_disjoint (u rc n : ℕ) :
    Disjoint (canonU u) (canonR u rc) ∧
    Disjoint (canonU u) (canonN u rc n) ∧
    Disjoint (canonR u rc) (canonN u rc n) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [canonU, canonR, canonN, Finset.mem_Ico] at hx1 hx2
      omega

@[simp] theorem card_canonU (u : ℕ) : (canonU u).card = u := by simp [canonU]
@[simp] theorem card_canonR (u rc : ℕ) : (canonR u rc).card = rc := by simp [canonR]
@[simp] theorem card_canonN (u rc n : ℕ) : (canonN u rc n).card = n := by simp [canonN]

theorem canon_union (u rc n : ℕ) :
    canonU u ∪ canonR u rc ∪ canonN u rc n = Finset.Ico 0 (u + rc + n) := by
  ext x
  simp only [canonU, canonR, canonN, Finset.mem_union, Finset.mem_Ico]
  omega

/-- Action of a single rule `r` on a 3-color count basis ket `|c⟩`. -/
noncomputable def occRule1 (r : SingleRule) (c : OccCount) : OccCount →₀ ℕ :=
  occStepOn r (canonU c.1) (canonR c.1 c.2.1) (canonN c.1 c.2.1 c.2.2)

/-- Linear scaling map `k ↦ k • v` into `OccCount →₀ ℕ`. -/
private noncomputable def scaleOcc (v : OccCount →₀ ℕ) : ℕ →ₗ[ℕ] (OccCount →₀ ℕ) where
  toFun k := k • v
  map_add' a b := add_smul a b v
  map_smul' a b := by simp [mul_smul]

@[simp]
private theorem scaleOcc_apply (v : OccCount →₀ ℕ) (k : ℕ) : scaleOcc v k = k • v := rfl

/-- Linear operator `occRho1 A` on the 3-color occurrence count module `OccCount →₀ ℕ`. -/
noncomputable def occRho1 (A : SingleRule →₀ ℕ) : (OccCount →₀ ℕ) →ₗ[ℕ] (OccCount →₀ ℕ) :=
  A.sum fun r c => c • Finsupp.lsum ℕ (fun x => scaleOcc (occRule1 r x))

@[simp]
theorem occRho1_zero : occRho1 0 = 0 := by simp [occRho1]

theorem occRho1_add (A B : SingleRule →₀ ℕ) : occRho1 (A + B) = occRho1 A + occRho1 B := by
  unfold occRho1
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]

theorem occRho1_smul (c : ℕ) (A : SingleRule →₀ ℕ) : occRho1 (c • A) = c • occRho1 A := by
  unfold occRho1
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext r
  rw [smul_eq_mul, mul_smul]

theorem occRho1_single_apply (r : SingleRule) (c : OccCount) :
    occRho1 (Finsupp.single r 1) (Finsupp.single c 1) = occRule1 r c := by
  simp [occRho1]

theorem occRho1_apply_single (A : SingleRule →₀ ℕ) (c : OccCount) :
    occRho1 A (Finsupp.single c 1) = A.sum (fun r coeff => coeff • occRule1 r c) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r coeff => ?_)
  · rw [occRho1_add, LinearMap.add_apply, hx, hy,
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]
  · simp [occRho1]

/-! ### Invariance of `occStepOn` under injective relabeling -/

private theorem image_sdiff_of_injOn {X A B : Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f X) (hA : A ⊆ X) (hB : B ⊆ X) :
    (A \ B).image f = A.image f \ B.image f := by
  ext y
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
    refine ⟨⟨x, hxA, rfl⟩, ?_⟩
    rintro ⟨x', hx'B, hfx⟩
    exact hxB (hf (hB hx'B) (hA hxA) hfx ▸ hx'B)
  · rintro ⟨⟨x, hxA, rfl⟩, hyB⟩
    refine ⟨x, ⟨hxA, fun hxB => hyB ⟨x, hxB, rfl⟩⟩, rfl⟩

private theorem image_inter_of_injOn {X A B : Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f X) (hA : A ⊆ X) (hB : B ⊆ X) :
    (A ∩ B).image f = A.image f ∩ B.image f := by
  ext y
  simp only [Finset.mem_image, Finset.mem_inter]
  constructor
  · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
    exact ⟨⟨x, hxA, rfl⟩, ⟨x, hxB, rfl⟩⟩
  · rintro ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hEq⟩⟩
    have : x₂ = x₁ := hf (hB hx₂) (hA hx₁) hEq
    subst this
    exact ⟨x₂, ⟨hx₁, hx₂⟩, rfl⟩

private theorem eq_of_image_eq_of_injOn {X A B : Finset ℕ} {f : ℕ → ℕ}
    (hf : Set.InjOn f X) (hA : A ⊆ X) (hB : B ⊆ X) (hEq : A.image f = B.image f) :
    A = B := by
  ext x
  constructor
  · intro hxA
    have : f x ∈ B.image f := hEq ▸ Finset.mem_image_of_mem f hxA
    rcases Finset.mem_image.mp this with ⟨x', hx'B, hfx⟩
    exact hf (hB hx'B) (hA hxA) hfx ▸ hx'B
  · intro hxB
    have : f x ∈ A.image f := hEq.symm ▸ Finset.mem_image_of_mem f hxB
    rcases Finset.mem_image.mp this with ⟨x', hx'A, hfx⟩
    exact hf (hA hx'A) (hB hxB) hfx ▸ hx'A

theorem occStepOn_image (r : SingleRule) (U R N : Finset ℕ) (f : ℕ → ℕ)
    (hf : Set.InjOn f (↑(U ∪ R ∪ N))) :
    occStepOn r (U.image f) (R.image f) (N.image f) = occStepOn r U R N := by
  let X := U ∪ R ∪ N
  have hUX : U ⊆ X := Finset.subset_union_left.trans Finset.subset_union_left
  have hRX : R ⊆ X := Finset.subset_union_right.trans Finset.subset_union_left
  have hNX : N ⊆ X := Finset.subset_union_right
  have hXimg : U.image f ∪ R.image f ∪ N.image f = X.image f := by
    simp only [X, Finset.image_union]
  unfold occStepOn
  rw [hXimg]
  symm
  refine Finset.sum_bij (fun p _ => (p.1.image f, p.2.image f)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_firingsOn] at hp ⊢
    rcases hp with ⟨hT1, hT2, hK1, hK2, hex⟩
    have hKX : p.2 ⊆ X := hK1.trans Finset.sdiff_subset
    refine ⟨Finset.image_subset_image hT1, ?_, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn (hf.mono hT1), hT2]
    · rw [← image_sdiff_of_injOn hf (Finset.Subset.refl X) hT1]
      exact Finset.image_subset_image hK1
    · rw [Finset.card_image_of_injOn (hf.mono hKX), hK2]
    · intro he
      rw [← Finset.image_union, hex he]
  · intro p₁ hp₁ p₂ hp₂ hEq
    rw [mem_firingsOn] at hp₁ hp₂
    simp only [Prod.mk.injEq] at hEq
    ext1
    · exact eq_of_image_eq_of_injOn hf hp₁.1 hp₂.1 hEq.1
    · exact eq_of_image_eq_of_injOn hf (hp₁.2.2.1.trans Finset.sdiff_subset)
        (hp₂.2.2.1.trans Finset.sdiff_subset) hEq.2
  · intro q hq
    rw [mem_firingsOn] at hq
    rcases hq with ⟨hT'1, hT'2, hK'1, hK'2, hex'⟩
    let T := X.filter fun x => f x ∈ q.1
    let K := X.filter fun x => f x ∈ q.2
    have hTX : T ⊆ X := Finset.filter_subset _ X
    have hKX : K ⊆ X := Finset.filter_subset _ X
    have hTimg : T.image f = q.1 := by
      ext y
      simp only [T, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hfx⟩, rfl⟩; exact hfx
      · intro hy
        rcases Finset.mem_image.mp (hT'1 hy) with ⟨x, hxX, rfl⟩
        exact ⟨x, ⟨hxX, hy⟩, rfl⟩
    have hKimg : K.image f = q.2 := by
      ext y
      simp only [K, Finset.mem_image, Finset.mem_filter]
      constructor
      · rintro ⟨x, ⟨_, hfx⟩, rfl⟩; exact hfx
      · intro hy
        have hyX : y ∈ X.image f := (hK'1.trans Finset.sdiff_subset) hy
        rcases Finset.mem_image.mp hyX with ⟨x, hxX, rfl⟩
        exact ⟨x, ⟨hxX, hy⟩, rfl⟩
    refine ⟨(T, K), ?_, Prod.ext hTimg hKimg⟩
    rw [mem_firingsOn]
    refine ⟨hTX, ?_, ?_, ?_, ?_⟩
    · rw [← Finset.card_image_of_injOn (hf.mono hTX), hTimg, hT'2]
    · intro x hxK
      rw [Finset.mem_sdiff]
      refine ⟨hKX hxK, fun hxT => ?_⟩
      have h1 : f x ∈ q.2 := (Finset.mem_filter.mp hxK).2
      have h2 : f x ∈ q.1 := (Finset.mem_filter.mp hxT).2
      exact (Finset.mem_sdiff.mp (hK'1 h1)).2 h2
    · rw [← Finset.card_image_of_injOn (hf.mono hKX), hKimg, hK'2]
    · intro he
      apply eq_of_image_eq_of_injOn hf (Finset.union_subset hTX hKX) (Finset.Subset.refl X)
      rw [Finset.image_union, hTimg, hKimg, hex' he]
  · intro p hp
    rw [mem_firingsOn] at hp
    rcases hp with ⟨hT1, _, hK1, _, _⟩
    have hKX : p.2 ⊆ X := hK1.trans Finset.sdiff_subset
    have hTKX : p.1 ∪ p.2 ⊆ X := Finset.union_subset hT1 hKX
    congr 1
    simp only [outCount, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · have hsub : U \ (p.1 ∪ p.2) ⊆ X := Finset.sdiff_subset.trans hUX
      rw [← Finset.card_image_of_injOn (hf.mono hsub),
        image_sdiff_of_injOn hf hUX hTKX, Finset.image_union]
    · have hsub : (R \ p.1) ∪ (U ∩ p.2) ⊆ X :=
        Finset.union_subset (Finset.sdiff_subset.trans hRX) (Finset.inter_subset_left.trans hUX)
      rw [← Finset.card_image_of_injOn (hf.mono hsub), Finset.image_union,
        image_sdiff_of_injOn hf hRX hT1, image_inter_of_injOn hf hUX hKX]
    · have hsub : N \ p.1 ⊆ X := Finset.sdiff_subset.trans hNX
      rw [← Finset.card_image_of_injOn (hf.mono hsub), image_sdiff_of_injOn hf hNX hT1]

/-- `occStepOn r U R N` depends on pairwise-disjoint `(U, R, N)` only through their cardinalities. -/
theorem occStepOn_eq_occRule1 (r : SingleRule) (U R N : Finset ℕ)
    (hUR : Disjoint U R) (hUN : Disjoint U N) (hRN : Disjoint R N) :
    occStepOn r U R N = occRule1 r (U.card, R.card, N.card) := by
  let u := U.card
  let rc := R.card
  let n := N.card
  let eU := U.orderIsoOfFin rfl
  let eR := R.orderIsoOfFin rfl
  let eN := N.orderIsoOfFin rfl
  let f : ℕ → ℕ := fun i =>
    if hi : i < u then (eU ⟨i, hi⟩ : ℕ)
    else if hr : i < u + rc then (eR ⟨i - u, by omega⟩ : ℕ)
    else if hn : i < u + rc + n then (eN ⟨i - (u + rc), by omega⟩ : ℕ)
    else 0
  have hfU : ∀ {i : ℕ} (hi : i < u), f i ∈ U := fun hi => by simp [f, hi, (eU ⟨_, hi⟩).2]
  have hfR : ∀ {i : ℕ} (h1 : ¬ i < u) (h2 : i < u + rc), f i ∈ R := fun h1 h2 => by
    simp [f, h1, h2, (eR ⟨_, _⟩).2]
  have hfN : ∀ {i : ℕ} (h1 : ¬ i < u) (h2 : ¬ i < u + rc) (h3 : i < u + rc + n), f i ∈ N :=
    fun h1 h2 h3 => by simp [f, h1, h2, h3, (eN ⟨_, _⟩).2]
  have hinj : Set.InjOn f (↑(canonU u ∪ canonR u rc ∪ canonN u rc n)) := by
    rw [canon_union]
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_Ico] at hi hj
    by_cases hi1 : i < u
    · by_cases hj1 : j < u
      · simp only [f, hi1, hj1, ↓reduceDIte] at hij
        have := eU.injective (Subtype.ext hij)
        simpa [Fin.ext_iff] using this
      · by_cases hj2 : j < u + rc
        · exfalso
          exact Finset.disjoint_left.mp hUR (hfU hi1) (hij ▸ hfR hj1 hj2)
        · exfalso
          exact Finset.disjoint_left.mp hUN (hfU hi1) (hij ▸ hfN hj1 hj2 hj.2)
    · by_cases hi2 : i < u + rc
      · by_cases hj1 : j < u
        · exfalso
          exact Finset.disjoint_left.mp hUR (hij.symm ▸ hfU hj1) (hfR hi1 hi2)
        · by_cases hj2 : j < u + rc
          · simp only [f, hi1, hi2, hj1, hj2, ↓reduceDIte] at hij
            have := eR.injective (Subtype.ext hij)
            simp only [Fin.ext_iff] at this
            omega
          · exfalso
            exact Finset.disjoint_left.mp hRN (hfR hi1 hi2) (hij ▸ hfN hj1 hj2 hj.2)
      · by_cases hj1 : j < u
        · exfalso
          exact Finset.disjoint_left.mp hUN (hij.symm ▸ hfU hj1) (hfN hi1 hi2 hi.2)
        · by_cases hj2 : j < u + rc
          · exfalso
            exact Finset.disjoint_left.mp hRN (hij.symm ▸ hfR hj1 hj2) (hfN hi1 hi2 hi.2)
          · simp only [f, hi1, hi2, hi.2, hj1, hj2, hj.2, ↓reduceDIte] at hij
            have := eN.injective (Subtype.ext hij)
            simp only [Fin.ext_iff] at this
            omega
  have himgU : (canonU u).image f = U := by
    ext x
    simp only [canonU, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨_, hi⟩, rfl⟩; exact hfU hi
    · intro hx
      let k := eU.symm ⟨x, hx⟩
      refine ⟨k.1, ⟨Nat.zero_le _, k.2⟩, ?_⟩
      dsimp only [f]
      rw [dif_pos k.2]
      exact congrArg Subtype.val (eU.apply_symm_apply ⟨x, hx⟩)
  have himgR : (canonR u rc).image f = R := by
    ext x
    simp only [canonR, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      exact hfR (by omega) hi2
    · intro hx
      let k := eR.symm ⟨x, hx⟩
      refine ⟨u + k.1, ⟨by omega, by omega⟩, ?_⟩
      have h1 : ¬ u + k.1 < u := by omega
      have h2 : u + k.1 < u + rc := by omega
      dsimp only [f]
      rw [dif_neg h1, dif_pos h2]
      have hsub : (⟨u + k.1 - u, by omega⟩ : Fin rc) = k := by ext; simp
      rw [hsub]
      exact congrArg Subtype.val (eR.apply_symm_apply ⟨x, hx⟩)
  have himgN : (canonN u rc n).image f = N := by
    ext x
    simp only [canonN, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      exact hfN (by omega) (by omega) hi2
    · intro hx
      let k := eN.symm ⟨x, hx⟩
      refine ⟨u + rc + k.1, ⟨by omega, by omega⟩, ?_⟩
      have h1 : ¬ u + rc + k.1 < u := by omega
      have h2 : ¬ u + rc + k.1 < u + rc := by omega
      have h3 : u + rc + k.1 < u + rc + n := by omega
      dsimp only [f]
      rw [dif_neg h1, dif_neg h2, dif_pos h3]
      have hsub : (⟨u + rc + k.1 - (u + rc), by omega⟩ : Fin n) = k := by ext; simp
      rw [hsub]
      exact congrArg Subtype.val (eN.apply_symm_apply ⟨x, hx⟩)
  unfold occRule1
  dsimp only
  rw [← occStepOn_image r (canonU u) (canonR u rc) (canonN u rc n) f hinj,
    himgU, himgR, himgN]

/-! ### Intertwining with `rho1` and faithfulness (`occRho1_injective`) -/

theorem forgetColors_occRule1 (r : SingleRule) (c : OccCount) :
    forgetColors (occRule1 r c) = rhoRule1 r (c.1 + c.2.1 + c.2.2) := by
  rcases c with ⟨u, rc, n⟩
  unfold occRule1 occStepOn rhoRule1
  dsimp only
  let U := canonU u
  let R := canonR u rc
  let N := canonN u rc n
  let X := U ∪ R ∪ N
  have hXcard : X.card = u + rc + n := by
    change (canonU u ∪ canonR u rc ∪ canonN u rc n).card = _
    rw [canon_union]
    simp
  rw [map_sum]
  have hterm : ∀ p ∈ firingsOn r X,
      forgetColors (Finsupp.single (outCount r U R N p.1 p.2) 1) =
        Finsupp.single (u + rc + n - r.take + r.make) 1 := by
    intro p hp
    rw [mem_firingsOn] at hp
    rcases hp with ⟨hT1, hT2, hK1, _, _⟩
    rw [forgetColors_single]
    congr 1
    dsimp only [outCount]
    rcases canon_disjoint u rc n with ⟨hUR, hUN, hRN⟩
    have h12 : Disjoint (U \ (p.1 ∪ p.2)) ((R \ p.1) ∪ (U ∩ p.2)) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx1 hx2
      rcases hx2 with ⟨hxR, _⟩ | ⟨_, hxK⟩
      · exact Finset.disjoint_left.mp hUR hx1.1 hxR
      · exact hx1.2 (Or.inr hxK)
    have h13 : Disjoint (U \ (p.1 ∪ p.2)) (N \ p.1) :=
      hUN.mono Finset.sdiff_subset Finset.sdiff_subset
    have h23 : Disjoint ((R \ p.1) ∪ (U ∩ p.2)) (N \ p.1) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx1 hx2
      rcases hx1 with ⟨hxR, _⟩ | ⟨hxU, _⟩
      · exact Finset.disjoint_left.mp hRN hxR hx2.1
      · exact Finset.disjoint_left.mp hUN hxU hx2.1
    have hunion : (U \ (p.1 ∪ p.2)) ∪ ((R \ p.1) ∪ (U ∩ p.2)) ∪ (N \ p.1) = X \ p.1 := by
      ext x
      have hKT : x ∈ p.2 → x ∉ p.1 := fun hxK => (Finset.mem_sdiff.mp (hK1 hxK)).2
      simp only [X, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    have hcards : (U \ (p.1 ∪ p.2)).card + ((R \ p.1) ∪ (U ∩ p.2)).card + (N \ p.1).card =
        (X \ p.1).card := by
      rw [← Finset.card_union_of_disjoint h12,
        ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨h13, h23⟩), hunion]
    have hXsdiff : (X \ p.1).card = u + rc + n - r.take := by
      rw [Finset.card_sdiff_of_subset hT1, hXcard, hT2]
    omega
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_firingsOn, hXcard, nat_smul_single_one]

/-- Color-forgetting intertwines the 3-color representation `occRho1` with `rho1`. -/
theorem forgetColors_occRho1 (A : SingleRule →₀ ℕ) :
    forgetColors.comp (occRho1 A) = (rho1 A).comp forgetColors := by
  apply Finsupp.lhom_ext'
  intro c
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r coeff => ?_)
  · rw [occRho1_add, rho1_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hx, hy]
  · rw [← nat_smul_single_one coeff r, occRho1_smul, rho1_smul, LinearMap.smul_apply,
      LinearMap.smul_apply, map_smul, occRho1_single_apply, forgetColors_single,
      rho1_single_apply, forgetColors_occRule1]

/-- Explicit closed form of `occRule1` on purely untouched initial tokens `(n, 0, 0)`. -/
theorem occRule1_untouched (r : SingleRule) (n : ℕ) :
    occRule1 r (n, 0, 0) =
      Finsupp.single (n - (r.take + r.keep), r.keep, r.make) (r.matchesCount n) := by
  unfold occRule1 occStepOn
  dsimp only
  have hR : canonR n 0 = ∅ := by simp [canonR]
  have hN : canonN n 0 0 = ∅ := by simp [canonN]
  rw [hR, hN, Finset.union_empty, Finset.union_empty]
  have hterm : ∀ p ∈ firingsOn r (canonU n),
      Finsupp.single (outCount r (canonU n) ∅ ∅ p.1 p.2) 1 =
        Finsupp.single (n - (r.take + r.keep), r.keep, r.make) 1 := by
    intro p hp
    rw [mem_firingsOn] at hp
    rcases hp with ⟨hT1, hT2, hK1, hK2, _⟩
    congr 1
    simp only [outCount, Finset.empty_sdiff, Finset.empty_union, Finset.card_empty, Nat.zero_add,
      Prod.mk.injEq, and_true]
    have hdisj : Disjoint p.1 p.2 := disjoint_sdiff_self_right.mono_right hK1
    have hKU : p.2 ⊆ canonU n := hK1.trans Finset.sdiff_subset
    have hTU : p.1 ∪ p.2 ⊆ canonU n := Finset.union_subset hT1 hKU
    refine ⟨?_, ?_⟩
    · rw [Finset.card_sdiff_of_subset hTU, card_canonU, Finset.card_union_of_disjoint hdisj,
        hT2, hK2]
    · rw [Finset.inter_eq_right.mpr hKU, hK2]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, card_firingsOn, card_canonU,
    nat_smul_single_one]

/-- **Faithfulness of `occRho1`**: two formal combinations of `SingleRule`s induce the
same linear operator on 3-color occurrence counts if and only if they are identical. -/
theorem occRho1_injective : Function.Injective occRho1 := by
  intro A B hAB
  ext ⟨t, k, m, e⟩
  have eval_at : ∀ (n u_out : ℕ),
      (occRho1 A (Finsupp.single (n, 0, 0) 1)) (u_out, k, m) =
        (occRho1 B (Finsupp.single (n, 0, 0) 1)) (u_out, k, m) := by
    intro n u_out
    exact congrArg (fun f => (f (Finsupp.single (n, 0, 0) 1)) (u_out, k, m)) hAB
  -- Helper evaluating `(occRho1 X |(t + k + d, 0, 0)⟩) (d, k, m)` for `d ∈ {0, 1}`.
  have coeff_formula : ∀ (X : SingleRule →₀ ℕ) (d : ℕ),
      (occRho1 X (Finsupp.single (t + k + d, 0, 0) 1)) (d, k, m) =
        X ⟨t, k, m, false⟩ * (SingleRule.matchesCount ⟨t, k, m, false⟩ (t + k + d)) +
        X ⟨t, k, m, true⟩ * (SingleRule.matchesCount ⟨t, k, m, true⟩ (t + k + d)) := by
    intro X d
    rw [occRho1_apply_single, Finsupp.sum_apply]
    unfold Finsupp.sum
    have hterm : ∀ r ∈ X.support,
        (X r • occRule1 r (t + k + d, 0, 0)) (d, k, m) =
          if r = ⟨t, k, m, false⟩ ∨ r = ⟨t, k, m, true⟩
          then X r * r.matchesCount (t + k + d)
          else 0 := by
      intro r _
      rw [occRule1_untouched, Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply]
      rcases r with ⟨t', k', m', e'⟩
      by_cases hmatch : (t + k + d - (t' + k'), k', m') = (d, k, m)
      · rw [if_pos hmatch]
        rcases Prod.mk.inj hmatch with ⟨hu, hk_eq⟩
        rcases Prod.mk.inj hk_eq with ⟨hk', hm'⟩
        subst k'; subst m'
        by_cases hle : t' + k ≤ t + k + d
        · have ht : t' = t := by omega
          subst ht
          cases e' <;> simp
        · have hzero : SingleRule.matchesCount ⟨t', k, m, e'⟩ (t + k + d) = 0 :=
            SingleRule.matchesCount_eq_zero_of_lt _ (by dsimp only; omega)
          rw [hzero, Nat.mul_zero, ite_self]
      · rw [if_neg hmatch, Nat.mul_zero]
        have hne : ¬ (SingleRule.mk t' k' m' e' = ⟨t, k, m, false⟩ ∨
            SingleRule.mk t' k' m' e' = ⟨t, k, m, true⟩) := by
          rintro (h | h)
          · rcases SingleRule.mk.inj h with ⟨ht', hk', hm', _⟩
            subst ht'; subst hk'; subst hm'
            exact hmatch (Prod.ext (by omega) rfl)
          · rcases SingleRule.mk.inj h with ⟨ht', hk', hm', _⟩
            subst ht'; subst hk'; subst hm'
            exact hmatch (Prod.ext (by omega) rfl)
        rw [if_neg hne]
    rw [Finset.sum_congr rfl hterm]
    let pair : Finset SingleRule := {⟨t, k, m, false⟩, ⟨t, k, m, true⟩}
    have hsum_pair :
        (∑ r ∈ X.support, if r = ⟨t, k, m, false⟩ ∨ r = ⟨t, k, m, true⟩
          then X r * r.matchesCount (t + k + d) else 0) =
        ∑ r ∈ pair, X r * r.matchesCount (t + k + d) := by
      rw [← Finset.sum_filter]
      refine Finset.sum_subset ?_ ?_
      · intro r hr
        rw [Finset.mem_filter] at hr
        rw [ Finset.mem_insert, Finset.mem_singleton ]
        exact hr.2
      · intro r hr hnot
        rw [Finset.mem_filter, Finsupp.mem_support_iff] at hnot
        have hpair : r = ⟨t, k, m, false⟩ ∨ r = ⟨t, k, m, true⟩ := by
          simpa [pair, Finset.mem_insert, Finset.mem_singleton] using hr
        by_cases hX0 : X r = 0
        · simp [hX0]
        · exact False.elim (hnot ⟨hX0, hpair⟩)
    have hne_pair : (⟨t, k, m, false⟩ : SingleRule) ≠ ⟨t, k, m, true⟩ := by
      intro h
      cases (SingleRule.mk.inj h).2.2.2
    rw [hsum_pair, Finset.sum_pair hne_pair]
  -- Step 1: `d = 1` isolates `exhaust = false`.
  have hd1 := eval_at (t + k + 1) 1
  rw [coeff_formula A 1, coeff_formula B 1] at hd1
  have htrue1 : SingleRule.matchesCount ⟨t, k, m, true⟩ (t + k + 1) = 0 := by
    simp [SingleRule.matchesCount]
  have hfalse1_pos : 0 < SingleRule.matchesCount ⟨t, k, m, false⟩ (t + k + 1) := by
    simp only [SingleRule.matchesCount, Bool.false_and]
    exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
  rw [htrue1, Nat.mul_zero, Nat.add_zero, Nat.mul_zero, Nat.add_zero] at hd1
  have hAfalse : A ⟨t, k, m, false⟩ = B ⟨t, k, m, false⟩ :=
    Nat.eq_of_mul_eq_mul_right hfalse1_pos hd1
  -- Step 2: `d = 0` recovers `exhaust = true`.
  cases e
  · exact hAfalse
  · have hd0 := eval_at (t + k + 0) 0
    rw [coeff_formula A 0, coeff_formula B 0, hAfalse] at hd0
    have htrue0_pos : 0 < SingleRule.matchesCount ⟨t, k, m, true⟩ (t + k + 0) := by
      simp only [SingleRule.matchesCount, Nat.add_zero, ne_eq, not_true_eq_false, decide_false,
        Bool.and_false]
      exact Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega))
    have hmul : A ⟨t, k, m, true⟩ * SingleRule.matchesCount ⟨t, k, m, true⟩ (t + k + 0) =
        B ⟨t, k, m, true⟩ * SingleRule.matchesCount ⟨t, k, m, true⟩ (t + k + 0) :=
      Nat.add_left_cancel hd0
    exact Nat.eq_of_mul_eq_mul_right htrue0_pos hmul

/-! ## Homomorphism theorem `occRho1 (compose1 r₂ r₁) = (occRho1 r₂) ∘ₗ (occRho1 r₁)` -/

/-- Witness data partitioning a composite firing `(T_old, K_old)` and fresh minted set `M₁`
into sequential firings `(T₁, K₁)` and `(T₂, K₂)`. -/
structure FiberWitness where
  uNew : Finset ℕ
  wNew : Finset ℕ
  t1Sub : Finset ℕ
  vSub : Finset ℕ
  k1Surv : Finset ℕ
  zSub : Finset ℕ
  deriving DecidableEq

/-- Finite set of fiber witnesses for overlap `ov`, fresh minted set `M₁`, and `(T_old, K_old)`. -/
def fiberWitnesses (r₁ : SingleRule) (ov : Overlap1) (M₁ T_old K_old : Finset ℕ) :
    Finset FiberWitness :=
  ((((((M₁.powersetCard ov.u).sigma fun uNew => (M₁ \ uNew).powersetCard ov.w).sigma
      fun _ => T_old.powersetCard r₁.take).sigma
      fun p => (T_old \ p.2).powersetCard ov.v).sigma
      fun _ => K_old.powersetCard (r₁.keep - ov.v)).sigma
      fun p => p.2.powersetCard ov.z).map
    ⟨fun s => ⟨s.1.1.1.1.1, s.1.1.1.1.2, s.1.1.1.2, s.1.1.2, s.1.2, s.2⟩, by
      intro a b h
      rcases a with ⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩
      rcases b with ⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩
      simp only [FiberWitness.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl⟩

theorem mem_fiberWitnesses {r₁ : SingleRule} {ov : Overlap1} {M₁ T_old K_old : Finset ℕ}
    {w : FiberWitness} :
    w ∈ fiberWitnesses r₁ ov M₁ T_old K_old ↔
      (w.uNew ⊆ M₁ ∧ w.uNew.card = ov.u) ∧
      (w.wNew ⊆ M₁ \ w.uNew ∧ w.wNew.card = ov.w) ∧
      (w.t1Sub ⊆ T_old ∧ w.t1Sub.card = r₁.take) ∧
      (w.vSub ⊆ T_old \ w.t1Sub ∧ w.vSub.card = ov.v) ∧
      (w.k1Surv ⊆ K_old ∧ w.k1Surv.card = r₁.keep - ov.v) ∧
      (w.zSub ⊆ w.k1Surv ∧ w.zSub.card = ov.z) := by
  rcases w with ⟨uNew, wNew, t1Sub, vSub, k1Surv, zSub⟩
  simp only [fiberWitnesses, Finset.mem_map, Finset.mem_sigma, Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, hmem, hEq⟩
    rcases FiberWitness.mk.inj hEq with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    tauto
  · intro h
    refine ⟨⟨⟨⟨⟨⟨uNew, wNew⟩, t1Sub⟩, vSub⟩, k1Surv⟩, zSub⟩, ?_, rfl⟩
    tauto

theorem card_fiberWitnesses (r₂ r₁ : SingleRule) (ov : Overlap1) (M₁ T_old K_old : Finset ℕ)
    (hM₁ : M₁.card = r₁.make)
    (hT : T_old.card = (Overlap1.composedRule r₂ r₁ ov).take)
    (hK : K_old.card = (Overlap1.composedRule r₂ r₁ ov).keep) :
    (fiberWitnesses r₁ ov M₁ T_old K_old).card = Overlap1.mult r₂ r₁ ov := by
  unfold fiberWitnesses Overlap1.mult
  dsimp only [Overlap1.composedRule] at hT hK
  rw [Finset.card_map]
  have step6 : ∀ x ∈ ((((M₁.powersetCard ov.u).sigma fun uNew => (M₁ \ uNew).powersetCard ov.w).sigma
      fun _ => T_old.powersetCard r₁.take).sigma
      fun p => (T_old \ p.2).powersetCard ov.v).sigma
      fun _ => K_old.powersetCard (r₁.keep - ov.v),
      (x.2.powersetCard ov.z).card = (r₁.keep - ov.v).choose ov.z := by
    intro x hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hx
    rw [Finset.card_powersetCard, hx.2.2]
  rw [Finset.card_sigma, Finset.sum_congr rfl step6, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_sigma, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, hK]
  have step4 : ∀ x ∈ (((M₁.powersetCard ov.u).sigma fun uNew => (M₁ \ uNew).powersetCard ov.w).sigma
      fun _ => T_old.powersetCard r₁.take),
      ((T_old \ x.2).powersetCard ov.v).card = (r₂.take - ov.u).choose ov.v := by
    intro x hx
    simp only [Finset.mem_sigma, Finset.mem_powersetCard] at hx
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hx.2.1, hT, hx.2.2,
      Nat.add_sub_cancel_left]
  rw [Finset.card_sigma, Finset.sum_congr rfl step4, Finset.sum_const, smul_eq_mul]
  rw [Finset.card_sigma, Finset.sum_const, smul_eq_mul, Finset.card_powersetCard, hT]
  have step2 : ∀ uNew ∈ M₁.powersetCard ov.u,
      ((M₁ \ uNew).powersetCard ov.w).card = (r₁.make - ov.u).choose ov.w := by
    intro uNew hu
    rw [Finset.mem_powersetCard] at hu
    rw [Finset.card_powersetCard, Finset.card_sdiff_of_subset hu.1, hM₁, hu.2]
  rw [Finset.card_sigma, Finset.sum_congr rfl step2, Finset.sum_const, smul_eq_mul,
    Finset.card_powersetCard, hM₁]

set_option maxHeartbeats 800000 in
/-- Key concrete representation identity: `occRho1` sends `compose1 r₂ r₁` to
`(occRho1 r₂) ∘ (occRho1 r₁)` on every 3-color count state. -/
theorem occRho1_compose1_apply (r₂ r₁ : SingleRule) (c : OccCount) :
    occRho1 (compose1 r₂ r₁) (Finsupp.single c 1) =
      occRho1 (Finsupp.single r₂ 1) (occRho1 (Finsupp.single r₁ 1) (Finsupp.single c 1)) := by
  rcases c with ⟨u₀, r₀, n₀⟩
  let U₀ := canonU u₀
  let R₀ := canonR u₀ r₀
  let N₀ := canonN u₀ r₀ n₀
  let X₀ := U₀ ∪ R₀ ∪ N₀
  let M₁ := Finset.Ico (u₀ + r₀ + n₀) (u₀ + r₀ + n₀ + r₁.make)
  have hM₁_card : M₁.card = r₁.make := by simp [M₁]
  have hXM₁ : Disjoint X₀ M₁ := by
    have hX : X₀ = Finset.Ico 0 (u₀ + r₀ + n₀) := canon_union u₀ r₀ n₀
    rw [hX, Finset.disjoint_left]
    intro x hx1 hx2
    simp only [M₁, Finset.mem_Ico] at hx1 hx2
    omega
  rcases canon_disjoint u₀ r₀ n₀ with ⟨hUR₀, hUN₀, hRN₀⟩
  -- Step 1: Expand RHS into a concrete sum over sequential firing pairs `⟨p₁, p₂⟩`.
  rw [occRho1_single_apply]
  change _ = occRho1 (Finsupp.single r₂ 1) (occStepOn r₁ U₀ R₀ N₀)
  unfold occStepOn
  rw [map_sum]
  have hrhs_step : ∀ p₁ ∈ firingsOn r₁ X₀,
      occRho1 (Finsupp.single r₂ 1) (Finsupp.single (outCount r₁ U₀ R₀ N₀ p₁.1 p₁.2) 1) =
        ∑ p₂ ∈ firingsOn r₂ ((X₀ \ p₁.1) ∪ M₁),
          Finsupp.single (outCount r₂ (U₀ \ (p₁.1 ∪ p₁.2)) ((R₀ \ p₁.1) ∪ (U₀ ∩ p₁.2))
            ((N₀ \ p₁.1) ∪ M₁) p₂.1 p₂.2) 1 := by
    intro p₁ hp₁
    rw [mem_firingsOn] at hp₁
    rcases hp₁ with ⟨hT₁X, _, hK₁X, _, _⟩
    rw [occRho1_single_apply]
    let U₁ := U₀ \ (p₁.1 ∪ p₁.2)
    let R₁ := (R₀ \ p₁.1) ∪ (U₀ ∩ p₁.2)
    let N₁ := (N₀ \ p₁.1) ∪ M₁
    have hUM₁ : Disjoint U₀ M₁ :=
      hXM₁.mono_left (Finset.subset_union_left.trans Finset.subset_union_left)
    have hRM₁ : Disjoint R₀ M₁ :=
      hXM₁.mono_left (Finset.subset_union_right.trans Finset.subset_union_left)
    have hNM₁ : Disjoint N₀ M₁ := hXM₁.mono_left Finset.subset_union_right
    have hU₁R₁ : Disjoint U₁ R₁ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [U₁, R₁, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx1 hx2
      rcases hx2 with ⟨hxR, _⟩ | ⟨_, hxK⟩
      · exact Finset.disjoint_left.mp hUR₀ hx1.1 hxR
      · exact hx1.2 (Or.inr hxK)
    have hU₁N₁ : Disjoint U₁ N₁ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [U₁, N₁, Finset.mem_sdiff, Finset.mem_union] at hx1 hx2
      rcases hx2 with ⟨hxN, _⟩ | hxM
      · exact Finset.disjoint_left.mp hUN₀ hx1.1 hxN
      · exact Finset.disjoint_left.mp hUM₁ hx1.1 hxM
    have hR₁N₁ : Disjoint R₁ N₁ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [R₁, N₁, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter] at hx1 hx2
      rcases hx1 with ⟨hxR, _⟩ | ⟨hxU, _⟩ <;> rcases hx2 with ⟨hxN, _⟩ | hxM
      · exact Finset.disjoint_left.mp hRN₀ hxR hxN
      · exact Finset.disjoint_left.mp hRM₁ hxR hxM
      · exact Finset.disjoint_left.mp hUN₀ hxU hxN
      · exact Finset.disjoint_left.mp hUM₁ hxU hxM
    have hN₁_card : N₁.card = (N₀ \ p₁.1).card + r₁.make := by
      rw [Finset.card_union_of_disjoint (hNM₁.mono_left Finset.sdiff_subset), hM₁_card]
    have hout_eq : outCount r₁ U₀ R₀ N₀ p₁.1 p₁.2 = (U₁.card, R₁.card, N₁.card) := by
      simp only [outCount, U₁, R₁, hN₁_card]
    rw [hout_eq, ← occStepOn_eq_occRule1 r₂ U₁ R₁ N₁ hU₁R₁ hU₁N₁ hR₁N₁]
    unfold occStepOn
    have hunion1 : U₁ ∪ R₁ ∪ N₁ = (X₀ \ p₁.1) ∪ M₁ := by
      ext x
      have hKT : x ∈ p₁.2 → x ∉ p₁.1 := fun hxK => (Finset.mem_sdiff.mp (hK₁X hxK)).2
      simp only [U₁, R₁, N₁, X₀, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    rw [hunion1]
  rw [Finset.sum_congr rfl hrhs_step]
  let seqSet := (firingsOn r₁ X₀).sigma fun p₁ => firingsOn r₂ ((X₀ \ p₁.1) ∪ M₁)
  have hseq_sigma :
      (∑ p₁ ∈ firingsOn r₁ X₀,
        ∑ p₂ ∈ firingsOn r₂ ((X₀ \ p₁.1) ∪ M₁),
          Finsupp.single (outCount r₂ (U₀ \ (p₁.1 ∪ p₁.2)) ((R₀ \ p₁.1) ∪ (U₀ ∩ p₁.2))
            ((N₀ \ p₁.1) ∪ M₁) p₂.1 p₂.2) 1) =
      ∑ s ∈ seqSet,
        Finsupp.single (outCount r₂ (U₀ \ (s.1.1 ∪ s.1.2)) ((R₀ \ s.1.1) ∪ (U₀ ∩ s.1.2))
          ((N₀ \ s.1.1) ∪ M₁) s.2.1 s.2.2) 1 :=
    (Finset.sum_sigma (firingsOn r₁ X₀) (fun p₁ => firingsOn r₂ ((X₀ \ p₁.1) ∪ M₁))
      (fun s => Finsupp.single (outCount r₂ (U₀ \ (s.1.1 ∪ s.1.2))
        ((R₀ \ s.1.1) ∪ (U₀ ∩ s.1.2)) ((N₀ \ s.1.1) ∪ M₁) s.2.1 s.2.2) 1)).symm
  rw [hseq_sigma]
  -- Step 2: Expand LHS into a concrete sum over `⟨⟨ov, p_old⟩, w⟩`.
  have hocc_sum : ∀ (S : Finset Overlap1) (g : Overlap1 → SingleRule →₀ ℕ),
      occRho1 (∑ ov ∈ S, g ov) (Finsupp.single (u₀, r₀, n₀) 1) =
        ∑ ov ∈ S, occRho1 (g ov) (Finsupp.single (u₀, r₀, n₀) 1) := by
    intro S g
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, occRho1_add, LinearMap.add_apply, ih, Finset.sum_insert ha]
  unfold compose1
  rw [hocc_sum]
  have hlhs_ov : ∀ ov ∈ Overlap1.candidates r₂ r₁,
      occRho1 (Finsupp.single (Overlap1.composedRule r₂ r₁ ov) (Overlap1.mult r₂ r₁ ov))
        (Finsupp.single (u₀, r₀, n₀) 1) =
        ∑ p_old ∈ firingsOn (Overlap1.composedRule r₂ r₁ ov) X₀,
          ∑ _w ∈ fiberWitnesses r₁ ov M₁ p_old.1 p_old.2,
            Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ ov) U₀ R₀ N₀ p_old.1 p_old.2) 1 := by
    intro ov _
    rw [← nat_smul_single_one (Overlap1.mult r₂ r₁ ov), occRho1_smul, LinearMap.smul_apply,
      occRho1_single_apply]
    change Overlap1.mult r₂ r₁ ov • occStepOn (Overlap1.composedRule r₂ r₁ ov) U₀ R₀ N₀ = _
    unfold occStepOn
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl ?_
    intro p_old hp_old
    rw [mem_firingsOn] at hp_old
    rw [Finset.sum_const,
      card_fiberWitnesses r₂ r₁ ov M₁ p_old.1 p_old.2 hM₁_card hp_old.2.1 hp_old.2.2.2.1]
  rw [Finset.sum_congr rfl hlhs_ov]
  let compMid := (Overlap1.candidates r₂ r₁).sigma fun ov =>
    firingsOn (Overlap1.composedRule r₂ r₁ ov) X₀
  let compSet := compMid.sigma fun q => fiberWitnesses r₁ q.1 M₁ q.2.1 q.2.2
  have hcomp_sigma1 :
      (∑ ov ∈ Overlap1.candidates r₂ r₁,
        ∑ p_old ∈ firingsOn (Overlap1.composedRule r₂ r₁ ov) X₀,
          ∑ _w ∈ fiberWitnesses r₁ ov M₁ p_old.1 p_old.2,
            Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ ov) U₀ R₀ N₀ p_old.1 p_old.2) 1) =
      ∑ q ∈ compMid,
        ∑ _w ∈ fiberWitnesses r₁ q.1 M₁ q.2.1 q.2.2,
          Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ q.1) U₀ R₀ N₀ q.2.1 q.2.2) 1 :=
    (Finset.sum_sigma (Overlap1.candidates r₂ r₁)
      (fun ov => firingsOn (Overlap1.composedRule r₂ r₁ ov) X₀)
      (fun q => ∑ _w ∈ fiberWitnesses r₁ q.1 M₁ q.2.1 q.2.2,
        Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ q.1) U₀ R₀ N₀ q.2.1 q.2.2) 1)).symm
  have hcomp_sigma2 :
      (∑ q ∈ compMid,
        ∑ _w ∈ fiberWitnesses r₁ q.1 M₁ q.2.1 q.2.2,
          Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ q.1) U₀ R₀ N₀ q.2.1 q.2.2) 1) =
      ∑ z ∈ compSet,
        Finsupp.single (outCount (Overlap1.composedRule r₂ r₁ z.1.1) U₀ R₀ N₀ z.1.2.1 z.1.2.2) 1 :=
    (Finset.sum_sigma compMid (fun q => fiberWitnesses r₁ q.1 M₁ q.2.1 q.2.2)
      (fun z => Finsupp.single
        (outCount (Overlap1.composedRule r₂ r₁ z.1.1) U₀ R₀ N₀ z.1.2.1 z.1.2.2) 1)).symm
  rw [hcomp_sigma1, hcomp_sigma2]
  symm
  clear hrhs_step hseq_sigma hocc_sum hlhs_ov hcomp_sigma1 hcomp_sigma2
  have hUM₁ : Disjoint U₀ M₁ :=
    hXM₁.mono_left (Finset.subset_union_left.trans Finset.subset_union_left)
  have hRM₁ : Disjoint R₀ M₁ :=
    hXM₁.mono_left (Finset.subset_union_right.trans Finset.subset_union_left)
  have hNM₁ : Disjoint N₀ M₁ := hXM₁.mono_left Finset.subset_union_right
  clear_value U₀ R₀ N₀ X₀ M₁
  -- Step 3: Explicit bijection `seqSet → compSet` via `Finset.sum_bij`.
  let fwd : ((_ : Finset ℕ × Finset ℕ) × (Finset ℕ × Finset ℕ)) →
      ((_ : (_ : Overlap1) × (Finset ℕ × Finset ℕ)) × FiberWitness) :=
    fun s =>
      let T₁ := s.1.1
      let K₁ := s.1.2
      let T₂ := s.2.1
      let K₂ := s.2.2
      let ov : Overlap1 := ⟨(T₂ ∩ M₁).card, (K₁ ∩ T₂).card, (K₂ ∩ M₁).card, (K₁ ∩ K₂).card⟩
      let T_old : Finset ℕ := T₁ ∪ (T₂ \ M₁)
      let K_old : Finset ℕ := (K₁ \ T₂) ∪ (K₂ \ M₁)
      let w : FiberWitness := ⟨T₂ ∩ M₁, K₂ ∩ M₁, T₁, K₁ ∩ T₂, K₁ \ T₂, K₁ ∩ K₂⟩
      ⟨⟨ov, (T_old, K_old)⟩, w⟩
  refine Finset.sum_bij (fun s _ => fwd s) ?_ ?_ ?_ ?_
  · -- `fwd` maps `seqSet` into `compSet`
    intro s hs
    rcases s with ⟨⟨T₁, K₁⟩, ⟨T₂, K₂⟩⟩
    simp only [seqSet, Finset.mem_sigma, mem_firingsOn] at hs
    simp only [compSet, compMid, fwd, Finset.mem_sigma, Overlap1.mem_candidates_iff, mem_firingsOn,
      mem_fiberWitnesses]
    clear seqSet compSet compMid fwd
    rcases hs with ⟨⟨hT₁X, hT₁c, hK₁X, hK₁c, hex₁⟩, ⟨hT₂X₁, hT₂c, hK₂X₁, hK₂c, hex₂⟩⟩
    have hK₁_sub : K₁ ⊆ X₀ := hK₁X.trans Finset.sdiff_subset
    have hK₁M₁ : Disjoint K₁ M₁ := hXM₁.mono_left hK₁_sub
    have hT₁M₁ : Disjoint T₁ M₁ := hXM₁.mono_left hT₁X
    have hT₂K₂ : Disjoint T₂ K₂ := disjoint_sdiff_self_right.mono_right hK₂X₁
    have hK₂_subX₁ : K₂ ⊆ (X₀ \ T₁) ∪ M₁ := hK₂X₁.trans Finset.sdiff_subset
    have hT₂_sdiff : T₂ \ M₁ ⊆ X₀ \ T₁ := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_union.mp (hT₂X₁ hx.1) with hx0 | hxM
      · exact hx0
      · exact False.elim (hx.2 hxM)
    have hK₂_sdiff : K₂ \ M₁ ⊆ X₀ \ T₁ := by
      intro x hx
      rw [Finset.mem_sdiff] at hx
      rcases Finset.mem_union.mp (hK₂_subX₁ hx.1) with hx0 | hxM
      · exact hx0
      · exact False.elim (hx.2 hxM)
    let ov : Overlap1 := ⟨(T₂ ∩ M₁).card, (K₁ ∩ T₂).card, (K₂ ∩ M₁).card, (K₁ ∩ K₂).card⟩
    have hov_valid : Overlap1.Valid r₂ r₁ ov := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · have hdisj : Disjoint (T₂ ∩ M₁) (K₂ ∩ M₁) :=
          hT₂K₂.mono Finset.inter_subset_left Finset.inter_subset_left
        have hsub : (T₂ ∩ M₁) ∪ (K₂ ∩ M₁) ⊆ M₁ :=
          Finset.union_subset Finset.inter_subset_right Finset.inter_subset_right
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, hM₁_card] at this
        exact this
      · have hdisj : Disjoint (K₁ ∩ T₂) (K₁ ∩ K₂) :=
          hT₂K₂.mono Finset.inter_subset_right Finset.inter_subset_right
        have hsub : (K₁ ∩ T₂) ∪ (K₁ ∩ K₂) ⊆ K₁ :=
          Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, hK₁c] at this
        exact this
      · have hdisj : Disjoint (T₂ ∩ M₁) (K₁ ∩ T₂) :=
          hK₁M₁.symm.mono Finset.inter_subset_right Finset.inter_subset_left
        have hsub : (T₂ ∩ M₁) ∪ (K₁ ∩ T₂) ⊆ T₂ :=
          Finset.union_subset Finset.inter_subset_left Finset.inter_subset_right
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, hT₂c] at this
        exact this
      · have hdisj : Disjoint (K₂ ∩ M₁) (K₁ ∩ K₂) :=
          hK₁M₁.symm.mono Finset.inter_subset_right Finset.inter_subset_left
        have hsub : (K₂ ∩ M₁) ∪ (K₁ ∩ K₂) ⊆ K₂ :=
          Finset.union_subset Finset.inter_subset_left Finset.inter_subset_right
        have := Finset.card_le_card hsub
        rw [Finset.card_union_of_disjoint hdisj, hK₂c] at this
        exact this
      · intro he1
        have hX₁_eq : (X₀ \ T₁) ∪ M₁ = K₁ ∪ M₁ := by
          ext x
          have hTK : T₁ ∪ K₁ = X₀ := hex₁ he1
          have hKT : x ∈ K₁ → x ∉ T₁ := fun hx => (Finset.mem_sdiff.mp (hK₁X hx)).2
          have : x ∈ X₀ ↔ x ∈ T₁ ∨ x ∈ K₁ := by
            rw [← Finset.mem_union, hTK]
          simp only [Finset.mem_union, Finset.mem_sdiff]
          tauto
        have hT₂_decomp : T₂ = (T₂ ∩ M₁) ∪ (K₁ ∩ T₂) := by
          ext x
          have hx1 := fun hx : x ∈ T₂ => hX₁_eq ▸ hT₂X₁ hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx1 ⊢
          tauto
        have hK₂_decomp : K₂ = (K₂ ∩ M₁) ∪ (K₁ ∩ K₂) := by
          ext x
          have hx1 := fun hx : x ∈ K₂ => hX₁_eq ▸ hK₂_subX₁ hx
          simp only [Finset.mem_union, Finset.mem_inter] at hx1 ⊢
          tauto
        have hdisjT : Disjoint (T₂ ∩ M₁) (K₁ ∩ T₂) :=
          hK₁M₁.symm.mono Finset.inter_subset_right Finset.inter_subset_left
        have hdisjK : Disjoint (K₂ ∩ M₁) (K₁ ∩ K₂) :=
          hK₁M₁.symm.mono Finset.inter_subset_right Finset.inter_subset_left
        refine ⟨?_, ?_⟩
        · rw [← hT₂c, hT₂_decomp, Finset.card_union_of_disjoint hdisjT]
        · rw [← hK₂c, hK₂_decomp, Finset.card_union_of_disjoint hdisjK]
      · intro he2
        have hTK₂ : T₂ ∪ K₂ = (X₀ \ T₁) ∪ M₁ := hex₂ he2
        have hM₁_decomp : M₁ = (T₂ ∩ M₁) ∪ (K₂ ∩ M₁) := by
          ext x
          have : x ∈ M₁ → x ∈ T₂ ∪ K₂ := fun hx => hTK₂.symm ▸ Finset.mem_union_right _ hx
          simp only [Finset.mem_union, Finset.mem_inter] at this ⊢
          tauto
        have hK₁_decomp : K₁ = (K₁ ∩ T₂) ∪ (K₁ ∩ K₂) := by
          ext x
          have : x ∈ K₁ → x ∈ T₂ ∪ K₂ := fun hx => hTK₂.symm ▸ Finset.mem_union_left _ (hK₁X hx)
          simp only [Finset.mem_union, Finset.mem_inter] at this ⊢
          tauto
        have hdisjM : Disjoint (T₂ ∩ M₁) (K₂ ∩ M₁) :=
          hT₂K₂.mono Finset.inter_subset_left Finset.inter_subset_left
        have hdisjK : Disjoint (K₁ ∩ T₂) (K₁ ∩ K₂) :=
          hT₂K₂.mono Finset.inter_subset_right Finset.inter_subset_right
        refine ⟨?_, ?_⟩
        · rw [← hM₁_card, hM₁_decomp, Finset.card_union_of_disjoint hdisjM]
        · rw [← hK₁c, hK₁_decomp, Finset.card_union_of_disjoint hdisjK]
    -- Now verify membership in `compSet`!
    let T_old := T₁ ∪ (T₂ \ M₁)
    let K_old := (K₁ \ T₂) ∪ (K₂ \ M₁)
    have hT₁_disj_T₂s : Disjoint T₁ (T₂ \ M₁) :=
      disjoint_sdiff_self_right.mono_right hT₂_sdiff
    have hT_old_card : T_old.card = r₁.take + (r₂.take - ov.u) := by
      rw [Finset.card_union_of_disjoint hT₁_disj_T₂s, hT₁c, Finset.card_sdiff, Finset.inter_comm,
        hT₂c]
    have hK_old_sub : K_old ⊆ X₀ \ T_old := by
      intro x hx
      simp only [K_old, T_old, Finset.mem_union, Finset.mem_sdiff] at hx ⊢
      rcases hx with ⟨hxK₁, hxT₂⟩ | ⟨hxK₂, hxM₁⟩
      · have hx0 := Finset.mem_sdiff.mp (hK₁X hxK₁)
        exact ⟨hx0.1, fun h => h.elim hx0.2 (fun h2 => hxT₂ h2.1)⟩
      · have hx0 := Finset.mem_sdiff.mp (hK₂_sdiff (Finset.mem_sdiff.mpr ⟨hxK₂, hxM₁⟩))
        have hxnotT₂ : x ∉ T₂ := Finset.disjoint_right.mp hT₂K₂ hxK₂
        exact ⟨hx0.1, fun h => h.elim hx0.2 (fun h2 => hxnotT₂ h2.1)⟩
    have hK_inter : (K₁ \ T₂) ∩ (K₂ \ M₁) = K₁ ∩ K₂ := by
      ext x
      have hxnotT₂ : x ∈ K₂ → x ∉ T₂ := fun hx => Finset.disjoint_right.mp hT₂K₂ hx
      have hxnotM₁ : x ∈ K₁ → x ∉ M₁ := fun hx => Finset.disjoint_left.mp hK₁M₁ hx
      simp only [Finset.mem_inter, Finset.mem_sdiff]
      tauto
    have hK_old_card : K_old.card = (r₁.keep - ov.v) + (r₂.keep - ov.w - ov.z) := by
      have hinc := Finset.card_union_add_card_inter (K₁ \ T₂) (K₂ \ M₁)
      rw [hK_inter] at hinc
      have hc1 : (K₁ \ T₂).card = r₁.keep - ov.v := by
        rw [Finset.card_sdiff, Finset.inter_comm, hK₁c]
      have hc2 : (K₂ \ M₁).card = r₂.keep - ov.w := by
        rw [Finset.card_sdiff, Finset.inter_comm, hK₂c]
      rw [hc1, hc2] at hinc
      have hwz : ov.w + ov.z ≤ r₂.keep := hov_valid.2.2.2.1
      have hvz : ov.v + ov.z ≤ r₁.keep := hov_valid.2.1
      change ((K₁ \ T₂) ∪ (K₂ \ M₁)).card = _
      dsimp only [ov] at hwz hvz hinc ⊢
      omega
    have hex_old : (r₁.exhaust || r₂.exhaust) = true → T_old ∪ K_old = X₀ := by
      intro hor
      apply Finset.Subset.antisymm
      · exact Finset.union_subset
          (Finset.union_subset hT₁X (hT₂_sdiff.trans Finset.sdiff_subset))
          (hK_old_sub.trans Finset.sdiff_subset)
      · intro x hx0
        simp only [Bool.or_eq_true] at hor
        rcases hor with he1 | he2
        · have hxTK₁ : x ∈ T₁ ∪ K₁ := (hex₁ he1).symm ▸ hx0
          have hxnotM₁ : x ∉ M₁ := Finset.disjoint_left.mp hXM₁ hx0
          simp only [T_old, K_old, Finset.mem_union, Finset.mem_sdiff] at hxTK₁ ⊢
          by_cases hxT₂ : x ∈ T₂ <;> tauto
        · by_cases hxT₁ : x ∈ T₁
          · exact Finset.mem_union_left _ (Finset.mem_union_left _ hxT₁)
          · have hxTK₂ : x ∈ T₂ ∪ K₂ :=
              (hex₂ he2).symm ▸ Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx0, hxT₁⟩)
            have hxnotM₁ : x ∉ M₁ := Finset.disjoint_left.mp hXM₁ hx0
            simp only [T_old, K_old, Finset.mem_union, Finset.mem_sdiff] at hxTK₂ ⊢
            tauto
    refine ⟨⟨hov_valid, ⟨Finset.union_subset hT₁X (hT₂_sdiff.trans Finset.sdiff_subset),
      hT_old_card, hK_old_sub, hK_old_card, hex_old⟩⟩, ?_⟩
    -- Fiber witness conditions:
    refine ⟨⟨Finset.inter_subset_right, trivial⟩, ⟨?_, trivial⟩,
      ⟨Finset.subset_union_left, hT₁c⟩, ⟨?_, trivial⟩,
      ⟨Finset.subset_union_left, by rw [Finset.card_sdiff, Finset.inter_comm, hK₁c]⟩,
      ⟨?_, trivial⟩⟩
    · intro x hx
      rw [Finset.mem_inter] at hx
      exact Finset.mem_sdiff.mpr
        ⟨hx.2, fun h => Finset.disjoint_right.mp hT₂K₂ hx.1 (Finset.mem_inter.mp h).1⟩
    · intro x hx
      rw [Finset.mem_inter] at hx
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ ?_, (Finset.mem_sdiff.mp (hK₁X hx.1)).2⟩
      exact Finset.mem_sdiff.mpr ⟨hx.2, Finset.disjoint_left.mp hK₁M₁ hx.1⟩
    · intro x hx
      rw [Finset.mem_inter] at hx
      exact Finset.mem_sdiff.mpr ⟨hx.1, Finset.disjoint_right.mp hT₂K₂ hx.2⟩
  · -- Injectivity of `fwd` on `seqSet`
    intro s₁ hs₁ s₂ hs₂ hEq
    rcases s₁ with ⟨⟨T₁, K₁⟩, ⟨T₂, K₂⟩⟩
    rcases s₂ with ⟨⟨T₁', K₁'⟩, ⟨T₂', K₂'⟩⟩
    simp only [seqSet, Finset.mem_sigma, mem_firingsOn] at hs₁ hs₂
    simp only [fwd, Sigma.mk.injEq, Prod.mk.injEq, FiberWitness.mk.injEq, heq_eq_eq] at hEq
    clear seqSet compSet compMid fwd
    rcases hEq with ⟨⟨_, hTold, hKold⟩, hUnew, hWnew, rfl, hV, hKsurv, hZ⟩
    have hK₁ : K₁ = K₁' := by
      rw [← Finset.sdiff_union_inter K₁ T₂, ← Finset.sdiff_union_inter K₁' T₂', hKsurv, hV]
    subst hK₁
    have hT₁_disj1 : Disjoint T₁ (T₂ \ M₁) := by
      rw [Finset.disjoint_left]
      intro x hxT₁ hxT₂
      rw [Finset.mem_sdiff] at hxT₂
      rcases Finset.mem_union.mp (hs₁.2.1 hxT₂.1) with hx0 | hxM
      · exact (Finset.mem_sdiff.mp hx0).2 hxT₁
      · exact hxT₂.2 hxM
    have hT₁_disj2 : Disjoint T₁ (T₂' \ M₁) := by
      rw [Finset.disjoint_left]
      intro x hxT₁ hxT₂
      rw [Finset.mem_sdiff] at hxT₂
      rcases Finset.mem_union.mp (hs₂.2.1 hxT₂.1) with hx0 | hxM
      · exact (Finset.mem_sdiff.mp hx0).2 hxT₁
      · exact hxT₂.2 hxM
    have hT₂_sdiff_eq : T₂ \ M₁ = T₂' \ M₁ := by
      have h1 : (T₁ ∪ (T₂ \ M₁)) \ T₁ = T₂ \ M₁ := by
        ext x
        have hd : x ∈ T₁ → x ∉ T₂ \ M₁ := fun hx => Finset.disjoint_left.mp hT₁_disj1 hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at hd ⊢
        tauto
      have h2 : (T₁ ∪ (T₂' \ M₁)) \ T₁ = T₂' \ M₁ := by
        ext x
        have hd : x ∈ T₁ → x ∉ T₂' \ M₁ := fun hx => Finset.disjoint_left.mp hT₁_disj2 hx
        simp only [Finset.mem_sdiff, Finset.mem_union] at hd ⊢
        tauto
      rw [← h1, hTold, h2]
    have hT₂ : T₂ = T₂' := by
      rw [← Finset.sdiff_union_inter T₂ M₁, ← Finset.sdiff_union_inter T₂' M₁, hT₂_sdiff_eq, hUnew]
    subst hT₂
    have hK₂_sdiff_eq : K₂ \ M₁ = K₂' \ M₁ := by
      ext x
      simp only [Finset.mem_sdiff]
      constructor
      · rintro ⟨hxK₂, hxnotM⟩
        refine ⟨?_, hxnotM⟩
        have hmem : x ∈ (K₁ \ T₂) ∪ (K₂' \ M₁) :=
          hKold ▸ Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxK₂, hxnotM⟩)
        rcases Finset.mem_union.mp hmem with hk1 | hk2
        · have hxk1 : x ∈ K₁ := (Finset.mem_sdiff.mp hk1).1
          exact (Finset.mem_inter.mp (hZ ▸ Finset.mem_inter.mpr ⟨hxk1, hxK₂⟩)).2
        · exact (Finset.mem_sdiff.mp hk2).1
      · rintro ⟨hxK₂', hxnotM⟩
        refine ⟨?_, hxnotM⟩
        have hmem : x ∈ (K₁ \ T₂) ∪ (K₂ \ M₁) :=
          hKold.symm ▸ Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxK₂', hxnotM⟩)
        rcases Finset.mem_union.mp hmem with hk1 | hk2
        · have hxk1 : x ∈ K₁ := (Finset.mem_sdiff.mp hk1).1
          exact (Finset.mem_inter.mp (hZ.symm ▸ Finset.mem_inter.mpr ⟨hxk1, hxK₂'⟩)).2
        · exact (Finset.mem_sdiff.mp hk2).1
    have hK₂ : K₂ = K₂' := by
      rw [← Finset.sdiff_union_inter K₂ M₁, ← Finset.sdiff_union_inter K₂' M₁, hK₂_sdiff_eq, hWnew]
    subst hK₂
    rfl
  · -- Surjectivity of `fwd` onto `compSet`
    intro b hb
    rcases b with ⟨⟨ov, ⟨T_old, K_old⟩⟩, ⟨uNew, wNew, t1Sub, vSub, k1Surv, zSub⟩⟩
    simp only [compSet, compMid, Finset.mem_sigma, Overlap1.mem_candidates_iff, mem_firingsOn,
      mem_fiberWitnesses] at hb
    clear compSet compMid
    rcases hb with ⟨⟨hov, ⟨hToldX, hToldc, hKoldX, hKoldc, hexOld⟩⟩,
      ⟨hu1, hu2⟩, ⟨hw1, hw2⟩, ⟨ht1, ht2⟩, ⟨hv1, hv2⟩, ⟨hks1, hks2⟩, ⟨hz1, hz2⟩⟩
    dsimp only [Overlap1.composedRule] at hToldc hKoldc hexOld
    rcases hov with ⟨hmk1, hkp1, htk2, hkp2, hex_ov1, hex_ov2⟩
    let T₁ := t1Sub
    let K₁ := k1Surv ∪ vSub
    let T₂ := (T_old \ t1Sub) ∪ uNew
    let K₂ := ((K_old \ k1Surv) ∪ zSub) ∪ wNew
    have hTK_disj : Disjoint T_old K_old := disjoint_sdiff_self_right.mono_right hKoldX
    have hToldM₁ : Disjoint T_old M₁ := hXM₁.mono_left hToldX
    have hKoldM₁ : Disjoint K_old M₁ := hXM₁.mono_left (hKoldX.trans Finset.sdiff_subset)
    have hks_v_disj : Disjoint k1Surv vSub :=
      hTK_disj.symm.mono hks1 (hv1.trans Finset.sdiff_subset)
    have hT₁X : T₁ ⊆ X₀ := ht1.trans hToldX
    have hK₁X : K₁ ⊆ X₀ \ T₁ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxk | hxv
      · have hx0 := Finset.mem_sdiff.mp (hKoldX (hks1 hxk))
        exact Finset.mem_sdiff.mpr ⟨hx0.1, fun h => hx0.2 (ht1 h)⟩
      · have hxt := Finset.mem_sdiff.mp (hv1 hxv)
        exact Finset.mem_sdiff.mpr ⟨hToldX hxt.1, hxt.2⟩
    have hK₁c : K₁.card = r₁.keep := by
      rw [Finset.card_union_of_disjoint hks_v_disj, hks2, hv2]
      omega
    have hT₂X₁ : T₂ ⊆ (X₀ \ T₁) ∪ M₁ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxt | hxu
      · have hxt' := Finset.mem_sdiff.mp hxt
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hToldX hxt'.1, hxt'.2⟩)
      · exact Finset.mem_union_right _ (hu1 hxu)
    have hT₂c : T₂.card = r₂.take := by
      have hdisj : Disjoint (T_old \ t1Sub) uNew :=
        hToldM₁.mono Finset.sdiff_subset hu1
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_sdiff_of_subset ht1, hToldc, ht2, hu2]
      omega
    have hK₂_disj_T₂ : Disjoint T₂ K₂ := by
      rw [Finset.disjoint_left]
      intro x hxT₂ hxK₂
      simp only [T₂, K₂, Finset.mem_union, Finset.mem_sdiff] at hxT₂ hxK₂
      rcases hxT₂ with ⟨hxTold, _⟩ | hxu
      · rcases hxK₂ with (⟨hxKold, _⟩ | hxz) | hxw
        · exact Finset.disjoint_left.mp hTK_disj hxTold hxKold
        · exact Finset.disjoint_left.mp hTK_disj hxTold (hks1 (hz1 hxz))
        · exact Finset.disjoint_left.mp hToldM₁ hxTold (Finset.sdiff_subset (hw1 hxw))
      · rcases hxK₂ with (⟨hxKold, _⟩ | hxz) | hxw
        · exact Finset.disjoint_right.mp hKoldM₁ (hu1 hxu) hxKold
        · exact Finset.disjoint_right.mp hKoldM₁ (hu1 hxu) (hks1 (hz1 hxz))
        · exact (Finset.mem_sdiff.mp (hw1 hxw)).2 hxu
    have hK₂X₁ : K₂ ⊆ ((X₀ \ T₁) ∪ M₁) \ T₂ := by
      intro x hxK₂
      refine Finset.mem_sdiff.mpr ⟨?_, Finset.disjoint_right.mp hK₂_disj_T₂ hxK₂⟩
      rcases Finset.mem_union.mp hxK₂ with hx1 | hxw
      · have hxKold : x ∈ K_old := by
          rcases Finset.mem_union.mp hx1 with hxs | hxz
          · exact Finset.sdiff_subset hxs
          · exact hks1 (hz1 hxz)
        have hx0 := Finset.mem_sdiff.mp (hKoldX hxKold)
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx0.1, fun h => hx0.2 (ht1 h)⟩)
      · exact Finset.mem_union_right _ (Finset.sdiff_subset (hw1 hxw))
    have hK₂c : K₂.card = r₂.keep := by
      have hd1 : Disjoint (K_old \ k1Surv) zSub :=
        disjoint_sdiff_self_left.mono_right hz1
      have hd2 : Disjoint ((K_old \ k1Surv) ∪ zSub) wNew := by
        refine hKoldM₁.mono ?_ (hw1.trans Finset.sdiff_subset)
        exact Finset.union_subset Finset.sdiff_subset (hz1.trans hks1)
      rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
        Finset.card_sdiff_of_subset hks1, hKoldc, hks2, hz2, hw2]
      omega
    have hex₁ : r₁.exhaust = true → T₁ ∪ K₁ = X₀ := by
      intro he1
      have hX₀ : T_old ∪ K_old = X₀ := hexOld (by simp [he1])
      rcases hex_ov1 he1 with ⟨htk_eq, hkp_eq⟩
      have hv_eq : vSub = T_old \ t1Sub := by
        apply Finset.eq_of_subset_of_card_le hv1
        rw [Finset.card_sdiff_of_subset ht1, hToldc, ht2, hv2]
        omega
      have hks_eq : k1Surv = K_old := by
        apply Finset.eq_of_subset_of_card_le hks1
        rw [hKoldc, hks2]
        omega
      have : T₁ ∪ K₁ = T_old ∪ K_old := by
        simp only [T₁, K₁, hv_eq, hks_eq]
        rw [Finset.union_left_comm, Finset.union_sdiff_of_subset ht1, Finset.union_comm]
      rw [this, hX₀]
    have hex₂ : r₂.exhaust = true → T₂ ∪ K₂ = (X₀ \ T₁) ∪ M₁ := by
      intro he2
      have hX₀ : T_old ∪ K_old = X₀ := hexOld (by simp [he2])
      rcases hex_ov2 he2 with ⟨hmk_eq, _⟩
      have huw_eq : uNew ∪ wNew = M₁ := by
        apply Finset.eq_of_subset_of_card_le
          (Finset.union_subset hu1 (hw1.trans Finset.sdiff_subset))
        rw [Finset.card_union_of_disjoint (disjoint_sdiff_self_right.mono_right hw1),
          hu2, hw2, hM₁_card, hmk_eq]
      have hz_eq : zSub = k1Surv := by
        apply Finset.eq_of_subset_of_card_le hz1
        rw [hks2, hz2]
        omega
      have hk_union : (K_old \ k1Surv) ∪ zSub = K_old := by
        rw [hz_eq, Finset.sdiff_union_of_subset hks1]
      have hTK_sub : (T_old \ t1Sub) ∪ K_old = X₀ \ t1Sub := by
        rw [← hX₀]
        ext x
        simp only [Finset.mem_union, Finset.mem_sdiff]
        constructor
        · rintro (⟨hxT, hxnot⟩ | hxK)
          · exact ⟨Or.inl hxT, hxnot⟩
          · exact ⟨Or.inr hxK, fun hxt => Finset.disjoint_left.mp hTK_disj (ht1 hxt) hxK⟩
        · rintro ⟨hxT | hxK, hxnot⟩
          · exact Or.inl ⟨hxT, hxnot⟩
          · exact Or.inr hxK
      show ((T_old \ t1Sub) ∪ uNew) ∪ (((K_old \ k1Surv) ∪ zSub) ∪ wNew) = (X₀ \ t1Sub) ∪ M₁
      rw [hk_union]
      have rearr : ((T_old \ t1Sub) ∪ uNew) ∪ (K_old ∪ wNew) =
          ((T_old \ t1Sub) ∪ K_old) ∪ (uNew ∪ wNew) := by
        ext x; simp only [Finset.mem_union]; constructor <;>
          (rintro ((h | h) | (h | h));
           · exact Or.inl (Or.inl h)
           · exact Or.inr (Or.inl h)
           · exact Or.inl (Or.inr h)
           · exact Or.inr (Or.inr h))
      rw [rearr, hTK_sub, huw_eq]
    refine ⟨⟨(T₁, K₁), (T₂, K₂)⟩, ?_, ?_⟩
    · simp only [seqSet, Finset.mem_sigma, mem_firingsOn]
      exact ⟨⟨hT₁X, ht2, hK₁X, hK₁c, hex₁⟩, ⟨hT₂X₁, hT₂c, hK₂X₁, hK₂c, hex₂⟩⟩
    · -- Verify `fwd ⟨(T₁, K₁), (T₂, K₂)⟩ = b`!
      have hT₂_inter_M₁ : T₂ ∩ M₁ = uNew := by
        show ((T_old \ t1Sub) ∪ uNew) ∩ M₁ = uNew
        rw [Finset.union_inter_distrib_right,
          Finset.disjoint_iff_inter_eq_empty.mp (hToldM₁.mono_left Finset.sdiff_subset),
          Finset.empty_union, Finset.inter_eq_left.mpr hu1]
      have hwM₁ : wNew ⊆ M₁ := hw1.trans Finset.sdiff_subset
      have hKold_sub_aux : (K_old \ k1Surv) ∪ zSub ⊆ K_old :=
        Finset.union_subset Finset.sdiff_subset (hz1.trans hks1)
      have hK₂_inter_M₁ : K₂ ∩ M₁ = wNew := by
        show (((K_old \ k1Surv) ∪ zSub) ∪ wNew) ∩ M₁ = wNew
        rw [Finset.union_inter_distrib_right,
          Finset.disjoint_iff_inter_eq_empty.mp (hKoldM₁.mono_left hKold_sub_aux),
          Finset.empty_union, Finset.inter_eq_left.mpr hwM₁]
      have hks_disj_T₂ : Disjoint k1Surv T₂ := by
        refine Finset.disjoint_union_right.mpr ⟨?_, hKoldM₁.mono hks1 hu1⟩
        exact hTK_disj.symm.mono hks1 Finset.sdiff_subset
      have hv_sub_T₂ : vSub ⊆ T₂ := hv1.trans Finset.subset_union_left
      have hK₁_inter_T₂ : K₁ ∩ T₂ = vSub := by
        show (k1Surv ∪ vSub) ∩ T₂ = vSub
        rw [Finset.union_inter_distrib_right,
          Finset.disjoint_iff_inter_eq_empty.mp hks_disj_T₂, Finset.empty_union,
          Finset.inter_eq_left.mpr hv_sub_T₂]
      have hK₁_sdiff_T₂ : K₁ \ T₂ = k1Surv := by
        show (k1Surv ∪ vSub) \ T₂ = k1Surv
        rw [Finset.union_sdiff_distrib, Finset.sdiff_eq_self_of_disjoint hks_disj_T₂,
          Finset.sdiff_eq_empty_iff_subset.mpr hv_sub_T₂, Finset.union_empty]
      have hv_disj_K₂ : Disjoint vSub K₂ := by
        refine Finset.disjoint_union_right.mpr ⟨?_, ?_⟩
        · exact hTK_disj.mono (hv1.trans Finset.sdiff_subset) hKold_sub_aux
        · exact hToldM₁.mono (hv1.trans Finset.sdiff_subset) hwM₁
      have hks_inter_K₂ : k1Surv ∩ K₂ = zSub := by
        show k1Surv ∩ (((K_old \ k1Surv) ∪ zSub) ∪ wNew) = zSub
        rw [Finset.inter_union_distrib_left, Finset.inter_union_distrib_left,
          Finset.disjoint_iff_inter_eq_empty.mp disjoint_sdiff_self_right, Finset.empty_union,
          Finset.disjoint_iff_inter_eq_empty.mp (hKoldM₁.mono hks1 hwM₁), Finset.union_empty,
          Finset.inter_eq_right.mpr hz1]
      have hK₁_inter_K₂ : K₁ ∩ K₂ = zSub := by
        show (k1Surv ∪ vSub) ∩ K₂ = zSub
        rw [Finset.union_inter_distrib_right,
          Finset.disjoint_iff_inter_eq_empty.mp hv_disj_K₂, Finset.union_empty,
          hks_inter_K₂]
      have hT₂_sdiff_M₁ : T₂ \ M₁ = T_old \ t1Sub := by
        show ((T_old \ t1Sub) ∪ uNew) \ M₁ = T_old \ t1Sub
        rw [Finset.union_sdiff_distrib,
          Finset.sdiff_eq_self_of_disjoint (hToldM₁.mono_left Finset.sdiff_subset),
          Finset.sdiff_eq_empty_iff_subset.mpr hu1, Finset.union_empty]
      have hK₂_sdiff_M₁ : K₂ \ M₁ = (K_old \ k1Surv) ∪ zSub := by
        show (((K_old \ k1Surv) ∪ zSub) ∪ wNew) \ M₁ = (K_old \ k1Surv) ∪ zSub
        rw [Finset.union_sdiff_distrib,
          Finset.sdiff_eq_self_of_disjoint (hKoldM₁.mono_left hKold_sub_aux),
          Finset.sdiff_eq_empty_iff_subset.mpr hwM₁, Finset.union_empty]
      have hTold_rec : T₁ ∪ (T₂ \ M₁) = T_old := by
        rw [hT₂_sdiff_M₁]
        exact Finset.union_sdiff_of_subset ht1
      have hKold_rec : (K₁ \ T₂) ∪ (K₂ \ M₁) = K_old := by
        rw [hK₁_sdiff_T₂, hK₂_sdiff_M₁, ← Finset.union_assoc,
          Finset.union_sdiff_of_subset hks1, Finset.union_eq_left.mpr (hz1.trans hks1)]
      have hov_rec : Overlap1.mk (T₂ ∩ M₁).card (K₁ ∩ T₂).card (K₂ ∩ M₁).card (K₁ ∩ K₂).card = ov := by
        rw [hT₂_inter_M₁, hK₁_inter_T₂, hK₂_inter_M₁, hK₁_inter_K₂, hu2, hv2, hw2, hz2]
      simp only [fwd, Sigma.mk.injEq, Prod.mk.injEq, FiberWitness.mk.injEq, heq_eq_eq]
      exact ⟨⟨hov_rec, hTold_rec, hKold_rec⟩, hT₂_inter_M₁, hK₂_inter_M₁, rfl,
        hK₁_inter_T₂, hK₁_sdiff_T₂, hK₁_inter_K₂⟩
  · -- Summand equality: `outCount` after `r₁` then `r₂` equals composite `outCount`!
    intro s hs
    rcases s with ⟨⟨T₁, K₁⟩, ⟨T₂, K₂⟩⟩
    simp only [seqSet, Finset.mem_sigma, mem_firingsOn] at hs
    rcases hs with ⟨⟨_, _, hK₁X, _, _⟩, ⟨_, _, hK₂X₁, _, _⟩⟩
    have hT₂K₂ : Disjoint T₂ K₂ := disjoint_sdiff_self_right.mono_right hK₂X₁
    have hK₂_not_T₁ : ∀ x ∈ K₂, x ∉ M₁ → x ∉ T₁ := by
      intro x hxK₂ hxnotM₁ hxT₁
      rcases Finset.mem_union.mp ((hK₂X₁.trans Finset.sdiff_subset) hxK₂) with hx0 | hxM
      · exact (Finset.mem_sdiff.mp hx0).2 hxT₁
      · exact hxnotM₁ hxM
    congr 1
    simp only [fwd, outCount, Overlap1.composedRule, Prod.mk.injEq]
    clear seqSet compSet compMid fwd
    refine ⟨?_, ?_, ?_⟩
    · congr 1
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · rintro ⟨⟨hxU, hxnot1⟩, hxnot2⟩
        refine ⟨hxU, fun h => ?_⟩
        rcases h with (h | ⟨h, _⟩) | (⟨h, _⟩ | ⟨h, _⟩)
        · exact hxnot1 (Or.inl h)
        · exact hxnot2 (Or.inl h)
        · exact hxnot1 (Or.inr h)
        · exact hxnot2 (Or.inr h)
      · rintro ⟨hxU, hxnot⟩
        have hxnotM : x ∉ M₁ := Finset.disjoint_left.mp hUM₁ hxU
        refine ⟨⟨hxU, ?_⟩, ?_⟩
        · rintro (hT₁ | hK₁)
          · exact hxnot (Or.inl (Or.inl hT₁))
          · by_cases hT₂ : x ∈ T₂
            · exact hxnot (Or.inl (Or.inr ⟨hT₂, hxnotM⟩))
            · exact hxnot (Or.inr (Or.inl ⟨hK₁, hT₂⟩))
        · rintro (hT₂ | hK₂)
          · exact hxnot (Or.inl (Or.inr ⟨hT₂, hxnotM⟩))
          · exact hxnot (Or.inr (Or.inr ⟨hK₂, hxnotM⟩))
    · congr 1
      ext x
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      constructor
      · rintro (⟨(⟨hxR, hxnotT₁⟩ | ⟨hxU, hxK₁⟩), hxnotT₂⟩ | ⟨⟨hxU, _⟩, hxK₂⟩)
        · exact Or.inl ⟨hxR, fun h => h.elim hxnotT₁ (fun h2 => hxnotT₂ h2.1)⟩
        · exact Or.inr ⟨hxU, Or.inl ⟨hxK₁, hxnotT₂⟩⟩
        · exact Or.inr ⟨hxU, Or.inr ⟨hxK₂, Finset.disjoint_left.mp hUM₁ hxU⟩⟩
      · rintro (⟨hxR, hxnot⟩ | ⟨hxU, ⟨hxK₁, hxnotT₂⟩ | ⟨hxK₂, hxnotM⟩⟩)
        · have hxnotM : x ∉ M₁ := Finset.disjoint_left.mp hRM₁ hxR
          exact Or.inl ⟨Or.inl ⟨hxR, fun h => hxnot (Or.inl h)⟩,
            fun h => hxnot (Or.inr ⟨h, hxnotM⟩)⟩
        · exact Or.inl ⟨Or.inr ⟨hxU, hxK₁⟩, hxnotT₂⟩
        · by_cases hxK₁ : x ∈ K₁
          · exact Or.inl ⟨Or.inr ⟨hxU, hxK₁⟩, Finset.disjoint_right.mp hT₂K₂ hxK₂⟩
          · exact Or.inr ⟨⟨hxU, fun h => h.elim (hK₂_not_T₁ x hxK₂ hxnotM) hxK₁⟩, hxK₂⟩
    · have hN_split : ((N₀ \ T₁) ∪ M₁) \ T₂ = (N₀ \ (T₁ ∪ (T₂ \ M₁))) ∪ (M₁ \ T₂) := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · rintro ⟨⟨hxN, hxnotT₁⟩ | hxM, hxnotT₂⟩
          · exact Or.inl ⟨hxN, fun h => h.elim hxnotT₁ (fun h2 => hxnotT₂ h2.1)⟩
          · exact Or.inr ⟨hxM, hxnotT₂⟩
        · rintro (⟨hxN, hxnot⟩ | ⟨hxM, hxnotT₂⟩)
          · exact ⟨Or.inl ⟨hxN, fun h => hxnot (Or.inl h)⟩,
              fun h => hxnot (Or.inr ⟨h, Finset.disjoint_left.mp hNM₁ hxN⟩)⟩
          · exact ⟨Or.inr hxM, hxnotT₂⟩
      have hdisj : Disjoint (N₀ \ (T₁ ∪ (T₂ \ M₁))) (M₁ \ T₂) :=
        hNM₁.mono Finset.sdiff_subset Finset.sdiff_subset
      have hM₁_sdiff : (M₁ \ T₂).card = r₁.make - (T₂ ∩ M₁).card := by
        rw [Finset.card_sdiff, Finset.inter_comm, hM₁_card]
      rw [hN_split, Finset.card_union_of_disjoint hdisj, hM₁_sdiff, Nat.add_assoc]

/-- `occRho1` is an algebra homomorphism from `(SingleRule →₀ ℕ, mul1)` to endomorphisms. -/
theorem occRho1_mul (A B : SingleRule →₀ ℕ) :
    occRho1 (mul1 A B) = (occRho1 A).comp (occRho1 B) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
  · rw [mul1_add_left, occRho1_add, occRho1_add, LinearMap.add_comp, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
    · rw [mul1_add_right, occRho1_add, occRho1_add, LinearMap.comp_add, hx, hy]
    · rw [mul1_smul_single_single, occRho1_smul, ← nat_smul_single_one c₂ r₂,
        ← nat_smul_single_one c₁ r₁, occRho1_smul, occRho1_smul, LinearMap.smul_comp,
        LinearMap.comp_smul, smul_smul]
      congr 1
      apply Finsupp.lhom_ext'
      intro c
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      exact occRho1_compose1_apply r₂ r₁ c

/-- The uncolored bag representation `rho1` is also a homomorphism (`rho1 (A * B) = rho1 A ∘ rho1 B`). -/
theorem rho1_mul (A B : SingleRule →₀ ℕ) :
    rho1 (mul1 A B) = (rho1 A).comp (rho1 B) := by
  apply Finsupp.lhom_ext'
  intro x
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have hlift : Finsupp.single x (1 : ℕ) = forgetColors (Finsupp.single (x, 0, 0) 1) := by
    simp
  rw [hlift]
  have h1 := LinearMap.congr_fun (forgetColors_occRho1 (mul1 A B)) (Finsupp.single (x, 0, 0) 1)
  have h2 := LinearMap.congr_fun (forgetColors_occRho1 B) (Finsupp.single (x, 0, 0) 1)
  have h3 := LinearMap.congr_fun (forgetColors_occRho1 A)
    (occRho1 B (Finsupp.single (x, 0, 0) 1))
  simp only [LinearMap.comp_apply] at h1 h2 h3 ⊢
  rw [← h1, occRho1_mul, LinearMap.comp_apply, h3, h2]

/-- **Associativity of single-species Behr–Krivine rule composition**, deduced immediately
from faithfulness (`occRho1_injective`) and `LinearMap.comp_assoc`. -/
theorem mul1_assoc (A B C : SingleRule →₀ ℕ) :
    mul1 (mul1 A B) C = mul1 A (mul1 B C) := by
  apply occRho1_injective
  rw [occRho1_mul, occRho1_mul, occRho1_mul, occRho1_mul, LinearMap.comp_assoc]

/-! ## `Semiring` instance on `SingleRuleAlgebra` -/

/-- Type synonym for `SingleRule →₀ ℕ` equipped with the Behr–Krivine rule-composition
`Semiring` structure. -/
def SingleRuleAlgebra := SingleRule →₀ ℕ

namespace SingleRuleAlgebra

noncomputable instance : AddCommMonoid SingleRuleAlgebra :=
  inferInstanceAs (AddCommMonoid (SingleRule →₀ ℕ))

/-- Basis element `[r]` in `SingleRuleAlgebra`. -/
noncomputable def ofRule (r : SingleRule) : SingleRuleAlgebra :=
  Finsupp.single r 1

noncomputable instance : Semiring SingleRuleAlgebra where
  mul := mul1
  mul_assoc := mul1_assoc
  one := Finsupp.single SingleRule.id 1
  one_mul := mul1_id_left
  mul_one := mul1_id_right
  zero_mul := mul1_zero_left
  mul_zero := mul1_zero_right
  left_distrib := mul1_add_right
  right_distrib := mul1_add_left
  nsmul := (· • ·)
  nsmul_zero := fun _ => zero_smul ℕ _
  nsmul_succ := fun n x => succ_nsmul x n

end SingleRuleAlgebra

end Mettapedia.Algebra.RuleAlgebra
