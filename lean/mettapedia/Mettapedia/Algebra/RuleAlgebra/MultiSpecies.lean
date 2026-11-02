import Mettapedia.Algebra.RuleAlgebra.SingleSpecies
import Mathlib.Data.Finset.Pi
import Mathlib.Data.Finsupp.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Multi-species Behr–Krivine rule algebra, signed Z-set operator ring, and controls

We lift the single-species rule algebra (`SingleSpecies.lean`) to arbitrary species /
row-class types `R` (`[DecidableEq R]`) by viewing each multi-species rule
`r : Rule R` (`take, keep, make : R →₀ ℕ`, `exhaust : Finset R`) as a finitely
supported tensor product of `SingleRule`s across species `a : R`.

## Main definitions and theorems

* `Rule R`: multi-species rule with `take`, `keep`, `make : R →₀ ℕ` and zero-residual
  exhaustion guard `exhaust : Finset R`.
* `tensorRules` & `tensorRules_apply`: restricted tensor product of single-species rule
  combinations over finite species supports.
* `compose`, `mul`, `mul_assoc`, `MultiRuleAlgebra R` (`Semiring`): exact associative
  multi-species Behr–Krivine rule algebra over `ℕ`.
* `compose_comm_of_disjoint_support`: disjoint-species rules commute on the nose.
* `SignedRuleAlgebra R` (`Ring`) and `commutator`: `ℤ`-linear rule operator ring
  supporting Lie commutators `[A, B]_⋆ = A * B - B * A` and signed delta updates.
* `rho` and `rhoZ`, `rho_mul` and `rhoZ_mul`: homomorphic representations on uncolored
  multi-species bag modules `(R →₀ ℕ) →₀ ℕ` and Z-set modules `(R →₀ ℕ) →₀ ℤ`.
* **Controls (Positive & Negative)**:
  - `rho_churn_eq_keep` & `single_churn_ne_keep`: the uncolored bag representation `rho`
    is *not* faithful (`[take a, make a]` and `[keep a]` act identically on uncolored
    bags while remaining distinct in `MultiRuleAlgebra R`, separated by `occRho1`).
  - `compose1_pureAbsent_take` & `naiveDropMul1_not_assoc`: `[absent a] ⋆ [take a]`
    shifts absence to unique-consumption (`take = 1, exhaust = true`), restoring
    associativity where naive drop-on-consume composition fails associativity.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RuleAlgebra

open scoped BigOperators

/-- A multi-species interaction rule over species / row-class type `R`:
* `take`: multiset of occurrences consumed;
* `keep`: multiset of surviving occurrences inspected (read arcs);
* `make`: multiset of fresh occurrences minted;
* `exhaust`: finite set of species required to have zero unmatched residual
  outside `take + keep`. -/
@[ext]
structure Rule (R : Type*) where
  take : R →₀ ℕ
  keep : R →₀ ℕ
  make : R →₀ ℕ
  exhaust : Finset R

instance {R : Type*} [DecidableEq R] : DecidableEq (Rule R) := fun r₁ r₂ =>
  if ht : r₁.take = r₂.take then
    if hk : r₁.keep = r₂.keep then
      if hm : r₁.make = r₂.make then
        if he : r₁.exhaust = r₂.exhaust then
          isTrue (Rule.ext ht hk hm he)
        else isFalse (fun h => he (congrArg Rule.exhaust h))
      else isFalse (fun h => hm (congrArg Rule.make h))
    else isFalse (fun h => hk (congrArg Rule.keep h))
  else isFalse (fun h => ht (congrArg Rule.take h))

namespace Rule

section Unconstrained

variable {R : Type*}

/-- Identity multi-species rule (`take = 0, keep = 0, make = 0, exhaust = ∅`). -/
def id : Rule R := ⟨0, 0, 0, ∅⟩

/-- Pure read-observable rule inspecting `P` occurrences (`take = 0, keep = P, make = 0`). -/
def keepOnly (P : R →₀ ℕ) : Rule R := ⟨0, P, 0, ∅⟩

/-- Pure absence guard requiring every species in `E` to have count `0`. -/
def pureAbsent (E : Finset R) : Rule R := ⟨0, 0, 0, E⟩

/-- Output bag produced when `r` fires on `X` (`X - r.take + r.make`). -/
noncomputable def nextBag (r : Rule R) (X : R →₀ ℕ) : R →₀ ℕ :=
  X - r.take + r.make

@[simp]
theorem nextBag_apply (r : Rule R) (X : R →₀ ℕ) (a : R) :
    r.nextBag X a = X a - r.take a + r.make a := by
  simp [nextBag]

@[simp]
theorem id_nextBag (X : R →₀ ℕ) : (Rule.id : Rule R).nextBag X = X := by
  ext a
  simp [Rule.id]

@[simp]
theorem keepOnly_nextBag (P X : R →₀ ℕ) : (Rule.keepOnly P).nextBag X = X := by
  ext a
  simp [Rule.keepOnly]

end Unconstrained

section Basic

variable {R : Type*} [DecidableEq R]

/-- Projection of a multi-species rule `r` to a single species `a : R`. -/
def atSpecies (r : Rule R) (a : R) : SingleRule where
  take := r.take a
  keep := r.keep a
  make := r.make a
  exhaust := decide (a ∈ r.exhaust)

@[simp]
theorem id_atSpecies (a : R) : (Rule.id : Rule R).atSpecies a = SingleRule.id := by
  simp [Rule.id, atSpecies, SingleRule.id]

theorem ext_atSpecies {r₁ r₂ : Rule R} (h : ∀ a : R, r₁.atSpecies a = r₂.atSpecies a) :
    r₁ = r₂ := by
  have h' : ∀ a : R, r₁.take a = r₂.take a ∧ r₁.keep a = r₂.keep a ∧
      r₁.make a = r₂.make a ∧ (a ∈ r₁.exhaust ↔ a ∈ r₂.exhaust) := by
    intro a
    have ha := h a
    simp only [atSpecies, SingleRule.mk.injEq, decide_eq_decide] at ha
    exact ha
  ext a
  · exact (h' a).1
  · exact (h' a).2.1
  · exact (h' a).2.2.1
  · exact (h' a).2.2.2

/-- Active species support of `r`: species where `r` takes, keeps, makes, or exhaust-checks. -/
def support (r : Rule R) : Finset R :=
  r.take.support ∪ r.keep.support ∪ r.make.support ∪ r.exhaust

@[simp]
theorem id_support : (Rule.id : Rule R).support = ∅ := by
  simp [Rule.id, support]

theorem notMem_support_iff (r : Rule R) (a : R) :
    a ∉ r.support ↔ r.atSpecies a = SingleRule.id := by
  simp only [support, Finset.mem_union, Finsupp.mem_support_iff, not_or, not_not,
    atSpecies, SingleRule.id, SingleRule.mk.injEq, decide_eq_false_iff_not]
  tauto

theorem atSpecies_eq_id_of_notMem_support {r : Rule R} {a : R} (ha : a ∉ r.support) :
    r.atSpecies a = SingleRule.id :=
  (notMem_support_iff r a).mp ha

theorem mem_support_iff (r : Rule R) (a : R) :
    a ∈ r.support ↔ r.atSpecies a ≠ SingleRule.id := by
  rw [← not_iff_not, not_not, notMem_support_iff]

/-- Embed a `SingleRule` at a single species `a : R`. -/
noncomputable def ofSingle (a : R) (s : SingleRule) : Rule R where
  take := Finsupp.single a s.take
  keep := Finsupp.single a s.keep
  make := Finsupp.single a s.make
  exhaust := if s.exhaust then {a} else ∅

@[simp]
theorem ofSingle_atSpecies_same (a : R) (s : SingleRule) :
    (ofSingle a s).atSpecies a = s := by
  cases s with
  | mk t k m e =>
    cases e <;> simp [ofSingle, atSpecies]

theorem ofSingle_atSpecies_ne {a b : R} (s : SingleRule) (h : b ≠ a) :
    (ofSingle a s).atSpecies b = SingleRule.id := by
  cases s with
  | mk t k m e =>
    cases e <;> simp [ofSingle, atSpecies, SingleRule.id, h]

theorem ofSingle_support_subset (a : R) (s : SingleRule) :
    (ofSingle a s).support ⊆ {a} := by
  intro b hb
  rw [Finset.mem_singleton]
  by_contra hba
  exact (mem_support_iff _ b).mp hb (ofSingle_atSpecies_ne s hba)

private theorem finset_sum_single_apply (S : Finset R) (g : R → ℕ) (b : R) :
    (S.sum fun a => Finsupp.single a (g a)) b = if b ∈ S then g b else 0 := by
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/-- Assemble a `Rule R` from a family `f : R → SingleRule` supported within `S : Finset R`. -/
noncomputable def ofFamily (S : Finset R) (f : R → SingleRule) : Rule R where
  take := S.sum fun a => Finsupp.single a (f a).take
  keep := S.sum fun a => Finsupp.single a (f a).keep
  make := S.sum fun a => Finsupp.single a (f a).make
  exhaust := S.filter fun a => (f a).exhaust = true

theorem ofFamily_atSpecies_of_mem {S : Finset R} {f : R → SingleRule} {a : R} (ha : a ∈ S) :
    (ofFamily S f).atSpecies a = f a := by
  cases hfa : f a with
  | mk t k m e =>
    simp [ofFamily, atSpecies, finset_sum_single_apply, ha, hfa]

theorem ofFamily_atSpecies_of_notMem {S : Finset R} {f : R → SingleRule} {a : R} (ha : a ∉ S) :
    (ofFamily S f).atSpecies a = SingleRule.id := by
  simp [ofFamily, atSpecies, finset_sum_single_apply, ha, SingleRule.id]

theorem ofFamily_support_subset (S : Finset R) (f : R → SingleRule) :
    (ofFamily S f).support ⊆ S := by
  intro a ha
  by_contra hnot
  exact (mem_support_iff _ a).mp ha (ofFamily_atSpecies_of_notMem hnot)

/-- Number of occurrence-subset matches of `r : Rule R` on a multi-species bag `X : R →₀ ℕ`. -/
def matchesBag (r : Rule R) (X : R →₀ ℕ) : ℕ :=
  ∏ a ∈ r.support, (r.atSpecies a).matchesCount (X a)

theorem nextBag_support_subset (r : Rule R) (X : R →₀ ℕ) :
    (r.nextBag X).support ⊆ X.support ∪ r.make.support := by
  intro a ha
  rw [Finsupp.mem_support_iff, nextBag_apply] at ha
  rw [Finset.mem_union, Finsupp.mem_support_iff, Finsupp.mem_support_iff]
  by_contra hnot
  rw [not_or, not_not, not_not] at hnot
  rw [hnot.1, hnot.2] at ha
  simp at ha

theorem matchesBag_eq_prod (r : Rule R) (X : R →₀ ℕ) {T : Finset R}
    (hrT : r.support ⊆ T) :
    r.matchesBag X = ∏ a ∈ T, (r.atSpecies a).matchesCount (X a) := by
  unfold matchesBag
  refine Finset.prod_subset hrT ?_
  intro a _ ha
  rw [Rule.atSpecies_eq_id_of_notMem_support ha, SingleRule.id_matchesCount]

@[simp]
theorem id_matchesBag (X : R →₀ ℕ) : (Rule.id : Rule R).matchesBag X = 1 := by
  simp [matchesBag]

end Basic

end Rule

/-! ## Restricted tensor product of single-species rule combinations -/

section Tensor

variable {R : Type*} [DecidableEq R]

/-- Assemble a `Rule R` from a dependent section `g : ∀ a ∈ S, SingleRule`. -/
noncomputable def ruleOfPi (S : Finset R) (g : ∀ a ∈ S, SingleRule) : Rule R :=
  Rule.ofFamily S (fun a => if ha : a ∈ S then g a ha else SingleRule.id)

theorem ruleOfPi_atSpecies_of_mem {S : Finset R} {g : ∀ a ∈ S, SingleRule} {a : R} (ha : a ∈ S) :
    (ruleOfPi S g).atSpecies a = g a ha := by
  rw [ruleOfPi, Rule.ofFamily_atSpecies_of_mem ha, dif_pos ha]

theorem ruleOfPi_atSpecies_of_notMem {S : Finset R} {g : ∀ a ∈ S, SingleRule} {a : R}
    (ha : a ∉ S) : (ruleOfPi S g).atSpecies a = SingleRule.id :=
  Rule.ofFamily_atSpecies_of_notMem ha

theorem ruleOfPi_support_subset (S : Finset R) (g : ∀ a ∈ S, SingleRule) :
    (ruleOfPi S g).support ⊆ S :=
  Rule.ofFamily_support_subset S _

theorem ruleOfPi_eq_iff (S : Finset R) (g : ∀ a ∈ S, SingleRule) (r : Rule R) :
    ruleOfPi S g = r ↔ r.support ⊆ S ∧ ∀ a (ha : a ∈ S), g a ha = r.atSpecies a := by
  constructor
  · rintro rfl
    exact ⟨ruleOfPi_support_subset S g, fun a ha => (ruleOfPi_atSpecies_of_mem ha).symm⟩
  · rintro ⟨hsub, hg⟩
    apply Rule.ext_atSpecies
    intro a
    by_cases ha : a ∈ S
    · rw [ruleOfPi_atSpecies_of_mem ha, hg a ha]
    · rw [ruleOfPi_atSpecies_of_notMem ha,
        Rule.atSpecies_eq_id_of_notMem_support (fun hm => ha (hsub hm))]

/-- Tensor product over `S : Finset R` of a family `F : R → (SingleRule →₀ ℕ)`. -/
noncomputable def tensorRules (S : Finset R) (F : R → (SingleRule →₀ ℕ)) : Rule R →₀ ℕ :=
  (S.pi fun a => (F a).support).sum fun g =>
    Finsupp.single (ruleOfPi S g) (∏ x ∈ S.attach, F x.1 (g x.1 x.2))

theorem tensorRules_support_subset (S : Finset R) (F : R → (SingleRule →₀ ℕ))
    {r : Rule R} (hr : r ∈ (tensorRules S F).support) : r.support ⊆ S := by
  rw [Finsupp.mem_support_iff] at hr
  unfold tensorRules at hr
  rw [Finsupp.finsetSum_apply] at hr
  obtain ⟨g, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hr
  by_cases hEq : ruleOfPi S g = r
  · rw [← hEq]
    exact ruleOfPi_support_subset S g
  · simp [hEq] at hne

private theorem tensorRules_apply_of_subset (S : Finset R) (F : R → (SingleRule →₀ ℕ))
    {r : Rule R} (hr : r.support ⊆ S) :
    tensorRules S F r = ∏ a ∈ S, F a (r.atSpecies a) := by
  unfold tensorRules
  rw [Finsupp.finsetSum_apply]
  let g₀ : ∀ a ∈ S, SingleRule := fun a _ => r.atSpecies a
  have hrew : ∀ g ∈ S.pi (fun a => (F a).support),
      (Finsupp.single (ruleOfPi S g) (∏ x ∈ S.attach, F x.1 (g x.1 x.2))) r =
        if g = g₀ then ∏ x ∈ S.attach, F x.1 (g x.1 x.2) else 0 := by
    intro g _
    have hiff : ruleOfPi S g = r ↔ g = g₀ := by
      rw [ruleOfPi_eq_iff]
      constructor
      · rintro ⟨_, hg⟩
        funext a ha
        exact hg a ha
      · rintro rfl
        exact ⟨hr, fun _ _ => rfl⟩
    by_cases h : g = g₀
    · rw [if_pos h, hiff.mpr h, Finsupp.single_eq_same]
    · have hne : r ≠ ruleOfPi S g := fun hEq => h (hiff.mp hEq.symm)
      rw [if_neg h, Finsupp.single_eq_of_ne hne]
  rw [Finset.sum_congr rfl hrew, Finset.sum_ite_eq']
  by_cases hmem : g₀ ∈ S.pi (fun a => (F a).support)
  · rw [if_pos hmem]
    exact Finset.prod_attach S (fun a => F a (r.atSpecies a))
  · rw [if_neg hmem]
    rw [Finset.mem_pi] at hmem
    have hex : ∃ a ∈ S, r.atSpecies a ∉ (F a).support := by
      by_contra hall
      exact hmem (fun a ha => Classical.not_not.mp fun hnot => hall ⟨a, ha, hnot⟩)
    rcases hex with ⟨a, haS, hnot⟩
    rw [Finsupp.notMem_support_iff] at hnot
    exact (Finset.prod_eq_zero haS hnot).symm

/-- Pointwise evaluation of `tensorRules S F` on any finite superset `T ⊇ S ∪ r.support`,
provided `F` acts as `[SingleRule.id]` outside `S`. -/
theorem tensorRules_apply {S T : Finset R} {F : R → (SingleRule →₀ ℕ)}
    (hF : ∀ a ∉ S, F a = Finsupp.single SingleRule.id 1)
    (hST : S ⊆ T) (r : Rule R) (hrT : r.support ⊆ T) :
    tensorRules S F r = ∏ a ∈ T, F a (r.atSpecies a) := by
  by_cases hrS : r.support ⊆ S
  · rw [tensorRules_apply_of_subset S F hrS]
    refine Finset.prod_subset hST ?_
    intro a _ haS
    have ha_id : r.atSpecies a = SingleRule.id :=
      Rule.atSpecies_eq_id_of_notMem_support (fun hm => haS (hrS hm))
    rw [hF a haS, ha_id, Finsupp.single_eq_same]
  · have hzero : tensorRules S F r = 0 := by
      by_contra hne
      exact hrS (tensorRules_support_subset S F (Finsupp.mem_support_iff.mpr hne))
    rw [hzero]
    rw [Finset.not_subset] at hrS
    rcases hrS with ⟨a₀, ha₀_supp, ha₀_notS⟩
    have ha₀_T : a₀ ∈ T := hrT ha₀_supp
    have ha₀_ne : r.atSpecies a₀ ≠ SingleRule.id := (Rule.mem_support_iff r a₀).mp ha₀_supp
    have hFa₀ : F a₀ (r.atSpecies a₀) = 0 := by
      rw [hF a₀ ha₀_notS]
      exact Finsupp.single_eq_of_ne ha₀_ne
    exact (Finset.prod_eq_zero ha₀_T hFa₀).symm

/-- `tensorRules S F` is invariant under enlarging `S` to any `T ⊇ S`. -/
theorem tensorRules_subset {S T : Finset R} {F : R → (SingleRule →₀ ℕ)}
    (hF : ∀ a ∉ S, F a = Finsupp.single SingleRule.id 1) (hST : S ⊆ T) :
    tensorRules S F = tensorRules T F := by
  ext r
  let U := T ∪ r.support
  have hSU : S ⊆ U := hST.trans Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_left
  have hrU : r.support ⊆ U := Finset.subset_union_right
  have hFT : ∀ a ∉ T, F a = Finsupp.single SingleRule.id 1 :=
    fun a haT => hF a (fun haS => haT (hST haS))
  rw [tensorRules_apply hF hSU r hrU, tensorRules_apply hFT hTU r hrU]

/-! ## Multi-species Behr–Krivine rule composition and `Semiring (MultiRuleAlgebra R)` -/

/-- Formal-sum Behr–Krivine composition `r₂ ⋆ r₁` of two multi-species rules. -/
noncomputable def compose (r₂ r₁ : Rule R) : Rule R →₀ ℕ :=
  tensorRules (r₂.support ∪ r₁.support) (fun a => compose1 (r₂.atSpecies a) (r₁.atSpecies a))

private theorem compose1_outside_union (r₂ r₁ : Rule R) (a : R)
    (ha : a ∉ r₂.support ∪ r₁.support) :
    compose1 (r₂.atSpecies a) (r₁.atSpecies a) = Finsupp.single SingleRule.id 1 := by
  rw [Finset.mem_union, not_or] at ha
  rw [Rule.atSpecies_eq_id_of_notMem_support ha.1,
    Rule.atSpecies_eq_id_of_notMem_support ha.2, compose1_id_left]

/-- Factorized product formula for multi-species rule composition `compose r₂ r₁ r`. -/
theorem compose_apply (r₂ r₁ r : Rule R) {T : Finset R}
    (hT : r₂.support ∪ r₁.support ∪ r.support ⊆ T) :
    compose r₂ r₁ r = ∏ a ∈ T, compose1 (r₂.atSpecies a) (r₁.atSpecies a) (r.atSpecies a) := by
  have h12 : r₂.support ∪ r₁.support ⊆ T := Finset.subset_union_left.trans hT
  have hr : r.support ⊆ T := Finset.subset_union_right.trans hT
  exact tensorRules_apply (compose1_outside_union r₂ r₁) h12 r hr

/-- Every composite rule `r ∈ (compose r₂ r₁).support` has active support contained in
`r₂.support ∪ r₁.support`. -/
theorem compose_support_subset {r₂ r₁ r : Rule R} (hr : r ∈ (compose r₂ r₁).support) :
    r.support ⊆ r₂.support ∪ r₁.support :=
  tensorRules_support_subset _ _ hr

theorem compose_id_left (r₁ : Rule R) :
    compose Rule.id r₁ = Finsupp.single r₁ 1 := by
  ext r
  let T := (Rule.id : Rule R).support ∪ r₁.support ∪ r.support
  rw [compose_apply Rule.id r₁ r (Finset.Subset.refl T)]
  by_cases hEq : r₁ = r
  · subst hEq
    rw [Finsupp.single_eq_same]
    apply Finset.prod_eq_one
    intro a _
    rw [Rule.id_atSpecies, compose1_id_left, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hEq)]
    have hex : ∃ a ∈ T, r₁.atSpecies a ≠ r.atSpecies a := by
      by_contra hfor
      apply hEq
      apply Rule.ext_atSpecies
      intro a
      by_cases haT : a ∈ T
      · exact Classical.not_not.mp fun hne => hfor ⟨a, haT, hne⟩
      · simp only [T, Finset.mem_union, not_or] at haT
        rw [Rule.atSpecies_eq_id_of_notMem_support haT.1.2,
          Rule.atSpecies_eq_id_of_notMem_support haT.2]
    rcases hex with ⟨a₀, ha₀T, hne⟩
    refine Finset.prod_eq_zero ha₀T ?_
    rw [Rule.id_atSpecies, compose1_id_left]
    exact Finsupp.single_eq_of_ne (Ne.symm hne)

theorem compose_id_right (r₂ : Rule R) :
    compose r₂ Rule.id = Finsupp.single r₂ 1 := by
  ext r
  let T := r₂.support ∪ (Rule.id : Rule R).support ∪ r.support
  rw [compose_apply r₂ Rule.id r (Finset.Subset.refl T)]
  by_cases hEq : r₂ = r
  · subst hEq
    rw [Finsupp.single_eq_same]
    apply Finset.prod_eq_one
    intro a _
    rw [Rule.id_atSpecies, compose1_id_right, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hEq)]
    have hex : ∃ a ∈ T, r₂.atSpecies a ≠ r.atSpecies a := by
      by_contra hfor
      apply hEq
      apply Rule.ext_atSpecies
      intro a
      by_cases haT : a ∈ T
      · exact Classical.not_not.mp fun hne => hfor ⟨a, haT, hne⟩
      · simp only [T, Finset.mem_union, not_or] at haT
        rw [Rule.atSpecies_eq_id_of_notMem_support haT.1.1,
          Rule.atSpecies_eq_id_of_notMem_support haT.2]
    rcases hex with ⟨a₀, ha₀T, hne⟩
    refine Finset.prod_eq_zero ha₀T ?_
    rw [Rule.id_atSpecies, compose1_id_right]
    exact Finsupp.single_eq_of_ne (Ne.symm hne)

/-- Rules with disjoint active species supports commute on the nose. -/
theorem compose_comm_of_disjoint_support {r₂ r₁ : Rule R}
    (hdisj : Disjoint r₂.support r₁.support) :
    compose r₂ r₁ = compose r₁ r₂ := by
  ext r
  let T := r₂.support ∪ r₁.support ∪ r.support
  have hT₁ : r₂.support ∪ r₁.support ∪ r.support ⊆ T := Finset.Subset.refl T
  have hT₂ : r₁.support ∪ r₂.support ∪ r.support ⊆ T := by
    rw [Finset.union_comm r₁.support r₂.support]
  rw [compose_apply r₂ r₁ r hT₁, compose_apply r₁ r₂ r hT₂]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases ha₂ : a ∈ r₂.support
  · have ha₁ : a ∉ r₁.support := Finset.disjoint_left.mp hdisj ha₂
    rw [Rule.atSpecies_eq_id_of_notMem_support ha₁, compose1_id_right, compose1_id_left]
  · rw [Rule.atSpecies_eq_id_of_notMem_support ha₂, compose1_id_left, compose1_id_right]

/-- Bilinear Behr–Krivine multiplication on `Rule R →₀ ℕ`. -/
noncomputable def mul (A B : Rule R →₀ ℕ) : Rule R →₀ ℕ :=
  A.sum fun r₂ c₂ => B.sum fun r₁ c₁ => (c₂ * c₁) • compose r₂ r₁

@[simp]
theorem mul_zero_left (B : Rule R →₀ ℕ) : mul 0 B = 0 := by simp [mul]

@[simp]
theorem mul_zero_right (A : Rule R →₀ ℕ) : mul A 0 = 0 := by simp [mul]

theorem mul_add_left (A₁ A₂ B : Rule R →₀ ℕ) :
    mul (A₁ + A₂) B = mul A₁ B + mul A₂ B := by
  unfold mul
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₂ a₁ a₂
    rw [← Finsupp.sum_add]
    congr 1; ext r₁ c₁
    rw [Nat.add_mul, add_smul]

theorem mul_add_right (A B₁ B₂ : Rule R →₀ ℕ) :
    mul A (B₁ + B₂) = mul A B₁ + mul A B₂ := by
  unfold mul
  rw [← Finsupp.sum_add]
  congr 1; ext r₂ c₂
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₁ b₁ b₂
    rw [Nat.mul_add, add_smul]

theorem mul_smul_single_single (c₂ c₁ : ℕ) (r₂ r₁ : Rule R) :
    mul (Finsupp.single r₂ c₂) (Finsupp.single r₁ c₁) = (c₂ * c₁) • compose r₂ r₁ := by
  simp [mul]

theorem mul_single_single (r₂ r₁ : Rule R) :
    mul (Finsupp.single r₂ 1) (Finsupp.single r₁ 1) = compose r₂ r₁ := by
  simp [mul]

theorem mul_smul_left (c : ℕ) (A B : Rule R →₀ ℕ) :
    mul (c • A) B = c • mul A B := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r k => ?_)
  · rw [smul_add, mul_add_left, hx, hy, mul_add_left, smul_add]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r' k' => ?_)
    · rw [mul_add_right, mul_add_right, hx, hy, smul_add]
    · ext x; simp [mul_smul_single_single]; ring

theorem mul_smul_right (c : ℕ) (A B : Rule R →₀ ℕ) :
    mul A (c • B) = c • mul A B := by
  refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r' k' => ?_)
  · rw [smul_add, mul_add_right, hx, hy, mul_add_right, smul_add]
  · refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r k => ?_)
    · rw [mul_add_left, mul_add_left, hx, hy, smul_add]
    · ext x; simp [mul_smul_single_single]; ring

private theorem mul_finset_sum_left {ι : Type*} (s : Finset ι) (f : ι → (Rule R →₀ ℕ))
    (B : Rule R →₀ ℕ) : mul (s.sum f) B = s.sum (fun i => mul (f i) B) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, mul_add_left, ih, Finset.sum_insert hi]

private theorem mul_finset_sum_right {ι : Type*} (s : Finset ι) (A : Rule R →₀ ℕ)
    (f : ι → (Rule R →₀ ℕ)) : mul A (s.sum f) = s.sum (fun i => mul A (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, mul_add_right, ih, Finset.sum_insert hi]

private theorem nat_smul_single_one_rule {α : Type*} (c : ℕ) (a : α) :
    c • Finsupp.single a (1 : ℕ) = Finsupp.single a c := by
  ext x
  by_cases h : a = x <;> simp [h]

theorem mul_id_left (A : Rule R →₀ ℕ) :
    mul (Finsupp.single Rule.id 1) A = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mul_add_right, hx, hy]) ?_
  intro r c
  rw [mul_smul_single_single, compose_id_left, Nat.one_mul, nat_smul_single_one_rule]

theorem mul_id_right (A : Rule R →₀ ℕ) :
    mul A (Finsupp.single Rule.id 1) = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mul_add_left, hx, hy]) ?_
  intro r c
  rw [mul_smul_single_single, compose_id_right, Nat.mul_one, nat_smul_single_one_rule]

private theorem mul1_apply_left_single (A : SingleRule →₀ ℕ) (r₁ s : SingleRule) :
    (mul1 A (Finsupp.single r₁ 1)) s =
      ∑ r₂ ∈ A.support, A r₂ * compose1 r₂ r₁ s := by
  unfold mul1
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun r₂ _ => ?_
  simp

private theorem mul1_apply_right_single (r₃ : SingleRule) (B : SingleRule →₀ ℕ) (s : SingleRule) :
    (mul1 (Finsupp.single r₃ 1) B) s =
      ∑ r₂ ∈ B.support, B r₂ * compose1 r₃ r₂ s := by
  unfold mul1
  rw [Finsupp.sum_single_index (by simp)]
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun r₂ _ => ?_
  simp

private theorem mul_compose_single_assoc (r₃ r₂ r₁ : Rule R) :
    mul (compose r₃ r₂) (Finsupp.single r₁ 1) =
      mul (Finsupp.single r₃ 1) (compose r₂ r₁) := by
  ext r
  let T := r₃.support ∪ r₂.support ∪ r₁.support ∪ r.support
  have hT₃ : r₃.support ⊆ T :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hT₂ : r₂.support ⊆ T :=
    Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hT₁ : r₁.support ⊆ T :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hTr : r.support ⊆ T := Finset.subset_union_right
  -- Left-hand side via `tensorRules T F₂₃` and `Finset.prod_sum`
  let F₂₃ : R → (SingleRule →₀ ℕ) := fun a => compose1 (r₃.atSpecies a) (r₂.atSpecies a)
  have hLHS_tensor : compose r₃ r₂ = tensorRules T F₂₃ :=
    tensorRules_subset (compose1_outside_union r₃ r₂) (Finset.union_subset hT₃ hT₂)
  have hLHS : (mul (compose r₃ r₂) (Finsupp.single r₁ 1)) r =
      ∏ a ∈ T, (mul1 (F₂₃ a) (Finsupp.single (r₁.atSpecies a) 1)) (r.atSpecies a) := by
    rw [hLHS_tensor]
    unfold tensorRules
    rw [mul_finset_sum_left, Finsupp.finsetSum_apply]
    have hterm : ∀ g ∈ T.pi (fun a => (F₂₃ a).support),
        (mul (Finsupp.single (ruleOfPi T g) (∏ x ∈ T.attach, F₂₃ x.1 (g x.1 x.2)))
          (Finsupp.single r₁ 1)) r =
          ∏ x ∈ T.attach, (F₂₃ x.1 (g x.1 x.2) *
            compose1 (g x.1 x.2) (r₁.atSpecies x.1) (r.atSpecies x.1)) := by
      intro g _
      rw [mul_smul_single_single, Nat.mul_one, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      have hsupp : (ruleOfPi T g).support ∪ r₁.support ∪ r.support ⊆ T :=
        Finset.union_subset (Finset.union_subset (ruleOfPi_support_subset T g) hT₁) hTr
      rw [compose_apply (ruleOfPi T g) r₁ r hsupp,
        ← Finset.prod_attach T (fun a =>
          compose1 ((ruleOfPi T g).atSpecies a) (r₁.atSpecies a) (r.atSpecies a)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [ruleOfPi_atSpecies_of_mem x.2]
    rw [Finset.sum_congr rfl hterm,
      ← Finset.prod_sum T (fun a => (F₂₃ a).support)
        (fun a s => F₂₃ a s * compose1 s (r₁.atSpecies a) (r.atSpecies a))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [mul1_apply_left_single]
  -- Right-hand side via `tensorRules T F₁₂` and `Finset.prod_sum`
  let F₁₂ : R → (SingleRule →₀ ℕ) := fun a => compose1 (r₂.atSpecies a) (r₁.atSpecies a)
  have hRHS_tensor : compose r₂ r₁ = tensorRules T F₁₂ :=
    tensorRules_subset (compose1_outside_union r₂ r₁) (Finset.union_subset hT₂ hT₁)
  have hRHS : (mul (Finsupp.single r₃ 1) (compose r₂ r₁)) r =
      ∏ a ∈ T, (mul1 (Finsupp.single (r₃.atSpecies a) 1) (F₁₂ a)) (r.atSpecies a) := by
    rw [hRHS_tensor]
    unfold tensorRules
    rw [mul_finset_sum_right, Finsupp.finsetSum_apply]
    have hterm : ∀ g ∈ T.pi (fun a => (F₁₂ a).support),
        (mul (Finsupp.single r₃ 1)
          (Finsupp.single (ruleOfPi T g) (∏ x ∈ T.attach, F₁₂ x.1 (g x.1 x.2)))) r =
          ∏ x ∈ T.attach, (F₁₂ x.1 (g x.1 x.2) *
            compose1 (r₃.atSpecies x.1) (g x.1 x.2) (r.atSpecies x.1)) := by
      intro g _
      rw [mul_smul_single_single, Nat.one_mul, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      have hsupp : r₃.support ∪ (ruleOfPi T g).support ∪ r.support ⊆ T :=
        Finset.union_subset (Finset.union_subset hT₃ (ruleOfPi_support_subset T g)) hTr
      rw [compose_apply r₃ (ruleOfPi T g) r hsupp,
        ← Finset.prod_attach T (fun a =>
          compose1 (r₃.atSpecies a) ((ruleOfPi T g).atSpecies a) (r.atSpecies a)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [ruleOfPi_atSpecies_of_mem x.2]
    rw [Finset.sum_congr rfl hterm,
      ← Finset.prod_sum T (fun a => (F₁₂ a).support)
        (fun a s => F₁₂ a s * compose1 (r₃.atSpecies a) s (r.atSpecies a))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [mul1_apply_right_single]
  rw [hLHS, hRHS]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only [F₂₃, F₁₂]
  rw [← mul1_single_single (r₃.atSpecies a) (r₂.atSpecies a),
    ← mul1_single_single (r₂.atSpecies a) (r₁.atSpecies a), mul1_assoc]

/-- **Associativity of multi-species Behr–Krivine rule composition** over any species
type `R` with `[DecidableEq R]`. -/
theorem mul_assoc (A B C : Rule R →₀ ℕ) :
    mul (mul A B) C = mul A (mul B C) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₃ c₃ => ?_)
  · rw [mul_add_left, mul_add_left, mul_add_left, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
    · rw [mul_add_right, mul_add_left, mul_add_left, mul_add_right, hx, hy]
    · refine Finsupp.induction_linear C (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
      · rw [mul_add_right, mul_add_right, mul_add_right, hx, hy]
      · rw [← nat_smul_single_one_rule c₃ r₃, ← nat_smul_single_one_rule c₂ r₂,
          ← nat_smul_single_one_rule c₁ r₁]
        simp only [mul_smul_left, mul_smul_right, smul_smul, mul_single_single]
        rw [mul_compose_single_assoc]
        congr 1; ring

end Tensor

/-- Multi-species Behr–Krivine rule algebra over `ℕ`. -/
def MultiRuleAlgebra (R : Type*) := Rule R →₀ ℕ

namespace MultiRuleAlgebra

variable {R : Type*} [DecidableEq R]

noncomputable instance : AddCommMonoid (MultiRuleAlgebra R) :=
  inferInstanceAs (AddCommMonoid (Rule R →₀ ℕ))

/-- Basis element `[r]` in `MultiRuleAlgebra R`. -/
noncomputable def ofRule (r : Rule R) : MultiRuleAlgebra R :=
  Finsupp.single r 1

noncomputable instance : Semiring (MultiRuleAlgebra R) where
  mul := mul
  mul_assoc := mul_assoc
  one := Finsupp.single Rule.id 1
  one_mul := mul_id_left
  mul_one := mul_id_right
  zero_mul := mul_zero_left
  mul_zero := mul_zero_right
  left_distrib := mul_add_right
  right_distrib := mul_add_left
  nsmul := (· • ·)
  nsmul_zero := fun _ => zero_smul ℕ _
  nsmul_succ := fun n x => succ_nsmul x n

end MultiRuleAlgebra

/-! ## Signed Z-set rule operator ring (`SignedRuleAlgebra R`) and Lie commutator -/

/-- Canonical coefficient embedding `(α →₀ ℕ) → (α →₀ ℤ)`. -/
noncomputable def castFinsuppInt {α : Type*} (f : α →₀ ℕ) : α →₀ ℤ :=
  f.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero

@[simp]
theorem castFinsuppInt_apply {α : Type*} (f : α →₀ ℕ) (a : α) :
    castFinsuppInt f a = (f a : ℤ) := rfl

@[simp]
theorem castFinsuppInt_zero {α : Type*} :
    castFinsuppInt (0 : α →₀ ℕ) = 0 := by ext; simp

theorem castFinsuppInt_add {α : Type*} (f g : α →₀ ℕ) :
    castFinsuppInt (f + g) = castFinsuppInt f + castFinsuppInt g := by ext; simp

theorem castFinsuppInt_smul {α : Type*} (c : ℕ) (f : α →₀ ℕ) :
    castFinsuppInt (c • f) = (c : ℤ) • castFinsuppInt f := by ext; simp

@[simp]
theorem castFinsuppInt_single {α : Type*} (a : α) (n : ℕ) :
    castFinsuppInt (Finsupp.single a n) = Finsupp.single a (n : ℤ) := by
  ext x
  by_cases h : a = x <;> simp [h]

section Signed

variable {R : Type*} [DecidableEq R]

/-- `ℤ`-valued Behr–Krivine composition `r₂ ⋆_ℤ r₁`. -/
noncomputable def composeZ (r₂ r₁ : Rule R) : Rule R →₀ ℤ :=
  castFinsuppInt (compose r₂ r₁)

/-- `ℤ`-bilinear Behr–Krivine multiplication on `Rule R →₀ ℤ`. -/
noncomputable def mulZ (A B : Rule R →₀ ℤ) : Rule R →₀ ℤ :=
  A.sum fun r₂ c₂ => B.sum fun r₁ c₁ => (c₂ * c₁) • composeZ r₂ r₁

@[simp]
theorem mulZ_zero_left (B : Rule R →₀ ℤ) : mulZ 0 B = 0 := by simp [mulZ]

@[simp]
theorem mulZ_zero_right (A : Rule R →₀ ℤ) : mulZ A 0 = 0 := by simp [mulZ]

theorem mulZ_add_left (A₁ A₂ B : Rule R →₀ ℤ) :
    mulZ (A₁ + A₂) B = mulZ A₁ B + mulZ A₂ B := by
  unfold mulZ
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₂ a₁ a₂
    rw [← Finsupp.sum_add]
    congr 1; ext r₁ c₁
    rw [add_mul, add_smul]

theorem mulZ_add_right (A B₁ B₂ : Rule R →₀ ℤ) :
    mulZ A (B₁ + B₂) = mulZ A B₁ + mulZ A B₂ := by
  unfold mulZ
  rw [← Finsupp.sum_add]
  congr 1; ext r₂ c₂
  rw [Finsupp.sum_add_index']
  · intro _; simp
  · intro r₁ b₁ b₂
    rw [mul_add, add_smul]

theorem mulZ_smul_single_single (c₂ c₁ : ℤ) (r₂ r₁ : Rule R) :
    mulZ (Finsupp.single r₂ c₂) (Finsupp.single r₁ c₁) = (c₂ * c₁) • composeZ r₂ r₁ := by
  simp [mulZ]

theorem mulZ_single_single (r₂ r₁ : Rule R) :
    mulZ (Finsupp.single r₂ 1) (Finsupp.single r₁ 1) = composeZ r₂ r₁ := by
  simp [mulZ]

theorem mulZ_smul_left (c : ℤ) (A B : Rule R →₀ ℤ) :
    mulZ (c • A) B = c • mulZ A B := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r k => ?_)
  · rw [smul_add, mulZ_add_left, hx, hy, mulZ_add_left, smul_add]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r' k' => ?_)
    · rw [mulZ_add_right, mulZ_add_right, hx, hy, smul_add]
    · rw [Finsupp.smul_single, smul_eq_mul, mulZ_smul_single_single, mulZ_smul_single_single]
      ext x; simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

theorem mulZ_smul_right (c : ℤ) (A B : Rule R →₀ ℤ) :
    mulZ A (c • B) = c • mulZ A B := by
  refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r' k' => ?_)
  · rw [smul_add, mulZ_add_right, hx, hy, mulZ_add_right, smul_add]
  · refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r k => ?_)
    · rw [mulZ_add_left, mulZ_add_left, hx, hy, smul_add]
    · rw [Finsupp.smul_single, smul_eq_mul, mulZ_smul_single_single, mulZ_smul_single_single]
      ext x; simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]; ring

private theorem int_smul_single_one_rule {α : Type*} (c : ℤ) (a : α) :
    c • Finsupp.single a (1 : ℤ) = Finsupp.single a c := by
  ext x
  by_cases h : a = x <;> simp [h]

theorem mulZ_cast (A B : Rule R →₀ ℕ) :
    mulZ (castFinsuppInt A) (castFinsuppInt B) = castFinsuppInt (mul A B) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
  · rw [castFinsuppInt_add, mulZ_add_left, mul_add_left, castFinsuppInt_add, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
    · rw [castFinsuppInt_add, mulZ_add_right, mul_add_right, castFinsuppInt_add, hx, hy]
    · rw [castFinsuppInt_single, castFinsuppInt_single, mulZ_smul_single_single,
        mul_smul_single_single, castFinsuppInt_smul, Nat.cast_mul, composeZ]

theorem mulZ_id_left (A : Rule R →₀ ℤ) :
    mulZ (Finsupp.single Rule.id 1) A = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mulZ_add_right, hx, hy]) ?_
  intro r c
  rw [mulZ_smul_single_single, one_mul, composeZ, compose_id_left, castFinsuppInt_single,
    Nat.cast_one, int_smul_single_one_rule]

theorem mulZ_id_right (A : Rule R →₀ ℤ) :
    mulZ A (Finsupp.single Rule.id 1) = A := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => by rw [mulZ_add_left, hx, hy]) ?_
  intro r c
  rw [mulZ_smul_single_single, mul_one, composeZ, compose_id_right, castFinsuppInt_single,
    Nat.cast_one, int_smul_single_one_rule]

theorem mulZ_assoc (A B C : Rule R →₀ ℤ) :
    mulZ (mulZ A B) C = mulZ A (mulZ B C) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₃ c₃ => ?_)
  · rw [mulZ_add_left, mulZ_add_left, mulZ_add_left, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
    · rw [mulZ_add_right, mulZ_add_left, mulZ_add_left, mulZ_add_right, hx, hy]
    · refine Finsupp.induction_linear C (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
      · rw [mulZ_add_right, mulZ_add_right, mulZ_add_right, hx, hy]
      · rw [← int_smul_single_one_rule c₃ r₃, ← int_smul_single_one_rule c₂ r₂,
          ← int_smul_single_one_rule c₁ r₁]
        simp only [mulZ_smul_left, mulZ_smul_right, smul_smul]
        have hcoeff : c₁ * (c₂ * c₃) = c₁ * c₂ * c₃ := by ring
        rw [hcoeff]
        congr 1
        have h1 : (Finsupp.single r₃ (1 : ℤ)) = castFinsuppInt (Finsupp.single r₃ 1) := by simp
        have h2 : (Finsupp.single r₂ (1 : ℤ)) = castFinsuppInt (Finsupp.single r₂ 1) := by simp
        have h3 : (Finsupp.single r₁ (1 : ℤ)) = castFinsuppInt (Finsupp.single r₁ 1) := by simp
        rw [h1, h2, h3, mulZ_cast, mulZ_cast, mulZ_cast, mulZ_cast, mul_assoc]

end Signed

/-- Signed `ℤ`-linear rule algebra (`Rule R →₀ ℤ`), serving as the operator ring over
Z-set / signed-bag states and hosting the Behr–Krivine Lie commutator. -/
def SignedRuleAlgebra (R : Type*) := Rule R →₀ ℤ

namespace SignedRuleAlgebra

variable {R : Type*} [DecidableEq R]

noncomputable instance : AddCommGroup (SignedRuleAlgebra R) :=
  inferInstanceAs (AddCommGroup (Rule R →₀ ℤ))

noncomputable instance : Ring (SignedRuleAlgebra R) where
  __ := (inferInstance : AddCommGroup (SignedRuleAlgebra R))
  mul := mulZ
  mul_assoc := mulZ_assoc
  one := Finsupp.single Rule.id 1
  one_mul := mulZ_id_left
  mul_one := mulZ_id_right
  zero_mul := mulZ_zero_left
  mul_zero := mulZ_zero_right
  left_distrib := mulZ_add_right
  right_distrib := mulZ_add_left

/-- Basis element `[r]` in `SignedRuleAlgebra R`. -/
noncomputable def ofRule (r : Rule R) : SignedRuleAlgebra R :=
  Finsupp.single r 1

/-- Lie commutator `[A, B]_⋆ = A * B - B * A` in `SignedRuleAlgebra R`. -/
noncomputable def commutator (A B : SignedRuleAlgebra R) : SignedRuleAlgebra R :=
  A * B - B * A

@[simp]
theorem commutator_self (A : SignedRuleAlgebra R) : commutator A A = 0 :=
  sub_self (A * A)

theorem commutator_add_right (A B₁ B₂ : SignedRuleAlgebra R) :
    commutator A (B₁ + B₂) = commutator A B₁ + commutator A B₂ := by
  unfold commutator
  rw [_root_.mul_add, _root_.add_mul]
  abel

theorem commutator_add_left (A₁ A₂ B : SignedRuleAlgebra R) :
    commutator (A₁ + A₂) B = commutator A₁ B + commutator A₂ B := by
  unfold commutator
  rw [_root_.add_mul, _root_.mul_add]
  abel

theorem commutator_ofRule_eq_zero_of_disjoint {r₂ r₁ : Rule R}
    (hdisj : Disjoint r₂.support r₁.support) :
    commutator (ofRule r₂) (ofRule r₁) = 0 := by
  change mulZ (Finsupp.single r₂ 1) (Finsupp.single r₁ 1) -
    mulZ (Finsupp.single r₁ 1) (Finsupp.single r₂ 1) = 0
  rw [mulZ_single_single, mulZ_single_single, composeZ, composeZ,
    compose_comm_of_disjoint_support hdisj, sub_self]

end SignedRuleAlgebra

/-! ## Multi-species uncolored bag (`rho`) and Z-set (`rhoZ`) representations -/

section BagRepresentation

variable {R : Type*} [DecidableEq R]

/-- Action of a single multi-species rule `r` on a bag basis ket `|X⟩`. -/
noncomputable def rhoRule (r : Rule R) (X : R →₀ ℕ) : (R →₀ ℕ) →₀ ℕ :=
  Finsupp.single (r.nextBag X) (r.matchesBag X)

/-- Tensor-product factorization of `(rhoRule r X) Y` into single-species `rhoRule1` matrix entries. -/
theorem rhoRule_apply_eq_prod (r : Rule R) (X Y : R →₀ ℕ) {T : Finset R}
    (hT : r.support ∪ X.support ∪ Y.support ⊆ T) :
    rhoRule r X Y = ∏ a ∈ T, rhoRule1 (r.atSpecies a) (X a) (Y a) := by
  have hrT : r.support ⊆ T :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans hT)
  have hXT : X.support ⊆ T :=
    Finset.subset_union_right.trans (Finset.subset_union_left.trans hT)
  have hYT : Y.support ⊆ T := Finset.subset_union_right.trans hT
  unfold rhoRule
  by_cases hEq : r.nextBag X = Y
  · subst hEq
    rw [Finsupp.single_eq_same, r.matchesBag_eq_prod X hrT]
    refine Finset.prod_congr rfl fun a _ => ?_
    unfold rhoRule1
    have hstep : X a - (r.atSpecies a).take + (r.atSpecies a).make = r.nextBag X a := by
      simp [Rule.atSpecies]
    rw [hstep, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne (Ne.symm hEq)]
    have hex : ∃ a ∈ T, r.nextBag X a ≠ Y a := by
      by_contra hfor
      apply hEq
      ext a
      by_cases haT : a ∈ T
      · exact Classical.not_not.mp fun hne => hfor ⟨a, haT, hne⟩
      · have hXa : X a = 0 := Finsupp.notMem_support_iff.mp (fun hm => haT (hXT hm))
        have hYa : Y a = 0 := Finsupp.notMem_support_iff.mp (fun hm => haT (hYT hm))
        have hra : r.atSpecies a = SingleRule.id :=
          Rule.atSpecies_eq_id_of_notMem_support (fun hm => haT (hrT hm))
        have hma : r.make a = 0 := congrArg SingleRule.make hra
        rw [Rule.nextBag_apply, hXa, hma, hYa]
        simp
    rcases hex with ⟨a₀, ha₀T, hne⟩
    refine (Finset.prod_eq_zero ha₀T ?_).symm
    unfold rhoRule1
    have hne' : Y a₀ ≠ X a₀ - (r.atSpecies a₀).take + (r.atSpecies a₀).make := by
      intro h
      exact hne (by simpa [Rule.atSpecies] using h.symm)
    exact Finsupp.single_eq_of_ne hne'

/-- Linear representation `ρ` of `Rule R →₀ ℕ` on multi-species bag states `(R →₀ ℕ) →₀ ℕ`. -/
noncomputable def rho (A : Rule R →₀ ℕ) : ((R →₀ ℕ) →₀ ℕ) →ₗ[ℕ] ((R →₀ ℕ) →₀ ℕ) :=
  A.sum fun r c => c • Finsupp.lsum ℕ (fun X =>
    (Finsupp.lsingle (r.nextBag X)).comp (LinearMap.mulLeft ℕ (r.matchesBag X)))

@[simp]
theorem rho_zero : rho (0 : Rule R →₀ ℕ) = 0 := by simp [rho]

theorem rho_add (A B : Rule R →₀ ℕ) : rho (A + B) = rho A + rho B := by
  unfold rho
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]

theorem rho_smul (c : ℕ) (A : Rule R →₀ ℕ) : rho (c • A) = c • rho A := by
  unfold rho
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext r
  rw [smul_eq_mul, mul_smul]

theorem rho_single_apply (r : Rule R) (X : R →₀ ℕ) :
    rho (Finsupp.single r 1) (Finsupp.single X 1) = rhoRule r X := by
  simp [rho, rhoRule]

private theorem rho_finset_sum_apply {ι : Type*} (s : Finset ι) (f : ι → (Rule R →₀ ℕ))
    (v : (R →₀ ℕ) →₀ ℕ) :
    rho (s.sum f) v = s.sum (fun i => rho (f i) v) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, rho_add, LinearMap.add_apply, ih, Finset.sum_insert hi]

private theorem rho1_apply_single (A : SingleRule →₀ ℕ) (x y : ℕ) :
    (rho1 A (Finsupp.single x 1)) y = ∑ s ∈ A.support, A s * rhoRule1 s x y := by
  unfold rho1
  rw [LinearMap.finsupp_sum_apply, Finsupp.sum_apply]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [rhoRule1]
  simp
  by_cases hy : x - s.take + s.make = y <;> simp [hy]

private theorem rho_compose_apply (r₂ r₁ : Rule R) (X : R →₀ ℕ) :
    rho (compose r₂ r₁) (Finsupp.single X 1) =
      rho (Finsupp.single r₂ 1) (rho (Finsupp.single r₁ 1) (Finsupp.single X 1)) := by
  ext Y
  let T := r₂.support ∪ r₁.support ∪ X.support ∪ Y.support
  have hT₂ : r₂.support ⊆ T :=
    Finset.subset_union_left.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hT₁ : r₁.support ⊆ T :=
    Finset.subset_union_right.trans (Finset.subset_union_left.trans Finset.subset_union_left)
  have hTX : X.support ⊆ T :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hTY : Y.support ⊆ T := Finset.subset_union_right
  -- Left-hand side via `tensorRules T F` and `Finset.prod_sum`
  let F : R → (SingleRule →₀ ℕ) := fun a => compose1 (r₂.atSpecies a) (r₁.atSpecies a)
  have htensor : compose r₂ r₁ = tensorRules T F :=
    tensorRules_subset (compose1_outside_union r₂ r₁) (Finset.union_subset hT₂ hT₁)
  have hLHS : (rho (compose r₂ r₁) (Finsupp.single X 1)) Y =
      ∏ a ∈ T, (rho1 (F a) (Finsupp.single (X a) 1)) (Y a) := by
    rw [htensor]
    unfold tensorRules
    rw [rho_finset_sum_apply, Finsupp.finsetSum_apply]
    have hterm : ∀ g ∈ T.pi (fun a => (F a).support),
        (rho (Finsupp.single (ruleOfPi T g) (∏ x ∈ T.attach, F x.1 (g x.1 x.2)))
          (Finsupp.single X 1)) Y =
          ∏ x ∈ T.attach, (F x.1 (g x.1 x.2) * rhoRule1 (g x.1 x.2) (X x.1) (Y x.1)) := by
      intro g _
      rw [← nat_smul_single_one_rule (∏ x ∈ T.attach, F x.1 (g x.1 x.2)) (ruleOfPi T g),
        rho_smul, LinearMap.smul_apply, rho_single_apply, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul]
      have hsupp : (ruleOfPi T g).support ∪ X.support ∪ Y.support ⊆ T :=
        Finset.union_subset (Finset.union_subset (ruleOfPi_support_subset T g) hTX) hTY
      rw [rhoRule_apply_eq_prod (ruleOfPi T g) X Y hsupp,
        ← Finset.prod_attach T (fun a => rhoRule1 ((ruleOfPi T g).atSpecies a) (X a) (Y a)),
        ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun x _ => ?_
      rw [ruleOfPi_atSpecies_of_mem x.2]
    rw [Finset.sum_congr rfl hterm,
      ← Finset.prod_sum T (fun a => (F a).support)
        (fun a s => F a s * rhoRule1 s (X a) (Y a))]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [rho1_apply_single]
  -- Right-hand side via `rhoRule_apply_eq_prod`
  have hRHS : (rho (Finsupp.single r₂ 1) (rho (Finsupp.single r₁ 1) (Finsupp.single X 1))) Y =
      ∏ a ∈ T, ((rho1 (Finsupp.single (r₂.atSpecies a) 1))
        ((rho1 (Finsupp.single (r₁.atSpecies a) 1)) (Finsupp.single (X a) 1))) (Y a) := by
    rw [rho_single_apply]
    unfold rhoRule
    rw [← nat_smul_single_one_rule (r₁.matchesBag X) (r₁.nextBag X), map_smul,
      rho_single_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    have hmake₁ : r₁.make.support ⊆ r₁.support :=
      Finset.subset_union_right.trans Finset.subset_union_left
    have hnextT : (r₁.nextBag X).support ⊆ T :=
      (r₁.nextBag_support_subset X).trans (Finset.union_subset hTX (hmake₁.trans hT₁))
    have hsupp₂ : r₂.support ∪ (r₁.nextBag X).support ∪ Y.support ⊆ T :=
      Finset.union_subset (Finset.union_subset hT₂ hnextT) hTY
    rw [r₁.matchesBag_eq_prod X hT₁, rhoRule_apply_eq_prod r₂ (r₁.nextBag X) Y hsupp₂,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [rho1_single_apply]
    unfold rhoRule1
    rw [← nat_smul_single_one_rule ((r₁.atSpecies a).matchesCount (X a))
      (X a - (r₁.atSpecies a).take + (r₁.atSpecies a).make),
      map_smul, rho1_single_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
    simp [Rule.atSpecies, rhoRule1]
  rw [hLHS, hRHS]
  refine Finset.prod_congr rfl fun a _ => ?_
  dsimp only [F]
  rw [← mul1_single_single (r₂.atSpecies a) (r₁.atSpecies a), rho1_mul, LinearMap.comp_apply]

/-- **`rho` is an algebra homomorphism**: multi-species Behr–Krivine composition acts
homomorphically on uncolored bag states `(R →₀ ℕ) →₀ ℕ`. -/
theorem rho_mul (A B : Rule R →₀ ℕ) :
    rho (mul A B) = (rho A).comp (rho B) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
  · rw [mul_add_left, rho_add, rho_add, LinearMap.add_comp, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
    · rw [mul_add_right, rho_add, rho_add, LinearMap.comp_add, hx, hy]
    · rw [mul_smul_single_single, rho_smul, ← nat_smul_single_one_rule c₂ r₂,
        ← nat_smul_single_one_rule c₁ r₁, rho_smul, rho_smul, LinearMap.smul_comp,
        LinearMap.comp_smul, smul_smul]
      congr 1
      apply Finsupp.lhom_ext'
      intro X
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      exact rho_compose_apply r₂ r₁ X

/-- Underlying `ℤ`-linear Z-set representation on `Rule R →₀ ℤ`. -/
noncomputable def rhoZAux (A : Rule R →₀ ℤ) : ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  A.sum fun r c => c • Finsupp.lsum ℤ (fun X =>
    (Finsupp.lsingle (r.nextBag X)).comp (LinearMap.mulLeft ℤ (r.matchesBag X : ℤ)))

@[simp]
theorem rhoZAux_zero : rhoZAux (0 : Rule R →₀ ℤ) = 0 := by
  simp [rhoZAux]

theorem rhoZAux_add (A B : Rule R →₀ ℤ) : rhoZAux (A + B) = rhoZAux A + rhoZAux B := by
  unfold rhoZAux
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]

theorem rhoZAux_smul (c : ℤ) (A : Rule R →₀ ℤ) : rhoZAux (c • A) = c • rhoZAux A := by
  unfold rhoZAux
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext r
  rw [smul_eq_mul, mul_smul]

theorem rhoZAux_single_apply (r : Rule R) (X : R →₀ ℕ) :
    rhoZAux (Finsupp.single r 1) (Finsupp.single X (1 : ℤ)) =
      Finsupp.single (r.nextBag X) (r.matchesBag X : ℤ) := by
  simp [rhoZAux]

theorem rhoZAux_cast_apply (A : Rule R →₀ ℕ) (X : R →₀ ℕ) :
    rhoZAux (castFinsuppInt A) (Finsupp.single X (1 : ℤ)) =
      castFinsuppInt (rho A (Finsupp.single X 1)) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r c => ?_)
  · rw [castFinsuppInt_add, rhoZAux_add, rho_add, LinearMap.add_apply, LinearMap.add_apply,
      castFinsuppInt_add, hx, hy]
  · rw [← nat_smul_single_one_rule c r, castFinsuppInt_smul, rhoZAux_smul, rho_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, castFinsuppInt_smul, castFinsuppInt_single,
      Nat.cast_one]
    congr 1
    rw [rho_single_apply, rhoRule, castFinsuppInt_single]
    exact rhoZAux_single_apply r X

theorem rhoZAux_mul (A B : Rule R →₀ ℤ) :
    rhoZAux (mulZ A B) = (rhoZAux A).comp (rhoZAux B) := by
  refine Finsupp.induction_linear A (by simp) (fun x y hx hy => ?_) (fun r₂ c₂ => ?_)
  · rw [mulZ_add_left, rhoZAux_add, rhoZAux_add, LinearMap.add_comp, hx, hy]
  · refine Finsupp.induction_linear B (by simp) (fun x y hx hy => ?_) (fun r₁ c₁ => ?_)
    · rw [mulZ_add_right, rhoZAux_add, rhoZAux_add, LinearMap.comp_add, hx, hy]
    · rw [mulZ_smul_single_single, rhoZAux_smul, ← int_smul_single_one_rule c₂ r₂,
        ← int_smul_single_one_rule c₁ r₁, rhoZAux_smul, rhoZAux_smul, LinearMap.smul_comp,
        LinearMap.comp_smul, smul_smul]
      congr 1
      apply Finsupp.lhom_ext'
      intro X
      apply LinearMap.ext_ring
      simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
      unfold composeZ
      rw [rhoZAux_cast_apply]
      have h1 := rho_compose_apply r₂ r₁ X
      rw [h1, rho_single_apply]
      unfold rhoRule
      rw [← nat_smul_single_one_rule (r₁.matchesBag X) (r₁.nextBag X), map_smul,
        rho_single_apply, castFinsuppInt_smul]
      unfold rhoRule
      rw [castFinsuppInt_single]
      have hstep : rhoZAux (Finsupp.single r₁ (1 : ℤ)) (Finsupp.single X (1 : ℤ)) =
          (r₁.matchesBag X : ℤ) • Finsupp.single (r₁.nextBag X) (1 : ℤ) := by
        rw [int_smul_single_one_rule]
        exact rhoZAux_single_apply r₁ X
      rw [hstep, map_smul]
      congr 1
      exact (rhoZAux_single_apply r₂ (r₁.nextBag X)).symm

theorem rhoZAux_neg (A : Rule R →₀ ℤ) : rhoZAux (-A) = -rhoZAux A := by
  rw [show -A = (-1 : ℤ) • A by simp, rhoZAux_smul, neg_one_smul]

/-- Signed Z-set representation `ρ_ℤ` of `SignedRuleAlgebra R` on `(R →₀ ℕ) →₀ ℤ`. -/
noncomputable def rhoZ (A : SignedRuleAlgebra R) : ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  rhoZAux A

@[simp]
theorem rhoZ_zero : rhoZ (0 : SignedRuleAlgebra R) = 0 := rhoZAux_zero

theorem rhoZ_add (A B : SignedRuleAlgebra R) : rhoZ (A + B) = rhoZ A + rhoZ B :=
  rhoZAux_add A B

theorem rhoZ_neg (A : SignedRuleAlgebra R) : rhoZ (-A) = -rhoZ A :=
  rhoZAux_neg A

theorem rhoZ_sub (A B : SignedRuleAlgebra R) : rhoZ (A - B) = rhoZ A - rhoZ B := by
  rw [sub_eq_add_neg, rhoZ_add, rhoZ_neg, ← sub_eq_add_neg]

theorem rhoZ_smul (c : ℤ) (A : SignedRuleAlgebra R) : rhoZ (c • A) = c • rhoZ A :=
  rhoZAux_smul c A

theorem rhoZ_single_apply (r : Rule R) (X : R →₀ ℕ) :
    rhoZ (SignedRuleAlgebra.ofRule r) (Finsupp.single X (1 : ℤ)) =
      Finsupp.single (r.nextBag X) (r.matchesBag X : ℤ) :=
  rhoZAux_single_apply r X

/-- **`rhoZ` is a ring homomorphism**: `SignedRuleAlgebra R` acts homomorphically on
signed Z-set bag distributions `(R →₀ ℕ) →₀ ℤ`. -/
theorem rhoZ_mul (A B : SignedRuleAlgebra R) :
    rhoZ (A * B) = (rhoZ A).comp (rhoZ B) :=
  rhoZAux_mul A B

@[simp]
theorem rhoZ_one : rhoZ (1 : SignedRuleAlgebra R) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, LinearMap.id_apply, Finsupp.lsingle_apply]
  change rhoZ (SignedRuleAlgebra.ofRule Rule.id) (Finsupp.single X 1) = _
  rw [rhoZ_single_apply, Rule.id_nextBag, Rule.id_matchesBag, Nat.cast_one]

theorem rhoZ_commutator (A B : SignedRuleAlgebra R) :
    rhoZ (SignedRuleAlgebra.commutator A B) =
      (rhoZ A).comp (rhoZ B) - (rhoZ B).comp (rhoZ A) := by
  unfold SignedRuleAlgebra.commutator
  rw [rhoZ_sub, rhoZ_mul, rhoZ_mul]

end BagRepresentation

/-! ## Positive & Negative Controls -/

section Controls

/-- **Negative Control 1 (Uncolored bag representation is NOT faithful)**:
At any species `a : R`, `[take a, make a]` (churn: consume one `a` and mint a fresh `a`)
and `[keep a]` (read: inspect one surviving `a`) are distinct elements of
`MultiRuleAlgebra R`, yet induce the **exact same** linear operator under `rho` on all
uncolored multi-species bag states `(R →₀ ℕ) →₀ ℕ`! (By contrast, `occRho1_injective` in
`SingleSpecies.lean` proves that the 3-color surviving-vs-minted representation separates them.) -/
theorem single_churn_ne_keep {R : Type*} [DecidableEq R] (a : R) :
    (Finsupp.single (Rule.ofSingle a ⟨1, 0, 1, false⟩) 1 : Rule R →₀ ℕ) ≠
      Finsupp.single (Rule.ofSingle a ⟨0, 1, 0, false⟩) 1 := by
  intro h
  have h1 : (Finsupp.single (Rule.ofSingle a ⟨1, 0, 1, false⟩) 1 : Rule R →₀ ℕ)
      (Rule.ofSingle a ⟨1, 0, 1, false⟩) = 1 := Finsupp.single_eq_same
  rw [h] at h1
  have hne : Rule.ofSingle a ⟨1, 0, 1, false⟩ ≠ Rule.ofSingle a ⟨0, 1, 0, false⟩ := by
    intro hEq
    have htake := congrArg (fun r => (r.atSpecies a).take) hEq
    rw [Rule.ofSingle_atSpecies_same, Rule.ofSingle_atSpecies_same] at htake
    exact Nat.one_ne_zero htake
  rw [Finsupp.single_eq_of_ne hne] at h1
  exact Nat.one_ne_zero h1.symm

theorem rho_churn_eq_keep {R : Type*} [DecidableEq R] (a : R) :
    rho (Finsupp.single (Rule.ofSingle a ⟨1, 0, 1, false⟩) 1) =
      rho (Finsupp.single (Rule.ofSingle a ⟨0, 1, 0, false⟩) 1) := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rho_single_apply, rhoRule]
  by_cases hX : X a = 0
  · have hm1 : (Rule.ofSingle a ⟨1, 0, 1, false⟩).matchesBag X = 0 := by
      rw [Rule.matchesBag_eq_prod _ X (Rule.ofSingle_support_subset a _), Finset.prod_singleton,
        Rule.ofSingle_atSpecies_same, hX]
      simp [SingleRule.matchesCount]
    have hm2 : (Rule.ofSingle a ⟨0, 1, 0, false⟩).matchesBag X = 0 := by
      rw [Rule.matchesBag_eq_prod _ X (Rule.ofSingle_support_subset a _), Finset.prod_singleton,
        Rule.ofSingle_atSpecies_same, hX]
      simp [SingleRule.matchesCount]
    rw [hm1, hm2, Finsupp.single_zero, Finsupp.single_zero]
  · have hm1 : (Rule.ofSingle a ⟨1, 0, 1, false⟩).matchesBag X = X a := by
      rw [Rule.matchesBag_eq_prod _ X (Rule.ofSingle_support_subset a _), Finset.prod_singleton,
        Rule.ofSingle_atSpecies_same]
      simp [SingleRule.matchesCount]
    have hm2 : (Rule.ofSingle a ⟨0, 1, 0, false⟩).matchesBag X = X a := by
      rw [Rule.matchesBag_eq_prod _ X (Rule.ofSingle_support_subset a _), Finset.prod_singleton,
        Rule.ofSingle_atSpecies_same]
      simp [SingleRule.matchesCount]
    have hnext : (Rule.ofSingle a ⟨1, 0, 1, false⟩).nextBag X =
        (Rule.ofSingle a ⟨0, 1, 0, false⟩).nextBag X := by
      ext b
      by_cases hba : b = a
      · subst hba
        have hpos : 1 ≤ X b := Nat.pos_of_ne_zero hX
        simp only [Rule.nextBag_apply, Rule.ofSingle, Finsupp.single_eq_same]
        omega
      · simp [Rule.nextBag_apply, Rule.ofSingle, hba]
    rw [hm1, hm2, hnext]

/-- **Positive Control 2 (Absence shift via `exhaust`)**:
Composing pure absence `[absent]` (`⟨0, 0, 0, true⟩`) after consumption `[take 1]`
(`⟨1, 0, 0, false⟩`) shifts the absence guard to `[take 1, exhaust = true]`
("consume the unique occurrence, requiring initial count `1`"). -/
theorem compose1_pureAbsent_take :
    compose1 SingleRule.pureAbsent ⟨1, 0, 0, false⟩ =
      Finsupp.single ⟨1, 0, 0, true⟩ 1 := by
  have hcand : Overlap1.candidates SingleRule.pureAbsent ⟨1, 0, 0, false⟩ = {⟨0, 0, 0, 0⟩} := by
    ext ov
    rw [Overlap1.mem_candidates_iff, Finset.mem_singleton]
    rcases ov with ⟨u, v, w, z⟩
    simp only [Overlap1.Valid, SingleRule.pureAbsent, Overlap1.mk.injEq]
    constructor
    · rintro ⟨h1, h2, _, _, _, _⟩; omega
    · rintro ⟨rfl, rfl, rfl, rfl⟩
      refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
      · intro h; cases h
      · intro _; exact ⟨rfl, rfl⟩
  rw [compose1, hcand, Finset.sum_singleton]
  rfl

/-- Naive single-species composition rule that *drops* `r₂`'s absence guard whenever
`r₁.take > 0` (and `r₁.make = 0`) instead of shifting it to `exhaust = true`. -/
noncomputable def naiveDropCompose1 (r₂ r₁ : SingleRule) : SingleRule →₀ ℕ :=
  if r₂.exhaust && decide (r₂.take = 0 ∧ r₂.keep = 0) && decide (r₁.take > 0 ∧ r₁.make = 0) then
    compose1 ⟨r₂.take, r₂.keep, r₂.make, false⟩ r₁
  else
    compose1 r₂ r₁

noncomputable def naiveDropMul1 (A B : SingleRule →₀ ℕ) : SingleRule →₀ ℕ :=
  A.sum fun r₂ c₂ => B.sum fun r₁ c₁ => (c₂ * c₁) • naiveDropCompose1 r₂ r₁

/-- **Negative Control 2 (Naive drop-on-consume absence composition FAILS associativity)**:
For `r₃ = pureAbsent`, `r₂ = [take 1]`, `r₁ = [make 1]`:
* `(r₃ ⋆_naive r₂) ⋆_naive r₁ = [take 1] ⋆ [make 1] = [id] + [take 1, make 1]`,
* `r₃ ⋆_naive (r₂ ⋆_naive r₁) = pureAbsent ⋆ ([id] + [take 1, make 1]) = [pureAbsent]`.
In contrast, `mul1_assoc` holds with `exhaust` shift, where both associations evaluate
to `[pureAbsent]`. -/
theorem naiveDropMul1_not_assoc :
    naiveDropMul1
      (naiveDropMul1 (Finsupp.single SingleRule.pureAbsent 1) (Finsupp.single ⟨1, 0, 0, false⟩ 1))
      (Finsupp.single ⟨0, 0, 1, false⟩ 1) ≠
    naiveDropMul1
      (Finsupp.single SingleRule.pureAbsent 1)
      (naiveDropMul1 (Finsupp.single ⟨1, 0, 0, false⟩ 1) (Finsupp.single ⟨0, 0, 1, false⟩ 1)) := by
  intro hEq
  have h12 : naiveDropCompose1 SingleRule.pureAbsent ⟨1, 0, 0, false⟩ =
      Finsupp.single ⟨1, 0, 0, false⟩ 1 := by
    unfold naiveDropCompose1
    have hcond : (SingleRule.pureAbsent.exhaust &&
        decide (SingleRule.pureAbsent.take = 0 ∧ SingleRule.pureAbsent.keep = 0) &&
        decide ((⟨1, 0, 0, false⟩ : SingleRule).take > 0 ∧
          (⟨1, 0, 0, false⟩ : SingleRule).make = 0)) = true := by
      decide
    rw [if_pos hcond]
    exact compose1_id_left ⟨1, 0, 0, false⟩
  have htake_make : compose1 ⟨1, 0, 0, false⟩ ⟨0, 0, 1, false⟩ =
      Finsupp.single ⟨1, 0, 1, false⟩ 1 + Finsupp.single SingleRule.id 1 := by
    have hcand : Overlap1.candidates ⟨1, 0, 0, false⟩ ⟨0, 0, 1, false⟩ =
        {⟨0, 0, 0, 0⟩, ⟨1, 0, 0, 0⟩} := by
      ext ov
      rw [Overlap1.mem_candidates_iff, Finset.mem_insert, Finset.mem_singleton]
      rcases ov with ⟨u, v, w, z⟩
      simp only [Overlap1.Valid, Overlap1.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4, _, _⟩
        have : u = 0 ∨ u = 1 := by omega
        rcases this with rfl | rfl
        · left; omega
        · right; omega
      · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
          refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
          (intro h; cases h)
    rw [compose1, hcand, Finset.sum_pair (by decide)]
    rfl
  have hLHS : (naiveDropMul1
      (naiveDropMul1 (Finsupp.single SingleRule.pureAbsent 1) (Finsupp.single ⟨1, 0, 0, false⟩ 1))
      (Finsupp.single ⟨0, 0, 1, false⟩ 1)) SingleRule.id = 1 := by
    have hstep1 : naiveDropMul1 (Finsupp.single SingleRule.pureAbsent 1)
        (Finsupp.single ⟨1, 0, 0, false⟩ 1) = Finsupp.single ⟨1, 0, 0, false⟩ 1 := by
      simp [naiveDropMul1, h12]
    rw [hstep1]
    have hstep2 : naiveDropMul1 (Finsupp.single ⟨1, 0, 0, false⟩ 1)
        (Finsupp.single ⟨0, 0, 1, false⟩ 1) =
        compose1 ⟨1, 0, 0, false⟩ ⟨0, 0, 1, false⟩ := by
      simp [naiveDropMul1, naiveDropCompose1]
    rw [hstep2, htake_make, Finsupp.add_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide)]
  have hRHS : (naiveDropMul1
      (Finsupp.single SingleRule.pureAbsent 1)
      (naiveDropMul1 (Finsupp.single ⟨1, 0, 0, false⟩ 1) (Finsupp.single ⟨0, 0, 1, false⟩ 1)))
      SingleRule.id = 0 := by
    have hstep1 : naiveDropMul1 (Finsupp.single ⟨1, 0, 0, false⟩ 1)
        (Finsupp.single ⟨0, 0, 1, false⟩ 1) =
        Finsupp.single ⟨1, 0, 1, false⟩ 1 + Finsupp.single SingleRule.id 1 := by
      simp [naiveDropMul1, naiveDropCompose1, htake_make]
    rw [hstep1]
    have hlin : naiveDropMul1 (Finsupp.single SingleRule.pureAbsent 1)
        (Finsupp.single ⟨1, 0, 1, false⟩ 1 + Finsupp.single SingleRule.id 1) =
        naiveDropCompose1 SingleRule.pureAbsent ⟨1, 0, 1, false⟩ +
          naiveDropCompose1 SingleRule.pureAbsent SingleRule.id := by
      unfold naiveDropMul1
      rw [Finsupp.sum_single_index (by simp),
        Finsupp.sum_add_index' (fun _ => by simp) (fun _ a b => by simp [add_smul])]
      simp
    rw [hlin]
    have hp1 : naiveDropCompose1 SingleRule.pureAbsent ⟨1, 0, 1, false⟩ = 0 := by
      have hf : ¬ ((SingleRule.pureAbsent.exhaust &&
          decide (SingleRule.pureAbsent.take = 0 ∧ SingleRule.pureAbsent.keep = 0) &&
          decide ((⟨1, 0, 1, false⟩ : SingleRule).take > 0 ∧
            (⟨1, 0, 1, false⟩ : SingleRule).make = 0)) = true) := by
        decide
      unfold naiveDropCompose1
      rw [if_neg hf]
      have hemp : Overlap1.candidates SingleRule.pureAbsent ⟨1, 0, 1, false⟩ = ∅ := by
        ext ov
        simp only [Finset.notMem_empty, iff_false, Overlap1.mem_candidates_iff, Overlap1.Valid]
        rintro ⟨_, _, h3, h4, _, h6⟩
        have ⟨hm, _⟩ := h6 rfl
        simp only [SingleRule.pureAbsent] at h3 h4 hm
        omega
      simp [compose1, hemp]
    have hp2 : naiveDropCompose1 SingleRule.pureAbsent SingleRule.id =
        Finsupp.single SingleRule.pureAbsent 1 := by
      have hf : ¬ ((SingleRule.pureAbsent.exhaust &&
          decide (SingleRule.pureAbsent.take = 0 ∧ SingleRule.pureAbsent.keep = 0) &&
          decide (SingleRule.id.take > 0 ∧ SingleRule.id.make = 0)) = true) := by
        decide
      unfold naiveDropCompose1
      rw [if_neg hf]
      exact compose1_id_right SingleRule.pureAbsent
    rw [hp1, hp2, zero_add]
    exact Finsupp.single_eq_of_ne (by decide)
  rw [hEq] at hLHS
  exact Nat.one_ne_zero (hLHS.symm.trans hRHS)

end Controls

end Mettapedia.Algebra.RuleAlgebra
