import Mettapedia.Algebra.RuleAlgebra.MultiSpecies

/-!
# Regional ownership gluing, sealed exhaustion, and frame equivariance (`Q3.3`)

How does the Behr–Krivine rule algebra glue across regional / open-space boundaries
when absence is only locally sealed?

For an owned region (or sealed channel/head set) `Ω : Finset R` and an external
environment bag `E : R →₀ ℕ` disjoint from `Ω` (`Disjoint E.support Ω`):

1. **`matchesBag_frame_iff_exhaust_subset` (Exact Boundary Characterization)**:
   For *every* rule `r : Rule R` whose positive read/consume footprint lies in `Ω`
   (`r.take.support ∪ r.keep.support ⊆ Ω`), external bag framing holds—
   `∀ X E, Disjoint E.support Ω → r.matchesBag (X + E) = r.matchesBag X`—
   **if and only if** `r.exhaust ⊆ Ω`!
   Notably, outbound cross-region transfers (`r.make` outside `Ω`) do **not** break
   framing; unsealed exhaustion (`a ∈ r.exhaust \ Ω`) is the *unique* obstruction.
2. **`rho_comm_shiftBag` & `rhoZ_comm_shiftBagZ` (Operator Frame Equivariance)**:
   Any rule combination `A` satisfying `ReadsWithin Ω` (`take, keep, exhaust ⊆ Ω`,
   arbitrary outbound `make`) commutes with external bag framing `|X⟩ ↦ |X + E⟩`.
3. **`ReadsWithin.of_compose` (Closure under Multi-Step Rule Fusion)**:
   `ReadsWithin Ω` is closed under Behr–Krivine composition `compose r₂ r₁`—even in
   the presence of outbound cross-region `make` emissions!
4. **`commutator_eq_zero_of_disjoint_regions` (Independent Regional Execution)**:
   Rule combinations fully supported in disjoint regions `Disjoint Ω₁ Ω₂` commute
   on the nose (`A * B = B * A`, `[A, B]_⋆ = 0`).
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RuleAlgebra

open scoped BigOperators

section Ownership

variable {R : Type*} [DecidableEq R]

namespace Rule

/-- A rule `r` *reads within* region `Ω` when it only consumes (`take`), inspects
(`keep`), and checks zero-residual exhaustion (`exhaust`) inside `Ω`.
Outbound message emissions (`r.make` outside `Ω`) are permitted! -/
def ReadsWithin (Ω : Finset R) (r : Rule R) : Prop :=
  r.take.support ⊆ Ω ∧ r.keep.support ⊆ Ω ∧ r.exhaust ⊆ Ω

theorem readsWithin_of_support_subset {Ω : Finset R} {r : Rule R} (h : r.support ⊆ Ω) :
    r.ReadsWithin Ω := by
  refine ⟨?_, ?_, ?_⟩
  · exact (Finset.subset_union_left.trans
      (Finset.subset_union_left.trans Finset.subset_union_left)).trans h
  · exact (Finset.subset_union_right.trans
      (Finset.subset_union_left.trans Finset.subset_union_left)).trans h
  · exact Finset.subset_union_right.trans h

theorem atSpecies_outside_readsWithin {Ω : Finset R} {r : Rule R}
    (hr : r.ReadsWithin Ω) {a : R} (ha : a ∉ Ω) :
    r.atSpecies a = ⟨0, 0, r.make a, false⟩ := by
  rcases hr with ⟨ht, hk, he⟩
  have hta : r.take a = 0 := Finsupp.notMem_support_iff.mp (fun hm => ha (ht hm))
  have hka : r.keep a = 0 := Finsupp.notMem_support_iff.mp (fun hm => ha (hk hm))
  have hea : a ∉ r.exhaust := fun hm => ha (he hm)
  simp [atSpecies, hta, hka, hea]

/-- Every rule `r : Rule R` has at least one match on its minimal witness bag `r.take + r.keep`. -/
theorem matchesBag_minimal_pos (r : Rule R) :
    0 < r.matchesBag (r.take + r.keep) := by
  unfold matchesBag
  apply Finset.prod_pos
  intro a _
  simp [atSpecies, SingleRule.matchesCount]
  exact Nat.choose_pos (Nat.le_add_right (r.take a) (r.keep a))

/-- Positive framing of `matchesBag`: if `r.ReadsWithin Ω`, adding any external bag `E`
disjoint from `Ω` leaves `r.matchesBag` unchanged (even if `r.make` emits outside `Ω`). -/
theorem matchesBag_frame_of_readsWithin {Ω : Finset R} {r : Rule R}
    (hr : r.ReadsWithin Ω) (X E : R →₀ ℕ) (hE : Disjoint E.support Ω) :
    r.matchesBag (X + E) = r.matchesBag X := by
  let T := Ω ∪ r.support
  have hrT : r.support ⊆ T := Finset.subset_union_right
  rw [r.matchesBag_eq_prod (X + E) hrT, r.matchesBag_eq_prod X hrT]
  refine Finset.prod_congr rfl fun a _ => ?_
  by_cases haΩ : a ∈ Ω
  · have hEa : E a = 0 :=
      Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hE haΩ)
    simp [hEa]
  · rw [r.atSpecies_outside_readsWithin hr haΩ]
    simp [SingleRule.matchesCount]

/-- **Exact Boundary Characterization (`Q3.3`)**:
For any rule `r` whose positive read/consume footprint lies in `Ω`
(`r.take.support ∪ r.keep.support ⊆ Ω`), `r.matchesBag` is invariant under arbitrary
external bags `E` outside `Ω` **if and only if** `r.exhaust ⊆ Ω`. -/
theorem matchesBag_frame_iff_exhaust_subset {Ω : Finset R} {r : Rule R}
    (hpos : r.take.support ∪ r.keep.support ⊆ Ω) :
    (∀ (X E : R →₀ ℕ), Disjoint E.support Ω → r.matchesBag (X + E) = r.matchesBag X) ↔
      r.exhaust ⊆ Ω := by
  constructor
  · intro hframe a₀ ha₀_ex
    by_contra ha₀_notΩ
    let X₀ : R →₀ ℕ := r.take + r.keep
    let E₀ : R →₀ ℕ := Finsupp.single a₀ 1
    have hE₀_disj : Disjoint E₀.support Ω := by
      refine Finset.disjoint_left.mpr fun b hb => ?_
      have hb_eq : b = a₀ := Finset.mem_singleton.mp (Finsupp.support_single_subset hb)
      subst hb_eq
      exact ha₀_notΩ
    have hEq := hframe X₀ E₀ hE₀_disj
    have hpos₀ : 0 < r.matchesBag X₀ := r.matchesBag_minimal_pos
    have ha₀_supp : a₀ ∈ r.support :=
      Finset.mem_union_right _ ha₀_ex
    have hzero : r.matchesBag (X₀ + E₀) = 0 := by
      unfold matchesBag
      refine Finset.prod_eq_zero ha₀_supp ?_
      simp only [X₀, E₀, atSpecies, SingleRule.matchesCount, Finsupp.add_apply,
        Finsupp.single_eq_same, ha₀_ex, decide_true, Bool.true_and, ite_eq_left_iff,
        decide_eq_true_eq]
      intro hne
      exfalso
      apply hne
      omega
    rw [hzero] at hEq
    exact Nat.ne_of_gt hpos₀ hEq.symm
  · intro hex X E hE
    exact r.matchesBag_frame_of_readsWithin
      ⟨Finset.subset_union_left.trans hpos, Finset.subset_union_right.trans hpos, hex⟩ X E hE

/-- Positive framing of `nextBag`: if `r.take.support ⊆ Ω` and `Disjoint E.support Ω`,
firing `r` on `X + E` yields `r.nextBag X + E` (outbound `r.make` outside `Ω` commutes
with `E` by additivity!). -/
theorem nextBag_frame {Ω : Finset R} {r : Rule R}
    (htake : r.take.support ⊆ Ω) (X E : R →₀ ℕ) (hE : Disjoint E.support Ω) :
    r.nextBag (X + E) = r.nextBag X + E := by
  ext a
  simp only [nextBag_apply, Finsupp.add_apply]
  by_cases haΩ : a ∈ Ω
  · have hEa : E a = 0 :=
      Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp hE haΩ)
    simp [hEa]
  · have hta : r.take a = 0 :=
      Finsupp.notMem_support_iff.mp (fun hm => haΩ (htake hm))
    rw [hta]
    omega

/-- **Closure of `ReadsWithin Ω` under Behr–Krivine Rule Fusion**:
Composing two rules that read/consume/exhaust within `Ω` produces only composite rules
that also read/consume/exhaust within `Ω`—even when both rules emit outbound messages
(`make`) outside `Ω`! -/
theorem ReadsWithin.of_compose {Ω : Finset R} {r₂ r₁ r : Rule R}
    (hr₂ : r₂.ReadsWithin Ω) (hr₁ : r₁.ReadsWithin Ω)
    (hr : r ∈ (compose r₂ r₁).support) :
    r.ReadsWithin Ω := by
  have houtside : ∀ a ∉ Ω, r.atSpecies a = ⟨0, 0, r₁.make a + r₂.make a, false⟩ := by
    intro a haΩ
    let T := r₂.support ∪ r₁.support ∪ r.support ∪ {a}
    have hsub : r₂.support ∪ r₁.support ∪ r.support ⊆ T := Finset.subset_union_left
    have haT : a ∈ T := Finset.mem_union_right _ (Finset.mem_singleton_self a)
    have hne : compose r₂ r₁ r ≠ 0 := Finsupp.mem_support_iff.mp hr
    rw [compose_apply r₂ r₁ r hsub] at hne
    have hfactor : compose1 (r₂.atSpecies a) (r₁.atSpecies a) (r.atSpecies a) ≠ 0 :=
      fun hz => hne (Finset.prod_eq_zero haT hz)
    rw [r₂.atSpecies_outside_readsWithin hr₂ haΩ,
      r₁.atSpecies_outside_readsWithin hr₁ haΩ] at hfactor
    have hcand : Overlap1.candidates ⟨0, 0, r₂.make a, false⟩ ⟨0, 0, r₁.make a, false⟩ =
        {⟨0, 0, 0, 0⟩} := by
      ext ov
      rw [Overlap1.mem_candidates_iff, Finset.mem_singleton]
      rcases ov with ⟨u, v, w, z⟩
      simp only [Overlap1.Valid, Overlap1.mk.injEq]
      constructor
      · rintro ⟨_, _, h3, h4, _, _⟩; omega
      · rintro ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩ <;> (intro h; cases h)
    simp only [compose1, hcand, Finset.sum_singleton, Overlap1.composedRule, Nat.sub_zero,
      Bool.or_self] at hfactor
    by_contra hne_rule
    exact hfactor (Finsupp.single_eq_of_ne hne_rule)
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_contra haΩ
    have h := congrArg SingleRule.take (houtside a haΩ)
    simp [atSpecies] at h
    exact (Finsupp.mem_support_iff.mp ha) h
  · intro a ha
    by_contra haΩ
    have h := congrArg SingleRule.keep (houtside a haΩ)
    simp [atSpecies] at h
    exact (Finsupp.mem_support_iff.mp ha) h
  · intro a ha
    by_contra haΩ
    have h := congrArg SingleRule.exhaust (houtside a haΩ)
    simp [atSpecies, ha] at h

end Rule

/-! ## Operator frame equivariance (`shiftBag` / `shiftBagZ`) -/

/-- Linear framing operator `|X⟩ ↦ |X + E⟩` on uncolored multi-species bag states. -/
noncomputable def shiftBag (E : R →₀ ℕ) : ((R →₀ ℕ) →₀ ℕ) →ₗ[ℕ] ((R →₀ ℕ) →₀ ℕ) :=
  Finsupp.lsum ℕ fun X => Finsupp.lsingle (X + E)

omit [DecidableEq R] in
@[simp]
theorem shiftBag_single (E X : R →₀ ℕ) (c : ℕ) :
    shiftBag E (Finsupp.single X c) = Finsupp.single (X + E) c := by
  simp [shiftBag]

/-- Signed Z-set framing operator `|X⟩ ↦ |X + E⟩` on `(R →₀ ℕ) →₀ ℤ`. -/
noncomputable def shiftBagZ (E : R →₀ ℕ) : ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  Finsupp.lsum ℤ fun X => Finsupp.lsingle (X + E)

omit [DecidableEq R] in
@[simp]
theorem shiftBagZ_single (E X : R →₀ ℕ) (c : ℤ) :
    shiftBagZ E (Finsupp.single X c) = Finsupp.single (X + E) c := by
  simp [shiftBagZ]

/-- Operator-level regional framing on `(R →₀ ℕ) →₀ ℕ`. -/
theorem rho_comm_shiftBag {Ω : Finset R} {A : Rule R →₀ ℕ}
    (hA : ∀ r ∈ A.support, r.ReadsWithin Ω)
    {E : R →₀ ℕ} (hE : Disjoint E.support Ω) :
    (rho A).comp (shiftBag E) = (shiftBag E).comp (rho A) := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, shiftBag_single]
  unfold rho
  rw [LinearMap.finsupp_sum_apply, LinearMap.finsupp_sum_apply, map_finsuppSum]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun r hr => ?_
  have hread : r.ReadsWithin Ω := hA r hr
  simp [r.matchesBag_frame_of_readsWithin hread X E hE, r.nextBag_frame hread.1 X E hE]

private theorem rhoZAux_comm_shiftBagZ {Ω : Finset R} {A : Rule R →₀ ℤ}
    (hA : ∀ r ∈ A.support, r.ReadsWithin Ω)
    {E : R →₀ ℕ} (hE : Disjoint E.support Ω) :
    (rhoZAux A).comp (shiftBagZ E) = (shiftBagZ E).comp (rhoZAux A) := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, shiftBagZ_single]
  unfold rhoZAux
  rw [LinearMap.finsupp_sum_apply, LinearMap.finsupp_sum_apply, map_finsuppSum]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun r hr => ?_
  have hread : r.ReadsWithin Ω := hA r hr
  simp [r.matchesBag_frame_of_readsWithin hread X E hE, r.nextBag_frame hread.1 X E hE]

/-- Operator-level regional framing on Z-set states `(R →₀ ℕ) →₀ ℤ`. -/
theorem rhoZ_comm_shiftBagZ {Ω : Finset R} {A : SignedRuleAlgebra R}
    (hA : ∀ r ∈ (A : Rule R →₀ ℤ).support, r.ReadsWithin Ω)
    {E : R →₀ ℕ} (hE : Disjoint E.support Ω) :
    (rhoZ A).comp (shiftBagZ E) = (shiftBagZ E).comp (rhoZ A) :=
  rhoZAux_comm_shiftBagZ hA hE

/-! ## Regional commutation for disjoint owned spaces -/

private theorem mulZ_comm_of_disjoint_regions {Ω₁ Ω₂ : Finset R} (hΩ : Disjoint Ω₁ Ω₂)
    {A B : Rule R →₀ ℤ}
    (hA : ∀ r ∈ A.support, r.support ⊆ Ω₁)
    (hB : ∀ r ∈ B.support, r.support ⊆ Ω₂) :
    mulZ A B = mulZ B A := by
  unfold mulZ
  rw [Finsupp.sum_comm]
  refine Finsupp.sum_congr fun r₁ hr₁ => ?_
  refine Finsupp.sum_congr fun r₂ hr₂ => ?_
  have hdisj : Disjoint r₂.support r₁.support :=
    hΩ.mono (hA r₂ hr₂) (hB r₁ hr₁)
  rw [mul_comm (A r₂) (B r₁), composeZ, composeZ, compose_comm_of_disjoint_support hdisj]

/-- Two rule operators `A, B : SignedRuleAlgebra R` supported in disjoint regions
`Disjoint Ω₁ Ω₂` commute on the nose (`A * B = B * A`). -/
theorem mul_comm_of_disjoint_regions {Ω₁ Ω₂ : Finset R} (hΩ : Disjoint Ω₁ Ω₂)
    {A B : SignedRuleAlgebra R}
    (hA : ∀ r ∈ (A : Rule R →₀ ℤ).support, r.support ⊆ Ω₁)
    (hB : ∀ r ∈ (B : Rule R →₀ ℤ).support, r.support ⊆ Ω₂) :
    A * B = B * A :=
  mulZ_comm_of_disjoint_regions hΩ hA hB

/-- Lie commutator `[A, B]_⋆ = 0` for rule operators in disjoint owned regions. -/
theorem commutator_eq_zero_of_disjoint_regions {Ω₁ Ω₂ : Finset R} (hΩ : Disjoint Ω₁ Ω₂)
    {A B : SignedRuleAlgebra R}
    (hA : ∀ r ∈ (A : Rule R →₀ ℤ).support, r.support ⊆ Ω₁)
    (hB : ∀ r ∈ (B : Rule R →₀ ℤ).support, r.support ⊆ Ω₂) :
    SignedRuleAlgebra.commutator A B = 0 := by
  unfold SignedRuleAlgebra.commutator
  rw [mul_comm_of_disjoint_regions hΩ hA hB, sub_self]

end Ownership

end Mettapedia.Algebra.RuleAlgebra
