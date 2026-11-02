import Mettapedia.Algebra.RuleAlgebra.OwnershipGluing

/-!
# Statistical mechanics & exact syntactic Ehrenfest moment equations (`Q3.2`)

Given the associative `ℤ`-linear rule ring `SignedRuleAlgebra R` and its Z-set
representation `rhoZ`, we construct the continuous-time Markov / master-equation
generator `generator H` for any weighted rule Hamiltonian `H : SignedRuleAlgebra R`
and prove that time-derivatives of expected pattern & absence observables reduce to
**purely syntactic Lie commutators** `[O, H]_⋆ = O * H - H * O`:

1. **`totalMass_comp_generator` (Conservation of Probability / Total Mass)**:
   `totalMass.comp (generator H) = 0` for every `H : SignedRuleAlgebra R`.
2. **`Rule.IsObservable` & `rhoZ_ofRule_isObservable` (Diagonal Observables)**:
   Every non-mutating rule `o` (`o.take = 0 ∧ o.make = 0`)—including *both*
   falling-factorial pattern counts `Rule.keepOnly P` and non-monotone absence /
   exact-count indicators `Rule.pureAbsent E`, `⟨0, P, 0, E⟩`—acts diagonally on
   bag states: `rhoZ [o] |X⟩ = (o.matchesBag X : ℤ) • |X⟩`.
3. **`syntactic_ehrenfest` (`Q3.2` Exact Moment Equation)**:
   For every observable combination `O` (`∀ o ∈ O.support, o.IsObservable`) and
   every Hamiltonian `H : SignedRuleAlgebra R`:
   `(expectation O).comp (generator H) = expectation (SignedRuleAlgebra.commutator O H)`.
4. **Leibniz Derivation & Closed-Form Reactive Moment Equations**:
   - `commutator_mul_right`: `[A, B * C]_⋆ = [A, B]_⋆ * C + B * [A, C]_⋆`.
   - `commutator_pureAbsent_take`: `[[pureAbsent a], [take a]]_⋆ = +[take unique a]`
     ($\frac{d}{dt}\mathbb{P}(X(a)=0) = +\mu\,\mathbb{P}(X(a)=1)$).
   - `commutator_count_autocatalytic`: `[[keep a], [A → 2A]]_⋆ = +[A → 2A]`
     (quadratic terms cancel syntactically, closing $\frac{d}{dt}\mathbb{E}[X(a)] = \lambda\,\mathbb{E}[X(a)]$).
   - `commutator_lock_mutexAcquire`: for `req ≠ lock`,
     `[[keep lock], [acquire(req, lock)]]_⋆ = +[acquire(req, lock)]`
     ($\frac{d}{dt}\mathbb{E}[X(\mathrm{lock})] = k_{\mathrm{acq}}\,\mathbb{E}[X(\mathrm{req})\mathbf{1}_{X(\mathrm{lock})=0}]$).
5. **Negative Control (`ehrenfest_fails_for_non_observable`)**:
   Demonstrates explicitly that `IsObservable` cannot be dropped: for mutating
   `M = H = [take ()]` on `|1⟩`, `(expectation M) (generator H |1⟩) = -1 ≠ 0 = expectation [M, H]_⋆ |1⟩`.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.RuleAlgebra

open scoped BigOperators

/-! ## Total-mass covector, master-equation generator, and mass conservation -/

/-- The covector `⟨1|` summing all coefficients of a signed Z-set bag distribution. -/
noncomputable def totalMass {R : Type*} : ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ℤ :=
  Finsupp.lsum ℤ fun _ => LinearMap.id

@[simp]
theorem totalMass_single {R : Type*} (X : R →₀ ℕ) (c : ℤ) :
    totalMass (Finsupp.single X c) = c := by
  simp [totalMass]

section Dynamics

variable {R : Type*} [DecidableEq R]

theorem totalMass_rhoZ_ofRule (r : Rule R) (X : R →₀ ℕ) :
    totalMass (rhoZ (SignedRuleAlgebra.ofRule r) (Finsupp.single X (1 : ℤ))) =
      (r.matchesBag X : ℤ) := by
  rw [rhoZ_single_apply, totalMass_single]

/-- Continuous-time Markov jump generator `L(r)` of a single rule `r : Rule R`:
`|X⟩ ↦ m(r, X) (|r.nextBag X⟩ - |X⟩)`. -/
noncomputable def generatorRule (r : Rule R) :
    ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  Finsupp.lsum ℤ fun X =>
    ((Finsupp.lsingle (r.nextBag X) - Finsupp.lsingle X :
      ℤ →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ))).comp (LinearMap.mulLeft ℤ (r.matchesBag X : ℤ))

theorem generatorRule_single (r : Rule R) (X : R →₀ ℕ) :
    generatorRule r (Finsupp.single X (1 : ℤ)) =
      Finsupp.single (r.nextBag X) (r.matchesBag X : ℤ) -
        Finsupp.single X (r.matchesBag X : ℤ) := by
  simp [generatorRule]

/-- Conservation of probability / total mass for a single rule generator. -/
theorem totalMass_comp_generatorRule (r : Rule R) :
    totalMass.comp (generatorRule r) = 0 := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp [generatorRule]

/-- Underlying `ℤ`-linear master-equation generator on `Rule R →₀ ℤ`. -/
noncomputable def generatorAux (H : Rule R →₀ ℤ) :
    ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  H.sum fun r w => w • generatorRule r

@[simp]
theorem generatorAux_zero : generatorAux (0 : Rule R →₀ ℤ) = 0 := by
  simp [generatorAux]

theorem generatorAux_add (H₁ H₂ : Rule R →₀ ℤ) :
    generatorAux (H₁ + H₂) = generatorAux H₁ + generatorAux H₂ := by
  unfold generatorAux
  rw [Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => add_smul _ _ _)]

theorem generatorAux_smul (c : ℤ) (H : Rule R →₀ ℤ) :
    generatorAux (c • H) = c • generatorAux H := by
  unfold generatorAux
  rw [Finsupp.sum_smul_index' (fun _ => by simp)]
  simp only [Finsupp.sum, Finset.smul_sum]
  congr 1; ext r
  rw [smul_eq_mul, mul_smul]

@[simp]
theorem generatorAux_single (r : Rule R) (w : ℤ) :
    generatorAux (Finsupp.single r w) = w • generatorRule r := by
  simp [generatorAux]

/-- Master-equation Markov generator `L(H)` for a weighted rule Hamiltonian
`H : SignedRuleAlgebra R`. -/
noncomputable def generator (H : SignedRuleAlgebra R) :
    ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ((R →₀ ℕ) →₀ ℤ) :=
  generatorAux H

@[simp]
theorem generator_zero : generator (0 : SignedRuleAlgebra R) = 0 := generatorAux_zero

theorem generator_add (H₁ H₂ : SignedRuleAlgebra R) :
    generator (H₁ + H₂) = generator H₁ + generator H₂ :=
  generatorAux_add H₁ H₂

theorem generator_smul (c : ℤ) (H : SignedRuleAlgebra R) :
    generator (c • H) = c • generator H :=
  generatorAux_smul c H

@[simp]
theorem generator_ofRule (r : Rule R) :
    generator (SignedRuleAlgebra.ofRule r) = generatorRule r := by
  change generatorAux (Finsupp.single r 1) = _
  simp

/-- **Conservation of Probability / Total Mass**: `⟨1| ∘ L(H) = 0` for every weighted
rule Hamiltonian `H : SignedRuleAlgebra R`. -/
theorem totalMass_comp_generator (H : SignedRuleAlgebra R) :
    totalMass.comp (generator H) = 0 := by
  change totalMass.comp (generatorAux H) = 0
  refine Finsupp.induction_linear (H : Rule R →₀ ℤ) (by simp) (fun x y hx hy => ?_) (fun r w => ?_)
  · rw [generatorAux_add, LinearMap.comp_add, hx, hy, add_zero]
  · rw [generatorAux_single, LinearMap.comp_smul, totalMass_comp_generatorRule, smul_zero]

/-! ## Diagonal observables and the Syntactic Ehrenfest Moment Equation (`Q3.2`) -/

namespace Rule

/-- A rule `o : Rule R` is a *non-mutating observable* when it neither consumes nor
mints tokens (`o.take = 0 ∧ o.make = 0`). Both `keep` (falling-factorial pattern
counts) and `exhaust` (absence / exact-count indicators) are permitted! -/
def IsObservable {R : Type*} (o : Rule R) : Prop :=
  o.take = 0 ∧ o.make = 0

omit [DecidableEq R] in
theorem keepOnly_isObservable (P : R →₀ ℕ) : (Rule.keepOnly P).IsObservable :=
  ⟨rfl, rfl⟩

omit [DecidableEq R] in
theorem pureAbsent_isObservable (E : Finset R) : (Rule.pureAbsent E).IsObservable :=
  ⟨rfl, rfl⟩

omit [DecidableEq R] in
theorem ofSingle_isObservable (a : R) {s : SingleRule}
    (ht : s.take = 0) (hm : s.make = 0) :
    (Rule.ofSingle a s).IsObservable := by
  simp [IsObservable, ofSingle, ht, hm]

omit [DecidableEq R] in
theorem IsObservable.nextBag_eq {o : Rule R} (ho : o.IsObservable) (X : R →₀ ℕ) :
    o.nextBag X = X := by
  ext a
  simp [Rule.nextBag_apply, ho.1, ho.2]

end Rule

private theorem int_smul_single_one_bag {α : Type*} (c : ℤ) (a : α) :
    c • Finsupp.single a (1 : ℤ) = Finsupp.single a c := by
  ext x
  by_cases h : a = x <;> simp [h]

/-- Every observable rule `o` acts **diagonally** on bag basis kets `|X⟩`. -/
theorem rhoZ_ofRule_isObservable {o : Rule R} (ho : o.IsObservable) (X : R →₀ ℕ) :
    rhoZ (SignedRuleAlgebra.ofRule o) (Finsupp.single X (1 : ℤ)) =
      (o.matchesBag X : ℤ) • Finsupp.single X (1 : ℤ) := by
  rw [rhoZ_single_apply, ho.nextBag_eq X, int_smul_single_one_bag]

/-- Linear expectation functional `ψ ↦ ⟨1 | ρ_ℤ(O) ψ⟩` associated to an algebra
element `O : SignedRuleAlgebra R`. -/
noncomputable def expectation (O : SignedRuleAlgebra R) : ((R →₀ ℕ) →₀ ℤ) →ₗ[ℤ] ℤ :=
  totalMass.comp (rhoZ O)

@[simp]
theorem expectation_zero : expectation (0 : SignedRuleAlgebra R) = 0 := by
  simp [expectation]

theorem expectation_add (O₁ O₂ : SignedRuleAlgebra R) :
    expectation (O₁ + O₂) = expectation O₁ + expectation O₂ := by
  unfold expectation
  rw [rhoZ_add, LinearMap.comp_add]

theorem expectation_sub (O₁ O₂ : SignedRuleAlgebra R) :
    expectation (O₁ - O₂) = expectation O₁ - expectation O₂ := by
  unfold expectation
  rw [rhoZ_sub, LinearMap.comp_sub]

theorem expectation_smul (c : ℤ) (O : SignedRuleAlgebra R) :
    expectation (c • O) = c • expectation O := by
  unfold expectation
  rw [rhoZ_smul, LinearMap.comp_smul]

theorem expectation_ofRule_single (r : Rule R) (X : R →₀ ℕ) :
    expectation (SignedRuleAlgebra.ofRule r) (Finsupp.single X (1 : ℤ)) =
      (r.matchesBag X : ℤ) := by
  simp [expectation, totalMass_rhoZ_ofRule]

/-- Single-rule Ehrenfest identity: for any non-mutating observable `o` and any
transition rule `r`, `⟨1 | ρ_ℤ([o]) L(r) = ⟨1 | ρ_ℤ([[o], [r]]_⋆)`. -/
theorem syntactic_ehrenfest_ofRule {o : Rule R} (ho : o.IsObservable) (r : Rule R) :
    (expectation (SignedRuleAlgebra.ofRule o)).comp (generatorRule r) =
      expectation (SignedRuleAlgebra.commutator
        (SignedRuleAlgebra.ofRule o) (SignedRuleAlgebra.ofRule r)) := by
  apply Finsupp.lhom_ext'
  intro X
  apply LinearMap.ext_ring
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have hLHS : expectation (SignedRuleAlgebra.ofRule o)
      (generatorRule r (Finsupp.single X 1)) =
      (r.matchesBag X : ℤ) * (o.matchesBag (r.nextBag X) : ℤ) -
        (r.matchesBag X : ℤ) * (o.matchesBag X : ℤ) := by
    rw [generatorRule_single, ← int_smul_single_one_bag (r.matchesBag X : ℤ) (r.nextBag X),
      ← int_smul_single_one_bag (r.matchesBag X : ℤ) X, map_sub, map_smul, map_smul,
      expectation_ofRule_single, expectation_ofRule_single, smul_eq_mul, smul_eq_mul]
  have hRHS : expectation (SignedRuleAlgebra.commutator
      (SignedRuleAlgebra.ofRule o) (SignedRuleAlgebra.ofRule r)) (Finsupp.single X 1) =
      (r.matchesBag X : ℤ) * (o.matchesBag (r.nextBag X) : ℤ) -
        (r.matchesBag X : ℤ) * (o.matchesBag X : ℤ) := by
    unfold expectation
    rw [LinearMap.comp_apply, rhoZ_commutator, LinearMap.sub_apply, map_sub,
      LinearMap.comp_apply, LinearMap.comp_apply]
    have ht1 : totalMass (rhoZ (SignedRuleAlgebra.ofRule o)
        (rhoZ (SignedRuleAlgebra.ofRule r) (Finsupp.single X 1))) =
        (r.matchesBag X : ℤ) * (o.matchesBag (r.nextBag X) : ℤ) := by
      rw [rhoZ_single_apply, ← int_smul_single_one_bag (r.matchesBag X : ℤ) (r.nextBag X),
        map_smul, map_smul, totalMass_rhoZ_ofRule, smul_eq_mul]
    have ht2 : totalMass (rhoZ (SignedRuleAlgebra.ofRule r)
        (rhoZ (SignedRuleAlgebra.ofRule o) (Finsupp.single X 1))) =
        (r.matchesBag X : ℤ) * (o.matchesBag X : ℤ) := by
      rw [rhoZ_ofRule_isObservable ho, map_smul, map_smul, totalMass_rhoZ_ofRule,
        smul_eq_mul, mul_comm]
    rw [ht1, ht2]
  rw [hLHS, hRHS]

private theorem mul_smul_left_signed (c : ℤ) (A B : SignedRuleAlgebra R) :
    (c • A) * B = c • (A * B) :=
  mulZ_smul_left c A B

private theorem mul_smul_right_signed (c : ℤ) (A B : SignedRuleAlgebra R) :
    A * (c • B) = c • (A * B) :=
  mulZ_smul_right c A B

private theorem commutator_smul_left (c : ℤ) (A B : SignedRuleAlgebra R) :
    SignedRuleAlgebra.commutator (c • A) B = c • SignedRuleAlgebra.commutator A B := by
  unfold SignedRuleAlgebra.commutator
  rw [mul_smul_left_signed, mul_smul_right_signed, smul_sub]

private theorem commutator_smul_right (c : ℤ) (A B : SignedRuleAlgebra R) :
    SignedRuleAlgebra.commutator A (c • B) = c • SignedRuleAlgebra.commutator A B := by
  unfold SignedRuleAlgebra.commutator
  rw [mul_smul_right_signed, mul_smul_left_signed, smul_sub]

private theorem expectation_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → SignedRuleAlgebra R) :
    expectation (s.sum f) = s.sum (fun i => expectation (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, expectation_add, ih, Finset.sum_insert hi]

private theorem generator_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → SignedRuleAlgebra R) :
    generator (s.sum f) = s.sum (fun i => generator (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, generator_add, ih, Finset.sum_insert hi]

private theorem commutator_finset_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → SignedRuleAlgebra R) (B : SignedRuleAlgebra R) :
    SignedRuleAlgebra.commutator (s.sum f) B =
      s.sum (fun i => SignedRuleAlgebra.commutator (f i) B) := by
  classical
  induction s using Finset.induction with
  | empty =>
    unfold SignedRuleAlgebra.commutator
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, SignedRuleAlgebra.commutator_add_left, ih, Finset.sum_insert hi]

private theorem commutator_finset_sum_right {ι : Type*} (A : SignedRuleAlgebra R)
    (s : Finset ι) (f : ι → SignedRuleAlgebra R) :
    SignedRuleAlgebra.commutator A (s.sum f) =
      s.sum (fun i => SignedRuleAlgebra.commutator A (f i)) := by
  classical
  induction s using Finset.induction with
  | empty =>
    unfold SignedRuleAlgebra.commutator
    simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, SignedRuleAlgebra.commutator_add_right, ih, Finset.sum_insert hi]

private theorem linearMap_sum_comp {ι M₁ M₂ M₃ : Type*} [Semiring ℤ]
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module ℤ M₁] [Module ℤ M₂] [Module ℤ M₃]
    (s : Finset ι) (f : ι → (M₂ →ₗ[ℤ] M₃)) (g : M₁ →ₗ[ℤ] M₂) :
    (s.sum f).comp g = s.sum (fun i => (f i).comp g) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, LinearMap.add_comp, ih, Finset.sum_insert hi]

private theorem linearMap_comp_sum {ι M₁ M₂ M₃ : Type*}
    [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M₃]
    [Module ℤ M₁] [Module ℤ M₂] [Module ℤ M₃]
    (g : M₂ →ₗ[ℤ] M₃) (s : Finset ι) (f : ι → (M₁ →ₗ[ℤ] M₂)) :
    g.comp (s.sum f) = s.sum (fun i => g.comp (f i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, LinearMap.comp_add, ih, Finset.sum_insert hi]

private theorem signedRuleAlgebra_decomp (A : Rule R →₀ ℤ) :
    (A : SignedRuleAlgebra R) = A.support.sum
      (fun r => (A r) • SignedRuleAlgebra.ofRule r) := by
  change A = A.support.sum (fun r => (A r) • Finsupp.single r (1 : ℤ))
  conv_lhs => rw [← Finsupp.sum_single A]
  unfold Finsupp.sum
  refine Finset.sum_congr rfl fun r _ => ?_
  exact (int_smul_single_one_bag (A r) r).symm

/-- **Syntactic Ehrenfest / Behr–Krivine Moment Equation (`Q3.2`)**:
For *every* linear combination of non-mutating observables `O : SignedRuleAlgebra R`
(`∀ o ∈ O.support, o.IsObservable`) and *every* weighted rule Hamiltonian
`H : SignedRuleAlgebra R`, the master-equation time-derivative of `expectation O`
equals `expectation [O, H]_⋆`! -/
theorem syntactic_ehrenfest {O : SignedRuleAlgebra R}
    (hO : ∀ o ∈ (O : Rule R →₀ ℤ).support, o.IsObservable)
    (H : SignedRuleAlgebra R) :
    (expectation O).comp (generator H) =
      expectation (SignedRuleAlgebra.commutator O H) := by
  let O' : Rule R →₀ ℤ := O
  let H' : Rule R →₀ ℤ := H
  have hOdecomp : O = O'.support.sum (fun o => (O' o) • SignedRuleAlgebra.ofRule o) :=
    signedRuleAlgebra_decomp O'
  have hHdecomp : H = H'.support.sum (fun r => (H' r) • SignedRuleAlgebra.ofRule r) :=
    signedRuleAlgebra_decomp H'
  rw [hOdecomp, hHdecomp, expectation_finset_sum, generator_finset_sum,
    linearMap_sum_comp, commutator_finset_sum_left, expectation_finset_sum]
  refine Finset.sum_congr rfl fun o ho => ?_
  rw [linearMap_comp_sum, commutator_finset_sum_right, expectation_finset_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [expectation_smul, generator_smul, LinearMap.smul_comp, LinearMap.comp_smul,
    generator_ofRule, syntactic_ehrenfest_ofRule (hO o ho) r,
    commutator_smul_left, commutator_smul_right, expectation_smul, expectation_smul]

/-! ## Leibniz Derivation Identity and Single-Species Embedding -/

/-- Leibniz derivation law `[A, B * C]_⋆ = [A, B]_⋆ * C + B * [A, C]_⋆` in `SignedRuleAlgebra R`. -/
theorem commutator_mul_right (A B C : SignedRuleAlgebra R) :
    SignedRuleAlgebra.commutator A (B * C) =
      SignedRuleAlgebra.commutator A B * C + B * SignedRuleAlgebra.commutator A C := by
  unfold SignedRuleAlgebra.commutator
  rw [sub_mul, mul_sub, _root_.mul_assoc A B C, _root_.mul_assoc B A C, _root_.mul_assoc B C A]
  abel

/-- Embedding single-species composition `compose1 s₂ s₁` at a species `a : R`. -/
theorem compose_ofSingle_same (a : R) (s₂ s₁ : SingleRule) :
    compose (Rule.ofSingle a s₂) (Rule.ofSingle a s₁) =
      (compose1 s₂ s₁).sum (fun s c => Finsupp.single (Rule.ofSingle a s) c) := by
  ext r
  let T : Finset R := {a} ∪ r.support
  have hsub : (Rule.ofSingle a s₂).support ∪ (Rule.ofSingle a s₁).support ∪ r.support ⊆ T := by
    refine Finset.union_subset (Finset.union_subset ?_ ?_) Finset.subset_union_right
    · exact (Rule.ofSingle_support_subset a s₂).trans Finset.subset_union_left
    · exact (Rule.ofSingle_support_subset a s₁).trans Finset.subset_union_left
  rw [compose_apply _ _ r hsub, Finsupp.sum_apply]
  by_cases hother : ∀ b : R, b ≠ a → r.atSpecies b = SingleRule.id
  · have hr_eq : r = Rule.ofSingle a (r.atSpecies a) := by
      apply Rule.ext_atSpecies
      intro b
      by_cases hba : b = a
      · subst hba; rw [Rule.ofSingle_atSpecies_same]
      · rw [hother b hba, Rule.ofSingle_atSpecies_ne _ hba]
    have haT : a ∈ T := Finset.mem_union_left _ (Finset.mem_singleton_self a)
    have hprod : ∏ b ∈ T,
        compose1 ((Rule.ofSingle a s₂).atSpecies b) ((Rule.ofSingle a s₁).atSpecies b)
          (r.atSpecies b) =
        compose1 s₂ s₁ (r.atSpecies a) := by
      rw [← Finset.mul_prod_erase T _ haT, Rule.ofSingle_atSpecies_same,
        Rule.ofSingle_atSpecies_same]
      have herase : ∏ b ∈ T.erase a,
          compose1 ((Rule.ofSingle a s₂).atSpecies b) ((Rule.ofSingle a s₁).atSpecies b)
            (r.atSpecies b) = 1 := by
        apply Finset.prod_eq_one
        intro b hb
        have hba : b ≠ a := (Finset.mem_erase.mp hb).1
        rw [Rule.ofSingle_atSpecies_ne s₂ hba, Rule.ofSingle_atSpecies_ne s₁ hba,
          hother b hba, compose1_id_left, Finsupp.single_eq_same]
      rw [herase, mul_one]
    rw [hprod]
    unfold Finsupp.sum
    have hsum : ∑ s ∈ (compose1 s₂ s₁).support,
        (Finsupp.single (Rule.ofSingle a s) (compose1 s₂ s₁ s)) r =
        ∑ s ∈ (compose1 s₂ s₁).support,
          if s = r.atSpecies a then compose1 s₂ s₁ s else 0 := by
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hs : s = r.atSpecies a
      · rw [if_pos hs, hs, ← hr_eq, Finsupp.single_eq_same]
      · have hne : r ≠ Rule.ofSingle a s := by
          intro hEq
          apply hs
          have := congrArg (fun x => x.atSpecies a) hEq
          simpa using this.symm
        rw [if_neg hs, Finsupp.single_eq_of_ne hne]
    rw [hsum, Finset.sum_ite_eq']
    by_cases hmem : r.atSpecies a ∈ (compose1 s₂ s₁).support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      exact Finsupp.notMem_support_iff.mp hmem
  · have hex : ∃ b : R, b ≠ a ∧ r.atSpecies b ≠ SingleRule.id := by
      by_contra hall
      exact hother (fun b hb => Classical.not_not.mp fun hne => hall ⟨b, hb, hne⟩)
    rcases hex with ⟨b₀, hb₀_ne, hb₀_id⟩
    have hb₀T : b₀ ∈ T :=
      Finset.mem_union_right _ ((Rule.mem_support_iff r b₀).mpr hb₀_id)
    have hLHS : ∏ b ∈ T,
        compose1 ((Rule.ofSingle a s₂).atSpecies b) ((Rule.ofSingle a s₁).atSpecies b)
          (r.atSpecies b) = 0 := by
      refine Finset.prod_eq_zero hb₀T ?_
      rw [Rule.ofSingle_atSpecies_ne s₂ hb₀_ne, Rule.ofSingle_atSpecies_ne s₁ hb₀_ne,
        compose1_id_left]
      exact Finsupp.single_eq_of_ne hb₀_id
    rw [hLHS]
    symm
    unfold Finsupp.sum
    apply Finset.sum_eq_zero
    intro s _
    have hne : r ≠ Rule.ofSingle a s := by
      intro hEq
      apply hb₀_id
      rw [hEq, Rule.ofSingle_atSpecies_ne s hb₀_ne]
    exact Finsupp.single_eq_of_ne hne

/-! ## Three Closed-Form Reactive Commutator Examples -/

/-- **Example 1 (Decay of Absence Probability)**:
At any species `a : R`, the Lie commutator of pure absence `[pureAbsent {a}]`
with single-token decay `[take a]` equals `+[take unique a]` (`⟨1, 0, 0, true⟩`),
yielding $\frac{d}{dt}\mathbb{P}(X_t(a)=0) = +\mu\,\mathbb{P}(X_t(a)=1)$. -/
theorem commutator_pureAbsent_take (a : R) :
    SignedRuleAlgebra.commutator
      (SignedRuleAlgebra.ofRule (Rule.ofSingle a SingleRule.pureAbsent))
      (SignedRuleAlgebra.ofRule (Rule.ofSingle a ⟨1, 0, 0, false⟩)) =
    SignedRuleAlgebra.ofRule (Rule.ofSingle a ⟨1, 0, 0, true⟩) := by
  have hrev : compose1 ⟨1, 0, 0, false⟩ SingleRule.pureAbsent = 0 := by
    have hemp : Overlap1.candidates ⟨1, 0, 0, false⟩ SingleRule.pureAbsent = ∅ := by
      ext ov
      simp only [Finset.notMem_empty, iff_false, Overlap1.mem_candidates_iff, Overlap1.Valid]
      rintro ⟨h1, h2, _, _, h5, _⟩
      have ⟨ht, _⟩ := h5 rfl
      simp only [SingleRule.pureAbsent] at h1 h2 ht
      omega
    simp [compose1, hemp]
  change mulZ (Finsupp.single (Rule.ofSingle a SingleRule.pureAbsent) 1)
      (Finsupp.single (Rule.ofSingle a ⟨1, 0, 0, false⟩) 1) -
    mulZ (Finsupp.single (Rule.ofSingle a ⟨1, 0, 0, false⟩) 1)
      (Finsupp.single (Rule.ofSingle a SingleRule.pureAbsent) 1) =
    Finsupp.single (Rule.ofSingle a ⟨1, 0, 0, true⟩) 1
  rw [mulZ_single_single, mulZ_single_single, composeZ, composeZ,
    compose_ofSingle_same, compose_ofSingle_same, compose1_pureAbsent_take, hrev]
  simp

/-- **Example 2 (Autocatalytic Branching `A → 2A` — Exact First-Moment Closure)**:
At any species `a : R`, let `O₁ = [keep a]` (`⟨0, 1, 0, false⟩`) and
`r_branch = [take a, make 2a]` (`⟨1, 0, 2, false⟩`).
In `O₁ * r_branch - r_branch * O₁`, the quadratic `[take a, keep a, make 2a]` terms
cancel (`1 - 1 = 0`), leaving `(2 - 1) • [r_branch] = +[r_branch]`!
Because `expectation [r_branch] |X⟩ = X(a) = expectation O₁ |X⟩`, this yields exact
first-moment closure $\frac{d}{dt}\mathbb{E}[X_t(a)] = \lambda\,\mathbb{E}[X_t(a)]$. -/
theorem commutator_count_autocatalytic (a : R) :
    SignedRuleAlgebra.commutator
      (SignedRuleAlgebra.ofRule (Rule.ofSingle a ⟨0, 1, 0, false⟩))
      (SignedRuleAlgebra.ofRule (Rule.ofSingle a ⟨1, 0, 2, false⟩)) =
    SignedRuleAlgebra.ofRule (Rule.ofSingle a ⟨1, 0, 2, false⟩) := by
  have h12 : compose1 ⟨0, 1, 0, false⟩ ⟨1, 0, 2, false⟩ =
      Finsupp.single ⟨1, 1, 2, false⟩ 1 + Finsupp.single ⟨1, 0, 2, false⟩ 2 := by
    have hcand : Overlap1.candidates ⟨0, 1, 0, false⟩ ⟨1, 0, 2, false⟩ =
        {⟨0, 0, 0, 0⟩, ⟨0, 0, 1, 0⟩} := by
      ext ov
      rw [Overlap1.mem_candidates_iff, Finset.mem_insert, Finset.mem_singleton]
      rcases ov with ⟨u, v, w, z⟩
      simp only [Overlap1.Valid, Overlap1.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4, _, _⟩
        have : w = 0 ∨ w = 1 := by omega
        rcases this with rfl | rfl
        · left; omega
        · right; omega
      · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
          refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
          (intro h; cases h)
    rw [compose1, hcand, Finset.sum_pair (by decide)]
    rfl
  have h21 : compose1 ⟨1, 0, 2, false⟩ ⟨0, 1, 0, false⟩ =
      Finsupp.single ⟨1, 1, 2, false⟩ 1 + Finsupp.single ⟨1, 0, 2, false⟩ 1 := by
    have hcand : Overlap1.candidates ⟨1, 0, 2, false⟩ ⟨0, 1, 0, false⟩ =
        {⟨0, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩} := by
      ext ov
      rw [Overlap1.mem_candidates_iff, Finset.mem_insert, Finset.mem_singleton]
      rcases ov with ⟨u, v, w, z⟩
      simp only [Overlap1.Valid, Overlap1.mk.injEq]
      constructor
      · rintro ⟨h1, h2, h3, h4, _, _⟩
        have : v = 0 ∨ v = 1 := by omega
        rcases this with rfl | rfl
        · left; omega
        · right; omega
      · rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;>
          refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩ <;>
          (intro h; cases h)
    rw [compose1, hcand, Finset.sum_pair (by decide)]
    rfl
  change mulZ (Finsupp.single (Rule.ofSingle a ⟨0, 1, 0, false⟩) 1)
      (Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) 1) -
    mulZ (Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) 1)
      (Finsupp.single (Rule.ofSingle a ⟨0, 1, 0, false⟩) 1) =
    Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) 1
  rw [mulZ_single_single, mulZ_single_single, composeZ, composeZ,
    compose_ofSingle_same, compose_ofSingle_same, h12, h21,
    Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => Finsupp.single_add _ _ _),
    Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => Finsupp.single_add _ _ _),
    Finsupp.sum_single_index (Finsupp.single_zero _),
    Finsupp.sum_single_index (Finsupp.single_zero _),
    Finsupp.sum_single_index (Finsupp.single_zero _),
    castFinsuppInt_add, castFinsuppInt_add, castFinsuppInt_single, castFinsuppInt_single,
    castFinsuppInt_single]
  have htwo : Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) ((2 : ℕ) : ℤ) =
      Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) ((1 : ℕ) : ℤ) +
        Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) ((1 : ℕ) : ℤ) := by
    rw [← Finsupp.single_add]
    rfl
  rw [htwo]
  change (Finsupp.single (Rule.ofSingle a ⟨1, 1, 2, false⟩) (1 : ℤ) +
      (Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) (1 : ℤ) +
        Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) (1 : ℤ))) -
    (Finsupp.single (Rule.ofSingle a ⟨1, 1, 2, false⟩) (1 : ℤ) +
      Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) (1 : ℤ)) =
    Finsupp.single (Rule.ofSingle a ⟨1, 0, 2, false⟩) (1 : ℤ)
  abel

/-- Two-species absence-guarded mutex acquisition rule: consumes one `req` token and
mints one `lock` token provided `lock` is currently absent (`exhaust = {lock}`). -/
noncomputable def mutexAcquireRule (req lock : R) : Rule R where
  take := Finsupp.single req 1
  keep := 0
  make := Finsupp.single lock 1
  exhaust := {lock}

/-- Factorization of `mutexAcquireRule req lock` (`req ≠ lock`) into single-species factors. -/
theorem mutexAcquireRule_factor {req lock : R} (hneq : req ≠ lock) :
    SignedRuleAlgebra.ofRule (mutexAcquireRule req lock) =
      SignedRuleAlgebra.ofRule (Rule.ofSingle req ⟨1, 0, 0, false⟩) *
        SignedRuleAlgebra.ofRule (Rule.ofSingle lock ⟨0, 0, 1, true⟩) := by
  have hcomp : compose (Rule.ofSingle req ⟨1, 0, 0, false⟩)
      (Rule.ofSingle lock ⟨0, 0, 1, true⟩) =
      Finsupp.single (mutexAcquireRule req lock) 1 := by
    ext r
    let T : Finset R := {req, lock} ∪ r.support
    have hsub : (Rule.ofSingle req ⟨1, 0, 0, false⟩).support ∪
        (Rule.ofSingle lock ⟨0, 0, 1, true⟩).support ∪ r.support ⊆ T := by
      refine Finset.union_subset (Finset.union_subset ?_ ?_) Finset.subset_union_right
      · exact (Rule.ofSingle_support_subset req _).trans
          ((Finset.singleton_subset_iff.mpr (Finset.mem_insert_self req {lock})).trans
            Finset.subset_union_left)
      · exact (Rule.ofSingle_support_subset lock _).trans
          ((Finset.singleton_subset_iff.mpr
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self lock))).trans
            Finset.subset_union_left)
    rw [compose_apply _ _ r hsub]
    have hreq_at : (mutexAcquireRule req lock).atSpecies req = ⟨1, 0, 0, false⟩ := by
      simp [mutexAcquireRule, Rule.atSpecies, hneq]
    have hlock_at : (mutexAcquireRule req lock).atSpecies lock = ⟨0, 0, 1, true⟩ := by
      simp [mutexAcquireRule, Rule.atSpecies, Ne.symm hneq]
    have hother_at : ∀ b : R, b ≠ req → b ≠ lock →
        (mutexAcquireRule req lock).atSpecies b = SingleRule.id := by
      intro b h1 h2
      simp [mutexAcquireRule, Rule.atSpecies, SingleRule.id, h1, h2]
    by_cases hEq : mutexAcquireRule req lock = r
    · subst hEq
      rw [Finsupp.single_eq_same]
      apply Finset.prod_eq_one
      intro b _
      by_cases hb1 : b = req
      · subst hb1
        rw [Rule.ofSingle_atSpecies_same, Rule.ofSingle_atSpecies_ne _ hneq,
          hreq_at, compose1_id_right, Finsupp.single_eq_same]
      · by_cases hb2 : b = lock
        · subst hb2
          rw [Rule.ofSingle_atSpecies_ne _ (Ne.symm hneq), Rule.ofSingle_atSpecies_same,
            hlock_at, compose1_id_left, Finsupp.single_eq_same]
        · rw [Rule.ofSingle_atSpecies_ne _ hb1, Rule.ofSingle_atSpecies_ne _ hb2,
            hother_at b hb1 hb2, compose1_id_left, Finsupp.single_eq_same]
    · rw [Finsupp.single_eq_of_ne (Ne.symm hEq)]
      have hex : ∃ b ∈ T, (mutexAcquireRule req lock).atSpecies b ≠ r.atSpecies b := by
        by_contra hfor
        apply hEq
        apply Rule.ext_atSpecies
        intro b
        by_cases hbT : b ∈ T
        · exact Classical.not_not.mp fun hne => hfor ⟨b, hbT, hne⟩
        · have hb1 : b ≠ req := fun h => hbT (Finset.mem_union_left _ (by simp [h]))
          have hb2 : b ≠ lock := fun h => hbT (Finset.mem_union_left _ (by simp [h]))
          have hbr : b ∉ r.support := fun h => hbT (Finset.mem_union_right _ h)
          rw [hother_at b hb1 hb2, Rule.atSpecies_eq_id_of_notMem_support hbr]
      rcases hex with ⟨b₀, hb₀T, hne⟩
      refine Finset.prod_eq_zero hb₀T ?_
      by_cases hb1 : b₀ = req
      · subst hb1
        rw [Rule.ofSingle_atSpecies_same, Rule.ofSingle_atSpecies_ne _ hneq, compose1_id_right]
        rw [hreq_at] at hne
        exact Finsupp.single_eq_of_ne (Ne.symm hne)
      · by_cases hb2 : b₀ = lock
        · subst hb2
          rw [Rule.ofSingle_atSpecies_ne _ (Ne.symm hneq), Rule.ofSingle_atSpecies_same,
            compose1_id_left]
          rw [hlock_at] at hne
          exact Finsupp.single_eq_of_ne (Ne.symm hne)
        · rw [Rule.ofSingle_atSpecies_ne _ hb1, Rule.ofSingle_atSpecies_ne _ hb2,
            compose1_id_left]
          rw [hother_at b₀ hb1 hb2] at hne
          exact Finsupp.single_eq_of_ne (Ne.symm hne)
  change Finsupp.single (mutexAcquireRule req lock) (1 : ℤ) =
    mulZ (Finsupp.single (Rule.ofSingle req ⟨1, 0, 0, false⟩) 1)
      (Finsupp.single (Rule.ofSingle lock ⟨0, 0, 1, true⟩) 1)
  rw [mulZ_single_single, composeZ, hcomp, castFinsuppInt_single, Nat.cast_one]

/-- **Example 3 (Absence-Guarded Mutex Acquisition via Leibniz Factorization)**:
For distinct species `req ≠ lock`, the Lie commutator of the lock-count observable
`[keep lock]` with `[mutexAcquireRule req lock]` equals `+[mutexAcquireRule req lock]`,
giving $\frac{d}{dt}\mathbb{E}[X_t(\mathrm{lock})] = k_{\mathrm{acq}}\,\mathbb{E}[X_t(\mathrm{req})\mathbf{1}_{X_t(\mathrm{lock})=0}]$. -/
theorem commutator_lock_mutexAcquire {req lock : R} (hneq : req ≠ lock) :
    SignedRuleAlgebra.commutator
      (SignedRuleAlgebra.ofRule (Rule.ofSingle lock ⟨0, 1, 0, false⟩))
      (SignedRuleAlgebra.ofRule (mutexAcquireRule req lock)) =
    SignedRuleAlgebra.ofRule (mutexAcquireRule req lock) := by
  rw [mutexAcquireRule_factor hneq, commutator_mul_right]
  have hdisj : Disjoint (Rule.ofSingle lock ⟨0, 1, 0, false⟩).support
      (Rule.ofSingle req ⟨1, 0, 0, false⟩).support := by
    refine (Finset.disjoint_singleton.mpr (Ne.symm hneq)).mono
      (Rule.ofSingle_support_subset lock _) (Rule.ofSingle_support_subset req _)
  rw [SignedRuleAlgebra.commutator_ofRule_eq_zero_of_disjoint hdisj, zero_mul, zero_add]
  have hlock_comm : SignedRuleAlgebra.commutator
      (SignedRuleAlgebra.ofRule (Rule.ofSingle lock ⟨0, 1, 0, false⟩))
      (SignedRuleAlgebra.ofRule (Rule.ofSingle lock ⟨0, 0, 1, true⟩)) =
      SignedRuleAlgebra.ofRule (Rule.ofSingle lock ⟨0, 0, 1, true⟩) := by
    have h12 : compose1 ⟨0, 1, 0, false⟩ ⟨0, 0, 1, true⟩ =
        Finsupp.single ⟨0, 0, 1, true⟩ 1 := by
      have hcand : Overlap1.candidates ⟨0, 1, 0, false⟩ ⟨0, 0, 1, true⟩ = {⟨0, 0, 1, 0⟩} := by
        ext ov
        rw [Overlap1.mem_candidates_iff, Finset.mem_singleton]
        rcases ov with ⟨u, v, w, z⟩
        simp only [Overlap1.Valid, Overlap1.mk.injEq]
        constructor
        · rintro ⟨h1, h2, h3, h4, h5, _⟩
          have ⟨_, hk⟩ := h5 trivial
          omega
        · rintro ⟨rfl, rfl, rfl, rfl⟩
          refine ⟨by omega, by omega, by omega, by omega, ?_, ?_⟩
          · intro _; exact ⟨rfl, rfl⟩
          · intro h; cases h
      rw [compose1, hcand, Finset.sum_singleton]
      rfl
    have h21 : compose1 ⟨0, 0, 1, true⟩ ⟨0, 1, 0, false⟩ = 0 := by
      have hemp : Overlap1.candidates ⟨0, 0, 1, true⟩ ⟨0, 1, 0, false⟩ = ∅ := by
        ext ov
        simp only [Finset.notMem_empty, iff_false, Overlap1.mem_candidates_iff, Overlap1.Valid]
        rintro ⟨_, _, h3, h4, _, h6⟩
        have ⟨_, hk⟩ := h6 trivial
        omega
      simp [compose1, hemp]
    change mulZ (Finsupp.single (Rule.ofSingle lock ⟨0, 1, 0, false⟩) 1)
        (Finsupp.single (Rule.ofSingle lock ⟨0, 0, 1, true⟩) 1) -
      mulZ (Finsupp.single (Rule.ofSingle lock ⟨0, 0, 1, true⟩) 1)
        (Finsupp.single (Rule.ofSingle lock ⟨0, 1, 0, false⟩) 1) =
      Finsupp.single (Rule.ofSingle lock ⟨0, 0, 1, true⟩) 1
    rw [mulZ_single_single, mulZ_single_single, composeZ, composeZ,
      compose_ofSingle_same, compose_ofSingle_same, h12, h21]
    simp
  rw [hlock_comm]

end Dynamics

/-! ## Negative Control: Failure of Ehrenfest for Mutating Operators -/

/-- **Negative Control (`IsObservable` is essential in `syntactic_ehrenfest`)**:
For the mutating rule `M = H = [take ()]` on single-species bags (`R = Unit`) and
initial state `|1⟩` (`X () = 1`):
* `[M, H]_⋆ = [M, M]_⋆ = 0`, so `expectation [M, H]_⋆ |1⟩ = 0`;
* `generator H |1⟩ = |0⟩ - |1⟩`, and `(expectation M) (|0⟩ - |1⟩) = 0 - 1 = -1 ≠ 0`! -/
theorem ehrenfest_fails_for_non_observable :
    let rTake : Rule Unit := Rule.ofSingle () ⟨1, 0, 0, false⟩
    let M : SignedRuleAlgebra Unit := SignedRuleAlgebra.ofRule rTake
    let ket1 : (Unit →₀ ℕ) →₀ ℤ := Finsupp.single (Finsupp.single () 1) 1
    (expectation M).comp (generator M) ket1 ≠
      expectation (SignedRuleAlgebra.commutator M M) ket1 := by
  dsimp only
  let rTake : Rule Unit := Rule.ofSingle () ⟨1, 0, 0, false⟩
  let bag1 : Unit →₀ ℕ := Finsupp.single () 1
  have hm1 : rTake.matchesBag bag1 = 1 := by
    rw [Rule.matchesBag_eq_prod _ bag1 (Rule.ofSingle_support_subset () _),
      Finset.prod_singleton, Rule.ofSingle_atSpecies_same]
    simp [bag1, SingleRule.matchesCount]
  have hnext1 : rTake.nextBag bag1 = 0 := by
    ext
    simp [rTake, bag1, Rule.ofSingle]
  have hm0 : rTake.matchesBag 0 = 0 := by
    rw [Rule.matchesBag_eq_prod _ 0 (Rule.ofSingle_support_subset () _),
      Finset.prod_singleton, Rule.ofSingle_atSpecies_same]
    simp [SingleRule.matchesCount]
  rw [SignedRuleAlgebra.commutator_self, expectation_zero, LinearMap.zero_apply,
    LinearMap.comp_apply, generator_ofRule, generatorRule_single, hm1, hnext1, Nat.cast_one,
    map_sub, expectation_ofRule_single, expectation_ofRule_single, hm0, hm1]
  decide

end Mettapedia.Algebra.RuleAlgebra
