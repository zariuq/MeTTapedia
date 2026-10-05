import Mettapedia.GSLT.Distinction.Probabilistic.LogicalDistance
import Mettapedia.GSLT.Distinction.Probabilistic.System
import Mettapedia.GSLT.Core.Composition

/-!
# Finite labelled Markov chains are probabilistic GSLTs

A finite labelled Markov chain (`Cybernetics.ApproximateAdequacy`) is a
probabilistic system over the discrete GSLT of its states
(`stateGSLT`, `chainSystem`): its atoms read the value of an
observable, `observe i s = r`, and its steps are the successor distributions.
On these finite-state probabilistic GSLTs the three behavioural equivalences
coincide (`lsBisimilar_iff_probabilisticallyBisimilar`,
`lsBisimilar_iff_bisimulationMetric_eq_zero`):

* Larsen–Skou bisimilarity of the probabilistic GSLT (`System`), an equivalence
  with equal class masses;
* probabilistic bisimilarity in coupling form (`CouplingBound`);
* distance zero in the Kantorovich fixed-point metric, which is the logical
  distance of functional expressions (`LogicalDistance`).

The passage from equal class masses to a coupling supported on the
equivalence (`exists_coupling_of_classMass_eq`) is the classical construction
`μ y · ν z / ν[z]` on related pairs, here for any equivalence relation.  The
converse passage (`mass_eq_of_coupling`) reads a supported coupling on closed
sets.

`Classical.choice` enters through `ℝ` and the decidability of the relations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.GSLT
open Mettapedia.Cybernetics.ApproximateAdequacy

variable {A Atom S : Type*} [Fintype S]

/-! ## Couplings and class masses -/

section Classes

variable {μ ν : S → ℝ} {R : S → S → Prop}

open Classical in
/-- The mass of the `R`-class of `x`. -/
noncomputable def relationMass (R : S → S → Prop) (μ : S → ℝ) (x : S) : ℝ :=
  ∑ y ∈ Finset.univ.filter (R x ·), μ y

theorem relationMass_congr (equivalence : Equivalence R) (μ : S → ℝ) {x y : S} (related : R x y) :
    relationMass R μ x = relationMass R μ y := by
  classical
  unfold relationMass
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun first => equivalence.trans (equivalence.symm related) first,
    fun second => equivalence.trans related second⟩

theorem eq_zero_of_relationMass_eq_zero (equivalence : Equivalence R)
    (distribution : IsDistribution μ) {x : S} (zero : relationMass R μ x = 0) : μ x = 0 := by
  classical
  have terms := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => distribution.nonneg y).mp zero
  exact terms x (by simp [equivalence.refl x])

open Classical in
/-- **A coupling from equal class masses**, supported on the equivalence. -/
noncomputable def classCoupling (equivalence : Equivalence R) (first : IsDistribution μ)
    (second : IsDistribution ν) (masses : ∀ x, relationMass R μ x = relationMass R ν x) :
    Coupling μ ν where
  weight y z := if R y z then μ y * ν z / relationMass R ν z else 0
  nonneg y z := by
    split_ifs
    · exact div_nonneg (mul_nonneg (first.nonneg y) (second.nonneg z))
        (Finset.sum_nonneg fun w _ => second.nonneg w)
    · exact le_rfl
  sum_right y := by
    rw [← Finset.sum_filter]
    have rewrite : ∀ z ∈ Finset.univ.filter (R y ·),
        μ y * ν z / relationMass R ν z = μ y * ν z / relationMass R ν y := fun z member => by
      rw [Finset.mem_filter] at member
      rw [relationMass_congr equivalence ν member.2]
    rw [Finset.sum_congr rfl rewrite, ← Finset.sum_div, ← Finset.mul_sum]
    change μ y * relationMass R ν y / relationMass R ν y = μ y
    by_cases zero : relationMass R ν y = 0
    · rw [zero, div_zero]
      exact (eq_zero_of_relationMass_eq_zero equivalence first ((masses y).trans zero)).symm
    · rw [mul_div_assoc, div_self zero, mul_one]
  sum_left z := by
    rw [← Finset.sum_filter, ← Finset.sum_div, ← Finset.sum_mul]
    have classSum : ∑ y ∈ Finset.univ.filter (fun y => R y z), μ y = relationMass R μ z := by
      unfold relationMass
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun related => equivalence.symm related, fun related => equivalence.symm related⟩
    rw [classSum, masses z]
    by_cases zero : relationMass R ν z = 0
    · rw [zero, zero_mul, zero_div]
      exact (eq_zero_of_relationMass_eq_zero equivalence second zero).symm
    · rw [mul_comm, mul_div_assoc, div_self zero, mul_one]

/-- **Equal class masses give a coupling supported on the equivalence.** -/
theorem exists_coupling_of_classMass_eq (equivalence : Equivalence R) (first : IsDistribution μ)
    (second : IsDistribution ν) (masses : ∀ x, relationMass R μ x = relationMass R ν x) :
    ∃ ω : Coupling μ ν, ∀ y z, ω.weight y z ≠ 0 → R y z := by
  classical
  refine ⟨classCoupling equivalence first second masses, fun y z positive => ?_⟩
  by_contra unrelated
  exact positive (by simp [classCoupling, unrelated])

open Classical in
/-- **A coupling supported on a relation gives closed sets equal masses.** -/
theorem mass_eq_of_coupling (ω : Coupling μ ν) (supported : ∀ y z, ω.weight y z ≠ 0 → R y z)
    {C : S → Prop} (closed : ∀ y z, R y z → (C y ↔ C z)) :
    (∑ y, if C y then μ y else 0) = ∑ z, if C z then ν z else 0 := by
  have left : (∑ y, if C y then μ y else 0) = ∑ y, ∑ z, if C y then ω.weight y z else 0 :=
    Finset.sum_congr rfl fun y _ => by
      split_ifs
      · exact (ω.sum_right y).symm
      · simp
  have right : (∑ z, if C z then ν z else 0) = ∑ y, ∑ z, if C z then ω.weight y z else 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun z _ => by
      split_ifs
      · exact (ω.sum_left z).symm
      · simp
  rw [left, right]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases zero : ω.weight y z = 0
  · simp [zero]
  · have same := closed y z (supported y z zero)
    by_cases holds : C y
    · rw [if_pos holds, if_pos (same.mp holds)]
    · rw [if_neg holds, if_neg fun other => holds (same.mpr other)]

end Classes

/-! ## The probabilistic GSLT of a finite chain -/

/-- The discrete GSLT of the states, as a reducible definition: its terms are
the states, its equations are equality, and it has no rewrites.  It is
`GSLT.discrete` (`stateGSLT_eq_discrete`). -/
abbrev stateGSLT (S : Type*) : GSLT where
  Term := S
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := fun _ impossible => impossible.elim
  rewrites_resp_right := fun impossible _ => impossible.elim

theorem stateGSLT_eq_discrete (S : Type*) : stateGSLT S = GSLT.discrete S := rfl

variable (P : LabelledMarkovChain ℝ A Atom S)

/-- **A finite labelled Markov chain as a probabilistic GSLT**: the discrete
GSLT of its states, atoms reading the value of an observable, and the
successor distributions as steps. -/
noncomputable abbrev chainSystem : ProbabilisticSystem (stateGSLT S) where
  Atom := Atom × ℝ
  observes atom state := P.observe atom.1 state = atom.2
  observes_resp atom left right equivalent := by
    have same : left = right := equivalent
    rw [same]
  Label := A
  kernel label state := SubDistribution.ofFunction (P.trans label state)
    (P.isDistribution label state).nonneg (P.isDistribution label state).sum_eq_one.le
  kernel_resp label left right equivalent _ _ := by
    have same : left = right := equivalent
    rw [same]

variable {P}

@[simp] theorem kernel_weight (label : A) (state target : S) :
    ((chainSystem P).kernel label state).weight target = P.trans label state target :=
  SubDistribution.ofFunction_weight (P.trans label state) (P.isDistribution label state).nonneg
    (P.isDistribution label state).sum_eq_one.le target

open Classical in
theorem prob_eq_sum (label : A) (state : S) (C : S → Prop) :
    (chainSystem P).prob label state C =
      ∑ x, if C x then P.trans label state x else 0 := by
  unfold ProbabilisticSystem.prob
  rw [SubDistribution.mass_eq_sum]
  simp only [SubDistribution.ofFunction_weight]

/-- **The steps of the support erasure are the transitions of positive
probability.** -/
theorem support_act_iff (label : A) (state target : S) :
    (chainSystem P).support.act label state target ↔ P.trans label state target ≠ 0 := by
  constructor
  · rintro ⟨x, member, same⟩
    have equal : x = target := same
    subst equal
    rw [Finsupp.mem_support_iff, kernel_weight] at member
    exact member
  · intro positive
    refine ⟨target, ?_, rfl⟩
    rw [Finsupp.mem_support_iff, kernel_weight]
    exact positive

/-! ## Three equivalences coincide -/

/-- **A Larsen–Skou bisimulation is a probabilistic bisimulation** in coupling
form. -/
theorem ProbabilisticSystem.IsLSBisimulation.isProbabilisticBisimulation {R : S → S → Prop}
    (bisimulation : (chainSystem P).IsLSBisimulation R) :
    IsProbabilisticBisimulation P P R := by
  classical
  intro x y related
  refine ⟨fun i => ?_, fun label => ?_⟩
  · have := (bisimulation.observes related (i, P.observe i x)).mp rfl
    exact this.symm
  · refine exists_coupling_of_classMass_eq bisimulation.equivalence (P.isDistribution label x)
      (P.isDistribution label y) fun z => ?_
    have closed : ProbabilisticSystem.ClosedUnder (S := stateGSLT S) R (R z) := by
      intro u v uv
      exact ⟨fun first => bisimulation.equivalence.trans first uv,
        fun second => bisimulation.equivalence.trans second (bisimulation.equivalence.symm uv)⟩
    have masses := bisimulation.masses related label (R z) closed
    rw [prob_eq_sum, prob_eq_sum] at masses
    unfold relationMass
    rw [Finset.sum_filter, Finset.sum_filter]
    exact masses

/-- Distance zero at discount one is an equivalence relation. -/
theorem equivalence_metric_zero [Fintype A] [Fintype Atom] [DecidableEq S] :
    Equivalence fun x y : S => bisimulationMetric P P 1 x y = 0 :=
  ⟨fun x => bisimulationMetric_self zero_lt_one le_rfl x,
    fun {x y} zero => by rw [bisimulationMetric_comm zero_le_one le_rfl]; exact zero,
    fun {x y z} first second => le_antisymm
      (by
        have := bisimulationMetric_triangle (P := P) (Q := P) P zero_le_one le_rfl x y z
        rw [first, second] at this
        linarith)
      (bisimulationMetric_nonneg zero_le_one le_rfl x z)⟩

/-- **Distance zero is a Larsen–Skou bisimulation.** -/
theorem isLSBisimulation_metric_zero [Fintype A] [Fintype Atom] [DecidableEq S] :
    (chainSystem P).IsLSBisimulation fun x y => bisimulationMetric P P 1 x y = 0 := by
  classical
  have bisimulation := (couplingBound_bisimulationMetric (P := P) (Q := P) zero_le_one
    le_rfl).isProbabilisticBisimulation_zero zero_lt_one
  refine ⟨equivalence_metric_zero, fun {x y} same => ?_, fun {x y} related atom => ?_,
    fun {x y} related label C closed => ?_⟩
  · have equal : x = y := same
    subst equal
    exact bisimulationMetric_self zero_lt_one le_rfl x
  · have observed := (bisimulation related).1 atom.1
    change P.observe atom.1 x = atom.2 ↔ P.observe atom.1 y = atom.2
    rw [observed]
  · obtain ⟨ω, supported⟩ := (bisimulation related).2 label
    rw [prob_eq_sum, prob_eq_sum]
    exact mass_eq_of_coupling ω supported closed

/-- **Larsen–Skou bisimilarity of the probabilistic GSLT is probabilistic
bisimilarity of the chain.** -/
theorem lsBisimilar_iff_probabilisticallyBisimilar [Fintype A] [Fintype Atom] {x y : S} :
    (chainSystem P).LSBisimilar x y ↔ ProbabilisticallyBisimilar P P x y := by
  classical
  constructor
  · rintro ⟨R, bisimulation, related⟩
    exact ⟨R, bisimulation.isProbabilisticBisimulation, related⟩
  · intro bisimilar
    exact ⟨_, isLSBisimulation_metric_zero,
      (bisimulationMetric_eq_zero_iff zero_lt_one le_rfl).mpr bisimilar⟩

/-- **Larsen–Skou bisimilarity is distance zero** in the Kantorovich metric, at
every discount `0 < c ≤ 1`. -/
theorem lsBisimilar_iff_bisimulationMetric_eq_zero [Fintype A] [Fintype Atom] {c : ℝ}
    (c_pos : 0 < c) (c_le : c ≤ 1) {x y : S} :
    (chainSystem P).LSBisimilar x y ↔ bisimulationMetric P P c x y = 0 :=
  lsBisimilar_iff_probabilisticallyBisimilar.trans (bisimulationMetric_eq_zero_iff c_pos c_le).symm

/-- **Larsen–Skou bisimilarity is logical distance zero**: agreement on every
functional expression. -/
theorem lsBisimilar_iff_logicalDistance_eq_zero [Fintype A] [Fintype Atom] {c : ℝ}
    (c_pos : 0 < c) (c_le : c ≤ 1) {x y : S} :
    (chainSystem P).LSBisimilar x y ↔ logicalDistance P c x y = 0 :=
  lsBisimilar_iff_probabilisticallyBisimilar.trans (logicalDistance_eq_zero_iff c_pos c_le).symm

end Mettapedia.GSLT.Distinction.Probabilistic
