import Mettapedia.Cybernetics.ApproximateAdequacy.BisimulationMetric

/-!
# Functional expressions characterise probabilistic bisimilarity

On a finite labelled Markov chain at a positive discount, two states that
take the same value on every functional expression are probabilistically
bisimilar (`isProbabilisticBisimulation_logicallyEquivalent`).  With the
soundness direction (`IsProbabilisticBisimulation.eval_eq`) and the zero set
of the bisimulation metric (`bisimulationMetric_eq_zero_iff`), three
conditions coincide (`bisimulationMetric_eq_zero_iff_logicallyEquivalent`):

* the bisimulation metric vanishes;
* the states are probabilistically bisimilar;
* no functional expression distinguishes them.

This is the qualitative half of the logical characterisation of K. G. Larsen
and A. Skou, in the real-valued logic of Desharnais, Gupta, Jagadeesan and
Panangaden.  The quantitative half, that the metric is the largest
difference of an expression, needs Kantorovich duality and is not proved
here.

**Proof.**  For each class `C` of logical equivalence an expression `χ_C`
takes a positive constant value on `C` and `0` elsewhere: a finite minimum of
truncated subtractions, one separating `C` from each state outside it
(`classExpression`).  Then `next a χ_C` reads the mass of `C` under the
successor distribution, so equivalent states give every class the same mass
(`classMass_eq`), and equal class masses yield a coupling supported on the
equivalence (`classCoupling`).
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.ApproximateAdequacy

open Finset FunctionalExpression

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  {A Atom S : Type*} [Fintype S]

/-- Two states agree on every functional expression. -/
def LogicallyEquivalent (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜) (s t : S) : Prop :=
  ∀ φ : FunctionalExpression 𝕜 A Atom, φ.eval P c s = φ.eval P c t

namespace LogicallyEquivalent

variable {P : LabelledMarkovChain 𝕜 A Atom S} {c : 𝕜}

omit [IsStrictOrderedRing 𝕜] in
theorem refl (s : S) : LogicallyEquivalent P c s s := fun _ => rfl

omit [IsStrictOrderedRing 𝕜] in
theorem symm {s t : S} (same : LogicallyEquivalent P c s t) : LogicallyEquivalent P c t s :=
  fun φ => (same φ).symm

omit [IsStrictOrderedRing 𝕜] in
theorem trans {s t u : S} (first : LogicallyEquivalent P c s t)
    (second : LogicallyEquivalent P c t u) : LogicallyEquivalent P c s u :=
  fun φ => (first φ).trans (second φ)

end LogicallyEquivalent

/-! ## Minima of finitely many expressions -/

/-- The minimum of a list of expressions, capped by `one`. -/
def minAll : List (FunctionalExpression 𝕜 A Atom) → FunctionalExpression 𝕜 A Atom
  | [] => .one
  | φ :: rest => .min φ (minAll rest)

section MinAll

variable (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜)

theorem eval_minAll_nonneg (s : S) :
    ∀ L : List (FunctionalExpression 𝕜 A Atom), (∀ φ ∈ L, 0 ≤ φ.eval P c s) →
      0 ≤ (minAll L).eval P c s
  | [], _ => by simp [minAll, eval]
  | φ :: rest, nonneg => by
      simp only [minAll, eval]
      exact le_min (nonneg φ (List.mem_cons_self ..))
        (eval_minAll_nonneg s rest fun ψ member => nonneg ψ (List.mem_cons_of_mem _ member))

omit [IsStrictOrderedRing 𝕜] in
theorem eval_minAll_le (s : S) :
    ∀ (L : List (FunctionalExpression 𝕜 A Atom)) {φ}, φ ∈ L → (minAll L).eval P c s ≤ φ.eval P c s
  | [], _, member => absurd member List.not_mem_nil
  | ψ :: rest, φ, member => by
      simp only [minAll, eval]
      rcases List.mem_cons.mp member with same | inside
      · subst same
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (eval_minAll_le s rest inside)

theorem eval_minAll_pos (s : S) :
    ∀ L : List (FunctionalExpression 𝕜 A Atom), (∀ φ ∈ L, 0 < φ.eval P c s) →
      0 < (minAll L).eval P c s
  | [], _ => by simp [minAll, eval]
  | φ :: rest, positive => by
      simp only [minAll, eval]
      exact lt_min (positive φ (List.mem_cons_self ..))
        (eval_minAll_pos s rest fun ψ member => positive ψ (List.mem_cons_of_mem _ member))

end MinAll

/-! ## Separating expressions -/

section Separation

variable (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜)

/-- The expression separating `x` from `y` built from an expression `φ` with
different values at them: positive at `x`, zero at `y`, nonnegative
everywhere. -/
def separatorOf (φ : FunctionalExpression 𝕜 A Atom) (x y : S) : FunctionalExpression 𝕜 A Atom :=
  if φ.eval P c y < φ.eval P c x then .sub φ (φ.eval P c y)
  else .sub (.oneMinus φ) (1 - φ.eval P c y)

omit [IsStrictOrderedRing 𝕜] in
theorem separatorOf_nonneg (φ : FunctionalExpression 𝕜 A Atom) (x y z : S) :
    0 ≤ (separatorOf P c φ x y).eval P c z := by
  unfold separatorOf
  split_ifs <;> simp [eval]

omit [IsStrictOrderedRing 𝕜] in
theorem separatorOf_self_zero (φ : FunctionalExpression 𝕜 A Atom) (x y : S) :
    (separatorOf P c φ x y).eval P c y = 0 := by
  unfold separatorOf
  split_ifs <;> simp [eval]

theorem separatorOf_pos {φ : FunctionalExpression 𝕜 A Atom} {x y : S}
    (separates : φ.eval P c x ≠ φ.eval P c y) : 0 < (separatorOf P c φ x y).eval P c x := by
  unfold separatorOf
  split_ifs with lt
  · simp only [eval]
    exact lt_max_of_lt_left (sub_pos.mpr lt)
  · simp only [eval]
    have gt : φ.eval P c x < φ.eval P c y := lt_of_le_of_ne (not_lt.mp lt) separates
    exact lt_max_of_lt_left (by linarith)

open Classical in
/-- An expression separating `x` from `y` when they are not equivalent, and
`one` otherwise. -/
noncomputable def separator (x y : S) : FunctionalExpression 𝕜 A Atom :=
  if different : LogicallyEquivalent P c x y then .one
  else separatorOf P c (Classical.choose (not_forall.mp different)) x y

theorem separator_nonneg (x y z : S) : 0 ≤ (separator P c x y).eval P c z := by
  unfold separator
  split_ifs
  · simp [eval]
  · exact separatorOf_nonneg P c _ x y z

omit [IsStrictOrderedRing 𝕜] in
theorem separator_self_zero {x y : S} (different : ¬ LogicallyEquivalent P c x y) :
    (separator P c x y).eval P c y = 0 := by
  unfold separator
  rw [dif_neg different]
  exact separatorOf_self_zero P c _ x y

theorem separator_pos {x y : S} (different : ¬ LogicallyEquivalent P c x y) :
    0 < (separator P c x y).eval P c x := by
  unfold separator
  rw [dif_neg different]
  exact separatorOf_pos P c (Classical.choose_spec (not_forall.mp different))

end Separation

/-! ## Class expressions and class masses -/

section Classes

variable (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜)

open Classical in
/-- The logical equivalence class of `x`. -/
noncomputable def logicalClass (x : S) : Finset S :=
  Finset.univ.filter fun y => LogicallyEquivalent P c x y

omit [IsStrictOrderedRing 𝕜] in
theorem mem_logicalClass {x y : S} : y ∈ logicalClass P c x ↔ LogicallyEquivalent P c x y := by
  classical
  simp [logicalClass]

open Classical in
/-- **The class expression** of `x`: positive and constant on the class of `x`,
zero outside it. -/
noncomputable def classExpression (x : S) : FunctionalExpression 𝕜 A Atom :=
  minAll ((Finset.univ.filter fun y => ¬ LogicallyEquivalent P c x y).toList.map (separator P c x))

theorem classExpression_pos (x : S) : 0 < (classExpression P c x).eval P c x := by
  classical
  refine eval_minAll_pos P c x _ fun φ member => ?_
  obtain ⟨y, inside, rfl⟩ := List.mem_map.mp member
  rw [Finset.mem_toList, Finset.mem_filter] at inside
  exact separator_pos P c inside.2

theorem classExpression_eq_zero {x y : S} (different : ¬ LogicallyEquivalent P c x y) :
    (classExpression P c x).eval P c y = 0 := by
  classical
  apply le_antisymm
  · have le := eval_minAll_le P c y
      ((Finset.univ.filter fun y => ¬ LogicallyEquivalent P c x y).toList.map (separator P c x))
      (φ := separator P c x y) (List.mem_map.mpr ⟨y, by simp [different], rfl⟩)
    rw [separator_self_zero P c different] at le
    exact le
  · exact eval_minAll_nonneg P c y _ fun φ member => by
      obtain ⟨z, _, rfl⟩ := List.mem_map.mp member
      exact separator_nonneg P c x z y

omit [IsStrictOrderedRing 𝕜] in
theorem classExpression_eq {x y : S} (same : LogicallyEquivalent P c x y) :
    (classExpression P c x).eval P c y = (classExpression P c x).eval P c x :=
  (same _).symm

/-- The mass of the class of `x` under a weighting. -/
noncomputable def classMass (μ : S → 𝕜) (x : S) : 𝕜 :=
  ∑ y ∈ logicalClass P c x, μ y

/-- **`next a` of a class expression reads the class mass.** -/
theorem eval_next_classExpression (a : A) (s x : S) :
    (FunctionalExpression.next a (classExpression P c x)).eval P c s =
      c * ((classExpression P c x).eval P c x * classMass P c (P.trans a s) x) := by
  classical
  simp only [eval, expect, classMass]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun y => LogicallyEquivalent P c x y)]
  have outside : ∑ y ∈ Finset.univ.filter (fun y => ¬ LogicallyEquivalent P c x y),
      P.trans a s y * (classExpression P c x).eval P c y = 0 :=
    Finset.sum_eq_zero fun y member => by
      rw [Finset.mem_filter] at member
      rw [classExpression_eq_zero P c member.2, mul_zero]
  rw [outside, add_zero]
  refine Finset.sum_congr (by ext y; simp [logicalClass]) fun y member => ?_
  rw [classExpression_eq P c ((mem_logicalClass P c).mp member)]
  ring

/-- **Equivalent states give every class the same mass**, at a positive
discount. -/
theorem classMass_eq (c_pos : 0 < c) {s t : S} (same : LogicallyEquivalent P c s t) (a : A)
    (x : S) : classMass P c (P.trans a s) x = classMass P c (P.trans a t) x := by
  have agree := same (FunctionalExpression.next a (classExpression P c x))
  rw [eval_next_classExpression, eval_next_classExpression] at agree
  have nonzero : c * (classExpression P c x).eval P c x ≠ 0 :=
    (mul_pos c_pos (classExpression_pos P c x)).ne'
  rw [← mul_assoc, ← mul_assoc] at agree
  exact mul_left_cancel₀ nonzero agree

omit [IsStrictOrderedRing 𝕜] in
theorem logicalClass_eq {x y : S} (same : LogicallyEquivalent P c x y) :
    logicalClass P c x = logicalClass P c y := by
  ext z
  rw [mem_logicalClass, mem_logicalClass]
  exact ⟨fun first => same.symm.trans first, fun second => same.trans second⟩

omit [IsStrictOrderedRing 𝕜] in
theorem classMass_congr (μ : S → 𝕜) {x y : S} (same : LogicallyEquivalent P c x y) :
    classMass P c μ x = classMass P c μ y := by
  unfold classMass
  rw [logicalClass_eq P c same]

omit [IsStrictOrderedRing 𝕜] in
theorem self_mem_logicalClass (x : S) : x ∈ logicalClass P c x :=
  (mem_logicalClass P c).mpr (LogicallyEquivalent.refl x)

end Classes

/-! ## The coupling from equal class masses -/

section Coupling

variable (P : LabelledMarkovChain 𝕜 A Atom S) (c : 𝕜)

theorem eq_zero_of_classMass_eq_zero {μ : S → 𝕜} (distribution : IsDistribution μ) {x : S}
    (zero : classMass P c μ x = 0) : μ x = 0 := by
  have terms := (Finset.sum_eq_zero_iff_of_nonneg fun y _ => distribution.nonneg y).mp zero
  exact terms x (self_mem_logicalClass P c x)

open Classical in
/-- **The coupling of two distributions with equal class masses**, supported on
logical equivalence. -/
noncomputable def classCoupling {μ ν : S → 𝕜} (first : IsDistribution μ) (second : IsDistribution ν)
    (masses : ∀ x, classMass P c μ x = classMass P c ν x) : Coupling μ ν where
  weight y z := if LogicallyEquivalent P c y z then μ y * ν z / classMass P c ν z else 0
  nonneg y z := by
    split_ifs
    · exact div_nonneg (mul_nonneg (first.nonneg y) (second.nonneg z))
        (Finset.sum_nonneg fun w _ => second.nonneg w)
    · exact le_rfl
  sum_right y := by
    rw [← Finset.sum_filter]
    have rewrite : ∀ z ∈ Finset.univ.filter (fun z => LogicallyEquivalent P c y z),
        μ y * ν z / classMass P c ν z = μ y * ν z / classMass P c ν y := fun z member => by
      rw [Finset.mem_filter] at member
      rw [classMass_congr P c ν member.2]
    rw [Finset.sum_congr rfl rewrite, ← Finset.sum_div, ← Finset.mul_sum]
    have classSum : ∑ z ∈ Finset.univ.filter (fun z => LogicallyEquivalent P c y z), ν z =
        classMass P c ν y := by
      unfold classMass logicalClass
      rfl
    rw [classSum]
    by_cases zero : classMass P c ν y = 0
    · rw [zero, div_zero]
      exact (eq_zero_of_classMass_eq_zero P c first ((masses y).trans zero)).symm
    · rw [mul_div_assoc, div_self zero, mul_one]
  sum_left z := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_div, ← Finset.sum_mul]
    have classSum : ∑ y ∈ Finset.univ.filter (fun y => LogicallyEquivalent P c y z), μ y =
        classMass P c μ z := by
      unfold classMass
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext y
      rw [Finset.mem_filter, mem_logicalClass]
      exact ⟨fun member => member.2.symm, fun member => ⟨Finset.mem_univ y, member.symm⟩⟩
    rw [classSum, masses z]
    by_cases zero : classMass P c ν z = 0
    · rw [zero, zero_mul, zero_div]
      exact (eq_zero_of_classMass_eq_zero P c second zero).symm
    · rw [mul_comm, mul_div_assoc, div_self zero, mul_one]

theorem classCoupling_supported {μ ν : S → 𝕜} (first : IsDistribution μ) (second : IsDistribution ν)
    (masses : ∀ x, classMass P c μ x = classMass P c ν x) {y z : S}
    (positive : (classCoupling P c first second masses).weight y z ≠ 0) :
    LogicallyEquivalent P c y z := by
  classical
  by_contra different
  exact positive (if_neg different)

end Coupling

/-! ## The characterisation -/

variable {P : LabelledMarkovChain 𝕜 A Atom S} {c : 𝕜}

/-- **Logical equivalence is a probabilistic bisimulation**, at a positive
discount. -/
theorem isProbabilisticBisimulation_logicallyEquivalent (c_pos : 0 < c) :
    IsProbabilisticBisimulation P P (LogicallyEquivalent P c) := by
  intro s t same
  refine ⟨fun i => same (.observe i), fun a => ?_⟩
  exact ⟨classCoupling P c (P.isDistribution a s) (P.isDistribution a t)
      (classMass_eq P c c_pos same a),
    fun y z positive => classCoupling_supported P c _ _ _ positive⟩

/-- **Bisimilarity is logical equivalence**, at a positive discount. -/
theorem probabilisticallyBisimilar_iff_logicallyEquivalent (c_pos : 0 < c) {s t : S} :
    ProbabilisticallyBisimilar P P s t ↔ LogicallyEquivalent P c s t :=
  ⟨fun bisimilar φ => bisimilar.eval_eq c φ,
    fun same => ⟨_, isProbabilisticBisimulation_logicallyEquivalent c_pos, same⟩⟩

variable [Fintype A] [Fintype Atom]

/-- **Zero distance, bisimilarity and logical equivalence coincide.** -/
theorem bisimulationMetric_eq_zero_iff_logicallyEquivalent {P : LabelledMarkovChain ℝ A Atom S}
    {c : ℝ} (c_pos : 0 < c) (c_le : c ≤ 1) {s t : S} :
    bisimulationMetric P P c s t = 0 ↔ LogicallyEquivalent P c s t :=
  (bisimulationMetric_eq_zero_iff c_pos c_le).trans
    (probabilisticallyBisimilar_iff_logicallyEquivalent c_pos)

end Mettapedia.Cybernetics.ApproximateAdequacy
