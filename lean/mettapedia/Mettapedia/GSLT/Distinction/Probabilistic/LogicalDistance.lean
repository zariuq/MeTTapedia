import Mettapedia.GSLT.Distinction.Probabilistic.KantorovichDuality

/-!
# The bisimulation metric is the logical distance

On a finite labelled Markov chain at a discount `0 ≤ c ≤ 1`, the bisimulation
metric of `Cybernetics.ApproximateAdequacy.BisimulationMetric` (the least fixed
point of the Kantorovich operator) is the supremum, over all functional
expressions, of the difference of their values
(`bisimulationMetric_eq_logicalDistance`).  This is the theorem of
J. Desharnais, V. Gupta, R. Jagadeesan and P. Panangaden (*Metrics for labelled
Markov processes*, TCS 318, 2004), in the fixed-point form of F. van Breugel
and J. Worrell.  The library had the soundness half; the completeness half is
new here and rests on Kantorovich duality (`KantorovichDuality`).

The same proof works depth by depth: the `n`-th Kantorovich iterate is the
supremum over expressions of modal depth at most `n`
(`approxMetric_eq_depthDistance`).

**Proof.**  Let `δ` be the logical distance over a set `E` of expressions closed
under the lattice operations, truncated subtraction, `1 −` and constants.
* *Lattice approximation* (`exists_close_expression`): every nonnegative
  function `f` with `f x - f y ≤ δ x y` is uniformly approximated, on the
  finitely many states, by an expression of `E`.  For each pair of states an
  expression of `E` matches `f` at both, up to `η`
  (`exists_pair_expression`): an expression separating the pair, translated
  and clamped between the two values of `f`.  The maximum over `x` of the
  minimum over `y` of these matches `f` everywhere.
* *Prefixed point* (`mul_kantorovich_le_distanceOver`): if `c` times the
  Kantorovich lifting of `δ` exceeded `δ s t`, duality would give a function `f`
  as above whose expectations under the successor distributions differ by
  more than `δ s t / c`; its approximation `F` would make `next a F` differ by
  more than `δ s t`.
* So `δ` is a prefixed point of the operator, hence above its least fixed
  point, the metric; soundness gives the converse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.Probabilistic

open Mettapedia.Cybernetics.ApproximateAdequacy
open FunctionalExpression

variable {A Atom S : Type*} [Fintype S]

/-! ## Sets of expressions closed under the lattice operations -/

/-- A set of functional expressions containing `one` and closed under `1 −`,
truncated subtraction, `min` and `max`. -/
structure LatticeClosed (E : Set (FunctionalExpression ℝ A Atom)) : Prop where
  one_mem : FunctionalExpression.one ∈ E
  oneMinus_mem : ∀ {φ}, φ ∈ E → FunctionalExpression.oneMinus φ ∈ E
  sub_mem : ∀ {φ}, φ ∈ E → ∀ q, FunctionalExpression.sub φ q ∈ E
  min_mem : ∀ {φ ψ}, φ ∈ E → ψ ∈ E → FunctionalExpression.min φ ψ ∈ E
  max_mem : ∀ {φ ψ}, φ ∈ E → ψ ∈ E → FunctionalExpression.max φ ψ ∈ E

/-- The constant expression with a nonnegative value `r`. -/
def constant (r : ℝ) : FunctionalExpression ℝ A Atom :=
  .sub .one (1 - r)

theorem eval_constant (P : LabelledMarkovChain ℝ A Atom S) (c : ℝ) {r : ℝ} (nonneg : 0 ≤ r)
    (s : S) : (constant r).eval P c s = r := by
  simp [constant, eval, nonneg]

theorem LatticeClosed.constant_mem {E : Set (FunctionalExpression ℝ A Atom)}
    (closed : LatticeClosed E) (r : ℝ) : constant r ∈ E :=
  closed.sub_mem closed.one_mem _

/-- All expressions. -/
theorem latticeClosed_univ : LatticeClosed (Set.univ : Set (FunctionalExpression ℝ A Atom)) :=
  ⟨trivial, fun _ => trivial, fun _ _ => trivial, fun _ _ => trivial, fun _ _ => trivial⟩

/-- The expressions of modal depth at most `n`. -/
def depthAtMost (n : ℕ) : Set (FunctionalExpression ℝ A Atom) := {φ | φ.depth ≤ n}

theorem mem_depthAtMost {φ : FunctionalExpression ℝ A Atom} {n : ℕ} :
    φ ∈ depthAtMost n ↔ φ.depth ≤ n :=
  Iff.rfl

theorem latticeClosed_depthAtMost (n : ℕ) : LatticeClosed (depthAtMost (A := A) (Atom := Atom) n) where
  one_mem := mem_depthAtMost.mpr (Nat.zero_le n)
  oneMinus_mem member := mem_depthAtMost.mpr (mem_depthAtMost.mp member)
  sub_mem member _ := mem_depthAtMost.mpr (mem_depthAtMost.mp member)
  min_mem first second :=
    mem_depthAtMost.mpr (max_le (mem_depthAtMost.mp first) (mem_depthAtMost.mp second))
  max_mem first second :=
    mem_depthAtMost.mpr (max_le (mem_depthAtMost.mp first) (mem_depthAtMost.mp second))

/-! ## Finite minima and maxima -/

/-- The minimum of a default expression and a list of expressions. -/
def minOver (default : FunctionalExpression ℝ A Atom) :
    List (FunctionalExpression ℝ A Atom) → FunctionalExpression ℝ A Atom
  | [] => default
  | φ :: rest => .min φ (minOver default rest)

/-- The maximum of a default expression and a list of expressions. -/
def maxOver (default : FunctionalExpression ℝ A Atom) :
    List (FunctionalExpression ℝ A Atom) → FunctionalExpression ℝ A Atom
  | [] => default
  | φ :: rest => .max φ (maxOver default rest)

section Folds

variable (P : LabelledMarkovChain ℝ A Atom S) (c : ℝ) (default : FunctionalExpression ℝ A Atom)
  (s : S)

theorem minOver_mem {E : Set (FunctionalExpression ℝ A Atom)} (closed : LatticeClosed E)
    (inside : default ∈ E) :
    ∀ L : List (FunctionalExpression ℝ A Atom), (∀ φ ∈ L, φ ∈ E) → minOver default L ∈ E
  | [], _ => inside
  | φ :: rest, all => closed.min_mem (all φ (List.mem_cons_self ..))
      (minOver_mem closed inside rest fun ψ member => all ψ (List.mem_cons_of_mem _ member))

theorem maxOver_mem {E : Set (FunctionalExpression ℝ A Atom)} (closed : LatticeClosed E)
    (inside : default ∈ E) :
    ∀ L : List (FunctionalExpression ℝ A Atom), (∀ φ ∈ L, φ ∈ E) → maxOver default L ∈ E
  | [], _ => inside
  | φ :: rest, all => closed.max_mem (all φ (List.mem_cons_self ..))
      (maxOver_mem closed inside rest fun ψ member => all ψ (List.mem_cons_of_mem _ member))

theorem eval_minOver_le_default :
    ∀ L : List (FunctionalExpression ℝ A Atom),
      (minOver default L).eval P c s ≤ default.eval P c s
  | [] => le_rfl
  | _ :: rest => (min_le_right _ _).trans (eval_minOver_le_default rest)

theorem eval_minOver_le :
    ∀ (L : List (FunctionalExpression ℝ A Atom)) {φ}, φ ∈ L →
      (minOver default L).eval P c s ≤ φ.eval P c s
  | [], _, member => absurd member List.not_mem_nil
  | ψ :: rest, φ, member => by
      rcases List.mem_cons.mp member with same | inside
      · subst same
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (eval_minOver_le rest inside)

theorem le_eval_minOver {b : ℝ} (first : b ≤ default.eval P c s) :
    ∀ L : List (FunctionalExpression ℝ A Atom), (∀ φ ∈ L, b ≤ φ.eval P c s) →
      b ≤ (minOver default L).eval P c s
  | [], _ => first
  | φ :: rest, all => le_min (all φ (List.mem_cons_self ..))
      (le_eval_minOver first rest fun ψ member => all ψ (List.mem_cons_of_mem _ member))

theorem le_eval_maxOver :
    ∀ (L : List (FunctionalExpression ℝ A Atom)) {φ}, φ ∈ L →
      φ.eval P c s ≤ (maxOver default L).eval P c s
  | [], _, member => absurd member List.not_mem_nil
  | ψ :: rest, φ, member => by
      rcases List.mem_cons.mp member with same | inside
      · subst same
        exact le_max_left _ _
      · exact (le_eval_maxOver rest inside).trans (le_max_right _ _)

theorem eval_maxOver_le {b : ℝ} (first : default.eval P c s ≤ b) :
    ∀ L : List (FunctionalExpression ℝ A Atom), (∀ φ ∈ L, φ.eval P c s ≤ b) →
      (maxOver default L).eval P c s ≤ b
  | [], _ => first
  | φ :: rest, all => max_le (all φ (List.mem_cons_self ..))
      (eval_maxOver_le first rest fun ψ member => all ψ (List.mem_cons_of_mem _ member))

end Folds

/-! ## The logical distance over a set of expressions -/

section Distance

variable (P : LabelledMarkovChain ℝ A Atom S) (c : ℝ)

/-- **The logical distance over `E`**: the largest difference of an expression
of `E` at two states. -/
noncomputable def distanceOver (E : Set (FunctionalExpression ℝ A Atom)) (s t : S) : ℝ :=
  ⨆ φ : E, |φ.1.eval P c s - φ.1.eval P c t|

/-- **The logical distance** of Desharnais, Gupta, Jagadeesan and Panangaden:
the largest difference of a functional expression. -/
noncomputable abbrev logicalDistance (s t : S) : ℝ := distanceOver P c Set.univ s t

variable {P c} {E : Set (FunctionalExpression ℝ A Atom)}

theorem distanceOver_self (closed : LatticeClosed E) (s : S) : distanceOver P c E s s = 0 := by
  have : Nonempty E := ⟨⟨_, closed.one_mem⟩⟩
  simp [distanceOver]

theorem distanceOver_comm (s t : S) : distanceOver P c E s t = distanceOver P c E t s := by
  unfold distanceOver
  congr 1
  funext φ
  exact abs_sub_comm _ _

/-! ## Lattice approximation -/

/-- **One pair of states.**  For a nonnegative function `f` that the distance
bounds, and states `u, v` with `f v ≤ f u`, an expression of `E` takes the
value `f v` at `v` and a value within `η` below `f u` at `u`. -/
theorem exists_pair_expression (closed : LatticeClosed E)
    {f : S → ℝ} (f_nonneg : ∀ x, 0 ≤ f x) (lipschitz : ∀ x y, f x - f y ≤ distanceOver P c E x y)
    {η : ℝ} (η_pos : 0 < η) {u v : S} (oriented : f v ≤ f u) :
    ∃ h ∈ E, h.eval P c u ≤ f u ∧ f u - η ≤ h.eval P c u ∧ h.eval P c v = f v := by
  by_cases close : f u - f v < η
  · refine ⟨constant (f v), closed.constant_mem _, ?_, ?_, ?_⟩
    · rw [eval_constant P c (f_nonneg v)]
      exact oriented
    · rw [eval_constant P c (f_nonneg v)]
      linarith
    · exact eval_constant P c (f_nonneg v) v
  · have far : η ≤ f u - f v := not_lt.mp close
    have : Nonempty E := ⟨⟨_, closed.one_mem⟩⟩
    have below : distanceOver P c E u v - η < distanceOver P c E u v := by linarith
    obtain ⟨⟨φ, member⟩, separates⟩ := exists_lt_of_lt_ciSup below
    simp only at separates
    obtain ⟨ψ, inside, gap⟩ : ∃ ψ ∈ E,
        distanceOver P c E u v - η < ψ.eval P c u - ψ.eval P c v := by
      by_cases order : φ.eval P c v ≤ φ.eval P c u
      · refine ⟨φ, member, ?_⟩
        rwa [abs_of_nonneg (sub_nonneg.mpr order)] at separates
      · refine ⟨.oneMinus φ, closed.oneMinus_mem member, ?_⟩
        rw [abs_of_neg (sub_neg.mpr (not_le.mp order))] at separates
        simp only [eval]
        linarith
    have bound := lipschitz u v
    set k := f v - ψ.eval P c v
    refine ⟨.max (constant (f v)) (.min (constant (f u)) (.sub ψ (-k))),
      closed.max_mem (closed.constant_mem _)
        (closed.min_mem (closed.constant_mem _) (closed.sub_mem inside _)), ?_, ?_, ?_⟩
    · simp only [eval, eval_constant P c (f_nonneg v), eval_constant P c (f_nonneg u)]
      exact max_le oriented (min_le_left _ _)
    · simp only [eval, eval_constant P c (f_nonneg v), eval_constant P c (f_nonneg u)]
      refine le_max_of_le_right (le_min (by linarith) (le_max_of_le_left ?_))
      simp only [k]
      linarith
    · simp only [eval, eval_constant P c (f_nonneg v), eval_constant P c (f_nonneg u)]
      have translated : ψ.eval P c v - -k = f v := by simp only [k]; ring
      rw [translated, max_eq_left (f_nonneg v), min_eq_right oriented, max_self]

/-- **Lattice approximation.**  A nonnegative function that the distance over
`E` bounds is approximated within `η`, from below, by an expression of `E`. -/
theorem exists_close_expression [Nonempty S] (closed : LatticeClosed E) {f : S → ℝ}
    (f_nonneg : ∀ x, 0 ≤ f x) (lipschitz : ∀ x y, f x - f y ≤ distanceOver P c E x y) {η : ℝ}
    (η_pos : 0 < η) :
    ∃ F ∈ E, ∀ z, F.eval P c z ≤ f z ∧ f z - η ≤ F.eval P c z := by
  classical
  have pair : ∀ x y, ∃ h ∈ E, (h.eval P c x ≤ f x ∧ f x - η ≤ h.eval P c x) ∧
      (h.eval P c y ≤ f y ∧ f y - η ≤ h.eval P c y) := by
    intro x y
    by_cases order : f y ≤ f x
    · obtain ⟨h, member, upper, lower, exact⟩ :=
        exists_pair_expression closed f_nonneg lipschitz η_pos order
      exact ⟨h, member, ⟨upper, lower⟩, by rw [exact]; exact ⟨le_rfl, by linarith⟩⟩
    · obtain ⟨h, member, upper, lower, exact⟩ := exists_pair_expression closed
        f_nonneg lipschitz η_pos (le_of_lt (not_le.mp order))
      exact ⟨h, member, by rw [exact]; exact ⟨le_rfl, by linarith⟩, ⟨upper, lower⟩⟩
  choose h member spec using pair
  let g : S → FunctionalExpression ℝ A Atom := fun x =>
    minOver (h x x) (Finset.univ.toList.map (h x))
  have g_mem : ∀ x, g x ∈ E := fun x => minOver_mem _ closed (member x x) _ fun φ inside => by
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp inside
    exact member x y
  have g_upper : ∀ x z, (g x).eval P c z ≤ f z := fun x z =>
    (eval_minOver_le P c _ z _ (List.mem_map.mpr ⟨z, Finset.mem_toList.mpr (Finset.mem_univ z),
      rfl⟩)).trans (spec x z).2.1
  have g_lower : ∀ x, f x - η ≤ (g x).eval P c x := fun x =>
    le_eval_minOver P c _ x (spec x x).1.2 _ fun φ inside => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp inside
      exact (spec x y).1.2
  obtain ⟨base⟩ := (inferInstance : Nonempty S)
  refine ⟨maxOver (g base) (Finset.univ.toList.map g),
    maxOver_mem _ closed (g_mem base) _ fun φ inside => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp inside
      exact g_mem x, fun z => ⟨?_, ?_⟩⟩
  · exact eval_maxOver_le P c _ z (g_upper base z) _ fun φ inside => by
      obtain ⟨x, _, rfl⟩ := List.mem_map.mp inside
      exact g_upper x z
  · exact (g_lower z).trans (le_eval_maxOver P c _ z _
      (List.mem_map.mpr ⟨z, Finset.mem_toList.mpr (Finset.mem_univ z), rfl⟩))

variable [Fintype A] [Fintype Atom]

theorem bddAbove_distanceOver (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) (s t : S) :
    BddAbove (Set.range fun φ : E => |φ.1.eval P c s - φ.1.eval P c t|) :=
  ⟨bisimulationMetric P P c s t, by
    rintro _ ⟨φ, rfl⟩
    exact abs_eval_sub_le_bisimulationMetric c_nonneg c_le φ.1 s t⟩

theorem abs_eval_sub_le_distanceOver (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) {φ} (member : φ ∈ E)
    (s t : S) : |φ.eval P c s - φ.eval P c t| ≤ distanceOver P c E s t :=
  le_ciSup (bddAbove_distanceOver c_nonneg c_le s t) ⟨φ, member⟩

theorem distanceOver_le_bisimulationMetric (closed : LatticeClosed E) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) (s t : S) : distanceOver P c E s t ≤ bisimulationMetric P P c s t :=
  have : Nonempty E := ⟨⟨_, closed.one_mem⟩⟩
  ciSup_le fun φ => abs_eval_sub_le_bisimulationMetric c_nonneg c_le φ.1 s t

theorem distanceOver_nonneg (closed : LatticeClosed E) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (s t : S) : 0 ≤ distanceOver P c E s t :=
  (abs_nonneg _).trans (abs_eval_sub_le_distanceOver c_nonneg c_le closed.one_mem s t)

theorem distanceOver_triangle (closed : LatticeClosed E) (c_nonneg : 0 ≤ c) (c_le : c ≤ 1)
    (s t u : S) : distanceOver P c E s u ≤ distanceOver P c E s t + distanceOver P c E t u :=
  have : Nonempty E := ⟨⟨_, closed.one_mem⟩⟩
  ciSup_le fun φ => (abs_sub_le _ (φ.1.eval P c t) _).trans
    (add_le_add (abs_eval_sub_le_distanceOver c_nonneg c_le φ.2 s t)
      (abs_eval_sub_le_distanceOver c_nonneg c_le φ.2 t u))

/-! ## The distance is a prefixed point of the Kantorovich operator -/

/-- **The Kantorovich step of the distance over `E`** is bounded by the distance
over any `E'` that contains `next a φ` for every `φ ∈ E`. -/
theorem mul_kantorovich_le_distanceOver (closed : LatticeClosed E) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) {E' : Set (FunctionalExpression ℝ A Atom)} (a : A)
    (next_mem : ∀ φ ∈ E, FunctionalExpression.next a φ ∈ E') (s t : S) :
    c * kantorovich (distanceOver P c E) (P.trans a s) (P.trans a t) ≤
      distanceOver P c E' s t := by
  have target_nonneg : 0 ≤ distanceOver P c E' s t :=
    (abs_nonneg _).trans (abs_eval_sub_le_distanceOver c_nonneg c_le
      (next_mem _ closed.one_mem) s t)
  rcases c_nonneg.eq_or_lt with zero | c_pos
  · have vanish : c * kantorovich (distanceOver P c E) (P.trans a s) (P.trans a t) = 0 := by
      rw [← zero, zero_mul]
    rw [vanish]
    exact target_nonneg
  by_contra not_le'
  have greater := not_le.mp not_le'
  have : Nonempty S := ⟨s⟩
  have lt : distanceOver P c E' s t / c <
      kantorovich (distanceOver P c E) (P.trans a s) (P.trans a t) := by
    rw [div_lt_iff₀ c_pos, mul_comm]
    exact greater
  obtain ⟨f, lipschitz, value⟩ := exists_lipschitz_of_lt_kantorovich (P.isDistribution a s)
    (P.isDistribution a t) (distanceOver_self closed)
    (distanceOver_triangle closed c_nonneg c_le) lt
  set low := Finset.univ.inf' Finset.univ_nonempty f
  set f' : S → ℝ := fun x => f x + -low
  have f'_nonneg : ∀ x, 0 ≤ f' x := fun x => by
    have := Finset.inf'_le f (Finset.mem_univ x)
    simp only [f']
    linarith
  have f'_lipschitz : ∀ x y, f' x - f' y ≤ distanceOver P c E x y := fun x y => by
    simp only [f']
    linarith [lipschitz x y]
  have shift : ∀ μ : S → ℝ, IsDistribution μ → expect μ f' = expect μ f + -low := fun μ dist => by
    rw [expect_add, expect_const dist]
  set gap := expect (P.trans a s) f - expect (P.trans a t) f -
    distanceOver P c E' s t / c
  have gap_pos : 0 < gap := by simp only [gap]; linarith
  obtain ⟨F, inside, close⟩ := exists_close_expression closed f'_nonneg f'_lipschitz
    (half_pos gap_pos)
  have upper : expect (P.trans a t) (F.eval P c) ≤ expect (P.trans a t) f' :=
    expect_mono (P.isDistribution a t) fun z => (close z).1
  have lower : expect (P.trans a s) f' + -(gap / 2) ≤ expect (P.trans a s) (F.eval P c) := by
    rw [← expect_const (P.isDistribution a s) (-(gap / 2)), ← expect_add]
    exact expect_mono (P.isDistribution a s) fun z => by linarith [(close z).2]
  rw [shift _ (P.isDistribution a s)] at lower
  rw [shift _ (P.isDistribution a t)] at upper
  have bound := abs_eval_sub_le_distanceOver (P := P) c_nonneg c_le (next_mem F inside) s t
  simp only [eval] at bound
  have difference : distanceOver P c E' s t / c <
      expect (P.trans a s) (F.eval P c) - expect (P.trans a t) (F.eval P c) := by
    simp only [gap] at lower
    linarith
  have scaled : distanceOver P c E' s t <
      c * expect (P.trans a s) (F.eval P c) - c * expect (P.trans a t) (F.eval P c) := by
    rw [← mul_sub, ← div_lt_iff₀' c_pos]
    exact difference
  exact absurd (bound.trans' (le_abs_self _)) (not_le.mpr scaled)

/-- The observation distance is below the distance over every `E` containing
the observables. -/
theorem observationDistance_le_distanceOver (closed : LatticeClosed E) (c_nonneg : 0 ≤ c)
    (c_le : c ≤ 1) (observe_mem : ∀ i, FunctionalExpression.observe i ∈ E) (s t : S) :
    observationDistance P P s t ≤ distanceOver P c E s t :=
  (observationDistance_le_iff P P).mpr ⟨distanceOver_nonneg closed c_nonneg c_le s t,
    fun i => abs_eval_sub_le_distanceOver c_nonneg c_le (observe_mem i) s t⟩

/-! ## The characterisation -/

/-- **The bisimulation metric is the logical distance** (Desharnais, Gupta,
Jagadeesan and Panangaden): on a finite chain at a discount `0 ≤ c ≤ 1`, the
least fixed point of the Kantorovich operator is the largest difference of a
functional expression. -/
theorem bisimulationMetric_eq_logicalDistance (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    bisimulationMetric P P c = logicalDistance P c := by
  funext s t
  refine le_antisymm (bisimulationMetric_le_of_step_le c_nonneg (fun x y => ?_) s t)
    (distanceOver_le_bisimulationMetric latticeClosed_univ c_nonneg c_le s t)
  exact kantorovichStep_le_iff.mpr
    ⟨observationDistance_le_distanceOver latticeClosed_univ c_nonneg c_le
        (fun i => Set.mem_univ _) x y,
      fun a => mul_kantorovich_le_distanceOver (E' := Set.univ) latticeClosed_univ c_nonneg c_le a
        (fun _ _ => Set.mem_univ _) x y⟩

/-- **The iterates are the depth-bounded logical distances**: the `n`-th
Kantorovich iterate from the observation distance is the largest difference of
an expression of modal depth at most `n`. -/
theorem approxMetric_eq_depthDistance (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    ∀ n, approxMetric P P c n = distanceOver P c (depthAtMost n)
  | 0 => by
      funext s t
      refine le_antisymm (observationDistance_le_distanceOver (latticeClosed_depthAtMost 0)
        c_nonneg c_le (fun _ => mem_depthAtMost.mpr (Nat.zero_le 0)) s t) ?_
      have : Nonempty (depthAtMost (A := A) (Atom := Atom) 0) :=
        ⟨⟨_, (latticeClosed_depthAtMost 0).one_mem⟩⟩
      exact ciSup_le fun φ => abs_eval_sub_le_approxMetric c_nonneg φ.1 0 φ.2 s t
  | n + 1 => by
      funext s t
      have previous := approxMetric_eq_depthDistance c_nonneg c_le n
      refine le_antisymm ?_ ?_
      · change kantorovichStep P P c (approxMetric P P c n) s t ≤ _
        rw [previous]
        exact kantorovichStep_le_iff.mpr
          ⟨observationDistance_le_distanceOver (latticeClosed_depthAtMost (n + 1)) c_nonneg c_le
              (fun _ => mem_depthAtMost.mpr (Nat.zero_le _)) s t,
            fun a => mul_kantorovich_le_distanceOver (latticeClosed_depthAtMost n) c_nonneg c_le a
              (fun φ member => mem_depthAtMost.mpr
                (Nat.succ_le_succ (mem_depthAtMost.mp member))) s t⟩
      · have : Nonempty (depthAtMost (A := A) (Atom := Atom) (n + 1)) :=
          ⟨⟨_, (latticeClosed_depthAtMost (n + 1)).one_mem⟩⟩
        exact ciSup_le fun φ => abs_eval_sub_le_approxMetric c_nonneg φ.1 (n + 1) φ.2 s t

/-- **The logical distance is a fixed point of the Kantorovich operator.** -/
theorem logicalDistance_eq_step (c_nonneg : 0 ≤ c) (c_le : c ≤ 1) :
    logicalDistance P c = kantorovichStep P P c (logicalDistance P c) := by
  rw [← bisimulationMetric_eq_logicalDistance c_nonneg c_le]
  exact bisimulationMetric_eq_step c_nonneg c_le

/-- **Distance zero, bisimilarity and logical equivalence**: at a positive
discount the logical distance vanishes exactly on probabilistic bisimilarity. -/
theorem logicalDistance_eq_zero_iff (c_pos : 0 < c) (c_le : c ≤ 1) {s t : S} :
    logicalDistance P c s t = 0 ↔ ProbabilisticallyBisimilar P P s t := by
  rw [← bisimulationMetric_eq_logicalDistance c_pos.le c_le]
  exact bisimulationMetric_eq_zero_iff c_pos c_le

end Distance

end Mettapedia.GSLT.Distinction.Probabilistic
