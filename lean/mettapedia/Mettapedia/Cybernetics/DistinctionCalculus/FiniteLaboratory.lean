import Mettapedia.Cybernetics.DistinctionCalculus.SanityTheorems

/-!
# A finite laboratory for pattern, closure and resonance

Goertzel, *Hyperseed in the d-Calculus*, ch. 5. Statement identifiers `HS5.*`
are the chapter's. Three objects, two contexts, and the source's numbers.

* **Path laws on tolerances** (`HS5.03`, `HS5.04`). For each path law the path
  closure of a tolerance is reflexive, above it, transitive for the law, and the
  least such kernel; for symmetric laws it is symmetric. The Łukasiewicz
  closure is the shortest-path metric closure, the product closure the least
  reflexive max-product-stable relation, the minimum closure the least
  ultrametric tolerance, and `α ≤ α♭ ≤ α× ≤ α∞`. Closure minimizes every
  nonnegative linear cost among coherent coarsenings.
* **Patterns** (`HS5.02`). The two-channel product score and the truth
  conjunction move in different orders as a pattern grows; their empty values
  are `B` and `T`.
* **Fixed-source resonance** (`HS5.06`–`HS5.09`). The gate `t ↦ t ∨ k s` is the
  nearest point of a box, monotone, inflationary, idempotent and nonexpansive,
  and it moves the receiver toward the source by at least its own step. The
  decision proxy changes by half the change in bias, so evidence growth alone
  does not raise it; opposition-only transfer never raises it. Interference
  changes by an explicit linear form in the receiver edit.
* **The source's experiment.** Every number of the chapter's tables is checked
  exactly over the rationals: weakness, closures, transport, completion costs,
  task scores, report distances, proxies and interference.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u v w

/-! ## Path closures of tolerances (`HS5.03`, `HS5.04`) -/

section PathClosure

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u}

/-- A tolerance read as channel gains. -/
def Tolerance.gains (a : Tolerance V R) : GainMatrix V R := ⟨a.similarity, a.nonnegative, a.bounded⟩

variable [Fintype V] [Nonempty V] [DecidableEq V]

/-- The unit vector at `y`. -/
def unitAt (y : V) : V → R := fun z => if z = y then 1 else 0

omit [Fintype V] [Nonempty V] in
theorem unitAt_mem (y : V) : InCube (unitAt (R := R) y) := fun z => by
  unfold unitAt
  split_ifs <;> norm_num

/-- **The path closure** of a tolerance under a path law: the strongest walk from
`x` to `y`, computed with at most `|V| − 1` steps. -/
def pathClosure (L : PathLaw R) (a : Tolerance V R) (x y : V) : R :=
  propagationClosure L a.gains (unitAt y) x

variable (L : PathLaw R) (a : Tolerance V R)

theorem pathClosure_mem (x y : V) : 0 ≤ pathClosure L a x y ∧ pathClosure L a x y ≤ 1 :=
  iterate_mem (unitAt_mem y) _ x

theorem pathClosure_self (x : V) : pathClosure L a x x = 1 :=
  le_antisymm (pathClosure_mem L a x x).2 (by
    have h := le_propagationClosure (L := L) (A := a.gains) (unitAt x) x
    simp only [unitAt] at h
    exact h)

/-- The path closure lies above the tolerance. -/
theorem le_pathClosure (x y : V) : a.similarity x y ≤ pathClosure L a x y := by
  have walk := walkSignal_le_closure (L := L) (A := a.gains) (unitAt_mem y) x [y]
  have value : walkSignal L a.gains (unitAt y) [x, y] = a.similarity x y := by
    rw [walkSignal_cons_cons]
    show L.op (a.similarity x y) (unitAt y y) = _
    rw [unitAt, if_pos rfl, L.op_one (a.nonnegative x y) (a.bounded x y)]
  rw [value] at walk
  exact walk

omit [Fintype V] [Nonempty V] in
/-- Every walk composes with a transmission-closed column. -/
theorem op_walkSignal_le {y : V} {v : V → R} (hv : InCube v)
    (closed : ∀ w w', L.op (a.similarity w w') (v w') ≤ v w) :
    ∀ (x : V) (rest : List V),
      L.op (walkSignal L a.gains (unitAt y) (x :: rest)) (v y) ≤ v x
  | x, [] => by
      by_cases same : x = y
      · subst same
        simp [walkSignal, unitAt, L.one_op (hv x).1 (hv x).2]
      · simp only [walkSignal, unitAt, same, if_false]
        rw [L.zero_op (hv y).1 (hv y).2]
        exact (hv x).1
  | x, x' :: rest => by
      have inner := walkSignal_mem (L := L) (A := a.gains) (unitAt_mem y) (x' :: rest)
      rw [walkSignal_cons_cons]
      show L.op (L.op (a.similarity x x') _) (v y) ≤ v x
      rw [L.op_assoc (a.nonnegative x x') (a.bounded x x') inner.1 inner.2 (hv y).1 (hv y).2]
      exact (L.op_mono (a.nonnegative x x') (L.op_nonneg inner.1 (hv y).1) le_rfl
        (op_walkSignal_le hv closed x' rest)).trans (closed x x')

/-- **The path closure is transitive for its law.** -/
theorem pathClosure_trans (x y z : V) :
    L.op (pathClosure L a x y) (pathClosure L a y z) ≤ pathClosure L a x z := by
  have column : InCube fun w => pathClosure L a w z := fun w => pathClosure_mem L a w z
  have closed : ∀ w w', L.op (a.similarity w w') (pathClosure L a w' z) ≤ pathClosure L a w z := by
    intro w w'
    have fixed := accumulate_propagationClosure (L := L) (A := a.gains) (unitAt_mem (R := R) z)
    have := congrFun fixed w
    rw [accumulate_apply] at this
    calc L.op (a.similarity w w') (pathClosure L a w' z)
        ≤ Finset.univ.sup' Finset.univ_nonempty
            (fun δ => L.op (a.gains.gain w δ) (propagationClosure L a.gains (unitAt z) δ)) :=
          Finset.le_sup' (fun δ => L.op (a.gains.gain w δ)
            (propagationClosure L a.gains (unitAt z) δ)) (Finset.mem_univ w')
      _ ≤ _ := le_max_right _ _
      _ = pathClosure L a w z := this
  obtain ⟨rest, -, eq⟩ := iterate_eq_walkSignal (L := L) (A := a.gains) (unitAt y)
    (Fintype.card V - 1) x
  have attained : pathClosure L a x y = walkSignal L a.gains (unitAt y) (x :: rest) := eq
  rw [attained]
  exact op_walkSignal_le L a column closed x rest

/-- **Leastness** (`HS5.04`): the path closure lies below every reflexive kernel
in `[0, 1]` above the tolerance that is transitive for the law. -/
theorem pathClosure_le {β : V → V → R} (bounds : ∀ x y, 0 ≤ β x y ∧ β x y ≤ 1)
    (refl : ∀ x, β x x = 1) (above : ∀ x y, a.similarity x y ≤ β x y)
    (trans : ∀ x y z, L.op (β x y) (β y z) ≤ β x z) (x y : V) : pathClosure L a x y ≤ β x y :=
  propagationClosure_le (v := fun w => β w y) (unitAt_mem y) (fun z => by
      unfold unitAt
      split_ifs with h
      · rw [h, refl]
      · exact (bounds z y).1)
    (fun w w' => (L.op_mono (a.nonnegative w w') (bounds w' y).1 (above w w') le_rfl).trans
      (trans w w' y)) x

/-- For a symmetric tolerance and a commutative law the path closure is
symmetric. -/
theorem pathClosure_symm (comm : ∀ s t, L.op s t = L.op t s) (x y : V) :
    pathClosure L a x y = pathClosure L a y x := by
  have flip : ∀ x y, pathClosure L a x y ≤ pathClosure L a y x := by
    intro x y
    refine pathClosure_le L a (β := fun x y => pathClosure L a y x)
      (fun x y => pathClosure_mem L a y x) (fun x => pathClosure_self L a x)
      (fun x y => (a.symmetric x y).symm ▸ le_pathClosure L a y x) (fun x y z => ?_) x y
    rw [comm]
    exact pathClosure_trans L a z y x
  exact le_antisymm (flip x y) (flip y x)

/-- The path closure of a commutative law as a tolerance. -/
def pathTolerance (comm : ∀ s t, L.op s t = L.op t s) : Tolerance V R where
  similarity := pathClosure L a
  nonnegative x y := (pathClosure_mem L a x y).1
  bounded x y := (pathClosure_mem L a x y).2
  reflexive := pathClosure_self L a
  symmetric := pathClosure_symm L a comm

end PathClosure

namespace PathLaw

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

@[simp] theorem productLaw_op (s t : R) : productLaw.op s t = s * t := rfl
@[simp] theorem bottleneckLaw_op (s t : R) : bottleneckLaw.op s t = min s t := rfl
@[simp] theorem lukasiewiczLaw_op (s t : R) : lukasiewiczLaw.op s t = max 0 (s + t - 1) := rfl

end PathLaw

section Laws

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {V : Type u} [Fintype V] [Nonempty V] [DecidableEq V] (a : Tolerance V R)

theorem lukasiewicz_comm (s t : R) : PathLaw.lukasiewiczLaw.op s t = PathLaw.lukasiewiczLaw.op t s := by
  rw [PathLaw.lukasiewiczLaw_op, PathLaw.lukasiewiczLaw_op, add_comm s t]

/-- **The Łukasiewicz path closure is the metric closure** (`HS5.03`): the stable
max-Łukasiewicz power is the least metric tolerance above the seed. -/
theorem lukasiewicz_closure_eq (x y : V) :
    pathClosure PathLaw.lukasiewiczLaw a x y = (shortestTolerance a).similarity x y := by
  have metric : (pathTolerance PathLaw.lukasiewiczLaw a lukasiewicz_comm).Metric := by
    rw [Tolerance.metric_iff_similarity]
    intro x y z
    have := pathClosure_trans PathLaw.lukasiewiczLaw a x y z
    rw [PathLaw.lukasiewiczLaw_op] at this
    exact (le_max_right _ _).trans this
  refine le_antisymm ?_ ?_
  · refine pathClosure_le _ a (fun x y => ⟨(shortestTolerance a).nonnegative x y,
      (shortestTolerance a).bounded x y⟩) (shortestTolerance a).reflexive
      (shortestTolerance_extends a) (fun x y z => ?_) x y
    have := (Tolerance.metric_iff_similarity _).mp (shortestTolerance_metric a) x y z
    rw [PathLaw.lukasiewiczLaw_op]
    exact max_le ((shortestTolerance a).nonnegative x z) this
  · exact (shortestTolerance_is_least a).2.2 (pathTolerance PathLaw.lukasiewiczLaw a lukasiewicz_comm)
      (le_pathClosure _ a) metric x y

/-- **Three nested completions** (`HS5.04`): `α ≤ α♭ ≤ α× ≤ α∞`. -/
theorem nested_completions (x y : V) :
    a.similarity x y ≤ pathClosure PathLaw.lukasiewiczLaw a x y ∧
      pathClosure PathLaw.lukasiewiczLaw a x y ≤ pathClosure PathLaw.productLaw a x y ∧
      pathClosure PathLaw.productLaw a x y ≤ pathClosure PathLaw.bottleneckLaw a x y := by
  refine ⟨le_pathClosure _ a x y, ?_, ?_⟩
  · refine pathClosure_le _ a (fun x y => pathClosure_mem _ a x y) (pathClosure_self _ a)
      (le_pathClosure _ a) (fun x y z => ?_) x y
    have product := pathClosure_trans PathLaw.productLaw a x y z
    have s := pathClosure_mem PathLaw.productLaw a x y
    have t := pathClosure_mem PathLaw.productLaw a y z
    rw [PathLaw.productLaw_op] at product
    rw [PathLaw.lukasiewiczLaw_op]
    exact max_le (pathClosure_mem _ a x z).1 (by nlinarith)
  · refine pathClosure_le _ a (fun x y => pathClosure_mem _ a x y) (pathClosure_self _ a)
      (le_pathClosure _ a) (fun x y z => ?_) x y
    have bottleneck := pathClosure_trans PathLaw.bottleneckLaw a x y z
    have s := pathClosure_mem PathLaw.bottleneckLaw a x y
    have t := pathClosure_mem PathLaw.bottleneckLaw a y z
    rw [PathLaw.bottleneckLaw_op] at bottleneck
    rw [PathLaw.productLaw_op]
    refine le_trans ?_ bottleneck
    rcases le_total (pathClosure PathLaw.bottleneckLaw a x y)
      (pathClosure PathLaw.bottleneckLaw a y z) with h | h
    · rw [min_eq_left h]; exact mul_le_of_le_one_right s.1 t.2
    · rw [min_eq_right h]; exact mul_le_of_le_one_left t.1 s.2

/-- **The minimum closure is the least ultrametric tolerance above α**
(`HS5.04`): ultrametric means `min (β x y) (β y z) ≤ β x z`. -/
theorem bottleneck_closure_least {β : Tolerance V R} (above : a.Extends β)
    (ultra : ∀ x y z, min (β.similarity x y) (β.similarity y z) ≤ β.similarity x z) (x y : V) :
    pathClosure PathLaw.bottleneckLaw a x y ≤ β.similarity x y :=
  pathClosure_le _ a (fun x y => ⟨β.nonnegative x y, β.bounded x y⟩) β.reflexive above ultra x y

/-- **The product closure is the least reflexive max-product-stable relation
above α** (`HS5.04`). -/
theorem product_closure_least {β : V → V → R} (bounds : ∀ x y, 0 ≤ β x y ∧ β x y ≤ 1)
    (refl : ∀ x, β x x = 1) (above : ∀ x y, a.similarity x y ≤ β x y)
    (stable : ∀ x y z, β x y * β y z ≤ β x z) (x y : V) :
    pathClosure PathLaw.productLaw a x y ≤ β x y :=
  pathClosure_le _ a bounds refl above stable x y

omit [Nonempty V] in
/-- **Least coherent coarsening minimizes every nonnegative linear cost**
(`HS5.03`). -/
theorem closure_minimizes_cost (price : V → V → R) (hprice : ∀ x y, 0 ≤ price x y)
    {β : Tolerance V R} (metric : β.Metric) (above : a.Extends β) :
    ∑ x, ∑ y, price x y * ((shortestTolerance a).similarity x y - a.similarity x y) ≤
      ∑ x, ∑ y, price x y * (β.similarity x y - a.similarity x y) :=
  Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
    (sub_le_sub_right ((shortestTolerance_is_least a).2.2 β above metric x y) _) (hprice x y)

end Laws

/-! ## Patterns: product scores and truth conjunctions (`HS5.02`) -/

section Patterns

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {ι : Type u} (r : ι → PBit R)

/-- **The two-channel product score** `S⊗(r, P) = (Π p_e, Π n_e)`. -/
def productScore (P : Finset ι) : PBit R :=
  ⟨∏ e ∈ P, (r e).support, ∏ e ∈ P, (r e).opposition,
    Finset.prod_nonneg fun e _ => (r e).support_nonneg,
    Finset.prod_le_one (fun e _ => (r e).support_nonneg) fun e _ => (r e).support_le_one,
    Finset.prod_nonneg fun e _ => (r e).opposition_nonneg,
    Finset.prod_le_one (fun e _ => (r e).opposition_nonneg) fun e _ => (r e).opposition_le_one⟩

/-- **The truth conjunction** `L(r, P) = (min p_e, max n_e)`, with `L(r, ∅) = T`. -/
def conjunctionScore (P : Finset ι) : PBit R :=
  ⟨P.fold min 1 fun e => (r e).support, P.fold max 0 fun e => (r e).opposition,
    (Finset.le_fold_min _).mpr ⟨zero_le_one, fun e _ => (r e).support_nonneg⟩,
    (Finset.fold_min_le _).mpr (Or.inl le_rfl),
    (Finset.le_fold_max _).mpr (Or.inl le_rfl),
    (Finset.fold_max_le _).mpr ⟨zero_le_one, fun e _ => (r e).opposition_le_one⟩⟩

/-- The empty pattern: the product unit is `B`, the empty conjunction is `T`. -/
theorem empty_pattern : productScore r ∅ = PBit.both ∧ conjunctionScore r ∅ = PBit.supported := by
  constructor <;> ext <;> simp [productScore, conjunctionScore, PBit.both, PBit.supported]

/-- **Pattern extension** (`HS5.02`): extending a pattern lowers both product
coordinates (knowledge order) and moves the conjunction down in the truth
order. -/
theorem pattern_extension {P Q : Finset ι} (sub : P ⊆ Q) :
    productScore r Q ≤ productScore r P ∧ (conjunctionScore r Q).TruthLE (conjunctionScore r P) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · exact Finset.prod_le_prod_of_subset_of_le_one sub (fun e _ => (r e).support_nonneg)
      (fun e _ _ => (r e).support_le_one)
  · exact Finset.prod_le_prod_of_subset_of_le_one sub (fun e _ => (r e).opposition_nonneg)
      (fun e _ _ => (r e).opposition_le_one)
  · exact (Finset.le_fold_min _).mpr ⟨(Finset.fold_min_le _).mpr (Or.inl le_rfl), fun e he =>
      (Finset.fold_min_le _).mpr (Or.inr ⟨e, sub he, le_rfl⟩)⟩
  · exact (Finset.fold_max_le _).mpr ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun e he =>
      (Finset.le_fold_max _).mpr (Or.inr ⟨e, sub he, le_rfl⟩)⟩

/-- **One decisive objection** (ch. 5, §3.1): for `(1, 0)` and `(0, 1)` the
product score is `(0, 0)` while the conjunction is `(0, 1)`. -/
theorem decisive_objection :
    let r : Bool → PBit R := fun b => if b then PBit.supported else PBit.opposed
    productScore r Finset.univ = PBit.neither ∧ conjunctionScore r Finset.univ = PBit.opposed := by
  intro r
  constructor <;> ext <;> simp [r, productScore, conjunctionScore, PBit.supported, PBit.opposed,
    PBit.neither, Fintype.univ_bool]

/-- The worst unmet sameness demand `D_P(α) = max_{e ∈ P} d_e`, and
`T_P = 1 − D_P = min α_e`; under the positive-support policy `T_P` is the
support of `L`. -/
def worstDefect (d : ι → R) (P : Finset ι) : R := P.fold max 0 d

theorem one_sub_worstDefect [DecidableEq ι] (P : Finset ι) :
    1 - worstDefect (fun e => 1 - (r e).support) P = (conjunctionScore r P).support := by
  show 1 - P.fold max 0 (fun e => 1 - (r e).support) = P.fold min 1 fun e => (r e).support
  induction P using Finset.induction_on with
  | empty => simp
  | insert e P notMem ih =>
      simp only [Finset.fold_insert notMem, ← min_sub_sub_left, sub_sub_cancel, ih]

end Patterns

/-! ## Fixed-source resonance (`HS5.06`–`HS5.09`) -/

section Gate

variable {R : Type} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {Q : Type u} [Fintype Q]

/-- The squared report distance `D_ω(s, t)²` between two report arrays on the
same probes. -/
def arrayDistSq (ρ : Distribution Q R) (s t : Q → PBit R) : R := ∑ q, ρ.weight q * (s q).distSq (t q)

/-- **The fixed-source gate** `G(t)_q = t_q ∨ k_q s_q`: the receiver adopts the
source's evidence, scaled by the gains, as lower bounds. -/
def gate (s k t : Q → PBit R) : Q → PBit R := fun q => t q ⊔ PBit.gain (k q) (s q)

/-- The box `B_{s,k}` of evidential lower bounds. -/
def InBox (s k u : Q → PBit R) : Prop := ∀ q, PBit.gain (k q) (s q) ≤ u q

variable (s k t : Q → PBit R)

omit [Fintype Q] in
theorem gate_inBox : InBox s k (gate s k t) := fun _ => le_sup_right

omit [Fintype Q] in
/-- The gate is inflationary. -/
theorem le_gate (q : Q) : t q ≤ gate s k t q := le_sup_left

omit [Fintype Q] in
/-- The gate is order-preserving. -/
theorem gate_mono {t' : Q → PBit R} (le : ∀ q, t q ≤ t' q) (q : Q) : gate s k t q ≤ gate s k t' q :=
  sup_le_sup_right (le q) _

omit [Fintype Q] in
/-- **The gate is idempotent**: repeating a fixed exposure changes nothing. -/
theorem gate_idem : gate s k (gate s k t) = gate s k t := by
  funext q
  simp only [gate, sup_assoc, sup_idem]

theorem coordinate_descent {src tgt c : R} (low : c ≤ src) :
    (src - max tgt c) ^ 2 + (tgt - max tgt c) ^ 2 ≤ (src - tgt) ^ 2 := by
  rcases le_total c tgt with h | h
  · rw [max_eq_left h]; nlinarith
  · rw [max_eq_right h]; nlinarith

theorem coordinate_nearest {tgt c u : R} (above : c ≤ u) : (tgt - max tgt c) ^ 2 ≤ (tgt - u) ^ 2 := by
  rcases le_total c tgt with h | h
  · rw [max_eq_left h]; nlinarith [sq_nonneg (tgt - u)]
  · rw [max_eq_right h]; nlinarith

theorem coordinate_nonexpansive (a b c : R) : (max a c - max b c) ^ 2 ≤ (a - b) ^ 2 := by
  rw [← sq_abs, ← sq_abs (a - b)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_max_sub_max_le_abs a b c) 2

/-- **The gate is the nearest point of the box** (`HS5.06`). -/
theorem gate_nearest (ρ : Distribution Q R) {u : Q → PBit R} (hu : InBox s k u) :
    arrayDistSq ρ t (gate s k t) ≤ arrayDistSq ρ t u := by
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ (ρ.nonnegative q)
  have p := coordinate_nearest (tgt := (t q).support) (hu q).1
  have n := coordinate_nearest (tgt := (t q).opposition) (hu q).2
  simp only [PBit.distSq, gate, PBit.sup_support, PBit.sup_opposition]
  linarith

/-- **The gate is nonexpansive in the receiver** (`HS5.06`). -/
theorem gate_nonexpansive (ρ : Distribution Q R) (t' : Q → PBit R) :
    arrayDistSq ρ (gate s k t) (gate s k t') ≤ arrayDistSq ρ t t' := by
  refine Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left ?_ (ρ.nonnegative q)
  have p := coordinate_nonexpansive (t q).support (t' q).support (PBit.gain (k q) (s q)).support
  have n := coordinate_nonexpansive (t q).opposition (t' q).opposition
    (PBit.gain (k q) (s q)).opposition
  simp only [PBit.distSq, gate, PBit.sup_support, PBit.sup_opposition]
  linarith

/-- **Approach to the source** (`HS5.06`):
`D(s, t)² ≥ D(s, G t)² + D(t, G t)²`. -/
theorem gate_descent (ρ : Distribution Q R) :
    arrayDistSq ρ s (gate s k t) + arrayDistSq ρ t (gate s k t) ≤ arrayDistSq ρ s t := by
  unfold arrayDistSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun q _ => ?_
  have lowP : (k q).support * (s q).support ≤ (s q).support :=
    mul_le_of_le_one_left (s q).support_nonneg (k q).support_le_one
  have lowN : (k q).opposition * (s q).opposition ≤ (s q).opposition :=
    mul_le_of_le_one_left (s q).opposition_nonneg (k q).opposition_le_one
  have p := coordinate_descent (tgt := (t q).support) lowP
  have n := coordinate_descent (tgt := (t q).opposition) lowN
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (ρ.nonnegative q)
  simp only [PBit.distSq, gate, PBit.sup_support, PBit.sup_opposition, PBit.gain]
  linarith

/-- Any change at a probe of positive weight strictly decreases the distance to
the source (`HS5.06`). -/
theorem gate_strict (ρ : Distribution Q R) {q : Q} (positive : 0 < ρ.weight q)
    (moved : gate s k t q ≠ t q) : arrayDistSq ρ s (gate s k t) < arrayDistSq ρ s t := by
  have descent := gate_descent s k t ρ
  have step : 0 < arrayDistSq ρ t (gate s k t) := by
    unfold arrayDistSq
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun q => ρ.weight q *
      (t q).distSq (gate s k t q)) (fun q _ => mul_nonneg (ρ.nonnegative q)
        (PBit.distSq_nonneg _ _)) (Finset.mem_univ q))
    refine mul_pos positive (lt_of_le_of_ne (PBit.distSq_nonneg _ _) ?_)
    intro zero
    exact moved (PBit.distSq_eq_zero_iff.mp zero.symm).symm
  linarith

/-- **The decision proxy** `π(v) = (1 + p − n)/2`. -/
def proxy (v : PBit R) : R := (1 + v.support - v.opposition) / 2

omit [Fintype Q] in
/-- **The proxy moves with the bias** (`HS5.07`). -/
theorem proxy_sub (v w : PBit R) :
    proxy w - proxy v = ((w.support - v.support) - (w.opposition - v.opposition)) / 2 := by
  unfold proxy
  ring

/-- **Evidence growth need not raise the proxy** (`HS5.07`): the conflicted
source `(1, 1)` lifts the receiver `(1, 0)` to `(1, 1)` under unit gains; the
report distance falls from `1/√2` to `0`, the proxy from `1` to `½`. -/
theorem growth_lowers_proxy :
    let src : Unit → PBit R := fun _ => PBit.both
    let tgt : Unit → PBit R := fun _ => PBit.supported
    gate src (fun _ => PBit.both) tgt () = PBit.both ∧
      arrayDistSq (EvidenceExamples.oneProbe R) src tgt = 1 / 2 ∧
      arrayDistSq (EvidenceExamples.oneProbe R) src (gate src (fun _ => PBit.both) tgt) = 0 ∧
      proxy (PBit.supported : PBit R) = 1 ∧ proxy (PBit.both : PBit R) = 1 / 2 := by
  intro src tgt
  have g : gate src (fun _ => PBit.both) tgt () = PBit.both := by
    ext <;> simp [gate, src, tgt, PBit.gain, PBit.both, PBit.supported]
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · simp [arrayDistSq, Distribution.uniform, src, tgt, PBit.distSq, PBit.both, PBit.supported]
  · simp [arrayDistSq, Distribution.uniform, src, g]
  · norm_num [proxy, PBit.supported]
  · norm_num [proxy, PBit.both]

omit [Fintype Q] in
/-- **Opposition-only transfer** (`HS5.08`): with support gain `0` the support
of every report is kept and opposition can only grow. -/
theorem oppositionGate_support (hk : ∀ q, (k q).support = 0) (q : Q) :
    (gate s k t q).support = (t q).support ∧ (t q).opposition ≤ (gate s k t q).opposition := by
  simp [gate, PBit.gain, hk q, (t q).support_nonneg]

omit [Fintype Q] in
/-- Opposition-only transfer never raises the proxy of a single demand
(`HS5.08`). -/
theorem oppositionGate_proxy (hk : ∀ q, (k q).support = 0) (q : Q) :
    proxy (gate s k t q) ≤ proxy (t q) := by
  obtain ⟨p, n⟩ := oppositionGate_support s k t hk q
  unfold proxy
  rw [p]
  linarith

omit [Fintype Q] in
/-- ... nor of a product pattern summary, nor of a truth conjunction (`HS5.08`). -/
theorem oppositionGate_pattern_proxy (hk : ∀ q, (k q).support = 0) (P : Finset Q) :
    proxy (productScore (gate s k t) P) ≤ proxy (productScore t P) ∧
      proxy (conjunctionScore (gate s k t) P) ≤ proxy (conjunctionScore t P) := by
  have supp : ∀ q, (gate s k t q).support = (t q).support := fun q =>
    (oppositionGate_support s k t hk q).1
  have opp : ∀ q, (t q).opposition ≤ (gate s k t q).opposition := fun q =>
    (oppositionGate_support s k t hk q).2
  constructor
  · unfold proxy productScore
    simp only [supp]
    have : ∏ q ∈ P, (t q).opposition ≤ ∏ q ∈ P, (gate s k t q).opposition :=
      Finset.prod_le_prod (fun q _ => (t q).opposition_nonneg) fun q _ => opp q
    linarith
  · unfold proxy conjunctionScore
    simp only [supp]
    have : P.fold max 0 (fun q => (t q).opposition) ≤ P.fold max 0 (fun q => (gate s k t q).opposition) :=
      (Finset.fold_max_le _).mpr ⟨(Finset.le_fold_max _).mpr (Or.inl le_rfl), fun q hq =>
        (Finset.le_fold_max _).mpr (Or.inr ⟨q, hq, opp q⟩)⟩
    linarith

/-- The equal-weight interference of two report arrays,
`Int(s, t) = ½ Z(s)·Z(t)`. -/
def arrayInterference (ω : Distribution Q R) (s t : Q → PBit R) : R :=
  ∑ q, ω.weight q * (s q).dot (t q) / 2

/-- The squared norm `‖Z(s)‖²` of an embedded report array. -/
def arraySqNorm (ω : Distribution Q R) (s : Q → PBit R) : R :=
  ∑ q, ω.weight q * ((s q).embed.1 ^ 2 + (s q).embed.2 ^ 2)

/-- **Interference in report coordinates** (ch. 5, §6.3):
`Int(s, t) = ‖(Z s + Z t)/2‖² − (‖Z s‖² + ‖Z t‖²)/4 = (‖Z s‖² + ‖Z t‖²)/4 − D(s, t)²`. -/
theorem arrayInterference_eq (ω : Distribution Q R) (s t : Q → PBit R) :
    arrayInterference ω s t =
        ∑ q, ω.weight q * ((((s q).embed.1 + (t q).embed.1) / 2) ^ 2 +
          (((s q).embed.2 + (t q).embed.2) / 2) ^ 2) - (arraySqNorm ω s + arraySqNorm ω t) / 4 ∧
      arrayInterference ω s t = (arraySqNorm ω s + arraySqNorm ω t) / 4 - arrayDistSq ω s t := by
  constructor
  · unfold arrayInterference arraySqNorm
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by simp only [PBit.dot]; ring
  · unfold arrayInterference arraySqNorm arrayDistSq
    rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    have := (PBit.embed_sq_dist (s q) (t q)).2
    simp only [PBit.dot]
    linear_combination (-(ω.weight q) / 4) * this

/-- **The exact interference change** (`HS5.09`): for a fixed source and any
receiver edit,
`Int(s, t') − Int(s, t) = Σ ω_e [(s⁺ − ½) Δp + (s⁻ − ½) Δn]`. -/
theorem interference_change (ω : Distribution Q R) (s t t' : Q → PBit R) :
    arrayInterference ω s t' - arrayInterference ω s t =
      ∑ q, ω.weight q * (((s q).support - 1 / 2) * ((t' q).support - (t q).support) +
        ((s q).opposition - 1 / 2) * ((t' q).opposition - (t q).opposition)) := by
  unfold arrayInterference
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by simp only [PBit.dot, PBit.embed]; ring

/-- **A sufficient sign condition** (`HS5.09`): under an inflationary edit,
source coordinates at least `½` on every changed channel make the interference
change nonnegative. -/
theorem interference_mono (ω : Distribution Q R) (s t t' : Q → PBit R) (grow : ∀ q, t q ≤ t' q)
    (half : ∀ q, ((t' q).support ≠ (t q).support → 1 / 2 ≤ (s q).support) ∧
      ((t' q).opposition ≠ (t q).opposition → 1 / 2 ≤ (s q).opposition)) :
    arrayInterference ω s t ≤ arrayInterference ω s t' := by
  rw [← sub_nonneg, interference_change]
  refine Finset.sum_nonneg fun q _ => mul_nonneg (ω.nonnegative q) (add_nonneg ?_ ?_)
  · by_cases same : (t' q).support = (t q).support
    · rw [same, sub_self, mul_zero]
    · exact mul_nonneg (by linarith [(half q).1 same]) (by linarith [(grow q).1])
  · by_cases same : (t' q).opposition = (t q).opposition
    · rw [same, sub_self, mul_zero]
    · exact mul_nonneg (by linarith [(half q).2 same]) (by linarith [(grow q).2])

end Gate

/-! ## The source's experiment (ch. 5) -/

namespace Laboratory

open EvidenceExamples (table)
open PatternExample (triple)

/-! Objects `a, b, c` are `Fin 3`; unordered pairs `ab, bc, ac` are `Fin 3` in
that order. -/

/-- The source context `C₁`. -/
def r₁ : Fin 3 → PBit ℚ
  | 0 => ⟨9 / 10, 4 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 1 => ⟨17 / 20, 1 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 2 => ⟨1 / 10, 7 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The initial receiver `C₂⁰`. -/
def r₂ : Fin 3 → PBit ℚ
  | 0 => ⟨1 / 5, 7 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 1 => ⟨3 / 10, 3 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 2 => ⟨1 / 10, 4 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The positive importance coordinates `η⁺ = (1, 4/5, 3/5)`. -/
def importance : Fin 3 → ℚ
  | 0 => 1
  | 1 => 4 / 5
  | 2 => 3 / 5

/-- The declared sampling measure `μ = (5/12, 1/3, 1/4)`. -/
def μ : Distribution (Fin 3) where
  weight
    | 0 => 5 / 12
    | 1 => 1 / 3
    | 2 => 1 / 4
  nonnegative x := by fin_cases x <;> norm_num
  normalized := by simp [Fin.sum_univ_succ]; norm_num

/-- The pair probes weighted by the conditional distinct-pair distribution
`ω = (20/47, 12/47, 15/47)`. -/
def ω : Distribution (Fin 3) where
  weight
    | 0 => 20 / 47
    | 1 => 12 / 47
    | 2 => 15 / 47
  nonnegative x := by fin_cases x <;> norm_num
  normalized := by simp [Fin.sum_univ_succ]; norm_num

/-- **The measure normalizes the importance**, with diagonal mass `25/72` and
pair masses `w = (5/18, 1/6, 5/24)`, whose conditional distribution is `ω`. -/
theorem measure_and_weights :
    (∀ x, μ.weight x = importance x / ∑ y, importance y) ∧
      ∑ x, μ.weight x ^ 2 = 25 / 72 ∧
      2 * μ.weight 0 * μ.weight 1 = 5 / 18 ∧ 2 * μ.weight 1 * μ.weight 2 = 1 / 6 ∧
      2 * μ.weight 0 * μ.weight 2 = 5 / 24 ∧
      (∀ e, ω.weight e = (2 * μ.weight (if e = 1 then 1 else 0) *
        μ.weight (if e = 0 then 1 else 2)) / (47 / 72)) := by
  refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, fun e => ?_⟩
  · fin_cases x <;> simp [μ, importance, Fin.sum_univ_succ] <;> norm_num
  · simp [μ, Fin.sum_univ_succ]; norm_num
  · norm_num [μ]
  · norm_num [μ]
  · norm_num [μ]
  · fin_cases e <;> norm_num [μ, ω]

theorem μ_pairAverage (f : Fin 3 → Fin 3 → ℚ) :
    μ.pairAverage f = (25 * f 0 0 + 20 * f 0 1 + 15 * f 0 2 + 20 * f 1 0 + 16 * f 1 1 +
      12 * f 1 2 + 15 * f 2 0 + 12 * f 2 1 + 9 * f 2 2) / 144 := by
  simp [Distribution.pairAverage, μ, Fin.sum_univ_succ]
  ring

/-- **The bracket on three objects** (eq. g3): every tolerance has
`g = (25 + 20 β_ab + 12 β_bc + 15 β_ac)/72`. -/
theorem graphtropy_three (β : Tolerance (Fin 3)) :
    μ.graphtropy β = (25 + 20 * β.similarity 0 1 + 12 * β.similarity 1 2 +
      15 * β.similarity 0 2) / 72 := by
  rw [Distribution.graphtropy, μ_pairAverage, β.reflexive 0, β.reflexive 1, β.reflexive 2,
    β.symmetric 1 0, β.symmetric 2 1, β.symmetric 2 0]
  ring

/-- **Exact three-object accounting** (`HS5.01`):
`g(β) − g(α) = Σ_e w_e (β_e − α_e)`; raising only `α_ac` by `t` costs `5t/24`. -/
theorem accounting (α β : Tolerance (Fin 3)) :
    μ.graphtropy β - μ.graphtropy α =
      5 / 18 * (β.similarity 0 1 - α.similarity 0 1) + 1 / 6 * (β.similarity 1 2 - α.similarity 1 2) +
        5 / 24 * (β.similarity 0 2 - α.similarity 0 2) := by
  rw [graphtropy_three, graphtropy_three]
  ring

/-- The positive-support policy: `α(x, y) = p(xy)` off the diagonal. -/
def positivePolicy (r : Fin 3 → PBit ℚ) : Tolerance (Fin 3) :=
  triple (r 0).support (r 1).support (r 2).support ⟨(r 0).support_nonneg, (r 0).support_le_one⟩
    ⟨(r 1).support_nonneg, (r 1).support_le_one⟩ ⟨(r 2).support_nonneg, (r 2).support_le_one⟩

theorem positivePolicy_pairs (r : Fin 3 → PBit ℚ) :
    (positivePolicy r).similarity 0 1 = (r 0).support ∧ (positivePolicy r).similarity 1 2 = (r 1).support ∧
      (positivePolicy r).similarity 0 2 = (r 2).support := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [positivePolicy, triple, table]

theorem graphtropy_positivePolicy (r : Fin 3 → PBit ℚ) :
    μ.graphtropy (positivePolicy r) =
      (25 + 20 * (r 0).support + 12 * (r 1).support + 15 * (r 2).support) / 72 := by
  obtain ⟨h₀, h₁, h₂⟩ := positivePolicy_pairs r
  rw [graphtropy_three, h₀, h₁, h₂]

/-- `g(α₁) = 547/720`, `g(α₂⁰) = 341/720`; raising the source's `ac` from
`0.10` to `0.75` costs `13/96`. -/
theorem initial_graphtropy :
    μ.graphtropy (positivePolicy r₁) = 547 / 720 ∧ μ.graphtropy (positivePolicy r₂) = 341 / 720 ∧
      5 / 24 * (3 / 4 - 1 / 10 : ℚ) = 13 / 96 := by
  refine ⟨?_, ?_, by norm_num⟩ <;> rw [graphtropy_positivePolicy] <;> norm_num [r₁, r₂]

/-- The strongest off-diagonal link `W_η` (ch. 5, eq. bottleneck): importance
products on pairs for support, opposition for the negative coordinate (whose
importance is one). -/
def offDiagonalWeakness (r : Fin 3 → PBit ℚ) : ℚ × ℚ :=
  (max (max (importance 0 * importance 1 * (r 0).support) (importance 1 * importance 2 * (r 1).support))
      (importance 0 * importance 2 * (r 2).support),
    max (max (r 0).opposition (r 1).opposition) (r 2).opposition)

/-- The all-pairs maximum with unit diagonal `R(x, x) = (1, 1)`. -/
def allPairsSupportWeakness (r : Fin 3 → PBit ℚ) : ℚ :=
  Finset.univ.sup' Finset.univ_nonempty fun xy : Fin 3 × Fin 3 =>
    importance xy.1 * importance xy.2 * (positivePolicy r).similarity xy.1 xy.2

/-- **Repairing the source maximum** (ch. 5, §2.1): with the unit diagonal the
all-pairs maximum is `1` in every context, contradicting the quoted Example 2
values; the off-diagonal maximum gives exactly `(0.72, 0.80)` and `(0.16, 0.80)`. -/
theorem weakness_repair :
    allPairsSupportWeakness r₁ = 1 ∧ allPairsSupportWeakness r₂ = 1 ∧
      offDiagonalWeakness r₁ = (18 / 25, 4 / 5) ∧ offDiagonalWeakness r₂ = (4 / 25, 4 / 5) := by
  have all : ∀ r, allPairsSupportWeakness r = 1 := by
    intro r
    refine le_antisymm (Finset.sup'_le _ _ fun xy _ => ?_) ?_
    · have i₁ : importance xy.1 ≤ 1 ∧ 0 ≤ importance xy.1 := by
        fin_cases xy <;> norm_num [importance]
      have i₂ : importance xy.2 ≤ 1 ∧ 0 ≤ importance xy.2 := by
        fin_cases xy <;> norm_num [importance]
      have b := (positivePolicy r).bounded xy.1 xy.2
      have n := (positivePolicy r).nonnegative xy.1 xy.2
      calc importance xy.1 * importance xy.2 * (positivePolicy r).similarity xy.1 xy.2
          ≤ 1 * 1 * 1 := mul_le_mul (mul_le_mul i₁.1 i₂.1 i₂.2 zero_le_one) b n (by norm_num)
        _ = 1 := by norm_num
    · refine Finset.le_sup'_of_le _ (Finset.mem_univ (0, 0)) ?_
      simp [importance, (positivePolicy r).reflexive]
  refine ⟨all r₁, all r₂, ?_, ?_⟩ <;> norm_num [offDiagonalWeakness, importance, r₁, r₂]

/-! ### Emergence as a choice of path law (ch. 5, §4) -/

/-- The three completions of the source's positive observer: metric `0.75`,
product `0.765`, ultrametric `0.85` on `ac`; the other edges do not move. -/
theorem source_completions :
    pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₁) 0 2 = 3 / 4 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₁) 0 2 = 153 / 200 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₁) 0 2 = 17 / 20 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₁) 0 1 = 9 / 10 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₁) 1 2 = 17 / 20 := by
  decide +kernel

theorem product_comm (s t : ℚ) : PathLaw.productLaw.op s t = PathLaw.productLaw.op t s := by
  rw [PathLaw.productLaw_op, PathLaw.productLaw_op, mul_comm]

theorem bottleneck_comm (s t : ℚ) : PathLaw.bottleneckLaw.op s t = PathLaw.bottleneckLaw.op t s := by
  rw [PathLaw.bottleneckLaw_op, PathLaw.bottleneckLaw_op, min_comm]

/-- **The completion table** (ch. 5, §4.2): raw `547/720`, metric `1289/1440`,
product `2587/2880`, ultrametric `1319/1440`. -/
theorem source_completion_graphtropy :
    μ.graphtropy (pathTolerance PathLaw.lukasiewiczLaw (positivePolicy r₁) lukasiewicz_comm) =
        1289 / 1440 ∧
      μ.graphtropy (pathTolerance PathLaw.productLaw (positivePolicy r₁) product_comm) = 2587 / 2880 ∧
      μ.graphtropy (pathTolerance PathLaw.bottleneckLaw (positivePolicy r₁) bottleneck_comm) =
        1319 / 1440 := by
  have values :
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₁) 0 1 = 9 / 10 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₁) 1 2 = 17 / 20 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₁) 0 2 = 3 / 4 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₁) 0 1 = 9 / 10 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₁) 1 2 = 17 / 20 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₁) 0 2 = 153 / 200 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₁) 0 1 = 9 / 10 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₁) 1 2 = 17 / 20 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₁) 0 2 = 17 / 20 := by
    decide +kernel
  obtain ⟨l₁, l₂, l₃, p₁, p₂, p₃, b₁, b₂, b₃⟩ := values
  refine ⟨?_, ?_, ?_⟩ <;> rw [graphtropy_three] <;> simp only [pathTolerance] <;>
    simp only [l₁, l₂, l₃, p₁, p₂, p₃, b₁, b₂, b₃] <;> norm_num

/-- **Max–min closure collapses more** (ch. 3, §8.2): on the raw sorites the
ultrametric closure raises `α(a, c)` to `4/5` (metric closure: `3/5`), giving
graphtropy `13/15`. -/
theorem sorites_ultrametric :
    pathClosure PathLaw.bottleneckLaw EvidenceExamples.soritesRaw 0 2 = 4 / 5 ∧
      pathClosure PathLaw.lukasiewiczLaw EvidenceExamples.soritesRaw 0 2 = 3 / 5 ∧
      Examples.uniformThree.graphtropy
        (pathTolerance PathLaw.bottleneckLaw EvidenceExamples.soritesRaw bottleneck_comm) = 13 / 15 := by
  have values :
      pathClosure PathLaw.bottleneckLaw EvidenceExamples.soritesRaw 0 1 = 4 / 5 ∧
      pathClosure PathLaw.bottleneckLaw EvidenceExamples.soritesRaw 1 2 = 4 / 5 ∧
      pathClosure PathLaw.bottleneckLaw EvidenceExamples.soritesRaw 0 2 = 4 / 5 ∧
      pathClosure PathLaw.lukasiewiczLaw EvidenceExamples.soritesRaw 0 2 = 3 / 5 := by
    decide +kernel
  obtain ⟨b₁, b₂, b₃, l₃⟩ := values
  refine ⟨b₃, l₃, ?_⟩
  rw [Distribution.graphtropy, Examples.uniformThree_average]
  simp only [pathTolerance, pathClosure_self, b₁, b₂, b₃,
    pathClosure_symm PathLaw.bottleneckLaw EvidenceExamples.soritesRaw bottleneck_comm 1 0,
    pathClosure_symm PathLaw.bottleneckLaw EvidenceExamples.soritesRaw bottleneck_comm 2 1,
    pathClosure_symm PathLaw.bottleneckLaw EvidenceExamples.soritesRaw bottleneck_comm 2 0]
  norm_num

/-- The opposition kernel of a context, as a tolerance with unit diagonal (the
gain convention of the source's closure). -/
def oppositionGains (r : Fin 3 → PBit ℚ) : Tolerance (Fin 3) :=
  triple (r 0).opposition (r 1).opposition (r 2).opposition
    ⟨(r 0).opposition_nonneg, (r 0).opposition_le_one⟩ ⟨(r 1).opposition_nonneg, (r 1).opposition_le_one⟩
    ⟨(r 2).opposition_nonneg, (r 2).opposition_le_one⟩

/-- **The negative channel moves too** (ch. 5, §4.3): componentwise product
closure raises `n(bc)` from `0.20` to `0.56` through `a`. -/
theorem negative_channel_closure :
    pathClosure PathLaw.productLaw (oppositionGains r₁) 0 1 = 4 / 5 ∧
      pathClosure PathLaw.productLaw (oppositionGains r₁) 1 2 = 14 / 25 ∧
      pathClosure PathLaw.productLaw (oppositionGains r₁) 0 2 = 7 / 10 := by
  decide +kernel

/-- Crisp opposition: `a` differs from `b` and from `c`, while `b` and `c` share a
category. -/
def crispOpposition : Tolerance (Fin 3) := triple 1 0 1 (by norm_num) (by norm_num) (by norm_num)

/-- **Product closure is not a sound rule for opposition to sameness**: it
derives full opposition between `b` and `c` from their opposition to `a`. -/
theorem opposition_closure_unsound :
    crispOpposition.similarity 1 2 = 0 ∧
      pathClosure PathLaw.productLaw crispOpposition 1 2 = 1 := by
  constructor
  · simp [crispOpposition, triple, table]
  · decide +kernel

/-! ### Transport and completion (ch. 5, §5) -/

/-- The gain `(0.9, 0.9)`. -/
def transferGain : PBit ℚ := ⟨9 / 10, 9 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The receiver after transport, `C₂¹`. -/
def r₂' : Fin 3 → PBit ℚ
  | 0 => ⟨81 / 100, 18 / 25, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 1 => ⟨153 / 200, 3 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
  | 2 => ⟨1 / 10, 4 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **The source's receiver update is exact** (ch. 5, eq. receiver). -/
theorem transport_exact : gate r₁ (fun _ => transferGain) r₂ = r₂' := by
  funext e
  fin_cases e <;> ext <;> norm_num [gate, PBit.gain, transferGain, r₁, r₂, r₂']

/-- **Transport, completion and their costs** (`HS5.05`). -/
theorem transport_and_completion :
    μ.graphtropy (positivePolicy r₂') = 1297 / 1800 ∧
      μ.graphtropy (positivePolicy r₂') - μ.graphtropy (positivePolicy r₂) = 889 / 3600 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 0 2 = 23 / 40 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 0 2 = 12393 / 20000 ∧
      pathClosure PathLaw.bottleneckLaw (positivePolicy r₂') 0 2 = 153 / 200 ∧
      (889 / 3600 : ℚ) + 5 / 24 * (23 / 40 - 1 / 10) = 4981 / 14400 ∧
      (5 / 24 : ℚ) * (23 / 40 - 1 / 10) = 19 / 192 ∧
      (5 / 24 : ℚ) * (12393 / 20000 - 23 / 40) = 893 / 96000 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by norm_num, by norm_num, by norm_num⟩
  · rw [graphtropy_positivePolicy]; norm_num [r₂']
  · rw [graphtropy_positivePolicy, graphtropy_positivePolicy]; norm_num [r₂, r₂']
  all_goals decide +kernel

/-- **The transport–completion balance as expected indistinction** (`HS5.05`):
the metric completion of the transported receiver sits `4981/14400` above the
initial receiver, and product closure another `893/96000` above it. -/
theorem completion_balance :
    μ.graphtropy (pathTolerance PathLaw.lukasiewiczLaw (positivePolicy r₂') lukasiewicz_comm) -
        μ.graphtropy (positivePolicy r₂) = 4981 / 14400 ∧
      μ.graphtropy (pathTolerance PathLaw.productLaw (positivePolicy r₂') product_comm) -
        μ.graphtropy (pathTolerance PathLaw.lukasiewiczLaw (positivePolicy r₂') lukasiewicz_comm) =
        893 / 96000 := by
  have values :
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 0 1 = 81 / 100 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 1 2 = 153 / 200 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 0 2 = 23 / 40 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 0 1 = 81 / 100 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 1 2 = 153 / 200 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 0 2 = 12393 / 20000 := by
    decide +kernel
  obtain ⟨l₁, l₂, l₃, p₁, p₂, p₃⟩ := values
  refine ⟨?_, ?_⟩
  · rw [graphtropy_three, graphtropy_positivePolicy]
    simp only [pathTolerance, l₁, l₂, l₃]
    norm_num [r₂]
  · rw [graphtropy_three, graphtropy_three]
    simp only [pathTolerance, l₁, l₂, l₃, p₁, p₂, p₃]
    norm_num

/-- The receiver's negative channel is already stable under max-product
composition, and the strongest link after transport is `(0.648, 0.80)`. -/
theorem receiver_after_transport :
    pathClosure PathLaw.productLaw (oppositionGains r₂') 0 1 = 18 / 25 ∧
      pathClosure PathLaw.productLaw (oppositionGains r₂') 1 2 = 3 / 5 ∧
      pathClosure PathLaw.productLaw (oppositionGains r₂') 0 2 = 4 / 5 ∧
      offDiagonalWeakness r₂' = (81 / 125, 4 / 5) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · norm_num [offDiagonalWeakness, importance, r₂']

/-- **Closing before transfer changes the experiment** (ch. 5, §5.2): importing the
completed source gives `ac = 0.675` (metric) and `0.6885` (product), against
`0.575` and `0.61965` for the raw source. -/
theorem close_then_transfer :
    pathClosure PathLaw.lukasiewiczLaw
        (triple (81 / 100) (153 / 200) (27 / 40) (by norm_num) (by norm_num) (by norm_num)) 0 2 =
        27 / 40 ∧
      pathClosure PathLaw.productLaw
        (triple (81 / 100) (153 / 200) (1377 / 2000) (by norm_num) (by norm_num) (by norm_num)) 0 2 =
        1377 / 2000 ∧
      max (1 / 10) (9 / 10 * (3 / 4 : ℚ)) = 27 / 40 ∧ max (1 / 10) (9 / 10 * (153 / 200 : ℚ)) = 1377 / 2000 ∧
      ∀ k d : ℚ, 1 - k * (1 - d) = (1 - k) + k * d := by
  refine ⟨by decide +kernel, by decide +kernel, by norm_num, by norm_num, fun k d => by ring⟩

/-- The task penalties `τ = (0.7, 0.6, 0.8)`, the receiver's initial opposition. -/
def receiverTask : Fin 3 → Fin 3 → ℚ := table (7 / 10) (3 / 5) (4 / 5)

theorem receiver_budget : budget μ (positivePolicy r₂) = 379 / 720 := by
  rw [budget, Distribution.distinction_eq_one_sub, graphtropy_positivePolicy]
  norm_num [r₂]

/-- The pattern score of a candidate on three objects. -/
theorem receiver_score (β : Tolerance (Fin 3)) :
    patternScore μ (positivePolicy r₂) receiverTask (3 / 2) β =
      ((5 / 18 * (β.similarity 0 1 - 1 / 5) + 1 / 6 * (β.similarity 1 2 - 3 / 10) +
          5 / 24 * (β.similarity 0 2 - 1 / 10)) -
        3 / 2 * (5 / 18 * (7 / 10) * (β.similarity 0 1 - 1 / 5) +
          1 / 6 * (3 / 5) * (β.similarity 1 2 - 3 / 10) +
          5 / 24 * (4 / 5) * (β.similarity 0 2 - 1 / 10))) / (379 / 720) := by
  obtain ⟨hγ, hℓ⟩ := budget_eq (task := receiverTask) (by rw [receiver_budget]; norm_num) β
  obtain ⟨a₀, a₁, a₂⟩ := positivePolicy_pairs r₂
  have r₂0 : (r₂ 0).support = 1 / 5 := rfl
  have r₂1 : (r₂ 1).support = 3 / 10 := rfl
  have r₂2 : (r₂ 2).support = 1 / 10 := rfl
  unfold patternScore
  rw [hγ, hℓ, receiver_budget, μ_pairAverage, μ_pairAverage, β.reflexive 0, β.reflexive 1,
    β.reflexive 2, β.symmetric 1 0, β.symmetric 2 1, β.symmetric 2 0,
    (positivePolicy r₂).reflexive 0, (positivePolicy r₂).reflexive 1, (positivePolicy r₂).reflexive 2,
    (positivePolicy r₂).symmetric 1 0, (positivePolicy r₂).symmetric 2 1,
    (positivePolicy r₂).symmetric 2 0, a₀, a₁, a₂, r₂0, r₂1, r₂2]
  simp only [receiverTask, table]
  norm_num [Fin.ext_iff]
  ring

/-- **A declared task can reject a more coherent pattern** (ch. 5, §5.3). -/
theorem task_rejects :
    patternScore μ (positivePolicy r₂) receiverTask (3 / 2) (positivePolicy r₂') = -13 / 9475 ∧
      patternScore μ (positivePolicy r₂) receiverTask (3 / 2)
        (pathTolerance PathLaw.lukasiewiczLaw (positivePolicy r₂') lukasiewicz_comm) = -1477 / 37900 ∧
      patternScore μ (positivePolicy r₂) receiverTask (3 / 2)
        (pathTolerance PathLaw.productLaw (positivePolicy r₂') product_comm) = -32219 / 758000 ∧
      (-32219 / 758000 : ℚ) - (-1477 / 37900) = -2679 / 758000 := by
  have values :
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 0 1 = 81 / 100 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 1 2 = 153 / 200 ∧
      pathClosure PathLaw.lukasiewiczLaw (positivePolicy r₂') 0 2 = 23 / 40 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 0 1 = 81 / 100 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 1 2 = 153 / 200 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₂') 0 2 = 12393 / 20000 := by
    decide +kernel
  obtain ⟨l₁, l₂, l₃, p₁, p₂, p₃⟩ := values
  obtain ⟨g₀, g₁, g₂⟩ := positivePolicy_pairs r₂'
  refine ⟨?_, ?_, ?_, by norm_num⟩ <;> rw [receiver_score]
  · rw [g₀, g₁, g₂]; norm_num [r₂']
  · simp only [pathTolerance, l₁, l₂, l₃]; norm_num
  · simp only [pathTolerance, p₁, p₂, p₃]; norm_num

/-! ### The geometry of resonance (ch. 5, §6) -/

/-- **Report distances to the source** (ch. 5, §6.3): `157/940` before and
`24467/940000` after transport; the `ac` residual stays `0.005`. -/
theorem report_distances :
    arrayDistSq ω r₁ r₂ = 157 / 940 ∧ arrayDistSq ω r₁ r₂' = 24467 / 940000 ∧
      (r₁ 2).distSq (r₂' 2) = 1 / 200 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [arrayDistSq, ω, Fin.sum_univ_succ, PBit.distSq, r₁, r₂, r₂'] <;> norm_num

/-! ### Habit, opposition and interference (ch. 5, §7) -/

/-- The chain pattern `{ab, bc}`. -/
def chain : Finset (Fin 3) := {0, 1}

theorem chain_scores (r : Fin 3 → PBit ℚ) :
    (productScore r chain).support = (r 0).support * (r 1).support ∧
      (productScore r chain).opposition = (r 0).opposition * (r 1).opposition ∧
      (conjunctionScore r chain).support = min (r 0).support (r 1).support ∧
      (conjunctionScore r chain).opposition = max (r 0).opposition (r 1).opposition := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [productScore, conjunctionScore, chain, Finset.fold_insert,
      min_eq_left (r 1).support_le_one, max_eq_left (r 1).opposition_nonneg]

/-- **The pattern and decision numbers** (ch. 5, §7.1). -/
theorem habit_numbers :
    proxy (productScore r₁ chain) = 321 / 400 ∧ proxy (productScore r₂ chain) = 8 / 25 ∧
      proxy (productScore r₂' chain) = 23753 / 40000 ∧
      proxy (conjunctionScore r₁ chain) = 21 / 40 ∧ proxy (conjunctionScore r₂ chain) = 1 / 4 ∧
      proxy (conjunctionScore r₂' chain) = 209 / 400 ∧
      (conjunctionScore r₁ chain).support = 17 / 20 ∧
      (conjunctionScore r₂' chain).support = 153 / 200 := by
  obtain ⟨a₁, b₁, c₁, d₁⟩ := chain_scores r₁
  obtain ⟨a₂, b₂, c₂, d₂⟩ := chain_scores r₂
  obtain ⟨a₃, b₃, c₃, d₃⟩ := chain_scores r₂'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [proxy, a₁, b₁, c₁, d₁, a₂, b₂, c₂, d₂,
    a₃, b₃, c₃, d₃] <;> norm_num [r₁, r₂, r₂']

/-- **Version matters** (ch. 5, §7.1): on the source's full two-channel product
closure the chain scores `(0.765, 0.448)`, not `(0.765, 0.16)`. -/
theorem full_closure_chain :
    pathClosure PathLaw.productLaw (positivePolicy r₁) 0 1 *
        pathClosure PathLaw.productLaw (positivePolicy r₁) 1 2 = 153 / 200 ∧
      pathClosure PathLaw.productLaw (oppositionGains r₁) 0 1 *
        pathClosure PathLaw.productLaw (oppositionGains r₁) 1 2 = 56 / 125 ∧
      (productScore r₁ chain).opposition = 4 / 25 := by
  have values : pathClosure PathLaw.productLaw (positivePolicy r₁) 0 1 = 9 / 10 ∧
      pathClosure PathLaw.productLaw (positivePolicy r₁) 1 2 = 17 / 20 := by decide +kernel
  obtain ⟨n₁, n₂, -⟩ := negative_channel_closure
  obtain ⟨-, b, -, -⟩ := chain_scores r₁
  refine ⟨by rw [values.1, values.2]; norm_num, by rw [n₁, n₂]; norm_num, by rw [b]; norm_num [r₁]⟩

/-- **Opposition-only transfer reverses the action bias without erasing support**
(ch. 5, §7.2): `(0.60, 0.20) ↦ (0.60, 0.81)`, proxy `0.70 ↦ 0.395`, conflict
`0.2 ↦ 0.6`, bias `0.40 ↦ −0.21`. -/
theorem opposition_transfer :
    let src : Unit → PBit ℚ := fun _ => ⟨1 / 10, 9 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
    let k : Unit → PBit ℚ := fun _ => ⟨0, 9 / 10, le_rfl, zero_le_one, by norm_num, by norm_num⟩
    let tgt : Unit → PBit ℚ := fun _ => ⟨3 / 5, 1 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    (gate src k tgt ()).support = 3 / 5 ∧ (gate src k tgt ()).opposition = 81 / 100 ∧
      proxy (tgt ()) = 7 / 10 ∧ proxy (gate src k tgt ()) = 79 / 200 ∧
      (tgt ()).conflict = 1 / 5 ∧ (gate src k tgt ()).conflict = 3 / 5 ∧
      (tgt ()).bias = 2 / 5 ∧ (gate src k tgt ()).bias = -21 / 100 := by
  intro src k tgt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [src, k, tgt, gate, PBit.gain, proxy, PBit.conflict, PBit.bias]

/-- **Interference numbers** (ch. 5, §7.3): on `ab` it rises from `−0.06` to
`0.19`; on the product chain from `−0.0894` to `0.05482725`; on the whole
weighted profile it was already positive, `9/470`, and rises to `7853/47000`. -/
theorem interference_numbers :
    (r₁ 0).dot (r₂ 0) / 2 = -3 / 50 ∧ (r₁ 0).dot (r₂' 0) / 2 = 19 / 100 ∧
      (productScore r₁ chain).dot (productScore r₂ chain) / 2 = -447 / 5000 ∧
      (productScore r₁ chain).dot (productScore r₂' chain) / 2 = 219309 / 4000000 ∧
      arrayInterference ω r₁ r₂ = 9 / 470 ∧ arrayInterference ω r₁ r₂' = 7853 / 47000 := by
  obtain ⟨a₁, b₁, -, -⟩ := chain_scores r₁
  obtain ⟨a₂, b₂, -, -⟩ := chain_scores r₂
  obtain ⟨a₃, b₃, -, -⟩ := chain_scores r₂'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [PBit.dot, PBit.embed, r₁, r₂]
  · norm_num [PBit.dot, PBit.embed, r₁, r₂']
  · simp only [PBit.dot, PBit.embed, a₁, b₁, a₂, b₂]; norm_num [r₁, r₂]
  · simp only [PBit.dot, PBit.embed, a₁, b₁, a₃, b₃]; norm_num [r₁, r₂']
  · simp [arrayInterference, ω, Fin.sum_univ_succ, PBit.dot, PBit.embed, r₁, r₂]; norm_num
  · simp [arrayInterference, ω, Fin.sum_univ_succ, PBit.dot, PBit.embed, r₁, r₂']; norm_num

/-- **Closer reports, smaller interference** (ch. 5, §7.3): the source `(0.2, 0.2)`
lifts the receiver `(0.1, 0.1)` to itself; the distance falls from `0.1` to `0`
while the interference falls from `0.24` to `0.18`. -/
theorem closer_but_weaker :
    let src : Unit → PBit ℚ := fun _ => ⟨1 / 5, 1 / 5, by norm_num, by norm_num, by norm_num, by norm_num⟩
    let tgt : Unit → PBit ℚ := fun _ => ⟨1 / 10, 1 / 10, by norm_num, by norm_num, by norm_num, by norm_num⟩
    gate src (fun _ => PBit.both) tgt = src ∧
      arrayDistSq (EvidenceExamples.oneProbe ℚ) src tgt = 1 / 100 ∧
      arrayInterference (EvidenceExamples.oneProbe ℚ) src tgt = 6 / 25 ∧
      arrayInterference (EvidenceExamples.oneProbe ℚ) src src = 9 / 50 := by
  intro src tgt
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext q
    ext <;> norm_num [gate, PBit.gain, PBit.both, src, tgt]
  · simp [arrayDistSq, Distribution.uniform, PBit.distSq, src, tgt]; norm_num
  · simp [arrayInterference, Distribution.uniform, PBit.dot, PBit.embed, src, tgt]; norm_num
  · simp [arrayInterference, Distribution.uniform, PBit.dot, PBit.embed, src]; norm_num

end Laboratory

end Mettapedia.Cybernetics.DistinctionCalculus
