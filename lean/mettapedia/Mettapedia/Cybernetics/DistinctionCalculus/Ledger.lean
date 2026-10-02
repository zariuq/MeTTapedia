import Mettapedia.Cybernetics.DistinctionCalculus.Completeness
import Mettapedia.Cybernetics.DistinctionCalculus.Weighted

/-!
# Exact ledgers for expected indistinction

Expected indistinction `g_P(α) = ⟨P|α|P⟩` (`Distribution.graphtropy`) is a
positive linear functional on similarity kernels. This module records what that
gives beyond monotonicity.

* **Crisp tolerances.** A decidable reflexive symmetric relation is a 0/1
  tolerance (`Tolerance.ofRel`); an equivalence relation gives a metric one
  (`Tolerance.ofSetoid`), whose zero kernel is the equivalence itself.
* **Exact coarsening account.** For `α ≤ β` the increment `g(β) − g(α)` is the
  bracket of `β − α`; it lies between `0` and the distinction `h(α)`, vanishes
  exactly when `β = α` on supported pairs, obeys a Markov bound, and bounds the
  largest pointwise change when every point has mass at least `m₀`. Along a
  chain the increments telescope into an exact ledger. For equivalence
  relations the increment is the pair mass of the newly identified pairs.
* **Valuation.** With pointwise maximum and minimum,
  `g(α ∨ β) + g(α ∧ β) = g(α) + g(β)`.
* **Closure of crisp seeds.** The least metric tolerance above a crisp seed is
  crisp: its zero kernel is the equivalence closure of the seed. So the join of
  two equivalence relations is the metric closure of the pointwise maximum of
  their tolerances, and on a finite carrier it is decidable.
* **Metric lattice and forced completion.** Metric tolerances are closed under
  pointwise minimum; their join is the closure of the pointwise maximum. The
  valuation law then acquires a nonnegative defect, the mass of the completion
  forced by the join, so expected indistinction is supermodular on metric
  tolerances and on equivalence relations.

Every numerical statement here is over `ℚ`. Its axioms include
`Classical.choice`, inherited from the core rational arithmetic lemmas
(`Rat.add_comm`, `Rat.le_refl` and their sources `Rat.normalize_eq`,
`Rat.add_def`); the constructions are computable.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus

universe u

variable {V : Type u}

/-! ## Crisp tolerances -/

namespace Tolerance

/-- The crisp tolerance of a decidable reflexive symmetric relation. -/
def ofRel (R : V → V → Prop) [DecidableRel R] (refl : ∀ x, R x x)
    (symm : ∀ {x y}, R x y → R y x) : Tolerance V where
  similarity x y := if R x y then 1 else 0
  nonnegative x y := by split_ifs <;> norm_num
  bounded x y := by split_ifs <;> norm_num
  reflexive x := by simp [refl x]
  symmetric x y := by
    by_cases related : R x y
    · simp [related, symm related]
    · have unrelated : ¬ R y x := fun related' => related (symm related')
      simp [related, unrelated]

section OfRel

variable (R : V → V → Prop) [DecidableRel R] (refl : ∀ x, R x x)
  (symm : ∀ {x y}, R x y → R y x)

theorem ofRel_similarity (x y : V) :
    (ofRel R refl symm).similarity x y = if R x y then 1 else 0 :=
  rfl

theorem ofRel_distance (x y : V) :
    (ofRel R refl symm).distance x y = if R x y then 0 else 1 := by
  unfold distance
  rw [ofRel_similarity]
  split_ifs <;> norm_num

theorem ofRel_similarity_eq_one_iff {x y : V} :
    (ofRel R refl symm).similarity x y = 1 ↔ R x y := by
  rw [ofRel_similarity]
  split_ifs with related
  · exact ⟨fun _ => related, fun _ => rfl⟩
  · exact ⟨fun h => absurd h (by norm_num), fun h => absurd h related⟩

theorem ofRel_indistinguishable_iff {x y : V} :
    (ofRel R refl symm).Indistinguishable x y ↔ R x y := by
  rw [indistinguishable_iff_similarity_one, ofRel_similarity_eq_one_iff]

/-- A transitive crisp tolerance is metric. -/
theorem ofRel_metric (trans : ∀ {x y z}, R x y → R y z → R x z) :
    (ofRel R refl symm).Metric := by
  intro x y z
  rw [ofRel_distance, ofRel_distance, ofRel_distance]
  by_cases first : R x y
  · by_cases second : R y z
    · simp [first, second, trans first second]
    · split_ifs <;> norm_num
  · split_ifs <;> norm_num

end OfRel

/-- The crisp metric tolerance of a decidable equivalence relation. -/
def ofSetoid (E : Setoid V) [DecidableRel E.r] : Tolerance V :=
  ofRel E.r E.refl' fun related => E.symm' related

section OfSetoid

variable (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r]

theorem ofSetoid_similarity (x y : V) :
    (ofSetoid E).similarity x y = if E x y then 1 else 0 :=
  rfl

theorem ofSetoid_distance (x y : V) :
    (ofSetoid E).distance x y = if E x y then 0 else 1 :=
  ofRel_distance E.r E.refl' (fun related => E.symm' related) x y

theorem ofSetoid_indistinguishable_iff {x y : V} :
    (ofSetoid E).Indistinguishable x y ↔ E x y :=
  ofRel_indistinguishable_iff E.r E.refl' (fun related => E.symm' related)

theorem ofSetoid_metric : (ofSetoid E).Metric :=
  ofRel_metric E.r E.refl' (fun related => E.symm' related)
    (fun first second => E.trans' first second)

/-- The zero kernel of the crisp tolerance of `E` is `E`. -/
theorem zeroSetoid_ofSetoid : (ofSetoid E).zeroSetoid (ofSetoid_metric E) = E := by
  ext x y
  exact ofSetoid_indistinguishable_iff E

/-- Coarsening an equivalence relation is extending its crisp tolerance. -/
theorem ofSetoid_extends_iff : (ofSetoid E).Extends (ofSetoid F) ↔ E ≤ F := by
  constructor
  · intro extended x y related
    have bound := extended x y
    rw [ofSetoid_similarity, ofSetoid_similarity, if_pos related] at bound
    by_contra unrelated
    rw [if_neg unrelated] at bound
    norm_num at bound
  · intro le x y
    rw [ofSetoid_similarity, ofSetoid_similarity]
    by_cases related : E x y
    · rw [if_pos related, if_pos (le related)]
    · rw [if_neg related]
      split_ifs <;> norm_num

end OfSetoid

/-! ## The pointwise lattice of tolerances -/

/-- Pointwise maximum of similarities: identifies whatever either identifies. -/
def sup (a b : Tolerance V) : Tolerance V where
  similarity x y := max (a.similarity x y) (b.similarity x y)
  nonnegative x y := le_max_of_le_left (a.nonnegative x y)
  bounded x y := max_le (a.bounded x y) (b.bounded x y)
  reflexive x := by simp [a.reflexive x, b.reflexive x]
  symmetric x y := by rw [a.symmetric x y, b.symmetric x y]

/-- Pointwise minimum of similarities: distinguishes whatever either
distinguishes. -/
def inf (a b : Tolerance V) : Tolerance V where
  similarity x y := min (a.similarity x y) (b.similarity x y)
  nonnegative x y := le_min (a.nonnegative x y) (b.nonnegative x y)
  bounded x y := min_le_of_left_le (a.bounded x y)
  reflexive x := by simp [a.reflexive x, b.reflexive x]
  symmetric x y := by rw [a.symmetric x y, b.symmetric x y]

variable (a b : Tolerance V)

theorem sup_similarity (x y : V) :
    (a.sup b).similarity x y = max (a.similarity x y) (b.similarity x y) :=
  rfl

theorem inf_similarity (x y : V) :
    (a.inf b).similarity x y = min (a.similarity x y) (b.similarity x y) :=
  rfl

theorem extends_sup_left : a.Extends (a.sup b) := fun _ _ => le_max_left _ _

theorem extends_sup_right : b.Extends (a.sup b) := fun _ _ => le_max_right _ _

theorem inf_extends_left : (a.inf b).Extends a := fun _ _ => min_le_left _ _

theorem inf_extends_right : (a.inf b).Extends b := fun _ _ => min_le_right _ _

theorem sup_extends_of {c : Tolerance V} (ha : a.Extends c) (hb : b.Extends c) :
    (a.sup b).Extends c :=
  fun x y => max_le (ha x y) (hb x y)

theorem extends_inf_of {c : Tolerance V} (ha : c.Extends a) (hb : c.Extends b) :
    c.Extends (a.inf b) :=
  fun x y => le_min (ha x y) (hb x y)

theorem inf_distance (x y : V) :
    (a.inf b).distance x y = max (a.distance x y) (b.distance x y) := by
  unfold distance
  rw [inf_similarity]
  rcases le_total (a.similarity x y) (b.similarity x y) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **The pointwise minimum of metric tolerances is metric**: the maximum of two
pseudometrics is a pseudometric. -/
theorem inf_metric {a b : Tolerance V} (ha : a.Metric) (hb : b.Metric) : (a.inf b).Metric := by
  intro x y z
  rw [inf_distance, inf_distance, inf_distance]
  apply max_le
  · exact (ha x y z).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (hb x y z).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

end Tolerance

/-! ## The valuation law -/

namespace Distribution

variable [Fintype V] (p : Distribution V)

/-- **Valuation law** (HS4.02): expected indistinction counts overlaps once. -/
theorem graphtropy_sup_add_inf (a b : Tolerance V) :
    p.graphtropy (a.sup b) + p.graphtropy (a.inf b) = p.graphtropy a + p.graphtropy b := by
  unfold graphtropy
  rw [← pairAverage_add, ← pairAverage_add]
  congr 1
  funext x y
  exact max_add_min _ _

/-! ## Exact coarsening account -/

/-- The increment of expected indistinction is the bracket of the change. -/
theorem graphtropy_sub_eq (a b : Tolerance V) :
    p.graphtropy b - p.graphtropy a =
      p.pairAverage fun x y => b.similarity x y - a.similarity x y :=
  (p.pairAverage_sub _ _).symm

/-- A coarsening never lowers expected indistinction (HS3.04). -/
theorem increment_nonneg {a b : Tolerance V} (coarser : a.Extends b) :
    0 ≤ p.graphtropy b - p.graphtropy a := by
  rw [graphtropy_sub_eq]
  exact p.pairAverage_nonnegative fun x y => sub_nonneg.mpr (coarser x y)

/-- The increment is at most the distinction available before coarsening. -/
theorem increment_le_distinction {a b : Tolerance V} :
    p.graphtropy b - p.graphtropy a ≤ p.distinction a := by
  rw [graphtropy_sub_eq]
  exact p.pairAverage_mono fun x y => by
    have := b.bounded x y
    unfold Tolerance.distance
    linarith

/-- **Strictness is visible only on supported pairs** (HS4.01): a coarsening
leaves expected indistinction unchanged exactly when it changes no pair of
positive mass. -/
theorem increment_eq_zero_iff {a b : Tolerance V} (coarser : a.Extends b) :
    p.graphtropy b - p.graphtropy a = 0 ↔
      ∀ x y, 0 < p.weight x → 0 < p.weight y → b.similarity x y = a.similarity x y := by
  rw [graphtropy_sub_eq]
  constructor
  · intro zero x y hx hy
    exact sub_eq_zero.mp (p.pairAverage_zero_on_support
      (fun u v => sub_nonneg.mpr (coarser u v)) zero x y hx hy)
  · intro same
    unfold pairAverage
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
    rcases (p.nonnegative x).lt_or_eq with hx | hx
    · rcases (p.nonnegative y).lt_or_eq with hy | hy
      · simp only [same x y hx hy, sub_self, mul_zero]
      · rw [← hy, mul_zero, zero_mul]
    · rw [← hx, zero_mul, zero_mul]

/-- The increment is positive exactly when some pair of positive mass becomes
more similar. -/
theorem increment_pos_iff {a b : Tolerance V} (coarser : a.Extends b) :
    0 < p.graphtropy b - p.graphtropy a ↔
      ∃ x y, 0 < p.weight x ∧ 0 < p.weight y ∧ a.similarity x y < b.similarity x y := by
  constructor
  · intro positive
    by_contra none
    have zero : p.graphtropy b - p.graphtropy a = 0 := by
      refine (p.increment_eq_zero_iff coarser).mpr fun x y hx hy => ?_
      refine le_antisymm ?_ (coarser x y)
      exact not_lt.mp fun lt => none ⟨x, y, hx, hy, lt⟩
    linarith
  · rintro ⟨x, y, hx, hy, lt⟩
    rcases (p.increment_nonneg coarser).lt_or_eq with positive | zero
    · exact positive
    · have := (p.increment_eq_zero_iff coarser).mp zero.symm x y hx hy
      linarith

/-- **Markov bound** (HS4.01): the pair mass on which the similarity rose by at
least `t` is at most the increment divided by `t`. -/
theorem markov_increment {a b : Tolerance V} (coarser : a.Extends b) {t : ℚ} (positive : 0 < t) :
    p.pairAverage (fun x y => if t ≤ b.similarity x y - a.similarity x y then 1 else 0) ≤
      (p.graphtropy b - p.graphtropy a) / t := by
  rw [le_div_iff₀ positive, graphtropy_sub_eq]
  have scaled :
      p.pairAverage (fun x y => if t ≤ b.similarity x y - a.similarity x y then 1 else 0) * t =
        p.pairAverage
          (fun x y => t * (if t ≤ b.similarity x y - a.similarity x y then 1 else 0)) := by
    unfold pairAverage
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [scaled]
  exact p.pairAverage_mono fun x y => by
    split_ifs with large
    · linarith
    · linarith [sub_nonneg.mpr (coarser x y)]

/-- A double sum of nonnegative terms dominates any two distinct entries. -/
theorem two_entries_le_double_sum [DecidableEq V] {f : V → V → ℚ}
    (nonnegative : ∀ x y, 0 ≤ f x y) {x y : V} (distinct : x ≠ y) :
    f x y + f y x ≤ ∑ u, ∑ v, f u v := by
  have pairs : (∑ u, ∑ v, f u v) = ∑ q ∈ (Finset.univ : Finset (V × V)), f q.1 q.2 := by
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [pairs]
  have distinctPairs : (x, y) ≠ (y, x) := fun equal => distinct (Prod.mk.inj equal).1
  have two : ∑ q ∈ ({(x, y), (y, x)} : Finset (V × V)), f q.1 q.2 = f x y + f y x := by
    rw [Finset.sum_pair distinctPairs]
  rw [← two]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun q _ _ => nonnegative q.1 q.2

/-- **Sup bound** (HS4.01): if every point has mass at least `m₀ > 0`, the
largest pointwise rise in similarity is at most the increment divided by
`2 m₀²`. -/
theorem similarity_rise_le [DecidableEq V] {a b : Tolerance V} (coarser : a.Extends b) {m₀ : ℚ}
    (positive : 0 < m₀) (floor : ∀ x, m₀ ≤ p.weight x) (x y : V) :
    b.similarity x y - a.similarity x y ≤ (p.graphtropy b - p.graphtropy a) / (2 * m₀ ^ 2) := by
  have denominator : 0 < 2 * m₀ ^ 2 := by positivity
  rw [le_div_iff₀ denominator]
  by_cases same : x = y
  · subst same
    rw [a.reflexive, b.reflexive, sub_self, zero_mul]
    exact p.increment_nonneg coarser
  · rw [graphtropy_sub_eq]
    have entries := two_entries_le_double_sum
      (f := fun u v => p.weight u * p.weight v * (b.similarity u v - a.similarity u v))
      (fun u v => mul_nonneg (mul_nonneg (p.nonnegative u) (p.nonnegative v))
        (sub_nonneg.mpr (coarser u v))) same
    have change := sub_nonneg.mpr (coarser x y)
    have symmetric : b.similarity y x - a.similarity y x = b.similarity x y - a.similarity x y := by
      rw [a.symmetric, b.symmetric]
    have massX := floor x
    have massY := floor y
    have product : m₀ ^ 2 ≤ p.weight x * p.weight y := by
      rw [sq]
      exact mul_le_mul massX massY positive.le (p.nonnegative x)
    have product' : m₀ ^ 2 ≤ p.weight y * p.weight x := by rwa [mul_comm]
    simp only [symmetric] at entries
    unfold pairAverage
    nlinarith [mul_le_mul_of_nonneg_right product change,
      mul_le_mul_of_nonneg_right product' change]

/-! ## The ledger along a chain -/

/-- The increments of expected indistinction along a list of tolerances. -/
def ledger : List (Tolerance V) → ℚ
  | [] => 0
  | [_] => 0
  | a :: b :: rest => (p.graphtropy b - p.graphtropy a) + ledger (b :: rest)

/-- **The ledger telescopes**: the increments along a chain add up exactly to
the total change, with no approximation. -/
theorem ledger_eq (a : Tolerance V) :
    ∀ rest : List (Tolerance V),
      p.ledger (a :: rest) = p.graphtropy ((a :: rest).getLast (List.cons_ne_nil a rest)) -
        p.graphtropy a
  | [] => by simp [ledger]
  | b :: rest => by
      rw [ledger, ledger_eq b rest]
      simp only [List.getLast_cons_cons]
      ring

/-- Along a chain of coarsenings every ledger entry is nonnegative. -/
theorem ledger_nonneg :
    ∀ chain : List (Tolerance V), chain.IsChain (fun a b => a.Extends b) → 0 ≤ p.ledger chain
  | [], _ => le_rfl
  | [_], _ => le_rfl
  | a :: b :: rest, chained => by
      rw [List.isChain_cons_cons] at chained
      rw [ledger]
      exact add_nonneg (p.increment_nonneg chained.1) (ledger_nonneg (b :: rest) chained.2)

/-! ## Equivalence relations: the increment is the mass of new pairs -/

section Setoids

variable (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r]

/-- For a crisp equivalence observer, expected indistinction is the pair mass of
the equivalence. -/
theorem graphtropy_ofSetoid :
    p.graphtropy (Tolerance.ofSetoid E) = p.pairAverage fun x y => if E x y then 1 else 0 :=
  rfl

/-- **Crisp ledger entry.** Coarsening `E` to `F` raises expected
indistinction by exactly the pair mass of the newly identified pairs. -/
theorem graphtropy_ofSetoid_sub {E F : Setoid V} [DecidableRel E.r] [DecidableRel F.r]
    (coarser : E ≤ F) :
    p.graphtropy (Tolerance.ofSetoid F) - p.graphtropy (Tolerance.ofSetoid E) =
      p.pairAverage fun x y => if F x y ∧ ¬ E x y then 1 else 0 := by
  rw [graphtropy_sub_eq]
  congr 1
  funext x y
  rw [Tolerance.ofSetoid_similarity, Tolerance.ofSetoid_similarity]
  by_cases related : E x y
  · rw [if_pos (coarser related), if_pos related, if_neg (fun h => h.2 related)]
    norm_num
  · rw [if_neg related]
    by_cases related' : F x y
    · rw [if_pos related', if_pos ⟨related', related⟩]
      norm_num
    · rw [if_neg related', if_neg (fun h => related' h.1)]
      norm_num

/-- The crisp increment is positive exactly when a newly identified pair has
positive mass. -/
theorem graphtropy_ofSetoid_lt_iff {E F : Setoid V} [DecidableRel E.r] [DecidableRel F.r]
    (coarser : E ≤ F) :
    p.graphtropy (Tolerance.ofSetoid E) < p.graphtropy (Tolerance.ofSetoid F) ↔
      ∃ x y, 0 < p.weight x ∧ 0 < p.weight y ∧ F x y ∧ ¬ E x y := by
  rw [← sub_pos, p.increment_pos_iff ((Tolerance.ofSetoid_extends_iff E F).mpr coarser)]
  constructor
  · rintro ⟨x, y, hx, hy, lt⟩
    rw [Tolerance.ofSetoid_similarity, Tolerance.ofSetoid_similarity] at lt
    refine ⟨x, y, hx, hy, ?_, ?_⟩
    · by_contra unrelated
      rw [if_neg unrelated] at lt
      split_ifs at lt <;> norm_num at lt
    · intro related
      rw [if_pos related, if_pos (coarser related)] at lt
      exact lt_irrefl _ lt
  · rintro ⟨x, y, hx, hy, related, unrelated⟩
    refine ⟨x, y, hx, hy, ?_⟩
    rw [Tolerance.ofSetoid_similarity, Tolerance.ofSetoid_similarity, if_neg unrelated,
      if_pos related]
    norm_num

end Setoids

end Distribution

/-! ## Equality of tolerances -/

namespace Tolerance

/-- Tolerances with the same similarity are equal. -/
@[ext]
theorem ext {a b : Tolerance V} (same : ∀ x y, a.similarity x y = b.similarity x y) : a = b := by
  cases a with
  | mk similarity _ _ _ _ =>
    cases b with
    | mk similarity' _ _ _ _ =>
      have : similarity = similarity' := funext fun x => funext fun y => same x y
      subst this
      rfl

/-- The pointwise maximum of two crisp tolerances is the crisp tolerance of the
union of the relations. -/
theorem ofSetoid_sup_ofSetoid (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r] :
    (ofSetoid E).sup (ofSetoid F) =
      ofRel (fun x y => E x y ∨ F x y) (fun x => Or.inl (E.refl' x))
        (fun related =>
          related.elim (fun h => Or.inl (E.symm' h)) (fun h => Or.inr (F.symm' h))) := by
  ext x y
  rw [sup_similarity, ofSetoid_similarity, ofSetoid_similarity, ofRel_similarity]
  by_cases first : E x y
  · rw [if_pos first, if_pos (Or.inl first)]
    exact max_eq_left (by split_ifs <;> norm_num)
  · rw [if_neg first]
    by_cases second : F x y
    · rw [if_pos second, if_pos (Or.inr second)]
      norm_num
    · have neither : ¬ (E x y ∨ F x y) := fun h => h.elim first second
      rw [if_neg second, if_neg neither]
      norm_num

/-- The pointwise minimum of two crisp tolerances is the crisp tolerance of the
intersection. -/
theorem ofSetoid_inf_ofSetoid (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r]
    [DecidableRel (E ⊓ F).r] :
    (ofSetoid E).inf (ofSetoid F) = ofSetoid (E ⊓ F) := by
  ext x y
  rw [inf_similarity, ofSetoid_similarity, ofSetoid_similarity, ofSetoid_similarity]
  have meet : (E ⊓ F) x y ↔ E x y ∧ F x y := Iff.rfl
  by_cases first : E x y
  · by_cases second : F x y
    · rw [if_pos first, if_pos second, if_pos (meet.mpr ⟨first, second⟩)]
      norm_num
    · rw [if_pos first, if_neg second, if_neg (fun h => second (meet.mp h).2)]
      norm_num
  · rw [if_neg first, if_neg (fun h => first (meet.mp h).1)]
    exact min_eq_left (by split_ifs <;> norm_num)

end Tolerance

/-! ## Closure of crisp seeds -/

section CrispClosure

/-- The reflexive symmetric closure of a relation, decided. -/
def reflSymmClosure (R : V → V → Prop) (x y : V) : Prop :=
  x = y ∨ R x y ∨ R y x

instance (R : V → V → Prop) [DecidableRel R] [DecidableEq V] : DecidableRel (reflSymmClosure R) :=
  fun x y => inferInstanceAs (Decidable (x = y ∨ R x y ∨ R y x))

theorem reflSymmClosure_refl (R : V → V → Prop) (x : V) : reflSymmClosure R x x :=
  Or.inl rfl

theorem reflSymmClosure_symm (R : V → V → Prop) {x y : V} (related : reflSymmClosure R x y) :
    reflSymmClosure R y x := by
  rcases related with equal | forward | backward
  · exact Or.inl equal.symm
  · exact Or.inr (Or.inr forward)
  · exact Or.inr (Or.inl backward)

theorem eqvGen_reflSymmClosure_iff (R : V → V → Prop) {x y : V} :
    Relation.EqvGen (reflSymmClosure R) x y ↔ Relation.EqvGen R x y := by
  constructor
  · intro generated
    induction generated with
    | rel u v related =>
        rcases related with equal | forward | backward
        · subst equal
          exact Relation.EqvGen.refl u
        · exact Relation.EqvGen.rel _ _ forward
        · exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ backward)
    | refl u => exact Relation.EqvGen.refl u
    | symm u v _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans u v w _ _ ih ih' => exact Relation.EqvGen.trans _ _ _ ih ih'
  · exact fun generated =>
      Relation.EqvGen.mono (fun _ _ related => Or.inr (Or.inl related)) x y generated

/-- Every metric tolerance above a crisp seed identifies the equivalence
closure of the seed. -/
theorem eqvGen_indistinguishable (R : V → V → Prop) [DecidableRel R] (refl : ∀ x, R x x)
    (symm : ∀ {x y}, R x y → R y x) {model : Tolerance V} (metric : model.Metric)
    (above : (Tolerance.ofRel R refl symm).Extends model) {x y : V}
    (generated : Relation.EqvGen R x y) : model.Indistinguishable x y := by
  induction generated with
  | rel u v related =>
      rw [Tolerance.indistinguishable_iff_similarity_one]
      have bound := above u v
      rw [(Tolerance.ofRel_similarity_eq_one_iff R refl symm).mpr related] at bound
      exact le_antisymm (model.bounded u v) bound
  | refl u => exact model.distance_self u
  | symm u v _ ih => exact (model.zeroSetoid metric).symm' ih
  | trans u v w _ _ ih ih' => exact (model.zeroSetoid metric).trans' ih ih'

/-- A chain of zero-distance edges of a crisp seed is a chain of related pairs. -/
theorem eqvGen_of_reflTransGen_zero (R : V → V → Prop) [DecidableRel R] (refl : ∀ x, R x x)
    (symm : ∀ {x y}, R x y → R y x) {x y : V}
    (chain :
      Relation.ReflTransGen (fun u v => (Tolerance.ofRel R refl symm).distance u v = 0) x y) :
    Relation.EqvGen R x y := by
  induction chain with
  | refl => exact Relation.EqvGen.refl x
  | @tail b c _ edge ih =>
      have related : R b c := by
        rw [Tolerance.ofRel_distance] at edge
        by_contra unrelated
        rw [if_neg unrelated] at edge
        norm_num at edge
      exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ related)

variable [DecidableEq V]

/-- A path of zero capped cost consists of zero-distance edges. -/
theorem reflTransGen_of_pathCost_eq_zero (a : Tolerance V) :
    ∀ (path : List V) {x y : V}, path.head? = some x → path.getLast? = some y →
      pathCost a path = 0 → Relation.ReflTransGen (fun u v => a.distance u v = 0) x y
  | [], _, _, head, _, _ => by simp at head
  | [z], x, y, head, last, _ => by
      simp only [List.head?_cons, Option.some.injEq] at head
      simp only [List.getLast?_singleton, Option.some.injEq] at last
      subst head
      subst last
      exact Relation.ReflTransGen.refl
  | z :: w :: rest, x, y, head, last, zero => by
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      have costs : a.distance z w + pathCost a (w :: rest) = 0 := by
        have split := zero
        simp only [pathCost, combine] at split
        rcases min_eq_iff.mp split with ⟨impossible, _⟩ | ⟨sum, _⟩
        · norm_num at impossible
        · exact sum
      have edge : a.distance z w = 0 := by
        have := a.distance_nonnegative z w
        have := pathCost_nonneg a (w :: rest)
        linarith
      have tail : pathCost a (w :: rest) = 0 := by
        have := a.distance_nonnegative z w
        have := pathCost_nonneg a (w :: rest)
        linarith
      have last' : (w :: rest).getLast? = some y := by
        rw [getLast?_cons_of_ne_nil z (List.cons_ne_nil w rest)] at last
        exact last
      exact Relation.ReflTransGen.head edge
        (reflTransGen_of_pathCost_eq_zero a (w :: rest) rfl last' tail)

/-- Zero closed distance is witnessed by a chain of zero-distance seed edges. -/
theorem reflTransGen_of_shortestDistance_eq_zero [Fintype V] (a : Tolerance V) {x y : V}
    (zero : shortestDistance a x y = 0) :
    Relation.ReflTransGen (fun u v => a.distance u v = 0) x y := by
  obtain ⟨path, member, attained⟩ :=
    Finset.exists_mem_eq_inf' (simplePaths_nonempty (x := x) (y := y)) (pathCost a)
  have properties := (mem_simplePaths (x := x) (y := y)).1 member
  have cost : pathCost a path = 0 := by
    have : shortestDistance a x y = pathCost a path := attained
    rw [← this, zero]
  exact reflTransGen_of_pathCost_eq_zero a path properties.2.1 properties.2.2.1 cost

section OfRel

variable (R : V → V → Prop) [DecidableRel R] (refl : ∀ x, R x x)
  (symm : ∀ {x y}, R x y → R y x)

/-- **The closure of a crisp seed identifies exactly the equivalence closure of
the seed.** -/
theorem closure_ofRel_indistinguishable_iff [Fintype V] {x y : V} :
    (shortestTolerance (Tolerance.ofRel R refl symm)).Indistinguishable x y ↔
      Relation.EqvGen R x y := by
  constructor
  · intro zero
    have closedZero : shortestDistance (Tolerance.ofRel R refl symm) x y = 0 := by
      rw [← shortestTolerance_distance]
      exact zero
    exact eqvGen_of_reflTransGen_zero R refl symm
      (reflTransGen_of_shortestDistance_eq_zero _ closedZero)
  · exact eqvGen_indistinguishable R refl symm (shortestTolerance_metric _)
      (shortestTolerance_extends _)

/-- A path whose edges all have distance `0` or `1` has capped cost `0` or `1`. -/
theorem pathCost_crisp (a : Tolerance V) (crisp : ∀ u v, a.distance u v = 0 ∨ a.distance u v = 1) :
    ∀ path : List V, pathCost a path = 0 ∨ pathCost a path = 1
  | [] => Or.inl rfl
  | [_] => Or.inl rfl
  | u :: v :: rest => by
      simp only [pathCost, combine]
      rcases crisp u v with edge | edge <;>
        rcases pathCost_crisp a crisp (v :: rest) with tail | tail <;>
        rw [edge, tail] <;> norm_num

/-- **The closure of a crisp seed is crisp.** -/
theorem closure_ofRel_crisp [Fintype V] (x y : V) :
    (shortestTolerance (Tolerance.ofRel R refl symm)).similarity x y = 0 ∨
      (shortestTolerance (Tolerance.ofRel R refl symm)).similarity x y = 1 := by
  obtain ⟨path, _, attained⟩ :=
    Finset.exists_mem_eq_inf' (simplePaths_nonempty (x := x) (y := y))
      (pathCost (Tolerance.ofRel R refl symm))
  have crisp : ∀ u v, (Tolerance.ofRel R refl symm).distance u v = 0 ∨
      (Tolerance.ofRel R refl symm).distance u v = 1 := by
    intro u v
    rw [Tolerance.ofRel_distance]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  have value : (shortestTolerance (Tolerance.ofRel R refl symm)).similarity x y =
      1 - pathCost (Tolerance.ofRel R refl symm) path := by
    change 1 - shortestDistance _ x y = _
    rw [show shortestDistance (Tolerance.ofRel R refl symm) x y = _ from attained]
  rw [value]
  rcases pathCost_crisp _ crisp path with zero | one
  · right
    rw [zero]
    norm_num
  · left
    rw [one]
    norm_num

end OfRel

/-- **The equivalence closure of a decidable relation on a finite carrier is
decidable**, computed by the metric closure of its crisp tolerance. -/
@[instance_reducible]
def decidableEqvGen [Fintype V] (R : V → V → Prop) [DecidableRel R] :
    DecidableRel (Relation.EqvGen R) := fun x y =>
  decidable_of_iff
    ((shortestTolerance (Tolerance.ofRel (reflSymmClosure R) (reflSymmClosure_refl R)
      (reflSymmClosure_symm R))).distance x y = 0)
    ((closure_ofRel_indistinguishable_iff _ _ _).trans (eqvGen_reflSymmClosure_iff R))

/-- **The join of two decidable equivalence relations on a finite carrier is
decidable**, computed by metric closure. -/
@[instance_reducible]
def decidableSup [Fintype V] (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r] :
    DecidableRel (E ⊔ F).r := fun x y =>
  haveI := decidableEqvGen (fun a b => E a b ∨ F a b)
  decidable_of_iff (Relation.EqvGen (fun a b => E a b ∨ F a b) x y) (by
    rw [Setoid.sup_eq_eqvGen]
    exact Iff.rfl)

/-- **The join of equivalence relations is the metric closure of the pointwise
maximum of their tolerances**: `1_{E ⊔ F} = Cl(1_E ∨ 1_F)`. This is the
graded form of the insertion of equivalence relations into relations. -/
theorem ofSetoid_sup_eq_closure [Fintype V] (E F : Setoid V) [DecidableRel E.r]
    [DecidableRel F.r] [DecidableRel (E ⊔ F).r] :
    Tolerance.ofSetoid (E ⊔ F) =
      shortestTolerance ((Tolerance.ofSetoid E).sup (Tolerance.ofSetoid F)) := by
  rw [Tolerance.ofSetoid_sup_ofSetoid]
  ext x y
  have join : (E ⊔ F) x y ↔ Relation.EqvGen (fun a b => E a b ∨ F a b) x y := by
    rw [Setoid.sup_eq_eqvGen]
    exact Iff.rfl
  rw [Tolerance.ofSetoid_similarity]
  rcases closure_ofRel_crisp (fun a b => E a b ∨ F a b) (fun z => Or.inl (E.refl' z))
      (fun related => related.elim (fun h => Or.inl (E.symm' h)) (fun h => Or.inr (F.symm' h)))
      x y with zero | one
  · rw [zero]
    rw [if_neg]
    intro related
    have := (closure_ofRel_indistinguishable_iff (fun a b => E a b ∨ F a b)
      (fun z => Or.inl (E.refl' z))
      (fun related => related.elim (fun h => Or.inl (E.symm' h)) (fun h => Or.inr (F.symm' h)))).mpr
      (join.mp related)
    rw [Tolerance.indistinguishable_iff_similarity_one, zero] at this
    norm_num at this
  · rw [one, if_pos]
    apply join.mpr
    apply (closure_ofRel_indistinguishable_iff (fun a b => E a b ∨ F a b)
      (fun z => Or.inl (E.refl' z))
      (fun related => related.elim (fun h => Or.inl (E.symm' h)) (fun h => Or.inr (F.symm' h)))).mp
    rw [Tolerance.indistinguishable_iff_similarity_one]
    exact one

end CrispClosure

/-! ## The metric lattice and the forced completion -/

section MetricJoin

variable [Fintype V] [DecidableEq V]

/-- The join of two tolerances among the metric tolerances: the closure of the
pointwise maximum. -/
def metricJoin (a b : Tolerance V) : Tolerance V :=
  shortestTolerance (a.sup b)

theorem metricJoin_metric (a b : Tolerance V) : (metricJoin a b).Metric :=
  shortestTolerance_metric _

theorem extends_metricJoin_left (a b : Tolerance V) : a.Extends (metricJoin a b) :=
  fun x y => (Tolerance.extends_sup_left a b x y).trans (shortestTolerance_extends _ x y)

theorem extends_metricJoin_right (a b : Tolerance V) : b.Extends (metricJoin a b) :=
  fun x y => (Tolerance.extends_sup_right a b x y).trans (shortestTolerance_extends _ x y)

/-- **The metric join is the least metric upper bound** (HS6.05): for metric
`c`, `metricJoin a b ≤ c` exactly when `a ≤ c` and `b ≤ c`. -/
theorem metricJoin_extends_iff {a b c : Tolerance V} (metric : c.Metric) :
    (metricJoin a b).Extends c ↔ a.Extends c ∧ b.Extends c :=
  ⟨fun le => ⟨fun x y => (extends_metricJoin_left a b x y).trans (le x y),
      fun x y => (extends_metricJoin_right a b x y).trans (le x y)⟩,
    fun ⟨ha, hb⟩ =>
      (shortestTolerance_is_least _).2.2 c (Tolerance.sup_extends_of a b ha hb) metric⟩

/-- **A metric guard survives joint completion** (HS6.06): if both proposals lie
below a metric tolerance, so does their metric join. -/
theorem metricJoin_extends_of_guard {a b guard : Tolerance V} (metric : guard.Metric)
    (ha : a.Extends guard) (hb : b.Extends guard) : (metricJoin a b).Extends guard :=
  (metricJoin_extends_iff metric).mpr ⟨ha, hb⟩

namespace Distribution

variable (p : Distribution V)

/-- The expected indistinction forced by metric coherence beyond the raw union
of two proposals. -/
def completionDefect (a b : Tolerance V) : ℚ :=
  p.graphtropy (metricJoin a b) - p.graphtropy (a.sup b)

theorem completionDefect_nonneg (a b : Tolerance V) : 0 ≤ p.completionDefect a b :=
  p.increment_nonneg (shortestTolerance_extends _)

/-- **Valuation with a completion defect.** In the lattice of metric
tolerances, with the metric join and the pointwise meet, expected
indistinction satisfies the valuation law up to the forced completion. -/
theorem graphtropy_metricJoin_add_inf (a b : Tolerance V) :
    p.graphtropy (metricJoin a b) + p.graphtropy (a.inf b) =
      p.graphtropy a + p.graphtropy b + p.completionDefect a b := by
  have valuation := p.graphtropy_sup_add_inf a b
  unfold completionDefect
  linarith

/-- **Expected indistinction is supermodular on metric tolerances.** -/
theorem graphtropy_add_le_metricJoin_add_inf (a b : Tolerance V) :
    p.graphtropy a + p.graphtropy b ≤ p.graphtropy (metricJoin a b) + p.graphtropy (a.inf b) := by
  have := p.graphtropy_metricJoin_add_inf a b
  have := p.completionDefect_nonneg a b
  linarith

/-- The defect vanishes exactly when the closure changes no supported pair. -/
theorem completionDefect_eq_zero_iff (a b : Tolerance V) :
    p.completionDefect a b = 0 ↔
      ∀ x y, 0 < p.weight x → 0 < p.weight y →
        (metricJoin a b).similarity x y = (a.sup b).similarity x y :=
  p.increment_eq_zero_iff (shortestTolerance_extends _)

/-- When the pointwise maximum is already metric, nothing is forced. -/
theorem completionDefect_eq_zero_of_metric {a b : Tolerance V} (metric : (a.sup b).Metric) :
    p.completionDefect a b = 0 := by
  have fixed : metricJoin a b = a.sup b := by
    ext x y
    have least := shortestTolerance_is_least (a.sup b)
    exact le_antisymm (least.2.2 _ (fun _ _ => le_rfl) metric x y) (least.1 x y)
  unfold completionDefect
  rw [fixed, sub_self]

end Distribution

end MetricJoin

/-! ### Equivalence relations: valuation with the forced completion -/

namespace Distribution

variable [Fintype V] (p : Distribution V)

section Setoids

variable (E F : Setoid V) [DecidableRel E.r] [DecidableRel F.r]
  [DecidableRel (E ⊔ F).r] [DecidableRel (E ⊓ F).r]

/-- **Valuation on equivalence relations, with the forced completion.**
`g(E ⊔ F) + g(E ⊓ F) = g(E) + g(F) + P²{(x, y) : (E ⊔ F) x y, neither E x y nor F x y}`.
The last term is the pair mass that the join identifies although neither
relation does: the completion forced by transitivity. -/
theorem graphtropy_setoid_sup_add_inf :
    p.graphtropy (Tolerance.ofSetoid (E ⊔ F)) + p.graphtropy (Tolerance.ofSetoid (E ⊓ F)) =
      p.graphtropy (Tolerance.ofSetoid E) + p.graphtropy (Tolerance.ofSetoid F) +
        p.pairAverage fun x y => if (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) then 1 else 0 := by
  have valuation := p.graphtropy_sup_add_inf (Tolerance.ofSetoid E) (Tolerance.ofSetoid F)
  rw [Tolerance.ofSetoid_inf_ofSetoid] at valuation
  have forced : p.graphtropy (Tolerance.ofSetoid (E ⊔ F)) -
      p.graphtropy ((Tolerance.ofSetoid E).sup (Tolerance.ofSetoid F)) =
        p.pairAverage fun x y => if (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) then 1 else 0 := by
    rw [graphtropy_sub_eq]
    congr 1
    funext x y
    rw [Tolerance.sup_similarity, Tolerance.ofSetoid_similarity, Tolerance.ofSetoid_similarity,
      Tolerance.ofSetoid_similarity]
    have below : E x y ∨ F x y → (E ⊔ F) x y := fun related =>
      related.elim (fun h => (le_sup_left : E ≤ E ⊔ F) h) (fun h => (le_sup_right : F ≤ E ⊔ F) h)
    by_cases first : E x y
    · have notForced : ¬ ((E ⊔ F) x y ∧ ¬ (E x y ∨ F x y)) := fun h => h.2 (Or.inl first)
      rw [if_pos first, if_pos (below (Or.inl first)), if_neg notForced]
      split_ifs <;> norm_num
    · by_cases second : F x y
      · have notForced : ¬ ((E ⊔ F) x y ∧ ¬ (E x y ∨ F x y)) := fun h => h.2 (Or.inr second)
        rw [if_pos second, if_pos (below (Or.inr second)), if_neg notForced, if_neg first]
        norm_num
      · rw [if_neg first, if_neg second]
        by_cases joined : (E ⊔ F) x y
        · have forcedPair : (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) :=
            ⟨joined, fun h => h.elim first second⟩
          rw [if_pos joined, if_pos forcedPair]
          norm_num
        · have notForced : ¬ ((E ⊔ F) x y ∧ ¬ (E x y ∨ F x y)) := fun h => joined h.1
          rw [if_neg joined, if_neg notForced]
          norm_num
  linarith

/-- **Expected indistinction is supermodular on equivalence relations.** -/
theorem graphtropy_setoid_add_le :
    p.graphtropy (Tolerance.ofSetoid E) + p.graphtropy (Tolerance.ofSetoid F) ≤
      p.graphtropy (Tolerance.ofSetoid (E ⊔ F)) + p.graphtropy (Tolerance.ofSetoid (E ⊓ F)) := by
  have := p.graphtropy_setoid_sup_add_inf E F
  have : 0 ≤ p.pairAverage fun x y => if (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) then (1 : ℚ) else 0 :=
    p.pairAverage_nonnegative fun _ _ => by split_ifs <;> norm_num
  linarith

/-- For comparable equivalence relations nothing is forced: the valuation law is
exact on chains. -/
theorem graphtropy_setoid_sup_add_inf_of_le (le : E ≤ F) :
    p.graphtropy (Tolerance.ofSetoid (E ⊔ F)) + p.graphtropy (Tolerance.ofSetoid (E ⊓ F)) =
      p.graphtropy (Tolerance.ofSetoid E) + p.graphtropy (Tolerance.ofSetoid F) := by
  rw [p.graphtropy_setoid_sup_add_inf E F]
  have none :
      (p.pairAverage fun x y => if (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) then (1 : ℚ) else 0) = 0 := by
    have vanish : (fun x y => if (E ⊔ F) x y ∧ ¬ (E x y ∨ F x y) then (1 : ℚ) else 0) =
        fun _ _ => 0 := by
      funext x y
      rw [if_neg]
      rintro ⟨joined, neither⟩
      rw [sup_eq_right.mpr le] at joined
      exact neither (Or.inr joined)
    rw [vanish, pairAverage_const]
  rw [none, add_zero]

end Setoids

end Distribution

end Mettapedia.Cybernetics.DistinctionCalculus
