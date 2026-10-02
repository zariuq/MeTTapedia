import Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruence
import Mettapedia.Cybernetics.DistinctionCalculus.LedgerControls

/-!
# Controls for graded congruences and approximate adequacy

* **Approximate adequacy.** A quotient is decodable within `ε` for a consumer
  exactly when every fibre has consumer diameter at most `2ε`
  (`decodable_iff_diameter`, the single-consumer form of HS8.06). Decodable
  quotients are closed under refinement. For consumer values `0, 2/5, 4/5` and
  `ε = 1/4` both adjacent merges are decodable, no decodable quotient contains
  both, and so **no greatest decodable quotient exists**
  (`no_greatest_decodable`), although the two merges have equal expected
  indistinction.
* **Protection must be metric.** Protecting the single pair `(0, 2)` is a
  non-metric guard: both crisp merges respect it and no metric tolerance above
  both does (`no_common_feasible_upper_bound`). A metric guard survives joint
  completion (`metricJoin_extends_of_guard`).
* **Thresholds are not equalities.** A metric tolerance whose threshold
  relation `d ≤ 1/5` is not transitive (`threshold_not_transitive`).
* **Generated against observational.** Two actions with the same observable
  endpoint are identified by the observational congruence and by no empty set
  of stipulations; stipulating them makes the stipulations complete.
* **The consumer guard is needed.** Two states that the consumer reads alike
  are separated by a continuation, so the greatest adequate graded congruence
  is strictly finer than `1 − d_F` when some context expands `d_F`.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruenceControls

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.Cybernetics.DistinctionCalculus.Examples
open Mettapedia.Cybernetics.DistinctionCalculus.LedgerControls

universe u

/-! ## Approximate adequacy has no greatest quotient -/

section Decoding

variable {V : Type u}

/-- A quotient `E` is decodable within `ε` for the consumer `f` when some
decoder, constant on fibres, reads every value up to `ε`. -/
def Decodable (f : V → ℚ) (ε : ℚ) (E : Setoid V) : Prop :=
  ∃ decoder : V → ℚ, (∀ x y, E x y → decoder x = decoder y) ∧ ∀ x, |f x - decoder x| ≤ ε

/-- Every fibre has consumer diameter at most `2ε`. -/
def FibreDiameterLE (f : V → ℚ) (ε : ℚ) (E : Setoid V) : Prop :=
  ∀ x y, E x y → |f x - f y| ≤ 2 * ε

theorem inf'_congr_finset {s t : Finset V} (same : s = t) (hs : s.Nonempty) (ht : t.Nonempty)
    (f : V → ℚ) : s.inf' hs f = t.inf' ht f := by
  subst same
  rfl

theorem sup'_congr_finset {s t : Finset V} (same : s = t) (hs : s.Nonempty) (ht : t.Nonempty)
    (f : V → ℚ) : s.sup' hs f = t.sup' ht f := by
  subst same
  rfl

variable [Fintype V]

/-- The fibre of a point. -/
def fibre (E : Setoid V) [DecidableRel E.r] (x : V) : Finset V :=
  Finset.univ.filter fun y => E x y

theorem mem_fibre (E : Setoid V) [DecidableRel E.r] {x y : V} : y ∈ fibre E x ↔ E x y := by
  simp [fibre]

theorem self_mem_fibre (E : Setoid V) [DecidableRel E.r] (x : V) : x ∈ fibre E x :=
  (mem_fibre E).mpr (E.refl' x)

theorem fibre_eq (E : Setoid V) [DecidableRel E.r] {x y : V} (related : E x y) :
    fibre E x = fibre E y := by
  ext z
  rw [mem_fibre, mem_fibre]
  exact ⟨fun h => E.trans' (E.symm' related) h, fun h => E.trans' related h⟩

theorem fibre_nonempty (E : Setoid V) [DecidableRel E.r] (x : V) : (fibre E x).Nonempty :=
  ⟨x, self_mem_fibre E x⟩

/-- The midpoint decoder. -/
def midpoint (E : Setoid V) [DecidableRel E.r] (f : V → ℚ) (x : V) : ℚ :=
  ((fibre E x).inf' (fibre_nonempty E x) f + (fibre E x).sup' (fibre_nonempty E x) f) / 2

/-- **Decoding and fibre diameter** (HS8.06, one consumer): a quotient is
decodable within `ε` exactly when every fibre has diameter at most `2ε`; the
midpoint of each fibre attains the bound. -/
theorem decodable_iff_diameter (f : V → ℚ) (ε : ℚ) (E : Setoid V) [DecidableRel E.r] :
    Decodable f ε E ↔ FibreDiameterLE f ε E := by
  constructor
  · rintro ⟨decoder, constant, close⟩ x y related
    have triangle := abs_sub_le (f x) (decoder y) (f y)
    have hx : |f x - decoder y| ≤ ε := by
      rw [← constant x y related]
      exact close x
    have hy : |decoder y - f y| ≤ ε := by
      rw [abs_sub_comm]
      exact close y
    linarith
  · intro diameter
    refine ⟨midpoint E f, fun x y related => ?_, ?_⟩
    · unfold midpoint
      rw [inf'_congr_finset (fibre_eq E related) _ (fibre_nonempty E y) f,
        sup'_congr_finset (fibre_eq E related) _ (fibre_nonempty E y) f]
    intro x
    obtain ⟨low, lowMem, lowEq⟩ :=
      Finset.exists_mem_eq_inf' (s := fibre E x) (fibre_nonempty E x) f
    obtain ⟨high, highMem, highEq⟩ :=
      Finset.exists_mem_eq_sup' (s := fibre E x) (fibre_nonempty E x) f
    have lowLe : f low ≤ f x := lowEq ▸ Finset.inf'_le f (self_mem_fibre E x)
    have highGe : f x ≤ f high := highEq ▸ Finset.le_sup' f (self_mem_fibre E x)
    have spread : f high - f low ≤ 2 * ε := by
      have related : E low high :=
        E.trans' (E.symm' ((mem_fibre E).mp lowMem)) ((mem_fibre E).mp highMem)
      have := diameter high low (E.symm' related)
      rw [abs_le] at this
      linarith
    unfold midpoint
    rw [lowEq, highEq, abs_le]
    constructor <;> linarith

omit [Fintype V] in
/-- Decodable quotients are closed under refinement. -/
theorem Decodable.refine {f : V → ℚ} {ε : ℚ} {E E' : Setoid V} (finer : E' ≤ E)
    (decodable : Decodable f ε E) : Decodable f ε E' := by
  obtain ⟨decoder, constant, close⟩ := decodable
  exact ⟨decoder, fun x y related => constant x y (finer related), close⟩

end Decoding

/-- The consumer values `0, 2/5, 4/5`. -/
def ramp (i : Fin 3) : ℚ :=
  if i = 0 then 0 else if i = 1 then 2 / 5 else 4 / 5

theorem ramp_zero : ramp 0 = 0 := by norm_num [ramp]

theorem ramp_one : ramp 1 = 2 / 5 := by norm_num [ramp, Fin.ext_iff]

theorem ramp_two : ramp 2 = 4 / 5 := by norm_num [ramp, Fin.ext_iff]

/-- The identity quotient is decodable at every nonnegative error. -/
theorem identity_decodable : Decodable ramp (1 / 4) identity :=
  ⟨ramp, fun x y related => by rw [show x = y from related], fun x => by simp⟩

/-- **Both adjacent merges are decodable within `1/4`.** -/
theorem merges_decodable :
    Decodable ramp (1 / 4) mergeAB ∧ Decodable ramp (1 / 4) mergeBC := by
  constructor <;> rw [decodable_iff_diameter] <;> intro x y related
  · rw [mergeAB_apply] at related
    fin_cases x <;> fin_cases y <;> simp at related <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ramp_zero, ramp_one, ramp_two] <;>
      norm_num [abs_le]
  · rw [mergeBC_apply] at related
    fin_cases x <;> fin_cases y <;> simp at related <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ramp_zero, ramp_one, ramp_two] <;>
      norm_num [abs_le]

/-- A quotient decodable within `1/4` never identifies `0` with `2`. -/
theorem decodable_separates_ends {E : Setoid (Fin 3)} [DecidableRel E.r]
    (decodable : Decodable ramp (1 / 4) E) : ¬ E 0 2 := by
  intro related
  have := (decodable_iff_diameter ramp (1 / 4) E).mp decodable 0 2 related
  rw [ramp_zero, ramp_two, abs_le] at this
  norm_num at this

/-- The abstract shape of the counterexample: two admissible merges whose
common coarsenings are all inadmissible leave no greatest admissible quotient. -/
theorem no_greatest_of_merges (Admissible : Setoid (Fin 3) → Prop)
    (left : Admissible mergeAB) (right : Admissible mergeBC)
    (separates : ∀ E, Admissible E → ¬ E 0 2) :
    ¬ ∃ G, Admissible G ∧ ∀ E, Admissible E → E ≤ G := by
  rintro ⟨G, admissible, greatest⟩
  have first : G 0 1 := greatest mergeAB left (show mergeAB 0 1 by decide)
  have second : G 1 2 := greatest mergeBC right (show mergeBC 1 2 by decide)
  exact separates G admissible (G.trans' first second)

/-- **Approximate adequacy has no greatest quotient** (HS8.06). -/
theorem no_greatest_decodable :
    ¬ ∃ G : Setoid (Fin 3), Decodable ramp (1 / 4) G ∧
      ∀ E, Decodable ramp (1 / 4) E → E ≤ G := by
  apply no_greatest_of_merges (fun E => Decodable ramp (1 / 4) E) merges_decodable.1
    merges_decodable.2
  intro E decodable related
  obtain ⟨decoder, constant, close⟩ := decodable
  have left := close 0
  have right := close 2
  rw [constant 0 2 related] at left
  rw [ramp_zero, abs_le] at left
  rw [ramp_two, abs_le] at right
  linarith [left.1, right.2]

/-- The connected threshold graph is not an admissible fibre: the join of the
two merges is not decodable. -/
theorem join_not_decodable : ¬ Decodable ramp (1 / 4) (mergeAB ⊔ mergeBC) := by
  intro decodable
  obtain ⟨decoder, constant, close⟩ := decodable
  have joined : (mergeAB ⊔ mergeBC) 0 2 := join_forces_endpoints.1
  have left := close 0
  have right := close 2
  rw [constant 0 2 joined] at left
  rw [ramp_zero, abs_le] at left
  rw [ramp_two, abs_le] at right
  linarith [left.1, right.2]

/-- Maximal expected indistinction does not pick a greatest policy either: the
two incomparable merges have equal expected indistinction. -/
theorem merges_equal_weakness :
    uniformThree.graphtropy (Tolerance.ofSetoid mergeAB) =
      uniformThree.graphtropy (Tolerance.ofSetoid mergeBC) := by
  simp only [Distribution.graphtropy, uniformThree_average, Tolerance.ofSetoid_similarity,
    mergeAB_apply, mergeBC_apply]
  norm_num [Fin.ext_iff]

/-! ## Protection must be metric -/

/-- Graded policies respecting a guard: metric tolerances below it. -/
def Respects (guard b : Tolerance (Fin 3)) : Prop :=
  b.Metric ∧ b.Extends guard

/-- The guard that protects only the pair `(0, 2)` is the non-metric chain. -/
theorem pairGuard_not_metric : ¬ chain.Metric :=
  chain_not_metric

/-- Both crisp merges respect the pairwise guard. -/
theorem merges_respect_pairGuard :
    Respects chain (Tolerance.ofSetoid mergeAB) ∧ Respects chain (Tolerance.ofSetoid mergeBC) := by
  refine ⟨⟨Tolerance.ofSetoid_metric _, ?_⟩, ⟨Tolerance.ofSetoid_metric _, ?_⟩⟩ <;> intro x y
  · simp only [Tolerance.ofSetoid_similarity, chain_similarity, mergeAB_apply]
    fin_cases x <;> fin_cases y <;> simp
  · simp only [Tolerance.ofSetoid_similarity, chain_similarity, mergeBC_apply]
    fin_cases x <;> fin_cases y <;> simp

/-- **No common upper bound respects a non-metric guard**: a metric tolerance
above both merges identifies `0` with `2`, which the guard forbids. -/
theorem no_common_feasible_upper_bound :
    ¬ ∃ b, Respects chain b ∧ (Tolerance.ofSetoid mergeAB).Extends b ∧
      (Tolerance.ofSetoid mergeBC).Extends b := by
  rintro ⟨b, ⟨metric, guarded⟩, aboveAB, aboveBC⟩
  have first : b.similarity 0 1 = 1 := by
    apply le_antisymm (b.bounded 0 1)
    have := aboveAB 0 1
    rwa [Tolerance.ofSetoid_similarity, if_pos (show mergeAB 0 1 by decide)] at this
  have second : b.similarity 1 2 = 1 := by
    apply le_antisymm (b.bounded 1 2)
    have := aboveBC 1 2
    rwa [Tolerance.ofSetoid_similarity, if_pos (show mergeBC 1 2 by decide)] at this
  have ends : b.similarity 0 2 = 1 := by
    have zero := (b.zeroSetoid metric).trans'
      ((Tolerance.indistinguishable_iff_similarity_one b 0 1).mpr first)
      ((Tolerance.indistinguishable_iff_similarity_one b 1 2).mpr second)
    exact (Tolerance.indistinguishable_iff_similarity_one b 0 2).mp zero
  have bound := guarded 0 2
  rw [ends, chain_similarity] at bound
  norm_num at bound

/-- Hence no greatest policy respects the pairwise guard. -/
theorem no_greatest_respecting_pairGuard :
    ¬ ∃ g, Respects chain g ∧ ∀ b, Respects chain b → b.Extends g := by
  rintro ⟨g, respects, greatest⟩
  exact no_common_feasible_upper_bound
    ⟨g, respects, greatest _ merges_respect_pairGuard.1, greatest _ merges_respect_pairGuard.2⟩

/-- Positive control: a metric guard is itself the greatest policy respecting
it, and the metric join of respecting policies respects it. -/
theorem metric_guard_greatest {guard : Tolerance (Fin 3)} (metric : guard.Metric) :
    Respects guard guard ∧ (∀ b, Respects guard b → b.Extends guard) ∧
      ∀ a b, Respects guard a → Respects guard b → Respects guard (metricJoin a b) :=
  ⟨⟨metric, fun _ _ => le_rfl⟩, fun _ respects => respects.2,
    fun a b ha hb => ⟨metricJoin_metric a b, metricJoin_extends_of_guard metric ha.2 hb.2⟩⟩

/-! ## Thresholds are not equalities -/

/-- **A threshold of a metric grade is not transitive**: in the metric
completion of the graded chain, `0` and `1` are within `1/5`, so are `1` and
`2`, but `0` and `2` are `2/5` apart. -/
theorem threshold_not_transitive :
    gradedCompletion.Metric ∧
      gradedCompletion.distance 0 1 ≤ 1 / 5 ∧ gradedCompletion.distance 1 2 ≤ 1 / 5 ∧
        ¬ gradedCompletion.distance 0 2 ≤ 1 / 5 := by
  refine ⟨graded_completion_is_least.2.1, ?_, ?_, ?_⟩ <;>
    norm_num [Tolerance.distance, gradedCompletion, Fin.ext_iff]

/-! ## Generated against observational -/

/-- One consumer reading the endpoint of an executed word: the empty word ends
at `0`, the words `a` and `b` both end at `1`. -/
def endpoint : ConsumerFamily Unit (Fin 3) where
  value _ i := if i = 0 then 0 else 1
  nonneg _ i := by split_ifs <;> norm_num
  le_one _ i := by split_ifs <;> norm_num

/-- The observational congruence identifies the two words. -/
theorem observational_identifies_words :
    (continuationTolerance (ContextMonoid.trivial (Fin 3)) endpoint).Indistinguishable 1 2 := by
  rw [continuationTolerance_indistinguishable_iff]
  intro _ _
  simp [endpoint, ContextMonoid.trivial]

/-- With no stipulations the generated congruence is equality. -/
theorem congGen_empty_eq {x y : Fin 3}
    (generated : CongGen (ContextMonoid.trivial (Fin 3)) (fun _ _ => False) x y) : x = y := by
  induction generated with
  | rel impossible => exact impossible.elim
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'
  | act _ _ ih => exact ih

/-- **Strict: generated inside observational, not equal.** No stipulation
relates the two words, yet no observation separates them. -/
theorem generated_strictly_inside_observational :
    (∀ {x y : Fin 3}, CongGen (ContextMonoid.trivial (Fin 3)) (fun _ _ => False) x y →
      (continuationTolerance (ContextMonoid.trivial (Fin 3)) endpoint).Indistinguishable x y) ∧
    ¬ CongGen (ContextMonoid.trivial (Fin 3)) (fun _ _ => False) 1 2 := by
  refine ⟨fun generated => congGen_le_observational _ endpoint _
    (fun impossible => impossible.elim) generated, fun generated => ?_⟩
  exact absurd (congGen_empty_eq generated) (by decide)

/-- The empty stipulations are not complete. -/
theorem empty_stipulations_incomplete :
    ¬ CompleteStipulations (ContextMonoid.trivial (Fin 3)) endpoint (fun _ _ => False) :=
  fun complete =>
    generated_strictly_inside_observational.2 (complete observational_identifies_words)

/-- Stipulating the two words identifies exactly the observational congruence:
the stipulations are complete. -/
theorem stipulated_words_complete :
    CompleteStipulations (ContextMonoid.trivial (Fin 3)) endpoint
      (fun x y => x = 1 ∧ y = 2) := by
  intro x y same
  rw [continuationTolerance_indistinguishable_iff] at same
  have values := same () ()
  simp only [endpoint, ContextMonoid.trivial] at values
  by_cases equal : x = y
  · subst equal
    exact CongGen.refl x
  · fin_cases x <;> fin_cases y <;> simp at values equal
    · exact CongGen.rel ⟨rfl, rfl⟩
    · exact CongGen.symm (CongGen.rel ⟨rfl, rfl⟩)

/-! ## The consumer guard is needed -/

/-- An idempotent continuation `c` on four states: `u ↦ 2`, `v ↦ 3`, and the
states `2`, `3` are fixed. -/
def continuation : ContextMonoid Bool (Fin 4) where
  act b i := if b then (if i = 0 then 2 else if i = 1 then 3 else i) else i
  unit := false
  mul := (· || ·)
  act_unit _ := rfl
  act_mul c d i := by
    cases c <;> cases d <;> fin_cases i <;> rfl

/-- The consumer reads `1` only at state `2`. -/
def reader : ConsumerFamily Unit (Fin 4) where
  value _ i := if i = 2 then 1 else 0
  nonneg _ i := by split_ifs <;> norm_num
  le_one _ i := by split_ifs <;> norm_num

/-- **Immediate agreement is too weak**: the consumer reads `u` and `v` alike,
but the continuation separates them, so the greatest adequate graded
congruence distinguishes what `1 − d_F` identifies. -/
theorem guard_needed :
    reader.tolerance.Indistinguishable 0 1 ∧
      ¬ (continuationTolerance continuation reader).Indistinguishable 0 1 ∧
      ¬ reader.tolerance.ContextClosed continuation := by
  have immediate : reader.tolerance.Indistinguishable 0 1 := by
    unfold Tolerance.Indistinguishable
    rw [ConsumerFamily.tolerance_distance, ConsumerFamily.distance_eq_zero_iff]
    intro _
    simp [reader]
  refine ⟨immediate, ?_, ?_⟩
  · rw [continuationTolerance_indistinguishable_iff]
    intro same
    have := same true ()
    simp [continuation, reader] at this
  · intro closed
    have separated := Tolerance.GradedCongruence.indistinguishable_act
      (M := continuation) ⟨reader.tolerance_metric, closed⟩ true immediate
    unfold Tolerance.Indistinguishable at separated
    rw [ConsumerFamily.tolerance_distance, ConsumerFamily.distance_eq_zero_iff] at separated
    have := separated ()
    simp [continuation, reader] at this

end Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruenceControls
