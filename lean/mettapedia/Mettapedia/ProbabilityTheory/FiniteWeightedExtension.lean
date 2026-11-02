import Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

/-!
# Weighted auxiliary variables and conservation of beliefs

An extended table is supplied independently of its source. Summing out its
auxiliary coordinate characterizes preservation of every source-query mass.
After normalization only proportionality remains observable. Thus a constant
multiplicity can disappear from probabilities while still changing mixture
revision. Zero total mass retains the existing absent-answer semantics.

Row-normalized weighted choices generalize deterministic extensions. Their
auxiliaries need not be unique, and source weights need not be independent.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.FiniteWeightedExtension

open scoped NNReal ENNReal BigOperators
open FiniteFunctionalExtension

variable {S A B : Type*} [Fintype S] [Fintype A] [Fintype B]

/-- Total weight of the auxiliary choices available at one source world. -/
def rowMass (kernel : S → A → ℝ≥0) (source : S) : ℝ≥0 := ∑ auxiliary, kernel source auxiliary

/-- Retain the source coordinate while attaching weighted auxiliary choices. -/
def weightedExtend (kernel : S → A → ℝ≥0) (weight : S → ℝ≥0) : S × A → ℝ≥0 :=
  fun world => weight world.1 * kernel world.1 world.2

omit [Fintype S] in
theorem marginalize_weightedExtend (kernel : S → A → ℝ≥0) (weight : S → ℝ≥0) :
    marginalize (weightedExtend kernel weight) = fun source => weight source * rowMass kernel source := by
  funext source
  simp [marginalize, weightedExtend, rowMass, Finset.mul_sum]

/-- Source observations depend exactly on the marginal, including total mass. -/
theorem observationMass_marginal (weight : S × A → ℝ≥0) :
    observationMass weight Prod.fst = observationMass (marginalize weight) id := by
  apply MassSemantics.ext
  · funext query
    simp only [observationMass, Fintype.sum_prod_type, marginalize, id_eq]
    apply congrArg (fun mass : ℝ≥0 => (mass : ℝ≥0∞))
    apply Finset.sum_congr rfl
    intro source _
    by_cases value : query source = true <;> simp [value]
  · simp [observationMass, marginalize, Fintype.sum_prod_type]

theorem observationMass_id_injective :
    Function.Injective (fun weight : S → ℝ≥0 => observationMass weight id) := by
  classical
  intro first second equal
  funext source
  have singleton := congrArg
    (fun mass : MassSemantics (S → Bool) => mass.queryMass (fun x => decide (x = source))) equal
  simp only [observationMass, id_eq, decide_eq_true_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at singleton
  exact ENNReal.coe_inj.mp singleton

/-- Exact conservation has a pointwise criterion; singleton queries prove necessity. -/
theorem mass_eq_iff_marginal (source : S → ℝ≥0) (target : S × A → ℝ≥0) :
    observationMass target Prod.fst = observationMass source id ↔ marginalize target = source := by
  rw [observationMass_marginal]
  exact observationMass_id_injective.eq_iff

/-- Zero-weight source worlds impose no condition on an auxiliary kernel. -/
theorem weighted_mass_eq_iff (kernel : S → A → ℝ≥0) (weight : S → ℝ≥0) :
    observationMass (weightedExtend kernel weight) Prod.fst = observationMass weight id ↔
      ∀ source, weight source ≠ 0 → rowMass kernel source = 1 := by
  rw [mass_eq_iff_marginal, marginalize_weightedExtend]
  constructor
  · intro equal source nonzero
    apply mul_left_cancel₀ nonzero
    simpa using congrFun equal source
  · intro rows
    funext source
    by_cases zero : weight source = 0
    · simp [zero]
    · simp [rows source zero]

theorem weighted_mass_eq_for_all_iff (kernel : S → A → ℝ≥0) :
    (∀ weight : S → ℝ≥0,
      observationMass (weightedExtend kernel weight) Prod.fst = observationMass weight id) ↔
      ∀ source, rowMass kernel source = 1 := by
  simp only [weighted_mass_eq_iff]
  constructor
  · intro all source
    exact all (fun _ => 1) source one_ne_zero
  · intro rows _ source _
    exact rows source

omit [Fintype S] [Fintype A] in
theorem weightedExtend_add (kernel : S → A → ℝ≥0) (first second : S → ℝ≥0) :
    weightedExtend kernel (first + second) = weightedExtend kernel first + weightedExtend kernel second := by
  funext world
  simp [weightedExtend, add_mul]

omit [Fintype S] [Fintype A] in
@[simp] theorem weightedExtend_zero (kernel : S → A → ℝ≥0) : weightedExtend kernel 0 = 0 := by
  funext world
  simp [weightedExtend]

/-- The second stage can depend on both the retained source and its first auxiliary. -/
def composeKernel (first : S → A → ℝ≥0) (second : S × A → B → ℝ≥0) : S → A × B → ℝ≥0 :=
  fun source auxiliary => first source auxiliary.1 * second (source, auxiliary.1) auxiliary.2

omit [Fintype S] in
theorem rowMass_composeKernel (first : S → A → ℝ≥0) (second : S × A → B → ℝ≥0) (source : S) :
    rowMass (composeKernel first second) source =
      ∑ auxiliary, first source auxiliary * rowMass second (source, auxiliary) := by
  simp [rowMass, composeKernel, Fintype.sum_prod_type, Finset.mul_sum]

omit [Fintype S] in
theorem composeKernel_normalized (first : S → A → ℝ≥0) (second : S × A → B → ℝ≥0)
    (firstRows : ∀ source, rowMass first source = 1)
    (secondRows : ∀ world, rowMass second world = 1) (source : S) :
    rowMass (composeKernel first second) source = 1 := by
  rw [rowMass_composeKernel]
  simp only [secondRows, mul_one]
  exact firstRows source

omit [Fintype S] [Fintype A] [Fintype B] in
theorem weightedExtend_staged (first : S → A → ℝ≥0) (second : S × A → B → ℝ≥0)
    (weight : S → ℝ≥0) (source : S) (a : A) (b : B) :
    weightedExtend second (weightedExtend first weight) ((source, a), b) =
      weightedExtend (composeKernel first second) weight (source, (a, b)) := by
  simp [weightedExtend, composeKernel, mul_assoc]

theorem staged_source_mass (first : S → A → ℝ≥0) (second : S × A → B → ℝ≥0)
    (firstRows : ∀ source, rowMass first source = 1)
    (secondRows : ∀ world, rowMass second world = 1) (weight : S → ℝ≥0) :
    observationMass (weightedExtend second (weightedExtend first weight)) (Prod.fst ∘ Prod.fst) =
      observationMass weight id := by
  have reassociate : weightedExtend second (weightedExtend first weight) =
      weightedExtend (composeKernel first second) weight ∘ Equiv.prodAssoc S A B := by
    funext world
    exact weightedExtend_staged first second weight world.1.1 world.1.2 world.2
  rw [reassociate]
  calc
    observationMass (weightedExtend (composeKernel first second) weight ∘ Equiv.prodAssoc S A B)
        (Prod.fst ∘ Prod.fst) =
        observationMass (weightedExtend (composeKernel first second) weight) Prod.fst :=
      observationMass_equiv (Equiv.prodAssoc S A B) _ Prod.fst
    _ = observationMass weight id :=
      (weighted_mass_eq_for_all_iff _).mpr (composeKernel_normalized first second firstRows secondRows) weight

section Deterministic

variable [DecidableEq A]

def deterministic (realize : S → A) : S → A → ℝ≥0 := fun source auxiliary =>
  if auxiliary = realize source then 1 else 0

omit [Fintype S] in
@[simp] theorem rowMass_deterministic (realize : S → A) (source : S) :
    rowMass (deterministic realize) source = 1 := by
  simp [rowMass, deterministic]

omit [Fintype S] [Fintype A] in
theorem deterministic_eq_extend (realize : S → A) (weight : S → ℝ≥0) :
    weightedExtend (deterministic realize) weight = extend realize weight := by
  funext world
  simp [weightedExtend, deterministic, extend, mul_ite]

end Deterministic

/-! ## What normalization forgets -/

theorem query_eq_some (weight : S → ℝ≥0) (positive : (∑ source, weight source) ≠ 0)
    (query : S → Bool) :
    (observationMass weight id).query query =
      some (((∑ source, if query source then weight source else 0) /
        ∑ source, weight source : ℝ≥0) : ℝ≥0∞) := by
  simp only [MassSemantics.query, MassSemantics.queryProb, observationMass, id_eq,
    ENNReal.coe_eq_zero, positive, if_false]
  rw [ENNReal.coe_div positive]

/-- With positive totals, all normalized answers agree precisely when the
complete source tables differ by one positive scalar. -/
theorem queries_eq_iff_proportional (source target : S → ℝ≥0)
    (sourcePositive : 0 < ∑ x, source x) (targetPositive : 0 < ∑ x, target x) :
    (∀ query, (observationMass target id).query query = (observationMass source id).query query) ↔
      ∃ scale : ℝ≥0, 0 < scale ∧ target = fun x => scale * source x := by
  classical
  constructor
  · intro equal
    refine ⟨(∑ x, target x) / ∑ x, source x, div_pos targetPositive sourcePositive, ?_⟩
    funext x
    have singleton := equal (fun y => decide (y = x))
    rw [query_eq_some target targetPositive.ne', query_eq_some source sourcePositive.ne'] at singleton
    have ratio : target x / (∑ y, target y) = source x / (∑ y, source y) := by
      simpa only [decide_eq_true_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Option.some.injEq, ENNReal.coe_inj] using singleton
    calc
      target x = (source x / ∑ y, source y) * ∑ y, target y :=
        (div_eq_iff targetPositive.ne').mp ratio
      _ = ((∑ y, target y) / ∑ y, source y) * source x := by
        simp only [div_eq_mul_inv]
        ac_rfl
  · rintro ⟨scale, positive, rfl⟩ query
    rw [query_eq_some _ targetPositive.ne', query_eq_some _ sourcePositive.ne']
    apply congrArg some
    apply congrArg (fun mass : ℝ≥0 => (mass : ℝ≥0∞))
    have numerator : (∑ x, if query x then scale * source x else 0) =
        scale * ∑ x, if query x then source x else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    rw [numerator, ← Finset.mul_sum]
    apply (div_eq_div_iff (mul_ne_zero positive.ne' sourcePositive.ne') sourcePositive.ne').mpr
    ac_rfl

/-- Auxiliary multiplicity is invisible to normalized source queries exactly
when its marginal is a common positive rescaling of the source. -/
theorem extended_queries_eq_iff (source : S → ℝ≥0) (target : S × A → ℝ≥0)
    (sourcePositive : 0 < ∑ x, source x) (targetPositive : 0 < ∑ world, target world) :
    (∀ query, (observationMass target Prod.fst).query query = (observationMass source id).query query) ↔
      ∃ scale : ℝ≥0, 0 < scale ∧ marginalize target = fun x => scale * source x := by
  rw [observationMass_marginal]
  apply queries_eq_iff_proportional source (marginalize target) sourcePositive
  simpa only [marginalize, Fintype.sum_prod_type] using targetPositive

theorem weighted_queries_eq_iff (kernel : S → A → ℝ≥0) (weight : S → ℝ≥0)
    (sourcePositive : 0 < ∑ x, weight x)
    (targetPositive : 0 < ∑ world, weightedExtend kernel weight world) :
    (∀ query, (observationMass (weightedExtend kernel weight) Prod.fst).query query =
      (observationMass weight id).query query) ↔
      ∃ scale : ℝ≥0, 0 < scale ∧
        ∀ source, weight source ≠ 0 → rowMass kernel source = scale := by
  rw [extended_queries_eq_iff weight _ sourcePositive targetPositive, marginalize_weightedExtend]
  constructor
  · rintro ⟨scale, positive, equal⟩
    refine ⟨scale, positive, fun source nonzero => ?_⟩
    apply mul_left_cancel₀ nonzero
    simpa only [mul_comm scale] using congrFun equal source
  · rintro ⟨scale, positive, rows⟩
    refine ⟨scale, positive, ?_⟩
    funext source
    by_cases zero : weight source = 0
    · simp [zero]
    · simp [rows source zero, mul_comm]

@[simp] theorem zero_source_query (kernel : S → A → ℝ≥0) (query : S → Bool) :
    (observationMass (weightedExtend kernel 0) Prod.fst).query query = none := by
  simp [weightedExtend, observationMass, MassSemantics.query]

open Mettapedia.Logic.WorldModel

/-- A normalized auxiliary kernel preserves source observations and additive
mixture revision. No observation of the auxiliary itself is asserted. -/
noncomputable def interpretation (kernel : S → A → ℝ≥0)
    (rows : ∀ source, rowMass kernel source = 1) :
    @RevisionMap (S → ℝ≥0) (S → Bool) (Option ℝ≥0∞)
      (S × A → ℝ≥0) (S → Bool) (Option ℝ≥0∞)
      (tableModel id).toWorldModel (tableModel Prod.fst).toWorldModel := by
  letI := tableModel (Source := S) id
  letI := tableModel (Source := S × A) Prod.fst
  exact {
    state := weightedExtend kernel
    query := id
    value := id
    observe := fun weight query => by
      change (observationMass (weightedExtend kernel weight) Prod.fst).query query =
        (observationMass weight id).query query
      rw [(weighted_mass_eq_for_all_iff kernel).mpr rows weight]
    empty := weightedExtend_zero kernel
    revise := weightedExtend_add kernel }

namespace Controls

def source : Bool → ℝ≥0 := fun value => if value then 3 else 1
def duplicate (_source _auxiliary : Bool) : ℝ≥0 := 1
noncomputable def half (_source _auxiliary : Bool) : ℝ≥0 := 1 / 2
def pointWeight (value : Bool) : Bool → ℝ≥0 := fun source => if source = value then 1 else 0

theorem duplicate_mass_changes :
    (observationMass (weightedExtend duplicate source) Prod.fst).totalMass = 8 ∧
      (observationMass source id).totalMass = 4 := by
  norm_num [observationMass, weightedExtend, duplicate, source, Fintype.sum_prod_type, Fintype.sum_bool]

theorem duplicate_probabilities_unchanged (query : Bool → Bool) :
    (observationMass (weightedExtend duplicate source) Prod.fst).query query =
      (observationMass source id).query query := by
  apply (weighted_queries_eq_iff duplicate source
    (by norm_num [source, Fintype.sum_bool])
    (by norm_num [weightedExtend, duplicate, source, Fintype.sum_prod_type, Fintype.sum_bool])).mpr
      ⟨2, by norm_num, fun value _ => by norm_num [rowMass, duplicate, Fintype.sum_bool]⟩ query

theorem nonunique_half_preserves_mass (weight : Bool → ℝ≥0) :
    observationMass (weightedExtend half weight) Prod.fst = observationMass weight id :=
  (weighted_mass_eq_for_all_iff half).mpr
    (fun _ => by norm_num [rowMass, half, Fintype.sum_bool]) weight

theorem both_auxiliaries_positive :
    0 < weightedExtend half source (true, false) ∧
      0 < weightedExtend half source (true, true) := by
  norm_num [weightedExtend, half, source]

/-- Source preservation does not determine a fresh auxiliary observation. -/
theorem auxiliary_observation_differs :
    (observationMass (weightedExtend half (fun _ => 2)) Prod.snd).query id = some (1/2 : ℝ≥0∞) ∧
      (observationMass (weightedExtend (deterministic (fun _ : Bool => false)) (fun _ => 2)) Prod.snd).query id =
        some (0 : ℝ≥0∞) := by
  simp only [observationMass, weightedExtend, half, deterministic,
    MassSemantics.query, MassSemantics.queryProb, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  have finiteRatio : (2 : ℝ≥0) / 4 = (2 : ℝ≥0)⁻¹ := by norm_num
  have castRatio := congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) finiteRatio
  simpa only [ENNReal.coe_div (by norm_num : (4 : ℝ≥0) ≠ 0),
    ENNReal.coe_inv (by norm_num : (2 : ℝ≥0) ≠ 0), ENNReal.coe_ofNat] using castRatio

theorem individual_rescaling_invisible (query : Bool → Bool) :
    (observationMass (fun x => 2 * pointWeight true x) id).query query =
      (observationMass (pointWeight true) id).query query := by
  apply (queries_eq_iff_proportional (pointWeight true) (fun x => 2 * pointWeight true x)
    (by norm_num [pointWeight, Fintype.sum_bool])
    (by norm_num [pointWeight, Fintype.sum_bool])).mpr ⟨2, by norm_num, rfl⟩ query

theorem separate_rescaling_biases_mixture :
    (observationMass (fun x => pointWeight true x + pointWeight false x) id).query id =
        some (1/2 : ℝ≥0∞) ∧
      (observationMass (fun x => 2 * pointWeight true x + pointWeight false x) id).query id =
        some (2/3 : ℝ≥0∞) := by
  norm_num [observationMass, pointWeight, MassSemantics.query, MassSemantics.queryProb, Fintype.sum_bool]

def unsupportedRows (source auxiliary : Bool) : ℝ≥0 :=
  if source then (if auxiliary then 1 else 0) else 42

theorem zero_source_row_irrelevant :
    rowMass unsupportedRows false = 84 ∧
      observationMass (weightedExtend unsupportedRows (pointWeight true)) Prod.fst =
        observationMass (pointWeight true) id := by
  constructor
  · norm_num [rowMass, unsupportedRows, Fintype.sum_bool]
  · apply (weighted_mass_eq_iff _ _).mpr
    intro value positive
    cases value
    · simp [pointWeight] at positive
    · norm_num [rowMass, unsupportedRows, Fintype.sum_bool]

noncomputable def dependentStages : Bool → Bool × Bool → ℝ≥0 :=
  composeKernel half (deterministic (fun world : Bool × Bool => world.1.xor world.2))

theorem dependent_stages_normalized (source : Bool) : rowMass dependentStages source = 1 := by
  apply composeKernel_normalized half (deterministic _)
  · intro value
    norm_num [rowMass, half, Fintype.sum_bool]
  · intro world
    exact rowMass_deterministic _ world

/-- Equal first-stage auxiliary weights do not erase the source needed later. -/
theorem dependent_stage_uses_retained_source :
    half false false = half true false ∧
      dependentStages false (false, true) = 0 ∧ dependentStages true (false, true) = 1/2 := by
  norm_num [half, dependentStages, composeKernel, deterministic]

end Controls

end Mettapedia.ProbabilityTheory.FiniteWeightedExtension
