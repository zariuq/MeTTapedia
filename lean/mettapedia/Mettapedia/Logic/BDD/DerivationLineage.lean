import Mettapedia.Logic.BDD.TseitinCounting
import Mettapedia.Evidence.SourceScopeProbabilityBoundary
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Derivation alternatives denote events, not independent observations

A lineage retains a finite list of derivation supports. Within each support,
base events are conjoined; alternatives are disjoined. Repeating a derivation
does not create probability mass. The construction is connected to the existing
positive ProbLog compilation relation, rather than postulating that an arbitrary
list enumerates every proof of a query.

Event realization is explicit. Provenance labels need not denote independent
events; normalized product-coordinate weights are a separate model assumption.
The counting backend is the existing certified BDD counter via emitted Tseitin
clauses. No claim is made about completeness of a bounded runtime search.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.BDDCore.DerivationLineage

open scoped NNReal ENNReal BigOperators
open LO.Propositional (Formula)
open PropositionalTseitin TseitinCounting
open Mettapedia.Logic.LP
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation

abbrev Lineage (α : Type*) := List (Finset α)

def supportHolds {α : Type*} (support : Finset α) (world : α → Bool) : Bool :=
  decide (∀ i ∈ support, world i = true)

def holds {α : Type*} (lineage : Lineage α) (world : α → Bool) : Bool :=
  lineage.any (fun support => supportHolds support world)

@[simp] theorem supportHolds_union {α : Type*} [DecidableEq α]
    (first second : Finset α) (world : α → Bool) :
    supportHolds (first ∪ second) world = (supportHolds first world && supportHolds second world) := by
  apply Bool.eq_iff_iff.mpr
  simp only [supportHolds, decide_eq_true_eq, Finset.mem_union, Bool.and_eq_true]
  aesop

@[simp] theorem holds_append {α : Type*} (first second : Lineage α) (world : α → Bool) :
    holds (first ++ second) world = (holds first world || holds second world) := by
  simp [holds]

/-- Keep derivation occurrences, while combining repeated base events idempotently. -/
def conjoin {α : Type*} [DecidableEq α] (first second : Lineage α) : Lineage α :=
  first.flatMap fun left => second.map fun right => left ∪ right

theorem holds_conjoin {α : Type*} [DecidableEq α]
    (first second : Lineage α) (world : α → Bool) :
    holds (conjoin first second) world = (holds first world && holds second world) := by
  apply Bool.eq_iff_iff.mpr
  simp only [holds, conjoin, List.any_eq_true, List.mem_flatMap, List.mem_map,
    Bool.and_eq_true]
  aesop

theorem duplicate_invariant {α : Type*} (lineage : Lineage α) (world : α → Bool) :
    holds (lineage ++ lineage) world = holds lineage world := by simp

theorem permutation_invariant {α : Type*} {first second : Lineage α}
    (permuted : first.Perm second) (world : α → Bool) : holds first world = holds second world :=
  List.Perm.any_eq permuted

def conjunction {α : Type*} : List α → Formula α
  | [] => .imp .falsum .falsum
  | atom :: rest => .and (.atom atom) (conjunction rest)

theorem eval_conjunction {α : Type*} (atoms : List α) (world : α → Bool) :
    eval world (conjunction atoms) = atoms.all world := by
  induction atoms <;> simp_all [conjunction, eval]

def supportFormula {n : Nat} (support : Finset (Fin n)) : Formula (Fin n) :=
  conjunction (support.sort (· ≤ ·))

theorem eval_supportFormula {n : Nat} (support : Finset (Fin n)) (world : Fin n → Bool) :
    eval world (supportFormula support) = supportHolds support world := by
  apply Bool.eq_iff_iff.mpr
  simp [supportFormula, eval_conjunction, supportHolds]

def lineageFormula {n : Nat} : Lineage (Fin n) → Formula (Fin n)
  | [] => .falsum
  | support :: rest => .or (supportFormula support) (lineageFormula rest)

theorem eval_lineageFormula {n : Nat} (lineage : Lineage (Fin n)) (world : Fin n → Bool) :
    eval world (lineageFormula lineage) = holds lineage world := by
  induction lineage <;> simp_all [lineageFormula, eval, holds, eval_supportFormula]

/-! ## Recover lineage from actual positive compilation derivations -/

private def HasLineage {n : Nat} (f : BDD n) : Prop :=
  ∃ lineage : Lineage (Fin n), ∀ world, f.eval world = holds lineage world

private theorem hasLineage_and {n : Nat} {first second : BDD n}
    (hf : HasLineage first) (hs : HasLineage second) : HasLineage (apply (· && ·) first second) := by
  obtain ⟨left, hl⟩ := hf
  obtain ⟨right, hr⟩ := hs
  exact ⟨conjoin left right, fun world => by rw [apply_eval, holds_conjoin, hl, hr]⟩

private theorem hasLineage_or {n : Nat} {first second : BDD n}
    (hf : HasLineage first) (hs : HasLineage second) : HasLineage (apply (· || ·) first second) := by
  obtain ⟨left, hl⟩ := hf
  obtain ⟨right, hr⟩ := hs
  exact ⟨left ++ right, fun world => by rw [apply_eval, holds_append, hl, hr]⟩

private theorem hasLineage_fold {n : Nat} (bdds : List (BDD n)) (initial : BDD n)
    (hi : HasLineage initial) (hb : ∀ b ∈ bdds, HasLineage b) :
    HasLineage (bdds.foldl (apply (· && ·)) initial) := by
  induction bdds generalizing initial with
  | nil => exact hi
  | cons b rest ih =>
    exact ih _ (hasLineage_and hi (hb b (by simp))) (fun b h => hb b (by simp [h]))

/-- The existence statement is proved from the compilation derivation, including
all grounded rule cases. It is not a computable extraction from a proof in `Prop`. -/
theorem GroundBDDCompile_hasLineage {σ : LPSignature} {n : Nat}
    {prog : ProbLogProgram σ n} {query : GroundAtom σ} {f : BDD n}
    (compiled : GroundBDDCompile prog query f) :
    ∃ lineage : Lineage (Fin n), ∀ world, f.eval world = holds lineage world := by
  change HasLineage f
  induction compiled with
  | fact i => exact ⟨[{i}], fun world => by simp [holds, supportHolds]⟩
  | ruleNil => exact ⟨[∅], fun world => by simp [holds, supportHolds]⟩
  | ruleOne _ _ _ _ _ ih => exact ih
  | rulePair _ _ _ _ _ _ _ _ _ frest hrest_len _ _ hconj ih₁ ih₂ ih_rest =>
    subst hconj
    apply hasLineage_fold _ _ ih₁
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hrest
    · exact ih₂
    · obtain ⟨j, hj⟩ := List.mem_iff_get.mp hrest
      rw [← hj]
      exact ih_rest ⟨j, by omega⟩
  | ruleG _ _ _ _ _ bodyBDDs hlen _ _ hconj =>
    subst hconj
    rename_i ih
    apply hasLineage_fold _ _ ⟨[∅], fun world => by simp [holds, supportHolds]⟩
    intro b hb
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hb
    rw [← hj]
    exact ih ⟨j, by omega⟩
  | disj _ _ _ _ _ ih₁ ih₂ => exact hasLineage_or ih₁ ih₂
  | bottom => exact ⟨[], fun world => by simp [holds]⟩

/-- Completeness is inherited from the existing query compiler. This does not
assert that a bounded search has found the complete cover. -/
theorem exists_complete_lineage {σ : LPSignature} {n : Nat}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (query : GroundAtom σ) :
    ∃ lineage : Lineage (Fin n),
      ∀ world, holds lineage world = true ↔ queryHoldsA prog query world := by
  obtain ⟨f, compiled, complete⟩ := exists_complete_bdd prog query
  obtain ⟨lineage, interpreted⟩ := GroundBDDCompile_hasLineage compiled
  refine ⟨lineage, fun world => ?_⟩
  rw [← interpreted world]
  exact ⟨GroundBDDCompile_sound prog query f compiled world, complete world⟩

/-- Supplied finite lineage is counted by the emitted-clause BDD, not by summing proofs. -/
theorem lineage_count_correct {n : Nat} (lineage : Lineage (Fin n)) (p : Fin n → ℝ≥0)
    (hp : ∀ i, p i ≤ 1) :
    tseitinCount (lineageFormula lineage) p =
      weightedSat (holds lineage) (fun i => (p i : ℝ≥0∞)) := by
  rw [tseitinCount_eq_weightedSat _ p hp]
  simp only [eval_lineageFormula]

/-- An incomplete compilation witness counts only worlds where the query holds. -/
theorem compiled_cover_count_le {σ : LPSignature} {n : Nat}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (query : GroundAtom σ) (f : BDD n)
    (compiled : GroundBDDCompile prog query f)
    (lineage : Lineage (Fin n)) (interpreted : ∀ world, f.eval world = holds lineage world)
    (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    tseitinCount (lineageFormula lineage) p ≤
      @weightedSat n (fun world => by classical exact decide (queryHoldsA prog query world))
        (fun i => (p i : ℝ≥0∞)) := by
  classical
  rw [lineage_count_correct _ p hp]
  apply Finset.sum_le_sum
  intro world _
  by_cases held : holds lineage world = true
  · have trueQuery := GroundBDDCompile_sound prog query f compiled world ((interpreted world).trans held)
    simp [held, trueQuery]
  · simp [held]

/-- Complete covers exist by the existing compiler's completeness theorem. -/
theorem exists_exact_query_count {σ : LPSignature} {n : Nat}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (query : GroundAtom σ) :
    ∃ lineage : Lineage (Fin n),
      (∀ world, holds lineage world = true ↔ queryHoldsA prog query world) ∧
      ∀ (p : Fin n → ℝ≥0), (∀ i, p i ≤ 1) →
        tseitinCount (lineageFormula lineage) p =
          @weightedSat n (fun world => by classical exact decide (queryHoldsA prog query world))
            (fun i => (p i : ℝ≥0∞)) := by
  classical
  obtain ⟨lineage, exactCover⟩ := exists_complete_lineage prog query
  refine ⟨lineage, exactCover, fun p hp => ?_⟩
  rw [lineage_count_correct lineage p hp]
  congr 1
  funext world
  exact Bool.eq_iff_iff.mpr (by simpa using exactCover world)

/-- Agreement with the existing positive ProbMeTTa runtime-core semantics.
The source program and its least-model query are retained on both routes. -/
theorem exists_runtime_count_agreement {σ : LPSignature} {n : Nat}
    [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (prog : ProbLogProgram σ n) (query : GroundAtom σ) :
    ∃ (lineage : Lineage (Fin n)) (f : BDD n),
      (∀ world, holds lineage world = true ↔ queryHoldsA prog query world) ∧
      ProbMeTTaCoreEval prog (.queryBDD query) f ∧ f.Ordered none ∧
      ∀ (p : Fin n → ℝ≥0), (∀ i, p i ≤ 1) →
        tseitinCount (lineageFormula lineage) p = bdd_wmc f (fun i => (p i : ℝ≥0∞)) := by
  classical
  obtain ⟨lineage, exactCover, counted⟩ := exists_exact_query_count prog query
  obtain ⟨f, executed, ordered, interpreted⟩ := probmetta_runtime_query_bdd_exact prog query
  refine ⟨lineage, f, exactCover, executed, ordered, fun p hp => ?_⟩
  rw [counted p hp, bdd_wmc_correct f ordered _ (fun i => by exact_mod_cast hp i)]
  congr 1
  funext world
  exact Bool.eq_iff_iff.mpr (by simpa using (interpreted world).symm)

/-! ## Independent event realization and probability -/

open MeasureTheory
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathDependency
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNMultiPathFrechet

def supportEvent {α Ω : Type*} (events : α → Set Ω) (support : Finset α) : Set Ω :=
  {world | ∀ i ∈ support, world ∈ events i}

def lineageEvent {α Ω : Type*} (events : α → Set Ω) (lineage : Lineage α) : Set Ω :=
  ⋃ i : Fin lineage.length, supportEvent events (lineage.get i)

theorem supportEvent_measurable {α Ω : Type*} [MeasurableSpace Ω]
    (events : α → Set Ω) (measurable : ∀ i, MeasurableSet (events i)) (support : Finset α) :
    MeasurableSet (supportEvent events support) := by
  classical
  induction support using Finset.induction_on with
  | empty => simp [supportEvent]
  | @insert i rest absent ih =>
    have equal : supportEvent events (insert i rest) = events i ∩ supportEvent events rest := by
      ext world
      simp [supportEvent]
    rw [equal]
    exact (measurable i).inter ih

theorem lineageEvent_measurable {α Ω : Type*} [MeasurableSpace Ω]
    (events : α → Set Ω) (measurable : ∀ i, MeasurableSet (events i)) (lineage : Lineage α) :
    MeasurableSet (lineageEvent events lineage) :=
  MeasurableSet.iUnion (fun _ => supportEvent_measurable events measurable _)

theorem lineageEvent_coordinates {n : Nat} (lineage : Lineage (Fin n)) :
    lineageEvent (fun i => {world : Fin n → Bool | world i = true}) lineage =
      {world | holds lineage world = true} := by
  ext world
  simp only [lineageEvent, Set.mem_iUnion, supportEvent, Set.mem_ofPred_eq,
    holds, List.any_eq_true, supportHolds, decide_eq_true_eq]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨lineage.get i, List.get_mem _ _, hi⟩
  · rintro ⟨support, member, held⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp member
    exact ⟨i, held⟩

noncomputable def productMeasure {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    Measure (Fin n → Bool) := Measure.pi fun i => probLogBernoulliMeasure (p i) (hp i)

instance productMeasure_probability {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    IsProbabilityMeasure (productMeasure p hp) := by unfold productMeasure; infer_instance

theorem productMeasure_singleton {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (world : Fin n → Bool) : productMeasure p hp {world} = (productWeight p world : ℝ≥0∞) := by
  rw [productMeasure, Measure.pi_singleton]
  simp only [productWeight]
  push_cast
  apply Finset.prod_congr rfl
  intro i _
  cases world i <;>
    simp [probLogBernoulliMeasure,
      Mettapedia.PLN.Bridges.Languages.ProbLog.Infinite.bernoulliMeasure_false]

theorem productMeasure_event {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (event : (Fin n → Bool) → Bool) :
    productMeasure p hp {world | event world = true} =
      weightedSat event (fun i => (p i : ℝ≥0∞)) := by
  classical
  have equal : {world | event world = true} =
      ((Finset.univ.filter fun world => event world = true : Finset (Fin n → Bool)) : Set (Fin n → Bool)) := by
    ext world
    simp
  rw [equal, ← sum_measure_singleton]
  simp [Finset.sum_filter, productMeasure_singleton, coe_productWeight, weightedSat]

/-- The event interpretation and emitted-clause counter agree under the explicit product law. -/
theorem lineage_probability_exact {n : Nat} (lineage : Lineage (Fin n))
    (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    productMeasure p hp (lineageEvent (fun i => {world : Fin n → Bool | world i = true}) lineage) =
      tseitinCount (lineageFormula lineage) p := by
  rw [lineageEvent_coordinates, productMeasure_event, lineage_count_correct lineage p hp]

/-! ## Exact conditions for combining derivation probabilities -/

/-- Summation requires almost-everywhere disjoint events, not disjoint source names. -/
theorem lineage_sum_exact_iff {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : α → Set Ω) (measurable : ∀ i, MeasurableSet (events i))
    (first : Finset α) (rest : Lineage α) :
    μ.real (lineageEvent events (first :: rest)) =
        ∑ i : Fin (rest.length + 1), μ.real (supportEvent events ((first :: rest).get i)) ↔
      Pairwise (fun i j : Fin (rest.length + 1) =>
        AEDisjoint μ (supportEvent events ((first :: rest).get i))
          (supportEvent events ((first :: rest).get j))) :=
  measureReal_iUnion_eq_sum_iff_pairwise_aedisjoint _
    (fun _ => (supportEvent_measurable events measurable _).nullMeasurableSet)

/-- For two events, noisy-or is exact precisely at their independence value. -/
theorem noisyOr_pair_exact_iff {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A B : Set Ω)
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    μ.real (A ∪ B) = noisyOrFrequency (fun i : Fin 2 => if i = 0 then μ.real A else μ.real B) ↔
      μ.real (A ∩ B) = μ.real A * μ.real B := by
  rw [pair_union_measureReal_eq_add_sub_inter μ hA hB]
  norm_num [noisyOrFrequency]
  constructor <;> intro h <;> nlinarith

/-- Joint independence licenses noisy-or for a whole finite family.
No converse from one numerical union equality to joint independence is asserted. -/
theorem lineage_noisyOr_of_independent {α Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (events : α → Set Ω) (measurable : ∀ i, MeasurableSet (events i)) (lineage : Lineage α)
    (independent : _root_.ProbabilityTheory.iIndepSet
      (fun i : Fin lineage.length => supportEvent events (lineage.get i)) μ) :
    μ.real (lineageEvent events lineage) = noisyOrFrequency
      (fun i : Fin lineage.length => μ.real (supportEvent events (lineage.get i))) :=
  measureReal_iUnion_eq_noisyOrFrequency_of_iIndepSet _
    (fun _ => supportEvent_measurable events measurable _) independent

def coordinateEvent {n : Nat} (i : Fin n) : Set (Fin n → Bool) := {world | world i = true}

theorem coordinateEvent_measurable {n : Nat} (i : Fin n) : MeasurableSet (coordinateEvent i) := by
  exact (measurable_pi_apply i : Measurable (fun world : Fin n → Bool => world i))
    (measurableSet_singleton true)

theorem supportEvent_inter {α Ω : Type*} [DecidableEq α] (events : α → Set Ω)
    (first second : Finset α) :
    supportEvent events first ∩ supportEvent events second = supportEvent events (first ∪ second) := by
  ext world
  simp only [supportEvent, Set.mem_inter_iff, Set.mem_ofPred_eq, Finset.mem_union]
  aesop

theorem productMeasure_support {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (support : Finset (Fin n)) :
    productMeasure p hp (supportEvent coordinateEvent support) = ∏ i ∈ support, (p i : ℝ≥0∞) := by
  change Measure.pi (fun i => probLogBernoulliMeasure (p i) (hp i))
    ((support : Set (Fin n)).pi (fun _ => ({true} : Set Bool))) = _
  rw [Measure.pi_pi_finset]
  simp only [probLogBernoulliMeasure_true]

theorem productMeasure_support_real {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1)
    (support : Finset (Fin n)) :
    (productMeasure p hp).real (supportEvent coordinateEvent support) = ∏ i ∈ support, (p i : ℝ) := by
  simp [Measure.real, productMeasure_support, ENNReal.toReal_prod]

/-- This converse needs strictly nondegenerate coordinates. Zero/one sources
can make shared-support events accidentally independent. -/
theorem product_support_factorization_iff {n : Nat} (p : Fin n → ℝ≥0)
    (positive : ∀ i, 0 < p i) (belowOne : ∀ i, p i < 1) (first second : Finset (Fin n)) :
    (∏ i ∈ first ∪ second, (p i : ℝ)) =
        (∏ i ∈ first, (p i : ℝ)) * (∏ i ∈ second, (p i : ℝ)) ↔ Disjoint first second := by
  constructor
  · intro equal
    have prodPositive : 0 < ∏ i ∈ first ∪ second, (p i : ℝ) :=
      Finset.prod_pos (fun i _ => by exact_mod_cast positive i)
    have overlapOne : (∏ i ∈ first ∩ second, (p i : ℝ)) = 1 := by
      apply mul_left_cancel₀ prodPositive.ne'
      calc
        _ = (∏ i ∈ first, (p i : ℝ)) * (∏ i ∈ second, (p i : ℝ)) := Finset.prod_union_inter
        _ = _ := by rw [← equal, mul_one]
    have overlapOneNN : (∏ i ∈ first ∩ second, p i) = 1 := by exact_mod_cast overlapOne
    have eachOne := (Finset.prod_eq_one_iff_of_le_one'
      (fun i (_ : i ∈ first ∩ second) => (belowOne i).le)).mp overlapOneNN
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (belowOne i).ne (eachOne i (Finset.mem_inter.mpr ⟨hi, hj⟩))
  · intro disjoint
    exact Finset.prod_union disjoint

/-- Disjoint coordinate supports are exactly the noisy-or case in the strictly
nondegenerate positive-conjunction fragment. -/
theorem product_noisyOr_exact_iff_disjoint {n : Nat} (p : Fin n → ℝ≥0)
    (positive : ∀ i, 0 < p i) (belowOne : ∀ i, p i < 1) (first second : Finset (Fin n)) :
    let μ := productMeasure p (fun i => (belowOne i).le)
    μ.real (supportEvent coordinateEvent first ∪ supportEvent coordinateEvent second) =
      noisyOrFrequency (fun i : Fin 2 => if i = 0 then μ.real (supportEvent coordinateEvent first)
        else μ.real (supportEvent coordinateEvent second)) ↔ Disjoint first second := by
  intro μ
  rw [noisyOr_pair_exact_iff μ _ _
    (supportEvent_measurable _ coordinateEvent_measurable first)
    (supportEvent_measurable _ coordinateEvent_measurable second), supportEvent_inter]
  simp only [μ, productMeasure_support_real]
  exact product_support_factorization_iff p positive belowOne first second

namespace Controls

def shared : Lineage (Fin 1) := [{0}, {0}]
def separate : Lineage (Fin 2) := [{0}, {1}]

theorem shared_event_once :
    tseitinCount (lineageFormula shared) (fun _ => 1/2) = 1/2 ∧
      noisyOrFrequency (fun _ : Fin 2 => (1/2 : ℝ)) = 3/4 ∧
      (∑ _ : Fin 2, (1/2 : ℝ)) = 1 := by
  constructor
  · rw [fair_count]
    have models : PropositionalTseitinMass.Controls.count
        (fun world : Fin 1 → Bool => eval world (lineageFormula shared)) = 1 := by
      simp_rw [eval_lineageFormula]
      decide
    norm_num [models]
  · norm_num [noisyOrFrequency]

/-- Disjoint fact coordinates can both hold: addition is still wrong for their OR. -/
theorem separate_coordinates_overlap_as_events :
    Disjoint ({0} : Finset (Fin 2)) {1} ∧
      tseitinCount (lineageFormula separate) (fun _ => 1/2) = 3/4 ∧
      tseitinCount (.and (.atom 0) (.atom 1) : Formula (Fin 2)) (fun _ => 1/2) = 1/4 := by
  refine ⟨by decide, ?_, TseitinCounting.Controls.correlated_mixture_not_product_marginals.2⟩
  rw [fair_count]
  have models : PropositionalTseitinMass.Controls.count
      (fun world : Fin 2 → Bool => eval world (lineageFormula separate)) = 3 := by
    simp_rw [eval_lineageFormula]
    decide
  norm_num [models]

/-- A zero-probability shared source is a boundary case for the strict-support converse. -/
theorem zero_shared_source_no_bias :
    tseitinCount (lineageFormula shared) (pointPrior (fun _ => false)) = 0 ∧
      noisyOrFrequency (fun _ : Fin 2 => (0 : ℝ)) = 0 ∧
      ¬ Disjoint ({0} : Finset (Fin 1)) {0} := by
  rw [point_count]
  norm_num [lineageFormula, shared, supportFormula, conjunction, eval, noisyOrFrequency]

theorem certain_shared_source_no_bias :
    tseitinCount (lineageFormula shared) (pointPrior (fun _ => true)) = 1 ∧
      noisyOrFrequency (fun _ : Fin 2 => (1 : ℝ)) = 1 := by
  rw [point_count]
  norm_num [lineageFormula, shared, supportFormula, conjunction, eval, noisyOrFrequency]

theorem empty_cover_zero {n : Nat} (p : Fin n → ℝ≥0) (hp : ∀ i, p i ≤ 1) :
    tseitinCount (lineageFormula []) p = 0 := by
  simp [tseitinCount_correct _ _ hp, lineageFormula, eval]

open Mettapedia.Evidence.SourceScopeProbabilityBoundary

/-- The original source-scope control, interpreted as two lineage alternatives. -/
theorem separate_labels_common_event :
    Mettapedia.Evidence.SourceScoped.Independent correlatedLeft correlatedRight ∧
      fairWorldMeasure (lineageEvent (fun _ : Fin 2 => commonLatentEvent) separate) = 1/2 ∧
      noisyOrFrequency (fun _ : Fin 2 => (1/2 : ℝ)) = 3/4 := by
  refine ⟨correlated_packets_sourceIndependent, ?_, by norm_num [noisyOrFrequency]⟩
  have equal : lineageEvent (fun _ : Fin 2 => commonLatentEvent) separate = commonLatentEvent := by
    ext world
    simp [lineageEvent, supportEvent, separate, Fin.exists_fin_two]
  rw [equal, fairWorldMeasure_commonLatentEvent]

/-! Two actual rule derivations share the same probabilistic fact. -/

private def signature : LPSignature where
  constants := Unit
  vars := Empty
  relationSymbols := Fin 3
  relationArity _ := 0
  functionSymbols := Empty
  functionArity := Empty.elim

private def atom (i : Fin 3) : GroundAtom signature := ⟨i, Fin.elim0⟩

private noncomputable def program : ProbLogProgram signature 1 where
  probFacts _ := atom 0
  probs _ := 1/2
  rules := [⟨(atom 2).toAtom, [(atom 0).toAtom]⟩,
    ⟨(atom 1).toAtom, [(atom 0).toAtom]⟩, ⟨(atom 2).toAtom, [(atom 1).toAtom]⟩]
  facts_injective := fun _ _ _ => Subsingleton.elim _ _

private theorem direct_derivation : GroundBDDCompile program (atom 2) (bddVar 0) :=
  .ruleOne (atom 2) (atom 0) (by simp [program]) _ (.fact 0)

private theorem indirect_derivation : GroundBDDCompile program (atom 2) (bddVar 0) :=
  .ruleOne (atom 2) (atom 1) (by simp [program]) _
    (.ruleOne (atom 1) (atom 0) (by simp [program]) _ (.fact 0))

theorem shared_cover_complete (world : Fin 1 → Bool) :
    holds shared world = true ↔ queryHoldsA program (atom 2) world := by
  let : Nonempty (GroundTerm signature) := ⟨.const ()⟩
  let : IsEmpty signature.functionSymbols := ⟨Empty.elim⟩
  simp only [holds, shared, List.any_cons, List.any_nil, Bool.or_false, Bool.or_self,
    supportHolds, decide_eq_true_eq, Finset.mem_singleton, forall_eq]
  constructor
  · intro present
    exact GroundBDDCompile_sound program (atom 2) (bddVar 0) direct_derivation world (by simpa using present)
  · intro present
    by_contra absent
    have emptyModel : T_P_LP (residualKBa program world) ∅ ⊆ ∅ := by
      rw [T_P_LP_le_iff]
      constructor
      · rintro _ ⟨i, hi, _⟩
        have index : i = (0 : Fin 1) := Subsingleton.elim _ _
        exact (absent (index ▸ hi)).elim
      · intro clause grounding member body
        simp only [residualKBa, program, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl
        all_goals
          have impossible := body _ (List.mem_cons_self ..)
          exact impossible.elim
    exact leastHerbrandModel_least (residualKBa program world) ∅ emptyModel present

theorem two_rule_derivations_one_event :
    GroundBDDCompile program (atom 2) (apply (· || ·) (bddVar 0) (bddVar 0)) ∧
      (∀ world, (apply (· || ·) (bddVar 0) (bddVar 0)).eval world = holds shared world) ∧
      tseitinCount (lineageFormula shared) (fun _ => 1/2) = 1/2 := by
  refine ⟨.disj _ _ _ direct_derivation indirect_derivation, ?_, shared_event_once.1⟩
  intro world
  simp [holds, shared, supportHolds]

end Controls

end Mettapedia.Logic.BDDCore.DerivationLineage
