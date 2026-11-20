import Mettapedia.ProbabilityTheory.BayesianInference.Coarsening
import Mathlib.Tactic

/-!
# Compositional finite probabilistic witnesses

Exact message elimination on finite binary factor trees, overlap-aware
observation support, and behavioral equivalence under future likelihoods.
The binary tree has a finite-domain variable at every node; its full configuration
space retains all variables. Messages eliminate only a child's private
variables and retain its separator value. Equality of current marginals is
weaker than agreement after future evidence.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition

open scoped BigOperators
open Mettapedia.InformationTheory Mettapedia.InformationTheory.FiniteRV

/-! ## Finite tree elimination -/

inductive Shape where
  | leaf
  | fork (left right : Shape)
  deriving DecidableEq

def Config (X : Type*) : Shape → Type _
  | .leaf => X
  | .fork left right => X × Config X left × Config X right

instance configFintype {X : Type*} [Fintype X] (shape : Shape) : Fintype (Config X shape) :=
  match shape with
  | .leaf => inferInstanceAs (Fintype X)
  | .fork left right =>
      letI := configFintype (X := X) left
      letI := configFintype (X := X) right
      inferInstanceAs (Fintype (X × Config X left × Config X right))

def root {X : Type*} : {shape : Shape} → Config X shape → X
  | .leaf, x => x
  | .fork _ _, configuration => configuration.1

/-- Unary factors and parent-child factors on a finite binary tree.
Nonnegativity is separate, so the algebraic elimination theorem also applies
to signed real factors. Probability readings require nonnegative factors. -/
inductive Factors (X : Type*) : Shape → Type _ where
  | leaf (potential : X → ℝ) : Factors X .leaf
  | fork {left right : Shape} (potential : X → ℝ)
      (leftEdge rightEdge : X → X → ℝ)
      (leftFactors : Factors X left) (rightFactors : Factors X right) :
      Factors X (.fork left right)

def weight {X : Type*} : {shape : Shape} → Factors X shape → Config X shape → ℝ
  | .leaf, .leaf potential, x => potential x
  | .fork _ _, .fork potential leftEdge rightEdge left right, configuration =>
      potential configuration.1 *
        leftEdge configuration.1 (root configuration.2.1) * weight left configuration.2.1 *
        rightEdge configuration.1 (root configuration.2.2) * weight right configuration.2.2

noncomputable def rootWeight {X : Type*} [Fintype X] :
    {shape : Shape} → Factors X shape → X → ℝ
  | .leaf, .leaf potential, x => potential x
  | .fork _ _, .fork potential leftEdge rightEdge left right, x =>
      potential x * (∑ y, leftEdge x y * rootWeight left y) *
        (∑ y, rightEdge x y * rootWeight right y)

def Factors.Nonnegative {X : Type*} : {shape : Shape} → Factors X shape → Prop
  | .leaf, .leaf potential => ∀ x, 0 ≤ potential x
  | .fork _ _, .fork potential leftEdge rightEdge left right =>
      (∀ x, 0 ≤ potential x) ∧ (∀ x y, 0 ≤ leftEdge x y) ∧
        (∀ x y, 0 ≤ rightEdge x y) ∧ left.Nonnegative ∧ right.Nonnegative

theorem weight_nonneg {X : Type*} {shape : Shape} (factors : Factors X shape)
    (valid : factors.Nonnegative) (configuration : Config X shape) :
    0 ≤ weight factors configuration := by
  induction factors with
  | leaf potential => exact valid configuration
  | fork potential leftEdge rightEdge left right il ir =>
      rcases valid with ⟨hp, hl, hr, hleft, hright⟩
      exact mul_nonneg
        (mul_nonneg (mul_nonneg (mul_nonneg (hp _) (hl _ _)) (il hleft _)) (hr _ _))
        (ir hright _)

theorem rootWeight_nonneg {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (valid : factors.Nonnegative) (x : X) :
    0 ≤ rootWeight factors x := by
  induction factors generalizing x with
  | leaf potential => exact valid x
  | fork potential leftEdge rightEdge left right il ir =>
      rcases valid with ⟨hp, hl, hr, hleft, hright⟩
      exact mul_nonneg
        (mul_nonneg (hp x) (Finset.sum_nonneg fun y _ => mul_nonneg (hl x y) (il hleft y)))
        (Finset.sum_nonneg fun y _ => mul_nonneg (hr x y) (ir hright y))

/-- Sum-product messages preserve every root observable, without enumerating
the child's private configurations at its parent. -/
theorem tree_elimination {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (query : X → ℝ) :
    (∑ configuration : Config X shape, weight factors configuration * query (root configuration)) =
      ∑ x, rootWeight factors x * query x := by
  induction factors generalizing query with
  | leaf potential => rfl
  | fork potential leftEdge rightEdge left right il ir =>
      change (∑ configuration : X × Config X _ × Config X _,
        weight (Factors.fork potential leftEdge rightEdge left right) configuration * query configuration.1) = _
      simp only [Fintype.sum_prod_type, rootWeight]
      apply Finset.sum_congr rfl
      intro x _
      have hl := il (query := fun y => leftEdge x y)
      have hr := ir (query := fun y => rightEdge x y)
      have hl' : (∑ y, leftEdge x y * rootWeight left y) =
          ∑ c, weight left c * leftEdge x (root c) := by
        rw [hl]
        apply Finset.sum_congr rfl
        intro y _
        ring
      have hr' : (∑ y, rightEdge x y * rootWeight right y) =
          ∑ c, weight right c * rightEdge x (root c) := by
        rw [hr]
        apply Finset.sum_congr rfl
        intro y _
        ring
      rw [hl', hr']
      simp only [Finset.mul_sum, Finset.sum_mul]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro lc _
      apply Finset.sum_congr rfl
      intro rc _
      change (potential x * leftEdge x (root lc) * weight left lc *
        rightEdge x (root rc) * weight right rc) * query x = _
      ring

/-- The same messages give the normalizer, not just an unnormalized answer. -/
theorem tree_normalizer {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) :
    (∑ configuration : Config X shape, weight factors configuration) =
      ∑ x, rootWeight factors x := by
  simpa using tree_elimination factors (fun _ => 1)

/-- Message elimination computes the actual root marginal of the full
configuration mass. It does not replace a marginal by an unrelated local model. -/
theorem tree_root_marginal {X : Type*} [Fintype X] [DecidableEq X] {shape : Shape}
    (factors : Factors X shape) : pushforward (weight factors) root = rootWeight factors := by
  funext x
  have h := tree_elimination factors (fun y => if y = x then 1 else 0)
  simpa only [pushforward_eq_sum_ite, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

/-- A nonnegative factor tree with positive total mass gives a normalized
root law. The messages need not themselves be normalized kernels. -/
noncomputable def rootLaw {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (valid : factors.Nonnegative)
    (possible : 0 < ∑ x, rootWeight factors x) : Prob X :=
  ⟨fun x => rootWeight factors x / ∑ y, rootWeight factors y,
    (fun x => div_nonneg (rootWeight_nonneg factors valid x) possible.le), by
      rw [← Finset.sum_div, div_self (ne_of_gt possible)]⟩

noncomputable def readout {X : Type*} [Fintype X] (mass : X → ℝ)
    (likelihood query : X → ℝ) : Option ℝ :=
  let denominator := ∑ x, mass x * likelihood x
  if denominator = 0 then none
  else some ((∑ x, mass x * likelihood x * query x) / denominator)

/-- Root-local future likelihoods and queries may be evaluated on the
separator messages; both numerator and denominator agree. -/
theorem tree_readout {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (likelihood query : X → ℝ) :
    readout (weight factors) (fun c => likelihood (root c)) (fun c => query (root c)) =
      readout (rootWeight factors) likelihood query := by
  unfold readout
  have hn := tree_elimination factors (fun x => likelihood x * query x)
  have hd := tree_elimination factors likelihood
  simp_rw [← mul_assoc] at hn
  rw [hn, hd]

/-! ## Observation identity and query witnesses -/

noncomputable def ledgerLikelihood {Event X : Type*} (events : Finset Event)
    (factor : Event → X → ℝ) (x : X) : ℝ :=
  ∏ event ∈ events, factor event x

/-- A shared observation is counted once in the merged support. The exact
correction is multiplicative and requires no division by a possibly zero
likelihood. Distinct event identifiers do not assert independence. -/
theorem ledger_overlap {Event X : Type*} [DecidableEq Event]
    (left right : Finset Event) (factor : Event → X → ℝ) (x : X) :
    ledgerLikelihood (left ∪ right) factor x * ledgerLikelihood (left ∩ right) factor x =
      ledgerLikelihood left factor x * ledgerLikelihood right factor x := by
  exact Finset.prod_union_inter

@[simp] theorem ledger_replay {Event X : Type*} [DecidableEq Event]
    (events : Finset Event) (factor : Event → X → ℝ) :
    ledgerLikelihood (events ∪ events) factor = ledgerLikelihood events factor := by
  simp

/-- A proof of a query transformation carries its observation dependencies.
The source and target observables are specified independently. -/
structure QueryWitness {Event X : Type*} (source target : X → ℝ) where
  observations : Finset Event
  agrees : ∀ x, source x = target x

def QueryWitness.comp {Event X : Type*} [DecidableEq Event]
    {first middle last : X → ℝ} (left : QueryWitness (Event := Event) first middle)
    (right : QueryWitness (Event := Event) middle last) : QueryWitness (Event := Event) first last where
  observations := left.observations ∪ right.observations
  agrees x := (left.agrees x).trans (right.agrees x)

/-- Composition retains shared dependencies once and preserves the readout
under the shared world model, rather than treating proofs as new samples. -/
theorem witness_readout {Event X : Type*} [Fintype X]
    {source target : X → ℝ} (witness : QueryWitness (Event := Event) source target)
    (mass : X → ℝ) (factor : Event → X → ℝ) :
    readout mass (ledgerLikelihood witness.observations factor) source =
      readout mass (ledgerLikelihood witness.observations factor) target := by
  have same : source = target := funext witness.agrees
  exact congrArg (fun q => readout mass (ledgerLikelihood witness.observations factor) q) same

/-- Nonzero merged support implies nonzero support for each retained part.
This implication uses event-set inclusion, with no probabilistic independence
assumption between the parts. -/
theorem ledger_nonzero_of_subset {Event X : Type*} [DecidableEq Event]
    {small large : Finset Event} (included : small ⊆ large)
    (factor : Event → X → ℝ) (x : X)
    (possible : ledgerLikelihood large factor x ≠ 0) :
    ledgerLikelihood small factor x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro event member
  exact Finset.prod_ne_zero_iff.mp possible event (included member)

/-- A local query transformation may require its recorded observations.
The proof is checked on exactly the worlds allowed by those likelihoods;
the likelihood interpretation is shared by all composed witnesses. -/
structure LocalWitness {Event X : Type*} (factor : Event → X → ℝ)
    (source target : X → ℝ) where
  observations : Finset Event
  agrees : ∀ x, ledgerLikelihood observations factor x ≠ 0 → source x = target x

def LocalWitness.comp {Event X : Type*} [DecidableEq Event]
    {factor : Event → X → ℝ} {first middle last : X → ℝ}
    (left : LocalWitness factor first middle) (right : LocalWitness factor middle last) :
    LocalWitness factor first last where
  observations := left.observations ∪ right.observations
  agrees x possible :=
    (left.agrees x (ledger_nonzero_of_subset Finset.subset_union_left factor x possible)).trans
      (right.agrees x (ledger_nonzero_of_subset Finset.subset_union_right factor x possible))

/-- A locally certified witness preserves Bayesian readout, including the
undefined result if its supporting observations have zero total mass. -/
theorem LocalWitness.readout_preserved {Event X : Type*} [Fintype X]
    {factor : Event → X → ℝ} {source target : X → ℝ}
    (witness : LocalWitness factor source target) (mass : X → ℝ) :
    readout mass (ledgerLikelihood witness.observations factor) source =
      readout mass (ledgerLikelihood witness.observations factor) target := by
  have numerator :
      (∑ x, mass x * ledgerLikelihood witness.observations factor x * source x) =
        ∑ x, mass x * ledgerLikelihood witness.observations factor x * target x := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases possible : ledgerLikelihood witness.observations factor x = 0
    · simp only [possible, mul_zero, zero_mul]
    · rw [witness.agrees x possible]
  unfold readout
  rw [numerator]

/-! ## Error certification when the separator approximation differs -/

theorem finite_query_error {X : Type*} [Fintype X]
    (exactMass approximateMass query : X → ℝ)
    (bounded : ∀ x, |query x| ≤ 1) :
    |(∑ x, exactMass x * query x) - ∑ x, approximateMass x * query x| ≤
      ∑ x, |exactMass x - approximateMass x| := by
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro x _
  rw [← sub_mul, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (bounded x)

/-- Separate error certificates for a query numerator and normalizer yield a
normalized answer bound, with explicit positive support margins. -/
theorem normalized_error {n n' z z' εn εz δ : ℝ}
    (hz : 0 < z) (hz' : 0 < z') (hδ : 0 < δ)
    (margin : δ ≤ z)
    (numeratorBound : |n'| ≤ z')
    (numError : |n - n'| ≤ εn) (massError : |z - z'| ≤ εz) :
    |n / z - n' / z'| ≤ (εn + εz) / δ := by
  have split : n / z - n' / z' = (n - n') / z + (n' / z') * ((z' - z) / z) := by
    field_simp
    ring
  rw [split]
  have hratio : |n' / z'| ≤ 1 := by
    rw [abs_div, abs_of_pos hz']
    exact (div_le_one hz').mpr numeratorBound
  have hnum : |(n - n') / z| ≤ εn / δ := by
    rw [abs_div, abs_of_pos hz]
    exact (div_le_div_of_nonneg_right numError hz.le).trans
      (div_le_div_of_nonneg_left (le_trans (abs_nonneg _) numError) hδ margin)
  have hmass : |(z' - z) / z| ≤ εz / δ := by
    rw [abs_div, abs_of_pos hz, abs_sub_comm]
    exact (div_le_div_of_nonneg_right massError hz.le).trans
      (div_le_div_of_nonneg_left (le_trans (abs_nonneg _) massError) hδ margin)
  calc
    |(n - n') / z + n' / z' * ((z' - z) / z)| ≤
        |(n - n') / z| + |n' / z' * ((z' - z) / z)| := abs_add_le _ _
    _ ≤ εn / δ + εz / δ := by
      apply add_le_add hnum
      rw [abs_mul]
      exact (mul_le_of_le_one_left (abs_nonneg _) hratio).trans hmass
    _ = (εn + εz) / δ := (add_div _ _ _).symm

/-- An approximate separator mass has an explicit error certificate against
the full tree query. The same L1 certificate controls its numerator and
normalizer. No independence property is inferred from closeness alone. -/
theorem tree_approximation_error {X : Type*} [Fintype X] {shape : Shape}
    (factors : Factors X shape) (approximateMass query : X → ℝ)
    (approximate_nonneg : ∀ x, 0 ≤ approximateMass x)
    (query_nonneg : ∀ x, 0 ≤ query x) (query_le_one : ∀ x, query x ≤ 1)
    {δ : ℝ} (positive : 0 < δ)
    (exact_margin : δ ≤ ∑ x, rootWeight factors x)
    (approximate_positive : 0 < ∑ x, approximateMass x) :
    |(∑ c : Config X shape, weight factors c * query (root c)) /
          (∑ c : Config X shape, weight factors c) -
        (∑ x, approximateMass x * query x) / (∑ x, approximateMass x)| ≤
      2 * (∑ x, |rootWeight factors x - approximateMass x|) / δ := by
  rw [tree_elimination, tree_normalizer]
  have hquery : ∀ x, |query x| ≤ 1 := fun x => by
    rw [abs_of_nonneg (query_nonneg x)]
    exact query_le_one x
  have numeratorBound : |∑ x, approximateMass x * query x| ≤ ∑ x, approximateMass x := by
    rw [abs_of_nonneg (Finset.sum_nonneg fun x _ => mul_nonneg (approximate_nonneg x) (query_nonneg x))]
    exact Finset.sum_le_sum fun x _ => mul_le_of_le_one_right (approximate_nonneg x) (query_le_one x)
  have massBound : |(∑ x, rootWeight factors x) - ∑ x, approximateMass x| ≤
      ∑ x, |rootWeight factors x - approximateMass x| := by
    simpa only [mul_one] using finite_query_error (rootWeight factors) approximateMass
      (fun _ => 1) (by intro x; norm_num)
  have h := normalized_error (lt_of_lt_of_le positive exact_margin) approximate_positive
    positive exact_margin numeratorBound
    (finite_query_error (rootWeight factors) approximateMass query hquery)
    massBound
  simpa only [mul_one, two_mul] using h

/-! ## Query equivalence stable under future observations -/

def historyLikelihood {Event X : Type*} (factors : Event → X → ℝ)
    (history : List Event) (x : X) : ℝ := (history.map (fun event => factors event x)).prod

def BehavioralEquivalent {Event Query X : Type*} [Fintype X]
    (updates : Event → X → ℝ) (queries : Query → X → ℝ) (left right : X → ℝ) : Prop :=
  ∀ history query, readout left (historyLikelihood updates history) (queries query) =
    readout right (historyLikelihood updates history) (queries query)

/-- A sufficient local view preserves all specified queries after any finite
history of likelihoods that factor through that view. -/
theorem sufficient_view_readout {X C : Type*} [Fintype X] [Fintype C] [DecidableEq C]
    (mass : X → ℝ) (view : X → C) (likelihood query : C → ℝ) :
    readout mass (likelihood ∘ view) (query ∘ view) =
      readout (pushforward mass view) likelihood query := by
  unfold readout
  have hn := sum_pushforward_mul mass view (fun x => likelihood x * query x)
  have hd := sum_pushforward_mul mass view likelihood
  simp_rw [← mul_assoc] at hn
  simp only [Function.comp_apply]
  rw [← hn, ← hd]

/-- Equality of the retained mass is sufficient for equivalence under all
future updates and queries that use that retained view. -/
theorem behavioral_of_pushforward {Event Query X C : Type*}
    [Fintype X] [Fintype C] [DecidableEq C]
    (updates : Event → C → ℝ) (queries : Query → C → ℝ) (view : X → C)
    (left right : X → ℝ) (same : pushforward left view = pushforward right view) :
    BehavioralEquivalent (fun event => updates event ∘ view) (fun query => queries query ∘ view)
      left right := by
  intro history query
  have historyFactors : historyLikelihood (fun event => updates event ∘ view) history =
      historyLikelihood updates history ∘ view := rfl
  rw [historyFactors, sufficient_view_readout, sufficient_view_readout, same]

end Mettapedia.PLN.WorldModel.ProbabilisticWitnessComposition
