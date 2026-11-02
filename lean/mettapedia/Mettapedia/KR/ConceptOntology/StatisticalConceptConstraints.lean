import Mettapedia.ProbabilityTheory.ImpreciseProbability.ConditionalConstraintBounds
import Mettapedia.KR.ConceptOntology.CredalFormation
import Mettapedia.KR.ConceptGeometry.Bridges.PLN.InheritanceIntegration

/-!
# Statistical concept constraints and named-individual beliefs

The probability space is explicit. Population statistics sample objects under
a fixed concept interpretation. Beliefs about a named individual sample possible
interpretations. Credal formation instead varies the evidence gate; its existing
lower/upper families remain a third, distinct semantics.

The PLN bridge identifies uniform-population conditional probability with the
extensional inheritance strength. Full inheritance also includes intensional
content and is not silently equated with that probability. No confidence is
inferred from an interval width, and no exception-priority semantics is assumed.

References: Thomas Lukasiewicz, *Expressive probabilistic description logics*
(Artificial Intelligence, 2008); Joseph Y. Halpern, *An analysis of first-order
logics of probability* (Artificial Intelligence, 1990).
-/

set_option autoImplicit false

namespace Mettapedia.KR.ConceptOntology.StatisticalConceptConstraints

open scoped BigOperators ENNReal
open Mettapedia.ProbabilityTheory
open ImpreciseProbability ImpreciseProbability.ProjectiveCredal
open ImpreciseProbability.FiniteConditionalConstraints ImpreciseProbability.ConditionalConstraintBounds
open Mettapedia.KR.ConceptGeometry.AbstractInheritance
open Mettapedia.KR.ConceptGeometry.IntensionalInheritance.Interpretation
open Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence
open FiniteEventMass

variable {Carrier Obj Attr World : Type*}

/-- A population observation fixes the interpretation and samples an object. -/
noncomputable def populationEvent (interpretation : Interpretation Carrier Obj Attr) (concept : Carrier) : Event Obj :=
  fun object => by classical exact decide (object ∈ (interpretation.meaning concept).extent)

/-- An individual observation fixes the object and samples an interpretation. -/
noncomputable def individualEvent (interpretations : World → Interpretation Carrier Obj Attr)
    (individual : Obj) (concept : Carrier) : Event World :=
  fun world => populationEvent (interpretations world) concept individual

noncomputable def uniform [Fintype Obj] [Nonempty Obj] : Distribution Obj where
  weight _ := (Fintype.card Obj : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg _)
  total := by simp [nsmul_eq_mul, ne_of_gt (Fintype.card_pos (α := Obj))]

theorem uniform_predicate_mass [Fintype Obj] [Nonempty Obj] (predicate : Obj → Prop) [DecidablePred predicate] :
    mass (uniform (Obj := Obj)).weight (fun object => decide (predicate object)) =
      (Fintype.card {object // predicate object} : ℝ) / Fintype.card Obj := by
  rw [mass_subtype]
  simp [uniform, div_eq_mul_inv, nsmul_eq_mul]

theorem population_conditioning_positive [Fintype Obj] [Nonempty Obj]
    (interpretation : Interpretation Carrier Obj Attr) (sub : Carrier) (nonempty : 0 < extentCount interpretation sub) :
    0 < mass (uniform (Obj := Obj)).weight (populationEvent interpretation sub) := by
  classical
  unfold populationEvent
  rw [uniform_predicate_mass]
  exact div_pos (by exact_mod_cast nonempty) (by exact_mod_cast Fintype.card_pos (α := Obj))

/-- The extensional scalar is an actual conditional on the uniform population. -/
theorem uniform_extensional_conditional [Fintype Obj] [Nonempty Obj]
    (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (nonempty : 0 < extentCount interpretation sub) :
    conditionalValue (uniform (Obj := Obj)) (populationEvent interpretation super) (populationEvent interpretation sub) =
      finiteInheritanceStrength interpretation sub super := by
  classical
  have intersection : (fun object => populationEvent interpretation super object && populationEvent interpretation sub object) =
      fun object => decide (object ∈ (interpretation.meaning sub).extent ∧ object ∈ (interpretation.meaning super).extent) := by
    funext object
    simp [populationEvent, Bool.and_comm]
  unfold conditionalValue
  rw [intersection, uniform_predicate_mass]
  unfold populationEvent
  rw [uniform_predicate_mass]
  change ((jointExtentCount interpretation sub super : ℝ) / Fintype.card Obj) /
      ((extentCount interpretation sub : ℝ) / Fintype.card Obj) = _
  rw [finiteInheritanceStrength_eq, finiteExtensionalProb, dif_neg (ne_of_gt nonempty)]
  have sizeNonzero : (Fintype.card Obj : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Fintype.card_pos (α := Obj)))
  have extentNonzero : (extentCount interpretation sub : ℝ) ≠ 0 := by exact_mod_cast nonempty.ne'
  field_simp

theorem uniform_extensional_readout [Fintype Obj] [Nonempty Obj]
    (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (nonempty : 0 < extentCount interpretation sub) :
    conditionalReadout (uniform (Obj := Obj)) (populationEvent interpretation super) (populationEvent interpretation sub) =
      some (ENNReal.ofReal (pureExtensionalStrength interpretation sub super)) := by
  rw [conditionalReadout_positive _ _ _ (population_conditioning_positive interpretation sub nonempty),
    uniform_extensional_conditional interpretation sub super nonempty,
    pureExtensionalStrength_eq_finiteInheritanceStrength]

/-- The full inheritance readout agrees only when intensional strength does not lower it. -/
theorem full_strength_agrees_iff [Fintype Obj] (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    fullInheritanceStrength interpretation sub super = finiteInheritanceStrength interpretation sub super ↔
      finiteInheritanceStrength interpretation sub super ≤ pureIntensionalStrength interpretation sub super := by
  rw [fullInheritanceStrength_eq_min_table_intensional, min_eq_left_iff]

theorem empty_extent_readout_absent [Fintype Obj] [Nonempty Obj]
    (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier) (empty : extentCount interpretation sub = 0) :
    conditionalReadout (uniform (Obj := Obj)) (populationEvent interpretation super) (populationEvent interpretation sub) = none := by
  classical
  apply (conditionalReadout_none_iff _ _ _).mpr
  unfold populationEvent
  rw [uniform_predicate_mass]
  change (extentCount interpretation sub : ℝ) / Fintype.card Obj = 0
  rw [empty]
  simp

noncomputable def inheritanceRatio [Fintype Obj] (interpretation : Interpretation Carrier Obj Attr)
    (sub super : Carrier) : ℚ := (jointExtentCount interpretation sub super : ℚ) / extentCount interpretation sub

theorem inheritanceRatio_cast [Fintype Obj] (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier) :
    (inheritanceRatio interpretation sub super : ℝ) = finiteInheritanceStrength interpretation sub super := by
  rw [finiteInheritanceStrength_eq]
  by_cases empty : extentCount interpretation sub = 0
  · simp [inheritanceRatio, finiteExtensionalProb, empty]
  · simp [inheritanceRatio, finiteExtensionalProb, empty]

/-- The scalar extensional edge as the degenerate rational interval. -/
noncomputable def inheritanceConstraint [Fintype Obj] (interpretation : Interpretation Carrier Obj Attr)
    (sub super : Carrier) : Constraint Obj :=
  pointConstraint (populationEvent interpretation super) (populationEvent interpretation sub)
    (inheritanceRatio interpretation sub super)
    (by
      have nonnegative := pureExtensionalStrength_nonneg interpretation sub super
      rw [pureExtensionalStrength_eq_finiteInheritanceStrength, ← inheritanceRatio_cast] at nonnegative
      exact_mod_cast nonnegative)
    (by
      have bounded := pureExtensionalStrength_le_one interpretation sub super
      rw [pureExtensionalStrength_eq_finiteInheritanceStrength, ← inheritanceRatio_cast] at bounded
      exact_mod_cast bounded)

theorem uniform_inheritance_point [Fintype Obj] [Nonempty Obj]
    (interpretation : Interpretation Carrier Obj Attr) (sub super : Carrier)
    (nonempty : 0 < extentCount interpretation sub) :
    (inheritanceConstraint interpretation sub super).Holds (uniform (Obj := Obj)).weight := by
  apply (pointConstraint_iff _ _ _ _ _ _ (population_conditioning_positive interpretation sub nonempty)).mpr
  rw [uniform_extensional_conditional interpretation sub super nonempty, inheritanceRatio_cast]

/-! ## Formation uncertainty remains an uncertainty over gates -/

theorem unconstrained_envelopes_dirac {Ω : Type*} [Fintype Ω] [Nonempty Ω] (gamble : Gamble Ω) :
    lowerEnvelope (credalModels ([] : KnowledgeBase Ω)) gamble =
        lowerEnvelope (Set.range (PrecisePrevision.dirac : Ω → PrecisePrevision Ω)) gamble ∧
      upperEnvelope (credalModels ([] : KnowledgeBase Ω)) gamble =
        upperEnvelope (Set.range (PrecisePrevision.dirac : Ω → PrecisePrevision Ω)) gamble := by
  have allModels : credalModels ([] : KnowledgeBase Ω) = Set.univ := by ext P; simp [credalModels]
  rw [allModels]
  have diracsNonempty : (Set.range (PrecisePrevision.dirac : Ω → PrecisePrevision Ω)).Nonempty :=
    ⟨_, ⟨Classical.arbitrary Ω, rfl⟩⟩
  have allNonempty : (Set.univ : Set (PrecisePrevision Ω)).Nonempty :=
    ⟨PrecisePrevision.dirac (Classical.arbitrary Ω), Set.mem_univ _⟩
  constructor
  · apply le_antisymm
    · apply le_lowerEnvelope_of_forall_le _ diracsNonempty
      intro P _
      exact lowerEnvelope_le_of_mem _ _ (finite_credalRange_bddBelow _ _) (Set.mem_univ P)
    · apply le_lowerEnvelope_of_forall_le _ allNonempty
      intro P _
      apply P.lower_bound
      intro world
      simpa only [PrecisePrevision.dirac] using
        lowerEnvelope_le_of_mem (Set.range (PrecisePrevision.dirac : Ω → PrecisePrevision Ω)) gamble
          (finite_credalRange_bddBelow _ _) ⟨world, rfl⟩
  · apply le_antisymm
    · apply upperEnvelope_le_of_forall_le _ allNonempty
      intro P _
      apply P.upper_bound
      intro world
      simpa only [PrecisePrevision.dirac] using
        le_upperEnvelope_of_mem (Set.range (PrecisePrevision.dirac : Ω → PrecisePrevision Ω)) gamble
          (finite_credalRange_bddAbove _ _) ⟨world, rfl⟩
    · apply upperEnvelope_le_of_forall_le _ diracsNonempty
      intro P _
      exact le_upperEnvelope_of_mem _ _ (finite_credalRange_bddAbove _ _) (Set.mem_univ P)

open Classical in
/-- Sharing the credal machinery does not change the sample space: here it is Gate. -/
theorem gate_formation_envelopes {Gate Q : Type*} [Fintype Gate] [Nonempty Gate]
    [Fintype Obj] [Fintype Attr] [Preorder Q]
    (gates : Gate → EvidenceGate Q) (meaning : Obj → Attr → Q) (concept : DualConcept Obj Attr) :
    lowerEnvelope (credalModels ([] : KnowledgeBase Gate)) (conceptFormationGamble gates meaning concept) =
        (if concept ∈ lowerConceptFamily gates meaning then 1 else 0) ∧
      upperEnvelope (credalModels ([] : KnowledgeBase Gate)) (conceptFormationGamble gates meaning concept) =
        (if concept ∈ upperConceptFamily gates meaning then 1 else 0) := by
  classical
  obtain ⟨lower, upper⟩ := unconstrained_envelopes_dirac (conceptFormationGamble gates meaning concept)
  exact ⟨lower.trans (lowerEnvelope_conceptFormationGamble_eq gates meaning concept),
    upper.trans (upperEnvelope_conceptFormationGamble_eq gates meaning concept)⟩

/-! ## Finite distributions and countermodels -/

namespace Controls

def a : Event (Fin 3) := ![true, false, false]
def b : Event (Fin 3) := ![true, true, false]
def c : Event (Fin 3) := ![false, true, true]
def certain {Ω : Type*} : Event Ω := fun _ => true
def impossible {Ω : Type*} : Event Ω := fun _ => false

def intervalConstraint {Ω : Type*} (event condition : Event Ω)
    (lower upper : ℚ) (nonneg : 0 ≤ lower) (ordered : lower ≤ upper) (bounded : upper ≤ 1) : Constraint Ω :=
  ⟨event, condition, lower, upper, nonneg, ordered, bounded⟩

def intervalBase : KnowledgeBase (Fin 3) :=
  [pointConstraint b certain (1/2) (by norm_num) (by norm_num),
   intervalConstraint a b (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num)]

noncomputable def lowerWitness : Distribution (Fin 3) where
  weight := ![1/8, 3/8, 1/2]
  nonneg w := by fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

noncomputable def upperWitness : Distribution (Fin 3) where
  weight := ![3/8, 1/8, 1/2]
  nonneg w := by fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

theorem lower_witness_model : lowerWitness ∈ models intervalBase := by
  norm_num [models, Satisfies, intervalBase, pointConstraint, intervalConstraint, Constraint.Holds,
    mass, lowerWitness, a, b, certain, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem upper_witness_model : upperWitness ∈ models intervalBase := by
  norm_num [models, Satisfies, intervalBase, pointConstraint, intervalConstraint, Constraint.Holds,
    mass, upperWitness, a, b, certain, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem lower_witness_value : conditionalValue lowerWitness a b = 1/4 := by
  norm_num [conditionalValue, mass, lowerWitness, a, b, Fin.sum_univ_succ]

theorem upper_witness_value : conditionalValue upperWitness a b = 3/4 := by
  norm_num [conditionalValue, mass, upperWitness, a, b, Fin.sum_univ_succ]

def inconsistentBase : KnowledgeBase (Fin 1) :=
  [pointConstraint certain certain 0 (by norm_num) (by norm_num)]

theorem inconsistent_no_model : ¬ Consistent inconsistentBase := by
  rintro ⟨p, member⟩
  have constraint := member _ (List.mem_cons_self ..)
  norm_num [Constraint.Holds, pointConstraint, certain, mass, p.total] at constraint
  have total := p.total
  simp only [Fin.sum_univ_one] at total
  linarith

def unsupportedBase : KnowledgeBase (Fin 3) :=
  [pointConstraint a b 0 (by norm_num) (by norm_num),
   pointConstraint a b 1 (by norm_num) (by norm_num)]

noncomputable def unsupportedWitness : Distribution (Fin 3) where
  weight := ![0, 0, 1]
  nonneg w := by fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

theorem unsupported_is_consistent : Consistent unsupportedBase := by
  refine ⟨unsupportedWitness, ?_⟩
  norm_num [models, Satisfies, unsupportedBase, Constraint.Holds, pointConstraint,
    unsupportedWitness, mass, a, b, Fin.sum_univ_succ, Matrix.cons_val_two]

theorem zero_support_every_interval (constraint : Constraint (Fin 3)) (onB : constraint.condition = b) :
    constraint.Holds unsupportedWitness.weight := by
  apply Constraint.holds_of_zero constraint unsupportedWitness
  rw [onB]
  norm_num [mass, unsupportedWitness, b, Fin.sum_univ_succ]

theorem zero_support_no_value : conditionalReadout unsupportedWitness a b = none := by
  apply (conditionalReadout_none_iff _ _ _).mpr
  norm_num [mass, unsupportedWitness, b, Fin.sum_univ_succ]

noncomputable def nontransitive : Distribution (Fin 3) where
  weight := ![81/91, 9/91, 1/91]
  nonneg w := by fin_cases w <;> norm_num
  total := by norm_num [Fin.sum_univ_succ]

theorem high_conditionals_not_transitive :
    conditionalValue nontransitive a b = 9/10 ∧ conditionalValue nontransitive b c = 9/10 ∧
      conditionalValue nontransitive a c = 0 ∧ 0 < mass nontransitive.weight b ∧ 0 < mass nontransitive.weight c := by
  norm_num [conditionalValue, mass, nontransitive, a, b, c, Fin.sum_univ_succ]

/-- Collapsing the interval to its midpoint excludes admissible distributions. -/
theorem midpoint_loses_models :
    ((1/4 : ℚ) + 3/4) / 2 = 1/2 ∧
      lowerWitness ∈ models intervalBase ∧
      ¬ (pointConstraint a b (1/2) (by norm_num) (by norm_num)).Holds lowerWitness.weight := by
  refine ⟨by norm_num, lower_witness_model, ?_⟩
  norm_num [pointConstraint, Constraint.Holds, mass, lowerWitness, a, b, Fin.sum_univ_succ]

/-- Every interpretation has exactly one of the two population members in the concept. -/
def interpretations (world : Bool) : Interpretation Unit Bool Unit where
  meaning _ := ⟨{object | object = world}, Set.univ⟩

noncomputable def dirac (world : Bool) : Distribution Bool where
  weight other := if other = world then 1 else 0
  nonneg other := by split_ifs <;> norm_num
  total := by simp

theorem identical_population_opposite_individual_beliefs :
    (∀ world, mass (uniform (Obj := Bool)).weight (populationEvent (interpretations world) ()) = 1/2) ∧
      mass (dirac false).weight (individualEvent interpretations false ()) = 1 ∧
      mass (dirac true).weight (individualEvent interpretations false ()) = 0 := by
  constructor
  · intro world
    cases world <;> norm_num [mass, uniform, populationEvent, interpretations, Fintype.sum_bool]
  · norm_num [mass, dirac, individualEvent, populationEvent, interpretations, Fintype.sum_bool]

/-! The executable exact-bound API is checked on the same semantic controls. -/

theorem computed_tight_interval : queryBoundsRat intervalBase a b = some (1/4, 3/4) := by
  apply queryBoundsRat_eq_of_witnesses
  · exact ⟨lowerWitness, lower_witness_model,
      by norm_num [mass, lowerWitness, b, Fin.sum_univ_succ], by simpa using lower_witness_value⟩
  · exact ⟨upperWitness, upper_witness_model,
      by norm_num [mass, upperWitness, b, Fin.sum_univ_succ], by simpa using upper_witness_value⟩
  · rintro value ⟨p, member, positive, rfl⟩
    have constrained := member (intervalConstraint a b (1/4) (3/4) (by norm_num) (by norm_num) (by norm_num))
      (by simp [intervalBase])
    exact (Constraint.holds_iff_conditional _ p positive).mp constrained

theorem computed_inconsistent : isConsistent inconsistentBase = false :=
  Bool.eq_false_iff.mpr (fun held => inconsistent_no_model ((isConsistent_correct inconsistentBase).mp held))

theorem computed_unsupported : queryBoundsRat unsupportedBase a b = none := by
  apply (queryBoundsRat_none_iff unsupportedBase a b).mpr
  rintro ⟨p, member, positive⟩
  have zero := member (pointConstraint a b 0 (by norm_num) (by norm_num)) (by simp [unsupportedBase])
  have one := member (pointConstraint a b 1 (by norm_num) (by norm_num)) (by simp [unsupportedBase])
  simp only [pointConstraint, Constraint.Holds, Rat.cast_zero, Rat.cast_one, zero_mul, one_mul] at zero one
  linarith

theorem computed_empty_worlds : isConsistent ([] : KnowledgeBase (Fin 0)) = false := by decide +kernel

theorem computed_impossible_query_condition :
    queryBoundsRat ([] : KnowledgeBase (Fin 1)) certain impossible = none := by
  apply (queryBoundsRat_none_iff _ _ _).mpr
  rintro ⟨p, _, positive⟩
  simp [mass, impossible] at positive

end Controls

end Mettapedia.KR.ConceptOntology.StatisticalConceptConstraints
