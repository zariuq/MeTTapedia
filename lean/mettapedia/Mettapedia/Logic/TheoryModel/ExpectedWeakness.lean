import Mettapedia.Cybernetics.DistinctionCalculus.GradedCongruenceControls
import Mettapedia.Logic.TheoryModel.WeaknessMeasures
import Mettapedia.GSLT.Logic.ObserverRefinement
import Mettapedia.GSLT.Logic.SaturatedRelativeBisimilarity

/-!
# The expectation form of the weakness bridge

A finite universe of structures with a declared sampling measure `P` and an
observer `E` (an equivalence relation on structures) has expected
indistinction `g_P(E) = ⟨P|1_E|P⟩`. This module proves that `g_P(E)` is the
expected mass of the observer's class of a random structure, and relates that
class to what the observer can say about the structure.

* **The class is inside the model class of the observed theory**
  (`saturation_subset_models_observedTheory`), so `g_P(E)` is at most the
  expected mass of the models of the observed theory of a random structure
  (`graphtropy_le_expected_model_mass`).
* **Equality with separation and negation.** If the observer is recovered
  from its observable sentences and the language has negation, the class of a
  structure *is* the model class of its observed theory
  (`models_observedTheory_singleton_eq`), and the bound is an equality.
  Without negation, or with a poor language, it is strict (controls).
* **Bubbles.** For an image-finite labelled system with Hennessy–Milner
  formulas, the bisimulation class of a term is the class of terms satisfying
  every formula it satisfies (`bisimilarClass_eq_models`). Applied to the
  saturated system of an admissible class this describes the bubble's
  equality; `g` is antitone in the observer class.
* **Crisp closure computes equational consequences**: the metric closure of a
  crisp seed identifies exactly the equations entailed by the seed over all
  interpretations (`closure_indistinguishable_iff_consequence`).
* **Peak against expectation.** The quantale weakness `⋁ μ(x) ⊗ μ(y)` used by
  `distinctionWeakness_antitone` is a peak: it preserves unions as joins
  (`weakness_union`) and is constant on every nonempty event when the weights
  are uniform (`weakness_uniform`). The expectation separates the identity, a
  merge and total collapse (`1/3`, `5/9`, `1`), where the peak does not; the
  expectation satisfies the valuation law, the peak the join law.

Rational statements inherit `Classical.choice` from core rational arithmetic;
the set-level statements do not use it, except that the bubble instance
inherits it from Hennessy–Milner adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TheoryModel.ExpectedWeakness

open Set
open Mettapedia.Cybernetics.DistinctionCalculus

universe uStr uSent uX

/-! ## The observer's class and the observed theory -/

section SetLevel

variable {Str : Type uStr} {Sent : Type uSent} {Sat : Str → Sent → Prop}

theorem mem_saturation_singleton {E : Setoid Str} {m x : Str} :
    x ∈ saturation E {m} ↔ E m x :=
  ⟨fun ⟨_, member, related⟩ => (show _ = m from member) ▸ related, fun related => ⟨m, rfl, related⟩⟩

/-- A language is closed under negation. -/
structure HasNegation (Sat : Str → Sent → Prop) where
  neg : Sent → Sent
  sat_neg : ∀ m φ, Sat m (neg φ) ↔ ¬ Sat m φ

/-- **With separation and negation, the observer's class of a structure is
exactly the model class of its observed theory.** Stability of satisfaction
(double-negation elimination for each instance) is what the converse
direction needs. -/
theorem models_observedTheory_singleton_eq {E : Setoid Str} (separates : Separates Sat E)
    (negation : HasNegation Sat) (stable : ∀ m φ, ¬ ¬ Sat m φ → Sat m φ) (m : Str) :
    models Sat (observedTheory Sat E {m}) = saturation E {m} := by
  apply Subset.antisymm _ (saturation_subset_models_observedTheory E {m})
  intro x model
  apply mem_saturation_singleton.mpr
  apply separates
  intro φ invariant
  constructor
  · intro holds
    exact model ⟨fun _ member => (show _ = m from member) ▸ holds, invariant⟩
  · intro holds
    apply stable m φ
    intro refuted
    have negObservable : negation.neg φ ∈ observable Sat E := fun a b related => by
      rw [negation.sat_neg, negation.sat_neg]
      exact not_congr (invariant related)
    have negHolds : Sat x (negation.neg φ) :=
      model ⟨fun _ member => (show _ = m from member) ▸ (negation.sat_neg m φ).mpr refuted,
        negObservable⟩
    exact (negation.sat_neg x φ).mp negHolds holds

end SetLevel

/-! ## Mass of classes and expected indistinction -/

section Mass

variable {Str : Type uStr} [Fintype Str] (P : Distribution Str)

/-- The `P`-mass of a decidable class of structures. -/
def mass (K : Set Str) [DecidablePred (· ∈ K)] : ℚ :=
  ∑ x, if x ∈ K then P.weight x else 0

theorem mass_mono {K K' : Set Str} [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')]
    (included : K ⊆ K') : mass P K ≤ mass P K' :=
  Finset.sum_le_sum fun x _ => by
    by_cases member : x ∈ K
    · rw [if_pos member, if_pos (included member)]
    · rw [if_neg member]
      split_ifs
      · exact P.nonnegative x
      · exact le_rfl

theorem mass_congr {K K' : Set Str} [DecidablePred (· ∈ K)] [DecidablePred (· ∈ K')]
    (same : K = K') : mass P K = mass P K' :=
  le_antisymm (mass_mono P same.le) (mass_mono P same.ge)

variable (E : Setoid Str) [DecidableRel E.r]

instance decidableSaturationSingleton (m : Str) : DecidablePred (· ∈ saturation E {m}) :=
  fun x => decidable_of_iff (E m x) mem_saturation_singleton.symm

/-- **Expected indistinction is the expected mass of a random structure's
class**: `g_P(E) = Σ_m P(m) · P([m]_E)`. -/
theorem graphtropy_eq_expected_class_mass :
    P.graphtropy (Tolerance.ofSetoid E) = ∑ m, P.weight m * mass P (saturation E {m}) := by
  unfold Distribution.graphtropy Distribution.pairAverage mass
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Tolerance.ofSetoid_similarity]
  by_cases related : E m x
  · rw [if_pos related, if_pos (mem_saturation_singleton.mpr related), mul_one]
  · rw [if_neg related, if_neg (fun member => related (mem_saturation_singleton.mp member)),
      mul_zero, mul_zero]

/-- **The expectation form of the weakness bridge, inequality.** Expected
indistinction is at most the expected mass of the models of what the observer
can say about a random structure. -/
theorem graphtropy_le_expected_model_mass {Sent : Type uSent} (Sat : Str → Sent → Prop)
    [∀ m, DecidablePred (· ∈ models Sat (observedTheory Sat E {m}))] :
    P.graphtropy (Tolerance.ofSetoid E) ≤
      ∑ m, P.weight m * mass P (models Sat (observedTheory Sat E {m})) := by
  rw [graphtropy_eq_expected_class_mass]
  exact Finset.sum_le_sum fun m _ => mul_le_mul_of_nonneg_left
    (mass_mono P (saturation_subset_models_observedTheory E {m})) (P.nonnegative m)

/-- **The expectation form of the weakness bridge, equality**, when the
observer separates and the language has negation. -/
theorem graphtropy_eq_expected_model_mass {Sent : Type uSent} (Sat : Str → Sent → Prop)
    [∀ m, DecidablePred (· ∈ models Sat (observedTheory Sat E {m}))]
    (separates : Separates Sat E) (negation : HasNegation Sat)
    (stable : ∀ m φ, ¬ ¬ Sat m φ → Sat m φ) :
    P.graphtropy (Tolerance.ofSetoid E) =
      ∑ m, P.weight m * mass P (models Sat (observedTheory Sat E {m})) := by
  rw [graphtropy_eq_expected_class_mass]
  exact Finset.sum_congr rfl fun m _ => by
    rw [mass_congr P (models_observedTheory_singleton_eq separates negation stable m)]

/-- Coarsening the observer raises expected indistinction; the increment is
the mass of the newly identified pairs (`graphtropy_ofSetoid_sub`). -/
theorem graphtropy_mono {E E' : Setoid Str} [DecidableRel E.r] [DecidableRel E'.r]
    (coarser : E ≤ E') :
    P.graphtropy (Tolerance.ofSetoid E) ≤ P.graphtropy (Tolerance.ofSetoid E') :=
  P.pairAverage_mono ((Tolerance.ofSetoid_extends_iff E E').mpr coarser)

end Mass

/-! ## Bubbles: Hennessy–Milner formulas -/

section Bubbles

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner

variable {S : GSLT} (M : System S)

/-- Satisfaction of Hennessy–Milner formulas, with terms as structures. -/
def hmSat (term : S.Term) (formula : Formula M.Atom M.Label) : Prop :=
  M.sat formula term

/-- Hennessy–Milner formulas are closed under negation. -/
def hmNegation : HasNegation (hmSat M) where
  neg := .neg
  sat_neg _ _ := Iff.rfl

/-- Every formula is observable by bisimilarity. -/
theorem observable_bisimilar_eq_univ : observable (hmSat M) M.behavioralSetoid = univ :=
  eq_univ_of_forall fun _ _ _ related => M.logicallyEquivalent_of_bisimilar related _

/-- Under image-finiteness, bisimilarity is recovered from its observable
formulas. -/
theorem separates_bisimilar (finite : M.ImageFiniteModulo) :
    Separates (hmSat M) M.behavioralSetoid := by
  intro left right indistinct
  exact M.bisimilar_of_logicallyEquivalent finite fun formula =>
    indistinct (by rw [observable_bisimilar_eq_univ]; exact mem_univ formula)

/-- **The bisimulation class of a term is the class of terms satisfying every
formula it satisfies** (image-finite systems). -/
theorem bisimilarClass_eq_models (finite : M.ImageFiniteModulo) (term : S.Term) :
    models (hmSat M) (observedTheory (hmSat M) M.behavioralSetoid {term}) =
      saturation M.behavioralSetoid {term} :=
  models_observedTheory_singleton_eq (separates_bisimilar M finite) (hmNegation M)
    (fun _ _ => Classical.not_not.mp) term

open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence

variable {rules : ContextualRules S}

/-- **A bubble's equality class, read logically**: for an image-finite
saturated system, the `A`-relative class of a term is the class of terms
satisfying every formula of the saturated system that the term satisfies. -/
theorem relEquivClass_eq_models (A : AdmissibleClass rules)
    (observations : ContextualRules.Observations S)
    (finite : (A.saturated observations).ImageFiniteModulo) (term : S.Term) :
    {other | A.RelEquiv observations term other} =
      models (hmSat (A.saturated observations))
        (observedTheory (hmSat (A.saturated observations))
          (A.saturated observations).behavioralSetoid {term}) := by
  rw [bisimilarClass_eq_models _ finite]
  ext other
  exact (mem_saturation_singleton (E := (A.saturated observations).behavioralSetoid) (m := term)
    (x := other)).symm

/-- On a finite fragment, expected indistinction of a bubble's equality is
antitone in the observer class. -/
theorem graphtropy_relEquiv_antitone {X : Type uX} [Fintype X] (P : Distribution X)
    (embed : X → S.Term) (observations : ContextualRules.Observations S)
    {A B : AdmissibleClass rules} (le : A ≤ B)
    [DecidableRel (fun x y => A.RelEquiv observations (embed x) (embed y))]
    [DecidableRel (fun x y => B.RelEquiv observations (embed x) (embed y))] :
    P.pairAverage (fun x y => if B.RelEquiv observations (embed x) (embed y) then 1 else 0) ≤
      P.pairAverage (fun x y => if A.RelEquiv observations (embed x) (embed y) then 1 else 0) :=
  P.pairAverage_mono fun x y => by
    by_cases related : B.RelEquiv observations (embed x) (embed y)
    · rw [if_pos related, if_pos (AdmissibleClass.relEquiv_antitone observations le related)]
    · rw [if_neg related]
      split_ifs <;> norm_num

end Bubbles

/-! ## Crisp closure computes equational consequences -/

section Equational

variable {X : Type uX} [Fintype X] [DecidableEq X] (R : Set (X × X)) [DecidablePred (· ∈ R)]

instance : DecidableRel (relationOf R) := fun x y =>
  inferInstanceAs (Decidable ((x, y) ∈ R))

/-- **The metric closure of a crisp seed computes the equational
consequences of the seed**: it identifies `x` and `y` exactly when every
interpretation satisfying the equations `R` identifies them. -/
theorem closure_indistinguishable_iff_consequence {x y : X} :
    (shortestTolerance (Tolerance.ofRel (reflSymmClosure (relationOf R))
      (reflSymmClosure_refl _) (reflSymmClosure_symm _))).Indistinguishable x y ↔
      (x, y) ∈ theoryOf equates (models equates R) := by
  rw [closure_ofRel_indistinguishable_iff, eqvGen_reflSymmClosure_iff, consequences_equations]
  exact Iff.rfl

end Equational

/-! ## Peak against expectation -/

section Peak

open Mettapedia.Algebra.QuantaleWeakness

variable {U : Type uX} [Fintype U] {Q : Type uStr} [Monoid Q] [CompleteLattice Q]

/-- **The peak form preserves unions as joins.** -/
theorem weakness_union [DecidableEq U] (wf : WeightFunction U Q) (H K : Finset (U × U)) :
    weakness wf (H ∪ K) = weakness wf H ⊔ weakness wf K := by
  unfold weakness
  rw [← sSup_union]
  congr 1
  ext q
  simp only [Finset.mem_union, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨p, member | member, rfl⟩
    · exact Or.inl ⟨p, member, rfl⟩
    · exact Or.inr ⟨p, member, rfl⟩
  · rintro (⟨p, member, rfl⟩ | ⟨p, member, rfl⟩)
    · exact ⟨p, Or.inl member, rfl⟩
    · exact ⟨p, Or.inr member, rfl⟩

/-- **With uniform weights the peak is constant on nonempty events**: it cannot
tell the identity, a merge and total collapse apart. -/
theorem weakness_uniform (wf : WeightFunction U Q) {c : Q} (uniform : ∀ u, wf.μ u = c)
    {H : Finset (U × U)} (nonempty : H.Nonempty) : weakness wf H = c * c := by
  unfold weakness
  have single : {x | ∃ p ∈ H, wf.μ p.1 * wf.μ p.2 = x} = ({c * c} : Set Q) := by
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff, uniform]
    constructor
    · rintro ⟨_, _, rfl⟩
      rfl
    · rintro rfl
      obtain ⟨p, member⟩ := nonempty
      exact ⟨p, member, rfl⟩
  rw [single, sSup_singleton]

open Mettapedia.Cybernetics.DistinctionCalculus.LedgerControls

/-- The equivalence events of the identity, a merge and total collapse on three
points are all nonempty. -/
theorem equivalenceEvents_nonempty :
    (setoidEquivalenceSet identity).Nonempty ∧ (setoidEquivalenceSet mergeAB).Nonempty ∧
      (setoidEquivalenceSet total).Nonempty := by
  refine ⟨⟨(0, 0), ?_⟩, ⟨(0, 0), ?_⟩, ⟨(0, 0), ?_⟩⟩ <;>
    simp only [setoidEquivalenceSet, Finset.mem_filter, Finset.mem_univ, true_and] <;>
    exact Setoid.refl' _ 0

/-- **Peak against expectation** (three uniform points). The peak form is the
same for the identity, a merge and total collapse, while expected
indistinction is `1/3`, `5/9` and `1`. -/
theorem peak_blind_expectation_separates (wf : WeightFunction (Fin 3) Q) {c : Q}
    (uniform : ∀ u, wf.μ u = c) :
    weakness wf (setoidEquivalenceSet identity) = weakness wf (setoidEquivalenceSet mergeAB) ∧
      weakness wf (setoidEquivalenceSet mergeAB) = weakness wf (setoidEquivalenceSet total) ∧
      Examples.uniformThree.graphtropy (Tolerance.ofSetoid identity) = 1 / 3 ∧
      Examples.uniformThree.graphtropy (Tolerance.ofSetoid mergeAB) = 5 / 9 ∧
      Examples.uniformThree.graphtropy (Tolerance.ofSetoid total) = 1 := by
  obtain ⟨identityNonempty, mergeNonempty, totalNonempty⟩ := equivalenceEvents_nonempty
  refine ⟨?_, ?_, uniform_bracket_values⟩
  · rw [weakness_uniform wf uniform identityNonempty, weakness_uniform wf uniform mergeNonempty]
  · rw [weakness_uniform wf uniform mergeNonempty, weakness_uniform wf uniform totalNonempty]

end Peak

/-! ## Controls: strictness without negation or with a poor language -/

namespace Control

open Mettapedia.Logic.TheoryModel.Control

/-- A language with the single sentence "the structure is `true`", and no
negation. -/
def trueSat (m : Bool) (_ : Unit) : Prop :=
  m = true

instance (m : Bool) (φ : Unit) : Decidable (trueSat m φ) :=
  inferInstanceAs (Decidable (m = true))

/-- The identity observer on `Bool`. -/
def identityBool : Setoid Bool := Setoid.ker id

instance : DecidableRel identityBool.r := fun x y => inferInstanceAs (Decidable (x = y))

/-- The single sentence separates the identity observer. -/
theorem trueSat_separates : Separates trueSat identityBool := by
  intro left right indistinct
  have observableUnit : () ∈ observable trueSat identityBool := fun a b related => by
    change a = b at related
    rw [related]
  have same := indistinct observableUnit
  change left = true ↔ right = true at same
  change left = right
  cases left <;> cases right <;> simp_all

/-- Without negation the model class of the observed theory of `false` is
everything, although the observer's class of `false` is `{false}`. -/
theorem models_observedTheory_false :
    true ∈ models trueSat (observedTheory trueSat identityBool {false}) ∧
      true ∉ saturation identityBool {false} := by
  constructor
  · rintro φ ⟨holds, _⟩
    exact absurd (holds (mem_singleton false)) (by simp [trueSat])
  · intro member
    have := mem_saturation_singleton.mp member
    exact Bool.false_ne_true this

theorem identityBool_apply (x y : Bool) : identityBool x y ↔ x = y := Iff.rfl

/-- What the identity observer can say about `m` in the negation-free
language: only "`true`", and only when `m` is `true`. -/
theorem mem_models_trueSat_iff {m x : Bool} :
    x ∈ models trueSat (observedTheory trueSat identityBool {m}) ↔ (m = true → x = true) := by
  constructor
  · intro model atTrue
    have member : () ∈ observedTheory trueSat identityBool {m} :=
      ⟨fun m' member => (show m' = m from member) ▸ atTrue, fun a b related => by
        change a = b at related
        rw [related]⟩
    exact model member
  · intro implication φ member
    exact implication (member.1 (mem_singleton m))

instance (m : Bool) :
    DecidablePred (· ∈ models trueSat (observedTheory trueSat identityBool {m})) :=
  fun _ => decidable_of_iff _ mem_models_trueSat_iff.symm

/-- **Strict without negation**: under the uniform measure the expected
indistinction of the identity observer is `1/2`, but the expected model mass
of its observed theories is `3/4`. -/
theorem strict_without_negation :
    Examples.uniformBool.graphtropy (Tolerance.ofSetoid identityBool) = 1 / 2 ∧
      ∑ m, Examples.uniformBool.weight m *
        mass Examples.uniformBool (models trueSat (observedTheory trueSat identityBool {m})) =
          3 / 4 := by
  constructor
  · simp only [Distribution.graphtropy, Distribution.pairAverage, Examples.uniformBool,
      Tolerance.ofSetoid_similarity, identityBool_apply, Fintype.sum_bool]
    norm_num
  · simp only [mass, Examples.uniformBool, mem_models_trueSat_iff, Fintype.sum_bool]
    norm_num

theorem mem_models_poor (m x : Proof) : x ∈ models poorSat (observedTheory poorSat relevant {m}) :=
  fun _ _ => trivial

instance (m : Proof) : DecidablePred (· ∈ models poorSat (observedTheory poorSat relevant {m})) :=
  fun x => isTrue (mem_models_poor m x)

instance : DecidableRel relevant.r := fun x y => by
  change Decidable (x = y)
  exact inferInstance

/-- **Strict for a poor language**: the relevant observer has expected
indistinction `1/2` under the uniform measure, while every model class of a
poor observed theory is everything. -/
theorem strict_for_poor_language :
    Examples.uniformBool.graphtropy (Tolerance.ofSetoid relevant) = 1 / 2 ∧
      ∑ m, Examples.uniformBool.weight m *
        mass Examples.uniformBool (models poorSat (observedTheory poorSat relevant {m})) = 1 := by
  constructor
  · have rel : ∀ x y : Bool, relevant x y ↔ x = y := fun _ _ => Iff.rfl
    simp only [Distribution.graphtropy, Distribution.pairAverage, Examples.uniformBool,
      Tolerance.ofSetoid_similarity, rel, Fintype.sum_bool]
    norm_num
  · simp only [mass, Examples.uniformBool, Fintype.sum_bool, mem_models_poor, if_true]
    norm_num

/-- Positive control: the full predicate language has negation (complement),
so the bound is an equality for every observer. -/
def predicateNegation {Str : Type uStr} : HasNegation (predicateSat (Str := Str)) where
  neg K := Kᶜ
  sat_neg _ _ := Iff.rfl

theorem predicate_class_eq_models {Str : Type uStr} (E : Setoid Str)
    (stable : ∀ (m : Str) (K : Set Str), ¬ ¬ predicateSat m K → predicateSat m K) (m : Str) :
    models predicateSat (observedTheory predicateSat E {m}) = saturation E {m} :=
  models_observedTheory_singleton_eq (predicate_separates E) predicateNegation stable m

end Control

/-! ## The observer-side twin of the theory-side counterexample -/

/-- **No weakest theory within a region, no greatest adequate policy.** On the
theory side, the region `{a, b}` has no weakest admissible theory in a
language without disjunction; on the observer side, approximate adequacy has
no greatest quotient. Both have two incomparable admissible options of equal
weakness. -/
theorem no_weakest_twins :
    (¬ ∃ T, IsWeakestAdmissible Mettapedia.Logic.TheoryModel.Control.atomSat
        (within Mettapedia.Logic.TheoryModel.Control.region) T) ∧
      (¬ ∃ G : Setoid (Fin 3), GradedCongruenceControls.Decodable GradedCongruenceControls.ramp
        (1 / 4) G ∧ ∀ E, GradedCongruenceControls.Decodable GradedCongruenceControls.ramp
          (1 / 4) E → E ≤ G) :=
  ⟨Mettapedia.Logic.TheoryModel.Control.no_weakest_within_region,
    GradedCongruenceControls.no_greatest_decodable⟩

end Mettapedia.Logic.TheoryModel.ExpectedWeakness
