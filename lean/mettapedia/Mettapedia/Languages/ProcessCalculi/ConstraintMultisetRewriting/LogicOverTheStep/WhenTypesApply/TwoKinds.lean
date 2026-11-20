import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.ThatsAll
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.NumberLens
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ParityBoundary
import Mettapedia.Cybernetics.DistinctionCalculus.ExclusionLearning

/-!
# Two ways to be a type, and what destroys each

**Constructor-defined** (`ThatsAll.Generated`): the least class closed under declared rules.

* **Membership has a finite witness, found at a finite unfolding** (`generated_iff_exists_stage`):
  a row is generated exactly when some finite stage of the rules holds it; the rules have finitely
  many premises, so a derivation reaches a finite stage (`exists_common_stage`).
* **The witness survives every growth** (`generated_mono`): more rows and more rules keep every
  derivation. Its closure clause ("no other members") is what growth can break, and it survives
  exactly when the region is owned (`ThatsAll.closedReadingSurvives_iff_owned`).

**Observer-defined** (a class no admitted observer splits).

* **One observation refutes** (`refuted_by_one`): an instance lies outside the least type containing
  another exactly when one reading tells them apart. **Finitely many observations never confirm** a
  type that no finite family decides (`Distinctions.ParityBoundary.evenCount_not_finitelyDetermined`).
* **More observers**: every old type stays a type
  (`Distinctions.ObserverConcepts.concepts_subset_iff`); **the least type containing an instance
  shrinks** (`conceptOf_shrinks`), strictly on the number lens: the fraction `5` is in the least
  type of the integer `5` under the value lens, and not under the storage lens
  (`five_least_type_shrinks`).
* **More instances: the predicate persists, the list of members does not** (`extendType`,
  `extendType_isConcept`, `extendType_restricts`, `extendType_grows`). A type on an old carrier
  extends to a new one as everything indistinguishable from an old member; restricted to the old
  instances it is the old type. On the numbers: the type "the integer `5`" on the integers, extended
  to all stored numbers under the value lens, gains the fraction `5`, which is no integer
  (`five_extension_grows`).

**The learning reading** (`Exclusion.Consistent`). A type asserted from positive and negative examples
is any type between the type the positives generate and the exclusion of the negatives
(`Exclusion.consistent_iff`); a new example narrows the interval (`Exclusion.generated_mono`,
`Exclusion.excluded_anti`).

* **It has collapsed to one type exactly when the examples cover every class** (`collapsed_iff`):
  every instance is indistinguishable from some example.
* So **with finitely many examples it never collapses when there are infinitely many classes**
  (`not_collapsed_of_finite`); on the step's knowledge-observed program "take one `T`" every finite
  separated set of examples leaves more than one type (`countingKnowledge_never_collapses`), and such
  sets exist (`countingKnowledge_separated_example`). Control: on `Bool` with the identity reading one
  positive and one negative example determine the type (`bool_collapses`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.TwoKinds

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Distinctions.ObserverConcepts
open ThatsAll (Generated)

universe u v w u' v'

/-! ## Constructor-defined types -/

section Constructors

variable {Row : Type u} (rules : Set (List Row × Row)) (initial : Set Row)

/-- One application of the rules. -/
def ruleStep (X : Set Row) : Set Row :=
  initial ∪ {r | ∃ premises, (premises, r) ∈ rules ∧ ∀ p ∈ premises, p ∈ X}

/-- The `k`-th stage of the rules. -/
def stage : ℕ → Set Row
  | 0 => ∅
  | k + 1 => ruleStep rules initial (stage k)

theorem ruleStep_mono {X Y : Set Row} (le : X ⊆ Y) : ruleStep rules initial X ⊆ ruleStep rules initial Y := by
  rintro r (inside | ⟨premises, rule, present⟩)
  · exact Or.inl inside
  · exact Or.inr ⟨premises, rule, fun p member => le (present p member)⟩

theorem stage_mono : Monotone (stage rules initial) := by
  refine monotone_nat_of_le_succ fun k => ?_
  induction k with
  | zero => exact empty_subset _
  | succ k ih => exact ruleStep_mono rules initial ih

theorem exists_common_stage : ∀ (l : List Row), (∀ p ∈ l, ∃ k, p ∈ stage rules initial k) →
    ∃ K, ∀ p ∈ l, p ∈ stage rules initial K
  | [], _ => ⟨0, fun _ member => absurd member List.not_mem_nil⟩
  | p :: l, each => by
      obtain ⟨k, hk⟩ := each p (by simp)
      obtain ⟨K, hK⟩ := exists_common_stage l fun q member => each q (by simp [member])
      refine ⟨max k K, fun q member => ?_⟩
      rcases List.mem_cons.mp member with rfl | later
      · exact stage_mono rules initial (le_max_left _ _) hk
      · exact stage_mono rules initial (le_max_right _ _) (hK q later)

/-- **Membership in a constructor-defined type has a finite witness**: a row is generated exactly
when some finite stage of the rules holds it. -/
theorem generated_iff_exists_stage (r : Row) :
    Generated rules initial r ↔ ∃ k, r ∈ stage rules initial k := by
  constructor
  · intro generated
    induction generated with
    | base inside => exact ⟨1, Or.inl inside⟩
    | rule rule _ ih =>
        obtain ⟨K, hK⟩ := exists_common_stage rules initial _ ih
        exact ⟨K + 1, Or.inr ⟨_, rule, hK⟩⟩
  · rintro ⟨k, inside⟩
    induction k generalizing r with
    | zero => exact absurd inside (notMem_empty r)
    | succ k ih =>
        rcases inside with base | ⟨premises, rule, present⟩
        · exact Generated.base base
        · exact Generated.rule rule fun p member => ih p (present p member)

/-- **A finite witness survives every growth**: more rows and more rules keep every derivation. -/
theorem generated_mono {rules' : Set (List Row × Row)} {initial' : Set Row}
    (moreRules : rules ⊆ rules') (moreRows : initial ⊆ initial') {r : Row}
    (generated : Generated rules initial r) : Generated rules' initial' r := by
  induction generated with
  | base inside => exact Generated.base (moreRows inside)
  | rule rule _ ih => exact Generated.rule (moreRules rule) ih

end Constructors

/-! ## Observer-defined types -/

section Observers

variable {V : Type u} {ι : Type v} {R : Type w} {read : ι → V → R}

/-- **One observation refutes**: an instance lies outside the least type containing another exactly
when one reading tells them apart. -/
theorem refuted_by_one (x y : V) : y ∉ conceptOf (Apart read) x ↔ ∃ i, read i x ≠ read i y := by
  rw [conceptOf_eq]
  exact apart_iff_not_indist.symm

/-- **More observers, a smaller least type**: under a finer lens the least type containing an
instance is contained in the one under the coarser lens. -/
theorem conceptOf_shrinks {ι' : Type u'} {R' : Type v'} {read' : ι' → V → R'}
    (finer : ∀ x y, Indist read x y → Indist read' x y) (x : V) :
    conceptOf (Apart read) x ⊆ conceptOf (Apart read') x := by
  rw [conceptOf_eq, conceptOf_eq]
  exact fun y same => finer x y same

end Observers

section NumberLens

open Distinctions.NumberLens

/-- **Control: the least type containing an instance shrinks strictly.** The fraction `5` is in the
least type of the integer `5` under the value lens, and not under the storage lens, which reads
more. -/
theorem five_least_type_shrinks :
    conceptOf (Apart storageLens) five ⊆ conceptOf (Apart valueLens) five ∧
      fiveFrac ∈ conceptOf (Apart valueLens) five ∧ fiveFrac ∉ conceptOf (Apart storageLens) five :=
  ⟨conceptOf_shrinks (fun _ _ same _ => same none) five, fiveFrac_mem_conceptOf,
    (refuted_by_one five fiveFrac).mpr apart_storage_five⟩

end NumberLens

/-! ## More instances: the predicate persists, the list of members does not -/

section OpenWorld

variable {V : Type u} {W : Type v} {ι : Type w} {R : Type u'} (embed : V → W) (readW : ι → W → R)

/-- The readings of the old instances, through their place among the new ones. -/
def restrict : ι → V → R := fun i x => readW i (embed x)

/-- **The extension of a type to a larger carrier**: everything indistinguishable from an old
member. -/
def extendType (X : Set V) : Set W := {w | ∃ x ∈ X, Indist readW (embed x) w}

/-- **The extension is a type.** -/
theorem extendType_isConcept (X : Set V) : IsConcept (Apart readW) (extendType embed readW X) :=
  (isConcept_iff_saturated _).mpr fun _ ⟨x, inX, same⟩ _ next => ⟨x, inX, indist_trans same next⟩

/-- **The predicate persists**: restricted to the old instances, the extension is the old type. -/
theorem extendType_restricts {X : Set V} (concept : IsConcept (Apart (restrict embed readW)) X) :
    embed ⁻¹' extendType embed readW X = X := by
  ext x
  constructor
  · rintro ⟨x', inX, same⟩
    exact (isConcept_iff_saturated X).mp concept x' inX x same
  · intro inX
    exact ⟨x, inX, indist_refl _⟩

/-- **The list does not**: a new instance indistinguishable from a member joins the extension. -/
theorem extendType_grows {X : Set V} {x : V} (member : x ∈ X) {w : W}
    (same : Indist readW (embed x) w) : w ∈ extendType embed readW X :=
  ⟨x, member, same⟩

end OpenWorld

section FiveExtends

open Distinctions.NumberLens

/-- **The type "the integer `5`" on the integers, extended to all stored numbers, gains the
fraction `5`**, which is no integer; restricted to the integers it is still "the integer `5`". -/
theorem five_extension_grows :
    IsConcept (Apart (restrict Stored.int valueLens)) ({5} : Set ℤ) ∧
      Stored.int ⁻¹' extendType Stored.int valueLens {5} = {5} ∧
      fiveFrac ∈ extendType Stored.int valueLens {5} ∧ ∀ n : ℤ, Stored.int n ≠ fiveFrac := by
  have concept : IsConcept (Apart (restrict Stored.int valueLens)) ({5} : Set ℤ) := by
    refine (isConcept_iff_saturated _).mpr fun n inside m same => ?_
    have values : ((n : ℚ)) = ((m : ℚ)) := same ()
    have nm : n = m := by exact_mod_cast values
    rw [Set.mem_singleton_iff] at inside ⊢
    rw [← nm]
    exact inside
  exact ⟨concept, extendType_restricts _ _ concept,
    extendType_grows _ _ (Set.mem_singleton 5) indist_value_five, fun _ same => by cases same⟩

end FiveExtends

/-! ## The learning reading -/

section Learning

variable {V : Type u} {ι : Type v} {R : Type w} {read : ι → V → R}

variable (read) in
/-- The examples **cover** every class: every instance is indistinguishable from an example. -/
def Covers (pos neg : Set V) : Prop :=
  ∀ y, (∃ x ∈ pos, Indist read x y) ∨ ∃ z ∈ neg, Indist read z y

/-- **A type asserted from examples has collapsed to one type exactly when the examples cover every
class.** -/
theorem collapsed_iff {pos neg : Set V} (separated : Separated (Apart read) pos neg) :
    (∃! S, Consistent (Apart read) pos neg S) ↔ Covers read pos neg := by
  have symm : ∀ x y, Apart read x y → Apart read y x := apart_symm
  have lower := consistent_generated symm separated
  have upper := consistent_excluded symm separated
  constructor
  · rintro ⟨S, -, unique⟩
    by_contra uncovered
    simp only [Covers, not_forall, not_or, not_exists, not_and] at uncovered
    obtain ⟨y, notPos, notNeg⟩ := uncovered
    have inUpper : y ∈ excluded (Apart read) neg := mem_excluded.mpr fun z inNeg =>
      apart_iff_not_indist.mpr fun same => notNeg z inNeg (indist_symm same)
    have notLower : y ∉ excluded (Apart read) (excluded (Apart read) pos) := by
      rw [excluded_excluded_eq]
      rintro ⟨x, inPos, same⟩
      exact notPos x inPos same
    have equal := (unique _ lower).trans (unique _ upper).symm
    exact notLower (equal ▸ inUpper)
  · intro covers
    have top : excluded (Apart read) neg ⊆ excluded (Apart read) (excluded (Apart read) pos) := by
      intro y inUpper
      rw [excluded_excluded_eq]
      rcases covers y with found | ⟨z, inNeg, same⟩
      · exact found
      · exact absurd (indist_symm same) (apart_iff_not_indist.mp (mem_excluded.mp inUpper z inNeg))
    refine ⟨_, lower, fun S consistent => ?_⟩
    obtain ⟨-, generated, excludes⟩ := (consistent_iff symm).mp consistent
    exact Subset.antisymm (Subset.trans excludes top) generated

/-- **Finitely many examples never determine the type when there are infinitely many classes.** -/
theorem not_collapsed_of_finite {pos neg : Set V} (finite : (pos ∪ neg).Finite)
    (infinitelyMany : ∀ F : Set V, F.Finite → ∃ y, ∀ x ∈ F, ¬ Indist read x y)
    (separated : Separated (Apart read) pos neg) :
    ¬ ∃! S, Consistent (Apart read) pos neg S := by
  rw [collapsed_iff separated]
  intro covers
  obtain ⟨y, far⟩ := infinitelyMany _ finite
  rcases covers y with ⟨x, inPos, same⟩ | ⟨z, inNeg, same⟩
  · exact far x (Or.inl inPos) same
  · exact far z (Or.inr inNeg) same

end Learning

section LearningOnTheStep

open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Distinctions.StepConcepts Distinctions.ParityBoundary NamesOnTheStep NamesOnTheStep.IssuingControls

/-- On the knowledge-observed step, indistinguishable stores have the same reach. -/
theorem reach_eq_of_indist {C D : Conf} (same : Indist (formulas countingKnowledge) C D) :
    reach C = reach D :=
  reach_eq_of_equivalent ((indist_formulas_iff countingKnowledge C D).mp same)

/-- There are infinitely many classes: past every finite set of stores lies one that can run longer. -/
theorem countingKnowledge_infinitelyMany (F : Set Conf) (finite : F.Finite) :
    ∃ D, ∀ C ∈ F, ¬ Indist (formulas countingKnowledge) C D := by
  refine ⟨copies (finite.toFinset.sup reach + 1), fun C inF same => ?_⟩
  have equal := reach_eq_of_indist same
  rw [reach_copies] at equal
  have bound : reach C ≤ finite.toFinset.sup reach := Finset.le_sup (finite.mem_toFinset.mpr inF)
  omega

/-- **On the step, finitely many examples never determine the type.** -/
theorem countingKnowledge_never_collapses {pos neg : Set Conf} (finite : (pos ∪ neg).Finite)
    (separated : Separated (Apart (formulas countingKnowledge)) pos neg) :
    ¬ ∃! S, Consistent (Apart (formulas countingKnowledge)) pos neg S :=
  not_collapsed_of_finite finite countingKnowledge_infinitelyMany separated

/-- **Such examples exist**: no copy against one copy is finite and separated. -/
theorem countingKnowledge_separated_example :
    ({copies 0} ∪ {copies 1} : Set Conf).Finite ∧
      Separated (Apart (formulas countingKnowledge)) ({copies 0} : Set Conf) ({copies 1} : Set Conf) := by
  refine ⟨(Set.finite_singleton _).union (Set.finite_singleton _), ?_⟩
  intro C inPos
  have isZero : C = copies 0 := inPos
  subst isZero
  refine mem_excluded.mpr fun D inNeg => ?_
  have isOne : D = copies 1 := inNeg
  subst isOne
  refine apart_iff_not_indist.mpr fun same => ?_
  have equal := reach_eq_of_indist same
  rw [reach_copies, reach_copies] at equal
  omega

end LearningOnTheStep

section BoolControl

open Distinctions.ObserverConcepts.Controls

/-- **Control: with finitely many classes, examples do determine the type.** On `Bool` read by the
identity, the positive `true` and the negative `false` leave exactly one type. -/
theorem bool_collapses : ∃! S, Consistent (Apart identity) {true} {false} S := by
  have separated : Separated (Apart identity) {true} {false} := by
    rintro x inPos
    rw [Set.mem_singleton_iff] at inPos
    subst inPos
    refine mem_excluded.mpr fun y inNeg => ?_
    rw [Set.mem_singleton_iff] at inNeg
    subst inNeg
    exact ⟨(), by decide⟩
  refine (collapsed_iff separated).mpr fun y => ?_
  cases y
  · exact Or.inr ⟨false, rfl, fun _ => rfl⟩
  · exact Or.inl ⟨true, rfl, fun _ => rfl⟩

end BoolControl

#print axioms generated_iff_exists_stage
#print axioms generated_mono
#print axioms refuted_by_one
#print axioms conceptOf_shrinks
#print axioms five_least_type_shrinks
#print axioms extendType_isConcept
#print axioms extendType_restricts
#print axioms five_extension_grows
#print axioms collapsed_iff
#print axioms not_collapsed_of_finite
#print axioms countingKnowledge_never_collapses
#print axioms countingKnowledge_separated_example
#print axioms bool_collapses

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.TwoKinds
