import Mettapedia.Ethics.DeonticValueDivergence
import Mettapedia.Ethics.MoralParadigmEquivalence

/-!
# Normative grades beside deontic and value tags

The ethics ontology judges with two three-valued tag systems: deontic
(obligation, permission, prohibition) and moral value (good, permissible, bad).
It also remarks that degrees of goodness can correlate with degrees of
obligation.  A third system takes that remark literally: four **normative
grades** ordered by strength,

  `prohibited < permissible < supererogatory < obligatory`.

None of the three is privileged here.  Each can be used as it is, and the
translations between them are theorems.

* **Both tag systems are quotients of the grades.**  `NormativeGrade.toDeontic`
  and `NormativeGrade.toValue` are monotone and surjective, and together they
  determine the grade (`projections_injective`).  The ontology's simple
  correspondence of obligation with goodness holds at every grade except
  supererogatory (`simpleCorrespondence_iff`).
* **A graded semantics projects to a deontic and a value semantics**
  (`toDeonticSemantics`, `toValueSemantics`), and when each formula has exactly
  one grade their verdicts are the grade's projections.
* **A deontic and a value semantics read as grades** (`ofDeonticValue`): a
  formula has the grade whose projections are its two verdicts.  When the two
  semantics agree on what is ruled out, a formula has a grade exactly when it is
  neither obligatory-but-not-good nor a prohibited good
  (`ofDeonticValue_exists_iff`).  Supererogation is a grade, not a divergence
  (`ofDeonticValue_supererogatory_iff`).  Reading a graded semantics's projections
  back as grades recovers it (`ofDeonticValue_projections`).
* **Grades from utility.**  With a threshold, utility yields grades: negative is
  prohibited, zero permissible, positive below the threshold supererogatory, and
  from the threshold on obligatory (`ofUtility`).  The value projection is the
  ontology's utility value semantics at every threshold (`ofUtility_toValue`).
  At threshold one the deontic projection is the ontology's aligned deontic
  semantics (`ofUtility_one_toDeontic`), so the current alignment is the graded
  reading with an empty supererogatory band; a higher threshold opens it
  (`supererogation_needs_threshold`).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics

open Mettapedia.Ethics.MoralParadigmEquivalence

universe u

/-! ## The grades -/

inductive NormativeGrade : Type
  | prohibited
  | permissible
  | supererogatory
  | obligatory
  deriving DecidableEq, Repr

namespace NormativeGrade

/-- Normative strength. -/
def strength : NormativeGrade → ℕ
  | .prohibited => 0
  | .permissible => 1
  | .supererogatory => 2
  | .obligatory => 3

theorem strength_injective : Function.Injective strength := by
  intro first second same
  cases first <;> cases second <;> simp_all [strength]

instance : LinearOrder NormativeGrade := LinearOrder.lift' strength strength_injective

theorem le_iff_strength_le {first second : NormativeGrade} :
    first ≤ second ↔ first.strength ≤ second.strength := Iff.rfl

/-- The deontic tag of a grade. -/
def toDeontic : NormativeGrade → DeonticAttribute
  | .prohibited => .Prohibition
  | .permissible => .Permission
  | .supererogatory => .Permission
  | .obligatory => .Obligation

/-- The value tag of a grade. -/
def toValue : NormativeGrade → MoralValueAttribute
  | .prohibited => .MorallyBad
  | .permissible => .MorallyPermissible
  | .supererogatory => .MorallyGood
  | .obligatory => .MorallyGood

/-- Deontic strength: prohibition, then permission, then obligation. -/
def deonticStrength : DeonticAttribute → ℕ
  | .Prohibition => 0
  | .Permission => 1
  | .Obligation => 2

/-- Value strength: bad, then permissible, then good. -/
def valueStrength : MoralValueAttribute → ℕ
  | .MorallyBad => 0
  | .MorallyPermissible => 1
  | .MorallyGood => 2

theorem toDeontic_monotone {first second : NormativeGrade} (le : first ≤ second) :
    deonticStrength first.toDeontic ≤ deonticStrength second.toDeontic := by
  rw [le_iff_strength_le] at le
  cases first <;> cases second <;> simp_all [strength, toDeontic, deonticStrength]

theorem toValue_monotone {first second : NormativeGrade} (le : first ≤ second) :
    valueStrength first.toValue ≤ valueStrength second.toValue := by
  rw [le_iff_strength_le] at le
  cases first <;> cases second <;> simp_all [strength, toValue, valueStrength]

theorem toDeontic_surjective : Function.Surjective toDeontic := by
  intro tag
  cases tag
  exacts [⟨.obligatory, rfl⟩, ⟨.prohibited, rfl⟩, ⟨.permissible, rfl⟩]

theorem toValue_surjective : Function.Surjective toValue := by
  intro tag
  cases tag
  exacts [⟨.obligatory, rfl⟩, ⟨.prohibited, rfl⟩, ⟨.permissible, rfl⟩]

/-- **The two tags together determine the grade.** -/
theorem projections_injective {first second : NormativeGrade}
    (sameDeontic : first.toDeontic = second.toDeontic) (sameValue : first.toValue = second.toValue) :
    first = second := by
  cases first <;> cases second <;> simp_all [toDeontic, toValue]

/-- **The ontology's simple correspondence holds exactly off supererogation.** -/
theorem simpleCorrespondence_iff (grade : NormativeGrade) :
    deonticToMoralValue grade.toDeontic = grade.toValue ↔ grade ≠ .supererogatory := by
  cases grade <;> simp [toDeontic, toValue, deonticToMoralValue]

end NormativeGrade

/-! ## Graded semantics -/

/-- Which formulas have each grade at each world. -/
structure GradedSemantics (World : Type u) : Type (max u 1) where
  graded : NormativeGrade → Formula World → Formula World

namespace GradedSemantics

variable {World : Type u}

/-- Every formula has exactly one grade at every world. -/
def Functional (semantics : GradedSemantics World) : Prop :=
  ∀ formula world, ∃! grade, semantics.graded grade formula world

/-- The deontic semantics of a graded semantics: a formula has a deontic tag when
it has a grade with that tag. -/
def toDeonticSemantics (semantics : GradedSemantics World) : DeonticSemantics World where
  deontic tag formula world := ∃ grade, semantics.graded grade formula world ∧ grade.toDeontic = tag

/-- The value semantics of a graded semantics. -/
def toValueSemantics (semantics : GradedSemantics World) : ValueSemantics World where
  morally tag formula world := ∃ grade, semantics.graded grade formula world ∧ grade.toValue = tag

theorem deonticVerdict_eq {semantics : GradedSemantics World} (functional : semantics.Functional)
    {grade : NormativeGrade} {formula : Formula World} {world : World}
    (holds : semantics.graded grade formula world) :
    semantics.toDeonticSemantics.verdict formula world = grade.toDeontic := by
  have only : ∀ other, semantics.graded other formula world → other = grade := fun other otherHolds =>
    (functional formula world).unique otherHolds holds
  have tagged : ∀ tag, semantics.toDeonticSemantics.deontic tag formula world ↔ grade.toDeontic = tag :=
    fun tag => ⟨fun ⟨other, otherHolds, same⟩ => only other otherHolds ▸ same,
      fun same => ⟨grade, holds, same⟩⟩
  unfold DeonticSemantics.verdict
  simp only [tagged]
  cases grade <;> simp [NormativeGrade.toDeontic]

theorem valueVerdict_eq {semantics : GradedSemantics World} (functional : semantics.Functional)
    {grade : NormativeGrade} {formula : Formula World} {world : World}
    (holds : semantics.graded grade formula world) :
    semantics.toValueSemantics.verdict formula world = grade.toValue := by
  have only : ∀ other, semantics.graded other formula world → other = grade := fun other otherHolds =>
    (functional formula world).unique otherHolds holds
  have tagged : ∀ tag, semantics.toValueSemantics.morally tag formula world ↔ grade.toValue = tag :=
    fun tag => ⟨fun ⟨other, otherHolds, same⟩ => only other otherHolds ▸ same,
      fun same => ⟨grade, holds, same⟩⟩
  unfold ValueSemantics.verdict
  simp only [tagged]
  cases grade <;> simp [NormativeGrade.toValue]

/-- The grade of a formula under a deontic and a value semantics: the grade whose
projections are the two verdicts. -/
noncomputable def ofDeonticValue (deontic : DeonticSemantics World) (value : ValueSemantics World) :
    GradedSemantics World where
  graded grade formula world :=
    deontic.verdict formula world = grade.toDeontic ∧ value.verdict formula world = grade.toValue

theorem ofDeonticValue_unique (deontic : DeonticSemantics World) (value : ValueSemantics World)
    {first second : NormativeGrade} {formula : Formula World} {world : World}
    (firstHolds : (ofDeonticValue deontic value).graded first formula world)
    (secondHolds : (ofDeonticValue deontic value).graded second formula world) : first = second :=
  NormativeGrade.projections_injective (firstHolds.1.symm.trans secondHolds.1)
    (firstHolds.2.symm.trans secondHolds.2)

/-- **A formula has a grade exactly when there is no conflict** between being
required and being good. -/
theorem ofDeonticValue_exists_iff {deontic : DeonticSemantics World} {value : ValueSemantics World}
    (agree : AgreeOnProhibition deontic value) (formula : Formula World) (world : World) :
    (∃ grade, (ofDeonticValue deontic value).graded grade formula world) ↔
      ¬ ObligatoryNotGood deontic value formula world ∧ ¬ ProhibitedGood deontic value formula world := by
  have permission := agree.permission_iff_not_prohibition formula world
  have bad := agree.bad_iff_prohibition formula world
  constructor
  · rintro ⟨grade, sameDeontic, sameValue⟩
    refine ⟨fun ⟨obligatory, permitted, notGood⟩ => ?_, fun ⟨good, prohibited⟩ => ?_⟩
    · rw [(DeonticSemantics.verdict_eq_obligation_iff _ _ _).mpr
          ⟨permission.mp permitted, obligatory⟩] at sameDeontic
      rw [(ValueSemantics.verdict_eq_permissible_iff _ _ _).mpr
          ⟨notGood, fun isBad => permission.mp permitted (bad.mp isBad)⟩] at sameValue
      cases grade <;> simp [NormativeGrade.toDeontic, NormativeGrade.toValue] at sameDeontic sameValue
    · rw [(DeonticSemantics.verdict_eq_prohibition_iff _ _ _).mpr prohibited] at sameDeontic
      rw [(ValueSemantics.verdict_eq_good_iff _ _ _).mpr good] at sameValue
      cases grade <;> simp [NormativeGrade.toDeontic, NormativeGrade.toValue] at sameDeontic sameValue
  · rintro ⟨notObligatoryNotGood, notProhibitedGood⟩
    by_cases prohibited : deontic.deontic .Prohibition formula world
    · have notGood : ¬ value.morally .MorallyGood formula world := fun good =>
        notProhibitedGood ⟨good, prohibited⟩
      exact ⟨.prohibited, (DeonticSemantics.verdict_eq_prohibition_iff _ _ _).mpr prohibited,
        (ValueSemantics.verdict_eq_bad_iff _ _ _).mpr ⟨notGood, bad.mpr prohibited⟩⟩
    · have notBad : ¬ value.morally .MorallyBad formula world := fun isBad => prohibited (bad.mp isBad)
      by_cases obligatory : deontic.deontic .Obligation formula world
      · by_cases good : value.morally .MorallyGood formula world
        · exact ⟨.obligatory, (DeonticSemantics.verdict_eq_obligation_iff _ _ _).mpr ⟨prohibited, obligatory⟩,
            (ValueSemantics.verdict_eq_good_iff _ _ _).mpr good⟩
        · exact absurd ⟨obligatory, permission.mpr prohibited, good⟩ notObligatoryNotGood
      · by_cases good : value.morally .MorallyGood formula world
        · exact ⟨.supererogatory,
            (DeonticSemantics.verdict_eq_permission_iff _ _ _).mpr ⟨prohibited, obligatory⟩,
            (ValueSemantics.verdict_eq_good_iff _ _ _).mpr good⟩
        · exact ⟨.permissible,
            (DeonticSemantics.verdict_eq_permission_iff _ _ _).mpr ⟨prohibited, obligatory⟩,
            (ValueSemantics.verdict_eq_permissible_iff _ _ _).mpr ⟨good, notBad⟩⟩

/-- **Supererogation is a grade.** -/
theorem ofDeonticValue_supererogatory_iff {deontic : DeonticSemantics World}
    {value : ValueSemantics World} (agree : AgreeOnProhibition deontic value) (formula : Formula World)
    (world : World) :
    (ofDeonticValue deontic value).graded .supererogatory formula world ↔
      Supererogatory deontic value formula world := by
  simp only [ofDeonticValue, NormativeGrade.toDeontic, NormativeGrade.toValue,
    DeonticSemantics.verdict_eq_permission_iff, ValueSemantics.verdict_eq_good_iff, Supererogatory,
    agree.permission_iff_not_prohibition]
  tauto

/-- **Reading a graded semantics's projections as grades recovers it.** -/
theorem ofDeonticValue_projections {semantics : GradedSemantics World}
    (functional : semantics.Functional) (grade : NormativeGrade) (formula : Formula World)
    (world : World) :
    (ofDeonticValue semantics.toDeonticSemantics semantics.toValueSemantics).graded grade formula world ↔
      semantics.graded grade formula world := by
  obtain ⟨actual, holds, -⟩ := functional formula world
  simp only [ofDeonticValue, deonticVerdict_eq functional holds, valueVerdict_eq functional holds]
  constructor
  · rintro ⟨sameDeontic, sameValue⟩
    exact NormativeGrade.projections_injective sameDeontic sameValue ▸ holds
  · intro gradeHolds
    obtain rfl := (functional formula world).unique holds gradeHolds
    exact ⟨rfl, rfl⟩

/-! ## Grades from utility -/

/-- The grade of a utility, given the threshold from which it is obligatory. -/
def gradeOfUtility (threshold utility : Int) : NormativeGrade :=
  if utility < 0 then .prohibited
  else if utility = 0 then .permissible
  else if utility < threshold then .supererogatory
  else .obligatory

/-- The graded semantics of a utility assignment. -/
def ofUtility (threshold : Int) (utility : UtilityAssignmentSemantics World) : GradedSemantics World where
  graded grade formula world := gradeOfUtility threshold (utility.utility world formula) = grade

theorem ofUtility_functional (threshold : Int) (utility : UtilityAssignmentSemantics World) :
    (ofUtility threshold utility).Functional :=
  fun _ _ => ⟨_, rfl, fun _ same => same.symm⟩

/-- **The value projection is the utility value semantics, at every threshold.** -/
theorem ofUtility_toValue (threshold : Int) (utility : UtilityAssignmentSemantics World)
    (tag : MoralValueAttribute) (formula : Formula World) (world : World) :
    (ofUtility threshold utility).toValueSemantics.morally tag formula world ↔
      (valueSemanticsOfUtility World utility).morally tag formula world := by
  simp only [toValueSemantics, ofUtility, exists_eq_left', valueSemanticsOfUtility]
  generalize utility.utility world formula = amount
  unfold gradeOfUtility
  cases tag <;> split_ifs <;> simp [NormativeGrade.toValue] <;> omega

/-- **At threshold one the deontic projection is the ontology's aligned deontic
semantics**: the current alignment is the graded reading with no supererogation. -/
theorem ofUtility_one_toDeontic (utility : UtilityAssignmentSemantics World) (tag : DeonticAttribute)
    (formula : Formula World) (world : World) :
    (ofUtility 1 utility).toDeonticSemantics.deontic tag formula world ↔
      (AlignedParadigmSemantics.ofUtility utility).deontic.deontic tag formula world := by
  simp only [toDeonticSemantics, ofUtility, exists_eq_left', AlignedParadigmSemantics.ofUtility,
    valueSemanticsOfUtility]
  generalize utility.utility world formula = amount
  unfold gradeOfUtility
  cases tag <;> split_ifs <;> simp [NormativeGrade.toDeontic, deonticToMoralValue] <;> omega

/-- **Supererogation needs a threshold above one**: at threshold one no utility is
supererogatory; at threshold two, utility one is. -/
theorem supererogation_needs_threshold :
    (∀ amount, gradeOfUtility 1 amount ≠ .supererogatory) ∧ gradeOfUtility 2 1 = .supererogatory := by
  refine ⟨fun amount => ?_, by decide⟩
  unfold gradeOfUtility
  by_cases negative : amount < 0
  · simp [negative]
  · by_cases zero : amount = 0
    · simp [zero]
    · have notBelow : ¬ amount < 1 := by omega
      simp [negative, zero, notBelow]

end GradedSemantics

#print axioms NormativeGrade.projections_injective
#print axioms GradedSemantics.ofDeonticValue_exists_iff
#print axioms GradedSemantics.ofDeonticValue_supererogatory_iff
#print axioms GradedSemantics.ofDeonticValue_projections
#print axioms GradedSemantics.ofUtility_toValue
#print axioms GradedSemantics.ofUtility_one_toDeontic
#print axioms GradedSemantics.supererogation_needs_threshold

end Mettapedia.Ethics
