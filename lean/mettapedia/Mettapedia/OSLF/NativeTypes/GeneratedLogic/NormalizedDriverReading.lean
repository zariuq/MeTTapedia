import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning

/-!
# The normalized driver, read at the front door

A normalized profile (`Instances.Normalized.Profile`) runs a generated plan natively: its steps are the plan's primitive
receipts between representatives equal under the profile's equality, which a certified normal form decides, and its
observations are predicates of normal forms. The front door reads a language through its reference structure.

- **What a reading needs** (`Agreement`): a region of object terms, on which the profile's steps are the reference
  structure's steps, which its steps do not leave, and on which its equality is the reference structure's
  identification. The region is the admitted terms when the profile's equality keeps them so; a profile whose equality
  reaches terms its sorting does not admit takes their class.
- **Observations that test for a term** (`Tests`): an observation holding exactly at one admitted term in normal form
  is the formula `is t`, since equality is identification in the reference structure (`test_agrees`).
- **The reading** (`reading`): from an agreement, a faithful reading in the reference structure, covering every
  observation that tests for a term, so each decided answer of the profile is the truth of a closed generated formula.

- **Profiles on a first-order root plan** (`agreement_rootPlan`): a profile with the authored equality, whose plan is
  the root plan of an aligned first-order profile without equations, agrees with the front door, since there the plan
  semantics is the reference relation (`FirstOrderProfile.general_step_iff_reference`). Other profiles prove their
  agreement from their own semantics (`NormalizedAuthoredReading`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.NativeTypes.Generation (Generated)
open Mettapedia.OSLF.NativeTypes.Instances.Normalized (Profile Source)
open LocalReading (pairVariable pairClosing pairClosing_positive pairClosing_negative pairClosing_forward
  isState_of_typed)

variable {generated : Generated} {expected : TypeExpr}

/-- **What the front door must agree on to read a normalized profile**: a region of object terms, on which the
profile's steps are the reference structure's, which its steps do not leave, and on which its equality is the reference
structure's identification. -/
structure Agreement (profile : Profile generated [] expected) (relEnv : RelationEnv) (language : LanguageDef)
    (reading : LanguageReading) (region : Pattern → Prop) : Prop where
  object : ∀ source, region source → IsObject source
  steps : ∀ source, region source → ∀ target,
    ((referenceStructure relEnv language reading).step source .any target ↔ profile.system.Step source target)
  closed : ∀ source target, region source → profile.system.Step source target → region target
  equal : ∀ first second, region first → region second →
    (ObjectEquivalent relEnv language reading first second ↔ profile.nf first = profile.nf second)

/-- **An observation that tests for a term**: it holds exactly at the term, which is admitted and in normal form. -/
structure Tests (profile : Profile generated [] expected) (leaf : profile.Leaf) (term : Pattern) : Prop where
  observe : ∀ pattern, profile.observations[leaf].observe pattern = true ↔ pattern = term
  admitted : Source generated [] expected term
  normal : profile.nf term = term

variable (profile : Profile generated [] expected)

/-- The formula of an observation: `is t` for the term it tests for. -/
def testFormula (terms : profile.Leaf → Option Pattern) (leaf : profile.Leaf) : Formula 0 :=
  match terms leaf with
  | some term => .is term
  | none => .top

theorem testFormula_forward (terms : profile.Leaf → Option Pattern) (leaf : profile.Leaf) :
    (testFormula profile terms leaf).forward = true := by
  unfold testFormula
  split <;> rfl

variable {profile}

/-- **An observation that tests for a term is the formula `is t`** at admitted closed terms. -/
theorem test_agrees {relEnv : RelationEnv} {language : LanguageDef} {reading : LanguageReading}
    {region : Pattern → Prop} (agreement : Agreement profile relEnv language reading region) {leaf : profile.Leaf}
    {term : Pattern} (tests : Tests profile leaf term) (termInside : region term) {source : Pattern}
    (inside : region source) :
    profile.observations[leaf].observe (profile.nf source) = true ↔
      (referenceStructure relEnv language reading).sat Env.closed (.is term) source := by
  rw [tests.observe]
  show profile.nf source = term ↔ IsObject source ∧ ObjectEquivalent relEnv language reading source term
  rw [agreement.equal source term inside termInside, tests.normal]
  exact ⟨fun same => ⟨agreement.object source inside, same⟩, fun holds => holds.2⟩

variable (profile)

/-- **The normalized driver's faithful reading in the reference structure**, from an agreement: on admitted closed
terms its steps are the reference structure's, and each observation that tests for a term is the formula `is t`. -/
def reading (relEnv : RelationEnv) (language : LanguageDef) (equations : LanguageReading) {region : Pattern → Prop}
    (agreement : Agreement profile relEnv language equations region) (terms : profile.Leaf → Option Pattern) :
    Embeddings.Faithful profile.driver relEnv language (fun leaf : profile.Leaf => pairVariable leaf true)
      (fun leaf : profile.Leaf => pairVariable leaf false) equations where
  structure_ := referenceStructure relEnv language equations
  region := region
  steps := agreement.steps
  closed := agreement.closed
  rendering := (BoundedMorphism.identity _).toSplit
  renders := rfl
  covers leaf := ∃ term, terms leaf = some term ∧ Tests profile leaf term ∧ region term
  test := testFormula profile terms
  testAgrees := by
    rintro leaf ⟨term, found, tests, termInside⟩ source admitted
    have key := test_agrees agreement tests termInside admitted
    rw [show testFormula profile terms leaf = .is term by simp [testFormula, found]]
    exact key
  closing := pairClosing (testFormula profile terms)
  closesPositive leaf := pairClosing_positive _ leaf
  closesNegative leaf := pairClosing_negative _ leaf
  closingForward := pairClosing_forward _ (testFormula_forward profile terms)

/-! ## Profiles on a first-order root plan -/

open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission (Plan)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (rootPlan FirstOrderProfile ReadsProvider)

variable {language : LanguageDef} {provider : GeneralPremise.ProviderSnapshot}

/-- **Without plan equations the authored equality is identity.** -/
theorem authored_equal_iff {plan : Plan} (empty : plan.equations = []) {first second : Pattern} :
    Relation.EqvGen (GeneralOccurrenceSemantics.Equation plan [] expected) first second ↔ first = second :=
  ⟨LocalReading.eq_of_eqvGen_of_empty (fun _ _ => LocalReading.not_equation empty),
    fun same => same ▸ Relation.EqvGen.refl _⟩

/-- **A profile with the authored equality on a first-order root plan agrees with the front door**: its steps are the
plan semantics' steps, which on an aligned first-order profile are the reference relation's, and both equalities are
identity. -/
theorem agreement_rootPlan (profile : Profile generated [] expected) (authored : profile.policy = .authored)
    (firstOrder : FirstOrderProfile language provider) (aligned : ReferenceStep.ReferenceProfile language)
    (relEnv : RelationEnv) (reads : ReadsProvider relEnv provider)
    (samePlan : generated.plan = rootPlan language provider) :
    Agreement profile relEnv language .syntax (Source generated [] expected) := by
  have empty : generated.plan.equations = [] := by rw [samePlan]; exact firstOrder.equations
  have system : ∀ source target, profile.system.Step source target ↔
      (GeneralOccurrenceSemantics.gslt generated.plan [] expected).Step source target := by
    intro source target
    refine (profile.step_iff_source source target).trans ?_
    rw [authored]
    exact Iff.rfl
  refine ⟨fun _ typed => (isState_of_typed typed).2, fun source typed target => ?_,
    fun source target _ step => ?_, fun first second _ _ => ?_⟩
  · refine Iff.trans ?_ (system source target).symm
    have typed' : OpenPatternWellSorted (rootPlan language provider).snapshot.language
        (rootPlan language provider).snapshot.free [] expected source := by
      have inside : OpenPatternWellSorted generated.plan.snapshot.language generated.plan.snapshot.free [] expected
          source := typed
      rw [samePlan] at inside
      exact inside
    rw [samePlan]
    exact LocalReading.rootStep_iff_reference firstOrder aligned relEnv reads expected typed'
  · exact LocalReading.step_target_typed empty ((system source target).mp step)
  · rw [objectEquivalent_iff_eq_of_isEquationFree firstOrder.equationFree, ← profile.equality_exact, authored]
    exact (authored_equal_iff empty).symm

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.NormalizedReading
