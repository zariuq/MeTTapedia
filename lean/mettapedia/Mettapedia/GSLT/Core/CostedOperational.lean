import Mettapedia.GSLT.Core.GSLTConstructions
import Mettapedia.GSLT.Core.IndexedOperational

/-!
# Functorial writer enrichment of operational GSLTs

A cost is not determined by a bare rewrite relation.  It is extra structure:
one must select a `GSLT.StepSpend` that grades authentic steps.  This module
packages systems carrying that selection into a category and proves that the
existing `GSLT.spendLift` construction is functorial on cost-preserving maps.

```text
cost-graded GSLTs ---- writer lift ----> operational GSLTs
       |                                      |
       +--------- forget grading ------------+
```

The writer lift accumulates grades in the term.  A natural erasure projects
the accumulator away and preserves every lifted step.  The construction is
therefore not called an endofunctor on bare GSLTs: doing so would incorrectly
claim that operational syntax determines its own resource model.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational

open CategoryTheory
open scoped CategoryTheory
open Mettapedia.GSLT

universe u

/-- An operational GSLT together with a selected monoidal grade for its
authentic steps. -/
structure CostedTheory (Grade : Type u) [Monoid Grade] where
  theory : GSLT.{u}
  spend : theory.StepSpend Grade

/-- A forward operational translation that retains every selected grade.
The target may have additional graded or ungraded behavior; exact coverage is
a separate property. -/
structure CostedTranslation {Grade : Type u} [Monoid Grade]
    (source target : CostedTheory.{u} Grade) where
  base : OperationalTranslation source.theory target.theory
  mapGrade : ∀ {sourceTerm targetTerm grade},
    source.spend.graded sourceTerm targetTerm grade →
      target.spend.graded (base.mapTerm sourceTerm)
        (base.mapTerm targetTerm) grade

namespace CostedTranslation

@[ext]
theorem ext {Grade : Type u} [Monoid Grade]
    {source target : CostedTheory.{u} Grade}
    {first second : CostedTranslation source target}
    (mapTerm : first.base.mapTerm = second.base.mapTerm) : first = second := by
  cases first with
  | mk firstBase firstMapGrade =>
      cases second with
      | mk secondBase secondMapGrade =>
          have baseEqual : firstBase = secondBase :=
            OperationalTranslation.ext mapTerm
          subst secondBase
          have gradeEqual : @firstMapGrade = @secondMapGrade := by
            apply Subsingleton.elim
          subst secondMapGrade
          rfl

/-- Identity retains every grade verbatim. -/
def id {Grade : Type u} [Monoid Grade]
    (system : CostedTheory.{u} Grade) :
    CostedTranslation system system where
  base := OperationalTranslation.id system.theory
  mapGrade := fun graded => graded

/-- Cost-preserving translations compose in execution order. -/
def comp {Grade : Type u} [Monoid Grade]
    {first middle last : CostedTheory.{u} Grade}
    (earlier : CostedTranslation first middle)
    (later : CostedTranslation middle last) :
    CostedTranslation first last where
  base := earlier.base.comp later.base
  mapGrade := fun graded => later.mapGrade (earlier.mapGrade graded)

/-- Lift a cost-preserving map to the writer-enriched systems. -/
def spendLift {Grade : Type u} [Monoid Grade]
    {source target : CostedTheory.{u} Grade}
    (translation : CostedTranslation source target) :
    OperationalTranslation
      (source.theory.spendLift source.spend)
      (target.theory.spendLift target.spend) where
  mapTerm := fun state => (translation.base.mapTerm state.1, state.2)
  mapEquiv := by
    intro left right equivalent
    exact ⟨translation.base.mapEquiv equivalent.1, equivalent.2⟩
  mapStep := by
    rintro sourceState targetState ⟨grade, graded, accumulated⟩
    exact ⟨grade, translation.mapGrade graded, accumulated⟩

/-- Erase the writer accumulator while retaining the underlying step. -/
def erase {Grade : Type u} [Monoid Grade]
    (system : CostedTheory.{u} Grade) :
    OperationalTranslation (system.theory.spendLift system.spend)
      system.theory where
  mapTerm := Prod.fst
  mapEquiv := fun equivalent => equivalent.1
  mapStep := fun step => GSLT.spendLift_erase_step system.spend step

end CostedTranslation

instance {Grade : Type u} [Monoid Grade] :
    CategoryTheory.Category (CostedTheory.{u} Grade) where
  Hom := CostedTranslation
  id := CostedTranslation.id
  comp earlier later := earlier.comp later
  id_comp morphism := by
    apply CostedTranslation.ext
    rfl
  comp_id morphism := by
    apply CostedTranslation.ext
    rfl
  assoc first second third := by
    apply CostedTranslation.ext
    rfl

/-- Forget the chosen grading but retain the underlying operational theory
and translation. -/
def forgetCost {Grade : Type u} [Monoid Grade] :
    CategoryTheory.Functor (CostedTheory.{u} Grade)
      OperationalTheory.{u} where
  obj system := ⟨system.theory⟩
  map translation := translation.base
  map_id system := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- The writer enrichment is functorial for maps that preserve the selected
step grades. -/
def spendLiftFunctor {Grade : Type u} [Monoid Grade] :
    CategoryTheory.Functor (CostedTheory.{u} Grade)
      OperationalTheory.{u} where
  obj system := ⟨system.theory.spendLift system.spend⟩
  map translation := translation.spendLift
  map_id system := by
    apply OperationalTranslation.ext
    rfl
  map_comp earlier later := by
    apply OperationalTranslation.ext
    rfl

/-- Writer erasure is natural when terms and grades live in the same universe:
translating a costed state and then erasing its account is exactly the same
state translation as erasing first. -/
def eraseCost {Grade : Type u} [Monoid Grade] :
    CategoryTheory.NatTrans (spendLiftFunctor (Grade := Grade))
      (forgetCost (Grade := Grade)) := by
  refine
    { app := fun system => CostedTranslation.erase system
      naturality := ?_ }
  intro source target translation
  apply OperationalTranslation.ext
  rfl

/-!
The universe-polymorphic natural erasure is exposed separately because Lean's
ordinary natural-transformation universe unification cannot quantify over the
grade universe in the declaration above without fixing it.  This pointwise
theorem is the reusable law for arbitrary grades.
-/

/-- Pointwise naturality of writer erasure for an arbitrary grade monoid. -/
theorem erase_naturality {Grade : Type u} [Monoid Grade]
    {source target : CostedTheory.{u} Grade}
    (translation : CostedTranslation source target) :
    translation.spendLift.comp (CostedTranslation.erase target) =
      (CostedTranslation.erase source).comp translation.base := by
  apply OperationalTranslation.ext
  rfl

namespace CostedOperationalCanary

def unitSystem : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun source target => source = false ∧ target = true
  rewrites_resp_left := by
    rintro source source' target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target target' step rfl
    exact step

def unitSpend : unitSystem.StepSpend Nat where
  graded := fun source target grade =>
    unitSystem.Step source target ∧ grade = 1
  sound := And.left
  resp_left := by
    rintro source source' target grade rfl graded
    exact ⟨target, graded, rfl⟩
  resp_right := by
    rintro source target target' grade graded rfl
    exact graded

/-- A second lawful grading of the identical bare operational theory. -/
def doubledUnitSpend : unitSystem.StepSpend Nat where
  graded := fun source target grade =>
    unitSystem.Step source target ∧ grade = 2
  sound := And.left
  resp_left := by
    rintro source source' target grade rfl graded
    exact ⟨target, graded, rfl⟩
  resp_right := by
    rintro source target target' grade graded rfl
    exact graded

def costedUnit : CostedTheory Nat := ⟨unitSystem, unitSpend⟩

theorem one_step_erases :
    unitSystem.Step false true := by
  have lifted :
      (unitSystem.spendLift unitSpend).Step (false, 1) (true, 1) :=
    ⟨1, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  exact (CostedTranslation.erase costedUnit).mapStep lifted

/-- Negative control: operational syntax alone does not determine a cost.
The same authentic step receives grade one under one lawful schedule and
grade two under another. -/
theorem bare_theory_does_not_determine_grade :
    unitSpend.graded false true 1 ∧
      doubledUnitSpend.graded false true 2 ∧
      ¬ doubledUnitSpend.graded false true 1 := by
  constructor
  · exact ⟨⟨rfl, rfl⟩, rfl⟩
  · constructor
    · exact ⟨⟨rfl, rfl⟩, rfl⟩
    · rintro ⟨_, impossible⟩
      omega

end CostedOperationalCanary

#print axioms CostedTranslation.spendLift
#print axioms erase_naturality
#print axioms CostedOperationalCanary.one_step_erases
#print axioms CostedOperationalCanary.bare_theory_does_not_determine_grade

end Mettapedia.GSLT.IndexedOperational
