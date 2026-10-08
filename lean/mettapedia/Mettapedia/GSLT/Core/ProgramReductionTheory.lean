import Mettapedia.GSLT.Core.LambdaTheoryBicategory
import Mathlib.CategoryTheory.Subobject.Limits

/-!
# Closed theories with an actual program reduction relation

A program theory has finite limits, a chosen cartesian closed structure,
a designated program object and a monomorphism into its product with itself.
Maps preserve the closed categorical structure and the complete source and
target of reduction. The program comparison may be a nonidentity isomorphism.

An authored occurrence of a rule is separate data: the monic relation records
the endpoints, and does not distinguish two occurrences with equal endpoints.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Core.ProgramReductionTheory

open _root_.CategoryTheory _root_.CategoryTheory.Limits

universe u v

-- This bundle, like the underlying LambdaTheory, keeps its two carrier levels explicit.
set_option linter.checkUnivs false in
structure Theory where
  closed : LambdaTheory.{u, v}
  program : closed.Obj
  reduction : Subobject (program ⨯ program)

namespace Theory

abbrev Event (theory : Theory.{u,v}) : theory.closed.Obj := theory.reduction

def source (theory : Theory.{u,v}) : theory.Event ⟶ theory.program :=
  theory.reduction.arrow ≫ prod.fst

def target (theory : Theory.{u,v}) : theory.Event ⟶ theory.program :=
  theory.reduction.arrow ≫ prod.snd

theorem endpoint_joint_cancel (theory : Theory.{u,v})
    {context : theory.closed.Obj} {first second : context ⟶ theory.Event}
    (sources : first ≫ theory.source = second ≫ theory.source)
    (targets : first ≫ theory.target = second ≫ theory.target) : first = second := by
  apply (cancel_mono theory.reduction.arrow).mp
  apply prod.hom_ext
  · simpa only [source, Category.assoc] using sources
  · simpa only [target, Category.assoc] using targets

end Theory

/-- A closed finite-limit map with actual program and reduction readouts. -/
structure Map (first second : Theory.{u,v}) where
  closed : LambdaTheoryMap first.closed second.closed
  program : closed.functor.obj first.program ≅ second.program
  reduction : closed.functor.obj first.Event ⟶ second.Event
  source : reduction ≫ second.source = closed.functor.map first.source ≫ program.hom
  target : reduction ≫ second.target = closed.functor.map first.target ≫ program.hom

namespace Map

variable {first second third fourth : Theory.{u,v}}

/-- The endpoint equations determine the entire reduction map. -/
theorem reduction_unique (mapping : Map first second)
    (candidate : mapping.closed.functor.obj first.Event ⟶ second.Event)
    (sources : candidate ≫ second.source =
      mapping.closed.functor.map first.source ≫ mapping.program.hom)
    (targets : candidate ≫ second.target =
      mapping.closed.functor.map first.target ≫ mapping.program.hom) :
    candidate = mapping.reduction :=
  second.endpoint_joint_cancel (sources.trans mapping.source.symm)
    (targets.trans mapping.target.symm)

def identity (theory : Theory.{u,v}) : Map theory theory where
  closed := LambdaTheoryMap.id theory.closed
  program := Iso.refl theory.program
  reduction := 𝟙 theory.Event
  source := (Category.id_comp _).trans (Category.comp_id _).symm
  target := (Category.id_comp _).trans (Category.comp_id _).symm

def compose (before : Map first second) (after : Map second third) : Map first third where
  closed := LambdaTheoryMap.comp after.closed before.closed
  program := after.closed.functor.mapIso before.program ≪≫ after.program
  reduction := after.closed.functor.map before.reduction ≫ after.reduction
  source := by
    change (after.closed.functor.map before.reduction ≫ after.reduction) ≫ third.source =
      after.closed.functor.map (before.closed.functor.map first.source) ≫
        (after.closed.functor.map before.program.hom ≫ after.program.hom)
    rw [Category.assoc, after.source, ← Category.assoc, ← Functor.map_comp,
      before.source, Functor.map_comp, Category.assoc]
  target := by
    change (after.closed.functor.map before.reduction ≫ after.reduction) ≫ third.target =
      after.closed.functor.map (before.closed.functor.map first.target) ≫
        (after.closed.functor.map before.program.hom ≫ after.program.hom)
    rw [Category.assoc, after.target, ← Category.assoc, ← Functor.map_comp,
      before.target, Functor.map_comp, Category.assoc]

@[simp] theorem compose_functor (before : Map first second) (after : Map second third) :
    (compose before after).closed.functor = before.closed.functor ⋙ after.closed.functor := rfl

@[simp] theorem compose_program (before : Map first second) (after : Map second third) :
    (compose before after).program.hom =
      after.closed.functor.map before.program.hom ≫ after.program.hom := rfl

@[simp] theorem compose_reduction (before : Map first second) (after : Map second third) :
    (compose before after).reduction =
      after.closed.functor.map before.reduction ≫ after.reduction := rfl

@[ext] theorem ext {before after : Map first second}
    (closed : before.closed = after.closed)
    (program : HEq before.program.hom after.program.hom) : before = after := by
  cases before with
  | mk firstClosed firstProgram firstReduction firstSource firstTarget =>
    cases after with
    | mk secondClosed secondProgram secondReduction secondSource secondTarget =>
      cases closed
      have equalProgram : firstProgram = secondProgram := Iso.ext (eq_of_heq program)
      cases equalProgram
      have equalReduction : firstReduction = secondReduction :=
        second.endpoint_joint_cancel (firstSource.trans secondSource.symm)
          (firstTarget.trans secondTarget.symm)
      cases equalReduction
      rfl

@[simp] theorem identity_compose (mapping : Map first second) :
    compose (identity first) mapping = mapping := by
  apply ext
  · apply LambdaTheoryMap.ext
    exact Functor.id_comp mapping.closed.functor
  · change HEq (mapping.closed.functor.map (𝟙 first.program) ≫ mapping.program.hom)
      mapping.program.hom
    exact heq_of_eq (by rw [_root_.CategoryTheory.Functor.map_id, Category.id_comp])

@[simp] theorem compose_identity (mapping : Map first second) :
    compose mapping (identity second) = mapping := by
  apply ext
  · apply LambdaTheoryMap.ext
    exact Functor.comp_id mapping.closed.functor
  · exact heq_of_eq (Category.comp_id mapping.program.hom)

theorem compose_assoc (before : Map first second) (middle : Map second third)
    (after : Map third fourth) :
    compose (compose before middle) after = compose before (compose middle after) := by
  apply ext
  · apply LambdaTheoryMap.ext
    exact Functor.assoc before.closed.functor middle.closed.functor after.closed.functor
  · exact heq_of_eq (by
      change after.closed.functor.map
        (middle.closed.functor.map before.program.hom ≫ middle.program.hom) ≫
          after.program.hom =
        after.closed.functor.map (middle.closed.functor.map before.program.hom) ≫
          (after.closed.functor.map middle.program.hom ≫ after.program.hom)
      rw [Functor.map_comp, Category.assoc])

end Map

instance : Category (Theory.{u,v}) where
  Hom := Map
  id := Map.identity
  comp := Map.compose
  id_comp := Map.identity_compose
  comp_id := Map.compose_identity
  assoc := Map.compose_assoc

/-- Forgetting designated programs and reductions retains the actual closed map. -/
def forget : Theory.{u,v} ⥤ LambdaTheory.{u,v} where
  obj theory := theory.closed
  map mapping := mapping.closed
  map_id _ := rfl
  map_comp _ _ := rfl

end Mettapedia.GSLT.Core.ProgramReductionTheory
