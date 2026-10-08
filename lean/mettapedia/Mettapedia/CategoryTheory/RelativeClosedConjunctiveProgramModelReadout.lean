import Mettapedia.CategoryTheory.ConjunctiveProgramTheory
import Mettapedia.CategoryTheory.RelativeClosedProgramReductionExtension

/-!
# Independent conjunctive interpretations with complete program readings

The generated program relation is compared to the original event object by
an earned isomorphism. This lets an independently supplied program-theory
map determine an actual reduction arrow under the generated interpretation.
Both endpoint equations follow from functoriality and the actual base
comparison. No interpretation or reduction compatibility law is a model field.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.ModelReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open ProgramReductionTheory

universe k

section Factor

variable {source middle target : Theory.{k,k}}
variable (inclusion : ProgramReductionTheory.Map source middle) [IsIso inclusion.reduction]

private theorem inverse_source :
    inv inclusion.reduction ≫ inclusion.closed.functor.map source.source =
      middle.source ≫ inclusion.program.inv := by
  apply (cancel_mono inclusion.program.hom).mp
  rw [Category.assoc, ← inclusion.source, IsIso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem inverse_target :
    inv inclusion.reduction ≫ inclusion.closed.functor.map source.target =
      middle.target ≫ inclusion.program.inv := by
  apply (cancel_mono inclusion.program.hom).mp
  rw [Category.assoc, ← inclusion.target, IsIso.inv_hom_id_assoc,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (closed : LambdaTheoryMap middle.closed target.closed)
variable (base : ProgramReductionTheory.Map source target)
variable (baseComparison : inclusion.closed.functor ⋙ closed.functor ≅ base.closed.functor)

def factor : ProgramReductionTheory.Map middle target where
  closed := closed
  program := closed.functor.mapIso inclusion.program.symm ≪≫ baseComparison.app source.program ≪≫ base.program
  reduction := closed.functor.map (inv inclusion.reduction) ≫ baseComparison.hom.app source.Event ≫ base.reduction
  source := by
    change (closed.functor.map (inv inclusion.reduction) ≫
        baseComparison.hom.app source.Event ≫ base.reduction) ≫ target.source =
      closed.functor.map middle.source ≫
        (closed.functor.map inclusion.program.inv ≫ baseComparison.hom.app source.program ≫ base.program.hom)
    calc
      _ = closed.functor.map (inv inclusion.reduction) ≫
          (baseComparison.hom.app source.Event ≫ base.closed.functor.map source.source) ≫ base.program.hom := by
        rw [Category.assoc, Category.assoc, base.source, Category.assoc]
      _ = closed.functor.map (inv inclusion.reduction) ≫
          ((inclusion.closed.functor ⋙ closed.functor).map source.source ≫
            baseComparison.hom.app source.program) ≫ base.program.hom :=
        congrArg (fun arrow => closed.functor.map (inv inclusion.reduction) ≫ arrow ≫ base.program.hom)
          (baseComparison.hom.naturality source.source).symm
      _ = closed.functor.map (inv inclusion.reduction ≫ inclusion.closed.functor.map source.source) ≫
          baseComparison.hom.app source.program ≫ base.program.hom := by
        rw [closed.functor.map_comp, Category.assoc, Category.assoc]
        rfl
      _ = closed.functor.map (middle.source ≫ inclusion.program.inv) ≫
          baseComparison.hom.app source.program ≫ base.program.hom :=
        congrArg (fun arrow => closed.functor.map arrow ≫ baseComparison.hom.app source.program ≫ base.program.hom)
          (inverse_source inclusion)
      _ = _ := by rw [closed.functor.map_comp, Category.assoc]
  target := by
    change (closed.functor.map (inv inclusion.reduction) ≫
        baseComparison.hom.app source.Event ≫ base.reduction) ≫ target.target =
      closed.functor.map middle.target ≫
        (closed.functor.map inclusion.program.inv ≫ baseComparison.hom.app source.program ≫ base.program.hom)
    calc
      _ = closed.functor.map (inv inclusion.reduction) ≫
          (baseComparison.hom.app source.Event ≫ base.closed.functor.map source.target) ≫ base.program.hom := by
        rw [Category.assoc, Category.assoc, base.target, Category.assoc]
      _ = closed.functor.map (inv inclusion.reduction) ≫
          ((inclusion.closed.functor ⋙ closed.functor).map source.target ≫
            baseComparison.hom.app source.program) ≫ base.program.hom :=
        congrArg (fun arrow => closed.functor.map (inv inclusion.reduction) ≫ arrow ≫ base.program.hom)
          (baseComparison.hom.naturality source.target).symm
      _ = closed.functor.map (inv inclusion.reduction ≫ inclusion.closed.functor.map source.target) ≫
          baseComparison.hom.app source.program ≫ base.program.hom := by
        rw [closed.functor.map_comp, Category.assoc, Category.assoc]
        rfl
      _ = closed.functor.map (middle.target ≫ inclusion.program.inv) ≫
          baseComparison.hom.app source.program ≫ base.program.hom :=
        congrArg (fun arrow => closed.functor.map arrow ≫ baseComparison.hom.app source.program ≫ base.program.hom)
          (inverse_target inclusion)
      _ = _ := by rw [closed.functor.map_comp, Category.assoc]

def factor_base : ProgramReductionTheoryIsoClasses.MapIso
    (ProgramReductionTheory.Map.compose inclusion (factor inclusion closed base baseComparison)) base where
  comparison := baseComparison
  program := by
    change baseComparison.hom.app source.program ≫ base.program.hom =
      closed.functor.map inclusion.program.hom ≫
        (closed.functor.map inclusion.program.inv ≫ baseComparison.hom.app source.program ≫ base.program.hom)
    rw [← Category.assoc, ← closed.functor.map_comp, Iso.hom_inv_id,
      closed.functor.map_id, Category.id_comp]

end Factor

def freeObject (source : Theory.{k,k}) : ConjunctiveProgramTheory.{k} where
  programTheory := RelativeClosedProgramReductionExtension.generatedTheory source
  operations := (RelativeClosedConjunctive.HomEquivalence.freeObject source.closed).operations
  laws := (RelativeClosedConjunctive.HomEquivalence.freeObject source.closed).laws

def unitMap (source : Theory.{k,k}) : ProgramReductionTheory.Map source (freeObject source).programTheory :=
  RelativeClosedProgramReductionExtension.generatedInclusion source

instance unit_reduction_isIso (source : Theory.{k,k}) : IsIso (unitMap source).reduction :=
  RelativeClosedProgramReductionExtension.complete_reduction_retained source
    (RelativeClosedConjunctive.HomEquivalence.freeObject source.closed).closed
    (RelativeClosedConjunctive.HomEquivalence.unitMap source.closed)

variable (source : Theory.{k,k}) (target : ConjunctiveProgramTheory.{k})
variable (base : ProgramReductionTheory.Map source target.programTheory)

abbrev independentConjunctive :=
  RelativeClosedConjunctive.HomEquivalence.extension source.closed target.conjunctive base.closed

abbrev independentBaseComparison :=
  RelativeClosedConjunctive.ModelReadout.baseComparison base.closed.functor target.operations target.laws

def extension : ConjunctiveProgramTheory.Map (freeObject source) target where
  conjunctive := independentConjunctive source target base
  program := (factor (unitMap source) (independentConjunctive source target base).underlying base
    (independentBaseComparison source target base)).program
  reduction := (factor (unitMap source) (independentConjunctive source target base).underlying base
    (independentBaseComparison source target base)).reduction
  source := (factor (unitMap source) (independentConjunctive source target base).underlying base
    (independentBaseComparison source target base)).source
  target := (factor (unitMap source) (independentConjunctive source target base).underlying base
    (independentBaseComparison source target base)).target

def restriction (mapping : ConjunctiveProgramTheory.Map (freeObject source) target) :
    ProgramReductionTheory.Map source target.programTheory :=
  ProgramReductionTheory.Map.compose (unitMap source) mapping.underlying

def extension_base : ProgramReductionTheoryIsoClasses.MapIso
    (restriction source target (extension source target base)) base :=
  factor_base (unitMap source) (independentConjunctive source target base).underlying base
    (independentBaseComparison source target base)

theorem complete_base_event_readout :
    (extension_base source target base).comparison.hom.app source.Event ≫ base.reduction =
      (restriction source target (extension source target base)).reduction :=
  (extension_base source target base).reduction_square

end Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.ModelReadout
