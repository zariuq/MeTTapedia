import Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgramModelReadout

/-!
# Complete extension and restriction over program reduction theories

An independently supplied program-theory map extends through the generated
conjunctive interpretation. The base and fresh-proposition comparisons earn
the whole natural isomorphism; its program reading follows from actual local
admission. Joint endpoint monicity then retains the complete reduction arrow.

Both hom-set roundtrips identify maps only by compatible natural isomorphisms.
The source and target keep all their actual categorical objects.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.HomEquivalence

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.GSLT.Core
open ProgramReductionTheory
open ConjunctiveProgramTheory
open RelativeClosedSyntax GeneratedCategory

universe k

abbrev freeObject := ModelReadout.freeObject.{k}
abbrev unitMap := ModelReadout.unitMap.{k}
abbrev extension := ModelReadout.extension.{k}
abbrev restriction := ModelReadout.restriction.{k}
abbrev extension_base := ModelReadout.extension_base.{k}

variable (source : Theory.{k,k}) (target : ConjunctiveProgramTheory.{k})
variable (base : ProgramReductionTheory.Map source target.programTheory)
variable (mapping : ConjunctiveProgramTheory.Map (freeObject source) target)
variable (baseComparison : ProgramReductionTheoryIsoClasses.MapIso (restriction source target mapping) base)

private def conjunctiveComparison : ConjunctiveClosedTheory.MapIso mapping.conjunctive
    (extension source target base).conjunctive :=
  RelativeClosedConjunctive.HomEquivalence.completeComparison source.closed target.conjunctive
    base.closed mapping.conjunctive baseComparison.comparison

private theorem complete_program_read :
    (conjunctiveComparison source target base mapping baseComparison).comparison.hom.app
        (freeObject source).programTheory.program =
      baseComparison.comparison.hom.app source.program ≫
        (ModelReadout.independentBaseComparison source target base).inv.app source.program := by
  let : PreservesFiniteLimits mapping.functor := mapping.conjunctive.finite
  let : MonoidalClosedFunctor mapping.functor := mapping.conjunctive.closed
  have admitted := RelativeClosedConjunctive.Universal.comparison_admitted
    base.closed.functor target.operations mapping.conjunctive.declarations baseComparison.comparison target.laws
  have original : (ModelReadout.independentBaseComparison source target base).inv.app source.program =
      eqToHom (RelativeClosedSyntax.Interpretation.functor_base_object
        (RelativeClosedConjunctive.ModelReadout.model base.closed.functor target.operations target.laws).meanings
        (RelativeClosedConjunctive.ModelReadout.model base.closed.functor target.operations target.laws).realization
        source.program).symm := by
    change (eqToHom (RelativeClosedSyntax.Interpretation.functor_base
      (RelativeClosedConjunctive.ModelReadout.model base.closed.functor target.operations target.laws).meanings
      (RelativeClosedConjunctive.ModelReadout.model base.closed.functor target.operations target.laws).realization).symm).app
      source.program = _
    rw [eqToHom_app]
  rw [original]
  exact admitted.base source.program

def completeComparison : ConjunctiveProgramTheory.MapIso mapping (extension source target base) where
  conjunctive := conjunctiveComparison source target base mapping baseComparison
  program := by
    have independent := (extension_base source target base).program
    change (ModelReadout.independentBaseComparison source target base).hom.app source.program ≫ base.program.hom =
      (extension source target base).functor.map (𝟙 _) ≫ (extension source target base).program.hom at independent
    rw [(extension source target base).functor.map_id, Category.id_comp] at independent
    have supplied := baseComparison.program
    change baseComparison.comparison.hom.app source.program ≫ base.program.hom =
      mapping.functor.map (𝟙 _) ≫ mapping.program.hom at supplied
    rw [mapping.functor.map_id, Category.id_comp] at supplied
    change (conjunctiveComparison source target base mapping baseComparison).comparison.hom.app
      (freeObject source).programTheory.program ≫ (extension source target base).program.hom = mapping.program.hom
    rw [complete_program_read, ← independent, Category.assoc,
      ← Category.assoc ((ModelReadout.independentBaseComparison source target base).inv.app source.program)
        ((ModelReadout.independentBaseComparison source target base).hom.app source.program) base.program.hom,
      Iso.inv_hom_id_app, Category.id_comp]
    exact supplied

def mapIsoOfRestriction {first second : ConjunctiveProgramTheory.Map (freeObject source) target}
    (comparison : ProgramReductionTheoryIsoClasses.MapIso
      (restriction source target first) (restriction source target second)) :
    ConjunctiveProgramTheory.MapIso first second :=
  (completeComparison source target (restriction source target second) first comparison).trans
    (completeComparison source target (restriction source target second) second
      (ProgramReductionTheoryIsoClasses.MapIso.refl _)).symm

def restriction_comparison {first second : ConjunctiveProgramTheory.Map (freeObject source) target}
    (comparison : ConjunctiveProgramTheory.MapIso first second) :
    ProgramReductionTheoryIsoClasses.MapIso (restriction source target first) (restriction source target second) :=
  comparison.underlying.precompose (unitMap source)

def extension_comparison {first second : ProgramReductionTheory.Map source target.programTheory}
    (comparison : ProgramReductionTheoryIsoClasses.MapIso first second) :
    ConjunctiveProgramTheory.MapIso (extension source target first) (extension source target second) :=
  mapIsoOfRestriction source target
    ((extension_base source target first).trans
      (comparison.trans (extension_base source target second).symm))

def restrict : (freeObject source ⟶ target) →
    (ProgramReductionTheoryIsoClasses.of source ⟶ ProgramReductionTheoryIsoClasses.of target.programTheory) :=
  Quotient.map (restriction source target)
    (fun first second comparison => by
      obtain ⟨comparison⟩ := (show Nonempty (ConjunctiveProgramTheory.MapIso first second) from comparison)
      exact ⟨restriction_comparison source target comparison⟩)

def extend : (ProgramReductionTheoryIsoClasses.of source ⟶ ProgramReductionTheoryIsoClasses.of target.programTheory) →
    (freeObject source ⟶ target) :=
  Quotient.map (extension source target)
    (fun first second comparison => by
      obtain ⟨comparison⟩ := (show Nonempty (ProgramReductionTheoryIsoClasses.MapIso first second) from comparison)
      exact ⟨extension_comparison source target comparison⟩)

theorem restrict_classOf (mapping : ConjunctiveProgramTheory.Map (freeObject source) target) :
    restrict source target (ConjunctiveProgramTheory.classOf mapping) =
      ProgramReductionTheoryIsoClasses.classOf (restriction source target mapping) := rfl

theorem extend_classOf (base : ProgramReductionTheory.Map source target.programTheory) :
    extend source target (ProgramReductionTheoryIsoClasses.classOf base) =
      ConjunctiveProgramTheory.classOf (extension source target base) := rfl

theorem restrict_extend
    (base : ProgramReductionTheoryIsoClasses.of source ⟶ ProgramReductionTheoryIsoClasses.of target.programTheory) :
    restrict source target (extend source target base) = base := by
  refine Quotient.inductionOn base fun base => ?_
  exact (ProgramReductionTheoryIsoClasses.classOf_equal_iff _ _).mpr ⟨extension_base source target base⟩

theorem restrict_injective : Function.Injective (restrict source target) := by
  intro first second
  refine Quotient.inductionOn₂ first second fun first second same => ?_
  obtain ⟨comparison⟩ := (ProgramReductionTheoryIsoClasses.classOf_equal_iff
    (restriction source target first) (restriction source target second)).mp same
  exact Quotient.sound ⟨mapIsoOfRestriction source target comparison⟩

theorem extend_restrict (mapping : freeObject source ⟶ target) :
    extend source target (restrict source target mapping) = mapping :=
  restrict_injective source target (restrict_extend source target (restrict source target mapping))

def homEquiv : (freeObject source ⟶ target) ≃
    (ProgramReductionTheoryIsoClasses.of source ⟶ ProgramReductionTheoryIsoClasses.of target.programTheory) where
  toFun := restrict source target
  invFun := extend source target
  left_inv := extend_restrict source target
  right_inv := restrict_extend source target

theorem restrict_as_base_composition (mapping : freeObject source ⟶ target) :
    restrict source target mapping =
      ProgramReductionTheoryIsoClasses.classOf (unitMap source) ≫ ConjunctiveProgramTheory.forget.map mapping := by
  refine Quotient.inductionOn mapping fun mapping => ?_
  rfl

theorem restrict_postcompose {later : ConjunctiveProgramTheory.{k}}
    (before : freeObject source ⟶ target) (after : target ⟶ later) :
    restrict source later (before ≫ after) =
      restrict source target before ≫ ConjunctiveProgramTheory.forget.map after := by
  rw [restrict_as_base_composition, restrict_as_base_composition,
    ConjunctiveProgramTheory.forget.map_comp, Category.assoc]

end Mettapedia.CategoryTheory.RelativeClosedConjunctiveProgram.HomEquivalence
