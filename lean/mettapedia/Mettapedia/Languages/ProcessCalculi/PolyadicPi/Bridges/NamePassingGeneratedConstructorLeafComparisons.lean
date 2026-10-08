import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorCanonicalRemaining
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalReadout
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationCells

/-!
# Leaf comparisons and whole evidence ports

Named source objects are primitive leaves of the constructor theory. Their
normalization comparisons are literal object transports. This calibrates
the canonical constructor squares with the independently recovered evidence
ports of the actual category compiler.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorLeafComparisons

open _root_.CategoryTheory MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingGeneratedConstructorComparison NamePassingGeneratedConstructorCanonical
open NamePassingGeneratedOperationalReadout

universe k

theorem sort_same (sort : NamePassing.Presentation.Srt) :
    compiler.obj (sourceOperations.{k}.sort sort) = targetOperations.sort sort :=
  (Functor.congr_obj complete_constructor_restriction (ClosedPresentation.sortObject _ sort)).trans
    (target_sort sort)

private theorem normalization_inverse (sort : NamePassing.Presentation.Srt) :
    (FunctorNormalization.comparison constructors.{k}).inv.app (ClosedPresentation.sortObject _ sort) =
      eqToHom (source_sort sort) := by
  change (FunctorNormalization.objectImage constructors (ClosedPresentation.sortObject _ sort)).comparison.inv = _
  have forward := FunctorNormalization.primitive_comparison_eqToHom constructors
    (ClosedPresentation.sortObject NamePassing.Presentation.signature sort)
    (FunctorNormalization.objectImage_named constructors (ULift.up sort))
  have same : (FunctorNormalization.objectImage constructors (ClosedPresentation.sortObject _ sort)).comparison =
      eqToIso (source_sort sort).symm := Iso.ext forward
  exact congrArg Iso.inv same

theorem sortComparison_eq (sort : NamePassing.Presentation.Srt) :
    ClosedFunctorNativeReadout.objectChange sourceNative.{k} compiler last square
      (ClosedPresentation.sortObject NamePassing.Presentation.signature sort)
      (sourceOperations.sort sort) (targetOperations.sort sort)
      (source_sort sort) (target_sort sort) = eqToIso (sort_same sort) := by
  apply Iso.ext
  simp only [ClosedFunctorNativeReadout.objectChange, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.app_hom, square,
    NamePassingGeneratedConstructorNaturality.comparison, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_inv, NatTrans.comp_app]
  dsimp only [eqToIso, Functor.whiskerRight]
  rw [eqToHom_app]
  change compiler.map (eqToHom (source_sort sort).symm) ≫
    (compiler.map ((FunctorNormalization.comparison constructors).inv.app
      (ClosedPresentation.sortObject NamePassing.Presentation.signature sort)) ≫
        eqToHom (Functor.congr_obj complete_constructor_restriction
          (ClosedPresentation.sortObject NamePassing.Presentation.signature sort))) ≫
      eqToHom (target_sort sort) = eqToHom (sort_same sort)
  rw [normalization_inverse]
  simp only [Category.assoc]
  erw [← compiler.map_comp_assoc,
    eqToHom_trans, eqToHom_refl, compiler.map_id, Category.id_comp, eqToHom_trans]

theorem nameComparison_eq : nameComparison.{k} = eqToIso (sort_same .nm) := sortComparison_eq .nm

theorem termComparison_eq : termComparison.{k} = eqToIso complete_program_object := sortComparison_eq .tm

def edgeComparison : compiler.obj NamePassingGeneratedOperationalPresentation.edges.{k} ≅
    NamePassingGeneratedOperational.continuations := eqToIso complete_edge_object

theorem whole_port_square (side : Bool) : edgeComparison.{k}.inv ≫
    compiler.map (if side then NamePassingGeneratedOperationalPresentation.edgeTarget else
      NamePassingGeneratedOperationalPresentation.edgeSource) ≫ termComparison.hom =
        NamePassingGeneratedOperational.functionEndpoint side := by
  rw [termComparison_eq]
  have whole := (conj_eqToHom_iff_heq _ _ complete_edge_object complete_program_object).mpr
    (complete_endpoint_heq side)
  rw [whole]
  simp only [edgeComparison, eqToIso, eqToHom_refl,
    Category.id_comp, Category.comp_id]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedConstructorLeafComparisons
