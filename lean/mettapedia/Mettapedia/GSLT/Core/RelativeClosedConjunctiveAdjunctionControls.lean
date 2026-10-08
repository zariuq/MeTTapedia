import Mettapedia.CategoryTheory.RelativeClosedConjunctiveMonad
import Mettapedia.CategoryTheory.PullbackCast
import Mettapedia.GSLT.Core.RelativeClosedConjunctiveCellExtensionBoundary

/-!
# A genuinely enlarging conjunctive adjunction and its complete fold

The fresh proposition object is not isomorphic to any old Boolean-order
object: an independently supplied closed interpretation sends old objects
to empty or subsingleton fibres and the fresh object to both Boolean values.
The actual free action on the constant-top base map is nonidentity.

The actual monad multiplication folds the second proposition, truth and
conjunction into the first declarations. Its composite semantic readout
retains both supplied Boolean inputs, rather than projecting an argument or
replacing the operation with a constant. Raw theory objects remain intact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveAdjunctionControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedConjunctive
open HomEquivalence FreeForgetful

abbrev source := LambdaTheoryStructuredControls.boolTheory
abbrev sourceClass := ClosedTheoryIsoClasses.of source
abbrev generated := freeObject source
abbrev firstDiagram := RelativeClosedConjunctiveCellExtensionBoundary.firstDiagram
abbrev firstModel := RelativeClosedConjunctiveCellExtensionBoundary.firstModel
abbrev firstBase := RelativeClosedWeakBaseControls.truthFunctor
abbrev fresh := generated.operations.proposition

theorem fresh_read : firstDiagram.obj fresh = ULift.{0} Bool :=
  RelativeClosedConjunctiveCellExtensionBoundary.first_proposition_read

theorem old_read (object : Bool) :
    firstDiagram.obj ((unitMap source).functor.obj object) = firstBase.obj object :=
  RelativeClosedSyntax.Interpretation.functor_base_object
    firstModel.meanings firstModel.realization object

theorem fresh_is_not_isomorphic_to_any_old_object (object : Bool) :
    ¬ Nonempty (fresh ≅ (unitMap source).functor.obj object) := by
  rintro ⟨comparison⟩
  let interpreted : ULift.{0} Bool ≅ firstBase.obj object :=
    eqToIso fresh_read.symm ≪≫ firstDiagram.mapIso comparison ≪≫ eqToIso (old_read object)
  cases object
  · exact RelativeClosedWeakBaseControls.false_fibre_empty.false (interpreted.hom (ULift.up false))
  · let : Subsingleton (firstBase.obj true) := by
      change Subsingleton (ULift.{0} (true ⟶ true))
      infer_instance
    have injective : Function.Injective interpreted.hom :=
      ((isIso_iff_bijective interpreted.hom).mp (by infer_instance)).1
    have collapsed : interpreted.hom (ULift.up false) = interpreted.hom (ULift.up true) :=
      Subsingleton.elim _ _
    exact Bool.false_ne_true (congrArg ULift.down (injective collapsed))

theorem actual_unit_is_not_essentially_surjective :
    ¬ (unitMap source).functor.EssSurj := by
  intro covers
  let := covers
  obtain ⟨object, ⟨comparison⟩⟩ := Functor.EssSurj.mem_essImage (unitMap source).functor fresh
  exact fresh_is_not_isomorphic_to_any_old_object object ⟨comparison.symm⟩

theorem no_faithful_return_to_the_old_theory (mapping : generated.closed.Obj ⥤ Bool) :
    ¬ mapping.Faithful := by
  intro faithful
  let := faithful
  apply RelativeClosedConjunctiveControls.native_identity_predicate_is_proper
  exact mapping.map_injective (Subsingleton.elim _ _)

theorem monad_object_is_not_isomorphic_to_the_old_theory :
    ¬ Nonempty (Construction.monad.obj sourceClass ≅ sourceClass) := by
  change ¬ Nonempty (ClosedTheoryIsoClasses.of generated.closed ≅ sourceClass)
  rintro ⟨comparison⟩
  obtain ⟨before, beforeRead⟩ := Quotient.exists_rep comparison.hom
  obtain ⟨after, afterRead⟩ := Quotient.exists_rep comparison.inv
  have complete :
      ClosedTheoryIsoClasses.classOf (LambdaTheoryMap.comp after before) =
        ClosedTheoryIsoClasses.classOf (LambdaTheoryMap.id generated.closed) := by
    change Quotient.mk _ before ≫ Quotient.mk _ after = 𝟙 (ClosedTheoryIsoClasses.of generated.closed)
    rw [beforeRead, afterRead]
    exact comparison.hom_inv_id
  obtain ⟨whole⟩ := (ClosedTheoryIsoClasses.classOf_equal_iff
    (LambdaTheoryMap.comp after before) (LambdaTheoryMap.id generated.closed)).mp complete
  change before.functor ⋙ after.functor ≅ 𝟭 generated.closed.Obj at whole
  exact no_faithful_return_to_the_old_theory before.functor
    (Functor.Faithful.of_comp_iso whole)

theorem actual_monad_is_not_the_identity_up_to_natural_isomorphism :
    ¬ Nonempty (Construction.monad.toFunctor ≅ 𝟭 (BicategoryIsoClasses LambdaTheory.{0,0})) := by
  rintro ⟨comparison⟩
  exact monad_object_is_not_isomorphic_to_the_old_theory ⟨comparison.app sourceClass⟩

def topExtension : ConjunctiveClosedTheory.Map generated generated :=
  extension source generated (LambdaTheoryMap.comp (unitMap source) LambdaTheoryStructuredControls.topMap)

theorem free_top_readout :
    free.map (ClosedTheoryIsoClasses.classOf LambdaTheoryStructuredControls.topMap) =
      ConjunctiveClosedTheory.classOf topExtension := rfl

theorem top_extension_changes_old_false :
    topExtension.functor.obj ((unitMap source).functor.obj false) =
      (unitMap source).functor.obj true :=
  RelativeClosedSyntax.Interpretation.functor_base_object
    (ModelReadout.model
      (LambdaTheoryMap.comp (unitMap source) LambdaTheoryStructuredControls.topMap).functor
      generated.operations generated.laws).meanings
    (ModelReadout.model
      (LambdaTheoryMap.comp (unitMap source) LambdaTheoryStructuredControls.topMap).functor
      generated.operations generated.laws).realization false

theorem top_extension_has_no_identity_comparison :
    ¬ Nonempty (topExtension.functor ≅ 𝟭 generated.closed.Obj) := by
  rintro ⟨comparison⟩
  let interpreted : firstBase.obj true ≅ firstBase.obj false :=
    eqToIso ((congrArg firstDiagram.obj top_extension_changes_old_false).trans (old_read true)).symm ≪≫
      firstDiagram.mapIso (comparison.app ((unitMap source).functor.obj false)) ≪≫ eqToIso (old_read false)
  exact RelativeClosedWeakBaseControls.false_fibre_empty.false
    (interpreted.hom RelativeClosedWeakBaseControls.trueValue)

theorem actual_free_action_is_nonidentity :
    free.map (ClosedTheoryIsoClasses.classOf LambdaTheoryStructuredControls.topMap) ≠ 𝟙 generated := by
  rw [free_top_readout]
  intro same
  have admitted := (ConjunctiveClosedTheory.classOf_equal_iff topExtension
    (ConjunctiveClosedTheory.Map.identity generated)).mp same
  obtain ⟨comparison⟩ := admitted
  exact top_extension_has_no_identity_comparison ⟨comparison.comparison⟩

theorem complete_base_hom_readout :
    HomEquivalence.homEquiv source generated
        (free.map (ClosedTheoryIsoClasses.classOf LambdaTheoryStructuredControls.topMap)) =
      ClosedTheoryIsoClasses.classOf LambdaTheoryStructuredControls.topMap ≫ FreeForgetful.unit sourceClass :=
  freeMap_restriction (ClosedTheoryIsoClasses.classOf LambdaTheoryStructuredControls.topMap)

abbrev second := freeObject generated.closed
abbrev multiplication := Construction.multiplicationMap sourceClass
abbrev foldDiagram := multiplication.functor ⋙ firstDiagram

private instance first_identity_closed : MonoidalClosedFunctor (𝟭 generated.closed.Obj) :=
  cartesianClosedFunctorOfLeftAdjointPreservesBinaryProducts _ Adjunction.id

theorem multiplication_proposition_read :
    multiplication.functor.obj second.operations.proposition = fresh :=
  Construction.folds_proposition sourceClass

theorem multiplication_product_read :
    multiplication.functor.obj (second.operations.proposition ⊗ second.operations.proposition) =
      fresh ⊗ fresh :=
  ModelReadout.product_read (𝟭 generated.closed.Obj) generated.operations generated.laws

theorem fold_proposition_read : foldDiagram.obj second.operations.proposition = ULift.{0} Bool :=
  (congrArg firstDiagram.obj multiplication_proposition_read).trans fresh_read

theorem fold_product_read :
    foldDiagram.obj (second.operations.proposition ⊗ second.operations.proposition) =
      ULift.{0} Bool ⊗ ULift.{0} Bool :=
  (congrArg firstDiagram.obj multiplication_product_read).trans
    RelativeClosedConjunctiveControls.native_conjunction_domain_read

theorem complete_fold_conjunction_heq :
    HEq (foldDiagram.map second.operations.conjunction) RelativeClosedConjunctiveControls.boolean.conjunction :=
  (Mettapedia.CategoryTheory.Functor.map_heq firstDiagram multiplication_product_read multiplication_proposition_read
    (Construction.folds_conjunction sourceClass)).trans
    (ModelReadout.conjunction_heq firstBase RelativeClosedConjunctiveControls.boolean
      RelativeClosedConjunctiveControls.boolean_laws)

def foldedConjunction : ULift.{0} Bool ⊗ ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom fold_product_read.symm ≫ foldDiagram.map second.operations.conjunction ≫
    eqToHom fold_proposition_read

theorem complete_fold_conjunction :
    foldedConjunction = RelativeClosedConjunctiveControls.boolean.conjunction :=
  ((conj_eqToHom_iff_heq RelativeClosedConjunctiveControls.boolean.conjunction _
    fold_product_read.symm fold_proposition_read.symm).mpr complete_fold_conjunction_heq.symm).symm

theorem fold_retains_both_supplied_inputs :
    (foldedConjunction (ULift.up true, ULift.up false)).down = false ∧
      (foldedConjunction (ULift.up true, ULift.up true)).down = true ∧
      (foldedConjunction (ULift.up false, ULift.up true)).down = false := by
  rw [complete_fold_conjunction]
  exact ⟨rfl, rfl, rfl⟩

theorem folded_conjunction_is_not_first_projection :
    foldedConjunction ≠ CartesianMonoidalCategory.fst (ULift.{0} Bool) (ULift.{0} Bool) := by
  intro same
  have actual := congrArg (fun arrow : ULift.{0} Bool ⊗ ULift.{0} Bool ⟶ ULift.{0} Bool =>
    (arrow (ULift.up true, ULift.up false)).down) same
  exact Bool.false_ne_true (fold_retains_both_supplied_inputs.1.symm.trans actual)

theorem folded_conjunction_is_not_constant_truth :
    foldedConjunction ≠ CartesianMonoidalCategory.toUnit (ULift.{0} Bool ⊗ ULift.{0} Bool) ≫
      RelativeClosedConjunctiveControls.boolean.truth := by
  intro same
  have actual := congrArg (fun arrow : ULift.{0} Bool ⊗ ULift.{0} Bool ⟶ ULift.{0} Bool =>
    (arrow (ULift.up true, ULift.up false)).down) same
  exact Bool.false_ne_true (fold_retains_both_supplied_inputs.1.symm.trans actual)

theorem monad_mu_retains_old_false :
    multiplication.functor.obj (baseObject (nativeSignature (C := generated.closed.Obj))
      ((unitMap source).functor.obj false)) = (unitMap source).functor.obj false :=
  Construction.retains_old_object sourceClass ((unitMap source).functor.obj false)

theorem ordinary_base_cells_still_need_their_own_admission :
    Nonempty (RelativeClosedConjunctiveCellExtensionBoundary.firstBase ⟶
      RelativeClosedConjunctiveCellExtensionBoundary.lastBase) ∧
      ¬ ∃ cell : RelativeClosedConjunctiveCellExtensionBoundary.firstDiagram ⟶
          RelativeClosedConjunctiveCellExtensionBoundary.lastDiagram,
        RelativeClosedConjunctiveCellExtensionBoundary.propositionCell cell = 𝟙 (ULift.{0} Bool) :=
  RelativeClosedConjunctiveCellExtensionBoundary.base_cell_is_supplied_and_cannot_have_that_extension

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveAdjunctionControls
