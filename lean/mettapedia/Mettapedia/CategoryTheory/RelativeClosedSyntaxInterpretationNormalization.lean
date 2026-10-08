import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationNormalizationReadout

/-!
# The independent interpretation satisfies canonical primitive admission

Actual parser product, exponential and presented-equalizer readouts
calibrate every constructor-built object comparison. The simultaneous raw
object recursion preserves the entire comparison, not just the object's
isomorphism class. It then earns recovery of each independently supplied
primitive arrow and the complete original assignment.

This is the canonical interpretation's unit calculation. It supplies no
free-extension action, biadjunction or monad law as an assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.InterpretationNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory Interpretation FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (meanings : Assignment C symbols D) (realization : Realization signature meanings)

theorem terminal_image : objectImage (interpreted meanings realization) (terminal signature) =
    ⟨(interpreted meanings realization).obj (terminal signature), Iso.refl _⟩ := by
  rw [objectImage_terminal]
  apply image_eq_refl _ (functor_terminal_object meanings realization).symm
  exact functor_terminalComparison meanings realization

theorem product_image (first second : Object signature)
    (firstCalibrated : objectImage (interpreted meanings realization) first =
      ⟨(interpreted meanings realization).obj first, Iso.refl _⟩)
    (secondCalibrated : objectImage (interpreted meanings realization) second =
      ⟨(interpreted meanings realization).obj second, Iso.refl _⟩) :
    objectImage (interpreted meanings realization) (product first second) =
      ⟨(interpreted meanings realization).obj (product first second), Iso.refl _⟩ := by
  rw [objectImage_product, firstCalibrated, secondCalibrated]
  apply image_eq_refl _ (functor_product_object meanings realization first second).symm
  change CartesianMonoidalCategory.prodComparison (interpreted meanings realization) first second ≫
    (𝟙 ((interpreted meanings realization).obj first) ⊗ₘ
      𝟙 ((interpreted meanings realization).obj second)) = _
  rw [id_tensorHom_id]
  exact (Category.comp_id (CartesianMonoidalCategory.prodComparison
    (interpreted meanings realization) first second)).trans
      (functor_productComparison meanings realization first second)

theorem exponential_image (argument result : Object signature)
    (argumentCalibrated : objectImage (interpreted meanings realization) argument =
      ⟨(interpreted meanings realization).obj argument, Iso.refl _⟩)
    (resultCalibrated : objectImage (interpreted meanings realization) result =
      ⟨(interpreted meanings realization).obj result, Iso.refl _⟩) :
    objectImage (interpreted meanings realization) (exponentialObject argument result) =
      ⟨(interpreted meanings realization).obj (exponentialObject argument result), Iso.refl _⟩ := by
  rw [objectImage_exponential, argumentCalibrated, resultCalibrated]
  apply image_eq_refl _ (functor_exponential_object meanings realization argument result).symm
  change (expComparison (interpreted meanings realization) argument).natTrans.app result ≫
    (functionIso (Iso.refl ((interpreted meanings realization).obj argument))
      (Iso.refl ((interpreted meanings realization).obj result))).hom = _
  rw [functionIso_refl]
  exact (Category.comp_id (show (interpreted meanings realization).obj (exponentialObject argument result) ⟶
    ((interpreted meanings realization).obj argument ⟶[D] (interpreted meanings realization).obj result) from
      (expComparison (interpreted meanings realization) argument).natTrans.app result)).trans
        (functor_expComparison meanings realization argument result)

theorem equalizer_image {source target : Object signature} (first second : RawHom source target)
    (sourceCalibrated : objectImage (interpreted meanings realization) source =
      ⟨(interpreted meanings realization).obj source, Iso.refl _⟩)
    (targetCalibrated : objectImage (interpreted meanings realization) target =
      ⟨(interpreted meanings realization).obj target, Iso.refl _⟩) :
    objectImage (interpreted meanings realization) (PresentedEqualizer.object first second) =
      ⟨(interpreted meanings realization).obj (PresentedEqualizer.object first second), Iso.refl _⟩ := by
  rw [objectImage_equalizer]
  change (⟨equalizer
      ((objectImage (interpreted meanings realization) source).comparison.inv ≫
        (interpreted meanings realization).map (classOf first) ≫
          (objectImage (interpreted meanings realization) target).comparison.hom)
      ((objectImage (interpreted meanings realization) source).comparison.inv ≫
        (interpreted meanings realization).map (classOf second) ≫
          (objectImage (interpreted meanings realization) target).comparison.hom),
    mappedPresentedIso (interpreted meanings realization) first second ≪≫
      equalizerTransport ((interpreted meanings realization).map (classOf first))
        ((interpreted meanings realization).map (classOf second))
        (objectImage (interpreted meanings realization) source).comparison
        (objectImage (interpreted meanings realization) target).comparison⟩ :
      ObjectImage (interpreted meanings realization) (PresentedEqualizer.object first second)) = _
  rw [sourceCalibrated, targetCalibrated]
  let before := (interpreted meanings realization).map (classOf first)
  let after := (interpreted meanings realization).map (classOf second)
  have beforeIdentity : 𝟙 ((interpreted meanings realization).obj source) ≫ before ≫
      𝟙 ((interpreted meanings realization).obj target) = before :=
    (Category.id_comp (before ≫ 𝟙 _)).trans (Category.comp_id before)
  have afterIdentity : 𝟙 ((interpreted meanings realization).obj source) ≫ after ≫
      𝟙 ((interpreted meanings realization).obj target) = after :=
    (Category.id_comp (after ≫ 𝟙 _)).trans (Category.comp_id after)
  apply image_eq_refl _
    ((congrArg₂ (fun f g => equalizer f g) beforeIdentity afterIdentity).trans
      (presented_object meanings realization first second).symm)
  change (mappedPresentedIso (interpreted meanings realization) first second).hom ≫
    (equalizerTransport before after (Iso.refl _) (Iso.refl _)).hom = _
  rw [presented_comparison, equalizerTransport_refl, eqToHom_trans]

theorem object_image (object : Object signature) :
    objectImage (interpreted meanings realization) object =
      ⟨(interpreted meanings realization).obj object, Iso.refl _⟩ := by
  rcases object with ⟨code, formed⟩
  revert formed
  cases code with
  | base object => exact fun _ => objectImage_base (interpreted meanings realization) object
  | name origin => exact fun _ => objectImage_named (interpreted meanings realization) origin
  | terminal => exact fun _ => terminal_image meanings realization
  | product first second =>
      intro formed
      obtain ⟨firstFormed, secondFormed⟩ := product_formation formed
      exact product_image meanings realization ⟨first, firstFormed⟩ ⟨second, secondFormed⟩
        (object_image ⟨first, firstFormed⟩) (object_image ⟨second, secondFormed⟩)
  | exponential argument result =>
      intro formed
      obtain ⟨argumentFormed, resultFormed⟩ := exponential_formation formed
      exact exponential_image meanings realization ⟨argument, argumentFormed⟩ ⟨result, resultFormed⟩
        (object_image ⟨argument, argumentFormed⟩) (object_image ⟨result, resultFormed⟩)
  | equalizer source target first second =>
      intro formed
      obtain ⟨sourceFormed, targetFormed, firstTyped, secondTyped⟩ := equalizer_formation formed
      exact equalizer_image meanings realization
        (⟨first, firstTyped⟩ : RawHom ⟨source, sourceFormed⟩ ⟨target, targetFormed⟩) ⟨second, secondTyped⟩
        (object_image ⟨source, sourceFormed⟩) (object_image ⟨target, targetFormed⟩)
termination_by objectDepth object.code
decreasing_by
  all_goals simp_all only [objectDepth]
  all_goals omega

theorem normalized_assignment (headers : HeaderFormation signature) :
    assignment (interpreted meanings realization) headers = meanings := by
  apply assignment_ext
  · exact functor_base meanings realization
  · funext origin
    exact objectValue_unique meanings realization (namedObject origin) _ rfl
  · funext origin
    have complete := functor_complete_readout meanings realization (namedArrow headers origin)
    change some (meanings.arrow origin) = some _ at complete
    change (⟨(objectImage (interpreted meanings realization) (headerSource headers origin)).value,
      (objectImage (interpreted meanings realization) (headerTarget headers origin)).value,
      (objectImage (interpreted meanings realization) (headerSource headers origin)).comparison.inv ≫
        (interpreted meanings realization).map (classOf (namedArrow headers origin)) ≫
        (objectImage (interpreted meanings realization) (headerTarget headers origin)).comparison.hom⟩ :
          ArrowValue D) = meanings.arrow origin
    rw [object_image, object_image]
    simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]
    exact (Option.some.inj complete).symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.InterpretationNormalization
