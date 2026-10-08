import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorExtension

/-!
# Native calibration of independently interpreted object comparisons

The parser's presented equalizers retain their actual authored arrows. Their
object and inclusion values are independently read before the canonical
limit comparison is identified. Generic equality transports also retain
the complete comparison arrow, including the contravariant function input.
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

theorem image_eq_refl {mapping : Object signature ⥤ D} {source : Object signature}
    (image : ObjectImage mapping source) (objects : image.value = mapping.obj source)
    (arrows : image.comparison.hom = eqToHom objects.symm) :
    image = ⟨mapping.obj source, Iso.refl _⟩ := by
  cases image with
  | mk value comparison =>
    dsimp at objects arrows
    cases objects
    have same : comparison = Iso.refl (mapping.obj source) := Iso.ext arrows
    cases same
    rfl

theorem assignment_ext {first second : Assignment C symbols D}
    (base : first.base = second.base) (objects : first.object = second.object)
    (arrows : first.arrow = second.arrow) : first = second := by
  cases first
  cases second
  cases base
  cases objects
  cases arrows
  rfl

variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]

omit [HasFiniteLimits D] in
theorem functionIso_refl (argument result : D) :
    functionIso (Iso.refl argument) (Iso.refl result) = Iso.refl (argument ⟶[D] result) := by
  apply Iso.ext
  change ((MonoidalClosed.internalHom (C := D)).map (𝟙 (Opposite.op argument))).app result ≫
    (ihom argument).map (𝟙 result) = 𝟙 _
  simp only [_root_.CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  rfl

omit [CartesianMonoidalCategory D] [MonoidalClosed D] in
theorem equalizer_eqToHom_inclusion {source target : D}
    {first second before after : source ⟶ target} (firstSame : first = before) (secondSame : second = after) :
    eqToHom (congrArg₂ (fun f g : source ⟶ target => equalizer f g) firstSame secondSame) ≫
      equalizer.ι before after = equalizer.ι first second := by
  cases firstSame
  cases secondSame
  exact Category.id_comp _

omit [CartesianMonoidalCategory D] [MonoidalClosed D] in
theorem equalizerTransport_refl {source target : D} (first second : source ⟶ target) :
    (equalizerTransport first second (Iso.refl source) (Iso.refl target)).hom =
      eqToHom (congrArg₂ (fun f g : source ⟶ target => equalizer f g)
        ((Category.id_comp (first ≫ 𝟙 target)).trans (Category.comp_id first)).symm
        ((Category.id_comp (second ≫ 𝟙 target)).trans (Category.comp_id second)).symm) := by
  apply (cancel_mono (equalizer.ι ((Iso.refl source).inv ≫ first ≫ (Iso.refl target).hom)
    ((Iso.refl source).inv ≫ second ≫ (Iso.refl target).hom))).mp
  rw [equalizerTransport_inclusion]
  exact (Category.comp_id (equalizer.ι first second)).trans
    (equalizer_eqToHom_inclusion
      ((Category.id_comp (first ≫ 𝟙 target)).trans (Category.comp_id first)).symm
      ((Category.id_comp (second ≫ 𝟙 target)).trans (Category.comp_id second)).symm).symm

variable (meanings : Assignment C symbols D) (realization : Realization signature meanings)

abbrev interpreted := Interpretation.functor meanings realization

theorem presented_object {source target : Object signature} (first second : RawHom source target) :
    (interpreted meanings realization).obj (PresentedEqualizer.object first second) =
      equalizer ((interpreted meanings realization).map (classOf first))
        ((interpreted meanings realization).map (classOf second)) :=
  objectValue_unique meanings realization (PresentedEqualizer.object first second) _
    (meanings.evaluate_equalizer _ _ (objectValue_readout meanings realization source)
      (objectValue_readout meanings realization target)
      (functor_complete_readout meanings realization first)
      (functor_complete_readout meanings realization second))

theorem presented_inclusion_heq {source target : Object signature} (first second : RawHom source target) :
    HEq ((interpreted meanings realization).map (PresentedEqualizer.inclusion first second))
      (equalizer.ι ((interpreted meanings realization).map (classOf first))
        ((interpreted meanings realization).map (classOf second))) :=
  functor_map_heq meanings realization
    (⟨.equalizerArrow source.code target.code first.code second.code,
      ⟨.equalizerArrow source.formed.some target.formed.some first.admitted.some second.admitted.some⟩⟩ :
        RawHom (PresentedEqualizer.object first second) source) _
    (meanings.evaluate_equalizer_arrow _ _ (objectValue_readout meanings realization source)
      (objectValue_readout meanings realization target)
      (functor_complete_readout meanings realization first)
      (functor_complete_readout meanings realization second))

theorem presented_inclusion {source target : Object signature} (first second : RawHom source target) :
    (interpreted meanings realization).map (PresentedEqualizer.inclusion first second) =
      eqToHom (presented_object meanings realization first second) ≫
        equalizer.ι ((interpreted meanings realization).map (classOf first))
          ((interpreted meanings realization).map (classOf second)) := by
  simpa only [eqToHom_refl, Category.comp_id] using
    (conj_eqToHom_iff_heq _ _ (presented_object meanings realization first second) rfl).mpr
      (presented_inclusion_heq meanings realization first second)

theorem presented_comparison {source target : Object signature} (first second : RawHom source target) :
    (mappedPresentedIso (interpreted meanings realization) first second).hom =
      eqToHom (presented_object meanings realization first second) := by
  apply (cancel_mono (equalizer.ι ((interpreted meanings realization).map (classOf first))
    ((interpreted meanings realization).map (classOf second)))).mp
  rw [mappedPresentedIso_inclusion]
  exact presented_inclusion meanings realization first second

end Mettapedia.CategoryTheory.RelativeClosedSyntax.InterpretationNormalization
