import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationNative

/-!
# Supplied equalizer candidates under native normalization

The literal authored lift and the selected universal lift have the same
complete inclusion readout. The earned source equalizer uniqueness compares
them without replacing the authored candidate code. Mapping that comparison
then computes the complete native lift of the supplied mapped candidate.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}

def authoredLift {source target context : Object signature}
    (first second : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code first.code) (.compose candidate.code second.code))) :
    RawHom context (PresentedEqualizer.object first second) :=
  ⟨.equalizerLift source.code target.code first.code second.code context.code candidate.code,
    ⟨.equalizerLift source.formed.some target.formed.some context.formed.some
      first.admitted.some second.admitted.some candidate.admitted.some commutes⟩⟩

theorem authoredLift_inclusion {source target context : Object signature}
    (first second : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code first.code) (.compose candidate.code second.code))) :
    classOf (authoredLift first second candidate commutes) ≫
      PresentedEqualizer.inclusion first second = classOf candidate :=
  Quotient.sound ⟨.equalizerBeta source.formed.some target.formed.some context.formed.some
    first.admitted.some second.admitted.some candidate.admitted.some commutes⟩

theorem authoredLift_is_universal {source target context : Object signature}
    (first second : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code first.code) (.compose candidate.code second.code))) :
    classOf (authoredLift first second candidate commutes) =
      PresentedEqualizer.lift first second (classOf candidate) (Quotient.sound ⟨commutes⟩) := by
  apply PresentedEqualizer.joint_cancel first second
  exact (authoredLift_inclusion first second candidate commutes).trans
    (PresentedEqualizer.lift_inclusion first second (classOf candidate) _).symm

variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

theorem mapped_condition {source target context : Object signature}
    (first second : RawHom source target) (candidate : context ⟶ source)
    (commutes : candidate ≫ classOf first = candidate ≫ classOf second) :
    (normalizedFunctor mapping).map candidate ≫ (normalizedFunctor mapping).map (classOf first) =
      (normalizedFunctor mapping).map candidate ≫ (normalizedFunctor mapping).map (classOf second) := by
  simpa only [Functor.map_comp] using congrArg (normalizedFunctor mapping).map commutes

set_option backward.isDefEq.respectTransparency false in
theorem normalized_equalizer_lift {source target context : Object signature}
    (first second : RawHom source target) (candidate : context ⟶ source)
    (commutes : candidate ≫ classOf first = candidate ≫ classOf second) :
    (normalizedFunctor mapping).map (PresentedEqualizer.lift first second candidate commutes) =
      equalizer.lift ((normalizedFunctor mapping).map candidate)
          (mapped_condition mapping first second candidate commutes) ≫
        eqToHom (normalized_equalizer_object mapping first second).symm := by
  apply (cancel_mono (eqToHom (normalized_equalizer_object mapping first second))).mp
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  apply equalizer.hom_ext
  rw [Category.assoc, ← normalized_equalizer_inclusion, ← Functor.map_comp,
    PresentedEqualizer.lift_inclusion, equalizer.lift_ι]

set_option backward.isDefEq.respectTransparency false in
theorem normalized_authoredLift {source target context : Object signature}
    (first second : RawHom source target) (candidate : RawHom context source)
    (commutes : Derivation signature (.equation context.code target.code
      (.compose candidate.code first.code) (.compose candidate.code second.code))) :
    (normalizedFunctor mapping).map (classOf (authoredLift first second candidate commutes)) =
      equalizer.lift ((normalizedFunctor mapping).map (classOf candidate))
          (mapped_condition mapping first second (classOf candidate) (Quotient.sound ⟨commutes⟩)) ≫
        eqToHom (normalized_equalizer_object mapping first second).symm := by
  rw [authoredLift_is_universal, normalized_equalizer_lift]

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
