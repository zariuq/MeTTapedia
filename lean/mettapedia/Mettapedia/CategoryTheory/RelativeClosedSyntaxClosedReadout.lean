import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxSoundness

/-!
# Complete readouts of the generated category's chosen closed structure

The actual adjunction constructed from generated curry beta and eta identifies
Mathlib uncurry with the authored evaluation application. These equations
bridge the tensor-left convention of the categorical adjunction and the
context-then-argument convention of the raw grammar.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

theorem monoidal_uncurry {context argument result : Object signature}
    (function : context ⟶ exponentialObject argument result) :
    MonoidalClosed.uncurry function = (exchange context argument).inv ≫ unabstract function := by
  change ((exponentialAdjunction argument).homEquiv context result).symm function = _
  have actual : (exponentialAdjunction argument).homEquiv context result =
      exponentialHomEquiv argument context result :=
    Equiv.ext (fun body => exponentialAdjunction_readout argument context result body)
  exact congrArg (fun correspondence => correspondence.symm function) actual

theorem unabstract_monoidal_uncurry {context argument result : Object signature}
    (function : context ⟶ exponentialObject argument result) :
    unabstract function = (exchange context argument).hom ≫ MonoidalClosed.uncurry function := by
  rw [monoidal_uncurry, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

theorem cartesian_exchange (first second : Object signature) :
    Interpretation.exchange first second = (exchange first second).hom := by
  apply product_joint_cancel
  · exact (CartesianMonoidalCategory.lift_fst _ _).trans
      (pairing_first (GeneratedCategory.second first second) (GeneratedCategory.first first second)).symm
  · exact (CartesianMonoidalCategory.lift_snd _ _).trans
      (pairing_second (GeneratedCategory.second first second) (GeneratedCategory.first first second)).symm

theorem unabstract_identity (argument result : Object signature) :
    unabstract (𝟙 (exponentialObject argument result)) = evaluation argument result := by
  have paired : pairing (first (exponentialObject argument result) argument)
      (second (exponentialObject argument result) argument) =
        𝟙 (product (exponentialObject argument result) argument) := by
    simpa only [Category.id_comp] using
      pairing_eta (𝟙 (product (exponentialObject argument result) argument))
  unfold unabstract
  rw [Category.comp_id, paired, Category.id_comp]

theorem monoidal_evaluation (argument result : Object signature) :
    Interpretation.evaluation argument result = evaluation argument result := by
  have actual : (ihom.ev argument).app result =
      (exchange (exponentialObject argument result) argument).inv ≫
        unabstract (𝟙 (exponentialObject argument result)) :=
    (MonoidalClosed.uncurry_id_eq_ev argument result).symm.trans
      (monoidal_uncurry (𝟙 (exponentialObject argument result)))
  have first : Interpretation.evaluation argument result =
      (exchange (exponentialObject argument result) argument).hom ≫ (ihom.ev argument).app result :=
    congrArg (fun incoming : product (exponentialObject argument result) argument ⟶
        product argument (exponentialObject argument result) => incoming ≫ (ihom.ev argument).app result)
      (cartesian_exchange (exponentialObject argument result) argument)
  have transported : (exchange (exponentialObject argument result) argument).hom ≫
      (ihom.ev argument).app result =
        (exchange (exponentialObject argument result) argument).hom ≫
          ((exchange (exponentialObject argument result) argument).inv ≫
            unabstract (𝟙 (exponentialObject argument result))) :=
    congrArg (fun outgoing : product argument (exponentialObject argument result) ⟶ result =>
      (exchange (exponentialObject argument result) argument).hom ≫ outgoing) actual
  exact first.trans (transported.trans
    (((exchange (exponentialObject argument result) argument).hom_inv_id_assoc _).trans
      (unabstract_identity argument result)))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
