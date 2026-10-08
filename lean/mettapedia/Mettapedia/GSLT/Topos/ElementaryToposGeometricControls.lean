import Mettapedia.CategoryTheory.ElementaryToposGeometric
import Mettapedia.CategoryTheory.TypeSubobjectClassifier
import Mettapedia.GSLT.Topos.SubobjectClassifier
import Mettapedia.GSLT.Core.LambdaTheoryClosedControls
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Geometric inverse-image controls

The diagonal from sets to two-index diagrams has an actual right adjoint
and preserves finite limits. Independent diagram components show that this
map is not full. Exchange of the indices is another geometric map and moves
a supplied component value. The Boolean power functor is finite-limit
preserving but cannot be a left adjoint: two maps agree on its mapped
coproduct injections and disagree on an independently supplied function.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Topos.ElementaryToposGeometricControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory
open Mettapedia.GSLT.Core.LambdaTheoryClosedControls

abbrev sets : ElementaryTopos.{1, 0} :=
  ElementaryTopos.ofCategory (Type) TypeSubobjectClassifier.classifier

/-- The classifier is transported from the constructively classified
presheaf category along the actual double-opposite equivalence. -/
def diagramClassifier : Subobject.Classifier Diagrams := by
  let : HasSubobjectClassifier ((Discrete Bool)ᵒᵖᵒᵖ ⥤ Type) :=
    presheafCategoryHasClassifierConstructive (Discrete Bool)ᵒᵖ
  let actual : Subobject.Classifier ((Discrete Bool)ᵒᵖᵒᵖ ⥤ Type) :=
    HasSubobjectClassifier.exists_classifier.some
  exact actual.ofEquivalence (opOpEquivalence (Discrete Bool)).congrLeft

abbrev diagrams : ElementaryTopos.{1, 0} :=
  ElementaryTopos.ofCategory Diagrams diagramClassifier

abbrev diagonal : ElementaryTopos.GeometricHom sets diagrams where
  functor := Functor.const (Discrete Bool)
  finite := by
    let : PreservesLimitsOfSize.{0, 0}
        (Functor.const (Discrete Bool) : Type ⥤ Diagrams) := inferInstance
    infer_instance
  leftAdjoint := ⟨lim, ⟨constLimAdj (J := Discrete Bool) (C := Type)⟩⟩

def independentShift : diagonal.functor.obj Nat ⟶ diagonal.functor.obj Nat :=
  Discrete.natTrans fun index => ↾fun (value : Nat) =>
    value + if index.as then 2 else 1

theorem independent_shift_left : independentShift.app ⟨false⟩ (10 : Nat) = (11 : Nat) := rfl

theorem independent_shift_right : independentShift.app ⟨true⟩ (10 : Nat) = (12 : Nat) := rfl

/-- This genuine geometric map is not an equivalence masquerading as
a general inverse-image map. -/
theorem diagonal_not_full : ¬ diagonal.functor.Full := by
  intro full
  let := full
  obtain ⟨arrow, mapped⟩ := diagonal.functor.map_surjective independentShift
  have left := congrArg (fun change : diagonal.functor.obj Nat ⟶
    diagonal.functor.obj Nat => change.app ⟨false⟩ (10 : Nat)) mapped
  have right := congrArg (fun change : diagonal.functor.obj Nat ⟶
    diagonal.functor.obj Nat => change.app ⟨true⟩ (10 : Nat)) mapped
  let sourceArrow : (Nat : Type) ⟶ (Nat : Type) := arrow
  have first : sourceArrow (10 : Nat) = 11 := left
  have second : sourceArrow (10 : Nat) = 12 := right
  cases first.symm.trans second

abbrev exchange : ElementaryTopos.GeometricHom diagrams diagrams where
  functor := swapEquivalence.functor
  finite := inferInstance
  leftAdjoint := swapEquivalence.isLeftAdjoint_functor

theorem exchange_nonidentity : exchange.functor ≠ 𝟭 Diagrams := swap_is_nonidentity

theorem exchanged_supplied_value :
    (exchange.functor.map shift).app ⟨false⟩ (10 : Nat) = (12 : Nat) := rfl

theorem exchanged_value_differs :
    ((exchange.functor.map shift).app ⟨false⟩ (10 : Nat) : Nat) ≠
      shift.app ⟨false⟩ (10 : Nat) := component_values_differ

def falseInjection : PUnit ⟶ Bool := ↾fun _ => false

def trueInjection : PUnit ⟶ Bool := ↾fun _ => true

def boolCofan : BinaryCofan PUnit PUnit := BinaryCofan.mk falseInjection trueInjection

def boolDesc {target : Type} (first second : PUnit ⟶ target) : Bool ⟶ target :=
  ↾fun flag => if flag then second PUnit.unit else first PUnit.unit

def boolCofanIsColimit : IsColimit boolCofan :=
  BinaryCofan.IsColimit.mk _ boolDesc
    (by
      intro target first second
      ext point
      cases point
      rfl)
    (by
      intro target first second
      ext point
      cases point
      rfl)
    (by
      intro target first second candidate left right
      ext flag
      cases flag
      · exact congrArg (fun arrow : PUnit ⟶ target => arrow PUnit.unit) left
      · exact congrArg (fun arrow : PUnit ⟶ target => arrow PUnit.unit) right)

/-- Right-adjoint finite-limit preservation does not imply the existence
of a right adjoint to that same functor. -/
theorem power_bool_not_left_adjoint :
    ¬ (CartesianClosedPowerFunctor.power Bool).IsLeftAdjoint := by
  intro admitted
  let := admitted
  let actual := mapIsColimitOfPreservesOfIsColimit
    (CartesianClosedPowerFunctor.power Bool) falseInjection trueInjection boolCofanIsColimit
  let first : (Bool ⟶ Bool) ⟶ Bool := ↾fun input => input false
  let second : (Bool ⟶ Bool) ⟶ Bool := ↾fun input => input true
  have same : first = second := BinaryCofan.IsColimit.hom_ext actual (by rfl) (by rfl)
  have impossible := congrArg (fun arrow : (Bool ⟶ Bool) ⟶ Bool =>
    arrow (↾fun flag => flag)) same
  cases impossible

theorem power_bool_preserves_finite_limits :
    PreservesFiniteLimits (CartesianClosedPowerFunctor.power Bool) := inferInstance

theorem no_geometric_power_map : ¬ ∃ route : ElementaryTopos.GeometricHom sets sets,
    route.functor = CartesianClosedPowerFunctor.power Bool := by
  rintro ⟨route, same⟩
  apply power_bool_not_left_adjoint
  exact same ▸ route.leftAdjoint

end Mettapedia.GSLT.Topos.ElementaryToposGeometricControls
