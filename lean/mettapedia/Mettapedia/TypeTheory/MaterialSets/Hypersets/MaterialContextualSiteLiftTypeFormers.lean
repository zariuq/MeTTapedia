import Mettapedia.TypeTheory.PresheafSiteLiftTypeFormers
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSiteLiftMaterial

/-!
# Actual material product and sum formation across raised sites

The upper product is built from all successor future arguments, the actual
raised output dictionaries, and the complete naturality predicate. Every
material function row is compared with its lower row. The upper sum is
independently built from its dependent coordinate dictionaries. Both actual
carriers and decoders commute with the material universe embedding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftTypeFormers

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open ContextualGeneratedUniverse
open PowerClassPresheafBaseChange

universe u
variable {C : Type u} [Category.{u} C] {original : LabelledContext C}
variable (domain : MaterialFamily original) (codomain : MaterialFamily domain.extension)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev upperDomain := ContextualSiteLiftMaterial.family domain
abbrev upperBody := ContextualSiteLiftMaterial.body domain codomain
abbrev lowerPosition := PowerClassPresheafProducts.indexedBody domain.family codomain.family
abbrev upperPosition := PresheafSiteLift.body original.base domain.family (lowerPosition domain codomain)

namespace Pi

def lowerIndex (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (index : PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point) :
    PowerClassContextualMaterialization.FutureArguments domain.family ((PresheafSiteLift.elementsDown original.base).obj point) :=
  ⟨⟨(PresheafSiteLift.elementsDown original.base).obj index.1.1,
    (PresheafSiteLift.elementsDown original.base).map index.1.2⟩, index.2.down⟩

def raiseIndex (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (index : PowerClassContextualMaterialization.FutureArguments domain.family ((PresheafSiteLift.elementsDown original.base).obj point)) :
    PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point :=
  ⟨⟨(PresheafSiteLift.elementsUp original.base).obj index.1.1,
    (PresheafSiteLift.elementsUp original.base).map index.1.2⟩, ULift.up index.2⟩

def indexEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point ≃
      PowerClassContextualMaterialization.FutureArguments domain.family ((PresheafSiteLift.elementsDown original.base).obj point) where
  toFun := lowerIndex domain point
  invFun := raiseIndex domain point
  left_inv _ := rfl
  right_inv _ := rfl

set_option backward.isDefEq.respectTransparency false in
theorem index_reading (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (index : PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point) :
    ((upperDomain domain).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point).reading index =
      HSet.lift ((domain.futureCoding arrows ((PresheafSiteLift.elementsDown original.base).obj point)).reading
        (lowerIndex domain point index)) := by
  dsimp only [MaterialFamily.futureCoding]
  rw [ArgumentCoding.contextual_reading, ArgumentCoding.contextual_reading, HSet.lift_kpair, HSet.lift_kpair]
  change HSet.kpair _ (HSet.kpair _ (HSet.mk _)) = HSet.kpair _ (HSet.kpair _ (HSet.lift (HSet.mk _)))
  dsimp only [MaterialFamily.termCoding]
  rw [PresentedType.mk_termGraph, PresentedType.mk_termGraph]
  rfl

def outputs (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (index : PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point) :
    PresentedType ((Future.result (upperDomain domain).family (upperPosition domain codomain) point).obj index) :=
  (upperBody domain codomain).model ⟨index.1.1.1, ⟨index.1.1.2, index.2⟩⟩

theorem output_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (index : PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point)
    (term : (Future.result (upperDomain domain).family (upperPosition domain codomain) point).obj index) :
    (outputs domain codomain point index).value term =
      HSet.lift ((domain.futureOutputs codomain ((PresheafSiteLift.elementsDown original.base).obj point)
        (lowerIndex domain point index)).value term.down) := rfl

def formed : MaterialFamily (ContextualSiteLiftMaterial.context original) where
  family := dependentFunctions (upperDomain domain).family (upperPosition domain codomain)
  model point := PowerClassContextualMaterialization.piModel (upperDomain domain).family
    (upperPosition domain codomain) point
    ((upperDomain domain).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point) (outputs domain codomain point)

theorem formed_family : (formed domain codomain arrows).family =
    ((upperDomain domain).pi (upperBody domain codomain) (ContextualSiteLiftMaterial.arrows arrows)).family :=
  congrArg (dependentFunctions (upperDomain domain).family) (ContextualSiteLiftMaterial.indexed_body domain codomain).symm

def semanticEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    (formed domain codomain arrows).family.obj point ≃
      (domain.pi codomain arrows).family.obj ((PresheafSiteLift.elementsDown original.base).obj point) :=
  PresheafSiteLiftTypeFormers.Pi.equiv original.base domain.family (lowerPosition domain codomain) point

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
theorem formed_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (function : (formed domain codomain arrows).family.obj point) :
    ((formed domain codomain arrows).model point).value function =
      HSet.lift (((domain.pi codomain arrows).model ((PresheafSiteLift.elementsDown original.base).obj point)).value
        (semanticEquiv domain codomain arrows point function)) := by
  change HSet.mk (LabelledDependentProducts.functionGraph
      ((upperDomain domain).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point) (outputs domain codomain point)
      (fun index => function.app index.1.1 index.1.2 index.2)) =
    HSet.lift (HSet.mk (LabelledDependentProducts.functionGraph
      (domain.futureCoding arrows ((PresheafSiteLift.elementsDown original.base).obj point))
      (domain.futureOutputs codomain ((PresheafSiteLift.elementsDown original.base).obj point))
      (fun index => (semanticEquiv domain codomain arrows point function).app index.1.1 index.1.2 index.2)))
  apply HSet.ext
  intro value
  rw [LabelledDependentProducts.mem_functionGraph_iff, HSet.mem_lift_iff]
  constructor
  · rintro ⟨index, same⟩
    refine ⟨HSet.kpair
      ((domain.futureCoding arrows ((PresheafSiteLift.elementsDown original.base).obj point)).reading (lowerIndex domain point index))
      ((domain.futureOutputs codomain ((PresheafSiteLift.elementsDown original.base).obj point)
        (lowerIndex domain point index)).value (function.app index.1.1 index.1.2 index.2).down), ?_, ?_⟩
    · exact (LabelledDependentProducts.mem_functionGraph_iff _ _ _ _).mpr ⟨lowerIndex domain point index, rfl⟩
    · exact (HSet.lift_kpair _ _).trans
        ((congrArg₂ HSet.kpair (index_reading domain arrows point index).symm
          (output_value domain codomain point index _).symm).trans same)
  · rintro ⟨old, belongs, same⟩
    obtain ⟨index, row⟩ := (LabelledDependentProducts.mem_functionGraph_iff _ _ _ _).mp belongs
    refine ⟨raiseIndex domain point index, ?_⟩
    exact ((congrArg₂ HSet.kpair (index_reading domain arrows point (raiseIndex domain point index))
      (output_value domain codomain point (raiseIndex domain point index) _)).trans
        ((HSet.lift_kpair _ _).symm.trans ((congrArg HSet.lift row).trans same)))

theorem formed_carrier (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    ((formed domain codomain arrows).model point).carrier =
      HSet.lift (((domain.pi codomain arrows).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier) :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ (semanticEquiv domain codomain arrows point)
    (formed_value domain codomain arrows point)

def memberEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrows).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((domain.pi codomain arrows).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier} :=
  PresentedTypeCumulativity.memberEquiv _ _ (semanticEquiv domain codomain arrows point)

theorem decoder (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrows).model point).carrier}) :
    ((domain.pi codomain arrows).model ((PresheafSiteLift.elementsDown original.base).obj point)).decode
      (memberEquiv domain codomain arrows point member) =
      semanticEquiv domain codomain arrows point (((formed domain codomain arrows).model point).decode member) :=
  PresentedTypeCumulativity.decode_memberEquiv _ _ _ member

theorem evaluation (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (function : (formed domain codomain arrows).family.obj point)
    (index : PowerClassContextualMaterialization.FutureArguments (upperDomain domain).family point) :
    LabelledDependentProducts.evalValue
        ((upperDomain domain).futureCoding (ContextualSiteLiftMaterial.arrows arrows) point) (outputs domain codomain point)
        (((formed domain codomain arrows).model point).value function) index =
      HSet.lift ((domain.futureOutputs codomain ((PresheafSiteLift.elementsDown original.base).obj point)
        (lowerIndex domain point index)).value
          ((semanticEquiv domain codomain arrows point function).app
            (lowerIndex domain point index).1.1 (lowerIndex domain point index).1.2 (lowerIndex domain point index).2)) :=
  (PowerClassContextualMaterialization.piModel_evaluation _ _ _ _ _ function index).trans
    (output_value domain codomain point index _)

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (step : first ⟶ second) (function : (formed domain codomain arrows).family.obj first) :
    semanticEquiv domain codomain arrows second ((formed domain codomain arrows).family.map step function) =
      (domain.pi codomain arrows).family.map ((PresheafSiteLift.elementsDown original.base).map step)
        (semanticEquiv domain codomain arrows first function) :=
  PresheafSiteLiftTypeFormers.Pi.lower_restrict original.base domain.family (lowerPosition domain codomain) step function

set_option backward.isDefEq.respectTransparency false in
theorem member_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain arrows).model first).carrier}) :
    memberEquiv domain codomain arrows second ((formed domain codomain arrows).memberRestriction step member) =
      (domain.pi codomain arrows).memberRestriction ((PresheafSiteLift.elementsDown original.base).map step)
        (memberEquiv domain codomain arrows first member) := by
  apply ((domain.pi codomain arrows).model ((PresheafSiteLift.elementsDown original.base).obj second)).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact semantic_restriction domain codomain arrows step (((formed domain codomain arrows).model first).decode member)

end Pi

namespace Sigma

def formed : MaterialFamily (ContextualSiteLiftMaterial.context original) where
  family := PowerClassPresheafProducts.IndexedSigma.family (upperDomain domain).family (upperPosition domain codomain)
  model point := PowerClassContextualMaterialization.sigmaModel (upperDomain domain).family (upperPosition domain codomain)
    point ((upperDomain domain).model point)
    (fun argument => (upperBody domain codomain).model ⟨point.1, ⟨point.2, argument⟩⟩)

theorem formed_family : (formed domain codomain).family = ((upperDomain domain).sigma (upperBody domain codomain)).family :=
  congrArg (PowerClassPresheafProducts.IndexedSigma.family (upperDomain domain).family)
    (ContextualSiteLiftMaterial.indexed_body domain codomain).symm

def semanticEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    (formed domain codomain).family.obj point ≃
      (domain.sigma codomain).family.obj ((PresheafSiteLift.elementsDown original.base).obj point) :=
  PresheafSiteLiftTypeFormers.Sigma.equiv original.base domain.family (lowerPosition domain codomain) point

set_option maxHeartbeats 800000 in
theorem formed_value (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (pair : (formed domain codomain).family.obj point) :
    ((formed domain codomain).model point).value pair =
      HSet.lift (((domain.sigma codomain).model ((PresheafSiteLift.elementsDown original.base).obj point)).value
        (semanticEquiv domain codomain point pair)) := by
  let oldPoint := (PresheafSiteLift.elementsDown original.base).obj point
  have upper := PowerClassContextualMaterialization.sigmaModel_value
    (upperDomain domain).family (upperPosition domain codomain) point ((upperDomain domain).model point)
    (fun argument => (upperBody domain codomain).model ⟨point.1, ⟨point.2, argument⟩⟩) pair
  have lower := PowerClassContextualMaterialization.sigmaModel_value
    domain.family (lowerPosition domain codomain) oldPoint (domain.model oldPoint)
    (fun argument => codomain.model ⟨oldPoint.1, ⟨oldPoint.2, argument⟩⟩) (semanticEquiv domain codomain point pair)
  exact upper.trans ((HSet.lift_kpair ((domain.model oldPoint).value pair.1.down)
    ((codomain.model ⟨oldPoint.1, ⟨oldPoint.2, pair.1.down⟩⟩).value pair.2.down)).symm.trans
      (congrArg HSet.lift lower.symm))

theorem formed_carrier (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    ((formed domain codomain).model point).carrier =
      HSet.lift (((domain.sigma codomain).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier) :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ (semanticEquiv domain codomain point)
    (formed_value domain codomain point)

def memberEquiv (point : (ContextualSiteLiftMaterial.context original).base.Elements) :
    {value : HSet.{u + 1} // value ∈ ((formed domain codomain).model point).carrier} ≃
      {value : HSet.{u} // value ∈ ((domain.sigma codomain).model ((PresheafSiteLift.elementsDown original.base).obj point)).carrier} :=
  PresentedTypeCumulativity.memberEquiv _ _ (semanticEquiv domain codomain point)

theorem decoder (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain).model point).carrier}) :
    ((domain.sigma codomain).model ((PresheafSiteLift.elementsDown original.base).obj point)).decode
      (memberEquiv domain codomain point member) =
      semanticEquiv domain codomain point (((formed domain codomain).model point).decode member) :=
  PresentedTypeCumulativity.decode_memberEquiv _ _ _ member

theorem first_coordinate (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (pair : (formed domain codomain).family.obj point) :
    HSet.fst (((formed domain codomain).model point).value pair) =
      HSet.lift ((domain.model ((PresheafSiteLift.elementsDown original.base).obj point)).value pair.1.down) :=
  PowerClassContextualMaterialization.sigmaModel_first_value
    (upperDomain domain).family (upperPosition domain codomain) point ((upperDomain domain).model point)
    (fun argument => (upperBody domain codomain).model ⟨point.1, ⟨point.2, argument⟩⟩) pair

theorem second_coordinate (point : (ContextualSiteLiftMaterial.context original).base.Elements)
    (pair : (formed domain codomain).family.obj point) :
    HSet.snd (((formed domain codomain).model point).value pair) =
      HSet.lift ((codomain.model ⟨((PresheafSiteLift.elementsDown original.base).obj point).1,
        ⟨((PresheafSiteLift.elementsDown original.base).obj point).2, pair.1.down⟩⟩).value pair.2.down) :=
  PowerClassContextualMaterialization.sigmaModel_second_value
    (upperDomain domain).family (upperPosition domain codomain) point ((upperDomain domain).model point)
    (fun argument => (upperBody domain codomain).model ⟨point.1, ⟨point.2, argument⟩⟩) pair

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (step : first ⟶ second) (pair : (formed domain codomain).family.obj first) :
    semanticEquiv domain codomain second ((formed domain codomain).family.map step pair) =
      (domain.sigma codomain).family.map ((PresheafSiteLift.elementsDown original.base).map step)
        (semanticEquiv domain codomain first pair) :=
  congrArg ULift.down (congrArg (fun operation => operation pair)
    ((PresheafSiteLiftTypeFormers.Sigma.comparison original.base domain.family (lowerPosition domain codomain)).naturality step))

set_option backward.isDefEq.respectTransparency false in
theorem member_restriction {first second : (ContextualSiteLiftMaterial.context original).base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ ((formed domain codomain).model first).carrier}) :
    memberEquiv domain codomain second ((formed domain codomain).memberRestriction step member) =
      (domain.sigma codomain).memberRestriction ((PresheafSiteLift.elementsDown original.base).map step)
        (memberEquiv domain codomain first member) := by
  apply ((domain.sigma codomain).model ((PresheafSiteLift.elementsDown original.base).obj second)).decode.injective
  rw [decoder, MaterialFamily.memberRestriction_decode, MaterialFamily.memberRestriction_decode, decoder]
  exact semantic_restriction domain codomain step (((formed domain codomain).model first).decode member)

end Sigma

namespace Growing

abbrev input := ContextualGeneratedUniverse.Growing.input
abbrev output := ContextualGeneratedUniverse.Growing.body
abbrev arrowCoding := ContextualGeneratedUniverse.Growing.arrowCoding
abbrev upperPoint (point : ContextualGeneratedUniverse.Growing.context.base.Elements) :=
  (PresheafSiteLift.elementsUp ContextualGeneratedUniverse.Growing.context.base).obj point

def identityFunction : (Pi.formed input output arrowCoding).family.obj (upperPoint ContextualGeneratedUniverse.Growing.old) :=
  (Pi.semanticEquiv input output arrowCoding _).symm (PowerClassContextualMaterialization.Growing.identityFunction.val
    ContextualGeneratedUniverse.Growing.old)

def constantFunction : (Pi.formed input output arrowCoding).family.obj (upperPoint ContextualGeneratedUniverse.Growing.old) :=
  (Pi.semanticEquiv input output arrowCoding _).symm (PowerClassContextualMaterialization.Growing.constantFunction.val
    ContextualGeneratedUniverse.Growing.old)

theorem full_future_values_differ :
    ((Pi.formed input output arrowCoding).model (upperPoint ContextualGeneratedUniverse.Growing.old)).value identityFunction ≠
      ((Pi.formed input output arrowCoding).model (upperPoint ContextualGeneratedUniverse.Growing.old)).value constantFunction := by
  intro same
  have first := Pi.formed_value input output arrowCoding _ identityFunction
  have second := Pi.formed_value input output arrowCoding _ constantFunction
  have oldSame := HSet.lift_injective (first.symm.trans (same.trans second))
  exact ContextualGeneratedUniverse.Growing.future_functions_differ oldSame

theorem present_evaluation_not_injective :
    ¬ Function.Injective (fun function : (Pi.formed input output arrowCoding).family.obj (upperPoint ContextualGeneratedUniverse.Growing.old) =>
      fun argument : (upperDomain input).family.obj (upperPoint ContextualGeneratedUniverse.Growing.old) =>
        function.app (upperPoint ContextualGeneratedUniverse.Growing.old) (𝟙 _) argument) := by
  intro injective
  apply ContextualGeneratedUniverse.Growing.present_evaluation_not_injective
  intro first second same
  apply (Pi.semanticEquiv input output arrowCoding (upperPoint ContextualGeneratedUniverse.Growing.old)).symm.injective
  apply injective
  funext argument
  exact congrArg ULift.up (congrFun same argument.down)

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftTypeFormers
