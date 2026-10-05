import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualSiteLiftFormation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialContextualIdentitySiteLift

/-!
# Cumulative codes compared with independent successor formation

The independently generated upper product, sum and W codes are interpreted
by their actual upper constructions. Explicit equivalences compare them to
the lifted lower constructions; complete material dictionaries preserve the
lifted values and actual restriction maps. The equivalences induce inverse
natural transformations and inverse maps on genuine contextual sections.

These are decoding comparisons. A lifted formation is a cumulative seed,
while an independently formed upper code has its own constructor trace;
neither semantic equivalence nor material carrier equality identifies those
codes. In particular ULift of a dependent sum is compared by an equivalence
with the sum of the lifted coordinates, not a false type equality.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseComparisons

open CategoryTheory ContextualGeneratedUniverse
open Mettapedia.TypeTheory
open ContextualSuccessorUniverse
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u v

def castTerm {D : Type v} [Category.{v} D] {context : LabelledContext D}
    {first second : MaterialFamily context} (same : first = second)
    (point : context.base.Elements) : first.family.obj point ≃ second.family.obj point :=
  match same with
  | rfl => {
      toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem castTerm_value {D : Type v} [Category.{v} D] {context : LabelledContext D}
    {first second : MaterialFamily context} (same : first = second)
    (point : context.base.Elements) (term : first.family.obj point) :
    (second.model point).value (castTerm same point term) = (first.model point).value term := by
  cases same
  rfl

theorem castTerm_map {D : Type v} [Category.{v} D] {context : LabelledContext D}
    {left right : MaterialFamily context} (same : left = right)
    {first second : context.base.Elements} (step : first ⟶ second) (term : left.family.obj first) :
    castTerm same second (left.family.map step term) = right.family.map step (castTerm same first term) := by
  cases same
  rfl

variable {C : Type u} [Category.{u} C]
variable (seeds : (context : LabelledContext C) → Type (u + 1))
variable (seedModel : (context : LabelledContext C) → seeds context → MaterialFamily context)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

abbrev Kind := ContextualClosedUniverseCodes.BinaryFormation

variable (kind : Kind) {context : LabelledContext C}
variable (domain : LowerCode seeds seedModel arrows context)
variable (body : LowerCode seeds seedModel arrows (lowerFamily seeds seedModel arrows domain).extension)

def lowerFormer : LowerCode seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.binary seeds seedModel arrows kind domain body

def rebuild : ContextualSuccessorUniverse.Code seeds seedModel arrows (ContextualSiteLiftMaterial.context context) :=
  ContextualClosedUniverseCodes.binary (LiftSeed seeds seedModel arrows)
    (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows) kind
    (liftCode seeds seedModel arrows domain) (liftBody seeds seedModel arrows domain body)

def formed : MaterialFamily (ContextualSiteLiftMaterial.context context) :=
  match kind with
  | .pi => MaterialContextualSiteLiftTypeFormers.Pi.formed
      (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body) arrows
  | .sigma => MaterialContextualSiteLiftTypeFormers.Sigma.formed
      (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body)
  | .w => MaterialContextualWSiteLift.formed
      (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body) arrows

theorem formed_material : formed seeds seedModel arrows kind domain body =
    ContextualClosedUniverseCodes.materialBinary (ContextualSiteLiftMaterial.arrows arrows) kind
      (ContextualSiteLiftMaterial.family (lowerFamily seeds seedModel arrows domain))
      (ContextualSiteLiftMaterial.body (lowerFamily seeds seedModel arrows domain)
        (lowerFamily seeds seedModel arrows body)) := by
  cases kind
  · exact MaterialContextualSiteLiftFormation.pi_formed_eq _ _ arrows
  · exact MaterialContextualSiteLiftFormation.sigma_formed_eq _ _
  · exact MaterialContextualSiteLiftFormation.w_formed_eq _ _ arrows

theorem decode_rebuild : decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body) =
    formed seeds seedModel arrows kind domain body := by
  unfold rebuild
  dsimp only [ContextualSuccessorUniverse.decode]
  rw [ContextualClosedUniverseCodes.decode_binary]
  exact (formed_material seeds seedModel arrows kind domain body).symm

/-- This image is about retained formation data. Independent upper formers
have a constructor trace different from every single cumulative seed. -/
theorem rebuild_not_lift (previous : LowerCode seeds seedModel arrows context) :
    rebuild seeds seedModel arrows kind domain body ≠ liftCode seeds seedModel arrows previous := by
  intro same
  have traces := congrArg
    (ContextualCodeSeedTrace.codeTrace (LiftSeed seeds seedModel arrows)
      (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows)) same
  simp only [rebuild, ContextualCodeSeedTrace.codeTrace_binary] at traces
  cases kind <;> (change _ = ContextualCodeSeedTrace.Trace.seed _ at traces; cases traces)

theorem lower_material : lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body) =
    ContextualClosedUniverseCodes.materialBinary arrows kind
      (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body) :=
  ContextualClosedUniverseCodes.decode_binary _ _ _ kind domain body

noncomputable def formedEquiv (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (formed seeds seedModel arrows kind domain body).family.obj point ≃
      (ContextualClosedUniverseCodes.materialBinary arrows kind
        (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body)).family.obj
        ((PresheafSiteLift.elementsDown context.base).obj point) :=
  match kind with
  | .pi => MaterialContextualSiteLiftTypeFormers.Pi.semanticEquiv _ _ arrows point
  | .sigma => MaterialContextualSiteLiftTypeFormers.Sigma.semanticEquiv _ _ point
  | .w => MaterialContextualWSiteLift.semanticEquiv _ _ arrows point

theorem formed_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (term : (formed seeds seedModel arrows kind domain body).family.obj point) :
    ((formed seeds seedModel arrows kind domain body).model point).value term =
      HSet.lift (((ContextualClosedUniverseCodes.materialBinary arrows kind
        (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body)).model
        ((PresheafSiteLift.elementsDown context.base).obj point)).value
        (formedEquiv seeds seedModel arrows kind domain body point term)) := by
  cases kind
  · exact MaterialContextualSiteLiftTypeFormers.Pi.formed_value _ _ arrows point term
  · exact MaterialContextualSiteLiftTypeFormers.Sigma.formed_value _ _ point term
  · exact MaterialContextualWSiteLift.formed_value _ _ arrows point term

theorem formed_restriction {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second) (term : (formed seeds seedModel arrows kind domain body).family.obj first) :
    formedEquiv seeds seedModel arrows kind domain body second
      ((formed seeds seedModel arrows kind domain body).family.map step term) =
      (ContextualClosedUniverseCodes.materialBinary arrows kind
        (lowerFamily seeds seedModel arrows domain) (lowerFamily seeds seedModel arrows body)).family.map
        ((PresheafSiteLift.elementsDown context.base).map step)
        (formedEquiv seeds seedModel arrows kind domain body first term) := by
  cases kind
  · exact MaterialContextualSiteLiftTypeFormers.Pi.semantic_restriction _ _ arrows step term
  · exact MaterialContextualSiteLiftTypeFormers.Sigma.semantic_restriction _ _ step term
  · exact MaterialContextualWSiteLift.semantic_restriction _ _ arrows step term

noncomputable def semantic (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.obj point ≃
      (lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).family.obj
        ((PresheafSiteLift.elementsDown context.base).obj point) :=
  (castTerm (decode_rebuild seeds seedModel arrows kind domain body) point).trans
    ((formedEquiv seeds seedModel arrows kind domain body point).trans
      (castTerm (lower_material seeds seedModel arrows kind domain body).symm
        ((PresheafSiteLift.elementsDown context.base).obj point)))

theorem semantic_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (term : (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.obj point) :
    ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).value term =
      HSet.lift (((lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).model
        ((PresheafSiteLift.elementsDown context.base).obj point)).value
        (semantic seeds seedModel arrows kind domain body point term)) := by
  unfold semantic
  simp only [Equiv.trans_apply]
  rw [castTerm_value]
  exact (castTerm_value (decode_rebuild seeds seedModel arrows kind domain body) point term).symm.trans
    (formed_value seeds seedModel arrows kind domain body point _)

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second)
    (term : (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.obj first) :
    semantic seeds seedModel arrows kind domain body second
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.map step term) =
      (lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).family.map
        ((PresheafSiteLift.elementsDown context.base).map step)
        (semantic seeds seedModel arrows kind domain body first term) := by
  unfold semantic
  simp only [Equiv.trans_apply]
  rw [castTerm_map, formed_restriction, castTerm_map]

noncomputable def comparison : NatTrans
    (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family
    (decode seeds seedModel arrows (liftCode seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).family where
  app point := TypeCat.ofHom fun term => ULift.up (semantic seeds seedModel arrows kind domain body point term)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro term
    exact congrArg ULift.up (semantic_restriction seeds seedModel arrows kind domain body step term)

noncomputable def inverse : NatTrans
    (decode seeds seedModel arrows (liftCode seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).family
    (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family where
  app point := TypeCat.ofHom fun term => (semantic seeds seedModel arrows kind domain body point).symm term.down
  naturality first second step := by
    apply ConcreteCategory.hom_ext
    intro term
    apply (semantic seeds seedModel arrows kind domain body second).injective
    change (semantic seeds seedModel arrows kind domain body second)
      ((semantic seeds seedModel arrows kind domain body second).symm
        ((lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).family.map
          ((PresheafSiteLift.elementsDown context.base).map step) term.down)) =
        (semantic seeds seedModel arrows kind domain body second)
          ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.map step
            ((semantic seeds seedModel arrows kind domain body first).symm term.down))
    rw [semantic_restriction, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

theorem comparison_left : compose (comparison seeds seedModel arrows kind domain body)
    (inverse seeds seedModel arrows kind domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  exact (semantic seeds seedModel arrows kind domain body point).symm_apply_apply term

theorem comparison_right : compose (inverse seeds seedModel arrows kind domain body)
    (comparison seeds seedModel arrows kind domain body) =
      Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.identity _ := by
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro term
  exact congrArg ULift.up ((semantic seeds seedModel arrows kind domain body point).apply_symm_apply term.down)

noncomputable def sectionComparison :
    (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.sections ≃
      (decode seeds seedModel arrows (liftCode seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body))).family.sections where
  toFun sectionValue := ⟨fun point => (comparison seeds seedModel arrows kind domain body).app point (sectionValue.val point), by
    intro first second step
    exact (congrArg (fun operation => operation (sectionValue.val first))
      ((comparison seeds seedModel arrows kind domain body).naturality step)).symm.trans
      (congrArg ((comparison seeds seedModel arrows kind domain body).app second) (sectionValue.property step))⟩
  invFun sectionValue := ⟨fun point => (inverse seeds seedModel arrows kind domain body).app point (sectionValue.val point), by
    intro first second step
    exact (congrArg (fun operation => operation (sectionValue.val first))
      ((inverse seeds seedModel arrows kind domain body).naturality step)).symm.trans
      (congrArg ((inverse seeds seedModel arrows kind domain body).app second) (sectionValue.property step))⟩
  left_inv sectionValue := by
    apply Subtype.ext
    funext point
    exact (semantic seeds seedModel arrows kind domain body point).symm_apply_apply (sectionValue.val point)
  right_inv sectionValue := by
    apply Subtype.ext
    funext point
    exact congrArg ULift.up ((semantic seeds seedModel arrows kind domain body point).apply_symm_apply (sectionValue.val point).down)

theorem carrier_equality (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).carrier =
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).model point).carrier :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _
    (semantic seeds seedModel arrows kind domain body point)
    (semantic_value seeds seedModel arrows kind domain body point)

noncomputable def memberComparison (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).carrier} ≃
    {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).model point).carrier} :=
  ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).decode.trans
    (((semantic seeds seedModel arrows kind domain body point).trans Equiv.ulift.symm).trans
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).model point).decode.symm)

theorem memberComparison_decode (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).carrier}) :
    ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).model point).decode
      (memberComparison seeds seedModel arrows kind domain body point member) =
      ULift.up (semantic seeds seedModel arrows kind domain body point
        (((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).decode member)) :=
  Equiv.apply_symm_apply _ _

theorem memberComparison_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).carrier}) :
    (memberComparison seeds seedModel arrows kind domain body point member).val = member.val := by
  change HSet.lift (((lowerFamily seeds seedModel arrows (lowerFormer seeds seedModel arrows kind domain body)).model
    ((PresheafSiteLift.elementsDown context.base).obj point)).value
      (semantic seeds seedModel arrows kind domain body point
        (((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).decode member))) = _
  exact (semantic_value seeds seedModel arrows kind domain body point _).symm.trans
    (((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).value_decode member)

theorem memberComparison_restriction {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model first).carrier}) :
    memberComparison seeds seedModel arrows kind domain body second
        ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).memberRestriction step member) =
      (decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).memberRestriction step
        (memberComparison seeds seedModel arrows kind domain body first member) := by
  apply ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
    (lowerFormer seeds seedModel arrows kind domain body))).model second).decode.injective
  rw [memberComparison_decode, MaterialFamily.memberRestriction_decode,
    MaterialFamily.memberRestriction_decode, memberComparison_decode]
  exact congrArg ULift.up (semantic_restriction seeds seedModel arrows kind domain body step _)

theorem sectionComparison_value
    (sectionValue : (decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).family.sections)
    (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerFormer seeds seedModel arrows kind domain body))).model point).value
      ((sectionComparison seeds seedModel arrows kind domain body sectionValue).val point) =
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows kind domain body)).model point).value
        (sectionValue.val point) :=
  (semantic_value seeds seedModel arrows kind domain body point (sectionValue.val point)).symm

namespace Identity

variable (left right : (lowerFamily seeds seedModel arrows domain).family.sections)

def lowerCode : LowerCode seeds seedModel arrows context :=
  ContextualClosedUniverseCodes.identity seeds seedModel arrows domain left right

def rebuild : ContextualSuccessorUniverse.Code seeds seedModel arrows (ContextualSiteLiftMaterial.context context) :=
  ContextualSuccessorUniverse.identity seeds seedModel arrows (liftCode seeds seedModel arrows domain)
    (sectionEquiv seeds seedModel arrows domain left) (sectionEquiv seeds seedModel arrows domain right)

theorem decode_rebuild : decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right) =
    MaterialContextualIdentitySiteLift.formed (lowerFamily seeds seedModel arrows domain) left right :=
  ContextualSuccessorUniverse.decode_identity seeds seedModel arrows _ _ _

theorem rebuild_not_lift (previous : LowerCode seeds seedModel arrows context) :
    rebuild seeds seedModel arrows domain left right ≠ liftCode seeds seedModel arrows previous := by
  intro same
  have traces := congrArg
    (ContextualCodeSeedTrace.codeTrace (LiftSeed seeds seedModel arrows)
      (liftSeedModel seeds seedModel arrows) (ContextualSiteLiftMaterial.arrows arrows)) same
  simp only [rebuild, ContextualSuccessorUniverse.identity,
    ContextualCodeSeedTrace.codeTrace_identity] at traces
  change ContextualCodeSeedTrace.Trace.identity _ = ContextualCodeSeedTrace.Trace.seed _ at traces
  cases traces

theorem lower_material : lowerFamily seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right) =
    (lowerFamily seeds seedModel arrows domain).identity left right :=
  ContextualClosedUniverseCodes.decode_identity seeds seedModel arrows domain left right

def semantic (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    (decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).family.obj point ≃
      (lowerFamily seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right)).family.obj
        ((PresheafSiteLift.elementsDown context.base).obj point) :=
  (castTerm (decode_rebuild seeds seedModel arrows domain left right) point).trans
    ((MaterialContextualIdentitySiteLift.semanticEquiv (lowerFamily seeds seedModel arrows domain) left right point).trans
      (castTerm (lower_material seeds seedModel arrows domain left right).symm
        ((PresheafSiteLift.elementsDown context.base).obj point)))

theorem semantic_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (term : (decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).family.obj point) :
    ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).value term =
      HSet.lift (((lowerFamily seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right)).model
        ((PresheafSiteLift.elementsDown context.base).obj point)).value
        (semantic seeds seedModel arrows domain left right point term)) := by
  unfold semantic
  simp only [Equiv.trans_apply]
  rw [castTerm_value]
  exact (castTerm_value (decode_rebuild seeds seedModel arrows domain left right) point term).symm.trans
    (MaterialContextualIdentitySiteLift.formed_value _ left right point _)

theorem semantic_restriction {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second)
    (term : (decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).family.obj first) :
    semantic seeds seedModel arrows domain left right second
        ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).family.map step term) =
      (lowerFamily seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right)).family.map
        ((PresheafSiteLift.elementsDown context.base).map step)
        (semantic seeds seedModel arrows domain left right first term) := by
  unfold semantic
  simp only [Equiv.trans_apply]
  rw [castTerm_map, MaterialContextualIdentitySiteLift.semantic_restriction, castTerm_map]

theorem carrier_equality (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).carrier =
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerCode seeds seedModel arrows domain left right))).model point).carrier :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _
    (semantic seeds seedModel arrows domain left right point)
    (semantic_value seeds seedModel arrows domain left right point)

def memberComparison (point : (ContextualSiteLiftMaterial.context context).base.Elements) :
    {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).carrier} ≃
    {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerCode seeds seedModel arrows domain left right))).model point).carrier} :=
  ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).decode.trans
    (((semantic seeds seedModel arrows domain left right point).trans Equiv.ulift.symm).trans
      ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerCode seeds seedModel arrows domain left right))).model point).decode.symm)

theorem memberComparison_decode (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).carrier}) :
    ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerCode seeds seedModel arrows domain left right))).model point).decode
      (memberComparison seeds seedModel arrows domain left right point member) =
      ULift.up (semantic seeds seedModel arrows domain left right point
        (((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).decode member)) :=
  Equiv.apply_symm_apply _ _

theorem memberComparison_value (point : (ContextualSiteLiftMaterial.context context).base.Elements)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).carrier}) :
    (memberComparison seeds seedModel arrows domain left right point member).val = member.val := by
  change HSet.lift (((lowerFamily seeds seedModel arrows (lowerCode seeds seedModel arrows domain left right)).model
    ((PresheafSiteLift.elementsDown context.base).obj point)).value
      (semantic seeds seedModel arrows domain left right point
        (((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).decode member))) = _
  exact (semantic_value seeds seedModel arrows domain left right point _).symm.trans
    (((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model point).value_decode member)

theorem memberComparison_restriction {first second : (ContextualSiteLiftMaterial.context context).base.Elements}
    (step : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈
      ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).model first).carrier}) :
    memberComparison seeds seedModel arrows domain left right second
        ((decode seeds seedModel arrows (rebuild seeds seedModel arrows domain left right)).memberRestriction step member) =
      (decode seeds seedModel arrows (liftCode seeds seedModel arrows
        (lowerCode seeds seedModel arrows domain left right))).memberRestriction step
        (memberComparison seeds seedModel arrows domain left right first member) := by
  apply ((decode seeds seedModel arrows (liftCode seeds seedModel arrows
    (lowerCode seeds seedModel arrows domain left right))).model second).decode.injective
  rw [memberComparison_decode, MaterialFamily.memberRestriction_decode,
    MaterialFamily.memberRestriction_decode, memberComparison_decode]
  exact congrArg ULift.up (semantic_restriction seeds seedModel arrows domain left right step _)

end Identity

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSuccessorUniverseComparisons
