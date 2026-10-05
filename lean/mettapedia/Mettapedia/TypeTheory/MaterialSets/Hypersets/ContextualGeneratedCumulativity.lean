import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedUniverse
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentedTypeCumulativity

/-!
# Successor material readings of generated contextual families

The original context, arrows and dependent semantic families remain external.
Each generated fibre has a successor material reading with constructed member
recovery. Restriction and decoding commute with this embedding.
Every transport retains the complete family dictionary. The enclosure
comparison concerns pointwise ranges of interpreted carriers.

The full contextual product is rebuilt from lifted faithful future labels,
lifted result dictionaries and the complete naturality predicate. Its material
function graph is proved equal to the lifted original function graph. Sums are
independently rebuilt from their two lifted dependent coordinate dictionaries.
These comparisons do not assert a translation into an internally small
successor-world grammar or equate its additional codes with the original codes.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCumulativity

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open ContextualGeneratedUniverse

universe u
variable {C : Type u} [Category.{u} C] {context : LabelledContext C}

def model (domain : MaterialFamily context) (point : context.base.Elements) :
    PresentedType (ULift.{u + 1, u} (domain.family.obj point)) :=
  PresentedTypeCumulativity.liftModel (domain.model point)

def memberEquiv (domain : MaterialFamily context) (point : context.base.Elements) :
    {value : HSet.{u} // value ∈ (domain.model point).carrier} ≃
      {value : HSet.{u + 1} // value ∈ (model domain point).carrier} :=
  HSet.liftedMembersEquiv (domain.model point).carrier

theorem memberEquiv_value (domain : MaterialFamily context) (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier}) :
    (memberEquiv domain point member).1 = HSet.lift member.1 := rfl

theorem memberEquiv_decode (domain : MaterialFamily context) (point : context.base.Elements)
    (member : {value : HSet.{u} // value ∈ (domain.model point).carrier}) :
    ((model domain point).decode (memberEquiv domain point member)).down =
      (domain.model point).decode member := by
  change (domain.model point).decode
    ((HSet.liftedMembersEquiv (domain.model point).carrier).symm
      (HSet.liftedMembersEquiv (domain.model point).carrier member)) = _
  rw [Equiv.symm_apply_apply]

def restriction (domain : MaterialFamily context) {first second : context.base.Elements} (arrow : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ (model domain first).carrier}) :
    {value : HSet.{u + 1} // value ∈ (model domain second).carrier} :=
  memberEquiv domain second (domain.memberRestriction arrow ((memberEquiv domain first).symm member))

theorem restriction_member (domain : MaterialFamily context) {first second : context.base.Elements} (arrow : first ⟶ second)
    (member : {value : HSet.{u} // value ∈ (domain.model first).carrier}) :
    restriction domain arrow (memberEquiv domain first member) =
      memberEquiv domain second (domain.memberRestriction arrow member) := by
  unfold restriction
  rw [Equiv.symm_apply_apply]

theorem restriction_decode (domain : MaterialFamily context) {first second : context.base.Elements} (arrow : first ⟶ second)
    (member : {value : HSet.{u + 1} // value ∈ (model domain first).carrier}) :
    ((model domain second).decode (restriction domain arrow member)).down =
      domain.family.map arrow (((model domain first).decode member).down) := by
  rw [restriction, memberEquiv_decode, MaterialFamily.memberRestriction_decode]
  change domain.family.map arrow _ = domain.family.map arrow _
  rfl

theorem restriction_id (domain : MaterialFamily context) (point : context.base.Elements)
    (member : {value : HSet.{u + 1} // value ∈ (model domain point).carrier}) :
    restriction domain (𝟙 point) member = member := by
  have original := domain.members.map_id_apply point ((memberEquiv domain point).symm member)
  exact (congrArg (memberEquiv domain point) original).trans
    ((memberEquiv domain point).apply_symm_apply member)

theorem restriction_comp (domain : MaterialFamily context) {first middle last : context.base.Elements}
    (earlier : first ⟶ middle) (later : middle ⟶ last)
    (member : {value : HSet.{u + 1} // value ∈ (model domain first).carrier}) :
    restriction domain later (restriction domain earlier member) = restriction domain (earlier ≫ later) member := by
  have inverse := (memberEquiv domain middle).symm_apply_apply
    (domain.memberRestriction earlier ((memberEquiv domain first).symm member))
  have composite := domain.members.map_comp_apply earlier later ((memberEquiv domain first).symm member)
  exact (congrArg (fun oldMember => memberEquiv domain last (domain.memberRestriction later oldMember)) inverse).trans
    (congrArg (memberEquiv domain last) composite).symm

/-- The successor material members form an actual functor over the full
original context. Its laws retain the same authored family restrictions. -/
def members (domain : MaterialFamily context) : context.base.Elements ⥤ Type (u + 2) where
  obj point := {value : HSet.{u + 1} // value ∈ (model domain point).carrier}
  map arrow := TypeCat.ofHom (restriction domain arrow)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact restriction_id domain point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    intro member
    exact (restriction_comp domain earlier later member).symm

section Functions

variable {I : Type u} {O : I → Type u} (coding : ArgumentCoding I) (outputs : (i : I) → PresentedType (O i))

/-- Equality of whole material function graphs compares every lifted row. -/
theorem functionGraph_lift (function : (i : I) → O i) :
    HSet.mk (LabelledDependentProducts.functionGraph coding.lift
      (fun i => PresentedTypeCumulativity.liftModel (outputs i.down))
      (fun i => ULift.up (function i.down))) =
        HSet.lift (HSet.mk (LabelledDependentProducts.functionGraph coding outputs function)) := by
  apply HSet.ext
  intro value
  refine (LabelledDependentProducts.mem_functionGraph_iff _ _ _ value).trans ?_
  refine Iff.trans ?_ HSet.mem_lift_iff.symm
  constructor
  · rintro ⟨i, same⟩
    refine ⟨HSet.kpair (coding.reading i.down) ((outputs i.down).value (function i.down)),
      (LabelledDependentProducts.mem_functionGraph_iff _ _ _ _).mpr ⟨i.down, rfl⟩, ?_⟩
    exact (HSet.lift_kpair _ _).trans same
  · rintro ⟨old, member, same⟩
    obtain ⟨i, row⟩ := (LabelledDependentProducts.mem_functionGraph_iff _ _ _ _).mp member
    refine ⟨ULift.up i, ?_⟩
    exact (HSet.lift_kpair _ _).symm.trans ((congrArg HSet.lift row).trans same)

end Functions

section FullPi

variable {D : Type u} [Category.{u} D]
variable (domain : D ⥤ Type u) (body : domain.Elements ⥤ Type u) (point : D)
variable (coding : ArgumentCoding (PowerClassContextualMaterialization.FutureArguments domain point))
variable (outputs : (argument : PowerClassContextualMaterialization.FutureArguments domain point) →
  PresentedType ((PowerClassPresheafBaseChange.Future.result domain body point).obj argument))

abbrev RaisedValues :=
  (argument : ULift.{u + 1, u} (PowerClassContextualMaterialization.FutureArguments domain point)) →
    ULift.{u + 1, u} ((PowerClassPresheafBaseChange.Future.result domain body point).obj argument.down)

def lowerValues (function : RaisedValues domain body point) :
    (argument : PowerClassContextualMaterialization.FutureArguments domain point) →
      (PowerClassPresheafBaseChange.Future.result domain body point).obj argument :=
  fun argument => (function (ULift.up argument)).down

/-- Compatibility retains the original complete future-arrow equation. -/
abbrev RaisedSection := {function : RaisedValues domain body point //
  lowerValues domain body point function ∈ (PowerClassPresheafBaseChange.Future.result domain body point).sections}

def sectionEquiv : RaisedSection domain body point ≃
    ULift.{u + 1, u} (PowerClassPresheafBaseChange.Future.result domain body point).sections where
  toFun function := ULift.up ⟨lowerValues domain body point function.val, function.property⟩
  invFun term := ⟨fun argument => ULift.up (term.down.val argument.down), term.down.property⟩
  left_inv function := by
    apply Subtype.ext
    funext argument
    cases argument
    rfl
  right_inv _ := rfl

private def uliftEquiv {A B : Type u} (comparison : A ≃ B) : ULift.{u + 1, u} A ≃ ULift.{u + 1, u} B where
  toFun term := ULift.up (comparison term.down)
  invFun term := ULift.up (comparison.symm term.down)
  left_inv term := ULift.ext _ _ (comparison.symm_apply_apply term.down)
  right_inv term := ULift.ext _ _ (comparison.apply_symm_apply term.down)

/-- The upper product is independently constructed by range and compatible
row separation, with its own unrestricted-function decoder. -/
def piModel : PresentedType (ULift.{u + 1, u} (DependentSection domain body point)) :=
  PresentedType.relabel
    (LabelledDependentProducts.compatibleProduct coding.lift
      (fun argument => PresentedTypeCumulativity.liftModel (outputs argument.down))
      (fun function => lowerValues domain body point function ∈
        (PowerClassPresheafBaseChange.Future.result domain body point).sections))
    ((sectionEquiv domain body point).trans
      (uliftEquiv (PowerClassPresheafBaseChange.Future.sectionEquiv domain body point).symm))

theorem piModel_value (function : ULift.{u + 1, u} (DependentSection domain body point)) :
    (piModel domain body point coding outputs).value function =
      HSet.lift ((PowerClassContextualMaterialization.piModel domain body point coding outputs).value function.down) :=
  functionGraph_lift coding outputs
    (fun argument => function.down.app argument.1.1 argument.1.2 argument.2)

theorem piModel_carrier :
    (piModel domain body point coding outputs).carrier =
      HSet.lift (PowerClassContextualMaterialization.piModel domain body point coding outputs).carrier :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ Equiv.ulift
    (piModel_value domain body point coding outputs)

/-- Actual evaluation at any future index recovers the lifted full result. -/
theorem piModel_evaluation (function : ULift.{u + 1, u} (DependentSection domain body point))
    (argument : PowerClassContextualMaterialization.FutureArguments domain point) :
    LabelledDependentProducts.evalValue coding.lift
      (fun index => PresentedTypeCumulativity.liftModel (outputs index.down))
      ((piModel domain body point coding outputs).value function) (ULift.up argument) =
        HSet.lift ((outputs argument).value (function.down.app argument.1.1 argument.1.2 argument.2)) :=
  LabelledDependentProducts.evalValue_functionGraph coding.lift _
    (fun index => ULift.up (function.down.app index.down.1.1 index.down.1.2 index.down.2)) (ULift.up argument)

end FullPi

section FullSigma

variable (domain : MaterialFamily context) (body : MaterialFamily domain.extension) (point : context.base.Elements)

private def sigmaEquiv :
    (Σ first : ULift.{u + 1, u} (domain.family.obj point),
      ULift.{u + 1, u} (body.family.obj ⟨point.1, ⟨point.2, first.down⟩⟩)) ≃
        ULift.{u + 1, u} ((domain.sigma body).family.obj point) where
  toFun term := ULift.up ⟨term.1.down, term.2.down⟩
  invFun term := ⟨ULift.up term.down.1, ULift.up term.down.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def sigmaModel : PresentedType (ULift.{u + 1, u} ((domain.sigma body).family.obj point)) :=
  PresentedType.relabel
    (PresentedType.sum (model domain point)
      (fun first => model body ⟨point.1, ⟨point.2, first.down⟩⟩))
    (sigmaEquiv domain body point)

theorem sigmaModel_value (term : ULift.{u + 1, u} ((domain.sigma body).family.obj point)) :
    (sigmaModel domain body point).value term = HSet.lift (((domain.sigma body).model point).value term.down) := by
  unfold sigmaModel
  rw [PresentedType.relabel_value, PresentedType.sum_value]
  change HSet.kpair (HSet.lift ((domain.model point).value term.down.1))
    (HSet.lift ((body.model ⟨point.1, ⟨point.2, term.down.1⟩⟩).value term.down.2)) =
      HSet.lift ((PresentedType.sum (domain.model point)
        (fun first => body.model ⟨point.1, ⟨point.2, first⟩⟩)).value term.down)
  exact (HSet.lift_kpair ((domain.model point).value term.down.1)
    ((body.model ⟨point.1, ⟨point.2, term.down.1⟩⟩).value term.down.2)).symm.trans
    (congrArg HSet.lift (PresentedType.sum_value (domain.model point)
      (fun first => body.model ⟨point.1, ⟨point.2, first⟩⟩) term.down)).symm

theorem sigmaModel_carrier :
    (sigmaModel domain body point).carrier = HSet.lift ((domain.sigma body).model point).carrier :=
  PresentedTypeCumulativity.carrier_eq_lift_of_values _ _ Equiv.ulift (sigmaModel_value domain body point)

end FullSigma

section BaseChange

variable (domain : MaterialFamily context) (body : MaterialFamily domain.extension)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))
variable {other : LabelledContext C} (change : NatTrans other.base context.base) (point : other.base.Elements)

/-- Rebuilding full products after base change and then raising their
material readings agrees with raising the original complete product. -/
theorem pi_baseChange_value
    (function : ULift.{u + 1, u} (((domain.pi body arrows).reindex change).family.obj point)) :
    (piModel (PowerClassPresheafProducts.reindex change domain.family)
      (PowerClassPresheafBaseChange.bodyReindex change domain.family
        (PowerClassPresheafProducts.indexedBody domain.family body.family)) point
      (PowerClassContextualMaterialization.BaseChange.codingReindex change domain.family point
        (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)))
      (PowerClassContextualMaterialization.BaseChange.outputsReindex change domain.family
        (PowerClassPresheafProducts.indexedBody domain.family body.family) point
        (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point)))).value
      (ULift.up (domain.piComparison body arrows change point function.down)) =
        (piModel domain.family (PowerClassPresheafProducts.indexedBody domain.family body.family)
          ((PowerClassPresheafProducts.elementMap change).obj point)
          (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))
          (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point))).value function := by
  have first := piModel_value (PowerClassPresheafProducts.reindex change domain.family)
    (PowerClassPresheafBaseChange.bodyReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family)) point
    (PowerClassContextualMaterialization.BaseChange.codingReindex change domain.family point
      (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point)))
    (PowerClassContextualMaterialization.BaseChange.outputsReindex change domain.family
      (PowerClassPresheafProducts.indexedBody domain.family body.family) point
      (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point)))
    (ULift.up (domain.piComparison body arrows change point function.down))
  have second := piModel_value domain.family
    (PowerClassPresheafProducts.indexedBody domain.family body.family)
    ((PowerClassPresheafProducts.elementMap change).obj point)
    (domain.futureCoding arrows ((PowerClassPresheafProducts.elementMap change).obj point))
    (domain.futureOutputs body ((PowerClassPresheafProducts.elementMap change).obj point)) function
  exact first.trans ((congrArg HSet.lift (domain.piUnder_value body arrows change point function.down)).trans second.symm)

end BaseChange

section Enclosure

variable (seeds : (declaredContext : LabelledContext C) → Type (u + 1))
variable (seedModel : (declaredContext : LabelledContext C) → seeds declaredContext → MaterialFamily declaredContext)
variable (arrows : (first second : Cᵒᵖ) → ArgumentCoding (first ⟶ second))

/-- This range contains the successor readings of exactly the original
generated codes. It does not quantify over additional successor codes. -/
def enclosure (point : context.base.Elements) : HSet.{u + 2} :=
  HSet.imageUp fun code : ULift.{u + 2, u + 1} (ContextualGeneratedUniverse.Code seeds seedModel arrows context) =>
    (model code.down.1 point).carrier

theorem enclosure_eq_lift (point : context.base.Elements) :
    enclosure seeds seedModel arrows point =
      HSet.lift (ContextualGeneratedUniverse.enclosure seeds seedModel arrows context point) := by
  apply HSet.ext
  intro value
  rw [enclosure, HSet.mem_imageUp_iff, HSet.mem_lift_iff]
  constructor
  · rintro ⟨code, same⟩
    exact ⟨HSet.lift (code.down.1.model point).carrier,
      (ContextualGeneratedUniverse.mem_enclosure_iff seeds seedModel arrows).mpr ⟨code.down, rfl⟩, same⟩
  · rintro ⟨old, member, same⟩
    obtain ⟨code, recovered⟩ := (ContextualGeneratedUniverse.mem_enclosure_iff seeds seedModel arrows).mp member
    exact ⟨ULift.up code, (congrArg HSet.lift recovered).trans same⟩

end Enclosure

namespace Growing

abbrev input := ContextualGeneratedUniverse.Growing.input
abbrev body := ContextualGeneratedUniverse.Growing.body
abbrev arrows := ContextualGeneratedUniverse.Growing.arrowCoding
abbrev old := ContextualGeneratedUniverse.Growing.old

def product : PresentedType (ULift.{1, 0} ((input.pi body arrows).family.obj old)) :=
  piModel input.family (PowerClassPresheafProducts.indexedBody input.family body.family) old
    (input.futureCoding arrows old) (input.futureOutputs body old)

theorem future_functions_differ :
    product.value (ULift.up (PowerClassContextualMaterialization.Growing.identityFunction.val old)) ≠
      product.value (ULift.up (PowerClassContextualMaterialization.Growing.constantFunction.val old)) := by
  intro same
  have first := piModel_value input.family (PowerClassPresheafProducts.indexedBody input.family body.family) old
    (input.futureCoding arrows old) (input.futureOutputs body old)
    (ULift.up (PowerClassContextualMaterialization.Growing.identityFunction.val old))
  have second := piModel_value input.family (PowerClassPresheafProducts.indexedBody input.family body.family) old
    (input.futureCoding arrows old) (input.futureOutputs body old)
    (ULift.up (PowerClassContextualMaterialization.Growing.constantFunction.val old))
  exact ContextualGeneratedUniverse.Growing.future_functions_differ
    (HSet.lift_injective (first.symm.trans (same.trans second)))

def currentIndex (argument : input.family.obj old) :
    PowerClassContextualMaterialization.FutureArguments input.family old := ⟨⟨old, 𝟙 old⟩, argument⟩

def currentEvaluation (function : ULift.{1, 0} ((input.pi body arrows).family.obj old)) :
    input.family.obj old → HSet.{1} :=
  fun argument => LabelledDependentProducts.evalValue (input.futureCoding arrows old).lift
    (fun index => PresentedTypeCumulativity.liftModel (input.futureOutputs body old index.down))
    (product.value function) (ULift.up (currentIndex argument))

/-- The successor model also retains a future distinction which no table
of material evaluations at the original present arguments can recover. -/
theorem current_evaluation_not_injective : ¬ Function.Injective currentEvaluation := by
  intro injective
  have currentSame : currentEvaluation
      (ULift.up (PowerClassContextualMaterialization.Growing.identityFunction.val old)) =
      currentEvaluation (ULift.up (PowerClassContextualMaterialization.Growing.constantFunction.val old)) := by
    funext argument
    have first := piModel_evaluation input.family (PowerClassPresheafProducts.indexedBody input.family body.family) old
      (input.futureCoding arrows old) (input.futureOutputs body old)
      (ULift.up (PowerClassContextualMaterialization.Growing.identityFunction.val old)) (currentIndex argument)
    have second := piModel_evaluation input.family (PowerClassPresheafProducts.indexedBody input.family body.family) old
      (input.futureCoding arrows old) (input.futureOutputs body old)
      (ULift.up (PowerClassContextualMaterialization.Growing.constantFunction.val old)) (currentIndex argument)
    exact first.trans ((congrArg (fun term => HSet.lift ((input.futureOutputs body old (currentIndex argument)).value term))
      (Mettapedia.GSLT.ContextualObservedFamilyEnclosure.GrowthControls.FutureArguments.current_applications_agree argument)).trans second.symm)
  exact future_functions_differ (congrArg product.value (injective currentSame))

end Growing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualGeneratedCumulativity
