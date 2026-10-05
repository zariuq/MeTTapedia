import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialEquivalence

/-!
# Dependent formation through material family equivalences

Corresponding domains act on their actual comprehension contexts. Body
equivalences compare the dependent fibres through that constructed action,
including their restrictions and complete material values.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialTypeFormerEquivalence

open CategoryTheory ContextualGeneratedUniverse ContextualMaterialEquivalence
open Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent

universe u
variable {C : Type u} [Category.{u} C]
variable {context : LabelledContext C}
variable {first second : MaterialFamily context}
variable (domain : Equivalence first second)
variable {left : MaterialFamily first.extension} {right : MaterialFamily second.extension}
variable (body : Equivalence left (right.reindex (other := first.extension) domain.comprehension))

private theorem arrow_heq {P : Cᵒᵖ ⥤ Type u}
    {first first' next next' : P.Elements} (sources : first = first') (targets : next = next')
    (earlier : first ⟶ next) (later : first' ⟶ next') (arrows : HEq earlier.1 later.1) : HEq earlier later := by
  cases sources
  cases targets
  exact heq_of_eq (Subtype.ext (eq_of_heq arrows))

private theorem map_heq {D : Type u} [Category.{u} D] (family : D ⥤ Type u)
    {first first' next next' : D} (sources : first = first') (targets : next = next')
    (earlier : first ⟶ next) (later : first' ⟶ next') (arrows : HEq earlier later)
    (member : family.obj first) (member' : family.obj first') (members : HEq member member') :
    HEq (family.map earlier member) (family.map later member') := by
  cases sources
  cases targets
  cases eq_of_heq arrows
  cases eq_of_heq members
  rfl

private def sigmaRight {A : Type u} {B D : A → Type u} (fibres : (argument : A) → B argument ≃ D argument) :
    Sigma B ≃ Sigma D where
  toFun pair := ⟨pair.1, fibres pair.1 pair.2⟩
  invFun pair := ⟨pair.1, (fibres pair.1).symm pair.2⟩
  left_inv pair := Sigma.ext rfl (heq_of_eq ((fibres pair.1).symm_apply_apply pair.2))
  right_inv pair := Sigma.ext rfl (heq_of_eq ((fibres pair.1).apply_symm_apply pair.2))

def sigmaFibre (point : context.base.Elements) :
    (first.sigma left).family.obj point ≃ (second.sigma right).family.obj point :=
  (sigmaRight (fun argument => body.fibre ⟨point.1, ⟨point.2, argument⟩⟩)).trans
    (Equiv.sigmaCongrLeft (β := fun argument => right.family.obj ⟨point.1, ⟨point.2, argument⟩⟩)
      (domain.fibre point))

theorem sigmaFibre_natural {point next : context.base.Elements} (step : point ⟶ next)
    (pair : (first.sigma left).family.obj point) :
    sigmaFibre domain body next ((first.sigma left).family.map step pair) =
      (second.sigma right).family.map step (sigmaFibre domain body point pair) := by
  apply Sigma.ext (domain.naturality step pair.1)
  let start : first.extension.base.Elements := ⟨point.1, ⟨point.2, pair.1⟩⟩
  let finish : first.extension.base.Elements := ⟨next.1, ⟨next.2, first.family.map step pair.1⟩⟩
  let bodyStep : start ⟶ finish :=
    (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
      (argumentMap first.family step pair.1)
  have preserved := body.naturality bodyStep pair.2
  have targets : (PowerClassPresheafProducts.elementMap domain.comprehension).obj finish =
      (⟨next.1, ⟨next.2, second.family.map step (domain.fibre point pair.1)⟩⟩ : second.extension.base.Elements) :=
    congrArg (fun argument => (⟨next.1, ⟨next.2, argument⟩⟩ : second.extension.base.Elements))
      (domain.naturality step pair.1)
  let targetStep :=
    (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
      (argumentMap second.family step (domain.fibre point pair.1))
  have underlying : ((PowerClassPresheafProducts.elementMap domain.comprehension).map bodyStep).1 = targetStep.1 := by
    change ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
      (argumentMap first.family step pair.1)).1 =
      ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
        (argumentMap second.family step (domain.fibre point pair.1))).1
    rw [Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying,
      Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying]
    rfl
  have arrows := arrow_heq rfl targets
    ((PowerClassPresheafProducts.elementMap domain.comprehension).map bodyStep) targetStep (heq_of_eq underlying)
  exact (heq_of_eq preserved).trans (map_heq right.family rfl targets _ _ arrows _ _ (heq_of_eq rfl))

theorem sigmaFibre_value (point : context.base.Elements) (pair : (first.sigma left).family.obj point) :
    ((second.sigma right).model point).value (sigmaFibre domain body point pair) =
      ((first.sigma left).model point).value pair := by
  have firstValue : ((first.sigma left).model point).value pair =
      HSet.kpair ((first.model point).value pair.1) ((left.model ⟨point.1, ⟨point.2, pair.1⟩⟩).value pair.2) :=
    PowerClassContextualMaterialization.sigmaModel_value _ _ _ _ _ _
  have secondValue : ((second.sigma right).model point).value (sigmaFibre domain body point pair) =
      HSet.kpair ((second.model point).value (domain.fibre point pair.1))
        (((right.reindex (other := first.extension) domain.comprehension).model ⟨point.1, ⟨point.2, pair.1⟩⟩).value
          (body.fibre ⟨point.1, ⟨point.2, pair.1⟩⟩ pair.2)) :=
    PowerClassContextualMaterialization.sigmaModel_value _ _ _ _ _ _
  exact secondValue.trans ((congrArg₂ HSet.kpair (domain.value point pair.1)
    (body.value ⟨point.1, ⟨point.2, pair.1⟩⟩ pair.2)).trans firstValue.symm)

def sigma : Equivalence (first.sigma left) (second.sigma right) where
  fibre := sigmaFibre domain body
  naturality := sigmaFibre_natural domain body
  value := sigmaFibre_value domain body

/-- The reverse dependent-body comparison is constructed using the actual
inverse comprehension square and its whole-family roundtrip law. -/
def bodyBackward : Equivalence right (left.reindex (other := second.extension) domain.comprehensionInverse) :=
  ((body.reindex domain.comprehensionInverse).trans
    (ofEquality (domain.symm.transportBody_roundtrip right))).symm

private theorem app_heq (point : context.base.Elements)
    (function : DependentSection first.family (PowerClassPresheafProducts.indexedBody first.family left.family) point)
    (next : context.base.Elements) (arrow : point ⟶ next) {argument other : first.family.obj next}
    (same : argument = other) : HEq (function.app next arrow argument) (function.app next arrow other) := by
  cases same
  rfl

private theorem mappedApplication (point : context.base.Elements)
    (function : DependentSection first.family (PowerClassPresheafProducts.indexedBody first.family left.family) point)
    {next later : context.base.Elements} (step : next ⟶ later) (restriction : point ⟶ next)
    (argument : second.family.obj next) :
    (left.reindex (other := second.extension) domain.comprehensionInverse).family.map
      ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
        (argumentMap second.family step argument))
      (function.app next restriction ((domain.fibre next).symm argument)) =
    function.app later (restriction ≫ step) ((domain.fibre later).symm (second.family.map step argument)) := by
  let start : second.extension.base.Elements := ⟨next.1, ⟨next.2, argument⟩⟩
  let finish : second.extension.base.Elements := ⟨later.1, ⟨later.2, second.family.map step argument⟩⟩
  let bodyStep : start ⟶ finish :=
    (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
      (argumentMap second.family step argument)
  let oldStep :=
    (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
      (argumentMap first.family step ((domain.fibre next).symm argument))
  have targets : (PowerClassPresheafProducts.elementMap domain.comprehensionInverse).obj finish =
      (⟨later.1, ⟨later.2, first.family.map step ((domain.fibre next).symm argument)⟩⟩ : first.extension.base.Elements) :=
    congrArg (fun a => (⟨later.1, ⟨later.2, a⟩⟩ : first.extension.base.Elements))
      (domain.symm.naturality step argument)
  have underlying : ((PowerClassPresheafProducts.elementMap domain.comprehensionInverse).map bodyStep).1 = oldStep.1 := by
    change ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
      (argumentMap second.family step argument)).1 =
      ((Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements first.family).map
        (argumentMap first.family step ((domain.fibre next).symm argument))).1
    rw [Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying,
      Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements_underlying]
    rfl
  have arrows := arrow_heq rfl targets
    ((PowerClassPresheafProducts.elementMap domain.comprehensionInverse).map bodyStep) oldStep (heq_of_eq underlying)
  have moved := map_heq left.family rfl targets _ _ arrows
    (function.app next restriction ((domain.fibre next).symm argument)) _ (heq_of_eq rfl)
  exact eq_of_heq (moved.trans ((heq_of_eq (function.naturality step restriction ((domain.fibre next).symm argument))).trans
    (app_heq point function later (restriction ≫ step) (domain.symm.naturality step argument).symm)))

variable (arrows : (start finish : Cᵒᵖ) → ArgumentCoding (start ⟶ finish))

def piForward (point : context.base.Elements) (function : (first.pi left arrows).family.obj point) :
    (second.pi right arrows).family.obj point where
  app next restriction argument :=
    (bodyBackward domain body).symm.fibre ⟨next.1, ⟨next.2, argument⟩⟩
      (function.app next restriction ((domain.fibre next).symm argument))
  naturality {next later} step restriction argument :=
    let bodyStep :=
      (Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge.displayedToTotalElements second.family).map
        (argumentMap second.family step argument);
    ((bodyBackward domain body).symm.naturality bodyStep
      (function.app next restriction ((domain.fibre next).symm argument))).symm.trans
        (congrArg ((bodyBackward domain body).symm.fibre ⟨later.1, ⟨later.2, second.family.map step argument⟩⟩)
          (mappedApplication domain point function step restriction argument))

theorem piForward_natural {point next : context.base.Elements} (step : point ⟶ next)
    (function : (first.pi left arrows).family.obj point) :
    piForward domain body arrows next ((first.pi left arrows).family.map step function) =
      (second.pi right arrows).family.map step (piForward domain body arrows point function) := by
  apply DependentSection.ext
  intro _ _ _
  rfl

def futureForward (point : context.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments first.family point) :
    PowerClassContextualMaterialization.FutureArguments second.family point :=
  ⟨argument.1, domain.fibre argument.1.1 argument.2⟩

def futureBackward (point : context.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments second.family point) :
    PowerClassContextualMaterialization.FutureArguments first.family point :=
  ⟨argument.1, (domain.fibre argument.1.1).symm argument.2⟩

theorem futureBackward_forward (point : context.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments first.family point) :
    futureBackward domain point (futureForward domain point argument) = argument :=
  Sigma.ext rfl (heq_of_eq ((domain.fibre argument.1.1).symm_apply_apply argument.2))

theorem futureBackward_reading (point : context.base.Elements)
    (argument : PowerClassContextualMaterialization.FutureArguments second.family point) :
    (first.futureCoding arrows point).reading (futureBackward domain point argument) =
      (second.futureCoding arrows point).reading argument := by
  have original := ArgumentCoding.contextual_reading context.labels
    (MaterialFamily.elementArrowCoding arrows) first.family first.termCoding point
    (futureBackward domain point argument)
  have target := ArgumentCoding.contextual_reading context.labels
    (MaterialFamily.elementArrowCoding arrows) second.family second.termCoding point argument
  have members : (first.termCoding argument.1.1).reading ((domain.fibre argument.1.1).symm argument.2) =
      (second.termCoding argument.1.1).reading argument.2 :=
    ((PresentedType.mk_termGraph _ _).trans (domain.symm.value argument.1.1 argument.2)).trans
      (PresentedType.mk_termGraph _ _).symm
  exact original.trans ((congrArg (HSet.kpair (context.labels.reading argument.1.1))
    (congrArg (HSet.kpair ((MaterialFamily.elementArrowCoding arrows point argument.1.1).reading argument.1.2)) members)).trans target.symm)

private def rowValue (source : MaterialFamily context) (output : MaterialFamily source.extension)
    (point : context.base.Elements) (function : (source.pi output arrows).family.obj point)
    (argument : PowerClassContextualMaterialization.FutureArguments source.family point) : HSet.{u} :=
  HSet.kpair ((source.futureCoding arrows point).reading argument)
    ((output.model ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩).value
      (function.app argument.1.1 argument.1.2 argument.2))

private theorem row_membership (source : MaterialFamily context) (output : MaterialFamily source.extension)
    (point : context.base.Elements) (function : (source.pi output arrows).family.obj point) (row : HSet.{u}) :
    row ∈ ((source.pi output arrows).model point).value function ↔
      ∃ argument, rowValue arrows source output point function argument = row :=
  LabelledDependentProducts.mem_functionGraph_iff (source.futureCoding arrows point)
    (source.futureOutputs output point)
    (fun argument => function.app argument.1.1 argument.1.2 argument.2) row

private theorem piForward_row (point : context.base.Elements) (function : (first.pi left arrows).family.obj point)
    (argument : PowerClassContextualMaterialization.FutureArguments second.family point) :
    rowValue arrows second right point (piForward domain body arrows point function) argument =
      rowValue arrows first left point function (futureBackward domain point argument) :=
  congrArg₂ HSet.kpair (futureBackward_reading domain arrows point argument).symm
    ((bodyBackward domain body).symm.value ⟨argument.1.1.1, ⟨argument.1.1.2, argument.2⟩⟩
      (function.app argument.1.1 argument.1.2 ((domain.fibre argument.1.1).symm argument.2)))

/-- Every complete future graph row retains the actual context, arrow,
argument label and dependent result value through the equivalence. -/
theorem piForward_value (point : context.base.Elements) (function : (first.pi left arrows).family.obj point) :
    ((second.pi right arrows).model point).value (piForward domain body arrows point function) =
      ((first.pi left arrows).model point).value function := by
  apply HSet.ext
  intro row
  constructor
  · intro belongs
    obtain ⟨argument, represented⟩ := (row_membership arrows second right point _ row).mp belongs
    exact (row_membership arrows first left point function row).mpr
      ⟨futureBackward domain point argument, (piForward_row domain body arrows point function argument).symm.trans represented⟩
  · intro belongs
    obtain ⟨argument, represented⟩ := (row_membership arrows first left point function row).mp belongs
    exact (row_membership arrows second right point _ row).mpr
      ⟨futureForward domain point argument,
        (piForward_row domain body arrows point function (futureForward domain point argument)).trans
          ((congrArg (rowValue arrows first left point function) (futureBackward_forward domain point argument)).trans represented)⟩

def piFibre (point : context.base.Elements) : (first.pi left arrows).family.obj point ≃
    (second.pi right arrows).family.obj point where
  toFun := piForward domain body arrows point
  invFun := piForward domain.symm (bodyBackward domain body) arrows point
  left_inv function := ((first.pi left arrows).model point).value_injective
    ((piForward_value domain.symm (bodyBackward domain body) arrows point _).trans
      (piForward_value domain body arrows point function))
  right_inv function := ((second.pi right arrows).model point).value_injective
    ((piForward_value domain body arrows point _).trans
      (piForward_value domain.symm (bodyBackward domain body) arrows point function))

def pi : Equivalence (first.pi left arrows) (second.pi right arrows) where
  fibre := piFibre domain body arrows
  naturality := piForward_natural domain body arrows
  value := piForward_value domain body arrows

theorem pi_application_value (point : context.base.Elements)
    (function : (first.pi left arrows).family.obj point)
    (next : context.base.Elements) (restriction : point ⟶ next) (argument : second.family.obj next) :
    (right.model ⟨next.1, ⟨next.2, argument⟩⟩).value
      ((pi domain body arrows).fibre point function |>.app next restriction argument) =
    (left.model ⟨next.1, ⟨next.2, (domain.fibre next).symm argument⟩⟩).value
      (function.app next restriction ((domain.fibre next).symm argument)) :=
  (bodyBackward domain body).symm.value ⟨next.1, ⟨next.2, argument⟩⟩ _

def identityFibre (left right : first.family.sections) (point : context.base.Elements) :
    (first.identity left right).family.obj point ≃
      (second.identity (domain.sections left) (domain.sections right)).family.obj point where
  toFun witness := PresheafIdentityWitness.encode
    (congrArg (domain.fibre point) (PresheafIdentityWitness.decode witness))
  invFun witness := PresheafIdentityWitness.encode
    ((domain.fibre point).injective (PresheafIdentityWitness.decode witness))
  left_inv witness := by
    change (PresheafIdentityWitness.encode _ : PresheafIdentityWitness.Witness _ _) = witness
    exact Subsingleton.elim _ _
  right_inv witness := by
    change (PresheafIdentityWitness.encode _ : PresheafIdentityWitness.Witness _ _) = witness
    exact Subsingleton.elim _ _

theorem identityFibre_value (left right : first.family.sections) (point : context.base.Elements)
    (witness : (first.identity left right).family.obj point) :
    ((second.identity (domain.sections left) (domain.sections right)).model point).value
      (identityFibre domain left right point witness) =
    ((first.identity left right).model point).value witness :=
  (PresheafIdentityWitness.member_condition (identityFibre domain left right point witness)).1.trans
    (PresheafIdentityWitness.member_condition witness).1.symm

/-- Discrete identity transports both endpoints through the actual natural
section equivalence. The witness represents ordinary endpoint equality. -/
def identity (left right : first.family.sections) :
    Equivalence (first.identity left right)
      (second.identity (domain.sections left) (domain.sections right)) where
  fibre := identityFibre domain left right
  naturality _ _ := by
    change (_ : PresheafIdentityWitness.Witness _ _) = _
    exact Subsingleton.elim _ _
  value := identityFibre_value domain left right

theorem identity_endpoints_reflected (left right : first.family.sections)
    (point : context.base.Elements) :
    (domain.sections left).val point = (domain.sections right).val point ↔ left.val point = right.val point :=
  (domain.fibre point).injective.eq_iff

namespace Controls

open ContextualMaterialEquivalence.Controls

def unitBody : MaterialFamily pairFamily.extension := MaterialFamily.unit pairFamily.extension

def transportedUnitBody : MaterialFamily reversedDictionary.extension :=
  coordinateEquivalence.transportBody unitBody

def unitBodyComparison : Equivalence unitBody
    (transportedUnitBody.reindex (other := pairFamily.extension) coordinateEquivalence.comprehension) :=
  ofEquality (coordinateEquivalence.transportBody_roundtrip unitBody).symm

def mixedDependentPair : (pairFamily.sigma unitBody).family.obj Growing.newPoint :=
  ⟨mixedPair, ⟨PUnit.unit⟩⟩

theorem transported_sigma_changes_first :
    ((sigma coordinateEquivalence unitBodyComparison).fibre Growing.newPoint mixedDependentPair).1 ≠
      mixedDependentPair.1 := coordinate_swap_changes_pair

theorem transported_sigma_preserves_material_pair :
    ((reversedDictionary.sigma transportedUnitBody).model Growing.newPoint).value
      ((sigma coordinateEquivalence unitBodyComparison).fibre Growing.newPoint mixedDependentPair) =
    ((pairFamily.sigma unitBody).model Growing.newPoint).value mixedDependentPair :=
  (sigma coordinateEquivalence unitBodyComparison).value Growing.newPoint mixedDependentPair

/-- The same coordinate permutation with the old dictionary changes the
actual material value; natural fibre bijections alone are insufficient. -/
theorem untransported_dictionary_changes_value :
    (pairFamily.model Growing.newPoint).value (swap Growing.newPoint mixedPair) ≠
      (pairFamily.model Growing.newPoint).value mixedPair :=
  fun same => coordinate_swap_changes_pair ((pairFamily.model Growing.newPoint).value_injective same)

end Controls

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialTypeFormerEquivalence
