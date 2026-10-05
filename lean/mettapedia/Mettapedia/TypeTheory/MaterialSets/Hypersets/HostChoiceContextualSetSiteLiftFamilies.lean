import Mettapedia.TypeTheory.ContextualFutureSiteLift
import Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftCoherence
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualHypersetFamilyClosure

/-!
# Actual argument-dependent member families across a model lift

An arbitrary original parameter map supplies a parent set. Its member
comprehension has a constructed natural inverse comparison with the actual
upper member comprehension. An arbitrary set-valued body on that original
comprehension is read after this inverse and embedded into the upper model.
Thus the independently formed upper body depends on the actual argument.

Both actual member signatures retain material values through their decoders.
The inverse member recovery and the actual set models explicitly inherit
external host Choice. No assertion that all upper bodies descend is made.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilies

open _root_.CategoryTheory
open Mettapedia.TypeTheory ContextualWitnessCover
open HostChoiceContextualSetSiteLift HostChoiceContextualSetSiteLiftCoherence
open HostChoiceContextualSetInterpretation

universe u v w h
variable {D : Type u} [Category.{u} D] {P : D ⥤ Type v}
variable (parent : NaturalHom P (lowerSets (D := D)))

noncomputable abbrev lowerDomain := HostChoiceContextualHypersetFamilyClosure.domain parent

noncomputable def raisedParent : NaturalHom (ContextualFutureSiteLift.base P) (source (D := D)) where
  app point value := parent.app point.down value
  naturality step value := parent.naturality step.down value

noncomputable def upperParent : NaturalHom (ContextualFutureSiteLift.base P) (upperSets (D := D)) :=
  (raisedParent parent).comp embedding

noncomputable abbrev upperDomain := HostChoiceContextualHypersetFamilyClosure.domain (upperParent parent)
noncomputable abbrev raisedDomain := ContextualFutureSiteLift.family P (lowerDomain parent)

noncomputable def domainEquiv (point : (ContextualFutureSiteLift.base P).Elements) :
    (raisedDomain parent).obj point ≃ (upperDomain parent).obj point where
  toFun code := codeEquiv ⟨point.1, (raisedParent parent).app point.1 point.2⟩ code.down
  invFun code := ULift.up ((codeEquiv ⟨point.1, (raisedParent parent).app point.1 point.2⟩).symm code)
  left_inv code := ULift.ext _ _ ((codeEquiv ⟨point.1, (raisedParent parent).app point.1 point.2⟩).symm_apply_apply code.down)
  right_inv code := (codeEquiv ⟨point.1, (raisedParent parent).app point.1 point.2⟩).apply_symm_apply code

theorem domain_natural {first second : (ContextualFutureSiteLift.base P).Elements}
    (step : first ⟶ second) (code : (raisedDomain parent).obj first) :
    (upperDomain parent).map step (domainEquiv parent first code) =
      domainEquiv parent second ((raisedDomain parent).map step code) :=
  show _ from code_natural ((ContextualSmallFamilyUniverse.elementMap (raisedParent parent)).map step) code.down

noncomputable def domainForward : WiderPresheafDependentFunctions.Hom (raisedDomain parent) (upperDomain parent) where
  app point code := domainEquiv parent point code
  naturality step code := domain_natural parent step code

noncomputable def domainBackward : WiderPresheafDependentFunctions.Hom (upperDomain parent) (raisedDomain parent) where
  app point := (domainEquiv parent point).symm
  naturality {first second} step code := by
    apply (domainEquiv parent second).injective
    exact (domain_natural parent step ((domainEquiv parent first).symm code)).symm.trans
      ((congrArg ((upperDomain parent).map step) ((domainEquiv parent first).apply_symm_apply code)).trans
        ((domainEquiv parent second).apply_symm_apply ((upperDomain parent).map step code)).symm)

noncomputable def comprehensionDown : NaturalHom (ContextualSmallFamilyUniverse.total (upperDomain parent))
    (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent)) where
  app point receipt := ⟨receipt.1, ((domainEquiv parent ⟨point, receipt.1⟩).symm receipt.2).down⟩
  naturality {first second} step receipt := by
    dsimp only [ContextualSmallFamilyUniverse.total, ContextualSmallFamilyUniverse.totalMap,
      ContextualFutureSiteLift.base, PresheafSiteLift.compose]
    refine Sigma.ext rfl ?_
    exact heq_of_eq ((backwardUnder (raisedParent parent)).naturality
      (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
        ⟨first, receipt.1⟩ ⟨second, P.map step.down receipt.1⟩ step rfl) receipt.2)

noncomputable def comprehensionUp : NaturalHom
    (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent))
    (ContextualSmallFamilyUniverse.total (upperDomain parent)) where
  app point receipt := ⟨receipt.1, domainEquiv parent ⟨point, receipt.1⟩ (ULift.up receipt.2)⟩
  naturality {first second} step receipt := by
    dsimp only [ContextualSmallFamilyUniverse.total, ContextualSmallFamilyUniverse.totalMap,
      ContextualFutureSiteLift.base, PresheafSiteLift.compose]
    refine Sigma.ext rfl ?_
    exact heq_of_eq (domain_natural parent
      (CategoryOfElements.homMk (F := ContextualFutureSiteLift.base P)
        ⟨first, receipt.1⟩ ⟨second, P.map step.down receipt.1⟩ step rfl) (ULift.up receipt.2))

theorem comprehension_down_up : (comprehensionDown parent).comp (comprehensionUp parent) =
    ContextualSmallMapConstructions.identity (ContextualSmallFamilyUniverse.total (upperDomain parent)) := by
  apply NaturalHom.ext
  intro point receipt
  dsimp only [NaturalHom.comp, comprehensionDown, comprehensionUp, ContextualSmallMapConstructions.identity]
  refine Sigma.ext rfl ?_
  exact heq_of_eq ((domainEquiv parent _).apply_symm_apply receipt.2)

theorem comprehension_up_down : (comprehensionUp parent).comp (comprehensionDown parent) =
    ContextualSmallMapConstructions.identity
      (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent)) := by
  apply NaturalHom.ext
  intro point receipt
  dsimp only [NaturalHom.comp, comprehensionDown, comprehensionUp, ContextualSmallMapConstructions.identity]
  refine Sigma.ext rfl ?_
  exact heq_of_eq (congrArg ULift.down
    ((domainEquiv parent ⟨point, receipt.1⟩).symm_apply_apply (ULift.up receipt.2)))

noncomputable def signatureContext : (raisedDomain parent).Elements ⥤ (upperDomain parent).Elements where
  obj point := ⟨point.1, domainEquiv parent point.1 point.2⟩
  map {first second} step := ⟨step.1,
    (domain_natural parent step.1 first.2).trans (congrArg (domainEquiv parent second.1) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def inverseSignatureContext : (upperDomain parent).Elements ⥤ (raisedDomain parent).Elements where
  obj point := ⟨point.1, (domainEquiv parent point.1).symm point.2⟩
  map {first second} step := ⟨step.1,
    ((domainBackward parent).naturality step.1 first.2).trans
      (congrArg ((domainEquiv parent second.1).symm) step.2)⟩
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def domainSections : (lowerDomain parent).sections ≃ (upperDomain parent).sections :=
  (ContextualFutureSiteLift.sections P (lowerDomain parent)).trans {
    toFun := (domainForward parent).mapSection
    invFun := (domainBackward parent).mapSection
    left_inv term := by
      apply Subtype.ext
      funext point
      exact (domainEquiv parent point).symm_apply_apply (term.val point)
    right_inv term := by
      apply Subtype.ext
      funext point
      exact (domainEquiv parent point).apply_symm_apply (term.val point) }

variable (bodyMap : NaturalHom (HostChoiceContextualHypersetFamilyClosure.comprehension parent) (lowerSets (D := D)))

noncomputable def raisedBodyMap : NaturalHom
    (ContextualFutureSiteLift.base (HostChoiceContextualHypersetFamilyClosure.comprehension parent))
    (source (D := D)) where
  app point receipt := bodyMap.app point.down receipt
  naturality step receipt := bodyMap.naturality step.down receipt

noncomputable def upperBodyMap : NaturalHom (ContextualSmallFamilyUniverse.total (upperDomain parent))
    (upperSets (D := D)) :=
  (comprehensionDown parent).comp ((raisedBodyMap parent bodyMap).comp embedding)

noncomputable abbrev lowerBody := HostChoiceContextualHypersetFamilyClosure.body parent bodyMap
noncomputable abbrev raisedBody := ContextualFutureSiteLift.body P (lowerDomain parent) (lowerBody parent bodyMap)
noncomputable abbrev upperBody := HostChoiceContextualHypersetFamilyClosure.body (upperParent parent) (upperBodyMap parent bodyMap)

theorem upperBodyMap_forward (point : (ContextualFutureSiteLift.base P).Elements)
    (argument : (raisedDomain parent).obj point) :
    (upperBodyMap parent bodyMap).app point.1 ⟨point.2, domainEquiv parent point argument⟩ =
      embedding.app point.1 (bodyMap.app point.1.down ⟨point.2, argument.down⟩) := by
  apply congrArg (embedding.app point.1)
  apply congrArg (bodyMap.app point.1.down)
  dsimp only [comprehensionDown]
  refine Sigma.ext rfl ?_
  exact heq_of_eq (congrArg ULift.down ((domainEquiv parent point).symm_apply_apply argument))

theorem memberCode_cast_value (point : UpperSite (D := D))
    {first second : upperSets.obj point} (same : first = second)
    (code : HostChoiceContextualHypersetModel.memberFamily.obj ⟨point, first⟩) :
    (HostChoiceContextualHypersetModel.memberDecoder ⟨point, second⟩
      (ContextualSmallFamilyUniverse.typeEqualityEquiv
        (congrArg (fun value : upperSets.obj point =>
          HostChoiceContextualHypersetModel.memberFamily.obj ⟨point, value⟩) same) code)).val =
      (HostChoiceContextualHypersetModel.memberDecoder ⟨point, first⟩ code).val := by
  cases same
  rfl

noncomputable def bodyEquiv (argument : (raisedDomain parent).Elements) :
    (raisedBody parent bodyMap).obj argument ≃
      (upperBody parent bodyMap).obj ((signatureContext parent).obj argument) :=
  let smaller : (raisedBody parent bodyMap).obj argument ≃
      (lowerBody parent bodyMap).obj ((ContextualFutureSiteLift.displayedDown P (lowerDomain parent)).obj argument) := {
    toFun code := code.down
    invFun := ULift.up
    left_inv _ := rfl
    right_inv _ := rfl }
  let original : (source (D := D)).Elements :=
    ⟨argument.1.1, bodyMap.app argument.1.1.down ⟨argument.1.2, argument.2.down⟩⟩
  smaller.trans ((codeEquiv original).trans
    (ContextualSmallFamilyUniverse.typeEqualityEquiv
      (congrArg (fun value : upperSets.obj argument.1.1 =>
        HostChoiceContextualHypersetModel.memberFamily.obj ⟨argument.1.1, value⟩)
        (upperBodyMap_forward parent bodyMap argument.1 argument.2).symm)))

theorem bodyEquiv_value (argument : (raisedDomain parent).Elements)
    (code : (raisedBody parent bodyMap).obj argument) :
    embedding.app argument.1.1
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
        ((ContextualFutureSiteLift.displayedDown P (lowerDomain parent)).obj argument) code.down).val =
      (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
        ((signatureContext parent).obj argument) (bodyEquiv parent bodyMap argument code)).val := by
  have original := code_value (D := D)
    (show (source (D := D)).Elements from
      ⟨argument.1.1, bodyMap.app argument.1.1.down ⟨argument.1.2, argument.2.down⟩⟩) code.down
  have moved := memberCode_cast_value argument.1.1
    (upperBodyMap_forward parent bodyMap argument.1 argument.2).symm
    (codeEquiv ⟨argument.1.1, bodyMap.app argument.1.1.down ⟨argument.1.2, argument.2.down⟩⟩ code.down)
  exact original.trans moved.symm

set_option maxHeartbeats 1000000 in
theorem body_natural {first second : (raisedDomain parent).Elements} (step : first ⟶ second)
    (code : (raisedBody parent bodyMap).obj first) :
    (upperBody parent bodyMap).map ((signatureContext parent).map step) (bodyEquiv parent bodyMap first code) =
      bodyEquiv parent bodyMap second ((raisedBody parent bodyMap).map step code) := by
  apply (HostChoiceContextualHypersetFamilyClosure.bodyDecoder (upperParent parent) (upperBodyMap parent bodyMap)
    ((signatureContext parent).obj second)).injective
  apply Subtype.ext
  have upperMoved := HostChoiceContextualHypersetFamilyClosure.bodyDecoder_value_natural
    (upperParent parent) (upperBodyMap parent bodyMap) ((signatureContext parent).map step)
    (bodyEquiv parent bodyMap first code)
  have lowerMoved := HostChoiceContextualHypersetFamilyClosure.bodyDecoder_value_natural parent bodyMap
    ((ContextualFutureSiteLift.displayedDown P (lowerDomain parent)).map step) code.down
  have firstValue := bodyEquiv_value parent bodyMap first code
  have secondValue := bodyEquiv_value parent bodyMap second ((raisedBody parent bodyMap).map step code)
  have natural := (embedding (D := D)).naturality step.1.1
    (HostChoiceContextualHypersetFamilyClosure.bodyDecoder parent bodyMap
      ((ContextualFutureSiteLift.displayedDown P (lowerDomain parent)).obj first) code.down).val
  exact upperMoved.symm.trans
    ((congrArg ((upperSets (D := D)).map step.1.1) firstValue.symm).trans
      (natural.trans ((congrArg (embedding.app second.1.1) lowerMoved).trans secondValue)))

noncomputable def bodyForward : WiderPresheafDependentFunctions.Hom (raisedBody parent bodyMap)
    (ContextualSmallFamilyUniverse.restrict (signatureContext parent) (upperBody parent bodyMap)) where
  app argument code := bodyEquiv parent bodyMap argument code
  naturality step code := body_natural parent bodyMap step code

noncomputable def bodyBackward : WiderPresheafDependentFunctions.Hom
    (ContextualSmallFamilyUniverse.restrict (signatureContext parent) (upperBody parent bodyMap))
    (raisedBody parent bodyMap) where
  app argument := (bodyEquiv parent bodyMap argument).symm
  naturality {first second} step code := by
    apply (bodyEquiv parent bodyMap second).injective
    exact (body_natural parent bodyMap step ((bodyEquiv parent bodyMap first).symm code)).symm.trans
      ((congrArg ((upperBody parent bodyMap).map ((signatureContext parent).map step))
        ((bodyEquiv parent bodyMap first).apply_symm_apply code)).trans
        ((bodyEquiv parent bodyMap second).apply_symm_apply
          ((upperBody parent bodyMap).map ((signatureContext parent).map step) code)).symm)

noncomputable def signature : WiderPresheafSignatureEquivalence.Signature
    (shape := raisedDomain parent) (nextShape := upperDomain parent)
    (position := raisedBody parent bodyMap) (nextPosition := upperBody parent bodyMap) where
  shapes := domainEquiv parent
  shape_natural step label := (domain_natural parent step label).symm
  positions point label := bodyEquiv parent bodyMap ⟨point, label⟩
  position_natural {first second} step label value := by
    have original := body_natural parent bodyMap
      (WiderPresheafDependentFunctions.argumentMap (raisedDomain parent) step label) value
    have target : ((signatureContext parent).obj
        (⟨second, (raisedDomain parent).map step label⟩ : (raisedDomain parent).Elements)) =
        (⟨second, (upperDomain parent).map step (domainEquiv parent first label)⟩ : (upperDomain parent).Elements) :=
      Sigma.ext rfl (heq_of_eq (domain_natural parent step label).symm)
    have arrows := ContextualSmallFamilyTypeFormers.elementArrow_heq rfl target
      ((signatureContext parent).map (WiderPresheafDependentFunctions.argumentMap (raisedDomain parent) step label))
      (WiderPresheafDependentFunctions.argumentMap (upperDomain parent) step (domainEquiv parent first label)) HEq.rfl
    exact (heq_of_eq original.symm).trans
      (ContextualSmallFamilyUniverse.familyMap_heq (upperBody parent bodyMap) rfl target _ _ arrows
        (bodyEquiv parent bodyMap ⟨first, label⟩ value) (bodyEquiv parent bodyMap ⟨first, label⟩ value) HEq.rfl)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetSiteLiftFamilies
