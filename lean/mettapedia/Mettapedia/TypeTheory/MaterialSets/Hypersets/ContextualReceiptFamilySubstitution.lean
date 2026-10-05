import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilyModels
import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence

/-!
# Complete future material dictionaries under parameter substitution

Independent product formation labels each actual future world, arrow and
argument. Parameter substitution changes the retained external parameter,
while its naturality square identifies those complete typed arguments and
result readings. Both directions compare whole function graphs.

The hereditary W comparison is the existing constructed native signature
comparison. Material members are transported through their independent
decoders and this actual equivalence. Its context square compares full
restriction, not merely present shape support.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilySubstitution

open CategoryTheory Mettapedia.TypeTheory
open ContextualWitnessCover ContextualSmallFamilyTypeFormers
open ContextualSmallFamilyTypeFormerCoherence PowerClassPresheafBaseChange
open ContextualReceiptFamilyModels

universe u v w
variable {D : Type u} [Category.{u} D] {base : D ⥤ Type v} {other : D ⥤ Type w}
variable (domain : base.Elements ⥤ Type u) (models : Model domain)
variable (body : domain.Elements ⥤ Type u) (bodyModels : (point : domain.Elements) → PresentedType (body.obj point))
variable (worlds : ArgumentCoding D) (arrows : (first second : D) → ArgumentCoding (first ⟶ second))
variable (change : NaturalHom other base)

def modelsUnder : Model (domainUnder change domain) :=
  fun point => models ((ContextualSmallFamilyUniverse.elementMap change).obj point)

def bodyModelsUnder (point : (domainUnder change domain).Elements) :
    PresentedType ((bodyUnder change domain body).obj point) :=
  bodyModels ((argumentsUnder change domain).obj point)

private def elementsEquiv {E : Type u} [Category.{u} E]
    {first second : E ⥤ Type u} (same : first = second) :
    first.Elements ≃ second.Elements where
  toFun := (Cat.elementsTransport same).obj
  invFun := (ContextualSmallFamilyUniverse.typeEqualityEquiv
    (congrArg Functor.Elements same.symm)).toFun
  left_inv := by cases same; intro argument; rfl
  right_inv := by cases same; intro argument; rfl

def argumentEquiv (point : other.Elements) :
    (futureDomain (domainUnder change domain) point).Elements ≃
      (futureDomain domain ((ContextualSmallFamilyUniverse.elementMap change).obj point)).Elements :=
  elementsEquiv (futureDomain_change change domain point)

theorem futureCoding_reading (point : base.Elements) (argument : (futureDomain domain point).Elements) :
    (futureCoding domain models worlds arrows point).reading argument =
      HSet.kpair (HSet.kpair (worlds.reading argument.1.1) ((arrows point.1 argument.1.1).reading argument.1.2))
        ((models ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj argument.1)).value argument.2) := by
  dsimp only [ArgumentCoding.reading, futureCoding, ArgumentCoding.sigma, futureWorldCoding, termCoding]
  rw [AccessiblePointedGraph.mk_kpairGraph, AccessiblePointedGraph.mk_kpairGraph]
  exact congrArg (HSet.kpair
    (HSet.kpair (worlds.reading argument.1.1) ((arrows point.1 argument.1.1).reading argument.1.2)))
      (PresentedType.mk_termGraph
        (models ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).obj argument.1)) argument.2)

theorem futureCoding_change (point : other.Elements)
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    (futureCoding domain models worlds arrows ((ContextualSmallFamilyUniverse.elementMap change).obj point)).reading
        ((argumentEquiv domain change point) argument) =
      (futureCoding (domainUnder change domain) (modelsUnder domain models change) worlds arrows point).reading argument := by
  rw [futureCoding_reading, futureCoding_reading]
  have futures := futureArgumentChange_context change domain point argument
  have points := congrArg Sigma.fst (futureArgumentChange_embedding change domain point argument)
  have terms := model_value_heq models points _ _ (futureArgumentChange_value change domain point argument)
  have labels := congrArg (fun future : Future.Objects point.1 =>
    HSet.kpair (worlds.reading future.1) ((arrows point.1 future.1).reading future.2)) futures
  exact congrArg₂ HSet.kpair labels terms

theorem output_change (point : other.Elements)
    (function : ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point))
    (argument : (futureDomain (domainUnder change domain) point).Elements) :
    (outputModels domain body bodyModels ((ContextualSmallFamilyUniverse.elementMap change).obj point)
        ((argumentEquiv domain change point) argument)).value
        (function.val ((argumentEquiv domain change point) argument)) =
      (outputModels (domainUnder change domain) (bodyUnder change domain body)
        (bodyModelsUnder domain body bodyModels change) point argument).value
        ((productComparison change domain body point function).val argument) :=
  model_value_heq bodyModels (futureArgumentChange_embedding change domain point argument)
    _ _ (productComparison_value change domain body point function argument).symm

/-- Substitution compares every graph row in both directions. No current
value or support-only criterion determines this equality. -/
theorem pi_value (point : other.Elements)
    (function : ProductAt domain body ((ContextualSmallFamilyUniverse.elementMap change).obj point)) :
    (piModel (domainUnder change domain) (modelsUnder domain models change)
      (bodyUnder change domain body) (bodyModelsUnder domain body bodyModels change)
      worlds arrows point).value (productComparison change domain body point function) =
        (piModel domain models body bodyModels worlds arrows
          ((ContextualSmallFamilyUniverse.elementMap change).obj point)).value function := by
  apply HSet.ext
  intro row
  change row ∈ HSet.mk (LabelledDependentProducts.functionGraph _ _ _) ↔
    row ∈ HSet.mk (LabelledDependentProducts.functionGraph _ _ _)
  rw [LabelledDependentProducts.mem_functionGraph_iff, LabelledDependentProducts.mem_functionGraph_iff]
  constructor
  · rintro ⟨argument, same⟩
    refine ⟨argumentEquiv domain change point argument, ?_⟩
    exact (congrArg₂ HSet.kpair (futureCoding_change domain models worlds arrows change point argument)
      (output_change domain body bodyModels change point function argument)).trans same
  · rintro ⟨argument, same⟩
    let original := (argumentEquiv domain change point).symm argument
    refine ⟨original, ?_⟩
    have recovered := (argumentEquiv domain change point).apply_symm_apply argument
    have labels := futureCoding_change domain models worlds arrows change point original
    have outputs := output_change domain body bodyModels change point function original
    rw [recovered] at labels outputs
    exact (congrArg₂ HSet.kpair labels outputs).symm.trans same

/-- Whole formation stability follows from the actual two-way native
comparison and preservation of every encoded row. -/
theorem pi_carrier (point : other.Elements) :
    (piModel (domainUnder change domain) (modelsUnder domain models change)
      (bodyUnder change domain body) (bodyModelsUnder domain body bodyModels change)
      worlds arrows point).carrier =
    (piModel domain models body bodyModels worlds arrows
      ((ContextualSmallFamilyUniverse.elementMap change).obj point)).carrier := by
  let old := piModel domain models body bodyModels worlds arrows
    ((ContextualSmallFamilyUniverse.elementMap change).obj point)
  let new := piModel (domainUnder change domain) (modelsUnder domain models change)
    (bodyUnder change domain body) (bodyModelsUnder domain body bodyModels change) worlds arrows point
  apply HSet.ext
  intro value
  constructor
  · intro member
    let term := (productComparison change domain body point).symm (new.decode ⟨value, member⟩)
    have encoded := (pi_value domain models body bodyModels worlds arrows change point term).symm
    have recovered := congrArg new.value
      ((productComparison change domain body point).apply_symm_apply (new.decode ⟨value, member⟩))
    have valueEq : old.value term = value := encoded.trans (recovered.trans (new.value_decode ⟨value, member⟩))
    exact valueEq ▸ old.value_mem term
  · intro member
    let term := old.decode ⟨value, member⟩
    have valueEq : new.value (productComparison change domain body point term) = value :=
      (pi_value domain models body bodyModels worlds arrows change point term).trans (old.value_decode ⟨value, member⟩)
    exact valueEq ▸ new.value_mem (productComparison change domain body point term)

abbrev oldWModels : Model (ContextualSmallFamilyWTypes.w domain body) :=
  wModel domain models body bodyModels worlds arrows

abbrev newWModels : Model
    (ContextualSmallFamilyWTypes.w (domainUnder change domain) (bodyUnder change domain body)) :=
  wModel (domainUnder change domain) (modelsUnder domain models change)
    (bodyUnder change domain body) (bodyModelsUnder domain body bodyModels change) worlds arrows

/-- The independent graph decoders compare material W members through the
constructed whole-signature tree equivalence. -/
def wMemberComparison (point : other.Elements) :
    {value : HSet.{u} // value ∈
      (oldWModels domain models body bodyModels worlds arrows
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)).carrier} ≃
    {value : HSet.{u} // value ∈
      (newWModels domain models body bodyModels worlds arrows change point).carrier} :=
  (oldWModels domain models body bodyModels worlds arrows
    ((ContextualSmallFamilyUniverse.elementMap change).obj point)).decode.trans
      ((ContextualSmallFamilyWSubstitution.wComparison change domain body point).trans
        (newWModels domain models body bodyModels worlds arrows change point).decode.symm)

theorem wMemberComparison_decode (point : other.Elements)
    (member : {value : HSet.{u} // value ∈
      (oldWModels domain models body bodyModels worlds arrows
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)).carrier}) :
    (newWModels domain models body bodyModels worlds arrows change point).decode
      (wMemberComparison domain models body bodyModels worlds arrows change point member) =
    ContextualSmallFamilyWSubstitution.wComparison change domain body point
      ((oldWModels domain models body bodyModels worlds arrows
        ((ContextualSmallFamilyUniverse.elementMap change).obj point)).decode member) :=
  (newWModels domain models body bodyModels worlds arrows change point).decode.apply_symm_apply _

/-- The material comparison commutes with the full contextual restriction,
including every hereditary future branch. -/
theorem wMemberComparison_restriction {first second : other.Elements} (step : first ⟶ second)
    (member : {value : HSet.{u} // value ∈
      (oldWModels domain models body bodyModels worlds arrows
        ((ContextualSmallFamilyUniverse.elementMap change).obj first)).carrier}) :
    memberMap (ContextualSmallFamilyWTypes.w (domainUnder change domain) (bodyUnder change domain body))
        (newWModels domain models body bodyModels worlds arrows change) step
        (wMemberComparison domain models body bodyModels worlds arrows change first member) =
      wMemberComparison domain models body bodyModels worlds arrows change second
        (memberMap (ContextualSmallFamilyWTypes.w domain body)
          (oldWModels domain models body bodyModels worlds arrows)
          ((ContextualSmallFamilyUniverse.elementMap change).map step) member) := by
  apply (newWModels domain models body bodyModels worlds arrows change second).decode.injective
  rw [memberMap_decode, wMemberComparison_decode, wMemberComparison_decode, memberMap_decode]
  exact (ContextualSmallFamilyWSubstitution.wComparison_natural change domain body step _).symm

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReceiptFamilySubstitution
