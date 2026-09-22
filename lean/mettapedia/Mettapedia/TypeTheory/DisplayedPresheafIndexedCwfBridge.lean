import Mettapedia.TypeTheory.DisplayedPresheafComprehension
import Mettapedia.TypeTheory.CategoryIndexedFamilyCwf

/-!
# Presheaf total contexts and indexed-family comprehension

A displayed presheaf family is a functor on the category of elements of its
base. Its indexed-family comprehension therefore has objects consisting of a
context, a base value, and evidence. The category of elements of the total
presheaf has the same data, grouped differently. The comparison below keeps
the actual arrows and their evidence-transport conditions, not only an
objectwise bijection.

This is a semantic context comparison. It does not identify an authored
Prime context category with a completed classifying theory.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension

universe uContext vContext uBase uFibre

variable {Context : Type uContext} [Category.{vContext} Context]
variable {base : Face.{uContext, vContext, uBase} Context}
variable (family : DisplayedFamily.{uContext, vContext, uBase, uFibre} base)

/-- Reassociate the object of a total presheaf's element category with the
corresponding object of the displayed family's element category. -/
def totalElementsObjectEquiv :
    (totalSpace family).Elements ≃ family.Elements where
  toFun
    | ⟨context, ⟨value, evidence⟩⟩ => ⟨⟨context, value⟩, evidence⟩
  invFun
    | ⟨⟨context, value⟩, evidence⟩ => ⟨context, ⟨value, evidence⟩⟩
  left_inv
    | ⟨_, ⟨_, _⟩⟩ => rfl
  right_inv
    | ⟨⟨_, _⟩, _⟩ => rfl

private def totalArrowToDisplayed
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (value : base.obj source) (evidence : family.obj ⟨source, value⟩)
    (receipt : TotalAt family target)
    (follows : totalMap family substitution ⟨value, evidence⟩ = receipt) :
    (let sourcePoint : family.Elements := ⟨⟨source, value⟩, evidence⟩
     let targetPoint : family.Elements := ⟨⟨target, receipt.1⟩, receipt.2⟩
     sourcePoint ⟶ targetPoint) := by
  cases follows
  exact ⟨CategoryOfElements.homMk _ _ substitution rfl, rfl⟩

private theorem totalArrowToDisplayed_underlying
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (value : base.obj source) (evidence : family.obj ⟨source, value⟩)
    (receipt : TotalAt family target)
    (follows : totalMap family substitution ⟨value, evidence⟩ = receipt) :
    ((totalArrowToDisplayed family substitution value evidence receipt follows).val).val =
      substitution := by
  cases follows
  rfl

private def displayedArrowToTotal
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (value : base.obj source) (evidence : family.obj ⟨source, value⟩)
    (receipt : TotalAt family target)
    (followsBase : base.map substitution value = receipt.1)
    (followsEvidence :
      family.map (CategoryOfElements.homMk _ _ substitution followsBase)
        evidence = receipt.2) :
    (let sourcePoint : (totalSpace family).Elements :=
      ⟨source, ⟨value, evidence⟩⟩
     let targetPoint : (totalSpace family).Elements := ⟨target, receipt⟩
     sourcePoint ⟶ targetPoint) := by
  rcases receipt with ⟨otherValue, otherEvidence⟩
  cases followsBase
  exact ⟨substitution, congrArg
    (fun evidence => (⟨base.map substitution value, evidence⟩ :
      TotalAt family target)) followsEvidence⟩

private theorem displayedArrowToTotal_underlying
    {source target : Contextᵒᵖ} (substitution : source ⟶ target)
    (value : base.obj source) (evidence : family.obj ⟨source, value⟩)
    (receipt : TotalAt family target)
    (followsBase : base.map substitution value = receipt.1)
    (followsEvidence :
      family.map (CategoryOfElements.homMk _ _ substitution followsBase)
        evidence = receipt.2) :
    (displayedArrowToTotal family substitution value evidence receipt
      followsBase followsEvidence).val = substitution := by
  rcases receipt with ⟨otherValue, otherEvidence⟩
  cases followsBase
  rfl

private def totalHomMap
    {first second : (totalSpace family).Elements}
    (arrow : first ⟶ second) :
    totalElementsObjectEquiv family first ⟶
      totalElementsObjectEquiv family second := by
  rcases first with ⟨source, ⟨value, evidence⟩⟩
  rcases second with ⟨target, receipt⟩
  rcases arrow with ⟨substitution, follows⟩
  change totalMap family substitution ⟨value, evidence⟩ = receipt at follows
  exact totalArrowToDisplayed family substitution value evidence receipt follows

@[simp] private theorem totalHomMap_underlying
    {first second : (totalSpace family).Elements}
    (arrow : first ⟶ second) :
    ((totalHomMap family arrow).val).val = arrow.val := by
  rcases first with ⟨source, ⟨value, evidence⟩⟩
  rcases second with ⟨target, receipt⟩
  rcases arrow with ⟨substitution, follows⟩
  exact totalArrowToDisplayed_underlying family substitution value evidence
    receipt follows

private def displayedHomMap
    {first second : family.Elements}
    (arrow : first ⟶ second) :
    (totalElementsObjectEquiv family).symm first ⟶
      (totalElementsObjectEquiv family).symm second := by
  rcases first with ⟨⟨source, value⟩, evidence⟩
  rcases second with ⟨⟨target, otherValue⟩, otherEvidence⟩
  rcases arrow with ⟨⟨substitution, followsBase⟩, followsEvidence⟩
  exact displayedArrowToTotal family substitution value evidence
    ⟨otherValue, otherEvidence⟩ followsBase followsEvidence

@[simp] private theorem displayedHomMap_underlying
    {first second : family.Elements}
    (arrow : first ⟶ second) :
    (displayedHomMap family arrow).val = arrow.val.val := by
  rcases first with ⟨⟨source, value⟩, evidence⟩
  rcases second with ⟨⟨target, otherValue⟩, otherEvidence⟩
  rcases arrow with ⟨⟨substitution, followsBase⟩, followsEvidence⟩
  exact displayedArrowToTotal_underlying family substitution value evidence
    ⟨otherValue, otherEvidence⟩ followsBase followsEvidence

/-- The object reassociation transports each contextual arrow with its
actual dependent evidence check to an arrow of indexed comprehension. -/
def totalElementsToDisplayed :
    (totalSpace family).Elements ⥤ family.Elements where
  obj := totalElementsObjectEquiv family
  map := totalHomMap family
  map_id point := by
    apply CategoryOfElements.ext family
    apply CategoryOfElements.ext base
    simp
    rfl
  map_comp earlier later := by
    apply CategoryOfElements.ext family
    apply CategoryOfElements.ext base
    simp
    rfl

/-- Regroup an indexed-comprehension arrow into a total-presheaf arrow. -/
def displayedToTotalElements :
    family.Elements ⥤ (totalSpace family).Elements where
  obj := (totalElementsObjectEquiv family).symm
  map := displayedHomMap family
  map_id point := by
    apply CategoryOfElements.ext (totalSpace family)
    simp
    rfl
  map_comp earlier later := by
    apply CategoryOfElements.ext (totalSpace family)
    simp
    rfl

@[simp] theorem totalElementsToDisplayed_underlying
    {first second : (totalSpace family).Elements}
    (arrow : first ⟶ second) :
    (((totalElementsToDisplayed family).map arrow).val).val = arrow.val := by
  rcases first with ⟨source, ⟨value, evidence⟩⟩
  rcases second with ⟨target, receipt⟩
  rcases arrow with ⟨substitution, follows⟩
  exact totalArrowToDisplayed_underlying family substitution value evidence
    receipt follows

@[simp] theorem displayedToTotalElements_underlying
    {first second : family.Elements}
    (arrow : first ⟶ second) :
    ((displayedToTotalElements family).map arrow).val = arrow.val.val := by
  rcases first with ⟨⟨source, value⟩, evidence⟩
  rcases second with ⟨⟨target, otherValue⟩, otherEvidence⟩
  rcases arrow with ⟨⟨substitution, followsBase⟩, followsEvidence⟩
  exact displayedArrowToTotal_underlying family substitution value evidence
    ⟨otherValue, otherEvidence⟩ followsBase followsEvidence

/-- Regrouping a total element into indexed comprehension and back recovers
the same contextual category, including its arrows. -/
theorem totalElements_roundtrip :
    totalElementsToDisplayed family ⋙ displayedToTotalElements family =
      𝟭 (totalSpace family).Elements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro point target arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (totalSpace family)
  simp
  rfl

/-- Regrouping indexed comprehension into a total element and back is also
the identity on contextual arrows. -/
theorem displayedElements_roundtrip :
    displayedToTotalElements family ⋙ totalElementsToDisplayed family =
      𝟭 family.Elements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro point target arrow
  apply heq_of_eq
  apply CategoryOfElements.ext family
  apply CategoryOfElements.ext base
  simp
  rfl

/-- The total presheaf's element category and indexed-family comprehension
are equivalent as categories, not merely as sets of objects. -/
def totalElementsEquivalence :
    (totalSpace family).Elements ≌ family.Elements :=
  CategoryTheory.Equivalence.mk (totalElementsToDisplayed family)
    (displayedToTotalElements family)
    (eqToIso (totalElements_roundtrip family).symm)
    (eqToIso (displayedElements_roundtrip family))

section OverBase

variable {smallBase : Face.{uContext, vContext, uBase} Context}
variable (smallFamily :
  DisplayedFamily.{uContext, vContext, uBase, uBase} smallBase)

/-- The equivalence is over the original base: regrouping a total receipt
and projecting its indexed-family comprehension agrees with the base
projection of the total presheaf itself. -/
theorem totalElementsEquivalence_over_base :
    totalElementsToDisplayed smallFamily ⋙ CategoryOfElements.π smallFamily =
      (totalProjection smallFamily).mapElements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext smallBase
  simp
  rfl

end OverBase

section BaseChangeCoherence

variable {originalBase replacementBase :
  Face.{uContext, vContext, uBase} Context}
variable (change : replacementBase ⟶ originalBase)
variable (originalFamily :
  DisplayedFamily.{uContext, vContext, uBase, uBase} originalBase)

/-- Reindexing a displayed family along a base observation induces the
corresponding map of indexed-comprehension contexts, with no inverse required
for that observation. -/
def reindexedElementsToOriginal :
    (reindexDisplayed change originalFamily).Elements ⥤
      originalFamily.Elements where
  obj point := ⟨change.mapElements.obj point.1, point.2⟩
  map arrow := CategoryOfElements.homMk _ _
    (change.mapElements.map arrow.val) arrow.property
  map_id point := by
    apply CategoryOfElements.ext originalFamily
    exact (change.mapElements).map_id point.1
  map_comp earlier later := by
    apply CategoryOfElements.ext originalFamily
    exact (change.mapElements).map_comp earlier.val later.val

@[simp] theorem reindexedElementsToOriginal_underlying
    {first second : (reindexDisplayed change originalFamily).Elements}
    (arrow : first ⟶ second) :
    ((reindexedElementsToOriginal change originalFamily).map arrow).val.val =
      arrow.val.val := rfl

/-- Regrouping a proof-relevant total context as indexed comprehension
commutes with arbitrary base change on objects and contextual arrows. -/
theorem totalElementsEquivalence_baseChange :
    (totalReindexMap change originalFamily).mapElements ⋙
        totalElementsToDisplayed originalFamily =
      totalElementsToDisplayed (reindexDisplayed change originalFamily) ⋙
        reindexedElementsToOriginal change originalFamily := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext originalFamily
  apply CategoryOfElements.ext originalBase
  change
    (((totalElementsToDisplayed originalFamily).map
      ((totalReindexMap change originalFamily).mapElements.map arrow)).val).val =
    (((reindexedElementsToOriginal change originalFamily).map
      ((totalElementsToDisplayed (reindexDisplayed change originalFamily)).map arrow)).val).val
  rw [totalElementsToDisplayed_underlying,
    reindexedElementsToOriginal_underlying,
    totalElementsToDisplayed_underlying]
  rfl

/-- The indexed-comprehension map for an identity base change is the
identity functor, including its action on evidence-bearing arrows. -/
theorem reindexedElementsToOriginal_id
    {oneBase : Face.{uContext, vContext, uBase} Context}
    (oneFamily : DisplayedFamily.{uContext, vContext, uBase, uBase} oneBase) :
    reindexedElementsToOriginal (𝟙 oneBase) oneFamily =
      𝟭 oneFamily.Elements := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext oneFamily
  apply CategoryOfElements.ext oneBase
  rfl

/-- Indexed-comprehension base change respects staged changes of the
observed base. No change is required to be invertible. -/
theorem reindexedElementsToOriginal_comp
    {finalBase : Face.{uContext, vContext, uBase} Context}
    (later : finalBase ⟶ replacementBase) :
    reindexedElementsToOriginal later (reindexDisplayed change originalFamily) ⋙
        reindexedElementsToOriginal change originalFamily =
      reindexedElementsToOriginal (later ≫ change) originalFamily := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext originalFamily
  apply CategoryOfElements.ext originalBase
  rfl

end BaseChangeCoherence

#print axioms totalElementsObjectEquiv
#print axioms totalElementsToDisplayed
#print axioms displayedToTotalElements
#print axioms totalElementsEquivalence
#print axioms totalElementsEquivalence_over_base
#print axioms totalElementsEquivalence_baseChange
#print axioms reindexedElementsToOriginal_id
#print axioms reindexedElementsToOriginal_comp

end Mettapedia.TypeTheory.DisplayedPresheafIndexedCwfBridge
