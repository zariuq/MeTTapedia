import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Equivalence

/-!
# Categories of elements under change of base

Precomposing a type-valued family with a base functor induces a functor
between its categories of elements. If the base functor is an equivalence,
this induced functor is an equivalence as well. Evidence values are carried
by the original family and are never reconstructed by search.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.CategoryOfElementsBaseChange

open CategoryTheory

universe uSource vSource uTarget vTarget w

variable {Source : Type uSource} [Category.{vSource} Source]
variable {Target : Type uTarget} [Category.{vTarget} Target]

/-- A change of indexing category carries actual evidence in a
precomposed family to the same evidence in the original family. -/
def mapPrecompElements (change : Source ⥤ Target)
    (family : Target ⥤ Type w) :
    (change ⋙ family).Elements ⥤ family.Elements where
  obj receipt := ⟨change.obj receipt.1, receipt.2⟩
  map {first second} arrow :=
    CategoryOfElements.homMk
      ⟨change.obj first.1, first.2⟩
      ⟨change.obj second.1, second.2⟩
      (change.map arrow.val) arrow.property
  map_id receipt := by
    apply CategoryOfElements.ext family
    exact change.map_id receipt.1
  map_comp firstStep secondStep := by
    apply CategoryOfElements.ext family
    exact change.map_comp firstStep.val secondStep.val

/-- Faithfulness of a base change survives when evidence is retained. -/
theorem mapPrecompElements_faithful
    (change : Source ⥤ Target) [change.Faithful]
    (family : Target ⥤ Type w) :
    (mapPrecompElements change family).Faithful := by
  refine ⟨?_⟩
  intro first second earlier later same
  apply CategoryOfElements.ext (change ⋙ family)
  apply change.map_injective
  exact congrArg Subtype.val same

/-- Fullness of a base change survives when the evidence equation is
transported through the chosen preimage arrow. -/
theorem mapPrecompElements_full
    (change : Source ⥤ Target) [change.Full]
    (family : Target ⥤ Type w) :
    (mapPrecompElements change family).Full := by
  refine ⟨?_⟩
  intro first second arrow
  let lifted := change.preimage arrow.val
  have evidence : (change ⋙ family).map lifted first.2 = second.2 := by
    change family.map (change.map lifted) first.2 = second.2
    have hmap : change.map lifted = arrow.val := by
      exact change.map_preimage arrow.val
    rw [hmap]
    exact arrow.property
  refine ⟨CategoryOfElements.homMk first second lifted evidence, ?_⟩
  apply CategoryOfElements.ext family
  exact change.map_preimage arrow.val

/-- An equivalence of base categories reaches every evidence-bearing
target object up to an isomorphism that transports that same evidence. -/
theorem mapPrecompElements_essSurj
    (equivalence : Source ≌ Target)
    (family : Target ⥤ Type w) :
    (mapPrecompElements equivalence.functor family).EssSurj := by
  refine ⟨?_⟩
  intro receipt
  let lifted : (equivalence.functor ⋙ family).Elements :=
    ⟨equivalence.inverse.obj receipt.1,
      family.map (equivalence.counitIso.inv.app receipt.1) receipt.2⟩
  refine ⟨lifted, ⟨CategoryOfElements.isoMk
    ((mapPrecompElements equivalence.functor family).obj lifted)
    receipt
    (equivalence.counitIso.app receipt.1)
    ?_⟩⟩
  change family.map (equivalence.counitIso.hom.app receipt.1)
      (family.map (equivalence.counitIso.inv.app receipt.1) receipt.2) =
    receipt.2
  calc
    _ = family.map
          (equivalence.counitIso.inv.app receipt.1 ≫
            equivalence.counitIso.hom.app receipt.1) receipt.2 := by
          rw [family.map_comp_apply]
    _ = receipt.2 := by
          rw [equivalence.counitIso.inv_hom_id_app]
          exact family.map_id_apply receipt.1 receipt.2

/-- An equivalence of bases induces an equivalence of the corresponding
evidence-bearing categories of elements. -/
noncomputable def precompElementsEquivalence
    (equivalence : Source ≌ Target)
    (family : Target ⥤ Type w) :
    (equivalence.functor ⋙ family).Elements ≌ family.Elements := by
  let changed := mapPrecompElements equivalence.functor family
  letI : changed.Faithful :=
    mapPrecompElements_faithful equivalence.functor family
  letI : changed.Full :=
    mapPrecompElements_full equivalence.functor family
  letI : changed.EssSurj :=
    mapPrecompElements_essSurj equivalence family
  letI : changed.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact changed.asEquivalence

#print axioms mapPrecompElements
#print axioms mapPrecompElements_faithful
#print axioms mapPrecompElements_full
#print axioms mapPrecompElements_essSurj
#print axioms precompElementsEquivalence

end Mettapedia.TypeTheory.CategoryOfElementsBaseChange
