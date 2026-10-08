import Mettapedia.SetTheory.CarveOuts.Sheaves.Collection
import Mettapedia.SetTheory.CarveOuts.Sites.SiteProjections
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Cantor space: sheaf models, their logic, and small maps

The test case: families over any context category `D`, valued in sheaves on Cantor
space `ℕ → Bool`.

**Covers are needed for agreement.** On the product site of `D` and the open sets of Cantor
space, let a presheaf have, on the whole space, a Boolean, and on every smaller open set a single
section (`wholeValues`). The two Booleans on the whole space are distinct sections of the
presheaf whose restrictions to each half agree.

* Forcing on the product site, and sheaf forcing on the sheafification, both force their
  equality on the whole space; contextual forcing without covers refutes it
  (`cover_free_disagrees`). So forcing without covers is not sheaf forcing, already for an
  atomic formula.
* The unit of sheafification identifies the two sections (`sheafUnit_identifies`); as a
  reading of the presheaf's sections it has a non-trivial fibre (`fiber_sheafUnit`).

**The logic of the sheaf models is not classical.** Through the agreement theorem, the region
models of `Sites.SiteProjections` give sheaf models in which excluded middle of membership in the left
half is forced only through the cover by the two halves (`sheaf_halves_excluded_middle`,
`sheaf_halves_neither_disjunct`), and excluded middle of membership in the complement of a point
is not forced on the whole space (`sheaf_puncture_excluded_middle_not_forced`).

**Small maps.** Sheaves on Cantor space satisfy (S1)–(S5) and (M) (`cantor_sheafSmallMapClass`,
`cantor_sheafMonosSmall`), collection whenever the base has it (`cantor_sheafCollection`), and
collection with host choice (`cantor_sheafCollection_of_choice`). (P1), (I) and (R) remain
hypotheses (`cantor_sheaf_basicSmallMapAxioms`).
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.CarveOuts.Sheaves

open CategoryTheory TopologicalSpace Opposite
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialLogic
open Mettapedia.SetTheory.CarveOuts.Sites
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps
open Mettapedia.GSLT.Core.NonFactorization

universe w

/-! ## Two sections that agree on each half -/

section Halves

variable {D : Type} [Category.{0} D]

theorem not_top_le_rightHalf : ¬ (⊤ : Opens (ℕ → Bool)) ≤ rightHalf := fun h =>
  Bool.false_ne_true (h (show constSeq true ∈ (⊤ : Opens (ℕ → Bool)) from trivial)).symm

/-- On the whole space a Boolean; on every smaller open set a single section. -/
def wholeValues : (D × (Opens (ℕ → Bool))ᵒᵈ) ⥤ Type where
  obj p := region p = ⊤ → Bool
  map a := TypeCat.ofHom fun s h => s (top_unique ((le_of_eq h.symm).trans (region_le a)))

/-- No membership. -/
def noMember : Model (wholeValues (D := D)) where
  member _ _ _ := False
  member_transport := by
    intro _ _ _ _ _ h
    exact h

/-- The two Booleans on the whole space. -/
def twoSections (c : D) : Environment (wholeValues (D := D)) 2 (whole c) :=
  fun index => fun _ => decide (index = 0)

theorem twoSections_ne (c : D) : twoSections c 0 ≠ twoSections c 1 := fun h =>
  Bool.false_ne_true (congrFun h rfl).symm

/-- On each half the two sections agree. -/
theorem twoSections_agree_on_halves (c : D) {V : Opens (ℕ → Bool)}
    (hV : V ≤ leftHalf ∨ V ≤ rightHalf) :
    transport wholeValues (shrink (whole c) (le_top : V ≤ ⊤)) (twoSections c) 0 =
      transport wholeValues (shrink (whole c) (le_top : V ≤ ⊤)) (twoSections c) 1 := by
  funext h
  exfalso
  rcases hV with hl | hr
  · exact not_top_le_leftHalf ((le_of_eq h.symm).trans hl)
  · exact not_top_le_rightHalf ((le_of_eq h.symm).trans hr)

/-- **Covers are needed for agreement.** The equality of the two sections is forced on the
product site and in sheaves, and refuted by contextual forcing without covers. -/
theorem cover_free_disagrees (c : D) :
    siteForce wholeValues noMember (.equal 0 1) (whole c) (twoSections c) ∧
      sheafForce (sheafifyModel wholeValues noMember) (.equal 0 1) (whole c)
        (pushEnv (sheafUnitMap wholeValues) (twoSections c)) ∧
      ¬ force wholeValues noMember (.equal 0 1) (whole c) (twoSections c) := by
  have site : siteForce wholeValues noMember (.equal 0 1) (whole c) (twoSections c) := by
    refine le_trans halves_cover (sup_le (le_sSup ⟨le_top, ?_⟩) (le_sSup ⟨le_top, ?_⟩))
    · exact twoSections_agree_on_halves c (Or.inl le_rfl)
    · exact twoSections_agree_on_halves c (Or.inr le_rfl)
  exact ⟨site, (siteForce_iff_sheafForce wholeValues noMember _ _ _).mp site, twoSections_ne c⟩

/-- **Sheafification identifies the two sections.** -/
theorem sheafUnit_identifies (c : D) :
    twoSections c 0 ≠ twoSections c 1 ∧
      (sheafUnit wholeValues).app (whole c) (twoSections c 0) =
        (sheafUnit wholeValues).app (whole c) (twoSections c 1) :=
  ⟨twoSections_ne c, (cover_free_disagrees c).2.1⟩

/-- **The unit of sheafification forgets a distinction**: two sections of the presheaf on the
whole space with one image. -/
def fiber_sheafUnit (c : D) :
    NonTrivialFiber ((sheafUnitMap wholeValues).app (whole c)) (fun s => s) where
  left := twoSections c 0
  right := twoSections c 1
  sameShadow := (sheafUnit_identifies c).2
  differentValue := twoSections_ne c

end Halves

/-! ## Excluded middle in sheaves on Cantor space -/

section Logic

variable {D : Type} [Category.{0} D]

/-- **Excluded middle of membership in the left half is forced in sheaves**, through the cover by
the two halves. -/
theorem sheaf_halves_excluded_middle (c : D) :
    sheafForce (sheafifyModel unitValues (regionModel leftHalf)) insideOrOutside (whole c)
      (pushEnv (sheafUnitMap unitValues) (unitEnv _)) :=
  (siteForce_iff_sheafForce _ _ _ _ _).mp (halves_excluded_middle c).1

/-- Neither disjunct is forced in sheaves on the whole space. -/
theorem sheaf_halves_neither_disjunct (c : D) :
    ¬ sheafForce (sheafifyModel unitValues (regionModel leftHalf)) inside (whole c)
        (pushEnv (sheafUnitMap unitValues) (unitEnv _)) ∧
      ¬ sheafForce (sheafifyModel unitValues (regionModel leftHalf)) outside (whole c)
        (pushEnv (sheafUnitMap unitValues) (unitEnv _)) :=
  ⟨fun h => (halves_neither_disjunct c).1 ((siteForce_iff_sheafForce _ _ _ _ _).mpr h),
    fun h => (halves_neither_disjunct c).2 ((siteForce_iff_sheafForce _ _ _ _ _).mpr h)⟩

/-- **Excluded middle fails in sheaves on Cantor space**: for the complement of a point it is not
forced on the whole space. -/
theorem sheaf_puncture_excluded_middle_not_forced (c : D) (f : ℕ → Bool) :
    ¬ sheafForce (sheafifyModel unitValues (regionModel (puncture f))) insideOrOutside (whole c)
      (pushEnv (sheafUnitMap unitValues) (unitEnv _)) := fun h =>
  puncture_excluded_middle_not_forced c f ((siteForce_iff_sheafForce _ _ _ _ _).mpr h)

end Logic

/-! ## Small maps on sheaves over Cantor space -/

/-- **(S1)–(S5) on sheaves over Cantor space.** -/
theorem cantor_sheafSmallMapClass :
    SmallMapClass (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_smallMapClass.{w, 0}

/-- **(M) on sheaves over Cantor space.** -/
theorem cantor_sheafMonosSmall :
    MonosSmall (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_monosSmall.{w, 0}

/-- **Collection on sheaves over Cantor space, from collection in the base.** -/
theorem cantor_sheafCollection (hbase : BaseCollection.{w, 0}) :
    CollectionAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_collection hbase

/-- **Collection on sheaves over Cantor space, with host choice.** -/
theorem cantor_sheafCollection_of_choice :
    CollectionAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheafSmall_collection_of_choice.{w, 0}

/-- With (P1), (I) and (R) supplied, small maps of sheaves over Cantor space satisfy the basic
small-map axioms. The hypothesis (R) cannot be met here
(`cantor_sheaf_not_representable`). -/
theorem cantor_sheaf_basicSmallMapAxioms
    (powerClass : PowerClassAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))))
    (naturalsSmall : NaturalsSmallAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))))
    (representable :
      RepresentabilityAxiom (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool)))) :
    BasicSmallMapAxioms (sheafSmall.{w} : MorphismProperty (SheafOn (ℕ → Bool))) :=
  sheaf_basicSmallMapAxioms.{w, 0} powerClass naturalsSmall representable

end Mettapedia.SetTheory.CarveOuts.Sheaves
