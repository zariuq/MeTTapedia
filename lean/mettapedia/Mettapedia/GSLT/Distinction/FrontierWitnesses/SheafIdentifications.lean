import Mettapedia.SetTheory.CarveOuts.Sheaves.Representability
import Mettapedia.SetTheory.CarveOuts.Sheaves.Naturals
import Mettapedia.SetTheory.CarveOuts.Sheaves.PowerClasses

/-!
# Identifications of options about small maps of sheaves

Three pairs of options that the option graph compares make the same identifications, and each is
stated here as one statement.

* **Small maps are the pullbacks of the universal small map**: a map of sheaves is small exactly
  when it is a pullback of membership over the power class of the generic sheaf.
* **The natural numbers object is unique**: every parametrised natural numbers object of sheaves
  is the sheaf of locally constant natural numbers, by a unique isomorphism respecting zero and
  the successor.
* **Small relations are maps into the power class**: pulling back membership is a bijection from
  maps into the power class of a sheaf onto the small relations into it.

Host choice enters through the encoding of small fibres (`Shrink`), Mathlib's limits and
sheafification, and the choice of the classifying map from its unique existence.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.FrontierWitnesses.SheafIdentifications

open CategoryTheory Limits TopologicalSpace Opposite
open Mettapedia.SetTheory.CarveOuts.Sites.SmallMaps
open Mettapedia.SetTheory.CarveOuts.Sheaves

universe w u

/-! ## Small maps and pullbacks of the universal small map -/

section Universal

variable {X : Type (max u (w + 1))} [TopologicalSpace X] [Small.{w} (Opens X)]

/-- A map of sheaves that is a pullback of the universal small map. -/
def IsUniversalPullback {A B : SheafOn X} (f : A ⟶ B) : Prop :=
  ∃ (k : A ⟶ universeTotal.{w, u} (X := X)) (c : B ⟶ universeBase.{w, u} (X := X)),
    IsPullback k f (universalMap.{w, u} (X := X)) c

/-- **A map of sheaves is small exactly when it is a pullback of the universal small map.** -/
theorem sheafSmall_iff_universalPullback {A B : SheafOn X} (f : A ⟶ B) :
    sheafSmall.{w} f ↔ IsUniversalPullback.{w, u} f :=
  ⟨fun small => ⟨_, _, small_isPullback_universal f small⟩,
    fun ⟨_, _, square⟩ => sheafSmall_pullback square.flip universalMap_small⟩

end Universal

/-! ## The natural numbers object -/

/-- **Every parametrised natural numbers object of sheaves is the sheaf of locally constant
natural numbers, by a unique isomorphism carrying zero to zero and the successor to the
successor.** -/
theorem parametrisedNNO_iso_natNNO {X : Type u} [TopologicalSpace X]
    (n : ParamNNO (SheafOn X)) :
    ∃! e : n.N ≅ (natNNO (X := X)).N,
      n.zero ≫ e.hom = (natNNO (X := X)).zero ∧
        n.succ ≫ e.hom = e.hom ≫ (natNNO (X := X)).succ := by
  refine ⟨paramNNOIso n natNNO, ⟨paramNNOMap_zero n natNNO, paramNNOMap_succ n natNNO⟩, ?_⟩
  rintro e ⟨zero, succ⟩
  apply Iso.ext
  exact paramNNO_hom_ext n _ _ zero succ (paramNNOMap_zero n natNNO) (paramNNOMap_succ n natNNO)

/-! ## Small relations and maps into the power class -/

section PowerClass

variable {X : Type u} [TopologicalSpace X] [Small.{w} (Opens X)]

/-- The relation a map into the power class classifies: the pullback of membership. -/
noncomputable def classified {I A : SheafOn X} (χ : I ⟶ powerSheaf.{w} A) : Subobject (I ⨯ A) :=
  (Subobject.pullback (prod.map χ (𝟙 A))).obj (Subobject.mk (memArrow.{w} A))

/-- **The relation a map into the power class classifies is small**: a section of it over an
index is determined by its member, which lies in the small family the map gives the index. -/
theorem classified_small {I A : SheafOn X} (χ : I ⟶ powerSheaf.{w} A) :
    IsSmallRelation (sheafSmall.{w} : MorphismProperty (SheafOn X)) (classified χ) := by
  intro U i
  let R := classified χ
  let member : {r // (R.arrow ≫ prod.fst).hom.app U r = i} →
      (χ.hom.app U i : SmallSub.{w} A (unop U)).carrier (unop U) le_rfl := fun r =>
    ⟨(prod.snd : I ⨯ A ⟶ A).hom.app U (R.arrow.hom.app U r.1), by
      have inMember := (pullback_mem_iff χ (unop U) (R.arrow.hom.app U r.1)).mp ⟨r.1, rfl⟩
      have index : (prod.fst : I ⨯ A ⟶ I).hom.app U (R.arrow.hom.app U r.1) = i := r.2
      rw [index] at inMember
      exact inMember⟩
  have injective : Function.Injective member := by
    intro r r' same
    have members : (prod.snd : I ⨯ A ⟶ A).hom.app U (R.arrow.hom.app U r.1) =
        (prod.snd : I ⨯ A ⟶ A).hom.app U (R.arrow.hom.app U r'.1) :=
      congrArg Subtype.val same
    have indices : (prod.fst : I ⨯ A ⟶ I).hom.app U (R.arrow.hom.app U r.1) =
        (prod.fst : I ⨯ A ⟶ I).hom.app U (R.arrow.hom.app U r'.1) :=
      (r.2 : _).trans (r'.2 : _).symm
    exact Subtype.ext (injective_of_mono R.arrow (unop U) (prod_sections_ext I A indices members))
  have := (χ.hom.app U i : SmallSub.{w} A (unop U)).small (unop U) le_rfl
  exact small_of_injective injective

/-- **Small relations into a sheaf are in bijection with maps into its power class**: pulling
back membership is injective on maps and reaches every small relation. -/
theorem classified_bijective (I A : SheafOn X) :
    Function.Bijective (fun χ : I ⟶ powerSheaf.{w} A =>
      (⟨classified χ, classified_small χ⟩ : {R : Subobject (I ⨯ A) //
        IsSmallRelation (sheafSmall.{w} : MorphismProperty (SheafOn X)) R})) := by
  refine ⟨fun χ χ' same => ?_, fun R => ?_⟩
  · have equal : classified χ = classified χ' := congrArg Subtype.val same
    exact ((sheafPowerClass.{w} A).classify _ (classified_small χ')).unique equal rfl
  · obtain ⟨χ, classifies, -⟩ := (sheafPowerClass.{w} A).classify R.1 R.2
    exact ⟨χ, Subtype.ext classifies⟩

end PowerClass

end Mettapedia.GSLT.Distinction.FrontierWitnesses.SheafIdentifications
