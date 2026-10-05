import Mettapedia.TypeTheory.HostChoiceWiderPresheafNativeAdjunction
import Mettapedia.TypeTheory.ContextualSmallFamilyNativeSigma

/-!
# Comparison with the successor-ambient native slice interface

Actual natural slice maps are identified with the native over-category
maps. The literal coordinate pullback satisfies its limit property and is
compared with the chosen native pullback. This optional interface inherits
the external assumptions of the native category and limit constructions;
the underlying original-bound coordinate constructions remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.HostChoiceContextualNativeSliceComparison

open CategoryTheory Limits
open ContextualWitnessCover ContextualImageFactorization ContextualNaturalSlices
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyNativeSlice

universe u

variable {C : Type u} [Category.{u} C]
variable {base X Y Z : Cᵒᵖ ⥤ Type (u + 1)}

def overObject (operation : NaturalHom X base) : Over base :=
  Over.mk operation.toNatTrans

def toOver {first : NaturalHom X base} {second : NaturalHom Y base} (mapping : Map first second) :
    overObject first ⟶ overObject second :=
  Over.homMk mapping.mapping.toNatTrans (by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro value
    exact mapping.square point value)

def fromOver {first : NaturalHom X base} {second : NaturalHom Y base}
    (mapping : overObject first ⟶ overObject second) : Map first second where
  mapping := NaturalHom.ofNatTrans mapping.left
  square point value := congrArg (fun map : NatTrans X base => map.app point value) (Over.w mapping)

def overHomEquiv (first : NaturalHom X base) (second : NaturalHom Y base) :
    Map first second ≃ (overObject first ⟶ overObject second) where
  toFun := toOver
  invFun := fromOver
  left_inv mapping := by
    apply Map.ext
    intro _ _
    rfl
  right_inv mapping := by
    apply Over.OverMorphism.ext
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro _
    rfl

theorem toOver_comp {first : NaturalHom X base} {second : NaturalHom Y base}
    {third : NaturalHom Z base} (earlier : Map first second) (later : Map second third) :
    toOver (earlier.comp later) = toOver earlier ≫ toOver later := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _
  rfl

theorem toOver_identity (first : NaturalHom X base) : toOver (Map.identity first) = 𝟙 (overObject first) := by
  apply Over.OverMorphism.ext
  apply NatTrans.ext
  funext point
  apply ConcreteCategory.hom_ext
  intro _
  rfl

theorem fromOver_comp {first : NaturalHom X base} {second : NaturalHom Y base}
    {third : NaturalHom Z base} (earlier : overObject first ⟶ overObject second)
    (later : overObject second ⟶ overObject third) :
    fromOver (earlier ≫ later) = (fromOver earlier).comp (fromOver later) := by
  apply Map.ext
  intro _ _
  rfl

variable (operation : NaturalHom X base) (change : NaturalHom Y base)

def literalPullbackCone : PullbackCone (C := Cᵒᵖ ⥤ Type (u + 1))
    operation.toNatTrans change.toNatTrans :=
  PullbackCone.mk (pullbackFirst operation change).toNatTrans (pullbackSecond operation change).toNatTrans (by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro pair
    exact pair.property)

def literalPullbackLimit : IsLimit (literalPullbackCone operation change) :=
  PullbackCone.IsLimit.mk _
    (fun cone => (pullbackPair operation change
      (NaturalHom.ofNatTrans cone.fst) (NaturalHom.ofNatTrans cone.snd) (by
        apply NaturalHom.ext
        intro point value
        exact congrArg (fun map : NatTrans cone.pt base => map.app point value) cone.condition)).toNatTrans)
    (by
      intro cone
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro _
      rfl)
    (by
      intro cone
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro _
      rfl)
    (by
      intro cone candidate firstLaw secondLaw
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro value
      apply Subtype.ext
      exact Prod.ext
        (congrArg (fun map : NatTrans cone.pt X => map.app point value) firstLaw)
        (congrArg (fun map : NatTrans cone.pt Y => map.app point value) secondLaw))

theorem literal_isPullback : IsPullback (C := Cᵒᵖ ⥤ Type (u + 1))
    (pullbackFirst operation change).toNatTrans
    (pullbackSecond operation change).toNatTrans operation.toNatTrans change.toNatTrans :=
  ⟨⟨(literalPullbackCone operation change).condition⟩, ⟨literalPullbackLimit operation change⟩⟩

noncomputable def literalPullbackIso :
    overObject (pullbackSecond operation change) ≅
      (Over.pullback change.toNatTrans).obj (overObject operation) :=
  Over.isoMk (literal_isPullback operation change).isoPullback
    (literal_isPullback operation change).isoPullback_hom_snd

theorem literalPullbackIso_first :
    (literalPullbackIso operation change).hom.left ≫
      Limits.pullback.fst (C := Cᵒᵖ ⥤ Type (u + 1)) operation.toNatTrans change.toNatTrans =
        (pullbackFirst operation change).toNatTrans :=
  (literal_isPullback operation change).isoPullback_hom_fst

theorem literalPullbackIso_second :
    (literalPullbackIso operation change).hom.left ≫
      Limits.pullback.snd (C := Cᵒᵖ ⥤ Type (u + 1)) operation.toNatTrans change.toNatTrans =
        (pullbackSecond operation change).toNatTrans :=
  (literal_isPullback operation change).isoPullback_hom_snd

variable {operation change}

theorem literalPullbackIso_natural {other : Cᵒᵖ ⥤ Type (u + 1)}
    {earlier : NaturalHom other base} (mapping : Map earlier operation) :
    toOver (pullbackMap mapping change) ≫ (literalPullbackIso operation change).hom =
      (literalPullbackIso earlier change).hom ≫ (Over.pullback change.toNatTrans).map (toOver mapping) := by
  apply Over.OverMorphism.ext
  apply Limits.pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      Limits.pullback.lift_fst]
    change (toOver (pullbackMap mapping change)).left ≫
        ((literalPullbackIso operation change).hom.left ≫
          Limits.pullback.fst (C := Cᵒᵖ ⥤ Type (u + 1)) operation.toNatTrans change.toNatTrans) =
      (literalPullbackIso earlier change).hom.left ≫
        Limits.pullback.fst (C := Cᵒᵖ ⥤ Type (u + 1)) earlier.toNatTrans change.toNatTrans ≫ (toOver mapping).left
    rw [literalPullbackIso_first]
    have firstSquare := congrArg (fun arrow :
        (ContextualImageFactorization.pullback earlier change ⟶ other) =>
          arrow ≫ (toOver mapping).left) (literalPullbackIso_first earlier change)
    have leftSquare : (toOver (pullbackMap mapping change)).left ≫
        (pullbackFirst operation change).toNatTrans =
      (pullbackFirst earlier change).toNatTrans ≫ (toOver mapping).left := by
      apply NatTrans.ext
      funext point
      apply ConcreteCategory.hom_ext
      intro _
      rfl
    exact leftSquare.trans (firstSquare.symm.trans
      (Category.assoc (obj := Cᵒᵖ ⥤ Type (u + 1))
        (literalPullbackIso earlier change).hom.left
        (Limits.pullback.fst (C := Cᵒᵖ ⥤ Type (u + 1)) earlier.toNatTrans change.toNatTrans)
        (toOver mapping).left))
  · simp only [Over.comp_left, Category.assoc, Over.pullback_map_left,
      Limits.pullback.lift_snd]
    change (toOver (pullbackMap mapping change)).left ≫
        ((literalPullbackIso operation change).hom.left ≫
          Limits.pullback.snd (C := Cᵒᵖ ⥤ Type (u + 1)) operation.toNatTrans change.toNatTrans) =
      (literalPullbackIso earlier change).hom.left ≫
        Limits.pullback.snd (C := Cᵒᵖ ⥤ Type (u + 1)) earlier.toNatTrans change.toNatTrans
    rw [literalPullbackIso_second, literalPullbackIso_second]
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro _
    rfl

theorem literalPullbackIso_inv_natural {other : Cᵒᵖ ⥤ Type (u + 1)}
    {earlier : NaturalHom other base} (mapping : Map earlier operation) :
    (literalPullbackIso earlier change).inv ≫ toOver (pullbackMap mapping change) =
      (Over.pullback change.toNatTrans).map (toOver mapping) ≫ (literalPullbackIso operation change).inv := by
  apply (cancel_epi (literalPullbackIso earlier change).hom).mp
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [← Category.assoc, ← literalPullbackIso_natural, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Mettapedia.TypeTheory.HostChoiceContextualNativeSliceComparison
