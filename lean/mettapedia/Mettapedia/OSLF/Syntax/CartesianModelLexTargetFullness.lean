import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafFullness

/-!
# Fullness of relative finite-limit restriction in a small target

Yoneda turns a transformation of target-valued authored models into a
presheaf-valued one. The pointwise Set-valued classification extends that
transformation; full faithfulness of Yoneda then descends it. Thus
restriction along authored contexts is fully faithful in every small
finitely complete target, not just in sets.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CartesianContextModels

open CategoryTheory CategoryTheory.Limits

variable (C : Type) [SmallCategory C] [HasFiniteProducts C]
variable (D : Type) [SmallCategory D] [HasFiniteLimits D]

universe u v

omit [HasFiniteProducts C] [HasFiniteLimits D] in
/-- A fully faithful target translation remains faithful on authored
product-preserving interpretations. -/
theorem changeCartesianTarget_faithful_of_faithful
    (E : Type u) [Category.{v} E] [HasFiniteLimits E]
    (H : D ⥤ E) [PreservesFiniteLimits H] [H.Faithful] :
    (changeCartesianTarget C D E H).Faithful := by
  constructor
  intro T U f g h
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext X
  apply H.map_injective
  have hh := congrArg
    (fun k : (changeCartesianTarget C D E H).obj T ⟶
      (changeCartesianTarget C D E H).obj U => k.hom.app X) h
  exact hh

omit [HasFiniteLimits D] in
/-- Every map of authored interpretations in a small target
extends to a unique map of left-exact finite-presentation
interpretations. Uniqueness comes from the separately proved finite-limit
generation theorem. -/
theorem restrictLeftExactTarget_full :
    (restrictLeftExactTarget C D).Full := by
  let P := Dᵒᵖ ⥤ Type
  let Y : D ⥤ P := yoneda
  let R := restrictLeftExactTarget C D
  let Rp := restrictLeftExactTarget C P
  let L := changeLeftExactTarget C D P Y
  let K := changeCartesianTarget C D P Y
  let e := changeTargetRestrictionIso C D P Y
  constructor
  intro T U f
  let fp : Rp.obj (L.obj T) ⟶ Rp.obj (L.obj U) :=
    (e.app T).hom ≫ K.map f ≫ (e.app U).inv
  let gp : L.obj T ⟶ L.obj U := Rp.preimage fp
  let WR := (Functor.whiskeringRight (FinitePresentationObjects C) D P).obj Y
  let gRaw : T.1 ⟶ U.1 := WR.preimage gp.hom
  let g : T ⟶ U := (LeftExactTargetInterpretation C D).homMk gRaw
  refine ⟨g, ?_⟩
  have hgp : L.map g = gp := by
    apply ObjectProperty.hom_ext
    exact WR.map_preimage gp.hom
  have hfp : Rp.map gp = fp := Rp.map_preimage fp
  have hcomm : K.map (R.map g) = K.map f := by
    have hRL : Rp.map (L.map g) = fp := by rw [hgp]; exact hfp
    change K.map (R.map g) = K.map f at hRL
    exact hRL
  exact (changeCartesianTarget_faithful_of_faithful C D P Y).map_injective hcomm

end Mettapedia.OSLF.CartesianContextModels
