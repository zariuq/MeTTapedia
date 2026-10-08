import Mettapedia.TypeTheory.ContextualCwfUniverseTypeLift

/-!
# Packing and full-motive elimination through carrier lifts

The actual lifted sum operations determine the same dependent component
maps as the supplied model. Their packing inverse and full-motive
eliminator retain the original arrows and supplied branch section.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualCwfUniverseLift

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v w w' uc vs wt ms
variable {C : Cwf.{u, v, w, w'}}

theorem term_cast_down_heq {Γ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    {A B : (Raised C).Ty Γ} (types : A = B) (term : (Raised C).Tm Γ A) :
    HEq (cast (congrArg ((Raised C).Tm Γ) types) term).down term.down := by
  cases types
  rfl

theorem read_down {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (δ : (Raised C).Sub Δ ((Raised C).ext Γ A)) :
    (ContextualSumComprehension.read A δ).down = ContextualSumComprehension.read A.down δ.down := by
  unfold ContextualSumComprehension.read
  exact cast_down (congrArg (C.Tm Δ.down) (C.tySub_comp A.down (C.wk A.down) δ.down).symm) _ _

theorem normalize_down_heq (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (σ : (Raised C).Sub Δ Γ) {A : (Raised C).Ty Γ}
    {B : (Raised C).Ty ((Raised C).ext Γ A)}
    (p : (Raised C).Tm Δ ((Raised C).tySub ((liftSums sums.operations).sigma A B) σ)) :
    HEq (normalize (liftStableSums sums) σ p).down
      (normalize sums σ.down p.down) := by
  exact (term_cast_down_heq ((liftStableSums sums).substitution.1 σ A B) p).trans
    (normalize_heq sums σ.down p.down).symm

theorem components_first_down (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (σ : (Raised C).Sub Δ Γ) (A : (Raised C).Ty Γ)
    (B : (Raised C).Ty ((Raised C).ext Γ A))
    (p : (Raised C).Tm Δ ((Raised C).tySub ((liftSums sums.operations).sigma A B) σ)) :
    HEq (componentsEquiv (liftStableSums sums) σ A B p).1.down
      (componentsEquiv sums σ.down A.down B.down p.down).1 := by
  change HEq (sums.operations.fst (normalize (liftStableSums sums) σ p).down)
    (sums.operations.fst (normalize sums σ.down p.down))
  exact fst_heq sums.operations rfl
    (heq_of_eq (congrArg (C.tySub B.down) (extensionSubstitution_readout σ A)))
    (normalize_down_heq sums σ p)

theorem components_second_down (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (σ : (Raised C).Sub Δ Γ) (A : (Raised C).Ty Γ)
    (B : (Raised C).Ty ((Raised C).ext Γ A))
    (p : (Raised C).Tm Δ ((Raised C).tySub ((liftSums sums.operations).sigma A B) σ)) :
    HEq (componentsEquiv (liftStableSums sums) σ A B p).2.down
      (componentsEquiv sums σ.down A.down B.down p.down).2 := by
  have component := sums_snd_readout sums.operations
    (normalize (liftStableSums sums) σ p)
  have native := snd_heq sums.operations rfl
    (heq_of_eq (congrArg (C.tySub B.down) (extensionSubstitution_readout σ A)))
    (normalize_down_heq sums σ p)
  have first := component.trans native
  change HEq ((secondEquiv σ A B _)
    ((liftSums sums.operations).snd (normalize (liftStableSums sums) σ p))).down _
  have secondTypes : (Raised C).tySub
      ((Raised C).tySub B (TypeOver.extensionSubstitution σ A))
      (ContextualProductComparison.selfExtend (Raised C)
        ((liftSums sums.operations).fst (normalize (liftStableSums sums) σ p))) =
      (Raised C).tySub B ((Raised C).pair σ A
        ((liftSums sums.operations).fst (normalize (liftStableSums sums) σ p))) := by
    rw [← (Raised C).tySub_comp, lift_selfExtend]
  unfold secondEquiv
  dsimp only [Equiv.cast, Equiv.coe_fn_mk]
  exact (term_cast_down_heq secondTypes _).trans (first.trans (cast_heq _ _).symm)

theorem sumArrow_first_down (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A))
    (δ : (Raised C).Sub Δ (sumContext (liftStableSums sums) A B)) :
    HEq (sumArrowEquiv (liftStableSums sums) A B δ).2.1.down
      (sumArrowEquiv sums A.down B.down δ.down).2.1 := by
  have component := components_first_down sums
    ((Raised C).compS ((Raised C).wk ((liftSums sums.operations).sigma A B)) δ) A B
    (ContextualSumComprehension.read ((liftSums sums.operations).sigma A B) δ)
  change HEq _ (componentsEquiv sums
    (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down)
    A.down B.down (ContextualSumComprehension.read (sums.operations.sigma A.down B.down) δ.down)).1
  change HEq _ (componentsEquiv sums
    (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down)
    A.down B.down (ContextualSumComprehension.read
      ((liftSums sums.operations).sigma A B) δ).down).1 at component
  exact component.trans (components_first_congr sums rfl
    (heq_of_eq (read_down ((liftSums sums.operations).sigma A B) δ)))

theorem sumArrow_second_down (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A))
    (δ : (Raised C).Sub Δ (sumContext (liftStableSums sums) A B)) :
    HEq (sumArrowEquiv (liftStableSums sums) A B δ).2.2.down
      (sumArrowEquiv sums A.down B.down δ.down).2.2 := by
  have component := components_second_down sums
    ((Raised C).compS ((Raised C).wk ((liftSums sums.operations).sigma A B)) δ) A B
    (ContextualSumComprehension.read ((liftSums sums.operations).sigma A B) δ)
  change HEq _ (componentsEquiv sums
    (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down)
    A.down B.down (ContextualSumComprehension.read (sums.operations.sigma A.down B.down) δ.down)).2
  change HEq _ (componentsEquiv sums
    (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down)
    A.down B.down (ContextualSumComprehension.read
      ((liftSums sums.operations).sigma A B) δ).down).2 at component
  exact component.trans (components_second_congr sums rfl
    (heq_of_eq (read_down ((liftSums sums.operations).sigma A B) δ)))

theorem unpackArrow_down (sums : StableSums C)
    {Γ Δ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A))
    (δ : (Raised C).Sub Δ (sumContext (liftStableSums sums) A B)) :
    (unpackArrow (liftStableSums sums) A B δ).down =
      unpackArrow sums A.down B.down δ.down := by
  have raisedMid := congrArg ULift.down
    (unpackArrow_mid (liftStableSums sums) A B δ)
  change C.compS (C.wk B.down) (unpackArrow (liftStableSums sums) A B δ).down =
    C.pair (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down) A.down
      (sumArrowEquiv (liftStableSums sums) A B δ).2.1.down at raisedMid
  have first := eq_of_heq (sumArrow_first_down sums A B δ)
  have mid := raisedMid.trans (congrArg
    (C.pair (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down) A.down) first)
  have middle := mid.trans (unpackArrow_mid sums A.down B.down δ.down).symm
  apply TypeOver.substitution_ext
  · exact middle
  · have types : C.tySub (C.tySub B.down (C.wk B.down))
        (unpackArrow (liftStableSums sums) A B δ).down =
        C.tySub B.down (C.pair
          (C.compS (C.wk (sums.operations.sigma A.down B.down)) δ.down) A.down
          (sumArrowEquiv (liftStableSums sums) A B δ).2.1.down) :=
      (C.tySub_comp B.down (C.wk B.down) _).symm.trans (congrArg (C.tySub B.down) raisedMid)
    have lowered := down_heq (congrArg (C.Tm Δ.down) types)
      (unpackArrow_second_raw (liftStableSums sums) A B δ)
    exact lowered.trans ((sumArrow_second_down sums A B δ).trans
      (unpackArrow_second_raw sums A.down B.down δ.down).symm)

theorem unpack_down (sums : StableSums C)
    {Γ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A)) :
    (unpack (liftStableSums sums) A B).down = unpack sums A.down B.down :=
  unpackArrow_down sums A B ((Raised C).idS _)

set_option backward.isDefEq.respectTransparency false in
/-- The packing comparison is earned by the actual inverse equations. -/
theorem pack_down (sums : StableSums C)
    {Γ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A)) :
    (pack (liftStableSums sums) A B).down = pack sums A.down B.down := by
  have inverse := congrArg ULift.down (unpack_pack (liftStableSums sums) A B)
  change C.compS (unpack (liftStableSums sums) A B).down
    (pack (liftStableSums sums) A B).down = C.idS _ at inverse
  rw [unpack_down] at inverse
  have compared := congrArg (C.compS (pack sums A.down B.down)) inverse
  rw [← C.comp_assoc, pack_unpack] at compared
  exact (C.id_comp _).symm.trans (compared.trans (C.comp_id _))

/-- The supplied branch section is transported only along the earned
packing equality; its full-motive result remains the original section. -/
theorem elimination_down (sums : StableSums C)
    {Γ : (Raised.{u, v, w, w', uc, vs, wt, ms} C).Ctx}
    (A : (Raised C).Ty Γ) (B : (Raised C).Ty ((Raised C).ext Γ A))
    (M : (Raised C).Ty (sumContext (liftStableSums sums) A B))
    (body : (Raised C).Tm (tupleContext A B)
      ((Raised C).tySub M (pack (liftStableSums sums) A B))) :
    (eliminate (liftStableSums sums) A B M body).down =
      eliminate sums A.down B.down M.down
        (cast (congrArg (C.Tm (tupleContext A.down B.down))
          (congrArg (C.tySub M.down) (pack_down sums A B))) body.down) := by
  apply eq_of_heq
  have first := term_cast_down_heq (motive_roundtrip (liftStableSums sums) A B M)
    ((Raised C).tmSub body (unpack (liftStableSums sums) A B))
  change HEq (eliminate (liftStableSums sums) A B M body).down
    (C.tmSub body.down (unpack (liftStableSums sums) A B).down) at first
  rw [unpack_down] at first
  exact first.trans ((TypeOver.tmSub_heq
    (congrArg (C.tySub M.down) (pack_down sums A B))
    (cast_heq _ _).symm (unpack sums A.down B.down)).trans
      (eliminate_heq sums A.down B.down M.down _).symm)

end Mettapedia.TypeTheory.ContextualCwfUniverseLift
