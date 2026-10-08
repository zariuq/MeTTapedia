import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Complete term readouts of contextual sum packing

The arbitrary-base pair classifier computes an actual local pair with the
second component transported by the earned comprehension square. Packing an
arrow is therefore determined by its original base and both variable readings.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumPairReadout

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualSumComprehension

universe u v w w'
variable {C : Cwf.{u, v, w, w'}}

theorem secondEquiv_symm_heq {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (a : C.Tm Δ (C.tySub A σ)) (b : C.Tm Δ (C.tySub B (C.pair σ A a))) :
    HEq ((secondEquiv σ A B a).symm b) b := cast_heq _ _

theorem pairAt_heq (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Δ (C.tySub A σ)) (b : C.Tm Δ (C.tySub B (C.pair σ A a))) :
    HEq (pairAt sums σ a b)
      (sums.operations.pair a ((secondEquiv σ A B a).symm b)) := by
  exact cast_heq _ _

theorem packArrow_pair_readout (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    packArrow sums A B δ =
      C.pair (tupleArrowEquiv A B δ).1 (sums.operations.sigma A B)
        (pairAt sums (tupleArrowEquiv A B δ).1
          (tupleArrowEquiv A B δ).2.1 (tupleArrowEquiv A B δ).2.2) := by
  apply (sumArrowEquiv sums A B).injective
  have classified := (sumArrowEquiv sums A B).apply_symm_apply (tupleArrowEquiv A B δ)
  exact classified.trans (by
    change _ = sumArrowEquiv sums A B
      ((arrowEquiv (sums.operations.sigma A B)).symm
        ⟨(tupleArrowEquiv A B δ).1,
          (componentsEquiv sums (tupleArrowEquiv A B δ).1 A B).symm
            (tupleArrowEquiv A B δ).2⟩)
    unfold sumArrowEquiv
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
    simp only [Equiv.sigmaCongrRight_apply, Equiv.apply_symm_apply])

theorem tupleArrow_base {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) :
    (tupleArrowEquiv A B δ).1 = C.compS (C.wk A) (C.compS (C.wk B) δ) := rfl

theorem tupleArrow_first_heq {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) :
    HEq (tupleArrowEquiv A B δ).2.1 (C.tmSub (C.vz A) (C.compS (C.wk B) δ)) :=
  read_heq A _

theorem tupleArrow_second_heq {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) :
    HEq (tupleArrowEquiv A B δ).2.2 (C.tmSub (C.vz B) δ) :=
  (cast_heq _ _).trans (read_heq B δ)

theorem tupleArrow_middle {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) :
    C.pair (tupleArrowEquiv A B δ).1 A (tupleArrowEquiv A B δ).2.1 =
      C.compS (C.wk B) δ := pair_read A _

end Mettapedia.TypeTheory.ContextualSumPairReadout
