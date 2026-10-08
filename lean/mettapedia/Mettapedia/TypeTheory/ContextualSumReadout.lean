import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Supplied readings of a dependent-pair context

The packing map's newest variable is the pair of the actual two component
readings. The equality is derived from the existing arrow equivalences and
the local pairing operation, including its dependent transports.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumComprehension

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

theorem pairAt_heq (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Δ (C.tySub A σ)) (b : C.Tm Δ (C.tySub B (C.pair σ A a))) :
    HEq (pairAt sums σ a b)
      (sums.operations.pair a ((secondEquiv σ A B a).symm b)) := by
  exact cast_heq _ _

theorem pairAt_pair_heq (sums : StableSums C) {Γ Δ : C.Ctx}
    {σ τ : C.Sub Δ Γ} (bases : σ = τ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Δ (C.tySub A σ)) (a' : C.Tm Δ (C.tySub A τ)) (first : HEq a a')
    (b : C.Tm Δ (C.tySub B (C.pair σ A a)))
    (b' : C.Tm Δ (C.tySub (C.tySub B (TypeOver.extensionSubstitution τ A))
      (selfExtend C a'))) (second : HEq b b') :
    HEq (pairAt sums σ a b) (sums.operations.pair a' b') := by
  cases bases
  cases eq_of_heq first
  have body : ((secondEquiv σ A B a).symm b) = b' :=
    eq_of_heq ((cast_heq _ _).trans second)
  exact (pairAt_heq sums σ a b).trans (by rw [body])

theorem read_congr {Γ Δ : C.Ctx} (A : C.Ty Γ)
    {first second : C.Sub Δ (C.ext Γ A)} (same : first = second) :
    HEq (read A first) (read A second) := by cases same; rfl

theorem packArrow_variable (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    HEq (C.tmSub (C.vz (sums.operations.sigma A B)) (packArrow sums A B δ))
      (pairAt sums (tupleArrowEquiv A B δ).1
        (tupleArrowEquiv A B δ).2.1 (tupleArrowEquiv A B δ).2.2) := by
  exact (heq_of_eq (C.vz_pair _ _ _)).trans (cast_heq _ _)

theorem tupleArrow_first {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    HEq (tupleArrowEquiv A B δ).2.1 (read A (C.compS (C.wk B) δ)) := HEq.rfl

theorem tupleArrow_second {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    HEq (tupleArrowEquiv A B δ).2.2 (read B δ) := cast_heq _ _

def genericFirst {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm (tupleContext A B) (C.tySub A (C.compS (C.wk A) (C.wk B))) :=
  read A (C.wk B)

theorem genericFirst_heq {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (genericFirst A B) (C.tmSub (C.vz A) (C.wk B)) := read_heq _ _

theorem genericFirst_pair {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.pair (C.compS (C.wk A) (C.wk B)) A (genericFirst A B) = C.wk B :=
  pair_read A (C.wk B)

theorem genericSecond_type {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.tySub B (C.wk B) =
      C.tySub (C.tySub B
        (TypeOver.extensionSubstitution (C.compS (C.wk A) (C.wk B)) A))
          (selfExtend C (genericFirst A B)) := by
  rw [← C.tySub_comp, lift_selfExtend, genericFirst_pair]

def genericSecond {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm (tupleContext A B)
      (C.tySub (C.tySub B
        (TypeOver.extensionSubstitution (C.compS (C.wk A) (C.wk B)) A))
          (selfExtend C (genericFirst A B))) :=
  cast (congrArg (C.Tm (tupleContext A B)) (genericSecond_type A B)) (C.vz B)

theorem genericSecond_heq {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (genericSecond A B) (C.vz B) := cast_heq _ _

theorem pack_variable (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (C.tmSub (C.vz (sums.operations.sigma A B)) (pack sums A B))
      (sums.operations.pair (genericFirst A B) (genericSecond A B)) := by
  have reading := packArrow_variable sums A B (C.idS (tupleContext A B))
  change HEq (C.tmSub (C.vz (sums.operations.sigma A B)) (pack sums A B)) _ at reading
  have base : (tupleArrowEquiv A B (C.idS (tupleContext A B))).1 =
      C.compS (C.wk A) (C.wk B) := by
    change C.compS (C.wk A) (C.compS (C.wk B) (C.idS _)) = _
    rw [C.comp_id]
  have first : HEq (tupleArrowEquiv A B (C.idS (tupleContext A B))).2.1
      (genericFirst A B) := by
    exact (tupleArrow_first A B (C.idS (tupleContext A B))).trans
      (read_congr A (C.comp_id (C.wk B)))
  have second : HEq (tupleArrowEquiv A B (C.idS (tupleContext A B))).2.2
      (C.vz B) :=
    (tupleArrow_second A B (C.idS (tupleContext A B))).trans
      ((read_heq B _).trans
        ((heq_of_eq (C.tmSub_id (C.vz B))).trans (cast_heq _ _)))
  exact reading.trans (pairAt_pair_heq sums base _ _ first _ _
    (second.trans (genericSecond_heq _ _).symm))

end Mettapedia.TypeTheory.ContextualSumComprehension
