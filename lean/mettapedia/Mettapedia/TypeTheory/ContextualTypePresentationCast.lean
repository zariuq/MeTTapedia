import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Context maps induced by equal dependent annotations

Equal supplied annotations determine an actual context map. Its projection
and newest-section equations are derived from the canonical fibre comparison;
the reflexive map is the context identity. The type of this map exposes the
contextual substitution directly without exposing a fibre-category instance
at each concrete model application.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualTypePresentationCast

open Mettapedia.GSLT.Core.ContextualLadder

universe c s t m
variable {K : Cwf.{c, s, t, m}} {Γ : K.Ctx} {A B : K.Ty Γ}

def extensionCast (same : A = B) : K.Sub (K.ext Γ A) (K.ext Γ B) :=
  (TypeOver.isoOfValEq (C := K) (A := ⟨A⟩) (B := ⟨B⟩) same).hom.substitution

@[simp] theorem extensionCast_refl (A : K.Ty Γ) : extensionCast (K := K) (rfl : A = A) =
    K.idS (K.ext Γ A) := rfl

theorem extensionCast_projection (same : A = B) :
    K.compS (K.wk B) (extensionCast same) = K.wk A := by
  cases same
  exact K.comp_id _

theorem extensionCast_newest (same : A = B) :
    HEq (K.tmSub (K.vz B) (extensionCast same)) (K.vz A) :=
  TypeOver.isoOfValEq_hom_reads_vz same

end Mettapedia.TypeTheory.ContextualTypePresentationCast
