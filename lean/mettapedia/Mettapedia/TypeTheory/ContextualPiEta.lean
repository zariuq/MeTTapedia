import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Generic-variable eta for dependent products

The section associated with a function is obtained by weakening the supplied
function and applying it to the newest variable. The comprehension equations
identify its result type with the original codomain. Eta is a separate local
equation on those operations; no source interpretation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPiEta

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

theorem lifted_generic_identity {Γ : C.Ctx} (A : C.Ty Γ) :
    C.compS (TypeOver.extensionSubstitution (C.wk A) A)
      (selfExtend C (C.vz A)) = C.idS (C.ext Γ A) := by
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc,
      wk_selfExtend, C.comp_id]
  · have variableTypes :
        C.tySub (C.tySub A (C.wk A))
          (TypeOver.extensionSubstitution (C.wk A) A) =
        C.tySub (C.tySub A (C.wk A)) (C.wk (C.tySub A (C.wk A))) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    exact (TypeOver.tmSub_comp_heq (C.vz A) _ _).trans
      ((TypeOver.tmSub_heq variableTypes
        (TypeOver.vz_extensionSubstitution (C.wk A) A)
        (selfExtend C (C.vz A))).trans
          ((vz_selfExtend (C.vz A)).trans
            ((heq_of_eq (C.tmSub_id (C.vz A))).trans (cast_heq _ _)).symm))

theorem generic_result_type {Γ : C.Ctx} (A : C.Ty Γ)
    (B : C.Ty (C.ext Γ A)) :
    C.tySub (C.tySub B (TypeOver.extensionSubstitution (C.wk A) A))
      (selfExtend C (C.vz A)) = B := by
  rw [← C.tySub_comp, lifted_generic_identity, C.tySub_id]

def genericSection (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.pi A B)) : C.Tm (C.ext Γ A) B :=
  cast (congrArg (C.Tm (C.ext Γ A)) (generic_result_type A B))
    (products.app (reindexFunction products formed (C.wk A) function) (C.vz A))

theorem genericSection_heq (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products)
    {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.pi A B)) :
    HEq (genericSection products formed function)
      (products.app (reindexFunction products formed (C.wk A) function) (C.vz A)) :=
  cast_heq _ _

/-- Eta compares a supplied function with abstraction of its actual
generic-variable application. -/
def PiEta (products : PiOperations C)
    (formed : StrictPiFormationSubstitution products) : Prop :=
  ∀ {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (function : C.Tm Γ (products.pi A B)),
    products.lam (genericSection products formed function) = function

end Mettapedia.TypeTheory.ContextualPiEta
