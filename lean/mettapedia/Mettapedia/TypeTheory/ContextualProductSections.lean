import Mettapedia.TypeTheory.ContextualPiEta

/-!
# Complete generic sections of stable dependent products

The local beta, eta and substitution equations give an inverse pair between
source function terms and their full generic-variable bodies. The body is
derived by weakening and application; it is not supplied as an independent
semantic inverse.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualProductSections

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualTypeOperations ContextualPiEta
open ContextualProductComparison (selfExtend)

universe u v w w'
variable {C : Cwf.{u, v, w, w'}}

/-- Local function equations, with the complete contextual action retained. -/
structure StableProducts (C : Cwf.{u, v, w, w'}) where
  operations : PiOperations C
  beta : PiBeta operations
  substitution : StrictPiSubstitution operations
  eta : PiEta operations substitution.1

theorem reindexFunction_lam (products : StableProducts C)
    {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (σ : C.Sub Δ Γ) (body : C.Tm (C.ext Γ A) B) :
    reindexFunction products.operations products.substitution.1 σ
        (products.operations.lam body) =
      products.operations.lam (C.tmSub body (TypeOver.extensionSubstitution σ A)) :=
  eq_of_heq ((reindexFunction_heq products.operations products.substitution.1
    σ (products.operations.lam body)).trans (products.substitution.2.1 σ body))

/-- Applying the actual weakened abstraction to the newest variable
returns the original complete dependent body. -/
theorem genericSection_lam (products : StableProducts C)
    {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (body : C.Tm (C.ext Γ A) B) :
    genericSection products.operations products.substitution.1
      (products.operations.lam body) = body := by
  have mapped :
      reindexFunction products.operations products.substitution.1 (C.wk A)
          (products.operations.lam body) =
        products.operations.lam
          (C.tmSub body (TypeOver.extensionSubstitution (C.wk A) A)) :=
    eq_of_heq ((reindexFunction_heq products.operations products.substitution.1
      (C.wk A) (products.operations.lam body)).trans
        (products.substitution.2.1 (C.wk A) body))
  unfold genericSection
  rw [mapped, products.beta]
  apply eq_of_heq
  have substituted := TypeOver.tmSub_comp_heq body
    (TypeOver.extensionSubstitution (C.wk A) A) (selfExtend C (C.vz A))
  rw [lifted_generic_identity, C.tmSub_id] at substituted
  exact (cast_heq _ _).trans (substituted.symm.trans (cast_heq _ _))

/-- Functions are exactly their whole dependent generic sections. -/
def bodyEquiv (products : StableProducts C)
    {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm Γ (products.operations.pi A B) ≃ C.Tm (C.ext Γ A) B where
  toFun := genericSection products.operations products.substitution.1
  invFun := products.operations.lam
  left_inv := products.eta
  right_inv := genericSection_lam products

/-- The whole generic section commutes with arbitrary source substitution;
the body is transported along the actual lifted comprehension map. -/
theorem genericSection_reindex (products : StableProducts C)
    {Γ Δ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (σ : C.Sub Δ Γ) (function : C.Tm Γ (products.operations.pi A B)) :
    genericSection products.operations products.substitution.1
        (reindexFunction products.operations products.substitution.1 σ function) =
      C.tmSub (genericSection products.operations products.substitution.1 function)
        (TypeOver.extensionSubstitution σ A) := by
  have recovered := products.eta function
  rw [← recovered, reindexFunction_lam, genericSection_lam, genericSection_lam]

end Mettapedia.TypeTheory.ContextualProductSections
