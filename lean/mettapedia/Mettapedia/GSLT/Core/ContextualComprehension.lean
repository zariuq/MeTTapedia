import Mettapedia.GSLT.Core.ContextualTypeCategory

/-!
# The dependent universal property of context comprehension

An arrow into an extended context is equivalent to an arrow into the base
together with a term of the reindexed type. The second component is dependent
on the first. Both inverse equations and naturality follow from the existing
CwF laws, including their explicit transport equalities.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

namespace Cwf

variable (C : Cwf.{u, v, w, w'})

abbrev ComprehensionData (Γ Δ : C.Ctx) (A : C.Ty Δ) :=
  Σ σ : C.Sub Γ Δ, C.Tm Γ (C.tySub A σ)

def decompose {Γ Δ : C.Ctx} (A : C.Ty Δ) (σ : C.Sub Γ (C.ext Δ A)) :
    C.ComprehensionData Γ Δ A :=
  ⟨C.compS (C.wk A) σ, cast (by rw [← C.tySub_comp]) (C.tmSub (C.vz A) σ)⟩

def assemble {Γ Δ : C.Ctx} {A : C.Ty Δ} (data : C.ComprehensionData Γ Δ A) :
    C.Sub Γ (C.ext Δ A) := C.pair data.1 A data.2

theorem assemble_decompose {Γ Δ : C.Ctx} (A : C.Ty Δ)
    (σ : C.Sub Γ (C.ext Δ A)) : C.assemble (C.decompose A σ) = σ :=
  C.pair_eta A σ

theorem decompose_assemble {Γ Δ : C.Ctx} {A : C.Ty Δ}
    (data : C.ComprehensionData Γ Δ A) : C.decompose A (C.assemble data) = data := by
  apply Sigma.ext (C.wk_pair data.1 A data.2)
  exact (cast_heq _ _).trans
    ((heq_of_eq (C.vz_pair data.1 A data.2)).trans (cast_heq _ _))

def comprehensionEquiv (Γ Δ : C.Ctx) (A : C.Ty Δ) :
    C.Sub Γ (C.ext Δ A) ≃ C.ComprehensionData Γ Δ A where
  toFun := C.decompose A
  invFun := C.assemble
  left_inv := C.assemble_decompose A
  right_inv := C.decompose_assemble

def precomposeData {Γ Δ Θ : C.Ctx} {A : C.Ty Θ}
    (data : C.ComprehensionData Δ Θ A) (τ : C.Sub Γ Δ) :
    C.ComprehensionData Γ Θ A :=
  ⟨C.compS data.1 τ,
    cast (by rw [C.tySub_comp]) (C.tmSub data.2 τ)⟩

theorem decompose_natural {Γ Δ Θ : C.Ctx} (A : C.Ty Θ)
    (σ : C.Sub Δ (C.ext Θ A)) (τ : C.Sub Γ Δ) :
    C.decompose A (C.compS σ τ) = C.precomposeData (C.decompose A σ) τ := by
  apply Sigma.ext (C.comp_assoc (C.wk A) σ τ).symm
  refine (cast_heq _ _).trans ?_
  refine (TypeOver.tmSub_comp_heq (C.vz A) σ τ).trans ?_
  refine (TypeOver.tmSub_heq ?_ (cast_heq _ _).symm τ).trans (cast_heq _ _).symm
  exact (C.tySub_comp A (C.wk A) σ).symm

theorem assemble_natural {Γ Δ Θ : C.Ctx} {A : C.Ty Θ}
    (data : C.ComprehensionData Δ Θ A) (τ : C.Sub Γ Δ) :
    C.assemble (C.precomposeData data τ) = C.compS (C.assemble data) τ := by
  apply (C.comprehensionEquiv Γ Θ A).injective
  change C.decompose A (C.assemble (C.precomposeData data τ)) =
    C.decompose A (C.compS (C.assemble data) τ)
  rw [C.decompose_assemble, C.decompose_natural, C.decompose_assemble]

theorem pair_distinguishes_terms {Γ Δ : C.Ctx} {A : C.Ty Δ}
    (σ : C.Sub Γ Δ) {first second : C.Tm Γ (C.tySub A σ)}
    (different : first ≠ second) : C.pair σ A first ≠ C.pair σ A second := by
  intro same
  have data := congrArg (C.decompose A) same
  change C.decompose A (C.assemble ⟨σ, first⟩) =
    C.decompose A (C.assemble ⟨σ, second⟩) at data
  rw [C.decompose_assemble, C.decompose_assemble] at data
  exact different (eq_of_heq (Sigma.mk.inj data).2)

end Cwf

end Mettapedia.GSLT.Core.ContextualLadder
