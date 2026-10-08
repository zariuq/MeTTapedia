import Mettapedia.TypeTheory.CwfYonedaCoherence

/-!
# Unique lifts of original future dependent arguments

Every original argument above a composite environment lifts uniquely to
the actual substituted source comprehension. The lift commutes with future
substitution and retains the complete original argument map. This is the
cartesian argument comparison used by dependent function readouts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.CwfYoneda

open CategoryTheory Opposite
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport

universe u w w'
variable (C : Cwf.{u, u, w, w'})

def liftArgument {Γ Δ Θ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (α : C.Sub Θ Δ)
    (argument : (family C A).obj ⟨op (context C Θ), C.compS σ α⟩) :
    (family C (C.tySub A σ)).obj ⟨op (context C Θ), α⟩ :=
  (substitutionIso C A σ).inv.app ⟨op (context C Θ), α⟩ argument

theorem liftArgument_projection {Γ Δ Θ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (α : C.Sub Θ Δ)
    (argument : (family C A).obj ⟨op (context C Θ), C.compS σ α⟩) :
    C.compS (C.wk (C.tySub A σ)) (liftArgument C A σ α argument).val = α :=
  (liftArgument C A σ α argument).property

theorem liftArgument_original {Γ Δ Θ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (α : C.Sub Θ Δ)
    (argument : (family C A).obj ⟨op (context C Θ), C.compS σ α⟩) :
    C.compS (TypeOver.extensionSubstitution σ A) (liftArgument C A σ α argument).val =
      argument.val := by
  have inverse := ConcreteCategory.congr_hom
    ((substitutionIso C A σ).app ⟨op (context C Θ), α⟩).inv_hom_id argument
  have values := congrArg Subtype.val inverse
  exact (substitutionFibreEquiv_val C A σ ⟨op (context C Θ), α⟩ _).symm.trans values

/-- The actual cartesian lift supplies the only map with both required
projection readouts. -/
theorem liftArgument_unique {Γ Δ Θ : C.Ctx} (A : C.Ty Γ) (σ : C.Sub Δ Γ)
    (α : C.Sub Θ Δ)
    (argument : (family C A).obj ⟨op (context C Θ), C.compS σ α⟩)
    (candidate : C.Sub Θ (C.ext Δ (C.tySub A σ)))
    (over : C.compS (C.wk (C.tySub A σ)) candidate = α)
    (original : C.compS (TypeOver.extensionSubstitution σ A) candidate = argument.val) :
    candidate = (liftArgument C A σ α argument).val := by
  have mapped :
      (substitutionIso C A σ).hom.app ⟨op (context C Θ), α⟩
          (⟨candidate, over⟩ : (family C (C.tySub A σ)).obj ⟨op (context C Θ), α⟩) = argument := by
    apply Subtype.ext
    exact (substitutionFibreEquiv_val C A σ ⟨op (context C Θ), α⟩ _).trans original
  have recovered := congrArg
    ((substitutionIso C A σ).inv.app ⟨op (context C Θ), α⟩) mapped
  have roundtrip := ConcreteCategory.congr_hom
    ((substitutionIso C A σ).app ⟨op (context C Θ), α⟩).hom_inv_id
      (⟨candidate, over⟩ : (family C (C.tySub A σ)).obj ⟨op (context C Θ), α⟩)
  exact congrArg Subtype.val (roundtrip.symm.trans recovered)

/-- Changing the future environment precomposes the complete lifted
argument; it cannot select a different witness. -/
theorem liftArgument_substitution {Γ Δ Θ Ψ : C.Ctx}
    (A : C.Ty Γ) (σ : C.Sub Δ Γ) (α : C.Sub Θ Δ) (β : C.Sub Ψ Θ)
    (argument : (family C A).obj ⟨op (context C Θ), C.compS σ α⟩) :
    (liftArgument C A σ (C.compS α β)
      (⟨C.compS argument.val β, by
        change C.compS (C.wk A) (C.compS argument.val β) =
          C.compS σ (C.compS α β)
        have over := argument.property
        change C.compS (C.wk A) argument.val = C.compS σ α at over
        rw [← C.comp_assoc, over, C.comp_assoc]⟩ :
          (family C A).obj ⟨op (context C Ψ), C.compS σ (C.compS α β)⟩)).val =
        C.compS (liftArgument C A σ α argument).val β := by
  apply (liftArgument_unique C A σ (C.compS α β) _ _ ?_ ?_).symm
  · rw [← C.comp_assoc, liftArgument_projection]
  · rw [← C.comp_assoc, liftArgument_original]

end Mettapedia.TypeTheory.CwfYoneda
