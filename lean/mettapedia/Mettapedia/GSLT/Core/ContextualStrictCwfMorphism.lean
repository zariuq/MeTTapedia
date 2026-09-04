import Mathlib.CategoryTheory.EqToHom
import Mettapedia.GSLT.Core.ContextualFamilyMorphism
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# Strict morphisms of contextual cores

A strict morphism of categories with families consists of the presheaf-level
pair `(F, σ)` together with preservation of the chosen terminal context and
chosen context comprehensions.  In the concrete presentation used here,
comprehension preservation says that extension contexts, their weakening
projections, and their generic variables are preserved.

Lean records "on the nose" preservation with equalities.  When an equality
identifies the translated extension context with the selected target
extension context, `eqToHom` is the canonical change-of-context map used to
state the projection and variable equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

open CategoryTheory

universe u v w w'

/-- A strict cwf morphism in the sense of a context functor and natural
family map preserving terminal context and comprehension structure on the
nose. -/
structure StrictCwfMorphism
    (C D : CwfWithTerminal.{u, v, w, w'}) where
  toFamilyMorphism : CwfFamilyMorphism C.toCwf D.toCwf
  empty_preserved :
    toFamilyMorphism.base.obj ⟨C.empty⟩ = ⟨D.empty⟩
  extension_preserved : ∀ (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ),
    toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ A⟩ =
      ⟨D.toCwf.ext (toFamilyMorphism.base.obj ⟨Γ⟩).val
        (toFamilyMorphism.mapType A)⟩
  projection_preserved : ∀ (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ),
    toFamilyMorphism.base.map
        (show (⟨C.toCwf.ext Γ A⟩ : C.toCwf.base.Context) ⟶ ⟨Γ⟩ from
          C.toCwf.wk A) =
      eqToHom (extension_preserved Γ A) ≫
        (show
          (⟨D.toCwf.ext (toFamilyMorphism.base.obj ⟨Γ⟩).val
              (toFamilyMorphism.mapType A)⟩ : D.toCwf.base.Context) ⟶
            toFamilyMorphism.base.obj ⟨Γ⟩
          from D.toCwf.wk (toFamilyMorphism.mapType A))
  variable_preserved : ∀ (Γ : C.toCwf.Ctx) (A : C.toCwf.Ty Γ),
    HEq (toFamilyMorphism.mapTerm (C.toCwf.vz A))
      (D.toCwf.tmSub (D.toCwf.vz (toFamilyMorphism.mapType A))
        (show D.toCwf.Sub
            (toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ A⟩).val
            (D.toCwf.ext (toFamilyMorphism.base.obj ⟨Γ⟩).val
              (toFamilyMorphism.mapType A))
          from eqToHom (extension_preserved Γ A)))

namespace StrictCwfMorphism

variable {C D : CwfWithTerminal.{u, v, w, w'}}

/-- The identity strict morphism. -/
def identity (C : CwfWithTerminal.{u, v, w, w'}) :
    StrictCwfMorphism C C where
  toFamilyMorphism := CwfFamilyMorphism.identity C.toCwf
  empty_preserved := rfl
  extension_preserved := fun _ _ => rfl
  projection_preserved := by
    intro Γ A
    change C.toCwf.wk A =
      C.toCwf.compS (C.toCwf.wk A) (C.toCwf.idS _)
    exact (C.toCwf.comp_id (C.toCwf.wk A)).symm
  variable_preserved := by
    intro Γ A
    change HEq (C.toCwf.vz A)
      (C.toCwf.tmSub (C.toCwf.vz A) (C.toCwf.idS _))
    exact ((heq_of_eq (C.toCwf.tmSub_id (C.toCwf.vz A))).trans
      (cast_heq _ _)).symm

/-- Positive canary: the identity strict morphism preserves the selected
empty context exactly. -/
@[simp]
theorem identity_empty (C : CwfWithTerminal.{u, v, w, w'}) :
    (identity C).toFamilyMorphism.base.obj ⟨C.empty⟩ = ⟨C.empty⟩ := rfl

/-- Positive canary: the identity strict morphism maps every type to itself. -/
@[simp]
theorem identity_mapType (C : CwfWithTerminal.{u, v, w, w'})
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) :
    (identity C).toFamilyMorphism.mapType A = A := rfl

/-! ## A terminal-preservation negative canary -/

/-- A strict endomorphism of the families cwf cannot map its selected empty
context `PUnit` to `PEmpty`.  This distinguishes preservation of the chosen
terminal context from an arbitrary object map. -/
theorem families_strict_morphism_cannot_send_empty_to_pempty
    (morphism : StrictCwfMorphism
      (familiesCwfWithTerminal.{w}) (familiesCwfWithTerminal.{w})) :
    morphism.toFamilyMorphism.base.obj
        (⟨PUnit⟩ : familiesCwf.base.Context) ≠
      (⟨PEmpty⟩ : familiesCwf.base.Context) := by
  intro sendsToEmpty
  have selectedTerminal := morphism.empty_preserved
  have contextEquality :
      (⟨PUnit⟩ : familiesCwf.base.Context) = ⟨PEmpty⟩ :=
    selectedTerminal.symm.trans sendsToEmpty
  have typeEquality : PUnit = PEmpty :=
    congrArg ContextualBase.Context.val contextEquality
  exact nomatch cast typeEquality PUnit.unit

#print axioms StrictCwfMorphism.identity
#print axioms StrictCwfMorphism.identity_empty
#print axioms StrictCwfMorphism.identity_mapType
#print axioms StrictCwfMorphism.families_strict_morphism_cannot_send_empty_to_pempty

end StrictCwfMorphism

end Mettapedia.GSLT.Core.ContextualLadder
