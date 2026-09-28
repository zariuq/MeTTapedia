import Mettapedia.GSLT.Core.ContextualAdmission
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism

/-!
# Forgetting admission preserves the contextual structure

Support subtypes forget to their original raw syntax by a faithful context
functor and a natural type-and-term map. With terminal evidence, this is a
strict CwF morphism. Faithfulness concerns admitted substitutions, whose
evidence is propositional support. It makes no injectivity assertion about
forgetting the separate Type-valued derivation fibres.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder.CwfDerivations

open CategoryTheory

universe u v w w' e

variable {C : Cwf.{u, v, w, w'}} (D : CwfDerivations.{u, v, w, w', e} C)

def forgetContext : D.admitted.base.Context ⥤ C.base.Context where
  obj Γ := ⟨Γ.val.val⟩
  map σ := σ.val

instance forgetContext_faithful : D.forgetContext.Faithful where
  map_injective := by
    intro Γ Δ σ τ equal
    exact Subtype.ext equal

def forgetFamily : CwfFamilyMorphism D.admitted C where
  base := D.forgetContext
  family :=
    { app := fun _ =>
        { onIndex := Subtype.val
          onFibre := fun _ => Subtype.val }
      naturality := by intro Γ Δ σ; rfl }

@[simp] theorem forgetFamily_type {Γ : D.Context} (A : D.TypeOver Γ) :
    D.forgetFamily.mapType A = A.val := rfl

@[simp] theorem forgetFamily_term {Γ : D.Context} {A : D.TypeOver Γ} (t : D.Term Γ A) :
    D.forgetFamily.mapTerm t = t.val := rfl

def forgetStrict (T : CwfWithTerminal.{u, v, w, w'})
    (D : CwfDerivations.{u, v, w, w', e} T.toCwf)
    (empty : D.context T.empty)
    (toEmpty : ∀ Γ, D.context Γ → D.substitution Γ T.empty (T.toEmpty Γ)) :
    StrictCwfMorphism (admittedWithTerminal T D empty toEmpty) T where
  toFamilyMorphism := D.forgetFamily
  empty_preserved := rfl
  extension_preserved := fun _ _ => rfl
  projection_preserved := by
    intro Γ A
    change T.toCwf.wk A.val = T.toCwf.compS (T.toCwf.wk A.val) (T.toCwf.idS _)
    exact (T.toCwf.comp_id (T.toCwf.wk A.val)).symm
  variable_preserved := by
    intro Γ A
    change HEq (T.toCwf.vz A.val)
      (T.toCwf.tmSub (T.toCwf.vz A.val) (T.toCwf.idS _))
    exact ((heq_of_eq (T.toCwf.tmSub_id (T.toCwf.vz A.val))).trans
      (cast_heq _ _)).symm

end Mettapedia.GSLT.Core.ContextualLadder.CwfDerivations
