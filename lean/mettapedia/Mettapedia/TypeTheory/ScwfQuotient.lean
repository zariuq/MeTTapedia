import Mathlib.Data.Quot
import Mettapedia.GSLT.Core.ContextualStrictCwfMorphism

/-!
# Quotients of simply typed categories with families

A congruence identifies substitutions and terms while retaining contexts and
types. Compatibility with composition, term substitution, and comprehension
is exactly what is needed to descend the structural operations. The quotient
projection is a strict CwF morphism after the constant-family inclusion.

This is a quotient of a simply typed contextual structure. It does not
quotient dependent type families or assume equality reflection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ContextualLadder

universe u v w w'

namespace Scwf

/-- A many-sorted congruence on substitutions and terms, with fixed contexts
and types. -/
structure Congruence (S : Scwf.{u, v, w, w'}) where
  sub : (Γ Δ : S.Ctx) → Setoid (S.Sub Γ Δ)
  tm : (Γ : S.Ctx) → (A : S.Ty) → Setoid (S.Tm Γ A)
  comp_rel : ∀ {Γ Δ Θ} {σ σ' : S.Sub Δ Θ} {τ τ' : S.Sub Γ Δ},
    (sub Δ Θ).r σ σ' → (sub Γ Δ).r τ τ' →
      (sub Γ Θ).r (S.compS σ τ) (S.compS σ' τ')
  tmSub_rel : ∀ {Γ Δ A} {t t' : S.Tm Δ A} {σ σ' : S.Sub Γ Δ},
    (tm Δ A).r t t' → (sub Γ Δ).r σ σ' →
      (tm Γ A).r (S.tmSub t σ) (S.tmSub t' σ')
  pair_rel : ∀ {Γ Δ A} {σ σ' : S.Sub Γ Δ} {t t' : S.Tm Γ A},
    (sub Γ Δ).r σ σ' → (tm Γ A).r t t' →
      (sub Γ (S.ext Δ A)).r (S.pair σ A t) (S.pair σ' A t')

namespace Congruence

variable {S : Scwf.{u, v, w, w'}} (R : S.Congruence)

abbrev Sub (Γ Δ : S.Ctx) := Quotient (R.sub Γ Δ)
abbrev Tm (Γ : S.Ctx) (A : S.Ty) := Quotient (R.tm Γ A)

def comp {Γ Δ Θ : S.Ctx} : R.Sub Δ Θ → R.Sub Γ Δ → R.Sub Γ Θ :=
  Quotient.map₂ S.compS (fun {_ _} hσ {_ _} hτ => R.comp_rel hσ hτ)

def substitute {Γ Δ : S.Ctx} {A : S.Ty} : R.Tm Δ A → R.Sub Γ Δ → R.Tm Γ A :=
  Quotient.map₂ S.tmSub (fun {_ _} ht {_ _} hσ => R.tmSub_rel ht hσ)

def extend {Γ Δ : S.Ctx} (A : S.Ty) :
    R.Sub Γ Δ → R.Tm Γ A → R.Sub Γ (S.ext Δ A) :=
  Quotient.map₂ (fun σ t => S.pair σ A t) (fun {_ _} hσ {_ _} ht => R.pair_rel hσ ht)

/-- The quotient retains all contextual structure and its comprehension laws. -/
def quotient : Scwf.{u, v, w, w'} where
  Ctx := S.Ctx
  Sub := R.Sub
  idS Γ := Quotient.mk _ (S.idS Γ)
  compS := R.comp
  id_comp := by
    intro Γ Δ σ
    induction σ using Quotient.inductionOn with
    | _ σ => exact congrArg (Quotient.mk _) (S.id_comp σ)
  comp_id := by
    intro Γ Δ σ
    induction σ using Quotient.inductionOn with
    | _ σ => exact congrArg (Quotient.mk _) (S.comp_id σ)
  comp_assoc := by
    intro Γ Δ Θ Ξ σ τ ρ
    induction σ, τ, ρ using Quotient.inductionOn₃ with
    | _ σ τ ρ => exact congrArg (Quotient.mk _) (S.comp_assoc σ τ ρ)
  Ty := S.Ty
  Tm := R.Tm
  tmSub := R.substitute
  tmSub_id := by
    intro Γ A t
    induction t using Quotient.inductionOn with
    | _ t => exact congrArg (Quotient.mk _) (S.tmSub_id t)
  tmSub_comp := by
    intro Γ Δ Θ A t σ τ
    induction t, σ, τ using Quotient.inductionOn₃ with
    | _ t σ τ => exact congrArg (Quotient.mk _) (S.tmSub_comp t σ τ)
  ext := S.ext
  wk A := Quotient.mk _ (S.wk A)
  vz A := Quotient.mk _ (S.vz A)
  pair σ A t := R.extend A σ t
  wk_pair := by
    intro Γ Δ σ A t
    induction σ, t using Quotient.inductionOn₂ with
    | _ σ t => exact congrArg (Quotient.mk _) (S.wk_pair σ A t)
  vz_pair := by
    intro Γ Δ σ A t
    induction σ, t using Quotient.inductionOn₂ with
    | _ σ t => exact congrArg (Quotient.mk _) (S.vz_pair σ A t)
  pair_eta := by
    intro Γ Δ A σ
    induction σ using Quotient.inductionOn with
    | _ σ => exact congrArg (Quotient.mk _) (S.pair_eta A σ)

open CategoryTheory

/-- The projection on context categories identifies exactly the declared
substitution congruence. -/
def projection : S.toCwf.base.Context ⥤ R.quotient.toCwf.base.Context where
  obj Γ := ⟨Γ.val⟩
  map σ := Quotient.mk _ σ
  map_id _ := rfl
  map_comp _ _ := rfl

theorem projection_eq_iff {Γ Δ : S.toCwf.base.Context} (σ τ : Γ ⟶ Δ) :
    R.projection.map σ = R.projection.map τ ↔ (R.sub Γ.val Δ.val).r σ τ :=
  Quotient.eq

theorem projection_surjective (Γ Δ : S.toCwf.base.Context) :
    Function.Surjective (R.projection.map (X := Γ) (Y := Δ)) := by
  intro σ
  exact Quotient.exists_rep σ

/-- Types are unchanged and term classes vary naturally under substitution. -/
def familyProjection : CwfFamilyMorphism S.toCwf R.quotient.toCwf where
  base := R.projection
  family :=
    { app := fun _ =>
        { onIndex := id
          onFibre := fun _ t => Quotient.mk _ t }
      naturality := by
        intro Γ Δ σ
        apply IndexedFamily.Hom.ext
        · rfl
        · intro A t
          rfl }

end Congruence
end Scwf

namespace ScwfWithTerminal

variable (S : ScwfWithTerminal.{u, v, w, w'}) (R : S.toScwf.Congruence)

/-- The empty context remains terminal after quotienting substitutions. -/
def quotient : ScwfWithTerminal.{u, v, w, w'} where
  toScwf := R.quotient
  empty := S.empty
  toEmpty Γ := Quotient.mk _ (S.toEmpty Γ)
  toEmpty_unique := by
    intro Γ σ
    induction σ using Quotient.inductionOn with
    | _ σ => exact congrArg (Quotient.mk _) (S.toEmpty_unique Γ σ)

/-- Passing to conversion classes preserves the terminal context and context
comprehension, not merely the term substitution action. -/
def quotientMorphism : StrictCwfMorphism S.toCwfWithTerminal
    (S.quotient R).toCwfWithTerminal where
  toFamilyMorphism := R.familyProjection
  empty_preserved := rfl
  extension_preserved _ _ := rfl
  projection_preserved := by
    intro Γ A
    change Quotient.mk (R.sub _ _) (S.toScwf.wk A) =
      R.quotient.compS (R.quotient.wk A) (R.quotient.idS _)
    exact (R.quotient.comp_id (R.quotient.wk A)).symm
  variable_preserved := by
    intro Γ A
    change HEq (Quotient.mk (R.tm _ _) (S.toScwf.vz A))
      (R.quotient.tmSub (R.quotient.vz A) (R.quotient.idS _))
    exact heq_of_eq (R.quotient.tmSub_id (R.quotient.vz A)).symm

#print axioms quotient
#print axioms quotientMorphism

end ScwfWithTerminal
end Mettapedia.GSLT.Core.ContextualLadder
