import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.FourFaceBetaExperiment
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-!
# The syntactic category with families of the simple function fragment

Contexts are lists of simple types and substitutions assign an intrinsically
typed term to each variable.  Capture-avoiding substitution supplies composition;
context extension supplies comprehension.  Terms retain their typing indices.
No quotient by beta or eta conversion is taken here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace FourFaceBetaExperiment.IntrinsicSTT

open Mettapedia.GSLT.Core.ContextualLadder

variable {Γ Δ Θ Ξ : List Ty} {A B : Ty}

def Renaming.id (Γ : List Ty) : Renaming Γ Γ := fun v => v

def Renaming.comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) : Renaming Γ Θ :=
  fun v => τ (ρ v)

@[simp] theorem liftRenaming_id :
    @liftRenaming Γ Γ B (Renaming.id Γ) = @Renaming.id (B :: Γ) := by
  funext A v
  cases v <;> rfl

@[simp] theorem liftRenaming_comp (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    @liftRenaming Γ Θ B (Renaming.comp ρ τ) =
      @Renaming.comp (B :: Γ) (B :: Δ) (B :: Θ) (liftRenaming ρ) (liftRenaming τ) := by
  funext A v
  cases v <;> rfl

@[simp] theorem Term.rename_id (t : Term Γ A) : t.rename (Renaming.id Γ) = t := by
  induction t with
  | var v => rfl
  | lam body ih => simpa only [Term.rename, liftRenaming_id] using congrArg Term.lam ih
  | app f a ihf iha => simp only [Term.rename, ihf, iha]

theorem Term.rename_comp (t : Term Γ A) (ρ : Renaming Γ Δ) (τ : Renaming Δ Θ) :
    (t.rename ρ).rename τ = t.rename (Renaming.comp ρ τ) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | lam body ih => simp only [Term.rename, liftRenaming_comp, ih]
  | app f a ihf iha => simp only [Term.rename, ihf, iha]

def Substitution.id (Γ : List Ty) : Substitution Γ Γ := fun v => .var v

def Substitution.comp (σ : Substitution Γ Δ) (τ : Substitution Δ Θ) :
    Substitution Γ Θ := fun v => (σ v).substitute τ

@[simp] theorem liftSubstitution_id :
    @liftSubstitution Γ Γ B (Substitution.id Γ) = @Substitution.id (B :: Γ) := by
  funext A v
  cases v <;> rfl

@[simp] theorem Term.substitute_id (t : Term Γ A) :
    t.substitute (Substitution.id Γ) = t := by
  induction t with
  | var v => rfl
  | lam body ih =>
      simpa only [Term.substitute, liftSubstitution_id] using congrArg Term.lam ih
  | app f a ihf iha => simp only [Term.substitute, ihf, iha]

theorem Term.substitute_rename (t : Term Γ A) (ρ : Renaming Γ Δ)
    (σ : Substitution Δ Θ) :
    (t.rename ρ).substitute σ = t.substitute (fun v => σ (ρ v)) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | @lam Γ A B body ih =>
      simp only [Term.rename, Term.substitute, ih]
      congr 2
      funext C v
      cases v <;> rfl
  | app f a ihf iha => simp only [Term.rename, Term.substitute, ihf, iha]

theorem Term.rename_substitute (t : Term Γ A) (σ : Substitution Γ Δ)
    (ρ : Renaming Δ Θ) :
    (t.substitute σ).rename ρ = t.substitute (fun v => (σ v).rename ρ) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | @lam Γ A B body ih =>
      simp only [Term.rename, Term.substitute, ih]
      congr 2
      funext C v
      cases v with
      | zero => rfl
      | succ v =>
          simp only [liftSubstitution, Term.rename_comp]
          rfl
  | app f a ihf iha => simp only [Term.rename, Term.substitute, ihf, iha]

theorem Term.substitute_comp (t : Term Γ A) (σ : Substitution Γ Δ)
    (τ : Substitution Δ Θ) :
    (t.substitute σ).substitute τ = t.substitute (Substitution.comp σ τ) := by
  induction t generalizing Δ Θ with
  | var v => rfl
  | @lam Γ A B body ih =>
      simp only [Term.substitute, ih]
      congr 2
      funext C v
      cases v with
      | zero => rfl
      | succ v =>
          change ((σ v).rename weakening).substitute (liftSubstitution τ) =
            ((σ v).substitute τ).rename weakening
          rw [Term.substitute_rename, Term.rename_substitute]
          rfl
  | app f a ihf iha => simp only [Term.substitute, ihf, iha]

@[simp] theorem liftSubstitution_comp (σ : Substitution Γ Δ) (τ : Substitution Δ Θ) :
    @liftSubstitution Γ Θ B (Substitution.comp σ τ) =
      @Substitution.comp (B :: Γ) (B :: Δ) (B :: Θ)
        (liftSubstitution σ) (liftSubstitution τ) := by
  funext A v
  cases v with
  | zero => rfl
  | succ v =>
      change ((σ v).substitute τ).rename weakening =
        ((σ v).rename weakening).substitute (liftSubstitution τ)
      rw [Term.rename_substitute, Term.substitute_rename]
      rfl

@[simp] theorem Substitution.id_comp (σ : Substitution Γ Δ) :
    @Substitution.comp Γ Γ Δ (Substitution.id Γ) σ = @σ := rfl

@[simp] theorem Substitution.comp_id (σ : Substitution Γ Δ) :
    @Substitution.comp Γ Δ Δ σ (Substitution.id Δ) = @σ := by
  funext A v
  exact (σ v).substitute_id

theorem Substitution.comp_assoc (σ : Substitution Γ Δ) (τ : Substitution Δ Θ)
    (υ : Substitution Θ Ξ) :
    @Substitution.comp Γ Θ Ξ (Substitution.comp σ τ) υ =
      @Substitution.comp Γ Δ Ξ σ (Substitution.comp τ υ) := by
  funext A v
  exact (σ v).substitute_comp τ υ

/-- Extend a simultaneous substitution by the image of the newest variable. -/
def Substitution.extend (σ : Substitution Δ Γ) (t : Term Γ A) :
    Substitution (A :: Δ) Γ := fun v =>
  match v with
  | .zero => t
  | .succ v => σ v

/-- The syntactic simply typed category with families.  A categorical
substitution `Γ → Δ` assigns terms in `Γ` to the variables of `Δ`. -/
def syntacticScwf : Scwf where
  Ctx := List Ty
  Sub Γ Δ := Substitution Δ Γ
  idS := Substitution.id
  compS σ τ := Substitution.comp σ τ
  id_comp := Substitution.id_comp
  comp_id := Substitution.comp_id
  comp_assoc σ τ ρ := Substitution.comp_assoc σ τ ρ
  Ty := Ty
  Tm := Term
  tmSub t σ := t.substitute σ
  tmSub_id := Term.substitute_id
  tmSub_comp t σ τ := (t.substitute_comp σ τ).symm
  ext Γ A := A :: Γ
  wk _ := fun v => .var (.succ v)
  vz _ := .var .zero
  pair σ _ t := Substitution.extend σ t
  wk_pair _ _ _ := rfl
  vz_pair _ _ _ := rfl
  pair_eta _ σ := by
    funext A v
    cases v <;> rfl

/-- The empty list is the terminal context of the simple syntax. -/
def syntacticScwfWithTerminal : ScwfWithTerminal where
  toScwf := syntacticScwf
  empty := []
  toEmpty _ := fun v => nomatch v
  toEmpty_unique Γ σ := by
    funext A v
    exact nomatch v

/-- Regard the simple syntax as a CwF with substitution-invariant types. -/
def syntacticCwfWithTerminal : CwfWithTerminal :=
  syntacticScwfWithTerminal.toCwfWithTerminal

/-- Substitution under a binder preserves an older variable's identity. -/
theorem substitute_under_binder (argument : Term Γ A) :
    (Term.lam (Term.var (.succ .zero)) : Term (A :: Γ) (.arr B A)).substitute
        (newestSubstitution argument) =
      .lam (argument.rename weakening) := rfl

/-- Replacing the older variable by the bound one would capture it. -/
theorem weakened_variable_ne_bound_variable :
    (Term.var (.succ .zero) : Term [A, A] A) ≠ Term.var .zero := by
  intro equal
  cases equal

#print axioms Term.substitute_comp
#print axioms syntacticScwf
#print axioms syntacticCwfWithTerminal
#print axioms substitute_under_binder
#print axioms weakened_variable_ne_bound_variable

end FourFaceBetaExperiment.IntrinsicSTT
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
