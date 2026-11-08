import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedStrategy

/-!
# Renaming scopes

A reference step renames an equation into any fresh scope; the machine renames it into the scope of
its firing. Their runs agree up to a renaming of scopes. This file gives the renamings and their
laws.

* `sren π`: the substitution moving every variable `(s, x)` to `(π s, x)`, for a permutation `π` of
  scopes; it copies a pattern at `n` to its copy at `π n` (`sren_at`) and is undone by `π⁻¹`
  (`sren_symm`).
* **Most general unifiers are equivariant** (`isMGU_sren`): renaming a problem by `sren π` renames its
  most general unifiers by conjugation (`conj`).
* The renamings act on expressions, frames, evaluation contexts and source rows, and commute with
  filling and unloading (`fill_subst`, `ctxOf_subst`, `epat_at_sren`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-! ## Scope renamings -/

/-- The variable map of a permutation of scopes. -/
def vperm (π : Equiv.Perm ℕ) : Equiv.Perm (ℕ × ℕ) := Equiv.prodCongr π (Equiv.refl ℕ)

/-- **Rename scopes** by a permutation. -/
def sren (π : Equiv.Perm ℕ) : Subst rows := fun v => .var (vperm π v)

theorem sren_var (π : Equiv.Perm ℕ) (v : ℕ × ℕ) : sren π v = .var (π v.1, v.2) := rfl

theorem sren_at (π : Equiv.Perm ℕ) (n : ℕ) : ∀ p : Pat, (sren π).applyTerm (p.at n) = p.at (π n)
  | .var _ => rfl
  | .sym _ => rfl
  | .cell a b => by rw [Pat.at, apply_node, sren_at π n a, sren_at π n b]; rfl

theorem sren_symm (π : Equiv.Perm ℕ) (t : Tm) :
    (sren π.symm).applyTerm ((sren π).applyTerm t) = t := by
  rw [← Subst.applyTerm_comp]
  refine Subst.applyTerm_eq_self fun v _ => ?_
  show (sren π.symm).applyTerm (.var (π v.1, v.2)) = .var v
  rw [Subst.applyTerm_var, sren_var]
  simp

theorem sren_symm' (π : Equiv.Perm ℕ) (t : Tm) :
    (sren π).applyTerm ((sren π.symm).applyTerm t) = t := by
  have := sren_symm π.symm t
  rwa [Equiv.symm_symm] at this

theorem mem_freeVars_sren {π : Equiv.Perm ℕ} {t : Tm} {x : ℕ × ℕ} :
    x ∈ ((sren π).applyTerm t).freeVars ↔ ∃ y ∈ t.freeVars, x = vperm π y := by
  rw [Subst.mem_freeVars_applyTerm (σ := rows)]
  refine exists_congr fun y => and_congr Iff.rfl ?_
  show x ∈ (Term.var (vperm π y) : Tm).freeVars ↔ _
  rw [Term.mem_freeVars_var (σ := rows)]

/-- **Conjugation of a substitution by a scope renaming.** -/
def conj (π : Equiv.Perm ℕ) (θ : Subst rows) : Subst rows := sren π ∘ₛ θ ∘ₛ sren π.symm

theorem conj_apply (π : Equiv.Perm ℕ) (θ : Subst rows) (t : Tm) :
    (conj π θ).applyTerm ((sren π).applyTerm t) = (sren π).applyTerm (θ.applyTerm t) := by
  rw [conj, Subst.applyTerm_comp, Subst.applyTerm_comp, sren_symm]

theorem conj_var (π : Equiv.Perm ℕ) (θ : Subst rows) (w : ℕ × ℕ) :
    conj π θ w = (sren π).applyTerm (θ ((vperm π).symm w)) := rfl

/-- Renaming both sides of every equation. -/
def renameProblem (π : Equiv.Perm ℕ) (P : List (Tm × Tm)) : List (Tm × Tm) :=
  P.map fun e => ((sren π).applyTerm e.1, (sren π).applyTerm e.2)

theorem mem_eqVars_rename {π : Equiv.Perm ℕ} {P : List (Tm × Tm)} {x : ℕ × ℕ} :
    x ∈ eqVars (renameProblem π P) ↔ (vperm π).symm x ∈ eqVars P := by
  rw [mem_eqVars (σ := rows), mem_eqVars (σ := rows)]
  constructor
  · rintro ⟨e', member, occurs⟩
    obtain ⟨e, eIn, rfl⟩ := List.mem_map.mp member
    refine ⟨e, eIn, ?_⟩
    rcases occurs with occurs | occurs
    · obtain ⟨y, yIn, rfl⟩ := mem_freeVars_sren.mp occurs
      rw [Equiv.symm_apply_apply]
      exact .inl yIn
    · obtain ⟨y, yIn, rfl⟩ := mem_freeVars_sren.mp occurs
      rw [Equiv.symm_apply_apply]
      exact .inr yIn
  · rintro ⟨e, eIn, occurs⟩
    refine ⟨_, List.mem_map.mpr ⟨e, eIn, rfl⟩, ?_⟩
    rcases occurs with occurs | occurs
    · exact .inl (mem_freeVars_sren.mpr ⟨_, occurs, (Equiv.apply_symm_apply _ x).symm⟩)
    · exact .inr (mem_freeVars_sren.mpr ⟨_, occurs, (Equiv.apply_symm_apply _ x).symm⟩)

/-- **Most general unifiers are equivariant under scope renamings.** -/
theorem isMGU_sren (π : Equiv.Perm ℕ) {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) :
    IsMGU (renameProblem π P) (conj π θ) := by
  refine ⟨fun e' member => ?_, fun δ unifies => ?_, ?_⟩
  · obtain ⟨e, eIn, rfl⟩ := List.mem_map.mp member
    show (conj π θ).applyTerm ((sren π).applyTerm e.1) = (conj π θ).applyTerm ((sren π).applyTerm e.2)
    rw [conj_apply, conj_apply, mgu.unifies e eIn]
  · have back : Unifies (δ ∘ₛ sren π) P := fun e eIn => by
      rw [Subst.applyTerm_comp, Subst.applyTerm_comp]
      exact unifies _ (List.mem_map.mpr ⟨e, eIn, rfl⟩)
    obtain ⟨ρ, hρ⟩ := mgu.general _ back
    refine ⟨ρ ∘ₛ sren π.symm, fun w => ?_⟩
    rw [conj_var, Subst.applyTerm_comp, sren_symm, ← hρ]
    show δ w = δ.applyTerm (Term.var (vperm π ((vperm π).symm w)) : Tm)
    rw [Equiv.apply_symm_apply, Subst.applyTerm_var]
  · refine ⟨fun w notIn => ?_, fun w wIn => ?_, fun w x hx => ?_⟩
    · have notIn' : (vperm π).symm w ∉ eqVars P := fun h => notIn (mem_eqVars_rename.mpr h)
      rw [conj_var, mgu.relevant.fixes _ notIn', Subst.applyTerm_var]
      show (Term.var (vperm π ((vperm π).symm w)) : Tm) = _
      rw [Equiv.apply_symm_apply]
    · intro x hx
      rw [conj_var] at hx
      obtain ⟨y, yIn, rfl⟩ := mem_freeVars_sren.mp hx
      apply mem_eqVars_rename.mpr
      rw [Equiv.symm_apply_apply]
      exact mgu.relevant.range _ (mem_eqVars_rename.mp wIn) yIn
    · rw [conj_var] at hx
      obtain ⟨y, yIn, rfl⟩ := mem_freeVars_sren.mp hx
      rw [conj_var, Equiv.symm_apply_apply, mgu.relevant.unbound _ y yIn, Subst.applyTerm_var]
      rfl

/-! ## Renamings of the source syntax -/

theorem Ex.subst_comp (θ θ' : Subst rows) : ∀ e : Ex, (e.subst θ).subst θ' = e.subst (θ' ∘ₛ θ)
  | .val t => by simp only [Ex.subst, Subst.applyTerm_comp]
  | .pair a b => by simp only [Ex.subst, Ex.subst_comp θ θ' a, Ex.subst_comp θ θ' b]
  | .call a => by simp only [Ex.subst, Ex.subst_comp θ θ' a]

theorem Ex.subst_congr {θ θ' : Subst rows} (same : ∀ v, θ v = θ' v) : ∀ e : Ex, e.subst θ = e.subst θ'
  | .val t => by simp only [Ex.subst, show θ = θ' from funext same]
  | .pair a b => by simp only [Ex.subst, Ex.subst_congr same a, Ex.subst_congr same b]
  | .call a => by simp only [Ex.subst, Ex.subst_congr same a]

/-- Renaming then the conjugate is the substitution then renaming. -/
theorem conj_comp (π : Equiv.Perm ℕ) (θ : Subst rows) : ∀ v, (conj π θ ∘ₛ sren π) v = (sren π ∘ₛ θ) v := by
  intro v
  show (conj π θ).applyTerm ((sren π).applyTerm (.var v)) = (sren π).applyTerm (θ.applyTerm (.var v))
  rw [conj_apply]

theorem Ex.subst_conj (π : Equiv.Perm ℕ) (θ : Subst rows) (e : Ex) :
    (e.subst (sren π)).subst (conj π θ) = (e.subst θ).subst (sren π) := by
  rw [Ex.subst_comp, Ex.subst_comp]
  exact Ex.subst_congr (conj_comp π θ) e

theorem epat_at_sren (π : Equiv.Perm ℕ) (n : ℕ) : ∀ e : EPat, (e.at n).subst (sren π) = e.at (π n)
  | .val p => by rw [EPat.at, Ex.subst, sren_at]; rfl
  | .pair a b => by rw [EPat.at, Ex.subst, epat_at_sren π n a, epat_at_sren π n b]; rfl
  | .call a => by rw [EPat.at, Ex.subst, epat_at_sren π n a]; rfl

/-- Apply a substitution to the data of an evaluation context. -/
def ECtx.subst (θ : Subst rows) : ECtx → ECtx
  | .hole => .hole
  | .pairL E b => .pairL (E.subst θ) (b.subst θ)
  | .pairR v E => .pairR (θ.applyTerm v) (E.subst θ)
  | .arg E => .arg (E.subst θ)

theorem fill_subst (θ : Subst rows) : ∀ (E : ECtx) (e : Ex), (E.fill e).subst θ = (E.subst θ).fill (e.subst θ)
  | .hole, _ => rfl
  | .pairL E b, e => by simp only [ECtx.fill, ECtx.subst, Ex.subst, fill_subst θ E e]
  | .pairR v E, e => by simp only [ECtx.fill, ECtx.subst, Ex.subst, fill_subst θ E e]
  | .arg E, e => by simp only [ECtx.fill, ECtx.subst, Ex.subst, fill_subst θ E e]

theorem comp_subst (θ : Subst rows) : ∀ (E E' : ECtx), (E.comp E').subst θ = (E.subst θ).comp (E'.subst θ)
  | .hole, _ => rfl
  | .pairL E b, E' => by simp only [ECtx.comp, ECtx.subst, comp_subst θ E E']
  | .pairR v E, E' => by simp only [ECtx.comp, ECtx.subst, comp_subst θ E E']
  | .arg E, E' => by simp only [ECtx.comp, ECtx.subst, comp_subst θ E E']

theorem ctxOf_subst (θ : Subst rows) : ∀ K : List Frame, ctxOf (K.map (Frame.subst θ)) = (ctxOf K).subst θ
  | [] => rfl
  | f :: K => by
      rw [List.map_cons, ctxOf, ctxOf, comp_subst, ctxOf_subst θ K]
      cases f <;> rfl

#print axioms sren_at
#print axioms sren_symm
#print axioms isMGU_sren
#print axioms Ex.subst_conj
#print axioms epat_at_sren
#print axioms fill_subst
#print axioms ctxOf_subst

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
