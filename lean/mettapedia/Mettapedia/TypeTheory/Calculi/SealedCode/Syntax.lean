import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

/-!
# Lambda terms with sealed names, lift and drop

Terms are well scoped: `Term n` has `n` variables in scope. Beside variables,
symbols, abstraction and application there are three forms for code.

* `quote M` is a sealed name. Its code `M` is closed and is kept as written:
  substitution never enters it.
* `lift M` constructs a name from `M`. Substitution passes through it, so the
  code is filled by the enclosing binders before it is sealed.
* `drop K` runs the code named by `K`.

Renaming and substitution act homomorphically, except that a sealed name is
left unchanged. A closed term embeds into every scope by `ofClosed`, and every
renaming and substitution fixes it.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SealedCode

/-- Terms with `n` variables in scope. -/
inductive Term : Nat → Type where
  | var {n : Nat} : Fin n → Term n
  | sym {n : Nat} : String → Term n
  | lam {n : Nat} : Term (n + 1) → Term n
  | app {n : Nat} : Term n → Term n → Term n
  | quote {n : Nat} : Term 0 → Term n
  | lift {n : Nat} : Term n → Term n
  | drop {n : Nat} : Term n → Term n
  deriving DecidableEq, Repr

namespace Term

variable {n m k : Nat}

/-! ## Renaming -/

/-- A renaming of variables. -/
abbrev Ren (n m : Nat) : Type := Fin n → Fin m

/-- Extend a renaming under a binder. -/
def liftRen (ρ : Ren n m) : Ren (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem liftRen_zero (ρ : Ren n m) : liftRen ρ 0 = 0 := rfl

@[simp] theorem liftRen_succ (ρ : Ren n m) (i : Fin n) :
    liftRen ρ i.succ = (ρ i).succ := rfl

/-- Rename the variables of a term. A sealed name is unchanged. -/
def rename : {n m : Nat} → Ren n m → Term n → Term m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, _, .sym s => .sym s
  | _, _, ρ, .lam b => .lam (rename (liftRen ρ) b)
  | _, _, ρ, .app f a => .app (rename ρ f) (rename ρ a)
  | _, _, _, .quote M => .quote M
  | _, _, ρ, .lift M => .lift (rename ρ M)
  | _, _, ρ, .drop K => .drop (rename ρ K)

theorem liftRen_id : liftRen (id : Ren n n) = id := by
  funext i
  cases i using Fin.cases <;> rfl

theorem liftRen_comp (ρ : Ren m k) (τ : Ren n m) :
    liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext i
  cases i using Fin.cases <;> rfl

@[simp] theorem rename_id : ∀ {n : Nat} (M : Term n), rename id M = M
  | _, .var _ => rfl
  | _, .sym _ => rfl
  | _, .lam b => by rw [rename, liftRen_id, rename_id b]
  | _, .app f a => by rw [rename, rename_id f, rename_id a]
  | _, .quote _ => rfl
  | _, .lift M => by rw [rename, rename_id M]
  | _, .drop K => by rw [rename, rename_id K]

theorem rename_rename : ∀ {n m k : Nat} (ρ : Ren m k) (τ : Ren n m) (M : Term n),
    rename ρ (rename τ M) = rename (ρ ∘ τ) M
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .sym _ => rfl
  | _, _, _, ρ, τ, .lam b => by
      rw [rename, rename, rename, rename_rename, liftRen_comp]
  | _, _, _, ρ, τ, .app f a => by
      rw [rename, rename, rename, rename_rename ρ τ f, rename_rename ρ τ a]
  | _, _, _, _, _, .quote _ => rfl
  | _, _, _, ρ, τ, .lift M => by rw [rename, rename, rename, rename_rename ρ τ M]
  | _, _, _, ρ, τ, .drop K => by rw [rename, rename, rename, rename_rename ρ τ K]

/-- Renaming along an injective renaming is injective. -/
theorem rename_injective : ∀ {n m : Nat} {ρ : Ren n m}, Function.Injective ρ →
    Function.Injective (rename ρ : Term n → Term m)
  | _, _, ρ, hρ, .var i, M', h => by
      cases M' <;> simp only [rename, reduceCtorEq, Term.var.injEq] at h
      exact congrArg Term.var (hρ h)
  | _, _, ρ, _, .sym s, M', h => by
      cases M' <;> simp only [rename, reduceCtorEq, Term.sym.injEq] at h
      exact congrArg Term.sym h
  | _, _, ρ, hρ, .lam b, M', h => by
      cases M' with
      | lam b' =>
          simp only [rename, Term.lam.injEq] at h
          have hlift : Function.Injective (liftRen ρ) := by
            intro i j hij
            cases i using Fin.cases <;> cases j using Fin.cases <;>
              simp_all [Fin.succ_ne_zero, (Fin.succ_ne_zero _).symm, hρ.eq_iff]
          exact congrArg Term.lam (rename_injective hlift h)
      | _ => simp only [rename, reduceCtorEq] at h
  | _, _, ρ, hρ, .app f a, M', h => by
      cases M' with
      | app f' a' =>
          simp only [rename, Term.app.injEq] at h
          rw [rename_injective hρ h.1, rename_injective hρ h.2]
      | _ => simp only [rename, reduceCtorEq] at h
  | _, _, ρ, _, .quote M, M', h => by
      cases M' <;> simp only [rename, reduceCtorEq, Term.quote.injEq] at h
      exact congrArg Term.quote h
  | _, _, ρ, hρ, .lift M, M', h => by
      cases M' with
      | lift M'' =>
          simp only [rename, Term.lift.injEq] at h
          exact congrArg Term.lift (rename_injective hρ h)
      | _ => simp only [rename, reduceCtorEq] at h
  | _, _, ρ, hρ, .drop K, M', h => by
      cases M' with
      | drop K' =>
          simp only [rename, Term.drop.injEq] at h
          exact congrArg Term.drop (rename_injective hρ h)
      | _ => simp only [rename, reduceCtorEq] at h

/-! ## Substitution -/

/-- A substitution of terms for variables. -/
abbrev Sub (n m : Nat) : Type := Fin n → Term m

/-- Extend a substitution under a binder. -/
def liftSub (σ : Sub n m) : Sub (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

@[simp] theorem liftSub_zero (σ : Sub n m) : liftSub σ 0 = .var 0 := rfl

@[simp] theorem liftSub_succ (σ : Sub n m) (i : Fin n) :
    liftSub σ i.succ = rename Fin.succ (σ i) := rfl

/-- Substitute for the variables of a term. Substitution passes through `lift`
and leaves a sealed name unchanged. -/
def subst : {n m : Nat} → Sub n m → Term n → Term m
  | _, _, σ, .var i => σ i
  | _, _, _, .sym s => .sym s
  | _, _, σ, .lam b => .lam (subst (liftSub σ) b)
  | _, _, σ, .app f a => .app (subst σ f) (subst σ a)
  | _, _, _, .quote M => .quote M
  | _, _, σ, .lift M => .lift (subst σ M)
  | _, _, σ, .drop K => .drop (subst σ K)

theorem liftSub_var : liftSub (Term.var : Sub n n) = Term.var := by
  funext i
  cases i using Fin.cases <;> rfl

theorem liftSub_ren (ρ : Ren n m) :
    liftSub (fun i => Term.var (ρ i)) = fun i => Term.var (liftRen ρ i) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Substituting variables is renaming. -/
theorem subst_ren : ∀ {n m : Nat} (ρ : Ren n m) (M : Term n),
    subst (fun i => Term.var (ρ i)) M = rename ρ M
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam b => by rw [subst, rename, liftSub_ren, subst_ren]
  | _, _, ρ, .app f a => by rw [subst, rename, subst_ren ρ f, subst_ren ρ a]
  | _, _, _, .quote _ => rfl
  | _, _, ρ, .lift M => by rw [subst, rename, subst_ren ρ M]
  | _, _, ρ, .drop K => by rw [subst, rename, subst_ren ρ K]

@[simp] theorem subst_var : ∀ {n : Nat} (M : Term n), subst Term.var M = M := by
  intro n M
  have := subst_ren (id : Ren n n) M
  simpa using this

theorem liftSub_rename (ρ : Ren m k) (σ : Sub n m) :
    liftSub (fun i => rename ρ (σ i)) = fun i => rename (liftRen ρ) (liftSub σ i) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      simp only [liftSub_succ, rename_rename]
      rfl

/-- Renaming after substitution. -/
theorem rename_subst : ∀ {n m k : Nat} (ρ : Ren m k) (σ : Sub n m) (M : Term n),
    rename ρ (subst σ M) = subst (fun i => rename ρ (σ i)) M
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .sym _ => rfl
  | _, _, _, ρ, σ, .lam b => by
      rw [subst, rename, subst, rename_subst, liftSub_rename]
  | _, _, _, ρ, σ, .app f a => by
      rw [subst, rename, subst, rename_subst ρ σ f, rename_subst ρ σ a]
  | _, _, _, _, _, .quote _ => rfl
  | _, _, _, ρ, σ, .lift M => by rw [subst, rename, subst, rename_subst ρ σ M]
  | _, _, _, ρ, σ, .drop K => by rw [subst, rename, subst, rename_subst ρ σ K]

theorem liftSub_comp_liftRen (σ : Sub m k) (ρ : Ren n m) :
    liftSub (fun i => σ (ρ i)) = fun i => liftSub σ (liftRen ρ i) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Substitution after renaming. -/
theorem subst_rename : ∀ {n m k : Nat} (σ : Sub m k) (ρ : Ren n m) (M : Term n),
    subst σ (rename ρ M) = subst (fun i => σ (ρ i)) M
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .sym _ => rfl
  | _, _, _, σ, ρ, .lam b => by
      rw [rename, subst, subst, subst_rename, liftSub_comp_liftRen σ ρ]
  | _, _, _, σ, ρ, .app f a => by
      rw [rename, subst, subst, subst_rename σ ρ f, subst_rename σ ρ a]
  | _, _, _, _, _, .quote _ => rfl
  | _, _, _, σ, ρ, .lift M => by rw [rename, subst, subst, subst_rename σ ρ M]
  | _, _, _, σ, ρ, .drop K => by rw [rename, subst, subst, subst_rename σ ρ K]

theorem liftSub_subst (σ : Sub n m) (τ : Sub m k) :
    liftSub (fun i => subst τ (σ i)) = fun i => subst (liftSub τ) (liftSub σ i) := by
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      simp only [liftSub_succ, rename_subst, subst_rename]

/-- Substitutions compose. -/
theorem subst_subst : ∀ {n m k : Nat} (τ : Sub m k) (σ : Sub n m) (M : Term n),
    subst τ (subst σ M) = subst (fun i => subst τ (σ i)) M
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .sym _ => rfl
  | _, _, _, τ, σ, .lam b => by
      rw [subst, subst, subst, subst_subst, liftSub_subst]
  | _, _, _, τ, σ, .app f a => by
      rw [subst, subst, subst, subst_subst τ σ f, subst_subst τ σ a]
  | _, _, _, _, _, .quote _ => rfl
  | _, _, _, τ, σ, .lift M => by rw [subst, subst, subst, subst_subst τ σ M]
  | _, _, _, τ, σ, .drop K => by rw [subst, subst, subst, subst_subst τ σ K]

/-! ## Instantiation -/

/-- The substitution replacing the newest variable. -/
def single (a : Term n) : Sub (n + 1) n := Fin.cases a Term.var

@[simp] theorem single_zero (a : Term n) : single a 0 = a := rfl

@[simp] theorem single_succ (a : Term n) (i : Fin n) : single a i.succ = .var i := rfl

/-- Instantiate the newest variable of a body. -/
def inst (b : Term (n + 1)) (a : Term n) : Term n := subst (single a) b

theorem subst_inst (σ : Sub n m) (b : Term (n + 1)) (a : Term n) :
    subst σ (inst b a) = inst (subst (liftSub σ) b) (subst σ a) := by
  unfold inst
  rw [subst_subst, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      simp only [single_succ, liftSub_succ, subst_rename]
      exact (subst_var (σ i)).symm

theorem rename_inst (ρ : Ren n m) (b : Term (n + 1)) (a : Term n) :
    rename ρ (inst b a) = inst (rename (liftRen ρ) b) (rename ρ a) := by
  rw [← subst_ren, ← subst_ren, ← subst_ren, subst_inst, liftSub_ren]

/-! ## Closed terms -/

/-- A closed term, placed in any scope. -/
def ofClosed (M : Term 0) : Term n := rename Fin.elim0 M

/-- Every renaming fixes a closed term. -/
@[simp] theorem rename_ofClosed (ρ : Ren n m) (M : Term 0) :
    rename ρ (ofClosed M : Term n) = ofClosed M := by
  unfold ofClosed
  rw [rename_rename]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Every substitution fixes a closed term. -/
@[simp] theorem subst_ofClosed (σ : Sub n m) (M : Term 0) :
    subst σ (ofClosed M : Term n) = ofClosed M := by
  unfold ofClosed
  rw [subst_rename, ← subst_ren]
  congr 1
  funext i
  exact Fin.elim0 i

@[simp] theorem ofClosed_zero (M : Term 0) : (ofClosed M : Term 0) = M := by
  unfold ofClosed
  have : (Fin.elim0 : Fin 0 → Fin 0) = id := funext fun i => Fin.elim0 i
  rw [this, rename_id]

theorem ofClosed_injective : Function.Injective (ofClosed : Term 0 → Term n) :=
  rename_injective fun i => Fin.elim0 i

/-! ## Variables a term mentions -/

/-- `M` mentions its variable `i`. The code of a sealed name mentions none. -/
def Mentions : {n : Nat} → Term n → Fin n → Prop
  | _, .var j, i => j = i
  | _, .sym _, _ => False
  | _, .lam b, i => Mentions b i.succ
  | _, .app f a, i => Mentions f i ∨ Mentions a i
  | _, .quote _, _ => False
  | _, .lift M, i => Mentions M i
  | _, .drop K, i => Mentions K i

/-- A term is open when it mentions a variable in scope. -/
def Open (M : Term n) : Prop := ∃ i, Mentions M i

theorem mentions_rename : ∀ {n m : Nat} (ρ : Ren n m) (M : Term n) (j : Fin m),
    Mentions (rename ρ M) j ↔ ∃ i, ρ i = j ∧ Mentions M i
  | _, _, ρ, .var i, j => by simp [rename, Mentions]
  | _, _, _, .sym _, _ => by simp [rename, Mentions]
  | _, _, ρ, .lam b, j => by
      simp only [rename, Mentions]
      rw [mentions_rename]
      constructor
      · rintro ⟨i, hi, hb⟩
        cases i using Fin.cases with
        | zero => exact absurd hi (Fin.succ_ne_zero j).symm
        | succ i =>
            exact ⟨i, Fin.succ_inj.mp hi, hb⟩
      · rintro ⟨i, hi, hb⟩
        exact ⟨i.succ, by simp [hi], hb⟩
  | _, _, ρ, .app f a, j => by
      simp only [rename, Mentions]
      rw [mentions_rename ρ f, mentions_rename ρ a]
      constructor
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · exact ⟨i, hi, .inl h⟩
        · exact ⟨i, hi, .inr h⟩
      · rintro ⟨i, hi, h | h⟩
        · exact .inl ⟨i, hi, h⟩
        · exact .inr ⟨i, hi, h⟩
  | _, _, _, .quote _, _ => by simp [rename, Mentions]
  | _, _, ρ, .lift M, j => by
      simp only [rename, Mentions]
      exact mentions_rename ρ M j
  | _, _, ρ, .drop K, j => by
      simp only [rename, Mentions]
      exact mentions_rename ρ K j

theorem open_rename (ρ : Ren n m) (M : Term n) : Open (rename ρ M) ↔ Open M := by
  unfold Open
  simp only [mentions_rename]
  constructor
  · rintro ⟨_, i, _, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨ρ i, i, rfl, h⟩

/-- A closed term mentions no variable. -/
theorem not_open_ofClosed (M : Term 0) : ¬ Open (ofClosed M : Term n) := by
  unfold ofClosed
  rw [open_rename]
  rintro ⟨i, _⟩
  exact Fin.elim0 i

end Term

end Mettapedia.TypeTheory.Calculi.SealedCode
