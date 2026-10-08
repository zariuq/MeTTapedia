import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

/-!
# Contextual code: templates with parameters bound inside the code

Terms are well scoped: `Term n` has `n` variables in scope. Beside variables,
symbols, abstraction and application there are four forms for code.

* `cquote k M` is a template: code `M` whose only variables are its own `k`
  parameters. It is closed in every outer variable, so no substitution enters
  it, and its parameters are variables of the code: they are renamed with the
  code and nothing outside can reach them. A sealed name is the case `k = 0`.
* `lift M` constructs a name. Substitution passes through it.
* `drop K` runs code. Running a template gives the function of its
  parameters.
* `cmatch k K P F` inspects code: when `K` is a template of `k` parameters
  whose code has the shape of the pattern `P`, the handler `F` receives the
  names of the pieces the holes of `P` cover.

Patterns form the second level. A hole of a pattern is filled by code that
mentions no variable at all (`Pat.fill`), so a hole can never capture a
variable bound inside the code (`Pat.mentions_fill`).

Variables are de Bruijn indices, so α-equivalent terms are equal. This file
proves the laws of substitution (`subst_subst`) and of filling holes
(`Pat.fill_bind`, `Pat.fill_rename`), and the injectivity of filling a pattern
that covers all its holes (`Pat.fill_injective`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ContextualCode

/-- Patterns: code with holes. `Pat m k` has `m` holes and is read with `k`
variables bound inside the code. Inside a nested template the scope is that
template's own parameters. -/
inductive Pat : Nat → Nat → Type where
  | hole {m k : Nat} : Fin m → Pat m k
  | var {m k : Nat} : Fin k → Pat m k
  | sym {m k : Nat} : String → Pat m k
  | lam {m k : Nat} : Pat m (k + 1) → Pat m k
  | app {m k : Nat} : Pat m k → Pat m k → Pat m k
  | cquote {m k : Nat} (j : Nat) : Pat m j → Pat m k
  | lift {m k : Nat} : Pat m k → Pat m k
  | drop {m k : Nat} : Pat m k → Pat m k
  deriving DecidableEq, Repr

/-- Terms with `n` variables in scope. -/
inductive Term : Nat → Type where
  | var {n : Nat} : Fin n → Term n
  | sym {n : Nat} : String → Term n
  | lam {n : Nat} : Term (n + 1) → Term n
  | app {n : Nat} : Term n → Term n → Term n
  | cquote {n : Nat} (k : Nat) : Term k → Term n
  | lift {n : Nat} : Term n → Term n
  | drop {n : Nat} : Term n → Term n
  | cmatch {n m : Nat} (k : Nat) : Term n → Pat m k → Term n → Term n
  deriving DecidableEq, Repr

namespace Term

/-! ## Renaming -/

/-- A renaming of variables. -/
abbrev Ren (n m : Nat) : Type := Fin n → Fin m

/-- Extend a renaming under a binder. -/
def liftRen {n m : Nat} (ρ : Ren n m) : Ren (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

@[simp] theorem liftRen_zero {n m : Nat} (ρ : Ren n m) : liftRen ρ 0 = 0 := rfl

@[simp] theorem liftRen_succ {n m : Nat} (ρ : Ren n m) (i : Fin n) :
    liftRen ρ i.succ = (ρ i).succ := rfl

theorem liftRen_id {n : Nat} : liftRen (id : Ren n n) = id := by
  funext i
  cases i using Fin.cases <;> rfl

theorem liftRen_comp {n m k : Nat} (ρ : Ren m k) (τ : Ren n m) :
    liftRen (ρ ∘ τ) = liftRen ρ ∘ liftRen τ := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Rename the variables of a term. A template is unchanged. -/
def rename : {n m : Nat} → Ren n m → Term n → Term m
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, _, .sym s => .sym s
  | _, _, ρ, .lam b => .lam (rename (liftRen ρ) b)
  | _, _, ρ, .app f a => .app (rename ρ f) (rename ρ a)
  | _, _, _, .cquote k M => .cquote k M
  | _, _, ρ, .lift M => .lift (rename ρ M)
  | _, _, ρ, .drop K => .drop (rename ρ K)
  | _, _, ρ, .cmatch k K P F => .cmatch k (rename ρ K) P (rename ρ F)

@[simp] theorem rename_id : ∀ {n : Nat} (M : Term n), rename id M = M
  | _, .var _ => rfl
  | _, .sym _ => rfl
  | _, .lam b => by rw [rename, liftRen_id, rename_id b]
  | _, .app f a => by rw [rename, rename_id f, rename_id a]
  | _, .cquote _ _ => rfl
  | _, .lift M => by rw [rename, rename_id M]
  | _, .drop K => by rw [rename, rename_id K]
  | _, .cmatch _ K _ F => by rw [rename, rename_id K, rename_id F]

theorem rename_rename : ∀ {n m k : Nat} (ρ : Ren m k) (τ : Ren n m) (M : Term n),
    rename ρ (rename τ M) = rename (ρ ∘ τ) M
  | _, _, _, _, _, .var _ => rfl
  | _, _, _, _, _, .sym _ => rfl
  | _, _, _, ρ, τ, .lam b => by
      rw [rename, rename, rename, rename_rename, liftRen_comp]
  | _, _, _, ρ, τ, .app f a => by
      rw [rename, rename, rename, rename_rename ρ τ f, rename_rename ρ τ a]
  | _, _, _, _, _, .cquote _ _ => rfl
  | _, _, _, ρ, τ, .lift M => by rw [rename, rename, rename, rename_rename ρ τ M]
  | _, _, _, ρ, τ, .drop K => by rw [rename, rename, rename, rename_rename ρ τ K]
  | _, _, _, ρ, τ, .cmatch _ K _ F => by
      rw [rename, rename, rename, rename_rename ρ τ K, rename_rename ρ τ F]

/-! ## Substitution -/

/-- A substitution of terms for variables. -/
abbrev Sub (n m : Nat) : Type := Fin n → Term m

/-- Extend a substitution under a binder. -/
def liftSub {n m : Nat} (σ : Sub n m) : Sub (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename Fin.succ (σ i))

@[simp] theorem liftSub_zero {n m : Nat} (σ : Sub n m) : liftSub σ 0 = .var 0 := rfl

@[simp] theorem liftSub_succ {n m : Nat} (σ : Sub n m) (i : Fin n) :
    liftSub σ i.succ = rename Fin.succ (σ i) := rfl

/-- Substitute for the variables of a term. Substitution passes through `lift`
and never enters a template. -/
def subst : {n m : Nat} → Sub n m → Term n → Term m
  | _, _, σ, .var i => σ i
  | _, _, _, .sym s => .sym s
  | _, _, σ, .lam b => .lam (subst (liftSub σ) b)
  | _, _, σ, .app f a => .app (subst σ f) (subst σ a)
  | _, _, _, .cquote k M => .cquote k M
  | _, _, σ, .lift M => .lift (subst σ M)
  | _, _, σ, .drop K => .drop (subst σ K)
  | _, _, σ, .cmatch k K P F => .cmatch k (subst σ K) P (subst σ F)

theorem liftSub_ren {n m : Nat} (ρ : Ren n m) :
    liftSub (fun i => (Term.var (ρ i) : Term m)) = fun i => Term.var (liftRen ρ i) := by
  funext i
  cases i using Fin.cases <;> rfl

/-- Substituting variables is renaming. -/
theorem subst_ren : ∀ {n m : Nat} (ρ : Ren n m) (M : Term n),
    subst (fun i => .var (ρ i)) M = rename ρ M
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam b => by rw [subst, rename, liftSub_ren, subst_ren]
  | _, _, ρ, .app f a => by rw [subst, rename, subst_ren ρ f, subst_ren ρ a]
  | _, _, _, .cquote _ _ => rfl
  | _, _, ρ, .lift M => by rw [subst, rename, subst_ren ρ M]
  | _, _, ρ, .drop K => by rw [subst, rename, subst_ren ρ K]
  | _, _, ρ, .cmatch _ K _ F => by rw [subst, rename, subst_ren ρ K, subst_ren ρ F]

@[simp] theorem subst_var {n : Nat} (M : Term n) : subst Term.var M = M := by
  have := subst_ren (id : Ren n n) M
  simpa using this

theorem liftSub_rename {n m k : Nat} (ρ : Ren m k) (σ : Sub n m) :
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
  | _, _, _, _, _, .cquote _ _ => rfl
  | _, _, _, ρ, σ, .lift M => by rw [subst, rename, subst, rename_subst ρ σ M]
  | _, _, _, ρ, σ, .drop K => by rw [subst, rename, subst, rename_subst ρ σ K]
  | _, _, _, ρ, σ, .cmatch _ K _ F => by
      rw [subst, rename, subst, rename_subst ρ σ K, rename_subst ρ σ F]

theorem liftSub_comp_liftRen {n m k : Nat} (σ : Sub m k) (ρ : Ren n m) :
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
  | _, _, _, _, _, .cquote _ _ => rfl
  | _, _, _, σ, ρ, .lift M => by rw [rename, subst, subst, subst_rename σ ρ M]
  | _, _, _, σ, ρ, .drop K => by rw [rename, subst, subst, subst_rename σ ρ K]
  | _, _, _, σ, ρ, .cmatch _ K _ F => by
      rw [rename, subst, subst, subst_rename σ ρ K, subst_rename σ ρ F]

theorem liftSub_subst {n m k : Nat} (σ : Sub n m) (τ : Sub m k) :
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
  | _, _, _, _, _, .cquote _ _ => rfl
  | _, _, _, τ, σ, .lift M => by rw [subst, subst, subst, subst_subst τ σ M]
  | _, _, _, τ, σ, .drop K => by rw [subst, subst, subst, subst_subst τ σ K]
  | _, _, _, τ, σ, .cmatch _ K _ F => by
      rw [subst, subst, subst, subst_subst τ σ K, subst_subst τ σ F]

/-! ### Instantiating the newest variable -/

/-- The substitution replacing the newest variable. -/
def single {n : Nat} (a : Term n) : Sub (n + 1) n := Fin.cases a Term.var

@[simp] theorem single_zero {n : Nat} (a : Term n) : single a 0 = a := rfl

@[simp] theorem single_succ {n : Nat} (a : Term n) (i : Fin n) : single a i.succ = .var i := rfl

/-- Instantiate the newest variable of a body. -/
def subst1 {n : Nat} (b : Term (n + 1)) (a : Term n) : Term n := subst (single a) b

theorem subst_subst1 {n m : Nat} (σ : Sub n m) (b : Term (n + 1)) (a : Term n) :
    subst σ (b.subst1 a) = (subst (liftSub σ) b).subst1 (subst σ a) := by
  unfold subst1
  rw [subst_subst, subst_subst]
  congr 1
  funext i
  cases i using Fin.cases with
  | zero => rfl
  | succ i =>
      simp only [single_succ, liftSub_succ, subst_rename]
      exact (subst_var (σ i)).symm

theorem rename_subst1 {n m : Nat} (ρ : Ren n m) (b : Term (n + 1)) (a : Term n) :
    rename ρ (b.subst1 a) = (rename (liftRen ρ) b).subst1 (rename ρ a) := by
  rw [← subst_ren, ← subst_ren, ← subst_ren, subst_subst1, liftSub_ren]

/-! ## Closed terms -/

/-- A closed term, placed in any scope. -/
def ofClosed {n : Nat} (M : Term 0) : Term n := rename Fin.elim0 M

/-- Every renaming fixes a closed term. -/
@[simp] theorem rename_ofClosed {n m : Nat} (ρ : Ren n m) (M : Term 0) :
    rename ρ (ofClosed M : Term n) = ofClosed M := by
  unfold ofClosed
  rw [rename_rename]
  congr 1
  funext i
  exact Fin.elim0 i

/-- Every substitution fixes a closed term. -/
@[simp] theorem subst_ofClosed {n m : Nat} (σ : Sub n m) (M : Term 0) :
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

theorem ofClosed_injective {n : Nat} : Function.Injective (ofClosed : Term 0 → Term n) := by
  intro M N h
  have retract : ∀ P : Term 0,
      subst (fun _ => (.sym "" : Term 0)) (ofClosed P : Term n) = P := by
    intro P
    unfold ofClosed
    rw [subst_rename]
    have : (fun i : Fin 0 => (fun _ : Fin n => (Term.sym "" : Term 0)) (Fin.elim0 i)) =
        Term.var := funext fun i => Fin.elim0 i
    rw [this, subst_var]
  rw [← retract M, ← retract N, h]

/-! ## Running a template -/

/-- The function of a template: `k` abstractions around its code. The
innermost abstraction binds parameter `0`, the outermost binds the first
parameter written. -/
def lamN : (k : Nat) → Term k → Term 0
  | 0, M => M
  | k + 1, M => lamN k (.lam M)

/-- Apply `F` to arguments, the first argument first. -/
def appsN {n : Nat} (F : Term n) : {k : Nat} → (Fin k → Term n) → Term n
  | 0, _ => F
  | k + 1, a => .app (appsN F (fun i => a i.castSucc)) (a (Fin.last k))

/-- The substitution giving a template's parameters the closed code of the
arguments, in the order in which the function of the template receives them:
the last argument fills parameter `0`. -/
def fillSub : {k : Nat} → (Fin k → Term 0) → Sub k 0
  | 0, _ => fun i => i.elim0
  | k + 1, V => Fin.cases (V (Fin.last k)) (fillSub (fun i => V i.castSucc))

theorem rename_appsN {n m k : Nat} (ρ : Ren n m) (F : Term n) (a : Fin k → Term n) :
    rename ρ (appsN F a) = appsN (rename ρ F) (fun i => rename ρ (a i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [appsN, rename]
      rw [ih]

theorem subst_appsN {n m k : Nat} (σ : Sub n m) (F : Term n) (a : Fin k → Term n) :
    subst σ (appsN F a) = appsN (subst σ F) (fun i => subst σ (a i)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [appsN, subst]
      rw [ih]

/-! ## Variables a term mentions -/

/-- `M` mentions its variable `i`. A template mentions none. -/
def Mentions : {n : Nat} → Term n → Fin n → Prop
  | _, .var j, i => j = i
  | _, .sym _, _ => False
  | _, .lam b, i => Mentions b i.succ
  | _, .app f a, i => Mentions f i ∨ Mentions a i
  | _, .cquote _ _, _ => False
  | _, .lift M, i => Mentions M i
  | _, .drop K, i => Mentions K i
  | _, .cmatch _ K _ F, i => Mentions K i ∨ Mentions F i

/-- A term is open when it mentions a variable in scope. -/
def Open {n : Nat} (M : Term n) : Prop := ∃ i, Mentions M i

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
        | succ i => exact ⟨i, Fin.succ_inj.mp hi, hb⟩
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
  | _, _, _, .cquote _ _, _ => by simp [rename, Mentions]
  | _, _, ρ, .lift M, j => by
      simp only [rename, Mentions]
      exact mentions_rename ρ M j
  | _, _, ρ, .drop K, j => by
      simp only [rename, Mentions]
      exact mentions_rename ρ K j
  | _, _, ρ, .cmatch _ K _ F, j => by
      simp only [rename, Mentions]
      rw [mentions_rename ρ K, mentions_rename ρ F]
      constructor
      · rintro (⟨i, hi, h⟩ | ⟨i, hi, h⟩)
        · exact ⟨i, hi, .inl h⟩
        · exact ⟨i, hi, .inr h⟩
      · rintro ⟨i, hi, h | h⟩
        · exact .inl ⟨i, hi, h⟩
        · exact .inr ⟨i, hi, h⟩

theorem open_rename {n m : Nat} (ρ : Ren n m) (M : Term n) : Open (rename ρ M) ↔ Open M := by
  unfold Open
  simp only [mentions_rename]
  constructor
  · rintro ⟨_, i, _, h⟩
    exact ⟨i, h⟩
  · rintro ⟨i, h⟩
    exact ⟨ρ i, i, rfl, h⟩

/-- A closed term mentions no variable. -/
theorem not_open_ofClosed {n : Nat} (M : Term 0) : ¬ Open (ofClosed M : Term n) := by
  unfold ofClosed
  rw [open_rename]
  rintro ⟨i, _⟩
  exact Fin.elim0 i

theorem not_mentions_ofClosed {n : Nat} (M : Term 0) (i : Fin n) :
    ¬ Mentions (ofClosed M : Term n) i :=
  fun h => not_open_ofClosed M ⟨i, h⟩

end Term

/-! ## Filling the holes of a pattern -/

namespace Pat

open Term

/-- Fill the holes of a pattern with closed code. A hole is filled by code
that mentions no variable, so it cannot capture a variable bound inside the
code. -/
def fill {m : Nat} (σ : Fin m → Term 0) : {k : Nat} → Pat m k → Term k
  | _, .hole j => ofClosed (σ j)
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .lam P => .lam (fill σ P)
  | _, .app P Q => .app (fill σ P) (fill σ Q)
  | _, .cquote j P => .cquote j (fill σ P)
  | _, .lift P => .lift (fill σ P)
  | _, .drop P => .drop (fill σ P)

/-- The hole `j` occurs in `P`. -/
def HasHole {m : Nat} : {k : Nat} → Pat m k → Fin m → Prop
  | _, .hole j, i => j = i
  | _, .var _, _ => False
  | _, .sym _, _ => False
  | _, .lam P, i => HasHole P i
  | _, .app P Q, i => HasHole P i ∨ HasHole Q i
  | _, .cquote _ P, i => HasHole P i
  | _, .lift P, i => HasHole P i
  | _, .drop P, i => HasHole P i

/-- Every hole occurs in the pattern. -/
def Covers {m k : Nat} (P : Pat m k) : Prop := ∀ j, P.HasHole j

/-- Two fillings agree on every hole where they give the same code. -/
theorem fill_eq_on_hole {m : Nat} {σ σ' : Fin m → Term 0} :
    ∀ {k : Nat} (P : Pat m k) (j : Fin m), P.fill σ = P.fill σ' → P.HasHole j → σ j = σ' j
  | _, .hole i, j, h, hj => by
      simp only [HasHole] at hj
      subst hj
      exact ofClosed_injective h
  | _, .var _, _, _, hj => hj.elim
  | _, .sym _, _, _, hj => hj.elim
  | _, .lam P, j, h, hj => by
      simp only [fill, Term.lam.injEq] at h
      exact fill_eq_on_hole P j h hj
  | _, .app P Q, j, h, hj => by
      simp only [fill, Term.app.injEq] at h
      rcases hj with hj | hj
      · exact fill_eq_on_hole P j h.1 hj
      · exact fill_eq_on_hole Q j h.2 hj
  | _, .cquote _ P, j, h, hj => by
      simp only [fill, Term.cquote.injEq, heq_eq_eq, true_and] at h
      exact fill_eq_on_hole P j h hj
  | _, .lift P, j, h, hj => by
      simp only [fill, Term.lift.injEq] at h
      exact fill_eq_on_hole P j h hj
  | _, .drop P, j, h, hj => by
      simp only [fill, Term.drop.injEq] at h
      exact fill_eq_on_hole P j h hj

/-- **A pattern that covers its holes determines how they were filled.** -/
theorem fill_injective {m k : Nat} {P : Pat m k} (hP : P.Covers) {σ σ' : Fin m → Term 0}
    (h : P.fill σ = P.fill σ') : σ = σ' :=
  funext fun j => fill_eq_on_hole P j h (hP j)

/-- The pattern writes the variable `i` itself, outside its holes. -/
def VarIn {m : Nat} : {k : Nat} → Pat m k → Fin k → Prop
  | _, .hole _, _ => False
  | _, .var j, i => j = i
  | _, .sym _, _ => False
  | _, .lam P, i => VarIn P i.succ
  | _, .app P Q, i => VarIn P i ∨ VarIn Q i
  | _, .cquote _ _, _ => False
  | _, .lift P, i => VarIn P i
  | _, .drop P, i => VarIn P i

/-- **Holes never capture.** A filled pattern mentions exactly the variables
the pattern writes itself: the code in the holes contributes none. -/
theorem mentions_fill {m : Nat} (σ : Fin m → Term 0) :
    ∀ {k : Nat} (P : Pat m k) (i : Fin k), Mentions (P.fill σ) i ↔ P.VarIn i
  | _, .hole j, i => by
      simp only [fill, VarIn, iff_false]
      exact not_mentions_ofClosed (σ j) i
  | _, .var _, _ => Iff.rfl
  | _, .sym _, _ => Iff.rfl
  | _, .lam P, i => mentions_fill σ P i.succ
  | _, .app P Q, i => or_congr (mentions_fill σ P i) (mentions_fill σ Q i)
  | _, .cquote _ _, _ => Iff.rfl
  | _, .lift P, i => mentions_fill σ P i
  | _, .drop P, i => mentions_fill σ P i

/-! ### Renaming the variables of a pattern -/

/-- Rename the variables bound inside the code of a pattern. -/
def rename {m : Nat} : {k k' : Nat} → Term.Ren k k' → Pat m k → Pat m k'
  | _, _, _, .hole j => .hole j
  | _, _, ρ, .var i => .var (ρ i)
  | _, _, _, .sym s => .sym s
  | _, _, ρ, .lam P => .lam (rename (liftRen ρ) P)
  | _, _, ρ, .app P Q => .app (rename ρ P) (rename ρ Q)
  | _, _, _, .cquote j P => .cquote j P
  | _, _, ρ, .lift P => .lift (rename ρ P)
  | _, _, ρ, .drop P => .drop (rename ρ P)

/-- **Filling commutes with renaming.** -/
theorem fill_rename {m : Nat} (σ : Fin m → Term 0) :
    ∀ {k k' : Nat} (ρ : Term.Ren k k') (P : Pat m k),
      (P.rename ρ).fill σ = Term.rename ρ (P.fill σ)
  | _, _, ρ, .hole j => by
      simp only [rename, fill, rename_ofClosed]
  | _, _, _, .var _ => rfl
  | _, _, _, .sym _ => rfl
  | _, _, ρ, .lam P => by
      simp only [rename, fill, Term.rename]
      rw [fill_rename σ (liftRen ρ) P]
  | _, _, ρ, .app P Q => by
      simp only [rename, fill, Term.rename]
      rw [fill_rename σ ρ P, fill_rename σ ρ Q]
  | _, _, _, .cquote _ _ => rfl
  | _, _, ρ, .lift P => by
      simp only [rename, fill, Term.rename]
      rw [fill_rename σ ρ P]
  | _, _, ρ, .drop P => by
      simp only [rename, fill, Term.rename]
      rw [fill_rename σ ρ P]

/-- A pattern without variables of the code, placed in any scope. -/
def ofClosed {m k : Nat} (P : Pat m 0) : Pat m k := P.rename Fin.elim0

theorem fill_ofClosed {m k : Nat} (σ : Fin m → Term 0) (P : Pat m 0) :
    (ofClosed P : Pat m k).fill σ = Term.ofClosed (P.fill σ) :=
  fill_rename σ _ P

/-! ### Substituting patterns for holes -/

/-- Replace each hole by a pattern without variables of the code. -/
def bind {m m' : Nat} (τ : Fin m → Pat m' 0) : {k : Nat} → Pat m k → Pat m' k
  | _, .hole j => ofClosed (τ j)
  | _, .var i => .var i
  | _, .sym s => .sym s
  | _, .lam P => .lam (bind τ P)
  | _, .app P Q => .app (bind τ P) (bind τ Q)
  | _, .cquote j P => .cquote j (bind τ P)
  | _, .lift P => .lift (bind τ P)
  | _, .drop P => .drop (bind τ P)

/-- **Filling after substituting patterns is filling with the filled
patterns.** -/
theorem fill_bind {m m' : Nat} (τ : Fin m → Pat m' 0) (σ : Fin m' → Term 0) :
    ∀ {k : Nat} (P : Pat m k), (P.bind τ).fill σ = P.fill (fun j => (τ j).fill σ)
  | _, .hole j => fill_ofClosed σ (τ j)
  | _, .var _ => rfl
  | _, .sym _ => rfl
  | _, .lam P => by simp only [bind, fill]; rw [fill_bind τ σ P]
  | _, .app P Q => by simp only [bind, fill]; rw [fill_bind τ σ P, fill_bind τ σ Q]
  | _, .cquote _ P => by simp only [bind, fill]; rw [fill_bind τ σ P]
  | _, .lift P => by simp only [bind, fill]; rw [fill_bind τ σ P]
  | _, .drop P => by simp only [bind, fill]; rw [fill_bind τ σ P]

/-- Filling holes with holes changes nothing. -/
theorem bind_hole {m : Nat} : ∀ {k : Nat} (P : Pat m k), P.bind Pat.hole = P
  | _, .hole _ => by
      simp only [bind, ofClosed, rename]
  | _, .var _ => rfl
  | _, .sym _ => rfl
  | _, .lam P => by simp only [bind]; rw [bind_hole P]
  | _, .app P Q => by simp only [bind]; rw [bind_hole P, bind_hole Q]
  | _, .cquote _ P => by simp only [bind]; rw [bind_hole P]
  | _, .lift P => by simp only [bind]; rw [bind_hole P]
  | _, .drop P => by simp only [bind]; rw [bind_hole P]

end Pat

end Mettapedia.TypeTheory.Calculi.ContextualCode
