import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Structural

/-!
# Annotated terms

The Church-style counterpart of the shared term grammar `Presentation.Tm`: an
abstraction carries the type of its bound variable, `λ (x : A). b`. Every other
former is as in `Presentation.Tm`; in particular pairs carry no annotation.

The domain of an abstraction is what a denotational model needs to validate the
η-law of functions as an equality of denotations: the interpretation of
`λ (x : A). b` sees its argument only through the type `A` (Carneiro, Coquand,
Frabetti Mathieu, Lennon-Bertrand, Melliès and Weirich, *Definitional
Inversion, Without Normalisation*, §2.5). A pair needs no annotation: the
η-law of pairs holds for every typed pair, all of whose observations are pair
observations, and the paper's pairs (§3.1) carry none.

The renaming and substitution algebra is that of `Presentation.Tm`, with the
domain of an abstraction renamed and substituted outside the binder.

This calculus is not the written-domains layer (`Presentation.ATm`,
`TypedEquality.ATyped`), in which a λ may carry its domain as a checked contract
and two terms are equal when their erasures are: there coherence of domains
holds by definition (`TypedEquality.AEqual.of_erase_eq`), and a model sees only
erasures. Here the annotated calculus has its own equality judgment, which a
denotational model can interpret by equality of denotations, and coherence is
a theorem (`Annotated.coherence`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

variable {Head : Type}

/-- Terms whose abstractions carry the type of their bound variable. -/
inductive CTm (Head : Type) : Nat → Type where
  | var {n : Nat} : Fin n → CTm Head n
  | const {n : Nat} : DeclName → CTm Head n
  | head {n : Nat} : Head → CTm Head n
  | pi {n : Nat} : CTm Head n → CTm Head (n + 1) → CTm Head n
  | sigma {n : Nat} : CTm Head n → CTm Head (n + 1) → CTm Head n
  | id {n : Nat} : CTm Head n → CTm Head n → CTm Head n → CTm Head n
  /-- `lam A b` is `λ (x : A). b`. -/
  | lam {n : Nat} : CTm Head n → CTm Head (n + 1) → CTm Head n
  | app {n : Nat} : CTm Head n → CTm Head n → CTm Head n
  | pair {n : Nat} : CTm Head n → CTm Head n → CTm Head n
  | fst {n : Nat} : CTm Head n → CTm Head n
  | snd {n : Nat} : CTm Head n → CTm Head n
  | refl {n : Nat} : CTm Head n → CTm Head n
  deriving DecidableEq, Repr

/-- Simultaneous substitutions of annotated terms. -/
abbrev CSub (Head : Type) (n m : Nat) := Fin n → CTm Head m

namespace CTm

/-! ## Renaming and substitution -/

/-- Renaming of free variables. -/
def rename {n m : Nat} (ρ : Ren n m) : CTm Head n → CTm Head m
  | .var i => .var (ρ i)
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .sigma A B => .sigma (rename ρ A) (rename (liftRen ρ) B)
  | .id A a b => .id (rename ρ A) (rename ρ a) (rename ρ b)
  | .lam A b => .lam (rename ρ A) (rename (liftRen ρ) b)
  | .app f a => .app (rename ρ f) (rename ρ a)
  | .pair a b => .pair (rename ρ a) (rename ρ b)
  | .fst p => .fst (rename ρ p)
  | .snd p => .snd (rename ρ p)
  | .refl a => .refl (rename ρ a)

/-- The identity substitution. -/
def ids {n : Nat} : CSub Head n n := fun i => .var i

/-- A substitution under one more binder. -/
def liftSub {n m : Nat} (σ : CSub Head n m) : CSub Head (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename wk (σ i))

/-- Simultaneous substitution. -/
def subst {n m : Nat} (σ : CSub Head n m) : CTm Head n → CTm Head m
  | .var i => σ i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (subst σ A) (subst (liftSub σ) B)
  | .sigma A B => .sigma (subst σ A) (subst (liftSub σ) B)
  | .id A a b => .id (subst σ A) (subst σ a) (subst σ b)
  | .lam A b => .lam (subst σ A) (subst (liftSub σ) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst p => .fst (subst σ p)
  | .snd p => .snd (subst σ p)
  | .refl a => .refl (subst σ a)

/-- The substitution of `u` for the newest variable. -/
def subst0 {n : Nat} (u : CTm Head n) : CSub Head (n + 1) n :=
  Fin.cases u (fun i => .var i)

/-- Opening the newest binder of `body` at `u`. -/
def inst0 {n : Nat} (u : CTm Head n) (body : CTm Head (n + 1)) : CTm Head n :=
  subst (subst0 u) body

/-- A closed term in an arbitrary context. -/
def liftClosed {n : Nat} (t : CTm Head 0) : CTm Head n :=
  rename Fin.elim0 t

/-! ## Renaming laws -/

theorem rename_ext {n m : Nat} {ρ ξ : Ren n m} (h : ∀ i, ρ i = ξ i) (t : CTm Head n) :
    rename ρ t = rename ξ t := by
  induction t generalizing m with
  | var i => simp [rename, h i]
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [rename, ihA h, ihB (liftRen_ext h)]
  | sigma A B ihA ihB => simp [rename, ihA h, ihB (liftRen_ext h)]
  | id A a b ihA iha ihb => simp [rename, ihA h, iha h, ihb h]
  | lam A b ihA ihb => simp [rename, ihA h, ihb (liftRen_ext h)]
  | app f a ihf iha => simp [rename, ihf h, iha h]
  | pair a b iha ihb => simp [rename, iha h, ihb h]
  | fst p ih => simp [rename, ih h]
  | snd p ih => simp [rename, ih h]
  | refl a ih => simp [rename, ih h]

@[simp] theorem rename_id {n : Nat} (t : CTm Head n) : rename idRen t = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [rename, ihA, ihB]
  | sigma A B ihA ihB => simp [rename, ihA, ihB]
  | id A a b ihA iha ihb => simp [rename, ihA, iha, ihb]
  | lam A b ihA ihb => simp [rename, ihA, ihb]
  | app f a ihf iha => simp [rename, ihf, iha]
  | pair a b iha ihb => simp [rename, iha, ihb]
  | fst p ih => simp [rename, ih]
  | snd p ih => simp [rename, ih]
  | refl a ih => simp [rename, ih]

@[simp] theorem rename_comp {n m k : Nat} (ρ₂ : Ren m k) (ρ₁ : Ren n m) (t : CTm Head n) :
    rename ρ₂ (rename ρ₁ t) = rename (fun i => ρ₂ (ρ₁ i)) t := by
  induction t generalizing m k with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [rename, ihA, ihB]
      rw [rename_ext (liftRen_comp_apply ρ₂ ρ₁) B]
  | sigma A B ihA ihB =>
      simp only [rename, ihA, ihB]
      rw [rename_ext (liftRen_comp_apply ρ₂ ρ₁) B]
  | id A a b ihA iha ihb => simp only [rename, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [rename, ihA, ihb]
      rw [rename_ext (liftRen_comp_apply ρ₂ ρ₁) b]
  | app f a ihf iha => simp only [rename, ihf, iha]
  | pair a b iha ihb => simp only [rename, iha, ihb]
  | fst p ih => simp only [rename, ih]
  | snd p ih => simp only [rename, ih]
  | refl a ih => simp only [rename, ih]

/-- Weakening past one binder commutes with lifting a renaming. -/
theorem rename_liftRen_wk {n m : Nat} (ρ : Ren n m) (t : CTm Head n) :
    rename (liftRen ρ) (rename wk t) = rename wk (rename ρ t) := by
  simp only [rename_comp]
  rfl

/-! ## Substitution laws -/

@[simp] theorem subst0_zero {n : Nat} (u : CTm Head n) : subst0 u 0 = u := rfl

@[simp] theorem subst0_succ {n : Nat} (u : CTm Head n) (i : Fin n) :
    subst0 u i.succ = .var i := rfl

@[simp] theorem liftSub_zero {n m : Nat} (σ : CSub Head n m) :
    liftSub σ 0 = (.var 0 : CTm Head (m + 1)) := rfl

@[simp] theorem liftSub_succ {n m : Nat} (σ : CSub Head n m) (i : Fin n) :
    liftSub σ i.succ = rename wk (σ i) := rfl

theorem liftSub_ext {n m : Nat} {σ τ : CSub Head n m} (h : ∀ i, σ i = τ i) :
    ∀ i, liftSub σ i = liftSub τ i := by
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp [h j]

theorem subst_ext {n m : Nat} {σ τ : CSub Head n m} (h : ∀ i, σ i = τ i) (t : CTm Head n) :
    subst σ t = subst τ t := by
  induction t generalizing m with
  | var i => exact h i
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [subst, ihA h, ihB (liftSub_ext h)]
  | sigma A B ihA ihB => simp [subst, ihA h, ihB (liftSub_ext h)]
  | id A a b ihA iha ihb => simp [subst, ihA h, iha h, ihb h]
  | lam A b ihA ihb => simp [subst, ihA h, ihb (liftSub_ext h)]
  | app f a ihf iha => simp [subst, ihf h, iha h]
  | pair a b iha ihb => simp [subst, iha h, ihb h]
  | fst p ih => simp [subst, ih h]
  | snd p ih => simp [subst, ih h]
  | refl a ih => simp [subst, ih h]

@[simp] theorem liftSub_ids {n : Nat} : liftSub (ids (Head := Head) (n := n)) = ids := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem subst_ids {n : Nat} (t : CTm Head n) : subst ids t = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [subst, ihA, ihB]
  | sigma A B ihA ihB => simp [subst, ihA, ihB]
  | id A a b ihA iha ihb => simp [subst, ihA, iha, ihb]
  | lam A b ihA ihb => simp [subst, ihA, ihb]
  | app f a ihf iha => simp [subst, ihf, iha]
  | pair a b iha ihb => simp [subst, iha, ihb]
  | fst p ih => simp [subst, ih]
  | snd p ih => simp [subst, ih]
  | refl a ih => simp [subst, ih]

theorem rename_liftSub {n m k : Nat} (ρ : Ren m k) (σ : CSub Head n m) (i : Fin (n + 1)) :
    rename (liftRen ρ) (liftSub σ i) = liftSub (fun j => rename ρ (σ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    simp only [liftSub_succ, rename_comp]
    rfl

theorem rename_subst {n m k : Nat} (ρ : Ren m k) (σ : CSub Head n m) (t : CTm Head n) :
    rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  induction t generalizing m k with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [subst_ext (rename_liftSub ρ σ) B]
  | sigma A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [subst_ext (rename_liftSub ρ σ) B]
  | id A a b ihA iha ihb => simp only [rename, subst, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [rename, subst, ihA, ihb]
      rw [subst_ext (rename_liftSub ρ σ) b]
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | pair a b iha ihb => simp only [rename, subst, iha, ihb]
  | fst p ih => simp only [rename, subst, ih]
  | snd p ih => simp only [rename, subst, ih]
  | refl a ih => simp only [rename, subst, ih]

theorem liftSub_liftRen_apply {n m k : Nat} (σ : CSub Head m k) (ρ : Ren n m)
    (i : Fin (n + 1)) : liftSub σ (liftRen ρ i) = liftSub (fun j => σ (ρ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem subst_rename {n m k : Nat} (σ : CSub Head m k) (ρ : Ren n m) (t : CTm Head n) :
    subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t := by
  induction t generalizing m k with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [subst_ext (liftSub_liftRen_apply σ ρ) B]
  | sigma A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [subst_ext (liftSub_liftRen_apply σ ρ) B]
  | id A a b ihA iha ihb => simp only [rename, subst, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [rename, subst, ihA, ihb]
      rw [subst_ext (liftSub_liftRen_apply σ ρ) b]
  | app f a ihf iha => simp only [rename, subst, ihf, iha]
  | pair a b iha ihb => simp only [rename, subst, iha, ihb]
  | fst p ih => simp only [rename, subst, ih]
  | snd p ih => simp only [rename, subst, ih]
  | refl a ih => simp only [rename, subst, ih]

@[simp] theorem subst_liftSub_wk {n m : Nat} (σ : CSub Head n m) (t : CTm Head n) :
    subst (liftSub σ) (rename wk t) = rename wk (subst σ t) := by
  rw [subst_rename, rename_subst]
  rfl

theorem liftSub_comp_apply {n m k : Nat} (τ : CSub Head m k) (σ : CSub Head n m)
    (i : Fin (n + 1)) :
    subst (liftSub τ) (liftSub σ i) = liftSub (fun j => subst τ (σ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact subst_liftSub_wk τ (σ j)

@[simp] theorem subst_comp {n m k : Nat} (τ : CSub Head m k) (σ : CSub Head n m)
    (t : CTm Head n) : subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  induction t generalizing m k with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [subst_ext (liftSub_comp_apply τ σ) B]
  | sigma A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [subst_ext (liftSub_comp_apply τ σ) B]
  | id A a b ihA iha ihb => simp only [subst, ihA, iha, ihb]
  | lam A b ihA ihb =>
      simp only [subst, ihA, ihb]
      rw [subst_ext (liftSub_comp_apply τ σ) b]
  | app f a ihf iha => simp only [subst, ihf, iha]
  | pair a b iha ihb => simp only [subst, iha, ihb]
  | fst p ih => simp only [subst, ih]
  | snd p ih => simp only [subst, ih]
  | refl a ih => simp only [subst, ih]

/-! ## Opening a binder, and closed terms -/

/-- Opening a weakened term cancels the weakening. -/
@[simp] theorem inst0_rename_wk {n : Nat} (u t : CTm Head n) : inst0 u (rename wk t) = t := by
  unfold inst0
  rw [subst_rename]
  exact subst_ids t

/-- Renaming commutes with opening the newest binder. -/
theorem rename_inst0 {n m : Nat} (ρ : Ren n m) (u : CTm Head n) (body : CTm Head (n + 1)) :
    rename ρ (inst0 u body) = inst0 (rename ρ u) (rename (liftRen ρ) body) := by
  unfold inst0
  rw [rename_subst, subst_rename]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

/-- Substitution commutes with opening the newest binder. -/
theorem subst_inst0 {n m : Nat} (σ : CSub Head n m) (u : CTm Head n) (body : CTm Head (n + 1)) :
    subst σ (inst0 u body) = inst0 (subst σ u) (subst (liftSub σ) body) := by
  unfold inst0
  rw [subst_comp, subst_comp]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact (inst0_rename_wk (subst σ u) (σ j)).symm

/-- Opening at the newest variable a body weakened under its binder. -/
@[simp] theorem inst0_var_rename_liftRen_wk {n : Nat} (body : CTm Head (n + 1)) :
    inst0 (.var 0) (rename (liftRen wk) body) = body := by
  unfold inst0
  rw [subst_rename]
  conv => rhs; rw [← subst_ids body]
  apply subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem rename_liftClosed {n m : Nat} (ρ : Ren n m) (t : CTm Head 0) :
    rename ρ (liftClosed t : CTm Head n) = liftClosed t := by
  unfold liftClosed
  rw [rename_comp]
  exact rename_ext (fun i => Fin.elim0 i) t

@[simp] theorem subst_liftClosed {n m : Nat} (σ : CSub Head n m) (t : CTm Head 0) :
    subst σ (liftClosed t : CTm Head n) = liftClosed t := by
  unfold liftClosed
  rw [subst_rename]
  have h : subst (fun i => σ (Fin.elim0 i)) t = subst (fun i => .var (Fin.elim0 i)) t :=
    subst_ext (fun i => Fin.elim0 i) t
  rw [h]
  have h' : subst (fun i : Fin 0 => (.var (Fin.elim0 i) : CTm Head m)) t =
      subst ids (rename Fin.elim0 t) := by
    rw [subst_rename]
    rfl
  rw [h', subst_ids]

end CTm

/-! ## Contexts -/

/-- Contexts of annotated types. -/
inductive CCtx (Head : Type) : Nat → Type where
  | nil : CCtx Head 0
  | snoc {n : Nat} : CCtx Head n → CTm Head n → CCtx Head (n + 1)

namespace CCtx

/-- The type of a variable, in the whole context. -/
def lookup : {n : Nat} → CCtx Head n → Fin n → CTm Head n
  | _, .nil, i => i.elim0
  | _, .snoc Γ A, i => Fin.cases (A.rename wk) (fun j => (lookup Γ j).rename wk) i

@[simp] theorem lookup_snoc_zero {n : Nat} (Γ : CCtx Head n) (A : CTm Head n) :
    lookup (.snoc Γ A) 0 = A.rename wk := rfl

@[simp] theorem lookup_snoc_succ {n : Nat} (Γ : CCtx Head n) (A : CTm Head n) (i : Fin n) :
    lookup (.snoc Γ A) i.succ = (lookup Γ i).rename wk := rfl

end CCtx

/-- A renaming that maps every variable of `Γ` to a variable of `Δ` of the
renamed type. -/
def CCtxRen {n m : Nat} (Γ : CCtx Head n) (Δ : CCtx Head m) (ρ : Ren n m) : Prop :=
  ∀ i, Δ.lookup (ρ i) = (Γ.lookup i).rename ρ

theorem CCtxRen.snoc {n m : Nat} {Γ : CCtx Head n} {Δ : CCtx Head m} {ρ : Ren n m}
    (compatible : CCtxRen Γ Δ ρ) (A : CTm Head n) :
    CCtxRen (.snoc Γ A) (.snoc Δ (A.rename ρ)) (liftRen ρ) := by
  intro i
  refine Fin.cases ?_ ?_ i
  · exact (CTm.rename_liftRen_wk ρ A).symm
  · intro j
    change (Δ.lookup (ρ j)).rename wk = ((Γ.lookup j).rename wk).rename (liftRen ρ)
    rw [compatible j, CTm.rename_liftRen_wk]

theorem CCtxRen.wk {n : Nat} (Γ : CCtx Head n) (A : CTm Head n) :
    CCtxRen Γ (.snoc Γ A) wk := fun _ => rfl

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
