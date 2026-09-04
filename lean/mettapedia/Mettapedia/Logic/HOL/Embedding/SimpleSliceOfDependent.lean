import Mettapedia.Logic.HOL.Syntax.Term

/-!
# Church-style HOL is the non-dependent slice of a minimal dependent core

The plural waist hosts an extensional STT node and an intensional DTT node.
This module proves the smallest synergy theorem between them: the house's
intrinsically typed HOL terms (`Logic/HOL/Syntax/Term.lean`) embed into a
minimal dependent core — Church STT plus dependent `Π` and one universe, a
DHOL-shaped calculus — and their typing is preserved *and reflected*.

* `tyToExpr`, `termToExpr`: the embedding of simple types and typed terms.
* `HasType`: syntax-directed typing of the dependent core (no conversion
  rule, so typing is unique: `HasType.unique`).
* `termToExpr_typed`: every HOL term is typed at its embedded type.
* `image_typing_reflects`: an embedded term has no other embedded type.
* `isSimple_iff_image`: the bvar-free types built from `prop`, `base`, `pi`
  are exactly HOL's types.
* `dependentType_formed`, `dependentType_not_image`: a genuinely dependent
  type is formed in the core and lies outside HOL's image.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The dependent core -/

/-- Expressions of the minimal dependent core, de Bruijn indexed.  Types and
terms share one syntax; `tyFam b` is a declared type family `b → 𝒰` used only
to exhibit genuine dependency. -/
inductive Expr (Base : Type u) (Const : Ty Base → Type v) : Type (max u v) where
  | bvar : Nat → Expr Base Const
  | univ : Expr Base Const
  | prop : Expr Base Const
  | base : Base → Expr Base Const
  | pi : Expr Base Const → Expr Base Const → Expr Base Const
  | lam : Expr Base Const → Expr Base Const → Expr Base Const
  | app : Expr Base Const → Expr Base Const → Expr Base Const
  | const : (τ : Ty Base) → Const τ → Expr Base Const
  | tyFam : Base → Expr Base Const
  | top : Expr Base Const
  | bot : Expr Base Const
  | and : Expr Base Const → Expr Base Const → Expr Base Const
  | or : Expr Base Const → Expr Base Const → Expr Base Const
  | imp : Expr Base Const → Expr Base Const → Expr Base Const
  | not : Expr Base Const → Expr Base Const
  | eq : Expr Base Const → Expr Base Const → Expr Base Const
  | all : Expr Base Const → Expr Base Const → Expr Base Const
  | ex : Expr Base Const → Expr Base Const → Expr Base Const

namespace Expr

/-- Shift free indices `≥ k` up by one. -/
def shiftAt (k : Nat) : Expr Base Const → Expr Base Const
  | bvar i => if i < k then bvar i else bvar (i + 1)
  | univ => univ
  | prop => prop
  | base b => base b
  | pi A B => pi (shiftAt k A) (shiftAt (k + 1) B)
  | lam A b => lam (shiftAt k A) (shiftAt (k + 1) b)
  | app f a => app (shiftAt k f) (shiftAt k a)
  | const τ c => const τ c
  | tyFam b => tyFam b
  | top => top
  | bot => bot
  | and p q => and (shiftAt k p) (shiftAt k q)
  | or p q => or (shiftAt k p) (shiftAt k q)
  | imp p q => imp (shiftAt k p) (shiftAt k q)
  | not p => not (shiftAt k p)
  | eq a b => eq (shiftAt k a) (shiftAt k b)
  | all A b => all (shiftAt k A) (shiftAt (k + 1) b)
  | ex A b => ex (shiftAt k A) (shiftAt (k + 1) b)

/-- Shift free indices up by `n`. -/
def shiftN : Nat → Expr Base Const → Expr Base Const
  | 0, e => e
  | n + 1, e => shiftAt 0 (shiftN n e)

/-- Substitute `s` for index `k`, lowering higher indices. -/
def substAt (k : Nat) (s : Expr Base Const) : Expr Base Const → Expr Base Const
  | bvar i => if i < k then bvar i else if i = k then shiftN k s else bvar (i - 1)
  | univ => univ
  | prop => prop
  | base b => base b
  | pi A B => pi (substAt k s A) (substAt (k + 1) s B)
  | lam A b => lam (substAt k s A) (substAt (k + 1) s b)
  | app f a => app (substAt k s f) (substAt k s a)
  | const τ c => const τ c
  | tyFam b => tyFam b
  | top => top
  | bot => bot
  | and p q => and (substAt k s p) (substAt k s q)
  | or p q => or (substAt k s p) (substAt k s q)
  | imp p q => imp (substAt k s p) (substAt k s q)
  | not p => not (substAt k s p)
  | eq a b => eq (substAt k s a) (substAt k s b)
  | all A b => all (substAt k s A) (substAt (k + 1) s b)
  | ex A b => ex (substAt k s A) (substAt (k + 1) s b)

end Expr

open Expr

/-- Simple types as core types: `⇒` becomes a non-dependent `Π`. -/
def tyToExpr : Ty Base → Expr Base Const
  | .prop => Expr.prop
  | .base b => Expr.base b
  | .arr σ τ => Expr.pi (tyToExpr σ) (tyToExpr τ)

/-- Syntax-directed typing of the dependent core.  There is no conversion
rule, so this is the formation/typing skeleton shared by the STT and DTT
nodes; computation is a separate layer. -/
inductive HasType : List (Expr Base Const) → Expr Base Const → Expr Base Const → Prop where
  | var {Γ : List (Expr Base Const)} {i : Nat} {A : Expr Base Const}
      (lookup : Γ[i]? = some A) : HasType Γ (bvar i) (shiftN (i + 1) A)
  | base {Γ} (b : Base) : HasType Γ (base b) univ
  | prop {Γ} : HasType Γ prop univ
  | pi {Γ A B} : HasType Γ A univ → HasType (A :: Γ) B univ → HasType Γ (pi A B) univ
  | lam {Γ A b B} : HasType Γ A univ → HasType (A :: Γ) b B →
      HasType Γ (lam A b) (pi A B)
  | app {Γ f a A B} : HasType Γ f (pi A B) → HasType Γ a A →
      HasType Γ (app f a) (substAt 0 a B)
  | const {Γ} (τ : Ty Base) (c : Const τ) : HasType Γ (const τ c) (tyToExpr τ)
  | tyFam {Γ} (b : Base) : HasType Γ (tyFam b) (pi (base b) univ)
  | top {Γ} : HasType Γ top prop
  | bot {Γ} : HasType Γ bot prop
  | and {Γ p q} : HasType Γ p prop → HasType Γ q prop → HasType Γ (and p q) prop
  | or {Γ p q} : HasType Γ p prop → HasType Γ q prop → HasType Γ (or p q) prop
  | imp {Γ p q} : HasType Γ p prop → HasType Γ q prop → HasType Γ (imp p q) prop
  | not {Γ p} : HasType Γ p prop → HasType Γ (not p) prop
  | eq {Γ a b A} : HasType Γ a A → HasType Γ b A → HasType Γ (eq a b) prop
  | all {Γ A b} : HasType Γ A univ → HasType (A :: Γ) b prop → HasType Γ (all A b) prop
  | ex {Γ A b} : HasType Γ A univ → HasType (A :: Γ) b prop → HasType Γ (ex A b) prop

/-! ## The embedding -/

/-- Simple contexts as core contexts. -/
def ctxToExpr : Ctx Base → List (Expr Base Const)
  | [] => []
  | τ :: Γ => tyToExpr τ :: ctxToExpr Γ

/-- The de Bruijn index of a typed variable. -/
def varIdx {Γ : Ctx Base} {τ : Ty Base} : Var Γ τ → Nat
  | .vz => 0
  | .vs v => varIdx v + 1

/-- Typed HOL terms as core expressions. -/
def termToExpr {Γ : Ctx Base} {τ : Ty Base} : Term Const Γ τ → Expr Base Const
  | .var v => bvar (varIdx v)
  | .const c => const _ c
  | .app f a => app (termToExpr f) (termToExpr a)
  | .lam (σ := σ) b => lam (tyToExpr σ) (termToExpr b)
  | .top => top
  | .bot => bot
  | .and p q => and (termToExpr p) (termToExpr q)
  | .or p q => or (termToExpr p) (termToExpr q)
  | .imp p q => imp (termToExpr p) (termToExpr q)
  | .not p => not (termToExpr p)
  | .eq a b => eq (termToExpr a) (termToExpr b)
  | .all (σ := σ) b => all (tyToExpr σ) (termToExpr b)
  | .ex (σ := σ) b => ex (tyToExpr σ) (termToExpr b)

/-! ## Embedded types are closed -/

theorem shiftAt_tyToExpr (k : Nat) : ∀ τ : Ty Base,
    shiftAt k (tyToExpr (Const := Const) τ) = tyToExpr τ
  | .prop => rfl
  | .base _ => rfl
  | .arr σ τ => by
      simp only [tyToExpr, shiftAt, shiftAt_tyToExpr k σ, shiftAt_tyToExpr (k + 1) τ]

theorem shiftN_tyToExpr : ∀ (n : Nat) (τ : Ty Base),
    shiftN n (tyToExpr (Const := Const) τ) = tyToExpr τ
  | 0, _ => rfl
  | n + 1, τ => by
      simp only [shiftN, shiftN_tyToExpr n τ, shiftAt_tyToExpr]

theorem substAt_tyToExpr (k : Nat) (s : Expr Base Const) : ∀ τ : Ty Base,
    substAt k s (tyToExpr τ) = tyToExpr τ
  | .prop => rfl
  | .base _ => rfl
  | .arr σ τ => by
      simp only [tyToExpr, substAt, substAt_tyToExpr k s σ, substAt_tyToExpr (k + 1) s τ]

theorem tyToExpr_injective : ∀ {σ τ : Ty Base},
    tyToExpr (Const := Const) σ = tyToExpr τ → σ = τ
  | .prop, .prop, _ => rfl
  | .base _, .base _, h => by
      simp only [tyToExpr, Expr.base.injEq] at h
      rw [h]
  | .arr σ₁ τ₁, .arr σ₂ τ₂, h => by
      simp only [tyToExpr, Expr.pi.injEq] at h
      rw [tyToExpr_injective h.1, tyToExpr_injective h.2]
  | .prop, .base _, h => by simp [tyToExpr] at h
  | .prop, .arr _ _, h => by simp [tyToExpr] at h
  | .base _, .prop, h => by simp [tyToExpr] at h
  | .base _, .arr _ _, h => by simp [tyToExpr] at h
  | .arr _ _, .prop, h => by simp [tyToExpr] at h
  | .arr _ _, .base _, h => by simp [tyToExpr] at h

theorem ctxLookup {Γ : Ctx Base} {τ : Ty Base} : ∀ v : Var Γ τ,
    (ctxToExpr (Const := Const) Γ)[varIdx v]? = some (tyToExpr τ)
  | .vz => rfl
  | .vs v => by
      simp only [ctxToExpr, varIdx, List.getElem?_cons_succ]
      exact ctxLookup v

/-- Embedded types are formed in every context. -/
theorem tyToExpr_formed (Γ : List (Expr Base Const)) : ∀ τ : Ty Base,
    HasType Γ (tyToExpr τ) univ
  | .prop => HasType.prop
  | .base b => HasType.base b
  | .arr σ τ => HasType.pi (tyToExpr_formed Γ σ) (tyToExpr_formed _ τ)

/-! ## Typing is preserved -/

/-- **HOL embeds.**  Every intrinsically typed HOL term is typed in the
dependent core at its embedded type. -/
theorem termToExpr_typed {Γ : Ctx Base} {τ : Ty Base} :
    ∀ t : Term Const Γ τ, HasType (ctxToExpr Γ) (termToExpr t) (tyToExpr τ)
  | .var v => by
      have h := HasType.var (Γ := ctxToExpr (Const := Const) Γ) (ctxLookup v)
      rwa [shiftN_tyToExpr] at h
  | .const c => HasType.const _ c
  | .app f a => by
      have h := HasType.app (termToExpr_typed f) (termToExpr_typed a)
      simp only [termToExpr]
      rwa [substAt_tyToExpr] at h
  | .lam (σ := σ) b =>
      HasType.lam (tyToExpr_formed _ σ) (termToExpr_typed b)
  | .top => HasType.top
  | .bot => HasType.bot
  | .and p q => HasType.and (termToExpr_typed p) (termToExpr_typed q)
  | .or p q => HasType.or (termToExpr_typed p) (termToExpr_typed q)
  | .imp p q => HasType.imp (termToExpr_typed p) (termToExpr_typed q)
  | .not p => HasType.not (termToExpr_typed p)
  | .eq a b => HasType.eq (termToExpr_typed a) (termToExpr_typed b)
  | .all (σ := σ) b => HasType.all (tyToExpr_formed _ σ) (termToExpr_typed b)
  | .ex (σ := σ) b => HasType.ex (tyToExpr_formed _ σ) (termToExpr_typed b)

/-! ## Typing is unique, hence reflected -/

/-- Without a conversion rule, typing is syntax-directed and unique. -/
theorem HasType.unique {Γ : List (Expr Base Const)} {e A : Expr Base Const}
    (h₁ : HasType Γ e A) : ∀ {A' : Expr Base Const}, HasType Γ e A' → A = A' := by
  induction h₁ with
  | var lookup =>
    intro A' h₂
    cases h₂ with
    | var lookup' => rw [Option.some_inj.mp (lookup.symm.trans lookup')]
  | base b => intro A' h₂; cases h₂; rfl
  | prop => intro A' h₂; cases h₂; rfl
  | pi _ _ _ _ => intro A' h₂; cases h₂; rfl
  | lam _ _ _ ihb =>
    intro A' h₂
    cases h₂ with
    | lam _ hb' => rw [ihb hb']
  | app _ _ ihf _ =>
    intro A' h₂
    cases h₂ with
    | app hf' _ =>
      have := ihf hf'
      simp only [Expr.pi.injEq] at this
      rw [this.2]
  | const τ c => intro A' h₂; cases h₂; rfl
  | tyFam b => intro A' h₂; cases h₂; rfl
  | top => intro A' h₂; cases h₂; rfl
  | bot => intro A' h₂; cases h₂; rfl
  | and _ _ _ _ => intro A' h₂; cases h₂; rfl
  | or _ _ _ _ => intro A' h₂; cases h₂; rfl
  | imp _ _ _ _ => intro A' h₂; cases h₂; rfl
  | not _ _ => intro A' h₂; cases h₂; rfl
  | eq _ _ _ _ => intro A' h₂; cases h₂; rfl
  | all _ _ _ _ => intro A' h₂; cases h₂; rfl
  | ex _ _ _ _ => intro A' h₂; cases h₂; rfl

/-- **Reflection.**  An embedded HOL term carries no embedded type other than
its own: the STT node's typing is exactly the core's typing on the image. -/
theorem image_typing_reflects {Γ : Ctx Base} {τ τ' : Ty Base} (t : Term Const Γ τ)
    (h : HasType (ctxToExpr Γ) (termToExpr t) (tyToExpr τ')) : τ' = τ :=
  (tyToExpr_injective ((termToExpr_typed t).unique h)).symm

/-! ## The image is exactly the closed simple types -/

/-- Types built from `prop`, `base`, and `pi` with no free index. -/
inductive IsSimple : Expr Base Const → Prop where
  | prop : IsSimple prop
  | base (b : Base) : IsSimple (base b)
  | pi {A B} : IsSimple A → IsSimple B → IsSimple (pi A B)

theorem isSimple_iff_image (e : Expr Base Const) :
    IsSimple e ↔ ∃ τ : Ty Base, tyToExpr τ = e := by
  constructor
  · intro h
    induction h with
    | prop => exact ⟨.prop, rfl⟩
    | base b => exact ⟨.base b, rfl⟩
    | pi _ _ ihA ihB =>
      obtain ⟨σ, rfl⟩ := ihA
      obtain ⟨τ, rfl⟩ := ihB
      exact ⟨.arr σ τ, rfl⟩
  · rintro ⟨τ, rfl⟩
    induction τ with
    | prop => exact IsSimple.prop
    | base b => exact IsSimple.base b
    | arr σ τ ihσ ihτ => exact IsSimple.pi ihσ ihτ

/-! ## A genuinely dependent type: formed, and outside the image -/

/-- `Π x : b. F_b x` for the declared family `F_b : b → 𝒰`. -/
def dependentType (b : Base) : Expr Base Const :=
  pi (base b) (app (tyFam b) (bvar 0))

theorem dependentType_formed (Γ : List (Expr Base Const)) (b : Base) :
    HasType Γ (dependentType b) univ := by
  refine HasType.pi (HasType.base b) ?_
  have hv : HasType (base b :: Γ) (bvar 0) (shiftN 1 (base b)) :=
    HasType.var (by simp)
  have happ := HasType.app (HasType.tyFam (Γ := base b :: Γ) b) hv
  simpa [shiftN, shiftAt, substAt] using happ

theorem dependentType_not_simple (b : Base) :
    ¬ IsSimple (dependentType (Const := Const) b) := by
  intro h
  cases h with
  | pi _ hB => cases hB

/-- The dependent type is not the image of any simple type. -/
theorem dependentType_not_image (b : Base) :
    ¬ ∃ τ : Ty Base, tyToExpr (Const := Const) τ = dependentType b := by
  intro h
  exact dependentType_not_simple b ((isSimple_iff_image _).mpr h)

#print axioms termToExpr_typed
#print axioms image_typing_reflects
#print axioms isSimple_iff_image
#print axioms dependentType_formed
#print axioms dependentType_not_image

end Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
