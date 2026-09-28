import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Syntax
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHead

/-!
# Erasure of annotations

`CTm.erase` forgets the domain of every abstraction and is the identity on
every other former. It commutes with renaming, substitution, opening a binder,
closed terms, context lookup, application spines and the change of universe
heads. Erasure is surjective (`erase_annotateWith`) and not injective: the
identity at two different domains has one erasure (`erase_not_injective`).
That second fact is why coherence of annotations is a theorem to prove rather
than a syntactic identity.

An erasure determines the former of the term it erases: the inversion lemmas
(`erase_eq_lam`, `erase_eq_app`, ...) read the shape of an annotated term, and
the erasures of its parts, off its erasure; a spine of a constant, the shape at
which root computations fire, is read off its erasure too
(`erase_eq_constSpine`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Annotated

open Normalization (appSpine)

variable {Head : Type}

namespace CTm

/-- Forget the domains of abstractions. -/
def erase {n : Nat} : CTm Head n → Tm Head n
  | .var i => .var i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (erase A) (erase B)
  | .sigma A B => .sigma (erase A) (erase B)
  | .id A a b => .id (erase A) (erase a) (erase b)
  | .lam _ b => .lam (erase b)
  | .app f a => .app (erase f) (erase a)
  | .pair a b => .pair (erase a) (erase b)
  | .fst p => .fst (erase p)
  | .snd p => .snd (erase p)
  | .refl a => .refl (erase a)

@[simp] theorem erase_rename {n m : Nat} (ρ : Ren n m) (t : CTm Head n) :
    (rename ρ t).erase = Presentation.rename ρ t.erase := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [rename, erase, Presentation.rename, ihA, ihB]
  | sigma A B ihA ihB => simp [rename, erase, Presentation.rename, ihA, ihB]
  | id A a b ihA iha ihb => simp [rename, erase, Presentation.rename, ihA, iha, ihb]
  | lam A b _ ihb => simp [rename, erase, Presentation.rename, ihb]
  | app f a ihf iha => simp [rename, erase, Presentation.rename, ihf, iha]
  | pair a b iha ihb => simp [rename, erase, Presentation.rename, iha, ihb]
  | fst p ih => simp [rename, erase, Presentation.rename, ih]
  | snd p ih => simp [rename, erase, Presentation.rename, ih]
  | refl a ih => simp [rename, erase, Presentation.rename, ih]

/-- The erasure of a substitution. -/
def eraseSub {n m : Nat} (σ : CSub Head n m) : Sub Head n m := fun i => (σ i).erase

theorem eraseSub_liftSub {n m : Nat} (σ : CSub Head n m) (i : Fin (n + 1)) :
    eraseSub (liftSub σ) i = Presentation.liftSub (eraseSub σ) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    exact erase_rename wk (σ j)

@[simp] theorem erase_subst {n m : Nat} (σ : CSub Head n m) (t : CTm Head n) :
    (subst σ t).erase = Presentation.subst (eraseSub σ) t.erase := by
  induction t generalizing m with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB =>
      simp only [subst, erase, Presentation.subst, ihA, ihB]
      rw [Presentation.subst_ext (eraseSub_liftSub σ)]
  | sigma A B ihA ihB =>
      simp only [subst, erase, Presentation.subst, ihA, ihB]
      rw [Presentation.subst_ext (eraseSub_liftSub σ)]
  | id A a b ihA iha ihb => simp only [subst, erase, Presentation.subst, ihA, iha, ihb]
  | lam A b _ ihb =>
      simp only [subst, erase, Presentation.subst, ihb]
      rw [Presentation.subst_ext (eraseSub_liftSub σ)]
  | app f a ihf iha => simp only [subst, erase, Presentation.subst, ihf, iha]
  | pair a b iha ihb => simp only [subst, erase, Presentation.subst, iha, ihb]
  | fst p ih => simp only [subst, erase, Presentation.subst, ih]
  | snd p ih => simp only [subst, erase, Presentation.subst, ih]
  | refl a ih => simp only [subst, erase, Presentation.subst, ih]

@[simp] theorem erase_inst0 {n : Nat} (u : CTm Head n) (body : CTm Head (n + 1)) :
    (inst0 u body).erase = Presentation.inst0 u.erase body.erase := by
  unfold inst0 Presentation.inst0
  rw [erase_subst]
  apply Presentation.subst_ext
  intro i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem erase_liftClosed {n : Nat} (t : CTm Head 0) :
    (liftClosed t : CTm Head n).erase = Presentation.liftClosed t.erase := by
  unfold liftClosed Presentation.liftClosed
  exact erase_rename _ t

/-! ## Application spines -/

/-- Apply a term to arguments, left to right. -/
def appSpine {n : Nat} (f : CTm Head n) (as : List (CTm Head n)) : CTm Head n :=
  as.foldl CTm.app f

@[simp] theorem erase_appSpine {n : Nat} (f : CTm Head n) (as : List (CTm Head n)) :
    (appSpine f as).erase = Normalization.appSpine f.erase (as.map erase) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
      simp only [appSpine, List.foldl_cons, List.map_cons, Normalization.appSpine_cons] at ih ⊢
      exact ih (.app f a)

theorem appSpine_concat {n : Nat} (f : CTm Head n) (as : List (CTm Head n)) (a : CTm Head n) :
    appSpine f (as ++ [a]) = .app (appSpine f as) a := by
  simp [appSpine, List.foldl_append]

/-! ## Universe heads -/

/-- Change the universe heads. -/
def mapHead {Head₂ : Type} (g : Head → Head₂) {n : Nat} : CTm Head n → CTm Head₂ n
  | .var i => .var i
  | .const c => .const c
  | .head h => .head (g h)
  | .pi A B => .pi (mapHead g A) (mapHead g B)
  | .sigma A B => .sigma (mapHead g A) (mapHead g B)
  | .id A a b => .id (mapHead g A) (mapHead g a) (mapHead g b)
  | .lam A b => .lam (mapHead g A) (mapHead g b)
  | .app f a => .app (mapHead g f) (mapHead g a)
  | .pair a b => .pair (mapHead g a) (mapHead g b)
  | .fst p => .fst (mapHead g p)
  | .snd p => .snd (mapHead g p)
  | .refl a => .refl (mapHead g a)

/-- Erasure commutes with changing the universe heads. -/
@[simp] theorem erase_mapHead {Head₂ : Type} (g : Head → Head₂) {n : Nat} (t : CTm Head n) :
    (mapHead g t).erase = t.erase.mapHead g := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [mapHead, erase, Tm.mapHead, ihA, ihB]
  | sigma A B ihA ihB => simp [mapHead, erase, Tm.mapHead, ihA, ihB]
  | id A a b ihA iha ihb => simp [mapHead, erase, Tm.mapHead, ihA, iha, ihb]
  | lam A b _ ihb => simp [mapHead, erase, Tm.mapHead, ihb]
  | app f a ihf iha => simp [mapHead, erase, Tm.mapHead, ihf, iha]
  | pair a b iha ihb => simp [mapHead, erase, Tm.mapHead, iha, ihb]
  | fst p ih => simp [mapHead, erase, Tm.mapHead, ih]
  | snd p ih => simp [mapHead, erase, Tm.mapHead, ih]
  | refl a ih => simp [mapHead, erase, Tm.mapHead, ih]

/-! ## Erasure is surjective and not injective -/

/-- Annotate every abstraction of a term with one closed domain. -/
def annotateWith (domain : CTm Head 0) {n : Nat} : Tm Head n → CTm Head n
  | .var i => .var i
  | .const c => .const c
  | .head h => .head h
  | .pi A B => .pi (annotateWith domain A) (annotateWith domain B)
  | .sigma A B => .sigma (annotateWith domain A) (annotateWith domain B)
  | .id A a b => .id (annotateWith domain A) (annotateWith domain a) (annotateWith domain b)
  | .lam b => .lam domain.liftClosed (annotateWith domain b)
  | .app f a => .app (annotateWith domain f) (annotateWith domain a)
  | .pair a b => .pair (annotateWith domain a) (annotateWith domain b)
  | .fst p => .fst (annotateWith domain p)
  | .snd p => .snd (annotateWith domain p)
  | .refl a => .refl (annotateWith domain a)

/-- Every term is an erasure. -/
@[simp] theorem erase_annotateWith (domain : CTm Head 0) {n : Nat} (t : Tm Head n) :
    (annotateWith domain t).erase = t := by
  induction t with
  | var => rfl
  | const => rfl
  | head => rfl
  | pi A B ihA ihB => simp [annotateWith, erase, ihA, ihB]
  | sigma A B ihA ihB => simp [annotateWith, erase, ihA, ihB]
  | id A a b ihA iha ihb => simp [annotateWith, erase, ihA, iha, ihb]
  | lam b ih => simp [annotateWith, erase, ih]
  | app f a ihf iha => simp [annotateWith, erase, ihf, iha]
  | pair a b iha ihb => simp [annotateWith, erase, iha, ihb]
  | fst p ih => simp [annotateWith, erase, ih]
  | snd p ih => simp [annotateWith, erase, ih]
  | refl a ih => simp [annotateWith, erase, ih]

/-- The identity at two different domains: two annotated terms with one
erasure. -/
theorem erase_not_injective {n : Nat} {A A' : CTm Head n} (different : A ≠ A') :
    lam A (.var 0) ≠ lam A' (.var 0) ∧ (lam A (.var 0)).erase = (lam A' (.var 0)).erase :=
  ⟨fun e => different (lam.inj e).1, rfl⟩

/-! ## Reading a term's shape off its erasure -/

section Inversion

variable {n : Nat} {t : CTm Head n}

theorem erase_eq_var {i : Fin n} (e : t.erase = .var i) : t = .var i := by
  cases t <;> simp_all [erase]

theorem erase_eq_const {c : DeclName} (e : t.erase = .const c) : t = .const c := by
  cases t <;> simp_all [erase]

theorem erase_eq_head {h : Head} (e : t.erase = .head h) : t = .head h := by
  cases t <;> simp_all [erase]

theorem erase_eq_pi {A : Tm Head n} {B : Tm Head (n + 1)} (e : t.erase = .pi A B) :
    ∃ A' B', t = .pi A' B' ∧ A'.erase = A ∧ B'.erase = B := by
  cases t <;> simp_all [erase]

theorem erase_eq_sigma {A : Tm Head n} {B : Tm Head (n + 1)} (e : t.erase = .sigma A B) :
    ∃ A' B', t = .sigma A' B' ∧ A'.erase = A ∧ B'.erase = B := by
  cases t <;> simp_all [erase]

theorem erase_eq_id {A a b : Tm Head n} (e : t.erase = .id A a b) :
    ∃ A' a' b', t = .id A' a' b' ∧ A'.erase = A ∧ a'.erase = a ∧ b'.erase = b := by
  cases t <;> simp_all [erase]

theorem erase_eq_lam {b : Tm Head (n + 1)} (e : t.erase = .lam b) :
    ∃ A b', t = .lam A b' ∧ b'.erase = b := by
  cases t <;> simp_all [erase]

theorem erase_eq_app {f a : Tm Head n} (e : t.erase = .app f a) :
    ∃ f' a', t = .app f' a' ∧ f'.erase = f ∧ a'.erase = a := by
  cases t <;> simp_all [erase]

theorem erase_eq_pair {a b : Tm Head n} (e : t.erase = .pair a b) :
    ∃ a' b', t = .pair a' b' ∧ a'.erase = a ∧ b'.erase = b := by
  cases t <;> simp_all [erase]

theorem erase_eq_fst {p : Tm Head n} (e : t.erase = .fst p) :
    ∃ p', t = .fst p' ∧ p'.erase = p := by
  cases t <;> simp_all [erase]

theorem erase_eq_snd {p : Tm Head n} (e : t.erase = .snd p) :
    ∃ p', t = .snd p' ∧ p'.erase = p := by
  cases t <;> simp_all [erase]

theorem erase_eq_refl {a : Tm Head n} (e : t.erase = .refl a) :
    ∃ a', t = .refl a' ∧ a'.erase = a := by
  cases t <;> simp_all [erase]

/-- A term whose erasure is a spine of a constant is a spine of that constant,
with arguments erasing to the spine's: the heads that root computations
inspect are read off erasures. -/
theorem erase_eq_constSpine {c : DeclName} (args : List (Tm Head n))
    (e : t.erase = Normalization.appSpine (.const c) args) :
    ∃ args', t = appSpine (.const c) args' ∧ args'.map erase = args := by
  induction args using List.reverseRecOn generalizing t with
  | nil =>
      obtain rfl := erase_eq_const e
      exact ⟨[], rfl, rfl⟩
  | append_singleton as a ih =>
      rw [Normalization.appSpine_concat] at e
      obtain ⟨f, a', rfl, ef, ea⟩ := erase_eq_app e
      obtain ⟨args', rfl, eargs⟩ := ih ef
      exact ⟨args' ++ [a'], (appSpine_concat _ _ _).symm, by simp [eargs, ea]⟩

end Inversion

end CTm

namespace CCtx

/-- Erase every entry of a context. -/
def erase : {n : Nat} → CCtx Head n → Ctx Head n
  | _, .nil => .nil
  | _, .snoc Γ A => .snoc (erase Γ) A.erase

@[simp] theorem erase_lookup {n : Nat} (Γ : CCtx Head n) (i : Fin n) :
    (Γ.lookup i).erase = Ctx.lookup Γ.erase i := by
  induction Γ with
  | nil => exact i.elim0
  | snoc Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · exact CTm.erase_rename wk A
      · intro j
        change ((Γ.lookup j).rename wk).erase = Presentation.rename wk (Ctx.lookup Γ.erase j)
        rw [CTm.erase_rename, ih]

end CCtx

end Annotated
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
