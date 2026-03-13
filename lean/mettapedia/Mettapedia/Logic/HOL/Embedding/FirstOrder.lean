import Foundation.FirstOrder.Basic
import Mettapedia.Logic.HOL.Semantics.Henkin

/-!
# First-Order Embedding into HOL

This module embeds Foundation first-order syntax into the real Church-style HOL
layer using one distinguished individual base type. The initial theorem surface
focuses on closed first-order syntax (`Semisentence` / `Sentence`) and semantic
truth preservation into the induced standard HOL model.
-/

namespace Mettapedia.Logic.HOL.Embedding.FirstOrder

open LO
open LO.FirstOrder

universe u w

/-- The single distinguished individual base type used for first-order embeddings. -/
inductive BaseTy
  | ind
deriving DecidableEq, Repr

abbrev indTy : Ty BaseTy := .base .ind

/-- HOL constants induced by a first-order language:
function symbols become curried individual-valued constants and relation
symbols become curried proposition-valued constants. -/
inductive Const (L : Language.{u}) : Ty BaseTy → Type u where
  | func {k : ℕ} : L.Func k → Const L (iterArrow k indTy indTy)
  | rel {k : ℕ} : L.Rel k → Const L (iterArrow k indTy propTy)

abbrev CtxOfArity (n : ℕ) : Ctx BaseTy := List.replicate n indTy

/-- The individual carrier used by the induced HOL model. -/
abbrev IndCarrier (M : Type w) : Type (max 1 w) := ULift.{1, w} M

/-- Constant base-type carrier function for the one-sorted first-order embedding. -/
abbrev BaseCarrier (M : Type w) : BaseTy → Type (max 1 w)
  | .ind => IndCarrier M

namespace Const

variable {L : Language.{u}} {M : Type w}

/-- Consume a curried HOL function on `k` individual arguments. -/
def applyCurried {τ : Ty BaseTy} :
    {k : ℕ} →
      Ty.denote (BaseCarrier M) (iterArrow k indTy τ) →
      (Fin k → IndCarrier M) →
      Ty.denote (BaseCarrier M) τ
  | 0, f, _ => f
  | k + 1, f, v =>
      applyCurried (τ := τ) (k := k) (f (v 0)) (fun i => v i.succ)

/-- Curry a `Fin k → IndCarrier M`-indexed operation into an iterated HOL arrow. -/
def curryVec {τ : Ty BaseTy} :
    {k : ℕ} →
      ((Fin k → IndCarrier M) → Ty.denote (BaseCarrier M) τ) →
      Ty.denote (BaseCarrier M) (iterArrow k indTy τ)
  | 0, f => f ![]
  | k + 1, f =>
      fun x => curryVec (τ := τ) (k := k) (fun v => f (x :> v))

@[simp] theorem applyCurried_curryVec {τ : Ty BaseTy} :
    ∀ {k : ℕ}
      (f : (Fin k → IndCarrier M) → Ty.denote (BaseCarrier M) τ)
      (v : Fin k → IndCarrier M),
      applyCurried (τ := τ) (k := k) (curryVec (τ := τ) (k := k) f) v = f v
  | 0, f, v => by
      have hv : v = ![] := by
        funext i
        exact Fin.elim0 i
      simp [applyCurried, curryVec, hv]
  | k + 1, f, v => by
      simpa [applyCurried, curryVec] using
        applyCurried_curryVec
          (τ := τ)
          (k := k)
          (f := fun w => f (v 0 :> w))
          (v := fun i => v i.succ)

end Const

namespace Term

variable {L : Language.{u}}

/-- Apply a curried HOL term to a `Fin k`-indexed argument family. -/
def mkApps {τ : Ty BaseTy} :
    {Γ : Ctx BaseTy} →
      {k : ℕ} →
      Term (Const L) Γ (iterArrow k indTy τ) →
      (Fin k → Term (Const L) Γ indTy) →
      Term (Const L) Γ τ
  | _, 0, t, _ => t
  | _, k + 1, t, v =>
      mkApps (τ := τ) (Γ := _) (k := k) (.app t (v 0)) (fun i => v i.succ)

end Term

section Translation

variable {L : Language.{u}}

/-- Translate a closed first-order semiterm into HOL. -/
def embedSemiterm : {n : ℕ} → ClosedSemiterm L n → Term (Const L) (CtxOfArity n) indTy
  | _, .bvar x => .var (Var.ofFinRepeat indTy _ x)
  | _, .fvar x => nomatch x
  | _, .func f v =>
      Term.mkApps (τ := indTy) (.const (.func f)) (fun i => embedSemiterm (v i))
termination_by n t => t.complexity
decreasing_by
  exact Semiterm.complexity_func_lt f v i

/-- Translate a closed first-order semiformula into HOL. -/
def embedSemiformula : {n : ℕ} → Semisentence L n → Formula (Const L) (CtxOfArity n)
  | _, .verum => .top
  | _, .falsum => .bot
  | _, .rel r v =>
      Term.mkApps (τ := propTy) (.const (.rel r)) (fun i => embedSemiterm (v i))
  | _, .nrel r v =>
      .not (Term.mkApps (τ := propTy) (.const (.rel r)) (fun i => embedSemiterm (v i)))
  | _, .and φ ψ => .and (embedSemiformula φ) (embedSemiformula ψ)
  | _, .or φ ψ => .or (embedSemiformula φ) (embedSemiformula ψ)
  | _, .all φ => .all (embedSemiformula φ)
  | _, .ex φ => .ex (embedSemiformula φ)

/-- Translate a first-order sentence into a closed HOL formula. -/
abbrev embedSentence (φ : LO.FirstOrder.Sentence L) : ClosedFormula (Const L) :=
  embedSemiformula φ

end Translation

/-- The standard HOL model induced by a first-order structure. -/
def standardModel {L : Language.{u}} {M : Type w} (s : Structure L M) : HenkinModel BaseTy (Const L) :=
  HenkinModel.standard
    (Carrier := BaseCarrier M)
    (constDen := fun {τ} c =>
      match c with
      | .func f =>
          Const.curryVec (τ := indTy) (k := _) (fun v => ULift.up (s.func f fun i => (v i).down))
      | .rel r =>
          Const.curryVec (τ := propTy) (k := _) (fun v => ULift.up (s.rel r fun i => (v i).down)))

/-- Valuation corresponding to a first-order bound-variable environment. -/
def envVal {L : Language.{u}} {M : Type w} (s : Structure L M) :
    {n : ℕ} → (Fin n → M) → HenkinModel.Valuation (standardModel s) (CtxOfArity n)
  | 0, _, _, v => nomatch v
  | _ + 1, e, _, .vz => ULift.up (e 0)
  | _ + 1, e, _, .vs v => envVal s (fun i => e i.succ) v

@[simp] theorem envVal_vz {L : Language.{u}} {M : Type w} (s : Structure L M) {n : ℕ}
    (e : Fin (n + 1) → M) :
    envVal s e Var.vz = ULift.up (e 0) := rfl

@[simp] theorem envVal_vs {L : Language.{u}} {M : Type w} (s : Structure L M)
    {n : ℕ} (e : Fin (n + 1) → M) {τ : Ty BaseTy}
    (v : Var (CtxOfArity n) τ) :
    envVal s e (Var.vs v) = envVal s (fun i => e i.succ) v := rfl

@[simp] theorem envVal_ofFinRepeat {L : Language.{u}} {M : Type w} (s : Structure L M) :
    ∀ {n : ℕ} (e : Fin n → M) (x : Fin n),
      envVal s e (Var.ofFinRepeat indTy n x) = ULift.up (e x)
  | 0, e, x => nomatch x
  | _ + 1, e, ⟨0, _⟩ => rfl
  | _ + 1, e, ⟨k + 1, hk⟩ => by
      simpa [Var.ofFinRepeat, envVal] using
        (envVal_ofFinRepeat s (e := fun i => e i.succ)
          (x := ⟨k, Nat.lt_of_succ_lt_succ hk⟩))

theorem envVal_extend {L : Language.{u}} {M : Type w} (s : Structure L M) {n : ℕ}
    (e : Fin n → M) (x : IndCarrier M) :
    (HenkinModel.extend (M := standardModel s) (σ := indTy) (envVal s e) x :
      HenkinModel.Valuation (standardModel s) (indTy :: CtxOfArity n)) =
    (envVal s (x.down :> e) : HenkinModel.Valuation (standardModel s) (indTy :: CtxOfArity n)) := by
  cases x with
  | up x =>
      funext τ
      funext v
      cases v with
      | vz => rfl
      | vs v => rfl

theorem denote_mkApps {L : Language.{u}} {M : Type w} (s : Structure L M)
    {Γ : Ctx BaseTy} {τ : Ty BaseTy}
    (ρ : HenkinModel.Valuation (standardModel s) Γ) :
    ∀ {k : ℕ}
      (t : Term (Const L) Γ (iterArrow k indTy τ))
      (v : Fin k → Term (Const L) Γ indTy),
      HenkinModel.denote (standardModel s) (Term.mkApps (τ := τ) t v) ρ =
        Const.applyCurried (τ := τ) (k := k)
          (HenkinModel.denote (standardModel s) t ρ)
          (fun i => HenkinModel.denote (standardModel s) (v i) ρ)
  | 0, t, v => rfl
  | k + 1, t, v => by
      simpa [Term.mkApps, Const.applyCurried] using
        (denote_mkApps s (ρ := ρ) (τ := τ) (t := .app t (v 0)) (v := fun i => v i.succ))

theorem denote_embedSemiterm {L : Language.{u}} {M : Type w} (s : Structure L M)
    {n : ℕ} (t : ClosedSemiterm L n) (e : Fin n → M) :
    HenkinModel.denote (standardModel s) (embedSemiterm t) (envVal s e) =
      ULift.up (Semiterm.valb s e t) := by
  induction t generalizing e with
  | bvar x =>
      simp [embedSemiterm]
  | fvar x =>
      nomatch x
  | @func k f v ih =>
      rw [embedSemiterm, denote_mkApps]
      change
        Const.applyCurried (τ := indTy)
          (Const.curryVec (τ := indTy) (k := k)
            (fun w => ULift.up (s.func f fun i => (w i).down)))
          (fun i =>
            HenkinModel.denote (standardModel s) (embedSemiterm (v i)) (envVal s e)) =
        ULift.up (s.func f fun i => Semiterm.val s e Empty.elim (v i))
      rw [Const.applyCurried_curryVec]
      have hv :
          (fun i =>
            (HenkinModel.denote (standardModel s) (embedSemiterm (v i)) (envVal s e)).down) =
          (fun i => Semiterm.val s e Empty.elim (v i)) := by
        funext i
        exact congrArg ULift.down (ih i e)
      rw [hv]

theorem denote_embedSemiformula_iffAux {L : Language.{u}} {M : Type w} (s : Structure L M) :
    ∀ {n : ℕ} (φ : Semisentence L n) (e : Fin n → M),
      (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s e)).down ↔
        Semiformula.EvalAux s Empty.elim e φ
  | _, .verum, e => by simp [embedSemiformula, Semiformula.EvalAux]
  | _, .falsum, e => by simp [embedSemiformula, Semiformula.EvalAux]
  | _, .rel r v, e => by
      change
        (HenkinModel.denote (standardModel s)
          (Term.mkApps (τ := propTy) (.const (.rel r)) (fun i => embedSemiterm (v i)))
          (envVal s e)).down ↔
        Semiformula.EvalAux s Empty.elim e (Semiformula.rel r v)
      rw [denote_mkApps]
      change
        (Const.applyCurried (τ := propTy)
          (Const.curryVec (τ := propTy) (k := _) (fun w => ULift.up (s.rel r fun i => (w i).down)))
          (fun i => HenkinModel.denote (standardModel s) (embedSemiterm (v i)) (envVal s e))).down ↔
        Semiformula.EvalAux s Empty.elim e (Semiformula.rel r v)
      simp [Const.applyCurried_curryVec, denote_embedSemiterm, Semiformula.EvalAux]
  | _, .nrel r v, e => by
      change
        (HenkinModel.denote (standardModel s)
          (.not (Term.mkApps (τ := propTy) (.const (.rel r)) (fun i => embedSemiterm (v i))))
          (envVal s e)).down ↔
        Semiformula.EvalAux s Empty.elim e (Semiformula.nrel r v)
      change ¬(HenkinModel.denote (standardModel s)
        (Term.mkApps (τ := propTy) (.const (.rel r)) (fun i => embedSemiterm (v i)))
        (envVal s e)).down ↔
        ¬Structure.rel r (fun i => Semiterm.val s e Empty.elim (v i))
      exact not_congr <| by
        rw [denote_mkApps]
        change
          (Const.applyCurried (τ := propTy)
            (Const.curryVec (τ := propTy) (k := _) (fun w => ULift.up (s.rel r fun i => (w i).down)))
            (fun i => HenkinModel.denote (standardModel s) (embedSemiterm (v i)) (envVal s e))).down ↔
          Structure.rel r (fun i => Semiterm.val s e Empty.elim (v i))
        simp [Const.applyCurried_curryVec, denote_embedSemiterm]
  | _, .and φ ψ, e => by
      simpa [embedSemiformula, Semiformula.EvalAux] using
        show
          (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s e)).down ∧
            (HenkinModel.denote (standardModel s) (embedSemiformula ψ) (envVal s e)).down ↔
              Semiformula.EvalAux s Empty.elim e (φ ⋏ ψ) by
          simp [denote_embedSemiformula_iffAux s (φ := φ) (e := e),
        denote_embedSemiformula_iffAux s (φ := ψ) (e := e), Semiformula.EvalAux]
  | _, .or φ ψ, e => by
      simpa [embedSemiformula, Semiformula.EvalAux] using
        show
          (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s e)).down ∨
            (HenkinModel.denote (standardModel s) (embedSemiformula ψ) (envVal s e)).down ↔
              Semiformula.EvalAux s Empty.elim e (φ ⋎ ψ) by
          simp [denote_embedSemiformula_iffAux s (φ := φ) (e := e),
        denote_embedSemiformula_iffAux s (φ := ψ) (e := e), Semiformula.EvalAux]
  | _, .all φ, e => by
      constructor
      · intro h x
        have hx :
            (HenkinModel.denote (standardModel s) (embedSemiformula φ)
              (HenkinModel.extend (M := standardModel s) (σ := indTy) (envVal s e) (ULift.up x))).down := by
          exact h (ULift.up x) trivial
        rw [envVal_extend] at hx
        exact (denote_embedSemiformula_iffAux s (φ := φ) (e := x :> e)).mp hx
      · intro h x hx
        have hx' :
            (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s (x.down :> e))).down :=
          (denote_embedSemiformula_iffAux s (φ := φ) (e := x.down :> e)).mpr (h x.down)
        rw [← envVal_extend (s := s) (e := e) (x := x)] at hx'
        exact hx'
  | _, .ex φ, e => by
      constructor
      · rintro ⟨x, -, hx⟩
        refine ⟨x.down, ?_⟩
        rw [envVal_extend] at hx
        exact (denote_embedSemiformula_iffAux s (φ := φ) (e := x.down :> e)).mp hx
      · rintro ⟨x, hx⟩
        refine ⟨ULift.up x, trivial, ?_⟩
        have hx' :
            (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s (x :> e))).down :=
          (denote_embedSemiformula_iffAux s (φ := φ) (e := x :> e)).mpr hx
        rw [← envVal_extend (s := s) (e := e) (x := ULift.up x)] at hx'
        exact hx'

theorem denote_embedSemiformula_iff {L : Language.{u}} {M : Type w} (s : Structure L M) :
    ∀ {n : ℕ} (φ : Semisentence L n) (e : Fin n → M),
      (HenkinModel.denote (standardModel s) (embedSemiformula φ) (envVal s e)).down ↔
        Semiformula.Evalb s e φ
  | _, φ, e => by
      simpa [Semiformula.Evalb, Semiformula.Eval] using
        (denote_embedSemiformula_iffAux s (φ := φ) (e := e))

/-- Truth preservation for first-order sentences in the induced standard HOL model. -/
theorem denote_embedSentence_iff {L : Language.{u}} {M : Type w} (s : Structure L M)
    (φ : LO.FirstOrder.Sentence L) :
    (HenkinModel.denote (standardModel s) (embedSentence φ) (fun v => nomatch v)).down ↔
      Semiformula.Evalb s ![] φ := by
  simpa [embedSentence, envVal] using
    (denote_embedSemiformula_iff s (φ := φ) (e := ![]))

end Mettapedia.Logic.HOL.Embedding.FirstOrder
