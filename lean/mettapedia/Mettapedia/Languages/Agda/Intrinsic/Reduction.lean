import Mettapedia.Languages.Agda.Intrinsic.Syntax

/-!
# Operational rules of the structural dependent core

This reference relation is specified independently of the authored rule
polynomial. It is full compatible reduction, including under binders. It is
not the old checker's weak-head strategy. Typed eta belongs to conversion,
not to this untyped reduction relation. Global unfolding requires an admitted
signature and is not part of this signature-free fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic

open Mettapedia.OSLF.Binding

inductive Root : {Γ : Ctx sig} → Tm Γ → Tm Γ → Prop where
  | beta {Γ} (body : Tm (.term :: Γ)) (arg : Tm Γ) :
      Root (app (lam body) arg) (inst body arg)
  | first {Γ} (a b : Tm Γ) : Root (fst (pair a b)) a
  | second {Γ} (a b : Tm Γ) : Root (snd (pair a b)) b
  | annotation {Γ} (t A : Tm Γ) : Root (ann t A) t
  | successor {Γ} (n : Tm Γ) : Root (app natSuc n) (suc n)
  | recZero {Γ} (l P z s : Tm Γ) : Root (natrec l P z s zero) z
  | recSuc {Γ} (l P z s n : Tm Γ) :
      Root (natrec l P z s (suc n)) (app (app s n) (natrec l P z s n))

mutual
/-- One compatible computational step, with one selected argument position. -/
inductive Step : {Γ : Ctx sig} → Tm Γ → Tm Γ → Prop where
  | root {Γ} {a b : Tm Γ} : Root a b → Step a b
  | congr {Γ} (op : Op .term) {as bs : Args sig (sig.arity op) Γ} :
      ArgsStep as bs → Step (.op op as) (.op op bs)

/-- Exactly one argument changes. Its step is in the context extended by
that argument's own binder list. -/
inductive ArgsStep : {Γ : Ctx sig} → {arity : List (List Srt × Srt)} →
    Args sig arity Γ → Args sig arity Γ → Prop where
  | head {Γ bs rest} {a b : Tm (bs ++ Γ)} (tail : Args sig rest Γ) :
      Step a b → ArgsStep (.cons a tail) (.cons b tail)
  | tail {Γ bs rest} (a : Tm (bs ++ Γ)) {as bs' : Args sig rest Γ} :
      ArgsStep as bs' → ArgsStep (.cons a as) (.cons a bs')
end

theorem root_substitute {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ)
    {a b : Tm Γ} (h : Root a b) : Root (bind σ a) (bind σ b) := by
  cases h with
  | beta body arg =>
      change Root (app (lam (bind (liftSub σ [.term]) body)) (bind σ arg)) _
      rw [substitute_inst]
      exact .beta _ _
  | first a b => exact .first _ _
  | second a b => exact .second _ _
  | annotation t A => exact .annotation _ _
  | successor n => exact .successor _
  | recZero l P z s => exact .recZero _ _ _ _
  | recSuc l P z s n => exact .recSuc _ _ _ _ _

mutual
theorem step_substitute : ∀ {Γ : Ctx sig} {a b : Tm Γ}, Step a b →
    ∀ {Δ : Ctx sig} (σ : Sub sig Γ Δ), Step (bind σ a) (bind σ b)
  | _, _, _, .root h, _, σ => .root (root_substitute σ h)
  | _, _, _, .congr op h, _, σ => .congr op (argsStep_substitute h σ)

theorem argsStep_substitute : ∀ {Γ : Ctx sig} {arity}
    {as bs : Args sig arity Γ}, ArgsStep as bs →
    ∀ {Δ : Ctx sig} (σ : Sub sig Γ Δ), ArgsStep (bindArgs σ as) (bindArgs σ bs)
  | _, _, _, _, .head tail h, _, σ => .head _ (step_substitute h (liftSub σ _))
  | _, _, _, _, .tail a h, _, σ => .tail _ (argsStep_substitute h σ)
end

theorem variable_inert {Γ : Ctx sig} (v : Var Γ .term) (t : Tm Γ) :
    ¬ Step (.var v) t := by
  intro h
  cases h with
  | root h => cases h

theorem zero_inert {Γ : Ctx sig} (t : Tm Γ) : ¬ Step zero t := by
  intro h
  cases h with
  | root h => cases h
  | congr op h => cases h

theorem unit_eta_is_not_reduction : ¬ Step (star : Tm []) zero := by
  intro h
  cases h with
  | root h => cases h

end Mettapedia.Languages.Agda.Intrinsic
