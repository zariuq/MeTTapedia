import Mettapedia.OSLF.Syntax.FreeBindingClone
import Mettapedia.OSLF.Syntax.ContextualLinearSubstitution

/-!
# A binding signature for the dependent Agda core

This is syntax, not an assertion that all its terms are well typed. Local
variables are positions in an explicit context; Pi, Sigma and Lam declare
their binders in the signature. Renaming, simultaneous substitution and their
laws are inherited from the generic free binding clone. Universe indices and
global names are parameters of nullary operators, not local variables.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Intrinsic

open Mettapedia.OSLF.Binding

inductive Srt where
  | term
  deriving DecidableEq

inductive Op : Srt → Type where
  | pi : Op .term
  | lam : Op .term
  | app : Op .term
  | ann : Op .term
  | sigma : Op .term
  | pair : Op .term
  | fst : Op .term
  | snd : Op .term
  | nat : Op .term
  | zero : Op .term
  | suc : Op .term
  | natSuc : Op .term
  | natrec : Op .term
  | unit : Op .term
  | star : Op .term
  | empty : Op .term
  | univ (level : Nat) : Op .term
  | global (name : Nat) : Op .term
  deriving DecidableEq

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} op => match op with
    | .pi | .sigma => [([], .term), ([.term], .term)]
    | .lam => [([.term], .term)]
    | .app | .ann | .pair => [([], .term), ([], .term)]
    | .fst | .snd | .suc => [([], .term)]
    | .natrec => List.replicate 5 ([], .term)
    | .nat | .zero | .natSuc | .unit | .star | .empty | .univ _ | .global _ => []

abbrev Tm (Γ : Ctx sig) := Term sig Γ .term

def pi {Γ : Ctx sig} (A : Tm Γ) (B : Tm (.term :: Γ)) : Tm Γ :=
  .op .pi (.cons A (.cons B .nil))
def lam {Γ : Ctx sig} (body : Tm (.term :: Γ)) : Tm Γ :=
  .op .lam (.cons body .nil)
def app {Γ : Ctx sig} (f a : Tm Γ) : Tm Γ := .op .app (.cons f (.cons a .nil))
def ann {Γ : Ctx sig} (t A : Tm Γ) : Tm Γ := .op .ann (.cons t (.cons A .nil))
def sigma {Γ : Ctx sig} (A : Tm Γ) (B : Tm (.term :: Γ)) : Tm Γ :=
  .op .sigma (.cons A (.cons B .nil))
def pair {Γ : Ctx sig} (a b : Tm Γ) : Tm Γ := .op .pair (.cons a (.cons b .nil))
def fst {Γ : Ctx sig} (p : Tm Γ) : Tm Γ := .op .fst (.cons p .nil)
def snd {Γ : Ctx sig} (p : Tm Γ) : Tm Γ := .op .snd (.cons p .nil)
def nat {Γ : Ctx sig} : Tm Γ := .op .nat .nil
def zero {Γ : Ctx sig} : Tm Γ := .op .zero .nil
def suc {Γ : Ctx sig} (n : Tm Γ) : Tm Γ := .op .suc (.cons n .nil)
def natSuc {Γ : Ctx sig} : Tm Γ := .op .natSuc .nil
def natrec {Γ : Ctx sig} (level motive base step index : Tm Γ) : Tm Γ :=
  .op .natrec (.cons level (.cons motive (.cons base (.cons step (.cons index .nil)))))
def unit {Γ : Ctx sig} : Tm Γ := .op .unit .nil
def star {Γ : Ctx sig} : Tm Γ := .op .star .nil
def empty {Γ : Ctx sig} : Tm Γ := .op .empty .nil
def univ {Γ : Ctx sig} (level : Nat) : Tm Γ := .op (.univ level) .nil
def global {Γ : Ctx sig} (name : Nat) : Tm Γ := .op (.global name) .nil

/-- The initial algebra is the existing generic construction, with this
signature's genuine binder arities. -/
def termsInitial : CategoryTheory.Limits.IsInitial (BindingCloneAlgebra.terms sig) :=
  FreeBindingClone.termsIsInitial sig

/-- Beta instantiation commutes with arbitrary ambient substitution. -/
theorem substitute_inst {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ)
    (body : Tm (.term :: Γ)) (arg : Tm Γ) :
    bind σ (inst body arg) =
      inst (bind (liftSub σ [.term]) body) (bind σ arg) :=
  ContextualLinearSubstitution.bind_inst σ body arg

/-- A free argument remains free when substituted beneath another lambda. -/
theorem beta_does_not_capture :
    inst (lam (.var (.succ .zero)) : Tm [.term, .term])
      (.var .zero : Tm [.term]) = lam (.var (.succ .zero)) := rfl

theorem beta_result_not_captured :
    inst (lam (.var (.succ .zero)) : Tm [.term, .term])
      (.var .zero : Tm [.term]) ≠ lam (.var .zero) := by
  intro h
  cases h

end Mettapedia.Languages.Agda.Intrinsic
