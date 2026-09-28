import Mettapedia.OSLF.Syntax.FreeBindingClone
import Mettapedia.OSLF.Syntax.ContextualLinearSubstitution

/-!
# Structural syntax with Agda elimination spines

The binding signature separates terms, sort-annotated types, universe syntax,
eliminations, and ordered elimination spines. `lam` and `pi` bind; their
`NoAbs` counterparts do not. Substitution is the generic binding-clone action.

`eliminate` retains an application of a spine before beta computation. This
administrative form makes substitution total on raw syntax. Agda's internal
head-spine representation instead performs beta computation in `applyTermE`;
its correspondence is a separate adequacy obligation. In particular, this
signature is not an assertion that every raw term is an admitted Agda term.

Source: Agda v2.8.0.2, `Agda.Syntax.Internal`, definitions `Term`, `Abs`,
`Type''`, and `Elims`; `Agda.TypeChecking.Substitute.applyTermE`.
Argument modalities, metavariable solving, and cubical eliminations are not
part of the present relevant-argument fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural

open Mettapedia.OSLF.Binding

inductive Srt where
  | term | type | sort | level | elim | spine
  deriving DecidableEq

inductive Op : Srt → Type where
  | lam : Op .term
  | lamNoAbs : Op .term
  | pi : Op .term
  | piNoAbs : Op .term
  | eliminate : Op .term
  | defined (name : String) : Op .term
  | constructor (name : String) : Op .term
  | natLiteral (value : Nat) : Op .term
  | sortTerm : Op .term
  | levelTerm : Op .term
  | el : Op .type
  | set : Op .sort
  | prop : Op .sort
  | setOmega (index : Nat) : Op .sort
  | levelClosed (value : Nat) : Op .level
  | levelSuc : Op .level
  | levelMax : Op .level
  | levelNeutral : Op .level
  | apply : Op .elim
  | proj (name : String) : Op .elim
  | nil : Op .spine
  | cons : Op .spine
  | append : Op .spine
  deriving DecidableEq

def sig : Signature where
  Srt := Srt
  Op := Op
  arity := fun {_} op => match op with
    | .lam => [([.term], .term)]
    | .lamNoAbs => [([], .term)]
    | .pi => [([], .type), ([.term], .type)]
    | .piNoAbs => [([], .type), ([], .type)]
    | .eliminate => [([], .term), ([], .spine)]
    | .defined _ | .constructor _ | .natLiteral _ => []
    | .sortTerm => [([], .sort)]
    | .levelTerm => [([], .level)]
    | .el => [([], .sort), ([], .term)]
    | .set | .prop => [([], .level)]
    | .setOmega _ | .levelClosed _ => []
    | .levelSuc => [([], .level)]
    | .levelMax => [([], .level), ([], .level)]
    | .levelNeutral | .apply => [([], .term)]
    | .proj _ | .nil => []
    | .cons => [([], .elim), ([], .spine)]
    | .append => [([], .spine), ([], .spine)]

abbrev Tm (Γ : Ctx sig) := Term sig Γ .term
abbrev Ty (Γ : Ctx sig) := Term sig Γ .type
abbrev UnivSort (Γ : Ctx sig) := Term sig Γ .sort
abbrev Level (Γ : Ctx sig) := Term sig Γ .level
abbrev Elim (Γ : Ctx sig) := Term sig Γ .elim
abbrev Spine (Γ : Ctx sig) := Term sig Γ .spine

def lam {Γ : Ctx sig} (body : Tm (.term :: Γ)) : Tm Γ :=
  .op .lam (.cons body .nil)
def lamNoAbs {Γ : Ctx sig} (body : Tm Γ) : Tm Γ :=
  .op .lamNoAbs (.cons body .nil)
def pi {Γ : Ctx sig} (domain : Ty Γ) (codomain : Ty (.term :: Γ)) : Tm Γ :=
  .op .pi (.cons domain (.cons codomain .nil))
def piNoAbs {Γ : Ctx sig} (domain codomain : Ty Γ) : Tm Γ :=
  .op .piNoAbs (.cons domain (.cons codomain .nil))
def eliminate {Γ : Ctx sig} (head : Tm Γ) (spine : Spine Γ) : Tm Γ :=
  .op .eliminate (.cons head (.cons spine .nil))
def defined {Γ : Ctx sig} (name : String) : Tm Γ := .op (.defined name) .nil
def constructor {Γ : Ctx sig} (name : String) : Tm Γ := .op (.constructor name) .nil
def natLiteral {Γ : Ctx sig} (value : Nat) : Tm Γ := .op (.natLiteral value) .nil
def sortTerm {Γ : Ctx sig} (sort : UnivSort Γ) : Tm Γ := .op .sortTerm (.cons sort .nil)
def levelTerm {Γ : Ctx sig} (level : Level Γ) : Tm Γ := .op .levelTerm (.cons level .nil)
def el {Γ : Ctx sig} (sort : UnivSort Γ) (term : Tm Γ) : Ty Γ :=
  .op .el (.cons sort (.cons term .nil))
def set {Γ : Ctx sig} (level : Level Γ) : UnivSort Γ := .op .set (.cons level .nil)
def prop {Γ : Ctx sig} (level : Level Γ) : UnivSort Γ := .op .prop (.cons level .nil)
def setOmega {Γ : Ctx sig} (index : Nat) : UnivSort Γ := .op (.setOmega index) .nil
def levelClosed {Γ : Ctx sig} (value : Nat) : Level Γ := .op (.levelClosed value) .nil
def levelSuc {Γ : Ctx sig} (level : Level Γ) : Level Γ := .op .levelSuc (.cons level .nil)
def levelMax {Γ : Ctx sig} (left right : Level Γ) : Level Γ :=
  .op .levelMax (.cons left (.cons right .nil))
def levelNeutral {Γ : Ctx sig} (term : Tm Γ) : Level Γ :=
  .op .levelNeutral (.cons term .nil)
def apply {Γ : Ctx sig} (argument : Tm Γ) : Elim Γ := .op .apply (.cons argument .nil)
def proj {Γ : Ctx sig} (name : String) : Elim Γ := .op (.proj name) .nil
def nil {Γ : Ctx sig} : Spine Γ := .op .nil .nil
def cons {Γ : Ctx sig} (head : Elim Γ) (tail : Spine Γ) : Spine Γ :=
  .op .cons (.cons head (.cons tail .nil))
def append {Γ : Ctx sig} (left right : Spine Γ) : Spine Γ :=
  .op .append (.cons left (.cons right .nil))

/-- Actual source contexts contain term variables. Other signature sorts
remain available to rule metavariables without becoming Agda local binders. -/
def scope (length : Nat) : Ctx sig := List.replicate length .term

@[simp] theorem scope_zero : scope 0 = [] := rfl
@[simp] theorem scope_succ (length : Nat) : scope (length + 1) = .term :: scope length := rfl

@[simp] theorem bind_lam {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (body : Tm (.term :: Γ)) :
    bind σ (lam body) = lam (bind (liftSub σ [.term]) body) := rfl
@[simp] theorem bind_lamNoAbs {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (body : Tm Γ) :
    bind σ (lamNoAbs body) = lamNoAbs (bind σ body) := rfl
@[simp] theorem bind_eliminate {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ)
    (head : Tm Γ) (spine : Spine Γ) :
    bind σ (eliminate head spine) = eliminate (bind σ head) (bind σ spine) := rfl
@[simp] theorem bind_cons {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (head : Elim Γ) (tail : Spine Γ) :
    bind σ (cons head tail) = cons (bind σ head) (bind σ tail) := rfl
@[simp] theorem bind_apply {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (argument : Tm Γ) :
    bind σ (apply argument) = apply (bind σ argument) := rfl
@[simp] theorem bind_append {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ) (left right : Spine Γ) :
    bind σ (append left right) = append (bind σ left) (bind σ right) := rfl

/-- Capture-avoiding beta instantiation is inherited, including open spines
and sort annotations in the ambient substitution. -/
theorem substitute_inst {Γ Δ : Ctx sig} (σ : Sub sig Γ Δ)
    (body : Tm (.term :: Γ)) (argument : Tm Γ) :
    bind σ (inst body argument) =
      inst (bind (liftSub σ [.term]) body) (bind σ argument) :=
  ContextualLinearSubstitution.bind_inst σ body argument

theorem binder_capture_control :
    inst (lam (.var (.succ .zero)) : Tm [.term, .term])
      (.var .zero : Tm [.term]) = lam (.var (.succ .zero)) := rfl

theorem binder_capture_negative :
    inst (lam (.var (.succ .zero)) : Tm [.term, .term])
      (.var .zero : Tm [.term]) ≠ lam (.var .zero) := by
  intro impossible
  cases impossible

theorem noAbs_is_not_abs {Γ : Ctx sig} (body : Tm Γ) (bound : Tm (.term :: Γ)) :
    lamNoAbs body ≠ lam bound := by
  intro impossible
  cases impossible

end Mettapedia.Languages.Agda.Structural
