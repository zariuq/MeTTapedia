import Mettapedia.Languages.Agda.Adequacy.StaticEmbedding

/-!
# Recursive observation of administrative structural syntax

The generic binding fold traverses every argument in its declared binder
context. This algebra observes empty elimination as the head, append as list
concatenation, and elimination as the source's unreduced ordered applications.
It also traverses bodies and annotated types. Syntax outside the finite-Set
fragment has no observation. Successful observation does not assert typing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.Observation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Structural (sig scope)

def Result (n : Nat) : Structural.Srt → Type
  | .term => StaticSpecification.Term n
  | .type => StaticSpecification.Ty n
  | .elim => StaticSpecification.Elim n
  | .spine => StaticSpecification.Spine n
  | .sort | .level => Nat

/-- A context-indexed fold can be read at any ordinary term-variable scope. -/
def Carrier (Γ : Ctx sig) (s : Structural.Srt) :=
  ∀ {n : Nat}, Γ = scope n → Option (Result n s)

def injectVariable {Γ : Ctx sig} {s : Structural.Srt} (v : Var Γ s) : Carrier Γ s := by
  intro n same
  cases same
  have sort := scope_sort v
  subst s
  exact some (.var (readVar v))

def operation {Γ : Ctx sig} {s : Structural.Srt} (op : Structural.Op s)
    (args : FamilyArgs sig Carrier (sig.arity op) Γ) : Carrier Γ s := by
  intro n same
  cases same
  cases op with
  | lam =>
      exact match args with
      | .cons body .nil => (body (n := n + 1) rfl).map (fun term => .lam (.bind term))
  | lamNoAbs =>
      exact match args with
      | .cons body .nil => (body rfl).map (fun term => .lam (.noBind term))
  | pi =>
      exact match args with
      | .cons domain (.cons body .nil) => do
          let domain ← domain rfl
          let body ← body (n := n + 1) rfl
          pure (.pi domain (.bind body))
  | piNoAbs =>
      exact match args with
      | .cons domain (.cons body .nil) => do
          let domain ← domain rfl
          let body ← body rfl
          pure (.pi domain (.noBind body))
  | eliminate =>
      exact match args with
      | .cons head (.cons spine .nil) => do
          let head ← head rfl
          let spine ← spine rfl
          pure (head.applySpine spine)
  | sortTerm =>
      exact match args with | .cons sort .nil => (sort rfl).map .sort
  | el =>
      exact match args with
      | .cons sort (.cons term .nil) => do
          let level ← sort rfl
          let term ← term rfl
          pure (.el level term)
  | set => exact match args with | .cons level .nil => level rfl
  | levelClosed value => exact some value
  | apply => exact match args with | .cons term .nil => (term rfl).map .apply
  | nil => exact some []
  | cons =>
      exact match args with
      | .cons head (.cons tail .nil) => do
          let head ← head rfl
          let tail ← tail rfl
          pure (head :: tail)
  | append =>
      exact match args with
      | .cons first (.cons second .nil) => do
          let first ← first rfl
          let second ← second rfl
          pure (List.append first second)
  | defined | constructor | natLiteral | levelTerm | prop | setOmega
    | levelSuc | levelMax | levelNeutral | proj => exact none

/-- The existing initial fold supplies recursion and all binder traversal. -/
def algebra : Algebra sig where
  Carrier := Carrier
  injectVar := injectVariable
  operation := operation

def observe {n : Nat} {s : Structural.Srt} (term : Term sig (scope n) s) : Option (Result n s) :=
  fold algebra term rfl

abbrev term {n : Nat} (t : Structural.Tm (scope n)) := observe t
abbrev type {n : Nat} (t : Structural.Ty (scope n)) := observe t
abbrev elim {n : Nat} (e : Structural.Elim (scope n)) := observe e
abbrev spine {n : Nat} (es : Structural.Spine (scope n)) := observe es

@[simp] theorem variable_eq {n : Nat} (v : Var (scope n) Structural.Srt.term) :
    term (.var v) = some (.var (readVar v)) := rfl

@[simp] theorem lam_eq {n : Nat} (body : Structural.Tm (scope (n + 1))) :
    term (Structural.lam body) = (term body).map (fun t => .lam (.bind t)) := rfl

@[simp] theorem lamNoAbs_eq {n : Nat} (body : Structural.Tm (scope n)) :
    term (Structural.lamNoAbs body) = (term body).map (fun t => .lam (.noBind t)) := rfl

@[simp] theorem pi_eq {n : Nat} (domain : Structural.Ty (scope n))
    (body : Structural.Ty (scope (n + 1))) :
    term (Structural.pi domain body) = (do
      let domain ← type domain
      let body ← type body
      pure (.pi domain (.bind body))) := rfl

@[simp] theorem piNoAbs_eq {n : Nat} (domain body : Structural.Ty (scope n)) :
    term (Structural.piNoAbs domain body) = (do
      let domain ← type domain
      let body ← type body
      pure (.pi domain (.noBind body))) := rfl

@[simp] theorem eliminate_eq {n : Nat} (head : Structural.Tm (scope n))
    (es : Structural.Spine (scope n)) :
    term (Structural.eliminate head es) = (do
      let head ← term head
      let es ← spine es
      pure (head.applySpine es)) := rfl

@[simp] theorem el_eq {n : Nat} (sort : Structural.UnivSort (scope n)) (head : Structural.Tm (scope n)) :
    type (Structural.el sort head) = (do
      let level ← observe sort
      let head ← term head
      pure (.el level head)) := rfl

@[simp] theorem apply_eq {n : Nat} (argument : Structural.Tm (scope n)) :
    elim (Structural.apply argument) = (term argument).map .apply := rfl

@[simp] theorem nil_eq {n : Nat} : spine (Structural.nil : Structural.Spine (scope n)) = some [] := rfl

@[simp] theorem cons_eq {n : Nat} (head : Structural.Elim (scope n)) (tail : Structural.Spine (scope n)) :
    spine (Structural.cons head tail) = (do
      let head ← elim head
      let tail ← spine tail
      pure (head :: tail)) := rfl

@[simp] theorem append_eq {n : Nat} (first second : Structural.Spine (scope n)) :
    spine (Structural.append first second) = (do
      let first ← spine first
      let second ← spine second
      pure (List.append first second)) := rfl

@[simp] theorem sortTerm_eq {n : Nat} (sort : Structural.UnivSort (scope n)) :
    term (Structural.sortTerm sort) = (observe sort).map .sort := rfl

@[simp] theorem set_eq {n : Nat} (level : Structural.Level (scope n)) :
    observe (Structural.set level) = observe level := rfl

@[simp] theorem levelClosed_eq {n : Nat} (value : Nat) :
    observe (Structural.levelClosed value : Structural.Level (scope n)) = some value := rfl

mutual
  @[simp] theorem term_embed {n : Nat} (t : StaticSpecification.Term n) :
      term (embedTerm t) = some t := by
    match t with
    | .var i => rw [embedTerm, variable_eq, read_embedVar]; rfl
    | .lam (.bind body) => rw [embedTerm, lam_eq, term_embed]; rfl
    | .lam (.noBind body) => rw [embedTerm, lamNoAbs_eq, term_embed]; rfl
    | .pi domain (.bind body) => rw [embedTerm, pi_eq, type_embed, type_embed]; rfl
    | .pi domain (.noBind body) => rw [embedTerm, piNoAbs_eq, type_embed, type_embed]; rfl
    | .sort _ => rfl
    | .elim head elimination =>
        rw [embedTerm, eliminate_eq, term_embed, cons_eq, elim_embed, nil_eq]
        rfl

  @[simp] theorem type_embed {n : Nat} (a : StaticSpecification.Ty n) :
      type (embedTy a) = some a := by
    match a with
    | .el level head => rw [embedTy, el_eq, set_eq, levelClosed_eq, term_embed]; rfl

  @[simp] theorem elim_embed {n : Nat} (e : StaticSpecification.Elim n) :
      elim (embedElim e) = some e := by
    match e with
    | .apply argument => rw [embedElim, apply_eq, term_embed]; rfl
end

@[simp] theorem spine_embed {n : Nat} (es : StaticSpecification.Spine n) :
    spine (embedSpine es) = some es := by
  induction es with
  | nil => rfl
  | cons e es ih => rw [embedSpine, cons_eq, elim_embed, ih]; rfl

/-- Administrative observation is many-to-one even before imposing typing. -/
@[simp] theorem eliminate_nil {n : Nat} (head : Structural.Tm (scope n)) :
    term (Structural.eliminate head Structural.nil) = term head := by
  rw [eliminate_eq, nil_eq]
  cases term head <;> rfl

theorem eliminate_append {n : Nat} (head : Structural.Tm (scope n))
    (first second : Structural.Spine (scope n)) :
    term (Structural.eliminate head (Structural.append first second)) =
      term (Structural.eliminate (Structural.eliminate head first) second) := by
  simp only [eliminate_eq, append_eq]
  cases term head <;> cases spine first <;> cases spine second <;> try rfl
  exact congrArg some (StaticSpecification.Term.applySpine_append _ _ _)

theorem apply_of_some {n : Nat} {argument : Structural.Tm (scope n)}
    {a : StaticSpecification.Term n} (supported : term argument = some a) :
    elim (Structural.apply argument) = some (.apply a) :=
  congrArg (Option.map StaticSpecification.Elim.apply) supported

theorem cons_of_some {n : Nat} {head : Structural.Elim (scope n)} {tail : Structural.Spine (scope n)}
    {e : StaticSpecification.Elim n} {es : StaticSpecification.Spine n}
    (first : elim head = some e) (rest : spine tail = some es) :
    spine (Structural.cons head tail) = some (e :: es) := by
  rw [cons_eq, first, rest]
  rfl

theorem append_of_some {n : Nat} {first second : Structural.Spine (scope n)}
    {es fs : StaticSpecification.Spine n}
    (left : spine first = some es) (right : spine second = some fs) :
    spine (Structural.append first second) = some (es ++ fs) := by
  rw [append_eq, left, right]
  rfl

theorem eliminate_of_some {n : Nat} {head : Structural.Tm (scope n)} {es : Structural.Spine (scope n)}
    {f : StaticSpecification.Term n} {sourceSpine : StaticSpecification.Spine n}
    (first : term head = some f) (rest : spine es = some sourceSpine) :
    term (Structural.eliminate head es) = some (f.applySpine sourceSpine) := by
  rw [eliminate_eq, first, rest]
  rfl

end Mettapedia.Languages.Agda.StaticAdequacy.Observation
