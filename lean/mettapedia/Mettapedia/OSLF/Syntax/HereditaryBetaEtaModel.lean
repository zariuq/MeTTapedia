import Mettapedia.OSLF.Syntax.HereditaryBetaEtaObject

/-!
# The standard model of the admitted object conversion

The base sort denotes binary trees with numbered leaves, and a function sort
denotes all functions between the denotations of its domain and codomain. A
metavariable denotes a function of its parameters. Terms of every declaration
frame are interpreted under a valuation of their variables and an
interpretation of their metavariables.

* Interpretation commutes with renaming and substitution (`den_rename`,
  `den_bind`).
* The admitted conversion is sound: convertible terms have equal
  denotations under every valuation and every interpretation of the
  metavariables (`den_conv`).
* Hence the conversion is not total: distinct constants are not convertible
  in any frame (`symbols_not_convertible`), and the identity on the base sort
  is not convertible to a constant function (`identity_not_constant`).

Soundness concerns one model. Whether every equation valid in the full set
model is derivable (completeness for this model class) is a separate
question and is not addressed here.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.HereditaryBetaEtaModel

open ContextualFamily (signature)
open HereditaryBetaEtaObject

/-- Values at the base sort. -/
inductive Tree where
  | leaf (number : Nat)
  | node (left right : Tree)
  deriving DecidableEq

/-- The standard denotation of the simple types. -/
def Den : Ty → Type
  | .base => Tree
  | .arrow domain codomain => Den domain → Den codomain

def defaultDen : (sort : Ty) → Den sort
  | .base => Tree.leaf 0
  | .arrow _ codomain => fun _ => defaultDen codomain

/-- Values of a list of variables. -/
abbrev Values (context : List Ty) : Type := (sort : Ty) → Var context sort → Den sort

def noValues : Values [] := fun _ position => nomatch position

def single {sort : Ty} (value : Den sort) : Values [sort] := fun _ position =>
  match position with
  | .zero => value
  | .succ position => nomatch position

def appendValues : {binders context : List Ty} → Values binders → Values context →
    Values (binders ++ context)
  | [], _, _, env => env
  | _ :: _, _, bound, env => fun _ position => match position with
      | .zero => bound _ .zero
      | .succ position => appendValues (fun s v => bound s (.succ v)) env _ position

/-- The denotation of an argument list: each argument as a function of the
values of the variables it binds. -/
def ArgsDen : List (List Ty × Ty) → Type
  | [] => Unit
  | (binders, sort) :: rest => (Values binders → Den sort) × ArgsDen rest

def toValues : {parameters : List Ty} → ArgsDen (parameters.map (fun b => ([], b))) → Values parameters
  | [], _ => noValues
  | _ :: _, (first, rest) => fun _ position => match position with
      | .zero => first noValues
      | .succ position => toValues rest _ position

/-- The object operators. -/
def objectNode : {sort : Ty} → (operator : sig.Op sort) → ArgsDen (sig.arity operator) → Den sort
  | _, .lam domain codomain, arguments =>
      let parts : (Values [domain] → Den codomain) × Unit := arguments
      fun value => parts.1 (single value)
  | _, .app domain codomain, arguments =>
      let parts : (Values [] → Den (.arrow domain codomain)) × ((Values [] → Den domain) × Unit) :=
        arguments
      parts.1 noValues (parts.2.1 noValues)
  | _, .symbol number, _ => Tree.leaf number
  | _, .pair, arguments =>
      let parts : (Values [] → Den .base) × ((Values [] → Den .base) × Unit) := arguments
      Tree.node (parts.1 noValues) (parts.2.1 noValues)

section Interpretation

variable {V : Type} {declaration : V → MetaArity sig}

/-- An interpretation of the metavariables: each denotes a function of its parameters. -/
abbrev MetaValues (declaration : V → MetaArity sig) : Type :=
  (identity : V) → Values (declaration identity).1 → Den (declaration identity).2

def node (interp : MetaValues declaration) : {sort : Ty} → (operator : (signature sig declaration).Op sort) →
    ArgsDen ((signature sig declaration).arity operator) → Den sort
  | _, .inl operator, arguments => objectNode operator arguments
  | _, .inr (.mk identity), arguments => interp identity (toValues arguments)

mutual

def den (interp : MetaValues declaration) : {Γ : Ctx sig} → {sort : Ty} →
    Term (signature sig declaration) Γ sort → Values Γ → Den sort
  | _, _, .var position, env => env _ position
  | _, _, .op operator arguments, env => node interp operator (denArgs interp arguments env)

def denArgs (interp : MetaValues declaration) : {arities : List (List Ty × Ty)} → {Γ : Ctx sig} →
    Args (signature sig declaration) arities Γ → Values Γ → ArgsDen arities
  | _, _, .nil, _ => ()
  | _, _, .cons head tail, env => (fun bound => den interp head (appendValues bound env), denArgs interp tail env)

end

theorem appendValues_liftRen {Γ Δ : List Ty} (rho : (s : Ty) → Var Γ s → Var Δ s) (env : Values Δ) :
    ∀ (binders : List Ty) (bound : Values binders) (s : Ty) (position : Var (binders ++ Γ) s),
      appendValues bound env s (liftRen rho binders s position) =
        appendValues bound (fun s v => env s (rho s v)) s position
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: binders, bound, s, .succ position =>
      appendValues_liftRen rho env binders (fun s v => bound s (.succ v)) s position

mutual

theorem den_rename (interp : MetaValues declaration) :
    ∀ {Γ Δ : Ctx sig} {sort : Ty} (rho : Ren (signature sig declaration) Γ Δ)
      (term : Term (signature sig declaration) Γ sort) (env : Values Δ),
      den interp (rename rho term) env = den interp term (fun s v => env s (rho s v))
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, rho, .op operator arguments, env => by
      simp only [rename, den, denArgs_renameArgs interp rho arguments env]

theorem denArgs_renameArgs (interp : MetaValues declaration) :
    ∀ {arities : List (List Ty × Ty)} {Γ Δ : Ctx sig} (rho : Ren (signature sig declaration) Γ Δ)
      (arguments : Args (signature sig declaration) arities Γ) (env : Values Δ),
      denArgs interp (renameArgs rho arguments) env = denArgs interp arguments (fun s v => env s (rho s v))
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, rho, .cons (bs := binders) head tail, env => by
      simp only [renameArgs, denArgs, denArgs_renameArgs interp rho tail env]
      congr 1
      funext bound
      rw [den_rename interp (liftRen rho binders) head (appendValues bound env)]
      congr 1
      funext s v
      exact appendValues_liftRen rho env binders bound s v

end

theorem den_liftSub (interp : MetaValues declaration) {Γ Δ : Ctx sig}
    (sigma : Sub (signature sig declaration) Γ Δ) (env : Values Δ) :
    ∀ (binders : List Ty) (bound : Values binders) (s : Ty) (position : Var (binders ++ Γ) s),
      den interp (liftSub sigma binders s position) (appendValues bound env) =
        appendValues bound (fun s v => den interp (sigma s v) env) s position
  | [], _, _, _ => rfl
  | _ :: _, _, _, .zero => rfl
  | _ :: binders, bound, s, .succ position => by
      show den interp (rename (fun _ v => Var.succ v) (liftSub sigma binders s position)) (appendValues bound env) =
        appendValues (fun s v => bound s (.succ v)) (fun s v => den interp (sigma s v) env) s position
      rw [den_rename]
      exact den_liftSub interp sigma env binders (fun s v => bound s (.succ v)) s position

mutual

theorem den_bind (interp : MetaValues declaration) :
    ∀ {Γ Δ : Ctx sig} {sort : Ty} (sigma : Sub (signature sig declaration) Γ Δ)
      (term : Term (signature sig declaration) Γ sort) (env : Values Δ),
      den interp (bind sigma term) env = den interp term (fun s v => den interp (sigma s v) env)
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, sigma, .op operator arguments, env => by
      simp only [bind, den, denArgs_bindArgs interp sigma arguments env]

theorem denArgs_bindArgs (interp : MetaValues declaration) :
    ∀ {arities : List (List Ty × Ty)} {Γ Δ : Ctx sig} (sigma : Sub (signature sig declaration) Γ Δ)
      (arguments : Args (signature sig declaration) arities Γ) (env : Values Δ),
      denArgs interp (bindArgs sigma arguments) env =
        denArgs interp arguments (fun s v => den interp (sigma s v) env)
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, sigma, .cons (bs := binders) head tail, env => by
      simp only [bindArgs, denArgs, denArgs_bindArgs interp sigma tail env]
      congr 1
      funext bound
      rw [den_bind interp (liftSub sigma binders) head (appendValues bound env)]
      congr 1
      funext s v
      exact den_liftSub interp sigma env binders bound s v

end

theorem den_beta (interp : MetaValues declaration) {Γ : Ctx sig} {domain codomain : Ty}
    (body : Term (signature sig declaration) (domain :: Γ) codomain)
    (argument : Term (signature sig declaration) Γ domain) (env : Values Γ) :
    den interp (app (lam body) argument) env = den interp (inst body argument) env := by
  show den interp body (appendValues (single (den interp argument (appendValues noValues env))) env) =
    den interp (bind (extend argument) body) env
  rw [den_bind]
  congr 1
  funext s v
  cases v <;> rfl

theorem den_eta (interp : MetaValues declaration) {Γ : Ctx sig} {domain codomain : Ty}
    (function : Term (signature sig declaration) Γ (.arrow domain codomain)) (env : Values Γ) :
    den interp (lam (app (weaken function) (.var .zero))) env = den interp function env := by
  funext value
  show den interp (weaken function) (appendValues noValues (appendValues (single value) env))
      (appendValues (single value) env domain .zero) = den interp function env value
  rw [weaken, den_rename]
  rfl

theorem den_root (interp : MetaValues declaration) {Γ : Ctx sig} {sort : Ty}
    {first second : Term (signature sig declaration) Γ sort} (root : Root first second) (env : Values Γ) :
    den interp first env = den interp second env := by
  cases root with
  | beta body argument => exact den_beta interp body argument env
  | eta function => exact den_eta interp function env

mutual

/-- **The admitted conversion is sound for the standard model.** -/
theorem den_conv (interp : MetaValues declaration) :
    ∀ {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort},
      Conv first second → ∀ env, den interp first env = den interp second env
  | _, _, _, _, .root root, env => den_root interp root env
  | _, _, _, _, .refl _, _ => rfl
  | _, _, _, _, .symm related, env => (den_conv interp related env).symm
  | _, _, _, _, .trans one two, env => (den_conv interp one env).trans (den_conv interp two env)
  | _, _, _, _, .congr operator related, env => by
      show node interp operator (denArgs interp _ env) = node interp operator (denArgs interp _ env)
      rw [denArgs_conv interp related env]

theorem denArgs_conv (interp : MetaValues declaration) :
    ∀ {arities : List (List Ty × Ty)} {Γ : Ctx sig}
      {first second : Args (signature sig declaration) arities Γ},
      ConvArgs first second → ∀ env, denArgs interp first env = denArgs interp second env
  | _, _, _, _, .nil, _ => rfl
  | _, _, _, _, .cons head rest, env => by
      show (fun bound => den interp _ (appendValues bound env), denArgs interp _ env) =
        (fun bound => den interp _ (appendValues bound env), denArgs interp _ env)
      rw [denArgs_conv interp rest env]
      congr 1
      funext bound
      exact den_conv interp head (appendValues bound env)

end

/-- The interpretation sending every metavariable to a constant. -/
def defaultMeta : MetaValues declaration := fun identity _ => defaultDen (declaration identity).2

def defaultValues (context : List Ty) : Values context := fun sort _ => defaultDen sort

/-- **Negative control: distinct constants are not convertible, in any frame.** -/
theorem symbols_not_convertible {Γ : Ctx sig} {first second : Nat} (different : first ≠ second) :
    ¬ Conv (symbol (declaration := declaration) (Γ := Γ) first) (symbol second) := by
  intro related
  have same : Tree.leaf first = Tree.leaf second := den_conv defaultMeta related (defaultValues Γ)
  exact different (Tree.leaf.inj same)

/-- **Negative control: the identity is not convertible to a constant function.** -/
theorem identity_not_constant {Γ : Ctx sig} (number : Nat) :
    ¬ Conv (lam (declaration := declaration) (Γ := Γ) (.var .zero)) (lam (symbol number)) := by
  intro related
  have same := congrFun (den_conv defaultMeta related (defaultValues Γ)) (Tree.leaf (number + 1))
  have leaves : Tree.leaf (number + 1) = Tree.leaf number := same
  have numbers := Tree.leaf.inj leaves
  omega

end Interpretation

end Mettapedia.OSLF.Binding.HereditaryBetaEtaModel

open Mettapedia.OSLF.Binding.HereditaryBetaEtaModel in
#print axioms den_bind
open Mettapedia.OSLF.Binding.HereditaryBetaEtaModel in
#print axioms den_conv
open Mettapedia.OSLF.Binding.HereditaryBetaEtaModel in
#print axioms symbols_not_convertible
open Mettapedia.OSLF.Binding.HereditaryBetaEtaModel in
#print axioms identity_not_constant
