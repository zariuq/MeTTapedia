import Mettapedia.Languages.LambdaCalculus.NamePassing

/-!
# The two-sort constructor presentation of name-passing lambda terms

The five displayed constructors of Native Type Theory Example 30 have
independent binding arities. Ordinary variables of the term sort are retained,
in addition to the reference variables used by the executable expression
fragment. Definition binds its reference in the continuation only.

The embedding below identifies the existing reference-only fragment with
its actual constructor trees. Root edges are independently authored; their
targets use the shared simultaneous substitution beneath the reference binder.
This is constructor syntax and not yet its finite-limit and closed completion.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation

open Mettapedia.OSLF.Binding

inductive Srt where
  | nm
  | tm
  deriving DecidableEq, Repr

inductive Operator : Srt → Type where
  | reference : Operator .tm
  | abstraction : Operator .tm
  | application : Operator .tm
  | definition : Operator .tm
  | carrier : Operator .tm

abbrev signature : Signature where
  Srt := Srt
  Op := Operator
  arity := fun {_} op => match op with
    | .reference => [([], .nm)]
    | .abstraction => [([.nm], .tm)]
    | .application => [([], .tm), ([], .nm)]
    | .definition => [([], .tm), ([.nm], .tm)]
    | .carrier => [([], .nm), ([], .tm), ([], .tm)]

abbrev Name (Γ : Ctx signature) := Term signature Γ .nm
abbrev Program (Γ : Ctx signature) := Term signature Γ .tm

def reference {Γ : Ctx signature} (name : Name Γ) : Program Γ :=
  .op .reference (.cons name .nil)

def abstraction {Γ : Ctx signature} (body : Program (.nm :: Γ)) : Program Γ :=
  .op .abstraction (.cons body .nil)

def application {Γ : Ctx signature} (function : Program Γ) (argument : Name Γ) : Program Γ :=
  .op .application (.cons function (.cons argument .nil))

def definition {Γ : Ctx signature} (value : Program Γ)
    (body : Program (.nm :: Γ)) : Program Γ :=
  .op .definition (.cons value (.cons body .nil))

def carrier {Γ : Ctx signature} (name : Name Γ) (value body : Program Γ) : Program Γ :=
  .op .carrier (.cons name (.cons value (.cons body .nil)))

/-- A reference has no constructor other than a variable of its own sort. -/
def nameVariable {Γ : Ctx signature} : Name Γ → Var Γ .nm
  | .var name => name
  | .op impossible _ => nomatch impossible

@[simp] theorem name_as_variable {Γ : Ctx signature} (name : Name Γ) :
    Term.var (nameVariable name) = name := by
  cases name with
  | var => rfl
  | op impossible => nomatch impossible

/-- The old expression language is embedded without replacing term holes by
references. Its image simply has no occurrences of ordinary term variables. -/
def embed : {Γ : Ctx signature} → Expr Srt.nm Γ → Program Γ
  | _, .var name => reference (.var name)
  | _, .lam body => abstraction (embed body)
  | _, .app function argument => application (embed function) (.var argument)
  | _, .defn value body => definition (embed value) (embed body)
  | _, .carrier name value body => carrier (.var name) (embed value) (embed body)

theorem embed_rename {Γ Δ : Ctx signature} (environment : Ren signature Γ Δ)
    (term : Expr Srt.nm Γ) :
    embed (NamePassing.rename environment term) = Mettapedia.OSLF.Binding.rename environment (embed term) := by
  induction term generalizing Δ with
  | var => rfl
  | lam body ih => exact congrArg abstraction (ih (liftRen environment [.nm]))
  | app function argument ih => exact congrArg (fun f => application f (.var (environment _ argument))) (ih environment)
  | defn value body ihv ihb =>
      exact congrArg₂ definition (ihv environment) (ihb (liftRen environment [.nm]))
  | carrier name value body ihv ihb =>
      exact congrArg₂ (carrier (.var (environment _ name))) (ihv environment) (ihb environment)

/-- The two displayed root rewrites admit arbitrary supplied term variables. -/
inductive RootEdge : {Γ : Ctx signature} → Program Γ → Program Γ → Type where
  | beta {Γ} (body : Program (.nm :: Γ)) (argument : Name Γ) :
      RootEdge (application (abstraction body) argument) (inst body argument)
  | fetch {Γ} (name : Name Γ) (value : Program Γ) :
      RootEdge (carrier name value (reference name)) value

end Mettapedia.Languages.LambdaCalculus.NamePassing.Presentation
