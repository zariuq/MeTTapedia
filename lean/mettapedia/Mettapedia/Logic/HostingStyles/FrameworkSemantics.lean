import Mettapedia.Logic.HostingStyles.Framework
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Models and canonical forms of the framework

Two tools for reasoning about framework terms up to the declared conversion.

## Models

A model of a signature gives a set to each base type and an operation to each
constant.  A term then has a value in every environment (`Tm.eval`), and
convertible terms have the same value (`Conv.eval`).  A model is therefore a
conversion-invariant readout of terms.  It is how a statement about all terms
convertible to a given one is proved here without first proving that the
declared computation rule is confluent: two terms with different values in
some model are not convertible (`not_conv_of_eval_ne`).

A function type is interpreted by functions *together with a mark* recording
whether the value came from an abstraction.  Beta is sound for this
interpretation and eta is not, so a model can tell a function from its eta
expansion, as the declared conversion does.

## Canonical forms

`Nf` are the canonical forms: beta-normal and eta-long, in spine form.

* At a function type a canonical form is an abstraction.
* At a base type it is a constant applied to canonical arguments, one for
  each of its argument types, or a variable or a hole applied to a spine of
  canonical arguments down to a base type.

`Nf.toTm` reads a canonical form as a term, and that term has no step
(`Nf.toTm_normal`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Framework

variable {B : Type} {signature : Signature B} {Hole : Type} {holes : Hole → Ty B}

/-! ## Models -/

/-- The values of a type: at a function type, a function and a mark. -/
def Ty.denote (Base : B → Type) : Ty B → Type
  | .base atom => Base atom
  | .arrow domain codomain => (domain.denote Base → codomain.denote Base) × Bool

/-- The value of a constant, from its operation on argument values. -/
def curry (Base : B → Type) : (count : Nat) → (arguments : Fin count → Ty B) → (result : B) →
    (((index : Fin count) → (arguments index).denote Base) → Base result) →
      (curried count arguments result).denote Base
  | 0, _, _, operation => operation fun index => index.elim0
  | count + 1, arguments, result, operation =>
      (fun first => curry Base count (fun index => arguments index.succ) result fun rest =>
        operation (Fin.cons (α := fun index => (arguments index).denote Base) first rest), false)

/-- A model of a signature with holes. -/
structure Model (signature : Signature B) {Hole : Type} (holes : Hole → Ty B) where
  Base : B → Type
  const : (constant : signature.Const) →
    ((index : Fin (signature.arity constant)) → (signature.argument constant index).denote Base) →
      Base (signature.result constant)
  hole : (slot : Hole) → (holes slot).denote Base

/-- An environment gives a value to every variable. -/
abbrev Env (Base : B → Type) (context : List (Ty B)) : Type :=
  ∀ type : Ty B, Var context type → type.denote Base

/-- Extend an environment by the value of a new variable. -/
def Env.cons {Base : B → Type} {context : List (Ty B)} {bound : Ty B}
    (value : bound.denote Base) (environment : Env Base context) : Env Base (bound :: context)
  | _, .zero => value
  | _, .succ name => environment _ name

/-- The environment of the empty context. -/
def Env.empty {Base : B → Type} : Env Base [] := fun _ name => nomatch name

/-- The value of a term in a model and an environment. -/
def Tm.eval (model : Model signature holes) : {context : List (Ty B)} → {type : Ty B} →
    Tm signature holes context type → Env model.Base context → type.denote model.Base
  | _, _, .var name, environment => environment _ name
  | _, _, .con constant, _ => curry model.Base _ _ _ (model.const constant)
  | _, _, .hole slot, _ => model.hole slot
  | _, _, .lam body, environment =>
      (fun value => body.eval model (Env.cons value environment), true)
  | _, _, .app function argument, environment =>
      (function.eval model environment).1 (argument.eval model environment)

theorem Tm.eval_rename (model : Model signature holes) {source target : List (Ty B)} {type : Ty B}
    (term : Tm signature holes source type) (rho : Renaming source target)
    (environment : Env model.Base target) :
    (term.rename rho).eval model environment =
      term.eval model fun type name => environment type (rho type name) := by
  induction term generalizing target with
  | var name => rfl
  | con constant => rfl
  | hole slot => rfl
  | lam body ih =>
      simp only [Tm.rename, Tm.eval]
      congr 1
      funext value
      rw [ih]
      congr 1
      funext type name
      cases name <;> rfl
  | app function argument ihFunction ihArgument =>
      simp only [Tm.rename, Tm.eval, ihFunction, ihArgument]

theorem Tm.eval_subst (model : Model signature holes) {source target : List (Ty B)} {type : Ty B}
    (term : Tm signature holes source type) (substitution : Subst signature holes source target)
    (environment : Env model.Base target) :
    (term.subst substitution).eval model environment =
      term.eval model fun type name => (substitution type name).eval model environment := by
  induction term generalizing target with
  | var name => rfl
  | con constant => rfl
  | hole slot => rfl
  | lam body ih =>
      simp only [Tm.subst, Tm.eval]
      congr 1
      funext value
      rw [ih]
      congr 1
      funext type name
      cases name with
      | zero => rfl
      | succ name => exact Tm.eval_rename model _ _ _
  | app function argument ihFunction ihArgument =>
      simp only [Tm.subst, Tm.eval, ihFunction, ihArgument]

theorem Tm.eval_inst (model : Model signature holes) {context : List (Ty B)} {bound type : Ty B}
    (body : Tm signature holes (bound :: context) type)
    (argument : Tm signature holes context bound) (environment : Env model.Base context) :
    (body.inst argument).eval model environment =
      body.eval model (Env.cons (argument.eval model environment) environment) := by
  rw [Tm.inst, Tm.eval_subst]
  congr 1
  funext type name
  cases name <;> rfl

/-- **The declared computation rule is sound in every model.** -/
theorem Step.eval (model : Model signature holes) {context : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes context type} (step : Step first second)
    (environment : Env model.Base context) :
    first.eval model environment = second.eval model environment := by
  induction step with
  | beta body argument => exact (Tm.eval_inst model body argument environment).symm
  | lam _ ih =>
      simp only [Tm.eval]
      congr 1
      funext value
      exact ih _
  | appLeft _ ih => simp only [Tm.eval, ih]
  | appRight _ ih => simp only [Tm.eval, ih]

/-- **Convertible terms have the same value in every model.** -/
theorem Conv.eval (model : Model signature holes) {context : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes context type} (convertible : Conv first second)
    (environment : Env model.Base context) :
    first.eval model environment = second.eval model environment := by
  induction convertible with
  | rel _ _ step => exact step.eval model environment
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- Two terms with different values in some model are not convertible. -/
theorem not_conv_of_eval_ne (model : Model signature holes) {context : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes context type} (environment : Env model.Base context)
    (different : first.eval model environment ≠ second.eval model environment) :
    ¬ Conv first second :=
  fun convertible => different (convertible.eval model environment)

/-! ## Constants applied to all their arguments -/

/-- Apply a head of a constant's type to all its arguments. -/
def Tm.applyArgs {context : List (Ty B)} : (count : Nat) → (arguments : Fin count → Ty B) →
    (result : B) → Tm signature holes context (curried count arguments result) →
      ((index : Fin count) → Tm signature holes context (arguments index)) →
        Tm signature holes context (.base result)
  | 0, _, _, head, _ => head
  | count + 1, arguments, result, head, values =>
      Tm.applyArgs count (fun index => arguments index.succ) result (.app head (values 0))
        fun index => values index.succ

/-- A constant applied to all its arguments. -/
def Tm.conApp {context : List (Ty B)} (constant : signature.Const)
    (values : (index : Fin (signature.arity constant)) →
      Tm signature holes context (signature.argument constant index)) :
    Tm signature holes context (.base (signature.result constant)) :=
  Tm.applyArgs _ _ _ (.con constant) values

theorem Tm.fill_applyArgs {Hole' : Type} {holes' : Hole' → Ty B}
    (filling : (slot : Hole) → Tm signature holes' [] (holes slot)) {context : List (Ty B)} :
    ∀ (count : Nat) (arguments : Fin count → Ty B) (result : B)
      (head : Tm signature holes context (curried count arguments result))
      (values : (index : Fin count) → Tm signature holes context (arguments index)),
      (Tm.applyArgs count arguments result head values).fill filling =
        Tm.applyArgs count arguments result (head.fill filling)
          fun index => (values index).fill filling
  | 0, _, _, _, _ => rfl
  | count + 1, arguments, result, head, values =>
      Tm.fill_applyArgs filling count (fun index => arguments index.succ) result
        (.app head (values 0)) fun index => values index.succ

/-- Filling commutes with applying a constant to its arguments. -/
theorem Tm.fill_conApp {Hole' : Type} {holes' : Hole' → Ty B}
    (filling : (slot : Hole) → Tm signature holes' [] (holes slot)) {context : List (Ty B)}
    (constant : signature.Const)
    (values : (index : Fin (signature.arity constant)) →
      Tm signature holes context (signature.argument constant index)) :
    (Tm.conApp constant values).fill filling =
      Tm.conApp constant fun index => (values index).fill filling :=
  Tm.fill_applyArgs filling _ _ _ _ _

theorem Conv.applyArgs {context : List (Ty B)} :
    ∀ (count : Nat) (arguments : Fin count → Ty B) (result : B)
      {head head' : Tm signature holes context (curried count arguments result)}
      {values values' : (index : Fin count) → Tm signature holes context (arguments index)},
      Conv head head' → (∀ index, Conv (values index) (values' index)) →
        Conv (Tm.applyArgs count arguments result head values)
          (Tm.applyArgs count arguments result head' values')
  | 0, _, _, _, _, _, _, heads, _ => heads
  | count + 1, arguments, result, _, _, _, _, heads, each =>
      Conv.applyArgs count (fun index => arguments index.succ) result
        (Conv.app heads (each 0)) fun index => each index.succ

/-- A constant applied to convertible arguments gives convertible terms. -/
theorem Conv.conApp {context : List (Ty B)} (constant : signature.Const)
    {values values' : (index : Fin (signature.arity constant)) →
      Tm signature holes context (signature.argument constant index)}
    (each : ∀ index, Conv (values index) (values' index)) :
    Conv (Tm.conApp constant values) (Tm.conApp constant values') :=
  Conv.applyArgs _ _ _ (.refl _) each

theorem Tm.eval_applyArgs (model : Model signature holes) {context : List (Ty B)}
    (environment : Env model.Base context) :
    ∀ (count : Nat) (arguments : Fin count → Ty B) (result : B)
      (head : Tm signature holes context (curried count arguments result))
      (values : (index : Fin count) → Tm signature holes context (arguments index))
      (operation : ((index : Fin count) → (arguments index).denote model.Base) →
        model.Base result),
      head.eval model environment = curry model.Base count arguments result operation →
        (Tm.applyArgs count arguments result head values).eval model environment =
          operation fun index => (values index).eval model environment
  | 0, _, _, head, values, operation, headValue => by
      refine headValue.trans ?_
      change operation (fun index => index.elim0) = operation _
      congr 1
      funext index
      exact index.elim0
  | count + 1, arguments, result, head, values, operation, headValue => by
      have applied := Tm.eval_applyArgs model environment count
        (fun index => arguments index.succ) result (.app head (values 0))
        (fun index => values index.succ)
        (fun rest => operation (Fin.cons (α := fun index => (arguments index).denote model.Base)
          ((values 0).eval model environment) rest))
        (congrArg (fun pair : ((arguments 0).denote model.Base →
            (curried count (fun index => arguments index.succ) result).denote model.Base) × Bool =>
          pair.1 ((values 0).eval model environment)) headValue)
      refine applied.trans ?_
      congr 1
      funext index
      refine Fin.cases ?_ (fun index => ?_) index <;> rfl

/-- **A constant applied to all its arguments is evaluated by its
operation.** -/
theorem Tm.eval_conApp (model : Model signature holes) {context : List (Ty B)}
    (environment : Env model.Base context) (constant : signature.Const)
    (values : (index : Fin (signature.arity constant)) →
      Tm signature holes context (signature.argument constant index)) :
    (Tm.conApp constant values).eval model environment =
      model.const constant fun index => (values index).eval model environment :=
  Tm.eval_applyArgs model environment _ _ _ _ _ _ rfl

/-! ## Normal terms -/

/-- The kind of a term, read from its outermost constructor. -/
def Tm.isLam {context : List (Ty B)} {type : Ty B} : Tm signature holes context type → Bool
  | .lam _ => true
  | _ => false

/-- The outermost constructor is an application. -/
def Tm.isApp {context : List (Ty B)} {type : Ty B} : Tm signature holes context type → Bool
  | .app _ _ => true
  | _ => false

/-- A step starts at an abstraction or an application. -/
theorem Step.source {context : List (Ty B)} {type : Ty B}
    {first second : Tm signature holes context type} (step : Step first second) :
    first.isLam = true ∨ first.isApp = true := by
  cases step <;> simp [Tm.isLam, Tm.isApp]

mutual

/-- Terms without a beta redex. -/
inductive NormalTm : {context : List (Ty B)} → {type : Ty B} →
    Tm signature holes context type → Prop where
  | lam {context : List (Ty B)} {domain codomain : Ty B}
      {body : Tm signature holes (domain :: context) codomain} :
      NormalTm body → NormalTm (.lam body)
  | neutral {context : List (Ty B)} {type : Ty B} {term : Tm signature holes context type} :
      NeutralTm term → NormalTm term

/-- Terms without a beta redex whose head is a variable, a constant or a
hole. -/
inductive NeutralTm : {context : List (Ty B)} → {type : Ty B} →
    Tm signature holes context type → Prop where
  | var {context : List (Ty B)} {type : Ty B} (name : Var context type) :
      NeutralTm (.var name : Tm signature holes context type)
  | con {context : List (Ty B)} (constant : signature.Const) :
      NeutralTm (.con constant : Tm signature holes context _)
  | hole {context : List (Ty B)} (slot : Hole) :
      NeutralTm (.hole slot : Tm signature holes context _)
  | app {context : List (Ty B)} {domain codomain : Ty B}
      {function : Tm signature holes context (.arrow domain codomain)}
      {argument : Tm signature holes context domain} :
      NeutralTm function → NormalTm argument → NeutralTm (.app function argument)

end

theorem NeutralTm.not_lam {context : List (Ty B)} {type : Ty B}
    {term : Tm signature holes context type} (neutral : NeutralTm term) : term.isLam = false := by
  cases neutral <;> rfl

mutual

/-- A term without a beta redex has no step. -/
theorem NormalTm.normal : ∀ {context : List (Ty B)} {type : Ty B}
    {term : Tm signature holes context type}, NormalTm term → Normal term
  | _, _, _, .lam normal, _, step => by
      cases step with
      | lam inner => exact normal.normal _ inner
  | _, _, _, .neutral neutral, _, step => neutral.normal _ step

theorem NeutralTm.normal : ∀ {context : List (Ty B)} {type : Ty B}
    {term : Tm signature holes context type}, NeutralTm term → Normal term
  | _, _, _, .var _, _, step => by
      have source := step.source
      simp [Tm.isLam, Tm.isApp] at source
  | _, _, _, .con _, _, step => by
      have source := step.source
      simp [Tm.isLam, Tm.isApp] at source
  | _, _, _, .hole _, _, step => by
      have source := step.source
      simp [Tm.isLam, Tm.isApp] at source
  | _, _, _, .app neutral normal, _, step => by
      cases step with
      | beta body argument => simpa [Tm.isLam] using neutral.not_lam
      | appLeft inner => exact neutral.normal _ inner
      | appRight inner => exact normal.normal _ inner

end

theorem NeutralTm.applyArgs {context : List (Ty B)} :
    ∀ (count : Nat) (arguments : Fin count → Ty B) (result : B)
      (head : Tm signature holes context (curried count arguments result))
      (values : (index : Fin count) → Tm signature holes context (arguments index)),
      NeutralTm head → (∀ index, NormalTm (values index)) →
        NeutralTm (Tm.applyArgs count arguments result head values)
  | 0, _, _, _, _, neutral, _ => neutral
  | count + 1, _, _, _, _, neutral, normal =>
      NeutralTm.applyArgs count _ _ _ _ (.app neutral (normal 0)) fun index => normal index.succ

/-! ## Canonical forms -/

mutual

/-- **Canonical forms**: beta-normal and eta-long. -/
inductive Nf (signature : Signature B) {Hole : Type} (holes : Hole → Ty B) :
    List (Ty B) → Ty B → Type where
  | lam {context : List (Ty B)} {domain codomain : Ty B} :
      Nf signature holes (domain :: context) codomain →
        Nf signature holes context (.arrow domain codomain)
  | con {context : List (Ty B)} (constant : signature.Const)
      (arguments : (index : Fin (signature.arity constant)) →
        Nf signature holes context (signature.argument constant index)) :
      Nf signature holes context (.base (signature.result constant))
  | var {context : List (Ty B)} {type : Ty B} {atom : B} :
      Var context type → Sp signature holes context type atom →
        Nf signature holes context (.base atom)
  | hole {context : List (Ty B)} {atom : B} (slot : Hole) :
      Sp signature holes context (holes slot) atom → Nf signature holes context (.base atom)

/-- A spine of canonical arguments, from a head type down to a base type. -/
inductive Sp (signature : Signature B) {Hole : Type} (holes : Hole → Ty B) :
    List (Ty B) → Ty B → B → Type where
  | nil {context : List (Ty B)} {atom : B} : Sp signature holes context (.base atom) atom
  | cons {context : List (Ty B)} {domain codomain : Ty B} {atom : B} :
      Nf signature holes context domain → Sp signature holes context codomain atom →
        Sp signature holes context (.arrow domain codomain) atom

end

mutual

/-- A canonical form, as a term. -/
def Nf.toTm : {context : List (Ty B)} → {type : Ty B} → Nf signature holes context type →
    Tm signature holes context type
  | _, _, .lam body => .lam body.toTm
  | _, _, .con constant arguments => Tm.conApp constant fun index => (arguments index).toTm
  | _, _, .var name spine => spine.toTm (.var name)
  | _, _, .hole slot spine => spine.toTm (.hole slot)

/-- Apply a head to a spine of canonical arguments. -/
def Sp.toTm : {context : List (Ty B)} → {type : Ty B} → {atom : B} →
    Sp signature holes context type atom → Tm signature holes context type →
      Tm signature holes context (.base atom)
  | _, _, _, .nil, head => head
  | _, _, _, .cons argument rest, head => rest.toTm (.app head argument.toTm)

end

mutual

theorem Nf.toTm_normalTm : ∀ {context : List (Ty B)} {type : Ty B}
    (normal : Nf signature holes context type), NormalTm normal.toTm
  | _, _, .lam body => by
      rw [Nf.toTm]
      exact .lam body.toTm_normalTm
  | _, _, .con constant arguments => by
      rw [Nf.toTm]
      exact .neutral (NeutralTm.applyArgs _ _ _ _ _ (.con constant)
        fun index => (arguments index).toTm_normalTm)
  | _, _, .var name spine => by
      rw [Nf.toTm]
      exact .neutral (spine.toTm_neutralTm (.var name))
  | _, _, .hole slot spine => by
      rw [Nf.toTm]
      exact .neutral (spine.toTm_neutralTm (.hole slot))

theorem Sp.toTm_neutralTm : ∀ {context : List (Ty B)} {type : Ty B} {atom : B}
    (spine : Sp signature holes context type atom) {head : Tm signature holes context type},
    NeutralTm head → NeutralTm (spine.toTm head)
  | _, _, _, .nil, _, neutral => by
      rw [Sp.toTm]
      exact neutral
  | _, _, _, .cons argument rest, _, neutral => by
      rw [Sp.toTm]
      exact rest.toTm_neutralTm (.app neutral argument.toTm_normalTm)

end

/-- **A canonical form has no step.** -/
theorem Nf.toTm_normal {context : List (Ty B)} {type : Ty B}
    (normal : Nf signature holes context type) : Normal normal.toTm :=
  normal.toTm_normalTm.normal

#print axioms Conv.eval
#print axioms Tm.eval_conApp
#print axioms NormalTm.normal
#print axioms Nf.toTm_normal

end Mettapedia.Logic.HostingStyles.Framework
