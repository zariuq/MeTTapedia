import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Object beta and eta as an admitted conversion theory

An object language with function sorts is presented by a binding signature:
`lam` binds one variable of the domain sort, `app` applies a term of a
function sort, and the base sort has constants and pairing. Object variables
of a function sort are ordinary variables of that sort, so application of
an object variable is syntax, not framework application.

Object beta and eta are therefore not built into the terms. They form an
admitted conversion theory: `Root` gives the two root equations in every
declaration frame, and `Conv` is the least congruence containing them. The
congruence includes metavariable occurrences, whose arguments may be
converted.

* `Conv` is stable under renaming (`conv_rename`) and substitutive
  (`conv_bind_pointwise`).
* `Conv` is preserved by contextual instantiation (`conv_instantiate`). Hence
  the admitted theory is a frame equivalence: instantiation is a morphism of
  the quotient frames.
* Contextual instantiation does not preserve object beta-normal forms. A
  metavariable at the function position of an application, instantiated by
  an abstraction, creates a redex (`instantiate_creates_redex_at_hole`). So
  does a function-sort parameter at the function position of an image,
  supplied with an abstraction (`instantiate_creates_redex_at_parameter`).
  In both cases the term and the images are beta-normal.
* `BetaStep` is one object beta step anywhere. `hasBeta` decides whether a
  term contains an object beta redex, and a term with none has no step
  (`betaNormal_of_hasBeta`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.HereditaryBetaEtaObject

open ContextualFamily (signature Assignment)

/-- Simple types over one base sort. -/
inductive Ty where
  | base
  | arrow (domain codomain : Ty)
  deriving DecidableEq

/-- Abstraction and application at every function sort, constants and
pairing at the base sort. -/
inductive Op : Ty → Type where
  | lam (domain codomain : Ty) : Op (.arrow domain codomain)
  | app (domain codomain : Ty) : Op codomain
  | symbol (number : Nat) : Op .base
  | pair : Op .base
  deriving DecidableEq

abbrev sig : Signature where
  Srt := Ty
  Op := Op
  arity := fun {_} operator => match operator with
    | .lam domain codomain => [([domain], codomain)]
    | .app domain codomain => [([], .arrow domain codomain), ([], domain)]
    | .symbol _ => []
    | .pair => [([], .base), ([], .base)]

section Terms

variable {V : Type} {declaration : V → MetaArity sig}

def lam {Γ : Ctx sig} {domain codomain : Ty}
    (body : Term (signature sig declaration) (domain :: Γ) codomain) :
    Term (signature sig declaration) Γ (.arrow domain codomain) :=
  .op (.inl (.lam domain codomain)) (.cons body .nil)

def app {Γ : Ctx sig} {domain codomain : Ty}
    (function : Term (signature sig declaration) Γ (.arrow domain codomain))
    (argument : Term (signature sig declaration) Γ domain) :
    Term (signature sig declaration) Γ codomain :=
  .op (.inl (.app domain codomain)) (.cons function (.cons argument .nil))

def symbol {Γ : Ctx sig} (number : Nat) : Term (signature sig declaration) Γ .base :=
  .op (.inl (.symbol number)) .nil

def pair {Γ : Ctx sig} (first second : Term (signature sig declaration) Γ .base) :
    Term (signature sig declaration) Γ .base :=
  .op (.inl .pair) (.cons first (.cons second .nil))

/-- The two admitted root equations. Eta has the intrinsic freshness
condition: the function is weakened past the bound variable. -/
inductive Root : {Γ : Ctx sig} → {sort : Ty} →
    Term (signature sig declaration) Γ sort → Term (signature sig declaration) Γ sort → Prop where
  | beta {Γ : Ctx sig} {domain codomain : Ty}
      (body : Term (signature sig declaration) (domain :: Γ) codomain)
      (argument : Term (signature sig declaration) Γ domain) :
      Root (app (lam body) argument) (inst body argument)
  | eta {Γ : Ctx sig} {domain codomain : Ty}
      (function : Term (signature sig declaration) Γ (.arrow domain codomain)) :
      Root (lam (app (weaken function) (.var .zero))) function

mutual

/-- The admitted conversion: the least congruence containing `Root`, in
every context and at every operator, metavariable occurrences included. -/
inductive Conv : {Γ : Ctx sig} → {sort : Ty} →
    Term (signature sig declaration) Γ sort → Term (signature sig declaration) Γ sort → Prop where
  | root {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort} :
      Root first second → Conv first second
  | refl {Γ : Ctx sig} {sort : Ty} (term : Term (signature sig declaration) Γ sort) : Conv term term
  | symm {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort} :
      Conv first second → Conv second first
  | trans {Γ : Ctx sig} {sort : Ty} {first middle last : Term (signature sig declaration) Γ sort} :
      Conv first middle → Conv middle last → Conv first last
  | congr {Γ : Ctx sig} {sort : Ty} (operator : (signature sig declaration).Op sort)
      {first second : Args (signature sig declaration) ((signature sig declaration).arity operator) Γ} :
      ConvArgs first second → Conv (.op operator first) (.op operator second)

inductive ConvArgs : {arities : List (List Ty × Ty)} → {Γ : Ctx sig} →
    Args (signature sig declaration) arities Γ → Args (signature sig declaration) arities Γ → Prop where
  | nil {Γ : Ctx sig} : ConvArgs (Args.nil (S := signature sig declaration) (Γ := Γ)) .nil
  | cons {binders : List Ty} {sort : Ty} {arities : List (List Ty × Ty)} {Γ : Ctx sig}
      {first second : Term (signature sig declaration) (binders ++ Γ) sort}
      {rest rest' : Args (signature sig declaration) arities Γ} :
      Conv first second → ConvArgs rest rest' → ConvArgs (.cons first rest) (.cons second rest')

end

/-! ## Renaming -/

theorem rename_app {Γ Δ : Ctx sig} {domain codomain : Ty} (rho : Ren (signature sig declaration) Γ Δ)
    (function : Term (signature sig declaration) Γ (.arrow domain codomain))
    (argument : Term (signature sig declaration) Γ domain) :
    rename rho (app function argument) = app (rename rho function) (rename rho argument) := rfl

theorem rename_lam {Γ Δ : Ctx sig} {domain codomain : Ty} (rho : Ren (signature sig declaration) Γ Δ)
    (body : Term (signature sig declaration) (domain :: Γ) codomain) :
    rename rho (lam body) = lam (rename (liftRen rho [domain]) body) := rfl

theorem rename_inst {Γ Δ : Ctx sig} {domain sort : Ty} (rho : Ren (signature sig declaration) Γ Δ)
    (body : Term (signature sig declaration) (domain :: Γ) sort)
    (argument : Term (signature sig declaration) Γ domain) :
    rename rho (inst body argument) = inst (rename (liftRen rho [domain]) body) (rename rho argument) := by
  unfold inst
  rw [rename_bind, bind_rename]
  congr 1
  funext s v
  cases v <;> rfl

theorem rename_weaken {Γ Δ : Ctx sig} {domain sort : Ty} (rho : Ren (signature sig declaration) Γ Δ)
    (term : Term (signature sig declaration) Γ sort) :
    rename (S := signature sig declaration) (Γ := domain :: Γ) (Δ := domain :: Δ) (liftRen rho [domain])
        (weaken term) = weaken (rename rho term) := by
  simp only [weaken, rename_comp]
  rfl

theorem root_rename {Γ Δ : Ctx sig} (rho : Ren (signature sig declaration) Γ Δ) :
    ∀ {sort : Ty} {first second : Term (signature sig declaration) Γ sort},
      Root first second → Root (rename rho first) (rename rho second)
  | _, _, _, .beta body argument => by
      rw [rename_app, rename_lam, rename_inst]
      exact .beta _ _
  | _, _, _, .eta function => by
      rw [rename_lam, rename_app, rename_weaken]
      exact .eta _

mutual

theorem conv_rename : ∀ {Γ Δ : Ctx sig} {sort : Ty} (rho : Ren (signature sig declaration) Γ Δ)
    {first second : Term (signature sig declaration) Γ sort},
    Conv first second → Conv (rename rho first) (rename rho second)
  | _, _, _, rho, _, _, .root root => .root (root_rename rho root)
  | _, _, _, _, _, _, .refl _ => .refl _
  | _, _, _, rho, _, _, .symm related => .symm (conv_rename rho related)
  | _, _, _, rho, _, _, .trans first second => .trans (conv_rename rho first) (conv_rename rho second)
  | _, _, _, rho, _, _, .congr operator related => .congr operator (convArgs_renameArgs rho related)

theorem convArgs_renameArgs : ∀ {arities : List (List Ty × Ty)} {Γ Δ : Ctx sig}
    (rho : Ren (signature sig declaration) Γ Δ)
    {first second : Args (signature sig declaration) arities Γ},
    ConvArgs first second → ConvArgs (renameArgs rho first) (renameArgs rho second)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, rho, _, _, .cons (binders := binders) head rest =>
      .cons (conv_rename (liftRen rho binders) head) (convArgs_renameArgs rho rest)

end

/-! ## Substitution of related terms -/

theorem conv_liftSub {Γ Δ : Ctx sig} {first second : Sub (signature sig declaration) Γ Δ}
    (related : ∀ s v, Conv (first s v) (second s v)) :
    ∀ (binders : List Ty) (s : Ty) (v : Var (binders ++ Γ) s),
      Conv (liftSub first binders s v) (liftSub second binders s v)
  | [], s, v => related s v
  | _ :: _, _, .zero => .refl _
  | _ :: binders, s, .succ v => conv_rename (fun _ w => .succ w) (conv_liftSub related binders s v)

mutual

/-- **The admitted conversion is substitutive.** -/
theorem conv_bind_pointwise : ∀ {Γ Δ : Ctx sig} {sort : Ty}
    {first second : Sub (signature sig declaration) Γ Δ},
    (∀ s v, Conv (first s v) (second s v)) →
    ∀ (term : Term (signature sig declaration) Γ sort), Conv (bind first term) (bind second term)
  | _, _, _, _, _, related, .var v => related _ v
  | _, _, _, _, _, related, .op operator arguments =>
      .congr operator (convArgs_bindArgs_pointwise related arguments)

theorem convArgs_bindArgs_pointwise : ∀ {arities : List (List Ty × Ty)} {Γ Δ : Ctx sig}
    {first second : Sub (signature sig declaration) Γ Δ},
    (∀ s v, Conv (first s v) (second s v)) →
    ∀ (arguments : Args (signature sig declaration) arities Γ),
      ConvArgs (bindArgs first arguments) (bindArgs second arguments)
  | _, _, _, _, _, _, .nil => .nil
  | _, _, _, _, _, related, .cons (bs := binders) head tail =>
      .cons (conv_bind_pointwise (conv_liftSub related binders) head)
        (convArgs_bindArgs_pointwise related tail)

end

theorem conv_argsToSub : ∀ (parameters : List Ty) {Γ : Ctx sig}
    {first second : Args (signature sig declaration) (parameters.map (fun b => ([], b))) Γ},
    ConvArgs first second → ∀ (s : Ty) (v : Var parameters s),
      Conv (argsToSub first s v) (argsToSub second s v)
  | [], _, _, _, _, _, v => nomatch v
  | _ :: parameters, _, _, _, related, s, v => by
      cases related with
      | cons head rest =>
          cases v with
          | zero => exact head
          | succ v => exact conv_argsToSub parameters rest s v

end Terms

/-! ## Instantiation preserves the admitted conversion -/

section Instantiation

variable {V W : Type} {declaration : V → MetaArity sig} {target : W → MetaArity sig}

theorem instantiate_app (assignment : Assignment declaration target) {Γ : Ctx sig} {domain codomain : Ty}
    (function : Term (signature sig declaration) Γ (.arrow domain codomain))
    (argument : Term (signature sig declaration) Γ domain) :
    ContextualFamily.instantiate assignment (app function argument) =
      app (ContextualFamily.instantiate assignment function) (ContextualFamily.instantiate assignment argument) :=
  rfl

theorem instantiate_lam (assignment : Assignment declaration target) {Γ : Ctx sig} {domain codomain : Ty}
    (body : Term (signature sig declaration) (domain :: Γ) codomain) :
    ContextualFamily.instantiate assignment (lam body) = lam (ContextualFamily.instantiate assignment body) :=
  rfl

theorem instantiate_inst (assignment : Assignment declaration target) {Γ : Ctx sig} {domain sort : Ty}
    (body : Term (signature sig declaration) (domain :: Γ) sort)
    (argument : Term (signature sig declaration) Γ domain) :
    ContextualFamily.instantiate assignment (inst body argument) =
      inst (ContextualFamily.instantiate assignment body) (ContextualFamily.instantiate assignment argument) := by
  unfold inst
  rw [ContextualFamily.instantiate_bind]
  congr 1
  funext s v
  cases v <;> rfl

theorem instantiate_weaken (assignment : Assignment declaration target) {Γ : Ctx sig} {domain sort : Ty}
    (term : Term (signature sig declaration) Γ sort) :
    ContextualFamily.instantiate assignment (weaken (t := domain) term) =
      weaken (ContextualFamily.instantiate assignment term) :=
  ContextualFamily.instantiate_rename assignment (fun _ v => .succ v) term

theorem root_instantiate (assignment : Assignment declaration target) :
    ∀ {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort},
      Root first second →
        Root (ContextualFamily.instantiate assignment first) (ContextualFamily.instantiate assignment second)
  | _, _, _, _, .beta body argument => by
      rw [instantiate_app, instantiate_lam, instantiate_inst]
      exact .beta _ _
  | _, _, _, _, .eta function => by
      rw [instantiate_lam, instantiate_app, instantiate_weaken]
      exact .eta _

mutual

/-- **Contextual instantiation preserves the admitted conversion.** -/
theorem conv_instantiate (assignment : Assignment declaration target) :
    ∀ {Γ : Ctx sig} {sort : Ty} {first second : Term (signature sig declaration) Γ sort},
      Conv first second →
        Conv (ContextualFamily.instantiate assignment first) (ContextualFamily.instantiate assignment second)
  | _, _, _, _, .root root => .root (root_instantiate assignment root)
  | _, _, _, _, .refl _ => .refl _
  | _, _, _, _, .symm related => .symm (conv_instantiate assignment related)
  | _, _, _, _, .trans first second =>
      .trans (conv_instantiate assignment first) (conv_instantiate assignment second)
  | _, _, _, _, .congr (.inl operator) related =>
      .congr (.inl operator) (convArgs_instantiateArgs assignment related)
  | _, _, _, _, .congr (.inr (.mk identity)) related =>
      conv_bind_pointwise (conv_argsToSub _ (convArgs_instantiateArgs assignment related))
        (assignment identity)

theorem convArgs_instantiateArgs (assignment : Assignment declaration target) :
    ∀ {arities : List (List Ty × Ty)} {Γ : Ctx sig}
      {first second : Args (signature sig declaration) arities Γ},
      ConvArgs first second →
        ConvArgs (ContextualFamily.instantiateArgs assignment first)
          (ContextualFamily.instantiateArgs assignment second)
  | _, _, _, _, .nil => .nil
  | _, _, _, _, .cons head rest =>
      .cons (conv_instantiate assignment head) (convArgs_instantiateArgs assignment rest)

end

end Instantiation

/-! ## Object beta-normal forms are not closed under instantiation -/

section Normality

variable {V : Type} {declaration : V → MetaArity sig}

mutual

/-- One object beta step, anywhere. -/
inductive BetaStep : {Γ : Ctx sig} → {sort : Ty} →
    Term (signature sig declaration) Γ sort → Term (signature sig declaration) Γ sort → Prop where
  | beta {Γ : Ctx sig} {domain codomain : Ty}
      (body : Term (signature sig declaration) (domain :: Γ) codomain)
      (argument : Term (signature sig declaration) Γ domain) :
      BetaStep (app (lam body) argument) (inst body argument)
  | inside {Γ : Ctx sig} {sort : Ty} (operator : (signature sig declaration).Op sort)
      {first second : Args (signature sig declaration) ((signature sig declaration).arity operator) Γ} :
      BetaStepArgs first second → BetaStep (.op operator first) (.op operator second)

inductive BetaStepArgs : {arities : List (List Ty × Ty)} → {Γ : Ctx sig} →
    Args (signature sig declaration) arities Γ → Args (signature sig declaration) arities Γ → Prop where
  | head {binders : List Ty} {sort : Ty} {arities : List (List Ty × Ty)} {Γ : Ctx sig}
      {first second : Term (signature sig declaration) (binders ++ Γ) sort}
      (tail : Args (signature sig declaration) arities Γ) :
      BetaStep first second → BetaStepArgs (.cons first tail) (.cons second tail)
  | tail {binders : List Ty} {sort : Ty} {arities : List (List Ty × Ty)} {Γ : Ctx sig}
      (head : Term (signature sig declaration) (binders ++ Γ) sort)
      {first second : Args (signature sig declaration) arities Γ} :
      BetaStepArgs first second → BetaStepArgs (.cons head first) (.cons head second)

end

/-- A term is beta-normal when it has no beta step. -/
def BetaNormal {Γ : Ctx sig} {sort : Ty} (term : Term (signature sig declaration) Γ sort) : Prop :=
  ∀ other, ¬ BetaStep term other

def isLam : {Γ : Ctx sig} → {sort : Ty} → Term (signature sig declaration) Γ sort → Bool
  | _, _, .op (.inl (.lam _ _)) _ => true
  | _, _, _ => false

def firstIsLam {Γ : Ctx sig} {binders : List Ty} {sort : Ty} {rest : List (List Ty × Ty)} :
    Args (signature sig declaration) ((binders, sort) :: rest) Γ → Bool
  | .cons function _ => isLam function

/-- Whether an operator node is itself a beta redex. -/
def headBeta {Γ : Ctx sig} : {sort : Ty} → (operator : (signature sig declaration).Op sort) →
    Args (signature sig declaration) ((signature sig declaration).arity operator) Γ → Bool
  | _, .inl (.app _ _), arguments => firstIsLam arguments
  | _, _, _ => false

mutual

/-- Whether a term contains a beta redex. -/
def hasBeta : {Γ : Ctx sig} → {sort : Ty} → Term (signature sig declaration) Γ sort → Bool
  | _, _, .var _ => false
  | _, _, .op operator arguments => headBeta operator arguments || hasBetaArgs arguments

def hasBetaArgs : {arities : List (List Ty × Ty)} → {Γ : Ctx sig} →
    Args (signature sig declaration) arities Γ → Bool
  | _, _, .nil => false
  | _, _, .cons head tail => hasBeta head || hasBetaArgs tail

end

mutual

theorem hasBeta_of_betaStep : ∀ {Γ : Ctx sig} {sort : Ty}
    {first second : Term (signature sig declaration) Γ sort}, BetaStep first second → hasBeta first = true
  | _, _, _, _, .beta _ _ => rfl
  | _, _, _, _, .inside operator inner => by
      show (headBeta operator _ || hasBetaArgs _) = true
      rw [hasBetaArgs_of_betaStepArgs inner, Bool.or_true]

theorem hasBetaArgs_of_betaStepArgs : ∀ {arities : List (List Ty × Ty)} {Γ : Ctx sig}
    {first second : Args (signature sig declaration) arities Γ},
    BetaStepArgs first second → hasBetaArgs first = true
  | _, _, _, _, .head _ inner => by
      show (hasBeta _ || hasBetaArgs _) = true
      rw [hasBeta_of_betaStep inner, Bool.true_or]
  | _, _, _, _, .tail _ inner => by
      show (hasBeta _ || hasBetaArgs _) = true
      rw [hasBetaArgs_of_betaStepArgs inner, Bool.or_true]

end

/-- A term without a beta redex is beta-normal. -/
theorem betaNormal_of_hasBeta {Γ : Ctx sig} {sort : Ty} {term : Term (signature sig declaration) Γ sort}
    (none : hasBeta term = false) : BetaNormal term := by
  intro other step
  rw [hasBeta_of_betaStep step] at none
  cases none

end Normality

/-! ## Two ways instantiation creates an object redex -/

namespace HiddenRedex

/-- A hole of function sort, and a hole with one function-sort parameter. -/
def holes : Bool → MetaArity sig
  | true => ([], .arrow .base .base)
  | false => ([.arrow .base .base], .base)

def closed (impossible : Empty) : MetaArity sig := nomatch impossible

/-- `F 1`: the hole sits at the function position of an application. -/
def holeApplied : Term (signature sig holes) [] .base :=
  app (.op (.inr (.mk true)) .nil) (symbol 1)

/-- `G[λx. x]`: the hole's argument is an abstraction. -/
def parameterApplied : Term (signature sig holes) [] .base :=
  .op (.inr (.mk false)) (.cons (lam (.var .zero)) .nil)

/-- `F := λx. x`, and `G[y] := y 1`. Both images are beta-normal. -/
def images : Assignment holes closed
  | true => lam (.var .zero)
  | false => app (.var .zero) (symbol 1)

def identityApplied : Term (signature sig closed) [] .base := app (lam (.var .zero)) (symbol 1)

theorem holeApplied_normal : BetaNormal holeApplied := betaNormal_of_hasBeta rfl
theorem parameterApplied_normal : BetaNormal parameterApplied := betaNormal_of_hasBeta rfl
theorem images_normal (identity : Bool) : BetaNormal (images identity) := by
  cases identity
  · exact betaNormal_of_hasBeta rfl
  · exact betaNormal_of_hasBeta rfl

theorem identityApplied_steps : BetaStep identityApplied (symbol 1) := .beta (.var .zero) (symbol 1)

/-- **A redex hidden behind a metavariable.** -/
theorem instantiate_creates_redex_at_hole :
    BetaNormal holeApplied ∧ (∀ identity, BetaNormal (images identity)) ∧
      ContextualFamily.instantiate images holeApplied = identityApplied ∧
      ¬ BetaNormal (ContextualFamily.instantiate images holeApplied) :=
  ⟨holeApplied_normal, images_normal, rfl, fun normal => normal _ identityApplied_steps⟩

/-- **A redex created through a function-sort parameter of an image.** -/
theorem instantiate_creates_redex_at_parameter :
    BetaNormal parameterApplied ∧ (∀ identity, BetaNormal (images identity)) ∧
      ContextualFamily.instantiate images parameterApplied = identityApplied ∧
      ¬ BetaNormal (ContextualFamily.instantiate images parameterApplied) :=
  ⟨parameterApplied_normal, images_normal, rfl, fun normal => normal _ identityApplied_steps⟩

/-- The created redex and its reduct are related by the admitted conversion,
and are different terms. -/
theorem created_redex_converts :
    Conv identityApplied (symbol 1) ∧ identityApplied ≠ symbol 1 :=
  ⟨.root (.beta (.var .zero) (symbol 1)), by
    intro same
    have heads := (Term.op.inj same).1
    cases heads⟩

end HiddenRedex

end Mettapedia.OSLF.Binding.HereditaryBetaEtaObject

open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms conv_rename
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms conv_bind_pointwise
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms conv_instantiate
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms betaNormal_of_hasBeta
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms HiddenRedex.instantiate_creates_redex_at_hole
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms HiddenRedex.instantiate_creates_redex_at_parameter
open Mettapedia.OSLF.Binding.HereditaryBetaEtaObject in
#print axioms HiddenRedex.created_redex_converts
