import Mettapedia.OSLF.Syntax.FreeBindingClone

/-!
# Semantic metavariables for binding equations

An authored metavariable of arity `(bs, s)` is interpreted by a value of sort
`s` in the dependency context `bs`. Its action on any argument vector is
semantic simultaneous substitution. This representation makes the action
natural in the ambient context and avoids postulating a separate operation at
each context.

The representability theorem below identifies every substitution-natural
metavariable operation with one such semantic body. This is the interface
needed to formulate the equation-model condition over all semantic values,
rather than only over syntactic instances.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.BindingEquationalModels

open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.BindingCloneFoldSubstitution

universe u

variable {S : Signature}

/-- An authored metavariable receives one semantic body in its declared
dependency context. -/
abbrev MetaValuation (A : BindingCloneAlgebra.Algebra.{u} S)
    (M : List (MetaArity S)) : Type u :=
  (k : Fin M.length) → A.substitution.Carrier (M.get k).1 (M.get k).2

/-- Read the non-binding arguments of a metavariable as the semantic
environment for its declared dependency context. -/
def argsEnvironment (A : BindingCloneAlgebra.Algebra.{u} S) :
    {bs : List S.Srt} → {Γ : Ctx S} →
      FamilyArgs S A.substitution.Carrier (bs.map (fun b => ([], b))) Γ →
      Environment S A.substitution.Carrier bs Γ
  | [], _, .nil => fun _ v => nomatch v
  | _ :: _, _, .cons head tail => fun _ v =>
      match v with
      | .zero => head
      | .succ old => argsEnvironment A tail _ old

/-- Converting the arguments to an environment commutes with semantic
substitution. The head case has an empty binder list by the meta-arity. -/
theorem argsEnvironment_substituteArgs
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S} (env : Environment S A.substitution.Carrier Γ Δ) :
    ∀ {bs : List S.Srt}
      (args : FamilyArgs S A.substitution.Carrier
        (bs.map (fun b => ([], b))) Γ)
      (sort : S.Srt) (x : Var bs sort),
      argsEnvironment A (A.substitution.substituteArgs env args) sort x =
        A.substitution.substitute env (argsEnvironment A args sort x)
  | [], .nil, _, x => nomatch x
  | _ :: _, .cons _head _tail, _, .zero => rfl
  | _ :: _, .cons _head tail, sort, .succ old =>
      argsEnvironment_substituteArgs A env tail sort old

/-- The action of one semantic metavariable body on its non-binding argument
vector is determined by simultaneous substitution. -/
def applyMeta (A : BindingCloneAlgebra.Algebra.{u} S)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort)
    {Γ : Ctx S}
    (args : FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ) :
    A.substitution.Carrier Γ sort :=
  A.substitution.substitute (argsEnvironment A args) body

/-- Semantic metavariable application is natural under substitution in the
ambient context. This uses the clone associativity law, not syntax. -/
theorem applyMeta_substitute (A : BindingCloneAlgebra.Algebra.{u} S)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort)
    {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (args : FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ) :
    A.substitution.substitute env (applyMeta A body args) =
      applyMeta A body (A.substitution.substituteArgs env args) := by
  unfold applyMeta
  rw [A.substitution.substitute_comp]
  congr 1
  funext s v
  exact (argsEnvironment_substituteArgs A env args s v).symm

/-- Form a metavariable argument vector from an environment on its declared
dependency context. -/
def argsOfEnvironment (A : BindingCloneAlgebra.Algebra.{u} S) :
    (bs : List S.Srt) → {Γ : Ctx S} →
      Environment S A.substitution.Carrier bs Γ →
      FamilyArgs S A.substitution.Carrier
        (bs.map (fun b => ([], b))) Γ
  | [], _, _ => .nil
  | b :: bs, _, env =>
      .cons (env b .zero)
        (argsOfEnvironment A bs (fun s v => env s (.succ v)))

theorem argsEnvironment_argsOfEnvironment
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ (bs : List S.Srt) {Γ : Ctx S}
      (env : Environment S A.substitution.Carrier bs Γ)
      (sort : S.Srt) (x : Var bs sort),
      argsEnvironment A (argsOfEnvironment A bs env) sort x = env sort x
  | _ :: _, _, _, _, .zero => rfl
  | _ :: bs, _, env, sort, .succ old =>
      argsEnvironment_argsOfEnvironment A bs
        (fun s v => env s (.succ v)) sort old

theorem argsOfEnvironment_argsEnvironment
    (A : BindingCloneAlgebra.Algebra.{u} S) :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier
        (bs.map (fun b => ([], b))) Γ),
      argsOfEnvironment A bs (argsEnvironment A args) = args
  | [], _, .nil => rfl
  | _ :: bs, _, .cons head tail => by
      change FamilyArgs.cons head
          (argsOfEnvironment A bs (argsEnvironment A tail)) =
        FamilyArgs.cons head tail
      exact congrArg (FamilyArgs.cons head)
        (argsOfEnvironment_argsEnvironment A tail)

/-- Argument vectors are a product of semantic values. Substitution on that
product acts componentwise, including when the vector was constructed from an
environment. -/
theorem substituteArgs_argsOfEnvironment
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ Δ : Ctx S}
    (later : Environment S A.substitution.Carrier Γ Δ) :
    ∀ (bs : List S.Srt)
      (before : Environment S A.substitution.Carrier bs Γ),
      A.substitution.substituteArgs later (argsOfEnvironment A bs before) =
        argsOfEnvironment A bs
          (fun s v => A.substitution.substitute later (before s v))
  | [], _ => rfl
  | _ :: bs, before => by
      simp only [argsOfEnvironment,
        BindingSubstitutionAlgebra.Algebra.substituteArgs,
        BindingSubstitutionAlgebra.Algebra.liftEnvironment]
      exact congrArg (FamilyArgs.cons _)
        (substituteArgs_argsOfEnvironment A later bs
          (fun s v => before s (.succ v)))

/-- Canonical metavariable arguments are the projections in their own
dependency context. -/
def projectionArgs (A : BindingCloneAlgebra.Algebra.{u} S)
    (bs : List S.Srt) :
    FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) bs :=
  argsOfEnvironment A bs (fun _ v => A.substitution.injectVar v)

theorem substituteArgs_projectionArgs
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {Γ : Ctx S} (bs : List S.Srt)
    (env : Environment S A.substitution.Carrier bs Γ) :
    A.substitution.substituteArgs env (projectionArgs A bs) =
      argsOfEnvironment A bs env := by
  rw [projectionArgs, substituteArgs_argsOfEnvironment]
  congr 1
  funext s v
  exact A.substitution.substitute_var env v

theorem applyMeta_projectionArgs
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort) :
    applyMeta A body (projectionArgs A bs) = body := by
  unfold applyMeta projectionArgs
  have env_eq :
      argsEnvironment A
        (argsOfEnvironment A bs
          (fun _ v => A.substitution.injectVar v)) =
        (fun s v => A.substitution.injectVar v :
          Environment S A.substitution.Carrier bs bs) := by
    funext s v
    exact argsEnvironment_argsOfEnvironment A bs
      (fun _ v => A.substitution.injectVar v) s v
  rw [env_eq]
  exact A.substitution.substitute_identity body

/-- A substitution-natural interpretation of a metavariable's arguments.
The theorem below proves this structure carries no more information than one
semantic body in the declared dependency context. -/
structure NaturalMetaOperation (A : BindingCloneAlgebra.Algebra.{u} S)
    (bs : List S.Srt) (sort : S.Srt) where
  apply : {Γ : Ctx S} →
    FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ →
    A.substitution.Carrier Γ sort
  natural : ∀ {Γ Δ : Ctx S}
    (env : Environment S A.substitution.Carrier Γ Δ)
    (args : FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ),
    A.substitution.substitute env (apply args) =
      apply (A.substitution.substituteArgs env args)

def NaturalMetaOperation.ofBody (A : BindingCloneAlgebra.Algebra.{u} S)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort) :
    NaturalMetaOperation A bs sort where
  apply := applyMeta A body
  natural := applyMeta_substitute A body

def NaturalMetaOperation.body {A : BindingCloneAlgebra.Algebra.{u} S}
    {bs : List S.Srt} {sort : S.Srt}
    (op : NaturalMetaOperation A bs sort) :
    A.substitution.Carrier bs sort :=
  op.apply (projectionArgs A bs)

/-- Every substitution-natural metavariable operation is represented by its
value on the canonical projection vector. -/
theorem NaturalMetaOperation.apply_eq_applyMeta
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {bs : List S.Srt} {sort : S.Srt}
    (op : NaturalMetaOperation A bs sort)
    {Γ : Ctx S}
    (args : FamilyArgs S A.substitution.Carrier
      (bs.map (fun b => ([], b))) Γ) :
    op.apply args = applyMeta A op.body args := by
  have h := op.natural (argsEnvironment A args) (projectionArgs A bs)
  rw [substituteArgs_projectionArgs,
    argsOfEnvironment_argsEnvironment A args] at h
  exact h.symm

/-- Representing a body and evaluating at the projections recovers exactly
that body. -/
theorem NaturalMetaOperation.body_ofBody
    (A : BindingCloneAlgebra.Algebra.{u} S)
    {bs : List S.Srt} {sort : S.Srt}
    (body : A.substitution.Carrier bs sort) :
    (NaturalMetaOperation.ofBody A body).body = body :=
  applyMeta_projectionArgs A body

@[ext] theorem NaturalMetaOperation.ext
    {A : BindingCloneAlgebra.Algebra.{u} S}
    {bs : List S.Srt} {sort : S.Srt}
    {first second : NaturalMetaOperation A bs sort}
    (agree : ∀ {Γ : Ctx S}
      (args : FamilyArgs S A.substitution.Carrier
        (bs.map (fun b => ([], b))) Γ),
      first.apply args = second.apply args) : first = second := by
  cases first with
  | mk firstApply firstNatural =>
    cases second with
    | mk secondApply secondNatural =>
      have h : @firstApply = @secondApply := by
        funext Γ args
        exact agree args
      cases h
      rfl

/-- Substitution-natural metavariable operations and values in the declared
dependency context are equivalent, not merely related by a one-way map. -/
def semanticMetaEquiv (A : BindingCloneAlgebra.Algebra.{u} S)
    (bs : List S.Srt) (sort : S.Srt) :
    A.substitution.Carrier bs sort ≃ NaturalMetaOperation A bs sort where
  toFun := NaturalMetaOperation.ofBody A
  invFun := NaturalMetaOperation.body
  left_inv := NaturalMetaOperation.body_ofBody A
  right_inv := by
    intro op
    apply NaturalMetaOperation.ext
    intro Γ args
    exact (op.apply_eq_applyMeta args).symm

/-- On the actual term algebra, semantic argument environments agree
pointwise with the existing syntactic `argsToSub` used by authored schema
instantiation. -/
theorem argsEnvironment_terms_syntaxToFamily :
    ∀ {bs : List S.Srt} {Γ : Ctx S}
      (args : Args S (bs.map (fun b => ([], b))) Γ)
      (sort : S.Srt) (x : Var bs sort),
      argsEnvironment (BindingCloneAlgebra.terms S)
        (FreeBindingTerms.syntaxToFamily args) sort x =
          argsToSub args sort x
  | [], _, .nil, _, x => nomatch x
  | _ :: _, _, .cons _head _tail, _, .zero => rfl
  | _ :: _, _, .cons _head tail, sort, .succ old =>
      argsEnvironment_terms_syntaxToFamily tail sort old

/-- Semantic metavariable application on terms is exactly the authored
schema's capture-avoiding instantiation at that occurrence. -/
theorem applyMeta_terms_eq_bind_argsToSub
    {bs : List S.Srt} {sort : S.Srt}
    (body : Term S bs sort)
    {Γ : Ctx S}
    (args : Args S (bs.map (fun b => ([], b))) Γ) :
    applyMeta (BindingCloneAlgebra.terms S) body
      (FreeBindingTerms.syntaxToFamily args) =
        bind (argsToSub args) body := by
  unfold applyMeta
  change bind
      (argsEnvironment (BindingCloneAlgebra.terms S)
        (FreeBindingTerms.syntaxToFamily args)) body =
      bind (argsToSub args) body
  congr 1
  funext s v
  exact argsEnvironment_terms_syntaxToFamily args s v

end Mettapedia.OSLF.Binding.BindingEquationalModels
