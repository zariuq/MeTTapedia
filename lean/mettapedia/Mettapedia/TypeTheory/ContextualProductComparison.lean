import Mettapedia.GSLT.Core.ContextualLadder
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Simple functions and dependent products over contextual structure

This module compares function-type structure across the strict
simply-typed-to-dependent contextual inclusion.  It does not define either
simple or dependent type theory.  Instead it isolates the smallest
introduction/elimination/beta capability on each side and proves that simple
function structure transports to the constant-family CwF, with arrow
formation reflected at any chosen base context.

The set-families model supplies the strict positive control.  A second
control constructs a genuinely varying dependent product family in the full
families CwF and proves that it is not equivalent to any constant family.
The converse requires a real context-uniformity condition: the fact that all
type families are constant does not itself force a chosen product operation
to ignore the context.  Thus simple function structure is recovered exactly
on its image without exhausting dependent-product structure.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualProductComparison

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u v w w'

/-! ## Minimal beta capabilities -/

/-- Pair the identity substitution with an argument. -/
def selfExtend (C : Cwf.{u, v, w, w'})
    {context : C.Ctx} {type : C.Ty context}
    (argument : C.Tm context type) :
  C.Sub context (C.ext context type) :=
  C.pair (C.idS context) type
    ((C.tySub_id type).symm ▸ argument)

/-- Simple function types with introduction, elimination, and beta.  Eta,
function extensionality, and substitution stability are separate
capabilities. -/
structure SimpleFunctionBeta (S : Scwf.{u, v, w, w'}) where
  arrow : S.Ty -> S.Ty -> S.Ty
  lam : {context : S.Ctx} -> {domain codomain : S.Ty} ->
    S.Tm (S.ext context domain) codomain ->
      S.Tm context (arrow domain codomain)
  app : {context : S.Ctx} -> {domain codomain : S.Ty} ->
    S.Tm context (arrow domain codomain) ->
      S.Tm context domain -> S.Tm context codomain
  beta : ∀ {context : S.Ctx} {domain codomain : S.Ty}
    (body : S.Tm (S.ext context domain) codomain)
    (argument : S.Tm context domain),
    app (lam body) argument =
      S.tmSub body (S.pair (S.idS context) domain argument)

/-- Dependent products with introduction, elimination, and beta over an
arbitrary contextual core.  No extensionality or substitution law is
included. -/
structure DependentProductBeta (C : Cwf.{u, v, w, w'}) where
  pi : {context : C.Ctx} ->
    (domain : C.Ty context) -> C.Ty (C.ext context domain) -> C.Ty context
  lam : {context : C.Ctx} -> {domain : C.Ty context} ->
    {codomain : C.Ty (C.ext context domain)} ->
    C.Tm (C.ext context domain) codomain ->
      C.Tm context (pi domain codomain)
  app : {context : C.Ctx} -> {domain : C.Ty context} ->
    {codomain : C.Ty (C.ext context domain)} ->
    C.Tm context (pi domain codomain) ->
    (argument : C.Tm context domain) ->
      C.Tm context (C.tySub codomain (selfExtend C argument))
  beta : ∀ {context : C.Ctx} {domain : C.Ty context}
    {codomain : C.Ty (C.ext context domain)}
    (body : C.Tm (C.ext context domain) codomain)
    (argument : C.Tm context domain),
    app (lam body) argument = C.tmSub body (selfExtend C argument)

/-! ## Faithful comparison on the constant-family inclusion -/

/-- Every simple beta-function capability becomes a dependent-product
capability on the constant-family CwF. -/
def simpleToDependent
    {S : Scwf.{u, v, w, w'}}
    (functions : SimpleFunctionBeta S) :
    DependentProductBeta S.toCwf where
  pi := functions.arrow
  lam := functions.lam
  app := functions.app
  beta := functions.beta

/-- Once the contextual structure has one context at which its type former
can be observed, equality after transport reflects equality of the simple
arrow formation operation.  The explicit base context matters: a
terminal-free CwF may have no contexts, in which case no context-indexed
operation can observe `arrow`. -/
theorem simpleToDependent_reflects_arrow (S : Scwf.{u, v, w, w'})
    (base : S.Ctx) {first second : SimpleFunctionBeta S}
    (equalProducts : simpleToDependent first = simpleToDependent second) :
    first.arrow = second.arrow := by
  funext domain codomain
  exact congrArg
    (fun products : DependentProductBeta S.toCwf =>
      products.pi (context := base) domain codomain)
    equalProducts

/-! ## The set-families controls -/

/-- Ordinary function types supply the beta capability in the canonical
simply typed families model. -/
def simpleFamiliesFunctions :
    SimpleFunctionBeta (simpleFamilies.{w}) where
  arrow domain codomain := domain -> codomain
  lam body context argument := body (context, argument)
  app function argument context := function context (argument context)
  beta _ _ := rfl

/-- The transported dependent product on the constant-family model is the
ordinary function space, definitionally. -/
theorem constantFamily_pi_agrees (domain codomain : Type w) :
    (simpleToDependent simpleFamiliesFunctions).pi
        (context := PUnit) domain codomain =
      (domain -> codomain) :=
  rfl

/-- Full set-indexed dependent products over the families CwF. -/
def familiesProducts : DependentProductBeta (familiesCwf.{w}) where
  pi domain codomain := fun context =>
    (argument : domain context) -> codomain ⟨context, argument⟩
  lam body context argument := body ⟨context, argument⟩
  app function argument context := function context (argument context)
  beta _ _ := rfl

/-- Functions out of the unit type are equivalent to their codomain. -/
def unitFunctionEquiv (A : Type w) : (PUnit -> A) ≃ A where
  toFun function := function PUnit.unit
  invFun value := fun _ => value
  left_inv function := by
    funext argument
    cases argument
    rfl
  right_inv _ := rfl

/-- A genuinely varying dependent codomain remains genuinely varying after
forming its product over the constant unit family. -/
theorem varying_product_not_constant :
    ¬ ∃ Constant : Type,
      ∀ context : Bool,
        Nonempty
          (((familiesProducts.pi
            (context := Bool) (constantFamily PUnit)
            (fun point => varyingBoolFamily point.1)) context) ≃ Constant) := by
  rintro ⟨Constant, productConstant⟩
  apply varyingBoolFamily_not_constant
  refine ⟨Constant, ?_⟩
  intro context
  rcases productConstant context with ⟨productEquiv⟩
  change (PUnit -> varyingBoolFamily context) ≃ Constant at productEquiv
  exact ⟨(unitFunctionEquiv (varyingBoolFamily context)).symm.trans
    productEquiv⟩

/-- The complete comparison: equality after transport reflects simple arrow
formation, while the full dependent model has product families outside every
constant-family image. -/
theorem constant_fragment_reflective_but_proper :
    (∀ {first second : SimpleFunctionBeta (simpleFamilies.{0})},
      simpleToDependent first = simpleToDependent second ->
        first.arrow = second.arrow) ∧
      (¬ ∃ Constant : Type,
        ∀ context : Bool,
          Nonempty
            (((familiesProducts.pi
              (context := Bool) (constantFamily PUnit)
              (fun point => varyingBoolFamily point.1)) context) ≃
                Constant)) :=
  ⟨fun equalProducts =>
      simpleToDependent_reflects_arrow simpleFamilies PUnit equalProducts,
    varying_product_not_constant⟩

#print axioms simpleToDependent_reflects_arrow
#print axioms constantFamily_pi_agrees
#print axioms varying_product_not_constant
#print axioms constant_fragment_reflective_but_proper

end Mettapedia.TypeTheory.ContextualProductComparison
