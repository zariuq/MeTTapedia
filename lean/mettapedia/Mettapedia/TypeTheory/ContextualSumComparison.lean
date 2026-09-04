import Mettapedia.TypeTheory.ContextualProductComparison

/-!
# Simple products and dependent sums over contextual structure

This module is the sum-type companion to the function/product comparison.
It isolates product beta rules on a simply typed contextual structure and
dependent-sum beta rules on a CwF.  Simple products transport to the
constant-family CwF, while the full set-families model supports genuinely
varying dependent sums.

The second projection law is heterogeneous because its result type depends
on the first projection.  No eta, surjective pairing, proof irrelevance, or
identity reflection is included.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumComparison

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualProductComparison
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u v w w'

/-! ## Minimal beta capabilities -/

/-- Binary products with projections and beta in a simply typed contextual
structure. -/
structure SimpleProductBeta (S : Scwf.{u, v, w, w'}) where
  product : S.Ty -> S.Ty -> S.Ty
  pair : {context : S.Ctx} -> {first second : S.Ty} ->
    S.Tm context first -> S.Tm context second ->
      S.Tm context (product first second)
  fst : {context : S.Ctx} -> {first second : S.Ty} ->
    S.Tm context (product first second) -> S.Tm context first
  snd : {context : S.Ctx} -> {first second : S.Ty} ->
    S.Tm context (product first second) -> S.Tm context second
  fst_pair : ∀ {context : S.Ctx} {first second : S.Ty}
    (left : S.Tm context first) (right : S.Tm context second),
    fst (pair left right) = left
  snd_pair : ∀ {context : S.Ctx} {first second : S.Ty}
    (left : S.Tm context first) (right : S.Tm context second),
    snd (pair left right) = right

/-- Dependent sums with projections and beta.  The dependent second
projection and its beta law retain their fibre dependency explicitly. -/
structure DependentSumBeta (C : Cwf.{u, v, w, w'}) where
  sigma : {context : C.Ctx} ->
    (domain : C.Ty context) -> C.Ty (C.ext context domain) -> C.Ty context
  pair : {context : C.Ctx} -> {domain : C.Ty context} ->
    {codomain : C.Ty (C.ext context domain)} ->
    (first : C.Tm context domain) ->
    C.Tm context (C.tySub codomain (selfExtend C first)) ->
      C.Tm context (sigma domain codomain)
  fst : {context : C.Ctx} -> {domain : C.Ty context} ->
    {codomain : C.Ty (C.ext context domain)} ->
    C.Tm context (sigma domain codomain) -> C.Tm context domain
  snd : {context : C.Ctx} -> {domain : C.Ty context} ->
    {codomain : C.Ty (C.ext context domain)} ->
    (value : C.Tm context (sigma domain codomain)) ->
      C.Tm context (C.tySub codomain (selfExtend C (fst value)))
  fst_pair : ∀ {context : C.Ctx} {domain : C.Ty context}
    {codomain : C.Ty (C.ext context domain)}
    (first : C.Tm context domain)
    (second : C.Tm context
      (C.tySub codomain (selfExtend C first))),
    fst (pair first second) = first
  snd_pair : ∀ {context : C.Ctx} {domain : C.Ty context}
    {codomain : C.Ty (C.ext context domain)}
    (first : C.Tm context domain)
    (second : C.Tm context
      (C.tySub codomain (selfExtend C first))),
    HEq (snd (pair first second)) second

/-! ## Constant-family transport -/

/-- A simple product becomes a dependent sum on the constant-family CwF. -/
def simpleToDependent
    {S : Scwf.{u, v, w, w'}} (products : SimpleProductBeta S) :
    DependentSumBeta S.toCwf where
  sigma := products.product
  pair := products.pair
  fst := products.fst
  snd := products.snd
  fst_pair := products.fst_pair
  snd_pair := by
    intro context domain codomain first second
    exact heq_of_eq (products.snd_pair first second)

/-- At every chosen context, equality after transport reflects equality of
the simple product formation operation. -/
theorem simpleToDependent_reflects_product
    (S : Scwf.{u, v, w, w'}) (base : S.Ctx)
    {first second : SimpleProductBeta S}
    (equalSums : simpleToDependent first = simpleToDependent second) :
    first.product = second.product := by
  funext left right
  exact congrArg
    (fun sums : DependentSumBeta S.toCwf =>
      sums.sigma (context := base) left right)
    equalSums

/-! ## Set-families controls -/

/-- Cartesian products in the canonical simply typed families model. -/
def simpleFamiliesProducts :
    SimpleProductBeta (simpleFamilies.{w}) where
  product first second := first × second
  pair left right context := (left context, right context)
  fst value context := (value context).1
  snd value context := (value context).2
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl

/-- The transported constant-family sum is the ordinary cartesian product. -/
theorem constantFamily_sigma_agrees (first second : Type w) :
    (simpleToDependent simpleFamiliesProducts).sigma
        (context := PUnit) first second = (first × second) :=
  rfl

/-- Full dependent sums in the set-families CwF. -/
def familiesSums : DependentSumBeta (familiesCwf.{w}) where
  sigma domain codomain := fun context =>
    Σ value : domain context, codomain ⟨context, value⟩
  pair first second context := ⟨first context, second context⟩
  fst value context := (value context).1
  snd value context := (value context).2
  fst_pair _ _ := rfl
  snd_pair _ _ := HEq.rfl

/-- A dependent sum over a constant unit domain is equivalent to its fibre. -/
def unitSigmaEquiv (A : Type w) : (Σ _ : PUnit, A) ≃ A where
  toFun value := value.2
  invFun value := ⟨PUnit.unit, value⟩
  left_inv value := by
    rcases value with ⟨onlyUnit, value⟩
    cases onlyUnit
    rfl
  right_inv _ := rfl

/-- A genuinely varying codomain remains varying after dependent summation
over the constant unit family. -/
theorem varying_sum_not_constant :
    ¬ ∃ Constant : Type,
      ∀ context : Bool,
        Nonempty
          (((familiesSums.sigma
            (context := Bool) (constantFamily PUnit)
            (fun point => varyingBoolFamily point.1)) context) ≃ Constant) := by
  rintro ⟨Constant, sumConstant⟩
  apply varyingBoolFamily_not_constant
  refine ⟨Constant, ?_⟩
  intro context
  rcases sumConstant context with ⟨sumEquiv⟩
  change (Sigma fun _ : PUnit => varyingBoolFamily context) ≃ Constant
    at sumEquiv
  exact ⟨(unitSigmaEquiv (varyingBoolFamily context)).symm.trans sumEquiv⟩

/-- Constant-family product formation is reflected at an inhabited context,
yet full dependent summation strictly exceeds the constant-family fragment. -/
theorem constant_fragment_reflective_but_proper :
    (∀ {first second : SimpleProductBeta (simpleFamilies.{0})},
      simpleToDependent first = simpleToDependent second ->
        first.product = second.product) ∧
      (¬ ∃ Constant : Type,
        ∀ context : Bool,
          Nonempty
            (((familiesSums.sigma
              (context := Bool) (constantFamily PUnit)
              (fun point => varyingBoolFamily point.1)) context) ≃
                Constant)) :=
  ⟨fun equalSums =>
      simpleToDependent_reflects_product simpleFamilies PUnit equalSums,
    varying_sum_not_constant⟩

#print axioms simpleToDependent_reflects_product
#print axioms constantFamily_sigma_agrees
#print axioms varying_sum_not_constant
#print axioms constant_fragment_reflective_but_proper

end Mettapedia.TypeTheory.ContextualSumComparison
