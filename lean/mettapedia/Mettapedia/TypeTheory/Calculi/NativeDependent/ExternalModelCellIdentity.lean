import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalPrimitiveCellIdentity
import Mettapedia.TypeTheory.ContextualProductCellUniqueness

/-!
# Constructor propagation from declaration-local cell admission

The independent evaluator supplies the actual domain and dependent codomain
for each successful type expression. Cartesian naturality propagates the
local primitive readings, dependent-pair comprehension propagates sums, and
dependent function evaluation together with target eta propagates products.
No identity premise for every generated type or context is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelCellIdentity

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCartesianCellIdentity
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualLogicalMorphism

universe a c s t m
variable {S : Symbols.{a}} {C E : CwfWithTerminal.{c,s,t,m}}
variable (source : ModelData S C) (target : ModelData S E)
  (F : StrictCwfMorphism C E)
  (cell : F.toFamilyMorphism.base ⟶ F.toFamilyMorphism.base)
  (sourceStable : StrictPiSubstitution source.products)
  (targetStable : StrictPiSubstitution target.products)
  (targetEta : PiEta target.products targetStable.1)
  (products : PiPreservation F source.products target.products)
  (primitive : PrimitiveIdentity source F cell)

include target sourceStable targetStable targetEta products primitive

/-- A successful independently authored type fixes its complete display
context once the caller context and the individual primitive readings are
fixed. The product step detects the complete function by generic evaluation. -/
theorem type_success_fixed : {n : Nat} →
    (Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n) →
    (type : TypeExpr S n) → (A : C.toCwf.Ty Γ.1) →
    source.evaluateType Γ type = some A →
    cell.app ⟨Γ.1⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ.1⟩) →
    cell.app ⟨C.toCwf.ext Γ.1 A⟩ =
      𝟙 (F.toFamilyMorphism.base.obj ⟨C.toCwf.ext Γ.1 A⟩)
  | _, Γ, .family symbol arguments, A, evaluated, baseFixed =>
      family_success_fixed source F cell primitive Γ symbol arguments A evaluated baseFixed
  | _, Γ, .pi domain body, A, evaluated, baseFixed => by
      have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [ModelData.evaluateTypeLifted] at lifted
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun first second => some (ULift.up (source.products.pi first second)))
        (ULift.up A)).mp lifted with ⟨actualA, actualB, first, second, last⟩
      have result : source.products.pi actualA actualB = A :=
        congrArg ULift.down (Option.some.inj last)
      have domainFixed := type_success_fixed Γ domain actualA first baseFixed
      have codomainFixed := type_success_fixed (Γ.snoc actualA) body actualB second domainFixed
      rw [← result]
      exact Mettapedia.TypeTheory.ContextualProductCellUniqueness.product_fixed
        F cell source.products target.products sourceStable.1 targetStable targetEta products
        actualA actualB baseFixed domainFixed codomainFixed
  | _, Γ, .sigma domain body, A, evaluated, baseFixed => by
      have lifted := (source.evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [ModelData.evaluateTypeLifted] at lifted
      rcases (source.dependentAnnotations_eq_some_iff Γ domain body
        (fun first second => some (ULift.up (source.sums.operations.sigma first second)))
        (ULift.up A)).mp lifted with ⟨actualA, actualB, first, second, last⟩
      have result : source.sums.operations.sigma actualA actualB = A :=
        congrArg ULift.down (Option.some.inj last)
      have domainFixed := type_success_fixed Γ domain actualA first baseFixed
      have codomainFixed := type_success_fixed (Γ.snoc actualA) body actualB second domainFixed
      rw [← result]
      exact sum_fixed F.toFamilyMorphism.base cell source.sums actualA actualB codomainFixed
termination_by _ Γ type _ _ _ => sizeOf type

/-- Actual successful telescope evaluation fixes every successive context.
The empty case uses the mapped terminal object, rather than a cell field. -/
theorem context_success_fixed : {n : Nat} → (raw : ContextExpr S n) →
    (Γ : Mettapedia.TypeTheory.ContextualModelTelescopes.Context C n) →
    source.evaluateContext raw = some Γ →
    cell.app ⟨Γ.1⟩ = 𝟙 (F.toFamilyMorphism.base.obj ⟨Γ.1⟩)
  | _, .nil, Γ, evaluated => by
      have same : Context.nil C = Γ := Option.some.inj evaluated
      rw [← same]
      exact empty_fixed F cell
  | _, .snoc previous type, Γ, evaluated => by
      rw [ModelData.evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨Δ, first, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, second, last⟩
      have same : Δ.snoc A = Γ := Option.some.inj last
      rw [← same]
      exact type_success_fixed source target F cell sourceStable targetStable targetEta products
        primitive Δ type A second (context_success_fixed previous Δ first)

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.ModelCellIdentity
