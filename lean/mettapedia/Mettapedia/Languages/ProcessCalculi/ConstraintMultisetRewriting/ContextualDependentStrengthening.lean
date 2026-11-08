import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReflection

/-!
# Typed equality reflection and certificate-based body strengthening

Exact context inclusions reflect typed equality between independently typed
source terms. An actual target checking certificate also reconstructs typing
for a raw body recovered in the smaller context. No inhabitants are chosen
for omitted declarations. The inclusion's declaration compatibility is
explicit; an arbitrary typed substitution is not assumed to reflect equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentStrengthening

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedEquality.StrongNormalization
open ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra reflects complete in
theorem equal_reflects {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {rho : Ren n m} (injective : Function.Injective rho) (compatible : CtxRen source target rho)
    (sourceFormed : CtxFormed S.R source) (targetFormed : CtxFormed S.R target)
    {first second type : Tm Head n} (firstTyped : Typed S.R source first type)
    (secondTyped : Typed S.R source second type)
    (same : Equal S.R target (Presentation.rename rho first) (Presentation.rename rho second)
      (Presentation.rename rho type)) : Equal S.R source first second type := by
  have comparison := Equal.algorithm (S := S) complete same targetFormed
  have reflected := ContextualDependentAlgorithmReflection.algorithm_reflects reflects comparison
    source rho injective compatible first second type rfl rfl rfl
  exact Algorithm.sound facts roots heads algebra reflected sourceFormed firstTyped secondTyped

include facts roots heads algebra reflects complete in
theorem equal_iff_renamed {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {rho : Ren n m} (injective : Function.Injective rho) (compatible : CtxRen source target rho)
    (sourceFormed : CtxFormed S.R source) (targetFormed : CtxFormed S.R target)
    {first second type : Tm Head n} (firstTyped : Typed S.R source first type)
    (secondTyped : Typed S.R source second type) :
    Equal S.R source first second type ↔
      Equal S.R target (Presentation.rename rho first) (Presentation.rename rho second) (Presentation.rename rho type) :=
  ⟨fun same => same.rename compatible,
    equal_reflects facts roots heads algebra reflects complete injective compatible sourceFormed targetFormed
      firstTyped secondTyped⟩

include facts roots heads algebra reflects complete in
theorem typeEq_reflects {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {rho : Ren n m} (injective : Function.Injective rho) (compatible : CtxRen source target rho)
    (sourceFormed : CtxFormed S.R source) (targetFormed : CtxFormed S.R target)
    {first second : Tm Head n} (firstType : IsType S.R source first) (secondType : IsType S.R source second)
    (same : TypeEq S.R target (Presentation.rename rho first) (Presentation.rename rho second)) :
    TypeEq S.R source first second := by
  have comparison := TypeEq.algorithm (S := S) complete same targetFormed
  have reflected := ContextualDependentAlgorithmReflection.algorithm_reflects reflects comparison
    source rho injective compatible first second rfl rfl
  exact Algorithm.typeEq facts roots heads algebra sourceFormed reflected firstType secondType

variable (declared : DeclaredTypesFormed S.R)

include facts roots heads algebra reflects declared in
theorem checked_body_typed {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (body : Tm Head source.arity)
    (certificate : CheckingAlgorithm S.R .check target.raw
      (Presentation.rename inclusion.forward body) (Presentation.rename inclusion.forward type.code)) :
    Typed S.R source.raw body type.code := by
  have reflected := ContextualDependentCheckingReflection.checking_reflects reflects certificate
    source.raw inclusion.forward inclusion.injective compatible body type.code rfl rfl
  exact CheckingAlgorithm.sound facts roots heads algebra declared reflected source.formed type.isType

/-- Only the raw inverse is computed. Its typing is recovered from the
target certificate by the proved reflection theorem. -/
def recover {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (term : Tm Head target.arity)
    (certificate : CheckingAlgorithm S.R .check target.raw term (Presentation.rename inclusion.forward type.code)) :
    Option (Recovery inclusion type term) :=
  match found : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) term with
  | none => none
  | some body =>
      let image := ContextualDependentInversion.invert_sound term inclusion.forward _
        (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective) body found
      some ⟨⟨body, checked_body_typed facts roots heads algebra reflects declared inclusion compatible type body
        (image.symm ▸ certificate)⟩, image⟩

theorem recover_code {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (term : Tm Head target.arity)
    (certificate : CheckingAlgorithm S.R .check target.raw term (Presentation.rename inclusion.forward type.code))
    {body : Tm Head source.arity}
    (found : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward) term = some body) :
    (recover facts roots heads algebra reflects declared inclusion compatible type term certificate).map
      (fun recovered => recovered.body.code) = some body := by
  unfold recover
  split
  · rename_i impossible
    rw [found] at impossible
    cases impossible
  · rename_i candidate computed
    have same := Option.some.inj (computed.symm.trans found)
    subst candidate
    rfl

theorem recover_of_image {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (body : Tm Head source.arity)
    (certificate : CheckingAlgorithm S.R .check target.raw (Presentation.rename inclusion.forward body)
      (Presentation.rename inclusion.forward type.code)) :
    (recover facts roots heads algebra reflects declared inclusion compatible type
      (Presentation.rename inclusion.forward body) certificate).map (fun recovered => recovered.body.code) = some body :=
  recover_code facts roots heads algebra reflects declared inclusion compatible type _ certificate
    (ContextualDependentInversion.invert_rename body inclusion.forward _
      (ContextualDependentInversion.lookup_exact inclusion.forward inclusion.injective))

end ContextualDependentStrengthening
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
