import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentProjectionInversion

/-!
# Normalized typed inversion without a smaller-context checker search

The input endpoint is independently typed. Its value is reduced, retaining
its original annotation by reduction preservation. A successful normal form
supplies a checking certificate by replay; exact inversion then strengthens
that certificate. The result solves the original endpoint, including redexes
outside the raw checker's fragment. No decidable head equality or separate
body-checking budget is required by this operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentNormalizedRecovery

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentTypedInversion

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (reflects : ContextualDependentReductionReflection.RootReflectsInjections S.R.computation)
  (root : ExecutableReduction.RootEvaluator S.R)
  (covers : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

def recover (fuel : Nat) {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (value : Term target (type.reindex inclusion.hom)) :
    Option (ContextualDependentProjectionInversion.Recovery S.levels inclusion.hom type
      (⟨type.reindex inclusion.hom, value⟩ : TotalTerm target)) :=
  match computed : ExecutableReduction.normalize S.R root fuel value.code with
  | none => none
  | some reduced => do
      let preserved := Reduces.preserve facts roots heads target.formed reduced.property value.typed
      let normalValue : Term target (type.reindex inclusion.hom) := ⟨reduced.val, preserved.1⟩
      have normal : ContextualDependentNormalChecking.Normal (S := S) normalValue.code :=
        ContextualDependentReductionBudget.normal_of_stopped S.R root covers reduced.val
          (ContextualDependentReductionBudget.stopped_of_success S.R root computed)
      let recovered ← ContextualDependentCheckingReplay.recover_normal facts algebra headTypingUnique complete
        roots heads declared reflects inclusion compatible type normalValue normal
      return ⟨recovered.body, by
        refine ⟨(type.reindex inclusion.hom).isType.refl, ?_⟩
        change Equal S.R target.raw (subst (renSub inclusion.forward) recovered.body.code) value.code
          (type.reindex inclusion.hom).code
        rw [subst_renSub, recovered.recovers]
        exact preserved.2.symm⟩

theorem recover_zero {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (value : Term target (type.reindex inclusion.hom)) :
    recover facts roots heads algebra headTypingUnique complete declared reflects root covers
      0 inclusion compatible type value = none := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Once value normalization and raw inversion succeed, typed recovery has
no additional search failure. Its answer still refers to the original value. -/
theorem recover_code {fuel : Nat} {source target : Context S.R} (inclusion : Inclusion source target)
    (compatible : CtxRen source.raw target.raw inclusion.forward) (type : TypeOver source)
    (value : Term target (type.reindex inclusion.hom))
    (reduced : ExecutableReduction.Result S.R value.code)
    (computed : ExecutableReduction.normalize S.R root fuel value.code = some reduced)
    {body : Tm Head source.arity}
    (inverted : ContextualDependentInversion.invert (ContextualDependentInversion.lookup inclusion.forward)
      reduced.val = some body) :
    (recover facts roots heads algebra headTypingUnique complete declared reflects root covers
      fuel inclusion compatible type value).map (fun result => result.body.code) = some body := by
  unfold recover
  split
  · rename_i impossible
    rw [computed] at impossible
    cases impossible
  · rename_i actual accepted
    have same := Option.some.inj (accepted.symm.trans computed)
    subst actual
    have normal : ContextualDependentNormalChecking.Normal (S := S) reduced.val :=
      ContextualDependentReductionBudget.normal_of_stopped S.R root covers reduced.val
        (ContextualDependentReductionBudget.stopped_of_success S.R root computed)
    let normalValue : Term target (type.reindex inclusion.hom) :=
      ⟨reduced.val, (Reduces.preserve facts roots heads target.formed reduced.property value.typed).1⟩
    have code := ContextualDependentCheckingReplay.recover_normal_code facts algebra headTypingUnique complete
      roots heads declared reflects inclusion compatible type normalValue normal inverted
    obtain ⟨answer, success, recoveredCode⟩ := Option.map_eq_some_iff.mp code
    let assemble (recovered : Recovery inclusion type normalValue.code) :
        ContextualDependentProjectionInversion.Recovery S.levels inclusion.hom type
          (⟨type.reindex inclusion.hom, value⟩ : TotalTerm target) :=
      ⟨recovered.body, by
        refine ⟨(type.reindex inclusion.hom).isType.refl, ?_⟩
        change Equal S.R target.raw (subst (renSub inclusion.forward) recovered.body.code) value.code
          (type.reindex inclusion.hom).code
        rw [subst_renSub, recovered.recovers]
        exact (Reduces.preserve facts roots heads target.formed reduced.property value.typed).2.symm⟩
    have finish {α β γ : Type} (input : Option α) (output : α) (build : α → β) (read : β → γ)
        (accepted : input = some output) :
        (input.bind (fun candidate => some (build candidate))).map read = some (read (build output)) := by
      rw [accepted]
      rfl
    have done := finish _ answer assemble (fun result => result.body.code) success
    exact done.trans (congrArg some recoveredCode)

end ContextualDependentNormalizedRecovery
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
