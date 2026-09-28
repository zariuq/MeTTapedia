import Mettapedia.OSLF.Syntax.Chapter7ClosedBindingControl
import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelModal

/-!
# A binder-local firing through histories and the OSLF observation

The actual LamCong rule uses a premise in the context extended by the
lambda variable. Its free evidence survives as an individual one-step
history, and its endpoint image induces a may-observation. The two lambda
programs remain distinct code despite the operational step.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Chapter7LambdaModelHistoryModal

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison
open Mettapedia.OSLF.Binding.Chapter7ClosedBindingControl
open Mettapedia.OSLF.Binding.IntrinsicLambdaFourRulePresentation
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelHistory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalModelModal
open Mettapedia.OSLF.Binding.EventGraphModalTransport
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

private abbrev A := BindingCloneAlgebra.terms LambdaContextualRung.sig
private noncomputable abbrev Y := SubstitutionModel.free rules A

noncomputable local instance : Quiver (State rules Y [] .term) :=
  modelQuiver rules Y [] .term

private def sourceState : State rules Y [] .term :=
  ⟨applyFunctionArgs A .lam sampleLamSource⟩

private def targetState : State rules Y [] .term :=
  ⟨applyFunctionArgs A .lam sampleLamTarget⟩

/-- The authored lambda congruence step has a retained individual firing
event in the generic contextual model. -/
theorem lamCong_event : Nonempty (sourceState ⟶ targetState) := by
  exact (sourceStep_iff_reduces.mp sampleLam_function_step)

/-- The event supplies a singleton history, preserving its individual
evidence rather than only the endpoint existence predicate. -/
theorem lamCong_history :
    Nonempty (Quiver.Path sourceState targetState) := by
  obtain ⟨event⟩ := lamCong_event
  exact ⟨event.toPath⟩

/-- The lambda programs related by that history are distinct syntax. -/
theorem lamCong_endpoints_distinct : sourceState ≠ targetState := by
  intro equality
  have codeEq := congrArg State.term equality
  change applyFunctionArgs A .lam sampleLamSource =
    applyFunctionArgs A .lam sampleLamTarget at codeEq
  rw [sampleLamSource_code, sampleLamTarget_code] at codeEq
  cases codeEq

/-- The generated OSLF may modality observes this actual binder-local
firing in the closed context. -/
theorem lamCong_may :
    let X : Base A := Opposite.op
      (ContextObject.ofList A.substitution.toClone [])
    gsltDiamond
      (theoryAt (modelEventGraph rules Y) X)
      (fun candidate => candidate = ⟨.term, targetState.term⟩)
      ⟨.term, sourceState.term⟩ := by
  intro X
  apply (gsltDiamond_singleton_iff_step
    (theoryAt (modelEventGraph rules Y) X)
    ⟨.term, sourceState.term⟩
    ⟨.term, targetState.term⟩).2
  exact (modelStep_iff_evidence rules Y X .term
    sourceState.term targetState.term).2 lamCong_event

#print axioms lamCong_event
#print axioms lamCong_history
#print axioms lamCong_endpoints_distinct
#print axioms lamCong_may

end Mettapedia.OSLF.Binding.Chapter7LambdaModelHistoryModal
