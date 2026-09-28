import Mettapedia.OSLF.Syntax.ScopedStepConstructorFrame
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# The authored LamCong firing contains a scoped child constructor

The general frame comparison is applied to the actual conditional-rule
execution. Its child is requested in the one-variable context of the lambda
body, with the selected premise event retained in the outer history.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.ScopedStepConstructorFrame
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-- The successful open LamCong firing has a selected recursive child at
ambient depth one. The same final assignment and event occur in its history. -/
theorem lamCong_firing_has_scoped_child :
    ∃ (firing : RuleFiring Unit) (spec : RuleBindingSpec)
      (captured completed : Assignment) (event : PremiseEvent Unit)
      (child : ChildRequest Unit),
      lamCongRule.bindings = some spec ∧
      admittedFor lamCongRule spec = true ∧
      firing ∈ applyRuleWithOracle betaOracle RelationEnv.empty language
        0 lamCongRule wrappedRedex ∧
      firing.target = wrappedTarget ∧
      firing.history = [event] ∧
      child.ambient = 1 ∧
      AdmittedChild betaOracle lamCongRule spec 0 0
        localStep.binders.length localStep.source localStep.target
        captured completed event child := by
  obtain ⟨firing, admittedFiring, targetEq, _⟩ :=
    lamCong_executes_open
  obtain ⟨spec, captured, completed, history, declared, admitted, _,
    run, finished⟩ :=
    (mem_applyRuleWithOracle_iff betaOracle RelationEnv.empty language
      0 lamCongRule wrappedRedex firing).mp admittedFiring
  change (completed, history) ∈
    runPremises betaOracle RelationEnv.empty language lamCongRule spec
      0 0 [.scopedStep localStep] captured at run
  have wellScoped : localStep.isWellScopedAt 0 = true := by
    decide +kernel
  obtain ⟨event, child, historyEq, childValid⟩ :=
    singleScopedRun_hasChild betaOracle RelationEnv.empty language
      lamCongRule spec 0 localStep captured completed history
      wellScoped run
  have retained : firing.history = history :=
    finish?_history lamCongRule spec 0 captured completed history
      firing finished
  have childAmbient : child.ambient = 1 := by
    simpa [localStep] using childValid.1
  exact ⟨firing, spec, captured, completed, event, child,
    declared, admitted, admittedFiring, targetEq,
    retained.trans historyEq,
    childAmbient, childValid⟩

private def actualSpec : RuleBindingSpec :=
  { dependencies := [("B", [.base "Term"]), ("C", [.base "Term"])],
    occurrences :=
      [{ «name» := "B", site := .left, path := [0, 0],
         arguments := [.bvar 0] },
       { «name» := "C", site := .right, path := [0, 0],
         arguments := [.bvar 0] },
       { «name» := "B", site := .premise 0 0 0, path := [],
         arguments := [.bvar 0] },
       { «name» := "C", site := .premise 0 0 1, path := [],
         arguments := [.bvar 0] }] }

private def actualCaptureValue : ContextualValue :=
  { dependencies := [.base "Term"], ambient := 0, body := openRedex }

private def actualCapture : Assignment := [("B", actualCaptureValue)]

private theorem actual_spec : lamCongRule.bindings = some actualSpec := by
  rfl

private theorem actual_capture :
    matchRuleAt lamCongRule actualSpec 0 wrappedRedex =
      [actualCapture] := by
  decide +kernel

private theorem actual_source :
    instantiateAt? lamCongRule actualSpec 0 (.premise 0 0 0) []
      localStep.binders.length actualCapture localStep.source =
        some openRedex := by
  decide +kernel

/-- A selected LamCong child has the open beta endpoints whenever all
oracle results at that source have the bound variable as target. This
separates contextual source recovery from the history carrier. -/
theorem selected_lamCong_child_exact_of_unique_target {Evidence : Type}
    (oracle : StepOracle Evidence)
    (outcome : ∀ evidence target,
      (evidence, target) ∈ oracle 1 openRedex →
        target = Pattern.bvar 0)
    (declaredSpec : RuleBindingSpec)
    (captured completed : Assignment) (event : PremiseEvent Evidence)
    (child : ChildRequest Evidence)
    (declared : lamCongRule.bindings = some declaredSpec)
    (selected : captured ∈
      matchRuleAt lamCongRule declaredSpec 0 wrappedRedex)
    (valid : AdmittedChild oracle lamCongRule declaredSpec 0 0
      localStep.binders.length localStep.source localStep.target
      captured completed event child) :
    child.source = openRedex ∧ child.target = .bvar 0 := by
  have specEq : declaredSpec = actualSpec := by
    have eq := declared.symm.trans actual_spec
    exact Option.some.inj eq
  subst declaredSpec
  have captureEq : captured = actualCapture := by
    rw [actual_capture] at selected
    simpa using selected
  subst captured
  have sourceEq : child.source = openRedex := by
    have instantiated := valid.2.1
    rw [actual_source] at instantiated
    exact Option.some.inj instantiated.symm
  have chosen := valid.2.2.2.1
  have ambientEq : child.ambient = 1 := by
    simpa [localStep] using valid.1
  rw [ambientEq, sourceEq] at chosen
  obtain ⟨bound, equality⟩ := List.mem_zipIdx' chosen
  have chosenMember : (child.evidence, child.target) ∈
      oracle 1 openRedex := by
    rw [equality]
    exact List.getElem_mem bound
  have targetEq := outcome child.evidence child.target chosenMember
  exact ⟨sourceEq, targetEq⟩

/-- The authored one-result beta oracle discharges the singleton premise
of the general contextual child theorem. -/
theorem selected_lamCong_child_exact (declaredSpec : RuleBindingSpec)
    (captured completed : Assignment) (event : PremiseEvent Unit)
    (child : ChildRequest Unit)
    (declared : lamCongRule.bindings = some declaredSpec)
    (selected : captured ∈
      matchRuleAt lamCongRule declaredSpec 0 wrappedRedex)
    (valid : AdmittedChild betaOracle lamCongRule declaredSpec 0 0
      localStep.binders.length localStep.source localStep.target
      captured completed event child) :
    child.source = openRedex ∧ child.target = .bvar 0 :=
  selected_lamCong_child_exact_of_unique_target betaOracle
    (by
      intro evidence target selected
      rw [inner_beta_open] at selected
      have pair : evidence = () ∧ target = Pattern.bvar 0 := by
        simpa only [List.mem_singleton, Prod.mk.injEq] using selected
      exact pair.2)
    declaredSpec captured completed event child
    declared selected valid

#print axioms selected_lamCong_child_exact_of_unique_target
#print axioms selected_lamCong_child_exact

end Mettapedia.GSLT.Examples.ScopedLamCongConstructorFrame
