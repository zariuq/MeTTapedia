import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentPublicContext
import Mettapedia.GSLT.Core.PolicyFamilyTransport
import Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission

/-!+# Live dependencies of retained service-program observations

Retaining a context and referring to the current context are different
interfaces. A retained runner remains correct for its original interpretation;
using it as an answer about a live context additionally requires adequate
dependency tracking. This module binds that requirement to the actual
service-program backend, including source and environment inspection.

The input family and requested consumers are fixed outside the proposed
dependency system. The concrete family below observes complete outputs,
original source and native environment. It is not a universal inventory of
all future public operations. Its revisions change an actual native binding
and an unrelated annotation. Neither this example nor the generic theorem
selects snapshot or live quotation as the only language interface.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentContextReuse

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open PolicyFamilyAdmittedAt
open SharedJudgmentFragment SharedJudgmentPublicContext
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

universe uRevision uDependency uValue uState

variable {n m : Nat} {State : Type uState}
  {dependencies : DependencySystem.{uRevision, uDependency, uValue}}

/-- Pull the declared consumers back along the actual completed computation.
The retained family has the same policy and result types at each revision. -/
def inspectionAt (assembly : Assembly)
    (inputs : dependencies.Revision → State → Input n m)
    (revision : dependencies.Revision) : PolicyFamily State :=
  (inspectionFamily n m).pullback (fun state => complete assembly (inputs revision state))

def liveInspection (assembly : Assembly)
    (inputs : dependencies.Revision → State → Input n m) :
    dependencies.Revision → (policy : Inspection) → State →
      (inspectionFamily n m).Result policy :=
  fun revision => (inspectionAt assembly inputs revision).decide

/-- Binding code, its actual substitution and the initial world is sufficient
for these three consumers. Complete-output agreement is derived from the
independent backend's elaboration theorem, not assumed as a cache invariant.
Source type/context metadata have no consumer in this particular family. -/
theorem inspection_dependencies_of_inputs (assembly : Assembly)
    (inputs : dependencies.Revision → State → Input n m)
    (bound : ∀ first second, dependencies.SameDependencies first second →
      ∀ state,
        (inputs first state).code = (inputs second state).code ∧
        (inputs first state).environment = (inputs second state).environment ∧
        (inputs first state).initialState = (inputs second state).initialState ∧
        (inputs first state).initialBranch = (inputs second state).initialBranch)
    (atRevision : dependencies.Revision) :
    DependenciesAdequate (family := inspectionAt assembly inputs atRevision)
      (liveInspection assembly inputs) := by
  intro first second same policy state
  obtain ⟨code, environment, world, branch⟩ := bound first second same state
  cases policy with
  | outputs =>
      change (inputs first state).run assembly = (inputs second state).run assembly
      apply run_eq_of_elaboration_eq assembly _ _ _ world branch
      simp only [Input.elaborated, code, environment]
  | originalSource => exact code
  | nativeEnvironment => exact environment

/-- A prepared readout may answer about the live revision only after the
actual dependency law has been supplied. Snapshot reuse needs no such claim
about a newer interpretation. -/
theorem reuse_inspection (assembly : Assembly)
    (inputs : dependencies.Revision → State → Input n m)
    {retained current : dependencies.Revision} {Key : Type*} {readout : State → Key}
    {admission : PolicyFamilyAdmittedAt dependencies retained
      (inspectionAt assembly inputs retained) readout}
    (active : admission.Active current)
    (adequate : DependenciesAdequate (family := inspectionAt assembly inputs retained)
      (liveInspection assembly inputs))
    (prepared : admission.PreparedState) (policy : Inspection) :
    active.runPrepared prepared policy =
      (inspectionFamily n m).decide policy (complete assembly (inputs current prepared.state)) := by
  exact active.runPrepared_live (liveInspection assembly inputs)
    (fun _ _ => rfl) adequate prepared policy

namespace Controls

open NativeWireDataDenotation
open SharedJudgmentPublicContext.Controls

/-- Only the binding affects the selected programs. The annotation represents
metadata outside these promised observations, not an authorization field. -/
structure Revision where
  binding : Value
  annotation : Nat

abbrev bindingDependencies : DependencySystem where
  Revision := Revision
  Dependency := Unit
  Value := Value
  read revision _ := revision.binding

abbrev annotationDependencies : DependencySystem where
  Revision := Revision
  Dependency := Unit
  Value := Nat
  read revision _ := revision.annotation

/-- The caller may inspect either of two genuinely different source
programs with the same output at each binding. -/
def input (revision : Revision) (useDetour : Bool) : Input 4 3 :=
  if useDetour then detour revision.binding else direct revision.binding

theorem input_admitted (revision : Revision) (useDetour : Bool) :
    (input revision useDetour).Admitted common OpaqueRelatorScopedComputation.Common.context := by
  cases useDetour
  · exact parameter_admitted revision.binding
  · exact detour_admitted revision.binding

theorem binding_dependency_adequate (atRevision : Revision) :
    DependenciesAdequate (dependencies := bindingDependencies)
      (family := inspectionAt (dependencies := bindingDependencies) common input atRevision)
      (liveInspection (dependencies := bindingDependencies) common input) := by
  apply inspection_dependencies_of_inputs
  intro first second same state
  have binding : first.binding = second.binding := same ()
  have equal : input first state = input second state := by simp only [input, binding]
  exact ⟨congrArg Input.code equal, congrArg Input.environment equal,
    congrArg Input.initialState equal, congrArg Input.initialBranch equal⟩

def original : Revision := ⟨.natural 2, 0⟩
def changedAnnotation : Revision := ⟨.natural 2, 99⟩
def changedBinding : Revision := ⟨.natural 3, 0⟩

theorem annotation_change_preserves_dependencies :
    bindingDependencies.SameDependencies original changedAnnotation := by
  intro dependency
  rfl

theorem binding_change_is_stale :
    ¬ bindingDependencies.SameDependencies original changedBinding := by
  intro same
  have impossible := same ()
  cases impossible

/-- Existing policy-vector admission retains all three observations. It is
used as a cache readout, not as a new semantic implementation of the source. -/
def admission (system : DependencySystem) (retained : system.Revision)
    (inputs : system.Revision → Bool → Input 4 3) :
    PolicyFamilyAdmittedAt system retained
      (inspectionAt (dependencies := system) common inputs retained)
      (inspectionAt (dependencies := system) common inputs retained).vector where
  realization := (inspectionAt (dependencies := system) common inputs retained).vectorRealization

theorem annotation_change_reuses_all_inspections (useDetour : Bool) (policy : Inspection) :
    ((admission bindingDependencies original input).activate
      annotation_change_preserves_dependencies).runPrepared
        ((admission bindingDependencies original input).prepare useDetour) policy =
      (inspectionFamily 4 3).decide policy (complete common (input changedAnnotation useDetour)) := by
  exact reuse_inspection (dependencies := bindingDependencies) common input _
    (binding_dependency_adequate original) _ policy

theorem changed_binding_changes_backend_output :
    (input original false).run common ≠ (input changedBinding false).run common := by
  exact (same_source_different_environment (.natural 2) (.natural 3) (by decide)).2

/-- A key that checks the unrelated annotation can activate even though the
actual native environment and backend output have changed. -/
theorem annotation_key_misses_binding :
    annotationDependencies.SameDependencies original changedBinding := by
  intro dependency
  rfl

theorem annotation_dependency_inadequate :
    ¬ DependenciesAdequate (dependencies := annotationDependencies)
      (family := inspectionAt (dependencies := annotationDependencies) common input original)
      (liveInspection (dependencies := annotationDependencies) common input) := by
  apply not_dependenciesAdequate_of_collision
    (family := inspectionAt (dependencies := annotationDependencies) common input original)
    (liveInspection (dependencies := annotationDependencies) common input)
    annotation_key_misses_binding Inspection.outputs false
  exact changed_binding_changes_backend_output

/-- Fixed-family correctness plus activation can still give the wrong live
answer. The missing premise is dependency adequacy, not the retained runner's
correctness at its original snapshot. -/
theorem activated_but_wrong_live_output :
    ((admission annotationDependencies original input).activate annotation_key_misses_binding).runPrepared
        ((admission annotationDependencies original input).prepare false) .outputs ≠
      (input changedBinding false).run common := by
  change (input original false).run common ≠ (input changedBinding false).run common
  exact changed_binding_changes_backend_output

/-- Keeping the original snapshot remains meaningful after a live update;
its result is still an actual completed run at the retained context. -/
theorem snapshot_still_authentic :
    (complete common (input original false)).Authentic common ∧
      (input original false).Admitted common OpaqueRelatorScopedComputation.Common.context :=
  ⟨complete_authentic _ _, input_admitted _ _⟩

end Controls

#print axioms inspection_dependencies_of_inputs
#print axioms reuse_inspection
#print axioms Controls.binding_dependency_adequate
#print axioms Controls.annotation_change_reuses_all_inspections
#print axioms Controls.annotation_dependency_inadequate
#print axioms Controls.activated_but_wrong_live_output
#print axioms Controls.snapshot_still_authentic

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentContextReuse
