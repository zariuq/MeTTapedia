import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport
import Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

/-!
# Policy transport as an abstract Prime implementation obligation

An admitted Prime implementation already carries a proof-relevant semantic
map on complete execution traces.  This module proves that target policy
families, their retained revision-indexed runners, and exact maximal-native
request fibres pull back along that map.

The implementation does not rerun a checker or selector.  Current activation
uses the retained semantic cell, and policy activation uses the retained keyed
function.  Reflection is deliberately separate: a non-surjective
implementation map may hide target distinctions and thereby make additional
policies valid only on its image.  Such capabilities require fresh
recognition; transport itself does not mint them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.NIKIndexedExecutionAdmission
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport
open Mettapedia.Languages.MeTTa.Prime.PrimeAbstractImplementationModel

universe u uObservation uSourceState uTargetState uPolicy uResult uReadout
  uIndex uCapability uArtifact uKey uRevision uDependency uDependencyValue

namespace AdmittedExecutionModel

variable {Observation : Type uObservation}
variable {dependencies : DependencySystem}
variable {revision currentRevision : dependencies.Revision}
variable {source target :
  IndexedObservedOperationalObject.{u, uObservation} Observation}

/-! ## The implementation's semantic state map -/

/-- The static semantic map on complete proof-relevant traces retained by an
abstract implementation model. -/
def traceMap
    (model : AdmittedExecutionModel dependencies revision source target) :
    ExecutionTrace source.operational → ExecutionTrace target.operational :=
  ExecutionTrace.map model.admission.refinement.refinement

/-- Current compilation is exactly the retained static trace map. -/
@[simp] theorem compileTrace_eq_traceMap
    (model : AdmittedExecutionModel dependencies revision source target)
    (active : model.admission.Active currentRevision)
    (trace : ExecutionTrace source.operational) :
    model.compileTrace active trace = traceMap model trace :=
  model.compileTrace_eq_map active trace

/-- Trace transport through composite implementation models is ordinary
composition of their retained semantic maps. -/
@[simp] theorem traceMap_comp
    {middle : IndexedObservedOperationalObject.{u, uObservation} Observation}
    (earlier : AdmittedExecutionModel dependencies revision source middle)
    (later : AdmittedExecutionModel dependencies revision middle target)
    (trace : ExecutionTrace source.operational) :
    traceMap (earlier.comp later) trace =
      traceMap later (traceMap earlier trace) :=
  earlier.comp_maps_traces later trace

/-! ## Revision-current policy admission over implementation traces -/

/-- Pull a target policy admission back through the implementation's retained
semantic trace map.  The runner and dependency revision are unchanged. -/
def pullbackPolicyAdmission
    (model : AdmittedExecutionModel dependencies revision source target)
    {family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational)}
    {Readout : Type uReadout}
    {readout : ExecutionTrace target.operational → Readout}
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout) :
    PolicyFamilyAdmittedAt dependencies revision
      (family.pullback (traceMap model)) (readout ∘ traceMap model) :=
  PolicyFamilyAdmittedAt.pullbackState (traceMap model) admission

/-- A current implementation supplies the same dependency witness needed to
activate the pulled-back policy display. -/
def pullbackPolicyActive
    (model : AdmittedExecutionModel dependencies revision source target)
    {family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational)}
    {Readout : Type uReadout}
    {readout : ExecutionTrace target.operational → Readout}
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (active : model.admission.Active currentRevision) :
    (pullbackPolicyAdmission model admission).Active currentRevision :=
  ⟨active.current⟩

/-- The implementation-level pulled policy uses exactly the target hot
function retained at admission. -/
@[simp] theorem pullbackPolicyActive_runKey
    (model : AdmittedExecutionModel dependencies revision source target)
    {family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational)}
    {Readout : Type uReadout}
    {readout : ExecutionTrace target.operational → Readout}
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (active : model.admission.Active currentRevision)
    (policy : family.Policy) (encoded : Readout) :
    (pullbackPolicyActive model admission active).runKey policy encoded =
      admission.realization.run policy encoded :=
  rfl

/-- Running the pulled policy at a compiled trace agrees with the target
policy after implementation.  No checking argument appears in either runner. -/
theorem pullbackPolicyActive_run_compiled
    (model : AdmittedExecutionModel dependencies revision source target)
    {family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational)}
    {Readout : Type uReadout}
    {readout : ExecutionTrace target.operational → Readout}
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    (active : model.admission.Active currentRevision)
    (policy : family.Policy) (trace : ExecutionTrace source.operational) :
    (pullbackPolicyActive model admission active).runKey policy
        (readout (model.compileTrace active trace)) =
      family.decide policy (model.compileTrace active trace) := by
  rw [compileTrace_eq_traceMap model active trace]
  exact admission.realization.agrees policy (traceMap model trace)

/-- A stale implementation revision disables the pulled policy display and
preserves the independently encoded raw trace. -/
theorem stale_prevents_pulled_policy_and_preserves_fallback
    (model : AdmittedExecutionModel dependencies revision source target)
    {family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational)}
    {Readout : Type uReadout}
    {readout : ExecutionTrace target.operational → Readout}
    (admission : PolicyFamilyAdmittedAt dependencies revision family readout)
    {candidateRevision : dependencies.Revision}
    (stale : model.StaleAt candidateRevision)
    (prepared : model.PreparedTrace) :
    (¬ (pullbackPolicyAdmission model admission).Active candidateRevision) ∧
      model.rawCodec.decode prepared.fallback = prepared.sourceTrace := by
  constructor
  · rintro ⟨current⟩
    exact stale current
  · exact model.stale_preserves_fallback stale prepared

/-- Pulling a target policy family through a composite implementation is
pointwise the same as pulling through each implementation in sequence. -/
theorem pullbackPolicy_comp_decide
    {middle : IndexedObservedOperationalObject.{u, uObservation} Observation}
    (earlier : AdmittedExecutionModel dependencies revision source middle)
    (later : AdmittedExecutionModel dependencies revision middle target)
    (family : PolicyFamily.{u, uPolicy, uResult}
      (ExecutionTrace target.operational))
    (policy : family.Policy) (trace : ExecutionTrace source.operational) :
    (family.pullback (traceMap (earlier.comp later))).decide policy trace =
      ((family.pullback (traceMap later)).pullback (traceMap earlier)).decide
        policy trace := by
  change family.decide policy (traceMap (earlier.comp later) trace) =
    family.decide policy (traceMap later (traceMap earlier trace))
  rw [traceMap_comp]

/-! ## Exact maximal-native requests over implementation traces -/

variable {Index : Type uIndex} [PartialOrder Index] [DecidableEq Index]
variable {admissionSource admissionTarget : AdmissionObject.{uArtifact}}
variable {base : RecognizedFamily.{uIndex, uCapability, uArtifact} Index
  admissionSource admissionTarget}
variable {policies : PolicyFamily.{u, uPolicy, uResult}
  (ExecutionTrace target.operational)}
variable {catalog :
  PolicyReadoutCatalog.{uIndex, u, uPolicy, uResult, uKey}
    Index (ExecutionTrace target.operational) policies}
variable {nativeRequest : base.CapabilityRequest}

/-- The exact native-plus-policy request seen from the implementation source. -/
def pullbackPolicyRequest
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyCapabilityRequest catalog nativeRequest) :
    PolicyCapabilityRequest
      (PolicyReadoutCatalog.pullbackState (traceMap model) catalog)
      nativeRequest :=
  PolicyCapabilityRequest.pullbackState (traceMap model) request

/-- A maximal target selection remains maximal over the implementation
source because the exact candidate fibre and capability order are retained. -/
def pullbackMaximalPolicySelection
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple) :
    (pullbackPolicyRequest model request).toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple :=
  PolicyCapabilityRequest.pullbackMaximalSelection (traceMap model) request
    selection

/-- A genuinely strongest target selection transports under the same exact
fibre law; no priority order is added. -/
def pullbackStrongestPolicySelection
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection : request.toCapabilityRequest.StrongestNativeCalculusPrinciple) :
    (pullbackPolicyRequest model request).toCapabilityRequest.StrongestNativeCalculusPrinciple :=
  PolicyCapabilityRequest.pullbackStrongestSelection (traceMap model) request
    selection

/-- Maximal implementation transport retains the exact keyed policy runner. -/
@[simp] theorem pullbackMaximalPolicySelection_run
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection :
      request.toCapabilityRequest.restrictedFamily.MaximalNativeCalculusPrinciple)
    (policy : (pullbackPolicyRequest model request).requestedFamily.Policy)
    (encoded : catalog.Key selection.1) :
    ((pullbackPolicyRequest model request).maximalRealization
      (pullbackMaximalPolicySelection model request selection)).run
        policy encoded =
      (request.maximalRealization selection).run policy encoded :=
  rfl

/-- Strongest implementation transport likewise retains the exact keyed
policy runner. -/
@[simp] theorem pullbackStrongestPolicySelection_run
    (model : AdmittedExecutionModel dependencies revision source target)
    (request : PolicyCapabilityRequest catalog nativeRequest)
    (selection : request.toCapabilityRequest.StrongestNativeCalculusPrinciple)
    (policy : (pullbackPolicyRequest model request).requestedFamily.Policy)
    (encoded : catalog.Key selection.1) :
    ((pullbackPolicyRequest model request).strongestRealization
      (pullbackStrongestPolicySelection model request selection)).run
        policy encoded =
      (request.strongestRealization selection).run policy encoded :=
  rfl

end AdmittedExecutionModel

/-! ## A non-surjective implementation boundary -/

namespace Canary

def dependencies : DependencySystem where
  Revision := Unit
  Dependency := Unit
  Value := Unit
  read := fun _ _ => ()

/-- Type-valued reflexive execution evidence for the discrete canary
objects. -/
inductive ReflExecution {State : Type} : State → State → Type where
  | refl (state : State) : ReflExecution state state

def sourceOperational : IndexedOperationalObject where
  State := Unit
  Execution := ReflExecution
  Meaning := fun _ => True

def targetOperational : IndexedOperationalObject where
  State := Bool
  Execution := ReflExecution
  Meaning := fun _ => True

def sourceObserved : IndexedObservedOperationalObject Unit where
  operational := sourceOperational
  observe := fun _ => none

def targetObserved : IndexedObservedOperationalObject Unit where
  operational := targetOperational
  observe := fun _ => none

def refinement : IndexedObservedRefinement sourceObserved targetObserved where
  refinement :=
    { mapState := fun _ => false
      mapExecution := fun
        | .refl _ => .refl false
      preservesMeaning := fun _ _ => True.intro }
  commutes := fun _ => rfl

def sourceCodec : ExactCodec (ExecutionTrace sourceOperational) where
  Representation := Unit
  encode := fun trace => trace.1
  decode := fun state => ⟨state, state, .refl state⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    cases execution
    rfl

def targetCodec : ExactCodec (ExecutionTrace targetOperational) where
  Representation := Bool
  encode := fun trace => trace.1
  decode := fun state => ⟨state, state, .refl state⟩
  decode_encode := by
    rintro ⟨first, last, execution⟩
    cases execution
    rfl

/-- A valid implementation whose semantic image contains only the `false`
target trace. -/
def model : AdmittedExecutionModel dependencies () sourceObserved
    targetObserved where
  admission := ⟨refinement⟩
  rawCodec := sourceCodec
  receiptCodec := targetCodec

def active : model.admission.Active () :=
  model.admission.activate (dependencies.sameDependencies_refl ())

def sourceTrace : ExecutionTrace sourceOperational :=
  ⟨(), (), .refl ()⟩

def falseTrace : ExecutionTrace targetOperational :=
  ⟨false, false, .refl false⟩

def trueTrace : ExecutionTrace targetOperational :=
  ⟨true, true, .refl true⟩

inductive Query where
  | firstState

def targetFamily : PolicyFamily (ExecutionTrace targetOperational) where
  Policy := Query
  Result := fun _ => Bool
  decide := fun _ trace => trace.1

def exactReadout : ExecutionTrace targetOperational → Bool :=
  fun trace => trace.1

def targetAdmission :
    PolicyFamilyAdmittedAt dependencies () targetFamily exactReadout where
  realization :=
    { run := fun _ observed => observed
      agrees := fun _ _ => rfl }

def sourceAdmission :=
  AdmittedExecutionModel.pullbackPolicyAdmission model targetAdmission

def sourcePolicyActive : sourceAdmission.Active () :=
  AdmittedExecutionModel.pullbackPolicyActive model targetAdmission active

/-- One current implementation witness activates the pulled policy, which
runs the target's retained function on the compiled trace. -/
theorem current_pulled_policy_runs_compiled_trace :
    sourcePolicyActive.runKey .firstState
        (exactReadout (model.compileTrace active sourceTrace)) = false :=
  rfl

def collapsedReadout : ExecutionTrace targetOperational → Unit :=
  fun _ => ()

/-- The collapsed readout cannot support the target family because it loses
the target state's Boolean distinction. -/
theorem target_refuses_collapsed_readout :
    ¬ targetFamily.SupportsReadout collapsedReadout := by
  exact targetFamily.not_supportsReadout_of_policy_collision
    collapsedReadout (first := falseTrace) (second := trueTrace) rfl
    .firstState (by
      change false ≠ true
      decide)

def sourceCollapsedRealization :
    (targetFamily.pullback (AdmittedExecutionModel.traceMap model)).ReadoutRealization
      (collapsedReadout ∘ AdmittedExecutionModel.traceMap model) where
  run := fun _ _ => false
  agrees := by
    intro policy trace
    rcases trace with ⟨first, last, execution⟩
    cases first
    cases execution
    rfl

/-- A non-surjective implementation can hide the target distinction: the
source image supports the collapsed readout although the target refuses it. -/
theorem image_support_does_not_reflect_to_target :
    (targetFamily.pullback
        (AdmittedExecutionModel.traceMap model)).SupportsReadout
        (collapsedReadout ∘ AdmittedExecutionModel.traceMap model) ∧
      ¬ targetFamily.SupportsReadout collapsedReadout :=
  ⟨⟨sourceCollapsedRealization⟩, target_refuses_collapsed_readout⟩

/-- The refusal witness also proves that this implementation trace map is not
surjective, exactly matching the generic reflection boundary. -/
theorem traceMap_not_surjective :
    ¬ Function.Surjective (AdmittedExecutionModel.traceMap model) := by
  intro surjective
  have reflected :=
    (targetFamily.supportsReadout_pullback_iff_of_surjective
      (AdmittedExecutionModel.traceMap model) surjective).1
      (show (targetFamily.pullback
          (AdmittedExecutionModel.traceMap model)).SupportsReadout
        (collapsedReadout ∘ AdmittedExecutionModel.traceMap model) from
          ⟨sourceCollapsedRealization⟩)
  exact target_refuses_collapsed_readout reflected

end Canary

#print axioms AdmittedExecutionModel.traceMap_comp
#print axioms AdmittedExecutionModel.pullbackPolicyActive_run_compiled
#print axioms AdmittedExecutionModel.stale_prevents_pulled_policy_and_preserves_fallback
#print axioms AdmittedExecutionModel.pullbackPolicy_comp_decide
#print axioms AdmittedExecutionModel.pullbackMaximalPolicySelection_run
#print axioms AdmittedExecutionModel.pullbackStrongestPolicySelection_run
#print axioms Canary.current_pulled_policy_runs_compiled_trace
#print axioms Canary.image_support_does_not_reflect_to_target
#print axioms Canary.traceMap_not_surjective

end Mettapedia.Languages.MeTTa.Prime.PrimeImplementationPolicyTransport
