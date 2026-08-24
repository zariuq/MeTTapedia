import Mettapedia.GSLT.LanguageDef.GSLTILEvidenceWorldTransport
import Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKSelection
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport

/-!
# NIK selection for transported proof-relevant GSLT-IL worlds

Complete elaboration histories transport only when a typed route supplies an
explicit `EvidenceWorldMap`.  Such a map induces both an admitted semantic
operation on ordered world histories and the pullback of target observation
policies to source histories.

The target complete-world request again selects the full-world face as its
unique strongest realization.  Current activation applies the retained world
map directly; stale activation is unavailable and leaves the source history
intact for fallback.  Transport and reflection remain separate.  A
non-injective evidence map can preserve list length while identifying two
source histories, so source-history reflection is licensed only by the
additional `ReflectsWorlds` capability.

This module does not infer an evidence-world map from an arbitrary authored or
represented GSLT-IL route.  It states exactly what NIK may retain once a hosted
language constructs that stronger route capability.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKTransport

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyTransport
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {sourceProgram targetProgram : Program}
variable {sourceProfile : Profile sourceProgram}
  {targetProfile : Profile targetProgram}
variable {sourceCommand : sourceProfile.Command}
  {targetCommand : targetProfile.Command}

variable (transport : EvidenceWorldMap sourceProfile sourceCommand
  targetProfile targetCommand)

/-! ## Semantic and observational transport -/

/-- Complete target-world meaning is preserved by every constructed world
map.  No inverse or source-reflection claim is needed for forward execution. -/
def worldTransportOperation :
    worldHistoryObject sourceProfile sourceCommand ⟶
      worldHistoryObject targetProfile targetCommand where
  run := transport.mapHistory
  preserves := fun state _sourceMeaning =>
    every_worldHistory_meaningful targetProfile targetCommand
      (transport.mapHistory state)

@[simp] theorem worldTransportOperation_run
    (state : List (sourceProfile.World sourceCommand)) :
    (worldTransportOperation transport).run state = transport.mapHistory state :=
  rfl

/-- Evidence-world transport composes as ordinary admitted execution. -/
theorem worldTransportOperation_comp
    {middleProgram : Program} {middleProfile : Profile middleProgram}
    {middleCommand : middleProfile.Command}
    (earlier : EvidenceWorldMap sourceProfile sourceCommand
      middleProfile middleCommand)
    (later : EvidenceWorldMap middleProfile middleCommand
      targetProfile targetCommand) :
    worldTransportOperation (EvidenceWorldMap.comp earlier later) =
      AdmissionHom.comp (worldTransportOperation earlier)
        (worldTransportOperation later) := by
  apply AdmissionHom.ext
  funext state
  exact EvidenceWorldMap.mapHistory_comp earlier later state

/-- Target questions become questions of a source history by first
transporting its complete worlds. -/
def transportedPolicies :
    PolicyFamily (List (sourceProfile.World sourceCommand)) :=
  (policies targetProfile targetCommand).pullback transport.mapHistory

/-- Every target readout and runner pulls back along the same evidence-world
map.  This preserves declared target support; it does not recognize new
source-only policies. -/
def transportedCatalog :
    PolicyReadoutCatalog Face (List (sourceProfile.World sourceCommand))
      (transportedPolicies transport) :=
  PolicyReadoutCatalog.pullbackState transport.mapHistory
    (catalog targetProfile targetCommand)

/-! ## Native faces for the transported operation -/

/-- Every observation face executes the same world transport.  Capability
strength records which target questions its readout can answer, not a change
to the transported semantic operation. -/
def transportedNativeFamily :
    RecognizedFamily Face
      (worldHistoryObject sourceProfile sourceCommand)
      (worldHistoryObject targetProfile targetCommand) where
  package := fun _face => worldTransportOperation transport
  Capability := Face
  supports := fun face capability => capability <= face
  supports_mono := by
    intro weaker stronger related capability supported
    exact supported.trans related
  strict_support_gain := by
    intro weaker stronger strict
    exact ⟨stronger, le_rfl, not_le_of_gt strict⟩
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := Finset.Subset.rfl
  licensed_nonempty := Finset.univ_nonempty

def neutralTransportRequest : (transportedNativeFamily transport).CapabilityRequest where
  required := ∅
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      refine ⟨by simp [transportedNativeFamily], ?_⟩
      intro capability required
      simp at required
    · intro _data
      simp
  candidates_nonempty := Finset.univ_nonempty

/-! ## Exact target-world request and strongest selection -/

/-- The transported request asks for the complete target worlds.  Only the
full-world target face has enough retained information to answer it. -/
def completeWorldTransportRequest :
    PolicyCapabilityRequest (transportedCatalog transport)
      (neutralTransportRequest transport) where
  requiredPolicies := {Policy.completeWorlds}
  candidates := {Face.worlds}
  candidates_exact := by
    intro candidate
    cases candidate with
    | cardinality =>
        constructor
        · simp
        · rintro ⟨_native, supported⟩
          have impossible := supported Policy.completeWorlds rfl
          simp [transportedCatalog, PolicyReadoutCatalog.pullbackState,
            catalog, supports] at impossible
    | outcomes =>
        constructor
        · simp
        · rintro ⟨_native, supported⟩
          have impossible := supported Policy.completeWorlds rfl
          simp [transportedCatalog, PolicyReadoutCatalog.pullbackState,
            catalog, supports] at impossible
    | worlds =>
        constructor
        · intro _member
          refine ⟨by simp [neutralTransportRequest], ?_⟩
          intro policy _required
          simp [transportedCatalog, PolicyReadoutCatalog.pullbackState,
            catalog, supports]
        · intro _data
          simp
  candidates_nonempty := by simp

def completeWorldTransportSelection :
    (completeWorldTransportRequest transport).toCapabilityRequest
      |>.StrongestNativeCalculusPrinciple :=
  ⟨Face.worlds, by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        PolicyCapabilityRequest.toCapabilityRequest,
        completeWorldTransportRequest]
    · intro candidate candidateMember
      cases candidate <;>
        simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
          PolicyCapabilityRequest.toCapabilityRequest,
          completeWorldTransportRequest] at candidateMember ⊢⟩

def requestedCompleteWorldPolicy :
    (completeWorldTransportRequest transport).requestedFamily.Policy :=
  ⟨Policy.completeWorlds, rfl⟩

/-- Strongest semantic execution is the retained world map, not a choice of
one source or target history. -/
@[simp] theorem selected_operation_transports_all_worlds
    (state : List (sourceProfile.World sourceCommand)) :
    ((completeWorldTransportRequest transport).toCapabilityRequest
      |>.strongestOperation
        (completeWorldTransportSelection transport)).run state =
      transport.mapHistory state :=
  rfl

/-- The selected target policy returns exactly the mapped complete worlds. -/
@[simp] theorem selected_completeWorld_policy_returns_mapped_worlds
    (state : List (sourceProfile.World sourceCommand)) :
    ((completeWorldTransportRequest transport).strongestRealization
      (completeWorldTransportSelection transport)).run
        (requestedCompleteWorldPolicy transport)
        ((transportedCatalog transport).readout Face.worlds state) =
      transport.mapHistory state :=
  rfl

/-- If the route separately proves complete-world reflection, selected
execution reflects ordered source histories as well. -/
theorem selected_operation_injective
    (reflects : transport.ReflectsWorlds) :
    Function.Injective
      ((completeWorldTransportRequest transport).toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection transport)).run := by
  change Function.Injective transport.mapHistory
  exact EvidenceWorldMap.mapHistory_injective transport reflects

/-! ## Revision-current transported admission -/

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def selectedAt :
    SelectedPolicyAdmissionAt (completeWorldTransportRequest transport)
      dependencies false :=
  SelectedPolicyAdmissionAt.ofStrongest
    (completeWorldTransportRequest transport)
    (completeWorldTransportSelection transport) dependencies false

def active : (selectedAt transport).Active false :=
  (selectedAt transport).activate
    (dependencies.sameDependencies_refl false)

def prepared (state : List (sourceProfile.World sourceCommand)) :
    (selectedAt transport).Prepared :=
  (selectedAt transport).prepare state state

/-- Current activation applies the evidence-world map twice: once as the
semantic operation and once as the requested complete-target-world policy. -/
@[simp] theorem current_run_transports_semantics_and_worlds
    (state : List (sourceProfile.World sourceCommand)) :
    (active transport).runPrepared (prepared transport state)
      (requestedCompleteWorldPolicy transport) =
        (transport.mapHistory state, transport.mapHistory state) :=
  rfl

theorem changed_revision_is_stale : (selectedAt transport).StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- A stale route cannot run, and fallback retains the source history rather
than pretending the target transport can be inverted. -/
theorem stale_refuses_transport_and_preserves_source
    (state : List (sourceProfile.World sourceCommand)) :
    (¬ (selectedAt transport).Active true) ∧
      (prepared transport state).fallback = (state, state) :=
  (selectedAt transport).stale_prevents_activation_and_preserves_fallback
    (changed_revision_is_stale transport) (prepared transport state)

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.Canary
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.EvidenceWorldMap.Canary

def duplicateIdentity :=
  EvidenceWorldMap.id duplicateHistoryProfile ()

/-- Identity transport through the selected current face retains both
histories, their order, and their multiplicity. -/
theorem identity_current_run_retains_both_histories :
    (active duplicateIdentity).runPrepared
        (prepared duplicateIdentity [firstDuplicateWorld, secondDuplicateWorld])
        (requestedCompleteWorldPolicy duplicateIdentity) =
      ([firstDuplicateWorld, secondDuplicateWorld],
        [firstDuplicateWorld, secondDuplicateWorld]) :=
  rfl

theorem source_singletons_distinct :
    [firstDuplicateWorld] ≠ [secondDuplicateWorld] := by
  intro equal
  injection equal with worldsEqual _tailEqual
  exact duplicateWorlds_distinct worldsEqual

/-- The strongest complete-target-world face still cannot reflect distinctions
that the route's evidence map deliberately identifies. -/
theorem collapse_selected_operation_identifies_source_histories :
    ((completeWorldTransportRequest collapseDuplicateHistory).toCapabilityRequest
      |>.strongestOperation
        (completeWorldTransportSelection collapseDuplicateHistory)).run
          [firstDuplicateWorld] =
      ((completeWorldTransportRequest collapseDuplicateHistory).toCapabilityRequest
        |>.strongestOperation
          (completeWorldTransportSelection collapseDuplicateHistory)).run
            [secondDuplicateWorld] := by
  change collapseDuplicateHistory.mapHistory [firstDuplicateWorld] =
    collapseDuplicateHistory.mapHistory [secondDuplicateWorld]
  simp [EvidenceWorldMap.mapHistory, collapseDuplicateHistory_collision]

/-- Current admission faithfully runs that declared forward map; NIK does not
silently strengthen it into a source-reflecting route. -/
theorem collapse_current_runs_agree :
    (active collapseDuplicateHistory).runPrepared
        (prepared collapseDuplicateHistory [firstDuplicateWorld])
        (requestedCompleteWorldPolicy collapseDuplicateHistory) =
      (active collapseDuplicateHistory).runPrepared
        (prepared collapseDuplicateHistory [secondDuplicateWorld])
        (requestedCompleteWorldPolicy collapseDuplicateHistory) := by
  have singletonEqual :
      collapseDuplicateHistory.mapHistory [firstDuplicateWorld] =
        collapseDuplicateHistory.mapHistory [secondDuplicateWorld] := by
    simp [EvidenceWorldMap.mapHistory,
      collapseDuplicateHistory_collision]
  exact congrArg (fun history => (history, history)) singletonEqual

/-- Stale fallback nevertheless retains the distinct source histories. -/
theorem collapse_stale_fallbacks_remain_distinct :
    (prepared collapseDuplicateHistory [firstDuplicateWorld]).fallback ≠
      (prepared collapseDuplicateHistory [secondDuplicateWorld]).fallback := by
  intro equal
  have firstComponents : [firstDuplicateWorld] = [secondDuplicateWorld] := by
    exact congrArg Prod.fst equal
  exact source_singletons_distinct firstComponents

end Canary

#print axioms worldTransportOperation_comp
#print axioms selected_operation_transports_all_worlds
#print axioms selected_completeWorld_policy_returns_mapped_worlds
#print axioms selected_operation_injective
#print axioms current_run_transports_semantics_and_worlds
#print axioms stale_refuses_transport_and_preserves_source
#print axioms Canary.identity_current_run_retains_both_histories
#print axioms Canary.collapse_selected_operation_identifies_source_histories
#print axioms Canary.collapse_current_runs_agree
#print axioms Canary.collapse_stale_fallbacks_remain_distinct

end Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKTransport
