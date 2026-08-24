import Mettapedia.GSLT.LanguageDef.GSLTILMultiworldObservation
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection

/-!
# NIK selection over proof-relevant GSLT-IL worlds

An ambiguous GSLT-IL command may retain several internal outcomes and several
derivation histories for one outcome.  This module connects that existing
multiworld semantics to request-local maximal-native NIK selection.

Three native observation faces expose successively more of one unchanged
world history:

* cardinality;
* visible internal outcomes with multiplicity;
* complete outcome/history worlds.

An exact policy request may select a face only when the requested answers
factor through its readout.  A complete-history request therefore selects the
full-world face, while the outcome and cardinality faces are excluded.  The
selected semantic operation is identity on the retained world history: NIK
selects an observation capability, not one elaboration world.  In particular,
this request-local strongest face can exist even when the underlying raw
elaboration relation has no functional representation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKSelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.MultiworldObservation
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {program : Program} (profile : Profile program)
  (command : profile.Command)

/-! ## The ordered native observation faces -/

/-- Native observation faces ordered by distinctions retained. -/
inductive Face where
  | cardinality
  | outcomes
  | worlds
deriving DecidableEq, Repr, Fintype

deriving instance Inhabited for Face

namespace Face

/-- Rank is exactly the information order: cardinality < outcomes < worlds. -/
def rank : Face -> Nat
  | .cardinality => 0
  | .outcomes => 1
  | .worlds => 2

theorem rank_injective : Function.Injective rank := by
  intro first second equal
  cases first <;> cases second <;> simp [rank] at equal ⊢

instance : LinearOrder Face := LinearOrder.lift' rank rank_injective

@[simp] theorem cardinality_le_outcomes :
    Face.cardinality <= Face.outcomes := by decide

@[simp] theorem outcomes_le_worlds :
    Face.outcomes <= Face.worlds := by decide

@[simp] theorem cardinality_le_worlds :
    Face.cardinality <= Face.worlds := by decide

end Face

abbrev State := List (profile.World command)

/-- The three exact consumer questions corresponding to the observation
faces.  Their result types remain heterogeneous. -/
inductive Policy where
  | count
  | visibleOutcomes
  | completeWorlds
deriving DecidableEq, Repr

/-- The policy family is evaluated against the retained complete world
history, independently of which native face later realizes it. -/
def policies : PolicyFamily (State profile command) where
  Policy := Policy
  Result := fun
    | .count => Nat
    | .visibleOutcomes => List Pattern
    | .completeWorlds => State profile command
  decide := fun
    | .count => List.length
    | .visibleOutcomes => List.map Sigma.fst
    | .completeWorlds => id

/-- The key type exposed by each face. -/
def Key : Face -> Type
  | .cardinality => Nat
  | .outcomes => List Pattern
  | .worlds => State profile command

/-- The native readout of each face. -/
def readout : (face : Face) -> State profile command -> Key profile command face
  | .cardinality => List.length
  | .outcomes => List.map Sigma.fst
  | .worlds => id

/-- Exact policy support.  A face supports precisely the prefix of questions
whose distinctions it retains. -/
def supports : Face -> Policy -> Prop
  | .cardinality, .count => True
  | .outcomes, .count => True
  | .outcomes, .visibleOutcomes => True
  | .worlds, _ => True
  | _, _ => False

/-- Execute a supported policy from the selected native key. -/
def runner (face : Face) (policy : Policy)
    (supported : supports face policy) :
    Key profile command face -> (policies profile command).Result policy :=
  match face, policy with
  | .cardinality, .count => id
  | .cardinality, .visibleOutcomes => False.elim supported
  | .cardinality, .completeWorlds => False.elim supported
  | .outcomes, .count => List.length
  | .outcomes, .visibleOutcomes => id
  | .outcomes, .completeWorlds => False.elim supported
  | .worlds, .count => List.length
  | .worlds, .visibleOutcomes => List.map Sigma.fst
  | .worlds, .completeWorlds => id

theorem runner_agrees (face : Face) (policy : Policy)
    (supported : supports face policy) (state : State profile command) :
    runner profile command face policy supported (readout profile command face state) =
      (policies profile command).decide policy state := by
  cases face <;> cases policy <;>
    simp [runner, readout, policies, supports] at supported ⊢

theorem supports_mono {weaker stronger : Face}
    (related : weaker <= stronger) (policy : Policy)
    (supported : supports weaker policy) : supports stronger policy := by
  change Face.rank weaker <= Face.rank stronger at related
  cases weaker <;> cases stronger <;> cases policy <;>
    simp [Face.rank, supports] at related supported ⊢

/-- The exact readouts and policy runners displayed over the three native
faces. -/
def catalog :
    PolicyReadoutCatalog Face (State profile command)
      (policies profile command) where
  Key := Key profile command
  readout := readout profile command
  Supports := supports
  runner := runner profile command
  agrees := runner_agrees profile command
  supports_mono := supports_mono

/-! ## The world-retaining native family -/

/-- The semantic fibre states that complete-world observation returns the
unchanged ordered history.  Empty and nonempty histories are both admitted;
no ambiguity is selected away. -/
def worldHistoryObject : AdmissionObject where
  Carrier := State profile command
  Meaning := fun state =>
    (worlds profile command).observe state = some state

theorem every_worldHistory_meaningful (state : State profile command) :
    (worldHistoryObject profile command).Meaning state :=
  worlds_observe profile command state

/-- Every observation face leaves the semantic world history untouched.
Only the separately displayed readout capability varies. -/
def identityOperation :
    worldHistoryObject profile command ⟶ worldHistoryObject profile command :=
  AdmissionHom.id (worldHistoryObject profile command)

/-- Native capability strength follows the distinctions retained by a face.
The executable semantic operation remains identity at every index. -/
def nativeFamily :
    RecognizedFamily Face (worldHistoryObject profile command)
      (worldHistoryObject profile command) where
  package := fun _ => identityOperation profile command
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

/-- Before a consumer declares its observation needs, every recognized face
is an exact native candidate. -/
def neutralNativeRequest : (nativeFamily profile command).CapabilityRequest where
  required := ∅
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      refine ⟨by simp [nativeFamily], ?_⟩
      intro capability required
      simp at required
    · intro _data
      simp
  candidates_nonempty := Finset.univ_nonempty

/-! ## Exact full-world request and strongest selection -/

/-- Complete-history consumers admit only the full-world face.  This is an
exact candidate statement, not a dispatcher preference. -/
def completeWorldRequest :
    PolicyCapabilityRequest (catalog profile command)
      (neutralNativeRequest profile command) where
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
          simp [catalog, supports] at impossible
    | outcomes =>
        constructor
        · simp
        · rintro ⟨_native, supported⟩
          have impossible := supported Policy.completeWorlds rfl
          simp [catalog, supports] at impossible
    | worlds =>
        constructor
        · intro _member
          refine ⟨by simp [neutralNativeRequest], ?_⟩
          intro policy _required
          simp [catalog, supports]
        · intro _data
          simp
  candidates_nonempty := by simp

/-- The complete-world face is the unique strongest member of the exact
complete-history request. -/
def completeWorldSelection :
    (completeWorldRequest profile command).toCapabilityRequest
      |>.StrongestNativeCalculusPrinciple :=
  ⟨Face.worlds, by
    constructor
    · simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
        PolicyCapabilityRequest.toCapabilityRequest,
        completeWorldRequest]
    · intro candidate candidateMember
      cases candidate <;>
        simp [RecognizedFamily.CapabilityRequest.restrictedFamily,
          PolicyCapabilityRequest.toCapabilityRequest,
          completeWorldRequest] at candidateMember ⊢⟩

def requestedCompleteWorldPolicy :
    (completeWorldRequest profile command).requestedFamily.Policy :=
  ⟨Policy.completeWorlds, rfl⟩

/-- The selected readout reconstructs the complete requested dependent policy
vector. -/
theorem selected_completeWorld_refines_requestedVector :
    NonFactorization.Factors
      ((catalog profile command).readout
        (completeWorldSelection profile command).1)
      (completeWorldRequest profile command).requestedFamily.vector :=
  ((completeWorldRequest profile command).strongestRealization
    (completeWorldSelection profile command)).vectorFactors

/-- Selecting the strongest full-history face does not transform, sort,
deduplicate, or choose from the retained world list. -/
@[simp] theorem selected_operation_retains_all_worlds
    (state : State profile command) :
    ((completeWorldRequest profile command).toCapabilityRequest
      |>.strongestOperation (completeWorldSelection profile command)).run state =
        state :=
  rfl

/-- Its policy runner returns the exact complete world history. -/
@[simp] theorem selected_completeWorld_policy_returns_all_worlds
    (state : State profile command) :
    ((completeWorldRequest profile command).strongestRealization
      (completeWorldSelection profile command)).run
        (requestedCompleteWorldPolicy profile command)
        ((catalog profile command).readout Face.worlds state) = state :=
  rfl

/-- Weaker faces are unavailable for a complete-history request. -/
theorem weaker_faces_refuse_completeWorld_policy :
    ¬ (catalog profile command).Supports Face.cardinality
        Policy.completeWorlds ∧
      ¬ (catalog profile command).Supports Face.outcomes
        Policy.completeWorlds := by
  simp [catalog, supports]

/-! ## Revision-current activation -/

def dependencies : Mettapedia.GSLT.LanguageDef.NIKRouteAdmission.DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read := fun revision _ => revision

def selectedAt :
    SelectedPolicyAdmissionAt (completeWorldRequest profile command)
      dependencies false :=
  SelectedPolicyAdmissionAt.ofStrongest
    (completeWorldRequest profile command)
    (completeWorldSelection profile command) dependencies false

def active : (selectedAt profile command).Active false :=
  (selectedAt profile command).activate
    (dependencies.sameDependencies_refl false)

def prepared (state : State profile command) :
    (selectedAt profile command).Prepared :=
  (selectedAt profile command).prepare state state

/-- Current activation runs the identity semantic operation and complete-world
policy directly from the retained functions. -/
@[simp] theorem current_run_retains_semantics_and_worlds
    (state : State profile command) :
    (active profile command).runPrepared (prepared profile command state)
      (requestedCompleteWorldPolicy profile command) = (state, state) :=
  rfl

theorem changed_revision_is_stale :
    (selectedAt profile command).StaleAt true := by
  intro same
  have impossible := same ()
  simp [dependencies] at impossible

/-- Revision staleness disables the native face while preserving both copies
of the full world history for fallback. -/
theorem stale_refuses_activation_and_preserves_worlds
    (state : State profile command) :
    (¬ (selectedAt profile command).Active true) ∧
      (prepared profile command state).fallback = (state, state) :=
  (selectedAt profile command).stale_prevents_activation_and_preserves_fallback
    (changed_revision_is_stale profile command)
    (prepared profile command state)

/-! ## The non-collapse canary -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.Canary

/-- NIK has a unique strongest face for a complete-history request even when
the underlying authored elaboration profile has two histories and no direct
functional representation.  Selection is relative to the observation request;
it does not functionalize the raw language. -/
theorem strongest_world_face_does_not_imply_functional_elaboration :
    Nonempty
        ((completeWorldRequest duplicateHistoryProfile ()).toCapabilityRequest
          |>.StrongestNativeCalculusPrinciple) ∧
      ¬ Nonempty (Representation duplicateHistoryProfile.related) :=
  ⟨⟨completeWorldSelection duplicateHistoryProfile ()⟩,
    duplicateHistory_not_representable⟩

def firstWorld : duplicateHistoryProfile.World () :=
  ⟨_, DuplicateHistory.first⟩

def secondWorld : duplicateHistoryProfile.World () :=
  ⟨_, DuplicateHistory.second⟩

theorem firstWorld_ne_secondWorld : firstWorld ≠ secondWorld := by
  intro equal
  injection equal with _ historiesEqual
  cases historiesEqual

/-- Both authored histories survive selected current execution in their
original order and multiplicity. -/
theorem selected_current_execution_keeps_both_histories :
    (active duplicateHistoryProfile ()).runPrepared
        (prepared duplicateHistoryProfile () [firstWorld, secondWorld])
        (requestedCompleteWorldPolicy duplicateHistoryProfile ()) =
      ([firstWorld, secondWorld], [firstWorld, secondWorld]) :=
  rfl

/-- The visible-outcome face still cannot answer every history-sensitive
question on this profile. -/
theorem outcome_face_remains_ineligible_for_complete_history :
    ¬ (catalog duplicateHistoryProfile ()).Supports Face.outcomes
      Policy.completeWorlds := by
  simp [catalog, supports]

end Canary

#print axioms runner_agrees
#print axioms selected_completeWorld_refines_requestedVector
#print axioms selected_operation_retains_all_worlds
#print axioms selected_completeWorld_policy_returns_all_worlds
#print axioms weaker_faces_refuse_completeWorld_policy
#print axioms current_run_retains_semantics_and_worlds
#print axioms stale_refuses_activation_and_preserves_worlds
#print axioms Canary.strongest_world_face_does_not_imply_functional_elaboration
#print axioms Canary.firstWorld_ne_secondWorld
#print axioms Canary.selected_current_execution_keeps_both_histories
#print axioms Canary.outcome_face_remains_ineligible_for_complete_history

end Mettapedia.Languages.MeTTa.Prime.GSLTILMultiworldPolicyNIKSelection
