import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.WireDataABT
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RequestActivation

/-!
# Send-only authority permits private take and unification read disclosure

Both controls use the actual two-sided ABT substitution action. The original
send-only schema wrapper permits these client steps. Full interaction
formation rejects receive, peek and even an empty private-region observation
without the corresponding facet. The kernel with all four facets can execute
the same ordinary qualified firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormationControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open InferenceSchemaActivation (Tm action Head)

abbrev Value := Bool × Tm
abbrev locatedAction := LocatedSubstitution.action (N := Bool) action
def secret : Tm := WireDataABT.encode (.atom 7)
def done : Tm := WireDataABT.encode (.atom 0)
def location (occurrence : Nat) : Bool := occurrence == 0
def payload (publicValue : Tm) (occurrence : Nat) : Tm := if occurrence = 0 then secret else publicValue
def label (publicValue : Tm) (occurrence : Nat) : Value := (location occurrence, payload publicValue occurrence)

def clientRights (space : Bool) : Facet → Bool
  | .send => !space
  | _ => false

def system : SchemaPublicationAuthority.System Unit Bool Bool Nat location (fun occurrence => location occurrence = true) where
  process := fun actor => ⟨if actor then fun _ _ => true else clientRights, [()]⟩
  kernel := true
  soleWriter := by
    intro actor client occurrence protectedHere
    cases actor with
    | true => exact False.elim (client rfl)
    | false => change clientRights (location occurrence) .send = false; rw [protectedHere]; rfl

def activate (rule : RuleInstance Value) : Unit → Unit → Option (RuleInstance Value) := fun _ _ => some rule
def before : Configuration Value Nat := ⟨[], {0}⟩

def steal : RuleInstance Value := ⟨[(true, secret)], [], [], [], [(false, done)]⟩
def stealSelection : Selection Nat := ⟨[0], [], [1]⟩

theorem steal_valid : stealSelection.Valid locatedAction (label done) steal before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨by simp [stealSelection, Selection.commit, before], by simp [stealSelection, Selection.commit],
      by simp [stealSelection, Selection.commit], by simp [stealSelection, Selection.commit, before],
      by simp [stealSelection, Selection.commit]⟩
  · refine ⟨action.identity, ?_⟩
    change locatedAction.Models action.identity ([] ++ Selection.equations (label done)
      [label done 0] [0] ++ [] ++ [])
    simpa only [List.nil_append, List.append_nil, List.map_cons, List.map_nil] using
      RequestActivation.self_equations locatedAction action.identity (label done) [0]
  · intro check member
    cases member

theorem send_only_client_can_take_private_snapshot :
    system.Step (activate steal) locatedAction (label done) false before
      (stealSelection.result (label done) steal before) := by
  refine ⟨(), by simp [system], (), steal, rfl, stealSelection, steal_valid, ?_, rfl⟩
  intro occurrence made
  have same : occurrence = 1 := by simpa [stealSelection] using made
  subst occurrence
  rfl

theorem taken_private_snapshot_disappears : 0 ∉ (stealSelection.result (label done) steal before).present := by
  simp [Selection.result, Selection.commit, stealSelection, before, fire]

def leak : RuleInstance Value := ⟨[], [(true, .idx 0)], [], [], [(false, .idx 0)]⟩
def leakSelection : Selection Nat := ⟨[], [0], [1]⟩
def binding : ABTProtectedParameters.Assignment Head 0 := ProtectedSubstitution.atBoundary 0 secret

theorem leak_models : locatedAction.Models binding (leakSelection.problem (label (.idx 0)) leak before) := by
  have solved := (ABTProtectedParameters.loose_against_parameterized_value 0 secret (WireDataABT.encode_supported _)).1
  change locatedAction.Models binding [((true, .idx 0), (true, secret))]
  simp only [SubstitutionAction.models_cons, SubstitutionAction.models_nil]
  exact ⟨⟨rfl, solved⟩, True.intro⟩

theorem leak_valid : leakSelection.Valid locatedAction (label (.idx 0)) leak before := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨binding, leak_models⟩, ?_⟩
  · exact ⟨by simp [leakSelection, Selection.commit], by simp [leakSelection, Selection.commit, before],
      by simp [leakSelection, Selection.commit], by simp [leakSelection, Selection.commit, before],
      by simp [leakSelection, Selection.commit]⟩
  · intro check member
    cases member

theorem send_only_client_can_read_private_snapshot :
    system.Step (activate leak) locatedAction (label (.idx 0)) false before
      (leakSelection.result (label (.idx 0)) leak before) := by
  refine ⟨(), by simp [system], (), leak, rfl, leakSelection, leak_valid, ?_, rfl⟩
  intro occurrence made
  have same : occurrence = 1 := by simpa [leakSelection] using made
  subst occurrence
  rfl

theorem private_read_discloses_through_two_way_binding :
    1 ∈ (leakSelection.result (label (.idx 0)) leak before).present ∧
      action.apply binding (payload (.idx 0) 1) = secret := by
  constructor
  · simp [Selection.result, Selection.commit, leakSelection, before, fire]
  · exact ProtectedSubstitution.atBoundary_apply 0 secret

theorem full_formation_refuses_private_take :
    ¬InteractionFormation.Formed clientRights (label done) stealSelection steal := by
  intro formed
  have allowed := formed.physical.taken 0 (by simp [Selection.commit, stealSelection])
  cases allowed

theorem full_formation_refuses_private_read :
    ¬InteractionFormation.Formed clientRights (label (.idx 0)) leakSelection leak := by
  intro formed
  exact InteractionFormation.no_peek_forbids_selected_read formed 0 (by simp [leakSelection]) rfl

theorem strengthened_client_cannot_take_same_snapshot :
    ¬InteractionFormation.SchemaStep system (activate steal) action (payload done) false before
      (stealSelection.result (label done) steal before) := by
  intro step
  have retained := InteractionFormation.no_receive_retains_occurrence step 0 (by simp [before]) rfl
  exact taken_private_snapshot_disappears retained

theorem strengthened_client_cannot_read_private_snapshot :
    ¬InteractionFormation.SchemaStep system (activate leak) action (payload (.idx 0)) false before
      (leakSelection.result (label (.idx 0)) leak before) := by
  rintro ⟨schema, installed, inputs, rule, computed, picked, valid, formed, destination⟩
  have same : leak = rule := Option.some.inj computed
  subst rule
  cases selected : picked.read with
  | nil =>
      have lengths := valid.read_length
      simp [leak, selected] at lengths
  | cons occurrence rest =>
      exact InteractionFormation.no_peek_forbids_selected_read formed occurrence (by rw [selected]; simp) rfl

def observeEmpty : RuleInstance Value := ⟨[], [], [], [.absent (true, secret)], [(false, done)]⟩
def observeSelection : Selection Nat := ⟨[], [], [1]⟩
def empty : Configuration Value Nat := ⟨[], ∅⟩

theorem private_absence_valid_even_when_empty : observeSelection.Valid locatedAction (label done) observeEmpty empty := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ⟨action.identity, by simp [Selection.problem, Selection.equations, empty, observeEmpty, observeSelection]⟩, ?_⟩
  · exact ⟨by simp [Selection.commit, observeSelection], by simp [Selection.commit, observeSelection],
      by simp [Selection.commit, observeSelection], by simp [Selection.commit, observeSelection, empty],
      by simp [Selection.commit, observeSelection]⟩
  · intro check member
    have same : check = .absent (true, secret) := List.mem_singleton.mp member
    subst check
    intro assignment _ occurrence present
    cases present

theorem full_formation_refuses_empty_private_observation :
    ¬InteractionFormation.Formed clientRights (label done) observeSelection observeEmpty := by
  intro formed
  exact InteractionFormation.no_observe_forbids_absence formed (true, secret) (by simp [observeEmpty]) rfl

theorem send_only_client_can_observe_empty_private_region :
    system.Step (activate observeEmpty) locatedAction (label done) false empty
      (observeSelection.result (label done) observeEmpty empty) := by
  refine ⟨(), by simp [system], (), observeEmpty, rfl, observeSelection,
    private_absence_valid_even_when_empty, ?_, rfl⟩
  intro occurrence made
  have same : occurrence = 1 := by simpa [observeSelection] using made
  subst occurrence
  rfl

theorem kernel_all_facets_form_the_same_firing (picked : Selection Nat) (rule : RuleInstance Value) (publicValue : Tm) :
    InteractionFormation.Formed (fun _ _ => true) (label publicValue) picked rule := by
  refine ⟨⟨by intro occurrence member; rfl, by intro occurrence member; rfl,
      by intro occurrence member; rfl, by intro read member value region; rfl⟩, ?_⟩
  intro check member
  cases check <;> trivial

theorem full_kernel_private_take_is_still_ordinary :
    InteractionFormation.SchemaStep system (activate steal) action (payload done) true before
      (stealSelection.result (label done) steal before) := by
  exact ⟨(), by simp [system], (), steal, rfl, stealSelection, steal_valid,
    kernel_all_facets_form_the_same_firing _ _ _, rfl⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormationControls
