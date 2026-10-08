import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2GrammarControls
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceResumableInstances

/-!
# Explicit BTM execution and its material continuation

The original three-premise `I`/`BTM` directive is admitted from its actual
source position. Its structural cursor pauses, then resumes and publishes
the completed two-row result. These are steps of the shared-space contract,
with an admitted execution history and the exact cursor poll account.

The observation retains current facts, the selected source literal and its
poll account. Publication supplies an actual dependent material continuation
and the existing inverse decoder. The row list comes from the structural
cursor, while source-order witnesses remain distinct from its reverse stack.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceMM2GrammarMaterial

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.GSLT.LanguageDef
open ProgrammableSpaceMM2GrammarControls
  (explicitRequest explicitSource explicitRows checkpoint100)

inductive Tag where
  | mm2
  deriving DecidableEq

def languages : Tag → Language Atom
  | .mm2 => ProgrammableSpaceMM2Resumable.language

def policies : (tag : Tag) → Policy (languages tag)
  | .mm2 => ProgrammableSpaceResumableInstances.transactionPolicy 180

abbrev Workspace := Space languages policies

def initial : Workspace := ⟨explicitSource, [], []⟩
def position : Fin explicitSource.length := ⟨5, by decide⟩

theorem source_admitted :
    Admitted languages policies initial .mm2 position explicitRequest :=
  ProgrammableSpaceMM2GrammarControls.explicit_source_admitted

def registered : Workspace :=
  start languages policies initial .mm2 .leaveInert (0 : Nat) position
    explicitRequest source_admitted

theorem registered_started : Started languages policies registered :=
  start_started languages policies initial .mm2 .leaveInert (0 : Nat)
    position explicitRequest source_admitted (initial_started languages policies explicitSource)

def session : Session (languages .mm2) (policies .mm2) where
  origin := ⟨explicitSource, position⟩
  scope := .leaveInert
  request := explicitRequest
  residual := .matching ProgrammableSpaceMM2GrammarControls.start
  policyState := (0 : Nat)

def pausedSession : Session (languages .mm2) (policies .mm2) :=
  { session with residual := .matching checkpoint100, policyState := (100 : Nat) }

def publication : ProgrammableSpaceMM2.Receipt :=
  ⟨explicitRequest, explicitSource, explicitRows⟩

def committedSession : Session (languages .mm2) (policies .mm2) :=
  { pausedSession with residual := .committed publication, policyState := (177 : Nat) }

def resultAtoms : List Atom :=
  ProgrammableSpaceMM2ReceiptControls.context ++ [ProgrammableSpaceMM2ReceiptControls.reachable]

def pauseReceipt : ProgrammableSpaceMM2Resumable.Receipt := ⟨100, 0, 100, none⟩
def commitReceipt : ProgrammableSpaceMM2Resumable.Receipt := ⟨100, 100, 177, some publication⟩

def pauseEvent : PolicyEvent (languages .mm2) (policies .mm2) where
  origin := session.origin
  scope := session.scope
  before := explicitSource
  after := explicitSource
  residualBefore := session.residual
  residualAfter := pausedSession.residual
  receipt := pauseReceipt
  policyBefore := (0 : Nat)
  policyAfter := (100 : Nat)

def commitEvent : PolicyEvent (languages .mm2) (policies .mm2) where
  origin := pausedSession.origin
  scope := pausedSession.scope
  before := explicitSource
  after := resultAtoms
  residualBefore := pausedSession.residual
  residualAfter := committedSession.residual
  receipt := commitReceipt
  policyBefore := (100 : Nat)
  policyAfter := (177 : Nat)

def afterPause : Workspace :=
  ⟨explicitSource, [⟨.mm2, pausedSession⟩], [⟨.mm2, pauseEvent⟩]⟩

def afterCommit : Workspace :=
  ⟨resultAtoms, [⟨.mm2, committedSession⟩], [⟨.mm2, pauseEvent⟩, ⟨.mm2, commitEvent⟩]⟩

theorem actual_pause_step : Step languages policies registered afterPause :=
  Step.fire (languages := languages) (policies := policies) Tag.mm2
    explicitSource explicitSource [] [] [] session pauseReceipt
    (.matching checkpoint100) (100 : Nat)
    ProgrammableSpaceMM2GrammarControls.actual_private_step
    ⟨rfl, by decide, rfl, by decide⟩

theorem actual_publication_step : Step languages policies afterPause afterCommit :=
  Step.fire (languages := languages) (policies := policies) Tag.mm2
    explicitSource resultAtoms [] [] [⟨Tag.mm2, pauseEvent⟩] pausedSession
    commitReceipt (.committed publication) (177 : Nat)
    ProgrammableSpaceMM2GrammarControls.actual_publication
    ⟨rfl, by decide, rfl, by decide⟩

theorem actual_run :
    Relation.ReflTransGen (Step languages policies) registered afterCommit :=
  (Relation.ReflTransGen.single actual_pause_step).tail actual_publication_step

theorem after_pause_started : Started languages policies afterPause :=
  step_started languages policies actual_pause_step registered_started

theorem after_commit_started : Started languages policies afterCommit :=
  step_started languages policies actual_publication_step after_pause_started

theorem events_are_source_and_policy_valid : SoundHistory languages policies afterCommit :=
  started_sound_history languages policies afterCommit after_commit_started

theorem original_scope_and_occurrence_retained :
    afterCommit.pending.map (sessionKey languages policies) =
      registered.pending.map (sessionKey languages policies) :=
  run_keeps_session_scopes languages policies actual_run

theorem original_explicit_literal_retained :
    committedSession.origin.atom = explicitRequest.directive.atom ∧
      publication.request.directive.atom = explicitRequest.directive.atom ∧
      publication.request.directive.atom ≠ ProgrammableSpaceMM2ReceiptControls.joinRequest.directive.atom :=
  ⟨rfl, rfl, ProgrammableSpaceMM2GrammarControls.explicit_input_is_retained.2⟩

theorem cursor_and_source_witness_order :
    (publication.rows.map Prod.snd).map (List.map Prod.snd) = [[2, 1, 0], [4, 3, 0]] ∧
      publication.witnessesInSourceOrder.map (List.map Prod.snd) = [[0, 1, 2], [0, 3, 4]] :=
  ⟨ProgrammableSpaceMM2GrammarControls.raw_stack_positions,
    ProgrammableSpaceMM2GrammarControls.public_source_positions⟩

theorem actual_account_and_publication :
    pausedSession.policyState = (100 : Nat) ∧ committedSession.policyState = (177 : Nat) ∧
      publication.rows.length = 2 := by
  refine ⟨rfl, rfl, ?_⟩
  decide +kernel

theorem private_rows_are_not_an_outcome (outcome : ProgrammableSpaceMM2.Outcome) :
    ¬ (languages .mm2).observes pausedSession.residual outcome := id

theorem publication_is_an_outcome :
    (languages .mm2).observes committedSession.residual ⟨resultAtoms, publication.rows⟩ :=
  ⟨ProgrammableSpaceMM2GrammarControls.explicit_finalization.symm, rfl⟩

/-- Facts, selected source syntax and the cursor account are distinct declared
fields. This observation does not claim to recover every retained packet. -/
def observations (space : Workspace) : List Atom :=
  space.atoms ++ space.pending.flatMap fun work =>
    match work with
    | ⟨.mm2, retained⟩ =>
        [ProgrammableSpaceMM2Controls.form "origin" [retained.origin.atom],
          ProgrammableSpaceMM2Controls.form "polls" [.grounded (.int (.ofNat retained.policyState))]]

def read (atom : Atom) (space : Workspace) : Prop := atom ∈ observations space

theorem observation_keeps_original_literal :
    read (ProgrammableSpaceMM2Controls.form "origin" [explicitRequest.directive.atom]) afterCommit := by
  unfold read observations afterCommit committedSession pausedSession session
  exact List.mem_append_right _ List.mem_cons_self

theorem polls_are_observable :
    ¬ read (ProgrammableSpaceMM2Controls.form "polls" [.grounded (.int 177)]) afterPause ∧
      read (ProgrammableSpaceMM2Controls.form "polls" [.grounded (.int 177)]) afterCommit := by
  unfold read observations
  decide +kernel

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open Mettapedia.GSLT

abbrev coding := ProgrammableSpaceAtomCoding.coding

def beforeState : (ProgrammableSpaceMaterial.states languages policies).obj (world 2) :=
  ⟨afterPause, after_pause_started, by decide⟩

def actualContinuation := ProgrammableSpaceMaterialFamilies.actionContinuation
  languages policies read coding (world 2) beforeState afterCommit (.execute actual_publication_step)

theorem actual_publication_is_material_member :
    ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read coding
        (world 2) beforeState afterCommit (.execute actual_publication_step) ∈
      ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).models
        (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 3)
          ((ProgrammableSpaceMaterial.states languages policies).map
            (ProgrammableSpaceMaterial.extend (world 2)) beforeState))).carrier :=
  ProgrammableSpaceMaterialFamilies.action_is_material_member languages policies read coding
    (world 2) beforeState afterCommit (.execute actual_publication_step)

theorem decoder_recovers_actual_continuation :
    ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).models
      (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 3)
        ((ProgrammableSpaceMaterial.states languages policies).map
          (ProgrammableSpaceMaterial.extend (world 2)) beforeState))).decode
        ⟨ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read coding
          (world 2) beforeState afterCommit (.execute actual_publication_step),
            actual_publication_is_material_member⟩ = actualContinuation :=
  ProgrammableSpaceMaterialFamilies.decode_action_continuation languages policies read coding
    (world 2) beforeState afterCommit (.execute actual_publication_step)

theorem empty_source_has_no_continuation :
    ¬ Nonempty ((ProgrammableSpaceMaterialFamilies.continuations languages policies read coding).native.obj
      (ProgrammableSpaceMaterialFamilies.parameter languages policies read coding (world 3)
        (ProgrammableSpaceMaterialFamilies.emptyState languages policies (world 3)))) := by
  rintro ⟨continuation⟩
  exact ProgrammableSpaceMaterialFamilies.empty_space_has_no_continuation
    languages policies read coding (world 3) continuation

end Mettapedia.GSLT.Logic.ProgrammableSpaceMM2GrammarMaterial
