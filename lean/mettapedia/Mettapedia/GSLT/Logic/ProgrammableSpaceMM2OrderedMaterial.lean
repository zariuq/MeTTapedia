import Mettapedia.GSLT.Logic.ProgrammableSpaceMM2KeyReadings
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceMM2RowMajorControls
import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterialFamilies

/-!
# Row-major MM2 execution and its declared material observations

Physical-key material support is the observation preserved by commuting
instantiated writes. Literal atom support remains separately available.
The conflicting add/remove example distinguishes both finalization orders,
while an actual admitted row-major execution has its own dependent material
continuation and inverse decoder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Logic.ProgrammableSpaceMM2OrderedMaterial

open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open MM2MatchingCursor

/-- The agreement observer codes physical keys, including their constructor
branch. It does not conflate this observation with literal source syntax. -/
theorem commuting_finalizers_material_agreement (space : List Atom)
    (request : ProgrammableSpaceMM2.Request) (rows : List Row)
    (allowed : ∀ sink ∈ request.directive.rule.tmpl.sinks,
      ProgrammableSpaceMM2RowMajorWrites.Allowed sink)
    (independent : ∀ first ∈ ProgrammableSpaceMM2RowMajorWrites.rowWrites
      request.directive.rule.input ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
      request.directive.rule.tmpl.sinks,
      ∀ second ∈ ProgrammableSpaceMM2RowMajorWrites.rowWrites
        request.directive.rule.input ((ProgrammableSpaceMM2Matching.guarded request rows).map Prod.fst)
        request.directive.rule.tmpl.sinks,
        ProgrammableSpaceMM2RowMajorWrites.Independent first second) :
    ProgrammableSpaceMM2KeyReadings.keySupport
        (ProgrammableSpaceMM2RowMajor.finalize space request rows) =
      ProgrammableSpaceMM2KeyReadings.keySupport
        (ProgrammableSpaceMM2Matching.finalize space request rows) := by
  apply (ProgrammableSpaceMM2KeyReadings.keySupport_eq_iff_support _ _).mpr
  exact ProgrammableSpaceMM2RowMajor.finalization_source_agreement
    space request rows allowed independent


open ProgrammableSpaceMM2RowMajorControls
  (request source actualRows nativeAfter sourceAfter checkpoint10)

theorem disjoint_effects_material_agreement :
    ProgrammableSpaceMM2KeyReadings.keySupport
        (ProgrammableSpaceMM2RowMajor.finalize
          ProgrammableSpaceMM2RowMajorControls.disjointSource request
          ProgrammableSpaceMM2RowMajorControls.disjointRows) =
      ProgrammableSpaceMM2KeyReadings.keySupport
        (ProgrammableSpaceMM2Matching.finalize
          ProgrammableSpaceMM2RowMajorControls.disjointSource request
          ProgrammableSpaceMM2RowMajorControls.disjointRows) := by
  apply (ProgrammableSpaceMM2KeyReadings.keySupport_eq_iff_support _ _).mpr
  exact ProgrammableSpaceMM2RowMajorControls.disjoint_mixed_effects_agree

theorem conflicting_effects_key_material_separate :
    ProgrammableSpaceMM2KeyReadings.keySupport nativeAfter ≠
      ProgrammableSpaceMM2KeyReadings.keySupport sourceAfter := by
  intro same
  exact ProgrammableSpaceMM2RowMajorControls.support_separation
    ((ProgrammableSpaceMM2KeyReadings.keySupport_eq_iff_support _ _).mp same)

theorem actual_literal_membership_separates :
    Atom.symbol "b" ∈ nativeAfter ∧ Atom.symbol "b" ∉ sourceAfter := by
  decide +kernel

theorem conflicting_effects_literal_material_separate :
    ProgrammableSpaceReadings.support ProgrammableSpaceAtomCoding.coding nativeAfter ≠
      ProgrammableSpaceReadings.support ProgrammableSpaceAtomCoding.coding sourceAfter := by
  intro same
  have membership :=
    (ProgrammableSpaceReadings.support_eq_iff ProgrammableSpaceAtomCoding.coding _ _).mp
      same (Atom.symbol "b")
  exact actual_literal_membership_separates.2
    (membership.mp actual_literal_membership_separates.1)

inductive Tag where
  | rowMajor
  deriving DecidableEq

def languages : Tag → Language Atom
  | .rowMajor => ProgrammableSpaceMM2RowMajorResumable.language

/-- This account bounds actual formal cursor polls. Native runtime work and
wall time are separate observations. -/
def cursorPolicy (budget : Nat) : Policy ProgrammableSpaceMM2RowMajorResumable.language where
  State := Nat
  permits spent _ _ _ receipt _ _ next :=
    receipt.spentBefore = spent ∧ receipt.spentAfter ≤ budget ∧
      next = receipt.spentAfter ∧ 0 < receipt.grant

def policies : (tag : Tag) → Policy (languages tag)
  | .rowMajor => cursorPolicy 30

abbrev Workspace := Space languages policies

def initial : Workspace := ⟨source, [], []⟩
def position : Fin source.length := ⟨2, by decide⟩

theorem source_admitted :
    Admitted languages policies initial .rowMajor position request :=
  ProgrammableSpaceMM2RowMajorControls.admitted

def registered : Workspace :=
  start languages policies initial .rowMajor .leaveInert (0 : Nat) position
    request source_admitted

theorem registered_started : Started languages policies registered :=
  start_started languages policies initial .rowMajor .leaveInert (0 : Nat) position
    request source_admitted (initial_started languages policies source)

def session : Session (languages .rowMajor) (policies .rowMajor) where
  origin := ⟨source, position⟩
  scope := .leaveInert
  request := request
  residual := .matching ProgrammableSpaceMM2RowMajorControls.start
  policyState := (0 : Nat)

def pausedSession : Session (languages .rowMajor) (policies .rowMajor) :=
  { session with residual := .matching checkpoint10, policyState := (10 : Nat) }

def publication : ProgrammableSpaceMM2.Receipt := ⟨request, source, actualRows⟩

def committedSession : Session (languages .rowMajor) (policies .rowMajor) :=
  { pausedSession with residual := .committed publication, policyState := (30 : Nat) }

def pauseReceipt : ProgrammableSpaceMM2RowMajorResumable.Receipt := ⟨10, 0, 10, none⟩
def commitReceipt : ProgrammableSpaceMM2RowMajorResumable.Receipt :=
  ⟨100, 10, 30, some publication⟩

def pauseEvent : PolicyEvent (languages .rowMajor) (policies .rowMajor) where
  origin := session.origin
  scope := session.scope
  before := source
  after := source
  residualBefore := session.residual
  residualAfter := pausedSession.residual
  receipt := pauseReceipt
  policyBefore := (0 : Nat)
  policyAfter := (10 : Nat)

def commitEvent : PolicyEvent (languages .rowMajor) (policies .rowMajor) where
  origin := pausedSession.origin
  scope := pausedSession.scope
  before := source
  after := nativeAfter
  residualBefore := pausedSession.residual
  residualAfter := committedSession.residual
  receipt := commitReceipt
  policyBefore := (10 : Nat)
  policyAfter := (30 : Nat)

def afterPause : Workspace :=
  ⟨source, [⟨.rowMajor, pausedSession⟩], [⟨.rowMajor, pauseEvent⟩]⟩

def afterCommit : Workspace :=
  ⟨nativeAfter, [⟨.rowMajor, committedSession⟩],
    [⟨.rowMajor, pauseEvent⟩, ⟨.rowMajor, commitEvent⟩]⟩

theorem actual_pause_step : Step languages policies registered afterPause :=
  Step.fire (languages := languages) (policies := policies) Tag.rowMajor
    source source [] [] [] session pauseReceipt (.matching checkpoint10) (10 : Nat)
    ProgrammableSpaceMM2RowMajorControls.actual_private_step
    ⟨rfl, by decide, rfl, by decide⟩

theorem actual_publication_step : Step languages policies afterPause afterCommit :=
  Step.fire (languages := languages) (policies := policies) Tag.rowMajor
    source nativeAfter [] [] [⟨Tag.rowMajor, pauseEvent⟩] pausedSession
    commitReceipt (.committed publication) (30 : Nat)
    ProgrammableSpaceMM2RowMajorControls.actual_publication
    ⟨rfl, by decide, rfl, by decide⟩

theorem actual_run :
    Relation.ReflTransGen (Step languages policies) registered afterCommit :=
  (Relation.ReflTransGen.single actual_pause_step).tail actual_publication_step

theorem after_pause_started : Started languages policies afterPause :=
  step_started languages policies actual_pause_step registered_started

theorem after_commit_started : Started languages policies afterCommit :=
  step_started languages policies actual_publication_step after_pause_started

theorem actual_history_is_sound : SoundHistory languages policies afterCommit :=
  started_sound_history languages policies afterCommit after_commit_started

theorem original_scope_and_occurrence_retained :
    afterCommit.pending.map (sessionKey languages policies) =
      registered.pending.map (sessionKey languages policies) :=
  run_keeps_session_scopes languages policies actual_run

theorem original_literal_and_physical_origins_retained :
    committedSession.origin.atom = request.directive.atom ∧
      publication.request.directive.atom = request.directive.atom ∧
      publication.witnessesInSourceOrder.map (List.map Prod.snd) = [[0], [1]] :=
  ⟨rfl, rfl, ProgrammableSpaceMM2RowMajorControls.physical_origins⟩

theorem publication_observed_in_declared_profile :
    (languages .rowMajor).observes committedSession.residual ⟨nativeAfter, actualRows⟩ :=
  ⟨ProgrammableSpaceMM2RowMajorControls.native_finalization.symm, rfl⟩

theorem unfinished_rows_stay_private (outcome : ProgrammableSpaceMM2.Outcome) :
    ¬ (languages .rowMajor).observes pausedSession.residual outcome := id

theorem actual_poll_account :
    pausedSession.policyState = (10 : Nat) ∧ committedSession.policyState = (30 : Nat) ∧
      commitReceipt.grant = 100 := ⟨rfl, rfl, rfl⟩

theorem insufficient_budget_refuses_publication :
    ¬ (cursorPolicy 29).permits (10 : Nat) .leaveInert source pausedSession.residual
      commitReceipt nativeAfter committedSession.residual (30 : Nat) := by
  intro admitted
  exact (by decide : ¬ (30 : Nat) ≤ 29) admitted.2.1

/-- Literal current facts and explicitly retained syntax/account fields are
observed here. Physical-key support is the separate comparison above. -/
def observations (space : Workspace) : List Atom :=
  space.atoms ++ space.pending.flatMap fun work =>
    match work with
    | ⟨.rowMajor, retained⟩ =>
        [ProgrammableSpaceMM2Controls.form "origin" [retained.origin.atom],
          ProgrammableSpaceMM2Controls.form "polls"
            [.grounded (.int (.ofNat retained.policyState))]]

def read (atom : Atom) (space : Workspace) : Prop := atom ∈ observations space

theorem publication_reveals_middle_fact :
    ¬ read (.symbol "b") afterPause ∧ read (.symbol "b") afterCommit := by
  unfold read observations
  decide +kernel

open _root_.CategoryTheory
open PowerClassPresheafDescent.Controls

def beforeState : (ProgrammableSpaceMaterial.states languages policies).obj (world 2) :=
  ⟨afterPause, after_pause_started, by decide⟩

def actualContinuation := ProgrammableSpaceMaterialFamilies.actionContinuation
  languages policies read ProgrammableSpaceAtomCoding.coding
    (world 2) beforeState afterCommit (.execute actual_publication_step)

theorem actual_publication_is_material_member :
    ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read
        ProgrammableSpaceAtomCoding.coding
        (world 2) beforeState afterCommit (.execute actual_publication_step) ∈
      ((ProgrammableSpaceMaterialFamilies.continuations languages policies read
        ProgrammableSpaceAtomCoding.coding).models
        (ProgrammableSpaceMaterialFamilies.parameter languages policies read
          ProgrammableSpaceAtomCoding.coding (world 3)
          ((ProgrammableSpaceMaterial.states languages policies).map
            (ProgrammableSpaceMaterial.extend (world 2)) beforeState))).carrier :=
  ProgrammableSpaceMaterialFamilies.action_is_material_member languages policies read
    ProgrammableSpaceAtomCoding.coding
    (world 2) beforeState afterCommit (.execute actual_publication_step)

theorem decoder_recovers_actual_continuation :
    ((ProgrammableSpaceMaterialFamilies.continuations languages policies read
      ProgrammableSpaceAtomCoding.coding).models
      (ProgrammableSpaceMaterialFamilies.parameter languages policies read
        ProgrammableSpaceAtomCoding.coding (world 3)
        ((ProgrammableSpaceMaterial.states languages policies).map
          (ProgrammableSpaceMaterial.extend (world 2)) beforeState))).decode
        ⟨ProgrammableSpaceMaterialFamilies.materialContinuation languages policies read
          ProgrammableSpaceAtomCoding.coding (world 2) beforeState afterCommit
          (.execute actual_publication_step), actual_publication_is_material_member⟩ =
      actualContinuation :=
  ProgrammableSpaceMaterialFamilies.decode_action_continuation languages policies read
    ProgrammableSpaceAtomCoding.coding
    (world 2) beforeState afterCommit (.execute actual_publication_step)

end Mettapedia.GSLT.Logic.ProgrammableSpaceMM2OrderedMaterial
