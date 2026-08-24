import Mettapedia.GSLT.LanguageDef.GSLTILEvidenceWorlds

/-!
# Transport of proof-relevant GSLT-IL elaboration worlds

A represented operational route transports execution paths, but that fact
alone says nothing about the proof histories by which authored commands were
elaborated.  Complete elaboration-world transport therefore requires its own
explicit capability.

An `EvidenceWorldMap` maps internal outcomes and lifts every retained
elaboration witness.  It induces a map on complete worlds and ordered finite
world histories, with identity and composition laws.  Injectivity of the
complete-world map is a strictly stronger optional reflection capability: a
valid forward map may preserve multiplicity while identifying distinct source
histories.

This module does not claim that every GSLT-IL route supplies such a map.  It is
the additional datum a typed route must carry when consumers require transport
of complete elaboration provenance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds

open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

variable {sourceProgram targetProgram : Program}
variable {sourceProfile : Profile sourceProgram}
  {targetProfile : Profile targetProgram}
variable {sourceCommand : sourceProfile.Command}
  {targetCommand : targetProfile.Command}

/-- An explicit capability for transporting one command's proof-relevant
elaboration fibre. -/
structure EvidenceWorldMap
    (sourceProfile : Profile sourceProgram)
    (sourceCommand : sourceProfile.Command)
    (targetProfile : Profile targetProgram)
    (targetCommand : targetProfile.Command) where
  mapInternal : Pattern -> Pattern
  mapEvidence : forall {internal},
    sourceProfile.Evidence sourceCommand internal ->
      targetProfile.Evidence targetCommand (mapInternal internal)

namespace EvidenceWorldMap

/-- Transport one complete outcome/evidence world. -/
def mapWorld
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand) :
    sourceProfile.World sourceCommand -> targetProfile.World targetCommand
  | ⟨internal, evidence⟩ =>
      ⟨transport.mapInternal internal, transport.mapEvidence evidence⟩

/-- Transport every occurrence in one ordered finite world history. -/
def mapHistory
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand) :
    List (sourceProfile.World sourceCommand) ->
      List (targetProfile.World targetCommand) :=
  List.map transport.mapWorld

/-- Identity transports outcomes and their evidence without changing either. -/
def id (profile : Profile sourceProgram) (command : profile.Command) :
    EvidenceWorldMap profile command profile command where
  mapInternal := _root_.id
  mapEvidence := _root_.id

/-- Composition retains the intermediate evidence transformation rather than
asserting a new direct map without construction. -/
def comp
    {middleProgram : Program} {middleProfile : Profile middleProgram}
    {middleCommand : middleProfile.Command}
    (earlier : EvidenceWorldMap sourceProfile sourceCommand
      middleProfile middleCommand)
    (later : EvidenceWorldMap middleProfile middleCommand
      targetProfile targetCommand) :
    EvidenceWorldMap sourceProfile sourceCommand targetProfile targetCommand where
  mapInternal := later.mapInternal ∘ earlier.mapInternal
  mapEvidence := fun evidence =>
    later.mapEvidence (earlier.mapEvidence evidence)

@[simp] theorem mapWorld_id
    (world : sourceProfile.World sourceCommand) :
    (id sourceProfile sourceCommand).mapWorld world = world := by
  rcases world with ⟨internal, evidence⟩
  rfl

@[simp] theorem mapHistory_id
    (history : List (sourceProfile.World sourceCommand)) :
    (id sourceProfile sourceCommand).mapHistory history = history := by
  induction history with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (id sourceProfile sourceCommand).mapWorld head ::
            (id sourceProfile sourceCommand).mapHistory tail =
          head :: tail
      rw [mapWorld_id, inductionHypothesis]

@[simp] theorem mapWorld_comp
    {middleProgram : Program} {middleProfile : Profile middleProgram}
    {middleCommand : middleProfile.Command}
    (earlier : EvidenceWorldMap sourceProfile sourceCommand
      middleProfile middleCommand)
    (later : EvidenceWorldMap middleProfile middleCommand
      targetProfile targetCommand)
    (world : sourceProfile.World sourceCommand) :
    (comp earlier later).mapWorld world =
      later.mapWorld (earlier.mapWorld world) := by
  rcases world with ⟨internal, evidence⟩
  rfl

@[simp] theorem mapHistory_comp
    {middleProgram : Program} {middleProfile : Profile middleProgram}
    {middleCommand : middleProfile.Command}
    (earlier : EvidenceWorldMap sourceProfile sourceCommand
      middleProfile middleCommand)
    (later : EvidenceWorldMap middleProfile middleCommand
      targetProfile targetCommand)
    (history : List (sourceProfile.World sourceCommand)) :
    (comp earlier later).mapHistory history =
      later.mapHistory (earlier.mapHistory history) := by
  induction history with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (comp earlier later).mapWorld head ::
            (comp earlier later).mapHistory tail =
          later.mapWorld (earlier.mapWorld head) ::
            later.mapHistory (earlier.mapHistory tail)
      rw [mapWorld_comp, inductionHypothesis]

/-- World transport never changes occurrence count, even when it identifies
the evidence stored at two positions. -/
@[simp] theorem mapHistory_length
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand)
    (history : List (sourceProfile.World sourceCommand)) :
    (transport.mapHistory history).length = history.length := by
  simp [mapHistory]

/-- Visible target outcomes are exactly the pointwise images of source
outcomes.  Evidence transport is retained in the full world list but absent
from this deliberately coarser projection. -/
@[simp] theorem mapHistory_outcomes
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand)
    (history : List (sourceProfile.World sourceCommand)) :
    (transport.mapHistory history).map Sigma.fst =
      history.map (transport.mapInternal ∘ Sigma.fst) := by
  induction history with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rcases head with ⟨internal, evidence⟩
      change
        transport.mapInternal internal ::
            (transport.mapHistory tail).map Sigma.fst =
          transport.mapInternal internal ::
            tail.map (transport.mapInternal ∘ Sigma.fst)
      rw [inductionHypothesis]

/-- Reflection of complete worlds is additional structure, not a consequence
of having a forward evidence map. -/
def ReflectsWorlds
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand) : Prop :=
  Function.Injective transport.mapWorld

theorem id_reflectsWorlds :
    (id sourceProfile sourceCommand).ReflectsWorlds := by
  intro first second equal
  simpa using equal

theorem comp_reflectsWorlds
    {middleProgram : Program} {middleProfile : Profile middleProgram}
    {middleCommand : middleProfile.Command}
    (earlier : EvidenceWorldMap sourceProfile sourceCommand
      middleProfile middleCommand)
    (later : EvidenceWorldMap middleProfile middleCommand
      targetProfile targetCommand)
    (earlierReflects : earlier.ReflectsWorlds)
    (laterReflects : later.ReflectsWorlds) :
    (comp earlier later).ReflectsWorlds := by
  intro first second equal
  apply earlierReflects
  apply laterReflects
  simpa using equal

/-- World reflection lifts exactly to ordered finite histories. -/
theorem mapHistory_injective
    (transport : EvidenceWorldMap sourceProfile sourceCommand
      targetProfile targetCommand)
    (reflects : transport.ReflectsWorlds) :
    Function.Injective transport.mapHistory := by
  exact List.map_injective_iff.mpr reflects

/-! ## Positive and negative controls -/

namespace Canary

open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds.Canary

def firstDuplicateWorld : duplicateHistoryProfile.World () :=
  ⟨_, DuplicateHistory.first⟩

def secondDuplicateWorld : duplicateHistoryProfile.World () :=
  ⟨_, DuplicateHistory.second⟩

theorem duplicateWorlds_distinct :
    firstDuplicateWorld ≠ secondDuplicateWorld := by
  intro equal
  injection equal with _ historiesEqual
  cases historiesEqual

/-- The identity capability retains both authored histories exactly. -/
theorem identity_retains_duplicate_histories :
    (EvidenceWorldMap.id duplicateHistoryProfile ()).mapHistory
        [firstDuplicateWorld, secondDuplicateWorld] =
      [firstDuplicateWorld, secondDuplicateWorld] :=
  rfl

/-- A sound forward evidence transport may deliberately forget which of two
source histories justified the common internal outcome. -/
def collapseDuplicateHistory :
    EvidenceWorldMap duplicateHistoryProfile () uniqueHistoryProfile () where
  mapInternal := _root_.id
  mapEvidence := by
    intro internal evidence
    cases evidence <;> exact UniqueHistory.only

theorem collapseDuplicateHistory_collision :
    collapseDuplicateHistory.mapWorld firstDuplicateWorld =
      collapseDuplicateHistory.mapWorld secondDuplicateWorld :=
  rfl

/-- Consequently a forward evidence map does not imply reflection of authored
history identity. -/
theorem collapseDuplicateHistory_not_reflects :
    ¬ collapseDuplicateHistory.ReflectsWorlds := by
  intro reflects
  exact duplicateWorlds_distinct
    (reflects collapseDuplicateHistory_collision)

/-- The collapse still preserves the two occurrence positions.  Multiplicity
preservation and history-identity reflection are independent capabilities. -/
theorem collapse_preserves_multiplicity_while_identifying_histories :
    (collapseDuplicateHistory.mapHistory
        [firstDuplicateWorld, secondDuplicateWorld]).length = 2 ∧
      collapseDuplicateHistory.mapHistory [firstDuplicateWorld] =
        collapseDuplicateHistory.mapHistory [secondDuplicateWorld] := by
  constructor
  · rfl
  · simp [mapHistory, collapseDuplicateHistory_collision]

end Canary

#print axioms EvidenceWorldMap.mapWorld_comp
#print axioms EvidenceWorldMap.mapHistory_comp
#print axioms EvidenceWorldMap.mapHistory_length
#print axioms EvidenceWorldMap.mapHistory_outcomes
#print axioms EvidenceWorldMap.mapHistory_injective
#print axioms Canary.identity_retains_duplicate_histories
#print axioms Canary.collapseDuplicateHistory_not_reflects
#print axioms Canary.collapse_preserves_multiplicity_while_identifying_histories

end EvidenceWorldMap

end Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
