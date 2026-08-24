import Mettapedia.GSLT.LanguageDef.GSLTILEvidenceWorldTransport
import Mettapedia.GSLT.LanguageDef.StructuralCategory

/-!
# Typed structural routes on proof-relevant GSLT-IL profiles

An operational presentation map determines how internal patterns are renamed,
but it does not by itself determine how authored commands or their elaboration
proofs move.  A `TypedEvidenceRoute` is the additional displayed structure:
it maps commands, proves that their surface syntax follows the structural map,
and transports every elaboration witness over the structurally mapped internal
pattern.

The construction has identity and composition laws.  Restricting it to one
source command produces the existing `EvidenceWorldMap`, so NIK's
request-local world transport is derived from this typed route capability
rather than supplied as an unrelated function.

Forward transport and reflection remain separate.  Command injectivity plus
fibrewise world injectivity is sufficient to reflect complete command/world
states and ordered command histories; neither condition is required for a
sound forward route.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- One evidence-valued authored profile displayed over a validated language
presentation.  The presentation and elaboration program remain separate
projections of the same hosted language package. -/
structure EvidenceProfileOver (presentation : ValidatedLanguageDef) where
  program : Program
  profile : Profile program

/-- A typed proof-world route displayed over one structural presentation
morphism.  It carries an executable internal map for native use and proves
that map pointwise equal to `structural.symbols`; the route also supplies the
genuinely additional command and evidence actions. -/
structure TypedEvidenceRoute
    {sourcePresentation targetPresentation : ValidatedLanguageDef}
    (source : EvidenceProfileOver sourcePresentation)
    (target : EvidenceProfileOver targetPresentation) where
  structural : StructuralMorphism sourcePresentation targetPresentation
  mapCommand : source.profile.Command -> target.profile.Command
  mapInternal : Pattern -> Pattern
  mapInternal_structural : forall internal,
    mapInternal internal = mapPattern structural.symbols internal
  surface_natural : forall command,
    target.profile.surface (mapCommand command) =
      mapInternal (source.profile.surface command)
  mapEvidence : forall {command internal},
    source.profile.Evidence command internal ->
      target.profile.Evidence (mapCommand command)
        (mapInternal internal)

namespace TypedEvidenceRoute

variable {sourcePresentation middlePresentation targetPresentation :
  ValidatedLanguageDef}
variable {source : EvidenceProfileOver sourcePresentation}
  {middle : EvidenceProfileOver middlePresentation}
  {target : EvidenceProfileOver targetPresentation}

/-- Restrict a typed route to one authored source command. -/
def atCommand (route : TypedEvidenceRoute source target)
    (command : source.profile.Command) :
    EvidenceWorldMap source.profile command target.profile
      (route.mapCommand command) where
  mapInternal := route.mapInternal
  mapEvidence := route.mapEvidence

/-- Map one complete authored command/world pair. -/
def mapCommandWorld (route : TypedEvidenceRoute source target) :
    (Sigma fun command => source.profile.World command) ->
      Sigma fun command => target.profile.World command
  | ⟨command, world⟩ =>
      ⟨route.mapCommand command, (route.atCommand command).mapWorld world⟩

/-- Map an ordered finite history together with the command whose worlds it
records. -/
def mapCommandHistory (route : TypedEvidenceRoute source target) :
    (Sigma fun command => List (source.profile.World command)) ->
      Sigma fun command => List (target.profile.World command)
  | ⟨command, history⟩ =>
      ⟨route.mapCommand command, (route.atCommand command).mapHistory history⟩

/-- The transported evidence is still an authored target elaboration.  The
surface coherence field identifies its surface command with the structural
image of the source surface. -/
theorem mappedWorld_elaborates_structural_surface
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (world : source.profile.World command) :
    Elaborates target.program
      (mapPattern route.structural.symbols
        (source.profile.surface command))
      (mapPattern route.structural.symbols world.1) := by
  rw [<- route.mapInternal_structural,
    <- route.mapInternal_structural,
    <- route.surface_natural command]
  exact target.profile.sound (route.mapEvidence world.2)

/-- Identity transports commands and their evidence worlds without choosing
or erasing a history. -/
def id (profile : EvidenceProfileOver sourcePresentation) :
    TypedEvidenceRoute profile profile where
  structural := StructuralMorphism.id sourcePresentation
  mapCommand := _root_.id
  mapInternal := _root_.id
  mapInternal_structural := fun internal => (mapPattern_id internal).symm
  surface_natural := fun _ => rfl
  mapEvidence := _root_.id

/-- Compose the structural action, command map, and dependent evidence map in
the same order. -/
def comp (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target) :
    TypedEvidenceRoute source target where
  structural := StructuralMorphism.comp earlier.structural later.structural
  mapCommand := later.mapCommand ∘ earlier.mapCommand
  mapInternal := later.mapInternal ∘ earlier.mapInternal
  mapInternal_structural := by
    intro internal
    calc
      later.mapInternal (earlier.mapInternal internal) =
          mapPattern later.structural.symbols
            (earlier.mapInternal internal) :=
        later.mapInternal_structural _
      _ = mapPattern later.structural.symbols
          (mapPattern earlier.structural.symbols internal) :=
        congrArg (mapPattern later.structural.symbols)
          (earlier.mapInternal_structural internal)
      _ = mapPattern
          (earlier.structural.symbols.comp later.structural.symbols)
          internal :=
        (mapPattern_comp earlier.structural.symbols
          later.structural.symbols internal).symm
  surface_natural := by
    intro command
    exact (later.surface_natural (earlier.mapCommand command)).trans
      (congrArg later.mapInternal (earlier.surface_natural command))
  mapEvidence := fun evidence =>
    later.mapEvidence (earlier.mapEvidence evidence)

@[simp] theorem atCommand_id_mapWorld
    (profile : EvidenceProfileOver sourcePresentation)
    (command : profile.profile.Command)
    (world : profile.profile.World command) :
    ((id profile).atCommand command).mapWorld world = world := by
  rcases world with ⟨internal, evidence⟩
  rfl

@[simp] theorem atCommand_id_mapHistory
    (profile : EvidenceProfileOver sourcePresentation)
    (command : profile.profile.Command)
    (history : List (profile.profile.World command)) :
    ((id profile).atCommand command).mapHistory history = history := by
  change List.map ((id profile).atCommand command).mapWorld history = history
  induction history with
  | nil => rfl
  | cons world rest inductionHypothesis =>
      simp only [List.map_cons]
      rw [atCommand_id_mapWorld, inductionHypothesis]
      rfl

@[simp] theorem atCommand_comp_mapWorld
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (command : source.profile.Command)
    (world : source.profile.World command) :
    ((comp earlier later).atCommand command).mapWorld world =
      (later.atCommand (earlier.mapCommand command)).mapWorld
        ((earlier.atCommand command).mapWorld world) := by
  rcases world with ⟨internal, evidence⟩
  rfl

@[simp] theorem atCommand_comp_mapHistory
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (command : source.profile.Command)
    (history : List (source.profile.World command)) :
    ((comp earlier later).atCommand command).mapHistory history =
      (later.atCommand (earlier.mapCommand command)).mapHistory
        ((earlier.atCommand command).mapHistory history) := by
  change
    List.map ((comp earlier later).atCommand command).mapWorld history =
      List.map (later.atCommand (earlier.mapCommand command)).mapWorld
        (List.map (earlier.atCommand command).mapWorld history)
  rw [List.map_map]
  exact List.map_congr_left fun world _ =>
    atCommand_comp_mapWorld earlier later command world

@[simp] theorem mapCommandWorld_id
    (profile : EvidenceProfileOver sourcePresentation)
    (state : Sigma fun command => profile.profile.World command) :
    (id profile).mapCommandWorld state = state := by
  rcases state with ⟨command, world⟩
  change
    Sigma.mk command ((id profile).atCommand command |>.mapWorld world) =
      Sigma.mk command world
  rw [atCommand_id_mapWorld]

@[simp] theorem mapCommandWorld_comp
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (state : Sigma fun command => source.profile.World command) :
    (comp earlier later).mapCommandWorld state =
      later.mapCommandWorld (earlier.mapCommandWorld state) := by
  rcases state with ⟨command, world⟩
  change
    Sigma.mk (later.mapCommand (earlier.mapCommand command))
        (((comp earlier later).atCommand command).mapWorld world) =
      Sigma.mk (later.mapCommand (earlier.mapCommand command))
        ((later.atCommand (earlier.mapCommand command)).mapWorld
          ((earlier.atCommand command).mapWorld world))
  rw [atCommand_comp_mapWorld]

@[simp] theorem mapCommandHistory_id
    (profile : EvidenceProfileOver sourcePresentation)
    (state : Sigma fun command => List (profile.profile.World command)) :
    (id profile).mapCommandHistory state = state := by
  rcases state with ⟨command, history⟩
  change
    Sigma.mk command ((id profile).atCommand command |>.mapHistory history) =
      (Sigma.mk command history :
        Sigma fun command => List (profile.profile.World command))
  rw [atCommand_id_mapHistory]

@[simp] theorem mapCommandHistory_comp
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (state : Sigma fun command => List (source.profile.World command)) :
    (comp earlier later).mapCommandHistory state =
      later.mapCommandHistory (earlier.mapCommandHistory state) := by
  rcases state with ⟨command, history⟩
  change
    Sigma.mk (later.mapCommand (earlier.mapCommand command))
        (((comp earlier later).atCommand command).mapHistory history) =
      (Sigma.mk (later.mapCommand (earlier.mapCommand command))
          ((later.atCommand (earlier.mapCommand command)).mapHistory
            ((earlier.atCommand command).mapHistory history)) :
        Sigma fun command => List (target.profile.World command))
  rw [atCommand_comp_mapHistory]

/-- Forward transport preserves the number and order positions of worlds even
when the evidence action identifies their contents. -/
@[simp] theorem mapCommandHistory_length
    (route : TypedEvidenceRoute source target)
    (command : source.profile.Command)
    (history : List (source.profile.World command)) :
    ((route.atCommand command).mapHistory history).length = history.length :=
  EvidenceWorldMap.mapHistory_length _ _

/-! ## Optional reflection capabilities -/

/-- The command projection is reflected by the route. -/
def ReflectsCommands (route : TypedEvidenceRoute source target) : Prop :=
  Function.Injective route.mapCommand

/-- Every fixed-command complete-world fibre is reflected. -/
def ReflectsWorlds (route : TypedEvidenceRoute source target) : Prop :=
  forall command, (route.atCommand command).ReflectsWorlds

theorem id_reflectsCommands
    (profile : EvidenceProfileOver sourcePresentation) :
    (id profile).ReflectsCommands := by
  intro first second equal
  exact equal

theorem id_reflectsWorlds
    (profile : EvidenceProfileOver sourcePresentation) :
    (id profile).ReflectsWorlds := by
  intro command first second equal
  have firstFixed := atCommand_id_mapWorld profile command first
  have secondFixed := atCommand_id_mapWorld profile command second
  exact firstFixed.symm.trans (equal.trans secondFixed)

theorem comp_reflectsCommands
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (earlierReflects : earlier.ReflectsCommands)
    (laterReflects : later.ReflectsCommands) :
    (comp earlier later).ReflectsCommands := by
  intro first second equal
  exact earlierReflects (laterReflects equal)

theorem comp_reflectsWorlds
    (earlier : TypedEvidenceRoute source middle)
    (later : TypedEvidenceRoute middle target)
    (earlierReflects : earlier.ReflectsWorlds)
    (laterReflects : later.ReflectsWorlds) :
    (comp earlier later).ReflectsWorlds := by
  intro command first second equal
  apply earlierReflects command
  apply laterReflects (earlier.mapCommand command)
  have firstMapped := atCommand_comp_mapWorld earlier later command first
  have secondMapped := atCommand_comp_mapWorld earlier later command second
  exact firstMapped.symm.trans (equal.trans secondMapped)

/-- Command reflection and fibrewise world reflection jointly reflect the
complete dependent command/world state. -/
theorem mapCommandWorld_injective
    (route : TypedEvidenceRoute source target)
    (reflectsCommands : route.ReflectsCommands)
    (reflectsWorlds : route.ReflectsWorlds) :
    Function.Injective route.mapCommandWorld := by
  rintro ⟨firstCommand, firstWorld⟩ ⟨secondCommand, secondWorld⟩ equal
  have commandEqual : firstCommand = secondCommand :=
    reflectsCommands (congrArg Sigma.fst equal)
  subst secondCommand
  have worldEqual :
      (route.atCommand firstCommand).mapWorld firstWorld =
        (route.atCommand firstCommand).mapWorld secondWorld := by
    exact eq_of_heq (Sigma.mk.inj equal).2
  have sourceWorldsEqual := reflectsWorlds firstCommand worldEqual
  cases sourceWorldsEqual
  rfl

/-- The same two reflection capabilities lift to ordered command histories. -/
theorem mapCommandHistory_injective
    (route : TypedEvidenceRoute source target)
    (reflectsCommands : route.ReflectsCommands)
    (reflectsWorlds : route.ReflectsWorlds) :
    Function.Injective route.mapCommandHistory := by
  rintro ⟨firstCommand, firstHistory⟩ ⟨secondCommand, secondHistory⟩ equal
  have commandEqual : firstCommand = secondCommand :=
    reflectsCommands (congrArg Sigma.fst equal)
  subst secondCommand
  have historyEqual :
      (route.atCommand firstCommand).mapHistory firstHistory =
        (route.atCommand firstCommand).mapHistory secondHistory := by
    exact eq_of_heq (Sigma.mk.inj equal).2
  have sourceHistoriesEqual :=
    EvidenceWorldMap.mapHistory_injective (route.atCommand firstCommand)
      (reflectsWorlds firstCommand) historyEqual
  cases sourceHistoriesEqual
  rfl

#print axioms mappedWorld_elaborates_structural_surface
#print axioms atCommand_comp_mapWorld
#print axioms mapCommandHistory_comp
#print axioms comp_reflectsWorlds
#print axioms mapCommandWorld_injective
#print axioms mapCommandHistory_injective

end TypedEvidenceRoute

end Mettapedia.GSLT.LanguageDef.GSLTIL.TypedEvidenceRoutes
