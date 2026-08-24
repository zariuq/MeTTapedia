import Mettapedia.GSLT.Core.LooseRelationCompanions
import Mettapedia.GSLT.LanguageDef.GSLTILCoherentCompilation

/-!
# Typed selection policies for relational GSLT-IL elaboration

Raw GSLT-IL elaboration is a relation.  A consumer may nevertheless provide
a typed profile that refines the raw relation and a policy selecting one
accepted internal command for every profile command.  Selection alone does
not claim that the raw relation is functional: it only embeds the selected
companion into the accepted relation.

An *exact* selection has the additional uniqueness law that every accepted
internal command is the selected command.  Exactly then the accepted relation
is represented by a companion, so direct elaboration, companion/conjoint
cells, and their binding equations are earned rather than postulated.

The ambiguous-route control has two distinct sound selections for the same
surface command and no exact selection of the raw profile.  An explicitly
occurrence-indexed profile is exact.  Thus a deterministic implementation is
a declared refinement capability, not the global semantics of authored
commands.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.FreePath
open Mettapedia.GSLT.LanguageDef.GSLTIL.WireCells
open Mettapedia.GSLT.LanguageDef.GSLTIL.CoherentCompilation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Typed elaboration profiles -/

/-- A typed family of authored commands together with the elaborations that
the profile accepts.  Accepted elaborations must remain valid in the ambient
authored program. -/
structure Profile (program : Program) where
  Command : Type
  surface : Command → Pattern
  Accepts : Command → Pattern → Prop
  sound : ∀ {command internal}, Accepts command internal →
    Elaborates program (surface command) internal

namespace Profile

/-- The accepted elaborations as a loose proof-relevant arrow. -/
def related {program : Program} (profile : Profile program) :
    Loose profile.Command Pattern :=
  fun command internal => ULift (PLift (profile.Accepts command internal))

instance relatedSubsingleton {program : Program} (profile : Profile program)
    (command : profile.Command) (internal : Pattern) :
    Subsingleton (profile.related command internal) where
  allEq first second := by
    rcases first with ⟨⟨firstProof⟩⟩
    rcases second with ⟨⟨secondProof⟩⟩
    rfl

/-- Every typed command has at least one accepted elaboration. -/
def Covered {program : Program} (profile : Profile program) : Prop :=
  ∀ command, ∃ internal, profile.Accepts command internal

/-- The accepted internal command is unique for every typed command. -/
def Determinate {program : Program} (profile : Profile program) : Prop :=
  ∀ command {first second},
    profile.Accepts command first → profile.Accepts command second →
      first = second

/-- The unrefined profile of all surface patterns and all valid authored
elaborations. -/
def raw (program : Program) : Profile program where
  Command := Pattern
  surface := _root_.id
  Accepts := Elaborates program
  sound := _root_.id

/-! ## Elaboration worlds -/

/-- One possible internal world of an authored command, together with the
evidence that the declared profile accepts it.  Distinct internal patterns
remain distinct worlds; no selection policy is built into this carrier. -/
def World {program : Program} (profile : Profile program)
    (command : profile.Command) : Type :=
  { internal : Pattern // profile.Accepts command internal }

/-- Coverage says exactly that every command has at least one world. -/
theorem covered_iff_world_nonempty {program : Program}
    (profile : Profile program) :
    profile.Covered ↔
      ∀ command, Nonempty (profile.World command) := by
  constructor
  · intro covered command
    obtain ⟨internal, accepted⟩ := covered command
    exact ⟨⟨internal, accepted⟩⟩
  · intro inhabited command
    obtain ⟨⟨internal, accepted⟩⟩ := inhabited command
    exact ⟨internal, accepted⟩

/-- Determinacy says exactly that every command's world fibre is a
subsingleton.  This does not assert coverage. -/
theorem determinate_iff_world_subsingleton {program : Program}
    (profile : Profile program) :
    profile.Determinate ↔
      ∀ command, Subsingleton (profile.World command) := by
  constructor
  · intro determinate command
    exact
      { allEq := fun first second =>
          Subtype.ext (determinate command first.property second.property) }
  · intro subsingleton command first second firstAccepted secondAccepted
    have same :
        (⟨first, firstAccepted⟩ : profile.World command) =
          ⟨second, secondAccepted⟩ :=
      (subsingleton command).allEq _ _
    exact congrArg Subtype.val same

end Profile

/-! ## Sound selection does not imply global functionality -/

/-- A policy selecting one accepted elaboration of every typed command. -/
structure SoundSelection {program : Program} (profile : Profile program) where
  select : profile.Command → Pattern
  selected : ∀ command, profile.Accepts command (select command)

namespace SoundSelection

/-- A sound policy chooses one inhabited point of every accepted world
fibre.  It need not contract the other worlds to that point. -/
def selectedWorld {program : Program} {profile : Profile program}
    (selection : SoundSelection profile) (command : profile.Command) :
    profile.World command :=
  ⟨selection.select command, selection.selected command⟩

/-- A sound selection embeds its chosen companion into the ambient accepted
relation.  The opposite cell requires exactness. -/
def chosenCell {program : Program} {profile : Profile program}
    (selection : SoundSelection profile) :
    Cell (_root_.id : profile.Command → profile.Command)
      (_root_.id : Pattern → Pattern)
      (companion selection.select) profile.related where
  map {source target} witness := by
    rcases witness with ⟨⟨same⟩⟩
    cases same
    exact ⟨⟨selection.selected source⟩⟩

/-- A sound selection always remains an ambient authored elaboration. -/
theorem elaborates {program : Program} {profile : Profile program}
    (selection : SoundSelection profile) (command : profile.Command) :
    Elaborates program (profile.surface command) (selection.select command) :=
  profile.sound (selection.selected command)

end SoundSelection

/-! ## Exact selection and companion representation -/

/-- An exact selection chooses an accepted elaboration and proves that every
accepted elaboration is that choice. -/
structure ExactSelection {program : Program} (profile : Profile program)
    extends SoundSelection profile where
  reflects : ∀ command {internal}, profile.Accepts command internal →
    select command = internal

namespace ExactSelection

/-- Strongest true reflection on the declared typed profile: an internal
command is accepted exactly when it is the selected command. -/
theorem accepts_iff_selected_eq {program : Program}
    {profile : Profile program} (selection : ExactSelection profile)
    (command : profile.Command) (internal : Pattern) :
    profile.Accepts command internal ↔ selection.select command = internal := by
  constructor
  · exact selection.reflects command
  · intro same
    cases same
    exact selection.selected command

/-- Exact selection identifies the accepted relation with the companion of
the selected direct elaborator. -/
def toRepresentation {program : Program} {profile : Profile program}
    (selection : ExactSelection profile) : Representation profile.related where
  map := selection.select
  exact command internal :=
    { toFun := fun accepted => ⟨⟨selection.reflects command accepted.down.down⟩⟩
      invFun := fun same => by
        cases same.down.down
        exact ⟨⟨selection.selected command⟩⟩
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ =>
        (instSubsingletonEqWitness _ _).allEq _ _ }

/-- Every exact representation of a typed elaboration profile yields its
unique exact selector. -/
def ofRepresentation {program : Program} {profile : Profile program}
    (representation : Representation profile.related) :
    ExactSelection profile where
  select := representation.map
  selected := fun command =>
    ((representation.exact command (representation.map command)).symm
      ⟨⟨rfl⟩⟩).down.down
  reflects := fun command {_} accepted =>
    (representation.exact command _ ⟨⟨accepted⟩⟩).down.down

/-- Exact selection is equivalent to representability of the accepted
elaboration relation. -/
theorem nonempty_iff_representable
    {program : Program} (profile : Profile program) :
    Nonempty (ExactSelection profile) ↔
      Nonempty (Representation profile.related) := by
  constructor
  · rintro ⟨selection⟩
    exact ⟨selection.toRepresentation⟩
  · rintro ⟨representation⟩
    exact ⟨ofRepresentation representation⟩

/-- Coverage plus proof-relevant determinacy is exactly the criterion for an
exact deterministic elaboration policy on a typed profile. -/
theorem nonempty_iff_covered_and_determinate
    {program : Program} (profile : Profile program) :
    Nonempty (ExactSelection profile) ↔
      profile.Covered ∧ profile.Determinate := by
  constructor
  · rintro ⟨selection⟩
    constructor
    · intro command
      exact ⟨selection.select command, selection.selected command⟩
    · intro command first second firstAccepted secondAccepted
      exact (selection.reflects command firstAccepted).symm.trans
        (selection.reflects command secondAccepted)
  · rintro ⟨covered, determinate⟩
    let select : profile.Command → Pattern := fun command =>
      Classical.choose (covered command)
    have selected : ∀ command, profile.Accepts command (select command) :=
      fun command => Classical.choose_spec (covered command)
    exact ⟨
      { select := select
        selected := selected
        reflects := fun command {internal} accepted =>
          determinate command (selected command) accepted }⟩

/-- Exact deterministic elaboration exists exactly when every accepted
world fibre is inhabited and contractible.  Natural ambiguity is therefore
retained by a non-subsingleton fibre rather than treated as failure. -/
theorem nonempty_iff_world_fibres_contractible
    {program : Program} (profile : Profile program) :
    Nonempty (ExactSelection profile) ↔
      ∀ command,
        Nonempty (profile.World command) ∧
          Subsingleton (profile.World command) := by
  rw [nonempty_iff_covered_and_determinate]
  constructor
  · rintro ⟨covered, determinate⟩ command
    exact ⟨
      (profile.covered_iff_world_nonempty.mp covered) command,
      (profile.determinate_iff_world_subsingleton.mp determinate) command⟩
  · intro contractible
    constructor
    · exact profile.covered_iff_world_nonempty.mpr fun command =>
        (contractible command).1
    · exact profile.determinate_iff_world_subsingleton.mpr fun command =>
        (contractible command).2

/-- Every world in an exact profile is the selected world. -/
theorem world_eq_selected {program : Program}
    {profile : Profile program} (selection : ExactSelection profile)
    (command : profile.Command) (world : profile.World command) :
    world = selection.toSoundSelection.selectedWorld command := by
  apply Subtype.ext
  exact (selection.reflects command world.property).symm

/-- The selected direct elaborator is unique once exactness is proved. -/
theorem select_unique {program : Program} {profile : Profile program}
    (first second : ExactSelection profile) :
    first.select = second.select :=
  Representation.map_unique first.toRepresentation second.toRepresentation

/-- Exact selection supplies both directions of the vertical isomorphism
between accepted elaboration and its selected companion. -/
theorem companion_left_inverse {program : Program}
    {profile : Profile program} (selection : ExactSelection profile) :
    Cell.vcomp selection.toRepresentation.toCompanionCell
        selection.toRepresentation.fromCompanionCell =
      Cell.id profile.related :=
  selection.toRepresentation.fromCompanion_vcomp_toCompanion

theorem companion_right_inverse {program : Program}
    {profile : Profile program} (selection : ExactSelection profile) :
    Cell.vcomp selection.toRepresentation.fromCompanionCell
        selection.toRepresentation.toCompanionCell =
      Cell.id (companion selection.select) :=
  selection.toRepresentation.toCompanion_vcomp_fromCompanion

end ExactSelection

/-! ## Global exact selection and coherent authored paths -/

/-- If the complete raw elaboration relation of one program is exact, every
authored path has coherent canonical internal boundaries.  The premise is
deliberately strong and is refuted by the ambiguity control below. -/
theorem exact_raw_selection_compiles_every_path
    {program : Program}
    (selection : ExactSelection (Profile.raw program)) :
    ∀ {source target} (path : AuthoredPath program source target),
      Certificate.Compilable path
  | _, _, .refl surface =>
      ⟨selection.select surface, selection.selected surface⟩
  | _, _, .cons _ (.refl _) => True.intro
  | _, _, .cons first (.cons second rest) => by
      constructor
      · exact
          (selection.reflects _
            (WireCell.ofEvent first).targetElaboration).symm.trans
          (selection.reflects _
            (WireCell.ofEvent second).sourceElaboration)
      · exact exact_raw_selection_compiles_every_path selection
          (.cons second rest)

/-! ## Positive and negative controls -/

namespace RouteOccurrenceCanary

private def atom (name : String) : Pattern := .apply name []
private def sourceSpace := atom "source-space"
private def targetA := atom "target-a"
private def targetB := atom "target-b"
private def state := atom "state"

private def routeA : RouteDecl :=
  { occurrence := atom "route-a"
    name := "shared"
    sourceSpace := sourceSpace
    targetSpace := targetA }

private def routeB : RouteDecl :=
  { occurrence := atom "route-b"
    name := "shared"
    sourceSpace := sourceSpace
    targetSpace := targetB }

private def program : Program :=
  { spaceRules := []
    routes := [routeA, routeB]
    routeRules := [] }

private def surface : Pattern := routeCall "shared" state

private def internalA : Pattern :=
  viaPattern forwardKind (routeIdentity routeA)
    routeA.sourceSpace routeA.targetSpace state

private def internalB : Pattern :=
  viaPattern forwardKind (routeIdentity routeB)
    routeB.sourceSpace routeB.targetSpace state

private theorem elaboratesA : Elaborates program surface internalA := by
  simpa [surface, internalA, routeA] using
    (Elaborates.route (program := program) (route := routeA)
      (by simp [program]) state)

private theorem elaboratesB : Elaborates program surface internalB := by
  simpa [surface, internalB, routeB] using
    (Elaborates.route (program := program) (route := routeB)
      (by simp [program]) state)

private theorem internals_distinct : internalA ≠ internalB := by
  simp [internalA, internalB, routeIdentity, routeA, routeB, atom,
    viaPattern, Pattern.apply.injEq]

/-- The raw singleton profile retains both declaration occurrences. -/
private def rawProfile : Profile program where
  Command := Unit
  surface := fun _ => surface
  Accepts := fun _ internal => Elaborates program surface internal
  sound := _root_.id

private def worldA : rawProfile.World () := ⟨internalA, elaboratesA⟩

private def worldB : rawProfile.World () := ⟨internalB, elaboratesB⟩

/-- The ambiguous command has two genuinely distinct elaboration worlds.
The relational semantics retains both before any policy selects one. -/
theorem elaboration_worlds_are_distinct : worldA ≠ worldB := by
  intro same
  exact internals_distinct (congrArg Subtype.val same)

/-- A policy may soundly choose the first occurrence. -/
def chooseA : SoundSelection rawProfile where
  select := fun _ => internalA
  selected := fun _ => elaboratesA

/-- A different policy may soundly choose the second occurrence. -/
def chooseB : SoundSelection rawProfile where
  select := fun _ => internalB
  selected := fun _ => elaboratesB

/-- The two sound policies genuinely select different internal commands. -/
theorem sound_selections_are_distinct : chooseA.select ≠ chooseB.select := by
  intro same
  exact internals_distinct (congrFun same ())

/-- Neither sound policy can represent all raw elaborations: the raw profile
is ambiguous and has no exact selection. -/
theorem raw_profile_has_no_exact_selection :
    ¬ Nonempty (ExactSelection rawProfile) := by
  rintro ⟨selection⟩
  have first := selection.reflects () elaboratesA
  have second := selection.reflects () elaboratesB
  exact internals_distinct (first.symm.trans second)

/-- Adding the declaration occurrence to the typed profile makes the intended
fragment exact without changing the authored surface command. -/
private def routeAProfile : Profile program where
  Command := Unit
  surface := fun _ => surface
  Accepts := fun _ internal => internal = internalA
  sound := by
    intro command internal same
    cases same
    exact elaboratesA

def routeAExact : ExactSelection routeAProfile where
  select := fun _ => internalA
  selected := by
    intro command
    rfl
  reflects := fun _ {internal} same => same.symm

/-- The occurrence-indexed profile earns direct companion representation. -/
theorem occurrence_indexed_profile_is_represented :
    Nonempty (Representation routeAProfile.related) :=
  ⟨routeAExact.toRepresentation⟩

/-- The exact profile carries both companion inverse equations. -/
theorem occurrence_indexed_companion_equations :
    Cell.vcomp routeAExact.toRepresentation.toCompanionCell
          routeAExact.toRepresentation.fromCompanionCell =
        Cell.id routeAProfile.related ∧
      Cell.vcomp routeAExact.toRepresentation.fromCompanionCell
          routeAExact.toRepresentation.toCompanionCell =
        Cell.id (companion routeAExact.select) :=
  ⟨routeAExact.companion_left_inverse,
    routeAExact.companion_right_inverse⟩

end RouteOccurrenceCanary

/-- The full authored language admits no global exact selection in general.
Typed exact profiles coexist with this language-level obstruction. -/
theorem exists_program_without_global_exact_selection :
    ∃ program : Program,
      ¬ Nonempty (ExactSelection (Profile.raw program)) := by
  obtain ⟨program, obstruction⟩ :=
    exists_program_without_global_functional_elaboration
  refine ⟨program, ?_⟩
  rintro ⟨selection⟩
  apply obstruction
  refine ⟨selection.select, ?_⟩
  intro surface internal
  constructor
  · exact selection.reflects surface
  · intro same
    cases same
    exact selection.selected surface

#print axioms SoundSelection.chosenCell
#print axioms ExactSelection.accepts_iff_selected_eq
#print axioms ExactSelection.nonempty_iff_representable
#print axioms ExactSelection.nonempty_iff_covered_and_determinate
#print axioms ExactSelection.nonempty_iff_world_fibres_contractible
#print axioms ExactSelection.world_eq_selected
#print axioms ExactSelection.select_unique
#print axioms ExactSelection.companion_left_inverse
#print axioms exact_raw_selection_compiles_every_path
#print axioms RouteOccurrenceCanary.sound_selections_are_distinct
#print axioms RouteOccurrenceCanary.raw_profile_has_no_exact_selection
#print axioms RouteOccurrenceCanary.occurrence_indexed_profile_is_represented
#print axioms RouteOccurrenceCanary.occurrence_indexed_companion_equations
#print axioms RouteOccurrenceCanary.elaboration_worlds_are_distinct
#print axioms exists_program_without_global_exact_selection

end Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection
