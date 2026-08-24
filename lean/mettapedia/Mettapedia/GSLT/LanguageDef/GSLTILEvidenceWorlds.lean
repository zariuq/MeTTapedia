import Mettapedia.GSLT.LanguageDef.GSLTILElaborationSelection
import Mettapedia.GSLT.LanguageDef.GSLTILOccurrenceCells

/-!
# Proof-relevant elaboration worlds for GSLT-IL

An authored command can be ambiguous in two independent ways:

* several internal commands may elaborate from the same surface command; or
* several derivation histories may justify the same internal command.

The proposition-valued elaboration profile records the first distinction.
This module retains both by making elaboration evidence Type-valued.  Outcome
determinacy only identifies internal commands; history thinness additionally
identifies their derivations.  Exact direct representation is earned exactly
when every command is covered, its outcome is determinate, and its history is
thin.  Thus a unique visible result does not by itself license erasing proof
history.
-/

namespace Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds

open Mettapedia.GSLT.LooseRelationEquipment
open Mettapedia.GSLT.LanguageDef.GSLTIL
open Mettapedia.GSLT.LanguageDef.GSLTIL.Syntax
open Mettapedia.GSLT.LanguageDef.GSLTIL.OccurrenceCells
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Evidence-valued profiles -/

/-- A family of authored commands whose accepted elaborations retain their
derivation histories as data. -/
structure Profile (program : Program) where
  Command : Type
  surface : Command -> Pattern
  Evidence : Command -> Pattern -> Type
  sound : forall {command internal}, Evidence command internal ->
    Elaborates program (surface command) internal

namespace Profile

/-- The evidence-valued elaboration relation. -/
abbrev related {program : Program} (profile : Profile program) :
    Loose profile.Command Pattern :=
  profile.Evidence

/-- One elaboration world contains both its internal command and the exact
history that produced it. -/
abbrev World {program : Program} (profile : Profile program)
    (command : profile.Command) : Type :=
  Sigma fun internal => profile.Evidence command internal

/-- Every profiled command has at least one evidence-bearing world. -/
def Covered {program : Program} (profile : Profile program) : Prop :=
  forall command, Nonempty (profile.World command)

/-- All worlds for one command have the same visible internal outcome.
Their histories may nevertheless remain distinct. -/
def OutcomeDeterminate {program : Program} (profile : Profile program) : Prop :=
  forall command (first second : profile.World command),
    first.1 = second.1

/-- Every fixed command/outcome fibre has at most one retained history. -/
def HistoryThin {program : Program} (profile : Profile program) : Prop :=
  forall command internal, Subsingleton (profile.Evidence command internal)

/-- Every complete outcome/history world fibre is a subsingleton. -/
def ProofDeterminate {program : Program} (profile : Profile program) : Prop :=
  forall command, Subsingleton (profile.World command)

/-- Proof-relevant determinacy factors exactly into visible outcome
determinacy and thinness of each fixed-outcome history fibre. -/
theorem proofDeterminate_iff_outcomeDeterminate_and_historyThin
    {program : Program} (profile : Profile program) :
    profile.ProofDeterminate <->
      profile.OutcomeDeterminate ∧ profile.HistoryThin := by
  constructor
  · intro determinate
    constructor
    · intro command first second
      exact congrArg Sigma.fst ((determinate command).allEq first second)
    · intro command internal
      constructor
      intro first second
      have same :
          (Sigma.mk internal first : profile.World command) =
            Sigma.mk internal second :=
        (determinate command).allEq _ _
      cases same
      rfl
  · rintro ⟨outcomeDeterminate, historyThin⟩ command
    constructor
    rintro ⟨firstInternal, firstHistory⟩
      ⟨secondInternal, secondHistory⟩
    have sameInternal : firstInternal = secondInternal :=
      outcomeDeterminate command
        ⟨firstInternal, firstHistory⟩ ⟨secondInternal, secondHistory⟩
    cases sameInternal
    have sameHistory : firstHistory = secondHistory :=
      (historyThin command firstInternal).allEq _ _
    cases sameHistory
    rfl

/-- Exact companion representation is earned precisely when the language
covers every command, chooses one visible outcome, and carries no unresolved
proof-history multiplicity at that outcome. -/
theorem representable_iff_covered_outcomeDeterminate_historyThin
    {program : Program} (profile : Profile program) :
    Nonempty (Representation profile.related) <->
      profile.Covered ∧ profile.OutcomeDeterminate ∧ profile.HistoryThin := by
  rw [Representation.nonempty_iff_total_and_deterministic]
  change (profile.Covered ∧ profile.ProofDeterminate) <-> _
  rw [profile.proofDeterminate_iff_outcomeDeterminate_and_historyThin]

/-- A represented profile contracts every complete evidence-bearing world
fibre. -/
theorem represented_world_contractible
    {program : Program} {profile : Profile program}
    (representation : Representation profile.related) (command : profile.Command) :
    Nonempty (profile.World command) ∧ Subsingleton (profile.World command) :=
  ⟨representation.total command, representation.deterministic command⟩

/-- Unresolved proof-history multiplicity prevents exact direct
representation even when the visible outcome happens to be unique. -/
theorem historyMultiplicity_prevents_representation
    {program : Program} {profile : Profile program}
    (notThin : ¬ profile.HistoryThin) :
    ¬ Nonempty (Representation profile.related) := by
  intro represented
  have complete :=
    (profile.representable_iff_covered_outcomeDeterminate_historyThin).mp
      represented
  exact notThin complete.2.2

end Profile

/-! ## Conservative embedding of proposition-valued profiles -/

namespace PropositionalBridge

open Mettapedia.GSLT.LanguageDef.GSLTIL.ElaborationSelection

/-- An existing proposition-valued profile becomes an evidence profile by
retaining its lifted acceptance proof.  This adds no proof-history
multiplicity because lifted propositions are subsingletons. -/
def ofPropositional {program : Program}
    (profile : ElaborationSelection.Profile program) : Profile program where
  Command := profile.Command
  surface := profile.surface
  Evidence := profile.related
  sound := by
    intro command internal evidence
    exact profile.sound evidence.down.down

theorem covered_iff {program : Program}
    (profile : ElaborationSelection.Profile program) :
    (ofPropositional profile).Covered <-> profile.Covered := by
  constructor
  · intro covered command
    obtain ⟨internal, evidence⟩ := covered command
    exact ⟨internal, evidence.down.down⟩
  · intro covered command
    obtain ⟨internal, accepted⟩ := covered command
    exact ⟨internal, ⟨⟨accepted⟩⟩⟩

theorem outcomeDeterminate_iff {program : Program}
    (profile : ElaborationSelection.Profile program) :
    (ofPropositional profile).OutcomeDeterminate <-> profile.Determinate := by
  constructor
  · intro determinate command first second firstAccepted secondAccepted
    exact determinate command
      ⟨first, ⟨⟨firstAccepted⟩⟩⟩ ⟨second, ⟨⟨secondAccepted⟩⟩⟩
  · intro determinate command first second
    exact determinate command first.2.down.down second.2.down.down

/-- Proposition-valued acceptance carries no distinct derivation histories
at a fixed internal command. -/
theorem historyThin {program : Program}
    (profile : ElaborationSelection.Profile program) :
    (ofPropositional profile).HistoryThin := by
  intro command internal
  exact profile.relatedSubsingleton command internal

/-- The richer evidence-world criterion is conservative: on an existing
proposition-valued profile, exact companion representation is precisely the
old exact-selection capability. -/
theorem representable_iff_exactSelection {program : Program}
    (profile : ElaborationSelection.Profile program) :
    Nonempty (Representation (ofPropositional profile).related) <->
      Nonempty (ExactSelection profile) := by
  simpa [ofPropositional] using
    (ExactSelection.nonempty_iff_representable profile).symm

/-- Expanding the evidence-world criterion on a proposition-valued profile
recovers exactly coverage plus the existing outcome determinacy law. -/
theorem criterion_reduces {program : Program}
    (profile : ElaborationSelection.Profile program) :
    Nonempty (Representation (ofPropositional profile).related) <->
      profile.Covered ∧ profile.Determinate := by
  rw [representable_iff_exactSelection]
  exact ExactSelection.nonempty_iff_covered_and_determinate profile

end PropositionalBridge

/-! ## Authored occurrence histories -/

/-- An occurrence-preserving compilation cell is a genuine elaboration
history at its source boundary.  The internal index is fixed while the cell
retains which authored occurrence produced the step. -/
inductive OccurrenceHistory {program : Program}
    (source target : Boundary) : Pattern -> Type
  | ofCell (cell : OccurrenceWireCell program source target) :
      OccurrenceHistory source target source.2

/-- The evidence profile generated by all occurrence-preserving cells between
one pair of double boundaries. -/
def occurrenceProfile (program : Program) (source target : Boundary) :
    Profile program where
  Command := Unit
  surface := fun _ => source.1
  Evidence := fun _ internal => OccurrenceHistory source target internal
  sound := by
    intro command internal history
    cases history with
    | ofCell cell => exact cell.sourceElaboration

theorem occurrenceProfile_covered {program : Program}
    {source target : Boundary}
    (cell : OccurrenceWireCell program source target) :
    (occurrenceProfile program source target).Covered := by
  intro command
  exact ⟨source.2, OccurrenceHistory.ofCell cell⟩

theorem occurrenceProfile_outcomeDeterminate {program : Program}
    {source target : Boundary} :
    (occurrenceProfile program source target).OutcomeDeterminate := by
  intro command first second
  rcases first with ⟨firstInternal, firstHistory⟩
  rcases second with ⟨secondInternal, secondHistory⟩
  cases firstHistory
  cases secondHistory
  rfl

/-- Distinct authored cells are distinct histories even when a later wire
quotient identifies their operational step. -/
theorem occurrenceProfile_not_historyThin_of_distinct
    {program : Program} {source target : Boundary}
    (first second : OccurrenceWireCell program source target)
    (distinct : first ≠ second) :
    ¬ (occurrenceProfile program source target).HistoryThin := by
  intro thin
  have same :
      OccurrenceHistory.ofCell first = OccurrenceHistory.ofCell second :=
    (thin () source.2).allEq _ _
  exact distinct (OccurrenceHistory.ofCell.inj same)

theorem distinct_occurrence_histories_not_representable
    {program : Program} {source target : Boundary}
    (first second : OccurrenceWireCell program source target)
    (distinct : first ≠ second) :
    ¬ Nonempty
      (Representation (occurrenceProfile program source target).related) :=
  (occurrenceProfile program source target).historyMultiplicity_prevents_representation
    (occurrenceProfile_not_historyThin_of_distinct first second distinct)

/-- The existing GSLT-IL occurrence canary supplies a real authored profile
with one visible internal outcome and two histories.  Wire-step equality does
not make that richer profile representable. -/
theorem exists_authored_occurrence_history_nonrepresentable :
    ∃ (program : Program) (source target : Boundary)
      (first second : OccurrenceWireCell program source target),
      first ≠ second ∧
        first.toRetainedWireStep = second.toRetainedWireStep ∧
        (occurrenceProfile program source target).Covered ∧
        (occurrenceProfile program source target).OutcomeDeterminate ∧
        ¬ Nonempty
          (Representation (occurrenceProfile program source target).related) := by
  obtain ⟨program, source, target, first, second, distinct, sameWire⟩ :=
    OccurrenceCells.DuplicateOccurrenceCanary.exists_distinct_cells_with_equal_wire_steps
  exact ⟨program, source, target, first, second, distinct, sameWire,
    occurrenceProfile_covered first,
    occurrenceProfile_outcomeDeterminate,
    distinct_occurrence_histories_not_representable first second distinct⟩

/-! ## Concrete separating controls -/

namespace Canary

private def atom (name : String) : Pattern := .apply name []
private def sourceSpace : Pattern := atom "source"
private def targetSpace : Pattern := atom "target"
private def state : Pattern := atom "state"

private def route : RouteDecl where
  occurrence := atom "route-occurrence"
  name := "route"
  sourceSpace := sourceSpace
  targetSpace := targetSpace

private def program : Program where
  spaceRules := []
  routes := [route]
  routeRules := []

private def surface : Pattern := routeCall route.name state
private def internal : Pattern :=
  viaPattern forwardKind (routeIdentity route)
    route.sourceSpace route.targetSpace state

private theorem elaborates : Elaborates program surface internal := by
  simpa [program, surface, internal, route] using
    (Elaborates.route (program := program) (route := route)
      (by simp [program]) state)

/-- Two independently retained histories can justify the same internal
command. -/
inductive DuplicateHistory : Pattern -> Type
  | first : DuplicateHistory internal
  | second : DuplicateHistory internal

def duplicateHistoryProfile : Profile program where
  Command := Unit
  surface := fun _ => surface
  Evidence := fun _ result => DuplicateHistory result
  sound := by
    intro command result evidence
    cases evidence <;> exact elaborates

theorem duplicateHistory_covered : duplicateHistoryProfile.Covered := by
  intro command
  exact ⟨internal, DuplicateHistory.first⟩

theorem duplicateHistory_outcomeDeterminate :
    duplicateHistoryProfile.OutcomeDeterminate := by
  intro command first second
  rcases first with ⟨firstInternal, firstHistory⟩
  rcases second with ⟨secondInternal, secondHistory⟩
  cases firstHistory <;> cases secondHistory <;> rfl

theorem duplicateHistory_not_historyThin :
    ¬ duplicateHistoryProfile.HistoryThin := by
  intro thin
  have same : DuplicateHistory.first = DuplicateHistory.second :=
    (thin () internal).allEq _ _
  cases same

/-- A unique visible elaboration with two proof histories is not a companion
and therefore cannot silently be compiled as an exact direct elaborator. -/
theorem duplicateHistory_not_representable :
    ¬ Nonempty (Representation duplicateHistoryProfile.related) :=
  duplicateHistoryProfile.historyMultiplicity_prevents_representation
    duplicateHistory_not_historyThin

/-- The same authored command with one retained history is an exact profile. -/
inductive UniqueHistory : Pattern -> Type
  | only : UniqueHistory internal

def uniqueHistoryProfile : Profile program where
  Command := Unit
  surface := fun _ => surface
  Evidence := fun _ result => UniqueHistory result
  sound := by
    intro command result evidence
    cases evidence
    exact elaborates

theorem uniqueHistory_covered : uniqueHistoryProfile.Covered := by
  intro command
  exact ⟨internal, UniqueHistory.only⟩

theorem uniqueHistory_outcomeDeterminate :
    uniqueHistoryProfile.OutcomeDeterminate := by
  intro command first second
  rcases first with ⟨firstInternal, firstHistory⟩
  rcases second with ⟨secondInternal, secondHistory⟩
  cases firstHistory
  cases secondHistory
  rfl

theorem uniqueHistory_historyThin : uniqueHistoryProfile.HistoryThin := by
  intro command result
  constructor
  intro first second
  cases first
  cases second
  rfl

theorem uniqueHistory_representable :
    Nonempty (Representation uniqueHistoryProfile.related) :=
  (uniqueHistoryProfile.representable_iff_covered_outcomeDeterminate_historyThin).2
    ⟨uniqueHistory_covered, uniqueHistory_outcomeDeterminate,
      uniqueHistory_historyThin⟩

/-- Direct execution selected by the exact representation is the unique
internal command. -/
theorem uniqueHistory_selected_internal
    (representation : Representation uniqueHistoryProfile.related) :
    representation.map () = internal := by
  let witness : uniqueHistoryProfile.related () internal := UniqueHistory.only
  exact (representation.exact () internal witness).down.down

end Canary

#print axioms Profile.proofDeterminate_iff_outcomeDeterminate_and_historyThin
#print axioms Profile.representable_iff_covered_outcomeDeterminate_historyThin
#print axioms Profile.represented_world_contractible
#print axioms Profile.historyMultiplicity_prevents_representation
#print axioms PropositionalBridge.representable_iff_exactSelection
#print axioms PropositionalBridge.criterion_reduces
#print axioms distinct_occurrence_histories_not_representable
#print axioms exists_authored_occurrence_history_nonrepresentable
#print axioms Canary.duplicateHistory_not_representable
#print axioms Canary.uniqueHistory_representable
#print axioms Canary.uniqueHistory_selected_internal

end Mettapedia.GSLT.LanguageDef.GSLTIL.EvidenceWorlds
