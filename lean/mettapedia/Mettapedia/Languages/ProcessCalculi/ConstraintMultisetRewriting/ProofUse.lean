import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ConditionalSchedule
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Provenance
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroComposition

/-!
# Logical hypothesis use inferred from actual occurrence selections

Each fresh protected output inherits the initial dependencies of its selected
protected premises. Surviving occurrences retain their dependencies. The
calculation uses occurrence identities, so a closed conclusion does not erase
a used assumption. The source schedule and its compiled conditions still
retain premise positions, resource multiplicities and every original guard.

The cut theorem retains the compiled condition and the final equations.
It does not generalize beyond permitted solutions or certify an unchecked
installation. These dependency sets express logical assumption use; they do
not replace the occurrence engine's resource accounting.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.TierZeroKernel (Derivable)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (protectedOccurrence : O → Prop) [DecidablePred protectedOccurrence]

abbrev Origins (O : Type uO) := O → Finset O

def initialOrigins : Origins O := fun occurrence => {occurrence}

def gathered (origins : Origins O) (selection : Selection O) : Finset O :=
  (Provenance.premises selection protectedOccurrence).biUnion origins

def advance (origins : Origins O) (selection : Selection O) : Origins O :=
  fun occurrence => if occurrence ∈ selection.made then gathered protectedOccurrence origins selection else origins occurrence

def followOrigins (origins : Origins O) : List (ConditionalSchedule.Firing T O) → Origins O
  | [] => origins
  | firing :: rest => followOrigins (advance protectedOccurrence origins firing.2) rest

def Hypotheses (A : SubstitutionAction T S) (assignment : S) (label : O → T) (sources : Finset O) : T → Prop :=
  fun judgment => ∃ source ∈ sources, judgment = A.apply assignment (label source)

def Correct (A : SubstitutionAction T S) (label : O → T) (installed : List (RuleInstance T))
    (state : Configuration T O) (origins : Origins O) : Prop :=
  ∀ assignment, A.Models assignment state.equations → ∀ occurrence ∈ state.present, protectedOccurrence occurrence →
    Derivable (Hypotheses A assignment label (origins occurrence))
      (Provenance.Infers A label protectedOccurrence installed) (A.apply assignment (label occurrence))

def Bounded (initialSources : Finset O) (state : Configuration T O) (origins : Origins O) : Prop :=
  ∀ occurrence ∈ state.present, protectedOccurrence occurrence → origins occurrence ⊆ initialSources

omit [DecidableEq O] in
theorem initial_bounded (state : Configuration T O) :
    Bounded protectedOccurrence (state.present.filter protectedOccurrence) state initialOrigins := by
  intro occurrence present isProtected source member
  have same : source = occurrence := Finset.mem_singleton.mp member
  subst source
  exact Finset.mem_filter.mpr ⟨present, isProtected⟩

theorem initial_correct (A : SubstitutionAction T S) (label : O → T)
    (installed : List (RuleInstance T)) (state : Configuration T O) :
    Correct protectedOccurrence A label installed state initialOrigins := by
  intro assignment _ occurrence _ _
  exact Derivable.initial ⟨occurrence, by simp [initialOrigins], rfl⟩

theorem weaken_hypotheses (A : SubstitutionAction T S) (assignment : S) (label : O → T)
    (installed : List (RuleInstance T)) {smaller larger : Finset O} (included : smaller ⊆ larger)
    {conclusion : T}
    (proof : Derivable (Hypotheses A assignment label smaller)
      (Provenance.Infers A label protectedOccurrence installed) conclusion) :
    Derivable (Hypotheses A assignment label larger)
      (Provenance.Infers A label protectedOccurrence installed) conclusion := by
  apply proof.cut
  intro judgment hypothesis
  obtain ⟨source, member, same⟩ := hypothesis
  exact Derivable.initial ⟨source, included member, same⟩

theorem valid_preserves (A : SubstitutionAction T S) (label : O → T) (installed : List (RuleInstance T))
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O} {origins : Origins O}
    (valid : selection.Valid A label rule before)
    (admitted : rule ∈ installed ∨ ∀ occurrence ∈ selection.made, ¬ protectedOccurrence occurrence)
    (prior : Correct protectedOccurrence A label installed before origins) :
    Correct protectedOccurrence A label installed (selection.result label rule before)
      (advance protectedOccurrence origins selection) := by
  intro assignment solved occurrence present isProtected
  have oldModels := valid.refines assignment solved
  rcases mem_fire.mp present with survived | produced
  · have notMade : occurrence ∉ selection.made := by
      intro made
      exact Finset.disjoint_left.mp valid.occurrences.fresh
        (by simpa [Selection.commit] using made) survived.1
    simpa only [advance, if_neg notMade] using prior assignment oldModels occurrence survived.1 isProtected
  · have made : occurrence ∈ selection.made := by simpa [Selection.commit] using produced
    rcases admitted with installedRule | noPublish
    · have derived : Derivable (Hypotheses A assignment label (gathered protectedOccurrence origins selection))
          (Provenance.Infers A label protectedOccurrence installed) (A.apply assignment (label occurrence)) := by
        apply Derivable.infer (premises := labels (fun source => A.apply assignment (label source))
          (Provenance.premises selection protectedOccurrence))
        · exact ⟨rule, installedRule, before, selection, assignment, valid, solved, rfl,
            occurrence, made, isProtected, rfl⟩
        · intro judgment member
          obtain ⟨source, selectedMember, rfl⟩ := Multiset.mem_map.mp member
          have selected : source ∈ Provenance.premises selection protectedOccurrence := by simpa using selectedMember
          obtain ⟨picked, protectedSource⟩ := Finset.mem_filter.mp selected
          have sourcePresent : source ∈ before.present := by
            rcases Finset.mem_union.mp picked with taken | read
            · exact valid.occurrences.taken_subset taken
            · exact valid.occurrences.kept_subset read
          exact weaken_hypotheses protectedOccurrence A assignment label installed
            (Finset.subset_biUnion_of_mem origins selected) (prior assignment oldModels source sourcePresent protectedSource)
      simpa only [advance, if_pos made] using derived
    · exact False.elim (noPublish occurrence made isProtected)

theorem valid_preserves_bounds (A : SubstitutionAction T S) (label : O → T)
    {rule : RuleInstance T} {selection : Selection O} {before : Configuration T O}
    {origins : Origins O} {initialSources : Finset O}
    (valid : selection.Valid A label rule before)
    (prior : Bounded protectedOccurrence initialSources before origins) :
    Bounded protectedOccurrence initialSources (selection.result label rule before)
      (advance protectedOccurrence origins selection) := by
  intro occurrence present isProtected source member
  by_cases made : occurrence ∈ selection.made
  · change source ∈ (if occurrence ∈ selection.made then _ else _) at member
    rw [if_pos made] at member
    obtain ⟨premise, selected, used⟩ := Finset.mem_biUnion.mp member
    obtain ⟨picked, protectedPremise⟩ := Finset.mem_filter.mp selected
    have premisePresent : premise ∈ before.present := by
      rcases Finset.mem_union.mp picked with taken | read
      · exact valid.occurrences.taken_subset taken
      · exact valid.occurrences.kept_subset read
    exact prior premise premisePresent protectedPremise used
  · have oldPresent : occurrence ∈ before.present := by
      rcases mem_fire.mp present with survived | produced
      · exact survived.1
      · exact False.elim (made (by simpa [Selection.commit] using produced))
    exact prior occurrence oldPresent isProtected (by simpa only [advance, if_neg made] using member)

def Admitted (installed : List (RuleInstance T)) (schedule : List (ConditionalSchedule.Firing T O)) : Prop :=
  ∀ firing ∈ schedule, firing.1 ∈ installed ∨ ∀ occurrence ∈ firing.2.made, ¬ protectedOccurrence occurrence

theorem executable_preserves (A : SubstitutionAction T S) (label : O → T) (installed : List (RuleInstance T)) :
    ∀ (before : Configuration T O) (origins : Origins O) (schedule : List (ConditionalSchedule.Firing T O)),
    ConditionalSchedule.Executable A label before schedule → Admitted protectedOccurrence installed schedule →
    Correct protectedOccurrence A label installed before origins →
      Correct protectedOccurrence A label installed (ConditionalSchedule.follow label before schedule)
        (followOrigins protectedOccurrence origins schedule)
  | _, _, [], _, _, prior => prior
  | before, origins, firing :: rest, executable, admitted, prior => by
      exact executable_preserves A label installed _ _ rest executable.2
        (fun next member => admitted next (List.mem_cons_of_mem _ member))
        (valid_preserves protectedOccurrence A label installed executable.1
          (admitted firing List.mem_cons_self) prior)

theorem executable_preserves_bounds (A : SubstitutionAction T S) (label : O → T)
    (initialSources : Finset O) :
    ∀ (before : Configuration T O) (origins : Origins O) (schedule : List (ConditionalSchedule.Firing T O)),
    ConditionalSchedule.Executable A label before schedule → Bounded protectedOccurrence initialSources before origins →
      Bounded protectedOccurrence initialSources (ConditionalSchedule.follow label before schedule)
        (followOrigins protectedOccurrence origins schedule)
  | _, _, [], _, prior => prior
  | _, _, _ :: rest, executable, prior =>
      executable_preserves_bounds A label initialSources _ _ rest executable.2
        (valid_preserves_bounds protectedOccurrence A label executable.1 prior)

theorem inferred_sources_are_initial_protected_occurrences
    (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O)
    (schedule : List (ConditionalSchedule.Firing T O))
    (executable : ConditionalSchedule.Executable A label before schedule)
    (occurrence : O) (present : occurrence ∈ (ConditionalSchedule.follow label before schedule).present)
    (isProtected : protectedOccurrence occurrence) :
    ∀ source ∈ followOrigins protectedOccurrence initialOrigins schedule occurrence,
      source ∈ before.present ∧ protectedOccurrence source := by
  have bound := executable_preserves_bounds protectedOccurrence A label (before.present.filter protectedOccurrence)
    before initialOrigins schedule executable (initial_bounded protectedOccurrence before)
  exact fun source member => Finset.mem_filter.mp (bound occurrence present isProtected member)

/-- Supplying derivations of the dependencies actually propagated by the
ordinary selections proves the conclusion. The retained compiled condition
and final equation model are part of this interface, even for closed outputs. -/
theorem compiled_cut (A : SubstitutionAction T S) (label : O → T) (installed : List (RuleInstance T))
    (before : Configuration T O) (schedule : List (ConditionalSchedule.Firing T O))
    (enabled : (ConditionalSchedule.compile label schedule).Holds A label before)
    (admitted : Admitted protectedOccurrence installed schedule)
    (assignment : S) (solved : A.Models assignment (ConditionalSchedule.follow label before schedule).equations)
    (occurrence : O) (present : occurrence ∈ (ConditionalSchedule.follow label before schedule).present)
    (isProtected : protectedOccurrence occurrence) (replacement : T → Prop)
    (supply : ∀ source ∈ followOrigins protectedOccurrence initialOrigins schedule occurrence,
      Derivable replacement (Provenance.Infers A label protectedOccurrence installed)
        (A.apply assignment (label source))) :
    Derivable replacement (Provenance.Infers A label protectedOccurrence installed)
      (A.apply assignment (label occurrence)) := by
  have executable := (ConditionalSchedule.compile_holds_iff A label before schedule).mp enabled
  have tracked := executable_preserves protectedOccurrence A label installed before initialOrigins schedule
    executable admitted (initial_correct protectedOccurrence A label installed before)
  apply (tracked assignment solved occurrence present isProtected).cut
  intro judgment hypothesis
  obtain ⟨source, member, same⟩ := hypothesis
  rw [same]
  exact supply source member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProofUse
