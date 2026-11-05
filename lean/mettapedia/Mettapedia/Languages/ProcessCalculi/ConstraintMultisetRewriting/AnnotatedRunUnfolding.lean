import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsRounds

/-!
# Finite candidate unfolding with complete alternatives at every cut

The construction enumerates histories from the existing admission relation.
Its correctness is proved against `AnnotatedRuns.Executable`, independently
of the enumerator. Each child receives its own successor configuration.
The finite catalogue limits the claimed coverage; arbitrary guards are tested
classically, so this is a semantic construction, not an executable guard solver.

Histories deliberately retain scheduling multiplicity. They are not yet
configurations of a prime event structure: read/take precedence, inhibition,
and joint consistency cannot be replaced by pairwise symmetric conflict.
In particular a depth frontier is not a certificate of completed search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)

variable {T S O : Type*} [DecidableEq O]
variable (A : SubstitutionAction T S) (label : O → T)

/-- Exact alternatives within a declared finite catalogue. Equal catalogue
entries retain their multiplicity; use a nodup catalogue for unique sites. -/
noncomputable def enabled (catalogue : List (Firing T S O)) (cut : Configuration T O) :
    List (Firing T S O) := by
  classical
  exact catalogue.filter fun firing => decide (firing.Valid A label cut)

theorem mem_enabled (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (firing : Firing T S O) :
    firing ∈ enabled A label catalogue cut ↔ firing ∈ catalogue ∧ firing.Valid A label cut := by
  classical
  simp [enabled]

/-- Independent depth expansion. The zero level records an empty consistent
history, and a successor level enumerates each enabled first firing. -/
noncomputable def frontier (catalogue : List (Firing T S O)) :
    Nat → Configuration T O → List (List (Firing T S O))
  | 0, cut => by
      classical
      exact if A.Consistent cut.equations then [[]] else []
  | depth + 1, cut => (enabled A label catalogue cut).flatMap fun firing =>
      (frontier catalogue depth (firing.result label cut)).map (firing :: ·)

/-- Soundness and completeness for every history in the declared finite
candidate universe, including guards and exact predicate censuses. -/
theorem mem_frontier (catalogue : List (Firing T S O)) (depth : Nat)
    (cut : Configuration T O) (word : List (Firing T S O)) :
    word ∈ frontier A label catalogue depth cut ↔
      word.length = depth ∧ Executable A label cut word ∧
        ∀ firing ∈ word, firing ∈ catalogue := by
  induction depth generalizing cut word with
  | zero =>
      classical
      cases word with
      | nil => simp [frontier, Executable]
      | cons firing rest => simp [frontier]
  | succ depth ih =>
      cases word with
      | nil => simp [frontier]
      | cons firing rest =>
          simp only [frontier, List.mem_flatMap, List.mem_map]
          constructor
          · rintro ⟨picked, chosen, suffix, member, same⟩
            cases same
            obtain ⟨inCatalogue, valid⟩ := (mem_enabled A label catalogue cut firing).mp chosen
            obtain ⟨length, executable, covered⟩ := (ih _ rest).mp member
            exact ⟨congrArg Nat.succ length, ⟨valid, executable⟩,
              by intro event present; rcases List.mem_cons.mp present with rfl | later
                 · exact inCatalogue
                 · exact covered event later⟩
          · rintro ⟨length, executable, covered⟩
            refine ⟨firing, (mem_enabled A label catalogue cut firing).mpr
              ⟨covered firing (by simp), executable.1⟩, rest, ?_, rfl⟩
            exact (ih _ rest).mpr ⟨Nat.succ.inj length, executable.2,
              fun event present => covered event (List.mem_cons_of_mem _ present)⟩

theorem frontier_sound {catalogue : List (Firing T S O)} {depth : Nat}
    {cut : Configuration T O} {word : List (Firing T S O)}
    (member : word ∈ frontier A label catalogue depth cut) :
    Executable A label cut word := ((mem_frontier A label catalogue depth cut word).mp member).2.1

/-- Semantic no-successor assertion relative to the named catalogue. -/
def Terminal (catalogue : List (Firing T S O)) (cut : Configuration T O) : Prop :=
  ∀ firing ∈ catalogue, ¬ firing.Valid A label cut

theorem enabled_empty_iff (catalogue : List (Firing T S O)) (cut : Configuration T O) :
    enabled A label catalogue cut = [] ↔ Terminal A label catalogue cut := by
  rw [List.eq_nil_iff_forall_not_mem]
  simp only [mem_enabled, Terminal, not_and]

theorem terminal_no_extension {catalogue : List (Firing T S O)}
    {cut : Configuration T O} (terminal : Terminal A label catalogue cut)
    {firing : Firing T S O} (member : firing ∈ catalogue) {rest : List (Firing T S O)} :
    ¬ Executable A label cut (firing :: rest) := fun run => terminal firing member run.1

/-- All levels up to a budget, then keep only independently terminal leaves.
No intermediate depth-bound leaf is silently reported as complete. -/
noncomputable def completed (catalogue : List (Firing T S O)) (budget : Nat)
    (cut : Configuration T O) : List (List (Firing T S O)) := by
  classical
  exact ((List.range (budget + 1)).flatMap fun depth => frontier A label catalogue depth cut).filter
    fun word => decide (Terminal A label catalogue (follow label cut word))

theorem mem_completed (catalogue : List (Firing T S O)) (budget : Nat)
    (cut : Configuration T O) (word : List (Firing T S O)) :
    word ∈ completed A label catalogue budget cut ↔
      word.length ≤ budget ∧ Executable A label cut word ∧
        (∀ firing ∈ word, firing ∈ catalogue) ∧
        Terminal A label catalogue (follow label cut word) := by
  classical
  simp only [completed, List.mem_filter, decide_eq_true_eq, List.mem_flatMap, List.mem_range]
  constructor
  · rintro ⟨⟨depth, bound, member⟩, terminal⟩
    obtain ⟨length, run, covered⟩ := (mem_frontier A label catalogue depth cut word).mp member
    exact ⟨by omega, run, covered, terminal⟩
  · rintro ⟨bound, run, covered, terminal⟩
    exact ⟨⟨word.length, by omega,
      (mem_frontier A label catalogue word.length cut word).mpr ⟨rfl, run, covered⟩⟩, terminal⟩

theorem initial_consistent {cut : Configuration T O} {word : List (Firing T S O)}
    (run : Executable A label cut word) : A.Consistent cut.equations := by
  cases word with
  | nil => exact run
  | cons firing rest =>
    obtain ⟨candidate, solved⟩ := run.1.firing.consistent
    rw [GuardFreeProcessOrders.problem_eq, A.models_append] at solved
    exact ⟨candidate, solved.1⟩

/-- If the full depth frontier is terminal, no catalogue-covered execution
can extend beyond it. This derives a global depth bound from the explored cut. -/
theorem closed_frontier_bounds (catalogue : List (Firing T S O)) (depth : Nat)
    (cut : Configuration T O)
    (closed : ∀ word ∈ frontier A label catalogue depth cut,
      Terminal A label catalogue (follow label cut word))
    (word : List (Firing T S O)) (run : Executable A label cut word)
    (covered : ∀ firing ∈ word, firing ∈ catalogue) : word.length ≤ depth := by
  induction depth generalizing cut word with
  | zero =>
    have terminal := closed [] ((mem_frontier A label catalogue 0 cut []).mpr
      ⟨rfl, initial_consistent A label run, by simp⟩)
    cases word with
    | nil => exact Nat.le_refl 0
    | cons firing rest => exact False.elim (terminal firing (covered firing (by simp)) run.1)
  | succ depth ih =>
    cases word with
    | nil => exact Nat.zero_le _
    | cons firing rest =>
      have tailBound := ih (firing.result label cut) (by
        intro suffix member
        obtain ⟨length, tailRun, tailCovered⟩ := (mem_frontier A label catalogue depth _ suffix).mp member
        exact closed (firing :: suffix) ((mem_frontier A label catalogue (depth + 1) cut _).mpr
          ⟨congrArg Nat.succ length, ⟨run.1, tailRun⟩, by
            intro event present
            rcases List.mem_cons.mp present with rfl | later
            · exact covered event (by simp)
            · exact tailCovered event later⟩)) rest run.2
        (fun event member => covered event (List.mem_cons_of_mem _ member))
      exact Nat.succ_le_succ tailBound

/-- At a certified closed frontier, collection includes every terminal
catalogue-covered history, with no externally assumed length bound. -/
theorem completed_exact_of_closed_frontier (catalogue : List (Firing T S O)) (depth : Nat)
    (cut : Configuration T O)
    (closed : ∀ word ∈ frontier A label catalogue depth cut,
      Terminal A label catalogue (follow label cut word)) (word : List (Firing T S O)) :
    word ∈ completed A label catalogue depth cut ↔
      Executable A label cut word ∧ (∀ firing ∈ word, firing ∈ catalogue) ∧
        Terminal A label catalogue (follow label cut word) := by
  rw [mem_completed]
  exact ⟨fun result => result.2,
    fun result => ⟨closed_frontier_bounds A label catalogue depth cut closed word result.1 result.2.1, result⟩⟩

/-- Flow, read/take precedence and query inhibition have distinct carriers. -/
def Flow (producer consumer : Firing T S O) : Prop :=
  ∃ occurrence ∈ producer.selection.made,
    occurrence ∈ consumer.selection.taken ∨ occurrence ∈ consumer.selection.read

def ReadBeforeTake (reader taker : Firing T S O) : Prop :=
  ∃ occurrence ∈ reader.selection.read, occurrence ∈ taker.selection.taken

def InhibitsAt (candidate : S) (writer observer : Firing T S O) : Prop :=
  ∃ query ∈ observer.queries, ∃ occurrence,
    (occurrence ∈ writer.selection.taken ∨ occurrence ∈ writer.selection.made) ∧
      query.region candidate (label occurrence) = true

omit [DecidableEq O] in
theorem noFlow_iff (first second : Firing T S O) :
    ¬ Flow first second ↔ GuardFreeProcessOrders.NoCause first.plain second.plain := by
  simp [Flow, GuardFreeProcessOrders.NoCause, Firing.plain, not_or]

omit [DecidableEq O] in
theorem noReadBeforeTake_iff (first second : Firing T S O) :
    ¬ ReadBeforeTake first second ↔ GuardFreeProcessOrders.NoAsym first.plain second.plain := by
  simp [ReadBeforeTake, GuardFreeProcessOrders.NoAsym, Firing.plain]

/-- This is an actual inhibition theorem at the new information cut, not
merely a name for a structural footprint overlap. -/
theorem inhibition_refuses {cut : Configuration T O} {writer observer : Firing T S O}
    (valid : observer.Valid A label cut)
    (writerEnabled : MeTTaCalculus.OccurrenceCommits.Enabled label cut.present
      (writer.selection.commit (T := T))) {candidate : S}
    (solved : A.Models candidate (observer.selection.problem label observer.rule
      (writer.result label cut))) (inhibits : InhibitsAt label candidate writer observer) :
    ¬ observer.Valid A label (writer.result label cut) := by
  obtain ⟨query, member, occurrence, written, inside⟩ := inhibits
  exact census_refused_after_writer A label valid writerEnabled member solved written inside

/-- At a node of the unfolding, maximality compares every enabled contender,
including contenders that the chosen scheduler did not run. -/
def Maximal (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (weight : Firing T S O → Nat) (chosen : Firing T S O) : Prop :=
  chosen ∈ enabled A label catalogue cut ∧
    ∀ other ∈ enabled A label catalogue cut, weight other ≤ weight chosen

theorem maximal_iff (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (weight : Firing T S O → Nat) (chosen : Firing T S O) :
    Maximal A label catalogue cut weight chosen ↔
      chosen ∈ catalogue ∧ chosen.Valid A label cut ∧
        ∀ other ∈ catalogue, other.Valid A label cut → weight other ≤ weight chosen := by
  simp only [Maximal, mem_enabled]
  constructor
  · rintro ⟨⟨member, valid⟩, greatest⟩
    exact ⟨member, valid, fun other inside ready => greatest other ⟨inside, ready⟩⟩
  · rintro ⟨member, valid, greatest⟩
    exact ⟨⟨member, valid⟩, fun other ready => greatest other ready.1 ready.2⟩

/-- Enabled-at-cut is independent of which equivalent representative of the
equation store is used. It supplies a finite-run fairness observation, not
an eventual-service theorem. -/
theorem enabled_congr (catalogue : List (Firing T S O)) {first second : Configuration T O}
    (same : SameUpTo A first second) :
    enabled A label catalogue first = enabled A label catalogue second := by
  classical
  unfold enabled
  apply List.filter_congr
  intro firing _
  simp only [Firing.valid_congr A label same]

/-- A bounded classifier retains its unresolved candidates independently of
the candidates already known to be enabled. -/
def known (catalogue : List (Firing T S O)) (check : Firing T S O → Option Bool) :=
  catalogue.filter fun firing => decide (check firing = some true)

def pending (catalogue : List (Firing T S O)) (check : Firing T S O → Option Bool) :=
  catalogue.filter fun firing => decide (check firing = none)

omit [DecidableEq O] in
theorem pending_empty_iff (catalogue : List (Firing T S O)) (check : Firing T S O → Option Bool) :
    pending catalogue check = [] ↔ ∀ firing ∈ catalogue, ∃ answer, check firing = some answer := by
  simp only [pending, List.eq_nil_iff_forall_not_mem, List.mem_filter, decide_eq_true_eq]
  constructor
  · intro closed firing member
    cases result : check firing with
    | none => exact False.elim (closed firing ⟨member, result⟩)
    | some answer => exact ⟨answer, rfl⟩
  · intro closed firing ⟨member, absent⟩
    obtain ⟨answer, result⟩ := closed firing member
    rw [absent] at result
    cases result

/-- Calibration of completed Boolean replies only. It grants no result to
an unfinished classifier. A concrete solver must prove this property. -/
def ClassifierSound (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (check : Firing T S O → Option Bool) : Prop :=
  ∀ firing ∈ catalogue, ∀ answer, check firing = some answer →
    (firing.Valid A label cut ↔ answer = true)

theorem closed_classifier_exact (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (check : Firing T S O → Option Bool) (sound : ClassifierSound A label catalogue cut check)
    (closed : pending catalogue check = []) :
    known catalogue check = enabled A label catalogue cut := by
  classical
  unfold known enabled
  apply List.filter_congr
  intro firing member
  obtain ⟨answer, result⟩ := (pending_empty_iff catalogue check).mp closed firing member
  rw [result]
  simp only [Option.some.injEq, sound firing member answer result]

theorem certified_empty_iff_terminal (catalogue : List (Firing T S O)) (cut : Configuration T O)
    (check : Firing T S O → Option Bool) (sound : ClassifierSound A label catalogue cut check)
    (closed : pending catalogue check = []) :
    known catalogue check = [] ↔ Terminal A label catalogue cut := by
  rw [closed_classifier_exact A label catalogue cut check sound closed, enabled_empty_iff]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunUnfolding
