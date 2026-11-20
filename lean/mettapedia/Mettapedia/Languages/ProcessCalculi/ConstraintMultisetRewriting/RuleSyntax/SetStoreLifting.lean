import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreFirings
import Mathlib.Data.List.Enum

/-! # A ground propagation instance lifts to an actual rule firing -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  {P : Program (Terms (Term signature))}

def madeIds (match_ : GroundMatch P) : List (Term signature × ℕ) :=
  (match_.rule.body.produce.zipIdx 1).map fun entry => (match_.assignment.applyTerm entry.1, entry.2)

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem madeIds_nodup (match_ : GroundMatch P) : (madeIds match_).Nodup := by
  apply List.Nodup.of_map Prod.snd
  simp only [madeIds, List.map_map, Function.comp_def]
  change ((match_.rule.body.produce.zipIdx 1).map Prod.snd).Nodup
  rw [List.zipIdx_map_snd]
  exact List.nodup_range' 1 (by decide)

def GroundMatch.firing (match_ : GroundMatch P) :
    Firing (Term signature × ℕ) (E (signature := signature)) P PUnit.unit :=
  ⟨match_.rule, match_.member, PUnit.unit, Subst.id signature,
    ⟨[], match_.rule.body.read.map (fun term => (match_.assignment.applyTerm term, 0)), madeIds match_⟩, []⟩

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem firing_read (match_ : GroundMatch P) : (match_.firing.opened X).read = match_.rule.body.read := by
  change match_.rule.body.read.map ((Subst.id signature).applyTerm) = _
  rw [show (Subst.id signature).applyTerm = id from funext Subst.applyTerm_id, List.map_id]

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem firing_produce (match_ : GroundMatch P) :
    (match_.firing.opened X).produce = match_.rule.body.produce := by
  change match_.rule.body.produce.map ((Subst.id signature).applyTerm) = _
  rw [show (Subst.id signature).applyTerm = id from funext Subst.applyTerm_id, List.map_id]

theorem firing_fresh (match_ : GroundMatch P) (rows : Finset (Term signature)) (ground : GroundRows rows) :
    match_.firing.Fresh X (SetStore.represent rows) := by
  intro b g h
  cases b
  refine ⟨h, ?_, ?_⟩
  · intro term mentioned
    obtain (known | known | ⟨o, present, rfl⟩) := mentioned
    · cases known
    · cases known
    · change h.applyTerm ((Subst.id signature).applyTerm o.1) = g.applyTerm o.1
      rw [Subst.applyTerm_id, FirstOrder.ground_fixed h o.1 (ground o.1 (present_value rows present)),
        FirstOrder.ground_fixed g o.1 (ground o.1 (present_value rows present))]
  · intro term _
    change h.applyTerm ((Subst.id signature).applyTerm term) = h.applyTerm term
    rw [Subst.applyTerm_id]

theorem firing_shapes (match_ : GroundMatch P) (rows : Finset (Term signature)) (ground : GroundRows rows) :
    match_.firing.Shapes X (SetStore.represent rows) := by
  refine ⟨firing_fresh match_ rows ground, List.nodup_nil, madeIds_nodup match_, ?_, ?_, ?_, ?_⟩
  · simp only [match_.propagates.noTake, GroundMatch.firing, List.length_nil]
  · simp only [GroundMatch.firing, List.length_map]
  · simp only [GroundMatch.firing, madeIds, List.length_map, List.length_zipIdx]
  · simp only [match_.propagates.positive.2, GroundMatch.firing, List.length_nil]

theorem firing_enabled (match_ : GroundMatch P) (rows : Finset (Term signature))
    (enabled : (consequence match_).read ⊆ rows) :
    MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Term signature × ℕ => ())
      (SetStore.represent rows).present (match_.firing.selection.commit (T := Unit)) := by
  refine ⟨by simp [GroundMatch.firing, Selection.commit], ?_, by simp [GroundMatch.firing, Selection.commit], ?_, ?_⟩
  · intro o read
    obtain ⟨term, member, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp read)
    exact Finset.mem_image.mpr ⟨_, enabled (List.mem_toFinset.mpr (List.mem_map.mpr ⟨term, member, rfl⟩)), rfl⟩
  · apply Finset.disjoint_left.mpr
    intro o made present
    obtain ⟨entry, inside, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
    obtain ⟨old, _, equal⟩ := Finset.mem_image.mp present
    have positive := (List.mem_zipIdx inside).1
    have zero : entry.2 = 0 := (congrArg Prod.snd equal).symm
    omega
  · intro q inside
    simp [Selection.commit] at inside

def problem (match_ : GroundMatch P) : EquationStore (Term signature) :=
  match_.rule.body.read.map fun term => (term, match_.assignment.applyTerm term)

theorem firing_information (match_ : GroundMatch P) (rows : Finset (Term signature)) :
    match_.firing.information X (SetStore.represent rows) = problem match_ := by
  change [] ++ (match_.firing.opened X).take.zipWith _ [] ++
    (match_.firing.opened X).read.zipWith
      (fun term (o : Term signature × ℕ) => (term, ((Subst.id signature).applyTerm o.1)))
      (match_.rule.body.read.map fun term => (match_.assignment.applyTerm term, 0)) ++
    (match_.firing.opened X).tell = _
  have takes : (match_.firing.opened X).take = [] := by
    change match_.rule.body.take.map _ = []
    rw [match_.propagates.noTake, List.map_nil]
  have tells : (match_.firing.opened X).tell = [] := by
    change match_.rule.body.tell.map _ = []
    rw [match_.propagates.noTell, List.map_nil]
  rw [takes, tells, firing_read]
  simp only [List.zipWith_nil_left, List.nil_append, List.append_nil, List.zipWith_map_right,
    Subst.applyTerm_id, List.zipWith_self]
  rfl

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem problem_solved (match_ : GroundMatch P) :
    (FirstOrder.action signature).Models match_.assignment (problem match_) := by
  intro pair inside
  obtain ⟨term, read, rfl⟩ := List.mem_map.mp inside
  change match_.assignment.applyTerm term = match_.assignment.applyTerm (match_.assignment.applyTerm term)
  exact (FirstOrder.ground_fixed _ _ (match_.groundReads term read)).symm

omit [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] in
theorem problem_reads (match_ : GroundMatch P) (other : Subst signature)
    (solved : (FirstOrder.action signature).Models other (problem match_)) :
    ∀ term ∈ match_.rule.body.read, other.applyTerm term = match_.assignment.applyTerm term := by
  intro term read
  have equal := solved (term, match_.assignment.applyTerm term) (List.mem_map.mpr ⟨term, read, rfl⟩)
  change other.applyTerm term = other.applyTerm (match_.assignment.applyTerm term) at equal
  rwa [FirstOrder.ground_fixed other _ (match_.groundReads term read)] at equal

theorem firing_admitted (match_ : GroundMatch P) (rows : Finset (Term signature))
    (ground : GroundRows rows) (enabled : (consequence match_).read ⊆ rows) :
    match_.firing.Admits X (SetStore.represent rows) := by
  refine ⟨firing_shapes match_ rows ground, firing_enabled match_ rows enabled, ?_, ?_⟩
  · exact ⟨PUnit.unit, match_.assignment, by rw [firing_information]; exact problem_solved match_⟩
  · intro b other solved
    cases b
    rw [firing_information] at solved
    refine ⟨?_, ?_⟩
    · intro check member
      obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
      obtain ⟨left, right, rfl⟩ := match_.propagates.positive.1 original inside
      change other.applyTerm ((Subst.id signature).applyTerm left) =
        other.applyTerm ((Subst.id signature).applyTerm right)
      simp only [Subst.applyTerm_id]
      exact checks_of_matches match_ other (problem_reads match_ other solved) left right inside
    · intro query inside
      have empty : match_.firing.collectOpened X = [] := by
        change match_.rule.collect.map _ = []
        rw [match_.propagates.positive.2, List.map_nil]
      change query ∈ (match_.firing.collectOpened X).zip [] at inside
      rw [empty] at inside
      cases inside

theorem sameRows_ground_eq {first second : Finset (Term signature)} (ground : GroundRows first)
    (same : SetStore.SameRows first second) : second = first := by
  obtain ⟨names, rfl⟩ := same
  have fixed : ∀ term ∈ first, UnificationRenaming.rename names term = term := by
    intro term inside
    exact FirstOrder.ground_fixed _ _ (ground term inside)
  simpa using Finset.image_congr fixed

theorem lifted_result (match_ : GroundMatch P) (rows : Finset (Term signature)) (ground : GroundRows rows)
    (answer : Subst signature) (solved : (FirstOrder.action signature).Models answer (problem match_)) :
    SetStore.setResult rows (Bag.single match_.firing) answer = rows ∪ (consequence match_).made := by
  have fixed : rows.image answer.applyTerm = rows := by
    calc
      _ = rows.image id := Finset.image_congr fun term inside => FirstOrder.ground_fixed answer term (ground term inside)
      _ = rows := Finset.image_id
  have produced := matches_determine_scoped_terms match_ answer (problem_reads match_ answer solved)
    match_.rule.body.produce match_.propagates.madeScoped
  have made : (match_.rule.body.produce.toFinset.image answer.applyTerm) = (consequence match_).made := by
    ext value
    simp only [consequence, Finset.mem_image, List.mem_toFinset]
    simpa only [List.mem_map] using
      Iff.of_eq (congrArg (fun terms : List (Term signature) => value ∈ terms) produced)
  unfold SetStore.setResult SetStore.update
  simp only [Bag.single]
  rw [Bag.selection_single, Bag.produce_single]
  change (rows \ ∅).image answer.applyTerm ∪
    (match_.firing.opened X).produce.toFinset.image answer.applyTerm = _
  rw [firing_produce, Finset.sdiff_empty, fixed, made]

/-- Every changing ground propagation instance is an actual admitted singleton set step. -/
theorem lift_step (timing : SetStore.AskTiming) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (step : SetStoreClosure.Step (consequence (P := P)) rows after) :
    SetStore.Step timing P rows after := by
  obtain ⟨match_, enabled, rfl, changed⟩ := step
  have firingYes := firing_admitted match_ rows ground enabled
  have bagYes := (Bag.single_admits_iff X (SetStore.represent rows) match_.firing).mpr firingYes
  have info : (Bag.single match_.firing).information X (SetStore.represent rows) = problem match_ := by
    simp only [Bag.single]
    rw [Bag.information_single]
    exact firing_information match_ rows
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent (problem match_)).mpr
    ⟨match_.assignment, problem_solved match_⟩
  have yes : SetStore.admitted timing rows (Bag.single match_.firing) := by
    cases timing with
    | afterTells => exact bagYes
    | beforeTells =>
      apply (Bag.beforeTells_iff_of_no_tells X (SetStore.represent rows) (Bag.single match_.firing) ?_).mpr bagYes
      intro member inside
      obtain rfl := List.mem_singleton.mp inside
      change match_.rule.body.tell.map _ = []
      rw [match_.propagates.noTell, List.map_nil]
  have result := lifted_result match_ rows ground answer (unifyTotal_sound _ _ accepted)
  refine ⟨Bag.single match_.firing, List.cons_ne_nil _ _, yes, answer, ?_, ?_, ?_⟩
  · rwa [info]
  · simpa only [SetStore.update_no_take, Finset.image_id] using result.symm
  · intro same
    exact changed (sameRows_ground_eq ground same)

theorem actual_terminal_iff_closed (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (rows : Finset (Term signature)) (ground : GroundRows rows) :
    (∀ after, ¬ SetStore.Step timing P rows after) ↔ SetStoreClosure.Closed (consequence (P := P)) rows := by
  constructor
  · intro terminal
    apply (SetStoreClosure.terminal_iff_closed _ _).mp
    intro after step
    exact terminal after (lift_step timing ground step)
  · exact closed_ground_terminal pure rows ground

theorem actual_reachable_ground (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStore.Step timing P) seed after) : GroundRows after := by
  induction run with
  | refl => exact ground
  | tail run step ih => exact actual_step_preserves_ground pure ih step

theorem actual_reachable_le_closure (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStore.Step timing P) seed after) :
    (after : Set (Term signature)) ⊆ SetStoreClosure.closure (consequence (P := P)) seed := by
  induction run with
  | refl => exact SetStoreClosure.seed_subset_closure _ _
  | tail run step ih =>
    exact actual_step_le_closure pure seed (actual_reachable_ground timing pure ground run) ih step

theorem actual_terminal_eq_closure (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) {seed after : Finset (Term signature)} (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStore.Step timing P) seed after)
    (terminal : ∀ later, ¬ SetStore.Step timing P after later) :
    (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed := by
  have laterGround := actual_reachable_ground timing pure ground run
  have closed := (actual_terminal_iff_closed timing pure after laterGround).mp terminal
  apply Set.Subset.antisymm (actual_reachable_le_closure timing pure ground run)
  apply (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
    (fun m => SetStoreClosure.action (consequence m)) (seed : Set (Term signature))).2
  refine ⟨?_, (SetStoreClosure.closed_action_iff _ _).mp closed⟩
  have includes : ∀ {state}, Relation.ReflTransGen (SetStore.Step timing P) seed state → seed ⊆ state := by
    intro state path
    induction path with
    | refl => exact Finset.Subset.refl _
    | tail path step ih => exact ih.trans (actual_step_extensive pure (actual_reachable_ground timing pure ground path) step)
  have subset := includes run
  exact subset

theorem lift_run (timing : SetStore.AskTiming) {seed after : Finset (Term signature)}
    (ground : GroundRows seed)
    (run : Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := P))) seed after) :
    Relation.ReflTransGen (SetStore.Step timing P) seed after := by
  induction run with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (lift_step timing (reachable_ground ground path) step)

theorem actual_exists_terminal (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier seed : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (inside : seed ⊆ carrier) (ground : GroundRows seed) :
    ∃ after, Relation.ReflTransGen (SetStore.Step timing P) seed after ∧
      (∀ later, ¬ SetStore.Step timing P after later) ∧
      (after : Set (Term signature)) = SetStoreClosure.closure (consequence (P := P)) seed := by
  obtain ⟨after, run, terminal⟩ := SetStoreClosure.exists_terminal (consequence (P := P)) carrier closed seed inside
  have afterGround := reachable_ground ground run
  have actualRun := lift_run timing ground run
  have actualTerminal := (actual_terminal_iff_closed timing pure after afterGround).mpr
    ((SetStoreClosure.terminal_iff_closed _ _).mp terminal)
  exact ⟨after, actualRun, actualTerminal, actual_terminal_eq_closure timing pure ground actualRun actualTerminal⟩

theorem actual_step_card_lt {timing : SetStore.AskTiming}
    (pure : ∀ rule ∈ P, Propagates rule) {rows after : Finset (Term signature)}
    (ground : GroundRows rows) (step : SetStore.Step timing P rows after) : rows.card < after.card := by
  have different : rows ≠ after := by
    intro same
    subst after
    exact SetStore.self_is_not_step timing rows step
  exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨actual_step_extensive pure ground step, different⟩)

theorem actual_no_infinite_run (timing : SetStore.AskTiming)
    (pure : ∀ rule ∈ P, Propagates rule) (carrier : Finset (Term signature))
    (closed : SetStoreClosure.Closed (consequence (P := P)) carrier)
    (run : ℕ → Finset (Term signature)) (inside : run 0 ⊆ carrier) (ground : GroundRows (run 0)) :
    ¬ ∀ n, SetStore.Step timing P (run n) (run (n + 1)) := by
  intro steps
  have closure_eq : SetStoreClosure.closure (consequence (P := P)) carrier = (carrier : Set (Term signature)) := by
    apply Set.Subset.antisymm
    · exact (Mettapedia.GSLT.OpenEnded.ChaoticIteration.isLeast_target
        (fun m => SetStoreClosure.action (consequence m)) (carrier : Set (Term signature))).2
          ⟨Set.Subset.refl _, (SetStoreClosure.closed_action_iff _ _).mp closed⟩
    · exact SetStoreClosure.seed_subset_closure _ _
  have bound : ∀ n, GroundRows (run n) ∧ run n ⊆ carrier ∧ n + (run 0).card ≤ (run n).card := by
    intro n
    induction n with
    | zero => exact ⟨ground, inside, by omega⟩
    | succ n ih =>
      refine ⟨actual_step_preserves_ground pure ih.1 (steps n), ?_, ?_⟩
      · have upper := actual_step_le_closure pure carrier ih.1
          (fun _ member => SetStoreClosure.seed_subset_closure _ _ (ih.2.1 member)) (steps n)
        rwa [closure_eq] at upper
      · have card := actual_step_card_lt pure ih.1 (steps n)
        omega
  have last := bound (carrier.card + 1)
  have card := Finset.card_le_card last.2.1
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreSyntax
