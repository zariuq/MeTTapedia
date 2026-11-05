import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunCandidatesFrontier

/-!
# Branch collection over the unfolding driven by the sources

The branches of `AnnotatedRunBranchCollection` come from a fixed catalogue. Here they come from
the sources: every cut generates and classifies its own candidates
(`AnnotatedRunCandidates.sourceFrontier`). A history ends a branch when the generation at its end
is complete and admits nothing (`sourceCompleted`). The collection is complete exactly when the
frontier of the depth budget is complete and every history there ends a branch (`SourceClosed`);
two budgets can leave it incomplete, the classification budget and the depth budget.

* **No longer history** (`length_le_of_sourceClosed`): at a closed frontier no run whose firings
  were candidates where they fired is longer than the depth budget.
* **Exactness** (`sourceCompleted_exact`): at a closed frontier the ended histories are exactly the
  runs whose firings were candidates where they fired and at whose end no candidate is admitted,
  with no length bound assumed; their causal classes are the branches (`sourceBranches_exact`).
* **Status** (`sourceCollect_eq_complete_iff`, `sourceCollect_incomplete_of_not_closed`): the
  collection is complete exactly when the frontier is closed; an incomplete collection that found
  nothing is not the complete empty one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection

open AnnotatedRuns
open AnnotatedRunCandidates (Sources sourceFrontier SourceRun CalibratedEverywhere Status Verdict
  sourceFrontier_sound sourceFrontier_exact sourceFrontier_succ_status mem_sourceFrontier_succ
  none_iff_terminal complete_exact)
open AnnotatedRunUnfolding (CausalClass Terminal)

variable {T S O : Type*} [DecidableEq O] {Answer : Type*}
variable (A : SubstitutionAction T S) (label : O → T)
variable {src : Sources T S O} {classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O}
  {budget : ℕ}

/-- The generation at the end of a history reports "no admitted firing". -/
def EndsBranch (src : Sources T S O) (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O)
    (budget : ℕ) (root : Configuration T O) (word : List (Firing T S O)) : Prop :=
  (src.generateAt classify budget (follow label root word)).verdict = .none

instance (src : Sources T S O) (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O)
    (budget : ℕ) (root : Configuration T O) (word : List (Firing T S O)) :
    Decidable (EndsBranch label src classify budget root word) :=
  inferInstanceAs (Decidable (_ = _))

/-- The histories within the depth budget that end a branch. -/
noncomputable def sourceCompleted (src : Sources T S O)
    (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O) (budget depth : ℕ)
    (root : Configuration T O) : List (List (Firing T S O)) :=
  ((List.range (depth + 1)).flatMap fun d => (sourceFrontier A label src classify budget d root).1).filter
    fun word => decide (EndsBranch label src classify budget root word)

/-- **The frontier of the depth budget is closed**: complete, and every history there ends a
branch. -/
def SourceClosed (src : Sources T S O)
    (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O) (budget depth : ℕ)
    (root : Configuration T O) : Prop :=
  (sourceFrontier A label src classify budget depth root).2 = .complete ∧
    ∀ word ∈ (sourceFrontier A label src classify budget depth root).1,
      EndsBranch label src classify budget root word

/-- A complete frontier is complete at every smaller depth. -/
theorem sourceFrontier_complete_of_le :
    ∀ (d depth : ℕ) (root : Configuration T O), d ≤ depth →
      (sourceFrontier A label src classify budget depth root).2 = .complete →
        (sourceFrontier A label src classify budget d root).2 = .complete
  | 0, _, _, _, _ => rfl
  | d + 1, 0, _, le, _ => absurd le (Nat.not_succ_le_zero d)
  | d + 1, depth + 1, root, le, complete => by
      obtain ⟨generated, children⟩ := (sourceFrontier_succ_status A label).mp complete
      exact (sourceFrontier_succ_status A label).mpr ⟨generated, fun f admitted =>
        sourceFrontier_complete_of_le d depth (f.result label root) (Nat.le_of_succ_le_succ le)
          (children f admitted)⟩

/-- An ended branch admits no candidate at its end. -/
theorem terminal_of_endsBranch (calibrated : CalibratedEverywhere A label src classify)
    {root : Configuration T O} {word : List (Firing T S O)}
    (ends : EndsBranch label src classify budget root word) :
    Terminal A label (src.candidatesAt (follow label root word)) (follow label root word) :=
  ((none_iff_terminal A label (calibrated (follow label root word))).mp ends).2

/-- **No longer history**: at a closed frontier, no run whose firings were candidates where they
fired is longer than the depth budget. -/
theorem length_le_of_sourceClosed (calibrated : CalibratedEverywhere A label src classify) :
    ∀ (depth : ℕ) (root : Configuration T O), SourceClosed A label src classify budget depth root →
      ∀ word, Executable A label root word → SourceRun label src root word → word.length ≤ depth
  | 0, root, closed, word, run, source => by
      cases source with
      | nil => exact le_refl 0
      | @cons _ f rest candidate _ =>
          exfalso
          have start : [] ∈ (sourceFrontier A label src classify budget 0 root).1 := by
            classical
            simp only [sourceFrontier]
            rw [if_pos (AnnotatedRunUnfolding.initial_consistent A label run)]
            exact List.mem_singleton_self _
          exact terminal_of_endsBranch A label calibrated (closed.2 [] start) f candidate run.1
  | depth + 1, root, closed, word, run, source => by
      cases source with
      | nil => exact Nat.zero_le _
      | @cons _ f rest candidate later =>
          obtain ⟨generated, children⟩ := (sourceFrontier_succ_status A label).mp closed.1
          have admitted : f ∈ (src.generateAt classify budget root).admitted :=
            (complete_exact A label (calibrated root) generated f).mpr ⟨candidate, run.1⟩
          have childClosed : SourceClosed A label src classify budget depth (f.result label root) :=
            ⟨children f admitted, fun suffix member =>
              closed.2 (f :: suffix) ((mem_sourceFrontier_succ A label).mpr
                ⟨f, admitted, suffix, member, rfl⟩)⟩
          exact Nat.succ_le_succ
            (length_le_of_sourceClosed calibrated depth (f.result label root) childClosed rest run.2 later)

/-- **Exactness of the ended histories**: at a closed frontier they are exactly the runs whose
firings were candidates where they fired and whose end admits no candidate. -/
theorem sourceCompleted_exact (calibrated : CalibratedEverywhere A label src classify)
    {depth : ℕ} {root : Configuration T O} (closed : SourceClosed A label src classify budget depth root)
    (word : List (Firing T S O)) :
    word ∈ sourceCompleted A label src classify budget depth root ↔
      Executable A label root word ∧ SourceRun label src root word ∧
        EndsBranch label src classify budget root word := by
  unfold sourceCompleted
  rw [List.mem_filter, decide_eq_true_eq, List.mem_flatMap]
  constructor
  · rintro ⟨⟨d, _, member⟩, ends⟩
    obtain ⟨_, run, source⟩ := sourceFrontier_sound A label calibrated d root word member
    exact ⟨run, source, ends⟩
  · rintro ⟨run, source, ends⟩
    have bound := length_le_of_sourceClosed A label calibrated depth root closed word run source
    refine ⟨⟨word.length, List.mem_range.mpr (Nat.lt_succ_of_le bound), ?_⟩, ends⟩
    exact (sourceFrontier_exact A label calibrated word.length root
      (sourceFrontier_complete_of_le A label word.length depth root bound closed.1) word).mpr
      ⟨rfl, run, source⟩

open Classical in
/-- The branches of the unfolding driven by the sources: the causal classes of ended histories. -/
noncomputable def sourceBranches (src : Sources T S O)
    (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O) (budget depth : ℕ)
    (root : Configuration T O) : Finset (CausalClass A label root) :=
  ((sourceCompleted A label src classify budget depth root).map (Quot.mk _)).toFinset

/-- **The branches at a closed frontier** are the causal classes of the runs whose firings were
candidates where they fired and whose end admits no candidate. -/
theorem sourceBranches_exact (calibrated : CalibratedEverywhere A label src classify)
    {depth : ℕ} {root : Configuration T O} (closed : SourceClosed A label src classify budget depth root)
    (trace : CausalClass A label root) :
    trace ∈ sourceBranches A label src classify budget depth root ↔
      ∃ word, Executable A label root word ∧ SourceRun label src root word ∧
        EndsBranch label src classify budget root word ∧ Quot.mk _ word = trace := by
  classical
  unfold sourceBranches
  rw [List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨word, member, same⟩
    obtain ⟨run, source, ends⟩ := (sourceCompleted_exact A label calibrated closed word).mp member
    exact ⟨word, run, source, ends, same⟩
  · rintro ⟨word, run, source, ends, same⟩
    exact ⟨word, (sourceCompleted_exact A label calibrated closed word).mpr ⟨run, source, ends⟩, same⟩

open Classical in
/-- **What `collapse` gathers over the unfolding driven by the sources**, complete exactly when
the frontier of the depth budget is closed. -/
noncomputable def sourceCollect (src : Sources T S O)
    (classify : Configuration T O → AnnotatedRunCandidates.Classifier T S O) (budget depth : ℕ)
    (root : Configuration T O) (observe : Configuration T O → Multiset Answer)
    (respects : RespectsClasses A observe) : Collection Answer :=
  if SourceClosed A label src classify budget depth root then
    .complete (∑ trace ∈ sourceBranches A label src classify budget depth root,
      observeClass A label root observe respects trace)
  else
    .incomplete (∑ trace ∈ sourceBranches A label src classify budget depth root,
      observeClass A label root observe respects trace)

/-- **The status of the collection**: complete exactly when the frontier is closed. -/
theorem sourceCollect_eq_complete_iff {depth : ℕ} {root : Configuration T O}
    {observe : Configuration T O → Multiset Answer} {respects : RespectsClasses A observe}
    (bag : Multiset Answer) :
    sourceCollect A label src classify budget depth root observe respects = .complete bag ↔
      SourceClosed A label src classify budget depth root ∧
        bag = ∑ trace ∈ sourceBranches A label src classify budget depth root,
          observeClass A label root observe respects trace := by
  classical
  unfold sourceCollect
  split
  · next closed =>
      constructor
      · intro same
        cases same
        exact ⟨closed, rfl⟩
      · rintro ⟨_, rfl⟩
        rfl
  · next open_ =>
      constructor
      · intro same
        cases same
      · rintro ⟨closed, _⟩
        exact absurd closed open_

/-- An open frontier leaves the collection incomplete, whatever it found. -/
theorem sourceCollect_incomplete_of_not_closed {depth : ℕ} {root : Configuration T O}
    {observe : Configuration T O → Multiset Answer} {respects : RespectsClasses A observe}
    (open_ : ¬ SourceClosed A label src classify budget depth root) :
    sourceCollect A label src classify budget depth root observe respects =
      .incomplete (∑ trace ∈ sourceBranches A label src classify budget depth root,
        observeClass A label root observe respects trace) := by
  classical
  unfold sourceCollect
  rw [if_neg open_]

#print axioms sourceCollect_incomplete_of_not_closed
#print axioms sourceFrontier_complete_of_le
#print axioms terminal_of_endsBranch
#print axioms length_le_of_sourceClosed
#print axioms sourceCompleted_exact
#print axioms sourceBranches_exact
#print axioms sourceCollect_eq_complete_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunBranchCollection
