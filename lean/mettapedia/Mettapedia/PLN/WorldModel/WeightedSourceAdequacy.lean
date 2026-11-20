import Mettapedia.PLN.WorldModel.WeightedSourceExecution

/-!
# Schedule-independent adequacy of finite weighted source execution

For the generated return/failure/choice fragment, every actual source step
preserves the multiset of eventual terminal data. Fragment membership is also
preserved. Consequently every quiescent source execution has the same branch
bag, and every completed collector execution has the same weighted answer
fold. These statements quantify over all source/collector schedules.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.WorldModel.WeightedSourceAdequacy

open scoped ENNReal
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open SourceLanguage SourceLanguage.Elaboration SourceLanguage.Toolkit
open Mettapedia.PLN.WorldModel.WeightedSourcePrograms
open Mettapedia.PLN.WorldModel.WeightedSourceExecution

inductive FiniteComp : SourceComp → Prop
  | ret (datum : MData) : FiniteComp (.ret datum)
  | fail : FiniteComp .fail
  | choice {left right : SourceComp} : FiniteComp left → FiniteComp right → FiniteComp (.choice left right)

inductive FiniteBranch : SourceBranch → Prop
  | eval {computation : SourceComp} : FiniteComp computation → FiniteBranch (start computation)
  | value (datum : MData) : FiniteBranch ⟨[], .value datum, [], []⟩

def terminalData (datum : MData) : SourceBranch := ⟨[], .value datum, [], []⟩

def compLeaves : SourceComp → Multiset MData
  | .ret datum => {datum}
  | .choice left right => compLeaves left + compLeaves right
  | _ => 0

def branchLeaves (branch : SourceBranch) : Multiset MData :=
  match branch.focus with
  | .eval computation => compLeaves computation
  | .value datum => {datum}
  | .refused _ _ => 0

def configLeaves (configuration : Config mkeys [] () D.Ty) : Multiset MData :=
  configuration.branches.bind branchLeaves

def FiniteConfig (configuration : Config mkeys [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches, FiniteBranch branch

theorem finite_store {branch : SourceBranch} (finite : FiniteBranch branch) : branch.store = [] := by
  cases finite <;> rfl

/-- This is a theorem about the actual source transition relation. -/
theorem move_preserves {before after : SourceWorld} {branch : SourceBranch} {branches : Multiset SourceBranch}
    (finite : FiniteBranch branch) (move : Move D program supply before branch after branches) :
    before = after ∧ (∀ result ∈ branches, FiniteBranch result) ∧
      branches.bind branchLeaves = branchLeaves branch := by
  cases finite with
  | value datum => cases move
  | eval body =>
    cases body with
    | ret datum =>
      cases move
      refine ⟨rfl, ?_, ?_⟩
      · intro result member
        rw [Multiset.mem_singleton.mp member]
        exact .value datum
      · simp [branchLeaves, compLeaves, start]
    | fail =>
      cases move
      refine ⟨rfl, ?_, ?_⟩
      · intro result member
        exact False.elim (Multiset.notMem_zero result member)
      · rfl
    | choice left right =>
      cases move
      refine ⟨rfl, ?_, ?_⟩
      · intro result member
        rcases Multiset.mem_cons.mp member with first | second
        · rw [first]
          exact .eval left
        · rw [Multiset.mem_singleton.mp second]
          exact .eval right
      · simp [branchLeaves, compLeaves, start]

/-- Arbitrary scheduling preserves the finite fragment and its complete terminal bag. -/
theorem step_preserves {before after : Config mkeys [] () D.Ty}
    (finite : FiniteConfig before) (step : Step D program supply before after) :
    FiniteConfig after ∧ configLeaves after = configLeaves before := by
  cases step with
  | move beforeWorld afterWorld branch rest branches live moved =>
    have preserved := move_preserves (finite branch (by simp)) moved
    refine ⟨?_, ?_⟩
    · intro result member
      rcases Multiset.mem_add.mp member with resultNew | resultOld
      · exact preserved.2.1 result resultNew
      · exact finite result (Multiset.mem_cons_of_mem resultOld)
    · simp only [configLeaves, Multiset.add_bind, Multiset.cons_bind, preserved.2.2]

theorem runs_preserve {before after : Config mkeys [] () D.Ty}
    (finite : FiniteConfig before) (run : Runs D program supply before after) :
    FiniteConfig after ∧ configLeaves after = configLeaves before := by
  induction run with
  | refl => exact ⟨finite, rfl⟩
  | tail previous step ih =>
    have next := step_preserves ih.1 step
    exact ⟨next.1, next.2.trans ih.2⟩

/-- A finite branch that cannot move has already returned a value. -/
theorem quiescent_value {configuration : Config mkeys [] () D.Ty}
    (finite : FiniteConfig configuration) (quiet : configuration.Quiescent program supply)
    (branch : SourceBranch) (member : branch ∈ configuration.branches) :
    ∃ datum, branch = terminalData datum := by
  have body := finite branch member
  cases body with
  | value datum => exact ⟨datum, rfl⟩
  | eval body =>
    have impossible := quiet _ member live_nil
    cases body with
    | ret datum => exact False.elim (impossible _ _ (.ret _ _ _ _ _))
    | fail => exact False.elim (impossible _ _ (.fail _ _ _ _))
    | choice left right => exact False.elim (impossible _ _ (.choice _ _ _ _ _ _))

theorem valueBag_eq_leaves (branches : Multiset SourceBranch)
    (values : ∀ branch ∈ branches, ∃ datum, branch = terminalData datum) :
    branches = (branches.bind branchLeaves).map terminalData := by
  induction branches using Multiset.induction_on with
  | empty => simp
  | @cons branch branches ih =>
    obtain ⟨datum, rfl⟩ := values branch (Multiset.mem_cons_self _ _)
    have tail := ih (fun result member => values result (Multiset.mem_cons_of_mem member))
    simp [branchLeaves, terminalData, ← tail]

/-- Any two quiescent schedules produce exactly the same source branch bag. -/
theorem quiescent_bags_agree {initial first second : Config mkeys [] () D.Ty}
    (finite : FiniteConfig initial)
    (firstRun : Runs D program supply initial first) (secondRun : Runs D program supply initial second)
    (firstQuiet : first.Quiescent program supply) (secondQuiet : second.Quiescent program supply) :
    first.branches = second.branches := by
  have firstProof := runs_preserve finite firstRun
  have secondProof := runs_preserve finite secondRun
  rw [valueBag_eq_leaves first.branches (quiescent_value firstProof.1 firstQuiet),
    valueBag_eq_leaves second.branches (quiescent_value secondProof.1 secondQuiet)]
  exact congrArg (Multiset.map terminalData) (firstProof.2.trans secondProof.2.symm)

theorem leaf_finite {n : Nat} (body : Body n) (world : Fin (2 ^ n)) : FiniteComp (leaf body world) := by
  rw [leaf_result]
  split
  · exact .ret _
  · exact .fail

theorem source_finite {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) :
    FiniteComp (sourceFrom body worlds) := by
  induction worlds with
  | nil => exact .fail
  | cons world worlds ih => exact .choice (leaf_finite body world) ih

theorem initial_finite {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld) :
    FiniteConfig ⟨shared, {start (sourceFrom body worlds)}⟩ := by
  intro branch member
  rw [Multiset.mem_singleton.mp member]
  exact .eval (source_finite body worlds)

/-- Source adequacy for every quiescent execution of every generated body. -/
theorem any_quiescent_bag {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n))) (shared : SourceWorld)
    {final : Config mkeys [] () D.Ty}
    (run : Runs D program supply ⟨shared, {start (sourceFrom body worlds)}⟩ final)
    (quiet : final.Quiescent program supply) :
    final.branches = (completed body worlds : Multiset SourceBranch) :=
  quiescent_bags_agree (initial_finite body worlds shared) run (source_runs body worlds shared)
    quiet (source_quiescent body worlds shared)

/-- In particular the weighted terminal mass is independent of the source schedule. -/
theorem any_quiescent_fold {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) (shared : SourceWorld)
    {final : Config mkeys [] () D.Ty}
    (run : Runs D program supply
      ⟨shared, {start (sourceFrom body (List.ofFn (fun world : Fin (2 ^ n) => world)))}⟩ final)
    (quiet : final.Quiescent program supply) :
    (final.branches.map (observe body probability query)).sum =
      (WeightedSourcePrograms.compile body query).count probability := by
  rw [any_quiescent_bag body _ shared run quiet]
  exact answer_fold_eq_compiled body probability bounded query

/-- All completed collector schedules retain exactly the same source rows.
No branch can be spuriously discarded: every finite-fragment store is live. -/
theorem any_completed_collector_rows {n : Nat} (body : Body n) (worlds : List (Fin (2 ^ n)))
    (shared : SourceWorld) {final : AnswerCollection.State mkeys [] () D}
    (run : AnswerCollection.CollectorRuns D program supply
      (AnswerCollection.State.initial ⟨shared, {start (sourceFrom body worlds)}⟩) final)
    (complete : final.current.branches = 0) :
    (final.reverseAnswers : Multiset SourceBranch) = (completed body worlds : Multiset SourceBranch) := by
  have valid := run.preserves_valid (AnswerCollection.State.initial_valid _)
  have sourceRun : Runs D program supply ⟨shared, {start (sourceFrom body worlds)}⟩ final.erase := by
    simpa only [AnswerCollection.State.erase_initial] using run.erase
  have finite := (runs_preserve (initial_finite body worlds shared) sourceRun).1
  have noRejected : final.refuted = 0 := by
    apply Multiset.eq_zero_of_forall_notMem
    intro branch member
    have memberErase : branch ∈ final.erase.branches := by
      exact Multiset.mem_add.mpr (Or.inr member)
    have emptyStore := finite_store (finite branch memberErase)
    exact valid.refuted branch member (emptyStore ▸ live_nil)
  have finish : final.finish? = some final.reverseAnswers.reverse :=
    (final.finish_some_iff _).mpr ⟨complete, rfl⟩
  have quiet := final.completed_quiescent (P := program) (supply := supply) valid _ finish
  have bag := any_quiescent_bag body worlds shared sourceRun quiet
  simpa only [AnswerCollection.State.erase, complete, noRejected, zero_add, add_zero] using bag

/-- Full operational/denotational adequacy: every completed execution of the
actual collector computes the same BDD mass, for every Boolean output query. -/
theorem any_completed_collector_fold {n : Nat} (body : Body n) (probability : Fin n → ℝ≥0∞)
    (bounded : ∀ i, probability i ≤ 1) (query : Bool → Bool) (shared : SourceWorld)
    {final : AnswerCollection.State mkeys [] () D}
    (run : AnswerCollection.CollectorRuns D program supply
      (AnswerCollection.State.initial
        ⟨shared, {start (sourceFrom body (List.ofFn (fun world : Fin (2 ^ n) => world)))}⟩) final)
    (complete : final.current.branches = 0) :
    (AnswerCollection.reify final (run.preserves_valid (AnswerCollection.State.initial_valid _))).map
      (fun space => Multiplicative.toAdd
        (space.fold (fun branch => Multiplicative.ofAdd (observe body probability query branch)))) =
      some ((WeightedSourcePrograms.compile body query).count probability) := by
  have rows := any_completed_collector_rows body _ shared run complete
  have counted := answer_fold_eq_compiled body probability bounded query
  simp only [AnswerCollection.reify, complete, Multiset.card_zero, ↓reduceIte, Option.map_some,
    AnswerCollection.AnswerSpace.fold]
  congr 1
  change ((final.reverseAnswers : Multiset SourceBranch).map (observe body probability query)).sum = _
  rw [rows]
  exact counted

#print axioms step_preserves
#print axioms quiescent_bags_agree
#print axioms any_quiescent_fold
#print axioms any_completed_collector_fold

end Mettapedia.PLN.WorldModel.WeightedSourceAdequacy
