import Mettapedia.Machines.ObserverLicence.HEWitness

/-!
# Realizing success-priority batches by bounded executions

The stack terminates at a fixed depth within its independently defined
expansion potential. When that depth settles the demand, a ready execution
exists. The iteration engine uses the established portfolio coordinator;
cut-off rounds discard their private successes and errors together.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.HEWitness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
open BoundedSearchPortfolio (Cursor Status Iteration)
open RuntimePlumbing

universe u w
variable {S : Type u} {Reply : Type}

theorem advance_terminal (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel : Nat) (cursor : Cursor S Reply)
    (terminal : status isError demand cursor ≠ .paused) :
    advance space isError demand fuel cursor = cursor := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [advance, tick, terminal] using ih

theorem paused_frontier_nonempty (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply)
    (paused : status isError demand cursor = .paused) : cursor.frontier ≠ [] := by
  intro empty
  simp only [status, empty, List.isEmpty_nil, ↓reduceIte] at paused
  split at paused <;> simp_all
  split at paused <;> contradiction

theorem advance_finishes (space : Space S Reply) (isError : Reply → Bool)
    (demand fuel : Nat) (cursor : Cursor S Reply)
    (enough : BoundedSearchPortfolio.pendingWork space cursor.frontier ≤ fuel) :
    status isError demand (advance space isError demand fuel cursor) ≠ .paused := by
  induction fuel generalizing cursor with
  | zero =>
      intro paused
      have nonempty := paused_frontier_nonempty isError demand cursor paused
      have positive := BoundedSearchPortfolio.pendingWork_positive space cursor.frontier nonempty
      omega
  | succ fuel ih =>
      by_cases paused : status isError demand cursor = .paused
      · have decrease := BoundedSearchPortfolio.expandOne_pendingWork space cursor
          (paused_frontier_nonempty isError demand cursor paused)
        simp only [advance, tick, paused, ↓reduceIte]
        exact ih _ (by omega)
      · rw [advance_terminal space isError demand (fuel + 1) cursor paused]
        exact paused

def Decides (space : Space S Reply) (isError : Reply → Bool) (demand depth : Nat) (root : S) : Prop :=
  demand ≤ (SuccessPriority.successes isError (bounded space depth root).1).length ∨
    (bounded space depth root).2 = false

theorem cutoff_shape (isError : Reply → Bool) (demand : Nat) (cursor : Cursor S Reply)
    (cutoff : status isError demand cursor = .cutoff) :
    cursor.frontier = [] ∧ cursor.cut = true ∧
      (SuccessPriority.successes isError cursor.answers).length < demand := by
  unfold status at cutoff
  split at cutoff
  · contradiction
  · rename_i insufficient
    split at cutoff
    · split at cutoff <;> simp_all [List.isEmpty_iff]
    · contradiction

theorem settled_run_ready (space : Space S Reply) (isError : Reply → Bool)
    (demand depth : Nat) (root : S) (settled : Decides space isError demand depth root) :
    BoundedSearchPortfolio.ready (status isError demand
      (run space isError demand (boundedWork space depth root) depth root)) = true := by
  let cursor := run space isError demand (boundedWork space depth root) depth root
  have terminal : status isError demand cursor ≠ .paused := by
    apply advance_finishes
    simp [BoundedSearchPortfolio.start, BoundedSearchPortfolio.pendingWork]
  cases outcome : status isError demand cursor with
  | paused => contradiction
  | full | exhausted => rfl
  | cutoff =>
      obtain ⟨empty, cut, insufficient⟩ := cutoff_shape isError demand cursor outcome
      have occurrences := run_occurrences space isError demand (boundedWork space depth root) depth root
      have cuts := run_cut space isError demand (boundedWork space depth root) depth root
      change cursor.answers ++ BoundedSearchPortfolio.pendingAnswers space cursor.frontier =
        (bounded space depth root).1 at occurrences
      change (cursor.cut || _) = _ at cuts
      have exactAnswers : cursor.answers = (bounded space depth root).1 := by
        simpa [empty, BoundedSearchPortfolio.pendingAnswers] using occurrences
      have actuallyCut : (bounded space depth root).2 = true := by
        simpa [cut] using cuts.symm
      rcases settled with enough | uncut
      · rw [exactAnswers] at insufficient
        omega
      · rw [uncut] at actuallyCut
        contradiction

theorem settled_execution_exists (space : Space S Reply) (isError : Reply → Bool)
    (demand depth : Nat) (root : S) (settled : Decides space isError demand depth root) :
    ∃ fuel, BoundedSearchPortfolio.ready (status isError demand (run space isError demand fuel depth root)) = true ∧
      BatchMeaning space root isError demand (batch isError demand (run space isError demand fuel depth root)) := by
  have ready := settled_run_ready space isError demand depth root settled
  exact ⟨boundedWork space depth root, ready,
    run_ready_meaning space isError demand _ depth root ready⟩

theorem a_success_has_a_settling_bound (space : Space S Reply) (isError : Reply → Bool)
    (root : S) {value : Reply} (answer : IsAnswer space root value) (success : isError value = false) :
    ∃ depth, Decides space isError 1 depth root := by
  obtain ⟨depth, reaches⟩ := answer
  have present := bounded_complete space reaches (Nat.le_refl depth)
  have inSuccess : value ∈ SuccessPriority.successes isError (bounded space depth root).1 := by
    simp [SuccessPriority.successes, present, success]
  exact ⟨depth, Or.inl (List.length_pos_of_mem inSuccess)⟩

def Valid (space : Space S Reply) (root : S) (iteration : Iteration S Reply) : Prop :=
  (iteration.cursor.answers ++ BoundedSearchPortfolio.pendingAnswers space iteration.cursor.frontier =
      (bounded space iteration.depth root).1) ∧
    (iteration.cursor.cut || BoundedSearchPortfolio.pendingCut space iteration.cursor.frontier) =
      (bounded space iteration.depth root).2

theorem begin_valid (space : Space S Reply) (root : S) (depth : Nat) :
    Valid space root (BoundedSearchPortfolio.beginIteration root depth) := by
  simp [Valid, BoundedSearchPortfolio.beginIteration, BoundedSearchPortfolio.start, Cursor.answers,
    BoundedSearchPortfolio.pendingAnswers, BoundedSearchPortfolio.pendingCut]

theorem tick_valid (space : Space S Reply) (isError : Reply → Bool) (root : S) (demand : Nat)
    (iteration : Iteration S Reply) (valid : Valid space root iteration) :
    Valid space root {iteration with cursor := tick space isError demand iteration.cursor} := by
  unfold Valid
  exact ⟨(by simpa [advance] using (advance_occurrences space isError demand 1 iteration.cursor).trans valid.1),
    (by simpa [advance] using (advance_cut space isError demand 1 iteration.cursor).trans valid.2)⟩

def engine (space : Space S Reply) (isError : Reply → Bool) (root : S) (demand : Nat) (E : Type w) :
    BoundedSearchPortfolio.Engine {iteration : Iteration S Reply // Valid space root iteration} Reply E where
  inspect iteration := status isError demand iteration.val.cursor
  batch iteration := batch isError demand iteration.val.cursor
  progress iteration :=
    (⟨{iteration.val with cursor := tick space isError demand iteration.val.cursor},
      tick_valid space isError root demand iteration.val iteration.property⟩, [])
  deepen iteration :=
    (⟨BoundedSearchPortfolio.nextIteration root iteration.val,
      begin_valid space root (iteration.val.depth + 1)⟩, [])

theorem engine_pure (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) : (engine space isError root demand E).Pure := by
  intro iteration
  exact ⟨rfl, rfl⟩

theorem engine_ready_law (space : Space S Reply) (isError : Reply → Bool) (root : S)
    (demand : Nat) (E : Type w) (iteration : {iteration : Iteration S Reply // Valid space root iteration})
    (ready : BoundedSearchPortfolio.ready ((engine space isError root demand E).inspect iteration) = true) :
    BatchMeaning space root isError demand ((engine space isError root demand E).batch iteration) :=
  cursor_ready_meaning space isError demand iteration.val.depth root iteration.val.cursor
    iteration.property.1 iteration.property.2 ready

theorem portfolio_publication_law (space : Space S Reply) (isError : Reply → Bool)
    (root : S) (demand : Nat) (E : Type w) (schedule : List BoundedSearchPortfolio.Origin)
    (portfolio : BoundedSearchPortfolio.Portfolio
      {iteration : Iteration S Reply // Valid space root iteration} Reply E)
    (uncommitted : portfolio.published = none) :
    ∀ origin answers,
      (BoundedSearchPortfolio.execute (engine space isError root demand E)
        (engine space isError root demand E) schedule portfolio).published = some (origin, answers) →
      BatchMeaning space root isError demand answers := by
  apply BoundedSearchPortfolio.execute_publication_law _ _ (BatchMeaning space root isError demand)
    (engine_ready_law space isError root demand E) (engine_ready_law space isError root demand E)
  intro origin answers impossible
  simp [uncommitted] at impossible

end Mettapedia.Machines.ObserverLicence.HEWitness
