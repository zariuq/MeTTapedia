import Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

/-!
# Private bounded answer batches and portfolio publication

A depth-bounded search is executed by a stack machine that retains both its
frontier and its private answer occurrences across work quanta. Its reference
is the independently defined recursive `IterativeDeepeningWitness.bounded`.
The invariant preserves the complete ordered occurrence list, not just support.

Reaching the demand bound and proving exhaustion are different terminal states.
A cut-off iteration is neither: iterative deepening must discard its private
batch before starting a greater bound. A portfolio publishes one strategy's
batch, never a mixture of rediscovered occurrences from several strategies.

Search expansion is pure in this model. Native admission must exclude visible
effects before speculative execution, including effectful host work and raises.
Pure aggregates additionally need cutoff-aware semantics: an enclosing
first-answer observer cannot repair a hidden incomplete collection. The native
derivation-depth meter, allocation and ownership remain implementation
correspondence obligations; one model step is not a time bound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BoundedSearchPortfolio

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness

universe u v b
variable {S : Type u} {A : Type v}

structure Task (S : Type u) where
  state : S
  depth : Nat
deriving Repr, DecidableEq

structure Cursor (S : Type u) (A : Type v) where
  frontier : List (Task S)
  reversed : List A
  cut : Bool
  work : Nat
deriving Repr, DecidableEq

def Cursor.answers (cursor : Cursor S A) : List A := cursor.reversed.reverse

def start (root : S) (depth : Nat) : Cursor S A :=
  ⟨[⟨root, depth⟩], [], false, 0⟩

def pendingAnswers (space : Space S A) (tasks : List (Task S)) : List A :=
  tasks.flatMap fun task => (bounded space task.depth task.state).1

def pendingCut (space : Space S A) (tasks : List (Task S)) : Bool :=
  tasks.any fun task => (bounded space task.depth task.state).2

def children (states : List S) (depth : Nat) : List (Task S) :=
  states.map fun state => ⟨state, depth⟩

inductive Status where
  | paused
  | full
  | exhausted
  | cutoff
deriving Repr, DecidableEq

def status (demand : Nat) (cursor : Cursor S A) : Status :=
  if demand ≤ cursor.reversed.length then .full
  else if cursor.frontier.isEmpty then
    if cursor.cut then .cutoff else .exhausted
  else .paused

/-- One actual stack expansion. Answers append by occurrence; no equality test
or set insertion is involved. -/
def expandOne (space : Space S A) (cursor : Cursor S A) : Cursor S A :=
  match cursor.frontier with
  | [] => cursor
  | task :: rest =>
      match space.expand task.state with
      | .answer value =>
          { cursor with
            frontier := rest
            reversed := value :: cursor.reversed
            work := cursor.work + 1 }
      | .branch states =>
          match task.depth with
          | 0 => { cursor with
                    frontier := rest
                    cut := cursor.cut || !states.isEmpty
                    work := cursor.work + 1 }
          | depth + 1 =>
              { cursor with
                frontier := children states depth ++ rest
                work := cursor.work + 1 }

def tick (space : Space S A) (demand : Nat) (cursor : Cursor S A) : Cursor S A :=
  if status demand cursor = .paused then expandOne space cursor else cursor

def advance (space : Space S A) (demand : Nat) : Nat → Cursor S A → Cursor S A
  | 0, cursor => cursor
  | fuel + 1, cursor => advance space demand fuel (tick space demand cursor)

def run (space : Space S A) (demand fuel depth : Nat) (root : S) : Cursor S A :=
  advance space demand fuel (start root depth)

/-- Expanding the target stack preserves the independently specified recursive
answer list, including every duplicate occurrence and its position. -/
theorem expandOne_answers (space : Space S A) (cursor : Cursor S A) :
    (expandOne space cursor).answers ++ pendingAnswers space (expandOne space cursor).frontier =
      cursor.answers ++ pendingAnswers space cursor.frontier := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨state, depth⟩
      cases expansion : space.expand state with
      | answer value =>
          simp [expandOne, expansion, Cursor.answers, pendingAnswers,
            bounded_answer space expansion, List.reverse_cons, List.append_assoc]
      | branch states =>
          cases depth with
          | zero =>
              simp [expandOne, expansion, Cursor.answers, pendingAnswers, bounded]
          | succ depth =>
              simp [expandOne, expansion, Cursor.answers, pendingAnswers, children,
                bounded, List.flatMap_append, List.flatMap_map]

theorem expandOne_cut (space : Space S A) (cursor : Cursor S A) :
    ((expandOne space cursor).cut || pendingCut space (expandOne space cursor).frontier) =
      (cursor.cut || pendingCut space cursor.frontier) := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => rfl
  | cons task rest =>
      rcases task with ⟨state, depth⟩
      cases expansion : space.expand state with
      | answer value =>
          simp [expandOne, expansion, pendingCut, bounded_answer space expansion]
      | branch states =>
          cases depth with
          | zero => simp [expandOne, expansion, pendingCut, bounded, Bool.or_assoc]
          | succ depth =>
              simp [expandOne, expansion, pendingCut, children, bounded, List.any_append,
                List.any_map, Function.comp_def]

theorem advance_answers (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A) :
    (advance space demand fuel cursor).answers ++
        pendingAnswers space (advance space demand fuel cursor).frontier =
      cursor.answers ++ pendingAnswers space cursor.frontier := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      rw [advance, ih]
      unfold tick
      split
      · exact expandOne_answers space cursor
      · rfl

theorem advance_cut (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A) :
    ((advance space demand fuel cursor).cut ||
        pendingCut space (advance space demand fuel cursor).frontier) =
      (cursor.cut || pendingCut space cursor.frontier) := by
  induction fuel generalizing cursor with
  | zero => rfl
  | succ fuel ih =>
      rw [advance, ih]
      unfold tick
      split
      · exact expandOne_cut space cursor
      · rfl

/-- Resumption continues the actual frontier and private batch. -/
theorem advance_add (space : Space S A) (demand first second : Nat)
    (cursor : Cursor S A) :
    advance space demand (first + second) cursor =
      advance space demand second (advance space demand first cursor) := by
  induction first generalizing cursor with
  | zero => simp [advance]
  | succ first ih =>
      simp only [Nat.succ_add, advance]
      exact ih (tick space demand cursor)

theorem run_occurrences (space : Space S A) (demand fuel depth : Nat) (root : S) :
    (run space demand fuel depth root).answers ++
        pendingAnswers space (run space demand fuel depth root).frontier =
      (bounded space depth root).1 := by
  simpa [run, start, Cursor.answers, pendingAnswers] using
    advance_answers space demand fuel (start root depth)

theorem run_cut (space : Space S A) (demand fuel depth : Nat) (root : S) :
    ((run space demand fuel depth root).cut ||
        pendingCut space (run space demand fuel depth root).frontier) =
      (bounded space depth root).2 := by
  simpa [run, start, pendingCut] using
    advance_cut space demand fuel (start root depth)

theorem run_sound (space : Space S A) (demand fuel depth : Nat) (root : S)
    {value : A} (member : value ∈ (run space demand fuel depth root).answers) :
    IsAnswer space root value := by
  have whole : value ∈ (bounded space depth root).1 := by
    rw [← run_occurrences space demand fuel depth root]
    exact List.mem_append_left _ member
  obtain ⟨distance, _, reaches⟩ := bounded_sound space depth whole
  exact ⟨distance, reaches⟩

theorem paused_below_bound (demand : Nat) (cursor : Cursor S A)
    (paused : status demand cursor = .paused) : cursor.reversed.length < demand := by
  by_contra notLess
  have enough : demand ≤ cursor.reversed.length := by omega
  simp [status, enough] at paused

theorem expandOne_length (space : Space S A) (cursor : Cursor S A) :
    cursor.reversed.length ≤ (expandOne space cursor).reversed.length ∧
      (expandOne space cursor).reversed.length ≤ cursor.reversed.length + 1 := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => simp [expandOne]
  | cons task rest =>
      cases expansion : space.expand task.state with
      | answer value => simp [expandOne, expansion]
      | branch states => cases depthEq : task.depth <;> simp [expandOne, expansion, depthEq]

theorem advance_bounded (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A)
    (boundedBatch : cursor.reversed.length ≤ demand) :
    (advance space demand fuel cursor).reversed.length ≤ demand := by
  induction fuel generalizing cursor with
  | zero => exact boundedBatch
  | succ fuel ih =>
      apply ih
      unfold tick
      split_ifs with paused
      · have below := paused_below_bound demand cursor paused
        have growth := (expandOne_length space cursor).2
        omega
      · exact boundedBatch

theorem run_bounded (space : Space S A) (demand fuel depth : Nat) (root : S) :
    (run space demand fuel depth root).answers.length ≤ demand := by
  simpa [run, Cursor.answers] using
    advance_bounded space demand fuel (start root depth) (by simp [start])

theorem tick_work (space : Space S A) (demand : Nat) (cursor : Cursor S A) :
    cursor.work ≤ (tick space demand cursor).work ∧
      (tick space demand cursor).work ≤ cursor.work + 1 := by
  unfold tick
  split
  · rcases cursor with ⟨frontier, reversed, cut, work⟩
    cases frontier with
    | nil => simp [expandOne]
    | cons task rest =>
        cases expansion : space.expand task.state with
        | answer value => simp [expandOne, expansion]
        | branch states => cases depthEq : task.depth <;> simp [expandOne, expansion, depthEq]
  · omega

theorem advance_work (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A) :
    cursor.work ≤ (advance space demand fuel cursor).work ∧
      (advance space demand fuel cursor).work ≤ cursor.work + fuel := by
  induction fuel generalizing cursor with
  | zero => simp [advance]
  | succ fuel ih =>
      have first := tick_work space demand cursor
      have rest := ih (tick space demand cursor)
      simp only [advance]
      omega

theorem full_length (demand : Nat) (cursor : Cursor S A)
    (limited : cursor.answers.length ≤ demand) (full : status demand cursor = .full) :
    cursor.answers.length = demand := by
  have enough : demand ≤ cursor.reversed.length := by
    by_contra notEnough
    simp [status, notEnough] at full
    split at full <;> simp_all
    split at full <;> contradiction
  simpa [Cursor.answers] using Nat.le_antisymm limited (by simpa [Cursor.answers] using enough)

theorem exhausted_shape (demand : Nat) (cursor : Cursor S A)
    (done : status demand cursor = .exhausted) :
    cursor.frontier = [] ∧ cursor.cut = false ∧ cursor.answers.length < demand := by
  unfold status at done
  split at done
  · contradiction
  · rename_i below
    split at done
    · rename_i empty
      split at done
      · contradiction
      · simp_all [List.isEmpty_iff, Cursor.answers]
    · contradiction

/-- Genuine exhaustion returns every bounded answer, and the bounded search
has cut no branch. A nonempty short batch can thus be a complete result. -/
theorem run_exhausted_exact (space : Space S A) (demand fuel depth : Nat) (root : S)
    (done : status demand (run space demand fuel depth root) = .exhausted) :
    (run space demand fuel depth root).answers = (bounded space depth root).1 ∧
      (bounded space depth root).2 = false := by
  obtain ⟨empty, uncut, _⟩ := exhausted_shape demand _ done
  have occurrences := run_occurrences space demand fuel depth root
  have cuts := run_cut space demand fuel depth root
  simp [empty, pendingAnswers] at occurrences
  simp [empty, uncut, pendingCut] at cuts
  exact ⟨occurrences, cuts⟩

theorem run_exhausted_complete (space : Space S A) (demand fuel depth : Nat) (root : S)
    (done : status demand (run space demand fuel depth root) = .exhausted) :
    ∀ value, IsAnswer space root value → value ∈ (run space demand fuel depth root).answers := by
  obtain ⟨exactAnswers, uncut⟩ := run_exhausted_exact space demand fuel depth root done
  rintro value ⟨distance, reaches⟩
  rw [exactAnswers]
  exact bounded_exhaustive space reaches uncut

theorem run_full_prefix (space : Space S A) (demand fuel depth : Nat) (root : S)
    (full : status demand (run space demand fuel depth root) = .full) :
    (run space demand fuel depth root).answers =
      (bounded space depth root).1.take demand := by
  have size := full_length demand _ (run_bounded space demand fuel depth root) full
  have same := congrArg (List.take (run space demand fuel depth root).answers.length)
    (run_occurrences space demand fuel depth root)
  rw [List.take_left] at same
  simpa only [size] using same

/-- Demand zero performs no expansion, even when arbitrarily much fuel is
offered. The computation behind the initial task is never inspected. -/
theorem advance_zero_demand (space : Space S A) (fuel : Nat) (cursor : Cursor S A) :
    advance space 0 fuel cursor = cursor := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [advance, tick, status] using ih

def pendingWork (space : Space S A) (tasks : List (Task S)) : Nat :=
  (tasks.map fun task => boundedWork space task.depth task.state).sum

theorem pendingWork_positive (space : Space S A) (tasks : List (Task S))
    (nonempty : tasks ≠ []) : 0 < pendingWork space tasks := by
  cases tasks with
  | nil => contradiction
  | cons task rest =>
      have positive := boundedWork_pos space task.depth task.state
      simp only [pendingWork, List.map_cons, List.sum_cons]
      omega

theorem expandOne_pendingWork (space : Space S A) (cursor : Cursor S A)
    (nonempty : cursor.frontier ≠ []) :
    pendingWork space (expandOne space cursor).frontier + 1 =
      pendingWork space cursor.frontier := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => contradiction
  | cons task rest =>
      rcases task with ⟨state, depth⟩
      cases depth <;> cases expansion : space.expand state <;>
        simp [expandOne, expansion, pendingWork, children, boundedWork,
          List.sum_append, List.map_map, Function.comp_def] <;>
          simp [Nat.add_assoc, Nat.add_comm]

theorem advance_terminal (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A)
    (done : status demand cursor ≠ .paused) : advance space demand fuel cursor = cursor := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [advance, tick, done] using ih

theorem paused_frontier_nonempty (demand : Nat) (cursor : Cursor S A)
    (paused : status demand cursor = .paused) : cursor.frontier ≠ [] := by
  intro empty
  simp [status, empty] at paused
  split at paused <;> simp_all
  split at paused <;> contradiction

/-- Existing recursive work counting also bounds the operational stack run.
The bound can be conservative when the requested batch fills early. -/
theorem advance_finishes (space : Space S A) (demand fuel : Nat) (cursor : Cursor S A)
    (enough : pendingWork space cursor.frontier ≤ fuel) :
    status demand (advance space demand fuel cursor) ≠ .paused := by
  induction fuel generalizing cursor with
  | zero =>
      intro paused
      have nonempty := paused_frontier_nonempty demand cursor paused
      have positive := pendingWork_positive space cursor.frontier nonempty
      omega
  | succ fuel ih =>
      by_cases paused : status demand cursor = .paused
      · have decrease := expandOne_pendingWork space cursor
          (paused_frontier_nonempty demand cursor paused)
        simp only [advance, tick, paused, ↓reduceIte]
        apply ih
        omega
      · rw [advance_terminal space demand (fuel + 1) cursor paused]
        exact paused

theorem run_finishes (space : Space S A) (demand depth : Nat) (root : S) :
    status demand (run space demand (boundedWork space depth root) depth root) ≠ .paused := by
  apply advance_finishes
  simp [start, pendingWork]

/-- Observers of the complete collection require exhaustion. A full requested
prefix is sufficient for bounded selection, but not for counting, absence, or
an enclosing handler that treats its private collection as complete. -/
def observeComplete {B : Type b} (observe : List A → B) (state : Status)
    (answers : List A) : Option B :=
  match state with
  | .exhausted => some (observe answers)
  | .paused | .full | .cutoff => none

theorem observeComplete_requires_exhaustion {B : Type b} (observe : List A → B)
    (state : Status) (answers : List A) (value : B)
    (published : observeComplete observe state answers = some value) :
    state = .exhausted ∧ value = observe answers := by
  cases state <;> simp_all [observeComplete]

theorem run_observeComplete_sound {B : Type b} (space : Space S A)
    (observe : List A → B) (demand fuel depth : Nat) (root : S) (value : B)
    (published : observeComplete observe (status demand (run space demand fuel depth root))
      (run space demand fuel depth root).answers = some value) :
    value = observe (bounded space depth root).1 ∧
      (bounded space depth root).2 = false := by
  obtain ⟨exhausted, output⟩ := observeComplete_requires_exhaustion _ _ _ _ published
  obtain ⟨exactAnswers, uncut⟩ := run_exhausted_exact space demand fuel depth root exhausted
  exact ⟨output.trans (congrArg observe exactAnswers), uncut⟩

structure Iteration (S : Type u) (A : Type v) where
  depth : Nat
  cursor : Cursor S A
deriving Repr, DecidableEq

def beginIteration (root : S) (depth : Nat) : Iteration S A :=
  ⟨depth, start root depth⟩

def nextIteration (root : S) (previous : Iteration S A) : Iteration S A :=
  beginIteration root (previous.depth + 1)

/-- This is the semantic invariant of an iteration, not a specification of
the target by running the reference implementation. -/
def Iteration.Valid (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) : Prop :=
  (iteration.cursor.answers ++ pendingAnswers space iteration.cursor.frontier =
      (bounded space iteration.depth root).1) ∧
  ((iteration.cursor.cut || pendingCut space iteration.cursor.frontier) =
      (bounded space iteration.depth root).2) ∧
  iteration.cursor.reversed.length ≤ demand

theorem beginIteration_valid (space : Space S A) (root : S) (demand depth : Nat) :
    (beginIteration root depth).Valid space root demand := by
  simp [Iteration.Valid, beginIteration, start, Cursor.answers, pendingAnswers, pendingCut]

theorem iteration_tick_valid (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (valid : iteration.Valid space root demand) :
    ({ iteration with cursor := tick space demand iteration.cursor }).Valid space root demand := by
  refine ⟨?_, ?_, ?_⟩
  · have law := advance_answers space demand 1 iteration.cursor
    simpa [advance] using law.trans valid.1
  · have law := advance_cut space demand 1 iteration.cursor
    simpa [advance] using law.trans valid.2.1
  · simpa [advance] using advance_bounded space demand 1 iteration.cursor valid.2.2

theorem nextIteration_valid (space : Space S A) (root : S) (demand : Nat)
    (previous : Iteration S A) :
    (nextIteration root previous).Valid space root demand :=
  beginIteration_valid space root demand (previous.depth + 1)

theorem nextIteration_discards (root : S) (previous : Iteration S A) :
    (nextIteration root previous).cursor.answers = [] ∧
      (nextIteration root previous).cursor.cut = false ∧
      (nextIteration root previous).depth = previous.depth + 1 := by
  simp [nextIteration, beginIteration, start, Cursor.answers]

def ready : Status → Bool
  | .full | .exhausted => true
  | .paused | .cutoff => false

/-- A batch belongs to one bounded traversal, with its occurrences unchanged.
A short published batch must be complete and uncut. The traversal depth is
part of this witness; it is never erased by unioning candidate batches. -/
def BatchMeaning (space : Space S A) (root : S) (demand : Nat) (batch : List A) : Prop :=
  ∃ depth suffix,
    batch ++ suffix = (bounded space depth root).1 ∧
    batch.length ≤ demand ∧
    (batch.length = demand ∨
      (batch = (bounded space depth root).1 ∧ (bounded space depth root).2 = false))

theorem iteration_ready_meaning (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (valid : iteration.Valid space root demand)
    (finished : ready (status demand iteration.cursor) = true) :
    BatchMeaning space root demand iteration.cursor.answers := by
  refine ⟨iteration.depth, pendingAnswers space iteration.cursor.frontier,
    valid.1, ?_, ?_⟩
  · simpa [Cursor.answers] using valid.2.2
  · cases outcome : status demand iteration.cursor with
    | paused => simp [outcome, ready] at finished
    | cutoff => simp [outcome, ready] at finished
    | full =>
        exact Or.inl (full_length demand iteration.cursor
          (by simpa [Cursor.answers] using valid.2.2) outcome)
    | exhausted =>
        obtain ⟨empty, uncut, _⟩ := exhausted_shape demand iteration.cursor outcome
        refine Or.inr ⟨?_, ?_⟩
        · simpa [empty, pendingAnswers] using valid.1
        · have := valid.2.1
          simpa [empty, uncut, pendingCut] using this.symm

theorem batchMeaning_sound (space : Space S A) (root : S) (demand : Nat)
    (batch : List A) (meaning : BatchMeaning space root demand batch) :
    batch.length ≤ demand ∧ (∀ value ∈ batch, IsAnswer space root value) := by
  obtain ⟨depth, suffix, occurrences, limited, _⟩ := meaning
  refine ⟨limited, ?_⟩
  intro value member
  have memberWhole : value ∈ (bounded space depth root).1 := by
    rw [← occurrences]
    exact List.mem_append_left suffix member
  obtain ⟨distance, _, reaches⟩ := bounded_sound space depth memberWhole
  exact ⟨distance, reaches⟩

/-! ## A common-budget portfolio with a single publication

The coordinator is independent of a strategy's physical control layout. Both
engines use the same abstract state type (a tagged union can supply different
representations). Effect receipts are included so that purity is an actual
admission obligation, rather than an implicit assertion about speculation.
-/

universe w t

structure Engine (T : Type t) (A : Type v) (E : Type w) where
  inspect : T → Status
  batch : T → List A
  progress : T → T × List E
  deepen : T → T × List E

def Engine.Pure {T : Type t} {E : Type w} (engine : Engine T A E) : Prop :=
  ∀ state, (engine.progress state).2 = [] ∧ (engine.deepen state).2 = []

inductive Origin where
  | left
  | right
deriving Repr, DecidableEq

structure Portfolio (T : Type t) (A : Type v) (E : Type w) where
  left : T
  right : T
  remaining : Nat
  spent : Nat
  effects : List E
  published : Option (Origin × List A)
deriving Repr, DecidableEq

def Portfolio.privateState {T : Type t} {E : Type w}
    (portfolio : Portfolio T A E) : Origin → T
  | .left => portfolio.left
  | .right => portfolio.right

def Portfolio.replace {T : Type t} {E : Type w}
    (portfolio : Portfolio T A E) (origin : Origin) (state : T) : Portfolio T A E :=
  match origin with
  | .left => { portfolio with left := state }
  | .right => { portfolio with right := state }

/-- Both progress and an IDD depth reset debit the same account. Private
iteration work counters may reset; the portfolio's spending never does. -/
def pay {T : Type t} {E : Type w} (origin : Origin) (result : Unit → T × List E)
    (portfolio : Portfolio T A E) : Portfolio T A E :=
  if portfolio.remaining = 0 then portfolio else
    let moved := result ()
    { portfolio.replace origin moved.1 with
      remaining := portfolio.remaining - 1
      spent := portfolio.spent + 1
      effects := portfolio.effects ++ moved.2 }

/-- One scheduled service. A ready batch is copied once to the publication;
running and cut-off batches remain private. -/
def serve {T : Type t} {E : Type w} (engine : Engine T A E) (origin : Origin)
    (portfolio : Portfolio T A E) : Portfolio T A E :=
  if portfolio.published.isSome then portfolio else
    let state := portfolio.privateState origin
    match engine.inspect state with
    | .full | .exhausted =>
        { portfolio with published := some (origin, engine.batch state) }
    | .paused => pay origin (fun _ => engine.progress state) portfolio
    | .cutoff => pay origin (fun _ => engine.deepen state) portfolio

def turn {T : Type t} {E : Type w} (left right : Engine T A E)
    (origin : Origin) (portfolio : Portfolio T A E) : Portfolio T A E :=
  match origin with
  | .left => serve left origin portfolio
  | .right => serve right origin portfolio

def execute {T : Type t} {E : Type w} (left right : Engine T A E) :
    List Origin → Portfolio T A E → Portfolio T A E
  | [], portfolio => portfolio
  | origin :: rest, portfolio => execute left right rest (turn left right origin portfolio)

theorem execute_append {T : Type t} {E : Type w} (left right : Engine T A E)
    (first second : List Origin) (portfolio : Portfolio T A E) :
    execute left right (first ++ second) portfolio =
      execute left right second (execute left right first portfolio) := by
  induction first generalizing portfolio with
  | nil => rfl
  | cons origin rest ih => exact ih (turn left right origin portfolio)

theorem pay_budget {T : Type t} {E : Type w} (origin : Origin) (result : Unit → T × List E)
    (portfolio : Portfolio T A E) :
    (pay origin result portfolio).remaining + (pay origin result portfolio).spent =
      portfolio.remaining + portfolio.spent := by
  unfold pay
  split_ifs with empty
  · rfl
  · simp only
    omega

theorem serve_budget {T : Type t} {E : Type w} (engine : Engine T A E) (origin : Origin)
    (portfolio : Portfolio T A E) :
    (serve engine origin portfolio).remaining + (serve engine origin portfolio).spent =
      portfolio.remaining + portfolio.spent := by
  unfold serve
  split
  · rfl
  · dsimp only
    cases engine.inspect (portfolio.privateState origin) with
    | full => rfl
    | exhausted => rfl
    | paused => exact pay_budget origin _ portfolio
    | cutoff => exact pay_budget origin _ portfolio

theorem execute_budget {T : Type t} {E : Type w} (left right : Engine T A E)
    (schedule : List Origin) (portfolio : Portfolio T A E) :
    (execute left right schedule portfolio).remaining +
        (execute left right schedule portfolio).spent =
      portfolio.remaining + portfolio.spent := by
  induction schedule generalizing portfolio with
  | nil => rfl
  | cons origin rest ih =>
      rw [execute, ih]
      cases origin <;> exact serve_budget _ _ portfolio

theorem execute_spent_le {T : Type t} {E : Type w} (left right : Engine T A E)
    (schedule : List Origin) (portfolio : Portfolio T A E) :
    (execute left right schedule portfolio).spent ≤ portfolio.remaining + portfolio.spent := by
  have := execute_budget left right schedule portfolio
  omega

theorem serve_after_publication {T : Type t} {E : Type w} (engine : Engine T A E)
    (origin : Origin) (portfolio : Portfolio T A E) (publication : Origin × List A)
    (committed : portfolio.published = some publication) :
    serve engine origin portfolio = portfolio := by simp [serve, committed]

/-- Publication freezes both private strategies as well as the public batch.
No subsequent schedule can append rediscovered occurrences or perform effects. -/
theorem execute_after_publication {T : Type t} {E : Type w} (left right : Engine T A E)
    (schedule : List Origin) (portfolio : Portfolio T A E) (publication : Origin × List A)
    (committed : portfolio.published = some publication) :
    execute left right schedule portfolio = portfolio := by
  induction schedule with
  | nil => rfl
  | cons origin rest ih =>
      simp only [execute, turn]
      cases origin <;> simp only [serve_after_publication _ _ portfolio publication committed, ih]

theorem pay_no_effects {T : Type t} {E : Type w} (origin : Origin) (result : Unit → T × List E)
    (portfolio : Portfolio T A E) (pure : (result ()).2 = []) :
    (pay origin result portfolio).effects = portfolio.effects := by
  unfold pay
  split <;> simp [pure]

theorem serve_no_effects {T : Type t} {E : Type w} (engine : Engine T A E)
    (pure : engine.Pure) (origin : Origin) (portfolio : Portfolio T A E) :
    (serve engine origin portfolio).effects = portfolio.effects := by
  unfold serve
  split
  · rfl
  · dsimp only
    cases engine.inspect (portfolio.privateState origin) with
    | full => rfl
    | exhausted => rfl
    | paused => exact pay_no_effects origin _ portfolio (pure _).1
    | cutoff => exact pay_no_effects origin _ portfolio (pure _).2

theorem execute_no_effects {T : Type t} {E : Type w} (left right : Engine T A E)
    (pureLeft : left.Pure) (pureRight : right.Pure)
    (schedule : List Origin) (portfolio : Portfolio T A E) :
    (execute left right schedule portfolio).effects = portfolio.effects := by
  induction schedule generalizing portfolio with
  | nil => rfl
  | cons origin rest ih =>
      rw [execute, ih]
      cases origin
      · exact serve_no_effects left pureLeft .left portfolio
      · exact serve_no_effects right pureRight .right portfolio

theorem pay_preserves_publication {T : Type t} {E : Type w} (origin : Origin)
    (result : Unit → T × List E) (portfolio : Portfolio T A E) :
    (pay origin result portfolio).published = portfolio.published := by
  unfold pay
  split
  · rfl
  · cases origin <;> rfl

/-- A newly published result is exactly the private batch of the selected
strategy at that instant, and that strategy was full or genuinely exhausted. -/
theorem serve_publication_source {T : Type t} {E : Type w} (engine : Engine T A E)
    (origin : Origin) (portfolio : Portfolio T A E)
    (uncommitted : portfolio.published = none) (publication : Origin × List A)
    (published : (serve engine origin portfolio).published = some publication) :
    publication = (origin, engine.batch (portfolio.privateState origin)) ∧
      ready (engine.inspect (portfolio.privateState origin)) = true := by
  simp only [serve, uncommitted, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at published
  cases outcome : engine.inspect (portfolio.privateState origin) with
  | full => simpa [outcome, ready] using published.symm
  | exhausted => simpa [outcome, ready] using published.symm
  | paused => simp [outcome, pay_preserves_publication, uncommitted] at published
  | cutoff => simp [outcome, pay_preserves_publication, uncommitted] at published

/-- A closed publication predicate transfers from both engines through every
schedule. This is independent of which engine wins or how work is interleaved. -/
theorem execute_publication_law {T : Type t} {E : Type w} (left right : Engine T A E)
    (law : List A → Prop)
    (leftLaw : ∀ state, ready (left.inspect state) = true → law (left.batch state))
    (rightLaw : ∀ state, ready (right.inspect state) = true → law (right.batch state))
    (schedule : List Origin) (portfolio : Portfolio T A E)
    (previous : ∀ source batch, portfolio.published = some (source, batch) → law batch) :
    ∀ source batch, (execute left right schedule portfolio).published = some (source, batch) →
      law batch := by
  induction schedule generalizing portfolio with
  | nil => exact previous
  | cons origin rest ih =>
      apply ih
      intro source batch published
      cases old : portfolio.published with
      | some publication =>
          have same : turn left right origin portfolio = portfolio := by
            cases origin <;> exact serve_after_publication _ _ portfolio publication old
          rw [same] at published
          exact previous source batch published
      | none =>
          cases origin with
          | left =>
              obtain ⟨same, finished⟩ := serve_publication_source left .left portfolio old
                (source, batch) published
              have payload := congrArg Prod.snd same
              dsimp only at payload
              rw [payload]
              exact leftLaw _ finished
          | right =>
              obtain ⟨same, finished⟩ := serve_publication_source right .right portfolio old
                (source, batch) published
              have payload := congrArg Prod.snd same
              dsimp only at payload
              rw [payload]
              exact rightLaw _ finished

/-- This concrete engine carries the established stack invariant as erased
proof evidence. Its executable state and transitions are the independent
stack machine above, not calls to the recursive reference search. -/
def boundedEngine (space : Space S A) (root : S) (demand : Nat) (E : Type w) :
    Engine { iteration : Iteration S A // iteration.Valid space root demand } A E where
  inspect iteration := status demand iteration.val.cursor
  batch iteration := iteration.val.cursor.answers
  progress iteration :=
    (⟨{ iteration.val with cursor := tick space demand iteration.val.cursor },
      iteration_tick_valid space root demand iteration.val iteration.property⟩, [])
  deepen iteration :=
    (⟨nextIteration root iteration.val,
      nextIteration_valid space root demand iteration.val⟩, [])

theorem boundedEngine_pure (space : Space S A) (root : S) (demand : Nat) (E : Type w) :
    (boundedEngine space root demand E).Pure := by intro state; exact ⟨rfl, rfl⟩

theorem boundedEngine_law (space : Space S A) (root : S) (demand : Nat) (E : Type w)
    (state : { iteration : Iteration S A // iteration.Valid space root demand })
    (finished : ready ((boundedEngine space root demand E).inspect state) = true) :
    BatchMeaning space root demand ((boundedEngine space root demand E).batch state) :=
  iteration_ready_meaning space root demand state.val state.property finished

/-- Concrete connection of the coordinator to the independently verified
bounded-search stack, including any number of discarded IDD iterations. -/
theorem boundedPortfolio_law (space : Space S A) (root : S) (demand : Nat) (E : Type w)
    (schedule : List Origin)
    (portfolio : Portfolio { iteration : Iteration S A // iteration.Valid space root demand } A E)
    (uncommitted : portfolio.published = none) :
    ∀ source batch,
      (execute (boundedEngine space root demand E) (boundedEngine space root demand E)
        schedule portfolio).published = some (source, batch) →
      BatchMeaning space root demand batch := by
  apply execute_publication_law _ _ (BatchMeaning space root demand)
    (boundedEngine_law space root demand E) (boundedEngine_law space root demand E)
  intro source batch impossible
  simp [uncommitted] at impossible

namespace Controls

set_option maxRecDepth 2048

def fan (values : List Nat) : Space (Option Nat) Nat where
  expand
    | none => .branch (values.map some)
    | some value => .answer value

theorem zero_no_expansion :
    (run (fan [1, 2, 3, 4, 5, 6]) 0 10 1 none).answers = [] ∧
      (run (fan [1, 2, 3, 4, 5, 6]) 0 10 1 none).work = 0 := by decide

theorem one_stops_at_first_occurrence :
    (run (fan [1, 2, 3, 4, 5, 6]) 1 10 1 none).answers = [1] ∧
      (run (fan [1, 2, 3, 4, 5, 6]) 1 10 1 none).work = 2 := by decide

theorem five_without_sixth_probe :
    (run (fan [1, 2, 3, 4, 5, 6]) 5 10 1 none).answers = [1, 2, 3, 4, 5] ∧
      (run (fan [1, 2, 3, 4, 5, 6]) 5 10 1 none).work = 6 ∧
      status 5 (run (fan [1, 2, 3, 4, 5, 6]) 5 10 1 none) = .full := by decide

theorem fewer_is_exhaustion :
    (run (fan [3, 4]) 5 10 1 none).answers = [3, 4] ∧
      status 5 (run (fan [3, 4]) 5 10 1 none) = .exhausted := by decide

theorem equal_values_are_distinct_occurrences :
    (run (fan [7, 7, 8]) 5 10 1 none).answers = [7, 7, 8] ∧
      ((run (fan [7, 7, 8]) 5 10 1 none).answers.count 7) = 2 := by decide

theorem resume_keeps_private_prefix :
    (advance (fan [1, 2, 3, 4, 5, 6]) 5 3
      (run (fan [1, 2, 3, 4, 5, 6]) 5 3 1 none)).answers = [1, 2, 3, 4, 5] ∧
      (advance (fan [1, 2, 3, 4, 5, 6]) 5 3
        (run (fan [1, 2, 3, 4, 5, 6]) 5 3 1 none)).work = 6 := by decide

def uneven : Space Nat Nat where
  expand
    | 0 => .branch [1, 2]
    | 1 => .answer 7
    | 2 => .branch [3]
    | 3 => .answer 9
    | _ => .branch []

theorem cutoff_is_not_exhaustion :
    (run uneven 5 10 1 0).answers = [7] ∧
      status 5 (run uneven 5 10 1 0) = .cutoff ∧
      (run uneven 5 10 2 0).answers = [7, 9] ∧
      status 5 (run uneven 5 10 2 0) = .exhausted := by decide

theorem empty_cutoff_does_not_prove_failure :
    (run (fan [7]) 5 10 0 none).answers = [] ∧
      status 5 (run (fan [7]) 5 10 0 none) = .cutoff ∧
      IsAnswer (fan [7]) none 7 := by
  refine ⟨by decide, by decide, 1, ?_⟩
  exact .branch (c := some 7) rfl (by simp) (.answer rfl)

/-- The same pure count changes when an incomplete inner collection is silently
treated as complete. The guarded observer retains the missing-answer condition. -/
theorem cutoff_changes_count :
    (run (fan [7]) 5 10 0 none).answers.length = 0 ∧
      (run (fan [7]) 5 10 1 none).answers.length = 1 ∧
      observeComplete List.length (status 5 (run (fan [7]) 5 10 0 none))
        (run (fan [7]) 5 10 0 none).answers = none ∧
      observeComplete List.length (status 5 (run (fan [7]) 5 10 1 none))
        (run (fan [7]) 5 10 1 none).answers = some 1 := by decide

theorem cutoff_changes_absence :
    (run (fan [7]) 5 10 0 none).answers.isEmpty = true ∧
      (run (fan [7]) 5 10 1 none).answers.isEmpty = false ∧
      observeComplete List.isEmpty (status 5 (run (fan [7]) 5 10 0 none))
        (run (fan [7]) 5 10 0 none).answers = none := by decide

theorem full_prefix_does_not_license_count :
    status 1 (run (fan [1, 2]) 1 10 1 none) = .full ∧
      (run (fan [1, 2]) 1 10 1 none).answers.length = 1 ∧
      (bounded (fan [1, 2]) 1 none).1.length = 2 ∧
      observeComplete List.length (status 1 (run (fan [1, 2]) 1 10 1 none))
        (run (fan [1, 2]) 1 10 1 none).answers = none := by decide

def opaqueCount (values : List Nat) : Space Unit Nat where
  expand _ := .answer values.length

/-- After an opaque aggregate erases an inner cutoff, an outer first-answer
observer cannot reconstruct it. Purity alone does not justify that erasure. -/
theorem outer_once_cannot_recover_inner_cutoff :
    (run (opaqueCount (run (fan [7]) 5 10 0 none).answers) 1 1 0 ()).answers = [0] ∧
      status 1 (run (opaqueCount (run (fan [7]) 5 10 0 none).answers) 1 1 0 ()) = .full ∧
      (run (opaqueCount (run (fan [7]) 5 10 1 none).answers) 1 1 0 ()).answers = [1] := by decide

/-- Reusing the shallow occurrence repeats the same derivation; filtering
equal payloads would also incorrectly erase legitimate duplicate derivations. -/
theorem retaining_old_idd_batch_duplicates :
    (run uneven 5 10 1 0).answers ++ (run uneven 5 10 2 0).answers = [7, 7, 9] ∧
      (run uneven 5 10 1 0).answers ++ (run uneven 5 10 2 0).answers ≠
        (bounded uneven 2 0).1 := by decide

theorem mixing_strategy_prefixes_duplicates :
    ([0, 1] : List Nat).take 1 ++ ([0, 1] : List Nat).take 1 = [0, 0] ∧
      (([0, 1] : List Nat).take 1 ++ ([0, 1] : List Nat).take 1).count 0 >
        ([0, 1] : List Nat).count 0 := by decide

def initial {T : Type t} {E : Type w} (left right : T) (budget : Nat) : Portfolio T Nat E :=
  ⟨left, right, budget, 0, [], none⟩

def oneResult (events : List Nat) : Engine Nat Nat Nat where
  inspect state := if state = 0 then .paused else .full
  batch state := [state]
  progress state := (state + 1, events)
  deepen state := (state + 1, events)

theorem one_strategy_publishes :
    (execute (oneResult []) (oneResult []) [.left, .right, .left, .right]
      (initial 0 0 10)).published = some (.left, [1]) ∧
      (execute (oneResult []) (oneResult []) [.left, .right, .left, .right]
        (initial 0 0 10)).spent = 2 := by decide

theorem impure_speculation_repeats_effects :
    (execute (oneResult [42]) (oneResult [42]) [.left, .right, .left]
      (initial 0 0 10)).published = some (.left, [1]) ∧
      (execute (oneResult [42]) (oneResult [42]) [.left, .right, .left]
        (initial 0 0 10)).effects = [42, 42] := by decide

def waiting : Engine Nat Nat Nat where
  inspect _ := .paused
  batch _ := []
  progress state := (state + 1, [])
  deepen state := (state + 1, [])

theorem both_strategies_share_one_budget :
    (execute waiting waiting [.left, .right, .left, .right, .left, .right]
      (initial 0 0 3)).spent = 3 ∧
      (execute waiting waiting [.left, .right, .left, .right, .left, .right]
        (initial 0 0 3)).left = 2 ∧
      (execute waiting waiting [.left, .right, .left, .right, .left, .right]
        (initial 0 0 3)).right = 1 := by decide

def initialUneven : { iteration : Iteration Nat Nat // iteration.Valid uneven 0 5 } :=
  ⟨beginIteration 0 1, beginIteration_valid uneven 0 5 1⟩

/-- A real coordinator run discards [7] at the cut boundary, spends a unit
on the depth change, and later publishes [7,9] only once. -/
theorem deepening_discards_then_publishes :
    (execute (boundedEngine uneven 0 5 Nat) (boundedEngine uneven 0 5 Nat)
      (List.replicate 9 .right) (initial initialUneven initialUneven 20)).published =
        some (.right, [7, 9]) ∧
    (execute (boundedEngine uneven 0 5 Nat) (boundedEngine uneven 0 5 Nat)
      (List.replicate 9 .right) (initial initialUneven initialUneven 20)).spent = 8 ∧
    (execute (boundedEngine uneven 0 5 Nat) (boundedEngine uneven 0 5 Nat)
      (List.replicate 4 .right) (initial initialUneven initialUneven 20)).right.val.cursor.answers =
        [] := by decide

end Controls

end Mettapedia.Machines.BoundedSearchPortfolio
