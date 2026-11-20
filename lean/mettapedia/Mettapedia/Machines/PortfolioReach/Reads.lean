import Mettapedia.Machines.PortfolioReach.EntryTyping

/-!
# Reads in a fragment that writes nothing, and the order of a read

**What a read depends on.** A read's rows come from the store (`System.expand` takes it), and
the store is everything the generator's steps can observe: the rows of every space it reads,
the program's own equations, and named state. "Writes nothing" therefore covers three things,
each part of `Quiet`: the generator's own steps (no reachable `write`), host calls (a step the
model does not compute itself is an effect), and the state the reads depend on (nothing but the
portfolio runs between the entry and the publication, so nothing else changes the store).

`reads_stable`: on a quiet root, the world at the start of every slice is the entry world, and
the run is the run of the search read at the entry store. Every read, in every round and at
every bound, gives the entry store's rows: a deeper round's replay observes nothing new and
performs nothing. `Controls.one_write`: with one write the rounds differ, the write is repeated
five times, and the batch is not the plain cursor's.

**Bag producers and ordered producers.** A read of a multiset or set space is a bag producer:
any order of its answers is the same observation, so `once` may answer any of them and the
portfolio's law (`BatchMeaning`) is its observation. A read of a stack, queue or priority space
is an ordered producer: the order is part of the observation, `once` is its first answer in the
space's order, `select k` its first `k`, which is the plain cursor's batch.
`Controls.ordered_first_differs`: an admitted generator over an ordered space, where the plain
cursor answers the first row's answer and the portfolio, lawfully for a bag, answers the second
row's.

`lockstep`, `uncut_ready`: a bounded round that has cut nothing is the depth-first walk, step for
step. So the only deepening batches that keep the order are batches the walk has after the same
number of expansions, and the walk, served first in every round with the same quanta, publishes
them no later: for an ordered producer the portfolio gains nothing over the plain cursor, and
ordered reads are excluded from admission (`admitsBag`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (Step Space Reaches IsAnswer bounded)
open Mettapedia.Machines.BoundedSearchPortfolio (Origin Task Cursor Status status ready
  expandOne children Iteration beginIteration nextIteration BatchMeaning start)

universe u v w x

/-! ## Reads give the same rows in every round -/

section Stable

variable {σ : Type x} {S : Type u} {A : Type v} {E : Type w}

/-- **Reads are stable.** On a quiet root, after any prefix of the slices the world is the entry
world, the rest of the run continues from there, and the whole run is the run of the search read
at the entry store. -/
theorem reads_stable (sys : System σ S A E) {store : σ} {root : S} (quiet : Quiet sys store root)
    (demand : Nat) (slices : List (Origin × Nat)) (log : List E) (count : Nat) :
    (portfolio sys root demand (slices.take count) store log).world = ⟨store, log, none⟩ ∧
      portfolio sys root demand slices store log =
        execute (walkActor sys demand) (deepenActor sys root demand) halted (slices.drop count)
          (portfolio sys root demand (slices.take count) store log) ∧
      portfolio sys root demand slices store log =
        purePortfolio (sys.space store) root demand slices ⟨store, log, none⟩ := by
  refine ⟨(portfolio_quiet sys quiet demand (slices.take count) log).2.1, ?_,
    (portfolio_quiet sys quiet demand slices log).1⟩
  unfold portfolio
  rw [← execute_append, List.take_append_drop]

end Stable

/-- In the search read at a store, a read gives that store's rows. -/
theorem space_read (program : Program) (store : Store) (env : List Val) (space : Nat)
    (goals : List Goal) (result : Operand) (rest : List Frame) :
    ((system program).space store).expand (⟨env, .read space :: goals, result⟩ :: rest) =
      .branch ((store space).map fun row => ⟨env ++ [row], goals, result⟩ :: rest) := rfl

/-! ## Bag producers and ordered producers -/

/-- How a space offers the rows of a read: as a bag, or in a declared order that is part of the
observation (a stack, a queue, a priority space). -/
inductive SpaceKind where
  | bag
  | ordered
  deriving DecidableEq, Repr

/-- The spaces a program reads. -/
def readSpaces (program : Program) : List Nat :=
  program.flatMap fun relation => relation.equations.flatMap fun equation =>
    equation.goals.filterMap fun goal =>
      match goal with
      | .read space => some space
      | _ => none

/-- Every space the program reads offers a bag. -/
def readsBags (kind : Nat → SpaceKind) (program : Program) : Bool :=
  (readSpaces program).all fun space => kind space == .bag

/-- Admission: entry typing, and reads of bag spaces only. -/
def admitsBag (program : Program) (rowKind : Nat → Bool) (kind : Nat → SpaceKind) (entry : Nat)
    (arguments : List Val) : Bool :=
  admits program rowKind entry arguments && readsBags kind program

/-! ## A round that has cut nothing is the walk -/

section Lockstep

variable {S : Type u} {A : Type v}

/-- A bounded cursor and a walk hold the same states and answers. -/
def Matches (cursor : Cursor S A) (walk : Walk S A) : Prop :=
  cursor.frontier.map Task.state = walk.stack ∧ cursor.reversed = walk.reversed

theorem expandOne_cut_mono (space : Space S A) (cursor : Cursor S A)
    (cut : cursor.cut = true) : (expandOne space cursor).cut = true := by
  rcases cursor with ⟨frontier, reversed, wasCut, work⟩
  simp only at cut
  subst cut
  cases frontier with
  | nil => rfl
  | cons task rest =>
      cases expansion : space.expand task.state with
      | answer value => simp [expandOne, expansion]
      | branch states => cases depthEq : task.depth <;> simp [expandOne, expansion, depthEq]

theorem matches_step (space : Space S A) {cursor : Cursor S A} {walk : Walk S A}
    (same : Matches cursor walk) (uncut : (expandOne space cursor).cut = false) :
    Matches (expandOne space cursor) (walkOne space walk) := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  rcases walk with ⟨stack, walkReversed⟩
  obtain ⟨sameStack, sameReversed⟩ := same
  simp only at sameStack sameReversed
  subst sameStack sameReversed
  cases frontier with
  | nil => exact ⟨rfl, rfl⟩
  | cons task rest =>
      cases expansion : space.expand task.state with
      | answer value =>
          simp [Matches, expandOne, walkOne, expansion]
      | branch states =>
          cases depthEq : task.depth with
          | zero =>
              have empty : states = [] := by
                simp only [expandOne, expansion, depthEq, Bool.or_eq_false_iff] at uncut
                simpa using uncut.2
              subst empty
              simp [Matches, expandOne, walkOne, expansion, depthEq]
          | succ depth =>
              simp [Matches, expandOne, walkOne, expansion, depthEq, children, List.map_map,
                Function.comp_def]

/-- **Lockstep.** As long as a bounded round has cut nothing, it has expanded exactly what the
depth-first walk expands in as many steps, in the same order, with the same answers. -/
theorem lockstep (space : Space S A) (root : S) (depth : Nat) : ∀ steps,
    ((expandOne space)^[steps] (start root depth)).cut = false →
      Matches ((expandOne space)^[steps] (start root depth))
        ((walkOne space)^[steps] ⟨[root], []⟩)
  | 0, _ => ⟨rfl, rfl⟩
  | steps + 1, uncut => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at *
      have before : ((expandOne space)^[steps] (start root depth)).cut = false := by
        cases wasCut : ((expandOne space)^[steps] (start root depth)).cut with
        | false => rfl
        | true =>
            have later := expandOne_cut_mono space _ wasCut
            rw [later] at uncut
            cases uncut
      exact matches_step space (lockstep space root depth steps before) uncut

/-- **An uncut ready round is the walk's batch.** A bounded round that is ready (full or
exhausted) and has cut nothing holds the walk's answers after as many steps, and the walk is
ready there too. -/
theorem uncut_ready (space : Space S A) (root : S) (depth demand steps : Nat)
    (uncut : ((expandOne space)^[steps] (start root depth)).cut = false)
    (finished : ready (status demand ((expandOne space)^[steps] (start root depth))) = true) :
    ((expandOne space)^[steps] (start root depth)).reversed =
        ((walkOne space)^[steps] ⟨[root], []⟩).reversed ∧
      ready (((walkOne space)^[steps] ⟨[root], []⟩).status demand) = true := by
  obtain ⟨sameStack, sameReversed⟩ := lockstep space root depth steps uncut
  refine ⟨sameReversed, ?_⟩
  have equal : status demand ((expandOne space)^[steps] (start root depth)) =
      ((walkOne space)^[steps] ⟨[root], []⟩).status demand := by
    unfold BoundedSearchPortfolio.status Walk.status
    rw [sameReversed, ← sameStack, uncut]
    cases ((expandOne space)^[steps] (start root depth)).frontier <;> simp
  rw [← equal]
  exact finished

end Lockstep

namespace Controls

/-- Relations `first` to `first + length - 1` call the next; relation `first + length` has no
equation, so the chain fails. -/
def failingChain (first length : Nat) : List Relation :=
  (List.range length).map (fun index => ⟨0, [⟨[.call (first + index + 1) []], .var 0⟩]⟩) ++
    [⟨0, []⟩]

/-- `(= (w) (dead-end))` and `(= (w) (let $u (add-atom space0 1) (match space0 $x $x)))`. -/
def oneWrite : Program :=
  ⟨0, [⟨[.call 1 []], .var 0⟩, ⟨[.write 0 (.lit (.int 1)), .read 0], .var 0⟩]⟩ ::
    failingChain 1 30

/-- **One write.** The plain cursor writes once and answers `[1]`. Under doubling quanta every
deepening round repeats the write (one, two, then four writes after three, four and five rounds),
each round reads a different space, and the portfolio publishes `[1, 1]` after five writes. -/
theorem one_write :
    admits oneWrite noRows 0 [] = false ∧
      (plain (system oneWrite) (root 0 []) 2 80 emptyStore []).2.2.reversed = [.int 1] ∧
      (plain (system oneWrite) (root 0 []) 2 80 emptyStore []).2.1.log = [.add 0 (.int 1)] ∧
      (portfolio (system oneWrite) (root 0 []) 2 (rounds (doubling 1) 3) emptyStore
        []).world.log.length = 1 ∧
      (portfolio (system oneWrite) (root 0 []) 2 (rounds (doubling 1) 4) emptyStore
        []).world.log.length = 2 ∧
      (portfolio (system oneWrite) (root 0 []) 2 (rounds (doubling 1) 5) emptyStore
        []).world.log.length = 4 ∧
      batch (portfolio (system oneWrite) (root 0 []) 2 (rounds (doubling 1) 6) emptyStore []) =
        some [.int 1, .int 1] ∧
      (portfolio (system oneWrite) (root 0 []) 2 (rounds (doubling 1) 6) emptyStore
        []).world.log.length = 5 := by
  decide

/-- Relations `first` to `first + length - 1` call the next; relation `first + length` answers
`0`. -/
def succeedingChain (first length : Nat) : List Relation :=
  (List.range length).map (fun index => ⟨0, [⟨[.call (first + index + 1) []], .var 0⟩]⟩) ++
    [⟨0, [⟨[], .lit (.int 0)⟩]⟩]

/-- A read of space `0`, then `(pick $x)`: the row `1` leads through a hundred calls, the row
`2` answers at once. -/
def orderedRead : Program :=
  ⟨0, [⟨[.read 0, .call 1 [.var 0]], .var 1⟩]⟩ ::
    ⟨1, [⟨[.test .eq (.var 0) (.lit (.int 1)), .call 2 []], .var 0⟩,
      ⟨[.test .eq (.var 0) (.lit (.int 2))], .var 0⟩]⟩ :: succeedingChain 2 100

/-- The space's rows, `1` before `2`. -/
def orderedRows : Store := fun _ => [.int 1, .int 2]

/-- **An ordered read.** The program is admitted by entry typing. The plain cursor answers `1`,
the answer of the first row in the space's order, which is what `once` observes over an ordered
space. The portfolio publishes `2` from deepening. The admission that asks the space's kind
refuses the program when the space is ordered and admits it when the space is a bag. -/
theorem ordered_first_differs :
    admits orderedRead (fun _ => true) 0 [] = true ∧
      (plain (system orderedRead) (root 0 []) 1 400 orderedRows []).2.2.reversed = [.int 1] ∧
      ready ((plain (system orderedRead) (root 0 []) 1 400 orderedRows []).2.2.status 1) = true ∧
      batch (portfolio (system orderedRead) (root 0 []) 1 (rounds (doubling 1) 6) orderedRows []) =
        some [.int 2] ∧
      admitsBag orderedRead (fun _ => true) (fun _ => .ordered) 0 [] = false ∧
      admitsBag orderedRead (fun _ => true) (fun _ => .bag) 0 [] = true := by
  decide

theorem orderedRows_int : RowsInt (fun _ => true) orderedRows := by
  intro space _ row member
  simp only [orderedRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- Both answers are lawful batches of the search read as a bag: the bag law cannot tell them
apart, and the ordered observation can. -/
theorem ordered_both_lawful_for_bags :
    BatchMeaning ((system orderedRead).space orderedRows) (root 0 []) 1 [.int 2] ∧
      BatchMeaning ((system orderedRead).space orderedRows) (root 0 []) 1 [.int 1] := by
  obtain ⟨admitted, plainAnswers, plainReady, published, _, _⟩ := ordered_first_differs
  constructor
  · exact (admitted_portfolio admitted orderedRows_int 1 (rounds (doubling 1) 6) []).2 _ published
  · have lawful := (plain_quiet (system orderedRead) (admits_quiet admitted orderedRows_int) 1
      400 []).2 plainReady
    rw [plainAnswers] at lawful
    exact lawful

end Controls

#print axioms reads_stable
#print axioms space_read
#print axioms lockstep
#print axioms uncut_ready
#print axioms Controls.one_write
#print axioms Controls.ordered_first_differs
#print axioms Controls.ordered_both_lawful_for_bags

end Mettapedia.Machines.PortfolioReach
