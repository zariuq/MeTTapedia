import Mettapedia.Machines.PortfolioReach.Race

/-!
# A search that can act on the world, and when it does not

A state of a search expands to an answer, to alternatives, to an effect on
the world followed by another state, or to a raise. The expansion may read a
store, and an effect changes it. `System.space` is the same search read at
one store as a pure search space.

Two strategies run on such a system and perform what they meet: a
depth-first walk, which is the plain cursor when it runs alone, and iterative
deepening, which discards a cut-off round and begins again one level deeper.
`portfolio` serves them in slices over one world: the store, the log of
events performed, and the raise that halted it.

`Quiet` says that no effect and no raise can be reached. For a quiet root
(`portfolio_quiet`), under every sequence of slices:

* the world after the portfolio is the world before it;
* both strategies moved exactly as the pure strategies of the search space
  read at the entry store;
* a published batch satisfies the existing `BatchMeaning` for that space.

The controls show a root that is not quiet: an effect met again by each
deepening round (`Controls.effect_repeated`) and an effect a bounded round
never reaches although the plain cursor performs it (`Controls.effect_lost`).

The depth bound of this model counts expansions on a path, as the stack
machine it builds on does. The native meter is the nesting depth of
activations, which rises and falls along a path.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.PortfolioReach

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (Step Space Reaches IsAnswer bounded)
open Mettapedia.Machines.BoundedSearchPortfolio (Origin Task Cursor Status status ready
  expandOne children Iteration beginIteration nextIteration BatchMeaning)

universe u v w x

variable {σ : Type x} {S : Type u} {A : Type v} {E : Type w}

/-- One expansion of a state of a search that can act on the world. -/
inductive Move (S : Type u) (A : Type v) (E : Type w) where
  | answer (value : A)
  | branch (children : List S)
  | effect (event : E) (next : S)
  | raise (event : E)

/-- An answer or alternatives: nothing the world can see. -/
def Move.quiet : Move S A E → Bool
  | .answer _ => true
  | .branch _ => true
  | .effect _ _ => false
  | .raise _ => false

/-- The move as a step of a pure search: an effect is passed over, and a
raise is a dead end. -/
def Move.step : Move S A E → Step S A
  | .answer value => .answer value
  | .branch children => .branch children
  | .effect _ next => .branch [next]
  | .raise _ => .branch []

/-- A search over a store: an expansion may read the store, and an effect
changes it. -/
structure System (σ : Type x) (S : Type u) (A : Type v) (E : Type w) where
  expand : σ → S → Move S A E
  apply : E → σ → σ

/-- The search read at one store, as a pure search space. -/
def System.space (sys : System σ S A E) (store : σ) : Space S A where
  expand state := (sys.expand store state).step

/-- A pure search space as a system over any store, which it never reads. -/
def System.ofSpace (space : Space S A) : System σ S A E where
  expand _ state :=
    match space.expand state with
    | .answer value => .answer value
    | .branch children => .branch children
  apply _ store := store

/-- `target` is reached from `state` through alternatives. -/
inductive Reachable (space : Space S A) : S → S → Prop
  | here (state : S) : Reachable space state state
  | step {state child target : S} {children : List S} :
      space.expand state = .branch children → child ∈ children →
        Reachable space child target → Reachable space state target

/-- No effect and no raise can be reached from `root` at this store. -/
def Quiet (sys : System σ S A E) (store : σ) (root : S) : Prop :=
  ∀ state, Reachable (sys.space store) root state → (sys.expand store state).quiet = true

theorem Quiet.here {sys : System σ S A E} {store : σ} {root : S} (quiet : Quiet sys store root) :
    (sys.expand store root).quiet = true :=
  quiet root (.here root)

theorem Quiet.child {sys : System σ S A E} {store : σ} {root child : S} {children : List S}
    (quiet : Quiet sys store root) (expands : (sys.space store).expand root = .branch children)
    (member : child ∈ children) : Quiet sys store child :=
  fun state reach => quiet state (.step expands member reach)

theorem ofSpace_quiet (space : Space S A) (store : σ) (root : S) :
    Quiet (System.ofSpace (σ := σ) (E := E) space) store root := by
  intro state _
  show (match space.expand state with
    | .answer value => (Move.answer value : Move S A E)
    | .branch children => .branch children).quiet = true
  cases space.expand state <;> rfl

theorem ofSpace_space (space : Space S A) (store : σ) :
    (System.ofSpace (σ := σ) (E := E) space).space store = space := by
  cases space with
  | mk expand =>
      show Space.mk _ = Space.mk expand
      congr 1
      funext state
      show (match expand state with
        | .answer value => (Move.answer value : Move S A E)
        | .branch children => .branch children).step = expand state
      cases expand state <;> rfl

/-- What a search acts on: the store, the events performed in order, and the
raise that halted it. -/
structure World (σ : Type x) (E : Type w) where
  store : σ
  log : List E
  raised : Option E

/-- A raise has halted the world. -/
def halted (world : World σ E) : Bool := world.raised.isSome

/-- The world after a move is performed. -/
def System.act (sys : System σ S A E) (world : World σ E) : Move S A E → World σ E
  | .answer _ => world
  | .branch _ => world
  | .effect event _ => ⟨sys.apply event world.store, world.log ++ [event], world.raised⟩
  | .raise event => ⟨world.store, world.log ++ [event], some event⟩

theorem System.act_quiet (sys : System σ S A E) (world : World σ E) {move : Move S A E}
    (quiet : move.quiet = true) : sys.act world move = world := by
  cases move <;> simp_all [Move.quiet, System.act]

/-! ## The depth-first walk -/

/-- A depth-first cursor: pending states, and the answers found, newest first. -/
structure Walk (S : Type u) (A : Type v) where
  stack : List S
  reversed : List A

/-- One expansion of the walk in a pure search space. -/
def walkOne (space : Space S A) (walk : Walk S A) : Walk S A :=
  match walk.stack with
  | [] => walk
  | state :: rest =>
      match space.expand state with
      | .answer value => ⟨rest, value :: walk.reversed⟩
      | .branch children => ⟨children ++ rest, walk.reversed⟩

/-- A walk never cuts: it has its answers, has finished, or goes on. -/
def Walk.status (demand : Nat) (walk : Walk S A) : Status :=
  if demand ≤ walk.reversed.length then .full
  else if walk.stack.isEmpty then .exhausted else .paused

/-- The walk of a pure search space. -/
def walkResumable (space : Space S A) (demand : Nat) : Resumable (Walk S A) where
  step := walkOne space
  ready walk := ready (walk.status demand)

/-- The walk of a system: it performs the move it meets, in the store of the
moment. Run alone, it is the plain cursor. -/
def walkActor (sys : System σ S A E) (demand : Nat) : Actor (World σ E) (Walk S A) where
  step world walk :=
    match walk.stack with
    | [] => (world, walk)
    | state :: _ =>
        (sys.act world (sys.expand world.store state), walkOne (sys.space world.store) walk)
  ready walk := ready (walk.status demand)

/-! ## Iterative deepening -/

/-- One unit of iterative deepening in a pure search space: an expansion, or
after a cut-off round the next bound from the root. -/
def deepenOne (space : Space S A) (root : S) (demand : Nat) (iteration : Iteration S A) :
    Iteration S A :=
  match status demand iteration.cursor with
  | .cutoff => nextIteration root iteration
  | _ => { iteration with cursor := expandOne space iteration.cursor }

def deepenResumable (space : Space S A) (root : S) (demand : Nat) :
    Resumable (Iteration S A) where
  step := deepenOne space root demand
  ready iteration := ready (status demand iteration.cursor)

/-- Iterative deepening of a system, performing the move it meets. -/
def deepenActor (sys : System σ S A E) (root : S) (demand : Nat) :
    Actor (World σ E) (Iteration S A) where
  step world iteration :=
    match status demand iteration.cursor with
    | .cutoff => (world, nextIteration root iteration)
    | _ =>
        ((match iteration.cursor.frontier with
          | [] => world
          | task :: _ => sys.act world (sys.expand world.store task.state)),
          { iteration with cursor := expandOne (sys.space world.store) iteration.cursor })
  ready iteration := ready (status demand iteration.cursor)

/-! ## A walk is a bounded run that never reaches its bound -/

/-- The walk and a bounded cursor hold the same states and answers, the
cursor has cut nothing, and every pending task has `floor` levels left. -/
def Shadows (floor : Nat) (walk : Walk S A) (cursor : Cursor S A) : Prop :=
  walk.stack = cursor.frontier.map Task.state ∧ walk.reversed = cursor.reversed ∧
    cursor.cut = false ∧ ∀ task ∈ cursor.frontier, floor ≤ task.depth

theorem Shadows.status {floor : Nat} {walk : Walk S A} {cursor : Cursor S A}
    (shadows : Shadows floor walk cursor) (demand : Nat) :
    status demand cursor = walk.status demand := by
  obtain ⟨stack, reversed, uncut, _⟩ := shadows
  unfold BoundedSearchPortfolio.status Walk.status
  rw [reversed, stack, uncut]
  cases cursor.frontier <;> simp

theorem Shadows.step (space : Space S A) {floor : Nat} {walk : Walk S A} {cursor : Cursor S A}
    (shadows : Shadows (floor + 1) walk cursor) :
    Shadows floor (walkOne space walk) (expandOne space cursor) := by
  rcases walk with ⟨stack, answers⟩
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  obtain ⟨same, sameAnswers, uncut, deep⟩ := shadows
  dsimp only at same sameAnswers uncut deep
  subst same sameAnswers uncut
  cases frontier with
  | nil => exact ⟨rfl, rfl, rfl, by simp [expandOne]⟩
  | cons task rest =>
      have restDeep : ∀ other ∈ rest, floor ≤ other.depth := fun other member =>
        Nat.le_of_succ_le (deep other (by simp [member]))
      cases expansion : space.expand task.state with
      | answer value =>
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [walkOne, expandOne, expansion]
          exact restDeep
      | branch states =>
          have taskDeep := deep task (by simp)
          cases depthEq : task.depth with
          | zero => omega
          | succ depth =>
              refine ⟨?_, ?_, ?_, ?_⟩ <;>
                simp [walkOne, expandOne, expansion, depthEq, children, List.map_map,
                  Function.comp_def]
              intro other member
              rcases member with ⟨state, _, rfl⟩ | inRest
              · show floor ≤ depth
                omega
              · exact restDeep other inRest

/-- The walk's invariant: at every floor some valid bounded iteration shadows
it. This is a property of the walk, not a run of the reference search. -/
def Walk.Valid (space : Space S A) (root : S) (demand : Nat) (walk : Walk S A) : Prop :=
  ∀ floor, ∃ iteration : Iteration S A,
    iteration.Valid space root demand ∧ Shadows floor walk iteration.cursor

theorem Walk.valid_start (space : Space S A) (root : S) (demand : Nat) :
    (⟨[root], []⟩ : Walk S A).Valid space root demand := fun floor =>
  ⟨beginIteration root floor, BoundedSearchPortfolio.beginIteration_valid space root demand floor,
    rfl, rfl, rfl, by simp [beginIteration, BoundedSearchPortfolio.start]⟩

theorem ready_false_paused {state : Status} (waiting : ready state = false)
    (uncut : state ≠ .cutoff) : state = .paused := by
  cases state <;> simp_all [ready]

theorem Walk.status_ne_cutoff (demand : Nat) (walk : Walk S A) :
    walk.status demand ≠ .cutoff := by
  unfold Walk.status
  split
  · simp
  · split <;> simp

theorem Iteration.valid_expand (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (valid : iteration.Valid space root demand)
    (paused : status demand iteration.cursor = .paused) :
    ({ iteration with cursor := expandOne space iteration.cursor } : Iteration S A).Valid
      space root demand := by
  have ticked := BoundedSearchPortfolio.iteration_tick_valid space root demand iteration valid
  simpa [BoundedSearchPortfolio.tick, paused] using ticked

theorem Walk.valid_step (space : Space S A) (root : S) (demand : Nat) (walk : Walk S A)
    (valid : walk.Valid space root demand) (waiting : ready (walk.status demand) = false) :
    (walkOne space walk).Valid space root demand := by
  intro floor
  obtain ⟨iteration, iterationValid, shadows⟩ := valid (floor + 1)
  have paused : BoundedSearchPortfolio.status demand iteration.cursor = .paused := by
    rw [shadows.status demand]
    exact ready_false_paused waiting (walk.status_ne_cutoff demand)
  exact ⟨{ iteration with cursor := expandOne space iteration.cursor },
    Iteration.valid_expand space root demand iteration iterationValid paused,
    shadows.step space⟩

/-- **The plain cursor's batch is lawful.** A walk that has its answers, or
has finished, holds a batch of the search space in the existing sense: a
prefix of a bounded traversal, complete and uncut when it is short. -/
theorem Walk.batch_meaning (space : Space S A) (root : S) (demand : Nat) (walk : Walk S A)
    (valid : walk.Valid space root demand) (finished : ready (walk.status demand) = true) :
    BatchMeaning space root demand walk.reversed.reverse := by
  obtain ⟨iteration, iterationValid, shadows⟩ := valid 0
  have meaning := BoundedSearchPortfolio.iteration_ready_meaning space root demand iteration
    iterationValid (by rw [shadows.status demand]; exact finished)
  have same : iteration.cursor.answers = walk.reversed.reverse := by
    rw [BoundedSearchPortfolio.Cursor.answers, shadows.2.1]
  rwa [same] at meaning

theorem Iteration.valid_deepen (space : Space S A) (root : S) (demand : Nat)
    (iteration : Iteration S A) (valid : iteration.Valid space root demand)
    (waiting : ready (status demand iteration.cursor) = false) :
    (deepenOne space root demand iteration).Valid space root demand := by
  unfold deepenOne
  cases outcome : status demand iteration.cursor with
  | cutoff => exact BoundedSearchPortfolio.nextIteration_valid space root demand iteration
  | paused => exact Iteration.valid_expand space root demand iteration valid outcome
  | full => simp [outcome, ready] at waiting
  | exhausted => simp [outcome, ready] at waiting

/-! ## The frame law for a quiet root -/

/-- What holds of the walk of a quiet root: every pending state is quiet, and
the walk is valid for the search space read at the entry store. -/
def WalkInv (sys : System σ S A E) (store : σ) (root : S) (demand : Nat) (walk : Walk S A) :
    Prop :=
  (∀ state ∈ walk.stack, Quiet sys store state) ∧ walk.Valid (sys.space store) root demand

/-- What holds of the deepening of a quiet root. -/
def DeepenInv (sys : System σ S A E) (store : σ) (root : S) (demand : Nat)
    (iteration : Iteration S A) : Prop :=
  (∀ task ∈ iteration.cursor.frontier, Quiet sys store task.state) ∧
    iteration.Valid (sys.space store) root demand

theorem walkOne_quiet (sys : System σ S A E) (store : σ) (walk : Walk S A)
    (quiet : ∀ state ∈ walk.stack, Quiet sys store state) :
    ∀ state ∈ (walkOne (sys.space store) walk).stack, Quiet sys store state := by
  rcases walk with ⟨stack, reversed⟩
  cases stack with
  | nil => exact quiet
  | cons top rest =>
      have root := quiet top (by simp)
      intro target member
      cases expansion : (sys.space store).expand top with
      | answer value =>
          simp only [walkOne, expansion] at member
          exact quiet target (by simp [member])
      | branch states =>
          simp only [walkOne, expansion, List.mem_append] at member
          rcases member with inStates | inRest
          · exact root.child expansion inStates
          · exact quiet target (by simp [inRest])

theorem expandOne_quiet (sys : System σ S A E) (store : σ) (cursor : Cursor S A)
    (quiet : ∀ task ∈ cursor.frontier, Quiet sys store task.state) :
    ∀ task ∈ (expandOne (sys.space store) cursor).frontier, Quiet sys store task.state := by
  rcases cursor with ⟨frontier, reversed, cut, work⟩
  cases frontier with
  | nil => exact quiet
  | cons top rest =>
      have root := quiet top (by simp)
      have restQuiet : ∀ task ∈ rest, Quiet sys store task.state := fun task member =>
        quiet task (by simp [member])
      intro target member
      cases expansion : (sys.space store).expand top.state with
      | answer value =>
          simp only [expandOne, expansion] at member
          exact restQuiet target member
      | branch states =>
          cases depthEq : top.depth with
          | zero =>
              simp only [expandOne, expansion, depthEq] at member
              exact restQuiet target member
          | succ depth =>
              simp only [expandOne, expansion, depthEq, List.mem_append, children,
                List.mem_map] at member
              rcases member with ⟨state, inStates, rfl⟩ | inRest
              · exact root.child expansion inStates
              · exact restQuiet target inRest

theorem walkActor_follows (sys : System σ S A E) (world : World σ E) (root : S) (demand : Nat) :
    (walkActor sys demand).Follows world (walkResumable (sys.space world.store) demand)
      (WalkInv sys world.store root demand) where
  ready _ := rfl
  step walk holds _ := by
    rcases walk with ⟨stack, reversed⟩
    cases stack with
    | nil => rfl
    | cons state rest =>
        have here := (holds.1 state (by simp)).here
        simp [walkActor, walkResumable, sys.act_quiet world here]
  keeps walk holds waiting :=
    ⟨walkOne_quiet sys world.store walk holds.1,
      Walk.valid_step (sys.space world.store) root demand walk holds.2 waiting⟩

theorem deepenActor_follows (sys : System σ S A E) (world : World σ E) (root : S) (demand : Nat)
    (quiet : Quiet sys world.store root) :
    (deepenActor sys root demand).Follows world
      (deepenResumable (sys.space world.store) root demand)
      (DeepenInv sys world.store root demand) where
  ready _ := rfl
  step iteration holds _ := by
    have act : (match iteration.cursor.frontier with
        | [] => world
        | task :: _ => sys.act world (sys.expand world.store task.state)) = world := by
      cases frontier : iteration.cursor.frontier with
      | nil => rfl
      | cons task rest =>
          exact sys.act_quiet world (holds.1 task (by simp [frontier])).here
    simp only [deepenActor, deepenResumable, deepenOne]
    cases status demand iteration.cursor <;> simp only [act]
  keeps iteration holds waiting := by
    refine ⟨?_, Iteration.valid_deepen (sys.space world.store) root demand iteration holds.2
      waiting⟩
    simp only [deepenResumable, deepenOne]
    cases status demand iteration.cursor
    case cutoff =>
      intro task member
      simp only [nextIteration, beginIteration, BoundedSearchPortfolio.start,
        List.mem_singleton] at member
      subst member
      exact quiet
    all_goals exact expandOne_quiet sys world.store iteration.cursor holds.1

/-! ## The portfolio -/

/-- Both strategies at the root: the walk, and deepening from bound zero. -/
def begin (world : World σ E) (root : S) : Duo (World σ E) (Walk S A) (Iteration S A) :=
  ⟨world, ⟨[root], []⟩, beginIteration root 0, 0, none⟩

/-- The portfolio of a system: the walk and deepening, served in slices over
one world, each performing what it meets. -/
def portfolio (sys : System σ S A E) (root : S) (demand : Nat) (slices : List (Origin × Nat))
    (store : σ) (log : List E) : Duo (World σ E) (Walk S A) (Iteration S A) :=
  execute (walkActor sys demand) (deepenActor sys root demand) halted slices
    (begin ⟨store, log, none⟩ root)

/-- The same slices over the pure strategies of a search space. -/
def purePortfolio (space : Space S A) (root : S) (demand : Nat) (slices : List (Origin × Nat))
    (world : World σ E) : Duo (World σ E) (Walk S A) (Iteration S A) :=
  execute ((walkResumable space demand).actor (World σ E))
    ((deepenResumable space root demand).actor (World σ E)) (fun _ => false) slices
    (begin world root)

/-- The batch a portfolio hands over: the publisher's answers, in its order. -/
def batch (duo : Duo (World σ E) (Walk S A) (Iteration S A)) : Option (List A) :=
  match duo.published with
  | none => none
  | some .left => some duo.first.reversed.reverse
  | some .right => some duo.second.cursor.answers

/-- **A portfolio on a quiet root performs nothing.** Under every sequence of
slices it is the pure portfolio of the search space read at the entry store,
the world is the world it began in, and a published batch is a batch of that
space in the existing sense. -/
theorem portfolio_quiet (sys : System σ S A E) {store : σ} {root : S}
    (quiet : Quiet sys store root) (demand : Nat) (slices : List (Origin × Nat)) (log : List E) :
    portfolio sys root demand slices store log =
        purePortfolio (sys.space store) root demand slices ⟨store, log, none⟩ ∧
      (portfolio sys root demand slices store log).world = ⟨store, log, none⟩ ∧
      ∀ answers, batch (portfolio sys root demand slices store log) = some answers →
        BatchMeaning (sys.space store) root demand answers := by
  have startWalk : WalkInv sys store root demand (⟨[root], []⟩ : Walk S A) :=
    ⟨by intro state member; simp only [List.mem_singleton] at member; subst member; exact quiet,
      Walk.valid_start (sys.space store) root demand⟩
  have startDeepen : DeepenInv sys store root demand (beginIteration root 0 : Iteration S A) :=
    ⟨by
        intro task member
        simp only [beginIteration, BoundedSearchPortfolio.start, List.mem_singleton] at member
        subst member
        exact quiet,
      BoundedSearchPortfolio.beginIteration_valid (sys.space store) root demand 0⟩
  obtain ⟨equal, sameWorld, keptWalk, keptDeepen⟩ :=
    execute_follows (walkActor_follows sys ⟨store, log, none⟩ root demand)
      (deepenActor_follows sys ⟨store, log, none⟩ root demand quiet) (halted := halted) rfl
      slices (begin ⟨store, log, none⟩ root) rfl startWalk startDeepen
  have settled := execute_settled (walkActor sys demand) (deepenActor sys root demand) halted
    slices (begin ⟨store, log, none⟩ root)
    ⟨(by intro published; cases published), (by intro published; cases published)⟩
  refine ⟨equal, sameWorld, ?_⟩
  intro answers handed
  unfold batch at handed
  cases winner : (portfolio sys root demand slices store log).published with
  | none => simp [winner] at handed
  | some origin =>
      cases origin with
      | left =>
          simp only [winner, Option.some.injEq] at handed
          subst handed
          exact Walk.batch_meaning (sys.space store) root demand _ keptWalk.2
            (settled.1 winner).1
      | right =>
          simp only [winner, Option.some.injEq] at handed
          subst handed
          exact BoundedSearchPortfolio.iteration_ready_meaning (sys.space store) root demand _
            keptDeepen.2 (settled.2 winner).1

/-- The plain cursor alone: depth-first, performing what it meets, for at
most `fuel` expansions. -/
def plain (sys : System σ S A E) (root : S) (demand fuel : Nat) (store : σ) (log : List E) :
    Nat × World σ E × Walk S A :=
  (walkActor sys demand).work halted fuel ⟨store, log, none⟩ ⟨[root], []⟩

/-- **The plain cursor on a quiet root performs nothing either**, and a batch
it finishes with is a batch of the search space read at the entry store. -/
theorem plain_quiet (sys : System σ S A E) {store : σ} {root : S} (quiet : Quiet sys store root)
    (demand fuel : Nat) (log : List E) :
    (plain sys root demand fuel store log).2.1 = ⟨store, log, none⟩ ∧
      (ready ((plain sys root demand fuel store log).2.2.status demand) = true →
        BatchMeaning (sys.space store) root demand
          (plain sys root demand fuel store log).2.2.reversed.reverse) := by
  have startWalk : WalkInv sys store root demand (⟨[root], []⟩ : Walk S A) :=
    ⟨by intro state member; simp only [List.mem_singleton] at member; subst member; exact quiet,
      Walk.valid_start (sys.space store) root demand⟩
  obtain ⟨worked, kept⟩ := Actor.work_follows
    (walkActor_follows sys ⟨store, log, none⟩ root demand) (halted := halted) rfl fuel _ startWalk
  unfold plain
  rw [worked]
  exact ⟨rfl, fun finished =>
    Walk.batch_meaning (sys.space store) root demand _ kept.2 finished⟩

namespace Controls

/-- An effect at the root and an answer three levels down. -/
def effectFirst : System Unit Nat Nat Nat where
  expand _ state :=
    match state with
    | 0 => .effect 7 1
    | 1 => .branch [2]
    | 2 => .branch [3]
    | 3 => .answer 9
    | _ => .branch []
  apply _ _ := ()

/-- The plain cursor performs the effect once. Under doubling quanta the walk
performs it once and deepening once in each of its two rounds: three times in
all, before the walk publishes. -/
theorem effect_repeated :
    (plain effectFirst 0 1 10 () []).2.1.log = [7] ∧
      (plain effectFirst 0 1 10 () []).2.2.reversed = [9] ∧
      batch (portfolio effectFirst 0 1 (rounds (doubling 1) 3) () []) = some [9] ∧
      (portfolio effectFirst 0 1 (rounds (doubling 1) 3) () []).world.log = [7, 7, 7] := by
  decide

/-- An effect nine levels down the first alternative, and a shallow answer in
the second. -/
def effectDeep : System Unit Nat Nat Nat where
  expand _ state :=
    match state with
    | 0 => .branch [1, 100]
    | 9 => .effect 7 10
    | 10 => .answer 5
    | 100 => .answer 6
    | state + 1 => if state < 8 then .branch [state + 2] else .branch []
  apply _ _ := ()

/-- The plain cursor performs the effect and answers `5`. Under doubling
quanta, deepening publishes the shallow `6` in the third round, before the
walk has reached the effect: the effect is lost, and the answer is another. -/
theorem effect_lost :
    (plain effectDeep 0 1 20 () []).2.1.log = [7] ∧
      (plain effectDeep 0 1 20 () []).2.2.reversed = [5] ∧
      (portfolio effectDeep 0 1 (rounds (doubling 1) 3) () []).published = some .right ∧
      batch (portfolio effectDeep 0 1 (rounds (doubling 1) 3) () []) = some [6] ∧
      (portfolio effectDeep 0 1 (rounds (doubling 1) 3) () []).world.log = [] := by
  decide

/-- A first alternative that never ends, and an answer in the second. -/
def sidetrack : Space Nat Nat where
  expand
    | 0 => .branch [1, 2]
    | 1 => .branch [1]
    | 2 => .answer 4
    | _ => .branch []

/-- The plain cursor never answers: after its first expansion it holds the
endless alternative and the answer behind it, for good. -/
theorem sidetrack_plain_never (fuel : Nat) :
    ready (((walkResumable sidetrack 1).step^[fuel + 1] ⟨[0], []⟩).status 1) = false := by
  have fixed : ∀ count, (walkResumable sidetrack 1).step^[count] ⟨[1, 2], []⟩ =
      (⟨[1, 2], []⟩ : Walk Nat Nat) := by
    intro count
    exact Function.iterate_fixed rfl count
  rw [Function.iterate_succ_apply]
  show ready (((walkResumable sidetrack 1).step^[fuel] ⟨[1, 2], []⟩).status 1) = false
  rw [fixed]
  rfl

/-- The portfolio answers it in the third doubling round, with nothing
performed: the positive case of `portfolio_quiet`. -/
theorem sidetrack_portfolio_answers :
    batch (portfolio (System.ofSpace (σ := Unit) (E := Nat) sidetrack) 0 1
        (rounds (doubling 1) 3) () []) = some [4] ∧
      (portfolio (System.ofSpace (σ := Unit) (E := Nat) sidetrack) 0 1
        (rounds (doubling 1) 3) () []).world.log = [] := by decide

end Controls

#print axioms portfolio_quiet
#print axioms plain_quiet
#print axioms Walk.batch_meaning
#print axioms Controls.effect_repeated
#print axioms Controls.effect_lost
#print axioms Controls.sidetrack_plain_never
#print axioms Controls.sidetrack_portfolio_answers

end Mettapedia.Machines.PortfolioReach
