import Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution

/-!
# An unifier over packed equations and term handles

The transitions never decode a term. In a binding transition, the
work list is retargeted through an exact substitution map, and the
original binding is retained on the elimination trail. Exhausting
fuel suspends the work; malformed input or insufficient storage is
not a proof of inconsistency.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist

open Mettapedia.Logic.LP
open PackedTerms (Arena lookup)
open UnifierHeaders (Symbols)
open Derivation.FiniteUnifier (Action Configuration Conflict Equations Trail Work)

abbrev Words := List (Word × Word)

structure Worklist where
  arena : Arena
  pending : Words
  trail : Words
  deriving Repr

inductive State where
  | working (work : Worklist)
  | solved (arena : Arena) (trail : Words)
  | inconsistent (why : Conflict)
  deriving Repr

def advance (work : Worklist) : Option State :=
  match work.pending with
  | [] => some (.solved work.arena work.trail)
  | (left, right) :: rest => do
    let selected ← PackedUnifierAction.inspect work.arena left right
    match selected with
    | .discard => some (.working { work with pending := rest })
    | .refuse why => some (.inconsistent why)
    | .decompose parts => some (.working { work with pending := parts ++ rest })
    | .bindVar name root => do
      let changed ← PackedSubstitution.substitute work.arena name root
      let pending ← PackedSubstitution.remapPending changed.mapped rest
      some (.working ⟨changed.target, pending, (name, root) :: work.trail⟩)

def step : State → Option State
  | .working work => advance work
  | endState => some endState

def run : ℕ → State → Option State
  | 0, state => some state
  | fuel + 1, state => (step state).bind (run fuel)

def terminal : State → Bool
  | .working _ => false
  | _ => true

theorem resume (first second : ℕ) (state : State) :
    (run first state).bind (run second) = run (first + second) state := by
  induction first generalizing state with
  | zero => simp [run]
  | succ first ih =>
    simp only [run, Option.bind_assoc, ih, show first + 1 + second = (first + second) + 1 by omega]

universe u p
variable {σ : LPSignature.{u,u,p,u}}

def readEquations (symbols : Symbols σ) (arena : Arena) (pending : Words) : Option (Equations σ) :=
  pending.mapM (PackedUnifierAction.pair (lookup symbols arena))

def readBinding (symbols : Symbols σ) (arena : Arena) (binding : Word × Word) : Option (σ.vars × Term σ) :=
  (symbols.vars.decode binding.1).bind fun v => (lookup symbols arena binding.2).map fun term => (v, term)

def readTrail (symbols : Symbols σ) (arena : Arena) (trail : Words) : Option (Trail σ) :=
  trail.mapM (readBinding symbols arena)

def read (symbols : Symbols σ) : State → Option (Configuration σ)
  | .working work => do
    let pending ← readEquations symbols work.arena work.pending
    let trail ← readTrail symbols work.arena work.trail
    some (.working ⟨pending, trail⟩)
  | .solved arena trail => (readTrail symbols arena trail).map Configuration.solved
  | .inconsistent why => some (.inconsistent why)

def Room (arena : Arena) : Prop :=
  arena.nodes.size + arena.nodes.size < 2 ^ 64 ∧
  arena.children.size + arena.nodes.size * arena.children.size < 2 ^ 64

def nodeCount : State → ℕ
  | .working work => work.arena.nodes.size
  | .solved arena _ => arena.nodes.size
  | .inconsistent _ => 0

def edgeCount : State → ℕ
  | .working work => work.arena.children.size
  | .solved arena _ => arena.children.size
  | .inconsistent _ => 0

theorem trail_kept (symbols : Symbols σ) (before after : Arena)
    (keep : PackedSubstitution.Keeps symbols before after) (trail : Words) (bindings : Trail σ)
    (earlier : readTrail symbols before trail = some bindings) :
    readTrail symbols after trail = some bindings := by
  apply PackedTermEdges.mapM_keep (readBinding symbols before) (readBinding symbols after) ?_ trail earlier
  intro code pair known
  unfold readBinding at known
  obtain ⟨v, name, readPair⟩ := Option.bind_eq_some_iff.mp known
  obtain ⟨term, value, rfl⟩ := Option.map_eq_some_iff.mp readPair
  simp [readBinding, name, keep code.2 term value]

theorem bind_decoded (symbols : Symbols σ) (arena : Arena) (name root : Word) (operation : Action σ)
    (decoded : PackedUnifierAction.read symbols arena (.bindVar name root) = some operation) :
    ∃ v value, symbols.vars.decode name = some v ∧ symbols.vars.encode v = some name ∧
      lookup symbols arena root = some value ∧ operation = .eliminate v value := by
  unfold PackedUnifierAction.read at decoded
  obtain ⟨v, named, readTerm⟩ := Option.bind_eq_some_iff.mp decoded
  by_cases canonical : symbols.vars.encode v = some name
  · simp only [if_pos canonical] at readTerm
    obtain ⟨term, found, shape⟩ := Option.map_eq_some_iff.mp readTerm
    exact ⟨v, term, named, canonical, found, shape.symm⟩
  · simp [canonical] at readTerm

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

/-- One actual packed transition is the finite-term solver
transition. The storage reserve is only used by elimination. -/
theorem advance_checked (symbols : Symbols σ) (work : Worklist) (typed : Work σ)
    (equations : readEquations symbols work.arena work.pending = some typed.pending)
    (bindings : readTrail symbols work.arena work.trail = some typed.trail)
    (room : Room work.arena) :
    ∃ after, advance work = some after ∧ read symbols after = some (Derivation.FiniteUnifier.advance typed) ∧
      nodeCount after ≤ work.arena.nodes.size + work.arena.nodes.size ∧
      edgeCount after ≤ work.arena.children.size + work.arena.nodes.size * work.arena.children.size := by
  rcases work with ⟨arena, pending, trail⟩
  rcases typed with ⟨logical, saved⟩
  change readEquations symbols arena pending = some logical at equations
  change readTrail symbols arena trail = some saved at bindings
  cases pending with
  | nil =>
    obtain rfl := Option.some.inj equations
    refine ⟨.solved arena trail, rfl, ?_, ?_, ?_⟩
    · simp [read, bindings, Derivation.FiniteUnifier.advance]
    · simp [nodeCount]
    · simp [edgeCount]
  | cons top pending =>
    rcases top with ⟨left, right⟩
    simp only [readEquations, List.mapM_cons] at equations
    obtain ⟨pair, headRead, tailRead⟩ := Option.bind_eq_some_iff.mp equations
    obtain ⟨rest, pendingRead, fullRead⟩ := Option.bind_eq_some_iff.mp tailRead
    obtain rfl := Option.some.inj fullRead
    unfold PackedUnifierAction.pair at headRead
    obtain ⟨l, leftRead, getRight⟩ := Option.bind_eq_some_iff.mp headRead
    obtain ⟨r, rightRead, rfl⟩ := Option.map_eq_some_iff.mp getRight
    have found := PackedUnifierAction.inspect_exact symbols arena left right l r leftRead rightRead
    change readEquations symbols arena pending = some rest at pendingRead
    cases selected : PackedUnifierAction.inspect arena left right with
    | none => simp [selected] at found
    | some operation =>
      rw [selected, Option.bind_some] at found
      cases operation with
      | discard =>
        have shape : Derivation.FiniteUnifier.action l r = .discard := (Option.some.inj found).symm
        refine ⟨.working ⟨arena, pending, trail⟩, ?_, ?_, ?_, ?_⟩
        · simp [advance, selected]
        · simp [read, pendingRead, bindings, Derivation.FiniteUnifier.advance, shape]
        · simp [nodeCount]
        · simp [edgeCount]
      | refuse why =>
        have shape : Derivation.FiniteUnifier.action l r = .refuse why := (Option.some.inj found).symm
        refine ⟨.inconsistent why, ?_, ?_, Nat.zero_le _, Nat.zero_le _⟩
        · simp [advance, selected]
        · simp [read, Derivation.FiniteUnifier.advance, shape]
      | decompose children =>
        change (readEquations symbols arena children).map Action.decompose =
          some (Derivation.FiniteUnifier.action l r) at found
        obtain ⟨parts, decoded, shape⟩ := Option.map_eq_some_iff.mp found
        have decodeAppend : readEquations symbols arena (children ++ pending) = some (parts ++ rest) := by
          unfold readEquations at decoded pendingRead ⊢
          simp [List.mapM_append, decoded, pendingRead]
        refine ⟨.working ⟨arena, children ++ pending, trail⟩, ?_, ?_, ?_, ?_⟩
        · simp [advance, selected]
        · simp [read, decodeAppend, bindings, Derivation.FiniteUnifier.advance, ← shape]
        · simp [nodeCount]
        · simp [edgeCount]
      | bindVar name root =>
        obtain ⟨v, value, nameRead, registered, valueRead, shape⟩ :=
          bind_decoded symbols arena name root _ found
        have bound : Room arena := room
        obtain ⟨changed, cooked, complete⟩ := PackedSubstitution.substitute_exact symbols arena v name root value
          registered valueRead bound.1 bound.2
        obtain ⟨rewritten, retargeted, context⟩ := PackedSubstitution.remap_pending_exact symbols arena
          (Subst.single v value) changed complete pending pendingRead
        have retained := trail_kept symbols arena changed.target complete.keeps trail saved bindings
        have newTrail : readTrail symbols changed.target ((name, root) :: trail) = some ((v, value) :: saved) := by
          have oldValue := complete.keeps root value valueRead
          unfold readTrail at retained ⊢
          simp only [List.mapM_cons, retained]
          simp [readBinding, nameRead, oldValue]
        change readEquations symbols changed.target rewritten = some ((Subst.single v value).applyEqs rest) at context
        refine ⟨.working ⟨changed.target, rewritten, (name, root) :: trail⟩, ?_, ?_, ?_, ?_⟩
        · simp [advance, selected, cooked, retargeted]
        · simp [read, context, newTrail, Derivation.FiniteUnifier.advance, shape]
        · have size : changed.mapped.size = arena.nodes.size := by simpa using complete.visits
          change changed.target.nodes.size ≤ arena.nodes.size + arena.nodes.size
          simpa only [size] using complete.nodesUsed
        · have size : changed.mapped.size = arena.nodes.size := by simpa using complete.visits
          change changed.target.children.size ≤ arena.children.size + arena.nodes.size * arena.children.size
          simpa only [size] using complete.edgesUsed

theorem advance_exact (symbols : Symbols σ) (work : Worklist) (typed : Work σ)
    (equations : readEquations symbols work.arena work.pending = some typed.pending)
    (bindings : readTrail symbols work.arena work.trail = some typed.trail)
    (room : Room work.arena) :
    (advance work).bind (read symbols) = some (Derivation.FiniteUnifier.advance typed) := by
  obtain ⟨after, ran, covered, _, _⟩ := advance_checked symbols work typed equations bindings room
  simp only [ran, Option.bind_some, covered]

theorem step_checked (symbols : Symbols σ) (state : State) (typed : Configuration σ)
    (available : nodeCount state + nodeCount state < 2 ^ 64 ∧
      edgeCount state + nodeCount state * edgeCount state < 2 ^ 64)
    (known : read symbols state = some typed) :
    ∃ after, step state = some after ∧ read symbols after = some (Derivation.FiniteUnifier.step typed) ∧
      nodeCount after ≤ nodeCount state + nodeCount state ∧
      edgeCount after ≤ edgeCount state + nodeCount state * edgeCount state := by
  cases state with
  | working work =>
    unfold read at known
    obtain ⟨equations, input, later⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨trail, bindings, typedRead⟩ := Option.bind_eq_some_iff.mp later
    obtain rfl := Option.some.inj typedRead
    exact advance_checked symbols work ⟨equations, trail⟩ input bindings available
  | solved arena trail =>
    have unchanged : Derivation.FiniteUnifier.step typed = typed := by
      unfold read at known
      obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp known
      rfl
    refine ⟨.solved arena trail, rfl, unchanged.symm ▸ known, ?_, ?_⟩
    · simp [nodeCount]
    · simp [edgeCount]
  | inconsistent why =>
    obtain rfl := Option.some.inj known
    exact ⟨.inconsistent why, rfl, rfl, Nat.zero_le _, Nat.zero_le _⟩

/-- A conservative word-width budget independent of equation shape.
This bounds handle arithmetic, not deployment memory or the cost of
native allocation. A finer resource accounting can charge only copies. -/
def Reserve : ℕ → ℕ → ℕ → Prop
  | 0, nodes, edges => nodes < 2 ^ 64 ∧ edges < 2 ^ 64
  | fuel + 1, nodes, edges => Reserve fuel (nodes + nodes) (edges + nodes * edges)

theorem reserve_mono (fuel : ℕ) {n₁ n₂ e₁ e₂ : ℕ} (nodes : n₁ ≤ n₂) (edges : e₁ ≤ e₂)
    (fits : Reserve fuel n₂ e₂) : Reserve fuel n₁ e₁ := by
  induction fuel generalizing n₁ n₂ e₁ e₂ with
  | zero => exact ⟨nodes.trans_lt fits.1, edges.trans_lt fits.2⟩
  | succ fuel ih =>
    exact ih (Nat.add_le_add nodes nodes) (Nat.add_le_add edges (Nat.mul_le_mul nodes edges)) fits

theorem reserve_current (fuel nodes edges : ℕ) (fits : Reserve fuel nodes edges) :
    nodes < 2 ^ 64 ∧ edges < 2 ^ 64 := by
  induction fuel generalizing nodes edges with
  | zero => exact fits
  | succ fuel ih =>
    obtain ⟨n, e⟩ := ih (nodes + nodes) (edges + nodes * edges) fits
    exact ⟨by omega, by omega⟩

theorem run_exact (symbols : Symbols σ) (fuel : ℕ) (state : State) (typed : Configuration σ)
    (known : read symbols state = some typed)
    (fits : Reserve fuel (nodeCount state) (edgeCount state)) :
    ∃ after, run fuel state = some after ∧ read symbols after = some (Derivation.FiniteUnifier.run fuel typed) := by
  induction fuel generalizing state typed with
  | zero => exact ⟨state, rfl, known⟩
  | succ fuel ih =>
    obtain ⟨after, ran, meaning, nodes, edges⟩ := step_checked symbols state typed
      (reserve_current fuel _ _ fits) known
    obtain ⟨output, further, readback⟩ := ih after (Derivation.FiniteUnifier.step typed) meaning
      (reserve_mono fuel nodes edges fits)
    exact ⟨output, by simp only [run, ran, Option.bind_some, further], readback⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] in
theorem terminal_read (symbols : Symbols σ) (state : State) (typed : Configuration σ)
    (known : read symbols state = some typed) : terminal state = Derivation.FiniteUnifier.terminal typed := by
  cases state with
  | working work =>
    unfold read at known
    obtain ⟨agenda, _, next⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨trail, _, found⟩ := Option.bind_eq_some_iff.mp next
    obtain rfl := Option.some.inj found
    rfl
  | solved arena trail =>
    unfold read at known
    obtain ⟨_, _, rfl⟩ := Option.map_eq_some_iff.mp known
    rfl
  | inconsistent why =>
    obtain rfl := Option.some.inj known
    rfl

/-- The packed execution has a complete run within the stated word
budget and reads back exactly the source unifier. The proof uses the
finite solver's termination measure; execution takes only packed steps. -/
theorem complete (symbols : Symbols σ) (state : State) (equations : Equations σ)
    (known : read symbols state = some (Derivation.FiniteUnifier.start equations))
    (fits : Reserve (Derivation.FiniteUnifier.stepsToFinish ⟨equations, []⟩) (nodeCount state) (edgeCount state)) :
    ∃ steps after result, run steps state = some after ∧ terminal after = true ∧
      read symbols after = some result ∧ Derivation.FiniteUnifier.meaning result = unifyTotal equations := by
  let steps := Derivation.FiniteUnifier.stepsToFinish (σ := σ) ⟨equations, []⟩
  let result := Derivation.FiniteUnifier.run steps (Derivation.FiniteUnifier.start equations)
  obtain ⟨after, finished, decoded⟩ := run_exact symbols steps state _ known fits
  exact ⟨steps, after, result, finished,
    (terminal_read symbols after result decoded).trans
      (Derivation.FiniteUnifier.finishes_at ⟨equations, []⟩), decoded,
    Derivation.FiniteUnifier.start_exact steps equations⟩

namespace Examples

private def arena : Arena :=
  ⟨#[⟨⟨0, 7⟩, 0, 0⟩, ⟨⟨1, 42⟩, 0, 0⟩, ⟨⟨2, 1⟩, 0, 1⟩, ⟨⟨2, 1⟩, 1, 1⟩], #[0, 1]⟩

def solvedTrail : Option State → Option Words
  | some (.solved _ trail) => some trail
  | _ => none

def conflict : Option State → Option Conflict
  | some (.inconsistent why) => some why
  | _ => none

theorem shared_compounds_solve_to_the_same_constant :
    solvedTrail (run 4 (.working ⟨arena, [(2, 3), (0, 1)], []⟩)) = some [(7, 1)] := by decide +kernel

theorem a_cyclic_equation_has_an_occurs_conflict :
    conflict (run 1 (.working ⟨arena, [(0, 2)], []⟩)) = some .occurs := by decide +kernel

theorem suspending_the_cyclic_equation_is_not_a_conflict :
    conflict (run 0 (.working ⟨arena, [(0, 2)], []⟩)) = none := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedWorklist
