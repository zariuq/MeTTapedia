import Mettapedia.Machines.StoredIdAlignment
import Mettapedia.Machines.MatchIndexProjection

/-!
# Bounded private views of compact stored rows

The source reconstructs a row from its skeleton and complete stored meanings.
One target exposes stored heads into a bounded private header heap, borrowing
cached views and constructing permitted scalar leaves. The direct target reads
stored headers and typed skeleton coordinates without building that heap.
Failed exposure retains an unknown candidate. Neither operational adapter
invokes source reconstruction.

Terms use the maintained binary encoding of finite constructor expressions;
native n-ary header coordinates retain their own correspondence obligation.
Variables keep their explicit frames. Constructor rejection is compared under
one shared simultaneous substitution. Native pointer lifetimes, list/ordinary
representation recognition, scalar equality and source/cancellation scheduling
remain separate correspondence obligations. Work purses count this adapter's
head observations and private headers, not semantic source fuel.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.BorrowedKeptFrontier

open ShapeStore ShapeScopedUnification
open Mettapedia.Logic.LP

variable {Atom Var Id : Type} [DecidableEq Var]

abbrev Reader := StoredIdViews.Reader Atom Var Id
abbrev StoredView := StoredIdViews.View Var Id

inductive Ref (Atom Var Id : Type) where
  | borrowed (view : StoredIdViews.View Var Id)
  | scalar (value : Atom)
  | header (index : Nat)
  deriving DecidableEq

abbrev Heap (Atom Var Id : Type) := List (Ref Atom Var Id × Ref Atom Var Id)

/-- Graph denotation is independent of the allocating builder. Header
coordinates refer to the actual completed private table. -/
inductive Denotes (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (heap : Heap Atom Var Id) : Ref Atom Var Id → LogicTerm Atom Var → Prop where
  | borrowed (view : StoredView (Var := Var) (Id := Id)) :
      Denotes reader heap (.borrowed view) (StoredIdViews.meaning reader view)
  | scalar (value : Atom) : Denotes reader heap (.scalar value) (.const value)
  | header {index : Nat} {left right : Ref Atom Var Id} {a b : LogicTerm Atom Var} :
      heap[index]? = some (left, right) → Denotes reader heap left a →
      Denotes reader heap right b → Denotes reader heap (.header index) (pair a b)

def Extends (before after : Heap Atom Var Id) : Prop :=
  ∃ suffix, after = before ++ suffix

omit [DecidableEq Var] in
theorem extends_refl (heap : Heap Atom Var Id) : Extends heap heap := ⟨[], by simp⟩

omit [DecidableEq Var] in
theorem extends_trans {first middle last : Heap Atom Var Id}
    (earlier : Extends first middle) (later : Extends middle last) : Extends first last := by
  obtain ⟨a, rfl⟩ := earlier
  obtain ⟨b, rfl⟩ := later
  exact ⟨a ++ b, by simp [List.append_assoc]⟩

private theorem lookup_append {α : Type} (first later : List α) (index : Nat) (value : α)
    (found : first[index]? = some value) : (first ++ later)[index]? = some value := by
  induction first generalizing index with
  | nil => simp at found
  | cons head rest ih =>
      cases index with
      | zero => simpa using found
      | succ index => simpa using ih index (by simpa using found)

theorem denotes_extends (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    {before after : Heap Atom Var Id} (extension : Extends before after)
    {ref : Ref Atom Var Id} {value : LogicTerm Atom Var} (known : Denotes reader before ref value) :
    Denotes reader after ref value := by
  obtain ⟨suffix, rfl⟩ := extension
  induction known with
  | borrowed view => exact .borrowed view
  | scalar value => exact .scalar value
  | header found _ _ left right => exact .header (lookup_append _ _ _ _ found) left right

structure Built (Atom Var Id : Type) where
  root : Ref Atom Var Id
  heap : Heap Atom Var Id

def emit (capacity : Nat) (heap : Heap Atom Var Id) (left right : Ref Atom Var Id) :
    Option (Built Atom Var Id) :=
  if heap.length < capacity then some ⟨.header heap.length, heap ++ [(left, right)]⟩ else none

theorem emit_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (capacity : Nat) (heap : Heap Atom Var Id) (left right : Ref Atom Var Id)
    (a b : LogicTerm Atom Var) (leftMeaning : Denotes reader heap left a)
    (rightMeaning : Denotes reader heap right b) (result : Built Atom Var Id)
    (built : emit capacity heap left right = some result) :
    Extends heap result.heap ∧ result.heap.length ≤ capacity ∧
      Denotes reader result.heap result.root (pair a b) := by
  unfold emit at built
  split at built
  · rename_i room
    cases built
    have extension : Extends heap (heap ++ [(left, right)]) := ⟨_, rfl⟩
    refine ⟨extension, by simpa using room, .header ?_
      (denotes_extends reader extension leftMeaning) (denotes_extends reader extension rightMeaning)⟩
    simp
  · contradiction

/-- These are metadata capabilities, not judgments about source syntax.
A cached view can be borrowed without a new constructor readback. -/
structure Policy (Atom Id : Type) where
  cached : Id → Bool
  available : Id → Bool
  scalar : Atom → Bool
  ordinary : Id → Bool

/-- Stored variables and unsupported uncached leaves decline exposure. A
cached open view retains its row frame, including shared variables. -/
def buildId (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (policy : Policy Atom Id) (frame capacity : Nat) :
    Nat → Id → Heap Atom Var Id → Option (Built Atom Var Id)
  | depth, id, heap =>
      if policy.cached id then some ⟨.borrowed (.stored id frame), heap⟩
      else if !policy.available id then none
      else match reader.inspect id with
        | .cell _ => none
        | .atom value => if policy.scalar value then some ⟨.scalar value, heap⟩ else none
        | .node left right => match depth with
          | 0 => none
          | remaining + 1 =>
              if policy.ordinary id then do
                let a ← buildId reader policy frame capacity remaining left heap
                let b ← buildId reader policy frame capacity remaining right a.heap
                emit capacity b.heap a.root b.root
              else none

theorem buildId_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (policy : Policy Atom Id) (frame capacity depth : Nat) (id : Id)
    (heap : Heap Atom Var Id) (room : heap.length ≤ capacity)
    (result : Built Atom Var Id) (built : buildId reader policy frame capacity depth id heap = some result) :
    Extends heap result.heap ∧ result.heap.length ≤ capacity ∧
      Denotes reader result.heap result.root (encode frame (reader.source id)) := by
  induction depth generalizing id heap result with
  | zero =>
      rw [buildId] at built
      split at built
      · cases built; exact ⟨extends_refl _, room, .borrowed _⟩
      · split at built
        · contradiction
        · cases exposed : reader.inspect id with
          | cell name => simp [exposed] at built
          | node left right => simp [exposed] at built
          | atom value =>
              simp only [exposed] at built
              split at built
              · cases built
                have source := reader.faithful id
                rw [exposed] at source
                rw [← source]
                exact ⟨extends_refl _, room, .scalar value⟩
              · contradiction
  | succ depth ih =>
      rw [buildId] at built
      split at built
      · cases built; exact ⟨extends_refl _, room, .borrowed _⟩
      · split at built
        · contradiction
        · cases exposed : reader.inspect id with
          | cell name => simp [exposed] at built
          | atom value =>
              simp only [exposed] at built
              split at built
              · cases built
                have source := reader.faithful id
                rw [exposed] at source
                rw [← source]
                exact ⟨extends_refl _, room, .scalar value⟩
              · contradiction
          | node left right =>
              simp only [exposed] at built
              split at built
              · obtain ⟨a, leftBuilt, remaining⟩ := Option.bind_eq_some_iff.mp built
                obtain ⟨b, rightBuilt, emitted⟩ := Option.bind_eq_some_iff.mp remaining
                obtain ⟨leftExtension, leftRoom, leftMeaning⟩ := ih left heap room a leftBuilt
                obtain ⟨rightExtension, rightRoom, rightMeaning⟩ := ih right a.heap leftRoom b rightBuilt
                have both := emit_correct reader capacity b.heap a.root b.root
                  (encode frame (reader.source left)) (encode frame (reader.source right))
                  (denotes_extends reader rightExtension leftMeaning) rightMeaning result emitted
                have source := reader.faithful id
                rw [exposed] at source
                refine ⟨extends_trans (extends_trans leftExtension rightExtension) both.1, both.2.1, ?_⟩
                rw [← source]
                exact both.2.2
              · contradiction

/-- The source reconstructs complete terms independently, using no cache,
header coordinates, workspace or depth allowance. -/
def reconstruct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) :
    Skel Atom → List Id → Option (OpenTerm Atom Var × List Id)
  | .hole, [] => none
  | .hole, id :: rest => some (reader.source id, rest)
  | .atom value, holes => some (.atom (.inl value), holes)
  | .node left right, holes => do
      let a ← reconstruct reader left holes
      let b ← reconstruct reader right a.2
      pure (.node a.1 b.1, b.2)

structure RowBuilt (Atom Var Id : Type) extends Built Atom Var Id where
  remaining : List Id

/-- Skeleton traversal and stored-subtree exposure share the private header
capacity. The depth allowance bounds newly inspected stored subtrees. -/
def buildRow (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (policy : Policy Atom Id) (frame capacity : Nat) :
    Skel Atom → Nat → List Id → Heap Atom Var Id → Option (RowBuilt Atom Var Id)
  | .hole, depth, id :: rest, heap => do
      let result ← buildId reader policy frame capacity depth id heap
      pure ⟨result, rest⟩
  | .hole, _, [], _ => none
  | .atom value, _, holes, heap => some ⟨⟨.scalar value, heap⟩, holes⟩
  | .node left right, depth, holes, heap => do
      let a ← buildRow reader policy frame capacity left (depth - 1) holes heap
      let b ← buildRow reader policy frame capacity right (depth - 1) a.remaining a.heap
      let parent ← emit capacity b.heap a.root b.root
      pure ⟨parent, b.remaining⟩

theorem buildRow_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (policy : Policy Atom Id) (frame capacity : Nat) (shape : Skel Atom)
    (depth : Nat) (holes : List Id) (heap : Heap Atom Var Id) (room : heap.length ≤ capacity)
    (result : RowBuilt Atom Var Id)
    (built : buildRow reader policy frame capacity shape depth holes heap = some result) :
    ∃ source, reconstruct reader shape holes = some (source, result.remaining) ∧
      Extends heap result.heap ∧ result.heap.length ≤ capacity ∧
      Denotes reader result.heap result.root (encode frame source) := by
  induction shape generalizing depth holes heap result with
  | hole =>
      cases holes with
      | nil => simp [buildRow] at built
      | cons id rest =>
          obtain ⟨a, made, equal⟩ := Option.bind_eq_some_iff.mp built
          simp only [Option.pure_def, Option.some.injEq] at equal
          subst result
          obtain ⟨extension, bound, meaning⟩ := buildId_correct reader policy frame capacity depth id heap room a made
          exact ⟨reader.source id, rfl, extension, bound, meaning⟩
  | atom value =>
      cases built
      exact ⟨.atom (.inl value), rfl, extends_refl _, room, .scalar value⟩
  | node left right ihLeft ihRight =>
      obtain ⟨a, leftBuilt, remaining⟩ := Option.bind_eq_some_iff.mp built
      obtain ⟨b, rightBuilt, remaining⟩ := Option.bind_eq_some_iff.mp remaining
      obtain ⟨parent, emitted, equal⟩ := Option.bind_eq_some_iff.mp remaining
      simp only [Option.pure_def, Option.some.injEq] at equal
      subst result
      obtain ⟨p, leftSource, leftExtension, leftRoom, leftMeaning⟩ :=
        ihLeft (depth - 1) holes heap room a leftBuilt
      obtain ⟨q, rightSource, rightExtension, rightRoom, rightMeaning⟩ :=
        ihRight (depth - 1) a.remaining a.heap leftRoom b rightBuilt
      have joined := emit_correct reader capacity b.heap a.root b.root (encode frame p) (encode frame q)
        (denotes_extends reader rightExtension leftMeaning) rightMeaning parent emitted
      refine ⟨.node p q, ?_, extends_trans (extends_trans leftExtension rightExtension) joined.1,
        joined.2.1, joined.2.2⟩
      simp [reconstruct, leftSource, rightSource]

abbrev Exposed (Atom Var Id : Type) :=
  StoredIdViews.Head Atom (ScopedVar Var) (Ref Atom Var Id)

inductive HeadDenotes (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (heap : Heap Atom Var Id) : Exposed Atom Var Id → LogicTerm Atom Var → Prop where
  | atom (value : Atom) : HeadDenotes reader heap (.atom value) (.const value)
  | cell (name : ScopedVar Var) : HeadDenotes reader heap (.cell name) (.var name)
  | node {left right : Ref Atom Var Id} {a b : LogicTerm Atom Var} :
      Denotes reader heap left a → Denotes reader heap right b →
      HeadDenotes reader heap (.node left right) (pair a b)

def rawExpose (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool)
    (heap : Heap Atom Var Id) : Ref Atom Var Id → Option (Exposed Atom Var Id)
  | .scalar value => some (.atom value)
  | .header index => heap[index]?.map fun children => .node children.1 children.2
  | .borrowed view =>
      if readable view then some (match StoredIdViews.head reader view with
        | .atom value => .atom value
        | .cell name => .cell name
        | .node left right => .node (.borrowed left) (.borrowed right))
      else none

/-- Unsupported equality is made unknown BEFORE constructor mismatch or
leaf comparison. The supplied observer recognizes only ordinary structure. -/
def expose (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (ref : Ref Atom Var Id) : Option (Exposed Atom Var Id) :=
  match rawExpose reader readable heap ref with
  | some (.atom value) => if safeLeaf value then some (.atom value) else none
  | other => other

theorem rawExpose_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool)
    (heap : Heap Atom Var Id) (ref : Ref Atom Var Id) (value : LogicTerm Atom Var)
    (denotes : Denotes reader heap ref value) (head : Exposed Atom Var Id)
    (exposed : rawExpose reader readable heap ref = some head) :
    HeadDenotes reader heap head value := by
  cases denotes with
  | scalar value => cases exposed; exact .atom value
  | header found left right =>
      simp only [rawExpose, found, Option.map_some, Option.some.injEq] at exposed
      subst head
      exact .node left right
  | borrowed view =>
      simp only [rawExpose] at exposed
      split at exposed
      · have correct := StoredIdViews.head_correct reader view
        cases inspected : StoredIdViews.head reader view with
        | atom a =>
            simp only [inspected, Option.some.injEq] at exposed
            subst head
            rw [inspected] at correct
            rw [← correct]
            exact .atom a
        | cell name =>
            simp only [inspected, Option.some.injEq] at exposed
            subst head
            rw [inspected] at correct
            rw [← correct]
            exact .cell name
        | node left right =>
            simp only [inspected, Option.some.injEq] at exposed
            subst head
            rw [inspected] at correct
            rw [← correct]
            exact .node (.borrowed left) (.borrowed right)
      · contradiction

theorem expose_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (ref : Ref Atom Var Id) (value : LogicTerm Atom Var)
    (denotes : Denotes reader heap ref value) (head : Exposed Atom Var Id)
    (exposed : expose reader readable safeLeaf heap ref = some head) :
    HeadDenotes reader heap head value := by
  unfold expose at exposed
  cases raw : rawExpose reader readable heap ref with
  | none => simp [raw] at exposed
  | some found =>
      cases found <;> simp only [raw] at exposed
      · split at exposed
        · cases exposed
          exact rawExpose_correct reader readable heap ref value denotes _ raw
        · contradiction
      · cases exposed; exact rawExpose_correct reader readable heap ref value denotes _ raw
      · cases exposed; exact rawExpose_correct reader readable heap ref value denotes _ raw

structure Probe (Atom Var Id : Type) where
  possible : Bool
  remaining : Nat
  observed : List (Ref Atom Var Id × Ref Atom Var Id)
  deriving DecidableEq

def continueProbe (first : Probe Atom Var Id) (later : Nat → Probe Atom Var Id) : Probe Atom Var Id :=
  if !first.possible || first.remaining == 0 then first
  else let next := later first.remaining
       {next with observed := first.observed ++ next.observed}

omit [DecidableEq Var] in
theorem continueProbe_account (credit : Nat) (first : Probe Atom Var Id)
    (later : Nat → Probe Atom Var Id)
    (earlier : first.observed.length + first.remaining = credit)
    (tail : ∀ remaining, (later remaining).observed.length + (later remaining).remaining = remaining) :
    (continueProbe first later).observed.length + (continueProbe first later).remaining = credit := by
  unfold continueProbe
  split
  · exact earlier
  · simp only [List.length_append]
    have next := tail first.remaining
    omega

omit [DecidableEq Var] in
theorem continueProbe_possible (first : Probe Atom Var Id) (later : Nat → Probe Atom Var Id)
    (earlier : first.possible = true) (tail : ∀ remaining, (later remaining).possible = true) :
    (continueProbe first later).possible = true := by
  unfold continueProbe
  split
  · exact earlier
  · exact tail _

/-- One unit pays for one observed pair. The shared work purse stops the
whole probe when exhausted, including before another sibling is visited. -/
def probe [DecidableEq Atom] (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) : Nat → Nat → Ref Atom Var Id → Ref Atom Var Id → Probe Atom Var Id
  | _, 0, _, _ => ⟨true, 0, []⟩
  | depth, credit + 1, left, right =>
      let result : Probe Atom Var Id := match expose reader readable safeLeaf heap left with
        | none => ⟨true, credit, []⟩
        | some p => match expose reader readable safeLeaf heap right with
          | none => ⟨true, credit, []⟩
          | some q => match p with
            | .cell _ => ⟨true, credit, []⟩
            | .atom a => match q with
              | .cell _ => ⟨true, credit, []⟩
              | .atom b => ⟨decide (a = b), credit, []⟩
              | .node _ _ => ⟨false, credit, []⟩
            | .node a b => match q with
              | .cell _ => ⟨true, credit, []⟩
              | .atom _ => ⟨false, credit, []⟩
              | .node c d => match depth with
                | 0 => ⟨true, credit, []⟩
                | remaining + 1 => continueProbe
                    (probe reader readable safeLeaf heap remaining credit a c)
                    (fun rest => probe reader readable safeLeaf heap remaining rest b d)
      {result with observed := (left, right) :: result.observed}

theorem probe_account [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (depth credit : Nat) (left right : Ref Atom Var Id) :
    (probe reader readable safeLeaf heap depth credit left right).observed.length +
      (probe reader readable safeLeaf heap depth credit left right).remaining = credit := by
  induction depth generalizing credit left right with
  | zero =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : expose reader readable safeLeaf heap left with
          | none => simp [Nat.add_comm]
          | some a =>
              cases q : expose reader readable safeLeaf heap right with
              | none => simp [Nat.add_comm]
              | some b => cases a <;> cases b <;> simp [Nat.add_comm]
  | succ depth ih =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : expose reader readable safeLeaf heap left with
          | none => simp [Nat.add_comm]
          | some a =>
              cases q : expose reader readable safeLeaf heap right with
              | none => simp [Nat.add_comm]
              | some b =>
                  cases a with
                  | cell name => simp [Nat.add_comm]
                  | atom value => cases b <;> simp [Nat.add_comm]
                  | node l r =>
                      cases b with
                      | cell name => simp [Nat.add_comm]
                      | atom value => simp [Nat.add_comm]
                      | node a b =>
                          have rest := continueProbe_account credit
                            (probe reader readable safeLeaf heap depth credit l a)
                            (fun rest => probe reader readable safeLeaf heap depth rest r b)
                            (ih credit l a) (fun rest => ih rest r b)
                          simp only [List.length_cons]
                          omega

/-- No constructor clash can reject a genuine unifier. The SAME simultaneous
substitution acts on query and row variables, preserving their distinct frames. -/
theorem probe_keeps_unifier [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (depth credit : Nat) (left right : Ref Atom Var Id)
    (a b : LogicTerm Atom Var) (leftMeaning : Denotes reader heap left a)
    (rightMeaning : Denotes reader heap right b)
    (θ : Mettapedia.Logic.LP.Subst (signature Atom Var)) (unified : θ.applyTerm a = θ.applyTerm b) :
    (probe reader readable safeLeaf heap depth credit left right).possible = true := by
  induction depth generalizing credit left right a b with
  | zero =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : expose reader readable safeLeaf heap left with
          | none => rfl
          | some head =>
              cases q : expose reader readable safeLeaf heap right with
              | none => rfl
              | some other =>
                  have hp := expose_correct reader readable safeLeaf heap left a leftMeaning head p
                  have hq := expose_correct reader readable safeLeaf heap right b rightMeaning other q
                  cases hp <;> cases hq <;>
                    simp_all [Subst.applyTerm, pair]
  | succ depth ih =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : expose reader readable safeLeaf heap left with
          | none => rfl
          | some head =>
              cases q : expose reader readable safeLeaf heap right with
              | none => rfl
              | some other =>
                  have hp := expose_correct reader readable safeLeaf heap left a leftMeaning head p
                  have hq := expose_correct reader readable safeLeaf heap right b rightMeaning other q
                  cases hp with
                  | cell name => rfl
                  | atom x =>
                      cases hq with
                      | cell name => rfl
                      | atom y =>
                          simp only [Subst.applyTerm_const, Term.const.injEq] at unified
                          subst y
                          simp
                      | node hc hd => simp [Subst.applyTerm, pair] at unified
                  | @node l r a b hl hr =>
                      cases hq with
                      | cell name => rfl
                      | atom value => simp [Subst.applyTerm, pair] at unified
                      | @node targetLeft targetRight c d hc hd =>
                          rw [apply_pair, apply_pair, pair_eq_iff] at unified
                          exact continueProbe_possible _ _
                            (ih credit l targetLeft a c hl hc unified.1)
                            (fun remaining => ih remaining r targetRight b d hr hd unified.2)

structure Row (Atom Id : Type) where
  shape : Skel Atom
  holes : List Id
  frame : Nat
  deriving DecidableEq

/-- The independent source demands exact consumption of the compact row. -/
def sourceRow (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (row : Row Atom Id) :
    Option (LogicTerm Atom Var) :=
  match reconstruct reader row.shape row.holes with
  | some (value, []) => some (encode row.frame value)
  | _ => none

def possible [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id) : Bool :=
  match buildRow reader policy row.frame capacity row.shape readDepth row.holes [] with
  | none => true
  | some result =>
      if result.remaining.isEmpty then
        (probe reader readable safeLeaf result.heap probeDepth work (.borrowed query) result.root).possible
      else true

theorem possible_keeps_unifier [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id) (value : LogicTerm Atom Var) (source : sourceRow reader row = some value)
    (θ : Mettapedia.Logic.LP.Subst (signature Atom Var))
    (unified : θ.applyTerm (StoredIdViews.meaning reader query) = θ.applyTerm value) :
    possible reader policy readable safeLeaf capacity readDepth probeDepth work query row = true := by
  cases built : buildRow reader policy row.frame capacity row.shape readDepth row.holes [] with
  | none => simp [possible, built]
  | some result =>
      rw [possible, built]
      change (if result.remaining.isEmpty then
        (probe reader readable safeLeaf result.heap probeDepth work (.borrowed query) result.root).possible
        else true) = true
      by_cases exactHoles : result.remaining.isEmpty = true
      · rw [if_pos exactHoles]
        have empty := List.isEmpty_iff.mp exactHoles
        obtain ⟨term, reconstructed, _, _, denotes⟩ :=
          buildRow_correct reader policy row.frame capacity row.shape readDepth row.holes []
            (by simp) result built
        have same : encode row.frame term = value := by
          simpa [sourceRow, reconstructed, empty] using source
        rw [same] at denotes
        exact probe_keeps_unifier reader readable safeLeaf result.heap probeDepth work
          (.borrowed query) result.root (StoredIdViews.meaning reader query) value
          (.borrowed query) denotes θ unified
      · exact if_neg exactHoles

/-- A rejected compact occurrence has no solution under any simultaneous
substitution. This is the negative certificate used to remove an alternative. -/
theorem rejected_row_has_no_unifier [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id) (value : LogicTerm Atom Var) (source : sourceRow reader row = some value)
    (rejected : possible reader policy readable safeLeaf capacity readDepth probeDepth work query row = false) :
    ∀ θ : Mettapedia.Logic.LP.Subst (signature Atom Var),
      θ.applyTerm (StoredIdViews.meaning reader query) ≠ θ.applyTerm value := by
  intro θ unified
  have kept := possible_keeps_unifier reader policy readable safeLeaf capacity readDepth probeDepth work
    query row value source θ unified
  rw [rejected] at kept
  cases kept

theorem unavailable_readback_keeps_candidate [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id)
    (unknown : buildRow reader policy row.frame capacity row.shape readDepth row.holes [] = none) :
    possible reader policy readable safeLeaf capacity readDepth probeDepth work query row = true := by
  simp [possible, unknown]

theorem zero_probe_work_keeps_candidate [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id) :
    possible reader policy readable safeLeaf capacity readDepth probeDepth 0 query row = true := by
  unfold possible
  split
  · rfl
  · split <;> simp only [probe]

/-- The ordinary source matcher is the maintained total tree unifier. Its
complete reconstruction is not called by the private candidate filter. -/
def solve [DecidableEq Atom] (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (query : StoredView (Var := Var) (Id := Id)) (row : Row Atom Id) :
    Option (Mettapedia.Logic.LP.Subst (signature Atom Var)) :=
  (sourceRow reader row).bind fun value => unifyTotal [(StoredIdViews.meaning reader query, value)]

theorem solved_row_kept [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (row : Row Atom Id) (θ : Mettapedia.Logic.LP.Subst (signature Atom Var))
    (solved : solve reader query row = some θ) :
    possible reader policy readable safeLeaf capacity readDepth probeDepth work query row = true := by
  obtain ⟨value, source, ran⟩ := Option.bind_eq_some_iff.mp solved
  have sound := unifyTotal_sound _ θ ran
  exact possible_keeps_unifier reader policy readable safeLeaf capacity readDepth probeDepth work query
    row value source θ
      (sound (StoredIdViews.meaning reader query, value) (List.mem_cons_self ..))

/-- Ordered occurrence filtering composes with the independently executed
matcher. Equal rows remain separate occurrences. -/
theorem matching_occurrences_exact [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work : Nat) (query : StoredView (Var := Var) (Id := Id))
    (rows : List (Row Atom Id)) :
    (rows.filter (possible reader policy readable safeLeaf capacity readDepth probeDepth work query)).filter
        (fun row => (solve reader query row).isSome) =
      rows.filter (fun row => (solve reader query row).isSome) := by
  apply MatchIndexProjection.filter_candidates
  intro row accepted
  cases solved : solve reader query row with
  | none => simp [solved] at accepted
  | some θ => exact solved_row_kept reader policy readable safeLeaf capacity readDepth probeDepth work query row θ solved

namespace Window

variable {Entry Answer : Type}

structure Fetch (Entry : Type) where
  current : Option Entry
  remaining : List Entry
  skipped : List Entry
  reads : Nat
  probed : List Entry
  deriving DecidableEq

/-- At most K refutations per fetch. The first row after budget exhaustion
is returned UNFILTERED; an exhaustion read is still one cursor operation. -/
def fetch (keep : Entry → Bool) : Nat → List Entry → Fetch Entry
  | _, [] => ⟨none, [], [], 1, []⟩
  | 0, row :: rest => ⟨some row, rest, [], 1, []⟩
  | budget + 1, row :: rest =>
      if keep row then ⟨some row, rest, [], 1, [row]⟩
      else let next := fetch keep budget rest
           {next with
             skipped := row :: next.skipped, reads := next.reads + 1,
             probed := row :: next.probed}

theorem fetch_partition (keep : Entry → Bool) (budget : Nat) (rows : List Entry) :
    rows = (fetch keep budget rows).skipped ++
      (fetch keep budget rows).current.toList ++ (fetch keep budget rows).remaining := by
  induction budget generalizing rows with
  | zero => cases rows <;> rfl
  | succ budget ih =>
      cases rows with
      | nil => rfl
      | cons row rest =>
          by_cases kept : keep row = true
          · simp [fetch, kept]
          · simpa [fetch, kept] using congrArg (row :: ·) (ih rest)

theorem fetch_bounds (keep : Entry → Bool) (budget : Nat) (rows : List Entry) :
    (fetch keep budget rows).reads ≤ budget + 1 ∧
      (fetch keep budget rows).probed.length ≤ budget ∧
      (fetch keep budget rows).skipped.length ≤ budget := by
  induction budget generalizing rows with
  | zero => cases rows <;> simp [fetch]
  | succ budget ih =>
      cases rows with
      | nil => simp [fetch]
      | cons row rest =>
          by_cases kept : keep row = true
          · simp [fetch, kept]
          · obtain ⟨reads, probes, skipped⟩ := ih rest
            simp only [fetch, kept, Bool.false_eq_true, if_false, List.length_cons]
            exact ⟨by omega, by omega, by omega⟩

theorem skipped_refuted (keep : Entry → Bool) (budget : Nat) (rows : List Entry) :
    ∀ row ∈ (fetch keep budget rows).skipped, keep row = false := by
  induction budget generalizing rows with
  | zero => cases rows <;> simp [fetch]
  | succ budget ih =>
      cases rows with
      | nil => simp [fetch]
      | cons row rest =>
          by_cases kept : keep row = true
          · simp [fetch, kept]
          · simp only [fetch, kept, Bool.false_eq_true, if_false, List.mem_cons]
            intro item member
            rcases member with rfl | later
            · exact Bool.eq_false_iff.mpr kept
            · exact ih rest item later

theorem fetch_progress (keep : Entry → Bool) (budget : Nat) (rows : List Entry) (item : Entry)
    (returned : (fetch keep budget rows).current = some item) :
    (fetch keep budget rows).remaining.length < rows.length := by
  have parts := fetch_partition keep budget rows
  rw [returned] at parts
  have lengths := congrArg List.length parts
  simp only [Option.toList_some, List.length_append, List.length_singleton] at lengths
  omega

theorem fetch_none_remaining (keep : Entry → Bool) (budget : Nat) (rows : List Entry)
    (exhausted : (fetch keep budget rows).current = none) :
    (fetch keep budget rows).remaining = [] := by
  induction budget generalizing rows with
  | zero => cases rows <;> simp_all [fetch]
  | succ budget ih =>
      cases rows with
      | nil => rfl
      | cons row rest =>
          by_cases kept : keep row = true
          · simp [fetch, kept] at exhausted
          · simpa [fetch, kept] using ih rest (by simpa [fetch, kept] using exhausted)

/-- The bounded client repeatedly fetches, then invokes the ordinary matcher
for each retained occurrence. It does not rescan or replay a dropped prefix. -/
def enumerate (keep : Entry → Bool) (matchRow : Entry → Option Answer) (budget : Nat)
    (rows : List Entry) : List Answer :=
  let next := fetch keep budget rows
  match _returned : next.current with
  | none => []
  | some item => (matchRow item).toList ++ enumerate keep matchRow budget next.remaining
termination_by rows.length
decreasing_by exact fetch_progress keep budget rows item _returned

/-- This generic client law is used below with the proved operational
candidate-soundness theorem, not with an assumed source/target equality. -/
theorem enumerate_exact (keep : Entry → Bool) (matchRow : Entry → Option Answer)
    (sound : ∀ row answer, matchRow row = some answer → keep row = true)
    (budget : Nat) (rows : List Entry) :
    enumerate keep matchRow budget rows = rows.filterMap matchRow := by
  induction rows using (measure (fun rows : List Entry => rows.length)).wf.induction with
  | h rows ih =>
      have parts := fetch_partition keep budget rows
      have noneSkipped : (fetch keep budget rows).skipped.filterMap matchRow = [] := by
        apply List.filterMap_eq_nil_iff.mpr
        intro item member
        cases matched : matchRow item with
        | none => rfl
        | some answer =>
            have kept := sound item answer matched
            have rejected := skipped_refuted keep budget rows item member
            rw [kept] at rejected
            cases rejected
      rw [enumerate]
      cases returned : (fetch keep budget rows).current with
      | none =>
          have emptyRest := fetch_none_remaining keep budget rows returned
          conv_rhs => rw [parts]
          simp only [returned, emptyRest, Option.toList_none, List.append_nil, noneSkipped]
      | some item =>
          rw [ih _ (fetch_progress keep budget rows item returned)]
          conv_rhs => rw [parts]
          simp only [List.filterMap_append, noneSkipped, List.nil_append, returned,
            Option.toList_some, List.filterMap_cons, List.filterMap_nil]
          cases matchRow item <;> rfl

end Window

/-- Complete source results, including each returned substitution and duplicate
occurrence, agree with bounded lazy filtering for every window allowance K. -/
theorem bounded_frontier_exact [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) (policy : Policy Atom Id)
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (capacity readDepth probeDepth work window : Nat) (query : StoredView (Var := Var) (Id := Id))
    (rows : List (Row Atom Id)) :
    Window.enumerate (possible reader policy readable safeLeaf capacity readDepth probeDepth work query)
        (solve reader query) window rows = rows.filterMap (solve reader query) := by
  exact Window.enumerate_exact _ _
    (fun row θ solved => solved_row_kept reader policy readable safeLeaf capacity readDepth probeDepth work
      query row θ solved) window rows

theorem probe_work_bounded [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (depth work : Nat) (left right : Ref Atom Var Id) :
    (probe reader readable safeLeaf heap depth work left right).observed.length ≤ work ∧
      (probe reader readable safeLeaf heap depth work left right).remaining ≤ work := by
  have account := probe_account reader readable safeLeaf heap depth work left right
  exact ⟨by omega, by omega⟩

theorem zero_work_observes_nothing [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (depth : Nat) (left right : Ref Atom Var Id) :
    probe reader readable safeLeaf heap depth 0 left right = ⟨true, 0, []⟩ := by rw [probe]

theorem unsupported_leaf_is_unknown_before_mismatch [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (heap : Heap Atom Var Id) (depth work : Nat) (value : Atom) (right : Ref Atom Var Id)
    (unsupported : safeLeaf value = false) :
    (probe reader readable safeLeaf heap depth work (.scalar value) right).possible = true := by
  cases work with
  | zero => rw [probe]
  | succ work => rw [probe]; simp [expose, rawExpose, unsupported]

namespace Controls

open StoredIdViews

def inspect : Nat → Head Nat Nat Nat
  | 0 => .cell 0
  | 1 => .atom 1
  | 2 => .atom 2
  | 3 => .atom 3
  | 4 => .node 0 0
  | 5 => .node 1 2
  | 6 => .node 2 1
  | 7 => .node 1 1
  | 8 => .node 1 3
  | id => .atom id

def source : Nat → OpenTerm Nat Nat
  | 0 => .atom (.inr 0)
  | 1 => .atom (.inl 1)
  | 2 => .atom (.inl 2)
  | 3 => .atom (.inl 3)
  | 4 => .node (.atom (.inr 0)) (.atom (.inr 0))
  | 5 => .node (.atom (.inl 1)) (.atom (.inl 2))
  | 6 => .node (.atom (.inl 2)) (.atom (.inl 1))
  | 7 => .node (.atom (.inl 1)) (.atom (.inl 1))
  | 8 => .node (.atom (.inl 1)) (.atom (.inl 3))
  | id => .atom (.inl id)

def reader : StoredIdViews.Reader Nat Nat Nat where
  inspect := inspect
  source := source
  faithful := by
    intro id
    rcases id with _ | _ | _ | _ | _ | _ | _ | _ | _ | id <;> rfl

def cold : Policy Nat Nat := ⟨fun _ => false, fun _ => true, fun _ => true, fun _ => true⟩
def warm : Policy Nat Nat := { cold with cached := fun _ => true }
def ordinary (_ : StoredIdViews.View Nat Nat) : Bool := true
def scalar (value : Nat) : Bool := value != 99

def pair12 : Row Nat Nat := ⟨.node .hole .hole, [1, 2], 7⟩
def pair21 : Row Nat Nat := ⟨.node .hole .hole, [2, 1], 7⟩
def repeated : Row Nat Nat := ⟨.node .hole .hole, [0, 0], 7⟩
def subtree : Row Nat Nat := ⟨.hole, [5], 7⟩

/-- A real private header is constructed from two borrowed/stored parts;
the source reconstruction is a separate complete term procedure. -/
theorem private_header_has_exact_hole_coordinates :
    (buildRow reader cold 7 1 pair12.shape 4 pair12.holes []).map
        (fun result => (result.root, result.heap, result.remaining)) =
      some (.header 0, [(.scalar 1, .scalar 2)], []) ∧
      sourceRow reader pair12 = some (pair (.const 1) (.const 2)) := by exact ⟨by decide, rfl⟩

theorem known_constructor_clash_rejects :
    possible reader cold ordinary scalar 8 4 4 32 (.stored 5 0) pair21 = false := by decide

theorem a_genuine_match_survives :
    possible reader cold ordinary scalar 8 4 4 32 (.stored 5 0) pair12 = true := by decide

theorem missing_metadata_keeps_a_genuine_match :
    possible reader { cold with available := fun _ => false } ordinary scalar 8 4 4 32
      (.stored 5 0) pair12 = true := by decide

theorem depth_workspace_and_cache_miss_are_not_rejection :
    possible reader cold ordinary scalar 8 0 4 32 (.stored 6 0) subtree = true ∧
      possible reader cold ordinary scalar 0 4 4 32 (.stored 6 0) subtree = true ∧
      possible reader warm ordinary scalar 0 0 4 32 (.stored 6 0) subtree = false := by decide

theorem unsupported_uncached_scalar_keeps_candidate :
    possible reader cold ordinary scalar 8 4 4 32 (.stored 5 0)
      ⟨.hole, [99], 7⟩ = true := by decide

/-- Cached unsupported data is refused by the probe even though no builder
allocation is required. It is not rejected merely for facing a constructor. -/
theorem unsupported_cached_leaf_is_not_a_constructor_clash :
    possible reader warm ordinary scalar 8 4 4 32 (.stored 5 0)
      ⟨.hole, [99], 7⟩ = true := by decide

theorem nonordinary_cached_structure_stays_unknown :
    possible reader warm (fun _ => false) scalar 8 4 4 32 (.stored 5 0) pair21 = true := by decide

theorem repeated_open_holes_keep_one_row_scope :
    sourceRow reader repeated = some
      (pair (.var (ScopedVar.at 7 0)) (.var (ScopedVar.at 7 0))) ∧
      possible reader warm ordinary scalar 8 4 4 32 (.stored 7 0) repeated = true := by exact ⟨rfl, by decide⟩

def simultaneous : Mettapedia.Logic.LP.Subst (signature Nat Nat) :=
  fun name => if name.scope = 7 then .const 1 else .var name

theorem shared_substitution_preserves_distinct_query_frame :
    simultaneous.applyTerm (pair (.var (ScopedVar.at 7 0)) (.var (ScopedVar.at 7 0))) =
      pair (.const 1) (.const 1) ∧
      simultaneous.applyTerm (.var (ScopedVar.at 0 0)) = .var (ScopedVar.at 0 0) := by
  constructor
  · rw [apply_pair]
    rfl
  · rfl

/-- A row variable facing a constructor remains possible; canonical names
must not turn it into a rigid constant. -/
theorem uncached_open_variable_declines_exposure_instead_of_rejecting :
    buildId reader cold 7 8 4 0 [] = none ∧
      possible reader cold ordinary scalar 8 4 4 32 (.stored 7 0) repeated = true := by decide

theorem cached_row_variable_is_not_rigid :
    possible reader warm ordinary scalar 8 4 4 32 (.stored 5 0)
      ⟨.hole, [0], 7⟩ = true := by decide

/-- This demonstrates why native filtering must follow frame restoration:
a bound view can refute a row that its restored unbound view can accept. -/
theorem binding_snapshot_changes_refutation :
    let bound : StoredIdViews.View Nat Nat := .subst (ScopedVar.at 0 0) (.stored 1 9) (.stored 0 0)
    possible reader warm ordinary scalar 8 4 4 32 bound ⟨.hole, [2], 7⟩ = false ∧
      possible reader warm ordinary scalar 8 4 4 32 (.stored 0 0) ⟨.hole, [2], 7⟩ = true := by decide

theorem shared_work_purse_stops_before_another_sibling :
    let limited := probe reader ordinary scalar [] 4 2 (.borrowed (.stored 5 0)) (.borrowed (.stored 8 7))
    limited.possible = true ∧ limited.remaining = 0 ∧ limited.observed.length = 2 ∧
      (probe reader ordinary scalar [] 4 3 (.borrowed (.stored 5 0))
        (.borrowed (.stored 8 7))).possible = false := by decide

def keep (row : Nat) : Bool := row == 7
def matchRow (row : Nat) : Option Nat := if row == 7 then some row else none

theorem zero_window_returns_the_first_row_unfiltered :
    Window.fetch keep 0 [1, 2, 7] = ⟨some 1, [2, 7], [], 1, []⟩ := by decide

theorem one_window_returns_the_second_row_unfiltered :
    Window.fetch keep 1 [1, 2, 7] = ⟨some 2, [7], [1], 2, [1]⟩ := by decide

theorem larger_window_has_an_actual_bounded_read_trace :
    Window.fetch keep 2 [1, 2, 7, 7] = ⟨some 7, [7], [1, 2], 3, [1, 2]⟩ := by decide

theorem windows_preserve_order_and_duplicates :
    Window.enumerate keep matchRow 0 [1, 7, 2, 7, 7] = [7, 7, 7] ∧
      Window.enumerate keep matchRow 1 [1, 7, 2, 7, 7] = [7, 7, 7] ∧
      Window.enumerate keep matchRow 8 [1, 7, 2, 7, 7] = [7, 7, 7] := by
  have sound : ∀ row answer, matchRow row = some answer → keep row = true := by
    intro row answer matched
    unfold matchRow at matched
    split at matched
    · simpa [keep] using ‹(row == 7) = true›
    · contradiction
  rw [Window.enumerate_exact keep matchRow sound, Window.enumerate_exact keep matchRow sound,
    Window.enumerate_exact keep matchRow sound]
  decide

/-- Replacing unknown stored variables by a dummy rigid literal would drop
this genuine possible instance. The real builder instead keeps it unknown. -/
theorem dummy_leaf_for_unknown_drops_a_possible_match :
    (probe reader ordinary scalar [] 4 32 (.scalar 1) (.scalar 2)).possible = false ∧
      (probe reader ordinary scalar [] 4 32 (.scalar 1) (.borrowed (.stored 0 7))).possible = true := by decide

/-- A faulty negative certificate loses an actual successful occurrence,
rather than merely changing a diagnostic counter. -/
theorem dropping_a_matching_occurrence_is_detected :
    Window.enumerate (fun _ : Nat => false) matchRow 1 [7] = [] ∧
      ([7] : List Nat).filterMap matchRow = [7] := by
  simp [Window.enumerate, Window.fetch, matchRow]

end Controls

/-! ## Direct stored-header observation

The direct adapter carries the existing stored views and typed skeleton
coordinates, without building a private header heap. Source reconstruction is
independent. Typed slots express the native skeleton/hole-array invariant;
native n-ary/preorder indexing and the work spent skipping an unexposed subtree
are separate obligations. Logical work below counts observed constructor pairs.
-/
namespace Direct

open StoredIdAlignment

/-- Complete source reconstruction, used only in specifications. -/
def slotSource (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) :
    {shape : Skel Atom} → Slots Atom Id shape → OpenTerm Atom Var
  | _, .hole id => reader.source id
  | _, .atom value => .atom (.inl value)
  | _, .node left right => .node (slotSource reader left) (slotSource reader right)

omit [DecidableEq Var] in
theorem reconstruction_of_slots
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    {shape : Skel Atom} (slots : Slots Atom Id shape) (tail : List Id) :
    reconstruct reader shape (slots.values ++ tail) = some (slotSource reader slots, tail) := by
  induction slots generalizing tail with
  | hole id => rfl
  | atom value => rfl
  | node left right ihl ihr =>
      simp [Slots.values, List.append_assoc, reconstruct, ihl, ihr, slotSource]

inductive Ref (Atom Var Id : Type) where
  | view (value : StoredView (Var := Var) (Id := Id))
  | row {shape : Skel Atom} (frame : Nat) (slots : Slots Atom Id shape)

def meaning (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) :
    Ref Atom Var Id → LogicTerm Atom Var
  | .view value => StoredIdViews.meaning reader value
  | .row frame slots => encode frame (slotSource reader slots)

abbrev Head (Atom Var Id : Type) := StoredIdViews.Head Atom (ScopedVar Var) (Ref Atom Var Id)

def viewHead (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (view : StoredView (Var := Var) (Id := Id)) : Head Atom Var Id :=
  match StoredIdViews.head reader view with
  | .atom value => .atom value
  | .cell name => .cell name
  | .node left right => .node (.view left) (.view right)

/-- A successful observation uses stored IDs and skeleton coordinates only;
no source reconstruction, cache population or private header allocation occurs. -/
def rawHead (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) :
    Ref Atom Var Id → Option (Head Atom Var Id)
  | .view view => if readable view then some (viewHead reader view) else none
  | .row frame (.hole id) =>
      if readable (.stored id frame) then some (viewHead reader (.stored id frame)) else none
  | .row _ (.atom value) => some (.atom value)
  | .row frame (.node left right) => some (.node (.row frame left) (.row frame right))

def head (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (ref : Ref Atom Var Id) : Option (Head Atom Var Id) :=
  match rawHead reader readable ref with
  | some (.atom value) => if safeLeaf value then some (.atom value) else none
  | other => other

def headMeaning (reader : Reader (Atom := Atom) (Var := Var) (Id := Id)) :
    Head Atom Var Id → LogicTerm Atom Var
  | .atom value => .const value
  | .cell name => .var name
  | .node left right => pair (meaning reader left) (meaning reader right)

theorem viewHead_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (view : StoredView (Var := Var) (Id := Id)) :
    headMeaning reader (viewHead reader view) = StoredIdViews.meaning reader view := by
  have correct := StoredIdViews.head_correct reader view
  cases exposed : StoredIdViews.head reader view <;>
    simpa [viewHead, exposed, headMeaning, meaning, StoredIdViews.headMeaning] using correct

theorem rawHead_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool)
    (ref : Ref Atom Var Id) (observed : Head Atom Var Id)
    (exposed : rawHead reader readable ref = some observed) :
    headMeaning reader observed = meaning reader ref := by
  cases ref with
  | view view =>
      simp only [rawHead] at exposed
      split at exposed
      · cases exposed; exact viewHead_correct reader view
      · contradiction
  | row frame slots =>
      cases slots with
      | hole id =>
          simp only [rawHead] at exposed
          split at exposed
          · cases exposed; exact viewHead_correct reader (.stored id frame)
          · contradiction
      | atom value => cases exposed; rfl
      | node left right => cases exposed; rfl

theorem head_correct (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (ref : Ref Atom Var Id) (observed : Head Atom Var Id)
    (exposed : head reader readable safeLeaf ref = some observed) :
    headMeaning reader observed = meaning reader ref := by
  unfold head at exposed
  cases raw : rawHead reader readable ref with
  | none => simp [raw] at exposed
  | some actual =>
      cases actual with
      | atom value =>
          simp only [raw] at exposed
          split at exposed
          · cases exposed; exact rawHead_correct reader readable ref (.atom value) raw
          · contradiction
      | cell name =>
          simp only [raw, Option.some.injEq] at exposed
          subst observed
          exact rawHead_correct reader readable ref (.cell name) raw
      | node left right =>
          simp only [raw, Option.some.injEq] at exposed
          subst observed
          exact rawHead_correct reader readable ref (.node left right) raw

structure Result (Atom Var Id : Type) where
  possible : Bool
  remaining : Nat
  observed : List (Ref Atom Var Id × Ref Atom Var Id)

def afterProbe (first : Result Atom Var Id) (later : Nat → Result Atom Var Id) : Result Atom Var Id :=
  if !first.possible || first.remaining == 0 then first
  else let next := later first.remaining
       {next with observed := first.observed ++ next.observed}

omit [DecidableEq Var] in
theorem continue_account (credit : Nat) (first : Result Atom Var Id)
    (later : Nat → Result Atom Var Id)
    (earlier : first.observed.length + first.remaining = credit)
    (tail : ∀ rest, (later rest).observed.length + (later rest).remaining = rest) :
    (afterProbe first later).observed.length + (afterProbe first later).remaining = credit := by
  unfold afterProbe
  split
  · exact earlier
  · simp only [List.length_append]
    have next := tail first.remaining
    omega

omit [DecidableEq Var] in
theorem continue_possible (first : Result Atom Var Id) (later : Nat → Result Atom Var Id)
    (earlier : first.possible = true) (tail : ∀ rest, (later rest).possible = true) :
    (afterProbe first later).possible = true := by
  unfold afterProbe
  split
  · exact earlier
  · exact tail _

/-- Direct target execution observes each exposed head once. Unsupported
heads and variables stay unknown; the shared purse stops sibling traversal. -/
def probe [DecidableEq Atom] (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool) :
    Nat → Nat → Ref Atom Var Id → Ref Atom Var Id → Result Atom Var Id
  | _, 0, _, _ => ⟨true, 0, []⟩
  | depth, credit + 1, left, right =>
      let result : Result Atom Var Id := match head reader readable safeLeaf left with
        | none => ⟨true, credit, []⟩
        | some p => match head reader readable safeLeaf right with
          | none => ⟨true, credit, []⟩
          | some q => match p with
            | .cell _ => ⟨true, credit, []⟩
            | .atom a => match q with
              | .cell _ => ⟨true, credit, []⟩
              | .atom b => ⟨decide (a = b), credit, []⟩
              | .node _ _ => ⟨false, credit, []⟩
            | .node a b => match q with
              | .cell _ => ⟨true, credit, []⟩
              | .atom _ => ⟨false, credit, []⟩
              | .node c d => match depth with
                | 0 => ⟨true, credit, []⟩
                | rest + 1 => afterProbe (probe reader readable safeLeaf rest credit a c)
                    (fun remaining => probe reader readable safeLeaf rest remaining b d)
      {result with observed := (left, right) :: result.observed}

theorem probe_account [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (depth credit : Nat) (left right : Ref Atom Var Id) :
    (probe reader readable safeLeaf depth credit left right).observed.length +
      (probe reader readable safeLeaf depth credit left right).remaining = credit := by
  induction depth generalizing credit left right with
  | zero =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : head reader readable safeLeaf left with
          | none => simp [Nat.add_comm]
          | some a =>
              cases q : head reader readable safeLeaf right with
              | none => simp [Nat.add_comm]
              | some b => cases a <;> cases b <;> simp [Nat.add_comm]
  | succ depth ih =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : head reader readable safeLeaf left with
          | none => simp [Nat.add_comm]
          | some a =>
              cases q : head reader readable safeLeaf right with
              | none => simp [Nat.add_comm]
              | some b =>
                  cases a with
                  | cell name => simp [Nat.add_comm]
                  | atom value => cases b <;> simp [Nat.add_comm]
                  | node l r =>
                      cases b with
                      | cell name => simp [Nat.add_comm]
                      | atom value => simp [Nat.add_comm]
                      | node a b =>
                          have rest := continue_account credit
                            (probe reader readable safeLeaf depth credit l a)
                            (fun rest => probe reader readable safeLeaf depth rest r b)
                            (ih credit l a) (fun rest => ih rest r b)
                          simp only [List.length_cons]
                          omega

/-- A single simultaneous substitution accounts for the query's bindings
and every repeated row-hole variable in its original frame. -/
theorem probe_keeps_unifier [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (depth credit : Nat) (left right : Ref Atom Var Id)
    (θ : Mettapedia.Logic.LP.Subst (signature Atom Var))
    (unified : θ.applyTerm (meaning reader left) = θ.applyTerm (meaning reader right)) :
    (probe reader readable safeLeaf depth credit left right).possible = true := by
  induction depth generalizing credit left right with
  | zero =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : head reader readable safeLeaf left with
          | none => rfl
          | some a =>
              cases q : head reader readable safeLeaf right with
              | none => rfl
              | some b =>
                  have hp := head_correct reader readable safeLeaf left a p
                  have hq := head_correct reader readable safeLeaf right b q
                  rw [← hp, ← hq] at unified
                  clear hp hq
                  cases a <;> cases b <;>
                    simp_all [headMeaning, pair]
  | succ depth ih =>
      cases credit with
      | zero => rfl
      | succ credit =>
          rw [probe]
          cases p : head reader readable safeLeaf left with
          | none => rfl
          | some a =>
              cases q : head reader readable safeLeaf right with
              | none => rfl
              | some b =>
                  have hp := head_correct reader readable safeLeaf left a p
                  have hq := head_correct reader readable safeLeaf right b q
                  rw [← hp, ← hq] at unified
                  clear hp hq
                  cases a with
                  | cell name => rfl
                  | atom value =>
                      cases b with
                      | cell name => rfl
                      | atom other =>
                          simp only [headMeaning, Subst.applyTerm_const, Term.const.injEq] at unified
                          subst other
                          simp
                      | node c d => simp [headMeaning, pair] at unified
                  | node l r =>
                      cases b with
                      | cell name => rfl
                      | atom value => simp [headMeaning, pair] at unified
                      | node a b =>
                          change θ.applyTerm (pair (meaning reader l) (meaning reader r)) =
                            θ.applyTerm (pair (meaning reader a) (meaning reader b)) at unified
                          rw [apply_pair, apply_pair, pair_eq_iff] at unified
                          exact continue_possible _ _ (ih credit l a unified.1)
                            (fun remaining => ih remaining r b unified.2)

structure Kept (Atom Id : Type) where
  shape : Skel Atom
  frame : Nat
  slots : Slots Atom Id shape

def Kept.row (kept : Kept Atom Id) : Row Atom Id :=
  ⟨kept.shape, kept.slots.values, kept.frame⟩

theorem kept_source (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (kept : Kept Atom Id) :
    sourceRow reader kept.row = some (meaning reader (.row kept.frame kept.slots)) := by
  have reconstructed := reconstruction_of_slots reader kept.slots []
  simp only [List.append_nil] at reconstructed
  unfold sourceRow Kept.row
  rw [reconstructed]
  rfl

def possible [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (depth credit : Nat) (query : StoredView (Var := Var) (Id := Id)) (kept : Kept Atom Id) : Bool :=
  (probe reader readable safeLeaf depth credit (.view query) (.row kept.frame kept.slots)).possible

theorem solved_kept [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (depth credit : Nat) (query : StoredView (Var := Var) (Id := Id)) (kept : Kept Atom Id)
    (θ : Mettapedia.Logic.LP.Subst (signature Atom Var))
    (solved : solve reader query kept.row = some θ) :
    possible reader readable safeLeaf depth credit query kept = true := by
  rw [solve, kept_source, Option.bind_some] at solved
  have sound := unifyTotal_sound _ θ solved
  exact probe_keeps_unifier reader readable safeLeaf depth credit
    (.view query) (.row kept.frame kept.slots) θ
    (sound _ (List.mem_cons_self ..))

theorem bounded_frontier_exact [DecidableEq Atom]
    (reader : Reader (Atom := Atom) (Var := Var) (Id := Id))
    (readable : StoredView (Var := Var) (Id := Id) → Bool) (safeLeaf : Atom → Bool)
    (depth credit window : Nat) (query : StoredView (Var := Var) (Id := Id))
    (rows : List (Kept Atom Id)) :
    Window.enumerate (possible reader readable safeLeaf depth credit query)
      (fun kept => solve reader query kept.row) window rows =
      rows.filterMap (fun kept => solve reader query kept.row) := by
  exact Window.enumerate_exact _ _
    (fun kept θ solved => solved_kept reader readable safeLeaf depth credit query kept θ solved)
    window rows

namespace Controls

open BorrowedKeptFrontier.Controls (reader ordinary scalar)

def pair12 : Kept Nat Nat := ⟨.node .hole .hole, 7, .node (.hole 1) (.hole 2)⟩
def pair21 : Kept Nat Nat := ⟨.node .hole .hole, 7, .node (.hole 2) (.hole 1)⟩
def repeated : Kept Nat Nat := ⟨.node .hole .hole, 7, .node (.hole 0) (.hole 0)⟩

theorem direct_known_match_and_clash :
    possible reader ordinary scalar 4 32 (.stored 5 0) pair12 = true ∧
      possible reader ordinary scalar 4 32 (.stored 5 0) pair21 = false := by decide

theorem direct_depth_and_work_remain_conservative :
    possible reader ordinary scalar 0 32 (.stored 5 0) pair21 = true ∧
      possible reader ordinary scalar 4 0 (.stored 5 0) pair21 = true := by decide

theorem repeated_holes_preserve_the_original_scope :
    sourceRow reader repeated.row = some
      (pair (.var (ScopedVar.at 7 0)) (.var (ScopedVar.at 7 0))) ∧
      possible reader ordinary scalar 4 32 (.stored 7 0) repeated = true := by
  exact ⟨rfl, by decide⟩

theorem one_shared_substitution_keeps_repeated_holes :
    BorrowedKeptFrontier.Controls.simultaneous.applyTerm
        (meaning reader (.row 7 repeated.slots)) = pair (.const 1) (.const 1) ∧
      BorrowedKeptFrontier.Controls.simultaneous.applyTerm
        (meaning reader (.view (.stored 0 0))) = .var (ScopedVar.at 0 0) := by
  constructor
  · rw [show meaning reader (.row 7 repeated.slots) =
        pair (.var (ScopedVar.at 7 0)) (.var (ScopedVar.at 7 0)) from rfl, apply_pair]
    rfl
  · rfl

theorem unsupported_values_are_unknown_before_kind_mismatch :
    (probe reader ordinary scalar 4 32 (.view (.stored 99 0))
      (.row 7 pair12.slots)).possible = true ∧
      possible reader (fun _ => false) scalar 4 32 (.stored 5 0) pair21 = true := by decide

theorem work_purse_stops_before_a_later_sibling :
    let right : Ref Nat Nat Nat := .row 7 (.node (.hole 1) (.hole 3))
    let limited := probe reader ordinary scalar 4 2 (.view (.stored 5 0)) right
    limited.possible = true ∧ limited.remaining = 0 ∧ limited.observed.length = 2 ∧
      (probe reader ordinary scalar 4 3 (.view (.stored 5 0)) right).possible = false := by decide

/-- An unknown first subtree does not shift the next rigid coordinate. -/
theorem unknown_subtree_retains_the_next_coordinate :
    let query : Ref Nat Nat Nat := .row 0 (.node (.hole 0) (.hole 1))
    let row : Ref Nat Nat Nat := .row 7 (.node (.node (.hole 1) (.hole 2)) (.hole 2))
    (probe reader ordinary scalar 4 32 query row).possible = false := by decide

theorem restored_query_is_not_the_previous_answer_binding :
    let bound : StoredView (Var := Nat) (Id := Nat) :=
      .subst (ScopedVar.at 0 0) (.stored 1 9) (.stored 0 0)
    let row : Kept Nat Nat := ⟨.hole, 7, .hole 2⟩
    possible reader ordinary scalar 4 32 bound row = false ∧
      possible reader ordinary scalar 4 32 (.stored 0 0) row = true := by decide

theorem direct_windows_preserve_duplicate_occurrences (window : Nat) :
    Window.enumerate (possible reader ordinary scalar 4 32 (.stored 5 0))
      (fun kept => solve reader (.stored 5 0) kept.row) window [pair12, pair21, pair12] =
      ([pair12, pair21, pair12].filterMap fun kept => solve reader (.stored 5 0) kept.row) :=
  Direct.bounded_frontier_exact reader ordinary scalar 4 32 window (.stored 5 0) _

/-- A wrong native coordinate mapping would reject this exact source row. -/
theorem swapped_hole_coordinates_lose_a_possible_match :
    sourceRow reader pair12.row = some (StoredIdViews.meaning reader (.stored 5 0)) ∧
      possible reader ordinary scalar 4 32 (.stored 5 0) pair12 = true ∧
      possible reader ordinary scalar 4 32 (.stored 5 0) pair21 = false := by
  exact ⟨rfl, by decide⟩

theorem unknown_variable_cannot_be_replaced_by_a_rigid_literal :
    (probe reader ordinary scalar 4 32 (.view (.stored 1 0))
      (.row 7 (.hole 0))).possible = true ∧
      (probe reader ordinary scalar 4 32 (.view (.stored 1 0))
        (.row 7 (.hole 2))).possible = false := by decide

end Controls

end Direct

end Mettapedia.Machines.BorrowedKeptFrontier
