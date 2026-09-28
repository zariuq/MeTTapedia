import Mettapedia.Machines.ConstructorContext
import Mathlib.Tactic

/-!
# Private constructor spines: filling, sealing and publication

The heap contains real addresses and independently mutable holes and cached
summaries. Resident values stand for already complete, externally owned
subgraphs. A fresh spine occupies an address interval; the addresses are
stable through filling and sealing. This is a sequential model, not a model
of C atom layout or a concurrent collector.

A spine's completed shape and its sealed summaries are separate invariants.
Sealing updates metadata only, from the innermost cell out. The decoder reads
the resulting heap, not a stored denotation. Publication requires the sealed
invariant. Private updates preserve arbitrary observations whose reads avoid
the changed cells. Collectors may inspect draft shape without consulting a
summary; normal atom observers may not.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorContextHeap

open ConstructorContext

universe u v w
variable {Label : Type u} {Value : Type v} {Summary : Type w}

inductive Ref (Value : Type v)
  | resident (value : Value)
  | cell (address : Nat)
  deriving Repr

structure Cell (Label : Type u) (Value : Type v) (Summary : Type w) where
  frame : Frame Label Value
  hole : Option (Ref Value)
  cache : Option Summary

abbrev Heap (Label : Type u) (Value : Type v) (Summary : Type w) :=
  Nat → Option (Cell Label Value Summary)

def put (heap : Heap Label Value Summary) (address : Nat)
    (cell : Cell Label Value Summary) : Heap Label Value Summary :=
  Function.update heap address (some cell)

@[simp] theorem put_same (heap : Heap Label Value Summary) (address : Nat)
    (cell : Cell Label Value Summary) : put heap address cell address = some cell := by
  simp [put]

@[simp] theorem put_other (heap : Heap Label Value Summary) (address other : Nat)
    (cell : Cell Label Value Summary) (different : other ≠ address) :
    put heap address cell other = heap other := by simp [put, different]

def modify (heap : Heap Label Value Summary) (address : Nat)
    (f : Cell Label Value Summary → Cell Label Value Summary) : Heap Label Value Summary :=
  Function.update heap address ((heap address).map f)

/-- Independent holes may be filled in either order. This permits linking
as cells are entered, even though the reference construction links on return. -/
theorem modify_commute (heap : Heap Label Value Summary) (a b : Nat)
    (f g : Cell Label Value Summary → Cell Label Value Summary) (distinct : a ≠ b) :
    modify (modify heap a f) b g = modify (modify heap b g) a f := by
  funext i
  by_cases ia : i = a <;> by_cases ib : i = b <;>
    simp_all [modify, Function.update]

def fill (heap : Heap Label Value Summary) (address : Nat) (value : Ref Value) :
    Heap Label Value Summary :=
  modify heap address fun cell => { cell with hole := some value, cache := none }

/-- One entry step allocates a fresh open cell before linking it from the
previous tip. No pointer to unallocated storage is introduced by this order. -/
def extend (heap : Heap Label Value Summary) (tip fresh : Nat)
    (frame : Frame Label Value) : Heap Label Value Summary :=
  fill (put heap fresh ⟨frame, none, none⟩) tip (.cell fresh)

theorem extend_new_cell (heap : Heap Label Value Summary) (tip fresh : Nat)
    (frame : Frame Label Value) (different : fresh ≠ tip) :
    extend heap tip fresh frame fresh = some ⟨frame, none, none⟩ := by
  simp [extend, fill, modify, Function.update, different]

theorem extend_tip (heap : Heap Label Value Summary) (tip fresh : Nat)
    (frame : Frame Label Value) (cell : Cell Label Value Summary)
    (different : tip ≠ fresh) (present : heap tip = some cell) :
    extend heap tip fresh frame tip =
      some { cell with hole := some (.cell fresh), cache := none } := by
  simp [extend, fill, modify, Function.update, put, different, present]

/-- A fresh cell may have no hole yet, but it has no falsely final cache. -/
theorem extend_unpublished (heap : Heap Label Value Summary) (tip fresh : Nat)
    (frame : Frame Label Value) (different : fresh ≠ tip) :
    (extend heap tip fresh frame fresh).bind Cell.cache = none := by
  rw [extend_new_cell heap tip fresh frame different]
  rfl

@[simp] theorem extend_other (heap : Heap Label Value Summary) (tip fresh i : Nat)
    (frame : Frame Label Value) (notTip : i ≠ tip) (notFresh : i ≠ fresh) :
    extend heap tip fresh frame i = heap i := by
  simp [extend, fill, modify, put, Function.update, notTip, notFresh]

/-- The collector may traverse draft edges, provided holes are represented
explicitly and every filled pointer already addresses an allocated cell. -/
def NoDangling (heap : Heap Label Value Summary) : Prop :=
  ∀ a cell, heap a = some cell → ∀ b, cell.hole = some (.cell b) →
    ∃ child, heap b = some child

theorem extend_preserves_presence (heap : Heap Label Value Summary)
    (tip fresh : Nat) (frame : Frame Label Value) (distinct : fresh ≠ tip)
    (i : Nat) (cell : Cell Label Value Summary) (present : heap i = some cell) :
    ∃ result, extend heap tip fresh frame i = some result := by
  by_cases isTip : i = tip
  · subst i
    exact ⟨_, extend_tip heap tip fresh frame cell (Ne.symm distinct) present⟩
  · by_cases isFresh : i = fresh
    · subst i
      exact ⟨_, extend_new_cell heap tip fresh frame distinct⟩
    · exact ⟨cell, by rw [extend_other _ _ _ _ _ isTip isFresh]; exact present⟩

theorem extend_no_dangling (heap : Heap Label Value Summary)
    (tip fresh : Nat) (frame : Frame Label Value) (distinct : fresh ≠ tip)
    (safe : NoDangling heap) : NoDangling (extend heap tip fresh frame) := by
  intro a cell present b hole
  by_cases isTip : a = tip
  · subst a
    cases old : heap tip with
    | none => simp [extend, fill, modify, put, Function.update, Ne.symm distinct, old] at present
    | some previous =>
        rw [extend_tip heap tip fresh frame previous (Ne.symm distinct) old] at present
        cases present
        have eq : fresh = b := by simpa using hole
        subst b
        exact ⟨_, extend_new_cell heap tip fresh frame distinct⟩
  · by_cases isFresh : a = fresh
    · subst a
      rw [extend_new_cell heap tip fresh frame distinct] at present
      cases present
      cases hole
    · rw [extend_other _ _ _ _ _ isTip isFresh] at present
      obtain ⟨child, hc⟩ := safe a cell present b hole
      exact extend_preserves_presence heap tip fresh frame distinct b child hc

/-- Read the actual pointer chain. `none` includes open holes, missing cells,
and insufficient fuel. No cached denotation is substituted for heap reading. -/
def decode (build : Label → List Value → Value) (heap : Heap Label Value Summary) :
    Nat → Ref Value → Option Value
  | _, .resident value => some value
  | 0, .cell _ => none
  | fuel + 1, .cell address =>
      match heap address with
      | none => none
      | some cell => match cell.hole with
        | none => none
        | some next => (decode build heap fuel next).map (cell.frame.apply build)

/-- A completed pointer spine, regardless of whether its summaries are ready. -/
inductive Chain (heap : Heap Label Value Summary) :
    Nat → List (Frame Label Value) → Value → Prop
  | nil (base : Nat) (value : Value) : Chain heap base [] value
  | cons {base : Nat} {frame : Frame Label Value} {rest : List (Frame Label Value)}
      {value : Value} {cell : Cell Label Value Summary}
      (present : heap base = some cell) (frame_eq : cell.frame = frame)
      (hole_eq : cell.hole = some (if rest.isEmpty then .resident value else .cell (base + 1)))
      (tail : Chain heap (base + 1) rest value) :
      Chain heap base (frame :: rest) value

/-- Heap changes strictly before the spine do not change its shape. -/
theorem Chain.congr {heap other : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (chain : Chain heap base frames value)
    (same : ∀ i, base ≤ i → heap i = other i) : Chain other base frames value := by
  induction chain with
  | nil => exact .nil _ _
  | @cons base frame rest value cell present frame_eq hole_eq tail ih =>
      exact .cons (by rw [← same base (by omega)]; exact present) frame_eq hole_eq
        (ih fun i hi => same i (by omega))

/-- The physical heap has exactly the functional context's value. -/
theorem Chain.decode_exact (build : Label → List Value → Value)
    {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (chain : Chain heap base frames value) :
    decode build heap frames.length
      (if frames.isEmpty then .resident value else .cell base) =
      some (plug build frames value) := by
  induction chain with
  | nil => rfl
  | @cons base frame rest value cell present frame_eq hole_eq tail ih =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      simp only [decode, present, hole_eq, ih, frame_eq, plug_cons]
      rfl

/-- A reference construction allocates each frame once, with an empty hole,
then fills that hole. It supplies the postcondition required of forward entry
and linking; disjoint hole updates commute. -/
def reserve (heap : Heap Label Value Summary) (base : Nat) :
    List (Frame Label Value) → Value → Heap Label Value Summary
  | [], _ => heap
  | frame :: rest, value =>
      let allocated := put heap base ⟨frame, none, none⟩
      let inner := reserve allocated (base + 1) rest value
      fill inner base (if rest.isEmpty then .resident value else .cell (base + 1))

theorem reserve_below (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (i : Nat) (before : i < base) :
    reserve heap base frames value i = heap i := by
  induction frames generalizing heap base with
  | nil => rfl
  | cons frame rest ih =>
      simp only [reserve, fill, modify]
      rw [Function.update_of_ne (by omega)]
      rw [ih _ _ (by omega)]
      exact put_other _ _ _ _ (by omega)

theorem reserve_chain (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    Chain (reserve heap base frames value) base frames value := by
  induction frames generalizing heap base with
  | nil => exact .nil _ _
  | cons frame rest ih =>
      let allocated := put heap base (⟨frame, none, none⟩ : Cell Label Value Summary)
      let inner := reserve allocated (base + 1) rest value
      have atBase : inner base = some ⟨frame, none, none⟩ := by
        rw [show inner base = allocated base from reserve_below _ _ _ _ _ (by omega)]
        exact put_same _ _ _
      apply Chain.cons (cell := ⟨frame,
        some (if rest.isEmpty then .resident value else .cell (base + 1)), none⟩)
      · change (fill inner base _ base) = _
        simp [fill, modify, atBase]
      · rfl
      · rfl
      · apply (ih allocated (base + 1)).congr
        intro i hi
        simp only [reserve, fill, modify]
        rw [Function.update_of_ne (by omega)]

/-- Allocation at a different address commutes with a private mutation. -/
theorem modify_put (heap : Heap Label Value Summary) (a b : Nat)
    (cell : Cell Label Value Summary)
    (f : Cell Label Value Summary → Cell Label Value Summary) (different : a ≠ b) :
    modify (put heap a cell) b f = put (modify heap b f) a cell := by
  funext i
  by_cases ia : i = a <;> by_cases ib : i = b <;>
    simp_all [modify, put, Function.update]

theorem reserve_modify_below (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (i : Nat)
    (f : Cell Label Value Summary → Cell Label Value Summary) (before : i < base) :
    reserve (modify heap i f) base frames value =
      modify (reserve heap base frames value) i f := by
  induction frames generalizing heap base with
  | nil => rfl
  | cons frame rest ih =>
      simp only [reserve]
      rw [← modify_put heap base i _ f (by omega), ih _ _ (by omega)]
      exact modify_commute _ i base f _ (by omega)

/-- The forward executor links the newly allocated child immediately, then
continues with that child's open destination. -/
def enterTail (heap : Heap Label Value Summary) (tip : Nat) :
    List (Frame Label Value) → Value → Heap Label Value Summary
  | [], value => fill heap tip (.resident value)
  | frame :: rest, value =>
      enterTail (extend heap tip (tip + 1) frame) (tip + 1) rest value

/-- Forward entry and immediate linking have the same heap result as the
reference's delayed, commuting pointer writes. -/
theorem enterTail_eq (heap : Heap Label Value Summary) (tip : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    enterTail heap tip frames value =
      fill (reserve heap (tip + 1) frames value) tip
        (if frames.isEmpty then .resident value else .cell (tip + 1)) := by
  induction frames generalizing heap tip with
  | nil => rfl
  | cons frame rest ih =>
      rw [enterTail, ih]
      simp only [extend, fill]
      rw [reserve_modify_below _ (tip + 1 + 1) rest value tip _ (by omega)]
      rw [modify_commute _ tip (tip + 1) _ _ (by omega)]
      rfl

def reserveForward (heap : Heap Label Value Summary) (base : Nat) :
    List (Frame Label Value) → Value → Heap Label Value Summary
  | [], _ => heap
  | frame :: rest, value =>
      enterTail (put heap base ⟨frame, none, none⟩) base rest value

theorem reserveForward_eq (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    reserveForward heap base frames value = reserve heap base frames value := by
  cases frames with
  | nil => rfl
  | cons frame rest => exact enterTail_eq _ _ _ _

variable (A : SummaryAlgebra Label Value Summary)

/-- Sealing changes only the cache. It allocates no cells and does not change
any pointer. Recursion is the mathematical counterpart of a reverse loop over
the retained address stack. -/
def finalize (heap : Heap Label Value Summary) (base : Nat) :
    Nat → Summary → Option (Heap Label Value Summary × Summary)
  | 0, result => some (heap, result)
  | n + 1, result =>
      match finalize heap (base + 1) n result with
      | none => none
      | some (inner, childSummary) => match inner base with
        | none => none
        | some cell =>
            let summary := A.act cell.frame childSummary
            some (put inner base { cell with cache := some summary }, summary)

theorem seal_below (heap : Heap Label Value Summary) (base count : Nat)
    (summary : Summary) (out : Heap Label Value Summary) (result : Summary)
    (run : finalize A heap base count summary = some (out, result))
    (i : Nat) (before : i < base) : out i = heap i := by
  induction count generalizing heap base out result with
  | zero => cases run; rfl
  | succ count ih =>
      simp only [finalize] at run
      cases child : finalize A heap (base + 1) count summary with
      | none => simp [child] at run
      | some pair =>
          rcases pair with ⟨inner, childSummary⟩
          cases cell : inner base with
          | none => simp [child, cell] at run
          | some c =>
              simp only [child, cell,
                Option.some.injEq, Prod.mk.injEq] at run
              rcases run with ⟨rfl, rfl⟩
              rw [put_other _ _ _ _ (by omega)]
              exact ih _ _ _ _ child (by omega)

/-- Finalization can pause after any inner suffix and resume on the remaining
outer cells. This is the law for bounded batches and cancellation points. -/
theorem finalize_split (heap : Heap Label Value Summary) (base outer inner : Nat)
    (summary : Summary) :
    finalize A heap base (outer + inner) summary =
      match finalize A heap (base + outer) inner summary with
      | none => none
      | some (next, result) => finalize A next base outer result := by
  induction outer generalizing heap base with
  | zero =>
      simp only [Nat.zero_add, Nat.add_zero]
      cases finalize A heap base inner summary <;> rfl
  | succ outer ih =>
      rw [Nat.succ_add, finalize, ih]
      rw [show base + 1 + outer = base + (outer + 1) by omega]
      cases finalize A heap (base + (outer + 1)) inner summary with
      | none => rfl
      | some pair => cases pair; rfl

/-- Every cell has its final pointer and exact summary before publication. -/
inductive Ready (heap : Heap Label Value Summary) :
    Nat → List (Frame Label Value) → Value → Prop
  | nil (base : Nat) (value : Value) : Ready heap base [] value
  | cons {base : Nat} {frame : Frame Label Value} {rest : List (Frame Label Value)}
      {value : Value} {cell : Cell Label Value Summary}
      (present : heap base = some cell) (frame_eq : cell.frame = frame)
      (hole_eq : cell.hole = some (if rest.isEmpty then .resident value else .cell (base + 1)))
      (cache_eq : cell.cache = some (A.observe (plug A.build (frame :: rest) value)))
      (tail : Ready heap (base + 1) rest value) :
      Ready heap base (frame :: rest) value

theorem Ready.chain {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value) : Chain heap base frames value := by
  induction ready with
  | nil => exact .nil _ _
  | cons present frame_eq hole_eq _ _ ih => exact .cons present frame_eq hole_eq ih

theorem Ready.congr {heap other : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value)
    (same : ∀ i, base ≤ i → heap i = other i) : Ready A other base frames value := by
  induction ready with
  | nil => exact .nil _ _
  | @cons base frame rest value cell present frame_eq hole_eq cache_eq tail ih =>
      exact .cons (by rw [← same base (by omega)]; exact present) frame_eq hole_eq cache_eq
        (ih fun i hi => same i (by omega))

/-- In-place sealing preserves the entire pointer chain and produces exact
summaries at every cell, for arbitrary constructor summary algebras. -/
theorem seal_correct {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (chain : Chain heap base frames value) :
    ∃ out, finalize A heap base frames.length (A.observe value) =
        some (out, A.observe (plug A.build frames value)) ∧
      Ready A out base frames value := by
  induction chain with
  | nil => exact ⟨_, rfl, .nil _ _⟩
  | @cons base frame rest value cell present frame_eq hole_eq tail ih =>
      obtain ⟨inner, run, ready⟩ := ih
      have atBase : inner base = some cell := by
        rw [seal_below A _ _ _ _ _ _ run _ (by omega)]
        exact present
      let summary := A.observe (plug A.build (frame :: rest) value)
      refine ⟨put inner base { cell with cache := some summary }, ?_, ?_⟩
      · simp only [List.length_cons, finalize, run, atBase,
          frame_eq]
        rw [show A.act frame (A.observe (plug A.build rest value)) = summary from
          (A.observe_frame frame (plug A.build rest value)).symm]
      · apply Ready.cons (cell := { cell with cache := some summary })
        · exact put_same _ _ _
        · exact frame_eq
        · exact hole_eq
        · rfl
        · exact ready.congr A fun i hi => (put_other _ _ _ _ (by omega)).symm

/-- The combined allocation/fill/finalize protocol refines functional plugging.
This statement reads the final heap and checks all caches, not just the root. -/
theorem build_correct (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    ∃ out, finalize A (reserve heap base frames value) base frames.length (A.observe value) =
        some (out, A.observe (plug A.build frames value)) ∧
      Ready A out base frames value ∧
      decode A.build out frames.length
        (if frames.isEmpty then .resident value else .cell base) =
        some (plug A.build frames value) := by
  obtain ⟨out, run, ready⟩ := seal_correct A (reserve_chain heap base frames value)
  exact ⟨out, run, ready, (ready.chain A).decode_exact A.build⟩

/-- The forward, single-allocation-per-frame constructor protocol, followed
by the metadata-only pass, implements functional plugging. -/
theorem forward_build_correct (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    ∃ out, finalize A (reserveForward heap base frames value) base frames.length
        (A.observe value) = some (out, A.observe (plug A.build frames value)) ∧
      Ready A out base frames value ∧
      decode A.build out frames.length
        (if frames.isEmpty then .resident value else .cell base) =
        some (plug A.build frames value) := by
  rw [reserveForward_eq]
  exact build_correct A heap base frames value

/-- Only addresses actually belonging to this spine need to be preserved. -/
theorem Ready.congr_range {heap other : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value)
    (same : ∀ i, base ≤ i → i < base + frames.length → heap i = other i) :
    Ready A other base frames value := by
  induction ready with
  | nil => exact .nil _ _
  | @cons base frame rest value cell present frame_eq hole_eq cache_eq tail ih =>
      exact .cons (by rw [← same base (by omega) (by simp only [List.length_cons]; omega)]; exact present)
        frame_eq hole_eq cache_eq (ih fun i hi hj => same i (by omega) (by simp only [List.length_cons]; omega))

/-- Releasing an arena suffix. Resident subgraphs have an independent owner. -/
def rollback (heap : Heap Label Value Summary) (mark : Nat) : Heap Label Value Summary :=
  fun address => if address < mark then heap address else none

/-- Protect the *whole* construction interval when keeping its published
root. Protecting only the root's allocation position is insufficient. -/
theorem Ready.rollback_safe {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value) (mark : Nat)
    (retained : base + frames.length ≤ mark) :
    Ready A (rollback heap mark) base frames value := by
  apply ready.congr_range A
  intro i _ hi
  simp [rollback, show i < mark by omega]

/-- A public reader checks completion at every visited cell. GC traversal
uses raw holes instead and must not infer reachability from draft summaries. -/
def publicRead (heap : Heap Label Value Summary) :
    Nat → Ref Value → Option (Value × Summary)
  | _, .resident value => some (value, A.observe value)
  | 0, .cell _ => none
  | fuel + 1, .cell address =>
      match heap address with
      | none => none
      | some cell => match cell.hole, cell.cache with
        | some next, some summary =>
            (publicRead heap fuel next).map fun result =>
              (cell.frame.apply A.build result.1, summary)
        | _, _ => none

theorem Ready.publicRead_exact {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value) :
    publicRead A heap frames.length
      (if frames.isEmpty then .resident value else .cell base) =
      some (plug A.build frames value, A.observe (plug A.build frames value)) := by
  induction ready with
  | nil => rfl
  | @cons base frame rest value cell present frame_eq hole_eq cache_eq tail ih =>
      simp only [List.length_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        publicRead, present, hole_eq, cache_eq, ih, Option.map_some, frame_eq, plug_cons]

/-- Raw pointer reachability deliberately ignores metadata readiness. -/
inductive Reaches (heap : Heap Label Value Summary) : Ref Value → Nat → Prop
  | here (address : Nat) : Reaches heap (.cell address) address
  | next {address target : Nat} {cell : Cell Label Value Summary} {next : Ref Value}
      (present : heap address = some cell) (hole : cell.hole = some next)
      (tail : Reaches heap next target) : Reaches heap (.cell address) target

/-- Changes disjoint from a reader's entire reachable graph preserve its
observation, including summaries. Root uniqueness alone would be too weak. -/
theorem publicRead_congr (heap other : Heap Label Value Summary)
    (fuel : Nat) (root : Ref Value)
    (same : ∀ i, Reaches heap root i → heap i = other i) :
    publicRead A heap fuel root = publicRead A other fuel root := by
  induction fuel generalizing root with
  | zero => cases root <;> rfl
  | succ fuel ih =>
      cases root with
      | resident value => rfl
      | cell address =>
          have head := same address (.here address)
          simp only [publicRead, ← head]
          cases h : heap address with
          | none => rfl
          | some cell =>
              cases hole : cell.hole with
              | none => simp [hole]
              | some next =>
                  cases cache : cell.cache with
                  | none => simp [hole, cache]
                  | some summary =>
                      simp only [hole, cache]
                      rw [ih next (fun i reach => same i (.next h hole reach))]

/-- A private region is unreachable from each public root. Ownership here
means transitive observational separation, not merely one root pointer. -/
def IsPrivate (heap : Heap Label Value Summary) (region : Nat → Prop)
    (roots : List (Ref Value)) : Prop :=
  ∀ root ∈ roots, ∀ i, Reaches heap root i → ¬ region i

theorem private_updates_invisible (heap other : Heap Label Value Summary)
    (region : Nat → Prop) (roots : List (Ref Value))
    (isolated : IsPrivate heap region roots)
    (onlyPrivate : ∀ i, ¬ region i → heap i = other i)
    (root : Ref Value) (visible : root ∈ roots) (fuel : Nat) :
    publicRead A heap fuel root = publicRead A other fuel root :=
  publicRead_congr A heap other fuel root
    (fun i reach => onlyPrivate i (isolated root visible i reach))

/-- Existing public graphs have no dangling addresses. -/
def WellRooted (heap : Heap Label Value Summary) (roots : List (Ref Value)) : Prop :=
  ∀ root ∈ roots, ∀ i, Reaches heap root i → ∃ cell, heap i = some cell

theorem fresh_region_private (heap : Heap Label Value Summary) (base : Nat)
    (roots : List (Ref Value)) (rooted : WellRooted heap roots)
    (fresh : ∀ i, base ≤ i → heap i = none) :
    IsPrivate heap (fun i => base ≤ i) roots := by
  intro root visible i reach after
  obtain ⟨cell, present⟩ := rooted root visible i reach
  rw [fresh i after] at present
  cases present

/-- The actual construction and finalization preserve all separated public
reads. Surviving aliases into old, immutable resident values are retained. -/
theorem build_preserves_public (heap out : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (summary : Summary)
    (run : finalize A (reserveForward heap base frames value) base frames.length
      (A.observe value) = some (out, summary))
    (roots : List (Ref Value)) (isolated : IsPrivate heap (fun i => base ≤ i) roots)
    (root : Ref Value) (visible : root ∈ roots) (fuel : Nat) :
    publicRead A heap fuel root = publicRead A out fuel root := by
  apply private_updates_invisible A heap out _ roots isolated _ root visible fuel
  intro i outside
  have before : i < base := by omega
  rw [seal_below A _ _ _ _ _ _ run i before, reserveForward_eq,
    reserve_below _ _ _ _ _ before]

/-- Meter the real entry operations: one allocation per extension, one link
per extension, and one final hole fill. No reconstruction allocation occurs. -/
def enterTailMetered (heap : Heap Label Value Summary) (tip : Nat) :
    List (Frame Label Value) → Value → Heap Label Value Summary × Nat × Nat
  | [], value => (fill heap tip (.resident value), 0, 1)
  | frame :: rest, value =>
      let result := enterTailMetered (extend heap tip (tip + 1) frame) (tip + 1) rest value
      (result.1, result.2.1 + 1, result.2.2 + 1)

theorem entry_work_exact (heap : Heap Label Value Summary) (tip : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    enterTailMetered heap tip frames value =
      (enterTail heap tip frames value, frames.length, frames.length + 1) := by
  induction frames generalizing heap tip with
  | nil => rfl
  | cons frame rest ih => simp [enterTailMetered, enterTail, ih]

/-- Include the first allocation and the final hole fill in the same meter. -/
def reserveForwardMetered (heap : Heap Label Value Summary) (base : Nat) :
    List (Frame Label Value) → Value → Heap Label Value Summary × Nat × Nat
  | [], _ => (heap, 0, 0)
  | frame :: rest, value =>
      let result := enterTailMetered (put heap base ⟨frame, none, none⟩) base rest value
      (result.1, result.2.1 + 1, result.2.2)

theorem allocation_and_filling_exact (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) :
    reserveForwardMetered heap base frames value =
      (reserveForward heap base frames value, frames.length, frames.length) := by
  cases frames with
  | nil => rfl
  | cons frame rest =>
      simp [reserveForwardMetered, entry_work_exact, reserveForward]

/-- Instrument each successful metadata update. This counter excludes the
cost inside the summary action, allocation, collection and bookkeeping. -/
def finalizeMetered (heap : Heap Label Value Summary) (base : Nat) :
    Nat → Summary → Option (Heap Label Value Summary × Summary × Nat)
  | 0, result => some (heap, result, 0)
  | n + 1, result =>
      match finalizeMetered heap (base + 1) n result with
      | none => none
      | some (inner, childSummary, writes) => match inner base with
        | none => none
        | some cell =>
            let summary := A.act cell.frame childSummary
            some (put inner base { cell with cache := some summary }, summary, writes + 1)

theorem metadata_work_exact (heap : Heap Label Value Summary) (base count : Nat)
    (summary : Summary) :
    finalizeMetered A heap base count summary =
      (finalize A heap base count summary).map (fun result => (result.1, result.2, count)) := by
  induction count generalizing base with
  | zero => rfl
  | succ count ih =>
      simp only [finalizeMetered, finalize, ih]
      cases child : finalize A heap (base + 1) count summary with
      | none => rfl
      | some result =>
          rcases result with ⟨inner, childSummary⟩
          cases atBase : inner base <;> simp [atBase]

/-- Any implementation that writes a final cache in every fresh cell must
write at least once per cell. This is a fixed-representation bound; omitting
per-cell caches or changing representation changes its premises. -/
theorem metadata_write_lower_bound (base count : Nat) (writes : List Nat)
    (covers : ∀ i ∈ List.range' base count, i ∈ writes) : count ≤ writes.length := by
  have subset : (List.range' base count).toFinset ⊆ writes.toFinset := by
    intro i member
    exact List.mem_toFinset.mpr (covers i (List.mem_toFinset.mp member))
  calc
    count = (List.range' base count).toFinset.card := by
      rw [List.toFinset_card_of_nodup (List.nodup_range' _ _), List.length_range']; decide
    _ ≤ writes.toFinset.card := Finset.card_le_card subset
    _ ≤ writes.length := List.toFinset_card_le writes

/-- The exact metadata-write lower bound is attained by finalizing this
concrete pointer chain. No claim about allocator cost or wall time follows. -/
theorem metadata_optimal {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (chain : Chain heap base frames value) (competitorWrites : List Nat)
    (covers : ∀ i ∈ List.range' base frames.length, i ∈ competitorWrites) :
    ∃ out, finalizeMetered A heap base frames.length (A.observe value) =
        some (out, A.observe (plug A.build frames value), frames.length) ∧
      frames.length ≤ competitorWrites.length := by
  obtain ⟨out, run, _⟩ := seal_correct A chain
  refine ⟨out, ?_, metadata_write_lower_bound base frames.length competitorWrites covers⟩
  rw [metadata_work_exact, run]
  rfl

/-- Competing metadata algorithms may choose arbitrary update orders and
repeat addresses. Their observable operation writes one cell's cache. -/
def writeCaches (heap : Heap Label Value Summary) : List (Nat × Summary) →
    Heap Label Value Summary
  | [] => heap
  | (address, summary) :: rest =>
      writeCaches (modify heap address fun cell => { cell with cache := some summary }) rest

theorem writeCaches_untouched (heap : Heap Label Value Summary)
    (writes : List (Nat × Summary)) (i : Nat)
    (absent : i ∉ writes.map Prod.fst) : writeCaches heap writes i = heap i := by
  induction writes generalizing heap with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨address, summary⟩
      simp only [List.map_cons, List.mem_cons, not_or] at absent
      rw [writeCaches, ih _ absent.2]
      simp [modify, Function.update, absent.1]

theorem Ready.cache_present {heap : Heap Label Value Summary} {base : Nat}
    {frames : List (Frame Label Value)} {value : Value}
    (ready : Ready A heap base frames value) (i : Nat)
    (lower : base ≤ i) (upper : i < base + frames.length) :
    ∃ summary, (heap i).bind Cell.cache = some summary := by
  induction ready with
  | nil => simp at upper; omega
  | @cons base frame rest value cell present frame_eq hole_eq cache_eq tail ih =>
      by_cases atBase : i = base
      · subst i
        exact ⟨A.observe (plug A.build (frame :: rest) value), by rw [present]; exact cache_eq⟩
      · exact ih (by omega) (by simp only [List.length_cons] at upper; omega)

/-- Successful sealing forces coverage; coverage is derived from the initial
and final heap states rather than assumed of the competing write trace. -/
theorem sealing_write_lower_bound (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (writes : List (Nat × Summary))
    (draft : ∀ i, base ≤ i → i < base + frames.length →
      (heap i).bind Cell.cache = none)
    (sealed : Ready A (writeCaches heap writes) base frames value) :
    frames.length ≤ writes.length := by
  have coverage : ∀ i ∈ List.range' base frames.length, i ∈ writes.map Prod.fst := by
    intro i inside
    obtain ⟨offset, within, address⟩ := List.mem_range'.mp inside
    have lower : base ≤ i := by omega
    have upper : i < base + frames.length := by omega
    by_contra absent
    obtain ⟨summary, present⟩ := sealed.cache_present A i lower upper
    rw [writeCaches_untouched heap writes i absent, draft i lower upper] at present
    cases present
  simpa using metadata_write_lower_bound base frames.length (writes.map Prod.fst) coverage

/-- Filling the fresh construction leaves every cache explicitly unready. -/
theorem reserve_caches_unready (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (i : Nat)
    (lower : base ≤ i) (upper : i < base + frames.length) :
    (reserve heap base frames value i).bind Cell.cache = none := by
  induction frames generalizing heap base with
  | nil => simp at upper; omega
  | cons frame rest ih =>
      by_cases atBase : i = base
      · subst i
        simp only [reserve, fill, modify, Function.update_self]
        cases reserve (put heap base ⟨frame, none, none⟩) (base + 1) rest value base <;> rfl
      · simp only [reserve, fill, modify]
        rw [Function.update_of_ne atBase]
        exact ih _ _ (by omega) (by simp only [List.length_cons] at upper; omega)

/-- The concrete finalizer is optimal among cache-write algorithms that seal
the same draft, with arbitrary write order, summaries and repeated writes. -/
theorem metadata_optimal_from_draft (heap : Heap Label Value Summary) (base : Nat)
    (frames : List (Frame Label Value)) (value : Value) (writes : List (Nat × Summary))
    (competitor : Ready A (writeCaches (reserveForward heap base frames value) writes)
      base frames value) :
    ∃ out, finalizeMetered A (reserveForward heap base frames value) base frames.length
        (A.observe value) = some (out, A.observe (plug A.build frames value), frames.length) ∧
      frames.length ≤ writes.length := by
  obtain ⟨out, run, _, _⟩ := forward_build_correct A heap base frames value
  refine ⟨out, ?_, ?_⟩
  · rw [metadata_work_exact, run]; rfl
  · apply sealing_write_lower_bound A _ base frames value writes _ competitor
    intro i lower upper
    rw [reserveForward_eq]
    exact reserve_caches_unready heap base frames value i lower upper

/-- Allocation indices need not be consecutive native pointer addresses.
Any bijective address renaming transports the same heap observations. -/
def Ref.rename (placement : Nat ≃ Nat) : Ref Value → Ref Value
  | .resident value => .resident value
  | .cell address => .cell (placement address)

def Cell.rename (placement : Nat ≃ Nat) (cell : Cell Label Value Summary) :
    Cell Label Value Summary :=
  { cell with hole := cell.hole.map (Ref.rename placement) }

def renameHeap (placement : Nat ≃ Nat) (heap : Heap Label Value Summary) :
    Heap Label Value Summary :=
  fun address => (heap (placement.symm address)).map (Cell.rename placement)

/-- Relocating every pointer and preserving cell contents preserves values
and summaries. A native moving collector still owes this correspondence and
must separately account for any changed arena labels. -/
theorem publicRead_rename (placement : Nat ≃ Nat) (heap : Heap Label Value Summary)
    (fuel : Nat) (root : Ref Value) :
    publicRead A (renameHeap placement heap) fuel (root.rename placement) =
      publicRead A heap fuel root := by
  induction fuel generalizing root with
  | zero => cases root <;> rfl
  | succ fuel ih =>
      cases root with
      | resident value => rfl
      | cell address =>
          simp only [Ref.rename, publicRead, renameHeap, Equiv.symm_apply_apply]
          cases h : heap address with
          | none => rfl
          | some cell =>
              cases hole : cell.hole with
              | none => simp [Cell.rename, hole]
              | some next =>
                  cases cache : cell.cache with
                  | none => simp [Cell.rename, hole, cache]
                  | some summary => simp [Cell.rename, hole, cache, ih]

namespace Controls

def addAlgebra : SummaryAlgebra Nat Nat Nat where
  build := fun label children => label + children.sum
  observe := id
  combine := fun label children => label + children.sum
  build_observe := by intros; simp

def frame (n : Nat) : Frame Nat Nat := ⟨n, [], []⟩
def empty : Heap Nat Nat Nat := fun _ => none

def exampleDraft : Heap Nat Nat Nat :=
  reserveForward empty 10 [frame 1, frame 2] 3

def exampleFinal : Heap Nat Nat Nat :=
  match finalize addAlgebra exampleDraft 10 2 3 with
  | none => empty
  | some result => result.1

/-- Reading shape and publishing an atom are different operations. -/
theorem draft_is_private_until_sealed :
    decode addAlgebra.build exampleDraft 2 (.cell 10) = some 6 ∧
    publicRead addAlgebra exampleDraft 2 (.cell 10) = none ∧
    publicRead addAlgebra exampleFinal 2 (.cell 10) = some (6, 6) := by decide

/-- Parent-first allocation makes a mark inside the spine unsafe, even
though the retained root already carries its final summary. -/
theorem rollback_inside_spine_breaks_answer :
    (rollback exampleFinal 11 10).bind Cell.cache = some 6 ∧
    publicRead addAlgebra (rollback exampleFinal 11) 2 (.cell 10) = none := by decide

/-- A second use of the same mutable destination changes the first answer.
A captured/multi-shot continuation needs unique ownership or fresh storage. -/
theorem shared_destination_is_unsound :
    let first : Heap Nat Nat Nat :=
      put empty 10 ⟨frame 1, some (.resident 3), some 4⟩
    let second := fill first 10 (.resident 7)
    decode addAlgebra.build first 1 (.cell 10) = some 4 ∧
    decode addAlgebra.build second 1 (.cell 10) = some 8 := by decide

/-- An interning operation may return a different representative. Keeping a
pointer to the discarded draft is not justified by equal value summaries. -/
theorem relocation_requires_pointer_repair :
    let heap : Heap Nat Nat Nat :=
      put (put empty 10 ⟨frame 1, some (.cell 11), some 6⟩)
        12 ⟨frame 2, some (.resident 3), some 5⟩
    publicRead addAlgebra heap 2 (.cell 10) = none ∧
    publicRead addAlgebra (fill heap 10 (.cell 12)) 2 (.cell 10) = none ∧
    decode addAlgebra.build (fill heap 10 (.cell 12)) 2 (.cell 10) = some 6 := by decide

end Controls

end Mettapedia.Machines.ConstructorContextHeap
