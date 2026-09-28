import Mathlib.Data.List.Basic

/-!
# Generations of the open tier's region collector

The open equation tier allocates in a region and collects it by copying.  A minor collection
copies only the region's reached objects, promoting them into an old generation, and leaves every
older object where it is: an older continuation, slot vector or argument vector is shared.  A
frame's argument vector never changes once the frame is pushed, so an old one is left untouched;
an activation's slot vector is filled by first-occurrence stores as it runs, so an old one the
collection reaches is renamed in place, each region object it names replaced by its copy and each
reached cell by its new index.  The trace goes through every reached old continuation to find those
vectors.  The store trail keeps an old vector's entries by identity and a copied one's by its copy,
and drops the entries of vectors it did not reach.  A collection that finds at least half of the
region reached declines and changes nothing.

This module models the heap, the running code's steps and the collector, and proves: every step
keeps the allocation-order invariant (an old object names only old objects and old cells, except an
old slot vector through a store made after its promotion) and a collection re-establishes it with no
exception; the collection's result is the image of what the state reaches under a renaming, so every
read agrees, every state a frame restores agrees, and every later run observes the same; the sharing
collection equals the full-copy one up to renaming; declining is the identity.  Witnesses show what
breaks when the in-place rewrite, the walk of old continuations or a store-trail entry is dropped,
and that renaming argument vectors in place would be correct too.

**Model.**  An `Addr` is a generation and an index; the generation stands for the collector's address
index, which decides whether an address lies in one of the region's blocks.  A `Val` is a cell, by
index, or an object.  An `Obj` has a `Kind` (atom, argument vector, continuation, or slot vector with
its birth: the number of frames live when its activation began), immutable content and fields.  A
`State` holds the region (`young`, in allocation order) and the old generation, the binding array and
its trail, the store trail, the frames (newest first, each with its roots and the lengths of the
region, the cells, the trail and the store trail at its push), the call's roots (destination and
query cells), the running code's values, and `oldCells`, below which old objects may name cells.
`Reach` is reachability from the roots.  `readAs` unfolds a value to a depth, showing cells by a
renaming.  The steps (`Step`, enabled by `Step.Enabled`) allocate an immutable object or begin an
activation in the region, make a cell, store into an empty slot of a slot vector (trailed when more
frames are live than its birth), bind an unbound cell (trailed when older than the newest frame's
cell mark), push a frame, restore the newest frame, or restore and drop it.  A restore cuts the
region back to the frame's mark, empties the slots the store trail names past the frame's store mark,
unbinds the cells the trail names past its trail mark, drops the cells made since, caps `oldCells`,
and hands the frame's roots to the running code.

**Invariants.**  `Generational` (the allocation-order invariant; `GenerationalOn` with another
exemption) and `Typed` (atoms and argument vectors name only atoms and cells) are kept by every step:
`Generational.step`, `Typed.step`.  `Disciplined` is the frame discipline the two trails keep: the
marks are sorted and fit, every state a frame restores dangles nowhere, the store trail names slot
vectors, those below a frame's store mark made before the frame, a slot vector is unreachable after
restoring any frame live at its birth, and a reachable one was born with at most the frames now
live.  `Disciplined.step` keeps it for every step, `collect_disciplined` and `minor_disciplined` for
a collection.

**Collections.**  A `Policy` says which old kinds a collection copies, renames in place and walks;
`Policy.Sound` states what it must do against an invariant.  `Traced` says a set `R` is closed under
the trace: it holds the roots and every cell below `oldCells`, and whatever a visited region object,
a visited old object of a walked kind, or a visited cell names.  `collectWith` copies the region's
reached objects in region order after the old generation (`promote`), renames old objects of
rewritten kinds in place, renumbers the reached cells (`renumber`), filters and renames the trail,
keeps the store-trail entries a predicate accepts, sets every frame's region mark to the empty region
and its other marks to what was kept below them, and empties the region.  `collect` keeps the entries
of reached vectors.  `sharing` is the tier's policy, `fullCopy` the full-copy minor that copies old
continuations, slot vectors and argument vectors again, and `rewritingArgs` renames argument vectors
in place as well.

**Results.**

* `collectWith_image` (keystone): the result is the `Image` of what the state reaches under
  `promote` and `renumber`; `reach_traced` is the frontier lemma behind it, everything reached being
  visited or an old atom.  `collectWith_read`: every read from a reached value agrees.
* `collectWith_generational`, `collectWith_older`: after promotion no reached object, slot vectors
  included, names the region or a cell above the new `oldCells`; `collectWith_typed`,
  `collectWith_noDangling`.
* `collect_restoreAt`, `collect_restoreAt_read`: restoring any frame after the collection gives the
  image of restoring it before; the renamed store trail and trail and the remapped marks are exactly
  what this needs.
* `collect_corr`, `Corr.step`, `Corr.run`, `collect_later_run`, `collect_later_read`: after the
  collection the state takes the mirrored run of any run the code can take from the state before, the
  two stay related (`Corr`), and every read agrees at every point.
* `sharing_fullCopy`: the full-copy result is the image of the sharing one under `fullCopyOf`, which
  moves only the old objects the full copy copied again, with every cell where it was.
* `rewritingArgs_sound` and `sharing_rewritingArgs`: renaming old argument vectors in place is sound
  even against the invariant that lets them name the region, and against the tier's it changes no
  reached object; their immutability is what lets the tier skip them.
* `minor_declined`, `minor_image`, `minor_corr`: a declined collection is the identity.
* `Machine.invariants`, `Machine.unobservable`: along any interleaving of steps and collections,
  declined or not, from a state keeping the invariants, every state keeps them, and a collection at
  any of them is unobservable by any later run.

**Witnesses** (`Witness`).  `stored` is reached from `promoted` by a push, an allocation and a store
into an old slot vector after its promotion (`stored_run`, `stored_machine`), keeping every invariant
along the way (`stored_invariants`).  `unrewritten_dangles`: sharing the
old slot vector without renaming it leaves its slot naming the emptied region, and
`unrewritten_reads_reused`: once the region is reused the slot reads an unrelated atom.
`unwalkedConts_dangles`: not walking the old continuation misses the slot vector below it.
`sharing_mutatedArgs_dangles` and `rewritingArgs_mutatedArgs_read`: an old argument vector naming the
region, which immutability rules out, would dangle under the tier's policy and not under the
rewriting one.  `dropped_entry_stale`: keeping only the store-trail entries of copied vectors lets the
restore leave the old vector's slot filled with a term built on the path it undid, while the tier's
collection keeps the restore emptying it (`sharing_restore_read`, `stored_later_read`).

**Correspondence with the C tier.**  The region is an arena of blocks; the collector sorts the
blocks' spans and decides by binary search whether a continuation or slot vector moves.  The trace
marks the region's expressions and non-variable leaves it visits in the atom's name key, null on every
non-variable, records them when the collection may decline, and clears the recorded marks when it
does; the copy phase memoizes copies in a table and in the expressions' name keys.  Frames' argument
vectors are traced and copied only when they lie in the region; continuations are walked through the
whole chain, and the copy phase copies the chain's region prefix and, from the first older
continuation on, renames each continuation's slot vector in place.  Every cell below the old
generation's cell count is a trace root, as are the query's cells, host goals' cells and the
destination; the reached cells take consecutive indices in order.  A frame's region mark becomes the
empty region's, its cell mark the number of reached cells below it, its trail and store marks the
number of kept entries below them.  The store trail keeps an entry exactly when its vector is in the
copy table, which holds the region's copied vectors and the old vectors renamed in place.  The old
generation's cell count becomes the number of reached cells.  A collection runs at the cursor loop's
head, where the running code holds nothing; the model renames the running code's values anyway.  A
first-occurrence store is trailed exactly when more frames are live than the vector's header
records; a binding is trailed exactly when its cell is older than the newest frame's cell mark; a
frame is popped only right after it is restored, and a restore caps the old generation's cell count.

**Not covered.**  The model's collector renames every reached cell and shunts none; the C collector
also replaces bound cells no live frame can unbind by their values, whose soundness is
`RegionVariableShunting.Region.shunt_resolve`; the composition is not formalized, and the cells a
shunt leaves unreached, which the C drops, the model keeps.  The trace is any closed set: the
worklist, the copy table and the marks are not modelled, so "declining is the identity" is by
construction here, and the C's obligation that every mark it sets is recorded and cleared is checked
by reading.  Copies go in region order rather than trace order, which only renames them.  The decline
test counts objects, not bytes; the thresholds deciding when to collect and how long to wait after a
decline or a promotion are policy.  Major collections, detaching, the blocks holding a match's rows
and a host goal's cells, program versions and the unifier's internals are not modelled.
-/

namespace Mettapedia.GSLT.LanguageDef.RegionGenerations

/-! ## Positions a filter keeps -/

section Keep

variable {α β : Type}

/-- The entries of `xs` at the positions `keep` accepts, each transformed by `f`, where `xs` starts
at position `start`. -/
def keepMap (keep : Nat → Bool) (f : α → β) : Nat → List α → List β
  | _, [] => []
  | start, x :: xs =>
      if keep start then f x :: keepMap keep f (start + 1) xs else keepMap keep f (start + 1) xs

/-- How many of the `n` positions from `start` on `keep` accepts. -/
def countFrom (keep : Nat → Bool) : Nat → Nat → Nat
  | _, 0 => 0
  | start, n + 1 => (if keep start then 1 else 0) + countFrom keep (start + 1) n

theorem countFrom_succ (keep : Nat → Bool) (start n : Nat) :
    countFrom keep start (n + 1) = countFrom keep start n + if keep (start + n) then 1 else 0 := by
  induction n generalizing start with
  | zero => simp [countFrom]
  | succ n ih =>
    rw [countFrom, ih, countFrom, show start + 1 + n = start + (n + 1) by omega, Nat.add_assoc]

theorem countFrom_mono (keep : Nat → Bool) (start : Nat) {n m : Nat} (le : n ≤ m) :
    countFrom keep start n ≤ countFrom keep start m := by
  induction m with
  | zero => rw [Nat.le_zero.mp le]; exact Nat.le_refl _
  | succ m ih =>
    rcases Nat.lt_or_eq_of_le le with lt | eq
    · rw [countFrom_succ]; exact Nat.le_add_right_of_le (ih (Nat.le_of_lt_succ lt))
    · rw [eq]; exact Nat.le_refl _

theorem countFrom_lt (keep : Nat → Bool) (start : Nat) {n m : Nat} (lt : n < m)
    (kept : keep (start + n) = true) : countFrom keep start n < countFrom keep start m := by
  have step : countFrom keep start (n + 1) = countFrom keep start n + 1 := by
    rw [countFrom_succ, if_pos kept]
  exact Nat.lt_of_lt_of_le (by rw [step]; exact Nat.lt_succ_self _) (countFrom_mono keep start lt)

theorem countFrom_inj (keep : Nat → Bool) (start : Nat) {n m : Nat}
    (keptN : keep (start + n) = true) (keptM : keep (start + m) = true)
    (same : countFrom keep start n = countFrom keep start m) : n = m := by
  rcases Nat.lt_trichotomy n m with lt | eq | gt
  · exact absurd same (Nat.ne_of_lt (countFrom_lt keep start lt keptN))
  · exact eq
  · exact absurd same.symm (Nat.ne_of_lt (countFrom_lt keep start gt keptM))

theorem countFrom_of_all (keep : Nat → Bool) (start : Nat) {n : Nat}
    (all : ∀ m < n, keep (start + m) = true) : countFrom keep start n = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [countFrom_succ, ih (fun m lt => all m (Nat.lt_succ_of_lt lt)),
      if_pos (all n (Nat.lt_succ_self n))]

theorem length_keepMap (keep : Nat → Bool) (f : α → β) (start : Nat) (xs : List α) :
    (keepMap keep f start xs).length = countFrom keep start xs.length := by
  induction xs generalizing start with
  | nil => rfl
  | cons x xs ih =>
    cases kept : keep start
    · simp only [keepMap, kept, List.length_cons, countFrom, ih, Bool.false_eq_true, if_false]
      omega
    · simp only [keepMap, kept, if_true, List.length_cons, countFrom, ih]; omega

theorem getElem?_keepMap (keep : Nat → Bool) (f : α → β) :
    ∀ (start : Nat) (xs : List α) (n : Nat), n < xs.length → keep (start + n) = true →
      (keepMap keep f start xs)[countFrom keep start n]? = xs[n]?.map f
  | _, [], _, lt, _ => absurd lt (Nat.not_lt_zero _)
  | start, x :: xs, 0, _, kept => by
    simp only [Nat.add_zero] at kept
    simp [keepMap, countFrom, kept]
  | start, x :: xs, n + 1, lt, kept => by
    have ih := getElem?_keepMap keep f (start + 1) xs n (by simpa using lt)
      (by rwa [show start + 1 + n = start + (n + 1) by omega])
    cases here : keep start
    · simp only [keepMap, here, countFrom, List.getElem?_cons_succ, Bool.false_eq_true, if_false,
        Nat.zero_add]
      exact ih
    · simp only [keepMap, here, if_true, countFrom, List.getElem?_cons_succ]
      rw [show 1 + countFrom keep (start + 1) n = countFrom keep (start + 1) n + 1 from
        Nat.add_comm _ _, List.getElem?_cons_succ, ih]

end Keep

/-! ## The heap -/

/-- The region's generation, the young one, and the old generation minor collections promote
into. -/
inductive Gen where
  | young
  | old
deriving DecidableEq, Repr

/-- An object's address: its generation and its position there.  The generation stands for the
collector's address index (the region's blocks), which decides whether an address lies in the
region. -/
structure Addr where
  gen : Gen
  index : Nat
deriving DecidableEq, Repr

/-- What a field, a slot, a binding or a root holds: a cell, by index, or an object. -/
inductive Val where
  | cell (index : Nat)
  | ref (addr : Addr)
deriving DecidableEq, Repr

/-- An object's kind.  Atoms, argument vectors and continuations never change once made; an
activation's slot vector is filled by first-occurrence stores, and carries the number of frames
live when its activation began. -/
inductive Kind where
  | atom
  | args
  | cont
  | slots (birth : Nat)
deriving DecidableEq, Repr

/-- Whether a kind is a slot vector. -/
def Kind.isSlots : Kind → Bool
  | .slots _ => true
  | _ => false

/-- A heap object: its kind, its immutable content (a leaf's data, a continuation's code
position), and its fields. -/
structure Obj (Label : Type) where
  kind : Kind
  label : Label
  fields : List (Option Val)
deriving DecidableEq, Repr

/-- A choice frame: its roots (its argument vector, its continuation, a host goal's cells) and the
lengths of the region, the cells, the trail and the store trail when it was pushed. -/
structure Frame where
  vals : List Val
  mark : Nat
  cellMark : Nat
  trailMark : Nat
  storeMark : Nat
deriving DecidableEq, Repr

/-- The cursor's state.  `young` is the region in allocation order and `old` the old generation;
`cells` is the binding array and `trail` the cells restores unbind; `stores` is the store trail,
the slots restores empty; `frames` lists the newest frame first; `call` holds the destination and
the query's cells, and `regs` the values the running code holds.  Cells below `oldCells` may be
named by old objects. -/
structure State (Label : Type) where
  young : List (Obj Label)
  old : List (Obj Label)
  cells : List (Option Val)
  oldCells : Nat
  trail : List Nat
  stores : List (Addr × Nat)
  frames : List Frame
  call : List Val
  regs : List Val
deriving DecidableEq, Repr

attribute [ext] State

variable {Label : Type}

namespace State

variable (s : State Label)

/-- The object at an address. -/
def get (a : Addr) : Option (Obj Label) :=
  match a.gen with
  | .young => s.young[a.index]?
  | .old => s.old[a.index]?

/-- The roots: the call's values, the running code's values and every frame's. -/
def Root (v : Val) : Prop :=
  v ∈ s.call ∨ v ∈ s.regs ∨ ∃ frame ∈ s.frames, v ∈ frame.vals

/-- A value that names something the state holds. -/
def Present : Val → Prop
  | .cell i => i < s.cells.length
  | .ref a => (s.get a).isSome

/-- A value an old object may name: an old object, or a cell below `oldCells`. -/
def Older : Val → Prop
  | .cell i => i < s.oldCells
  | .ref b => b.gen = .old

/-- The cell mark of the newest frame. -/
def newestCellMark : Nat :=
  match s.frames with
  | [] => 0
  | frame :: _ => frame.cellMark

/-- Update the object at an address. -/
def update (a : Addr) (f : Obj Label → Obj Label) : State Label :=
  match a.gen with
  | .young => { s with young := s.young.modify a.index f }
  | .old => { s with old := s.old.modify a.index f }

end State

@[simp] theorem get_young (s : State Label) (n : Nat) : s.get ⟨.young, n⟩ = s.young[n]? := rfl

@[simp] theorem get_old (s : State Label) (m : Nat) : s.get ⟨.old, m⟩ = s.old[m]? := rfl

theorem get_update (s : State Label) (a : Addr) (f : Obj Label → Obj Label) (b : Addr) :
    (s.update a f).get b = if b = a then (s.get a).map f else s.get b := by
  obtain ⟨genA, a⟩ := a
  obtain ⟨genB, b⟩ := b
  cases genA <;> cases genB <;>
    simp [State.update, State.get, List.getElem?_modify, eq_comm] <;> split <;> simp_all

/-- Reachability from the roots, through fields and bindings. -/
inductive Reach (s : State Label) : Val → Prop
  | root {v : Val} : s.Root v → Reach s v
  | field {a : Addr} {o : Obj Label} {v : Val} :
      Reach s (.ref a) → s.get a = some o → some v ∈ o.fields → Reach s v
  | binding {i : Nat} {v : Val} : Reach s (.cell i) → s.cells[i]? = some (some v) → Reach s v

/-- A property closed under the roots, fields and bindings of `s` holds of everything reachable. -/
theorem Reach.closed {s : State Label} (P : Val → Prop) (root : ∀ v, s.Root v → P v)
    (field : ∀ a o v, P (.ref a) → s.get a = some o → some v ∈ o.fields → P v)
    (binding : ∀ i v, P (.cell i) → s.cells[i]? = some (some v) → P v) :
    ∀ v, Reach s v → P v := by
  intro v reach
  induction reach with
  | root isRoot => exact root _ isRoot
  | field _ found member ih => exact field _ _ _ ih found member
  | binding _ bound ih => exact binding _ _ ih bound

/-- A state no reachable value dangles in. -/
def NoDangling (s : State Label) : Prop :=
  ∀ v, Reach s v → s.Present v

instance (s : State Label) : DecidablePred s.Present
  | .cell i => inferInstanceAs (Decidable (i < s.cells.length))
  | .ref a => inferInstanceAs (Decidable ((s.get a).isSome = true))

/-- The roots, listed. -/
theorem root_mem {s : State Label} {v : Val} (root : s.Root v) :
    v ∈ s.call ++ s.regs ++ s.frames.flatMap Frame.vals := by
  rcases root with call | regs | ⟨frame, member, vals⟩
  · simp [call]
  · simp [regs]
  · simp only [List.mem_append, List.mem_flatMap]
    exact Or.inr ⟨frame, member, vals⟩

/-! ## Reads -/

/-- What a read of a value unfolds to, to a depth. -/
inductive Tree (Label : Type) where
  | cell (index : Nat) (binding : Option (Tree Label))
  | node (kind : Kind) (label : Label) (fields : List (Option (Tree Label)))
  | dangling
  | cutoff

/-- A read of `v` to depth `n`, showing cell `i` as `ρ i`. -/
def readAs (ρ : Nat → Nat) (s : State Label) : Nat → Val → Tree Label
  | 0, _ => .cutoff
  | n + 1, .cell i =>
      match s.cells[i]? with
      | some binding => .cell (ρ i) (binding.map (readAs ρ s n))
      | none => .dangling
  | n + 1, .ref a =>
      match s.get a with
      | some o => .node o.kind o.label (o.fields.map (Option.map (readAs ρ s n)))
      | none => .dangling

/-- A read of `v` to depth `n`. -/
def read (s : State Label) : Nat → Val → Tree Label :=
  readAs id s

/-! ## Renaming -/

/-- Rename a value: objects by `φ`, cells by `ρ`. -/
def mapVal (φ : Addr → Addr) (ρ : Nat → Nat) : Val → Val
  | .cell i => .cell (ρ i)
  | .ref a => .ref (φ a)

/-- Rename an object's fields. -/
def Obj.map (f : Val → Val) (o : Obj Label) : Obj Label :=
  { o with fields := o.fields.map (Option.map f) }

@[simp] theorem Obj.map_kind (f : Val → Val) (o : Obj Label) : (o.map f).kind = o.kind := rfl

@[simp] theorem Obj.map_label (f : Val → Val) (o : Obj Label) : (o.map f).label = o.label := rfl

@[simp] theorem Obj.map_fields (f : Val → Val) (o : Obj Label) :
    (o.map f).fields = o.fields.map (Option.map f) := rfl

theorem Obj.map_eq_self {f : Val → Val} {o : Obj Label} (fixed : ∀ v, some v ∈ o.fields → f v = v) :
    o.map f = o := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [Obj.map, Obj.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id fields]
  refine List.map_congr_left fun field member => ?_
  cases field with
  | none => rfl
  | some v => simp [fixed v member]

/-- `t` is the image of what `s` reaches, under the renaming `φ` of objects and `ρ` of cells: each
reached object and cell is where the renaming puts it, with its fields renamed, and the roots are
the renamed roots. -/
structure Image (φ : Addr → Addr) (ρ : Nat → Nat) (s t : State Label) : Prop where
  obj : ∀ a, Reach s (.ref a) → t.get (φ a) = (s.get a).map (Obj.map (mapVal φ ρ))
  cell : ∀ i, Reach s (.cell i) → t.cells[ρ i]? = s.cells[i]?.map (Option.map (mapVal φ ρ))
  call : t.call = s.call.map (mapVal φ ρ)
  regs : t.regs = s.regs.map (mapVal φ ρ)
  frames : t.frames.map Frame.vals = s.frames.map fun frame => frame.vals.map (mapVal φ ρ)

/-- Under an image, every read from a reached value agrees, the cells shown by their new
names. -/
theorem Image.read_eq {φ : Addr → Addr} {ρ : Nat → Nat} {s t : State Label} (image : Image φ ρ s t) :
    ∀ (n : Nat) (v : Val), Reach s v → read t n (mapVal φ ρ v) = readAs ρ s n v
  | 0, _, _ => rfl
  | n + 1, .cell i, reach => by
    have ih := Image.read_eq image n
    simp only [read, mapVal, readAs, image.cell i reach, id]
    cases found : s.cells[i]? with
    | none => rfl
    | some binding =>
      cases binding with
      | none => rfl
      | some v => simpa [read] using ih v (Reach.binding reach found)
  | n + 1, .ref a, reach => by
    have ih := Image.read_eq image n
    simp only [read, mapVal, readAs, image.obj a reach]
    cases found : s.get a with
    | none => rfl
    | some o =>
      simp only [Option.map_some, Obj.map_kind, Obj.map_label, Obj.map_fields, List.map_map,
        Tree.node.injEq, true_and]
      refine List.map_congr_left fun field member => ?_
      cases field with
      | none => rfl
      | some v => simpa [read] using ih v (Reach.field reach found member)

/-! ## The mutator -/

/-- Empty the slots `entries` names in the object at `a`. -/
def clearSlots (entries : List (Addr × Nat)) (a : Addr) (o : Obj Label) : Obj Label :=
  { o with fields := o.fields.mapIdx fun j field => if (a, j) ∈ entries then none else field }

namespace State

variable (s : State Label)

/-- Allocate an object in the region; the running code holds it. -/
def alloc (kind : Kind) (label : Label) (fields : List (Option Val)) : State Label :=
  { s with
    young := s.young ++ [⟨kind, label, fields⟩]
    regs := .ref ⟨.young, s.young.length⟩ :: s.regs }

/-- Begin an activation: a slot vector born with the frames now live, holding `initial`. -/
def activate (label : Label) (initial : List (Option Val)) : State Label :=
  s.alloc (.slots s.frames.length) label initial

/-- A fresh unbound cell; the running code holds it. -/
def newCell : State Label :=
  { s with cells := s.cells ++ [none], regs := .cell s.cells.length :: s.regs }

/-- Whether a store into the vector at `vector` is trailed: a frame newer than its activation is
live. -/
def trailsStore (vector : Addr) : Bool :=
  match s.get vector with
  | some o =>
    match o.kind with
    | .slots birth => decide (birth < s.frames.length)
    | _ => false
  | none => false

/-- A first-occurrence store of `value` into slot `slot` of the vector at `vector`. -/
def store (vector : Addr) (slot : Nat) (value : Val) : State Label :=
  { s.update vector (fun o => { o with fields := o.fields.set slot (some value) }) with
    stores := if s.trailsStore vector then s.stores ++ [(vector, slot)] else s.stores }

/-- Bind cell `cell` to `value`, trailed when a frame newer than the cell is live. -/
def bind (cell : Nat) (value : Val) : State Label :=
  { s with
    cells := s.cells.set cell (some value)
    trail := if cell < s.newestCellMark then s.trail ++ [cell] else s.trail }

/-- Push a frame with roots `vals`. -/
def push (vals : List Val) : State Label :=
  { s with
    frames := ⟨vals, s.young.length, s.cells.length, s.trail.length, s.stores.length⟩ :: s.frames }

/-- Back to `frame`'s state: the region cut back to its mark, the slots stored and the cells bound
since it emptied, the cells made since dropped; the running code holds the frame's roots.  The
frames are left as they are.  The unwinding of both trails is applied at once: each entry empties
its slot or unbinds its cell, so the order does not matter. -/
def restoreTo (frame : Frame) : State Label :=
  { s with
    young := (s.young.mapIdx fun n o =>
      clearSlots (s.stores.drop frame.storeMark) ⟨.young, n⟩ o).take frame.mark
    old := s.old.mapIdx fun m o => clearSlots (s.stores.drop frame.storeMark) ⟨.old, m⟩ o
    cells := (s.cells.mapIdx fun i binding =>
      if i ∈ s.trail.drop frame.trailMark then none else binding).take frame.cellMark
    oldCells := min s.oldCells frame.cellMark
    trail := s.trail.take frame.trailMark
    stores := s.stores.take frame.storeMark
    regs := frame.vals }

/-- Restore the newest frame, which stays for its next alternative. -/
def restore : State Label :=
  match s.frames with
  | [] => s
  | frame :: _ => s.restoreTo frame

/-- Restore the newest frame and drop it: its last alternative runs with nothing to return to. -/
def pop : State Label :=
  match s.frames with
  | [] => s
  | frame :: older => { s.restoreTo frame with frames := older }

/-- Restore the frame at `depth` below the newest, dropping the frames above it. -/
def restoreAt (depth : Nat) : State Label :=
  match s.frames[depth]? with
  | none => s
  | some frame => { s.restoreTo frame with frames := s.frames.drop depth }

end State

/-- A step of the running code. -/
inductive Step (Label : Type) where
  | alloc (kind : Kind) (label : Label) (fields : List (Option Val))
  | activate (label : Label) (initial : List (Option Val))
  | newCell
  | store (vector : Addr) (slot : Nat) (value : Val)
  | bind (cell : Nat) (value : Val)
  | push (vals : List Val)
  | pop
  | restore

/-- The state after a step. -/
def Step.run : Step Label → State Label → State Label
  | .alloc kind label fields, s => s.alloc kind label fields
  | .activate label initial, s => s.activate label initial
  | .newCell, s => s.newCell
  | .store vector slot value, s => s.store vector slot value
  | .bind cell value, s => s.bind cell value
  | .push vals, s => s.push vals
  | .pop, s => s.pop
  | .restore, s => s.restore

/-- The steps the running code can take: it names only what it reaches; `alloc` makes an
immutable object, an atom or argument vector naming only atoms and cells; a store fills an empty
slot of a slot vector; a bind binds an unbound cell; a restore or pop needs a frame. -/
inductive Step.Enabled (s : State Label) : Step Label → Prop
  | alloc {kind : Kind} {label : Label} {fields : List (Option Val)} :
      kind.isSlots = false → (∀ v, some v ∈ fields → Reach s v) →
      ((kind = .atom ∨ kind = .args) →
        ∀ b, some (.ref b) ∈ fields → ∃ p, s.get b = some p ∧ p.kind = .atom) →
      Step.Enabled s (.alloc kind label fields)
  | activate {label : Label} {initial : List (Option Val)} :
      (∀ v, some v ∈ initial → Reach s v) → Step.Enabled s (.activate label initial)
  | newCell : Step.Enabled s .newCell
  | store {vector : Addr} {slot : Nat} {value : Val} {o : Obj Label} {birth : Nat} :
      Reach s (.ref vector) → Reach s value → s.get vector = some o → o.kind = .slots birth →
      o.fields[slot]? = some none → Step.Enabled s (.store vector slot value)
  | bind {cell : Nat} {value : Val} :
      Reach s (.cell cell) → Reach s value → s.cells[cell]? = some none →
      Step.Enabled s (.bind cell value)
  | push {vals : List Val} : (∀ v ∈ vals, Reach s v) → Step.Enabled s (.push vals)
  | pop {frame : Frame} {older : List Frame} : s.frames = frame :: older → Step.Enabled s .pop
  | restore {frame : Frame} {older : List Frame} : s.frames = frame :: older →
      Step.Enabled s .restore

/-! ### How each step changes the heap -/

section Heap

variable (s : State Label)

theorem get_alloc (kind : Kind) (label : Label) (fields : List (Option Val)) (a : Addr) :
    (s.alloc kind label fields).get a =
      if a = ⟨.young, s.young.length⟩ then some ⟨kind, label, fields⟩ else s.get a := by
  obtain ⟨gen, n⟩ := a
  cases gen with
  | old => simp [State.alloc, State.get]
  | young =>
    simp only [State.alloc, State.get, Addr.mk.injEq, true_and]
    rw [List.getElem?_append]
    by_cases lt : n < s.young.length
    · rw [if_pos lt, if_neg (Nat.ne_of_lt lt)]
    · rw [if_neg lt]
      by_cases eq : n = s.young.length
      · subst eq; simp
      · rw [if_neg eq, List.getElem?_eq_none (Nat.le_of_not_lt lt)]
        rw [List.getElem?_singleton, if_neg (by omega)]

theorem get_store (vector : Addr) (slot : Nat) (value : Val) (a : Addr) :
    (s.store vector slot value).get a =
      if a = vector then (s.get vector).map (fun o => { o with fields := o.fields.set slot (some value) })
      else s.get a := by
  have := get_update s vector (fun o => { o with fields := o.fields.set slot (some value) }) a
  obtain ⟨gen, n⟩ := vector
  cases gen <;> simpa [State.store, State.update, State.get] using this

@[simp] theorem store_call (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).call = s.call := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_regs (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).regs = s.regs := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_frames (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).frames = s.frames := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_cells (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).cells = s.cells := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_oldCells (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).oldCells = s.oldCells := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_trail (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).trail = s.trail := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

@[simp] theorem store_young_length (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).young.length = s.young.length := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> simp [State.store, State.update]

@[simp] theorem store_stores (vector : Addr) (slot : Nat) (value : Val) :
    (s.store vector slot value).stores =
      if s.trailsStore vector then s.stores ++ [(vector, slot)] else s.stores := by
  obtain ⟨gen, n⟩ := vector; cases gen <;> rfl

theorem get_restoreTo (frame : Frame) (a : Addr) :
    (s.restoreTo frame).get a =
      if a.gen = .young ∧ frame.mark ≤ a.index then none
      else (s.get a).map (clearSlots (s.stores.drop frame.storeMark) a) := by
  obtain ⟨gen, n⟩ := a
  cases gen with
  | old => simp [State.restoreTo, State.get]
  | young =>
    simp only [State.restoreTo, State.get, List.getElem?_take, List.getElem?_mapIdx, true_and]
    by_cases le : frame.mark ≤ n
    · rw [if_neg (by omega), if_pos le]
    · rw [if_pos (by omega), if_neg le]

theorem cells_restoreTo (frame : Frame) (i : Nat) :
    (s.restoreTo frame).cells[i]? =
      if i < frame.cellMark then
        s.cells[i]?.map fun binding => if i ∈ s.trail.drop frame.trailMark then none else binding
      else none := by
  simp [State.restoreTo, List.getElem?_take, List.getElem?_mapIdx]

theorem mem_clearSlots {entries : List (Addr × Nat)} {a : Addr} {o : Obj Label} {v : Val}
    (member : some v ∈ (clearSlots entries a o).fields) : some v ∈ o.fields := by
  simp only [clearSlots, List.mem_mapIdx] at member
  obtain ⟨j, lt, eq⟩ := member
  split at eq
  · exact absurd eq (by simp)
  · rw [← eq]; exact List.getElem_mem _

end Heap

/-! ### Reachability after each step -/

section Reachability

variable {s : State Label}

theorem reach_alloc {kind : Kind} {label : Label} {fields : List (Option Val)}
    (named : ∀ v, some v ∈ fields → Reach s v) :
    ∀ v, Reach (s.alloc kind label fields) v → Reach s v ∨ v = .ref ⟨.young, s.young.length⟩ := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    rcases root with call | regs | ⟨frame, member, vals⟩
    · exact Or.inl (Reach.root (Or.inl call))
    · rcases List.mem_cons.mp regs with eq | regs
      · exact Or.inr eq
      · exact Or.inl (Reach.root (Or.inr (Or.inl regs)))
    · exact Or.inl (Reach.root (Or.inr (Or.inr ⟨frame, member, vals⟩)))
  · intro a o v reached found member
    rw [get_alloc] at found
    split at found
    · cases found
      exact Or.inl (named v member)
    · rcases reached with reached | eq
      · exact Or.inl (Reach.field reached found member)
      · cases eq
        exact absurd rfl ‹¬_›
  · intro i v reached bound
    rcases reached with reached | eq
    · exact Or.inl (Reach.binding reached bound)
    · cases eq

theorem reach_newCell :
    ∀ v, Reach s.newCell v → Reach s v ∨ v = .cell s.cells.length := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    rcases root with call | regs | ⟨frame, member, vals⟩
    · exact Or.inl (Reach.root (Or.inl call))
    · rcases List.mem_cons.mp regs with eq | regs
      · exact Or.inr eq
      · exact Or.inl (Reach.root (Or.inr (Or.inl regs)))
    · exact Or.inl (Reach.root (Or.inr (Or.inr ⟨frame, member, vals⟩)))
  · intro a o v reached found member
    rcases reached with reached | eq
    · exact Or.inl (Reach.field reached found member)
    · cases eq
  · intro i v reached bound
    simp only [State.newCell] at bound
    rw [List.getElem?_append] at bound
    split at bound
    · rcases reached with reached | eq
      · exact Or.inl (Reach.binding reached bound)
      · cases eq; exact absurd ‹_› (Nat.lt_irrefl _)
    · rw [List.getElem?_singleton] at bound
      split at bound <;> cases bound

theorem reach_store {vector : Addr} {slot : Nat} {value : Val} (named : Reach s value) :
    ∀ v, Reach (s.store vector slot value) v → Reach s v := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    simp only [State.Root, store_call, store_regs, store_frames] at root
    exact Reach.root root
  · intro a o v reached found member
    rw [get_store] at found
    split at found
    · rename_i eq
      subst eq
      obtain ⟨o', found', rfl⟩ := Option.map_eq_some_iff.mp found
      rcases List.mem_or_eq_of_mem_set member with member | eq
      · exact Reach.field reached found' member
      · cases eq; exact named
    · exact Reach.field reached found member
  · intro i v reached bound
    rw [store_cells] at bound
    exact Reach.binding reached bound

theorem reach_bind {cell : Nat} {value : Val} (named : Reach s value) :
    ∀ v, Reach (s.bind cell value) v → Reach s v := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    exact Reach.root (by simpa [State.bind, State.Root] using root)
  · intro a o v reached found member
    exact Reach.field reached (by simpa [State.bind, State.get] using found) member
  · intro i v reached bound
    simp only [State.bind, List.getElem?_set] at bound
    split at bound
    · split at bound
      · cases bound; exact named
      · cases bound
    · exact Reach.binding reached bound

theorem reach_push {vals : List Val} (named : ∀ v ∈ vals, Reach s v) :
    ∀ v, Reach (s.push vals) v → Reach s v := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    rcases root with call | regs | ⟨frame, member, inVals⟩
    · exact Reach.root (Or.inl call)
    · exact Reach.root (Or.inr (Or.inl regs))
    · rcases List.mem_cons.mp member with eq | member
      · subst eq; exact named v inVals
      · exact Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩))
  · intro a o v reached found member
    exact Reach.field reached (by simpa [State.push, State.get] using found) member
  · intro i v reached bound
    exact Reach.binding reached (by simpa [State.push] using bound)

/-- Restoring a live frame, with any frames dropped, reaches nothing new. -/
theorem reach_restoreTo {frame : Frame} {frames : List Frame} (live : frame ∈ s.frames)
    (fewer : ∀ other ∈ frames, other ∈ s.frames) :
    ∀ v, Reach { s.restoreTo frame with frames := frames } v → Reach s v := by
  refine Reach.closed _ ?_ ?_ ?_
  · intro v root
    rcases root with call | regs | ⟨other, member, vals⟩
    · exact Reach.root (Or.inl call)
    · exact Reach.root (Or.inr (Or.inr ⟨frame, live, regs⟩))
    · exact Reach.root (Or.inr (Or.inr ⟨other, fewer other member, vals⟩))
  · intro a o v reached found member
    have found' : (s.restoreTo frame).get a = some o := by
      obtain ⟨gen, n⟩ := a
      cases gen <;> exact found
    rw [get_restoreTo] at found'
    split at found'
    · cases found'
    · obtain ⟨o', found'', rfl⟩ := Option.map_eq_some_iff.mp found'
      exact Reach.field reached found'' (mem_clearSlots member)
  · intro i v reached bound
    have bound' : (s.restoreTo frame).cells[i]? = some (some v) := bound
    rw [cells_restoreTo] at bound'
    split at bound'
    · obtain ⟨binding, found, eq⟩ := Option.map_eq_some_iff.mp bound'
      split at eq
      · cases eq
      · cases eq; exact Reach.binding reached found
    · cases bound'

theorem reach_restore : ∀ v, Reach s.restore v → Reach s v := by
  unfold State.restore
  split
  · exact fun _ => id
  · rename_i frame older frames
    exact reach_restoreTo (s := s) (frame := frame) (frames := s.frames)
      (by rw [frames]; exact List.mem_cons_self) (fun _ => id)

theorem reach_pop : ∀ v, Reach s.pop v → Reach s v := by
  unfold State.pop
  split
  · exact fun _ => id
  · rename_i frame older frames
    exact reach_restoreTo (by rw [frames]; exact List.mem_cons_self)
      (fun other member => by rw [frames]; exact List.mem_cons_of_mem _ member)

theorem reach_restoreAt (depth : Nat) : ∀ v, Reach (s.restoreAt depth) v → Reach s v := by
  unfold State.restoreAt
  split
  · exact fun _ => id
  · rename_i frame found
    exact reach_restoreTo (List.mem_of_getElem? found) (fun _ member => List.mem_of_mem_drop member)

end Reachability

/-! ## The allocation-order invariant -/

/-- A reached old object whose kind is not `exempt` names only old objects and cells below
`oldCells`. -/
def GenerationalOn (exempt : Kind → Bool) (s : State Label) : Prop :=
  ∀ a o v, Reach s (.ref a) → a.gen = .old → s.get a = some o → exempt o.kind = false →
    some v ∈ o.fields → s.Older v

/-- The mutator's allocation-order invariant: a reached old object other than a slot vector names
only old objects and cells below `oldCells`.  An old object was made before every region object
and every cell above `oldCells`; only an old slot vector changes after its promotion, by a store,
and so only it may name the region. -/
def Generational (s : State Label) : Prop :=
  GenerationalOn Kind.isSlots s

/-- A reached atom or argument vector names only atoms and cells. -/
def Typed (s : State Label) : Prop :=
  ∀ a o b, Reach s (.ref a) → s.get a = some o → (o.kind = .atom ∨ o.kind = .args) →
    some (.ref b) ∈ o.fields → ∃ p, s.get b = some p ∧ p.kind = .atom

section Preservation

variable {s : State Label}

theorem Generational.alloc (generational : Generational s) {kind : Kind} {label : Label}
    {fields : List (Option Val)} (named : ∀ v, some v ∈ fields → Reach s v) :
    Generational (s.alloc kind label fields) := by
  intro a o v reached old found notSlots member
  rcases reach_alloc named _ reached with reached | eq
  · rw [get_alloc, if_neg (by rintro rfl; cases old)] at found
    exact generational a o v reached old found notSlots member
  · cases eq; cases old

theorem Generational.newCell (generational : Generational s) : Generational s.newCell := by
  intro a o v reached old found notSlots member
  rcases reach_newCell _ reached with reached | eq
  · exact generational a o v reached old found notSlots member
  · cases eq

theorem Generational.store (generational : Generational s) {vector : Addr} {slot : Nat} {value : Val}
    {o : Obj Label} {birth : Nat} (named : Reach s value) (found : s.get vector = some o)
    (isVector : o.kind = .slots birth) : Generational (s.store vector slot value) := by
  intro a p v reached old found' notSlots member
  have reached' := reach_store named _ reached
  rw [get_store] at found'
  split at found'
  · rename_i eq
    subst eq
    rw [found] at found'
    cases found'
    simp [isVector, Kind.isSlots] at notSlots
  · have := generational a p v reached' old found' notSlots member
    obtain ⟨gen, n⟩ := vector
    cases v <;> cases gen <;> exact this

theorem Generational.bind (generational : Generational s) {cell : Nat} {value : Val}
    (named : Reach s value) : Generational (s.bind cell value) := by
  intro a o v reached old found notSlots member
  exact generational a o v (reach_bind named _ reached) old found notSlots member

theorem Generational.push (generational : Generational s) {vals : List Val}
    (named : ∀ v ∈ vals, Reach s v) : Generational (s.push vals) := by
  intro a o v reached old found notSlots member
  exact generational a o v (reach_push named _ reached) old found notSlots member

/-- A restore keeps the invariant when what it reaches is there: an old object still reached
names no cell made after the frame. -/
theorem Generational.restoreTo (generational : Generational s) {frame : Frame}
    {frames : List Frame} (live : frame ∈ s.frames) (fewer : ∀ other ∈ frames, other ∈ s.frames)
    (present : NoDangling { s.restoreTo frame with frames := frames }) :
    Generational { s.restoreTo frame with frames := frames } := by
  intro a o v reached old found notSlots member
  have reached' := reach_restoreTo live fewer _ reached
  have found' : (s.restoreTo frame).get a = some o := by
    obtain ⟨gen, n⟩ := a
    cases gen <;> exact found
  rw [get_restoreTo, if_neg (by rw [old]; simp)] at found'
  obtain ⟨o', found'', rfl⟩ := Option.map_eq_some_iff.mp found'
  have older := generational a o' v reached' old found'' notSlots (mem_clearSlots member)
  cases v with
  | ref b => exact older
  | cell i =>
    have there := present _ (Reach.field reached found member)
    simp only [State.Present, State.restoreTo, List.length_take, List.length_mapIdx] at there
    simp only [State.Older, State.restoreTo] at older ⊢
    omega


theorem Typed.alloc (typed : Typed s) {kind : Kind} {label : Label} {fields : List (Option Val)}
    (named : ∀ v, some v ∈ fields → Reach s v)
    (atoms : (kind = .atom ∨ kind = .args) →
      ∀ b, some (.ref b) ∈ fields → ∃ p, s.get b = some p ∧ p.kind = .atom) :
    Typed (s.alloc kind label fields) := by
  have stays : ∀ b p, s.get b = some p → (s.alloc kind label fields).get b = some p := by
    intro b p found
    rw [get_alloc, if_neg]
    · exact found
    · rintro rfl; simp at found
  intro a o b reached found kindOf member
  rw [get_alloc] at found
  split at found
  · cases found
    obtain ⟨p, found', atom⟩ := atoms kindOf b member
    exact ⟨p, stays b p found', atom⟩
  · rcases reach_alloc named _ reached with reached | eq
    · obtain ⟨p, found', atom⟩ := typed a o b reached found kindOf member
      exact ⟨p, stays b p found', atom⟩
    · cases eq; exact absurd rfl ‹¬_›

theorem Typed.newCell (typed : Typed s) : Typed s.newCell := by
  intro a o b reached found kindOf member
  rcases reach_newCell _ reached with reached | eq
  · exact typed a o b reached found kindOf member
  · cases eq

theorem Typed.store (typed : Typed s) {vector : Addr} {slot : Nat} {value : Val}
    {o : Obj Label} {birth : Nat} (named : Reach s value) (found : s.get vector = some o)
    (isVector : o.kind = .slots birth) : Typed (s.store vector slot value) := by
  have kinds : ∀ b p, s.get b = some p → ∃ p', (s.store vector slot value).get b = some p' ∧
      p'.kind = p.kind := by
    intro b p found'
    rw [get_store]
    split
    · rename_i eq; subst eq; rw [found'] at found ⊢; exact ⟨_, rfl, rfl⟩
    · exact ⟨p, found', rfl⟩
  intro a p b reached found' kindOf member
  rw [get_store] at found'
  split at found'
  · rename_i eq
    subst eq
    rw [found] at found'
    cases found'
    rcases kindOf with k | k <;> simp [isVector] at k
  · obtain ⟨q, foundB, atom⟩ := typed a p b (reach_store named _ reached) found' kindOf member
    obtain ⟨q', foundB', same⟩ := kinds b q foundB
    exact ⟨q', foundB', same.trans atom⟩

theorem Typed.bind (typed : Typed s) {cell : Nat} {value : Val} (named : Reach s value) :
    Typed (s.bind cell value) := by
  intro a o b reached found kindOf member
  exact typed a o b (reach_bind named _ reached) found kindOf member

theorem Typed.push (typed : Typed s) {vals : List Val} (named : ∀ v ∈ vals, Reach s v) :
    Typed (s.push vals) := by
  intro a o b reached found kindOf member
  exact typed a o b (reach_push named _ reached) found kindOf member

theorem Typed.restoreTo (typed : Typed s) {frame : Frame} {frames : List Frame}
    (live : frame ∈ s.frames) (fewer : ∀ other ∈ frames, other ∈ s.frames)
    (present : NoDangling { s.restoreTo frame with frames := frames }) :
    Typed { s.restoreTo frame with frames := frames } := by
  intro a o b reached found kindOf member
  have found' : (s.restoreTo frame).get a = some o := by
    obtain ⟨gen, n⟩ := a
    cases gen <;> exact found
  rw [get_restoreTo] at found'
  split at found'
  · cases found'
  · obtain ⟨o', found'', rfl⟩ := Option.map_eq_some_iff.mp found'
    obtain ⟨p, foundB, atom⟩ :=
      typed a o' b (reach_restoreTo live fewer _ reached) found'' kindOf (mem_clearSlots member)
    have there := present _ (Reach.field reached found member)
    simp only [State.Present] at there
    obtain ⟨q, foundB'⟩ := Option.isSome_iff_exists.mp there
    have foundB'' : (s.restoreTo frame).get b = some q := by
      obtain ⟨gen, n⟩ := b
      cases gen <;> exact foundB'
    rw [get_restoreTo] at foundB''
    split at foundB''
    · cases foundB''
    · rw [foundB] at foundB''
      cases foundB''
      exact ⟨_, foundB', atom⟩

end Preservation

/-! ## Minor collections -/

/-- How a minor collection treats the old objects it reaches, by kind: whether it copies them
into the old generation as it copies the region's (`copies`), renames their fields in place
(`rewrites`), and whether its trace goes through them (`walks`).  Every region object it reaches
is copied and walked. -/
structure Policy where
  copies : Kind → Bool
  rewrites : Kind → Bool
  walks : Kind → Bool

/-- What a policy must do, against an invariant that lets old objects of the `exempt` kinds name
the region: walk continuations, which reach slot vectors; copy or rewrite slot vectors and the
exempt kinds; walk what it copies or rewrites; never copy atoms, which are never exempt; and copy
continuations whenever it copies anything, so no continuation left in place names a copied
object. -/
structure Policy.Sound (policy : Policy) (exempt : Kind → Bool) : Prop where
  walks_cont : policy.walks .cont = true
  slots : ∀ birth, policy.copies (.slots birth) = true ∨ policy.rewrites (.slots birth) = true
  handles : ∀ kind, exempt kind = true → policy.copies kind = true ∨ policy.rewrites kind = true
  copies_walked : ∀ kind, policy.copies kind = true → policy.walks kind = true
  rewrites_walked : ∀ kind, policy.rewrites kind = true → policy.walks kind = true
  copies_atom : policy.copies .atom = false
  exempt_atom : exempt .atom = false
  copies_cont : ∀ kind, policy.copies kind = true → policy.copies .cont = true

/-- The open tier's minor collection: every old object stays in place; old slot vectors are
renamed in place; the trace goes through old continuations and slot vectors, but not through old
atoms or old argument vectors. -/
def sharing : Policy where
  copies _ := false
  rewrites := Kind.isSlots
  walks kind := kind == .cont || kind.isSlots

/-- The full-copy minor collection: old continuations, slot vectors and argument vectors are
copied again, old atoms are shared. -/
def fullCopy : Policy where
  copies kind := kind != .atom
  rewrites _ := false
  walks kind := kind != .atom

/-- A minor collection that treats old argument vectors as mutable, renaming them in place as it
does slot vectors. -/
def rewritingArgs : Policy where
  copies _ := false
  rewrites kind := kind == .args || kind.isSlots
  walks kind := kind != .atom

/-- The invariant that also lets old argument vectors name the region, as it would have to if
argument vectors could change after their frame is pushed. -/
def argsOrSlots (kind : Kind) : Bool := kind == .args || kind.isSlots

theorem sharing_sound : sharing.Sound Kind.isSlots where
  walks_cont := rfl
  slots _ := Or.inr rfl
  handles _ exempt := Or.inr exempt
  copies_walked _ copies := absurd copies (by simp [sharing])
  rewrites_walked kind rewrites := by
    cases kind <;> simp_all [sharing, Kind.isSlots]
  copies_atom := rfl
  exempt_atom := rfl
  copies_cont _ copies := absurd copies (by simp [sharing])

theorem fullCopy_sound : fullCopy.Sound argsOrSlots where
  walks_cont := rfl
  slots _ := Or.inl rfl
  handles kind exempt := by
    left; cases kind <;> simp_all [fullCopy, argsOrSlots, Kind.isSlots]
  copies_walked _ copies := copies
  rewrites_walked _ rewrites := absurd rewrites (by simp [fullCopy])
  copies_atom := rfl
  exempt_atom := rfl
  copies_cont _ _ := rfl

theorem rewritingArgs_sound : rewritingArgs.Sound argsOrSlots where
  walks_cont := rfl
  slots _ := Or.inr rfl
  handles _ exempt := Or.inr exempt
  copies_walked _ copies := absurd copies (by simp [rewritingArgs])
  rewrites_walked kind rewrites := by
    cases kind <;> simp_all [rewritingArgs, Kind.isSlots]
  copies_atom := rfl
  exempt_atom := rfl
  copies_cont _ copies := absurd copies (by simp [rewritingArgs])

/-- A policy sound against an invariant is sound against any stronger one. -/
theorem Policy.Sound.narrow {policy : Policy} {exempt narrower : Kind → Bool}
    (sound : policy.Sound exempt) (within : ∀ kind, narrower kind = true → exempt kind = true)
    (narrower_atom : narrower .atom = false) : policy.Sound narrower where
  walks_cont := sound.walks_cont
  slots := sound.slots
  handles kind isExempt := sound.handles kind (within kind isExempt)
  copies_walked := sound.copies_walked
  rewrites_walked := sound.rewrites_walked
  copies_atom := sound.copies_atom
  exempt_atom := narrower_atom
  copies_cont := sound.copies_cont

/-- `R` holds what a trace under `policy` visits: the roots, every cell below `oldCells` (an old
object may name any of them), whatever a visited region object or a visited old object of a
walked kind names, and a visited cell's binding. -/
structure Traced (policy : Policy) (s : State Label) (R : Val → Bool) : Prop where
  root : ∀ v, s.Root v → R v = true
  fixed : ∀ i, i < s.oldCells → R (.cell i) = true
  field : ∀ a o v, R (.ref a) = true → s.get a = some o →
    (a.gen = .young ∨ policy.walks o.kind = true) → some v ∈ o.fields → R v = true
  binding : ∀ i v, R (.cell i) = true → s.cells[i]? = some (some v) → R v = true

/-- An old atom: what a trace may reach without visiting. -/
def OldAtom (s : State Label) (v : Val) : Prop :=
  ∃ a p, v = .ref a ∧ a.gen = .old ∧ s.get a = some p ∧ p.kind = .atom

section Trace

variable {policy : Policy} {exempt : Kind → Bool} {s : State Label} {R : Val → Bool}

/-- Everything reached is visited, or is an old atom: an old atom or argument vector the trace
does not walk names only old atoms and old cells, which the trace holds already. -/
theorem reach_traced (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) :
    ∀ v, Reach s v → R v = true ∨ OldAtom s v := by
  intro v reach
  induction reach with
  | root isRoot => exact Or.inl (traced.root _ isRoot)
  | @field a o v reached found member ih =>
    have frontier : a.gen = .old → (o.kind = .atom ∨ o.kind = .args) →
        exempt o.kind = false → R v = true ∨ OldAtom s v := by
      intro old kind notExempt
      have older := generational a o v reached old found notExempt member
      cases v with
      | cell i => exact Or.inl (traced.fixed i older)
      | ref b =>
        obtain ⟨p, found', atom⟩ := typed a o b reached found kind member
        exact Or.inr ⟨b, p, rfl, older, found', atom⟩
    rcases ih with inR | ⟨a', p, eq, old, found', atom⟩
    · by_cases walked : a.gen = .young ∨ policy.walks o.kind = true
      · exact Or.inl (traced.field a o v inR found walked member)
      · have old : a.gen = .old := by
          cases gen : a.gen with
          | young => exact absurd (Or.inl gen) walked
          | old => rfl
        have notWalked : policy.walks o.kind = false := by
          cases walks : policy.walks o.kind with
          | false => rfl
          | true => exact absurd (Or.inr walks) walked
        have notExempt : exempt o.kind = false := by
          cases isExempt : exempt o.kind with
          | false => rfl
          | true =>
            rcases sound.handles _ isExempt with copies | rewrites
            · rw [sound.copies_walked _ copies] at notWalked; cases notWalked
            · rw [sound.rewrites_walked _ rewrites] at notWalked; cases notWalked
        refine frontier old ?_ notExempt
        cases kind : o.kind with
        | atom => exact Or.inl rfl
        | args => exact Or.inr rfl
        | cont => rw [kind, sound.walks_cont] at notWalked; cases notWalked
        | slots birth =>
          rw [kind] at notWalked
          rcases sound.slots birth with copies | rewrites
          · rw [sound.copies_walked _ copies] at notWalked; cases notWalked
          · rw [sound.rewrites_walked _ rewrites] at notWalked; cases notWalked
    · cases eq
      rw [found] at found'
      cases found'
      exact frontier old (Or.inl atom) (by rw [atom]; exact sound.exempt_atom)
  | @binding i v reached bound ih =>
    rcases ih with inR | ⟨a, p, eq, _⟩
    · exact Or.inl (traced.binding i v inR bound)
    · cases eq

theorem traced_cell (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) {i : Nat}
    (reached : Reach s (.cell i)) :
    R (.cell i) = true := by
  rcases reach_traced sound traced generational typed _ reached with inR | ⟨a, p, eq, _⟩
  · exact inR
  · cases eq

end Trace

section Collect

variable (policy : Policy) (R : Val → Bool) (s : State Label)

/-- The region objects a collection copies: those it reached. -/
def keepYoung (n : Nat) : Bool := R (.ref ⟨.young, n⟩)

/-- The old objects a collection copies: those it reached, of a kind it copies. -/
def keepOld (m : Nat) : Bool :=
  R (.ref ⟨.old, m⟩) && ((s.old[m]?).map fun o => policy.copies o.kind).getD false

/-- The cells a collection keeps: those it reached. -/
def keepCell (i : Nat) : Bool := R (.cell i)

/-- The store-trail entries a collection keeps: those whose vector it reached. -/
def keepStore (e : Addr × Nat) : Bool := R (.ref e.1)

/-- How many region objects a collection copies. -/
def youngCopies : Nat := countFrom (keepYoung R) 0 s.young.length

/-- Where a collection puts each object: a region object's copy follows the old generation, a
copied old object's copy follows the region's copies, and every other old object stays. -/
def promote (a : Addr) : Addr :=
  match a.gen with
  | .young => ⟨.old, s.old.length + countFrom (keepYoung R) 0 a.index⟩
  | .old =>
    if keepOld policy R s a.index then
      ⟨.old, s.old.length + youngCopies R s + countFrom (keepOld policy R s) 0 a.index⟩
    else a

/-- A kept cell's new index: how many kept cells lie below it. -/
def renumber (i : Nat) : Nat := countFrom (keepCell R) 0 i

/-- A collection's renaming of values. -/
def rename : Val → Val := mapVal (promote policy R s) (renumber R)

/-- An old object after a collection: renamed in place when reached and of a kind the policy
rewrites. -/
def rewriteOld (m : Nat) (o : Obj Label) : Obj Label :=
  if R (.ref ⟨.old, m⟩) && policy.rewrites o.kind then o.map (rename policy R s) else o

/-- A frame after a collection: its roots renamed, its region mark at the empty region, and its
other marks counting what the collection kept below them. -/
def collectFrame (keepS : Addr × Nat → Bool) (frame : Frame) : Frame where
  vals := frame.vals.map (rename policy R s)
  mark := 0
  cellMark := renumber R frame.cellMark
  trailMark := (s.trail.take frame.trailMark).countP (keepCell R)
  storeMark := (s.stores.take frame.storeMark).countP keepS

/-- A minor collection under `policy` from the reached set `R`, keeping the store-trail entries
`keepS` accepts.  The region's reached objects are copied in region order after the old
generation, then the old objects the policy copies; the region is left empty. -/
def collectWith (keepS : Addr × Nat → Bool) : State Label where
  young := []
  old := s.old.mapIdx (rewriteOld policy R s) ++
    keepMap (keepYoung R) (Obj.map (rename policy R s)) 0 s.young ++
    keepMap (keepOld policy R s) (Obj.map (rename policy R s)) 0 s.old
  cells := keepMap (keepCell R) (Option.map (rename policy R s)) 0 s.cells
  oldCells := renumber R s.cells.length
  trail := (s.trail.filter (keepCell R)).map (renumber R)
  stores := (s.stores.filter keepS).map fun e => (promote policy R s e.1, e.2)
  frames := s.frames.map (collectFrame policy R s keepS)
  call := s.call.map (rename policy R s)
  regs := s.regs.map (rename policy R s)

/-- The minor collection: it keeps the store-trail entries of the vectors it reached. -/
def collect : State Label := collectWith policy R s (keepStore R)

/-- A minor collection declines when it has reached at least half of the region. -/
def declines : Bool := s.young.length ≤ 2 * youngCopies R s

/-- A minor collection, or its decline, which leaves the state as it is. -/
def minor : State Label := if declines R s then s else collect policy R s

end Collect

section CollectHeap

variable (policy : Policy) (R : Val → Bool) (s : State Label) (keepS : Addr × Nat → Bool)

theorem collectWith_get_inPlace {m : Nat} (lt : m < s.old.length) :
    (collectWith policy R s keepS).get ⟨.old, m⟩ = (s.old[m]?).map (rewriteOld policy R s m) := by
  simp only [get_old, collectWith]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_append_left (by simpa using lt),
    List.getElem?_mapIdx]

theorem collectWith_get_youngCopy {n : Nat} (lt : n < s.young.length)
    (kept : keepYoung R n = true) :
    (collectWith policy R s keepS).get (promote policy R s ⟨.young, n⟩) =
      (s.young[n]?).map (Obj.map (rename policy R s)) := by
  have below : countFrom (keepYoung R) 0 n < youngCopies R s :=
    countFrom_lt _ 0 lt (by simpa using kept)
  simp only [promote, get_old, collectWith]
  rw [List.getElem?_append_left (by simp [length_keepMap]; exact below),
    List.getElem?_append_right (by simp), List.length_mapIdx, Nat.add_sub_cancel_left,
    getElem?_keepMap _ _ 0 s.young n lt (by simpa using kept)]

theorem collectWith_get_oldCopy {m : Nat} (lt : m < s.old.length)
    (kept : keepOld policy R s m = true) :
    (collectWith policy R s keepS).get (promote policy R s ⟨.old, m⟩) =
      (s.old[m]?).map (Obj.map (rename policy R s)) := by
  simp only [promote, kept, if_true, get_old, collectWith]
  rw [List.getElem?_append_right (by simp [length_keepMap, youngCopies])]
  simp only [List.length_append, List.length_mapIdx, length_keepMap]
  rw [show s.old.length + youngCopies R s + countFrom (keepOld policy R s) 0 m -
      (s.old.length + countFrom (keepYoung R) 0 s.young.length) =
      countFrom (keepOld policy R s) 0 m by simp [youngCopies],
    getElem?_keepMap _ _ 0 s.old m lt (by simpa using kept)]

theorem promote_old (a : Addr) : (promote policy R s a).gen = .old := by
  obtain ⟨gen, n⟩ := a
  cases gen with
  | young => rfl
  | old =>
    simp only [promote]
    split <;> rfl

end CollectHeap

section CollectImage

variable {policy : Policy} {exempt : Kind → Bool} {R : Val → Bool} {s : State Label}

/-- An old object a collection neither copies nor rewrites names only what the renaming fixes. -/
theorem rename_fixed (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) {m : Nat} {o : Obj Label}
    (reached : Reach s (.ref ⟨.old, m⟩)) (found : s.old[m]? = some o)
    (stays : keepOld policy R s m = false)
    (unrewritten : (R (.ref ⟨.old, m⟩) && policy.rewrites o.kind) = false) :
    o.map (rename policy R s) = o := by
  have visited : o.kind ≠ .atom → R (.ref ⟨.old, m⟩) = true := by
    intro notAtom
    rcases reach_traced sound traced generational typed _ reached with
      inR | ⟨a, p, eq, _, found', atom⟩
    · exact inR
    · cases eq
      simp only [get_old] at found'
      rw [found] at found'
      cases found'
      exact absurd atom notAtom
  have notExempt : exempt o.kind = false := by
    by_cases atom : o.kind = .atom
    · rw [atom]; exact sound.exempt_atom
    · have inR := visited atom
      cases isExempt : exempt o.kind with
      | false => rfl
      | true =>
        exfalso
        rcases sound.handles _ isExempt with copies | rewrites
        · simp [keepOld, inR, found, copies] at stays
        · simp [inR, rewrites] at unrewritten
  have notSlots : o.kind.isSlots = false := by
    cases kind : o.kind with
    | slots birth =>
      have inR := visited (by rw [kind]; simp)
      exfalso
      rcases sound.slots birth with copies | rewrites
      · simp [keepOld, inR, found, kind, copies] at stays
      · simp [inR, kind, rewrites] at unrewritten
    | _ => rfl
  apply Obj.map_eq_self
  intro v member
  have older := generational ⟨.old, m⟩ o v reached rfl found notExempt member
  cases v with
  | cell i =>
    simp only [rename, mapVal, renumber, Val.cell.injEq]
    exact countFrom_of_all _ 0 fun j lt => by
      simpa [keepCell] using traced.fixed j (Nat.lt_trans lt older)
  | ref b =>
    obtain ⟨gen, n⟩ := b
    simp only [State.Older] at older
    subst older
    have stay : keepOld policy R s n = false := by
      cases kind : o.kind with
      | atom =>
        obtain ⟨p, found', atom⟩ :=
          typed _ o _ reached found (Or.inl kind) member
        simp only [get_old] at found'
        simp [keepOld, found', atom, sound.copies_atom]
      | args =>
        obtain ⟨p, found', atom⟩ :=
          typed _ o _ reached found (Or.inr kind) member
        simp only [get_old] at found'
        simp [keepOld, found', atom, sound.copies_atom]
      | cont =>
        have inR := visited (by rw [kind]; simp)
        have noCont : policy.copies .cont = false := by
          simpa [keepOld, inR, found, kind] using stays
        have none : ∀ kind, policy.copies kind = false := by
          intro kind
          cases copies : policy.copies kind with
          | false => rfl
          | true => rw [sound.copies_cont _ copies] at noCont; cases noCont
        cases found' : s.old[n]? with
        | none => simp [keepOld, found']
        | some p => simp [keepOld, found', none]
      | slots birth => rw [kind] at notSlots; cases notSlots
    simp [rename, mapVal, promote, stay]

/-- A minor collection's result is the image of what the state reaches: region objects moved to
their copies, old objects in place (renamed in place where the policy rewrites them), reached
cells renumbered, roots renamed. -/
theorem collectWith_image (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) :
    Image (promote policy R s) (renumber R) s (collectWith policy R s keepS) where
  obj a reached := by
    have there := present _ reached
    simp only [State.Present] at there
    obtain ⟨o, found⟩ := Option.isSome_iff_exists.mp there
    obtain ⟨gen, n⟩ := a
    cases gen with
    | young =>
      have inR : keepYoung R n = true := by
        rcases reach_traced sound traced generational typed _ reached with
          inR | ⟨a', p, eq, old, _⟩
        · exact inR
        · cases eq; cases old
      have lt : n < s.young.length := by
        simp only [get_young] at found
        exact (List.getElem?_eq_some_iff.mp found).1
      exact collectWith_get_youngCopy policy R s keepS lt inR
    | old =>
      have lt : n < s.old.length := by
        simp only [get_old] at found
        exact (List.getElem?_eq_some_iff.mp found).1
      cases kept : keepOld policy R s n with
      | true => exact collectWith_get_oldCopy policy R s keepS lt kept
      | false =>
        have stay : promote policy R s ⟨.old, n⟩ = ⟨.old, n⟩ := by simp [promote, kept]
        rw [stay, collectWith_get_inPlace policy R s keepS lt]
        simp only [get_old] at found ⊢
        rw [found, Option.map_some, Option.map_some]
        congr 1
        unfold rewriteOld
        cases rewrites : (R (.ref ⟨.old, n⟩) && policy.rewrites o.kind) with
        | true => rfl
        | false =>
          rw [if_neg (by simp)]
          exact (rename_fixed sound traced generational typed reached found kept rewrites).symm
  cell i reached := by
    have inR := traced_cell sound traced generational typed reached
    have lt : i < s.cells.length := present _ reached
    exact getElem?_keepMap _ _ 0 s.cells i lt (by simpa [keepCell] using inR)
  call := rfl
  regs := rfl
  frames := by
    simp only [collectWith, List.map_map]
    rfl

end CollectImage

/-! ## Images -/

section Images

variable {φ : Addr → Addr} {ρ : Nat → Nat} {s t : State Label}

/-- Everything the image reaches is the image of something the state reaches. -/
theorem Image.reach (image : Image φ ρ s t) :
    ∀ w, Reach t w → ∃ v, Reach s v ∧ w = mapVal φ ρ v := by
  intro w reach
  induction reach with
  | @root w isRoot =>
    rcases isRoot with call | regs | ⟨frame', member, vals⟩
    · rw [image.call] at call
      obtain ⟨v, member, rfl⟩ := List.mem_map.mp call
      exact ⟨v, Reach.root (Or.inl member), rfl⟩
    · rw [image.regs] at regs
      obtain ⟨v, member, rfl⟩ := List.mem_map.mp regs
      exact ⟨v, Reach.root (Or.inr (Or.inl member)), rfl⟩
    · have inVals : frame'.vals ∈ t.frames.map Frame.vals := List.mem_map_of_mem member
      rw [image.frames] at inVals
      obtain ⟨frame, member', eq⟩ := List.mem_map.mp inVals
      rw [← eq] at vals
      obtain ⟨v, member'', rfl⟩ := List.mem_map.mp vals
      exact ⟨v, Reach.root (Or.inr (Or.inr ⟨frame, member', member''⟩)), rfl⟩
  | @field b o' w _ found member ih =>
    obtain ⟨v, reached, eq⟩ := ih
    cases v with
    | cell i => cases eq
    | ref a =>
      cases eq
      rw [image.obj a reached] at found
      obtain ⟨o, found', rfl⟩ := Option.map_eq_some_iff.mp found
      simp only [Obj.map_fields, List.mem_map] at member
      obtain ⟨field, member', eq⟩ := member
      cases field with
      | none => cases eq
      | some v =>
        cases eq
        exact ⟨v, Reach.field reached found' member', rfl⟩
  | @binding j w _ bound ih =>
    obtain ⟨v, reached, eq⟩ := ih
    cases v with
    | ref a => cases eq
    | cell i =>
      cases eq
      rw [image.cell i reached] at bound
      obtain ⟨binding, found, eq⟩ := Option.map_eq_some_iff.mp bound
      cases binding with
      | none => cases eq
      | some v =>
        cases eq
        exact ⟨v, Reach.binding reached found, rfl⟩

/-- The image of a state no reached value dangles in dangles nowhere either. -/
theorem Image.noDangling (image : Image φ ρ s t) (present : NoDangling s) : NoDangling t := by
  intro w reached
  obtain ⟨v, reached', rfl⟩ := image.reach w reached
  have there := present v reached'
  cases v with
  | ref a =>
    show (t.get (φ a)).isSome = true
    rw [image.obj a reached']
    simp only [State.Present] at there
    obtain ⟨o, found⟩ := Option.isSome_iff_exists.mp there
    simp [found]
  | cell i =>
    show ρ i < t.cells.length
    have := image.cell i reached'
    have there' : i < s.cells.length := there
    rw [List.getElem?_eq_getElem there', Option.map_some] at this
    exact (List.getElem?_eq_some_iff.mp this).1

theorem mapVal_id (v : Val) : mapVal id id v = v := by
  cases v <;> rfl

theorem mapVal_id_id : mapVal id id = id := funext mapVal_id

theorem Obj.map_id (o : Obj Label) : o.map id = o := Obj.map_eq_self fun _ _ => rfl

/-- Every state is the image of itself. -/
theorem Image.refl (s : State Label) : Image id id s s where
  obj a _ := by
    show s.get a = (s.get a).map (Obj.map (mapVal id id))
    rw [mapVal_id_id]
    cases s.get a with
    | none => rfl
    | some o => rw [Option.map_some, Obj.map_id]
  cell i _ := by
    show s.cells[i]? = s.cells[i]?.map (Option.map (mapVal id id))
    rw [mapVal_id_id]
    cases s.cells[i]? with
    | none => rfl
    | some binding => cases binding <;> rfl
  call := by rw [mapVal_id_id, List.map_id]
  regs := by rw [mapVal_id_id, List.map_id]
  frames := by rw [mapVal_id_id]; simp

end Images

theorem Obj.map_map (f g : Val → Val) (o : Obj Label) : (o.map f).map g = o.map (g ∘ f) := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [Obj.map, List.map_map, Obj.mk.injEq, true_and]
  refine List.map_congr_left fun field _ => ?_
  cases field <;> rfl

theorem Obj.map_congr {f g : Val → Val} {o : Obj Label}
    (same : ∀ v, some v ∈ o.fields → f v = g v) : o.map f = o.map g := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [Obj.map, Obj.mk.injEq, true_and]
  refine List.map_congr_left fun field member => ?_
  cases field with
  | none => rfl
  | some v => simp [same v member]

/-- Two images of one state are images of each other, through a renaming that takes the first
image's names to the second's. -/
theorem Image.across {φ₁ φ₂ ψ : Addr → Addr} {ρ₁ ρ₂ σ : Nat → Nat} {s t₁ t₂ : State Label}
    (first : Image φ₁ ρ₁ s t₁) (second : Image φ₂ ρ₂ s t₂)
    (commutes : ∀ v, Reach s v → mapVal ψ σ (mapVal φ₁ ρ₁ v) = mapVal φ₂ ρ₂ v) :
    Image ψ σ t₁ t₂ where
  obj b reached := by
    obtain ⟨v, reachedS, eq⟩ := first.reach _ reached
    cases v with
    | cell i => cases eq
    | ref a =>
      cases eq
      have moved : ψ (φ₁ a) = φ₂ a := by simpa [mapVal] using commutes _ reachedS
      rw [moved, second.obj a reachedS, first.obj a reachedS]
      cases found : s.get a with
      | none => rfl
      | some o =>
        simp only [Option.map_some, Obj.map_map]
        exact congrArg some
          (Obj.map_congr fun v member => (commutes v (Reach.field reachedS found member)).symm)
  cell j reached := by
    obtain ⟨v, reachedS, eq⟩ := first.reach _ reached
    cases v with
    | ref a => cases eq
    | cell i =>
      cases eq
      have moved : σ (ρ₁ i) = ρ₂ i := by simpa [mapVal] using commutes _ reachedS
      rw [moved, second.cell i reachedS, first.cell i reachedS]
      cases found : s.cells[i]? with
      | none => rfl
      | some binding =>
        cases binding with
        | none => rfl
        | some w =>
          simp only [Option.map_some]
          rw [commutes w (Reach.binding reachedS found)]
  call := by
    rw [second.call, first.call, List.map_map]
    exact List.map_congr_left fun v member => (commutes v (Reach.root (Or.inl member))).symm
  regs := by
    rw [second.regs, first.regs, List.map_map]
    exact List.map_congr_left fun v member =>
      (commutes v (Reach.root (Or.inr (Or.inl member)))).symm
  frames := by
    have split : (t₁.frames.map fun frame => frame.vals.map (mapVal ψ σ)) =
        (t₁.frames.map Frame.vals).map (List.map (mapVal ψ σ)) := by
      rw [List.map_map]; rfl
    rw [split, second.frames, first.frames, List.map_map]
    refine List.map_congr_left fun frame member => ?_
    simp only [Function.comp_apply, List.map_map]
    exact List.map_congr_left fun v inVals =>
      (commutes v (Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩)))).symm

/-! ## After a minor collection -/

section After

variable {policy : Policy} {exempt : Kind → Bool} {R : Val → Bool} {s : State Label}

/-- Every read from a reached value agrees after a minor collection, cells shown by their new
indices. -/
theorem collectWith_read (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) (n : Nat) (v : Val) (reached : Reach s v) :
    read (collectWith policy R s keepS) n (rename policy R s v) = readAs (renumber R) s n v :=
  (collectWith_image sound traced generational typed present keepS).read_eq n v reached

theorem collectWith_noDangling (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) : NoDangling (collectWith policy R s keepS) :=
  (collectWith_image sound traced generational typed present keepS).noDangling present

/-- After promotion nothing reached names the region: every reached value is an old object or a
cell below the new `oldCells`. -/
theorem collectWith_older (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) :
    ∀ w, Reach (collectWith policy R s keepS) w → (collectWith policy R s keepS).Older w := by
  intro w reached
  have there := collectWith_noDangling sound traced generational typed present keepS w reached
  obtain ⟨v, _, rfl⟩ :=
    (collectWith_image sound traced generational typed present keepS).reach w reached
  cases v with
  | ref a => exact promote_old policy R s a
  | cell i =>
    have lt : renumber R i < (collectWith policy R s keepS).cells.length := there
    show renumber R i < renumber R s.cells.length
    simpa [collectWith, length_keepMap, renumber] using lt

/-- A minor collection re-establishes the allocation-order invariant without its exemption:
after promotion, no reached object, slot vectors included, names the region. -/
theorem collectWith_generational (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) :
    GenerationalOn (fun _ => false) (collectWith policy R s keepS) := by
  intro a o v reached _ found _ member
  exact collectWith_older sound traced generational typed present keepS v
    (Reach.field reached found member)

theorem collectWith_typed (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (keepS : Addr × Nat → Bool) : Typed (collectWith policy R s keepS) := by
  have image := collectWith_image sound traced generational typed present keepS
  intro a' o' b' reached found kind member
  obtain ⟨v, reachedS, eq⟩ := image.reach _ reached
  cases v with
  | cell i => cases eq
  | ref a =>
    cases eq
    rw [image.obj a reachedS] at found
    obtain ⟨o, foundS, rfl⟩ := Option.map_eq_some_iff.mp found
    simp only [Obj.map_fields, List.mem_map] at member
    obtain ⟨field, member', eq⟩ := member
    cases field with
    | none => cases eq
    | some v =>
      cases v with
      | cell i => cases eq
      | ref b =>
        cases eq
        obtain ⟨p, foundB, atom⟩ := typed a o b reachedS foundS kind member'
        refine ⟨p.map (rename policy R s), ?_, atom⟩
        rw [image.obj b (Reach.field reachedS foundS member'), foundB]
        rfl

theorem minor_declined {policy : Policy} {R : Val → Bool} {s : State Label}
    (declined : declines R s = true) : minor policy R s = s := by
  simp [minor, declined]

/-- A minor collection, declined or not, leaves an image of what the state reaches; a declined
one is the identity. -/
theorem minor_image (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s) :
    Image (if declines R s then id else promote policy R s) (if declines R s then id else renumber R)
      s (minor policy R s) := by
  cases declined : declines R s with
  | true => simpa [minor, declined] using Image.refl s
  | false =>
    simpa [minor, declined, collect] using
      collectWith_image sound traced generational typed present (keepStore R)

end After

/-! ## Three policies, one result -/

section Policies

variable {R : Val → Bool} {s : State Label}

/-- A trace closed under a policy's walks is closed under any policy that walks less. -/
theorem Traced.mono {policy₁ policy₂ : Policy}
    (walks : ∀ kind, policy₁.walks kind = true → policy₂.walks kind = true)
    (traced : Traced policy₂ s R) : Traced policy₁ s R where
  root := traced.root
  fixed := traced.fixed
  field a o v inR found walked member := traced.field a o v inR found (walked.imp id (walks _)) member
  binding := traced.binding

theorem keepOld_of_copies_none {policy : Policy} (none : ∀ kind, policy.copies kind = false)
    (m : Nat) : keepOld policy R s m = false := by
  cases found : s.old[m]? <;> simp [keepOld, found, none]

theorem sharing_walks_fullCopy : ∀ kind, sharing.walks kind = true → fullCopy.walks kind = true := by
  intro kind; cases kind <;> simp [sharing, fullCopy, Kind.isSlots]

theorem sharing_walks_rewritingArgs :
    ∀ kind, sharing.walks kind = true → rewritingArgs.walks kind = true := by
  intro kind; cases kind <;> simp [sharing, rewritingArgs, Kind.isSlots]

theorem isSlots_argsOrSlots : ∀ kind, Kind.isSlots kind = true → argsOrSlots kind = true := by
  intro kind; cases kind <;> simp [argsOrSlots, Kind.isSlots]

/-- Where the full-copy collection puts what the sharing one leaves in place: an old object the
full copy copies again goes to its copy; everything else keeps its address. -/
def fullCopyOf (R : Val → Bool) (s : State Label) (b : Addr) : Addr :=
  if b.gen = .old ∧ b.index < s.old.length then promote fullCopy R s b else b

/-- The sharing minor collection and the full-copy one agree up to renaming: the full copy's
result is the image of the sharing one's under `fullCopyOf`, with every cell where it was. -/
theorem sharing_fullCopy (traced : Traced fullCopy s R) (generational : Generational s)
    (typed : Typed s) (present : NoDangling s) :
    Image (fullCopyOf R s) id (collect sharing R s) (collect fullCopy R s) := by
  refine Image.across
    (collectWith_image sharing_sound (traced.mono sharing_walks_fullCopy) generational typed
      present _)
    (collectWith_image (fullCopy_sound.narrow isSlots_argsOrSlots rfl) traced generational typed
      present _) ?_
  intro v reached
  cases v with
  | cell i => rfl
  | ref a =>
    obtain ⟨gen, n⟩ := a
    cases gen with
    | young =>
      simp only [mapVal, promote, fullCopyOf, Val.ref.injEq]
      rw [if_neg (by simp)]
    | old =>
      have lt : n < s.old.length := by
        have there := present _ reached
        simp only [State.Present, get_old] at there
        simpa using there
      have stays : keepOld sharing R s n = false := keepOld_of_copies_none (fun _ => rfl) n
      simp [mapVal, promote, stays, fullCopyOf, lt]

/-- Renaming old argument vectors in place changes nothing the sharing collection reaches: its
result and the rewriting one's are images of each other under the identity. -/
theorem sharing_rewritingArgs (traced : Traced rewritingArgs s R) (generational : Generational s)
    (typed : Typed s) (present : NoDangling s) :
    Image id id (collect sharing R s) (collect rewritingArgs R s) := by
  refine Image.across
    (collectWith_image sharing_sound (traced.mono sharing_walks_rewritingArgs) generational typed
      present _)
    (collectWith_image (rewritingArgs_sound.narrow isSlots_argsOrSlots rfl) traced generational
      typed present _) ?_
  intro v _
  have same : ∀ a, promote sharing R s a = promote rewritingArgs R s a := by
    intro a
    obtain ⟨gen, n⟩ := a
    cases gen with
    | young => rfl
    | old =>
      simp [promote, keepOld_of_copies_none (policy := sharing) (fun _ => rfl),
        keepOld_of_copies_none (policy := rewritingArgs) (fun _ => rfl)]
  cases v with
  | cell i => rfl
  | ref a => simp [mapVal, same]

end Policies

/-! ## Restores after a minor collection -/

section Restores

theorem drop_filter_map {α β : Type} (xs : List α) (p : α → Bool) (f : α → β) (n : Nat) :
    ((xs.filter p).map f).drop ((xs.take n).countP p) = ((xs.drop n).filter p).map f := by
  calc ((xs.filter p).map f).drop ((xs.take n).countP p)
      = (((xs.take n).filter p).map f ++ ((xs.drop n).filter p).map f).drop
          ((xs.take n).countP p) := by
        rw [← List.map_append, ← List.filter_append, List.take_append_drop]
    _ = ((xs.drop n).filter p).map f :=
        List.drop_left' (by rw [List.length_map, List.countP_eq_length_filter])

theorem clearSlots_map (f : Val → Val) {es es' : List (Addr × Nat)} {a b : Addr} (o : Obj Label)
    (same : ∀ j, (a, j) ∈ es ↔ (b, j) ∈ es') :
    (clearSlots es a o).map f = clearSlots es' b (o.map f) := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [clearSlots, Obj.map, Obj.mk.injEq, true_and]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_map, List.getElem?_mapIdx]
  cases fields[j]? with
  | none => rfl
  | some field =>
    simp only [Option.map_some]
    by_cases member : (a, j) ∈ es
    · rw [if_pos member, if_pos ((same j).mp member)]; rfl
    · rw [if_neg member, if_neg (fun other => member ((same j).mpr other))]

variable {policy : Policy} {exempt : Kind → Bool} {R : Val → Bool} {s : State Label}

/-- A collection's renaming is injective on the objects the state holds, where the region's are
the reached ones. -/
theorem promote_inj {a b : Addr} (thereA : (s.get a).isSome) (thereB : (s.get b).isSome)
    (keptA : a.gen = .young → R (.ref a) = true) (keptB : b.gen = .young → R (.ref b) = true)
    (same : promote policy R s a = promote policy R s b) : a = b := by
  obtain ⟨genA, n⟩ := a
  obtain ⟨genB, m⟩ := b
  have youngBelow : ∀ k, k < s.young.length → R (.ref ⟨.young, k⟩) = true →
      countFrom (keepYoung R) 0 k < youngCopies R s := fun k lt kept =>
    countFrom_lt _ 0 lt (by simpa [keepYoung] using kept)
  cases genA <;> cases genB
  · simp only [promote, Addr.mk.injEq, true_and, Nat.add_left_cancel_iff] at same
    rw [countFrom_inj (keepYoung R) 0 (by simpa [keepYoung] using keptA rfl)
      (by simpa [keepYoung] using keptB rfl) same]
  · exfalso
    have ltA : n < s.young.length := by simpa using thereA
    have ltB : m < s.old.length := by simpa using thereB
    have below := youngBelow n ltA (keptA rfl)
    simp only [promote] at same
    split at same
    · simp only [Addr.mk.injEq, true_and] at same; omega
    · simp only [Addr.mk.injEq, true_and] at same; omega
  · exfalso
    have ltA : n < s.old.length := by simpa using thereA
    have ltB : m < s.young.length := by simpa using thereB
    have below := youngBelow m ltB (keptB rfl)
    simp only [promote] at same
    split at same
    · simp only [Addr.mk.injEq, true_and] at same; omega
    · simp only [Addr.mk.injEq, true_and] at same; omega
  · have ltA : n < s.old.length := by simpa using thereA
    have ltB : m < s.old.length := by simpa using thereB
    simp only [promote] at same
    by_cases keptN : keepOld policy R s n = true <;> by_cases keptM : keepOld policy R s m = true
    · rw [if_pos keptN, if_pos keptM] at same
      simp only [Addr.mk.injEq, true_and, Nat.add_left_cancel_iff] at same
      rw [countFrom_inj _ 0 (by simpa using keptN) (by simpa using keptM) same]
    · rw [if_pos keptN, if_neg keptM] at same
      simp only [Addr.mk.injEq, true_and] at same; omega
    · rw [if_neg keptN, if_pos keptM] at same
      simp only [Addr.mk.injEq, true_and] at same; omega
    · rw [if_neg keptN, if_neg keptM] at same
      exact same

/-- Restoring a frame after a minor collection gives the image of restoring it before: the store
trail keeps each reached vector's entries, renamed, the trail each reached cell's, and the
frame's marks count what was kept below them.  A frame's region mark is the empty region's,
which every object the restored state reaches lies below, since the collection moved it into the
old generation. -/
theorem collect_restoreTo (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (storesSlots : ∀ e ∈ s.stores, ∃ o birth, s.get e.1 = some o ∧ o.kind = .slots birth)
    {frame : Frame} {frames : List Frame} (live : frame ∈ s.frames)
    (fewer : ∀ other ∈ frames, other ∈ s.frames)
    (restorable : NoDangling { s.restoreTo frame with frames := frames }) :
    Image (promote policy R s) (renumber R) { s.restoreTo frame with frames := frames }
      { (collect policy R s).restoreTo (collectFrame policy R s (keepStore R) frame) with
        frames := frames.map (collectFrame policy R s (keepStore R)) } := by
  have image := collectWith_image sound traced generational typed present (keepStore R)
  have visitedYoung : ∀ a, Reach s (.ref a) → a.gen = .young → R (.ref a) = true := by
    intro a reached young
    rcases reach_traced sound traced generational typed _ reached with inR | ⟨a', p, eq, old, _⟩
    · exact inR
    · cases eq; rw [young] at old; cases old
  refine ⟨?_, ?_, image.call, rfl, ?_⟩
  · intro a reached
    have reachedS := reach_restoreTo live fewer _ reached
    have there := restorable _ reached
    change ((s.restoreTo frame).get a).isSome at there
    change ((collect policy R s).restoreTo (collectFrame policy R s (keepStore R) frame)).get
        (promote policy R s a) = ((s.restoreTo frame).get a).map _
    rw [get_restoreTo, get_restoreTo, if_neg (by simp [promote_old])]
    rw [get_restoreTo] at there
    split at there
    · simp at there
    · rename_i notCut
      rw [if_neg notCut]
      change ((collectWith policy R s (keepStore R)).get (promote policy R s a)).map _ = _
      rw [image.obj a reachedS]
      cases found : s.get a with
      | none => simp [found] at there
      | some o =>
        simp only [Option.map_some]
        refine congrArg some (clearSlots_map _ o fun j => ?_).symm
        have esT : (collect policy R s).stores.drop
            (collectFrame policy R s (keepStore R) frame).storeMark =
            ((s.stores.drop frame.storeMark).filter (keepStore R)).map
              fun e => (promote policy R s e.1, e.2) :=
          drop_filter_map _ _ _ _
        rw [esT]
        constructor
        · intro member
          refine List.mem_map.mpr ⟨(a, j), List.mem_filter.mpr ⟨member, ?_⟩, rfl⟩
          obtain ⟨p, birth, foundE, kind⟩ := storesSlots _ (List.mem_of_mem_drop member)
          rcases reach_traced sound traced generational typed _ reachedS with
            inR | ⟨a', q, eq, _, found', atom⟩
          · exact inR
          · cases eq
            rw [foundE] at found'
            cases found'
            rw [kind] at atom
            cases atom
        · intro member
          obtain ⟨e, memberE, eq⟩ := List.mem_map.mp member
          obtain ⟨memberE, keptE⟩ := List.mem_filter.mp memberE
          obtain ⟨p, birth, foundE, _⟩ := storesSlots _ (List.mem_of_mem_drop memberE)
          obtain ⟨e₁, e₂⟩ := e
          simp only [Prod.mk.injEq] at eq
          obtain ⟨sameAddr, rfl⟩ := eq
          have : e₁ = a :=
            promote_inj (by simp [foundE]) (by simp [found]) (fun _ => keptE)
              (visitedYoung a reachedS) sameAddr
          subst this
          exact memberE
  · intro i reached
    have reachedS := reach_restoreTo live fewer _ reached
    have inR := traced_cell sound traced generational typed reachedS
    have there : i < (s.restoreTo frame).cells.length := restorable _ reached
    have ltMark : i < frame.cellMark := by
      simp only [State.restoreTo, List.length_take, List.length_mapIdx] at there
      omega
    change ((collect policy R s).restoreTo (collectFrame policy R s (keepStore R) frame)).cells[
        renumber R i]? = (s.restoreTo frame).cells[i]?.map _
    have ltT : renumber R i < (collectFrame policy R s (keepStore R) frame).cellMark :=
      countFrom_lt (keepCell R) 0 ltMark (by simpa [keepCell] using inR)
    rw [cells_restoreTo, cells_restoreTo, if_pos ltMark, if_pos ltT]
    change ((collectWith policy R s (keepStore R)).cells[renumber R i]?).map _ = _
    rw [image.cell i reachedS]
    have trT : (collect policy R s).trail.drop
        (collectFrame policy R s (keepStore R) frame).trailMark =
        ((s.trail.drop frame.trailMark).filter (keepCell R)).map (renumber R) :=
      drop_filter_map _ _ _ _
    have unbound : renumber R i ∈ (collect policy R s).trail.drop
        (collectFrame policy R s (keepStore R) frame).trailMark ↔
        i ∈ s.trail.drop frame.trailMark := by
      rw [trT]
      constructor
      · intro member
        obtain ⟨i', member', same⟩ := List.mem_map.mp member
        obtain ⟨member', kept⟩ := List.mem_filter.mp member'
        rw [countFrom_inj (keepCell R) 0 (by simpa using kept) (by simpa [keepCell] using inR)
          same] at member'
        exact member'
      · intro member
        exact List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨member, by simpa [keepCell] using inR⟩, rfl⟩
    cases s.cells[i]? with
    | none => rfl
    | some binding =>
      simp only [Option.map_some]
      by_cases member : i ∈ s.trail.drop frame.trailMark
      · rw [if_pos (unbound.mpr member), if_pos member]; rfl
      · rw [if_neg (fun other => member (unbound.mp other)), if_neg member]
  · simp only [List.map_map]
    rfl

/-- Every state a frame restores is kept by a minor collection: restoring the frame at any depth
afterwards gives the image of restoring it before. -/
theorem collect_restoreAt (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (storesSlots : ∀ e ∈ s.stores, ∃ o birth, s.get e.1 = some o ∧ o.kind = .slots birth)
    (depth : Nat) (restorable : NoDangling (s.restoreAt depth)) :
    Image (promote policy R s) (renumber R) (s.restoreAt depth)
      ((collect policy R s).restoreAt depth) := by
  have frames : (collect policy R s).frames = s.frames.map (collectFrame policy R s (keepStore R)) :=
    rfl
  unfold State.restoreAt at restorable ⊢
  rw [frames, List.getElem?_map]
  cases found : s.frames[depth]? with
  | none => exact collectWith_image sound traced generational typed present (keepStore R)
  | some frame =>
    rw [found] at restorable
    simp only [Option.map_some]
    rw [← List.map_drop]
    exact collect_restoreTo sound traced generational typed present storesSlots
      (List.mem_of_getElem? found) (fun _ member => List.mem_of_mem_drop member) restorable

/-- A read from a reached value of any state a frame restores agrees after a minor collection. -/
theorem collect_restoreAt_read (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (present : NoDangling s)
    (storesSlots : ∀ e ∈ s.stores, ∃ o birth, s.get e.1 = some o ∧ o.kind = .slots birth)
    (depth : Nat) (restorable : NoDangling (s.restoreAt depth)) (n : Nat) (v : Val)
    (reached : Reach (s.restoreAt depth) v) :
    read ((collect policy R s).restoreAt depth) n (rename policy R s v) =
      readAs (renumber R) (s.restoreAt depth) n v :=
  (collect_restoreAt sound traced generational typed present storesSlots depth restorable).read_eq
    n v reached

end Restores

/-! ## States that hold the same -/

section Holds

variable {s t : State Label} {φ : Addr → Addr} {ρ : Nat → Nat}

/-- `t` holds what `s` reaches as `s` holds it: the same roots, the same object at every address
`s` reaches and the same binding at every cell it reaches. -/
structure Holds (s t : State Label) : Prop where
  call : t.call = s.call
  regs : t.regs = s.regs
  frames : t.frames.map Frame.vals = s.frames.map Frame.vals
  obj : ∀ a, Reach s (.ref a) → t.get a = s.get a
  cell : ∀ i, Reach s (.cell i) → t.cells[i]? = s.cells[i]?

theorem frameRoot_of_vals {s t : State Label} (frames : t.frames.map Frame.vals = s.frames.map Frame.vals)
    {v : Val} : (∃ frame ∈ t.frames, v ∈ frame.vals) → ∃ frame ∈ s.frames, v ∈ frame.vals := by
  rintro ⟨frame, member, inVals⟩
  have inMap : frame.vals ∈ s.frames.map Frame.vals := by
    rw [← frames]; exact List.mem_map_of_mem member
  obtain ⟨frame', member', eq⟩ := List.mem_map.mp inMap
  exact ⟨frame', member', eq ▸ inVals⟩

theorem Holds.root (holds : Holds s t) {v : Val} : t.Root v ↔ s.Root v := by
  simp only [State.Root, holds.call, holds.regs]
  constructor
  · rintro (call | regs | frame)
    · exact Or.inl call
    · exact Or.inr (Or.inl regs)
    · exact Or.inr (Or.inr (frameRoot_of_vals holds.frames frame))
  · rintro (call | regs | frame)
    · exact Or.inl call
    · exact Or.inr (Or.inl regs)
    · exact Or.inr (Or.inr (frameRoot_of_vals holds.frames.symm frame))

theorem Holds.reach (holds : Holds s t) : ∀ v, Reach t v ↔ Reach s v := by
  intro v
  constructor
  · intro reach
    induction reach with
    | root isRoot => exact Reach.root (holds.root.mp isRoot)
    | @field a o v _ found member ih =>
      rw [holds.obj a ih] at found
      exact Reach.field ih found member
    | @binding i v _ bound ih =>
      rw [holds.cell i ih] at bound
      exact Reach.binding ih bound
  · intro reach
    induction reach with
    | root isRoot => exact Reach.root (holds.root.mpr isRoot)
    | @field a o v reached found member ih =>
      exact Reach.field ih (by rw [holds.obj a reached]; exact found) member
    | @binding i v reached bound ih =>
      exact Reach.binding ih (by rw [holds.cell i reached]; exact bound)

theorem Holds.present (holds : Holds s t) {v : Val} (reached : Reach s v) :
    t.Present v ↔ s.Present v := by
  cases v with
  | ref a => simp only [State.Present, holds.obj a reached]
  | cell i =>
    show i < t.cells.length ↔ i < s.cells.length
    have iffT : i < t.cells.length ↔ t.cells[i]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]; omega
    have iffS : i < s.cells.length ↔ s.cells[i]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]; omega
    rw [iffT, iffS, holds.cell i reached]

theorem Holds.noDangling (holds : Holds s t) (present : NoDangling s) : NoDangling t :=
  fun v reached =>
    (holds.present ((holds.reach v).mp reached)).mpr (present v ((holds.reach v).mp reached))

theorem Holds.refl (s : State Label) : Holds s s :=
  ⟨rfl, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Holds.of_eq (eq : s = t) : Holds s t := eq ▸ Holds.refl s

/-- Changing an object a state does not reach changes nothing it holds. -/
theorem holds_of_unreached (a : Addr) (unreached : ¬ Reach s (.ref a)) (call : t.call = s.call)
    (regs : t.regs = s.regs) (frames : t.frames.map Frame.vals = s.frames.map Frame.vals)
    (obj : ∀ b, b ≠ a → t.get b = s.get b) (cells : t.cells = s.cells) : Holds s t where
  call := call
  regs := regs
  frames := frames
  obj b reached := obj b fun eq => unreached (eq ▸ reached)
  cell i _ := by rw [cells]

/-- The image of a reached value is reached. -/
theorem Image.reach_map (image : Image φ ρ s t) : ∀ v, Reach s v → Reach t (mapVal φ ρ v) := by
  intro v reach
  induction reach with
  | root isRoot =>
    apply Reach.root
    rcases isRoot with call | regs | ⟨frame, member, vals⟩
    · exact Or.inl (by rw [image.call]; exact List.mem_map_of_mem call)
    · exact Or.inr (Or.inl (by rw [image.regs]; exact List.mem_map_of_mem regs))
    · have inMap : frame.vals.map (mapVal φ ρ) ∈ t.frames.map Frame.vals := by
        rw [image.frames]
        exact List.mem_map_of_mem (f := fun frame => frame.vals.map (mapVal φ ρ)) member
      obtain ⟨frame', member', eq⟩ := List.mem_map.mp inMap
      exact Or.inr (Or.inr ⟨frame', member', by rw [eq]; exact List.mem_map_of_mem vals⟩)
  | @field a o v reached found member ih =>
    refine Reach.field ih (o := o.map (mapVal φ ρ)) ?_ ?_
    · show t.get (φ a) = _
      rw [image.obj a reached, found]; rfl
    · simp only [Obj.map_fields]
      exact List.mem_map_of_mem (f := Option.map (mapVal φ ρ)) member
  | @binding i v reached bound ih =>
    exact Reach.binding ih (by show t.cells[ρ i]? = _; rw [image.cell i reached, bound]; rfl)

/-- An image carries over to states holding the same. -/
theorem Image.holds (image : Image φ ρ s t) {s' t' : State Label} (holdsS : Holds s s')
    (holdsT : Holds t t') : Image φ ρ s' t' where
  obj a reached := by
    have reachedS := (holdsS.reach _).mp reached
    rw [holdsT.obj _ (image.reach_map _ reachedS), image.obj a reachedS, holdsS.obj a reachedS]
  cell i reached := by
    have reachedS := (holdsS.reach _).mp reached
    rw [holdsT.cell _ (image.reach_map _ reachedS), image.cell i reachedS,
      holdsS.cell i reachedS]
  call := by rw [holdsT.call, holdsS.call, image.call]
  regs := by rw [holdsT.regs, holdsS.regs, image.regs]
  frames := by
    have split : ∀ frames : List Frame,
        frames.map (fun frame => frame.vals.map (mapVal φ ρ)) =
          (frames.map Frame.vals).map (List.map (mapVal φ ρ)) := fun frames => by
      rw [List.map_map]; rfl
    rw [holdsT.frames, image.frames, split, split, holdsS.frames]

/-- An image under renamings that agree on what the state reaches. -/
theorem Image.congr {φ' : Addr → Addr} {ρ' : Nat → Nat} (image : Image φ ρ s t)
    (sameObj : ∀ a, Reach s (.ref a) → φ' a = φ a)
    (sameCell : ∀ i, Reach s (.cell i) → ρ' i = ρ i) : Image φ' ρ' s t := by
  have same : ∀ v, Reach s v → mapVal φ' ρ' v = mapVal φ ρ v := by
    intro v reached
    cases v with
    | cell i => simp [mapVal, sameCell i reached]
    | ref a => simp [mapVal, sameObj a reached]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a reached
    rw [sameObj a reached, image.obj a reached]
    cases found : s.get a with
    | none => rfl
    | some o =>
      simp only [Option.map_some]
      exact congrArg some (Obj.map_congr fun v member =>
        (same v (Reach.field reached found member)).symm)
  · intro i reached
    rw [sameCell i reached, image.cell i reached]
    cases found : s.cells[i]? with
    | none => rfl
    | some binding =>
      cases binding with
      | none => rfl
      | some v => simp [same v (Reach.binding reached found)]
  · rw [image.call]
    exact List.map_congr_left fun v member => (same v (Reach.root (Or.inl member))).symm
  · rw [image.regs]
    exact List.map_congr_left fun v member =>
      (same v (Reach.root (Or.inr (Or.inl member)))).symm
  · rw [image.frames]
    refine List.map_congr_left fun frame member => ?_
    exact List.map_congr_left fun v inVals =>
      (same v (Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩)))).symm

end Holds

/-! ## The algebra of restores -/

/-- A frame's marks lie below another's. -/
def Frame.Below (older newer : Frame) : Prop :=
  older.mark ≤ newer.mark ∧ older.cellMark ≤ newer.cellMark ∧
    older.trailMark ≤ newer.trailMark ∧ older.storeMark ≤ newer.storeMark

/-- A frame's marks lie below the state's lengths. -/
def State.Fits (s : State Label) (frame : Frame) : Prop :=
  frame.mark ≤ s.young.length ∧ frame.cellMark ≤ s.cells.length ∧
    frame.trailMark ≤ s.trail.length ∧ frame.storeMark ≤ s.stores.length

section RestoreAlgebra

variable (s : State Label)

theorem clearSlots_clearSlots (es₁ es₂ : List (Addr × Nat)) (a : Addr) (o : Obj Label) :
    clearSlots es₂ a (clearSlots es₁ a o) =
      { o with fields := o.fields.mapIdx fun j field =>
          if (a, j) ∈ es₁ ∨ (a, j) ∈ es₂ then none else field } := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [clearSlots, Obj.mk.injEq, true_and]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_mapIdx]
  cases fields[j]? with
  | none => rfl
  | some field =>
    simp only [Option.map_some, Option.some.injEq]
    by_cases first : (⟨kind, label, fields⟩ : Obj Label) = ⟨kind, label, fields⟩ <;>
      by_cases one : (a, j) ∈ es₁ <;> by_cases two : (a, j) ∈ es₂ <;> simp [one, two]

theorem clearSlots_nil (a : Addr) (o : Obj Label) : clearSlots [] a o = o := by
  obtain ⟨kind, label, fields⟩ := o
  simp only [clearSlots, List.not_mem_nil, if_false, Obj.mk.injEq, true_and]
  apply List.ext_getElem?
  intro j
  simp only [List.getElem?_mapIdx]
  cases fields[j]? <;> rfl

/-- What lies past an earlier mark is what lies between the marks and past the later one. -/
theorem mem_drop_split {α : Type} {l : List α} {m n : Nat} (le : m ≤ n) (x : α) :
    x ∈ l.drop m ↔ x ∈ (l.take n).drop m ∨ x ∈ l.drop n := by
  have split : l.drop m = (l.take n).drop m ++ (l.drop n).drop (m - (l.take n).length) := by
    conv_lhs => rw [← List.take_append_drop n l]
    exact List.drop_append
  rw [split, List.mem_append]
  rcases Nat.lt_or_ge n l.length with lt | ge
  · rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt lt), Nat.sub_eq_zero_of_le le,
      List.drop_zero]
  · rw [List.drop_eq_nil_of_le ge]
    simp

/-- Restoring a frame after restoring a newer one is restoring the older frame. -/
theorem restoreTo_restoreTo {older newer : Frame} (below : older.Below newer)
    (fits : s.Fits newer) : (s.restoreTo newer).restoreTo older = s.restoreTo older := by
  obtain ⟨m1, m2, m3, m4⟩ := below
  obtain ⟨f1, f2, f3, f4⟩ := fits
  have entries : ∀ x, x ∈ s.stores.drop newer.storeMark ∨
      x ∈ (s.stores.take newer.storeMark).drop older.storeMark ↔
      x ∈ s.stores.drop older.storeMark := fun x =>
    or_comm.trans (mem_drop_split (l := s.stores) m4 x).symm
  have unbound : ∀ i, i ∈ s.trail.drop newer.trailMark ∨
      i ∈ (s.trail.take newer.trailMark).drop older.trailMark ↔
      i ∈ s.trail.drop older.trailMark := fun i =>
    or_comm.trans (mem_drop_split (l := s.trail) m3 i).symm
  have clear : ∀ (a : Addr) (o : Obj Label),
      clearSlots ((s.stores.take newer.storeMark).drop older.storeMark) a
          (clearSlots (s.stores.drop newer.storeMark) a o) =
        clearSlots (s.stores.drop older.storeMark) a o := by
    intro a o
    rw [clearSlots_clearSlots]
    obtain ⟨kind, label, fields⟩ := o
    simp only [clearSlots, Obj.mk.injEq, true_and]
    apply List.ext_getElem?
    intro j
    simp only [List.getElem?_mapIdx, entries]
  refine State.ext ?_ ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
  · simp only [State.restoreTo]
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_take, List.getElem?_mapIdx]
    by_cases lt : n < older.mark
    · rw [if_pos lt, if_pos (Nat.lt_of_lt_of_le lt m1), if_pos lt, Option.map_map]
      cases s.young[n]? with
      | none => rfl
      | some o => exact congrArg some (clear _ o)
    · rw [if_neg lt, if_neg lt]
  · simp only [State.restoreTo]
    apply List.ext_getElem?
    intro m
    simp only [List.getElem?_mapIdx, Option.map_map]
    cases s.old[m]? with
    | none => rfl
    | some o => exact congrArg some (clear _ o)
  · simp only [State.restoreTo]
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_mapIdx]
    by_cases lt : i < older.cellMark
    · rw [if_pos lt, if_pos (Nat.lt_of_lt_of_le lt m2), if_pos lt, Option.map_map]
      cases s.cells[i]? with
      | none => rfl
      | some binding =>
        simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
        by_cases one : i ∈ s.trail.drop newer.trailMark
        · have : i ∈ s.trail.drop older.trailMark := (unbound i).mp (Or.inl one)
          simp [one, this]
        · by_cases two : i ∈ (s.trail.take newer.trailMark).drop older.trailMark
          · have : i ∈ s.trail.drop older.trailMark := (unbound i).mp (Or.inr two)
            simp [two, this]
          · have : i ∉ s.trail.drop older.trailMark := fun member =>
              ((unbound i).mpr member).elim one two
            simp [one, two, this]
    · rw [if_neg lt, if_neg lt]
  · simp only [State.restoreTo]; omega
  · simp only [State.restoreTo]; rw [List.take_take, Nat.min_eq_left m3]
  · simp only [State.restoreTo]; rw [List.take_take, Nat.min_eq_left m4]

/-- Restoring after a push restores what the push left. -/
theorem restoreTo_push (vals : List Val) (frame : Frame) :
    (s.push vals).restoreTo frame = { s.restoreTo frame with frames := (s.push vals).frames } :=
  rfl

/-- Restoring a frame pushed just now changes nothing but the running code's values. -/
theorem restoreTo_now (vals : List Val) :
    s.restoreTo ⟨vals, s.young.length, s.cells.length, s.trail.length, s.stores.length⟩ =
      { s with regs := vals, oldCells := min s.oldCells s.cells.length } := by
  refine State.ext ?_ ?_ ?_ rfl ?_ ?_ rfl rfl rfl
  · simp only [State.restoreTo, List.drop_length]
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_take, List.getElem?_mapIdx, clearSlots_nil]
    by_cases lt : n < s.young.length
    · rw [if_pos lt]; cases s.young[n]? <;> rfl
    · rw [if_neg lt, List.getElem?_eq_none (Nat.le_of_not_lt lt)]
  · simp only [State.restoreTo, List.drop_length]
    apply List.ext_getElem?
    intro m
    simp only [List.getElem?_mapIdx, clearSlots_nil]
    cases s.old[m]? <;> rfl
  · simp only [State.restoreTo, List.drop_length, List.not_mem_nil, if_false]
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_mapIdx]
    by_cases lt : i < s.cells.length
    · rw [if_pos lt]; cases s.cells[i]? <;> rfl
    · rw [if_neg lt, List.getElem?_eq_none (Nat.le_of_not_lt lt)]
  · simp [State.restoreTo]
  · simp [State.restoreTo]

/-- An allocation since a frame is undone by restoring it. -/
theorem restoreTo_alloc {frame : Frame} (fits : frame.mark ≤ s.young.length) (kind : Kind)
    (label : Label) (fields : List (Option Val)) :
    (s.alloc kind label fields).restoreTo frame = s.restoreTo frame := by
  refine State.ext ?_ rfl rfl rfl rfl rfl rfl rfl rfl
  simp only [State.restoreTo, State.alloc]
  rw [List.mapIdx_append, List.take_append_of_le_length (by simpa using fits)]

/-- A cell made since a frame is dropped by restoring it. -/
theorem restoreTo_newCell {frame : Frame} (fits : frame.cellMark ≤ s.cells.length) :
    s.newCell.restoreTo frame = s.restoreTo frame := by
  refine State.ext rfl rfl ?_ rfl rfl rfl rfl rfl rfl
  simp only [State.restoreTo, State.newCell]
  rw [List.mapIdx_append, List.take_append_of_le_length (by simpa using fits)]
  rfl

/-- A trailed bind is undone by restoring a frame it followed. -/
theorem restoreTo_bind_trailed {frame : Frame} {cell : Nat} {value : Val}
    (unbound : s.cells[cell]? = some none) (fits : frame.trailMark ≤ s.trail.length)
    (trailed : cell < s.newestCellMark) :
    (s.bind cell value).restoreTo frame = s.restoreTo frame := by
  refine State.ext rfl rfl ?_ rfl ?_ rfl rfl rfl rfl
  · simp only [State.restoreTo, State.bind, if_pos trailed]
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_mapIdx, List.getElem?_set]
    by_cases same : cell = i
    · subst same
      have lt : cell < s.cells.length := (List.getElem?_eq_some_iff.mp unbound).1
      have member : cell ∈ (s.trail ++ [cell]).drop frame.trailMark := by
        rw [List.drop_append_of_le_length fits]
        simp
      have cellNone : s.cells[cell]'lt = none := by
        rw [List.getElem?_eq_getElem lt] at unbound
        exact Option.some.inj unbound
      simp [lt, member, cellNone]
    · rw [if_neg same]
      have iff : i ∈ (s.trail ++ [cell]).drop frame.trailMark ↔
          i ∈ s.trail.drop frame.trailMark := by
        rw [List.drop_append_of_le_length fits, List.mem_append, List.mem_singleton]
        constructor
        · rintro (member | eq)
          · exact member
          · exact absurd eq.symm same
        · exact Or.inl
      cases s.cells[i]? with
      | none => rfl
      | some binding => simp only [Option.map_some, iff]
  · simp only [State.restoreTo, State.bind, if_pos trailed]
    exact List.take_append_of_le_length fits

/-- An untrailed bind binds a cell made since every live frame, which restoring any drops. -/
theorem restoreTo_bind_untrailed {frame : Frame} {cell : Nat} {value : Val}
    (untrailed : ¬ cell < s.newestCellMark) (above : frame.cellMark ≤ cell) :
    (s.bind cell value).restoreTo frame = s.restoreTo frame := by
  refine State.ext rfl rfl ?_ rfl ?_ rfl rfl rfl rfl
  · simp only [State.restoreTo, State.bind, if_neg untrailed]
    apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_mapIdx, List.getElem?_set]
    by_cases lt : i < frame.cellMark
    · rw [if_pos lt, if_pos lt, if_neg (by omega)]
    · rw [if_neg lt, if_neg lt]
  · simp only [State.restoreTo, State.bind, if_neg untrailed]

/-- A trailed store into an empty slot is undone by restoring a frame it followed. -/
theorem restoreTo_store_trailed {frame : Frame} {vector : Addr} {slot : Nat} {value : Val}
    {o : Obj Label} (found : s.get vector = some o) (empty : o.fields[slot]? = some none)
    (fits : frame.storeMark ≤ s.stores.length) (trailed : s.trailsStore vector = true) :
    (s.store vector slot value).restoreTo frame = s.restoreTo frame := by
  have entries : ∀ b j, (b, j) ∈ (s.stores ++ [(vector, slot)]).drop frame.storeMark ↔
      (b, j) ∈ s.stores.drop frame.storeMark ∨ (b = vector ∧ j = slot) := by
    intro b j
    rw [List.drop_append_of_le_length fits, List.mem_append, List.mem_singleton, Prod.mk.injEq]
  have cleared : ∀ b (p : Obj Label), s.get b = some p →
      clearSlots ((s.stores ++ [(vector, slot)]).drop frame.storeMark) b
          (if b = vector then { p with fields := p.fields.set slot (some value) } else p) =
        clearSlots (s.stores.drop frame.storeMark) b p := by
    intro b p foundB
    by_cases same : b = vector
    · subst same
      rw [found] at foundB
      cases foundB
      obtain ⟨kind, label, fields⟩ := o
      simp only [if_true, clearSlots, Obj.mk.injEq, true_and]
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_mapIdx, List.getElem?_set, entries]
      by_cases here : slot = j
      · subst here
        have lt : slot < fields.length := (List.getElem?_eq_some_iff.mp empty).1
        have slotNone : fields[slot]'lt = none := by
          have empty' : fields[slot]? = some none := empty
          rw [List.getElem?_eq_getElem lt] at empty'
          exact Option.some.inj empty'
        simp [lt, slotNone]
      · rw [if_neg here]
        have ne : ¬ j = slot := fun eq => here eq.symm
        cases fields[j]? with
        | none => rfl
        | some field => simp [ne]
    · obtain ⟨kind, label, fields⟩ := p
      simp only [if_neg same, clearSlots, Obj.mk.injEq, true_and]
      apply List.ext_getElem?
      intro j
      simp only [List.getElem?_mapIdx, entries, same, false_and, or_false]
  have getStore : ∀ b, (s.store vector slot value).get b =
      (s.get b).map fun p =>
        if b = vector then { p with fields := p.fields.set slot (some value) } else p := by
    intro b
    rw [get_store]
    by_cases same : b = vector
    · subst same; simp
    · simp [same]
  have stores : (s.store vector slot value).stores = s.stores ++ [(vector, slot)] := by
    rw [store_stores, if_pos trailed]
  have young : ((s.store vector slot value).restoreTo frame).young = (s.restoreTo frame).young := by
    simp only [State.restoreTo, stores]
    apply List.ext_getElem?
    intro n
    simp only [List.getElem?_take, List.getElem?_mapIdx]
    have lengths : (s.store vector slot value).young.length = s.young.length :=
      store_young_length s vector slot value
    split
    · have eqGet := getStore ⟨.young, n⟩
      simp only [get_young] at eqGet
      rw [eqGet]
      cases foundN : s.young[n]? with
      | none => rfl
      | some p => exact congrArg some (cleared ⟨.young, n⟩ p foundN)
    · rfl
  have old : ((s.store vector slot value).restoreTo frame).old = (s.restoreTo frame).old := by
    simp only [State.restoreTo, stores]
    apply List.ext_getElem?
    intro m
    simp only [List.getElem?_mapIdx]
    have eqGet := getStore ⟨.old, m⟩
    simp only [get_old] at eqGet
    rw [eqGet]
    cases foundM : s.old[m]? with
    | none => rfl
    | some p => exact congrArg some (cleared ⟨.old, m⟩ p foundM)
  refine State.ext young old ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp [State.restoreTo]
  · simp [State.restoreTo]
  · simp [State.restoreTo]
  · simp only [State.restoreTo, stores]
    exact List.take_append_of_le_length fits
  · simp [State.restoreTo]
  · simp [State.restoreTo]
  · simp [State.restoreTo]

/-- An untrailed store changes, after restoring a frame, only the vector it filled. -/
theorem restoreTo_store_untrailed {frame : Frame} {vector : Addr} {slot : Nat} {value : Val}
    (untrailed : s.trailsStore vector = false) (b : Addr) (other : b ≠ vector) :
    ((s.store vector slot value).restoreTo frame).get b = (s.restoreTo frame).get b := by
  rw [get_restoreTo, get_restoreTo, get_store, if_neg other]
  simp [untrailed]

theorem restoreTo_store_cells {frame : Frame} {vector : Addr} {slot : Nat} {value : Val} :
    ((s.store vector slot value).restoreTo frame).cells = (s.restoreTo frame).cells := by
  simp [State.restoreTo]

end RestoreAlgebra

/-! ## The frames' marks -/

/-- Frames mark what was there when they were pushed: an older frame's marks lie below a newer
one's, and every frame's below the lengths now. -/
structure Marked (s : State Label) : Prop where
  sorted : s.frames.Pairwise fun newer older => older.Below newer
  fits : ∀ frame ∈ s.frames, s.Fits frame

theorem Frame.Below.refl (frame : Frame) : frame.Below frame :=
  ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

section Marks

variable {s : State Label}

theorem Marked.below_newest {newest : Frame} {older : List Frame} (marked : Marked s)
    (frames : s.frames = newest :: older) : ∀ frame ∈ s.frames, frame.Below newest := by
  intro frame member
  rw [frames] at member
  rcases List.mem_cons.mp member with eq | member
  · rw [eq]; exact Frame.Below.refl _
  · have sorted := marked.sorted
    rw [frames, List.pairwise_cons] at sorted
    exact sorted.1 frame member

theorem State.restoreAt_eq {depth : Nat} {frame : Frame} (found : s.frames[depth]? = some frame) :
    s.restoreAt depth = { s.restoreTo frame with frames := s.frames.drop depth } := by
  unfold State.restoreAt
  rw [found]

theorem get_restoreAt {depth : Nat} {frame : Frame} (found : s.frames[depth]? = some frame)
    (a : Addr) : (s.restoreAt depth).get a = (s.restoreTo frame).get a := by
  rw [State.restoreAt_eq found]
  obtain ⟨gen, n⟩ := a
  cases gen <;> rfl

theorem cells_restoreAt {depth : Nat} {frame : Frame} (found : s.frames[depth]? = some frame) :
    (s.restoreAt depth).cells = (s.restoreTo frame).cells := by
  rw [State.restoreAt_eq found]

theorem restoreTo_lengths {frame : Frame} (fits : s.Fits frame) :
    (s.restoreTo frame).young.length = frame.mark ∧
      (s.restoreTo frame).cells.length = frame.cellMark ∧
      (s.restoreTo frame).trail.length = frame.trailMark ∧
      (s.restoreTo frame).stores.length = frame.storeMark := by
  obtain ⟨f1, f2, f3, f4⟩ := fits
  simp only [State.restoreTo, List.length_take, List.length_mapIdx]
  omega

theorem get_restoreTo_some {frame : Frame} {a : Addr} {o : Obj Label}
    (found : (s.restoreTo frame).get a = some o) :
    ∃ o₀, s.get a = some o₀ ∧ o.kind = o₀.kind ∧ (a.gen = .old ∨ a.index < frame.mark) := by
  rw [get_restoreTo] at found
  split at found
  · cases found
  · rename_i notCut
    obtain ⟨o₀, found₀, rfl⟩ := Option.map_eq_some_iff.mp found
    refine ⟨o₀, found₀, rfl, ?_⟩
    obtain ⟨gen, n⟩ := a
    cases gen with
    | old => exact Or.inl rfl
    | young => exact Or.inr (by simp at notCut; omega)

end Marks

/-! ## The frame discipline -/

/-- The frame discipline the trails keep: every state a frame restores dangles nowhere; the store
trail names slot vectors, those below a frame's store mark made before the frame; and an
activation's slot vector, which carries the number of frames live at its birth, is reached by no
state that restores one of those frames, nor while fewer frames than that are live. -/
structure Disciplined (s : State Label) : Prop where
  marked : Marked s
  present : NoDangling s
  restorable : ∀ depth frame, s.frames[depth]? = some frame → NoDangling (s.restoreAt depth)
  stores : ∀ e ∈ s.stores, ∃ o birth, s.get e.1 = some o ∧ o.kind = .slots birth
  storesBelow : ∀ frame ∈ s.frames, ∀ e ∈ s.stores.take frame.storeMark,
    e.1.gen = .old ∨ e.1.index < frame.mark
  births : ∀ a o birth depth, s.get a = some o → o.kind = .slots birth →
    depth < s.frames.length → s.frames.length ≤ depth + birth → ¬ Reach (s.restoreAt depth) (.ref a)
  born : ∀ a o birth, Reach s (.ref a) → s.get a = some o → o.kind = .slots birth →
    birth ≤ s.frames.length

section Discipline

variable {s : State Label}

theorem Disciplined.fits (disciplined : Disciplined s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) : s.Fits frame :=
  disciplined.marked.fits frame (List.mem_of_getElem? found)

theorem present_alloc {kind : Kind} {label : Label} {fields : List (Option Val)} {v : Val}
    (there : s.Present v) : (s.alloc kind label fields).Present v := by
  cases v with
  | cell i => exact there
  | ref a =>
    show ((s.alloc kind label fields).get a).isSome = true
    rw [get_alloc, if_neg]
    · exact there
    · rintro rfl
      simp [State.Present] at there

theorem Disciplined.alloc (disciplined : Disciplined s) {kind : Kind} {label : Label}
    {fields : List (Option Val)} (named : ∀ v, some v ∈ fields → Reach s v)
    (birth : ∀ b, kind = .slots b → b = s.frames.length) :
    Disciplined (s.alloc kind label fields) := by
  have fresh : ∀ a, (s.get a).isSome → a ≠ ⟨.young, s.young.length⟩ := by
    rintro a there rfl
    simp at there
  have restoreAt : ∀ depth frame, s.frames[depth]? = some frame →
      (s.alloc kind label fields).restoreAt depth = s.restoreAt depth := by
    intro depth frame found
    rw [State.restoreAt_eq (s := s.alloc kind label fields) found, State.restoreAt_eq found,
      restoreTo_alloc s (disciplined.fits found).1]
    rfl
  have getOld : ∀ a o, s.get a = some o → (s.alloc kind label fields).get a = some o := by
    intro a o found
    rw [get_alloc, if_neg (fresh a (by simp [found]))]
    exact found
  have getNew : ∀ a o, (s.alloc kind label fields).get a = some o →
      (a = ⟨.young, s.young.length⟩ ∧ o = ⟨kind, label, fields⟩) ∨ s.get a = some o := by
    intro a o found
    rw [get_alloc] at found
    split at found
    · cases found; exact Or.inl ⟨‹_›, rfl⟩
    · exact Or.inr found
  refine ⟨⟨disciplined.marked.sorted, fun frame member => ?_⟩, ?_, ?_, ?_,
    disciplined.storesBelow, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4⟩ := disciplined.marked.fits frame member
    exact ⟨by simp [State.alloc]; omega, f2, f3, f4⟩
  · intro v reached
    rcases reach_alloc named v reached with reached | rfl
    · exact present_alloc (disciplined.present v reached)
    · show ((s.alloc kind label fields).get _).isSome = true
      rw [get_alloc, if_pos rfl]; rfl
  · intro depth frame found
    rw [restoreAt depth frame found]
    exact disciplined.restorable depth frame found
  · intro e member
    obtain ⟨o, b, found, kindOf⟩ := disciplined.stores e member
    exact ⟨o, b, getOld _ _ found, kindOf⟩
  · intro a o b depth found kindOf lt le
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    rw [restoreAt depth _ foundFrame]
    rcases getNew a o found with ⟨rfl, rfl⟩ | found
    · intro reached
      have there := disciplined.restorable depth _ foundFrame _ reached
      have none : (s.restoreAt depth).get ⟨.young, s.young.length⟩ = none := by
        rw [get_restoreAt foundFrame, get_restoreTo, if_pos ⟨rfl, (disciplined.fits foundFrame).1⟩]
      simp [State.Present, none] at there
    · exact disciplined.births a o b depth found kindOf lt le
  · intro a o b reached found kindOf
    rcases reach_alloc named _ reached with reached | eq
    · rcases getNew a o found with ⟨rfl, _⟩ | found
      · exact absurd (disciplined.present _ reached) (by simp [State.Present])
      · exact disciplined.born a o b reached found kindOf
    · cases eq
      rw [get_alloc, if_pos rfl] at found
      cases found
      exact Nat.le_of_eq (birth b kindOf)

/-- A state with the same heap whose roots another state reaches reaches nothing new. -/
theorem reach_of_same_heap {t : State Label} (get : ∀ a, t.get a = s.get a)
    (cells : t.cells = s.cells) (roots : ∀ v, t.Root v → Reach s v) :
    ∀ v, Reach t v → Reach s v :=
  Reach.closed _ roots (fun a _ _ reached found member => Reach.field reached (get a ▸ found) member)
    (fun _ _ reached bound => Reach.binding reached (cells ▸ bound))

theorem Disciplined.newCell (disciplined : Disciplined s) : Disciplined s.newCell := by
  have restoreAt : ∀ depth frame, s.frames[depth]? = some frame →
      s.newCell.restoreAt depth = s.restoreAt depth := by
    intro depth frame found
    rw [State.restoreAt_eq (s := s.newCell) found, State.restoreAt_eq found,
      restoreTo_newCell s (disciplined.fits found).2.1]
    rfl
  refine ⟨⟨disciplined.marked.sorted, fun frame member => ?_⟩, ?_, ?_,
    fun e member => disciplined.stores e member, disciplined.storesBelow, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4⟩ := disciplined.marked.fits frame member
    exact ⟨f1, by simp [State.newCell]; omega, f3, f4⟩
  · intro v reached
    rcases reach_newCell v reached with reached | rfl
    · have there := disciplined.present v reached
      cases v with
      | ref a => exact there
      | cell i =>
        show i < (s.cells ++ [none]).length
        have : i < s.cells.length := there
        simp; omega
    · show s.cells.length < (s.cells ++ [none]).length
      simp
  · intro depth frame found
    rw [restoreAt depth frame found]
    exact disciplined.restorable depth frame found
  · intro a o b depth found kindOf lt le
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    rw [restoreAt depth _ foundFrame]
    exact disciplined.births a o b depth found kindOf lt le
  · intro a o b reached found kindOf
    rcases reach_newCell _ reached with reached | eq
    · exact disciplined.born a o b reached found kindOf
    · cases eq

theorem Disciplined.store (disciplined : Disciplined s) {vector : Addr} {slot : Nat}
    {value : Val} {o : Obj Label} {birth : Nat} (named : Reach s value)
    (found : s.get vector = some o) (isVector : o.kind = .slots birth)
    (empty : o.fields[slot]? = some none) : Disciplined (s.store vector slot value) := by
  have kinds : ∀ b p, (s.store vector slot value).get b = some p →
      ∃ p₀, s.get b = some p₀ ∧ p.kind = p₀.kind := by
    intro b p foundB
    rw [get_store] at foundB
    split at foundB
    · rename_i eq
      subst eq
      obtain ⟨p₀, found₀, rfl⟩ := Option.map_eq_some_iff.mp foundB
      exact ⟨p₀, found₀, rfl⟩
    · exact ⟨p, foundB, rfl⟩
  have exists' : ∀ b, ((s.store vector slot value).get b).isSome = (s.get b).isSome := by
    intro b
    rw [get_store]
    split
    · rename_i eq; subst eq; cases s.get b <;> rfl
    · rfl
  have holdsAt : ∀ depth frame, s.frames[depth]? = some frame →
      Holds (s.restoreAt depth) ((s.store vector slot value).restoreAt depth) := by
    intro depth frame foundFrame
    cases trailed : s.trailsStore vector with
    | true =>
      apply Holds.of_eq
      rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using foundFrame),
        State.restoreAt_eq foundFrame,
        restoreTo_store_trailed s found empty (disciplined.fits foundFrame).2.2.2 trailed,
        store_frames]
    | false =>
      have untrailed : s.frames.length ≤ birth := by
        unfold State.trailsStore at trailed
        simp only [found, isVector] at trailed
        simpa using trailed
      have lt : depth < s.frames.length := (List.getElem?_eq_some_iff.mp foundFrame).1
      refine holds_of_unreached vector
        (disciplined.births vector o birth depth found isVector lt (by omega)) ?_ ?_ ?_ ?_ ?_
      · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using foundFrame),
          State.restoreAt_eq foundFrame]
        show (s.store vector slot value).call = s.call
        exact store_call s vector slot value
      · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using foundFrame),
          State.restoreAt_eq foundFrame]
        rfl
      · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using foundFrame),
          State.restoreAt_eq foundFrame]
        show ((s.store vector slot value).frames.drop depth).map Frame.vals =
          (s.frames.drop depth).map Frame.vals
        rw [store_frames]
      · intro b other
        rw [get_restoreAt (s := s.store vector slot value) (by simpa using foundFrame),
          get_restoreAt foundFrame, restoreTo_store_untrailed s trailed b other]
      · rw [cells_restoreAt (s := s.store vector slot value) (by simpa using foundFrame),
          cells_restoreAt foundFrame, restoreTo_store_cells]
  refine ⟨⟨by simpa using disciplined.marked.sorted, fun frame member => ?_⟩, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [store_frames] at member
    obtain ⟨f1, f2, f3, f4⟩ := disciplined.marked.fits frame member
    refine ⟨by rw [store_young_length]; exact f1, by rw [store_cells]; exact f2,
      by rw [store_trail]; exact f3, ?_⟩
    rw [store_stores]
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · exact f4
  · intro v reached
    have reached' := reach_store named v reached
    have there := disciplined.present v reached'
    cases v with
    | ref a => show ((s.store vector slot value).get a).isSome = true; rw [exists']; exact there
    | cell i => show i < (s.store vector slot value).cells.length; rw [store_cells]; exact there
  · intro depth frame foundFrame
    rw [store_frames] at foundFrame
    exact (holdsAt depth frame foundFrame).noDangling (disciplined.restorable depth frame foundFrame)
  · intro e member
    rw [store_stores] at member
    split at member
    · rcases List.mem_append.mp member with member | member
      · obtain ⟨p, b, foundE, kindOf⟩ := disciplined.stores e member
        have := exists' e.1
        rw [foundE] at this
        obtain ⟨p', foundE'⟩ := Option.isSome_iff_exists.mp (by simpa using this)
        obtain ⟨p₀, found₀, same⟩ := kinds _ _ foundE'
        rw [foundE] at found₀
        cases found₀
        exact ⟨p', b, foundE', same.trans kindOf⟩
      · rw [List.mem_singleton] at member
        subst member
        rw [get_store, if_pos rfl, found]
        exact ⟨_, birth, rfl, isVector⟩
    · obtain ⟨p, b, foundE, kindOf⟩ := disciplined.stores e member
      have := exists' e.1
      rw [foundE] at this
      obtain ⟨p', foundE'⟩ := Option.isSome_iff_exists.mp (by simpa using this)
      obtain ⟨p₀, found₀, same⟩ := kinds _ _ foundE'
      rw [foundE] at found₀
      cases found₀
      exact ⟨p', b, foundE', same.trans kindOf⟩
  · intro frame member e inTake
    rw [store_frames] at member
    rw [store_stores] at inTake
    have fits := (disciplined.marked.fits frame member).2.2.2
    split at inTake
    · rw [List.take_append_of_le_length fits] at inTake
      exact disciplined.storesBelow frame member e inTake
    · exact disciplined.storesBelow frame member e inTake
  · intro a p b depth foundA kindOf lt le
    rw [store_frames] at lt le
    obtain ⟨p₀, found₀, same⟩ := kinds a p foundA
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    intro reached
    have reached' := ((holdsAt depth _ foundFrame).reach _).mp reached
    exact disciplined.births a p₀ b depth found₀ (same ▸ kindOf) lt le reached'
  · intro a p b reached foundA kindOf
    rw [store_frames]
    obtain ⟨p₀, found₀, same⟩ := kinds a p foundA
    exact disciplined.born a p₀ b (reach_store named _ reached) found₀ (same ▸ kindOf)

theorem Disciplined.bind (disciplined : Disciplined s) {cell : Nat} {value : Val}
    (named : Reach s value) (unbound : s.cells[cell]? = some none) :
    Disciplined (s.bind cell value) := by
  have restoreAt : ∀ depth frame, s.frames[depth]? = some frame →
      (s.bind cell value).restoreAt depth = s.restoreAt depth := by
    intro depth frame found
    rw [State.restoreAt_eq (s := s.bind cell value) found, State.restoreAt_eq found]
    by_cases trailed : cell < s.newestCellMark
    · rw [restoreTo_bind_trailed s unbound (disciplined.fits found).2.2.1 trailed]; rfl
    · have below : frame.cellMark ≤ s.newestCellMark := by
        cases frames : s.frames with
        | nil => rw [frames] at found; simp at found
        | cons newest older =>
          have := disciplined.marked.below_newest frames frame (List.mem_of_getElem? found)
          simp only [State.newestCellMark, frames]
          exact this.2.1
      rw [restoreTo_bind_untrailed s trailed (by omega)]; rfl
  have lengths : (s.bind cell value).cells.length = s.cells.length := by simp [State.bind]
  refine ⟨⟨disciplined.marked.sorted, fun frame member => ?_⟩, ?_, ?_,
    fun e member => disciplined.stores e member, disciplined.storesBelow, ?_, ?_⟩
  · obtain ⟨f1, f2, f3, f4⟩ := disciplined.marked.fits frame member
    refine ⟨f1, by rw [lengths]; exact f2, ?_, f4⟩
    show frame.trailMark ≤ (if cell < s.newestCellMark then s.trail ++ [cell] else s.trail).length
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · exact f3
  · intro v reached
    have there := disciplined.present v (reach_bind named v reached)
    cases v with
    | ref a => exact there
    | cell i => show i < (s.bind cell value).cells.length; rw [lengths]; exact there
  · intro depth frame found
    rw [restoreAt depth frame found]
    exact disciplined.restorable depth frame found
  · intro a o b depth found kindOf lt le
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    rw [restoreAt depth _ foundFrame]
    exact disciplined.births a o b depth found kindOf lt le
  · intro a o b reached found kindOf
    exact disciplined.born a o b (reach_bind named _ reached) found kindOf

theorem Disciplined.push (disciplined : Disciplined s) {vals : List Val}
    (named : ∀ v ∈ vals, Reach s v) : Disciplined (s.push vals) := by
  have later : ∀ depth frame, s.frames[depth]? = some frame →
      (s.push vals).restoreAt (depth + 1) = s.restoreAt depth := by
    intro depth frame found
    rw [State.restoreAt_eq (s := s.push vals) (show (s.push vals).frames[depth + 1]? = some frame
      from found), State.restoreAt_eq found, restoreTo_push]
    rfl
  have eq : (s.push vals).restoreAt 0 =
      { s.push vals with regs := vals, oldCells := min s.oldCells s.cells.length } := by
    rw [State.restoreAt_eq (s := s.push vals) (show (s.push vals).frames[0]? =
      some ⟨vals, s.young.length, s.cells.length, s.trail.length, s.stores.length⟩ from rfl),
      restoreTo_push, restoreTo_now]
    rfl
  have now : ∀ v, Reach ((s.push vals).restoreAt 0) v → Reach s v := by
    rw [eq]
    refine reach_of_same_heap (fun a => ?_) rfl ?_
    · obtain ⟨gen, n⟩ := a; cases gen <;> rfl
    · intro v root
      rcases root with call | regs | ⟨frame, member, inVals⟩
      · exact Reach.root (Or.inl call)
      · exact named v regs
      · rcases List.mem_cons.mp member with eq | member
        · subst eq; exact named v inVals
        · exact Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩))
  refine ⟨⟨?_, fun frame member => ?_⟩, ?_, ?_, fun e member => disciplined.stores e member, ?_,
    ?_, ?_⟩
  · refine List.Pairwise.cons (fun older member => ?_) disciplined.marked.sorted
    obtain ⟨f1, f2, f3, f4⟩ := disciplined.marked.fits older member
    exact ⟨f1, f2, f3, f4⟩
  · rcases List.mem_cons.mp member with eq | member
    · subst eq; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
    · exact disciplined.marked.fits frame member
  · intro v reached
    exact disciplined.present v (reach_push named v reached)
  · intro depth frame found
    cases depth with
    | zero =>
      intro v reached
      have there := disciplined.present v (now v reached)
      have heap : ((s.push vals).restoreAt 0).Present v ↔ s.Present v := by
        rw [eq]
        cases v with
        | ref a => obtain ⟨gen, n⟩ := a; cases gen <;> rfl
        | cell i => rfl
      exact heap.mpr there
    | succ depth =>
      have found' : s.frames[depth]? = some frame := found
      rw [later depth frame found']
      exact disciplined.restorable depth frame found'
  · intro frame member e inTake
    rcases List.mem_cons.mp member with eq | member
    · subst eq
      change e ∈ s.stores.take s.stores.length at inTake
      rw [List.take_length] at inTake
      obtain ⟨p, b, foundE, _⟩ := disciplined.stores e inTake
      obtain ⟨⟨gen, n⟩, j⟩ := e
      cases gen with
      | old => exact Or.inl rfl
      | young =>
        right
        simp only [get_young] at foundE
        exact (List.getElem?_eq_some_iff.mp foundE).1
    · exact disciplined.storesBelow frame member e inTake
  · intro a o b depth found kindOf lt le
    cases depth with
    | zero =>
      intro reached
      have := disciplined.born a o b (now _ reached) found kindOf
      simp [State.push] at le
      omega
    | succ depth =>
      simp only [State.push, List.length_cons] at lt le
      have foundFrame : s.frames[depth]? = some s.frames[depth] :=
        List.getElem?_eq_getElem (by omega)
      rw [later depth _ foundFrame]
      exact disciplined.births a o b depth found kindOf (by omega) (by omega)
  · intro a o b reached found kindOf
    have := disciplined.born a o b (reach_push named _ reached) found kindOf
    simp [State.push]
    omega

/-- Restoring the newest frame and then another is restoring the other. -/
theorem restoreAt_restoreTo (disciplined : Disciplined s) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) :
    { s.restoreTo newest with frames := s.frames.drop depth }.restoreTo frame =
      { s.restoreTo frame with frames := s.frames.drop depth } := by
  have below := disciplined.marked.below_newest frames frame (List.mem_of_getElem? found)
  have fits := disciplined.marked.fits newest (by rw [frames]; exact List.mem_cons_self)
  have := restoreTo_restoreTo s below fits
  rw [← this]
  rfl

theorem stores_restoreTo (disciplined : Disciplined s) {frame : Frame} (live : frame ∈ s.frames) :
    ∀ e ∈ (s.restoreTo frame).stores, ∃ o birth, (s.restoreTo frame).get e.1 = some o ∧
      o.kind = .slots birth := by
  intro e member
  have inTake : e ∈ s.stores.take frame.storeMark := member
  obtain ⟨o, b, found, kindOf⟩ := disciplined.stores e (List.mem_of_mem_take inTake)
  refine ⟨clearSlots (s.stores.drop frame.storeMark) e.1 o, b, ?_, kindOf⟩
  rw [get_restoreTo, if_neg, found]
  · rfl
  · rintro ⟨young, above⟩
    rcases disciplined.storesBelow frame live e inTake with old | below
    · rw [young] at old; cases old
    · omega

theorem Disciplined.restore (disciplined : Disciplined s) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) : Disciplined s.restore := by
  have restoreEq : s.restore = s.restoreTo newest := by
    unfold State.restore; rw [frames]
  have atZero : s.restore = s.restoreAt 0 := by
    rw [restoreEq, State.restoreAt_eq (show s.frames[0]? = some newest by rw [frames]; rfl)]
    rfl
  have restoreAt : ∀ depth frame, s.frames[depth]? = some frame →
      s.restore.restoreAt depth = s.restoreAt depth := by
    intro depth frame found
    rw [restoreEq, State.restoreAt_eq (s := s.restoreTo newest) found, State.restoreAt_eq found]
    have := restoreAt_restoreTo disciplined frames found
    rw [← this]
    rfl
  have live : newest ∈ s.frames := by rw [frames]; exact List.mem_cons_self
  have fits := disciplined.marked.fits newest live
  obtain ⟨young, cells, trail, stores⟩ := restoreTo_lengths fits
  have framesEq : s.restore.frames = s.frames := by rw [restoreEq]; rfl
  refine ⟨⟨?_, fun frame member => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [framesEq]; exact disciplined.marked.sorted
  · rw [framesEq] at member
    have below := disciplined.marked.below_newest frames frame member
    rw [restoreEq]
    exact ⟨young ▸ below.1, cells ▸ below.2.1, trail ▸ below.2.2.1, stores ▸ below.2.2.2⟩
  · rw [atZero]
    exact disciplined.restorable 0 newest (by rw [frames]; rfl)
  · intro depth frame found
    rw [framesEq] at found
    rw [restoreAt depth frame found]
    exact disciplined.restorable depth frame found
  · rw [restoreEq]; exact stores_restoreTo disciplined live
  · intro frame member e inTake
    rw [framesEq] at member
    rw [restoreEq] at inTake
    have below := disciplined.marked.below_newest frames frame member
    change e ∈ (s.stores.take newest.storeMark).take frame.storeMark at inTake
    rw [List.take_take, Nat.min_eq_left below.2.2.2] at inTake
    exact disciplined.storesBelow frame member e inTake
  · intro a o b depth found kindOf lt le
    rw [framesEq] at lt le
    rw [restoreEq] at found
    obtain ⟨o₀, found₀, same, _⟩ := get_restoreTo_some found
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    rw [restoreAt depth _ foundFrame]
    exact disciplined.births a o₀ b depth found₀ (same ▸ kindOf) lt le
  · intro a o b reached found kindOf
    rw [framesEq]
    rw [restoreEq] at found
    obtain ⟨o₀, found₀, same, _⟩ := get_restoreTo_some found
    exact disciplined.born a o₀ b (reach_restore _ reached) found₀ (same ▸ kindOf)

theorem Disciplined.pop (disciplined : Disciplined s) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) : Disciplined s.pop := by
  have popEq : s.pop = { s.restoreTo newest with frames := older } := by
    unfold State.pop; rw [frames]
  have restoreAt : ∀ depth frame, older[depth]? = some frame →
      s.pop.restoreAt depth = s.restoreAt (depth + 1) := by
    intro depth frame found
    have found' : s.frames[depth + 1]? = some frame := by rw [frames]; exact found
    rw [popEq, State.restoreAt_eq (s := { s.restoreTo newest with frames := older }) found,
      State.restoreAt_eq found']
    have := restoreAt_restoreTo disciplined frames found'
    rw [← this]
    simp only [frames, List.drop_succ_cons]
    rfl
  have live : newest ∈ s.frames := by rw [frames]; exact List.mem_cons_self
  have fits := disciplined.marked.fits newest live
  obtain ⟨young, cells, trail, stores⟩ := restoreTo_lengths fits
  have inFrames : ∀ frame ∈ older, frame ∈ s.frames := fun frame member => by
    rw [frames]; exact List.mem_cons_of_mem _ member
  have toZero : ∀ v, Reach s.pop v → Reach (s.restoreAt 0) v := by
    rw [popEq, State.restoreAt_eq (show s.frames[0]? = some newest by rw [frames]; rfl)]
    refine reach_of_same_heap (fun a => ?_) rfl ?_
    · obtain ⟨gen, n⟩ := a; cases gen <;> rfl
    · intro v root
      rcases root with call | regs | ⟨frame, member, inVals⟩
      · exact Reach.root (Or.inl call)
      · exact Reach.root (Or.inr (Or.inl regs))
      · exact Reach.root (Or.inr (Or.inr ⟨frame, by simpa using inFrames frame member, inVals⟩))
  have framesEq : s.pop.frames = older := by rw [popEq]
  refine ⟨⟨?_, fun frame member => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [framesEq]
    have sorted := disciplined.marked.sorted
    rw [frames] at sorted
    exact sorted.of_cons
  · rw [framesEq] at member
    have below := disciplined.marked.below_newest frames frame (inFrames frame member)
    rw [popEq]
    exact ⟨young ▸ below.1, cells ▸ below.2.1, trail ▸ below.2.2.1, stores ▸ below.2.2.2⟩
  · intro v reached
    have there := disciplined.restorable 0 newest (by rw [frames]; rfl) v (toZero v reached)
    rw [State.restoreAt_eq (show s.frames[0]? = some newest by rw [frames]; rfl)] at there
    rw [popEq]
    cases v with
    | ref a => obtain ⟨gen, n⟩ := a; cases gen <;> exact there
    | cell i => exact there
  · intro depth frame found
    rw [framesEq] at found
    rw [restoreAt depth frame found]
    exact disciplined.restorable (depth + 1) frame (by rw [frames]; exact found)
  · rw [popEq]
    intro e member
    obtain ⟨o, b, found, kindOf⟩ := stores_restoreTo disciplined live e member
    exact ⟨o, b, by obtain ⟨⟨gen, n⟩, j⟩ := e; cases gen <;> exact found, kindOf⟩
  · intro frame member e inTake
    rw [framesEq] at member
    rw [popEq] at inTake
    have below := disciplined.marked.below_newest frames frame (inFrames frame member)
    change e ∈ (s.stores.take newest.storeMark).take frame.storeMark at inTake
    rw [List.take_take, Nat.min_eq_left below.2.2.2] at inTake
    exact disciplined.storesBelow frame (inFrames frame member) e inTake
  · intro a o b depth found kindOf lt le
    rw [framesEq] at lt le
    have foundPop : (s.restoreTo newest).get a = some o := by
      rw [popEq] at found; obtain ⟨gen, n⟩ := a; cases gen <;> exact found
    obtain ⟨o₀, found₀, same, _⟩ := get_restoreTo_some foundPop
    have foundFrame : older[depth]? = some older[depth] := List.getElem?_eq_getElem lt
    rw [restoreAt depth _ foundFrame]
    have lengths : s.frames.length = older.length + 1 := by rw [frames]; rfl
    exact disciplined.births a o₀ b (depth + 1) found₀ (same ▸ kindOf) (by omega) (by omega)
  · intro a o b reached found kindOf
    rw [framesEq]
    have foundPop : (s.restoreTo newest).get a = some o := by
      rw [popEq] at found; obtain ⟨gen, n⟩ := a; cases gen <;> exact found
    obtain ⟨o₀, found₀, same, _⟩ := get_restoreTo_some foundPop
    have lengths : s.frames.length = older.length + 1 := by rw [frames]; rfl
    have bound := disciplined.born a o₀ b (reach_pop _ reached) found₀ (same ▸ kindOf)
    by_contra over
    have atTop : b = s.frames.length := by omega
    exact disciplined.births a o₀ b 0 found₀ (same ▸ kindOf) (by omega) (by omega)
      (toZero _ reached)

/-- The frame discipline is kept by every step the running code can take. -/
theorem Disciplined.step (disciplined : Disciplined s) {step : Step Label}
    (enabled : step.Enabled s) : Disciplined (step.run s) := by
  cases enabled with
  | alloc notSlots named _ =>
    refine disciplined.alloc named fun b kind => ?_
    subst kind
    cases notSlots
  | activate named => exact disciplined.alloc named fun _ kind => by cases kind; rfl
  | newCell => exact disciplined.newCell
  | store _ named found isVector empty => exact disciplined.store named found isVector empty
  | bind _ named unbound => exact disciplined.bind named unbound
  | push named => exact disciplined.push named
  | pop frames => exact disciplined.pop frames
  | restore frames => exact disciplined.restore frames

/-- The allocation-order invariant is kept by every step the running code can take. -/
theorem Generational.step (generational : Generational s) (disciplined : Disciplined s)
    {step : Step Label} (enabled : step.Enabled s) : Generational (step.run s) := by
  cases enabled with
  | alloc _ named _ => exact generational.alloc named
  | activate named => exact generational.alloc named
  | newCell => exact generational.newCell
  | store _ named found isVector _ => exact generational.store named found isVector
  | bind _ named _ => exact generational.bind named
  | push named => exact generational.push named
  | @pop newest older frames =>
    have := (disciplined.pop frames).present
    show Generational s.pop
    unfold State.pop at this ⊢
    rw [frames] at this ⊢
    exact generational.restoreTo (by rw [frames]; exact List.mem_cons_self)
      (fun other member => by rw [frames]; exact List.mem_cons_of_mem _ member) this
  | @restore newest older frames =>
    have := (disciplined.restore frames).present
    show Generational s.restore
    unfold State.restore at this ⊢
    rw [frames] at this ⊢
    exact generational.restoreTo (frames := s.frames) (by rw [frames]; exact List.mem_cons_self)
      (fun _ => id) this

/-- Atoms and argument vectors keep naming atoms and cells. -/
theorem Typed.step (typed : Typed s) (disciplined : Disciplined s) {step : Step Label}
    (enabled : step.Enabled s) : Typed (step.run s) := by
  cases enabled with
  | alloc _ named atoms => exact typed.alloc named atoms
  | activate named =>
    exact typed.alloc named fun kind => by rcases kind with kind | kind <;> cases kind
  | newCell => exact typed.newCell
  | store _ named found isVector _ => exact typed.store named found isVector
  | bind _ named _ => exact typed.bind named
  | push named => exact typed.push named
  | @pop newest older frames =>
    have := (disciplined.pop frames).present
    show Typed s.pop
    unfold State.pop at this ⊢
    rw [frames] at this ⊢
    exact typed.restoreTo (by rw [frames]; exact List.mem_cons_self)
      (fun other member => by rw [frames]; exact List.mem_cons_of_mem _ member) this
  | @restore newest older frames =>
    have := (disciplined.restore frames).present
    show Typed s.restore
    unfold State.restore at this ⊢
    rw [frames] at this ⊢
    exact typed.restoreTo (frames := s.frames) (by rw [frames]; exact List.mem_cons_self)
      (fun _ => id) this

end Discipline

/-! ### A minor collection keeps the frame discipline -/

section CollectDiscipline

variable {policy : Policy} {exempt : Kind → Bool} {R : Val → Bool} {s : State Label}

theorem collectFrame_below {older newer : Frame} (below : older.Below newer) :
    (collectFrame policy R s (keepStore R) older).Below (collectFrame policy R s (keepStore R) newer) :=
  ⟨Nat.le_refl _, countFrom_mono _ 0 below.2.1,
    (List.take_sublist_take_left below.2.2.1).countP_le,
    (List.take_sublist_take_left below.2.2.2).countP_le⟩

theorem collectFrame_fits {frame : Frame} (fits : s.Fits frame) :
    (collect policy R s).Fits (collectFrame policy R s (keepStore R) frame) := by
  refine ⟨Nat.le_refl _, ?_, ?_, ?_⟩
  · show renumber R frame.cellMark ≤ (keepMap (keepCell R) _ 0 s.cells).length
    rw [length_keepMap]
    exact countFrom_mono _ 0 fits.2.1
  · show (s.trail.take frame.trailMark).countP (keepCell R) ≤
      ((s.trail.filter (keepCell R)).map (renumber R)).length
    rw [List.length_map, ← List.countP_eq_length_filter]
    exact (List.take_sublist _ _).countP_le
  · show (s.stores.take frame.storeMark).countP (keepStore R) ≤
      ((s.stores.filter (keepStore R)).map fun e => (promote policy R s e.1, e.2)).length
    rw [List.length_map, ← List.countP_eq_length_filter]
    exact (List.take_sublist _ _).countP_le

theorem collect_get_promote {a : Addr} {o : Obj Label} (found : s.get a = some o)
    (kept : a.gen = .young → R (.ref a) = true) :
    ∃ o', (collect policy R s).get (promote policy R s a) = some o' ∧ o'.kind = o.kind := by
  obtain ⟨gen, n⟩ := a
  cases gen with
  | young =>
    have lt : n < s.young.length := (List.getElem?_eq_some_iff.mp found).1
    refine ⟨o.map (rename policy R s), ?_, rfl⟩
    rw [show collect policy R s = collectWith policy R s (keepStore R) from rfl,
      collectWith_get_youngCopy policy R s _ lt (kept rfl)]
    simp only [get_young] at found
    rw [found]; rfl
  | old =>
    have lt : n < s.old.length := (List.getElem?_eq_some_iff.mp found).1
    simp only [get_old] at found
    cases keptOld : keepOld policy R s n with
    | true =>
      refine ⟨o.map (rename policy R s), ?_, rfl⟩
      rw [show collect policy R s = collectWith policy R s (keepStore R) from rfl,
        collectWith_get_oldCopy policy R s _ lt keptOld, found]
      rfl
    | false =>
      have stay : promote policy R s ⟨.old, n⟩ = ⟨.old, n⟩ := by simp [promote, keptOld]
      refine ⟨rewriteOld policy R s n o, ?_, ?_⟩
      · rw [stay, show collect policy R s = collectWith policy R s (keepStore R) from rfl,
          collectWith_get_inPlace policy R s _ lt, found]
        rfl
      · unfold rewriteOld; split <;> rfl

/-- A minor collection keeps the frame discipline: the restored states it keeps are images of
the ones before, the store trail it keeps names slot vectors in the old generation, and every
frame's region mark is the empty region's. -/
theorem collect_disciplined (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s) :
    Disciplined (collect policy R s) := by
  have image := collectWith_image sound traced generational typed disciplined.present (keepStore R)
  have framesEq : (collect policy R s).frames =
      s.frames.map (collectFrame policy R s (keepStore R)) := rfl
  have restoredImage : ∀ depth frame, s.frames[depth]? = some frame →
      Image (promote policy R s) (renumber R) (s.restoreAt depth)
        ((collect policy R s).restoreAt depth) := fun depth frame found =>
    collect_restoreAt sound traced generational typed disciplined.present disciplined.stores depth
      (disciplined.restorable depth frame found)
  refine ⟨⟨?_, fun frame' member => ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [framesEq]
    exact disciplined.marked.sorted.map _ fun newer older below => collectFrame_below below
  · rw [framesEq] at member
    obtain ⟨frame, memberS, rfl⟩ := List.mem_map.mp member
    exact collectFrame_fits (disciplined.marked.fits frame memberS)
  · exact image.noDangling disciplined.present
  · intro depth frame' found'
    rw [framesEq, List.getElem?_map] at found'
    obtain ⟨frame, found, _⟩ := Option.map_eq_some_iff.mp found'
    exact (restoredImage depth frame found).noDangling (disciplined.restorable depth frame found)
  · intro e' member
    obtain ⟨e, memberS, rfl⟩ := List.mem_map.mp member
    obtain ⟨memberS, keptE⟩ := List.mem_filter.mp memberS
    obtain ⟨o, b, found, kindOf⟩ := disciplined.stores e memberS
    obtain ⟨o', found', same⟩ := collect_get_promote (policy := policy) found (fun _ => keptE)
    exact ⟨o', b, found', same.trans kindOf⟩
  · intro frame' _ e' inTake
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take inTake)
    exact Or.inl (promote_old policy R s e.1)
  · intro b' o' β depth found' kindOf lt le reached
    rw [framesEq, List.length_map] at lt le
    have foundFrame : s.frames[depth]? = some s.frames[depth] := List.getElem?_eq_getElem lt
    obtain ⟨v, reachedS, eq⟩ := (restoredImage depth _ foundFrame).reach _ reached
    cases v with
    | cell i => cases eq
    | ref a =>
      cases eq
      have reachedA := reach_restoreAt depth _ reachedS
      rw [show collect policy R s = collectWith policy R s (keepStore R) from rfl,
        image.obj a reachedA] at found'
      obtain ⟨o, found, rfl⟩ := Option.map_eq_some_iff.mp found'
      exact disciplined.births a o β depth found kindOf lt le reachedS
  · intro b' o' β reached found' kindOf
    rw [framesEq, List.length_map]
    obtain ⟨v, reachedS, eq⟩ := image.reach _ reached
    cases v with
    | cell i => cases eq
    | ref a =>
      cases eq
      rw [show collect policy R s = collectWith policy R s (keepStore R) from rfl,
        image.obj a reachedS] at found'
      obtain ⟨o, found, rfl⟩ := Option.map_eq_some_iff.mp found'
      exact disciplined.born a o β reachedS found kindOf

/-- A minor collection, declined or not, keeps the frame discipline. -/
theorem minor_disciplined (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s) :
    Disciplined (minor policy R s) := by
  unfold minor
  split
  · exact disciplined
  · exact collect_disciplined sound traced generational typed disciplined

end CollectDiscipline

/-! ## Later runs -/

section RestoreSteps

variable {s : State Label}

theorem Marked.fitsAt (marked : Marked s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) : s.Fits frame :=
  marked.fits frame (List.mem_of_getElem? found)

theorem restoreAt_alloc (marked : Marked s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) (kind : Kind) (label : Label)
    (fields : List (Option Val)) :
    (s.alloc kind label fields).restoreAt depth = s.restoreAt depth := by
  rw [State.restoreAt_eq (s := s.alloc kind label fields) found, State.restoreAt_eq found,
    restoreTo_alloc s (marked.fitsAt found).1]
  rfl

theorem restoreAt_newCell (marked : Marked s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) : s.newCell.restoreAt depth = s.restoreAt depth := by
  rw [State.restoreAt_eq (s := s.newCell) found, State.restoreAt_eq found,
    restoreTo_newCell s (marked.fitsAt found).2.1]
  rfl

theorem restoreAt_store_trailed (marked : Marked s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) {vector : Addr} {slot : Nat} {value : Val}
    {o : Obj Label} (foundVector : s.get vector = some o) (empty : o.fields[slot]? = some none)
    (trailed : s.trailsStore vector = true) :
    (s.store vector slot value).restoreAt depth = s.restoreAt depth := by
  rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using found),
    State.restoreAt_eq found,
    restoreTo_store_trailed s foundVector empty (marked.fitsAt found).2.2.2 trailed, store_frames]

/-- After an untrailed store, a restored state holds what it held, the filled vector aside. -/
theorem restoreAt_store_holds {depth : Nat} {frame : Frame} (found : s.frames[depth]? = some frame)
    {vector : Addr} {slot : Nat} {value : Val} (untrailed : s.trailsStore vector = false)
    (unreached : ¬ Reach (s.restoreAt depth) (.ref vector)) :
    Holds (s.restoreAt depth) ((s.store vector slot value).restoreAt depth) := by
  refine holds_of_unreached vector unreached ?_ ?_ ?_ ?_ ?_
  · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using found),
      State.restoreAt_eq found]
    show (s.store vector slot value).call = s.call
    exact store_call s vector slot value
  · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using found),
      State.restoreAt_eq found]
    rfl
  · rw [State.restoreAt_eq (s := s.store vector slot value) (by simpa using found),
      State.restoreAt_eq found]
    show ((s.store vector slot value).frames.drop depth).map Frame.vals =
      (s.frames.drop depth).map Frame.vals
    rw [store_frames]
  · intro b other
    rw [get_restoreAt (s := s.store vector slot value) (by simpa using found),
      get_restoreAt found, restoreTo_store_untrailed s untrailed b other]
  · rw [cells_restoreAt (s := s.store vector slot value) (by simpa using found),
      cells_restoreAt found, restoreTo_store_cells]

theorem restoreAt_bind (marked : Marked s) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) {cell : Nat} {value : Val}
    (unbound : s.cells[cell]? = some none) :
    (s.bind cell value).restoreAt depth = s.restoreAt depth := by
  rw [State.restoreAt_eq (s := s.bind cell value) found, State.restoreAt_eq found]
  by_cases trailed : cell < s.newestCellMark
  · rw [restoreTo_bind_trailed s unbound (marked.fitsAt found).2.2.1 trailed]; rfl
  · have below : frame.cellMark ≤ s.newestCellMark := by
      cases frames : s.frames with
      | nil => rw [frames] at found; simp at found
      | cons newest older =>
        have := marked.below_newest frames frame (List.mem_of_getElem? found)
        simp only [State.newestCellMark, frames]
        exact this.2.1
    rw [restoreTo_bind_untrailed s trailed (by omega)]; rfl

theorem restoreAt_push_succ {depth : Nat} {frame : Frame} (found : s.frames[depth]? = some frame)
    (vals : List Val) : (s.push vals).restoreAt (depth + 1) = s.restoreAt depth := by
  rw [State.restoreAt_eq (s := s.push vals) (show (s.push vals).frames[depth + 1]? = some frame
    from found), State.restoreAt_eq found, restoreTo_push]
  rfl

theorem restoreAt_push_zero (vals : List Val) :
    (s.push vals).restoreAt 0 =
      { s.push vals with regs := vals, oldCells := min s.oldCells s.cells.length } := by
  rw [State.restoreAt_eq (s := s.push vals) (show (s.push vals).frames[0]? =
    some ⟨vals, s.young.length, s.cells.length, s.trail.length, s.stores.length⟩ from rfl),
    restoreTo_push, restoreTo_now]
  rfl

theorem restore_eq_restoreAt {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) : s.restore = s.restoreAt 0 := by
  unfold State.restore
  rw [frames, State.restoreAt_eq (show s.frames[0]? = some newest by rw [frames]; rfl)]
  rfl

theorem restoreAt_restore (marked : Marked s) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) : s.restore.restoreAt depth = s.restoreAt depth := by
  have restoreEq : s.restore = s.restoreTo newest := by unfold State.restore; rw [frames]
  have below := marked.below_newest frames frame (List.mem_of_getElem? found)
  have fits := marked.fits newest (by rw [frames]; exact List.mem_cons_self)
  rw [restoreEq, State.restoreAt_eq (s := s.restoreTo newest) found, State.restoreAt_eq found,
    ← restoreTo_restoreTo s below fits]
  rfl

theorem restoreAt_pop (marked : Marked s) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) {depth : Nat} {frame : Frame}
    (found : older[depth]? = some frame) : s.pop.restoreAt depth = s.restoreAt (depth + 1) := by
  have popEq : s.pop = { s.restoreTo newest with frames := older } := by
    unfold State.pop; rw [frames]
  have found' : s.frames[depth + 1]? = some frame := by rw [frames]; exact found
  have below := marked.below_newest frames frame (List.mem_of_getElem? found')
  have fits := marked.fits newest (by rw [frames]; exact List.mem_cons_self)
  rw [popEq, State.restoreAt_eq (s := { s.restoreTo newest with frames := older }) found,
    State.restoreAt_eq found', ← restoreTo_restoreTo s below fits]
  simp only [frames, List.drop_succ_cons]
  rfl

end RestoreSteps

/-- An image carries over to states with the same heaps and fewer roots. -/
theorem Image.reroot {φ : Addr → Addr} {ρ : Nat → Nat} {s t s₂ t₂ : State Label}
    (image : Image φ ρ s t) (getS : ∀ a, s₂.get a = s.get a) (cellsS : s₂.cells = s.cells)
    (getT : ∀ a, t₂.get a = t.get a) (cellsT : t₂.cells = t.cells)
    (roots : ∀ v, s₂.Root v → Reach s v) (call : t₂.call = s₂.call.map (mapVal φ ρ))
    (regs : t₂.regs = s₂.regs.map (mapVal φ ρ))
    (frames : t₂.frames.map Frame.vals = s₂.frames.map fun frame => frame.vals.map (mapVal φ ρ)) :
    Image φ ρ s₂ t₂ where
  obj a reached := by
    rw [getT, getS, image.obj a (reach_of_same_heap getS cellsS roots _ reached)]
  cell i reached := by
    rw [cellsT, cellsS, image.cell i (reach_of_same_heap getS cellsS roots _ reached)]
  call := call
  regs := regs
  frames := frames

/-- `t` corresponds to `s` under the renamings `φ` of objects and `ρ` of cells: `t` is the image
of what `s` reaches, as is each state a frame of `t` restores of the state the same frame of `s`
restores, and the renamings are injective on what `s` reaches. -/
structure Corr (φ : Addr → Addr) (ρ : Nat → Nat) (s t : State Label) : Prop where
  now : Image φ ρ s t
  restored : ∀ depth frame, s.frames[depth]? = some frame →
    Image φ ρ (s.restoreAt depth) (t.restoreAt depth)
  injObj : ∀ a b, Reach s (.ref a) → Reach s (.ref b) → φ a = φ b → a = b
  injCell : ∀ i j, Reach s (.cell i) → Reach s (.cell j) → ρ i = ρ j → i = j

section Corr

variable {φ : Addr → Addr} {ρ : Nat → Nat} {s t : State Label}

theorem Image.frames_length (image : Image φ ρ s t) : t.frames.length = s.frames.length := by
  have := congrArg List.length image.frames
  simpa using this

theorem Image.frame_some (image : Image φ ρ s t) {depth : Nat} {frame : Frame}
    (found : s.frames[depth]? = some frame) :
    ∃ frame', t.frames[depth]? = some frame' ∧ frame'.vals = frame.vals.map (mapVal φ ρ) := by
  have lt : depth < t.frames.length := by
    rw [image.frames_length]; exact (List.getElem?_eq_some_iff.mp found).1
  refine ⟨t.frames[depth], List.getElem?_eq_getElem lt, ?_⟩
  have := congrArg (·[depth]?) image.frames
  simp only [List.getElem?_map, List.getElem?_eq_getElem lt, found, Option.map_some,
    Option.some.injEq] at this
  exact this

theorem Image.present (image : Image φ ρ s t) (present : NoDangling s) {v : Val}
    (reached : Reach s v) : t.Present (mapVal φ ρ v) :=
  image.noDangling present _ (image.reach_map v reached)

end Corr

/-- A step with its arguments renamed. -/
def Step.rename (φ : Addr → Addr) (ρ : Nat → Nat) : Step Label → Step Label
  | .alloc kind label fields => .alloc kind label (fields.map (Option.map (mapVal φ ρ)))
  | .activate label initial => .activate label (initial.map (Option.map (mapVal φ ρ)))
  | .newCell => .newCell
  | .store vector slot value => .store (φ vector) slot (mapVal φ ρ value)
  | .bind cell value => .bind (ρ cell) (mapVal φ ρ value)
  | .push vals => .push (vals.map (mapVal φ ρ))
  | .pop => .pop
  | .restore => .restore

/-- The object renaming extended by the objects the next allocations make. -/
def extendObj (φ : Addr → Addr) (s t : State Label) (a : Addr) : Addr :=
  if a = ⟨.young, s.young.length⟩ then ⟨.young, t.young.length⟩ else φ a

/-- The cell renaming extended by the cells the next new cells make. -/
def extendCell (ρ : Nat → Nat) (s t : State Label) (i : Nat) : Nat :=
  if i = s.cells.length then t.cells.length else ρ i

/-- The object renaming after a step. -/
def Step.nextObj (φ : Addr → Addr) (s t : State Label) : Step Label → Addr → Addr
  | .alloc _ _ _ => extendObj φ s t
  | .activate _ _ => extendObj φ s t
  | _ => φ

/-- The cell renaming after a step. -/
def Step.nextCell (ρ : Nat → Nat) (s t : State Label) : Step Label → Nat → Nat
  | .newCell => extendCell ρ s t
  | _ => ρ

section CorrSteps

variable {φ : Addr → Addr} {ρ : Nat → Nat} {s t : State Label}

theorem get_push (vals : List Val) (a : Addr) : (s.push vals).get a = s.get a := by
  obtain ⟨gen, n⟩ := a; cases gen <;> rfl

theorem get_newCell (a : Addr) : s.newCell.get a = s.get a := by
  obtain ⟨gen, n⟩ := a; cases gen <;> rfl

theorem get_bind (cell : Nat) (value : Val) (a : Addr) : (s.bind cell value).get a = s.get a := by
  obtain ⟨gen, n⟩ := a; cases gen <;> rfl

theorem restore_frames : s.restore.frames = s.frames := by
  unfold State.restore; split <;> rfl

theorem pop_frames {newest : Frame} {older : List Frame} (frames : s.frames = newest :: older) :
    s.pop.frames = older := by
  unfold State.pop; rw [frames]

theorem Corr.frame_cons (corr : Corr φ ρ s t) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) :
    ∃ newest' older', t.frames = newest' :: older' ∧ newest'.vals = newest.vals.map (mapVal φ ρ) ∧
      older'.map Frame.vals = older.map fun frame => frame.vals.map (mapVal φ ρ) := by
  have eq := corr.now.frames
  rw [frames] at eq
  cases framesT : t.frames with
  | nil => rw [framesT] at eq; cases eq
  | cons newest' older' =>
    rw [framesT] at eq
    simp only [List.map_cons, List.cons.injEq] at eq
    exact ⟨newest', older', rfl, eq.1, eq.2⟩

theorem Corr.alloc (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {kind : Kind} {label : Label} {fields : List (Option Val)}
    (named : ∀ v, some v ∈ fields → Reach s v) :
    Corr (extendObj φ s t) ρ (s.alloc kind label fields)
      (t.alloc kind label (fields.map (Option.map (mapVal φ ρ)))) := by
  have freshS : ∀ a, Reach s (.ref a) → a ≠ ⟨.young, s.young.length⟩ := by
    rintro a reached rfl
    have := disciplinedS.present _ reached
    simp [State.Present] at this
  have freshT : ∀ a, Reach s (.ref a) → φ a ≠ ⟨.young, t.young.length⟩ := by
    intro a reached eq
    have := corr.now.present disciplinedS.present reached
    simp only [mapVal, State.Present, eq] at this
    simp at this
  have sameObj : ∀ a, Reach s (.ref a) → extendObj φ s t a = φ a := fun a reached => by
    simp [extendObj, freshS a reached]
  have same : ∀ v, Reach s v → mapVal (extendObj φ s t) ρ v = mapVal φ ρ v := by
    intro v reached
    cases v with
    | cell i => rfl
    | ref a => simp [mapVal, sameObj a reached]
  have fieldsSame : fields.map (Option.map (mapVal (extendObj φ s t) ρ)) =
      fields.map (Option.map (mapVal φ ρ)) := by
    refine List.map_congr_left fun field member => ?_
    cases field with
    | none => rfl
    | some v => simp [same v (named v member)]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a reached
    rcases reach_alloc named _ reached with reached | eqNew
    · rw [sameObj a reached, get_alloc, if_neg (freshT a reached), corr.now.obj a reached,
        get_alloc, if_neg (freshS a reached)]
      cases found : s.get a with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        exact congrArg some (Obj.map_congr fun v member =>
          (same v (Reach.field reached found member)).symm)
    · cases eqNew
      have moved : extendObj φ s t ⟨.young, s.young.length⟩ = ⟨.young, t.young.length⟩ := by
        simp [extendObj]
      rw [moved, get_alloc, if_pos rfl, get_alloc, if_pos rfl]
      simp only [Option.map_some, Obj.map, fieldsSame]
  · intro i reached
    rcases reach_alloc named _ reached with reached | eq
    · show t.cells[ρ i]? = s.cells[i]?.map (Option.map (mapVal (extendObj φ s t) ρ))
      rw [corr.now.cell i reached]
      cases found : s.cells[i]? with
      | none => rfl
      | some binding =>
        cases binding with
        | none => rfl
        | some v => simp [same v (Reach.binding reached found)]
    · cases eq
  · show t.call = s.call.map (mapVal (extendObj φ s t) ρ)
    rw [corr.now.call]
    exact List.map_congr_left fun v member => (same v (Reach.root (Or.inl member))).symm
  · show Val.ref ⟨.young, t.young.length⟩ :: t.regs =
      (Val.ref ⟨.young, s.young.length⟩ :: s.regs).map (mapVal (extendObj φ s t) ρ)
    rw [corr.now.regs, List.map_cons]
    simp only [mapVal, extendObj, if_true, List.cons.injEq, true_and]
    exact List.map_congr_left fun v member =>
      (same v (Reach.root (Or.inr (Or.inl member)))).symm
  · show t.frames.map Frame.vals =
      s.frames.map fun frame => frame.vals.map (mapVal (extendObj φ s t) ρ)
    rw [corr.now.frames]
    refine List.map_congr_left fun frame member => ?_
    exact List.map_congr_left fun v inVals =>
      (same v (Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩)))).symm
  · intro depth frame found
    obtain ⟨frame', found', _⟩ := corr.now.frame_some found
    rw [restoreAt_alloc disciplinedS.marked found, restoreAt_alloc disciplinedT.marked found']
    exact (corr.restored depth frame found).congr
      (fun a reached => sameObj a (reach_restoreAt depth _ reached)) (fun _ _ => rfl)
  · intro a b reachedA reachedB eq
    rcases reach_alloc named _ reachedA with reachedA | eqA <;>
      rcases reach_alloc named _ reachedB with reachedB | eqB
    · rw [sameObj a reachedA, sameObj b reachedB] at eq
      exact corr.injObj a b reachedA reachedB eq
    · cases eqB
      rw [sameObj a reachedA] at eq
      simp only [extendObj, if_true] at eq
      exact absurd eq (freshT a reachedA)
    · cases eqA
      rw [sameObj b reachedB] at eq
      simp only [extendObj, if_true] at eq
      exact absurd eq.symm (freshT b reachedB)
    · cases eqA; cases eqB; rfl
  · intro i j reachedI reachedJ eq
    rcases reach_alloc named _ reachedI with reachedI | eq' <;>
      rcases reach_alloc named _ reachedJ with reachedJ | eq''
    · exact corr.injCell i j reachedI reachedJ eq
    all_goals first | cases eq' | cases eq''

theorem Corr.newCell (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) : Corr φ (extendCell ρ s t) s.newCell t.newCell := by
  have freshS : ∀ i, Reach s (.cell i) → i ≠ s.cells.length := by
    intro i reached eq
    have : i < s.cells.length := disciplinedS.present _ reached
    omega
  have freshT : ∀ i, Reach s (.cell i) → ρ i ≠ t.cells.length := by
    intro i reached eq
    have : ρ i < t.cells.length := corr.now.present disciplinedS.present reached
    omega
  have sameCell : ∀ i, Reach s (.cell i) → extendCell ρ s t i = ρ i := fun i reached => by
    simp [extendCell, freshS i reached]
  have same : ∀ v, Reach s v → mapVal φ (extendCell ρ s t) v = mapVal φ ρ v := by
    intro v reached
    cases v with
    | cell i => simp [mapVal, sameCell i reached]
    | ref a => rfl
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro a reached
    rcases reach_newCell _ reached with reached | eq
    · rw [get_newCell, corr.now.obj a reached, get_newCell]
      cases found : s.get a with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        exact congrArg some (Obj.map_congr fun v member =>
          (same v (Reach.field reached found member)).symm)
    · cases eq
  · intro i reached
    rcases reach_newCell _ reached with reached | eq
    · have ltS : i < s.cells.length := disciplinedS.present _ reached
      have ltT : ρ i < t.cells.length := corr.now.present disciplinedS.present reached
      rw [sameCell i reached]
      show (t.cells ++ [none])[ρ i]? = (s.cells ++ [none])[i]?.map _
      rw [List.getElem?_append_left ltT, List.getElem?_append_left ltS, corr.now.cell i reached]
      cases found : s.cells[i]? with
      | none => rfl
      | some binding =>
        cases binding with
        | none => rfl
        | some v => simp [same v (Reach.binding reached found)]
    · cases eq
      simp only [extendCell, if_true]
      show (t.cells ++ [none])[t.cells.length]? = (s.cells ++ [none])[s.cells.length]?.map _
      simp
  · show t.call = s.call.map (mapVal φ (extendCell ρ s t))
    rw [corr.now.call]
    exact List.map_congr_left fun v member => (same v (Reach.root (Or.inl member))).symm
  · show Val.cell t.cells.length :: t.regs =
      (Val.cell s.cells.length :: s.regs).map (mapVal φ (extendCell ρ s t))
    rw [corr.now.regs, List.map_cons]
    simp only [mapVal, extendCell, if_true, List.cons.injEq, true_and]
    exact List.map_congr_left fun v member =>
      (same v (Reach.root (Or.inr (Or.inl member)))).symm
  · show t.frames.map Frame.vals =
      s.frames.map fun frame => frame.vals.map (mapVal φ (extendCell ρ s t))
    rw [corr.now.frames]
    refine List.map_congr_left fun frame member => ?_
    exact List.map_congr_left fun v inVals =>
      (same v (Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩)))).symm
  · intro depth frame found
    obtain ⟨frame', found', _⟩ := corr.now.frame_some found
    rw [restoreAt_newCell disciplinedS.marked found, restoreAt_newCell disciplinedT.marked found']
    exact (corr.restored depth frame found).congr (fun _ _ => rfl)
      (fun i reached => sameCell i (reach_restoreAt depth _ reached))
  · intro a b reachedA reachedB eq
    rcases reach_newCell _ reachedA with reachedA | eqA
    · rcases reach_newCell _ reachedB with reachedB | eqB
      · exact corr.injObj a b reachedA reachedB eq
      · cases eqB
    · cases eqA
  · intro i j reachedI reachedJ eq
    rcases reach_newCell _ reachedI with reachedI | eqI <;>
      rcases reach_newCell _ reachedJ with reachedJ | eqJ
    · rw [sameCell i reachedI, sameCell j reachedJ] at eq
      exact corr.injCell i j reachedI reachedJ eq
    · cases eqJ
      rw [sameCell i reachedI] at eq
      simp only [extendCell, if_true] at eq
      exact absurd eq (freshT i reachedI)
    · cases eqI
      rw [sameCell j reachedJ] at eq
      simp only [extendCell, if_true] at eq
      exact absurd eq.symm (freshT j reachedJ)
    · cases eqI; cases eqJ; rfl

theorem Corr.store (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {vector : Addr} {slot : Nat} {value : Val} {o : Obj Label}
    {birth : Nat} (reachedVector : Reach s (.ref vector)) (named : Reach s value)
    (found : s.get vector = some o) (isVector : o.kind = .slots birth)
    (empty : o.fields[slot]? = some none) :
    Corr φ ρ (s.store vector slot value) (t.store (φ vector) slot (mapVal φ ρ value)) := by
  have foundT : t.get (φ vector) = some (o.map (mapVal φ ρ)) := by
    rw [corr.now.obj vector reachedVector, found]; rfl
  have emptyT : (o.map (mapVal φ ρ)).fields[slot]? = some none := by simp [Obj.map, empty]
  have trailsSame : t.trailsStore (φ vector) = s.trailsStore vector := by
    unfold State.trailsStore
    rw [foundT, found]
    simp only [Obj.map_kind, isVector, corr.now.frames_length]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro b reached
    have reachedB := reach_store named _ reached
    rw [get_store, get_store]
    by_cases same : b = vector
    · subst same
      rw [if_pos rfl, if_pos rfl, foundT, found]
      simp [Obj.map]
    · rw [if_neg (fun eq => same (corr.injObj b vector reachedB reachedVector eq)), if_neg same]
      exact corr.now.obj b reachedB
  · intro i reached
    rw [store_cells, store_cells]
    exact corr.now.cell i (reach_store named _ reached)
  · rw [store_call, store_call]; exact corr.now.call
  · rw [store_regs, store_regs]; exact corr.now.regs
  · rw [store_frames, store_frames]; exact corr.now.frames
  · intro depth frame foundFrame
    rw [store_frames] at foundFrame
    obtain ⟨frame', foundFrame', _⟩ := corr.now.frame_some foundFrame
    cases trailed : s.trailsStore vector with
    | true =>
      rw [restoreAt_store_trailed disciplinedS.marked foundFrame found empty trailed,
        restoreAt_store_trailed disciplinedT.marked foundFrame' foundT emptyT
          (trailsSame.trans trailed)]
      exact corr.restored depth frame foundFrame
    | false =>
      have untrailed : s.frames.length ≤ birth := by
        unfold State.trailsStore at trailed
        simp only [found, isVector] at trailed
        simpa using trailed
      have lt : depth < s.frames.length := (List.getElem?_eq_some_iff.mp foundFrame).1
      have unreachedS : ¬ Reach (s.restoreAt depth) (.ref vector) :=
        disciplinedS.births vector o birth depth found isVector lt (by omega)
      have unreachedT : ¬ Reach (t.restoreAt depth) (.ref (φ vector)) := by
        intro reached
        obtain ⟨w, reachedW, eq⟩ := (corr.restored depth frame foundFrame).reach _ reached
        cases w with
        | cell i => cases eq
        | ref b =>
          simp only [mapVal, Val.ref.injEq] at eq
          have := corr.injObj vector b reachedVector (reach_restoreAt depth _ reachedW) eq
          subst this
          exact unreachedS reachedW
      exact (corr.restored depth frame foundFrame).holds
        (restoreAt_store_holds foundFrame trailed unreachedS)
        (restoreAt_store_holds foundFrame' (trailsSame.trans trailed) unreachedT)
  · intro a b reachedA reachedB eq
    exact corr.injObj a b (reach_store named _ reachedA) (reach_store named _ reachedB) eq
  · intro i j reachedI reachedJ eq
    exact corr.injCell i j (reach_store named _ reachedI) (reach_store named _ reachedJ) eq

theorem Corr.bind (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {cell : Nat} {value : Val} (reachedCell : Reach s (.cell cell))
    (named : Reach s value) (unbound : s.cells[cell]? = some none) :
    Corr φ ρ (s.bind cell value) (t.bind (ρ cell) (mapVal φ ρ value)) := by
  have unboundT : t.cells[ρ cell]? = some none := by
    rw [corr.now.cell cell reachedCell, unbound]; rfl
  have ltS : cell < s.cells.length := (List.getElem?_eq_some_iff.mp unbound).1
  have ltT : ρ cell < t.cells.length := (List.getElem?_eq_some_iff.mp unboundT).1
  refine ⟨⟨?_, ?_, corr.now.call, corr.now.regs, corr.now.frames⟩, ?_, ?_, ?_⟩
  · intro a reached
    rw [get_bind, get_bind]
    exact corr.now.obj a (reach_bind named _ reached)
  · intro j reached
    have reachedJ := reach_bind named _ reached
    show (t.cells.set (ρ cell) (some (mapVal φ ρ value)))[ρ j]? =
      (s.cells.set cell (some value))[j]?.map _
    rw [List.getElem?_set, List.getElem?_set]
    by_cases same : cell = j
    · subst same
      simp [ltS, ltT]
    · rw [if_neg (fun eq => same (corr.injCell cell j reachedCell reachedJ eq)), if_neg same]
      exact corr.now.cell j reachedJ
  · intro depth frame found
    obtain ⟨frame', found', _⟩ := corr.now.frame_some found
    rw [restoreAt_bind disciplinedS.marked found unbound,
      restoreAt_bind disciplinedT.marked found' unboundT]
    exact corr.restored depth frame found
  · intro a b reachedA reachedB eq
    exact corr.injObj a b (reach_bind named _ reachedA) (reach_bind named _ reachedB) eq
  · intro i j reachedI reachedJ eq
    exact corr.injCell i j (reach_bind named _ reachedI) (reach_bind named _ reachedJ) eq

theorem Corr.push (corr : Corr φ ρ s t) {vals : List Val} (named : ∀ v ∈ vals, Reach s v) :
    Corr φ ρ (s.push vals) (t.push (vals.map (mapVal φ ρ))) := by
  have roots : ∀ v, (s.push vals).Root v → Reach s v := by
    intro v root
    rcases root with call | regs | ⟨frame, member, inVals⟩
    · exact Reach.root (Or.inl call)
    · exact Reach.root (Or.inr (Or.inl regs))
    · rcases List.mem_cons.mp member with eq | member
      · subst eq; exact named v inVals
      · exact Reach.root (Or.inr (Or.inr ⟨frame, member, inVals⟩))
  have framesEq : (t.push (vals.map (mapVal φ ρ))).frames.map Frame.vals =
      (s.push vals).frames.map fun frame => frame.vals.map (mapVal φ ρ) := by
    show vals.map (mapVal φ ρ) :: t.frames.map Frame.vals =
      vals.map (mapVal φ ρ) :: s.frames.map fun frame => frame.vals.map (mapVal φ ρ)
    rw [corr.now.frames]
  refine ⟨corr.now.reroot (get_push vals) rfl (get_push _) rfl roots corr.now.call corr.now.regs
    framesEq, ?_, ?_, ?_⟩
  · intro depth frame found
    cases depth with
    | zero =>
      rw [restoreAt_push_zero, restoreAt_push_zero]
      refine corr.now.reroot (fun a => ?_) rfl (fun a => ?_) rfl ?_ corr.now.call rfl framesEq
      · obtain ⟨gen, n⟩ := a; cases gen <;> rfl
      · obtain ⟨gen, n⟩ := a; cases gen <;> rfl
      · intro v root
        rcases root with call | regs | frame
        · exact Reach.root (Or.inl call)
        · exact named v regs
        · exact roots v (Or.inr (Or.inr frame))
    | succ depth =>
      have foundS : s.frames[depth]? = some frame := found
      obtain ⟨frame', found', _⟩ := corr.now.frame_some foundS
      rw [restoreAt_push_succ foundS, restoreAt_push_succ found']
      exact corr.restored depth frame foundS
  · intro a b reachedA reachedB eq
    exact corr.injObj a b (reach_push named _ reachedA) (reach_push named _ reachedB) eq
  · intro i j reachedI reachedJ eq
    exact corr.injCell i j (reach_push named _ reachedI) (reach_push named _ reachedJ) eq

theorem Corr.restore (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) : Corr φ ρ s.restore t.restore := by
  obtain ⟨newest', older', framesT, _, _⟩ := corr.frame_cons frames
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [restore_eq_restoreAt frames, restore_eq_restoreAt framesT]
    exact corr.restored 0 newest (by rw [frames]; rfl)
  · intro depth frame found
    rw [restore_frames] at found
    obtain ⟨frame', found', _⟩ := corr.now.frame_some found
    rw [restoreAt_restore disciplinedS.marked frames found,
      restoreAt_restore disciplinedT.marked framesT found']
    exact corr.restored depth frame found
  · intro a b reachedA reachedB eq
    exact corr.injObj a b (reach_restore _ reachedA) (reach_restore _ reachedB) eq
  · intro i j reachedI reachedJ eq
    exact corr.injCell i j (reach_restore _ reachedI) (reach_restore _ reachedJ) eq

theorem Corr.pop (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {newest : Frame} {older : List Frame}
    (frames : s.frames = newest :: older) : Corr φ ρ s.pop t.pop := by
  obtain ⟨newest', older', framesT, newestVals, olderVals⟩ := corr.frame_cons frames
  have zeroS : s.frames[0]? = some newest := by rw [frames]; rfl
  have zeroT : t.frames[0]? = some newest' := by rw [framesT]; rfl
  have popS : s.pop = { s.restoreTo newest with frames := older } := by
    unfold State.pop; rw [frames]
  have popT : t.pop = { t.restoreTo newest' with frames := older' } := by
    unfold State.pop; rw [framesT]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (corr.restored 0 newest zeroS).reroot (fun a => ?_) ?_ (fun a => ?_) ?_ ?_ ?_ ?_ ?_
    · rw [popS, get_restoreAt zeroS]; obtain ⟨gen, n⟩ := a; cases gen <;> rfl
    · rw [popS, cells_restoreAt zeroS]
    · rw [popT, get_restoreAt zeroT]; obtain ⟨gen, n⟩ := a; cases gen <;> rfl
    · rw [popT, cells_restoreAt zeroT]
    · intro v root
      rw [popS] at root
      rw [State.restoreAt_eq zeroS]
      rcases root with call | regs | ⟨frame, member, inVals⟩
      · exact Reach.root (Or.inl call)
      · exact Reach.root (Or.inr (Or.inl regs))
      · refine Reach.root (Or.inr (Or.inr ⟨frame, ?_, inVals⟩))
        show frame ∈ s.frames.drop 0
        rw [frames]; exact List.mem_cons_of_mem _ member
    · rw [popS, popT]; exact corr.now.call
    · rw [popS, popT]; exact newestVals
    · rw [popS, popT]; exact olderVals
  · intro depth frame found
    rw [pop_frames frames] at found
    have foundS : s.frames[depth + 1]? = some frame := by rw [frames]; exact found
    obtain ⟨frame', found', _⟩ := corr.now.frame_some foundS
    have foundT : older'[depth]? = some frame' := by rw [framesT] at found'; exact found'
    rw [restoreAt_pop disciplinedS.marked frames found, restoreAt_pop disciplinedT.marked framesT foundT]
    exact corr.restored (depth + 1) frame foundS
  · intro a b reachedA reachedB eq
    exact corr.injObj a b (reach_pop _ reachedA) (reach_pop _ reachedB) eq
  · intro i j reachedI reachedJ eq
    exact corr.injCell i j (reach_pop _ reachedI) (reach_pop _ reachedJ) eq

/-- The mirrored step is one the corresponding state can take. -/
theorem Corr.enabled (corr : Corr φ ρ s t) {step : Step Label} (enabled : step.Enabled s) :
    (step.rename φ ρ).Enabled t := by
  have fieldsNamed : ∀ fields : List (Option Val), (∀ v, some v ∈ fields → Reach s v) →
      ∀ w, some w ∈ fields.map (Option.map (mapVal φ ρ)) → Reach t w := by
    intro fields named w member
    obtain ⟨field, member', eq⟩ := List.mem_map.mp member
    cases field with
    | none => cases eq
    | some v =>
      cases eq
      exact corr.now.reach_map v (named v member')
  cases enabled with
  | alloc notSlots named atoms =>
    refine Step.Enabled.alloc notSlots (fieldsNamed _ named) fun kind b' member => ?_
    obtain ⟨field, member', eq⟩ := List.mem_map.mp member
    cases field with
    | none => cases eq
    | some v =>
      cases v with
      | cell i => cases eq
      | ref b =>
        simp only [Option.map_some, mapVal, Option.some.injEq, Val.ref.injEq] at eq
        subst eq
        obtain ⟨p, found, atom⟩ := atoms kind b member'
        refine ⟨p.map (mapVal φ ρ), ?_, atom⟩
        rw [corr.now.obj b (named _ member'), found]; rfl
  | activate named => exact Step.Enabled.activate (fieldsNamed _ named)
  | newCell => exact Step.Enabled.newCell
  | @store vector slot value o birth reached named found isVector empty =>
    exact Step.Enabled.store (o := o.map (mapVal φ ρ)) (birth := birth)
      (corr.now.reach_map _ reached) (corr.now.reach_map _ named)
      (by rw [corr.now.obj _ reached, found]; rfl) (by simpa using isVector)
      (by simp [Obj.map, empty])
  | bind reached named unbound =>
    exact Step.Enabled.bind (corr.now.reach_map _ reached) (corr.now.reach_map _ named)
      (by rw [corr.now.cell _ reached, unbound]; rfl)
  | push named =>
    refine Step.Enabled.push fun w member => ?_
    obtain ⟨v, member', rfl⟩ := List.mem_map.mp member
    exact corr.now.reach_map v (named v member')
  | pop frames =>
    obtain ⟨newest', older', framesT, _⟩ := corr.frame_cons frames
    exact Step.Enabled.pop framesT
  | restore frames =>
    obtain ⟨newest', older', framesT, _⟩ := corr.frame_cons frames
    exact Step.Enabled.restore framesT

/-- The correspondence survives every step the running code can take, mirrored with renamed
arguments. -/
theorem Corr.step (corr : Corr φ ρ s t) (disciplinedS : Disciplined s)
    (disciplinedT : Disciplined t) {step : Step Label} (enabled : step.Enabled s) :
    Corr (step.nextObj φ s t) (step.nextCell ρ s t) (step.run s) ((step.rename φ ρ).run t) := by
  cases enabled with
  | alloc _ named _ => exact corr.alloc disciplinedS disciplinedT named
  | activate named =>
    show Corr (extendObj φ s t) ρ (s.alloc (.slots s.frames.length) _ _)
      (t.alloc (.slots t.frames.length) _ _)
    rw [corr.now.frames_length]
    exact corr.alloc disciplinedS disciplinedT named
  | newCell => exact corr.newCell disciplinedS disciplinedT
  | store reached named found isVector empty =>
    exact corr.store disciplinedS disciplinedT reached named found isVector empty
  | bind reached named unbound => exact corr.bind disciplinedS disciplinedT reached named unbound
  | push named => exact corr.push named
  | pop frames => exact corr.pop disciplinedS disciplinedT frames
  | restore frames => exact corr.restore disciplinedS disciplinedT frames

end CorrSteps

/-! ### Any later run -/

/-- A run the running code can take: every step enabled where it is taken. -/
inductive Runs : State Label → List (Step Label) → Prop
  | nil {s : State Label} : Runs s []
  | cons {s : State Label} {step : Step Label} {steps : List (Step Label)} :
      step.Enabled s → Runs (step.run s) steps → Runs s (step :: steps)

/-- The state after a run. -/
def runSteps : List (Step Label) → State Label → State Label
  | [], s => s
  | step :: steps, s => runSteps steps (step.run s)

/-- The run mirroring `steps` from `t`: each step with its arguments renamed by the renamings in
force when it is taken. -/
def mirror : (Addr → Addr) → (Nat → Nat) → State Label → State Label → List (Step Label) →
    List (Step Label)
  | _, _, _, _, [] => []
  | φ, ρ, s, t, step :: steps =>
    step.rename φ ρ ::
      mirror (step.nextObj φ s t) (step.nextCell ρ s t) (step.run s) ((step.rename φ ρ).run t) steps

/-- The renamings in force after a mirrored run. -/
def renamingsAfter : (Addr → Addr) → (Nat → Nat) → State Label → State Label →
    List (Step Label) → (Addr → Addr) × (Nat → Nat)
  | φ, ρ, _, _, [] => (φ, ρ)
  | φ, ρ, s, t, step :: steps =>
    renamingsAfter (step.nextObj φ s t) (step.nextCell ρ s t) (step.run s)
      ((step.rename φ ρ).run t) steps

section Runs

variable {s : State Label}

/-- A correspondence survives any run: the corresponding state takes the mirrored run, and the
two ends correspond under the renamings in force there. -/
theorem Corr.run {steps : List (Step Label)} (runs : Runs s steps) :
    ∀ {φ : Addr → Addr} {ρ : Nat → Nat} {t : State Label}, Corr φ ρ s t → Disciplined s →
      Disciplined t →
      Runs t (mirror φ ρ s t steps) ∧
        Corr (renamingsAfter φ ρ s t steps).1 (renamingsAfter φ ρ s t steps).2
          (runSteps steps s) (runSteps (mirror φ ρ s t steps) t) := by
  induction runs with
  | nil => intro φ ρ t corr _ _; exact ⟨Runs.nil, corr⟩
  | @cons s step steps enabled _ ih =>
    intro φ ρ t corr disciplinedS disciplinedT
    have enabledT := corr.enabled enabled
    obtain ⟨runsT, corr'⟩ := ih (corr.step disciplinedS disciplinedT enabled)
      (disciplinedS.step enabled) (disciplinedT.step enabledT)
    exact ⟨Runs.cons enabledT runsT, corr'⟩

/-- Every state corresponds to itself. -/
theorem Corr.refl (s : State Label) : Corr id id s s where
  now := Image.refl s
  restored _ _ _ := Image.refl _
  injObj _ _ _ _ eq := eq
  injCell _ _ _ _ eq := eq

end Runs

section CollectCorr

variable {policy : Policy} {exempt : Kind → Bool} {R : Val → Bool} {s : State Label}

theorem traced_young (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) {a : Addr}
    (reached : Reach s (.ref a)) (young : a.gen = .young) : R (.ref a) = true := by
  rcases reach_traced sound traced generational typed _ reached with inR | ⟨a', p, eq, old, _⟩
  · exact inR
  · cases eq; rw [young] at old; cases old

/-- A minor collection's result corresponds to the state before it. -/
theorem collect_corr (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s) :
    Corr (promote policy R s) (renumber R) s (collect policy R s) where
  now := collectWith_image sound traced generational typed disciplined.present (keepStore R)
  restored depth frame found :=
    collect_restoreAt sound traced generational typed disciplined.present disciplined.stores depth
      (disciplined.restorable depth frame found)
  injObj a b reachedA reachedB eq :=
    promote_inj (disciplined.present _ reachedA) (disciplined.present _ reachedB)
      (traced_young sound traced generational typed reachedA)
      (traced_young sound traced generational typed reachedB) eq
  injCell i j reachedI reachedJ eq :=
    countFrom_inj (keepCell R) 0
      (by simpa [keepCell] using traced_cell sound traced generational typed reachedI)
      (by simpa [keepCell] using traced_cell sound traced generational typed reachedJ) eq

/-- A minor collection, declined or not, corresponds to the state before it; a declined one
under the identity. -/
theorem minor_corr (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s) :
    Corr (if declines R s then id else promote policy R s) (if declines R s then id else renumber R)
      s (minor policy R s) := by
  cases declined : declines R s with
  | true => simpa [minor, declined] using Corr.refl s
  | false =>
    simpa [minor, declined] using collect_corr sound traced generational typed disciplined

/-- After a minor collection, any later run of the running code observes what it would have
without the collection: the collected state takes the mirrored run, and at its end the two
states correspond, so every read from a reached value agrees, and so does every read from a
state a frame restores. -/
theorem collect_later_run (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s)
    {steps : List (Step Label)} (runs : Runs s steps) :
    Runs (collect policy R s)
        (mirror (promote policy R s) (renumber R) s (collect policy R s) steps) ∧
      Corr (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).1
        (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).2
        (runSteps steps s)
        (runSteps (mirror (promote policy R s) (renumber R) s (collect policy R s) steps)
          (collect policy R s)) :=
  (collect_corr sound traced generational typed disciplined).run runs disciplined
    (collect_disciplined sound traced generational typed disciplined)

/-- The reads at the end of any later run agree. -/
theorem collect_later_read (sound : policy.Sound exempt) (traced : Traced policy s R)
    (generational : GenerationalOn exempt s) (typed : Typed s) (disciplined : Disciplined s)
    {steps : List (Step Label)} (runs : Runs s steps) (n : Nat) (v : Val)
    (reached : Reach (runSteps steps s) v) :
    read (runSteps (mirror (promote policy R s) (renumber R) s (collect policy R s) steps)
        (collect policy R s)) n
      (mapVal (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).1
        (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).2 v) =
      readAs (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).2
        (runSteps steps s) n v :=
  (collect_later_run sound traced generational typed disciplined runs).2.now.read_eq n v reached

end CollectCorr

/-! ### Every state the machine reaches -/

/-- The states reached from `s₀` by the running code's steps and by minor collections, declined or
not, under a policy sound against the tier's invariant, from a closed trace. -/
inductive Machine (s₀ : State Label) : State Label → Prop
  | start : Machine s₀ s₀
  | step {s : State Label} {step : Step Label} : Machine s₀ s → step.Enabled s →
      Machine s₀ (step.run s)
  | collection {s : State Label} {policy : Policy} {R : Val → Bool} : Machine s₀ s →
      policy.Sound Kind.isSlots → Traced policy s R → Machine s₀ (minor policy R s)

/-- Every state the machine reaches keeps the frame discipline and the allocation-order invariant,
whatever steps and collections led there. -/
theorem Machine.invariants {s₀ s : State Label}
    (initial : Disciplined s₀ ∧ Generational s₀ ∧ Typed s₀) (machine : Machine s₀ s) :
    Disciplined s ∧ Generational s ∧ Typed s := by
  induction machine with
  | start => exact initial
  | step _ enabled ih =>
    obtain ⟨disciplined, generational, typed⟩ := ih
    exact ⟨disciplined.step enabled, generational.step disciplined enabled,
      typed.step disciplined enabled⟩
  | @collection s policy R _ sound traced ih =>
    obtain ⟨disciplined, generational, typed⟩ := ih
    unfold minor
    split
    · exact ⟨disciplined, generational, typed⟩
    · refine ⟨collect_disciplined sound traced generational typed disciplined, ?_,
        collectWith_typed sound traced generational typed disciplined.present _⟩
      intro a o v reached old found _ member
      exact collectWith_generational sound traced generational typed disciplined.present _ a o v
        reached old found rfl member

/-- At every state the machine reaches, a minor collection is unobservable: any later run is
mirrored from the collected state, and every read agrees at its end. -/
theorem Machine.unobservable {s₀ s : State Label}
    (initial : Disciplined s₀ ∧ Generational s₀ ∧ Typed s₀) (machine : Machine s₀ s)
    {policy : Policy} {R : Val → Bool} (sound : policy.Sound Kind.isSlots)
    (traced : Traced policy s R) {steps : List (Step Label)} (runs : Runs s steps) (n : Nat)
    (v : Val) (reached : Reach (runSteps steps s) v) :
    read (runSteps (mirror (promote policy R s) (renumber R) s (collect policy R s) steps)
        (collect policy R s)) n
      (mapVal (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).1
        (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).2 v) =
      readAs (renamingsAfter (promote policy R s) (renumber R) s (collect policy R s) steps).2
        (runSteps steps s) n v := by
  obtain ⟨disciplined, generational, typed⟩ := machine.invariants initial
  exact collect_later_read sound traced generational typed disciplined runs n v reached

/-! ## Witnesses -/

/-- A state closed under a predicate on values that holds only of present ones dangles
nowhere. -/
theorem noDangling_of_closed {s : State Label} (P : Val → Bool) (root : ∀ v, s.Root v → P v = true)
    (field : ∀ a o v, P (.ref a) = true → s.get a = some o → some v ∈ o.fields → P v = true)
    (binding : ∀ i v, P (.cell i) = true → s.cells[i]? = some (some v) → P v = true)
    (there : ∀ v, P v = true → s.Present v) : NoDangling s :=
  fun v reached => there v (Reach.closed (fun v => P v = true) root field binding v reached)

namespace Witness

/-- An old slot vector born when no frame was live, and the old continuation that resumes its
activation; the running code holds the continuation. -/
def promoted : State Nat where
  young := []
  old := [⟨.slots 0, 0, [none]⟩, ⟨.cont, 1, [some (.ref ⟨.old, 0⟩)]⟩]
  cells := []
  oldCells := 0
  trail := []
  stores := []
  frames := []
  call := []
  regs := [.ref ⟨.old, 1⟩]

/-- `promoted` after a frame is pushed, an atom is made in the region, and the activation stores
the atom into its slot: the store is trailed, the frame being newer than the activation. -/
def stored : State Nat where
  young := [⟨.atom, 7, []⟩]
  old := [⟨.slots 0, 0, [some (.ref ⟨.young, 0⟩)]⟩, ⟨.cont, 1, [some (.ref ⟨.old, 0⟩)]⟩]
  cells := []
  oldCells := 0
  trail := []
  stores := [(⟨.old, 0⟩, 0)]
  frames := [⟨[.ref ⟨.old, 1⟩], 0, 0, 0, 0⟩]
  call := []
  regs := [.ref ⟨.young, 0⟩, .ref ⟨.old, 1⟩]

theorem stored_run :
    ((promoted.push [.ref ⟨.old, 1⟩]).alloc .atom 7 []).store ⟨.old, 0⟩ 0 (.ref ⟨.young, 0⟩) =
      stored := by
  decide

theorem promoted_generational : Generational promoted := by
  intro a o v _ old found notSlots member
  obtain ⟨gen, m⟩ := a
  simp only at old
  subst old
  simp only [get_old] at found
  rcases m with _ | _ | m <;> simp [promoted] at found <;> subst found
  · simp [Kind.isSlots] at notSlots
  · simp at member; subst member; rfl

theorem promoted_typed : Typed promoted := by
  intro a o b _ found kind _
  obtain ⟨gen, m⟩ := a
  cases gen with
  | young => simp [promoted] at found
  | old =>
    simp only [get_old] at found
    rcases m with _ | _ | m <;> simp [promoted] at found <;> subst found <;> simp at kind

theorem promoted_root : promoted.Root (.ref ⟨.old, 1⟩) := Or.inr (Or.inl (by simp [promoted]))

/-- The allocation-order invariant along the run: each step preserves it. -/
theorem stored_generational : Generational stored := by
  rw [← stored_run]
  refine ((promoted_generational.push ?_).alloc ?_).store (o := ⟨.slots 0, 0, [none]⟩) (birth := 0)
    ?_ rfl rfl
  · intro v member
    simp only [List.mem_singleton] at member
    subst member
    exact Reach.root promoted_root
  · intro v member; simp at member
  · exact Reach.root (Or.inr (Or.inl List.mem_cons_self))

theorem stored_typed : Typed stored := by
  rw [← stored_run]
  refine ((promoted_typed.push ?_).alloc ?_ ?_).store (o := ⟨.slots 0, 0, [none]⟩) (birth := 0)
    ?_ rfl rfl
  · intro v member
    simp only [List.mem_singleton] at member
    subst member
    exact Reach.root promoted_root
  · intro v member; simp at member
  · intro _ b member; simp at member
  · exact Reach.root (Or.inr (Or.inl List.mem_cons_self))

/-- What the sharing collection reaches from `stored`. -/
def reached (v : Val) : Bool := decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.old, 0⟩, .ref ⟨.young, 0⟩])

theorem stored_closed :
    ∀ a o v, reached (.ref a) = true → stored.get a = some o → some v ∈ o.fields →
      reached v = true := by
  intro a o v inR found member
  simp only [reached, decide_eq_true_eq, List.mem_cons, Val.ref.injEq, List.not_mem_nil,
    or_false] at inR
  rcases inR with rfl | rfl | rfl <;> simp [stored] at found <;> subst found <;>
    simp at member <;> subst member <;> decide

theorem stored_noDangling : NoDangling stored := by
  refine noDangling_of_closed reached ?_ stored_closed ?_ ?_
  · intro v root
    exact (by decide : ∀ v ∈ stored.call ++ stored.regs ++ stored.frames.flatMap Frame.vals,
      reached v = true) v (root_mem root)
  · intro i v _ bound; simp [stored] at bound
  · intro v inR
    simp only [reached, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at inR
    rcases inR with rfl | rfl | rfl <;> decide

theorem stored_traced : Traced sharing stored reached where
  root v root :=
    (by decide : ∀ v ∈ stored.call ++ stored.regs ++ stored.frames.flatMap Frame.vals,
      reached v = true) v (root_mem root)
  fixed i lt := absurd lt (Nat.not_lt_zero _)
  field a o v inR found _ member := stored_closed a o v inR found member
  binding i v _ bound := by simp [stored] at bound

theorem stored_reach_cont : Reach stored (.ref ⟨.old, 1⟩) :=
  Reach.root (Or.inr (Or.inl (by simp [stored])))

/-- Before the collection the frame's continuation reads the stored atom through its slot. -/
theorem stored_read :
    readAs (renumber reached) stored 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some (.node .atom 7 [])])] := rfl

/-- The sharing collection keeps that read: the slot, renamed in place, names the atom's copy. -/
theorem sharing_read :
    read (collect sharing reached stored) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some (.node .atom 7 [])])] :=
  (collectWith_read sharing_sound stored_traced stored_generational stored_typed
    stored_noDangling (keepStore reached) 3 _ stored_reach_cont).trans rfl

/-- A collection that shares old slot vectors without renaming them. -/
def unrewritten : Policy where
  copies _ := false
  rewrites _ := false
  walks kind := kind == .cont || kind.isSlots

theorem unrewritten_unsound (exempt : Kind → Bool) : ¬ unrewritten.Sound exempt := fun sound => by
  rcases sound.slots 0 with copies | rewrites
  · cases copies
  · cases rewrites

theorem unrewritten_traced : Traced unrewritten stored reached where
  root := stored_traced.root
  fixed := stored_traced.fixed
  field a o v inR found _ member := stored_closed a o v inR found member
  binding := stored_traced.binding

/-- Without the in-place rewrite the old slot still names the region, which the collection
emptied: the read from the frame's continuation dangles. -/
theorem unrewritten_dangles :
    read (collect unrewritten reached stored) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some .dangling])] := rfl

/-- Once the region is reused, the old slot reads whatever was made there next. -/
theorem unrewritten_reads_reused :
    read ((collect unrewritten reached stored).alloc .atom 9 []) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some (.node .atom 9 [])])] := rfl

theorem unrewritten_changes_read :
    read (collect unrewritten reached stored) 3 (.ref ⟨.old, 1⟩) ≠
      readAs (renumber reached) stored 3 (.ref ⟨.old, 1⟩) := by
  rw [unrewritten_dangles, stored_read]
  simp

/-- A collection that renames old slot vectors in place but does not walk old continuations. -/
def unwalkedConts : Policy where
  copies _ := false
  rewrites := Kind.isSlots
  walks := Kind.isSlots

theorem unwalkedConts_unsound (exempt : Kind → Bool) : ¬ unwalkedConts.Sound exempt :=
  fun sound => by cases sound.walks_cont

/-- What that collection reaches from `stored`: the continuation, and the atom the running code
holds, but not the slot vector below the continuation. -/
def reachedUnwalked (v : Val) : Bool := decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.young, 0⟩])

theorem unwalkedConts_traced : Traced unwalkedConts stored reachedUnwalked where
  root v root :=
    (by decide : ∀ v ∈ stored.call ++ stored.regs ++ stored.frames.flatMap Frame.vals,
      reachedUnwalked v = true) v (root_mem root)
  fixed i lt := absurd lt (Nat.not_lt_zero _)
  field a o v inR found walked member := by
    simp only [reachedUnwalked, decide_eq_true_eq, List.mem_cons, Val.ref.injEq,
      List.not_mem_nil, or_false] at inR
    rcases inR with rfl | rfl <;> simp [stored] at found <;> subst found
    · simp [unwalkedConts, Kind.isSlots] at walked
    · simp at member
  binding i v _ bound := by simp [stored] at bound

/-- Not walking the old continuation misses the old slot vector below it, which keeps naming the
region: the read dangles, although the atom was copied. -/
theorem unwalkedConts_dangles :
    read (collect unwalkedConts reachedUnwalked stored) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some .dangling])] := rfl

/-- A frame whose old argument vector names a region atom: what argument vectors could look like
if they changed after their frame is pushed. -/
def mutatedArgs : State Nat where
  young := [⟨.atom, 7, []⟩]
  old := [⟨.args, 0, [some (.ref ⟨.young, 0⟩)]⟩]
  cells := []
  oldCells := 0
  trail := []
  stores := []
  frames := [⟨[.ref ⟨.old, 0⟩], 0, 0, 0, 0⟩]
  call := []
  regs := []

theorem mutatedArgs_reach : Reach mutatedArgs (.ref ⟨.old, 0⟩) :=
  Reach.root (Or.inr (Or.inr ⟨_, List.mem_singleton_self _, List.mem_singleton_self _⟩))

theorem mutatedArgs_not_generational : ¬ Generational mutatedArgs := fun generational => by
  have := generational ⟨.old, 0⟩ ⟨.args, 0, [some (.ref ⟨.young, 0⟩)]⟩ (.ref ⟨.young, 0⟩)
    mutatedArgs_reach rfl rfl rfl (List.mem_singleton_self _)
  cases this

theorem mutatedArgs_generationalOn : GenerationalOn argsOrSlots mutatedArgs := by
  intro a o v _ old found notExempt _
  obtain ⟨gen, m⟩ := a
  simp only at old
  subst old
  simp only [get_old] at found
  rcases m with _ | m <;> simp [mutatedArgs] at found
  subst found
  simp [argsOrSlots] at notExempt

theorem mutatedArgs_typed : Typed mutatedArgs := by
  intro a o b _ found _ member
  obtain ⟨gen, m⟩ := a
  cases gen with
  | young =>
    simp only [get_young] at found
    rcases m with _ | m <;> simp [mutatedArgs] at found
    subst found
    simp at member
  | old =>
    simp only [get_old] at found
    rcases m with _ | m <;> simp [mutatedArgs] at found
    subst found
    simp at member
    subst member
    exact ⟨_, rfl, rfl⟩

/-- What the sharing collection reaches: the old argument vector, which it does not walk. -/
def argsReached (v : Val) : Bool := decide (v ∈ [.ref ⟨.old, 0⟩])

/-- What the rewriting collection reaches: it walks the argument vector to the atom. -/
def argsWalked (v : Val) : Bool := decide (v ∈ [.ref ⟨.old, 0⟩, .ref ⟨.young, 0⟩])

theorem mutatedArgs_closed :
    ∀ a o v, argsWalked (.ref a) = true → mutatedArgs.get a = some o → some v ∈ o.fields →
      argsWalked v = true := by
  intro a o v inR found member
  simp only [argsWalked, decide_eq_true_eq, List.mem_cons, Val.ref.injEq, List.not_mem_nil,
    or_false] at inR
  rcases inR with rfl | rfl
  · simp [mutatedArgs] at found
    subst found
    simp at member
    subst member
    decide
  · simp [mutatedArgs] at found
    subst found
    simp at member

theorem mutatedArgs_noDangling : NoDangling mutatedArgs := by
  refine noDangling_of_closed argsWalked ?_ mutatedArgs_closed ?_ ?_
  · intro v root
    exact (by decide : ∀ v ∈ mutatedArgs.call ++ mutatedArgs.regs ++
      mutatedArgs.frames.flatMap Frame.vals, argsWalked v = true) v (root_mem root)
  · intro i v _ bound; simp [mutatedArgs] at bound
  · intro v inR
    simp only [argsWalked, decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at inR
    rcases inR with rfl | rfl <;> decide

theorem mutatedArgs_traced_sharing : Traced sharing mutatedArgs argsReached where
  root v root :=
    (by decide : ∀ v ∈ mutatedArgs.call ++ mutatedArgs.regs ++
      mutatedArgs.frames.flatMap Frame.vals, argsReached v = true) v (root_mem root)
  fixed i lt := absurd lt (Nat.not_lt_zero _)
  field a o v inR found walked member := by
    simp only [argsReached, decide_eq_true_eq, List.mem_singleton, Val.ref.injEq] at inR
    subst inR
    simp [mutatedArgs] at found
    subst found
    simp [sharing, Kind.isSlots] at walked
  binding i v _ bound := by simp [mutatedArgs] at bound

theorem mutatedArgs_traced_rewriting : Traced rewritingArgs mutatedArgs argsWalked where
  root v root :=
    (by decide : ∀ v ∈ mutatedArgs.call ++ mutatedArgs.regs ++
      mutatedArgs.frames.flatMap Frame.vals, argsWalked v = true) v (root_mem root)
  fixed i lt := absurd lt (Nat.not_lt_zero _)
  field a o v inR found _ member := mutatedArgs_closed a o v inR found member
  binding i v _ bound := by simp [mutatedArgs] at bound

/-- Sharing an old argument vector untouched relies on its immutability: had it changed after
the push, the collection would leave it naming the emptied region. -/
theorem sharing_mutatedArgs_dangles :
    read (collect sharing argsReached mutatedArgs) 2 (.ref ⟨.old, 0⟩) =
      .node .args 0 [some .dangling] := rfl

/-- Renaming argument vectors in place needs no immutability: the rewriting collection keeps the
read under the weaker invariant. -/
theorem rewritingArgs_mutatedArgs_read :
    read (collect rewritingArgs argsWalked mutatedArgs) 2 (.ref ⟨.old, 0⟩) =
      .node .args 0 [some (.node .atom 7 [])] :=
  (collectWith_read rewritingArgs_sound mutatedArgs_traced_rewriting mutatedArgs_generationalOn
    mutatedArgs_typed mutatedArgs_noDangling (keepStore argsWalked) 2 _ mutatedArgs_reach).trans rfl

/-- A store-trail remap that keeps only the entries of the vectors the collection copied,
dropping those of the old vectors it renamed in place. -/
def keepCopiedStores (R : Val → Bool) (e : Addr × Nat) : Bool :=
  R (.ref e.1) && e.1.gen == .young

theorem stored_restored_noDangling : NoDangling (stored.restoreAt 0) := by
  have restored : stored.restoreAt 0 = {
      young := []
      old := [⟨.slots 0, 0, [none]⟩, ⟨.cont, 1, [some (.ref ⟨.old, 0⟩)]⟩]
      cells := []
      oldCells := 0
      trail := []
      stores := []
      frames := [⟨[.ref ⟨.old, 1⟩], 0, 0, 0, 0⟩]
      call := []
      regs := [.ref ⟨.old, 1⟩] } := by decide
  rw [restored]
  refine noDangling_of_closed (fun v => decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.old, 0⟩])) ?_ ?_ ?_ ?_
  · intro v root
    exact (by decide : ∀ v ∈ [.ref ⟨.old, 1⟩], decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.old, 0⟩]) = true)
      v (by simpa using root_mem root)
  · intro a o v inR found member
    simp only [decide_eq_true_eq, List.mem_cons, Val.ref.injEq, List.not_mem_nil, or_false] at inR
    rcases inR with rfl | rfl
    · simp at found
      subst found
      simp at member
      subst member
      decide
    · simp at found
      subst found
      simp at member
  · intro i v _ bound; simp at bound
  · intro v inR
    simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at inR
    rcases inR with rfl | rfl <;> decide

theorem stored_storesSlots :
    ∀ e ∈ stored.stores, ∃ o birth, stored.get e.1 = some o ∧ o.kind = .slots birth := by
  intro e member
  simp only [stored, List.mem_singleton] at member
  subst member
  exact ⟨_, 0, rfl, rfl⟩

/-- Restoring the frame empties the slot the store filled after it. -/
theorem stored_restore_read :
    readAs (renumber reached) (stored.restoreAt 0) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [none])] := rfl

/-- After the sharing collection the store trail keeps the in-place vector's entry, and the
restore still empties the slot. -/
theorem sharing_restore_read :
    read ((collect sharing reached stored).restoreAt 0) 3 (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [none])] := by
  exact (collect_restoreAt_read sharing_sound stored_traced stored_generational stored_typed
    stored_noDangling stored_storesSlots 0 stored_restored_noDangling 3 (.ref ⟨.old, 1⟩)
    (Reach.root (Or.inr (Or.inl List.mem_cons_self)))).trans rfl

/-- Dropping the entry of a vector the collection still reached lets the restore leave the slot
filled: it holds a term built on the path the restore undid. -/
theorem dropped_entry_stale :
    read ((collectWith sharing reached stored (keepCopiedStores reached)).restoreAt 0) 3
        (.ref ⟨.old, 1⟩) =
      .node .cont 1 [some (.node (.slots 0) 0 [some (.node .atom 7 [])])] := rfl

theorem dropped_entry_changes_read :
    read ((collectWith sharing reached stored (keepCopiedStores reached)).restoreAt 0) 3
        (.ref ⟨.old, 1⟩) ≠
      readAs (renumber reached) (stored.restoreAt 0) 3 (.ref ⟨.old, 1⟩) := by
  rw [dropped_entry_stale, stored_restore_read]
  simp

/-- The initial state keeps the frame discipline: no frame is live, and its one slot vector was
born with none. -/
theorem promoted_disciplined : Disciplined promoted := by
  refine ⟨⟨List.Pairwise.nil, fun frame member => by simp [promoted] at member⟩, ?_, ?_,
    fun e member => by simp [promoted] at member, fun frame member => by simp [promoted] at member,
    fun _ _ _ depth _ _ lt => by simp [promoted] at lt, ?_⟩
  · refine noDangling_of_closed (fun v => decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.old, 0⟩])) ?_ ?_ ?_ ?_
    · intro v root
      exact (by decide : ∀ v ∈ promoted.call ++ promoted.regs ++ promoted.frames.flatMap Frame.vals,
        decide (v ∈ [.ref ⟨.old, 1⟩, .ref ⟨.old, 0⟩]) = true) v (root_mem root)
    · intro a o v inR found member
      simp only [decide_eq_true_eq, List.mem_cons, Val.ref.injEq, List.not_mem_nil, or_false] at inR
      rcases inR with rfl | rfl
      · simp [promoted] at found
        subst found
        simp at member
        subst member
        decide
      · simp [promoted] at found
        subst found
        simp at member
    · intro i v _ bound; simp [promoted] at bound
    · intro v inR
      simp only [decide_eq_true_eq, List.mem_cons, List.not_mem_nil, or_false] at inR
      rcases inR with rfl | rfl <;> decide
  · intro depth frame found; simp [promoted] at found
  · intro a o b _ found kind
    obtain ⟨gen, m⟩ := a
    cases gen with
    | young => simp [promoted] at found
    | old =>
      simp only [get_old] at found
      rcases m with _ | _ | m <;> simp [promoted] at found <;> subst found <;> simp at kind
      subst kind
      exact Nat.le_refl _

/-- The frame discipline along the run to `stored`: each step keeps it. -/
theorem stored_disciplined : Disciplined stored := by
  rw [← stored_run]
  refine ((promoted_disciplined.push ?_).alloc ?_ ?_).store (o := ⟨.slots 0, 0, [none]⟩)
    (birth := 0) ?_ rfl rfl rfl
  · intro v member
    simp only [List.mem_singleton] at member
    subst member
    exact Reach.root promoted_root
  · intro v member; simp at member
  · intro b kind; cases kind
  · exact Reach.root (Or.inr (Or.inl List.mem_cons_self))

/-- `stored` is a state the machine reaches from `promoted`, which keeps every invariant. -/
theorem stored_machine : Machine promoted stored := by
  rw [← stored_run]
  refine Machine.step (step := .store ⟨.old, 0⟩ 0 (.ref ⟨.young, 0⟩))
    (Machine.step (step := .alloc .atom 7 [])
      (Machine.step (step := .push [.ref ⟨.old, 1⟩]) Machine.start ?_) ?_) ?_
  · refine Step.Enabled.push fun v member => ?_
    simp only [List.mem_singleton] at member
    subst member
    exact Reach.root promoted_root
  · exact Step.Enabled.alloc rfl (fun v member => by simp at member)
      (fun _ b member => by simp at member)
  · exact Step.Enabled.store (o := ⟨.slots 0, 0, [none]⟩) (birth := 0)
      (Reach.field (Reach.root (Or.inr (Or.inl (List.mem_cons_of_mem _ List.mem_cons_self))))
        (o := ⟨.cont, 1, [some (.ref ⟨.old, 0⟩)]⟩) rfl List.mem_cons_self)
      (Reach.root (Or.inr (Or.inl List.mem_cons_self))) rfl rfl rfl

theorem stored_invariants : Disciplined stored ∧ Generational stored ∧ Typed stored :=
  stored_machine.invariants ⟨promoted_disciplined, promoted_generational, promoted_typed⟩

/-- Restoring the frame is a run `stored` can take. -/
theorem stored_runs : Runs stored [.restore] :=
  Runs.cons (Step.Enabled.restore (frame := ⟨[.ref ⟨.old, 1⟩], 0, 0, 0, 0⟩) (older := []) rfl)
    Runs.nil

/-- The later-run theorem applied to `stored`: after the sharing collection, restoring the
frame reads through the continuation what restoring it would have read before. -/
theorem stored_later_read :
    read (runSteps (mirror (promote sharing reached stored) (renumber reached) stored
        (collect sharing reached stored) [.restore]) (collect sharing reached stored)) 3
      (.ref ⟨.old, 1⟩) = .node .cont 1 [some (.node (.slots 0) 0 [none])] :=
  (collect_later_read sharing_sound stored_traced stored_generational stored_typed
    stored_disciplined stored_runs 3 (.ref ⟨.old, 1⟩)
    (Reach.root (Or.inr (Or.inl List.mem_cons_self)))).trans rfl

end Witness

end Mettapedia.GSLT.LanguageDef.RegionGenerations
