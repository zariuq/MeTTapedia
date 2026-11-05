import Mettapedia.GSLT.LanguageDef.Collections.Spines
import Mettapedia.Languages.MeTTa.ListValueNativeLayout
import Mettapedia.Machines.Cursor.PrefixBuffer

/-!
# CeTTa's list layout

CeTTa holds a complete list as one flat array of its elements, and a list with
an unbound or improper rest as cells, each an element before the rest of the
list (`Native`). This module makes that representation a `Layouts.Layout` and
separates three accounts of it.

* **Correctness.** The abstraction of a native value is its elements with its
  terminal, and prepend, head, tail, indexing and known length are specified
  through it (`native`). Every observation of the abstraction therefore agrees
  on all native values with one abstraction, and with every other layout of
  the same list (`Layouts.Layout.agree`). A prepend keeps a complete list flat
  and puts a cell before any other value; a chain of cells whose rest became a
  complete list is the same list as the flat array of its elements, which
  `flatten` produces (`abs_flatten`, `flatten_canonical`).
* **Agreement with the stored roots.** A native value is written as the root
  fields `(LIST x₁ … xₙ)` or `(LIST_REST x₁ … x_k t)` of
  `Languages.MeTTa.ListValueNativeLayout` (`toRoot`). Decoding those fields with
  `readRoot` and reading the decoded term as a list gives back the abstraction
  (`readRoot_toRoot_reading`); on list values that reading is
  `Spines.abstractOf` (`abstractOf_toTerm`). Conversely every normal form is
  the term of a native value, read as its abstraction (`toTerm_ofTerm`,
  `abs_ofTerm`), so every root the builder writes decodes to the term of a
  native value (`readRoot_layout_native`).
* **Front slack and sharing.** A complete list's array is a view of a prefix
  buffer (`Machines.Cursor.PrefixBuffer`). A prepend there either claims the
  free slot below the view or copies the list into a fresh buffer; either way
  the new view realizes the layout's prepend, and every other live view keeps
  realizing the value it held (`prepend_realizes`, `prepend_keeps`). So the
  value semantics above holds for every holder of a shared buffer. Which path
  a prepend takes is a cost, not a correctness, fact: one slot for a claim, the
  whole list for a copy (`prepend_claim_cost`, `prepend_copy_cost`); along one
  chain of prepends the copies are paid for by the claims
  (`PrefixBuffer.run_cost`), and two prepends onto one shared list at every
  step cost a quadratic total (`Machines.SharedPrependCost.sharedFlat_total`).

The buffer protocol is sequential; ownership, arena lifetimes and reclamation
are not modelled here.

Controls: the cell `[1 | (2 3)]` and the flat `(1 2 3)` are one value
(`Controls.cells_and_flat_agree`), while the number of cells, a physical
fact, separates them (`Controls.cell_count_not_abstract`); a raw expression
prepend onto the list root exposes the list tag
(`Controls.raw_prepend_exposes_tag`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.NativeLayout

open Layouts (Terminal Abstract Layout)

universe u v

/-- A list value as CeTTa's runtime holds it. -/
inductive Native (A : Type u) (V : Type v) where
  /-- A complete list: one flat array of its elements. -/
  | flat (elements : List A)
  /-- An open cell: one element before the rest of the list. -/
  | cell (head : A) (rest : Native A V)
  /-- The unbound rest of an open list. -/
  | unbound (rest : V)
  /-- The improper rest of a list. -/
  | improper (rest : A)
  deriving DecidableEq, Repr

namespace Native

variable {A : Type u} {V : Type v}

/-- The elements of a native value with its terminal. -/
def abs : Native A V → Abstract A V
  | .flat xs => (xs, .nil)
  | .cell x rest => (x :: (abs rest).1, (abs rest).2)
  | .unbound v => ([], .var v)
  | .improper t => ([], .improper t)

/-- Prepend: a complete list stays one flat array; any other value gets a cell. -/
def cons (x : A) : Native A V → Native A V
  | .flat xs => .flat (x :: xs)
  | other => .cell x other

def head : Native A V → Option A
  | .flat xs => xs.head?
  | .cell x _ => some x
  | .unbound _ => none
  | .improper _ => none

/-- The tail of a flat array is the suffix view of the same array. -/
def tail : Native A V → Option (Native A V)
  | .flat [] => none
  | .flat (_ :: xs) => some (.flat xs)
  | .cell _ rest => some rest
  | .unbound _ => none
  | .improper _ => none

def nth : Native A V → ℕ → Option A
  | .flat xs, i => xs[i]?
  | .cell x _, 0 => some x
  | .cell _ rest, i + 1 => nth rest i
  | .unbound _, _ => none
  | .improper _, _ => none

def knownLength : Native A V → ℕ
  | .flat xs => xs.length
  | .cell _ rest => knownLength rest + 1
  | .unbound _ => 0
  | .improper _ => 0

theorem abs_cons (x : A) (l : Native A V) : abs (cons x l) = (x :: (abs l).1, (abs l).2) := by
  cases l <;> rfl

theorem head_spec (l : Native A V) : head l = (abs l).1.head? := by
  cases l <;> rfl

theorem tail_spec (l : Native A V) :
    (tail l).map abs = (abs l).1.tail?.map fun rest => (rest, (abs l).2) := by
  match l with
  | .flat [] => rfl
  | .flat (_ :: _) => rfl
  | .cell _ _ => rfl
  | .unbound _ => rfl
  | .improper _ => rfl

theorem nth_spec : ∀ (l : Native A V) (i : ℕ), nth l i = (abs l).1[i]?
  | .flat _, _ => rfl
  | .cell _ _, 0 => rfl
  | .cell _ rest, i + 1 => by rw [nth, nth_spec rest i]; rfl
  | .unbound _, i => by cases i <;> rfl
  | .improper _, i => by cases i <;> rfl

theorem knownLength_spec : ∀ l : Native A V, knownLength l = (abs l).1.length
  | .flat _ => rfl
  | .cell _ rest => by rw [knownLength, knownLength_spec rest]; rfl
  | .unbound _ => rfl
  | .improper _ => rfl

/-! ### Complete lists are flat -/

/-- No chain of cells ends in a complete list: such a chain is held as the
flat array of its elements. -/
def Canonical : Native A V → Prop
  | .flat _ => True
  | .cell _ rest => Canonical rest ∧ ∀ ys, rest ≠ .flat ys
  | .unbound _ => True
  | .improper _ => True

/-- A cell before a value, joining a complete list's array. -/
def join (x : A) : Native A V → Native A V
  | .flat ys => .flat (x :: ys)
  | other => .cell x other

/-- Read a chain of cells whose rest became a complete list back into one flat
array. -/
def flatten : Native A V → Native A V
  | .cell x rest => join x (flatten rest)
  | other => other

theorem abs_join (x : A) (l : Native A V) : abs (join x l) = abs (.cell x l) := by
  cases l <;> rfl

theorem join_canonical (x : A) : ∀ l : Native A V, Canonical l → Canonical (join x l)
  | .flat _, _ => trivial
  | .cell _ _, canonical => ⟨canonical, fun _ equal => by cases equal⟩
  | .unbound _, _ => ⟨trivial, fun _ equal => by cases equal⟩
  | .improper _, _ => ⟨trivial, fun _ equal => by cases equal⟩

theorem abs_flatten : ∀ l : Native A V, abs (flatten l) = abs l
  | .flat _ => rfl
  | .unbound _ => rfl
  | .improper _ => rfl
  | .cell x rest => by
      rw [flatten, abs_join]
      simp only [abs, abs_flatten rest]

theorem flatten_canonical : ∀ l : Native A V, Canonical (flatten l)
  | .flat _ => trivial
  | .unbound _ => trivial
  | .improper _ => trivial
  | .cell x rest => join_canonical x _ (flatten_canonical rest)

/-- On every value, prepending is joining. -/
theorem cons_eq_join (x : A) (l : Native A V) : cons x l = join x l := by
  cases l <;> rfl

theorem cons_canonical (x : A) (l : Native A V) (canonical : Canonical l) : Canonical (cons x l) := by
  rw [cons_eq_join]
  exact join_canonical x l canonical

theorem tail_canonical : ∀ {l rest : Native A V}, Canonical l → tail l = some rest → Canonical rest
  | .flat (_ :: _), _, _, taken => by cases taken; trivial
  | .cell _ _, _, canonical, taken => by cases taken; exact canonical.1

end Native

/-- **CeTTa's list layout.** -/
def native {A : Type u} {V : Type v} : Layout.{u, v, max u v} A V where
  Carrier := Native A V
  abs := Native.abs
  cons := Native.cons
  head := Native.head
  tail := Native.tail
  nth := Native.nth
  knownLength := Native.knownLength
  abs_cons := Native.abs_cons
  head_spec := Native.head_spec
  tail_spec := Native.tail_spec
  nth_spec := Native.nth_spec
  knownLength_spec := Native.knownLength_spec

/-! ## The stored roots -/

section Roots

open Mettapedia.Logic.Unification.ListSplice
open Mettapedia.Languages.MeTTa.ListValueNativeLayout (Root rawLayout readRoot ValidRoot)

variable {Leaf Var : Type}

/-- The term a native value stands for. -/
def toTerm : Native (Term Leaf Var) Var → Term Leaf Var
  | .flat xs => .list xs
  | .cell x rest => splice [x] (toTerm rest)
  | .unbound v => .var v
  | .improper t => t

/-- The root fields CeTTa writes for a native value: `(LIST x₁ … xₙ)` for a
complete list, `(LIST_REST x₁ … x_k t)` for an open or improper one. -/
def toRoot (l : Native (Term Leaf Var) Var) : Root Leaf Var := rawLayout (toTerm l)

/-- Every term read as a list: its explicit elements and how it ends. A
variable is the open list with no elements, and a term that is neither a
variable nor a list value is an improper rest. -/
def reading : Term Leaf Var → Abstract (Term Leaf Var) Var
  | .list xs => (xs, .nil)
  | .rest xs (.var v) => (xs, .var v)
  | .rest xs t => (xs, .improper t)
  | .var v => ([], .var v)
  | t => ([], .improper t)

/-- Improper rests are improper terms, neither list values nor variables. -/
def Proper : Native (Term Leaf Var) Var → Prop
  | .cell _ rest => Proper rest
  | .improper t => Spines.ImproperTail t
  | _ => True

/-- The term of a value that is not a bare rest is a list value. -/
theorem toTerm_cell (x : Term Leaf Var) (rest : Native (Term Leaf Var) Var) (proper : Proper rest) :
    toTerm (.cell x rest) = .list (x :: (Native.abs rest).1) ∧ (Native.abs rest).2 = .nil ∨
      ∃ t, toTerm (.cell x rest) = .rest (x :: (Native.abs rest).1) t ∧ reading (.rest [] t) = ([], (Native.abs rest).2) ∧
        ValidRoot t := by
  induction rest generalizing x with
  | flat ys => exact Or.inl ⟨rfl, rfl⟩
  | unbound v => exact Or.inr ⟨.var v, rfl, rfl, trivial⟩
  | improper t =>
      refine Or.inr ⟨t, ?_, ?_, ?_⟩
      · cases t <;> simp_all [Proper, Spines.ImproperTail, toTerm, splice, Native.abs]
      · cases t <;> simp_all [Proper, Spines.ImproperTail, reading, Native.abs]
      · cases t <;> simp_all [Proper, Spines.ImproperTail, ValidRoot]
  | cell y rest ih =>
      rcases ih y proper with ⟨same, closed⟩ | ⟨t, same, ending, valid⟩
      · refine Or.inl ⟨?_, closed⟩
        change splice [x] (toTerm (.cell y rest)) = _
        rw [same, splice_list]
        rfl
      · refine Or.inr ⟨t, ?_, ending, valid⟩
        change splice [x] (toTerm (.cell y rest)) = _
        rw [same, splice_rest]
        rfl

/-- **The stored term reads as the abstraction.** -/
theorem reading_toTerm : ∀ (l : Native (Term Leaf Var) Var), Proper l → reading (toTerm l) = Native.abs l
  | .flat _, _ => rfl
  | .unbound _, _ => rfl
  | .improper t, improper => by cases t <;> simp_all [Proper, Spines.ImproperTail, reading, toTerm, Native.abs]
  | .cell x rest, proper => by
      rcases toTerm_cell x rest proper with ⟨same, closed⟩ | ⟨t, same, ending, -⟩
      · rw [same]
        simp [reading, Native.abs, closed]
      · rw [same]
        change reading (.rest (x :: (Native.abs rest).1) t) = (x :: (Native.abs rest).1, (Native.abs rest).2)
        cases t <;> simpa [reading] using ending

theorem validRoot_toTerm : ∀ (l : Native (Term Leaf Var) Var), Proper l → ValidRoot (toTerm l)
  | .flat _, _ => trivial
  | .unbound _, _ => trivial
  | .improper t, improper => by cases t <;> simp_all [Proper, Spines.ImproperTail, ValidRoot, toTerm]
  | .cell x rest, proper => by
      rcases toTerm_cell x rest proper with ⟨same, -⟩ | ⟨t, same, -, -⟩
      · rw [same]; trivial
      · rw [same]; simp [ValidRoot]

/-- `readRoot` decodes the written root to the term the value stands for. -/
theorem readRoot_toRoot (l : Native (Term Leaf Var) Var) (proper : Proper l) :
    readRoot (toRoot l) = some (toTerm l) :=
  Mettapedia.Languages.MeTTa.ListValueNativeLayout.readRoot_rawLayout _ (validRoot_toTerm l proper)

/-- **The abstraction agrees with `readRoot`**: decoding the written root and
reading the decoded term as a list gives the native value's abstraction. -/
theorem readRoot_toRoot_reading (l : Native (Term Leaf Var) Var) (proper : Proper l) :
    (readRoot (toRoot l)).map reading = some (Native.abs l) := by
  rw [readRoot_toRoot l proper, Option.map_some, reading_toTerm l proper]

/-- On list values, the reading is the spine abstraction. -/
theorem reading_eq_of_abstractOf {t : Term Leaf Var} {a : Abstract (Term Leaf Var) Var}
    (abstracted : Spines.abstractOf t = some a) : reading t = a := by
  match t, abstracted with
  | .list _, rfl => rfl
  | .rest _ (.var _), rfl => rfl
  | .rest _ (.atom _), rfl => rfl
  | .rest _ (.expr _), rfl => rfl
  | .rest _ (.list _), rfl => rfl
  | .rest _ (.rest _ _), rfl => rfl

/-- A native value that is not a bare rest stands for a list value whose spine
abstraction is the native abstraction. -/
theorem abstractOf_toTerm (l : Native (Term Leaf Var) Var) (proper : Proper l)
    (listValue : ∀ end_, l ≠ .unbound end_) (notRest : ∀ t, l ≠ .improper t) :
    Spines.abstractOf (toTerm l) = some (Native.abs l) := by
  match l, proper with
  | .flat _, _ => rfl
  | .unbound v, _ => exact (listValue v rfl).elim
  | .improper t, _ => exact (notRest t rfl).elim
  | .cell x rest, proper =>
      rcases toTerm_cell x rest proper with ⟨same, closed⟩ | ⟨t, same, ending, -⟩
      · rw [same]
        simp [Spines.abstractOf, Native.abs, closed]
      · rw [same]
        change Spines.abstractOf (.rest (x :: (Native.abs rest).1) t) =
          some (x :: (Native.abs rest).1, (Native.abs rest).2)
        cases t <;> simp_all [Spines.abstractOf, reading]

/-- The cells of a prefix before a rest. -/
def cells (xs : List (Term Leaf Var)) (rest : Native (Term Leaf Var) Var) : Native (Term Leaf Var) Var :=
  xs.foldr .cell rest

/-- The native value of a list term: a list value is a flat array, an open or
improper spine its cells, and any other term a bare rest. -/
def ofTerm : Term Leaf Var → Native (Term Leaf Var) Var
  | .list xs => .flat xs
  | .rest xs (.var v) => cells xs (.unbound v)
  | .rest xs t => cells xs (.improper t)
  | .var v => .unbound v
  | t => .improper t

theorem toTerm_cells (xs : List (Term Leaf Var)) (rest : Native (Term Leaf Var) Var) :
    toTerm (cells xs rest) = splice xs (toTerm rest) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change splice [x] (toTerm (cells xs rest)) = splice (x :: xs) (toTerm rest)
      rw [ih, ← splice_append]
      rfl

/-- A normal list term in splice normal form: a list value, an open or improper
spine with a nonempty prefix, a variable, or an improper term. -/
def NormalSpine : Term Leaf Var → Prop
  | .rest xs t => xs ≠ [] ∧ (Spines.ImproperTail t ∨ ∃ v, t = .var v)
  | .list _ => True
  | .var _ => True
  | t => Spines.ImproperTail t

/-- **Every normal list term is the term of a native value.** -/
theorem toTerm_ofTerm : ∀ (t : Term Leaf Var), NormalSpine t → toTerm (ofTerm t) = t
  | .list _, _ => rfl
  | .var _, _ => rfl
  | .atom _, _ => rfl
  | .expr _, _ => rfl
  | .rest xs t, ⟨nonempty, tail⟩ => by
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
      rcases tail with improper | ⟨v, rfl⟩
      · cases t <;> simp_all [Spines.ImproperTail, ofTerm, toTerm_cells, toTerm, splice]
      · simp [ofTerm, toTerm_cells, toTerm, splice]

theorem normalSpine_splice (xs : List (Term Leaf Var)) (tail : Term Leaf Var) (normal : NormalSpine tail) :
    NormalSpine (splice xs tail) := by
  cases xs with
  | nil => exact normal
  | cons x xs =>
      cases tail with
      | list ys => trivial
      | rest ys t =>
          rw [splice_rest]
          exact ⟨by simp, normal.2⟩
      | var v => exact ⟨by simp, Or.inr ⟨v, rfl⟩⟩
      | atom a => exact ⟨by simp, Or.inl trivial⟩
      | expr ys => exact ⟨by simp, Or.inl trivial⟩

/-- **Every normal form is a normal spine**, so every root the builder writes
decodes to the term of a native value. -/
theorem normalSpine_normalize (t : Term Leaf Var) : NormalSpine (normalize t) := by
  match t with
  | .atom _ => rw [normalize]; exact trivial
  | .var _ => rw [normalize]; exact trivial
  | .expr _ => rw [normalize]; exact trivial
  | .list _ => rw [normalize]; exact trivial
  | .rest xs tail =>
      rw [normalize]
      exact normalSpine_splice _ _ (normalSpine_normalize tail)
termination_by sizeOf t

theorem proper_cells (xs : List (Term Leaf Var)) (rest : Native (Term Leaf Var) Var) (proper : Proper rest) :
    Proper (cells xs rest) := by
  induction xs with
  | nil => exact proper
  | cons x xs ih => exact ih

theorem proper_ofTerm : ∀ (t : Term Leaf Var), NormalSpine t → Proper (ofTerm t)
  | .list _, _ => trivial
  | .var _, _ => trivial
  | .atom _, _ => trivial
  | .expr _, _ => trivial
  | .rest xs t, ⟨_, tail⟩ => by
      rcases tail with improper | ⟨v, rfl⟩
      · cases t with
        | atom _ => exact proper_cells _ _ trivial
        | expr _ => exact proper_cells _ _ trivial
        | var _ => exact improper.elim
        | list _ => exact improper.elim
        | rest _ _ => exact improper.elim
      · exact proper_cells _ _ trivial

/-- The native value of a normal spine reads as the spine. -/
theorem abs_ofTerm (t : Term Leaf Var) (normal : NormalSpine t) : Native.abs (ofTerm t) = reading t := by
  rw [← reading_toTerm _ (proper_ofTerm t normal), toTerm_ofTerm t normal]

/-- **The builder's roots are the roots of native values**: the root written
for any term decodes to the term of the native value of its normal form. -/
theorem readRoot_layout_native (t : Term Leaf Var) :
    readRoot (Mettapedia.Languages.MeTTa.ListValueNativeLayout.layout t) =
      some (toTerm (ofTerm (normalize t))) := by
  rw [Mettapedia.Languages.MeTTa.ListValueNativeLayout.readRoot_layout,
    toTerm_ofTerm _ (normalSpine_normalize t)]

end Roots

/-! ## Front slack: complete lists in prefix buffers -/

section Buffers

open Mettapedia.Machines.Cursor.PrefixBuffer

variable {α : Type} {V : Type v}

/-- A live view of a prefix buffer realizes the complete list it reads. -/
def Realizes (H : Heap α) (view : View) (l : Native α V) : Prop :=
  Live H view ∧ ∃ xs, l = .flat xs ∧ read H view = some xs

/-- A prepend in the buffer, claiming or copying, realizes the layout's prepend. -/
theorem prepend_realizes {H : Heap α} {view : View} {xs : List α} (x : α)
    (realized : Realizes H view (.flat xs : Native α V)) :
    Realizes (prepend H view xs x).1 (prepend H view xs x).2.1 (native.cons x (.flat xs) : Native α V) := by
  obtain ⟨live, ys, same, readView⟩ := realized
  have elements : xs = ys := by injection same
  subst elements
  exact ⟨live_prepend x live, x :: xs, rfl, read_prepend x readView⟩

/-- **Every other holder keeps its value**: a prepend onto any view leaves each
live view realizing the value it realized. -/
theorem prepend_keeps {H : Heap α} {view other : View} {xs : List α} {l : Native α V} (x : α)
    (realized : Realizes H other l) : Realizes (prepend H view xs x).1 other l := by
  obtain ⟨live, ys, same, readOther⟩ := realized
  exact ⟨live_stable x live, ys, same, (read_stable x live).trans readOther⟩

/-- A claim writes one slot. -/
theorem prepend_claim_cost {H : Heap α} {view : View} {xs : List α} (x : α)
    (claimable : Claimable H view) : (prepend H view xs x).2.2 = 1 := by
  simp [prepend, claimable]

/-- A copy writes the whole list and the new element. -/
theorem prepend_copy_cost {H : Heap α} {view : View} {xs : List α} (x : α)
    (blocked : ¬ Claimable H view) : (prepend H view xs x).2.2 = view.len + 1 :=
  Mettapedia.Machines.Cursor.PrefixBuffer.prepend_copy_cost x blocked

end Buffers

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.Unification.ListSplice
open Mettapedia.Languages.MeTTa.ListValueNativeLayout (Root Field Tag rawLayout readRoot)

/-- `[1 | (2 3)]` held as a cell before a flat array, and `(1 2 3)` held flat:
one value, read the same by every observation of the layout. -/
theorem cells_and_flat_agree :
    (native (A := ℕ) (V := Unit)).abs (.cell 1 (.flat [2, 3])) =
        (native (A := ℕ) (V := Unit)).abs (.flat [1, 2, 3]) ∧
      Native.flatten (.cell 1 (.flat [2, 3]) : Native ℕ Unit) = .flat [1, 2, 3] :=
  ⟨rfl, rfl⟩

/-- The number of cells is a physical fact the abstraction does not expose. -/
theorem cell_count_not_abstract :
    let celled : Native ℕ Unit := .cell 1 (.flat [2, 3])
    let flatList : Native ℕ Unit := .flat [1, 2, 3]
    native.abs celled = native.abs flatList ∧ celled ≠ flatList ∧
      ¬ Native.Canonical celled ∧ Native.Canonical flatList := by
  refine ⟨rfl, by decide, fun canonical => canonical.2 [2, 3] rfl, trivial⟩

/-- An open list `[a | $t]` is a cell before its unbound rest, and the root
CeTTa writes for it is `(LIST_REST a $t)`. -/
theorem open_cell_root :
    toRoot (.cell (.atom "a") (.unbound "t") : Native (Term String String) String) =
      .expression [.tag .rest, .payload (.atom "a"), .payload (.var "t")] := rfl

/-- A raw expression prepend onto the list root exposes the list tag as a
payload position, so the result decodes to no term: prepend must go through
the layout, not through the root's fields. -/
theorem raw_prepend_exposes_tag :
    (Mettapedia.Languages.MeTTa.ListValueNativeLayout.rawFieldCons (.atom "z")
        (toRoot (.flat [.atom "a"] : Native (Term String String) String))).bind readRoot = none ∧
      readRoot (toRoot (native.cons (.atom "z") (.flat [.atom "a"]) :
        Native (Term String String) String)) = some (.list [.atom "z", .atom "a"]) :=
  ⟨Mettapedia.Languages.MeTTa.ListValueNativeLayout.rawFieldCons_list_rejected _ _, rfl⟩

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.NativeLayout
