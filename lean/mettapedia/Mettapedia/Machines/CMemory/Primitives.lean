import Mettapedia.Machines.CMemory.Block
import Mettapedia.GSLT.Logic.AbstractSeparationLogic

/-!
# The C memory primitives as local actions

Seven primitives act on block memory:

* `load p` reads an initialized cell, with any permission on it;
* `store p v` writes a cell, with the whole permission on it;
* `malloc n` either fails and returns null, or returns a fresh block of `n`
  indeterminate cells;
* `free p` is a no-op on null, and otherwise kills the block of which `p` is
  the base, with the whole block held;
* `realloc p n` on null behaves as `malloc n`; otherwise, with the whole block
  held and `n > 0`, it either fails and changes nothing, or makes a fresh block
  of `n` cells, moves the first `min m n` cells into it, leaves the rest
  indeterminate, and kills the old block;
* `ptrEq p q` compares two pointers, each null or valid;
* `undefined` is undefined behaviour.

`malloc`, `realloc` and failure are nondeterministic: a program is safe only if
every choice is.  A fresh block is one of which nothing at all is held, header
or cells; dead blocks keep their header, so they are never chosen again.

Every case the C standard leaves undefined has no defined step: loading an
indeterminate or unheld cell, writing a cell without the whole permission,
freeing an interior pointer, freeing twice, freeing or reallocating a block
not wholly held, `realloc` of a live block to size zero (undefined in C23),
and comparing a pointer into a dead block.

Each primitive is a local action (`act_local`), and each has an outcome wherever
it is defined (`act_progress`).  The frame rule therefore holds for every
program over these primitives (`frame`).

Global sanity: running a primitive on the whole state of memory keeps that
state well formed (`act_wellFormed`), and every load and store that is defined
there lands inside a live block (`load_lands_in_live_block`,
`store_lands_in_live_block`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open CellPermission

universe u

/-- **The primitive memory operations** over cell values `V`. -/
inductive Op (V : Type) where
  | load (p : Ptr)
  | store (p : Ptr) (v : V)
  | malloc (n : ℕ)
  | free (p : Option Ptr)
  | realloc (p : Option Ptr) (n : ℕ)
  | ptrEq (p q : Option Ptr)
  | undefined

/-- The result type of each primitive. -/
def Op.Ret {V : Type} : Op V → Type
  | .load _ => V
  | .store _ _ => Unit
  | .malloc _ => Option Ptr
  | .free _ => Unit
  | .realloc _ _ => Option Ptr
  | .ptrEq _ _ => Bool
  | .undefined => Empty

/-- **C programs** over the memory primitives. -/
abbrev CProg (V : Type) (α : Type) := Prog (Op V) Op.Ret α

namespace CProg

variable {V : Type}

/-- One call of a primitive. -/
def prim (o : Op V) : CProg V o.Ret := Prog.prim o

def load (p : Ptr) : CProg V V := prim (.load p)
def store (p : Ptr) (v : V) : CProg V Unit := prim (.store p v)
def malloc (n : ℕ) : CProg V (Option Ptr) := prim (.malloc n)
def free (p : Option Ptr) : CProg V Unit := prim (.free p)
def realloc (p : Option Ptr) (n : ℕ) : CProg V (Option Ptr) := prim (.realloc p n)
def ptrEq (p q : Option Ptr) : CProg V Bool := prim (.ptrEq p q)
def undefined {α : Type} : CProg V α := Prog.call (Op.undefined (V := V)) fun e => Empty.elim e

end CProg

section Semantics

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-- The block `malloc n` installs: alive, with `n` whole indeterminate cells. -/
def freshBlock (n : ℕ) : BlockRes L :=
  (.own ⟨n, true⟩, fun i => if i < n then whole none else 0)

namespace Heap

/-- Replace the cell at `p`. -/
def setCell (σ : Heap L) (p : Ptr) (x : L) : Heap L :=
  Function.update σ p.block ((σ p.block).1, Function.update (σ p.block).2 p.offset x)

/-- The block `b` of size `n`, killed: its header records death, and its cells
are released. -/
def killedBlock (σ : Heap L) (b : BlockId) (n : ℕ) : BlockRes L :=
  (.own ⟨n, false⟩, fun i => if i < n then 0 else (σ b).2 i)

def kill (σ : Heap L) (b : BlockId) (n : ℕ) : Heap L :=
  Function.update σ b (killedBlock σ b n)

/-- The block that `realloc` makes from block `b` of size `m`, with `n` cells:
the first `min m n` cells are moved, the remaining ones are indeterminate. -/
def grownBlock (σ : Heap L) (b : BlockId) (m n : ℕ) : BlockRes L :=
  (.own ⟨n, true⟩, fun i => if i < m ∧ i < n then (σ b).2 i else if i < n then whole none else 0)

/-- Move block `b` of size `m` into the fresh block `b'` of `n` cells. -/
def move (σ : Heap L) (b : BlockId) (m : ℕ) (b' : BlockId) (n : ℕ) : Heap L :=
  Function.update (σ.kill b m) b' (σ.grownBlock b m n)

end Heap

/-- The whole block `b` of size `n` is held: its live header and every cell
with the whole permission. -/
def HoldsBlock (σ : Heap L) (b : BlockId) (n : ℕ) : Prop :=
  (σ b).1 = .own ⟨n, true⟩ ∧ ∀ i < n, ∃ c, (σ b).2 i = whole c

/-- The outcomes of allocating `n` cells: failure with null and no change, or
a fresh block. -/
def AllocStep (n : ℕ) (σ : Heap L) (r : Option Ptr) (σ' : Heap L) : Prop :=
  (r = none ∧ σ' = σ) ∨
    ∃ b, σ b = 0 ∧ r = some ⟨b, 0⟩ ∧ σ' = Function.update σ b (freshBlock n)

/-- **The meaning of each primitive.** -/
def act : (o : Op V) → Action (Heap L) o.Ret
  | .load p => ⟨fun σ => ∃ v, read ((σ p.block).2 p.offset) = some (some v),
      fun σ (v : V) σ' => read ((σ p.block).2 p.offset) = some (some v) ∧ σ' = σ⟩
  | .store p v => ⟨fun σ => ∃ c, (σ p.block).2 p.offset = whole c,
      fun σ _ σ' => σ' = σ.setCell p (whole (some v))⟩
  | .malloc n => ⟨fun _ => True, AllocStep n⟩
  | .free none => ⟨fun _ => True, fun σ _ σ' => σ' = σ⟩
  | .free (some p) => ⟨fun σ => p.offset = 0 ∧ ∃ n, HoldsBlock σ p.block n,
      fun σ _ σ' => ∃ n, (σ p.block).1 = .own ⟨n, true⟩ ∧ σ' = σ.kill p.block n⟩
  | .realloc none n => ⟨fun _ => True, AllocStep n⟩
  | .realloc (some p) n => ⟨fun σ => 0 < n ∧ p.offset = 0 ∧ ∃ m, HoldsBlock σ p.block m,
      fun σ (r : Option Ptr) σ' => (r = none ∧ σ' = σ) ∨
        ∃ m b', (σ p.block).1 = .own ⟨m, true⟩ ∧ σ b' = 0 ∧ r = some ⟨b', 0⟩ ∧
          σ' = σ.move p.block m b' n⟩
  | .ptrEq p q => ⟨fun σ => ValidOpt σ p ∧ ValidOpt σ q,
      fun σ (r : Bool) σ' => r = decide (p = q) ∧ σ' = σ⟩
  | .undefined => ⟨fun _ => False, fun _ _ _ => False⟩

/-! ## Framing lemmas for the heap operations -/

section Framing

variable {σ τ : Heap L}

theorem frame_cell_zero {p : Ptr} {c : Option V} (separate : σ ## τ)
    (whole_at : (σ p.block).2 p.offset = whole c) : (τ p.block).2 p.offset = 0 := by
  have := (separate p.block).2 p.offset
  rw [whole_at] at this
  exact eq_zero_of_whole_separate this

theorem frame_header_empty {b : BlockId} {header : Header} (separate : σ ## τ)
    (owned : (σ b).1 = .own header) : (τ b).1 = .empty := by
  rcases (separate b).1 with empty | empty
  · rw [owned] at empty
    cases empty
  · exact empty

theorem HoldsBlock.frame {b : BlockId} {n : ℕ} (holds : HoldsBlock σ b n)
    (separate : σ ## τ) : HoldsBlock (σ + τ) b n := by
  refine ⟨by rw [heap_add_header, holds.1]; rfl, fun i inside => ?_⟩
  obtain ⟨c, whole_at⟩ := holds.2 i inside
  refine ⟨c, ?_⟩
  rw [heap_add_cell, whole_at]
  exact whole_add_of_separate (whole_at ▸ (separate b).2 i)

theorem HoldsBlock.frame_zero {b : BlockId} {n : ℕ} (holds : HoldsBlock σ b n)
    (separate : σ ## τ) {i : ℕ} (inside : i < n) : (τ b).2 i = 0 := by
  obtain ⟨c, whole_at⟩ := holds.2 i inside
  exact frame_cell_zero (p := ⟨b, i⟩) separate whole_at

theorem setCell_frame {p : Ptr} {c : Option V} (separate : σ ## τ)
    (whole_at : (σ p.block).2 p.offset = whole c) (x : L) (separateX : x ## 0) :
    (σ + τ).setCell p x = σ.setCell p x + τ ∧ σ.setCell p x ## τ := by
  have frameZero := frame_cell_zero separate whole_at
  constructor
  · rw [Heap.setCell, Heap.setCell, update_add]
    congr 1
    refine blockRes_ext rfl fun i => ?_
    by_cases same : i = p.offset
    · subst i
      simp only [Prod.snd_add, Pi.add_apply, Function.update_self, frameZero,
        SepAlgebra.add_zero]
    · simp only [Prod.snd_add, Pi.add_apply, Function.update_of_ne same]
  · refine update_separate separate ⟨(separate p.block).1, fun i => ?_⟩
    by_cases same : i = p.offset
    · subst i
      simpa only [Function.update_self, frameZero] using separateX
    · simpa only [Function.update_of_ne same] using (separate p.block).2 i

theorem kill_frame {b : BlockId} {n : ℕ} (holds : HoldsBlock σ b n) (separate : σ ## τ) :
    (σ + τ).kill b n = σ.kill b n + τ ∧ σ.kill b n ## τ := by
  have headerEmpty := frame_header_empty separate holds.1
  constructor
  · rw [Heap.kill, Heap.kill, update_add]
    congr 1
    refine blockRes_ext ?_ fun i => ?_
    · simp only [Heap.killedBlock, Prod.fst_add, headerEmpty]
      rfl
    · simp only [Heap.killedBlock, Prod.snd_add, Pi.add_apply]
      split
      · rename_i inside
        rw [holds.frame_zero separate inside, SepAlgebra.add_zero]
      · rfl
  · refine update_separate separate ⟨Or.inr headerEmpty, fun i => ?_⟩
    simp only [Heap.killedBlock]
    split
    · exact SepAlgebra.zero_separate _
    · exact (separate b).2 i

theorem grownBlock_frame {b : BlockId} {m : ℕ} (holds : HoldsBlock σ b m)
    (separate : σ ## τ) (n : ℕ) :
    (σ + τ).grownBlock b m n = σ.grownBlock b m n := by
  refine blockRes_ext rfl fun i => ?_
  simp only [Heap.grownBlock, heap_add_cell]
  split
  · rename_i inside
    rw [holds.frame_zero separate inside.1, SepAlgebra.add_zero]
  · rfl

theorem alloc_frame {n : ℕ} {r : Option Ptr} {σ' : Heap L} (separate : σ ## τ)
    (step : AllocStep n (σ + τ) r σ') :
    ∃ σ₁, σ₁ ## τ ∧ σ' = σ₁ + τ ∧ AllocStep n σ r σ₁ := by
  rcases step with ⟨rfl, rfl⟩ | ⟨b, fresh, rfl, rfl⟩
  · exact ⟨σ, separate, rfl, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨freshσ, freshτ⟩ := blockRes_eq_zero_of_add_eq_zero (separate b) fresh
    refine ⟨Function.update σ b (freshBlock n), ?_, ?_, Or.inr ⟨b, freshσ, rfl, rfl⟩⟩
    · exact update_separate separate (freshτ ▸ SepAlgebra.separate_zero _)
    · rw [update_add, freshτ, SepAlgebra.add_zero]

end Framing

/-! ## Locality -/

/-- **Every primitive is a local action.** -/
theorem act_local : ∀ o : Op V, (act (L := L) o).Local
  | .load p => {
      safe_frame := by
        rintro σ τ ⟨v, readV⟩ separate
        exact ⟨v, by rw [heap_add_cell]; exact read_add ((separate p.block).2 p.offset) readV⟩
      step_frame := by
        rintro σ τ σ' r ⟨v, readV⟩ separate ⟨readR, rfl⟩
        have global := read_add ((separate p.block).2 p.offset) readV
        rw [heap_add_cell, global] at readR
        cases readR
        exact ⟨σ, separate, rfl, readV, rfl⟩ }
  | .store p v => {
      safe_frame := by
        rintro σ τ ⟨c, whole_at⟩ separate
        refine ⟨c, ?_⟩
        rw [heap_add_cell, whole_at]
        exact whole_add_of_separate (whole_at ▸ (separate p.block).2 p.offset)
      step_frame := by
        rintro σ τ σ' r ⟨c, whole_at⟩ separate rfl
        obtain ⟨equal, separated⟩ :=
          setCell_frame separate whole_at (whole (some v)) (SepAlgebra.separate_zero _)
        exact ⟨_, separated, equal, rfl⟩ }
  | .malloc n => {
      safe_frame := fun _ _ => trivial
      step_frame := fun _ separate step => alloc_frame separate step }
  | .free none => {
      safe_frame := fun _ _ => trivial
      step_frame := by
        rintro σ τ σ' r - separate rfl
        exact ⟨σ, separate, rfl, rfl⟩ }
  | .free (some p) => {
      safe_frame := by
        rintro σ τ ⟨base, n, holds⟩ separate
        exact ⟨base, n, holds.frame separate⟩
      step_frame := by
        rintro σ τ σ' r ⟨-, n, holds⟩ separate ⟨n', header, rfl⟩
        have same : n' = n := by
          rw [heap_add_header, holds.1] at header
          cases header
          rfl
        subst n'
        obtain ⟨equal, separated⟩ := kill_frame holds separate
        exact ⟨_, separated, equal, n, holds.1, rfl⟩ }
  | .realloc none n => {
      safe_frame := fun _ _ => trivial
      step_frame := fun _ separate step => alloc_frame separate step }
  | .realloc (some p) n => {
      safe_frame := by
        rintro σ τ ⟨positive, base, m, holds⟩ separate
        exact ⟨positive, base, m, holds.frame separate⟩
      step_frame := by
        rintro σ τ σ' r ⟨-, -, m, holds⟩ separate step
        rcases step with ⟨rfl, rfl⟩ | ⟨m', b', header, fresh, rfl, rfl⟩
        · exact ⟨σ, separate, rfl, Or.inl ⟨rfl, rfl⟩⟩
        · have same : m' = m := by
            rw [heap_add_header, holds.1] at header
            cases header
            rfl
          subst m'
          obtain ⟨freshσ, freshτ⟩ := blockRes_eq_zero_of_add_eq_zero (separate b') fresh
          obtain ⟨killed, killedSeparate⟩ := kill_frame holds separate
          refine ⟨σ.move p.block m b' n, ?_, ?_, Or.inr ⟨m, b', holds.1, freshσ, rfl, rfl⟩⟩
          · exact update_separate killedSeparate (freshτ ▸ SepAlgebra.separate_zero _)
          · rw [Heap.move, Heap.move, update_add, killed, freshτ, SepAlgebra.add_zero,
              grownBlock_frame holds separate] }
  | .ptrEq p q => {
      safe_frame := by
        rintro σ τ ⟨validP, validQ⟩ separate
        exact ⟨ValidOpt.frame separate validP, ValidOpt.frame separate validQ⟩
      step_frame := by
        rintro σ τ σ' r - separate ⟨rfl, rfl⟩
        exact ⟨σ, separate, rfl, rfl, rfl⟩ }
  | .undefined => {
      safe_frame := fun impossible _ => impossible.elim
      step_frame := fun impossible _ _ => impossible.elim }

/-- **Every primitive has an outcome wherever it is defined.** -/
theorem act_progress : ∀ o : Op V, (act (L := L) o).Progress
  | .load _ => fun σ ⟨v, readV⟩ => ⟨v, σ, readV, rfl⟩
  | .store _ _ => fun _ _ => ⟨(), _, rfl⟩
  | .malloc _ => fun σ _ => ⟨none, σ, Or.inl ⟨rfl, rfl⟩⟩
  | .free none => fun σ _ => ⟨(), σ, rfl⟩
  | .free (some _) => fun _ ⟨_, n, holds⟩ => ⟨(), _, n, holds.1, rfl⟩
  | .realloc none _ => fun σ _ => ⟨none, σ, Or.inl ⟨rfl, rfl⟩⟩
  | .realloc (some _) _ => fun σ _ => ⟨none, σ, Or.inl ⟨rfl, rfl⟩⟩
  | .ptrEq _ _ => fun σ _ => ⟨_, σ, rfl, rfl⟩
  | .undefined => fun _ impossible => impossible.elim

/-! ## The logic of C programs -/

/-- Hoare triples for C programs over cell permissions `L`. -/
abbrev CTriple {α : Type} (P : Heap L → Prop) (c : CProg V α) (Q : α → Heap L → Prop) :
    Prop :=
  Triple (act (L := L)) P c Q

/-- **The frame rule for every C program.** -/
theorem frame {α : Type} {P : Heap L → Prop} {c : CProg V α} {Q : α → Heap L → Prop}
    (spec : CTriple P c Q) (F : Heap L → Prop) :
    CTriple (P ∗ F) c (fun a => Q a ∗ F) :=
  triple_frame act act_local spec F

/-- The frame rule with the frame on the left. -/
theorem frame_left {α : Type} {P : Heap L → Prop} {c : CProg V α}
    {Q : α → Heap L → Prop} (spec : CTriple P c Q) (F : Heap L → Prop) :
    CTriple (F ∗ P) c (fun a => F ∗ Q a) :=
  triple_frame_left act act_local spec F

/-- A safe C program always has a terminating execution. -/
theorem exists_runs {α : Type} (c : CProg V α) (σ : Heap L) (safe : c.Safe act σ) :
    ∃ a σ', c.Runs act σ a σ' :=
  Prog.exists_runs act act_progress c σ safe

/-- One call of a primitive runs whenever its action steps. -/
theorem prim_runs {o : Op V} {σ σ' : Heap L} {r : o.Ret} (step : (act o).Step σ r σ') :
    (CProg.prim o).Runs act σ r σ' :=
  ⟨r, σ', step, rfl, rfl⟩

/-- A program is not safe if some execution of its first part reaches a state
from which its continuation is not safe. -/
theorem not_safe_bind {α β : Type} {c : CProg V α} {f : α → CProg V β} {σ σ' : Heap L}
    {a : α} (runs : c.Runs act σ a σ') (stuck : ¬ (f a).Safe act σ') :
    ¬ (c.bind f).Safe act σ := by
  rw [Prog.safe_bind]
  exact fun ⟨_, after⟩ => stuck (after a σ' runs)

/-- A program is not safe if its first part, specified by a triple, must reach
states from which its continuation is not safe. -/
theorem not_safe_of_triple {α β : Type} {P : Heap L → Prop} {c : CProg V α}
    {R : α → Heap L → Prop} {f : α → CProg V β} (spec : CTriple P c R) {σ : Heap L}
    (holds : P σ) (stuck : ∀ a τ, R a τ → ¬ (f a).Safe act τ) :
    ¬ (c.bind f).Safe act σ := by
  intro safe
  obtain ⟨safeC, after⟩ := (Prog.safe_bind act c f σ).mp safe
  obtain ⟨a, τ, runs⟩ := exists_runs c σ safeC
  exact stuck a τ ((spec σ holds).2 a τ runs) (after a τ runs)

/-! ## Global sanity: memory stays well formed -/

theorem read_ne_zero {x : L} {c : Option V} (readC : read x = some c) : x ≠ 0 := by
  rintro rfl
  rw [read_zero] at readC
  cases readC

/-- **Every defined load lands in a live block, inside its bounds.** -/
theorem load_lands_in_live_block {σ : Heap L} (wellFormed : WellFormed σ) {p : Ptr}
    (safe : (act (L := L) (V := V) (.load p)).Safe σ) :
    ∃ n, (σ p.block).1 = .own ⟨n, true⟩ ∧ p.offset < n := by
  obtain ⟨v, readV⟩ := safe
  exact wellFormed.live (read_ne_zero readV)

/-- **Every defined store lands in a live block, inside its bounds.** -/
theorem store_lands_in_live_block {σ : Heap L} (wellFormed : WellFormed σ) {p : Ptr}
    {v : V} (safe : (act (L := L) (.store p v)).Safe σ) :
    ∃ n, (σ p.block).1 = .own ⟨n, true⟩ ∧ p.offset < n := by
  obtain ⟨c, whole_at⟩ := safe
  exact wellFormed.live (whole_at ▸ whole_ne_zero c)

omit [Add L] [SepAlgebra L] in
theorem wellFormed_update {σ : Heap L} (wellFormed : WellFormed σ) (b : BlockId)
    (r : BlockRes L) (covered : ∀ i, r.2 i ≠ 0 → ∃ n, r.1 = .own ⟨n, true⟩ ∧ i < n) :
    WellFormed (Function.update σ b r) := by
  intro x i held
  by_cases same : x = b
  · subst x
    simp only [Function.update_self] at held ⊢
    exact covered i held
  · simp only [Function.update_of_ne same] at held ⊢
    exact wellFormed x i held

omit [Add L] [SepAlgebra L] in
theorem wellFormed_kill {σ : Heap L} (wellFormed : WellFormed σ) {b : BlockId} {n : ℕ}
    (header : (σ b).1 = .own ⟨n, true⟩) : WellFormed (σ.kill b n) := by
  apply wellFormed_update wellFormed
  intro i held
  simp only [Heap.killedBlock] at held
  split at held
  · exact absurd rfl held
  · rename_i outside
    obtain ⟨n', header', inside⟩ := wellFormed b i held
    rw [header] at header'
    cases header'
    exact absurd inside outside

/-- **Running a defined primitive on the whole of memory keeps it well
formed.** -/
theorem act_wellFormed {σ σ' : Heap L} (wellFormed : WellFormed σ) (o : Op V) {r : o.Ret}
    (safe : (act o).Safe σ) (step : (act o).Step σ r σ') : WellFormed σ' := by
  cases o with
  | load p =>
    obtain ⟨-, rfl⟩ := step
    exact wellFormed
  | store p v =>
    obtain ⟨c, whole_at⟩ := safe
    subst step
    apply wellFormed_update wellFormed
    intro i held
    by_cases same : i = p.offset
    · subst i
      exact wellFormed p.block p.offset (whole_at ▸ whole_ne_zero c)
    · simp only [Function.update_of_ne same] at held
      exact wellFormed p.block i held
  | malloc n =>
    rcases step with ⟨-, rfl⟩ | ⟨b, -, -, rfl⟩
    · exact wellFormed
    · apply wellFormed_update wellFormed
      intro i held
      simp only [freshBlock] at held
      split at held
      · rename_i inside
        exact ⟨n, rfl, inside⟩
      · exact absurd rfl held
  | free p =>
    cases p with
    | none =>
      subst step
      exact wellFormed
    | some p =>
      obtain ⟨n, header, rfl⟩ := step
      exact wellFormed_kill wellFormed header
  | realloc p n =>
    cases p with
    | none =>
      rcases step with ⟨-, rfl⟩ | ⟨b, -, -, rfl⟩
      · exact wellFormed
      · apply wellFormed_update wellFormed
        intro i held
        simp only [freshBlock] at held
        split at held
        · rename_i inside
          exact ⟨n, rfl, inside⟩
        · exact absurd rfl held
    | some p =>
      rcases step with ⟨-, rfl⟩ | ⟨m, b', header, -, -, rfl⟩
      · exact wellFormed
      · apply wellFormed_update (wellFormed_kill wellFormed header)
        intro i held
        simp only [Heap.grownBlock] at held
        split at held
        · rename_i inside
          exact ⟨n, rfl, inside.2⟩
        · split at held
          · rename_i inside
            exact ⟨n, rfl, inside⟩
          · exact absurd rfl held
  | ptrEq p q =>
    obtain ⟨-, rfl⟩ := step
    exact wellFormed
  | undefined => exact safe.elim

/-- **Running a safe program on the whole of memory keeps it well formed.** -/
theorem runs_wellFormed {α : Type} (c : CProg V α) {σ τ : Heap L} {a : α}
    (wellFormed : WellFormed σ) (safe : c.Safe act σ) (runs : c.Runs act σ a τ) :
    WellFormed τ := by
  induction c generalizing σ with
  | ret b =>
    obtain ⟨-, rfl⟩ := runs
    exact wellFormed
  | call o k ih =>
    obtain ⟨r, σ₁, step, rest⟩ := runs
    exact ih r (act_wellFormed wellFormed o safe.1 step) (safe.2 r σ₁ step) rest

/-- `not_safe_of_triple` for the whole of memory: the intermediate states are
well formed too. -/
theorem not_safe_of_triple_wf {α β : Type} {P : Heap L → Prop} {c : CProg V α}
    {R : α → Heap L → Prop} {f : α → CProg V β} (spec : CTriple P c R) {σ : Heap L}
    (holds : P σ) (wellFormed : WellFormed σ)
    (stuck : ∀ a τ, R a τ → WellFormed τ → ¬ (f a).Safe act τ) :
    ¬ (c.bind f).Safe act σ := by
  intro safe
  obtain ⟨safeC, after⟩ := (Prog.safe_bind act c f σ).mp safe
  obtain ⟨a, τ, runs⟩ := exists_runs c σ safeC
  exact stuck a τ ((spec σ holds).2 a τ runs) (runs_wellFormed c wellFormed safeC runs)
    (after a τ runs)

end Semantics

end Mettapedia.Machines.CMemory
