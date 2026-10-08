import Mettapedia.Machines.CMemory.Fractional
import Mettapedia.GSLT.Logic.LockInvariant

/-!
# Layer 3 for C memory: data-race freedom

A **data race** is two primitives that access one cell, at least one of them
writing (C11 5.1.2.4p35).  Loads read their cell; stores write it; `free` and
`realloc` write every cell of their block.

**Race freedom** (`no_race`): two primitives that are defined on separate
parts of a well-formed memory never race.  A write needs the whole permission
on its cell, or the whole block, so the other part holds nothing there; a
cell beyond a block's size is held by nobody, because memory is well formed.

**Every reachable interleaving is race free**, under both disciplines of
`AbstractSeparationLogic`:

* disjoint threads, each verified alone (`disjoint_race_free`);
* threads that share state only through one lock with invariant `I`
  (`lock_race_free`).

The interleaving semantics is sequentially consistent by construction.  For
race-free programs, the C11 memory model (Boehm and Adve, PLDI 2008; Batty et
al., POPL 2011) and POSIX (XBD 4.12) guarantee that every execution of the real
program is one of these sequentially consistent ones; that external theorem is
the bridge from these proofs to compiled, threaded C.

## Examples

* **Positive.**  The publisher's two appends run in parallel on separate
  arrays (`parallel_appends`); two threads read one cell through half
  permissions (`parallel_shared_reads`); two threads increment a counter
  through the lock without race (`locked_counter_race_free`).
* **Negative.**  Unsynchronized increments lose an update
  (`unsynchronized_increments_lose_an_update`), and their precondition cannot
  be split between the threads (`shared_counter_unsplittable`); freeing a
  block while another thread loads from it faults (`free_races_with_load`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CMemory.Concurrency

open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open scoped Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Machines.CMemory
open CellPermission

universe u

variable {L : Type u} {V : Type} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option V)]

/-! ## Races -/

/-- The cells a primitive accesses, and whether it writes them. -/
def Accesses : Op V → Ptr → Bool → Prop
  | .load p, q, write => q = p ∧ write = false
  | .store p _, q, write => q = p ∧ write = true
  | .free (some p), q, write => q.block = p.block ∧ write = true
  | .realloc (some p) _, q, write => q.block = p.block ∧ write = true
  | _, _, _ => False

/-- **A data race**: two primitives access one cell, and one of them writes. -/
def Race (o₁ o₂ : Op V) : Prop :=
  ∃ q w₁ w₂, Accesses o₁ q w₁ ∧ Accesses o₂ q w₂ ∧ (w₁ = true ∨ w₂ = true)

/-- What a defined access holds: the cell (wholly, if it writes), or the whole
block. -/
theorem access_holds {σ : Heap L} {o : Op V} {q : Ptr} {w : Bool}
    (safe : (act o).Safe σ) (accesses : Accesses o q w) :
    ((σ q.block).2 q.offset ≠ 0 ∧ (w = true → ∃ c, (σ q.block).2 q.offset = whole c)) ∨
      ∃ n, HoldsBlock σ q.block n := by
  cases o with
  | load p =>
    obtain ⟨rfl, rfl⟩ := accesses
    obtain ⟨v, readV⟩ := safe
    exact Or.inl ⟨read_ne_zero readV, fun impossible => absurd impossible (by simp)⟩
  | store p v =>
    obtain ⟨rfl, -⟩ := accesses
    obtain ⟨c, whole_at⟩ := safe
    exact Or.inl ⟨whole_at ▸ whole_ne_zero c, fun _ => ⟨c, whole_at⟩⟩
  | malloc n => exact accesses.elim
  | free p =>
    cases p with
    | none => exact accesses.elim
    | some p =>
      obtain ⟨same, -⟩ := accesses
      obtain ⟨-, n, holds⟩ := safe
      exact Or.inr ⟨n, same ▸ holds⟩
  | realloc p n =>
    cases p with
    | none => exact accesses.elim
    | some p =>
      obtain ⟨same, -⟩ := accesses
      obtain ⟨-, -, m, holds⟩ := safe
      exact Or.inr ⟨m, same ▸ holds⟩
  | ptrEq p q => exact accesses.elim
  | undefined => exact accesses.elim

section Exclusive

variable {σ₁ σ₂ ρ : Heap L}

omit [CellPermission L (Option V)] in
theorem cell_ne_zero_left {C : Type} [CellPermission L C] (separate : σ₁ ## σ₂)
    (apart : (σ₁ + σ₂) ## ρ) {q : Ptr} (held : (σ₁ q.block).2 q.offset ≠ 0) :
    ((σ₁ + σ₂ + ρ) q.block).2 q.offset ≠ 0 := by
  simp only [heap_add_cell]
  exact add_ne_zero_of_ne_zero ((apart q.block).2 q.offset)
    (add_ne_zero_of_ne_zero ((separate q.block).2 q.offset) held)

omit [CellPermission L (Option V)] in
theorem cell_ne_zero_right {C : Type} [CellPermission L C] (separate : σ₁ ## σ₂)
    (apart : (σ₁ + σ₂) ## ρ) {q : Ptr} (held : (σ₂ q.block).2 q.offset ≠ 0) :
    ((σ₁ + σ₂ + ρ) q.block).2 q.offset ≠ 0 := by
  rw [SepAlgebra.add_comm separate] at apart ⊢
  exact cell_ne_zero_left (SepAlgebra.separate_symm separate) apart held

omit [Zero L] [SepAlgebra L] [CellPermission L (Option V)] in
theorem header_global_left {b : BlockId} {n : ℕ}
    (header : (σ₁ b).1 = .own ⟨n, true⟩) : ((σ₁ + σ₂ + ρ) b).1 = .own ⟨n, true⟩ := by
  simp only [heap_add_header, header]
  rfl

omit [CellPermission L (Option V)] in
theorem header_global_right (separate : σ₁ ## σ₂) {b : BlockId} {n : ℕ}
    (header : (σ₂ b).1 = .own ⟨n, true⟩) : ((σ₁ + σ₂ + ρ) b).1 = .own ⟨n, true⟩ := by
  rw [SepAlgebra.add_comm separate]
  exact header_global_left header

omit [Add L] [SepAlgebra L] [CellPermission L (Option V)] in
/-- In well-formed memory, a held cell lies inside its block's bounds. -/
theorem block_bounds {σ : Heap L} (wellFormed : WellFormed σ) {q : Ptr} {n : ℕ}
    (header : (σ q.block).1 = .own ⟨n, true⟩) (held : (σ q.block).2 q.offset ≠ 0) :
    q.offset < n := by
  obtain ⟨n', header', inside⟩ := wellFormed q.block q.offset held
  rw [header] at header'
  cases header'
  exact inside

/-- **A cell held by one part, wholly if written, is not accessed by the
other.** -/
theorem holds_exclusive (separate : σ₁ ## σ₂) (apart : (σ₁ + σ₂) ## ρ)
    (wellFormed : WellFormed (σ₁ + σ₂ + ρ)) {q : Ptr} {w₁ w₂ : Bool}
    (holds₁ : ((σ₁ q.block).2 q.offset ≠ 0 ∧
      (w₁ = true → ∃ c, (σ₁ q.block).2 q.offset = whole c)) ∨ ∃ n, HoldsBlock σ₁ q.block n)
    (holds₂ : ((σ₂ q.block).2 q.offset ≠ 0 ∧
      (w₂ = true → ∃ c, (σ₂ q.block).2 q.offset = whole c)) ∨ ∃ n, HoldsBlock σ₂ q.block n)
    (writes : w₁ = true ∨ w₂ = true) : False := by
  rcases holds₁ with ⟨held₁, whole₁⟩ | ⟨n₁, block₁⟩ <;>
    rcases holds₂ with ⟨held₂, whole₂⟩ | ⟨n₂, block₂⟩
  · rcases writes with write | write
    · obtain ⟨c, whole_at⟩ := whole₁ write
      exact held₂ (frame_cell_zero separate whole_at)
    · obtain ⟨c, whole_at⟩ := whole₂ write
      exact held₁ (frame_cell_zero (SepAlgebra.separate_symm separate) whole_at)
  · by_cases inside : q.offset < n₂
    · obtain ⟨c, whole_at⟩ := block₂.2 q.offset inside
      exact held₁ (frame_cell_zero (p := q) (SepAlgebra.separate_symm separate) whole_at)
    · exact inside (block_bounds wellFormed
        (header_global_right separate block₂.1) (cell_ne_zero_left separate apart held₁))
  · by_cases inside : q.offset < n₁
    · obtain ⟨c, whole_at⟩ := block₁.2 q.offset inside
      exact held₂ (frame_cell_zero (p := q) separate whole_at)
    · exact inside (block_bounds wellFormed
        (header_global_left block₁.1) (cell_ne_zero_right separate apart held₂))
  · have headers := (separate q.block).1
    rw [block₁.1, block₂.1] at headers
    exact Excl.not_separate_own _ _ headers

/-- **Primitives defined on separate parts of well-formed memory never
race.** -/
theorem no_race (separate : σ₁ ## σ₂) (apart : (σ₁ + σ₂) ## ρ)
    (wellFormed : WellFormed (σ₁ + σ₂ + ρ)) {o₁ o₂ : Op V}
    (safe₁ : (act o₁).Safe σ₁) (safe₂ : (act o₂).Safe σ₂) : ¬ Race o₁ o₂ := by
  rintro ⟨q, w₁, w₂, access₁, access₂, writes⟩
  exact holds_exclusive separate apart wellFormed (access_holds safe₁ access₁)
    (access_holds safe₂ access₂) writes

end Exclusive

/-! ## Disjoint threads -/

/-- The primitive a program performs next. -/
def nextOp {α : Type} : CProg V α → Option (Op V)
  | .ret _ => none
  | .call o _ => some o

theorem good_wellFormed_step {α β : Type} {Q₁ : α → Heap L → Prop} {Q₂ : β → Heap L → Prop}
    {c₁ c₁' : CProg V α} {c₂ c₂' : CProg V β} {σ σ' : Heap L}
    (good : Good act Q₁ Q₂ c₁ c₂ σ) (wellFormed : WellFormed σ)
    (step : ParStep act c₁ c₂ σ c₁' c₂' σ') : WellFormed σ' := by
  obtain ⟨σ₁, σ₂, separate, rfl, meets₁, meets₂⟩ := good
  cases step with
  | left step =>
    exact act_wellFormed wellFormed _ ((act_local _).safe_frame meets₁.1.1 separate) step
  | right step =>
    have safe := (act_local _).safe_frame meets₂.1.1 (SepAlgebra.separate_symm separate)
    rw [← SepAlgebra.add_comm separate] at safe
    exact act_wellFormed wellFormed _ safe step

theorem good_wellFormed_of_reaches {α β : Type} {Q₁ : α → Heap L → Prop}
    {Q₂ : β → Heap L → Prop} {c₁ c₁' : CProg V α} {c₂ c₂' : CProg V β} {σ σ' : Heap L}
    (good : Good act Q₁ Q₂ c₁ c₂ σ) (wellFormed : WellFormed σ)
    (reaches : ParReaches act c₁ c₂ σ c₁' c₂' σ') :
    Good act Q₁ Q₂ c₁' c₂' σ' ∧ WellFormed σ' := by
  induction reaches with
  | refl => exact ⟨good, wellFormed⟩
  | step step _ ih =>
    exact ih (good_step act_local good step) (good_wellFormed_step good wellFormed step)

/-- **Disjoint threads never race.**  In every configuration that some
interleaving reaches from separate preconditions on well-formed memory, the
next primitives of the two threads do not race. -/
theorem disjoint_race_free {α β : Type} {P₁ P₂ : Heap L → Prop} {c₁ : CProg V α}
    {c₂ : CProg V β} {Q₁ : α → Heap L → Prop} {Q₂ : β → Heap L → Prop}
    (spec₁ : CTriple P₁ c₁ Q₁) (spec₂ : CTriple P₂ c₂ Q₂) {σ : Heap L}
    (holds : (P₁ ∗ P₂) σ) (wellFormed : WellFormed σ) {c₁' : CProg V α} {c₂' : CProg V β}
    {σ' : Heap L} (reaches : ParReaches act c₁ c₂ σ c₁' c₂' σ') {o₁ o₂ : Op V}
    (next₁ : nextOp c₁' = some o₁) (next₂ : nextOp c₂' = some o₂) : ¬ Race o₁ o₂ := by
  obtain ⟨σ₁, σ₂, separate, rfl, holds₁, holds₂⟩ := holds
  have good : Good act Q₁ Q₂ c₁ c₂ (σ₁ + σ₂) :=
    ⟨σ₁, σ₂, separate, rfl, spec₁ σ₁ holds₁, spec₂ σ₂ holds₂⟩
  obtain ⟨⟨τ₁, τ₂, separate', rfl, meets₁, meets₂⟩, wellFormed'⟩ :=
    good_wellFormed_of_reaches good wellFormed reaches
  cases c₁' with
  | ret _ => cases next₁
  | call o k =>
    cases c₂' with
    | ret _ => cases next₂
    | call o' k' =>
      cases next₁
      cases next₂
      refine no_race separate' (SepAlgebra.separate_zero _) ?_ meets₁.1.1 meets₂.1.1
      rwa [SepAlgebra.add_zero]

/-! ## Threads sharing through the lock -/

/-- The base primitive a lock program performs next, if its next step is one. -/
def nextBase {α : Type} : LProg (Op V) Op.Ret α → Option (Op V)
  | .call (.base o) _ => some o
  | _ => none

theorem lockGood_wellFormed_step {α β : Type} {I : Heap L → Prop} {Q₁ : α → Heap L → Prop}
    {Q₂ : β → Heap L → Prop} {c₁ c₁' : LProg (Op V) Op.Ret α} {c₂ c₂' : LProg (Op V) Op.Ret β}
    {l l' : LockState} {σ σ' : Heap L} (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ)
    (wellFormed : WellFormed σ) (step : LockStep act c₁ c₂ l σ c₁' c₂' l' σ') :
    WellFormed σ' := by
  cases step with
  | leftBase step =>
    cases l with
    | free => exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
    | first => exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
    | second => exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
  | rightBase step =>
    cases l with
    | free =>
      change (_ ∗ (_ ∗ I)) σ at good
      rw [sepConj_left_comm] at good
      exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
    | first =>
      change (_ ∗ _) σ at good
      rw [sepConj_comm] at good
      exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
    | second =>
      change (_ ∗ _) σ at good
      rw [sepConj_comm] at good
      exact act_wellFormed wellFormed _ (lsafe_base_safe act_local good) step
  | leftAcquire => exact wellFormed
  | rightAcquire => exact wellFormed
  | leftRelease => exact wellFormed
  | rightRelease => exact wellFormed

theorem lockGood_wellFormed_of_reaches {α β : Type} {I : Heap L → Prop}
    {Q₁ : α → Heap L → Prop} {Q₂ : β → Heap L → Prop} {c₁ c₁' : LProg (Op V) Op.Ret α}
    {c₂ c₂' : LProg (Op V) Op.Ret β} {l l' : LockState} {σ σ' : Heap L}
    (good : LockGood act I Q₁ Q₂ c₁ c₂ l σ) (wellFormed : WellFormed σ)
    (reaches : LockReaches act c₁ c₂ l σ c₁' c₂' l' σ') :
    LockGood act I Q₁ Q₂ c₁' c₂' l' σ' ∧ WellFormed σ' := by
  induction reaches with
  | refl => exact ⟨good, wellFormed⟩
  | step step _ ih =>
    exact ih (lockGood_step act_local good step) (lockGood_wellFormed_step good wellFormed step)

/-- Two threads' parts in a separating conjunction of three: they are separate,
and with the rest they make up the state. -/
theorem parts_of_sepConj₃ {A B C : Heap L → Prop} {σ : Heap L} (holds : (A ∗ (B ∗ C)) σ) :
    ∃ x y ρ, x ## y ∧ (x + y) ## ρ ∧ σ = x + y + ρ ∧ A x ∧ B y := by
  obtain ⟨x, _, separate, rfl, holdsA, y, ρ, separate', rfl, holdsB, -⟩ := holds
  obtain ⟨apart, separateXY⟩ := SepAlgebra.separate_add_left separate' separate
  exact ⟨x, y, ρ, separateXY, apart, (SepAlgebra.add_assoc_of_separate separateXY apart).symm,
    holdsA, holdsB⟩

theorem parts_of_sepConj₂ {A B : Heap L → Prop} {σ : Heap L} (holds : (A ∗ B) σ) :
    ∃ x y ρ, x ## y ∧ (x + y) ## ρ ∧ σ = x + y + ρ ∧ A x ∧ B y := by
  obtain ⟨x, y, separate, rfl, holdsA, holdsB⟩ := holds
  exact ⟨x, y, 0, separate, SepAlgebra.separate_zero _, (SepAlgebra.add_zero _).symm,
    holdsA, holdsB⟩

/-- **Threads that share only through the lock never race.**  In every
configuration that some interleaving reaches from `P₁ ∗ P₂ ∗ I` on well-formed
memory, the next base primitives of the two threads do not race. -/
theorem lock_race_free {α β : Type} {I : Heap L → Prop} {P₁ P₂ : Heap L → Prop}
    {c₁ : LProg (Op V) Op.Ret α} {c₂ : LProg (Op V) Op.Ret β} {Q₁ : α → Heap L → Prop}
    {Q₂ : β → Heap L → Prop} (safe₁ : P₁ ≤ LSafe act I Q₁ c₁ false)
    (safe₂ : P₂ ≤ LSafe act I Q₂ c₂ false) {σ : Heap L} (holds : (P₁ ∗ (P₂ ∗ I)) σ)
    (wellFormed : WellFormed σ) {c₁' : LProg (Op V) Op.Ret α} {c₂' : LProg (Op V) Op.Ret β}
    {l : LockState} {σ' : Heap L} (reaches : LockReaches act c₁ c₂ .free σ c₁' c₂' l σ')
    {o₁ o₂ : Op V} (next₁ : nextBase c₁' = some o₁) (next₂ : nextBase c₂' = some o₂) :
    ¬ Race o₁ o₂ := by
  have good : LockGood act I Q₁ Q₂ c₁ c₂ .free σ :=
    sepConj_mono safe₁ (sepConj_mono safe₂ le_rfl) σ holds
  obtain ⟨good', wellFormed'⟩ := lockGood_wellFormed_of_reaches good wellFormed reaches
  obtain ⟨x, y, ρ, separate, apart, rfl, safeX, safeY⟩ :
      ∃ x y ρ, x ## y ∧ (x + y) ## ρ ∧ σ' = x + y + ρ ∧
        LSafe act I Q₁ c₁' (l = .first) x ∧ LSafe act I Q₂ c₂' (l = .second) y := by
    cases l with
    | free => exact parts_of_sepConj₃ good'
    | first => exact parts_of_sepConj₂ good'
    | second => exact parts_of_sepConj₂ good'
  cases c₁' with
  | ret _ => cases next₁
  | call op k =>
    cases op with
    | acquire => cases next₁
    | release => cases next₁
    | base o =>
      cases c₂' with
      | ret _ => cases next₂
      | call op' k' =>
        cases op' with
        | acquire => cases next₂
        | release => cases next₂
        | base o' =>
          cases next₁
          cases next₂
          exact no_race separate apart wellFormed' safeX.1 safeY.1

/-! ## Examples -/

section Examples

/-- **Positive control**: the publisher's two appends can run in parallel when
the arrays are separate. -/
theorem parallel_appends (p q : Ptr) (n m : ℕ) (xs ys : List V) (v w : V)
    (roomP : xs.length < n) (roomQ : ys.length < m) :
    ParTriple (act (L := L)) (DynArray (some p) n xs ∗ DynArray (some q) m ys)
      (CProg.store (p + xs.length) v) (CProg.store (q + ys.length) w)
      (fun _ _ => DynArray (some p) n (xs ++ [v]) ∗ DynArray (some q) m (ys ++ [w])) :=
  triple_par act_local (store_append p n xs v roomP) (store_append q m ys w roomQ)

/-- Two loads never race, even on one cell. -/
theorem loads_never_race (p q : Ptr) : ¬ Race (V := V) (.load p) (.load q) := by
  rintro ⟨_, w₁, w₂, ⟨-, rfl⟩, ⟨-, rfl⟩, writes⟩
  simp at writes

/-- **Positive control**: two threads read one cell in parallel, each through
half of the permission. -/
theorem parallel_shared_reads (p : Ptr) (v : V) :
    ParTriple (act (L := Frac (Option V))) (PointsTo p v) (CProg.load p) (CProg.load p)
      (fun a b σ => a = v ∧ b = v ∧ PointsTo p v σ) := by
  rw [pointsTo_eq_halves]
  intro σ holds
  have par := triple_par act_local (load_half p v) (load_half p v) σ holds
  refine ⟨par.1, fun a b σ' runs => ?_⟩
  obtain ⟨x, y, separate, rfl, ⟨readA, holdsX⟩, ⟨readB, holdsY⟩⟩ := par.2 a b σ' runs
  exact ⟨readA, readB, x, y, separate, rfl, holdsX, holdsY⟩

/-- **Negative control**: freeing a block while another thread loads from it
faults in some interleaving. -/
theorem free_races_with_load (b : BlockId) (v : V) :
    ParFaults (act (L := L)) (CProg.free (V := V) (some ⟨b, 0⟩)) (CProg.load (V := V) ⟨b, 0⟩)
      (atBlock b (.own ⟨1, true⟩, segment 0 [whole (some v)])) := by
  refine ParFaults.step (ParStep.left (r := ()) ⟨1, by simp, rfl⟩) (ParFaults.right ?_)
  rintro ⟨w, readW⟩
  simp only [Heap.kill, Function.update_self, Heap.killedBlock, if_pos Nat.zero_lt_one,
    read_zero] at readW
  cases readW

end Examples

section Counter

variable {L : Type u} [Zero L] [Add L] [SepAlgebra L] [CellPermission L (Option CVal)]

/-- `(*c)++` on a `uint32_t` counter. -/
def increment (c : Ptr) : CProg CVal Unit :=
  CProg.loadU32 c >>= fun n => CProg.store c (.u32 (n + 1))

/-- The counter cell, with whatever value it holds. -/
def Counter (c : Ptr) : Heap L → Prop := fun σ => ∃ n : UInt32, PointsTo c (CVal.u32 n) σ

theorem pointsTo_read {p : Ptr} {v : CVal} {σ : Heap L} (holds : PointsTo p v σ) :
    read ((σ p.block).2 p.offset) = some (some v) := by
  have framed : (PointsTo (L := L) p v ∗ emp) σ := by
    rw [sepConj_emp]
    exact holds
  exact read_of_pointsTo framed

theorem increment_spec (c : Ptr) :
    CTriple (L := L) (Counter c) (increment c) (fun _ => Counter c) := by
  apply triple_exists
  intro n
  unfold increment
  simp only [Prog.bind_eq]
  refine triple_bind _ (loadU32_rule (n := n) fun σ holds => pointsTo_read holds) fun m => ?_
  apply triple_pure
  intro same
  subst same
  exact triple_post _ (triple_pre _ (fun σ holds => ⟨_, holds⟩)
    (store_spec c (CVal.u32 (m + 1)))) fun _ σ holds => ⟨_, holds⟩

/-- **Positive control: a counter shared through the lock.**  Two threads each
increment the counter inside the lock: no interleaving faults, every complete
interleaving leaves a counter, and no reachable configuration has a race. -/
theorem locked_counter_race_free (c : Ptr) (σ : Heap L) (holds : Counter c σ)
    (wellFormed : WellFormed σ) :
    ¬ LockFaults act (LProg.withLock (increment c)) (LProg.withLock (increment c)) .free σ ∧
      (∀ σ', LockRuns act (LProg.withLock (increment c)) (LProg.withLock (increment c))
        .free σ () () σ' → Counter c σ') ∧
      ∀ (c₁ c₂ : LProg (Op CVal) Op.Ret Unit) (l : LockState) (σ' : Heap L) (o₁ o₂ : Op CVal),
        LockReaches act (LProg.withLock (increment c)) (LProg.withLock (increment c)) .free σ
          c₁ c₂ l σ' → nextBase c₁ = some o₁ → nextBase c₂ = some o₂ → ¬ Race o₁ o₂ := by
  have critical : Triple (act (L := L)) (emp ∗ Counter c) (increment c)
      (fun _ => emp ∗ Counter c) := by
    rw [emp_sepConj]
    simpa only [emp_sepConj] using increment_spec (L := L) c
  have safe : emp ≤ LSafe act (Counter c) (fun _ => emp) (LProg.withLock (increment c)) false :=
    lsafe_withLock critical
  have start : (emp ∗ (emp ∗ Counter c)) σ := by
    rw [emp_sepConj, emp_sepConj]
    exact holds
  obtain ⟨noFaults, runs⟩ := lock_par act_local safe safe σ start
  refine ⟨noFaults, fun σ' run => ?_, fun c₁ c₂ l σ' o₁ o₂ reaches next₁ next₂ =>
    lock_race_free safe safe start wellFormed reaches next₁ next₂⟩
  have final := runs () () σ' run
  rwa [emp_sepConj, emp_sepConj] at final

/-- **Negative control**: two threads cannot each hold the counter, so the
disjoint rule does not apply to unsynchronized increments. -/
theorem shared_counter_unsplittable (c : Ptr) (σ : Heap L) :
    ¬ (Counter c ∗ Counter c) σ := by
  rintro ⟨x, y, separate, rfl, ⟨n, holdsX⟩, ⟨m, holdsY⟩⟩
  exact pointsTo_sepConj_self_false c (CVal.u32 n) (CVal.u32 m) (x + y)
    ⟨x, y, separate, rfl, holdsX, holdsY⟩

/-- The memory of one counter cell holding `n`. -/
def counterMemory (c : Ptr) (n : UInt32) : Heap L :=
  atBlock c.block (.empty, segment c.offset [whole (some (CVal.u32 n))])

theorem counterMemory_pointsTo (c : Ptr) (n : UInt32) :
    PointsTo c (CVal.u32 n) (counterMemory (L := L) c n) := rfl

/-- **Negative control: unsynchronized increments lose an update.**  Both
threads load `0` before either stores, and the counter ends at `1`. -/
theorem unsynchronized_increments_lose_an_update (c : Ptr) :
    ∃ σ', ParRuns (act (L := L)) (increment c) (increment c) (counterMemory c 0) () () σ' ∧
      PointsTo c (CVal.u32 1) σ' := by
  have read0 := pointsTo_read (counterMemory_pointsTo (L := L) c 0)
  have stored : ∀ σ : Heap L, PointsToAny c σ →
      PointsTo c (CVal.u32 1) (σ.setCell c (whole (some (CVal.u32 1)))) := fun σ holds =>
    (store_spec (L := L) c (CVal.u32 1) σ holds).2 () _
      (prim_runs (o := .store c (CVal.u32 1)) rfl)
  refine ⟨_, ParRuns.step (ParStep.left (r := CVal.u32 0) ⟨read0, rfl⟩)
    (ParRuns.step (ParStep.right (r := CVal.u32 0) ⟨read0, rfl⟩)
      (ParRuns.step (ParStep.left (o := Op.store c (CVal.u32 1)) (r := ()) rfl)
        (ParRuns.step (ParStep.right (o := Op.store c (CVal.u32 1)) (r := ()) rfl)
          ParRuns.done))), ?_⟩
  exact stored _ ⟨_, stored _ ⟨_, counterMemory_pointsTo c 0⟩⟩

end Counter

end Mettapedia.Machines.CMemory.Concurrency
