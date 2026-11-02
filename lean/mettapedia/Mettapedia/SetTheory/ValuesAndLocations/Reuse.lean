import Mettapedia.SetTheory.ValuesAndLocations.Readings
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Basic

/-!
# Values held in cells: an update may be done in place exactly when no one else can see it

The value reading (`Readings`) says that `$a` goes on denoting `{a b}` after `insert c $a` is
computed. A runtime keeps values in cells and hands out references to them. This module proves
when it may compute `insert c` by writing over the old cell instead of filling a new one.

## The model

* A **root** is anything that holds a reference: a name in scope, an occurrence in a space, the
  continuation of a step (`StepReuse` takes the roots to be `O ⊕ K`).
* A **heap** (`Heap`) gives each root a reference to a cell (`ref`) and each cell a value
  (`cell`). A root denotes the value of its cell (`Heap.denote`).
* The **value semantics** of an update (`Env.apply`): the root `r` now denotes `f` of its value,
  and every other root denotes what it did.
* Two ways to carry it out: write `f v` over the cell of `r` (`writeInPlace`), or put `f v` in a
  fresh cell and point `r` at it (`writeCopy`).

## One update

* `writeCopy_refines`: a copy always carries out the value semantics.
* `writeInPlace_refines_iff` (headline): writing in place carries it out **exactly when** every
  other root that references the cell would see no change, `f v = v`.
* `writeInPlace_refines_iff_unobserved`: for an update that changes every value, such as adding to
  a bag (`bag_cons_ne_self`), exactly when no other root references the cell (`Observed`); with
  finitely many roots that is a reference count of one (`unobserved_iff_rc_eq_one`).
* For sets, `insert x` changes a set exactly when `x` is not a member, so an add of a member may be
  done in place even when the set is shared (`setInsert_inPlace_iff`).
* **Counterexample** (`Controls.shared_inPlace_wrong`): two roots reference the cell of `{1 2}`;
  writing `insert 3` in place makes the second root see `{1 2 3}`.

## Programs

A small language of updates (`Instr`): `share` (a second name for a value), `drop` (a name goes
out of scope), `apply dst src f` (compute `f` of `src` into `dst`; `src` is used up) and
`applyKeep dst src f` (the same, with `src` still in scope). Its value semantics is `Instr.eval`.
The implementation (`Machine.step`) allocates cells from a counter. On `apply` it reuses the cell of
`src` when no root other than `src` and `dst` references it: Ullrich and de Moura's `reset`/`reuse`
(Counting Immutable Beans, 2019: rules Reset-Uniq and Reset-Shared) and Perceus's `drop-reuse`
(Reinking, Xie, de Moura and Leijen, 2021), with the reference count computed from the roots.
Otherwise, and always on `applyKeep`, it copies.

* `Machine.run_refines`: for every program, the implementation's heap denotes what the value
  semantics computes.
* `Machine.repeat_inPlace`: a name that alone holds its set, updated `n` times, is updated in place
  each time: no cell is allocated. This is "functional but in place".
* Without the test the implementation is wrong (`Controls.unguarded_wrong`), and so is `applyKeep`
  done in place (`Controls.keep_inPlace_wrong`): its source is still in scope and sees the change.

The model leaves out cells that reference cells; with them an observer is any root from which the
cell can be reached, and `Persistent` treats the structure-sharing case.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ValuesAndLocations.Reuse

universe u v w

/-- The value semantics: what each root denotes (`none`: it holds nothing). -/
abbrev Env (Root : Type u) (V : Type w) := Root → Option V

/-- **The value semantics of an update**: `r` now denotes `f` of its value; every other root
denotes what it did. -/
def Env.apply {Root : Type u} {V : Type w} [DecidableEq Root] (ρ : Env Root V) (r : Root)
    (f : V → V) : Env Root V :=
  Function.update ρ r ((ρ r).map f)

/-- A heap: each root's reference and each cell's value. -/
structure Heap (Root : Type u) (Ptr : Type v) (V : Type w) where
  ref : Root → Option Ptr
  cell : Ptr → Option V

namespace Heap

variable {Root : Type u} {Ptr : Type v} {V : Type w}

/-- What each root denotes through the heap. -/
def denote (h : Heap Root Ptr V) : Env Root V := fun r => (h.ref r).bind h.cell

@[simp] theorem denote_apply (h : Heap Root Ptr V) (r : Root) : h.denote r = (h.ref r).bind h.cell :=
  rfl

/-- **An observer of the old version**: another root references the cell of `r`, and that cell
holds a value. -/
def Observed (h : Heap Root Ptr V) (r : Root) : Prop :=
  ∃ r', r' ≠ r ∧ ∃ p v, h.ref r = some p ∧ h.ref r' = some p ∧ h.cell p = some v

/-- `q` is fresh: no root references it. -/
def Fresh (h : Heap Root Ptr V) (q : Ptr) : Prop := ∀ r, h.ref r ≠ some q

/-- The number of roots that reference `p`. -/
def rc [Fintype Root] (h : Heap Root Ptr V) (p : Ptr) [DecidableEq Ptr] : ℕ :=
  (Finset.univ.filter fun r => h.ref r = some p).card

variable [DecidableEq Ptr]

/-- A write to a cell that a reference does not name leaves what the reference denotes. -/
theorem bind_update_of_ne {x : Option Ptr} {cell : Ptr → Option V} {q : Ptr} {w : Option V}
    (apart : x ≠ some q) : x.bind (Function.update cell q w) = x.bind cell := by
  cases x with
  | none => rfl
  | some p =>
      have : p ≠ q := fun e => apart (e ▸ rfl)
      simp [Function.update_of_ne this]

/-- **Update in place**: write `f v` over the cell of `r`. -/
def writeInPlace (h : Heap Root Ptr V) (r : Root) (f : V → V) : Heap Root Ptr V :=
  match h.ref r with
  | some p => ⟨h.ref, Function.update h.cell p ((h.cell p).map f)⟩
  | none => h

variable [DecidableEq Root]

/-- **Update by copy**: put `f v` in the cell `q` and point `r` at it. -/
def writeCopy (h : Heap Root Ptr V) (r : Root) (f : V → V) (q : Ptr) : Heap Root Ptr V :=
  ⟨Function.update h.ref r (some q), Function.update h.cell q ((h.denote r).map f)⟩

/-- **A copy into a fresh cell carries out the value semantics.** -/
theorem writeCopy_refines (h : Heap Root Ptr V) (r : Root) (f : V → V) {q : Ptr}
    (fresh : h.Fresh q) : (h.writeCopy r f q).denote = h.denote.apply r f := by
  funext r'
  by_cases same : r' = r
  · subst same
    simp [writeCopy, denote, Env.apply]
  · simp only [writeCopy, denote, Env.apply, Function.update_of_ne same]
    cases hr : h.ref r' with
    | none => rfl
    | some p =>
        have apart : p ≠ q := fun e => fresh r' (e ▸ hr)
        simp [Function.update_of_ne apart]

/-- **Writing in place carries out the value semantics exactly when every other root that
references the cell would see no change.** -/
theorem writeInPlace_refines_iff (h : Heap Root Ptr V) (r : Root) (f : V → V) :
    (h.writeInPlace r f).denote = h.denote.apply r f ↔
      ∀ r', r' ≠ r → ∀ p v, h.ref r = some p → h.ref r' = some p → h.cell p = some v →
        f v = v := by
  cases hr : h.ref r with
  | none =>
      simp only [writeInPlace, hr]
      constructor
      · intro _ r' _ p v hp
        cases hp
      · intro _
        funext r'
        by_cases same : r' = r
        · subst same
          simp [Env.apply, denote, hr]
        · simp [Env.apply, Function.update_of_ne same]
  | some p =>
      simp only [writeInPlace, hr]
      constructor
      · intro eq r' ne p' v hp' hr' hv
        obtain rfl := Option.some.inj hp'
        have := congrFun eq r'
        simp only [denote, Env.apply, Function.update_of_ne ne, hr', Option.bind_some,
          Function.update_self, hv, Option.map_some, Option.some.injEq] at this
        exact this
      · intro fixes
        funext r'
        by_cases same : r' = r
        · subst same
          simp [denote, Env.apply, hr]
        · simp only [denote, Env.apply, Function.update_of_ne same]
          cases hr' : h.ref r' with
          | none => rfl
          | some p' =>
              by_cases pp : p' = p
              · subst pp
                cases hv : h.cell p' with
                | none => simp [hv]
                | some v => simp [hv, fixes r' same p' v rfl hr' hv]
              · simp [Function.update_of_ne pp]

/-- **For an update that changes every value, writing in place is right exactly when no other root
references the cell.** -/
theorem writeInPlace_refines_iff_unobserved (h : Heap Root Ptr V) (r : Root) {f : V → V}
    (moves : ∀ v, f v ≠ v) :
    (h.writeInPlace r f).denote = h.denote.apply r f ↔ ¬ h.Observed r := by
  rw [writeInPlace_refines_iff]
  constructor
  · rintro fixes ⟨r', ne, p, v, hp, hr', hv⟩
    exact moves v (fixes r' ne p v hp hr' hv)
  · intro unobserved r' ne p v hp hr' hv
    exact absurd ⟨r', ne, p, v, hp, hr', hv⟩ unobserved

/-- **Adding to a bag in place is right exactly when no other root references the cell.** -/
theorem bagCons_inPlace_iff {A : Type w} (h : Heap Root Ptr (Multiset A)) (r : Root) (x : A) :
    (h.writeInPlace r (x ::ₘ ·)).denote = h.denote.apply r (x ::ₘ ·) ↔ ¬ h.Observed r :=
  writeInPlace_refines_iff_unobserved h r (bag_cons_ne_self x)

/-- **Adding to a set in place is right exactly when the element is a member already or no other
root references the cell.** -/
theorem setInsert_inPlace_iff {A : Type w} [DecidableEq A] (h : Heap Root Ptr (Finset A))
    (r : Root) (x : A) {p : Ptr} {s : Finset A} (hp : h.ref r = some p) (hs : h.cell p = some s) :
    (h.writeInPlace r (insert x)).denote = h.denote.apply r (insert x) ↔
      x ∈ s ∨ ¬ h.Observed r := by
  rw [writeInPlace_refines_iff]
  constructor
  · intro fixes
    by_cases observed : h.Observed r
    · obtain ⟨r', ne, p', v, hp', hr', hv⟩ := observed
      obtain rfl := Option.some.inj (hp.symm.trans hp')
      obtain rfl := Option.some.inj (hs.symm.trans hv)
      exact Or.inl (Finset.insert_eq_self.mp (fixes r' ne p s hp hr' hs))
    · exact Or.inr observed
  · rintro (member | unobserved) r' ne p' v hp' hr' hv
    · obtain rfl := Option.some.inj (hp.symm.trans hp')
      obtain rfl := Option.some.inj (hs.symm.trans hv)
      exact Finset.insert_eq_self.mpr member
    · exact absurd ⟨r', ne, p', v, hp', hr', hv⟩ unobserved

/-- **A reference count of one is the absence of other observers**, for a cell that holds a
value. -/
theorem unobserved_iff_rc_eq_one [Fintype Root] (h : Heap Root Ptr V) {r : Root} {p : Ptr}
    {v : V} (hp : h.ref r = some p) (hv : h.cell p = some v) :
    ¬ h.Observed r ↔ h.rc p = 1 := by
  unfold rc
  rw [Finset.card_eq_one]
  constructor
  · intro unobserved
    refine ⟨r, Finset.ext fun r' => ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hr'
      by_contra ne
      exact unobserved ⟨r', ne, p, v, hp, hr', hv⟩
    · rintro rfl
      exact hp
  · rintro ⟨a, ha⟩ ⟨r', ne, p', v', hp', hr', -⟩
    obtain rfl := Option.some.inj (hp.symm.trans hp')
    have memR : r ∈ Finset.univ.filter fun x => h.ref x = some p := by simp [hp]
    have memR' : r' ∈ Finset.univ.filter fun x => h.ref x = some p := by simp [hr']
    rw [ha, Finset.mem_singleton] at memR memR'
    exact ne (memR'.trans memR.symm)

end Heap

/-! ## Programs -/

/-- Instructions over values. -/
inductive Instr (Root : Type u) (V : Type w) where
  /-- `dst` is a second name for the value of `src`. -/
  | share (dst src : Root)
  /-- `r` goes out of scope. -/
  | drop (r : Root)
  /-- `dst` gets `f` of the value of `src`; `src` is used up. -/
  | apply (dst src : Root) (f : V → V)
  /-- `dst` gets `f` of the value of `src`; `src` stays in scope. -/
  | applyKeep (dst src : Root) (f : V → V)

section Programs

variable {Root : Type u} {V : Type w} [DecidableEq Root]

/-- **The value semantics of an instruction.** -/
def Instr.eval : Instr Root V → Env Root V → Env Root V
  | .share dst src, ρ => Function.update ρ dst (ρ src)
  | .drop r, ρ => Function.update ρ r none
  | .apply dst src f, ρ => Function.update (Function.update ρ src none) dst ((ρ src).map f)
  | .applyKeep dst src f, ρ => Function.update ρ dst ((ρ src).map f)

/-- The value semantics of a program. -/
def evalList : List (Instr Root V) → Env Root V → Env Root V
  | [], ρ => ρ
  | i :: is, ρ => evalList is (i.eval ρ)

/-- The implementation: a heap over the pointers `ℕ`, and the next pointer to allocate. -/
structure Machine (Root : Type u) (V : Type w) where
  heap : Heap Root ℕ V
  next : ℕ

namespace Machine

/-- No root references a pointer at or above `next`. -/
def Bounded (m : Machine Root V) : Prop := ∀ r p, m.heap.ref r = some p → p < m.next

variable [Fintype Root]

/-- Some root other than `src` and `dst` references `p`: the test of `reset`, computed from the
roots. -/
def othersRef (m : Machine Root V) (src dst : Root) (p : ℕ) : Bool :=
  decide (∃ r, r ≠ src ∧ r ≠ dst ∧ m.heap.ref r = some p)

/-- **One step of the implementation.** `apply` reuses the cell of `src` when no other root
references it, and copies otherwise; `applyKeep` copies. -/
def step (m : Machine Root V) : Instr Root V → Machine Root V
  | .share dst src => ⟨⟨Function.update m.heap.ref dst (m.heap.ref src), m.heap.cell⟩, m.next⟩
  | .drop r => ⟨⟨Function.update m.heap.ref r none, m.heap.cell⟩, m.next⟩
  | .apply dst src f =>
      match m.heap.ref src with
      | none => ⟨⟨Function.update (Function.update m.heap.ref src none) dst none, m.heap.cell⟩,
          m.next⟩
      | some p =>
          if m.othersRef src dst p then
            ⟨⟨Function.update (Function.update m.heap.ref src none) dst (some m.next),
              Function.update m.heap.cell m.next ((m.heap.cell p).map f)⟩, m.next + 1⟩
          else
            ⟨⟨Function.update (Function.update m.heap.ref src none) dst (some p),
              Function.update m.heap.cell p ((m.heap.cell p).map f)⟩, m.next⟩
  | .applyKeep dst src f =>
      match m.heap.ref src with
      | none => ⟨⟨Function.update m.heap.ref dst none, m.heap.cell⟩, m.next⟩
      | some p =>
          ⟨⟨Function.update m.heap.ref dst (some m.next),
            Function.update m.heap.cell m.next ((m.heap.cell p).map f)⟩, m.next + 1⟩

/-- Run a program. -/
def run (m : Machine Root V) : List (Instr Root V) → Machine Root V
  | [] => m
  | i :: is => (m.step i).run is

theorem othersRef_false {m : Machine Root V} {src dst : Root} {p : ℕ}
    (no : m.othersRef src dst p = false) :
    ∀ r, r ≠ src → r ≠ dst → m.heap.ref r ≠ some p := by
  intro r hs hd hr
  have : m.othersRef src dst p = true := decide_eq_true ⟨r, hs, hd, hr⟩
  rw [no] at this
  cases this

omit [Fintype Root] in
/-- What a heap denotes after `dst` gets the reference `x` and `src` is used up. -/
theorem denote_moved (ref : Root → Option ℕ) (cell : ℕ → Option V) (dst src : Root)
    (x : Option ℕ) (r : Root) :
    (Heap.mk (Function.update (Function.update ref src none) dst x) cell).denote r =
      if r = dst then x.bind cell else if r = src then none else (ref r).bind cell := by
  unfold Heap.denote
  by_cases d : r = dst
  · subst d
    simp
  · by_cases s : r = src
    · subst s
      simp [d]
    · simp [d, s]

omit [Fintype Root] in
/-- The value semantics of `apply`, root by root. -/
theorem eval_apply (ρ : Env Root V) (dst src : Root) (f : V → V) (r : Root) :
    (Instr.apply dst src f).eval ρ r =
      if r = dst then (ρ src).map f else if r = src then none else ρ r := by
  unfold Instr.eval
  by_cases d : r = dst
  · subst d
    simp
  · by_cases s : r = src
    · subst s
      simp [d]
    · simp [d, s]

omit [Fintype Root] in
/-- Where a moved reference points. -/
theorem ref_moved {ref : Root → Option ℕ} {dst src r : Root} {x : Option ℕ} {p : ℕ}
    (hr : Function.update (Function.update ref src none) dst x r = some p) :
    (r = dst ∧ x = some p) ∨ (r ≠ dst ∧ r ≠ src ∧ ref r = some p) := by
  by_cases d : r = dst
  · subst d
    rw [Function.update_self] at hr
    exact Or.inl ⟨rfl, hr⟩
  · rw [Function.update_of_ne d] at hr
    by_cases s : r = src
    · subst s
      rw [Function.update_self] at hr
      cases hr
    · rw [Function.update_of_ne s] at hr
      exact Or.inr ⟨d, s, hr⟩

/-- **One step refines the value semantics, and keeps the heap bounded.** -/
theorem step_refines (m : Machine Root V) (bounded : m.Bounded) (i : Instr Root V) :
    (m.step i).heap.denote = i.eval m.heap.denote ∧ (m.step i).Bounded := by
  have fresh : ∀ r, m.heap.ref r ≠ some m.next := fun r h => lt_irrefl _ (bounded r _ h)
  cases i with
  | share dst src =>
      refine ⟨funext fun r => ?_, fun r p hr => ?_⟩
      · simp only [step, Instr.eval, Heap.denote]
        by_cases d : r = dst
        · subst d
          simp
        · simp [Function.update_of_ne d]
      · simp only [step] at hr ⊢
        by_cases d : r = dst
        · subst d
          rw [Function.update_self] at hr
          exact bounded src p hr
        · rw [Function.update_of_ne d] at hr
          exact bounded r p hr
  | drop x =>
      refine ⟨funext fun r => ?_, fun r p hr => ?_⟩
      · simp only [step, Instr.eval, Heap.denote]
        by_cases d : r = x
        · subst d
          simp
        · simp [Function.update_of_ne d]
      · simp only [step] at hr ⊢
        by_cases d : r = x
        · subst d
          rw [Function.update_self] at hr
          cases hr
        · rw [Function.update_of_ne d] at hr
          exact bounded r p hr
  | apply dst src f =>
      cases hsrc : m.heap.ref src with
      | none =>
          have e : m.step (.apply dst src f) =
              ⟨⟨Function.update (Function.update m.heap.ref src none) dst none, m.heap.cell⟩,
                m.next⟩ := by
            simp [step, hsrc]
          rw [e]
          refine ⟨funext fun r => ?_, fun r p hr => ?_⟩
          · rw [denote_moved, eval_apply]
            split_ifs
            · simp [Heap.denote, hsrc]
            · rfl
            · rfl
          · rcases ref_moved hr with ⟨-, h⟩ | ⟨-, -, h⟩
            · cases h
            · exact bounded r p h
      | some p =>
          have pBound : p < m.next := bounded src p hsrc
          cases others : m.othersRef src dst p with
          | true =>
              have e : m.step (.apply dst src f) =
                  ⟨⟨Function.update (Function.update m.heap.ref src none) dst (some m.next),
                    Function.update m.heap.cell m.next ((m.heap.cell p).map f)⟩, m.next + 1⟩ := by
                simp [step, hsrc, others]
              rw [e]
              refine ⟨funext fun r => ?_, fun r q hr => ?_⟩
              · rw [denote_moved, eval_apply]
                split_ifs
                · simp [Heap.denote, hsrc]
                · rfl
                · rw [Heap.bind_update_of_ne (fresh r)]
                  rfl
              · rcases ref_moved hr with ⟨-, h⟩ | ⟨-, -, h⟩
                · obtain rfl := Option.some.inj h
                  exact Nat.lt_succ_self _
                · exact Nat.lt_succ_of_lt (bounded r q h)
          | false =>
              have alone := othersRef_false others
              have e : m.step (.apply dst src f) =
                  ⟨⟨Function.update (Function.update m.heap.ref src none) dst (some p),
                    Function.update m.heap.cell p ((m.heap.cell p).map f)⟩, m.next⟩ := by
                simp [step, hsrc, others]
              rw [e]
              refine ⟨funext fun r => ?_, fun r q hr => ?_⟩
              · rw [denote_moved, eval_apply]
                split_ifs with d s
                · simp [Heap.denote, hsrc]
                · rfl
                · rw [Heap.bind_update_of_ne (alone r s d)]
                  rfl
              · rcases ref_moved hr with ⟨-, h⟩ | ⟨-, -, h⟩
                · obtain rfl := Option.some.inj h
                  exact pBound
                · exact bounded r q h
  | applyKeep dst src f =>
      cases hsrc : m.heap.ref src with
      | none =>
          have e : m.step (.applyKeep dst src f) =
              ⟨⟨Function.update m.heap.ref dst none, m.heap.cell⟩, m.next⟩ := by
            simp [step, hsrc]
          rw [e]
          refine ⟨funext fun r => ?_, fun r p hr => ?_⟩
          · simp only [Instr.eval, Heap.denote]
            by_cases d : r = dst
            · subst d
              simp [hsrc]
            · simp [Function.update_of_ne d]
          · by_cases d : r = dst
            · subst d
              simp at hr
            · simp only [Function.update_of_ne d] at hr
              exact bounded r p hr
      | some p =>
          have e : m.step (.applyKeep dst src f) =
              ⟨⟨Function.update m.heap.ref dst (some m.next),
                Function.update m.heap.cell m.next ((m.heap.cell p).map f)⟩, m.next + 1⟩ := by
            simp [step, hsrc]
          rw [e]
          refine ⟨funext fun r => ?_, fun r q hr => ?_⟩
          · simp only [Instr.eval, Heap.denote]
            by_cases d : r = dst
            · subst d
              simp [hsrc]
            · simp only [Function.update_of_ne d]
              exact Heap.bind_update_of_ne (fresh r)
          · by_cases d : r = dst
            · subst d
              simp only [Function.update_self, Option.some.injEq] at hr
              subst hr
              exact Nat.lt_succ_self _
            · simp only [Function.update_of_ne d] at hr
              exact Nat.lt_succ_of_lt (bounded r q hr)

/-- **The refinement theorem.** For every program, the implementation, which updates in place
exactly when no other root references the cell, ends with a heap that denotes what the value
semantics computes. -/
theorem run_refines (m : Machine Root V) (bounded : m.Bounded) (prog : List (Instr Root V)) :
    (m.run prog).heap.denote = evalList prog m.heap.denote := by
  induction prog generalizing m with
  | nil => rfl
  | cons i rest ih =>
      obtain ⟨refines, bounded'⟩ := m.step_refines bounded i
      simp only [run, evalList]
      rw [ih (m.step i) bounded', refines]

/-- **Functional but in place.** If `a` alone references its cell `p`, then updating `a` from itself
`n` times reuses `p` every time: nothing is allocated, and `p` holds `f` applied `n` times. -/
theorem repeat_inPlace (m : Machine Root V) (a : Root) (f : V → V) {p : ℕ}
    (ha : m.heap.ref a = some p) (alone : ∀ r, r ≠ a → m.heap.ref r ≠ some p) (n : ℕ) :
    (m.run (List.replicate n (.apply a a f))).next = m.next ∧
      (m.run (List.replicate n (.apply a a f))).heap.ref = m.heap.ref ∧
      (m.run (List.replicate n (.apply a a f))).heap.cell p = (m.heap.cell p).map f^[n] := by
  induction n generalizing m with
  | zero => simp [run]
  | succ n ih =>
      have others : m.othersRef a a p = false := by
        unfold othersRef
        exact decide_eq_false fun ⟨r, ne, _, hr⟩ => alone r ne hr
      have refEq : (m.step (.apply a a f)).heap.ref = m.heap.ref := by
        funext r
        simp only [step, ha, others, Bool.false_eq_true, if_false]
        by_cases same : r = a
        · subst same
          simp [ha]
        · simp [Function.update_of_ne same]
      have nextEq : (m.step (.apply a a f)).next = m.next := by
        simp [step, ha, others]
      have cellEq : (m.step (.apply a a f)).heap.cell p = (m.heap.cell p).map f := by
        simp [step, ha, others]
      have ha' : (m.step (.apply a a f)).heap.ref a = some p := by rw [refEq]; exact ha
      have alone' : ∀ r, r ≠ a → (m.step (.apply a a f)).heap.ref r ≠ some p := by
        rw [refEq]; exact alone
      obtain ⟨n₁, r₁, c₁⟩ := ih (m.step (.apply a a f)) ha' alone'
      refine ⟨?_, ?_, ?_⟩
      · rw [List.replicate_succ, run, n₁, nextEq]
      · rw [List.replicate_succ, run, r₁, refEq]
      · rw [List.replicate_succ, run, c₁, cellEq, Option.map_map, ← Function.iterate_succ]

end Machine

end Programs

/-! ## Controls -/

namespace Controls

open Heap

/-- Two roots, `true` (`$a`) and `false` (`$b`), both referencing cell `0`, which holds `{1 2}`. -/
def sharedPair : Heap Bool ℕ (Multiset ℕ) := ⟨fun _ => some 0, fun p => if p = 0 then some {1, 2} else none⟩

/-- **Counterexample: in place under sharing.** Writing `insert 3` over the shared cell makes
`$b`, which the value semantics leaves at `{1 2}`, see `{1 2 3}`. -/
theorem shared_inPlace_wrong :
    (sharedPair.writeInPlace true (3 ::ₘ ·)).denote false = some {3, 1, 2} ∧
      sharedPair.denote.apply true (3 ::ₘ ·) false = some {1, 2} := by
  refine ⟨by decide, ?_⟩
  simp [Env.apply, sharedPair, Heap.denote]

/-- **The same write with `$b` gone is right**: `$a` alone references the cell. -/
def alone : Heap Bool ℕ (Multiset ℕ) :=
  ⟨fun r => if r then some 0 else none, fun p => if p = 0 then some {1, 2} else none⟩

theorem alone_inPlace_right :
    (alone.writeInPlace true (3 ::ₘ ·)).denote = alone.denote.apply true (3 ::ₘ ·) := by
  refine (bagCons_inPlace_iff alone true 3).mpr ?_
  rintro ⟨r', ne, p, v, hp, hr', -⟩
  cases r'
  · simp [alone] at hr'
  · exact ne rfl

/-- **Sets: an add of a member may be done in place under sharing.** -/
theorem shared_set_member_inPlace :
    let h : Heap Bool ℕ (Finset ℕ) :=
      ⟨fun _ => some 0, fun p => if p = 0 then some {1, 2} else none⟩
    (h.writeInPlace true (insert 1)).denote = h.denote.apply true (insert 1) := by
  intro h
  exact (setInsert_inPlace_iff h true 1 (p := 0) (s := {1, 2}) rfl rfl).mpr (Or.inl (by decide))

/-- The program `share b a; apply a2 a (insert 3)`, over the roots `Fin 3` (`a`, `b`, `a2`). -/
def shareThenAdd : List (Instr (Fin 3) (Multiset ℕ)) := [.share 1 0, .apply 2 0 (3 ::ₘ ·)]

/-- `a` references cell `0`, which holds `{1 2}`; nothing else is allocated. -/
def start : Machine (Fin 3) (Multiset ℕ) :=
  ⟨⟨fun r => if r = 0 then some 0 else none, fun p => if p = 0 then some {1, 2} else none⟩, 1⟩

theorem start_bounded : start.Bounded := by
  intro r p hr
  simp only [start] at hr
  split_ifs at hr
  · obtain rfl := Option.some.inj hr
    exact Nat.zero_lt_one

/-- **The guarded machine copies here**, since `b` still references the cell, and `b` keeps
`{1 2}`; the value semantics agrees (`Machine.run_refines`). -/
theorem guarded_copies :
    (start.run shareThenAdd).next = 2 ∧ (start.run shareThenAdd).heap.denote 1 = some {1, 2} ∧
      (start.run shareThenAdd).heap.denote 2 = some {3, 1, 2} := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [Machine.run_refines start start_bounded]
    decide
  · rw [Machine.run_refines start start_bounded]
    decide

/-- **Counterexample: without the test.** The same program with `apply` always reusing the cell:
after `share b a`, writing over cell `0` makes `b` see `{1 2 3}`. -/
theorem unguarded_wrong :
    let afterShare := start.step (.share 1 0)
    (afterShare.heap.writeInPlace 0 (3 ::ₘ ·)).denote 1 = some {3, 1, 2} ∧
      evalList shareThenAdd start.heap.denote 1 = some {1, 2} := by
  refine ⟨by decide, by decide⟩

/-- **Counterexample: `applyKeep` in place.** `a2` gets `insert 3` of `a` while `a` stays in scope;
writing over `a`'s cell makes `a` itself see `{1 2 3}`, while the value semantics keeps `{1 2}`. -/
theorem keep_inPlace_wrong :
    (start.heap.writeInPlace 0 (3 ::ₘ ·)).denote 0 = some {3, 1, 2} ∧
      (Instr.applyKeep 2 0 (3 ::ₘ ·) : Instr (Fin 3) (Multiset ℕ)).eval start.heap.denote 0 =
        some {1, 2} := by
  refine ⟨by decide, by decide⟩

end Controls

end Mettapedia.SetTheory.ValuesAndLocations.Reuse
