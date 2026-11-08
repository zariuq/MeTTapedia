import Mettapedia.Logic.ASP.Solver

/-!
# Executable propagation with two watched literals

The solver's `propagate` rule applies any unit nogood of the database. This
module gives the executable propagation a solver runs, with two watched
literals per nogood, and proves that it refines the specification.

## Data

* `Watched`: a nogood and its two watched literals.
* `WState`: the trail (newest first), the watched nogoods, the watch index (for
  each literal, the identifiers of the nogoods watching it), and the literals
  pushed but not yet processed.
* For a nogood, "true" means on the trail; a literal is a good watch while it is
  not true. A nogood is satisfied when the complement of one of its literals is on
  the trail.

## The operation

`propagateWatched` takes a pending literal `x` and visits only the nogoods in the
watch list of `x` (`processList`). For each nogood watching `x`, with other watch
`o` (`visit`):

* if the complement of `o` is on the trail, the nogood is satisfied: keep it;
* else, if some literal other than `x` and `o` is not true, watch it instead of `x`;
* else, if `o` is true, every literal is true: a conflict;
* else the nogood is unit on `o`: push the complement of `o`, with the nogood as
  its reason, and keep watching.

## Results

* **The invariant** (`WInv`): every watched nogood has two distinct watched
  literals; the index lists each nogood under both of its watches; and every
  watched nogood is satisfied, or each of its true watches is pending. With no
  pending literal this is the fixpoint invariant: every nogood is satisfied or
  watched by two literals that are not true.
* **Refinement** (`propagateWatched_spec`): every literal the propagation pushes is
  a step of specification unit propagation (`UPStep`) by a nogood of the database;
  a reported conflict nogood is falsified; the invariant is kept.
* **Fixpoint** (`WInv.quiescent`): with nothing pending, no nogood is unit or
  falsified.
* **Same consequences** (`closure`): at such a fixpoint every literal that
  specification unit propagation derives from the starting trail is on the trail.
  So propagation by watches computes exactly the unit-propagation closure.
* **Solver steps** (`UPStep.solverStep`, `upSteps_solver`): specification unit
  propagation by database nogoods over program variables is a sequence of
  `propagate` steps of `Program.Step`.
* Decisions keep the invariant at a fixpoint (`WInv.decide`), and the initial
  watched database over an empty trail satisfies it (`WInv.init`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Relation

universe u

variable {A : Type u}

/-- A nogood with its two watched literals. -/
structure Watched (A : Type u) where
  nogood : Nogood A
  w1 : Lit A
  w2 : Lit A

/-- The state of watched propagation. -/
structure WState (A : Type u) where
  /-- The trail, newest first. -/
  trail : List (Entry A)
  /-- The watched nogoods, by identifier. -/
  db : List (Watched A)
  /-- The identifiers of the nogoods watching each literal. -/
  watches : Lit A → List ℕ
  /-- Literals pushed and not yet processed. -/
  pending : List (Lit A)

/-- The literals on the trail. -/
def WState.lits (st : WState A) : List (Lit A) := st.trail.map Entry.lit

/-- The state with trail `t` and nothing else, to read `Falsifies` and `UnitOn` on a trail. -/
def onTrail (t : List (Entry A)) : State A := ⟨t, [], 0⟩

/-- A nogood is satisfied by the literals `lits`: the complement of one of its literals is
among them. -/
def Satisfied (lits : List (Lit A)) (δ : Nogood A) : Prop := ∃ m ∈ δ.lits, m.compl ∈ lits

/-- **Unit propagation by the nogoods `Δ`**, the specification. -/
inductive UPStep (Δ : List (Nogood A)) : List (Entry A) → List (Entry A) → Prop
  | unit {t : List (Entry A)} {δ : Nogood A} {l : Lit A} : δ ∈ Δ → (onTrail t).UnitOn δ l →
      UPStep Δ t (⟨l.compl, levelOf t, some δ⟩ :: t)

theorem Lit.eq_or_eq_compl {l m : Lit A} (h : l.var = m.var) : l = m ∨ l = m.compl := by
  obtain ⟨x, b⟩ := l
  obtain ⟨y, c⟩ := m
  simp only at h
  subst h
  cases b <;> cases c <;> simp [Lit.compl]

theorem Lit.compl_ne (l : Lit A) : l.compl ≠ l := by
  obtain ⟨x, b⟩ := l
  cases b <;> simp [Lit.compl]

section Watches

variable [DecidableEq A]

/-- The other watch of a nogood visited for `x`. -/
def Watched.other (w : Watched A) (x : Lit A) : Lit A := if w.w1 = x then w.w2 else w.w1

/-- What visiting a watched nogood decides. -/
inductive Visit (A : Type u)
  | keep
  | move (r : Lit A)
  | unit
  | conflict

/-- Visit a nogood watching `x`, which has just become true. -/
def visit (lits : List (Lit A)) (x : Lit A) (w : Watched A) : Visit A :=
  if (w.other x).compl ∈ lits then .keep
  else
    match w.nogood.lits.find? (fun r => decide (r ≠ x ∧ r ≠ w.other x ∧ r ∉ lits)) with
    | some r => .move r
    | none => if w.other x ∈ lits then .conflict else .unit

/-- Watch `r` instead of `x` in the nogood `w` with identifier `i`. -/
def WState.move (st : WState A) (i : ℕ) (w : Watched A) (x r : Lit A) : WState A :=
  { st with
    db := st.db.set i ⟨w.nogood, w.other x, r⟩
    watches := Function.update st.watches r (i :: st.watches r) }

/-- Push the complement of the other watch of `w`, and make it pending. -/
def WState.pushUnit (st : WState A) (w : Watched A) (x : Lit A) : WState A :=
  { st with
    trail := ⟨(w.other x).compl, levelOf st.trail, some w.nogood⟩ :: st.trail
    pending := (w.other x).compl :: st.pending }

/-- The result of visiting a watch list. -/
inductive Pass (A : Type u)
  | ok (st : WState A)
  | conflict (δ : Nogood A) (st : WState A)

/-- **Visit the nogoods watching `x`**: `todo` the identifiers left, `kept` those staying in the
watch list of `x`. -/
def processList (x : Lit A) : WState A → List ℕ → List ℕ → Pass A
  | st, [], kept => .ok { st with watches := Function.update st.watches x kept }
  | st, i :: todo, kept =>
    match st.db[i]? with
    | none => processList x st todo kept
    | some w =>
      if w.w1 = x ∨ w.w2 = x then
        match visit st.lits x w with
        | .keep => processList x st todo (i :: kept)
        | .move r => processList x (st.move i w x r) todo kept
        | .unit => processList x (st.pushUnit w x) todo (i :: kept)
        | .conflict => .conflict w.nogood { st with watches := Function.update st.watches x (i :: todo ++ kept) }
      else processList x st todo kept

/-- The outcome of propagation. -/
inductive Outcome (A : Type u)
  | fixpoint (st : WState A)
  | conflict (δ : Nogood A) (st : WState A)
  | outOfFuel (st : WState A)

/-- **Propagation by watches**, processing at most `fuel` pending literals. -/
def propagateWatched : ℕ → WState A → Outcome A
  | 0, st => .outOfFuel st
  | fuel + 1, st =>
    match st.pending with
    | [] => .fixpoint st
    | x :: rest =>
      match processList x { st with pending := rest } (st.watches x) [] with
      | .ok st' => propagateWatched fuel st'
      | .conflict δ st' => .conflict δ st'

/-! ## The invariants -/

/-- **The watch invariant.** -/
structure WInv (Δ : List (Nogood A)) (st : WState A) : Prop where
  db : st.db.map Watched.nogood = Δ
  shape : ∀ w ∈ st.db, w.w1 ≠ w.w2 ∧ w.w1 ∈ w.nogood.lits ∧ w.w2 ∈ w.nogood.lits
  index : ∀ (i : ℕ) (w : Watched A), st.db[i]? = some w → i ∈ st.watches w.w1 ∧ i ∈ st.watches w.w2
  watch : ∀ (i : ℕ) (w : Watched A), st.db[i]? = some w → Satisfied st.lits w.nogood ∨
    ∀ y, (y = w.w1 ∨ y = w.w2) → y ∈ st.lits → y ∈ st.pending
  pending : ∀ y ∈ st.pending, y ∈ st.lits
  nodup : (st.trail.map fun e => e.lit.var).Nodup

/-- The invariant while the nogoods watching `x` are visited. -/
structure PInv (Δ : List (Nogood A)) (x : Lit A) (todo kept : List ℕ) (st : WState A) : Prop where
  db : st.db.map Watched.nogood = Δ
  shape : ∀ w ∈ st.db, w.w1 ≠ w.w2 ∧ w.w1 ∈ w.nogood.lits ∧ w.w2 ∈ w.nogood.lits
  index : ∀ (i : ℕ) (w : Watched A), st.db[i]? = some w → ∀ y, (y = w.w1 ∨ y = w.w2) →
    (y ≠ x → i ∈ st.watches y) ∧ (y = x → i ∈ todo ∨ i ∈ kept)
  watch : ∀ (i : ℕ) (w : Watched A), st.db[i]? = some w → Satisfied st.lits w.nogood ∨
    ∀ y, (y = w.w1 ∨ y = w.w2) → y ∈ st.lits → y ∈ st.pending ∨ (y = x ∧ i ∈ todo)
  pending : ∀ y ∈ st.pending, y ∈ st.lits
  current : x ∈ st.lits
  nodup : (st.trail.map fun e => e.lit.var).Nodup

/-- What visiting a watch list establishes. -/
def PassOK (Δ : List (Nogood A)) (t₀ : List (Entry A)) : Pass A → Prop
  | .ok st => WInv Δ st ∧ ReflTransGen (UPStep Δ) t₀ st.trail
  | .conflict δ st => δ ∈ Δ ∧ (onTrail st.trail).Falsifies δ ∧ ReflTransGen (UPStep Δ) t₀ st.trail

omit [DecidableEq A] in
theorem PassOK.head {Δ : List (Nogood A)} {t₀ t₁ : List (Entry A)} {p : Pass A} (step : UPStep Δ t₀ t₁)
    (h : PassOK Δ t₁ p) : PassOK Δ t₀ p := by
  cases p with
  | ok st => exact ⟨h.1, ReflTransGen.head step h.2⟩
  | conflict δ st => exact ⟨h.1, h.2.1, ReflTransGen.head step h.2.2⟩

omit [DecidableEq A] in
theorem Satisfied.mono {lits lits' : List (Lit A)} {δ : Nogood A} (h : Satisfied lits δ)
    (sub : ∀ l ∈ lits, l ∈ lits') : Satisfied lits' δ := by
  obtain ⟨m, hm, hc⟩ := h
  exact ⟨m, hm, sub _ hc⟩

omit [DecidableEq A] in
theorem mem_of_getElem? {l : List (Watched A)} {i : ℕ} {w : Watched A} (h : l[i]? = some w) : w ∈ l :=
  List.mem_of_getElem? h

omit [DecidableEq A] in
theorem mem_nogoods {Δ : List (Nogood A)} {db : List (Watched A)} (h : db.map Watched.nogood = Δ) {i : ℕ}
    {w : Watched A} (hw : db[i]? = some w) : w.nogood ∈ Δ := by
  rw [← h]
  exact List.mem_map_of_mem (mem_of_getElem? hw)

omit [DecidableEq A] in
/-- Entering a watch list. -/
theorem WInv.start {Δ : List (Nogood A)} {st : WState A} {x : Lit A} {rest : List (Lit A)} (inv : WInv Δ st)
    (pending : st.pending = x :: rest) : PInv Δ x (st.watches x) [] { st with pending := rest } where
  db := inv.db
  shape := inv.shape
  index := by
    intro i w hw y hy
    have both := inv.index i w hw
    have iy : i ∈ st.watches y := by
      rcases hy with rfl | rfl
      · exact both.1
      · exact both.2
    exact ⟨fun _ => iy, fun same => Or.inl (same ▸ iy)⟩
  watch := by
    intro i w hw
    rcases inv.watch i w hw with sat | watched
    · exact Or.inl sat
    · right
      intro y hy on
      have := watched y hy on
      rw [pending] at this
      rcases List.mem_cons.mp this with rfl | h
      · right
        have both := inv.index i w hw
        refine ⟨rfl, ?_⟩
        rcases hy with rfl | rfl
        · exact both.1
        · exact both.2
      · exact Or.inl h
  pending := fun y hy => inv.pending y (by rw [pending]; exact List.mem_cons_of_mem _ hy)
  current := inv.pending x (by rw [pending]; exact List.mem_cons_self)
  nodup := inv.nodup

/-- Leaving a watch list. -/
theorem PInv.finish {Δ : List (Nogood A)} {x : Lit A} {kept : List ℕ} {st : WState A} (inv : PInv Δ x [] kept st) :
    WInv Δ { st with watches := Function.update st.watches x kept } where
  db := inv.db
  shape := inv.shape
  index := by
    intro i w hw
    have get : ∀ y, (y = w.w1 ∨ y = w.w2) → i ∈ Function.update st.watches x kept y := by
      intro y hy
      by_cases same : y = x
      · subst same
        rw [Function.update_self]
        rcases (inv.index i w hw y hy).2 rfl with h | h
        · exact absurd h List.not_mem_nil
        · exact h
      · rw [Function.update_of_ne same]
        exact (inv.index i w hw y hy).1 same
    exact ⟨get _ (Or.inl rfl), get _ (Or.inr rfl)⟩
  watch := by
    intro i w hw
    rcases inv.watch i w hw with sat | watched
    · exact Or.inl sat
    · right
      intro y hy on
      rcases watched y hy on with h | ⟨-, h⟩
      · exact h
      · exact absurd h List.not_mem_nil
  pending := inv.pending
  nodup := inv.nodup

omit [DecidableEq A] in
/-- Dropping an identifier that does not watch `x`. -/
theorem PInv.drop {Δ : List (Nogood A)} {x : Lit A} {i : ℕ} {todo kept : List ℕ} {st : WState A}
    (inv : PInv Δ x (i :: todo) kept st) (stale : ∀ w, st.db[i]? = some w → ¬ (w.w1 = x ∨ w.w2 = x)) :
    PInv Δ x todo kept st where
  db := inv.db
  shape := inv.shape
  index := by
    intro j w hw y hy
    refine ⟨(inv.index j w hw y hy).1, fun same => ?_⟩
    rcases (inv.index j w hw y hy).2 same with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · subst same
        exact absurd (hy.imp Eq.symm Eq.symm) (stale w hw)
      · exact Or.inl h
    · exact Or.inr h
  watch := by
    intro j w hw
    rcases inv.watch j w hw with sat | watched
    · exact Or.inl sat
    · right
      intro y hy on
      rcases watched y hy on with h | ⟨same, h⟩
      · exact Or.inl h
      · rcases List.mem_cons.mp h with rfl | h
        · subst same
          exact absurd (hy.imp Eq.symm Eq.symm) (stale w hw)
        · exact Or.inr ⟨same, h⟩
  pending := inv.pending
  current := inv.current
  nodup := inv.nodup

omit [DecidableEq A] in
/-- Keeping a satisfied nogood in the watch list of `x`. -/
theorem PInv.keep {Δ : List (Nogood A)} {x : Lit A} {i : ℕ} {todo kept : List ℕ} {st : WState A} {w : Watched A}
    (inv : PInv Δ x (i :: todo) kept st) (hw : st.db[i]? = some w) (sat : Satisfied st.lits w.nogood) :
    PInv Δ x todo (i :: kept) st where
  db := inv.db
  shape := inv.shape
  index := by
    intro j w' hw' y hy
    refine ⟨(inv.index j w' hw' y hy).1, fun same => ?_⟩
    rcases (inv.index j w' hw' y hy).2 same with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  watch := by
    intro j w' hw'
    by_cases ji : j = i
    · subst ji
      rw [hw] at hw'
      cases hw'
      exact Or.inl sat
    · rcases inv.watch j w' hw' with sat' | watched
      · exact Or.inl sat'
      · right
        intro y hy on
        rcases watched y hy on with h | ⟨same, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨same, (List.mem_cons.mp h).resolve_left ji⟩
  pending := inv.pending
  current := inv.current
  nodup := inv.nodup

theorem other_ne {w : Watched A} {x : Lit A} (distinct : w.w1 ≠ w.w2) (watching : w.w1 = x ∨ w.w2 = x) :
    w.other x ≠ x := by
  unfold Watched.other
  split
  · rename_i h
    rw [← h]
    exact Ne.symm distinct
  · rename_i h
    exact fun same => h (by rcases watching with h' | h'; exact h'; exact absurd same (by rw [← h']; exact distinct))

theorem other_watch {w : Watched A} {x : Lit A} : w.other x = w.w1 ∨ w.other x = w.w2 := by
  unfold Watched.other
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem watch_cases {w : Watched A} {x y : Lit A} (watching : w.w1 = x ∨ w.w2 = x) (hy : y = w.w1 ∨ y = w.w2) :
    y = x ∨ y = w.other x := by
  unfold Watched.other
  split
  · rename_i h
    rcases hy with rfl | rfl
    · exact Or.inl h
    · exact Or.inr rfl
  · rename_i h
    rcases hy with rfl | rfl
    · exact Or.inr rfl
    · rcases watching with h' | h'
      · exact absurd h' h
      · exact Or.inl h'

/-- Moving the watch of a nogood from `x` to a literal `r` that is not true. -/
theorem PInv.move {Δ : List (Nogood A)} {x : Lit A} {i : ℕ} {todo kept : List ℕ} {st : WState A} {w : Watched A}
    {r : Lit A} (inv : PInv Δ x (i :: todo) kept st) (hw : st.db[i]? = some w) (watching : w.w1 = x ∨ w.w2 = x)
    (hr : r ∈ w.nogood.lits) (rx : r ≠ x) (ro : r ≠ w.other x) (off : r ∉ st.lits) :
    PInv Δ x todo kept (st.move i w x r) where
  db := by
    show (st.db.set i ⟨w.nogood, w.other x, r⟩).map Watched.nogood = Δ
    rw [List.map_set, ← inv.db]
    obtain ⟨lt, hget⟩ := List.getElem?_eq_some_iff.mp hw
    have lt' : i < (st.db.map Watched.nogood).length := by simpa using lt
    have same : (st.db.map Watched.nogood)[i]'lt' = w.nogood := by
      simp [hget]
    conv_rhs => rw [← List.set_getElem_self lt']
    rw [same]
  shape := by
    intro w' hw'
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hw'
    change (st.db.set i ⟨w.nogood, w.other x, r⟩)[j]? = some w' at hj
    rw [List.getElem?_set] at hj
    split at hj
    · split at hj
      · cases hj
        have old := inv.shape w (mem_of_getElem? hw)
        exact ⟨Ne.symm ro, by rcases other_watch (w := w) (x := x) with h | h <;> rw [h]; exact old.2.1; exact old.2.2,
          hr⟩
      · cases hj
    · exact inv.shape w' (mem_of_getElem? hj)
  index := by
    intro j w' hw' y hy
    change (st.db.set i ⟨w.nogood, w.other x, r⟩)[j]? = some w' at hw'
    change (y ≠ x → j ∈ Function.update st.watches r (i :: st.watches r) y) ∧ _
    rw [List.getElem?_set] at hw'
    split at hw'
    · rename_i same
      subst same
      split at hw'
      · cases hw'
        refine ⟨fun yx => ?_, fun yx => ?_⟩
        · rcases hy with rfl | rfl
          · have old := inv.index i w hw (w.other x) other_watch
            rw [Function.update_of_ne (Ne.symm ro)]
            exact (old.1 (other_ne (inv.shape w (mem_of_getElem? hw)).1 watching))
          · rw [Function.update_self]
            exact List.mem_cons_self
        · rcases hy with rfl | rfl
          · exact absurd yx (other_ne (inv.shape w (mem_of_getElem? hw)).1 watching)
          · exact absurd yx rx
      · cases hw'
    · rename_i ne
      refine ⟨fun yx => ?_, fun yx => ?_⟩
      · by_cases yr : y = r
        · subst yr
          rw [Function.update_self]
          exact List.mem_cons_of_mem _ ((inv.index j w' hw' _ hy).1 yx)
        · rw [Function.update_of_ne yr]
          exact (inv.index j w' hw' y hy).1 yx
      · rcases (inv.index j w' hw' y hy).2 yx with h | h
        · exact Or.inl ((List.mem_cons.mp h).resolve_left (Ne.symm ne))
        · exact Or.inr h
  watch := by
    intro j w' hw'
    change (st.db.set i ⟨w.nogood, w.other x, r⟩)[j]? = some w' at hw'
    change Satisfied st.lits w'.nogood ∨ _
    rw [List.getElem?_set] at hw'
    split at hw'
    · rename_i same
      subst same
      split at hw'
      · cases hw'
        rcases inv.watch i w hw with sat | watched
        · exact Or.inl sat
        · right
          intro y hy on
          rcases hy with rfl | rfl
          · rcases watched _ other_watch on with h | ⟨same, -⟩
            · exact Or.inl h
            · exact absurd same (other_ne (inv.shape w (mem_of_getElem? hw)).1 watching)
          · exact absurd on off
      · cases hw'
    · rename_i ne
      rcases inv.watch j w' hw' with sat | watched
      · exact Or.inl sat
      · right
        intro y hy on
        rcases watched y hy on with h | ⟨same, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨same, (List.mem_cons.mp h).resolve_left (Ne.symm ne)⟩
  pending := inv.pending
  current := inv.current
  nodup := inv.nodup

/-- Pushing the complement of the other watch of a unit nogood. -/
theorem PInv.unit {Δ : List (Nogood A)} {x : Lit A} {i : ℕ} {todo kept : List ℕ} {st : WState A} {w : Watched A}
    (inv : PInv Δ x (i :: todo) kept st) (hw : st.db[i]? = some w) (off : w.other x ∉ st.lits)
    (offCompl : (w.other x).compl ∉ st.lits) :
    PInv Δ x todo (i :: kept) (st.pushUnit w x) where
  db := inv.db
  shape := inv.shape
  index := by
    intro j w' hw' y hy
    refine ⟨(inv.index j w' hw' y hy).1, fun same => ?_⟩
    rcases (inv.index j w' hw' y hy).2 same with h | h
    · rcases List.mem_cons.mp h with rfl | h
      · exact Or.inr List.mem_cons_self
      · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)
  watch := by
    intro j w' hw'
    simp only [WState.pushUnit, WState.lits, List.map_cons] at hw' ⊢
    by_cases ji : j = i
    · subst ji
      rw [hw] at hw'
      cases hw'
      left
      rcases other_watch (w := w) (x := x) with h | h
      · exact ⟨w.other x, by rw [h]; exact (inv.shape w (mem_of_getElem? hw)).2.1, List.mem_cons_self⟩
      · exact ⟨w.other x, by rw [h]; exact (inv.shape w (mem_of_getElem? hw)).2.2, List.mem_cons_self⟩
    · rcases inv.watch j w' hw' with sat | watched
      · exact Or.inl (sat.mono fun l hl => List.mem_cons_of_mem _ hl)
      · right
        intro y hy on
        rcases List.mem_cons.mp on with rfl | on
        · exact Or.inl List.mem_cons_self
        · rcases watched y hy on with h | ⟨same, h⟩
          · exact Or.inl (List.mem_cons_of_mem _ h)
          · exact Or.inr ⟨same, (List.mem_cons.mp h).resolve_left ji⟩
  pending := by
    intro y hy
    simp only [WState.pushUnit, WState.lits, List.map_cons] at hy ⊢
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (inv.pending y hy)
  current := List.mem_cons_of_mem _ inv.current
  nodup := by
    simp only [WState.pushUnit, List.map_cons]
    refine List.nodup_cons.mpr ⟨fun h => ?_, inv.nodup⟩
    obtain ⟨e, he, same⟩ := List.mem_map.mp h
    rcases Lit.eq_or_eq_compl (l := e.lit) (m := w.other x) (by rw [same]; rfl) with h | h
    · exact off (h ▸ List.mem_map_of_mem he)
    · exact offCompl (by rw [← h]; exact List.mem_map_of_mem he)

/-! ## Visiting a watch list -/

theorem find?_none_mem {δ : Nogood A} {x o : Lit A} {lits : List (Lit A)}
    (h : δ.lits.find? (fun r => decide (r ≠ x ∧ r ≠ o ∧ r ∉ lits)) = none) (current : x ∈ lits) :
    ∀ m ∈ δ.lits, m ≠ o → m ∈ lits := by
  intro m hm ne
  have := List.find?_eq_none.mp h m hm
  simp only [decide_eq_true_eq, not_and, not_not] at this
  by_cases mx : m = x
  · exact mx ▸ current
  · exact this mx ne

/-- **Visiting a watch list is correct.** -/
theorem processList_spec {Δ : List (Nogood A)} (x : Lit A) :
    ∀ (todo kept : List ℕ) (st : WState A), PInv Δ x todo kept st → PassOK Δ st.trail (processList x st todo kept)
  | [], kept, st, inv => ⟨inv.finish, ReflTransGen.refl⟩
  | i :: todo, kept, st, inv => by
    unfold processList
    cases hw : st.db[i]? with
    | none =>
      exact processList_spec x todo kept st (inv.drop fun w h => by rw [hw] at h; cases h)
    | some w =>
      simp only
      by_cases watching : w.w1 = x ∨ w.w2 = x
      · rw [if_pos watching]
        have shape := inv.shape w (mem_of_getElem? hw)
        unfold visit
        by_cases sat : (w.other x).compl ∈ st.lits
        · rw [if_pos sat]
          refine processList_spec x todo (i :: kept) st (inv.keep hw ?_)
          rcases other_watch (w := w) (x := x) with h | h
          · exact ⟨w.other x, by rw [h]; exact shape.2.1, sat⟩
          · exact ⟨w.other x, by rw [h]; exact shape.2.2, sat⟩
        · rw [if_neg sat]
          cases hfind : w.nogood.lits.find? (fun r => decide (r ≠ x ∧ r ≠ w.other x ∧ r ∉ st.lits)) with
          | some r =>
            simp only
            have pred := List.find?_some hfind
            simp only [decide_eq_true_eq] at pred
            exact processList_spec x todo kept _
              (inv.move hw watching (List.mem_of_find?_eq_some hfind) pred.1 pred.2.1 pred.2.2)
          | none =>
            simp only
            have others := find?_none_mem hfind inv.current
            have otherMem : w.other x ∈ w.nogood.lits := by
              rcases other_watch (w := w) (x := x) with h | h
              · rw [h]; exact shape.2.1
              · rw [h]; exact shape.2.2
            by_cases on : w.other x ∈ st.lits
            · rw [if_pos on]
              refine ⟨mem_nogoods inv.db hw, ?_, ReflTransGen.refl⟩
              intro m hm
              by_cases mo : m = w.other x
              · exact mo ▸ on
              · exact others m hm mo
            · rw [if_neg on]
              have step : UPStep Δ st.trail (⟨(w.other x).compl, levelOf st.trail, some w.nogood⟩ :: st.trail) := by
                refine UPStep.unit (mem_nogoods inv.db hw) ⟨otherMem, others, ?_⟩
                rintro ⟨e, he, same⟩
                rcases Lit.eq_or_eq_compl same with h | h
                · exact on (h ▸ List.mem_map_of_mem he)
                · exact sat (by rw [← h]; exact List.mem_map_of_mem he)
              exact PassOK.head step (processList_spec x todo (i :: kept) _ (inv.unit hw on sat))
      · rw [if_neg watching]
        exact processList_spec x todo kept st (inv.drop fun w' h => by rw [hw] at h; cases h; exact watching)

/-- What propagation establishes. -/
def OutcomeOK (Δ : List (Nogood A)) (t₀ : List (Entry A)) : Outcome A → Prop
  | .fixpoint st => WInv Δ st ∧ st.pending = [] ∧ ReflTransGen (UPStep Δ) t₀ st.trail
  | .conflict δ st => δ ∈ Δ ∧ (onTrail st.trail).Falsifies δ ∧ ReflTransGen (UPStep Δ) t₀ st.trail
  | .outOfFuel st => WInv Δ st ∧ ReflTransGen (UPStep Δ) t₀ st.trail

/-- **Propagation by watches refines unit propagation and keeps the invariant.** -/
theorem propagateWatched_spec {Δ : List (Nogood A)} :
    ∀ (fuel : ℕ) (st : WState A), WInv Δ st → OutcomeOK Δ st.trail (propagateWatched fuel st)
  | 0, st, inv => ⟨inv, ReflTransGen.refl⟩
  | fuel + 1, st, inv => by
    unfold propagateWatched
    cases hp : st.pending with
    | nil => exact ⟨inv, hp, ReflTransGen.refl⟩
    | cons x rest =>
      simp only
      have pass := processList_spec x (st.watches x) [] { st with pending := rest } (inv.start hp)
      cases hpass : processList x { st with pending := rest } (st.watches x) [] with
      | ok st' =>
        dsimp only
        rw [hpass] at pass
        have rest' := propagateWatched_spec fuel st' pass.1
        cases hout : propagateWatched fuel st' with
        | fixpoint st'' =>
          rw [hout] at rest'
          exact ⟨rest'.1, rest'.2.1, pass.2.trans rest'.2.2⟩
        | conflict δ st'' =>
          rw [hout] at rest'
          exact ⟨rest'.1, rest'.2.1, pass.2.trans rest'.2.2⟩
        | outOfFuel st'' =>
          rw [hout] at rest'
          exact ⟨rest'.1, pass.2.trans rest'.2⟩
      | conflict δ st' =>
        dsimp only
        rw [hpass] at pass
        exact pass

omit [DecidableEq A] in
/-- Unit propagation only adds literals. -/
theorem upSteps_lits {Δ : List (Nogood A)} {t t' : List (Entry A)} (h : ReflTransGen (UPStep Δ) t t') :
    ∀ l ∈ t.map Entry.lit, l ∈ t'.map Entry.lit := by
  induction h with
  | refl => exact fun l hl => hl
  | tail _ step ih =>
    cases step with
    | unit _ _ => exact fun l hl => List.mem_cons_of_mem _ (ih l hl)

/-! ## The fixpoint -/

omit [DecidableEq A] in
/-- **At a fixpoint no nogood is falsified or unit.** -/
theorem WInv.quiescent {Δ : List (Nogood A)} {st : WState A} (inv : WInv Δ st) (empty : st.pending = []) :
    ∀ δ ∈ Δ, ¬ (onTrail st.trail).Falsifies δ ∧ ∀ l, ¬ (onTrail st.trail).UnitOn δ l := by
  intro δ hδ
  rw [← inv.db] at hδ
  obtain ⟨w, hwmem, rfl⟩ := List.mem_map.mp hδ
  obtain ⟨i, hw⟩ := List.mem_iff_getElem?.mp hwmem
  have shape := inv.shape w hwmem
  -- two entries with complementary literals contradict the distinct variables
  have consistent : ∀ m, m ∈ st.lits → m.compl ∈ st.lits → False := by
    intro m hm hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    obtain ⟨f, hf, same⟩ := List.mem_map.mp hc
    have := List.inj_on_of_nodup_map inv.nodup hf he (by show f.lit.var = e.lit.var; rw [same]; rfl)
    subst this
    exact Lit.compl_ne _ same.symm
  rcases inv.watch i w hw with ⟨m, hm, hc⟩ | watched
  · refine ⟨fun falsified => consistent m (falsified m hm) hc, fun l unit => ?_⟩
    by_cases ml : m = l
    · subst ml
      exact unit.2.2 ⟨_, (List.mem_map.mp hc).choose_spec.1, by
        rw [(List.mem_map.mp hc).choose_spec.2]; rfl⟩
    · exact consistent m (unit.2.1 m hm ml) hc
  · have off : ∀ y, (y = w.w1 ∨ y = w.w2) → y ∉ st.lits := by
      intro y hy on
      have := watched y hy on
      rw [empty] at this
      exact List.not_mem_nil this
    refine ⟨fun falsified => off w.w1 (Or.inl rfl) (falsified _ shape.2.1), fun l unit => ?_⟩
    by_cases l1 : w.w1 = l
    · exact off w.w2 (Or.inr rfl) (unit.2.1 _ shape.2.2 (by rw [← l1]; exact Ne.symm shape.1))
    · exact off w.w1 (Or.inl rfl) (unit.2.1 _ shape.2.1 l1)

/-- **Same consequences.** If no nogood of `Δ` is falsified or unit on a trail `t` that contains
the literals of `t₀`, then every trail unit propagation reaches from `t₀` has its literals on
`t`. -/
theorem closure {Δ : List (Nogood A)} {t : List (Entry A)}
    (quiet : ∀ δ ∈ Δ, ¬ (onTrail t).Falsifies δ ∧ ∀ l, ¬ (onTrail t).UnitOn δ l) {t₀ t' : List (Entry A)}
    (sub : ∀ l ∈ t₀.map Entry.lit, l ∈ t.map Entry.lit) (reach : ReflTransGen (UPStep Δ) t₀ t') :
    ∀ l ∈ t'.map Entry.lit, l ∈ t.map Entry.lit := by
  induction reach with
  | refl => exact sub
  | @tail t₁ t₂ _ step ih =>
    cases step with
    | @unit δ l hδ unit =>
      intro m hm
      rw [List.map_cons, List.mem_cons] at hm
      rcases hm with rfl | hm
      · obtain ⟨member, others, -⟩ := unit
        have othersOn : ∀ m ∈ δ.lits, m ≠ l → m ∈ t.map Entry.lit := fun m hm ne => ih m (others m hm ne)
        by_cases assigned : (onTrail t).Assigned l.var
        · obtain ⟨e, he, same⟩ := assigned
          rcases Lit.eq_or_eq_compl same with h | h
          · exfalso
            apply (quiet δ hδ).1
            intro m hm
            by_cases ml : m = l
            · rw [ml, ← h]
              exact List.mem_map_of_mem he
            · exact othersOn m hm ml
          · show l.compl ∈ t.map Entry.lit
            rw [← h]
            exact List.mem_map_of_mem he
        · exact absurd ⟨member, othersOn, assigned⟩ ((quiet δ hδ).2 l)
      · exact ih m hm

/-- **Propagation by watches computes the unit-propagation closure**: at a reported fixpoint the
trail is reached by unit propagation, and every trail unit propagation reaches from the start has
its literals on it. -/
theorem propagateWatched_closure {Δ : List (Nogood A)} {fuel : ℕ} {st st' : WState A} (inv : WInv Δ st)
    (h : propagateWatched fuel st = .fixpoint st') :
    ReflTransGen (UPStep Δ) st.trail st'.trail ∧
      ∀ t', ReflTransGen (UPStep Δ) st.trail t' → ∀ l ∈ t'.map Entry.lit, l ∈ st'.trail.map Entry.lit := by
  have spec := propagateWatched_spec fuel st inv
  rw [h] at spec
  obtain ⟨inv', empty, reach⟩ := spec
  exact ⟨reach, fun t' reach' => closure (inv'.quiescent empty) (upSteps_lits reach) reach'⟩

/-! ## Refinement of the solver -/

namespace Program

variable (P : Program A)

/-- **Specification unit propagation by database nogoods is solver propagation.** -/
theorem UPStep.solverStep {Δ : List (Nogood A)} {learned : List (Nogood A)} {mark : ℕ}
    (database : ∀ δ ∈ Δ, P.InDatabase ⟨[], learned, 0⟩ δ) (vars : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, P.IsVar l.var)
    {t t' : List (Entry A)} (h : UPStep Δ t t') : P.Step (.running ⟨t, learned, mark⟩) (.running ⟨t', learned, mark⟩) := by
  cases h with
  | unit hδ unit => exact .propagate (database _ hδ) unit (vars _ hδ _ unit.1)

theorem upSteps_solver {Δ : List (Nogood A)} {learned : List (Nogood A)} {mark : ℕ}
    (database : ∀ δ ∈ Δ, P.InDatabase ⟨[], learned, 0⟩ δ) (vars : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, P.IsVar l.var)
    {t t' : List (Entry A)} (h : ReflTransGen (UPStep Δ) t t') :
    ReflTransGen P.Step (.running ⟨t, learned, mark⟩) (.running ⟨t', learned, mark⟩) := by
  induction h with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (UPStep.solverStep P database vars step)

end Program

/-! ## Starting and deciding -/

/-- The first two distinct literals of a list. -/
def twoWatches : List (Lit A) → Option (Lit A × Lit A)
  | [] => none
  | l :: rest => (rest.find? (· ≠ l)).map fun m => (l, m)

/-- The watched nogoods of a list of nogoods: those with two distinct literals, watching the first
two. -/
def watchedOf (Δ : List (Nogood A)) : List (Watched A) :=
  Δ.filterMap fun δ => (twoWatches δ.lits).map fun p => ⟨δ, p.1, p.2⟩

/-- The watch index of a list of watched nogoods. -/
def indexOf (db : List (Watched A)) (y : Lit A) : List ℕ :=
  (List.range db.length).filter fun i => (db[i]?).any fun w => decide (w.w1 = y ∨ w.w2 = y)

/-- The watched state over a trail with nothing pending. -/
def WState.init (Δ : List (Nogood A)) (t : List (Entry A)) : WState A :=
  ⟨t, watchedOf Δ, indexOf (watchedOf Δ), []⟩

/-- The nogoods of `Δ` with two distinct literals. -/
def watchable (Δ : List (Nogood A)) : List (Nogood A) := (watchedOf Δ).map Watched.nogood

theorem twoWatches_spec {lits : List (Lit A)} {p : Lit A × Lit A} (h : twoWatches lits = some p) :
    p.1 ≠ p.2 ∧ p.1 ∈ lits ∧ p.2 ∈ lits := by
  cases lits with
  | nil => cases h
  | cons l rest =>
    simp only [twoWatches, Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    have pred := List.find?_some hm
    simp only [ne_eq, decide_eq_true_eq] at pred
    exact ⟨Ne.symm pred, List.mem_cons_self, List.mem_cons_of_mem _ (List.mem_of_find?_eq_some hm)⟩

/-- **The initial watched state satisfies the invariant** on a trail making no watch true. -/
theorem WInv.init (Δ : List (Nogood A)) {t : List (Entry A)} (nodup : (t.map fun e => e.lit.var).Nodup)
    (off : ∀ w ∈ watchedOf Δ, w.w1 ∉ t.map Entry.lit ∧ w.w2 ∉ t.map Entry.lit) :
    WInv (watchable Δ) (WState.init Δ t) where
  db := rfl
  shape := by
    intro w hw
    obtain ⟨δ, -, hδ⟩ := List.mem_filterMap.mp hw
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp hδ
    exact twoWatches_spec hp
  index := by
    intro i w hw
    have lt : i < (watchedOf Δ).length := (List.getElem?_eq_some_iff.mp hw).1
    constructor <;>
    · simp only [WState.init, indexOf, List.mem_filter, List.mem_range, lt, true_and]
      have hw' : (watchedOf Δ)[i]? = some w := hw
      rw [hw']
      simp
  watch := by
    intro i w hw
    right
    intro y hy on
    have := off w (mem_of_getElem? hw)
    rcases hy with rfl | rfl
    · exact absurd on this.1
    · exact absurd on this.2
  pending := fun y hy => absurd hy List.not_mem_nil
  nodup := nodup

/-- A decision at a fixpoint: push `x` and make it pending. -/
def WState.decide (st : WState A) (x : Lit A) : WState A :=
  { st with trail := ⟨x, levelOf st.trail + 1, none⟩ :: st.trail, pending := [x] }

omit [DecidableEq A] in
/-- **A decision of an unassigned literal at a fixpoint keeps the invariant.** -/
theorem WInv.decide {Δ : List (Nogood A)} {st : WState A} (inv : WInv Δ st) (empty : st.pending = [])
    {x : Lit A} (unassigned : ¬ (onTrail st.trail).Assigned x.var) : WInv Δ (st.decide x) where
  db := inv.db
  shape := inv.shape
  index := inv.index
  watch := by
    intro i w hw
    rcases inv.watch i w hw with sat | watched
    · exact Or.inl (sat.mono fun l hl => List.mem_cons_of_mem _ hl)
    · right
      intro y hy on
      simp only [WState.decide, WState.lits, List.map_cons] at on ⊢
      rcases List.mem_cons.mp on with rfl | on
      · exact List.mem_cons_self
      · have := watched y hy on
        rw [empty] at this
        exact absurd this List.not_mem_nil
  pending := by
    intro y hy
    simp only [WState.decide, List.mem_singleton] at hy
    subst hy
    exact List.mem_cons_self
  nodup := by
    simp only [WState.decide, List.map_cons]
    exact List.nodup_cons.mpr ⟨fun h => unassigned (by
      obtain ⟨e, he, same⟩ := List.mem_map.mp h
      exact ⟨e, he, same⟩), inv.nodup⟩

omit [DecidableEq A] in
/-- **Backjumping keeps the invariant when the kept trail is pending again.** A solver may instead
keep a level-aware form of the invariant and leave nothing pending; that form is not proved here. -/
theorem WInv.backjump {Δ : List (Nogood A)} {st : WState A} (inv : WInv Δ st) {newer older : List (Entry A)}
    (split : st.trail = newer ++ older) :
    WInv Δ { st with trail := older, pending := older.map Entry.lit } where
  db := inv.db
  shape := inv.shape
  index := inv.index
  watch := fun _ _ _ => Or.inr fun _ _ on => on
  pending := fun _ hy => hy
  nodup := by
    have := inv.nodup
    rw [split, List.map_append] at this
    exact (List.nodup_append.mp this).2.1

end Watches

end Mettapedia.Logic.ASP
