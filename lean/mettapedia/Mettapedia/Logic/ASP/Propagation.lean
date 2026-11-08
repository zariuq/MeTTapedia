import Mettapedia.Logic.ASP.Watches
import Mettapedia.Logic.ASP.SourcePointers
import Mettapedia.Logic.ASP.Emission
import Mettapedia.Logic.ASP.Freshness

/-!
# One propagation loop: watches, short nogoods and source pointers

The reference driver (`Driver`) propagates with three operations and alternates
them until none applies:

* two watched literals (`propagateWatched`, from `Watches`) for every database
  nogood with two distinct literals;
* a scan of the short nogoods (`scanShort`), those without two distinct literals,
  which cannot be watched;
* the source-pointer unfounded-set check (`SourcePointers`). Its marked atoms
  that are not falsum atoms (`Program.loopMarked`), in atom order, are the
  driver's unfounded set; its unassigned atoms are pushed false with their loop
  nogoods as reasons (`pushUnfounded`), each loop nogood first named by a loop
  step of the certificate. The set is unfounded at the propagation fixpoint where
  the check runs (`Program.Quiet.loopMarked_unfounded`): a falsum atom is false by
  its unit support nogood, so a rule with a falsum atom among its positive atoms
  has a false body. Its loop nogoods are over variables, and its loop steps hold no
  falsum atom, as the certificate checker requires.

## Results

* **Fuel for watched propagation.** Watched propagation processes one pending
  literal per unit of fuel, and pushing a literal adds one entry to the trail and
  one to the pending list. So `|pending| + (|V| - |trail|)` falls by one per
  processed literal, where `V` holds the variables of the trail and the database
  (`propagateWatched_ne_outOfFuel`). With the pending literals distinct and on the
  trail, **one more than the number of variables suffices**
  (`propagateWatched_ne_outOfFuel_of_nodup`).
* **Watches after a conflict.** A reported conflict keeps the data part of the
  watch invariant (`WShape`): the database, the watched literals and the index
  (`propagateWatched_shapeOK`).
* **Watches across backjumps.** Re-queueing the kept trail restores the full
  invariant from the data part (`WShape.requeue`). A newly learned nogood with two
  distinct literals is watched on its first two (`WState.addWatched`,
  `WShape.addWatched`), and pushing an unassigned literal while making it pending
  keeps the invariant (`WInv.push`).
* **One loop, closed under both** (`Program.propagateAll_spec`). Started from a
  driver state whose run is an emitting run and a run of the discipline, the loop
  reports either a falsified, named database nogood or a state that is closed
  (`Closed`): no completion or learned nogood is unit or falsified, and every
  program atom of an unfounded set is assigned false. Every push is an emitting
  step and a step of the discipline, so the reported state is reached by both.
* **No loop nogood is falsified at a closed state** (`Program.Closed.loops`): a
  falsified loop nogood would leave a true atom in an unfounded set.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Relation

universe u

variable {A : Type u}

section Propagation

variable [DecidableEq A]

/-! ## Watched propagation: shapes and fuel -/

/-- The data part of the watch invariant: the database, the watched literals and the index. -/
structure WShape (Δ : List (Nogood A)) (st : WState A) : Prop where
  db : st.db.map Watched.nogood = Δ
  shape : ∀ w ∈ st.db, w.w1 ≠ w.w2 ∧ w.w1 ∈ w.nogood.lits ∧ w.w2 ∈ w.nogood.lits
  index : ∀ (i : ℕ) (w : Watched A), st.db[i]? = some w → i ∈ st.watches w.w1 ∧ i ∈ st.watches w.w2

omit [DecidableEq A] in
theorem WInv.toShape {Δ : List (Nogood A)} {st : WState A} (h : WInv Δ st) : WShape Δ st :=
  ⟨h.db, h.shape, h.index⟩

/-- A pass extends the trail and the pending literals by the same new entries. -/
def Pass.Extends (t : List (Entry A)) (pend : List (Lit A)) : Pass A → Prop
  | .ok st => ∃ new : List (Entry A), st.trail = new ++ t ∧ st.pending = new.map Entry.lit ++ pend
  | .conflict _ st => ∃ new : List (Entry A), st.trail = new ++ t ∧ st.pending = new.map Entry.lit ++ pend

/-- A reported conflict keeps the data part of the watch invariant. -/
def Pass.ShapeOK (Δ : List (Nogood A)) : Pass A → Prop
  | .ok _ => True
  | .conflict _ st => WShape Δ st

omit [DecidableEq A] in
theorem Pass.Extends.of_cons {t : List (Entry A)} {pend : List (Lit A)} {e : Entry A} :
    ∀ {p : Pass A}, p.Extends (e :: t) (e.lit :: pend) → p.Extends t pend
  | .ok _, ⟨new, htrail, hpend⟩ =>
    ⟨new ++ [e], by rw [htrail, List.append_assoc]; rfl, by rw [hpend, List.map_append, List.append_assoc]; rfl⟩
  | .conflict _ _, ⟨new, htrail, hpend⟩ =>
    ⟨new ++ [e], by rw [htrail, List.append_assoc]; rfl, by rw [hpend, List.map_append, List.append_assoc]; rfl⟩

/-- **A pass only pushes**: trail and pending literals grow by the same entries. -/
theorem processList_extends (x : Lit A) :
    ∀ (todo kept : List ℕ) (st : WState A), (processList x st todo kept).Extends st.trail st.pending
  | [], kept, st => ⟨[], rfl, rfl⟩
  | i :: todo, kept, st => by
    unfold processList
    split
    · exact processList_extends x todo kept st
    · rename_i w _
      split
      · split
        · exact processList_extends x todo (i :: kept) st
        · rename_i r _
          exact processList_extends x todo kept (st.move i w x r)
        · exact Pass.Extends.of_cons (processList_extends x todo (i :: kept) (st.pushUnit w x))
        · exact ⟨[], rfl, rfl⟩
      · exact processList_extends x todo kept st

/-- A conflict met while visiting the nogoods watching `x` keeps the data part of the invariant. -/
theorem PInv.conflictShape {Δ : List (Nogood A)} {x : Lit A} {i : ℕ} {todo kept : List ℕ} {st : WState A}
    (inv : PInv Δ x (i :: todo) kept st) :
    WShape Δ { st with watches := Function.update st.watches x (i :: todo ++ kept) } where
  db := inv.db
  shape := inv.shape
  index := by
    intro j w hw
    have get : ∀ y, (y = w.w1 ∨ y = w.w2) → j ∈ Function.update st.watches x (i :: todo ++ kept) y := by
      intro y hy
      by_cases same : y = x
      · subst same
        rw [Function.update_self]
        rcases (inv.index j w hw y hy).2 rfl with h | h
        · exact List.mem_append_left _ h
        · exact List.mem_append_right _ h
      · rw [Function.update_of_ne same]
        exact (inv.index j w hw y hy).1 same
    exact ⟨get _ (Or.inl rfl), get _ (Or.inr rfl)⟩

/-- **A reported conflict keeps the data part of the invariant.** -/
theorem processList_shapeOK {Δ : List (Nogood A)} (x : Lit A) :
    ∀ (todo kept : List ℕ) (st : WState A), PInv Δ x todo kept st → (processList x st todo kept).ShapeOK Δ
  | [], kept, st, _ => trivial
  | i :: todo, kept, st, inv => by
    unfold processList
    cases hw : st.db[i]? with
    | none =>
      exact processList_shapeOK x todo kept st (inv.drop fun w h => by rw [hw] at h; cases h)
    | some w =>
      simp only
      by_cases watching : w.w1 = x ∨ w.w2 = x
      · rw [if_pos watching]
        have shape := inv.shape w (mem_of_getElem? hw)
        unfold visit
        by_cases sat : (w.other x).compl ∈ st.lits
        · rw [if_pos sat]
          refine processList_shapeOK x todo (i :: kept) st (inv.keep hw ?_)
          rcases other_watch (w := w) (x := x) with h | h
          · exact ⟨w.other x, by rw [h]; exact shape.2.1, sat⟩
          · exact ⟨w.other x, by rw [h]; exact shape.2.2, sat⟩
        · rw [if_neg sat]
          cases hfind : w.nogood.lits.find? (fun r => decide (r ≠ x ∧ r ≠ w.other x ∧ r ∉ st.lits)) with
          | some r =>
            simp only
            have pred := List.find?_some hfind
            simp only [decide_eq_true_eq] at pred
            exact processList_shapeOK x todo kept _
              (inv.move hw watching (List.mem_of_find?_eq_some hfind) pred.1 pred.2.1 pred.2.2)
          | none =>
            simp only
            by_cases on : w.other x ∈ st.lits
            · rw [if_pos on]
              exact inv.conflictShape
            · rw [if_neg on]
              exact processList_shapeOK x todo (i :: kept) _ (inv.unit hw on sat)
      · rw [if_neg watching]
        exact processList_shapeOK x todo kept st (inv.drop fun w' h => by rw [hw] at h; cases h; exact watching)

/-- A reported conflict of propagation keeps the data part of the invariant. -/
def Outcome.ShapeOK (Δ : List (Nogood A)) : Outcome A → Prop
  | .conflict _ st => WShape Δ st
  | _ => True

/-- **Propagation by watches keeps the data part of the invariant at a conflict.** -/
theorem propagateWatched_shapeOK {Δ : List (Nogood A)} :
    ∀ (fuel : ℕ) (st : WState A), WInv Δ st → (propagateWatched fuel st).ShapeOK Δ
  | 0, _, _ => trivial
  | fuel + 1, st, inv => by
    unfold propagateWatched
    cases hp : st.pending with
    | nil => trivial
    | cons x rest =>
      simp only
      have shape := processList_shapeOK x (st.watches x) [] { st with pending := rest } (inv.start hp)
      have pass := processList_spec x (st.watches x) [] { st with pending := rest } (inv.start hp)
      cases hpass : processList x { st with pending := rest } (st.watches x) [] with
      | ok st' =>
        dsimp only
        rw [hpass] at pass
        exact propagateWatched_shapeOK fuel st' pass.1
      | conflict δ st' =>
        dsimp only
        rw [hpass] at shape
        exact shape

/-- Unit propagation pushes only literals of its nogoods. -/
theorem upSteps_vars {Δ : List (Nogood A)} {V : Finset (Var A)} (hΔ : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, l.var ∈ V)
    {t t' : List (Entry A)} (reach : ReflTransGen (UPStep Δ) t t') (ht : ∀ e ∈ t, e.lit.var ∈ V) :
    ∀ e ∈ t', e.lit.var ∈ V := by
  induction reach with
  | refl => exact ht
  | tail _ step ih =>
    cases step with
    | unit hδ unit =>
      rintro e (_ | ⟨_, he⟩)
      · exact (hΔ _ hδ _ unit.1 : _)
      · exact ih e he

/-- A trail of distinct variables from `V` is no longer than `V`. -/
theorem trail_length_le_card {t : List (Entry A)} {V : Finset (Var A)} (nodup : (t.map fun e => e.lit.var).Nodup)
    (vars : ∀ e ∈ t, e.lit.var ∈ V) : t.length ≤ V.card := by
  classical
  have card := List.toFinset_card_of_nodup nodup
  rw [List.length_map] at card
  rw [← card]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact vars e he

/-- **Fuel for watched propagation.** Each processed literal lowers `|pending| + (|V| - |trail|)`
by one, so fuel above it never runs out. -/
theorem propagateWatched_ne_outOfFuel {Δ : List (Nogood A)} {V : Finset (Var A)}
    (hΔ : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, l.var ∈ V) :
    ∀ (fuel : ℕ) (st : WState A), WInv Δ st → (∀ e ∈ st.trail, e.lit.var ∈ V) →
      st.pending.length + (V.card - st.trail.length) < fuel → ∀ st', propagateWatched fuel st ≠ .outOfFuel st'
  | 0, _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | fuel + 1, st, inv, vars, bound, st' => by
    unfold propagateWatched
    cases hp : st.pending with
    | nil => simp
    | cons x rest =>
      simp only
      have pass := processList_spec x (st.watches x) [] { st with pending := rest } (inv.start hp)
      have ext := processList_extends x (st.watches x) [] { st with pending := rest }
      cases hpass : processList x { st with pending := rest } (st.watches x) [] with
      | conflict δ st'' => simp
      | ok st'' =>
        dsimp only
        rw [hpass] at pass ext
        obtain ⟨winv, reach⟩ := pass
        obtain ⟨new, htrail, hpend⟩ := ext
        have vars' := upSteps_vars hΔ reach vars
        have length := trail_length_le_card winv.nodup vars'
        apply propagateWatched_ne_outOfFuel hΔ fuel st'' winv vars'
        rw [hp, List.length_cons] at bound
        have ht : st''.trail.length = new.length + st.trail.length := by
          rw [htrail, List.length_append]
        have hpl : st''.pending.length = new.length + rest.length := by
          rw [hpend, List.length_append, List.length_map]
        omega

/-- **One more than the number of variables suffices** when the pending literals are distinct and
on the trail. -/
theorem propagateWatched_ne_outOfFuel_of_nodup {Δ : List (Nogood A)} {V : Finset (Var A)}
    (hΔ : ∀ δ ∈ Δ, ∀ l ∈ δ.lits, l.var ∈ V) {st : WState A} (inv : WInv Δ st)
    (vars : ∀ e ∈ st.trail, e.lit.var ∈ V) (pending : st.pending.Nodup) {fuel : ℕ} (enough : V.card + 1 ≤ fuel) :
    ∀ st', propagateWatched fuel st ≠ .outOfFuel st' := by
  apply propagateWatched_ne_outOfFuel hΔ fuel st inv vars
  have sub : st.pending.length ≤ st.trail.length := by
    have sub : st.pending.Subperm st.lits := pending.subperm fun y hy => inv.pending y hy
    simpa [WState.lits] using sub.length_le
  have := trail_length_le_card inv.nodup vars
  omega

/-! ## Pushing, re-queueing and watching learned nogoods -/

/-- Push an entry and make its literal pending. -/
def WState.pushLit (ws : WState A) (e : Entry A) : WState A :=
  { ws with trail := e :: ws.trail, pending := e.lit :: ws.pending }

omit [DecidableEq A] in
/-- **Pushing an unassigned literal and making it pending keeps the invariant.** -/
theorem WInv.push {Δ : List (Nogood A)} {st : WState A} (inv : WInv Δ st) (e : Entry A)
    (unassigned : ¬ (onTrail st.trail).Assigned e.lit.var) : WInv Δ (st.pushLit e) where
  db := inv.db
  shape := inv.shape
  index := inv.index
  watch := by
    intro i w hw
    rcases inv.watch i w hw with sat | watched
    · exact Or.inl (sat.mono fun l hl => List.mem_cons_of_mem _ hl)
    · right
      intro y hy on
      simp only [WState.pushLit, WState.lits, List.map_cons] at on ⊢
      rcases List.mem_cons.mp on with rfl | on
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (watched y hy on)
  pending := by
    intro y hy
    simp only [WState.pushLit, WState.lits, List.map_cons] at hy ⊢
    rcases List.mem_cons.mp hy with rfl | hy
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (inv.pending y hy)
  nodup := by
    simp only [WState.pushLit, List.map_cons]
    exact List.nodup_cons.mpr ⟨fun h => unassigned (by
      obtain ⟨f, hf, same⟩ := List.mem_map.mp h
      exact ⟨f, hf, same⟩), inv.nodup⟩

omit [DecidableEq A] in
/-- **Re-queueing a trail restores the invariant**: with every literal of the new trail pending, the
data part is all that is needed. -/
theorem WShape.requeue {Δ : List (Nogood A)} {st : WState A} (h : WShape Δ st) (t : List (Entry A))
    (nodup : (t.map fun e => e.lit.var).Nodup) :
    WInv Δ { st with trail := t, pending := t.map Entry.lit } where
  db := h.db
  shape := h.shape
  index := h.index
  watch := fun _ _ _ => Or.inr fun _ _ on => on
  pending := fun _ hy => hy
  nodup := nodup

/-- Add `i` to the watch list of `y`. -/
def addWatch (watches : Lit A → List ℕ) (y : Lit A) (i : ℕ) : Lit A → List ℕ :=
  Function.update watches y (i :: watches y)

theorem mem_addWatch_of_mem {watches : Lit A → List ℕ} {y z : Lit A} {i j : ℕ} (h : j ∈ watches z) :
    j ∈ addWatch watches y i z := by
  unfold addWatch
  by_cases same : z = y
  · subst same
    rw [Function.update_self]
    exact List.mem_cons_of_mem _ h
  · rw [Function.update_of_ne same]
    exact h

theorem mem_addWatch_self (watches : Lit A → List ℕ) (y : Lit A) (i : ℕ) : i ∈ addWatch watches y i y := by
  unfold addWatch
  rw [Function.update_self]
  exact List.mem_cons_self

/-- Watch a new nogood: append it to the database and index it under both watches. -/
def WState.addWatched (st : WState A) (w : Watched A) : WState A :=
  { st with
    db := st.db ++ [w]
    watches := addWatch (addWatch st.watches w.w1 st.db.length) w.w2 st.db.length }

/-- **Watching a new nogood keeps the data part of the invariant.** -/
theorem WShape.addWatched {Δ : List (Nogood A)} {st : WState A} (h : WShape Δ st) (w : Watched A)
    (hw : w.w1 ≠ w.w2 ∧ w.w1 ∈ w.nogood.lits ∧ w.w2 ∈ w.nogood.lits) :
    WShape (Δ ++ [w.nogood]) (st.addWatched w) where
  db := by
    simp only [WState.addWatched, List.map_append, List.map_singleton, h.db]
  shape := by
    intro w' hw'
    simp only [WState.addWatched, List.mem_append, List.mem_singleton] at hw'
    rcases hw' with hw' | rfl
    · exact h.shape w' hw'
    · exact hw
  index := by
    intro i w' hw'
    simp only [WState.addWatched] at hw' ⊢
    rw [List.getElem?_append] at hw'
    split at hw'
    · have old := h.index i w' hw'
      exact ⟨mem_addWatch_of_mem (mem_addWatch_of_mem old.1), mem_addWatch_of_mem (mem_addWatch_of_mem old.2)⟩
    · rename_i ge
      rw [List.getElem?_singleton] at hw'
      split at hw'
      · rename_i zero
        cases hw'
        have same : i = st.db.length := by omega
        subst same
        exact ⟨mem_addWatch_of_mem (mem_addWatch_self _ _ _), mem_addWatch_self _ _ _⟩
      · cases hw'

/-- A nogood without two distinct literals: all its literals are equal. -/
def AllSame (lits : List (Lit A)) : Prop := ∀ m ∈ lits, ∀ n ∈ lits, m = n

theorem twoWatches_none {lits : List (Lit A)} (h : twoWatches lits = none) : AllSame lits := by
  cases lits with
  | nil => intro m hm; cases hm
  | cons l rest =>
    simp only [twoWatches, Option.map_eq_none_iff, List.find?_eq_none, ne_eq, decide_eq_true_eq,
      not_not] at h
    have all : ∀ m ∈ l :: rest, m = l := by
      rintro m (_ | ⟨_, hm⟩)
      · rfl
      · exact h m hm
    intro m hm n hn
    rw [all m hm, all n hn]

omit [DecidableEq A] in
/-- A literal and its complement are never both on a trail of distinct variables. -/
theorem consistent_of_nodup {t : List (Entry A)} (nodup : (t.map fun e => e.lit.var).Nodup) {m : Lit A}
    (hm : m ∈ t.map Entry.lit) (hc : m.compl ∈ t.map Entry.lit) : False := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
  obtain ⟨f, hf, same⟩ := List.mem_map.mp hc
  have := List.inj_on_of_nodup_map nodup hf he (by show f.lit.var = e.lit.var; rw [same]; rfl)
  subst this
  exact Lit.compl_ne _ same.symm

omit [DecidableEq A] in
/-- **A satisfied nogood is neither falsified nor unit.** -/
theorem Satisfied.quiet {t : List (Entry A)} (nodup : (t.map fun e => e.lit.var).Nodup) {δ : Nogood A}
    (sat : Satisfied (t.map Entry.lit) δ) : ¬ (onTrail t).Falsifies δ ∧ ∀ l, ¬ (onTrail t).UnitOn δ l := by
  obtain ⟨m, hm, hc⟩ := sat
  refine ⟨fun falsified => consistent_of_nodup nodup (falsified m hm) hc, fun l unit => ?_⟩
  by_cases ml : m = l
  · subst ml
    obtain ⟨e, he, same⟩ := List.mem_map.mp hc
    exact unit.2.2 ⟨e, he, by rw [same]; rfl⟩
  · exact consistent_of_nodup nodup (unit.2.1 m hm ml) hc

omit [DecidableEq A] in
/-- Unit propagation extends the trail. -/
theorem upSteps_extends {Δ : List (Nogood A)} {t t' : List (Entry A)} (reach : ReflTransGen (UPStep Δ) t t') :
    ∃ new, t' = new ++ t := by
  induction reach with
  | refl => exact ⟨[], rfl⟩
  | tail _ step ih =>
    obtain ⟨new, rfl⟩ := ih
    cases step with
    | unit _ _ => exact ⟨_ :: new, rfl⟩

/-! ## Short nogoods -/

/-- The result of scanning the short nogoods. -/
inductive Scan (A : Type u)
  | ok (ws : WState A)
  | conflict (δ : Nogood A) (ws : WState A)

/-- **Scan the short nogoods**, those without two distinct literals: a nogood whose literal is on
the trail is falsified; one whose literal's complement is on the trail is satisfied; otherwise the
complement is pushed and made pending. -/
def scanShort : List (Nogood A) → WState A → Scan A
  | [], ws => .ok ws
  | δ :: rest, ws =>
    match δ.lits with
    | [] => .conflict δ ws
    | l :: _ =>
      if l ∈ ws.lits then .conflict δ ws
      else if l.compl ∈ ws.lits then scanShort rest ws
      else scanShort rest (ws.pushLit ⟨l.compl, levelOf ws.trail, some δ⟩)

/-- What scanning the nogoods `l`, drawn from `S`, establishes from the trail `t` and the pending
literals `pend`. -/
def ScanOK (S Δ : List (Nogood A)) (t : List (Entry A)) (pend : List (Lit A)) (l : List (Nogood A)) :
    Scan A → Prop
  | .ok ws => WInv Δ ws ∧ ReflTransGen (UPStep S) t ws.trail ∧
      (∃ new : List (Entry A), ws.trail = new ++ t ∧ ws.pending = new.map Entry.lit ++ pend) ∧
      ∀ δ ∈ l, Satisfied ws.lits δ
  | .conflict δ ws => δ ∈ S ∧ (onTrail ws.trail).Falsifies δ ∧ WInv Δ ws ∧ ReflTransGen (UPStep S) t ws.trail

omit [DecidableEq A] in
theorem ScanOK.extend {S Δ : List (Nogood A)} {t t' : List (Entry A)} {pend pend' : List (Lit A)}
    {δ : Nogood A} {l : List (Nogood A)} {r : Scan A} (reach : ReflTransGen (UPStep S) t t')
    (new₀ : List (Entry A)) (ht : t' = new₀ ++ t) (hp : pend' = new₀.map Entry.lit ++ pend)
    (sat : Satisfied (t'.map Entry.lit) δ) (h : ScanOK S Δ t' pend' l r) : ScanOK S Δ t pend (δ :: l) r := by
  cases r with
  | ok ws =>
    obtain ⟨winv, reach', ⟨new, htrail, hpend⟩, sats⟩ := h
    refine ⟨winv, reach.trans reach', ⟨new ++ new₀, by rw [htrail, ht, List.append_assoc],
      by rw [hpend, hp, List.map_append, List.append_assoc]⟩, ?_⟩
    rintro δ' (_ | ⟨_, hδ'⟩)
    · refine sat.mono fun m hm => ?_
      simp only [WState.lits, htrail, List.map_append, List.mem_append]
      exact Or.inr hm
    · exact sats δ' hδ'
  | conflict δ' ws =>
    obtain ⟨mem, falsified, winv, reach'⟩ := h
    exact ⟨mem, falsified, winv, reach.trans reach'⟩

/-- **Scanning the short nogoods is unit propagation**, keeps the watch invariant, and leaves every
scanned nogood satisfied unless it reports a falsified one. -/
theorem scanShort_spec {S Δ : List (Nogood A)} :
    ∀ (l : List (Nogood A)) (ws : WState A), (∀ δ ∈ l, δ ∈ S) → (∀ δ ∈ l, AllSame δ.lits) → WInv Δ ws →
      ScanOK S Δ ws.trail ws.pending l (scanShort l ws)
  | [], ws, _, _, inv => ⟨inv, .refl, ⟨[], rfl, rfl⟩, fun _ h => absurd h List.not_mem_nil⟩
  | δ :: rest, ws, within, same, inv => by
    have withinRest : ∀ δ' ∈ rest, δ' ∈ S := fun δ' h => within δ' (List.mem_cons_of_mem _ h)
    have sameRest : ∀ δ' ∈ rest, AllSame δ'.lits := fun δ' h => same δ' (List.mem_cons_of_mem _ h)
    have hδ := within δ List.mem_cons_self
    have hsame := same δ List.mem_cons_self
    unfold scanShort
    split
    · rename_i empty
      refine ⟨hδ, ?_, inv, .refl⟩
      intro m hm
      rw [empty] at hm
      cases hm
    · rename_i l tail hlits
      have all : ∀ m ∈ δ.lits, m = l := fun m hm => hsame m hm l (by rw [hlits]; exact List.mem_cons_self)
      split
      · rename_i on
        exact ⟨hδ, fun m hm => (all m hm) ▸ on, inv, .refl⟩
      · rename_i off
        split
        · rename_i sat
          exact ScanOK.extend .refl [] rfl rfl ⟨l, by rw [hlits]; exact List.mem_cons_self, sat⟩
            (scanShort_spec rest ws withinRest sameRest inv)
        · rename_i unsat
          have unassigned : ¬ (onTrail ws.trail).Assigned l.var := by
            rintro ⟨e, he, hvar⟩
            rcases Lit.eq_or_eq_compl hvar with h | h
            · exact off (h ▸ List.mem_map_of_mem he)
            · exact unsat (by rw [← h]; exact List.mem_map_of_mem he)
          have step : UPStep S ws.trail (⟨l.compl, levelOf ws.trail, some δ⟩ :: ws.trail) := by
            refine UPStep.unit hδ ⟨by rw [hlits]; exact List.mem_cons_self, fun m hm ne => absurd (all m hm) ne, ?_⟩
            exact unassigned
          have inv' := inv.push ⟨l.compl, levelOf ws.trail, some δ⟩ (by simpa [Lit.compl] using unassigned)
          exact ScanOK.extend (.single step) [⟨l.compl, levelOf ws.trail, some δ⟩] rfl rfl
            ⟨l, by rw [hlits]; exact List.mem_cons_self, by simp⟩
            (scanShort_spec rest _ withinRest sameRest inv')

/-! ## The driver state -/

/-- **The state of the reference driver.** -/
structure DState (A : Type u) where
  /-- The trail, the watched nogoods, the watch lists and the pending literals. -/
  ws : WState A
  /-- The learned nogoods, newest first. -/
  learned : List (Nogood A)
  /-- The nogoods without two distinct literals, which are scanned instead of watched. -/
  short : List (Nogood A)
  /-- The source pointers of the last unfounded-set check. -/
  src : List (A × Rule A)
  /-- The emitted certificate. -/
  book : Book A

/-- The solver state a driver state stands for. -/
def DState.spec (st : DState A) : State A := ⟨st.ws.trail, st.learned, 0⟩

namespace Program

variable (P : Program A)

theorem varFinset_card : P.varFinset.card = P.varList.length := by
  rw [varFinset, List.card_toFinset]
  rfl

/-- **The driver invariant**: the run so far is an emitting run and a run of the discipline; the
watched and short nogoods are exactly the completion and learned nogoods. -/
structure Good (st : DState A) : Prop where
  emit : P.EmitReachable (.running st.spec) st.book
  cdnl : P.CDNLReachable (.running st.spec)
  dbIn : ∀ δ ∈ st.ws.db.map Watched.nogood, δ ∈ P.completionNogoods ∨ δ ∈ st.learned
  shortIn : ∀ δ ∈ st.short, δ ∈ P.completionNogoods ∨ δ ∈ st.learned
  shortSame : ∀ δ ∈ st.short, AllSame δ.lits
  cover : ∀ δ, δ ∈ P.completionNogoods ∨ δ ∈ st.learned → δ ∈ st.ws.db.map Watched.nogood ∨ δ ∈ st.short

variable {P}

theorem Good.inv {st : DState A} (g : P.Good st) : P.Inv st.spec :=
  P.reachable_inv (P.emitReachable_reachable g.emit)

theorem Good.named {st : DState A} (g : P.Good st) {δ : Nogood A}
    (h : δ ∈ P.completionNogoods ∨ δ ∈ st.learned) : Named st.book δ.lits := by
  rcases h with h | h
  · exact (P.emitReachable_inv g.emit).1.completion δ h
  · exact ((P.emitReachable_inv g.emit).2 _ rfl).2 δ h

theorem Good.vars {st : DState A} (g : P.Good st) {δ : Nogood A}
    (h : δ ∈ P.completionNogoods ∨ δ ∈ st.learned) : ∀ l ∈ δ.lits, P.IsVar l.var := by
  rcases h with h | h
  · exact P.completionNogoods_vars h
  · exact g.inv.learnedVars δ h

theorem Good.trail_vars {st : DState A} (g : P.Good st) : ∀ e ∈ st.ws.trail, e.lit.var ∈ P.varFinset :=
  fun e he => (P.mem_varFinset).mpr (g.inv.vars e he)

theorem Good.trail_length {st : DState A} (g : P.Good st) : st.ws.trail.length ≤ P.varList.length := by
  have := P.trail_length_le g.inv
  rw [P.varFinset_card] at this
  exact this

variable (P)

/-- **Unit propagation by named database nogoods is an emitting run and a run of the discipline.** -/
theorem upSteps_emit {Δ L : List (Nogood A)} {b : Book A}
    (hΔ : ∀ δ ∈ Δ, (δ ∈ P.completionNogoods ∨ δ ∈ L) ∧ Named b δ.lits ∧ ∀ l ∈ δ.lits, P.IsVar l.var)
    {t t' : List (Entry A)} (reach : ReflTransGen (UPStep Δ) t t')
    (emit : P.EmitReachable (.running ⟨t, L, 0⟩) b) (cdnl : P.CDNLReachable (.running ⟨t, L, 0⟩)) :
    P.EmitReachable (.running ⟨t', L, 0⟩) b ∧ P.CDNLReachable (.running ⟨t', L, 0⟩) := by
  induction reach with
  | refl => exact ⟨emit, cdnl⟩
  | @tail t₁ t₂ _ step ih =>
    cases step with
    | @unit δ l hδ unit =>
      obtain ⟨member, named, vars⟩ := hΔ δ hδ
      have database : P.InDatabase ⟨t₁, L, 0⟩ δ := by
        rcases member with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      exact ⟨ih.1.tail (P.propagate_emit ih.1 database unit (vars l unit.1) named),
        ih.2.tail (CDNL.propagate database unit (vars l unit.1))⟩

/-- Push the atoms `new` of the unfounded set `M` false, each with its loop nogood as reason after
naming that nogood by a loop step. -/
def pushUnfounded (M : List A) : List A → WState A → Book A → WState A × Book A
  | [], ws, b => (ws, b)
  | a :: rest, ws, b =>
    pushUnfounded M rest (ws.pushLit ⟨fAtom a, levelOf ws.trail, some (P.loopNogood M.toFinset a)⟩)
      (P.emitLoop b M a)

theorem unfoundedBy_mono {assigned assigned' : List (Lit A)} {U : Finset A} (h : P.UnfoundedBy assigned U)
    (sub : ∀ l ∈ assigned, l ∈ assigned') : P.UnfoundedBy assigned' U := by
  intro r hr head
  rcases h r hr head with h | h
  · exact Or.inl (sub _ h)
  · exact Or.inr h

/-- **Unfounded atoms are pushed by emitting steps of the discipline.** -/
theorem pushUnfounded_spec (M : List A) (hM : ∀ x ∈ M, P.IsVar (.atom x)) (hF : ∀ x ∈ M, ¬ P.Falsum x)
    {L Δ : List (Nogood A)} :
    ∀ (new : List A) (ws : WState A) (b : Book A), new.Nodup → (∀ a ∈ new, a ∈ M) →
      (∀ a ∈ new, ¬ (onTrail ws.trail).Assigned (.atom a)) → P.UnfoundedBy ws.lits M.toFinset →
      P.EmitReachable (.running ⟨ws.trail, L, 0⟩) b → P.CDNLReachable (.running ⟨ws.trail, L, 0⟩) → WInv Δ ws →
      P.EmitReachable (.running ⟨(P.pushUnfounded M new ws b).1.trail, L, 0⟩) (P.pushUnfounded M new ws b).2 ∧
        P.CDNLReachable (.running ⟨(P.pushUnfounded M new ws b).1.trail, L, 0⟩) ∧
        WInv Δ (P.pushUnfounded M new ws b).1 ∧
        ∃ pushed : List (Entry A), (P.pushUnfounded M new ws b).1.trail = pushed ++ ws.trail ∧
          (P.pushUnfounded M new ws b).1.pending = pushed.map Entry.lit ++ ws.pending ∧
          pushed.length = new.length
  | [], ws, b, _, _, _, _, emit, cdnl, winv => ⟨emit, cdnl, winv, [], rfl, rfl, rfl⟩
  | a :: rest, ws, b, nodup, within, unassigned, unfounded, emit, cdnl, winv => by
    have ha := within a List.mem_cons_self
    have hun := unassigned a List.mem_cons_self
    set δ := P.loopNogood M.toFinset a with hδ
    have unit : (⟨ws.trail, L, 0⟩ : State A).UnitOn δ (tAtom a) :=
      ⟨List.mem_cons_self, P.loopNogood_unit_of_unfounded unfounded a, hun⟩
    have database : P.InDatabase ⟨ws.trail, L, 0⟩ δ :=
      Or.inr (Or.inr ⟨M.toFinset, fun x hx => hF x (List.mem_toFinset.mp hx), a, List.mem_toFinset.mpr ha, rfl⟩)
    have emit₁ : P.EmitReachable (.running ⟨ws.trail, L, 0⟩) (P.emitLoop b M a) := emit.tail (Emit.loop ha hM hF)
    have named : Named (P.emitLoop b M a) δ.lits := named_self _ _ _ _ _ _
    have emit₂ := emit₁.tail (P.propagate_emit emit₁ database unit (hM a ha) named)
    have cdnl₂ := cdnl.tail (CDNL.propagate database unit (hM a ha))
    have winv₂ := winv.push ⟨fAtom a, levelOf ws.trail, some δ⟩ hun
    have rest' := pushUnfounded_spec M hM hF rest (ws.pushLit ⟨fAtom a, levelOf ws.trail, some δ⟩) (P.emitLoop b M a)
      (List.nodup_cons.mp nodup).2 (fun x hx => within x (List.mem_cons_of_mem _ hx))
      (by
        intro x hx
        rintro ⟨e, (_ | ⟨_, he⟩), same⟩
        · exact (List.nodup_cons.mp nodup).1 (by cases same; exact hx)
        · exact unassigned x (List.mem_cons_of_mem _ hx) ⟨e, he, same⟩)
      (P.unfoundedBy_mono unfounded fun l hl => List.mem_cons_of_mem _ hl) emit₂ cdnl₂ winv₂
    obtain ⟨emit₃, cdnl₃, winv₃, pushed, htrail, hpend, hlen⟩ := rest'
    refine ⟨emit₃, cdnl₃, winv₃, pushed ++ [⟨fAtom a, levelOf ws.trail, some δ⟩], ?_, ?_, ?_⟩
    · exact htrail.trans (by simp [WState.pushLit])
    · exact hpend.trans (by simp [WState.pushLit])
    · simp [hlen]

/-! ## The combined loop -/

omit [DecidableEq A] in
theorem _root_.Mettapedia.Logic.ASP.WInv.self {Δ : List (Nogood A)} {st : WState A} (h : WInv Δ st) :
    WInv (st.db.map Watched.nogood) st := by
  rw [h.db]
  exact h

omit [DecidableEq A] in
theorem _root_.Mettapedia.Logic.ASP.WShape.self {Δ : List (Nogood A)} {st : WState A} (h : WShape Δ st) :
    WShape (st.db.map Watched.nogood) st := by
  rw [h.db]
  exact h

omit [DecidableEq A] in
theorem assigned_iff {t : List (Entry A)} {x : Var A} :
    (onTrail t).Assigned x ↔ (⟨x, true⟩ : Lit A) ∈ t.map Entry.lit ∨ (⟨x, false⟩ : Lit A) ∈ t.map Entry.lit := by
  constructor
  · rintro ⟨e, he, hvar⟩
    obtain ⟨⟨y, b⟩, level, reason⟩ := e
    simp only at hvar
    subst hvar
    cases b
    · exact Or.inr (List.mem_map_of_mem (f := Entry.lit) he)
    · exact Or.inl (List.mem_map_of_mem (f := Entry.lit) he)
  · rintro (h | h) <;>
    · obtain ⟨e, he, same⟩ := List.mem_map.mp h
      exact ⟨e, he, by rw [same]⟩

omit [DecidableEq A] in
theorem nodup_lits_of_prefix {new t : List (Entry A)} (h : ((new ++ t).map fun e => e.lit.var).Nodup) :
    (new.map Entry.lit).Nodup := by
  rw [List.map_append] at h
  have vars := (List.nodup_append.mp h).1
  apply List.Nodup.of_map Lit.var
  rw [List.map_map]
  exact vars

/-- **Closed under both propagators**: no completion or learned nogood is unit or falsified, and
every program atom of an unfounded set is assigned false. -/
def Propagated (L : List (Nogood A)) (t : List (Entry A)) : Prop :=
  (∀ δ, δ ∈ P.completionNogoods ∨ δ ∈ L → ¬ (onTrail t).Falsifies δ ∧ ∀ l, ¬ (onTrail t).UnitOn δ l) ∧
    ∀ (U : Finset A), P.UnfoundedBy (t.map Entry.lit) U → ∀ a ∈ U, a ∈ P.atomSet → fAtom a ∈ t.map Entry.lit

/-- The unfounded set of the driver: the marked atoms that are not falsum atoms, in atom order. -/
def loopMarked (lits : List (Lit A)) (src : List (A × Rule A)) : List A :=
  (P.marked lits src).filter fun a => !P.falsum a

theorem mem_loopMarked {lits : List (Lit A)} {src : List (A × Rule A)} {a : A} :
    a ∈ P.loopMarked lits src ↔ a ∈ P.marked lits src ∧ ¬ P.Falsum a := by
  simp [loopMarked, ← P.falsum_iff]

theorem loopMarked_isVar {lits : List (Lit A)} {src : List (A × Rule A)} :
    ∀ x ∈ P.loopMarked lits src, P.IsVar (.atom x) :=
  fun _ hx => (P.mem_allAtoms).mp (List.mem_filter.mp ((P.mem_loopMarked).mp hx).1).1

/-- The completion nogoods are neither unit nor falsified on the trail. -/
def Quiet (t : List (Entry A)) : Prop :=
  ∀ δ ∈ P.completionNogoods, ¬ (onTrail t).Falsifies δ ∧ ∀ l, ¬ (onTrail t).UnitOn δ l

theorem bodyPos_mem_completion {r : Rule A} (hr : r ∈ P) (hf : ¬ P.Falsum r.head) (hu : ¬ r.body.IsUnit)
    {b : A} (hb : b ∈ r.pos) :
    (⟨[tBody r.body, fAtom b], .bodyPos r.body b⟩ : Nogood A) ∈ P.completionNogoods := by
  have : (⟨[tBody r.body, fAtom b], .bodyPos r.body b⟩ : Nogood A) ∈ bodyNogoods r.body := by
    rw [bodyNogoods, if_neg hu]
    exact List.mem_append_left _ (List.mem_cons_of_mem _
      (List.mem_map_of_mem (f := fun a => (⟨[tBody r.body, fAtom a], .bodyPos r.body a⟩ : Nogood A)) hb))
  refine List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, ?_⟩)
  rw [ruleNogoods, if_neg (P.falsum_ne_true hf)]
  exact List.mem_cons_of_mem _ this

variable {P}

/-- **A falsum atom is false at a quiet trail**: its support nogood is the unit `T f`. -/
theorem Quiet.falsum_false {t : List (Entry A)} (quiet : P.Quiet t) {f : A} (hf : P.Falsum f)
    (program : f ∈ P.atomSet) : fAtom f ∈ t.map Entry.lit := by
  have member : P.supportNogood f ∈ P.completionNogoods :=
    List.mem_append_right _ (List.mem_map_of_mem ((P.mem_allAtoms).mpr program))
  have lits : (P.supportNogood f).lits = [tAtom f] := by
    simp [supportNogood, (P.falsum_iff).mpr hf]
  obtain ⟨notFalsified, notUnit⟩ := quiet _ member
  have notTrue : tAtom f ∉ t.map Entry.lit := fun on => notFalsified fun m hm => by
    rw [lits, List.mem_singleton] at hm
    subst hm
    exact on
  have assigned : (onTrail t).Assigned (.atom f) := by
    by_contra unassigned
    refine notUnit (tAtom f) ⟨by rw [lits]; exact List.mem_cons_self, fun m hm ne => ?_, unassigned⟩
    rw [lits, List.mem_singleton] at hm
    exact absurd hm ne
  rcases assigned_iff.mp assigned with h | h
  · exact absurd h notTrue
  · exact h

/-- **A body with a false positive atom is false at a quiet trail**, for a rule of an atom that is
no falsum atom: the complement of its literal is on the trail. A unit body `b` is `F b` itself;
otherwise the nogood `{T B, F b}` would be unit or falsified. -/
theorem Quiet.body_false {t : List (Entry A)} (quiet : P.Quiet t) {r : Rule A} (hr : r ∈ P)
    (hf : ¬ P.Falsum r.head) {b : A} (hb : b ∈ r.pos) (bFalse : fAtom b ∈ t.map Entry.lit) :
    r.body.lit.compl ∈ t.map Entry.lit := by
  by_cases hu : r.body.IsUnit
  · rcases Body.isUnit_iff.mp hu with ⟨a, same⟩ | ⟨c, same⟩
    · have pos : r.pos = [a] := congrArg Body.pos same
      rw [pos, List.mem_singleton] at hb
      subst hb
      rw [same]
      exact bFalse
    · have pos : r.pos = [] := congrArg Body.pos same
      rw [pos] at hb
      exact absurd hb List.not_mem_nil
  rw [Body.lit_of_not_isUnit hu]
  have q := quiet _ (P.bodyPos_mem_completion hr hf hu hb)
  have notTrue : tBody r.body ∉ t.map Entry.lit := fun on => q.1 fun m hm => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact on
    · exact bFalse
  have assigned : (onTrail t).Assigned (.body r.body) := by
    by_contra unassigned
    apply q.2 (tBody r.body)
    refine ⟨List.mem_cons_self, fun m hm ne => ?_, unassigned⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · exact absurd rfl ne
    · exact bFalse
  rcases assigned_iff.mp assigned with h | h
  · exact absurd h notTrue
  · exact h

/-- **The driver's unfounded set is unfounded at a quiet trail.** A rule for one of its atoms is
handled by the greatest unfounded set, unless its unfounded positive atom is a falsum atom; that
atom is false by its unit nogood, and so is the rule's body. -/
theorem Quiet.loopMarked_unfounded {t : List (Entry A)} (quiet : P.Quiet t) (src : List (A × Rule A)) :
    P.UnfoundedBy (t.map Entry.lit) (P.loopMarked (t.map Entry.lit) src).toFinset := by
  intro r hr head
  rw [List.mem_toFinset, P.mem_loopMarked] at head
  rcases P.unfoundedCheck_unfounded (t.map Entry.lit) src r hr (List.mem_toFinset.mpr head.1) with h | ⟨b, hb, inside⟩
  · exact Or.inl h
  · by_cases bf : P.Falsum b
    · exact Or.inl (quiet.body_false hr head.2 hb (quiet.falsum_false bf ⟨r, hr, Or.inr (Or.inl hb)⟩))
    · exact Or.inr ⟨b, hb, List.mem_toFinset.mpr ((P.mem_loopMarked).mpr ⟨List.mem_toFinset.mp inside, bf⟩)⟩

variable (P)

/-- What the unfounded-set check decides. -/
inductive UResult (A : Type u)
  /-- A marked atom is true. -/
  | conflict (a : A) (marked : List A) (src : List (A × Rule A))
  /-- Every marked atom is false. -/
  | closed (src : List (A × Rule A))
  /-- Some marked atoms are unassigned. -/
  | push (new marked : List A) (src : List (A × Rule A))

/-- **The unfounded-set step**: run the source-pointer check; of the marked atoms that are not
falsum atoms, report a true one, or the unassigned ones, or that every one is false. -/
def unfoundedStep (lits : List (Lit A)) (src : List (A × Rule A)) : UResult A :=
  let src' := P.sources lits src
  let M := (P.allAtoms.filter fun a => a ∉ src'.map Prod.fst).filter fun a => !P.falsum a
  match M.find? (fun a => decide (tAtom a ∈ lits)) with
  | some a => .conflict a M src'
  | none =>
    match M.filter (fun a => decide (fAtom a ∉ lits)) with
    | [] => .closed src'
    | a :: rest => .push (a :: rest) M src'

/-- What the unfounded-set step establishes. -/
def UResult.OK (lits : List (Lit A)) (src : List (A × Rule A)) : UResult A → Prop
  | .conflict a M _ => M = P.loopMarked lits src ∧ a ∈ M ∧ tAtom a ∈ lits
  | .closed _ => ∀ a ∈ P.loopMarked lits src, fAtom a ∈ lits
  | .push new M _ => M = P.loopMarked lits src ∧ new ≠ [] ∧ new.Nodup ∧
      ∀ a ∈ new, a ∈ M ∧ tAtom a ∉ lits ∧ fAtom a ∉ lits

theorem unfoundedStep_spec (lits : List (Lit A)) (src : List (A × Rule A)) :
    (P.unfoundedStep lits src).OK P lits src := by
  have nodupM : (P.loopMarked lits src).Nodup := ((List.nodup_dedup _).filter _).filter _
  unfold unfoundedStep
  simp only
  split
  · rename_i a hf
    exact ⟨rfl, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩
  · rename_i hf
    have off : ∀ a ∈ P.loopMarked lits src, tAtom a ∉ lits := by
      intro a ha on
      have := List.find?_eq_none.mp hf a ha
      simp only [decide_eq_true_eq] at this
      exact this on
    split
    · rename_i hfilter
      intro a ha
      have := List.filter_eq_nil_iff.mp hfilter a ha
      simpa using this
    · rename_i a rest hfilter
      refine ⟨rfl, List.cons_ne_nil _ _, ?_, ?_⟩
      · rw [← hfilter]
        exact nodupM.filter _
      · intro x hx
        rw [← hfilter] at hx
        obtain ⟨hx, notFalse⟩ := List.mem_filter.mp hx
        exact ⟨hx, off x hx, by simpa using notFalse⟩

/-- The result of propagation. -/
inductive PResult (A : Type u)
  | closed (st : DState A)
  | conflict (δ : Nogood A) (st : DState A)
  | outOfFuel

/-- **The combined propagation loop**: watches to a fixpoint, then the short nogoods, then the
unfounded-set check; repeat while something is pushed. Each round is given one more unit of fuel
than there are variables, and the loop at most that many rounds. -/
def propagateAll : ℕ → DState A → PResult A
  | 0, _ => .outOfFuel
  | n + 1, st =>
    match propagateWatched (P.varList.length + 1) st.ws with
    | .outOfFuel _ => .outOfFuel
    | .conflict δ ws => .conflict δ { st with ws := ws }
    | .fixpoint ws =>
      match scanShort st.short ws with
      | .conflict δ ws' => .conflict δ { st with ws := ws' }
      | .ok ws' =>
        match ws'.pending with
        | _ :: _ => propagateAll n { st with ws := ws' }
        | [] =>
          match P.unfoundedStep ws'.lits st.src with
          | .conflict a M src =>
            .conflict (P.loopNogood M.toFinset a) { st with ws := ws', src := src, book := P.emitLoop st.book M a }
          | .closed src => .closed { st with ws := ws', src := src }
          | .push new M src =>
            let pushed := P.pushUnfounded M new ws' st.book
            propagateAll n { st with ws := pushed.1, src := src, book := pushed.2 }

/-- What propagation establishes, relative to the starting state. -/
def PropOK (st₀ : DState A) : PResult A → Prop
  | .closed st => P.Good st ∧ WInv (st.ws.db.map Watched.nogood) st.ws ∧ st.ws.pending = [] ∧
      st.learned = st₀.learned ∧ (∃ new, st.ws.trail = new ++ st₀.ws.trail) ∧ P.Propagated st.learned st.ws.trail
  | .conflict δ st => P.Good st ∧ WShape (st.ws.db.map Watched.nogood) st.ws ∧ st.learned = st₀.learned ∧
      (∃ new, st.ws.trail = new ++ st₀.ws.trail) ∧ P.InDatabase st.spec δ ∧ Named st.book δ.lits ∧
      st.spec.Falsifies δ
  | .outOfFuel => False

variable {P}

theorem PropOK.trans {st₀ st : DState A} {r : PResult A} (h : P.PropOK st r) (learned : st.learned = st₀.learned)
    (ext : ∃ new, st.ws.trail = new ++ st₀.ws.trail) : P.PropOK st₀ r := by
  obtain ⟨new₀, h₀⟩ := ext
  cases r with
  | closed st' =>
    obtain ⟨good, winv, empty, learned', ⟨new, htrail⟩, closed⟩ := h
    exact ⟨good, winv, empty, learned'.trans learned, ⟨new ++ new₀, by rw [htrail, h₀, List.append_assoc]⟩, closed⟩
  | conflict δ st' =>
    obtain ⟨good, shape, learned', ⟨new, htrail⟩, rest⟩ := h
    exact ⟨good, shape, learned'.trans learned, ⟨new ++ new₀, by rw [htrail, h₀, List.append_assoc]⟩, rest⟩
  | outOfFuel => exact h

/-- After unit propagation by database nogoods, the driver invariant holds of the new trail. -/
theorem Good.of_run {st : DState A} (good : P.Good st) {S : List (Nogood A)}
    (hS : ∀ δ ∈ S, δ ∈ P.completionNogoods ∨ δ ∈ st.learned) {ws : WState A}
    (reach : ReflTransGen (UPStep S) st.ws.trail ws.trail)
    (db : ws.db.map Watched.nogood = st.ws.db.map Watched.nogood) : P.Good { st with ws := ws } := by
  obtain ⟨emit, cdnl⟩ := P.upSteps_emit (L := st.learned) (b := st.book)
    (fun δ h => ⟨hS δ h, good.named (hS δ h), good.vars (hS δ h)⟩) reach good.emit good.cdnl
  refine ⟨emit, cdnl, ?_, good.shortIn, good.shortSame, ?_⟩
  · intro δ h
    exact good.dbIn δ (by rw [← db]; exact h)
  · intro δ h
    rcases good.cover δ h with h | h
    · exact Or.inl (by simp only [db]; exact h)
    · exact Or.inr h

variable (P)

/-- **The combined loop is correct.** From a good driver state with the watch invariant and distinct
pending literals, with enough fuel, it reports a falsified, named database nogood or a closed
state; in both cases the run is an emitting run and a run of the discipline that extends the
trail. -/
theorem propagateAll_spec : ∀ (n : ℕ) (st : DState A), P.Good st → WInv (st.ws.db.map Watched.nogood) st.ws →
    st.ws.pending.Nodup → P.varList.length - st.ws.trail.length < n → P.PropOK st (P.propagateAll n st)
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, st, good, winv, nodup, fuel => by
    have varsV : ∀ δ ∈ st.ws.db.map Watched.nogood, ∀ l ∈ δ.lits, l.var ∈ P.varFinset :=
      fun δ h l hl => (P.mem_varFinset).mpr (good.vars (good.dbIn δ h) l hl)
    have spec := propagateWatched_spec (P.varList.length + 1) st.ws winv
    have shape := propagateWatched_shapeOK (P.varList.length + 1) st.ws winv
    have notOut := propagateWatched_ne_outOfFuel_of_nodup varsV winv good.trail_vars nodup
      (fuel := P.varList.length + 1) (by rw [P.varFinset_card])
    unfold propagateAll
    cases hw : propagateWatched (P.varList.length + 1) st.ws with
    | outOfFuel ws => exact absurd hw (notOut ws)
    | conflict δ ws =>
      rw [hw] at spec shape
      obtain ⟨hδ, falsified, reach⟩ := spec
      have good₁ := good.of_run good.dbIn reach shape.db
      exact ⟨good₁, shape.self, rfl, upSteps_extends reach, Or.elim (good.dbIn δ hδ) Or.inl (fun h => Or.inr (Or.inl h)),
        good.named (good.dbIn δ hδ), falsified⟩
    | fixpoint ws =>
      rw [hw] at spec
      obtain ⟨winv₁, empty, reach⟩ := spec
      have good₁ := good.of_run good.dbIn reach winv₁.db
      have ext₁ := upSteps_extends reach
      dsimp only
      have scan := scanShort_spec (S := st.short) st.short ws (fun δ h => h) good.shortSame winv₁
      cases hs : scanShort st.short ws with
      | conflict δ ws' =>
        rw [hs] at scan
        obtain ⟨hδ, falsified, winv₂, reach₂⟩ := scan
        have good₂ : P.Good { st with ws := ws' } :=
          good₁.of_run (S := st.short) good.shortIn reach₂ (winv₂.db.trans winv₁.db.symm)
        obtain ⟨new₂, h₂⟩ := upSteps_extends reach₂
        obtain ⟨new₁, h₁⟩ := ext₁
        exact ⟨good₂, winv₂.toShape.self, rfl, ⟨new₂ ++ new₁, by rw [h₂, h₁, List.append_assoc]⟩,
          Or.elim (good.shortIn δ hδ) Or.inl (fun h => Or.inr (Or.inl h)), good.named (good.shortIn δ hδ), falsified⟩
      | ok ws' =>
        rw [hs] at scan
        obtain ⟨winv₂, reach₂, ⟨new, htrail, hpend⟩, sats⟩ := scan
        have good₂ : P.Good { st with ws := ws' } :=
          good₁.of_run (S := st.short) good.shortIn reach₂ (winv₂.db.trans winv₁.db.symm)
        obtain ⟨new₁, h₁⟩ := ext₁
        have ext₂ : ∃ new', ws'.trail = new' ++ st.ws.trail := ⟨new ++ new₁, by rw [htrail, h₁, List.append_assoc]⟩
        rw [empty, List.append_nil] at hpend
        dsimp only
        cases hp : ws'.pending with
        | cons y ys =>
          dsimp only
          have nonempty : new ≠ [] := by
            rintro rfl
            rw [hp] at hpend
            cases hpend
          have nodup' : ws'.pending.Nodup := by
            rw [hpend]
            exact nodup_lits_of_prefix (htrail ▸ winv₂.nodup)
          have fuel' : P.varList.length - ws'.trail.length < n := by
            have len := good₂.trail_length
            have : ws'.trail.length = new.length + new₁.length + st.ws.trail.length := by
              rw [htrail, h₁, List.length_append, List.length_append]
              omega
            have pos : 0 < new.length := List.length_pos_iff.mpr nonempty
            change ws'.trail.length ≤ P.varList.length at len
            omega
          exact (propagateAll_spec n { st with ws := ws' } good₂ winv₂.self nodup' fuel').trans rfl ext₂
        | nil =>
          dsimp only
          have ok := P.unfoundedStep_spec ws'.lits st.src
          have nodupTrail := winv₂.nodup
          have quiet : P.Quiet ws'.trail := fun δ hδ =>
            (good.cover δ (Or.inl hδ)).elim (winv₂.quiescent hp δ) fun h => Satisfied.quiet nodupTrail (sats δ h)
          have hF : ∀ x ∈ P.loopMarked ws'.lits st.src, ¬ P.Falsum x := fun x hx => ((P.mem_loopMarked).mp hx).2
          cases hu : P.unfoundedStep ws'.lits st.src with
          | conflict a M src =>
            rw [hu] at ok
            obtain ⟨hM, ha, isTrue⟩ := ok
            subst hM
            set M := P.loopMarked ws'.lits st.src with hMdef
            have emit₃ : P.EmitReachable (.running { st with ws := ws' }.spec) (P.emitLoop st.book M a) :=
              good₂.emit.tail (Emit.loop ha P.loopMarked_isVar hF)
            have good₃ : P.Good { st with ws := ws', src := src, book := P.emitLoop st.book M a } :=
              ⟨emit₃, good₂.cdnl, good₂.dbIn, good₂.shortIn, good₂.shortSame, good₂.cover⟩
            have database : P.InDatabase { st with ws := ws', src := src, book := P.emitLoop st.book M a }.spec
                (P.loopNogood M.toFinset a) :=
              Or.inr (Or.inr ⟨M.toFinset, fun x hx => hF x (List.mem_toFinset.mp hx), a, List.mem_toFinset.mpr ha, rfl⟩)
            have named : Named (P.emitLoop st.book M a) (P.loopNogood M.toFinset a).lits := by
              unfold emitLoop
              exact named_self _ _ _ _ _ _
            have falsified : ({ st with ws := ws' } : DState A).spec.Falsifies (P.loopNogood M.toFinset a) := by
              intro l hl
              by_cases same : l = tAtom a
              · exact same ▸ isTrue
              · exact P.loopNogood_unit_of_unfounded (quiet.loopMarked_unfounded st.src) a l hl same
            exact ⟨good₃, winv₂.toShape.self, rfl, ext₂, database, named, falsified⟩
          | closed src =>
            rw [hu] at ok
            refine ⟨⟨good₂.emit, good₂.cdnl, good₂.dbIn, good₂.shortIn, good₂.shortSame, good₂.cover⟩,
              winv₂.self, hp, rfl, ext₂, ?_, ?_⟩
            · intro δ hδ
              rcases good.cover δ hδ with h | h
              · exact winv₂.quiescent hp δ h
              · exact Satisfied.quiet nodupTrail (sats δ h)
            · intro U unfounded a ha program
              by_cases hf : P.Falsum a
              · exact quiet.falsum_false hf program
              · exact ok a ((P.mem_loopMarked).mpr ⟨P.unfoundedCheck_greatest ws'.lits st.src unfounded ha program, hf⟩)
          | push pushNew M src =>
            rw [hu] at ok
            obtain ⟨hM, nonempty, nodupNew, within⟩ := ok
            subst hM
            dsimp only
            obtain ⟨emit₃, cdnl₃, winv₃, pushed, htrail₃, hpend₃, hlen⟩ :=
              P.pushUnfounded_spec (P.loopMarked ws'.lits st.src) P.loopMarked_isVar hF (L := st.learned) pushNew ws'
                st.book nodupNew
                (fun a ha => (within a ha).1)
                (fun a ha assigned => by
                  rcases assigned_iff.mp assigned with h | h
                  · exact (within a ha).2.1 h
                  · exact (within a ha).2.2 h)
                (quiet.loopMarked_unfounded st.src) good₂.emit good₂.cdnl winv₂
            set r := P.pushUnfounded (P.loopMarked ws'.lits st.src) pushNew ws' st.book with hr
            have good₃ : P.Good { st with ws := r.1, src := src, book := r.2 } :=
              ⟨emit₃, cdnl₃, fun δ h => good.dbIn δ (by rw [← winv₃.db]; exact h), good.shortIn,
                good.shortSame, fun δ h => by
                  rcases good.cover δ h with h | h
                  · exact Or.inl (by show δ ∈ r.1.db.map Watched.nogood; rw [winv₃.db]; exact h)
                  · exact Or.inr h⟩
            have nodup' : r.1.pending.Nodup := by
              rw [hpend₃, hp, List.append_nil]
              exact nodup_lits_of_prefix (htrail₃ ▸ winv₃.nodup)
            have fuel' : P.varList.length - r.1.trail.length < n := by
              have len := good₃.trail_length
              change r.1.trail.length ≤ P.varList.length at len
              have : r.1.trail.length = pushed.length + ws'.trail.length := by
                rw [htrail₃, List.length_append]
              have : ws'.trail.length = new.length + new₁.length + st.ws.trail.length := by
                rw [htrail, h₁, List.length_append, List.length_append]
                omega
              have pos : 0 < pushNew.length := List.length_pos_iff.mpr nonempty
              omega
            obtain ⟨new₂, h₂⟩ := ext₂
            exact (propagateAll_spec n _ good₃ winv₃.self nodup' fuel').trans rfl
              ⟨pushed ++ new₂, by rw [htrail₃, h₂, List.append_assoc]⟩

/-! ## Closed states -/

/-- **No loop nogood is falsified at a closed state**: the atoms of its set that are not false form
an unfounded set containing its true atom. -/
theorem Propagated.loops {L : List (Nogood A)} {t : List (Entry A)} (closed : P.Propagated L t)
    (nodup : (t.map fun e => e.lit.var).Nodup) (vars : ∀ e ∈ t, P.IsVar e.lit.var) (U : Finset A) {a : A}
    (aIn : a ∈ U) :
    ¬ (onTrail t).Falsifies (P.loopNogood U a) := by
  intro falsified
  have isTrue : tAtom a ∈ t.map Entry.lit := falsified _ List.mem_cons_self
  have external : ∀ r ∈ P, ExternalFor U r → r.body.lit.compl ∈ t.map Entry.lit := by
    intro r hr ext
    apply falsified
    simp only [loopNogood, externalBodies, List.mem_cons, List.mem_map, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨r.body, ⟨r, ⟨hr, ext⟩, rfl⟩, rfl⟩
  set U' := U.filter fun x => fAtom x ∉ t.map Entry.lit with hU'
  have unfounded : P.UnfoundedBy (t.map Entry.lit) U' := by
    intro r hr head
    rw [Finset.mem_filter] at head
    by_cases inside : ∃ b ∈ r.pos, b ∈ U
    · obtain ⟨b, hb, bU⟩ := inside
      by_cases bFalse : fAtom b ∈ t.map Entry.lit
      · left
        have quiet : P.Quiet t := fun δ hδ => closed.1 δ (Or.inl hδ)
        have hf : ¬ P.Falsum r.head := fun hf => head.2 (quiet.falsum_false hf ⟨r, hr, Or.inl rfl⟩)
        exact quiet.body_false hr hf hb bFalse
      · right
        exact ⟨b, hb, Finset.mem_filter.mpr ⟨bU, bFalse⟩⟩
    · push Not at inside
      exact Or.inl (external r hr ⟨head.1, inside⟩)
  have notFalse : fAtom a ∉ t.map Entry.lit := fun h => consistent_of_nodup nodup isTrue h
  have program : a ∈ P.atomSet := by
    obtain ⟨e, he, same⟩ := List.mem_map.mp isTrue
    have := vars e he
    rw [same] at this
    exact this
  exact notFalse (closed.2 U' unfounded a (Finset.mem_filter.mpr ⟨aIn, notFalse⟩) program)

end Program

end Propagation

end Mettapedia.Logic.ASP
