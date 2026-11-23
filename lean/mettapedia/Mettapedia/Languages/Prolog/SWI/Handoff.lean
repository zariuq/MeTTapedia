/-
The hand-over of protection from a snapshot to the frame of its goal.

A snapshot keeps the clauses visible in its generation `gs`.  Part A: a
handle of db_snapshot/1 is in the list of open snapshots until it is
closed.  db_snapshot_call/2 stamps the frame of its goal at the call port
(in depart_alerted, after lTop was moved above the frame): the frame gets
`gs` and FR_SNAPSHOT.  The stamp takes no lock, so its stores may still be
in the owner's store buffer.  Only the owner closes the handle, and only
after a stamp that succeeded (a closed handle makes the stamp fail), under
L_MISC.  Clause GC marks the generations of the open snapshots under L_MISC
and then scans the frames.

`handle_safe`: the frame never holds a clause that clause GC reclaimed.
`handle_frames_first_unsafe`: scanning the frames before marking the open
snapshots loses the clause (the surviving mutant r_gc_order).
`handle_close_unsynced_unsafe`: a close that does not order the stamp
before it (no lock) loses it too.

Part B: db_snapshot_scope/2 stamps its own frame under the scan lock of its
thread: the frame reads the global generation and is flagged in one step
with respect to the scan.  `scope_safe`; `scope_split_unsafe`: reading the
generation and flagging the frame in two steps, with the scan between them,
loses the clause.

Other registrations (the frame's own predicate, other frames) only add
protection and are left out.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mettapedia.Languages.Prolog.SWI.Handoff

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def before (g : Nat) : Option Nat → Bool
  | none => true
  | some e => decide (g < e)

/-- The frame of the goal. -/
inductive Fr (K : Type) where
  | none
  | live
  | holding (k : K)
  | gone
deriving DecidableEq

namespace Fr
def inUse {K : Type} : Fr K → Bool
  | live => true
  | holding _ => true
  | _ => false
end Fr

/-- Clause GC: started; one of marking/scanning done; both done. -/
inductive GA where
  | idle
  | started
  | half
  | full
deriving DecidableEq

/-! ## Part A: a handle of db_snapshot/1 -/

namespace A

structure St (K : Type) where
  G      : Nat
  born   : K → Nat
  erased : K → Option Nat
  freed  : K → Bool
  gs     : Nat
  isOpen : Bool
  fr     : Fr K
  /-- the stamp (flag, generation, lTop) is still in the owner's store buffer -/
  buf    : Bool
  gpc    : GA
  start  : Nat
  /-- this run found the snapshot open -/
  regS   : Bool
  /-- this run found the flagged frame -/
  regF   : Bool

structure Proto where
  /-- clause GC marks the open snapshots before it scans the frames -/
  snapFirst : Bool
  /-- closing orders the stamp before it (L_MISC) -/
  closeSync : Bool

def fixed : Proto := ⟨true, true⟩
def framesFirst : Proto := ⟨false, true⟩
def closeUnsynced : Proto := ⟨true, false⟩

variable {K : Type} [DecidableEq K]

def St.visAt (s : St K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

instance (s : St K) (k : K) (g : Nat) : Decidable (s.visAt k g) := by
  unfold St.visAt; infer_instance

def mark (s : St K) : St K := { s with regS := s.isOpen }
def scan (s : St K) : St K := { s with regF := s.fr.inUse && !s.buf }

inductive Step (P : Proto) : St K → St K → Prop where
  | bump (s : St K) : Step P s { s with G := s.G + 1 }
  | erase (s : St K) (k : K) (h : s.erased k = none) :
      Step P s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  /-- The call port of the goal stamps its frame (needs the handle open). -/
  | stamp (s : St K) (h : s.fr = .none) (ho : s.isOpen = true) :
      Step P s { s with fr := .live, buf := true }
  | drain (s : St K) : Step P s { s with buf := false }
  | select (s : St K) (k : K) (h : s.fr.inUse = true) (hk : s.visAt k s.gs) :
      Step P s { s with fr := .holding k }
  | close (s : St K) (h : s.isOpen = true) :
      Step P s { s with isOpen := false, buf := if P.closeSync then false else s.buf }
  | exit (s : St K) (h : s.fr.inUse = true) : Step P s { s with fr := .gone, buf := false }
  | gcStart (s : St K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .started, start := s.G, regS := false, regF := false }
  | gcFirst (s : St K) (h : s.gpc = .started) :
      Step P s { (if P.snapFirst then mark s else scan s) with gpc := .half }
  | gcSecond (s : St K) (h : s.gpc = .half) :
      Step P s { (if P.snapFirst then scan s else mark s) with gpc := .full }
  | reclaim (s : St K) (k : K) (e : Nat) (h : s.gpc = .full) (he : s.erased k = some e)
      (hlt : e < s.start) (hnot : ¬ ((s.regS || s.regF) = true ∧ s.visAt k s.gs)) :
      Step P s { s with freed := upd s.freed k true }
  | gcEnd (s : St K) (h : s.gpc = .full) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St K → St K → Prop where
  | refl (s : St K) : Reach P s s
  | tail {s t u : St K} : Reach P s t → Step P t u → Reach P s u

/-- The handle exists (open), its generation is not in the future, no frame yet. -/
def Init (s : St K) : Prop :=
  s.gs ≤ s.G ∧ s.isOpen = true ∧ s.fr = .none ∧ s.buf = false ∧ s.gpc = .idle ∧
  ∀ k, s.freed k = false

def Safe (s : St K) : Prop := ∀ k, s.fr = .holding k → s.freed k = false

/-- The owner may use clauses of the snapshot now or later. -/
def canUse (s : St K) : Prop := (s.fr = .none ∧ s.isOpen = true) ∨ s.fr.inUse = true

structure Inv (s : St K) : Prop where
  gs_le     : s.gs ≤ s.G
  hold      : ∀ k, s.fr = .holding k → s.visAt k s.gs
  closed_drained : s.isOpen = false → s.buf = false
  freed_unused : ∀ k, s.freed k = true → s.visAt k s.gs → ¬ canUse s
  run_mark  : (s.gpc = .half ∨ s.gpc = .full) → s.regS = false → s.isOpen = false
  run_scan  : s.gpc = .full → s.regS = false → s.regF = false → s.fr.inUse = false

theorem visAt_erase_gs {s : St K} {k0 : K} (hle : s.gs ≤ s.G) (hk0 : s.erased k0 = none)
    (k : K) :
    St.visAt { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } k s.gs ↔
      s.visAt k s.gs := by
  by_cases hk : k = k0
  · subst hk
    simp [St.visAt, upd, hk0, before]
    omega
  · simp [St.visAt, upd, hk]

theorem canUse_mono {s t : St K} (hfr : s.fr = .none ∨ s.fr = .gone → t.fr = s.fr)
    (ho : s.isOpen = false → t.isOpen = false) (h : ¬ canUse s) : ¬ canUse t := by
  intro ht
  apply h
  unfold canUse at h ht ⊢
  have hn : ¬ ((s.fr = .none ∧ s.isOpen = true) ∨ s.fr.inUse = true) := h
  rcases Classical.em (s.fr.inUse = true) with hu | hu
  · exact Or.inr hu
  · have hs : s.fr = .none ∨ s.fr = .gone := by
      cases hf : s.fr <;> simp [hf, Fr.inUse] at hu ⊢
    have hft := hfr hs
    rcases hs with hs | hs
    · have hopen : s.isOpen = true := by
        cases hso : s.isOpen
        · exfalso
          rcases ht with ⟨_, hto⟩ | htu
          · rw [ho hso] at hto; cases hto
          · rw [hft, hs] at htu; simp [Fr.inUse] at htu
        · rfl
      exact Or.inl ⟨hs, hopen⟩
    · exfalso
      rcases ht with ⟨htn, _⟩ | htu
      · rw [hft, hs] at htn; cases htn
      · rw [hft, hs] at htu; simp [Fr.inUse] at htu

theorem step_inv {s t : St K} (h : Inv s) (hst : Step fixed s t) : Inv t := by
  cases hst with
  | bump =>
    exact
      { gs_le := Nat.le_succ_of_le h.gs_le
        hold := h.hold
        closed_drained := h.closed_drained
        freed_unused := fun k hk hv => canUse_mono (s := s) (fun _ => rfl) id (h.freed_unused k hk hv)
        run_mark := h.run_mark
        run_scan := h.run_scan }
  | erase k0 hk0 =>
    have hv := visAt_erase_gs h.gs_le hk0
    exact
      { gs_le := Nat.le_succ_of_le h.gs_le
        hold := fun k hk => (hv k).2 (h.hold k hk)
        closed_drained := h.closed_drained
        freed_unused := by
          intro k hk hvk
          have hk' : s.freed k = true := by
            by_cases hkk : k = k0
            · subst hkk; exact hk
            · exact hk
          exact canUse_mono (s := s) (fun _ => rfl) id (h.freed_unused k hk' ((hv k).1 hvk))
        run_mark := h.run_mark
        run_scan := h.run_scan }
  | stamp hfr ho =>
    exact
      { gs_le := h.gs_le
        hold := by intro k hk; cases hk
        closed_drained := by intro hc; simp [ho] at hc
        freed_unused := by
          intro k hk hv _
          exact h.freed_unused k hk hv (Or.inl ⟨hfr, ho⟩)
        run_mark := by
          intro hg hr
          have := h.run_mark hg hr
          rw [ho] at this; cases this
        run_scan := by
          intro hg hr _
          have := h.run_mark (Or.inr hg) hr
          rw [ho] at this; cases this }
  | drain =>
    exact
      { gs_le := h.gs_le, hold := h.hold
        closed_drained := fun _ => rfl
        freed_unused := fun k hk hv => canUse_mono (s := s) (fun _ => rfl) id (h.freed_unused k hk hv)
        run_mark := h.run_mark, run_scan := h.run_scan }
  | select k hu hk =>
    exact
      { gs_le := h.gs_le
        hold := by intro k' hk'; simp at hk'; subst hk'; exact hk
        closed_drained := h.closed_drained
        freed_unused := by
          intro k' hk' hv' _
          exact h.freed_unused k' hk' hv' (Or.inr hu)
        run_mark := h.run_mark
        run_scan := by
          intro hg hr hf
          have := h.run_scan hg hr hf
          rw [hu] at this; cases this }
  | close ho =>
    exact
      { gs_le := h.gs_le
        hold := h.hold
        closed_drained := fun _ => by simp [fixed]
        freed_unused := by
          intro k hk hv
          exact canUse_mono (s := s) (fun _ => rfl) (fun _ => rfl) (h.freed_unused k hk hv)
        run_mark := fun _ _ => rfl
        run_scan := h.run_scan }
  | exit hu =>
    exact
      { gs_le := h.gs_le
        hold := by intro k hk; cases hk
        closed_drained := fun _ => rfl
        freed_unused := by
          intro k hk hv hc
          rcases hc with ⟨hn, _⟩ | hu'
          · cases hn
          · simp [Fr.inUse] at hu'
        run_mark := h.run_mark
        run_scan := by intro _ _ _; rfl }
  | gcStart hg =>
    exact
      { gs_le := h.gs_le, hold := h.hold, closed_drained := h.closed_drained
        freed_unused := fun k hk hv => canUse_mono (s := s) (fun _ => rfl) id (h.freed_unused k hk hv)
        run_mark := by intro hg'; rcases hg' with hg' | hg' <;> cases hg'
        run_scan := by intro hg'; cases hg' }
  | gcFirst hg =>
    exact
      { gs_le := h.gs_le, hold := h.hold, closed_drained := h.closed_drained
        freed_unused := fun k hk hv =>
          canUse_mono (s := s) (fun _ => by simp [fixed, mark]) (fun hc => by simp [fixed, mark, hc])
            (h.freed_unused k hk hv)
        run_mark := by
          intro _ hr
          simp [fixed, mark] at hr ⊢
          exact hr
        run_scan := by intro hg'; simp at hg' }
  | gcSecond hg =>
    exact
      { gs_le := h.gs_le, hold := h.hold, closed_drained := h.closed_drained
        freed_unused := fun k hk hv =>
          canUse_mono (s := s) (fun _ => by simp [fixed, scan]) (fun hc => by simp [fixed, scan, hc])
            (h.freed_unused k hk hv)
        run_mark := by
          intro _ hr
          simp [fixed, scan] at hr
          exact h.run_mark (Or.inl hg) hr
        run_scan := by
          intro _ hr hf
          simp [fixed, scan] at hr hf
          have hclosed := h.run_mark (Or.inl hg) hr
          have hb := h.closed_drained hclosed
          rw [hb] at hf
          simpa [fixed, scan] using hf }
  | reclaim k0 e hg he hlt hnot =>
    exact
      { gs_le := h.gs_le, hold := h.hold, closed_drained := h.closed_drained
        freed_unused := by
          intro k hk hv
          by_cases hkk : k = k0
          · subst hkk
            have hreg : ¬ ((s.regS || s.regF) = true) := fun hr => hnot ⟨hr, hv⟩
            have hS : s.regS = false := by
              cases hs : s.regS <;> simp [hs] at hreg ⊢
            have hF : s.regF = false := by
              cases hf : s.regF <;> simp [hf, hS] at hreg ⊢
            have hclosed := h.run_mark (Or.inr hg) hS
            have hunused := h.run_scan hg hS hF
            intro hc
            rcases hc with ⟨_, ho⟩ | hu
            · simp only at ho; rw [hclosed] at ho; cases ho
            · simp only at hu; rw [hunused] at hu; cases hu
          · have hk' : s.freed k = true := by simpa [upd, hkk] using hk
            exact h.freed_unused k hk' hv
        run_mark := h.run_mark, run_scan := h.run_scan }
  | gcEnd hg =>
    exact
      { gs_le := h.gs_le, hold := h.hold, closed_drained := h.closed_drained
        freed_unused := fun k hk hv => canUse_mono (s := s) (fun _ => rfl) id (h.freed_unused k hk hv)
        run_mark := by intro hg'; rcases hg' with hg' | hg' <;> cases hg'
        run_scan := by intro hg'; cases hg' }

theorem init_inv {s : St K} (h : Init s) : Inv s where
  gs_le := h.1
  hold := by intro k hk; rw [h.2.2.1] at hk; cases hk
  closed_drained := by intro hc; rw [h.2.1] at hc; cases hc
  freed_unused := by intro k hk; rw [h.2.2.2.2.2 k] at hk; cases hk
  run_mark := by intro hg; rw [h.2.2.2.2.1] at hg; rcases hg with hg | hg <;> cases hg
  run_scan := by intro hg; rw [h.2.2.2.2.1] at hg; cases hg

theorem Inv.safe {s : St K} (h : Inv s) : Safe s := by
  intro k hk
  cases hf : s.freed k with
  | false => rfl
  | true =>
    exact absurd (Or.inr (by simp [hk, Fr.inUse])) (h.freed_unused k hf (h.hold k hk))

theorem reach_inv {s t : St K} (h : Inv s) (hr : Reach fixed s t) : Inv t := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact step_inv ih hst

theorem handle_safe {s0 s : St K} (h0 : Init s0) (hr : Reach fixed s0 s) : Safe s :=
  (reach_inv (init_inv h0) hr).safe

/-! Counterexamples: one clause, born and snapshotted at generation 0. -/

def a0 : St Unit := ⟨0, fun _ => 0, fun _ => none, fun _ => false, 0, true, .none, false,
  .idle, 0, false, false⟩

theorem a0_init : Init a0 := ⟨Nat.le_refl _, rfl, rfl, rfl, rfl, fun _ => rfl⟩

/-- Clause GC scans the frames first (the goal has no frame yet), the owner
stamps, selects the clause and closes the handle, then clause GC marks the
open snapshots: none. -/
theorem handle_frames_first_unsafe : ∃ s, Reach framesFirst a0 s ∧ ¬ Safe s := by
  let s1 : St Unit := { a0 with G := a0.G + 1, erased := upd a0.erased () (some (a0.G + 1)) }
  let s2 : St Unit := { s1 with G := s1.G + 1 }
  let s3 : St Unit := { s2 with gpc := .started, start := s2.G, regS := false, regF := false }
  let s4 : St Unit := { (if framesFirst.snapFirst then mark s3 else scan s3) with gpc := .half }
  let s5 : St Unit := { s4 with fr := .live, buf := true }
  let s6 : St Unit := { s5 with fr := .holding () }
  let s7 : St Unit := { s6 with isOpen := false,
                                buf := if framesFirst.closeSync then false else s6.buf }
  let s8 : St Unit := { (if framesFirst.snapFirst then scan s7 else mark s7) with gpc := .full }
  let s9 : St Unit := { s8 with freed := upd s8.freed () true }
  refine ⟨s9, ?_, ?_⟩
  · exact Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.refl a0)
      (Step.erase a0 () (by decide)))
      (Step.bump s1))
      (Step.gcStart s2 (by decide)))
      (Step.gcFirst s3 (by decide)))
      (Step.stamp s4 (by decide) (by decide)))
      (Step.select s5 () (by decide) (by decide)))
      (Step.close s6 (by decide)))
      (Step.gcSecond s7 (by decide)))
      (Step.reclaim s8 () 1 (by decide) (by decide) (by decide) (by decide))
  · intro hs; have := hs () (by decide); simp [s9, upd] at this

/-- The owner stamps (stores still buffered), selects the clause and closes
the handle without ordering the stamp before the close; clause GC finds the
handle closed and the frame not yet visible. -/
theorem handle_close_unsynced_unsafe : ∃ s, Reach closeUnsynced a0 s ∧ ¬ Safe s := by
  let s1 : St Unit := { a0 with G := a0.G + 1, erased := upd a0.erased () (some (a0.G + 1)) }
  let s2 : St Unit := { s1 with G := s1.G + 1 }
  let s3 : St Unit := { s2 with fr := .live, buf := true }
  let s4 : St Unit := { s3 with fr := .holding () }
  let s5 : St Unit := { s4 with isOpen := false,
                                buf := if closeUnsynced.closeSync then false else s4.buf }
  let s6 : St Unit := { s5 with gpc := .started, start := s5.G, regS := false, regF := false }
  let s7 : St Unit := { (if closeUnsynced.snapFirst then mark s6 else scan s6) with gpc := .half }
  let s8 : St Unit := { (if closeUnsynced.snapFirst then scan s7 else mark s7) with gpc := .full }
  let s9 : St Unit := { s8 with freed := upd s8.freed () true }
  refine ⟨s9, ?_, ?_⟩
  · exact Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.refl a0)
      (Step.erase a0 () (by decide)))
      (Step.bump s1))
      (Step.stamp s2 (by decide) (by decide)))
      (Step.select s3 () (by decide) (by decide)))
      (Step.close s4 (by decide)))
      (Step.gcStart s5 (by decide)))
      (Step.gcFirst s6 (by decide)))
      (Step.gcSecond s7 (by decide)))
      (Step.reclaim s8 () 1 (by decide) (by decide) (by decide) (by decide))
  · intro hs; have := hs () (by decide); simp [s9, upd] at this

end A

/-! ## Part B: the frame of db_snapshot_scope/2 -/

namespace B

/-- The scope frame: called (unflagged), halfway through an unlocked stamp
(generation read, flag not yet stored), stamped (flagged, generation `gsc`). -/
inductive Sc where
  | none
  | half
  | stamped
  | gone
deriving DecidableEq

structure St (K : Type) where
  G      : Nat
  born   : K → Nat
  erased : K → Option Nat
  freed  : K → Bool
  sc     : Sc
  gsc    : Nat
  /-- a goal frame inside the scope that holds a clause -/
  hold   : Option K
  gpc    : GA
  start  : Nat
  regF   : Bool

structure Proto where
  /-- the stamp reads the generation and flags the frame under the scan lock -/
  locked : Bool

def fixed : Proto := ⟨true⟩
def split : Proto := ⟨false⟩

variable {K : Type} [DecidableEq K]

def St.visAt (s : St K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

instance (s : St K) (k : K) (g : Nat) : Decidable (s.visAt k g) := by
  unfold St.visAt; infer_instance

inductive Step (P : Proto) : St K → St K → Prop where
  | bump (s : St K) : Step P s { s with G := s.G + 1 }
  | erase (s : St K) (k : K) (h : s.erased k = none) :
      Step P s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  /-- '$db_snapshot_scope'/1 under the scan lock: read the generation, flag. -/
  | stampLocked (s : St K) (hp : P.locked = true) (h : s.sc = .none) :
      Step P s { s with sc := .stamped, gsc := s.G }
  /-- Without the lock: read the generation ... -/
  | readGen (s : St K) (hp : P.locked = false) (h : s.sc = .none) :
      Step P s { s with sc := .half, gsc := s.G }
  /-- ... and flag the frame later. -/
  | flag (s : St K) (h : s.sc = .half) : Step P s { s with sc := .stamped }
  /-- A goal of db_snapshot_call/2 in the scope selects a clause in `gsc`. -/
  | select (s : St K) (k : K) (h : s.sc = .stamped) (hk : s.visAt k s.gsc) :
      Step P s { s with hold := some k }
  /-- The goals and then the scope frame exit. -/
  | exit (s : St K) (h : s.sc = .stamped) : Step P s { s with sc := .gone, hold := none }
  | gcStart (s : St K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .started, start := s.G, regF := false }
  /-- The scan of the owner's frames, under its scan lock. -/
  | gcScan (s : St K) (h : s.gpc = .started) :
      Step P s { s with gpc := .full, regF := decide (s.sc = .stamped) }
  | reclaim (s : St K) (k : K) (e : Nat) (h : s.gpc = .full) (he : s.erased k = some e)
      (hlt : e < s.start) (hnot : ¬ (s.regF = true ∧ s.visAt k s.gsc)) :
      Step P s { s with freed := upd s.freed k true }
  | gcEnd (s : St K) (h : s.gpc = .full) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St K → St K → Prop where
  | refl (s : St K) : Reach P s s
  | tail {s t u : St K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St K) : Prop :=
  s.sc = .none ∧ s.hold = none ∧ s.gpc = .idle ∧ ∀ k, s.freed k = false

def Safe (s : St K) : Prop := ∀ k, s.hold = some k → s.freed k = false

/-- The scope may still select clauses in `gsc`. -/
def canUse (s : St K) : Prop := s.sc = .none ∨ s.sc = .stamped

structure Inv (s : St K) : Prop where
  gsc_le    : s.sc = .stamped → s.gsc ≤ s.G
  hold_sc   : ∀ k, s.hold = some k → s.sc = .stamped ∧ s.visAt k s.gsc
  start_le  : (s.gpc = .started ∨ s.gpc = .full) → s.start ≤ s.G
  freed_old : ∀ k, s.freed k = true → ∃ e, s.erased k = some e ∧ e < s.G
  /-- a clause reclaimed while the scope may still use it is invisible in
      every generation the scope can get from now on -/
  freed_unused : ∀ k, s.freed k = true → s.sc = .stamped → ¬ s.visAt k s.gsc
  /-- the scan missed the stamp: the stamp comes later, reading a newer
      generation; or it saw it -/
  run_scan  : s.gpc = .full → s.regF = false → s.sc = .stamped → s.start ≤ s.gsc
  half_no   : s.sc ≠ .half

theorem step_inv {s t : St K} (h : Inv s) (hst : Step fixed s t) : Inv t := by
  cases hst with
  | bump =>
    exact
      { gsc_le := fun hs => Nat.le_succ_of_le (h.gsc_le hs)
        hold_sc := h.hold_sc
        start_le := fun hg => Nat.le_succ_of_le (h.start_le hg)
        freed_old := fun k hk => by
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          exact ⟨e, he, by show e < s.G + 1; omega⟩
        freed_unused := h.freed_unused
        run_scan := h.run_scan
        half_no := h.half_no }
  | erase k0 hk0 =>
    have fne : ∀ k, s.freed k = true → k ≠ k0 := by
      intro k hk heq
      obtain ⟨e, he, _⟩ := h.freed_old k hk
      rw [heq, hk0] at he; cases he
    have vis_ne : ∀ k g, k ≠ k0 →
        (St.visAt { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } k g ↔
          s.visAt k g) := by
      intro k g hne; simp [St.visAt, upd, hne]
    exact
      { gsc_le := fun hs => Nat.le_succ_of_le (h.gsc_le hs)
        hold_sc := by
          intro k hk
          obtain ⟨hst, hv⟩ := h.hold_sc k hk
          refine ⟨hst, ?_⟩
          by_cases hkk : k = k0
          · subst hkk
            have := h.gsc_le hst
            simp only [St.visAt, upd] at hv ⊢
            exact ⟨hv.1, by simp [before]; omega⟩
          · exact (vis_ne k _ hkk).2 hv
        start_le := fun hg => Nat.le_succ_of_le (h.start_le hg)
        freed_old := by
          intro k hk
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          exact ⟨e, by simp [upd, fne k hk, he], by show e < s.G + 1; omega⟩
        freed_unused := by
          intro k hk hst hv
          exact h.freed_unused k hk hst ((vis_ne k _ (fne k hk)).1 hv)
        run_scan := h.run_scan
        half_no := h.half_no }
  | stampLocked _ hsc =>
    exact
      { gsc_le := fun _ => Nat.le_refl _
        hold_sc := by
          intro k hk
          obtain ⟨hst, _⟩ := h.hold_sc k hk
          rw [hsc] at hst; cases hst
        start_le := h.start_le
        freed_old := h.freed_old
        freed_unused := by
          intro k hk _ hv
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          have hb := hv.2
          simp only at hb
          rw [he] at hb; simp [before] at hb; omega
        run_scan := fun hg _ _ => h.start_le (Or.inr hg)
        half_no := by simp }
  | readGen hp => simp [fixed] at hp
  | flag hsc => exact absurd hsc h.half_no
  | select k hsc hk =>
    exact
      { gsc_le := h.gsc_le
        hold_sc := by intro k' hk'; simp at hk'; subst hk'; exact ⟨hsc, hk⟩
        start_le := h.start_le
        freed_old := h.freed_old
        freed_unused := h.freed_unused
        run_scan := h.run_scan
        half_no := h.half_no }
  | exit hsc =>
    exact
      { gsc_le := by intro hs; cases hs
        hold_sc := by intro k hk; cases hk
        start_le := h.start_le
        freed_old := h.freed_old
        freed_unused := by intro k _ hs; cases hs
        run_scan := by intro _ _ hs; cases hs
        half_no := by simp }
  | gcStart hg =>
    exact
      { gsc_le := h.gsc_le, hold_sc := h.hold_sc
        start_le := fun _ => Nat.le_refl _
        freed_old := h.freed_old, freed_unused := h.freed_unused
        run_scan := by intro hg'; cases hg'
        half_no := h.half_no }
  | gcScan hg =>
    exact
      { gsc_le := h.gsc_le, hold_sc := h.hold_sc
        start_le := fun _ => h.start_le (Or.inl hg)
        freed_old := h.freed_old, freed_unused := h.freed_unused
        run_scan := by
          intro _ hr hs
          simp only at hr hs
          simp [hs] at hr
        half_no := h.half_no }
  | reclaim k0 e hg he hlt hnot =>
    exact
      { gsc_le := h.gsc_le, hold_sc := h.hold_sc, start_le := h.start_le
        freed_old := by
          intro k hk
          by_cases hkk : k = k0
          · subst hkk; exact ⟨e, he, by show e < s.G; have := h.start_le (Or.inr hg); omega⟩
          · exact h.freed_old k (by simpa [upd, hkk] using hk)
        freed_unused := by
          intro k hk hst hv
          by_cases hkk : k = k0
          · subst hkk
            by_cases hr : s.regF = true
            · exact hnot ⟨hr, hv⟩
            · have hr' : s.regF = false := by simpa using hr
              have hle := h.run_scan hg hr' hst
              have hb := hv.2
              simp only at hb
              rw [he] at hb; simp [before] at hb; omega
          · exact h.freed_unused k (by simpa [upd, hkk] using hk) hst hv
        run_scan := h.run_scan
        half_no := h.half_no }
  | gcEnd hg =>
    exact
      { gsc_le := h.gsc_le, hold_sc := h.hold_sc
        start_le := by intro hg'; rcases hg' with hg' | hg' <;> cases hg'
        freed_old := h.freed_old, freed_unused := h.freed_unused
        run_scan := by intro hg'; cases hg'
        half_no := h.half_no }

theorem init_inv {s : St K} (h : Init s) : Inv s where
  gsc_le := by intro hs; rw [h.1] at hs; cases hs
  hold_sc := by intro k hk; rw [h.2.1] at hk; cases hk
  start_le := by intro hg; rw [h.2.2.1] at hg; rcases hg with hg | hg <;> cases hg
  freed_old := by intro k hk; rw [h.2.2.2 k] at hk; cases hk
  freed_unused := by intro k hk; rw [h.2.2.2 k] at hk; cases hk
  run_scan := by intro hg; rw [h.2.2.1] at hg; cases hg
  half_no := by rw [h.1]; simp

theorem Inv.safe {s : St K} (h : Inv s) : Safe s := by
  intro k hk
  obtain ⟨hst, hv⟩ := h.hold_sc k hk
  cases hf : s.freed k with
  | false => rfl
  | true => exact absurd hv (h.freed_unused k hf hst)

theorem reach_inv {s t : St K} (h : Inv s) (hr : Reach fixed s t) : Inv t := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact step_inv ih hst

theorem scope_safe {s0 s : St K} (h0 : Init s0) (hr : Reach fixed s0 s) : Safe s :=
  (reach_inv (init_inv h0) hr).safe

def b0 : St Unit := ⟨0, fun _ => 0, fun _ => none, fun _ => false, .none, 0, none, .idle, 0, false⟩

theorem b0_init : Init b0 := ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- The scope reads generation 0, the clause is erased, clause GC starts and
scans before the frame is flagged, then the goal selects the clause. -/
theorem scope_split_unsafe : ∃ s, Reach split b0 s ∧ ¬ Safe s := by
  let s1 : St Unit := { b0 with sc := .half, gsc := b0.G }
  let s2 : St Unit := { s1 with G := s1.G + 1, erased := upd s1.erased () (some (s1.G + 1)) }
  let s3 : St Unit := { s2 with G := s2.G + 1 }
  let s4 : St Unit := { s3 with gpc := .started, start := s3.G, regF := false }
  let s5 : St Unit := { s4 with gpc := .full, regF := decide (s4.sc = .stamped) }
  let s6 : St Unit := { s5 with sc := .stamped }
  let s7 : St Unit := { s6 with hold := some () }
  let s8 : St Unit := { s7 with freed := upd s7.freed () true }
  refine ⟨s8, ?_, ?_⟩
  · exact Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.refl b0)
      (Step.readGen b0 (by decide) (by decide)))
      (Step.erase s1 () (by decide)))
      (Step.bump s2))
      (Step.gcStart s3 (by decide)))
      (Step.gcScan s4 (by decide)))
      (Step.flag s5 (by decide)))
      (Step.select s6 () (by decide) (by decide)))
      (Step.reclaim s7 () 1 (by decide) (by decide) (by decide) (by decide))
  · intro hs; have := hs () (by decide); simp [s8, upd] at this

end B

end Mettapedia.Languages.Prolog.SWI.Handoff
