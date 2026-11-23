/-
The publication protocol with an asymmetric barrier.

The reader moves lTop above its frame and re-reads the generation with no
hardware barrier (a compiler barrier keeps the two in program order).
Clause GC, after reading its start generation, issues one process-wide
barrier (membarrier(MEMBARRIER_CMD_PRIVATE_EXPEDITED) on Linux,
FlushProcessWriteBuffers() on Windows): every store buffer drains before it
scans.  A reader that published before the barrier is visible to the scan;
one that publishes after it re-reads a generation that is not older than
the start.

`asym_safe`: no frame ever holds a clause that clause GC reclaimed.  This
would let S_STATIC take the same protocol at the cost of a load and a
compare, and S_DYNAMIC drop its full barrier.  Without the process-wide
barrier this is `Publish.noReaderFence`, which is unsafe
(`Publish.no_reader_fence_unsafe`).
-/

import Mettapedia.Languages.Prolog.SWI.Publish

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mettapedia.Languages.Prolog.SWI.PublishAsym

open Mettapedia.Languages.Prolog.SWI.Publish

/-- Clause GC: begun, start generation read, process-wide barrier issued. -/
inductive GQ where
  | idle
  | begun
  | started
  | flushed
deriving DecidableEq

structure St (R K : Type) where
  G      : Nat
  born   : K → Nat
  erased : K → Option Nat
  freed  : K → Bool
  rd     : R → RS K
  gpc    : GQ
  start  : Nat

variable {R K : Type} [DecidableEq R] [DecidableEq K]

def St.visAt (s : St R K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

instance (s : St R K) (k : K) (g : Nat) : Decidable (s.visAt k g) := by
  unfold St.visAt; infer_instance

def St.setR (s : St R K) (r : R) (x : RS K) : St R K := { s with rd := upd s.rd r x }

/-- The process-wide barrier drains every store buffer. -/
def flushRS (x : RS K) : RS K := { x with vis := x.vis || x.buf, buf := false }

inductive Step : St R K → St R K → Prop where
  | bump (s : St R K) : Step s { s with G := s.G + 1 }
  | erase (s : St R K) (k : K) (h : s.erased k = none) :
      Step s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  | drain (s : St R K) (r : R) (h : (s.rd r).buf = true) :
      Step s (s.setR r { s.rd r with vis := true, buf := false })
  | call (s : St R K) (r : R) (h : (s.rd r).pc = .idle) :
      Step s (s.setR r { s.rd r with pc := .called, gen := s.G })
  | publish (s : St R K) (r : R) (h : (s.rd r).pc = .called) :
      Step s (s.setR r { s.rd r with pc := .published, buf := true })
  /-- Re-read without a barrier: the store may still be buffered. -/
  | retake (s : St R K) (r : R) (h : (s.rd r).pc = .published)
      (hne : (s.rd r).gen ≠ s.G) :
      Step s (s.setR r { s.rd r with gen := s.G })
  | confirm (s : St R K) (r : R) (h : (s.rd r).pc = .published)
      (heq : (s.rd r).gen = s.G) :
      Step s (s.setR r { s.rd r with pc := .ready })
  | select (s : St R K) (r : R) (k : K) (h : (s.rd r).pc.active = true)
      (hk : s.visAt k (s.rd r).gen) :
      Step s (s.setR r { s.rd r with pc := .holding k })
  | exit (s : St R K) (r : R) (h : (s.rd r).pc.active = true)
      (hb : (s.rd r).buf = false) :
      Step s (s.setR r { s.rd r with pc := .idle, vis := false })
  | gcBegin (s : St R K) (h : s.gpc = .idle) :
      Step s { s with gpc := .begun, rd := fun r => { s.rd r with seen := none } }
  | gcStart (s : St R K) (h : s.gpc = .begun) :
      Step s { s with gpc := .started, start := s.G }
  /-- membarrier(): all store buffers drain. -/
  | gcFlush (s : St R K) (h : s.gpc = .started) :
      Step s { s with gpc := .flushed, rd := fun r => flushRS (s.rd r) }
  | scan (s : St R K) (r : R) (h : s.gpc = .flushed) (hn : (s.rd r).seen = none) :
      Step s (s.setR r { s.rd r with
        seen := some (if (s.rd r).vis then some (s.rd r).gen else none) })
  | reclaim (s : St R K) (k : K) (e : Nat) (h : s.gpc = .flushed)
      (hall : ∀ r, (s.rd r).seen ≠ none) (he : s.erased k = some e)
      (hlt : e < s.start)
      (hinv : ∀ r g, (s.rd r).seen = some (some g) → ¬ s.visAt k g) :
      Step s { s with freed := upd s.freed k true }
  | gcEnd (s : St R K) (h : s.gpc = .flushed) : Step s { s with gpc := .idle }

inductive Reach : St R K → St R K → Prop where
  | refl (s : St R K) : Reach s s
  | tail {s t u : St R K} : Reach s t → Step t u → Reach s u

def Init (s : St R K) : Prop :=
  (∀ r, (s.rd r).pc = .idle ∧ (s.rd r).vis = false ∧ (s.rd r).buf = false ∧
        (s.rd r).seen = none ∧ (s.rd r).gen ≤ s.G) ∧
  s.gpc = .idle ∧ (∀ k, s.freed k = false)

def Safe (s : St R K) : Prop := ∀ r k, (s.rd r).pc = .holding k → s.freed k = false

structure RInv (s : St R K) (x : RS K) : Prop where
  gen_le    : x.gen ≤ s.G
  lo        : x.pc = .idle ∨ x.pc = .called → x.vis = false ∧ x.buf = false
  pub       : x.pc ≠ .idle → x.pc ≠ .called →
                (x.buf = true ∧ x.vis = false) ∨ (x.buf = false ∧ x.vis = true)
  hold      : ∀ k, x.pc = .holding k → s.visAt k x.gen
  act_free  : x.pc.active = true → ∀ k, s.freed k = true → ¬ s.visAt k x.gen
  /-- a store still buffered after the barrier was made after it, and so
      was every later re-read -/
  late_buf  : s.gpc = .flushed → x.buf = true → x.pc.active = true → s.start ≤ x.gen
  scan_none : s.gpc = .flushed → x.seen = some none → x.pc.active = true →
                s.start ≤ x.gen
  scan_some : s.gpc = .flushed → ∀ g, x.seen = some (some g) → x.pc ≠ .idle →
                x.gen = g ∨ s.start ≤ x.gen
  unscanned : s.gpc = .begun ∨ s.gpc = .started → x.seen = none

structure Inv (s : St R K) : Prop where
  start_le  : s.gpc = .started ∨ s.gpc = .flushed → s.start ≤ s.G
  freed_old : ∀ k, s.freed k = true → ∃ e, s.erased k = some e ∧ e < s.G
  rd        : ∀ r, RInv s (s.rd r)

section lemmas

@[simp] theorem setR_same (s : St R K) (r : R) (x : RS K) : (s.setR r x).rd r = x := by
  simp [St.setR, upd]

theorem setR_ne (s : St R K) {r r' : R} (x : RS K) (h : r' ≠ r) :
    (s.setR r x).rd r' = s.rd r' := by
  simp [St.setR, upd, h]

theorem visAt_congr {s t : St R K} (hb : s.born = t.born) (he : s.erased = t.erased)
    (k : K) (g : Nat) : s.visAt k g ↔ t.visAt k g := by
  simp [St.visAt, hb, he]

theorem RInv.congr {s t : St R K} {x : RS K} (hG : s.G = t.G) (hb : s.born = t.born)
    (he : s.erased = t.erased) (hf : s.freed = t.freed) (hg : s.gpc = t.gpc)
    (hs : s.start = t.start) (h : RInv s x) : RInv t x where
  gen_le := hG ▸ h.gen_le
  lo := h.lo
  pub := h.pub
  hold := fun k hk => (visAt_congr hb he k x.gen).1 (h.hold k hk)
  act_free := fun ha k hk hv =>
    h.act_free ha k (hf ▸ hk) ((visAt_congr hb he k x.gen).2 hv)
  late_buf := fun hgf hb' ha => hs ▸ h.late_buf (hg ▸ hgf) hb' ha
  scan_none := fun hgs hseen ha => hs ▸ h.scan_none (hg ▸ hgs) hseen ha
  scan_some := fun hgs g hseen hne => hs ▸ h.scan_some (hg ▸ hgs) g hseen hne
  unscanned := fun hgb => h.unscanned (hg ▸ hgb)

theorem active_ne_idle {x : RS K} (h : x.pc.active = true) : x.pc ≠ .idle := by
  intro h'; rw [h'] at h; simp [Pc.active] at h

theorem active_ne_called {x : RS K} (h : x.pc.active = true) : x.pc ≠ .called := by
  intro h'; rw [h'] at h; simp [Pc.active] at h

theorem inv_setR {s : St R K} {r : R} {x : RS K} (h : Inv s) (hx : RInv s x) :
    Inv (s.setR r x) where
  start_le := h.start_le
  freed_old := h.freed_old
  rd := by
    intro r'
    by_cases hr : r' = r
    · subst hr; simp only [setR_same]
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl hx
    · rw [setR_ne s x hr]
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl (h.rd r')

end lemmas

section preservation

theorem step_inv {s t : St R K} (h : Inv s) (hst : Step s t) : Inv t := by
  cases hst with
  | bump =>
    exact
      { start_le := fun hg => Nat.le_succ_of_le (h.start_le hg)
        freed_old := fun k hk => by
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          exact ⟨e, he, by show e < s.G + 1; omega⟩
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := by show (s.rd r).gen ≤ s.G + 1; have := hx.gen_le; omega
              lo := hx.lo, pub := hx.pub, hold := hx.hold, act_free := hx.act_free
              late_buf := hx.late_buf, scan_none := hx.scan_none
              scan_some := hx.scan_some, unscanned := hx.unscanned } }
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
      { start_le := fun hg => Nat.le_succ_of_le (h.start_le hg)
        freed_old := by
          intro k hk
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          exact ⟨e, by simp [upd, fne k hk, he], by show e < s.G + 1; omega⟩
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := by show (s.rd r).gen ≤ s.G + 1; have := hx.gen_le; omega
              lo := hx.lo, pub := hx.pub
              hold := by
                intro k hk
                by_cases hkk : k = k0
                · subst hkk
                  have hv := hx.hold k hk
                  have := hx.gen_le
                  simp only [St.visAt, upd] at hv ⊢
                  exact ⟨hv.1, by simp [before]; omega⟩
                · exact (vis_ne k _ hkk).2 (hx.hold k hk)
              act_free := by
                intro ha k hk hv
                exact hx.act_free ha k hk ((vis_ne k _ (fne k hk)).1 hv)
              late_buf := hx.late_buf, scan_none := hx.scan_none
              scan_some := hx.scan_some, unscanned := hx.unscanned } }
  | drain r hb =>
    have hx := h.rd r
    apply inv_setR h
    have hnl : (s.rd r).pc ≠ .idle ∧ (s.rd r).pc ≠ .called := by
      constructor <;> intro hp
      · have := (hx.lo (Or.inl hp)).2; rw [hb] at this; cases this
      · have := (hx.lo (Or.inr hp)).2; rw [hb] at this; cases this
    exact
      { gen_le := hx.gen_le
        lo := by
          intro hl; rcases hl with hl | hl
          · exact absurd hl hnl.1
          · exact absurd hl hnl.2
        pub := fun _ _ => Or.inr ⟨rfl, rfl⟩
        hold := hx.hold, act_free := hx.act_free
        late_buf := by intro _ hb'; cases hb'
        scan_none := hx.scan_none, scan_some := hx.scan_some, unscanned := hx.unscanned }
  | call r hpc =>
    have hx := h.rd r
    have hlo := hx.lo (Or.inl hpc)
    apply inv_setR h
    exact
      { gen_le := Nat.le_refl _
        lo := fun _ => hlo
        pub := by intro _ hc; exact absurd rfl hc
        hold := by intro k hk; simp at hk
        act_free := by intro ha; simp [Pc.active] at ha
        late_buf := by intro _ _ ha; simp [Pc.active] at ha
        scan_none := by intro _ _ ha; simp [Pc.active] at ha
        scan_some := fun hg _ _ _ => Or.inr (h.start_le (Or.inr hg))
        unscanned := hx.unscanned }
  | publish r hpc =>
    have hx := h.rd r
    have hlo := hx.lo (Or.inr hpc)
    apply inv_setR h
    exact
      { gen_le := hx.gen_le
        lo := by intro hl; simp at hl
        pub := fun _ _ => Or.inl ⟨rfl, hlo.1⟩
        hold := by intro k hk; simp at hk
        act_free := by intro ha; simp [Pc.active] at ha
        late_buf := by intro _ _ ha; simp [Pc.active] at ha
        scan_none := by intro _ _ ha; simp [Pc.active] at ha
        scan_some := fun hg g hs _ => hx.scan_some hg g hs (by rw [hpc]; simp)
        unscanned := hx.unscanned }
  | retake r hpc _ =>
    have hx := h.rd r
    apply inv_setR h
    exact
      { gen_le := Nat.le_refl _
        lo := by intro hl; rw [hpc] at hl; simp at hl
        pub := fun h1 h2 => hx.pub h1 h2
        hold := by intro k hk; simp [hpc] at hk
        act_free := by intro ha; simp [hpc, Pc.active] at ha
        late_buf := by intro _ _ ha; simp [hpc, Pc.active] at ha
        scan_none := by intro _ _ ha; simp [hpc, Pc.active] at ha
        scan_some := fun hg _ _ _ => Or.inr (h.start_le (Or.inr hg))
        unscanned := hx.unscanned }
  | confirm r hpc heq =>
    have hx := h.rd r
    apply inv_setR h
    exact
      { gen_le := hx.gen_le
        lo := by intro hl; simp at hl
        pub := fun _ _ => hx.pub (by rw [hpc]; simp) (by rw [hpc]; simp)
        hold := by intro k hk; simp at hk
        act_free := by
          intro _ k hk hv
          obtain ⟨e, he, hlt⟩ := h.freed_old k hk
          have hb2 := hv.2
          simp only at hb2
          rw [he, heq] at hb2
          simp [before] at hb2
          omega
        late_buf := fun hg _ _ => by simp only; rw [heq]; exact h.start_le (Or.inr hg)
        scan_none := fun hg _ _ => by simp only; rw [heq]; exact h.start_le (Or.inr hg)
        scan_some := fun hg g hs _ => hx.scan_some hg g hs (by rw [hpc]; simp)
        unscanned := hx.unscanned }
  | select r k hpc hk =>
    have hx := h.rd r
    apply inv_setR h
    exact
      { gen_le := hx.gen_le
        lo := by intro hl; simp at hl
        pub := fun _ _ => hx.pub (active_ne_idle hpc) (active_ne_called hpc)
        hold := by intro k' hk'; simp at hk'; subst hk'; exact hk
        act_free := fun _ => hx.act_free hpc
        late_buf := fun hg hb _ => hx.late_buf hg hb hpc
        scan_none := fun hg hs _ => hx.scan_none hg hs hpc
        scan_some := fun hg g hs _ => hx.scan_some hg g hs (active_ne_idle hpc)
        unscanned := hx.unscanned }
  | exit r _ hb =>
    have hx := h.rd r
    apply inv_setR h
    exact
      { gen_le := hx.gen_le
        lo := fun _ => ⟨rfl, hb⟩
        pub := by intro hi; exact absurd rfl hi
        hold := by intro k hk; simp at hk
        act_free := by intro ha; simp [Pc.active] at ha
        late_buf := by intro _ _ ha; simp [Pc.active] at ha
        scan_none := by intro _ _ ha; simp [Pc.active] at ha
        scan_some := by intro _ _ _ hne; simp at hne
        unscanned := hx.unscanned }
  | gcBegin hg =>
    exact
      { start_le := by intro hg'; rcases hg' with hg' | hg' <;> cases hg'
        freed_old := h.freed_old
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, hold := hx.hold
              act_free := hx.act_free
              late_buf := by intro hg'; cases hg'
              scan_none := by intro hg'; cases hg'
              scan_some := by intro hg'; cases hg'
              unscanned := fun _ => rfl } }
  | gcStart hg =>
    exact
      { start_le := fun _ => Nat.le_refl _
        freed_old := h.freed_old
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, hold := hx.hold
              act_free := hx.act_free
              late_buf := by intro hg'; cases hg'
              scan_none := by intro hg'; cases hg'
              scan_some := by intro hg'; cases hg'
              unscanned := fun _ => hx.unscanned (Or.inl hg) } }
  | gcFlush hg =>
    exact
      { start_le := fun _ => h.start_le (Or.inl hg)
        freed_old := h.freed_old
        rd := fun r => by
          have hx := h.rd r
          have hn := hx.unscanned (Or.inr hg)
          exact
            { gen_le := hx.gen_le
              lo := by
                intro hl
                have := hx.lo hl
                simp [flushRS, this.1, this.2]
              pub := by
                intro h1 h2
                right
                rcases hx.pub h1 h2 with ⟨hb, _⟩ | ⟨hb, hv⟩
                · simp [flushRS, hb]
                · simp [flushRS, hb, hv]
              hold := hx.hold
              act_free := hx.act_free
              late_buf := by intro _ hb; simp [flushRS] at hb
              scan_none := by intro _ hs; simp [flushRS, hn] at hs
              scan_some := by intro _ g hs; simp [flushRS, hn] at hs
              unscanned := by intro hg'; rcases hg' with hg' | hg' <;> cases hg' } }
  | scan r hg _ =>
    have hx := h.rd r
    apply inv_setR h
    exact
      { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, hold := hx.hold
        act_free := hx.act_free, late_buf := hx.late_buf
        scan_none := by
          intro hgf hs ha
          by_cases hv : (s.rd r).vis = true
          · simp [hv] at hs
          · -- invisible while active: its store is still buffered
            have hb : (s.rd r).buf = true := by
              rcases hx.pub (active_ne_idle ha) (active_ne_called ha) with ⟨hb, _⟩ | ⟨_, hv'⟩
              · exact hb
              · exact absurd hv' hv
            exact hx.late_buf hgf hb ha
        scan_some := by
          intro _ g hs _
          by_cases hv : (s.rd r).vis = true
          · simp [hv] at hs; exact Or.inl hs
          · simp [hv] at hs
        unscanned := by intro hg'; rw [hg] at hg'; rcases hg' with hg' | hg' <;> cases hg' }
  | reclaim k0 e hg hall he hlt hinv =>
    exact
      { start_le := h.start_le
        freed_old := by
          intro k hk
          by_cases hkk : k = k0
          · subst hkk; exact ⟨e, he, by show e < s.G; have := h.start_le (Or.inr hg); omega⟩
          · exact h.freed_old k (by simpa [upd, hkk] using hk)
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, hold := hx.hold
              act_free := by
                intro ha k hk hv
                by_cases hkk : k = k0
                · subst hkk
                  have hv' : s.visAt k (s.rd r).gen := hv
                  cases hs : (s.rd r).seen with
                  | none => exact hall r hs
                  | some o =>
                    cases o with
                    | none =>
                      have := hx.scan_none hg hs ha
                      have hb2 := hv'.2
                      rw [he] at hb2; simp [before] at hb2
                      omega
                    | some g =>
                      rcases hx.scan_some hg g hs (active_ne_idle ha) with hgen | hle
                      · exact hinv r g hs (hgen ▸ hv')
                      · have hb2 := hv'.2
                        rw [he] at hb2; simp [before] at hb2
                        omega
                · exact hx.act_free ha k (by simpa [upd, hkk] using hk) hv
              late_buf := hx.late_buf, scan_none := hx.scan_none
              scan_some := hx.scan_some, unscanned := hx.unscanned } }
  | gcEnd hg =>
    exact
      { start_le := by intro hg'; rcases hg' with hg' | hg' <;> cases hg'
        freed_old := h.freed_old
        rd := fun r => by
          have hx := h.rd r
          exact
            { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, hold := hx.hold
              act_free := hx.act_free
              late_buf := by intro hg'; cases hg'
              scan_none := by intro hg'; cases hg'
              scan_some := by intro hg'; cases hg'
              unscanned := by intro hg'; rcases hg' with hg' | hg' <;> cases hg' } }

end preservation

theorem init_inv {s : St R K} (h : Init s) : Inv s where
  start_le := by intro hg; rw [h.2.1] at hg; rcases hg with hg | hg <;> cases hg
  freed_old := by intro k hk; rw [h.2.2 k] at hk; cases hk
  rd := fun r => by
    obtain ⟨hpc, hv, hb, hs, hg⟩ := h.1 r
    exact
      { gen_le := hg
        lo := fun _ => ⟨hv, hb⟩
        pub := by intro hi; exact absurd hpc hi
        hold := by intro k hk; rw [hpc] at hk; cases hk
        act_free := by intro ha; simp [hpc, Pc.active] at ha
        late_buf := by intro _ hb'; rw [hb] at hb'; cases hb'
        scan_none := by intro _ hs'; rw [hs] at hs'; cases hs'
        scan_some := by intro _ g hs'; rw [hs] at hs'; cases hs'
        unscanned := fun _ => hs }

theorem Inv.safe {s : St R K} (h : Inv s) : Safe s := by
  intro r k hk
  have hx := h.rd r
  have ha : (s.rd r).pc.active = true := by simp [hk, Pc.active]
  cases hf : s.freed k with
  | false => rfl
  | true => exact absurd (hx.hold k hk) (hx.act_free ha k hf)

theorem reach_inv {s t : St R K} (h : Inv s) (hr : Reach s t) : Inv t := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact step_inv ih hst

/-- With a process-wide barrier in clause GC, readers need no barrier. -/
theorem asym_safe {s0 s : St R K} (h0 : Init s0) (hr : Reach s0 s) : Safe s :=
  (reach_inv (init_inv h0) hr).safe

end Mettapedia.Languages.Prolog.SWI.PublishAsym
