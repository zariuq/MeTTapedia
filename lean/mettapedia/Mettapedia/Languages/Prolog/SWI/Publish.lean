/-
The publication protocol between the call port and clause GC.

A frame takes its generation at the call port while it is still at lTop,
where clause GC does not look.  publishGenerationFrame() (S_DYNAMIC,
S_INCR_DYNAMIC; pushPredicateAccessObj() for clause/2 and retract/1 has the
same shape) moves lTop above the frame, issues a full barrier and re-reads
the global generation until it equals the frame's.  Clause GC reads its
start generation, issues a barrier, scans the frames below lTop of every
thread and reclaims a clause erased before the start that is invisible in
every generation it registered (ddi_is_garbage()).

The model has any number of readers and clauses, writers that erase clauses
or advance the generation, and one clause GC run at a time.  The store that
moves lTop goes through the reader's store buffer and becomes visible when
the buffer drains (TSO); a full barrier waits for the drain.  Without its
barrier, clause GC may scan before it reads the start generation (load-load
reordering, allowed on ARM and POWER).  The writer's two stores (erased
generation, then global generation, with a release barrier between) are one
step, and a reader reads clause fields after its generation (see the
assumptions at the end of the file).

`fixed_safe`: with re-validation and both barriers, no frame ever holds a
clause that clause GC reclaimed.  `stock_unsafe`, `no_reader_fence_unsafe`
and `no_gc_fence_unsafe`: without any one of the three, an explicit schedule
reaches a frame holding a reclaimed clause.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mettapedia.Languages.Prolog.SWI.Publish

/-! ## Basics -/

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β)
    (h : x ≠ a) : upd f a b x = f x := by simp [upd, h]

/-- `g` comes before the erased generation; true if the clause is not erased. -/
def before (g : Nat) : Option Nat → Bool
  | none => true
  | some e => decide (g < e)

/-- Program counter of a reader. -/
inductive Pc (K : Type) where
  | idle
  /-- the call port gave the frame a generation; the frame is at lTop -/
  | called
  /-- lTop was moved above the frame (the store may still be buffered) -/
  | published
  /-- the generation is final -/
  | ready
  /-- the frame selected clause `k` and may use it until it exits -/
  | holding (k : K)
deriving DecidableEq

namespace Pc
/-- ready or holding: the frame selects clauses in its generation -/
def active {K : Type} : Pc K → Bool
  | ready => true
  | holding _ => true
  | _ => false
end Pc

/-- Program counter of the clause GC. -/
inductive GPc where
  | idle
  | begun
  | started
deriving DecidableEq

/-- A reader (a frame).  `seen` is what the running clause GC recorded:
not scanned yet, scanned while invisible, or scanned with a generation. -/
structure RS (K : Type) where
  pc   : Pc K
  gen  : Nat
  vis  : Bool
  buf  : Bool
  seen : Option (Option Nat)

structure St (R K : Type) where
  G      : Nat
  born   : K → Nat
  erased : K → Option Nat
  freed  : K → Bool
  rd     : R → RS K
  gpc    : GPc
  start  : Nat

/-- Which of the three orderings the protocol has. -/
structure Proto where
  /-- re-read the generation after moving lTop (publishGenerationFrame) -/
  validate    : Bool
  /-- full barrier between moving lTop and re-reading the generation -/
  readerFence : Bool
  /-- barrier between reading the start generation and scanning -/
  gcFence     : Bool

def fixed : Proto := ⟨true, true, true⟩
/-- The stock call port, and S_STATIC: no re-validation. -/
def stock : Proto := ⟨false, true, true⟩
def noReaderFence : Proto := ⟨true, false, true⟩
def noGcFence : Proto := ⟨true, true, false⟩

variable {R K : Type} [DecidableEq R] [DecidableEq K]

def St.visAt (s : St R K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

instance (s : St R K) (k : K) (g : Nat) : Decidable (s.visAt k g) := by
  unfold St.visAt; infer_instance

def St.setR (s : St R K) (r : R) (x : RS K) : St R K := { s with rd := upd s.rd r x }

/-! ## Transitions -/

inductive Step (P : Proto) : St R K → St R K → Prop where
  /-- Any other change of the database advances the generation. -/
  | bump (s : St R K) : Step P s { s with G := s.G + 1 }
  /-- retract_clause(): under L_GENERATION, erased := G+1, release barrier,
      G := G+1. -/
  | erase (s : St R K) (k : K) (h : s.erased k = none) :
      Step P s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  /-- The store buffer of `r` drains: other threads see lTop above the frame. -/
  | drain (s : St R K) (r : R) (h : (s.rd r).buf = true) :
      Step P s (s.setR r { s.rd r with vis := true, buf := false })
  /-- The call port gives the frame the current generation. -/
  | call (s : St R K) (r : R) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { s.rd r with pc := .called, gen := s.G })
  /-- lTop is moved above the frame; the store enters the store buffer. -/
  | publish (s : St R K) (r : R) (h : (s.rd r).pc = .called) :
      Step P s (s.setR r { s.rd r with pc := .published, buf := true })
  /-- The generation moved: take it again and re-read. -/
  | retake (s : St R K) (r : R) (hv : P.validate = true)
      (h : (s.rd r).pc = .published)
      (hf : P.readerFence = true → (s.rd r).buf = false)
      (hne : (s.rd r).gen ≠ s.G) :
      Step P s (s.setR r { s.rd r with gen := s.G })
  /-- The generation equals the frame's: select clauses. -/
  | confirm (s : St R K) (r : R) (hv : P.validate = true)
      (h : (s.rd r).pc = .published)
      (hf : P.readerFence = true → (s.rd r).buf = false)
      (heq : (s.rd r).gen = s.G) :
      Step P s (s.setR r { s.rd r with pc := .ready })
  /-- Without re-validation: select at once. -/
  | skip (s : St R K) (r : R) (hv : P.validate = false)
      (h : (s.rd r).pc = .published) :
      Step P s (s.setR r { s.rd r with pc := .ready })
  /-- Select a clause visible in the frame's generation (first call or
      backtracking); the frame holds it until it exits. -/
  | select (s : St R K) (r : R) (k : K) (h : (s.rd r).pc.active = true)
      (hk : s.visAt k (s.rd r).gen) :
      Step P s (s.setR r { s.rd r with pc := .holding k })
  /-- The frame exits: lTop drops below it. -/
  | exit (s : St R K) (r : R) (h : (s.rd r).pc.active = true)
      (hb : (s.rd r).buf = false) :
      Step P s (s.setR r { s.rd r with pc := .idle, vis := false })
  /-- A clause GC run begins. -/
  | gcBegin (s : St R K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .begun, rd := fun r => { s.rd r with seen := none } }
  /-- It reads its start generation. -/
  | gcStart (s : St R K) (h : s.gpc = .begun) :
      Step P s { s with gpc := .started, start := s.G }
  /-- It scans reader `r`: a frame below lTop registers its generation.
      Without the barrier the scan may come before the start generation. -/
  | scan (s : St R K) (r : R)
      (h : s.gpc = .started ∨ (P.gcFence = false ∧ s.gpc = .begun))
      (hn : (s.rd r).seen = none) :
      Step P s (s.setR r { s.rd r with
        seen := some (if (s.rd r).vis then some (s.rd r).gen else none) })
  /-- ddi_is_garbage(): erased before the start and invisible in every
      registered generation.  (The interval mode reclaims fewer clauses.) -/
  | reclaim (s : St R K) (k : K) (e : Nat) (h : s.gpc = .started)
      (hall : ∀ r, (s.rd r).seen ≠ none) (he : s.erased k = some e)
      (hlt : e < s.start)
      (hinv : ∀ r g, (s.rd r).seen = some (some g) → ¬ s.visAt k g) :
      Step P s { s with freed := upd s.freed k true }
  /-- The run ends. -/
  | gcEnd (s : St R K) (h : s.gpc = .started) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St R K → St R K → Prop where
  | refl (s : St R K) : Reach P s s
  | tail {s t u : St R K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St R K) : Prop :=
  (∀ r, (s.rd r).pc = .idle ∧ (s.rd r).vis = false ∧ (s.rd r).buf = false ∧
        (s.rd r).seen = none ∧ (s.rd r).gen ≤ s.G) ∧
  s.gpc = .idle ∧ (∀ k, s.freed k = false)

/-- No frame holds a reclaimed clause. -/
def Safe (s : St R K) : Prop := ∀ r k, (s.rd r).pc = .holding k → s.freed k = false

/-! ## The invariant -/

structure RInv (s : St R K) (x : RS K) : Prop where
  gen_le    : x.gen ≤ s.G
  lo        : x.pc = .idle ∨ x.pc = .called → x.vis = false ∧ x.buf = false
  pub       : x.pc = .published →
                (x.buf = true ∧ x.vis = false) ∨ (x.buf = false ∧ x.vis = true)
  act       : x.pc.active = true → x.vis = true ∧ x.buf = false
  hold      : ∀ k, x.pc = .holding k → s.visAt k x.gen
  act_free  : x.pc.active = true → ∀ k, s.freed k = true → ¬ s.visAt k x.gen
  scan_none : s.gpc = .started → x.seen = some none → x.pc.active = true →
                s.start ≤ x.gen
  scan_some : s.gpc = .started → ∀ g, x.seen = some (some g) → x.pc ≠ .idle →
                x.gen = g ∨ s.start ≤ x.gen
  begun     : s.gpc = .begun → x.seen = none

structure Inv (s : St R K) : Prop where
  start_le  : s.gpc = .started → s.start ≤ s.G
  freed_old : ∀ k, s.freed k = true → ∃ e, s.erased k = some e ∧ e < s.G
  rd        : ∀ r, RInv s (s.rd r)

section lemmas

@[simp] theorem setR_same (s : St R K) (r : R) (x : RS K) : (s.setR r x).rd r = x := by
  simp [St.setR, upd]

theorem setR_ne (s : St R K) {r r' : R} (x : RS K) (h : r' ≠ r) :
    (s.setR r x).rd r' = s.rd r' := by
  simp [St.setR, upd, h]

@[simp] theorem setR_G (s : St R K) (r : R) (x : RS K) : (s.setR r x).G = s.G := rfl
@[simp] theorem setR_born (s : St R K) (r : R) (x : RS K) : (s.setR r x).born = s.born := rfl
@[simp] theorem setR_erased (s : St R K) (r : R) (x : RS K) :
    (s.setR r x).erased = s.erased := rfl
@[simp] theorem setR_freed (s : St R K) (r : R) (x : RS K) :
    (s.setR r x).freed = s.freed := rfl
@[simp] theorem setR_gpc (s : St R K) (r : R) (x : RS K) : (s.setR r x).gpc = s.gpc := rfl
@[simp] theorem setR_start (s : St R K) (r : R) (x : RS K) :
    (s.setR r x).start = s.start := rfl

theorem visAt_congr {s t : St R K} (hb : s.born = t.born) (he : s.erased = t.erased)
    (k : K) (g : Nat) : s.visAt k g ↔ t.visAt k g := by
  simp [St.visAt, hb, he]

/-- An invariant of a reader depends only on the shared fields. -/
theorem RInv.congr {s t : St R K} {x : RS K} (hG : s.G = t.G) (hb : s.born = t.born)
    (he : s.erased = t.erased) (hf : s.freed = t.freed) (hg : s.gpc = t.gpc)
    (hs : s.start = t.start) (h : RInv s x) : RInv t x where
  gen_le := hG ▸ h.gen_le
  lo := h.lo
  pub := h.pub
  act := h.act
  hold := fun k hk => (visAt_congr hb he k x.gen).1 (h.hold k hk)
  act_free := fun ha k hk hv =>
    h.act_free ha k (hf ▸ hk) ((visAt_congr hb he k x.gen).2 hv)
  scan_none := fun hgs hseen ha => hs ▸ h.scan_none (hg ▸ hgs) hseen ha
  scan_some := fun hgs g hseen hne => hs ▸ h.scan_some (hg ▸ hgs) g hseen hne
  begun := fun hgb => h.begun (hg ▸ hgb)

theorem active_ne_idle {x : RS K} (h : x.pc.active = true) : x.pc ≠ .idle := by
  intro h'; rw [h'] at h; simp [Pc.active] at h

/-- A reader step: the other readers keep their invariant. -/
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

/-! ## Preservation -/

section preservation

theorem inv_bump {s : St R K} (h : Inv s) : Inv { s with G := s.G + 1 } where
  start_le := fun hg => Nat.le_succ_of_le (h.start_le hg)
  freed_old := fun k hk => by
    obtain ⟨e, he, hlt⟩ := h.freed_old k hk
    exact ⟨e, he, by simp; omega⟩
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := by simp; have := hx.gen_le; omega
        lo := hx.lo, pub := hx.pub, act := hx.act
        hold := hx.hold, act_free := hx.act_free
        scan_none := hx.scan_none, scan_some := hx.scan_some, begun := hx.begun }

theorem inv_erase {s : St R K} {k0 : K} (h : Inv s) (hk0 : s.erased k0 = none) :
    Inv { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } := by
  -- a freed clause is erased, so it is not k0
  have fne : ∀ k, s.freed k = true → k ≠ k0 := by
    intro k hk heq
    obtain ⟨e, he, _⟩ := h.freed_old k hk
    rw [heq, hk0] at he; cases he
  -- visibility of every clause but k0 is unchanged
  have vis_ne : ∀ k g, k ≠ k0 →
      (St.visAt { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } k g ↔
        s.visAt k g) := by
    intro k g hne
    simp [St.visAt, upd, hne]
  refine ⟨?_, ?_, ?_⟩
  · intro hg; have := h.start_le hg; simp; omega
  · intro k hk
    obtain ⟨e, he, hlt⟩ := h.freed_old k hk
    refine ⟨e, ?_, by simp; omega⟩
    simp [upd, fne k hk, he]
  · intro r
    have hx := h.rd r
    exact
      { gen_le := by simp; have := hx.gen_le; omega
        lo := hx.lo, pub := hx.pub, act := hx.act
        hold := by
          intro k hk
          by_cases hkk : k = k0
          · subst hkk
            have hv := hx.hold k hk
            have := hx.gen_le
            simp only [St.visAt, upd_same] at hv ⊢
            exact ⟨hv.1, by simp [before]; omega⟩
          · exact (vis_ne k _ hkk).2 (hx.hold k hk)
        act_free := by
          intro ha k hk hv
          exact hx.act_free ha k hk ((vis_ne k _ (fne k hk)).1 hv)
        scan_none := hx.scan_none, scan_some := hx.scan_some, begun := hx.begun }

theorem inv_drain {s : St R K} {r : R} (h : Inv s) (hb : (s.rd r).buf = true) :
    Inv (s.setR r { s.rd r with vis := true, buf := false }) := by
  have hx := h.rd r
  -- a buffered store means the reader just published
  have hpub : (s.rd r).pc = .published := by
    cases hpc : (s.rd r).pc with
    | idle => have := (hx.lo (Or.inl hpc)).2; rw [hb] at this; cases this
    | called => have := (hx.lo (Or.inr hpc)).2; rw [hb] at this; cases this
    | published => rfl
    | ready =>
        have := (hx.act (by simp [hpc, Pc.active])).2; rw [hb] at this; cases this
    | holding k =>
        have := (hx.act (by simp [hpc, Pc.active])).2; rw [hb] at this; cases this
  apply inv_setR h
  exact
    { gen_le := hx.gen_le
      lo := by intro hl; rw [hpub] at hl; simp at hl
      pub := fun _ => Or.inr ⟨rfl, rfl⟩
      act := by intro ha; simp [hpub, Pc.active] at ha
      hold := by intro k hk; simp [hpub] at hk
      act_free := by intro ha; simp [hpub, Pc.active] at ha
      scan_none := by intro _ _ ha; simp [hpub, Pc.active] at ha
      scan_some := hx.scan_some
      begun := hx.begun }

theorem inv_call {s : St R K} {r : R} (h : Inv s) (hpc : (s.rd r).pc = .idle) :
    Inv (s.setR r { s.rd r with pc := .called, gen := s.G }) := by
  have hx := h.rd r
  have hlo := hx.lo (Or.inl hpc)
  apply inv_setR h
  exact
    { gen_le := Nat.le_refl _
      lo := fun _ => hlo
      pub := by intro hp; simp at hp
      act := by intro ha; simp [Pc.active] at ha
      hold := by intro k hk; simp at hk
      act_free := by intro ha; simp [Pc.active] at ha
      scan_none := by intro _ _ ha; simp [Pc.active] at ha
      scan_some := fun hg _ _ _ => Or.inr (h.start_le hg)
      begun := hx.begun }

theorem inv_publish {s : St R K} {r : R} (h : Inv s) (hpc : (s.rd r).pc = .called) :
    Inv (s.setR r { s.rd r with pc := .published, buf := true }) := by
  have hx := h.rd r
  have hlo := hx.lo (Or.inr hpc)
  apply inv_setR h
  exact
    { gen_le := hx.gen_le
      lo := by intro hl; simp at hl
      pub := fun _ => Or.inl ⟨rfl, hlo.1⟩
      act := by intro ha; simp [Pc.active] at ha
      hold := by intro k hk; simp at hk
      act_free := by intro ha; simp [Pc.active] at ha
      scan_none := by intro _ _ ha; simp [Pc.active] at ha
      scan_some := fun hg g hs _ => hx.scan_some hg g hs (by rw [hpc]; simp)
      begun := hx.begun }

theorem inv_retake {s : St R K} {r : R} (h : Inv s) (hpc : (s.rd r).pc = .published) :
    Inv (s.setR r { s.rd r with gen := s.G }) := by
  have hx := h.rd r
  apply inv_setR h
  exact
    { gen_le := Nat.le_refl _
      lo := by intro hl; rw [hpc] at hl; simp at hl
      pub := fun hp => hx.pub hp
      act := by intro ha; simp [hpc, Pc.active] at ha
      hold := by intro k hk; simp [hpc] at hk
      act_free := by intro ha; simp [hpc, Pc.active] at ha
      scan_none := by intro _ _ ha; simp [hpc, Pc.active] at ha
      scan_some := fun hg _ _ _ => Or.inr (h.start_le hg)
      begun := hx.begun }

theorem inv_confirm {s : St R K} {r : R} (h : Inv s) (hpc : (s.rd r).pc = .published)
    (hb : (s.rd r).buf = false) (heq : (s.rd r).gen = s.G) :
    Inv (s.setR r { s.rd r with pc := .ready }) := by
  have hx := h.rd r
  have hvis : (s.rd r).vis = true := by
    rcases hx.pub hpc with ⟨hb', _⟩ | ⟨_, hv⟩
    · rw [hb] at hb'; cases hb'
    · exact hv
  apply inv_setR h
  exact
    { gen_le := hx.gen_le
      lo := by intro hl; simp at hl
      pub := by intro hp; simp at hp
      act := fun _ => ⟨hvis, hb⟩
      hold := by intro k hk; simp at hk
      act_free := by
        intro _ k hk hv
        obtain ⟨e, he, hlt⟩ := h.freed_old k hk
        have hb2 := hv.2
        simp only at hb2
        rw [he, heq] at hb2
        simp [before] at hb2
        omega
      scan_none := fun hg _ _ => by
        simp only; rw [heq]; exact h.start_le hg
      scan_some := fun hg g hs _ => hx.scan_some hg g hs (by rw [hpc]; simp)
      begun := hx.begun }

theorem inv_select {s : St R K} {r : R} {k : K} (h : Inv s)
    (hpc : (s.rd r).pc.active = true) (hk : s.visAt k (s.rd r).gen) :
    Inv (s.setR r { s.rd r with pc := .holding k }) := by
  have hx := h.rd r
  apply inv_setR h
  exact
    { gen_le := hx.gen_le
      lo := by intro hl; simp at hl
      pub := by intro hp; simp at hp
      act := fun _ => hx.act hpc
      hold := by intro k' hk'; simp at hk'; subst hk'; exact hk
      act_free := fun _ => hx.act_free hpc
      scan_none := fun hg hs _ => hx.scan_none hg hs hpc
      scan_some := fun hg g hs _ => hx.scan_some hg g hs (active_ne_idle hpc)
      begun := hx.begun }

theorem inv_exit {s : St R K} {r : R} (h : Inv s) (hb : (s.rd r).buf = false) :
    Inv (s.setR r { s.rd r with pc := .idle, vis := false }) := by
  have hx := h.rd r
  apply inv_setR h
  exact
    { gen_le := hx.gen_le
      lo := fun _ => ⟨rfl, hb⟩
      pub := by intro hp; simp at hp
      act := by intro ha; simp [Pc.active] at ha
      hold := by intro k hk; simp at hk
      act_free := by intro ha; simp [Pc.active] at ha
      scan_none := by intro _ _ ha; simp [Pc.active] at ha
      scan_some := by intro _ _ _ hne; simp at hne
      begun := hx.begun }

theorem inv_gcBegin {s : St R K} (h : Inv s) :
    Inv { s with gpc := .begun, rd := fun r => { s.rd r with seen := none } } where
  start_le := by intro hg; simp at hg
  freed_old := h.freed_old
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, act := hx.act
        hold := hx.hold, act_free := hx.act_free
        scan_none := by intro hg; simp at hg
        scan_some := by intro hg; simp at hg
        begun := fun _ => rfl }

theorem inv_gcStart {s : St R K} (h : Inv s) (hg : s.gpc = .begun) :
    Inv { s with gpc := .started, start := s.G } where
  start_le := fun _ => Nat.le_refl _
  freed_old := h.freed_old
  rd := fun r => by
    have hx := h.rd r
    have hn := hx.begun hg
    exact
      { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, act := hx.act
        hold := hx.hold, act_free := hx.act_free
        scan_none := by intro _ hs; rw [hn] at hs; cases hs
        scan_some := by intro _ g hs; rw [hn] at hs; cases hs
        begun := by intro hb; simp at hb }

theorem inv_scan {s : St R K} {r : R} (h : Inv s) (hg : s.gpc = .started) :
    Inv (s.setR r { s.rd r with
      seen := some (if (s.rd r).vis then some (s.rd r).gen else none) }) := by
  have hx := h.rd r
  apply inv_setR h
  exact
    { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, act := hx.act
      hold := hx.hold, act_free := hx.act_free
      scan_none := by
        intro _ hs ha
        have hv := (hx.act ha).1
        simp [hv] at hs
      scan_some := by
        intro _ g hs _
        by_cases hv : (s.rd r).vis = true
        · simp [hv] at hs; exact Or.inl hs
        · simp [hv] at hs
      begun := by intro hb; rw [hg] at hb; cases hb }

theorem inv_reclaim {s : St R K} {k0 : K} {e : Nat} (h : Inv s) (hg : s.gpc = .started)
    (hall : ∀ r, (s.rd r).seen ≠ none) (he : s.erased k0 = some e) (hlt : e < s.start)
    (hinv : ∀ r g, (s.rd r).seen = some (some g) → ¬ s.visAt k0 g) :
    Inv { s with freed := upd s.freed k0 true } where
  start_le := h.start_le
  freed_old := by
    intro k hk
    by_cases hkk : k = k0
    · subst hkk; exact ⟨e, he, by show e < s.G; have := h.start_le hg; omega⟩
    · simp [upd, hkk] at hk; exact h.freed_old k hk
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, act := hx.act
        hold := hx.hold
        act_free := by
          intro ha k hk hv
          by_cases hkk : k = k0
          · subst hkk
            -- the reader was scanned: invisible, or with its generation
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
          · simp [upd, hkk] at hk
            exact hx.act_free ha k hk hv
        scan_none := hx.scan_none, scan_some := hx.scan_some, begun := hx.begun }

theorem inv_gcEnd {s : St R K} (h : Inv s) : Inv { s with gpc := .idle } where
  start_le := by intro hg; simp at hg
  freed_old := h.freed_old
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, lo := hx.lo, pub := hx.pub, act := hx.act
        hold := hx.hold, act_free := hx.act_free
        scan_none := by intro hg; simp at hg
        scan_some := by intro hg; simp at hg
        begun := by intro hb; simp at hb }

theorem step_inv {s t : St R K} (h : Inv s) (hst : Step fixed s t) : Inv t := by
  cases hst with
  | bump => exact inv_bump h
  | erase k hk => exact inv_erase h hk
  | drain r hb => exact inv_drain h hb
  | call r hpc => exact inv_call h hpc
  | publish r hpc => exact inv_publish h hpc
  | retake r _ hpc _ _ => exact inv_retake h hpc
  | confirm r _ hpc hf heq => exact inv_confirm h hpc (hf rfl) heq
  | skip r hv _ => simp [fixed] at hv
  | select r k hpc hk => exact inv_select h hpc hk
  | exit r _ hb => exact inv_exit h hb
  | gcBegin => exact inv_gcBegin h
  | gcStart hg => exact inv_gcStart h hg
  | scan r hg _ =>
      rcases hg with hg | ⟨hf, _⟩
      · exact inv_scan h hg
      · simp [fixed] at hf
  | reclaim k e hg hall he hlt hinv => exact inv_reclaim h hg hall he hlt hinv
  | gcEnd => exact inv_gcEnd h

end preservation

theorem init_inv {s : St R K} (h : Init s) : Inv s where
  start_le := by intro hg; rw [h.2.1] at hg; cases hg
  freed_old := by intro k hk; rw [h.2.2 k] at hk; cases hk
  rd := fun r => by
    obtain ⟨hpc, hv, hb, hs, hg⟩ := h.1 r
    exact
      { gen_le := hg
        lo := fun _ => ⟨hv, hb⟩
        pub := by intro hp; rw [hpc] at hp; cases hp
        act := by intro ha; simp [hpc, Pc.active] at ha
        hold := by intro k hk; rw [hpc] at hk; cases hk
        act_free := by intro ha; simp [hpc, Pc.active] at ha
        scan_none := by intro _ hs'; rw [hs] at hs'; cases hs'
        scan_some := by intro _ g hs'; rw [hs] at hs'; cases hs'
        begun := fun _ => hs }

theorem Inv.safe {s : St R K} (h : Inv s) : Safe s := by
  intro r k hk
  have hx := h.rd r
  have ha : (s.rd r).pc.active = true := by simp [hk, Pc.active]
  cases hf : s.freed k with
  | false => rfl
  | true => exact absurd (hx.hold k hk) (hx.act_free ha k hf)

theorem reach_inv {s t : St R K} (h : Inv s) (hr : Reach fixed s t) : Inv t := by
  induction hr with
  | refl => exact h
  | tail _ hst ih => exact step_inv ih hst

/-- With re-validation and both barriers, no frame ever holds a clause that
clause GC reclaimed, for any schedule. -/
theorem fixed_safe {s0 s : St R K} (h0 : Init s0) (hr : Reach fixed s0 s) : Safe s :=
  (reach_inv (init_inv h0) hr).safe

/-! ## Each ordering is needed

One reader and one clause, born at generation 0. -/

section counterexamples

def r0 : RS Unit := ⟨.idle, 0, false, false, none⟩
def c0 : St Unit Unit := ⟨0, fun _ => 0, fun _ => none, fun _ => false, fun _ => r0, .idle, 0⟩

theorem c0_init : Init c0 := by
  refine ⟨fun r => ?_, rfl, fun _ => rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, Nat.le_refl _⟩

theorem not_safe_of {s : St Unit Unit} (hh : (s.rd ()).pc = .holding ())
    (hf : s.freed () = true) : ¬ Safe s := by
  intro hs; have := hs () () hh; rw [hf] at this; cases this

/-- Unsafe states are reachable when a step sequence leads to one. -/
theorem reach_of_steps {P : Proto} {s t u : St Unit Unit} (h1 : Reach P s t)
    (h2 : Step P t u) : Reach P s u := Reach.tail h1 h2

/-- The stock call port (and S_STATIC): the frame keeps the generation of the
call port.  It is taken; the clause is erased; clause GC starts, does not see
the frame (still at lTop) and reclaims the clause; the frame then moves lTop
and selects it. -/
theorem stock_unsafe : ∃ s, Reach stock c0 s ∧ ¬ Safe s := by
  let s1 := c0.setR () { c0.rd () with pc := .called, gen := c0.G }
  let s2 : St Unit Unit := { s1 with G := s1.G + 1, erased := upd s1.erased () (some (s1.G + 1)) }
  let s3 : St Unit Unit := { s2 with G := s2.G + 1 }
  let s4 : St Unit Unit := { s3 with gpc := .begun, rd := fun r => { s3.rd r with seen := none } }
  let s5 : St Unit Unit := { s4 with gpc := .started, start := s4.G }
  let s6 := s5.setR () { s5.rd () with
              seen := some (if (s5.rd ()).vis then some (s5.rd ()).gen else none) }
  let s7 : St Unit Unit := { s6 with freed := upd s6.freed () true }
  let s8 := s7.setR () { s7.rd () with pc := .published, buf := true }
  let s9 := s8.setR () { s8.rd () with vis := true, buf := false }
  let s10 := s9.setR () { s9.rd () with pc := .ready }
  let s11 := s10.setR () { s10.rd () with pc := .holding () }
  refine ⟨s11, ?_, not_safe_of (by decide) (by decide)⟩
  refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
    (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl c0)
    (Step.call c0 () (by decide)))
    (Step.erase s1 () (by decide)))
    (Step.bump s2))
    (Step.gcBegin s3 (by decide)))
    (Step.gcStart s4 (by decide)))
    (Step.scan s5 () (Or.inl (by decide)) (by decide)))
    (Step.reclaim s6 () 1 (by decide) (by intro r; cases r; decide) (by decide)
      (by decide) ?_))
    (Step.publish s7 () (by decide)))
    (Step.drain s8 () (by decide)))
    (Step.skip s9 () (by decide) (by decide)))
    (Step.select s10 () () (by decide) (by decide))
  intro r g hs
  cases r
  have : (s6.rd ()).seen = some none := by decide
  rw [this] at hs; cases hs

/-- Without the reader's barrier the store that moves lTop can still be in
the store buffer when the frame re-reads the generation.  The frame selects
the clause; it is erased; clause GC scans while the store is buffered, does
not see the frame and reclaims the clause. -/
theorem no_reader_fence_unsafe : ∃ s, Reach noReaderFence c0 s ∧ ¬ Safe s := by
  let s1 := c0.setR () { c0.rd () with pc := .called, gen := c0.G }
  let s2 := s1.setR () { s1.rd () with pc := .published, buf := true }
  let s3 := s2.setR () { s2.rd () with pc := .ready }
  let s4 := s3.setR () { s3.rd () with pc := .holding () }
  let s5 : St Unit Unit := { s4 with G := s4.G + 1, erased := upd s4.erased () (some (s4.G + 1)) }
  let s6 : St Unit Unit := { s5 with G := s5.G + 1 }
  let s7 : St Unit Unit := { s6 with gpc := .begun, rd := fun r => { s6.rd r with seen := none } }
  let s8 : St Unit Unit := { s7 with gpc := .started, start := s7.G }
  let s9 := s8.setR () { s8.rd () with
              seen := some (if (s8.rd ()).vis then some (s8.rd ()).gen else none) }
  let s10 : St Unit Unit := { s9 with freed := upd s9.freed () true }
  refine ⟨s10, ?_, not_safe_of (by decide) (by decide)⟩
  refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
    (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl c0)
    (Step.call c0 () (by decide)))
    (Step.publish s1 () (by decide)))
    (Step.confirm s2 () (by decide) (by decide) (by decide) (by decide)))
    (Step.select s3 () () (by decide) (by decide)))
    (Step.erase s4 () (by decide)))
    (Step.bump s5))
    (Step.gcBegin s6 (by decide)))
    (Step.gcStart s7 (by decide)))
    (Step.scan s8 () (Or.inl (by decide)) (by decide)))
    (Step.reclaim s9 () 1 (by decide) (by intro r; cases r; decide) (by decide)
      (by decide) ?_)
  intro r g hs
  cases r
  have : (s9.rd ()).seen = some none := by decide
  rw [this] at hs; cases hs

/-- Without the barrier of clause GC its scan can come before it reads the
start generation: it scans before the frame exists, the frame takes the
generation, publishes and selects the clause, the clause is erased, and
clause GC reads a start generation after the erasure. -/
theorem no_gc_fence_unsafe : ∃ s, Reach noGcFence c0 s ∧ ¬ Safe s := by
  let s1 : St Unit Unit := { c0 with gpc := .begun, rd := fun r => { c0.rd r with seen := none } }
  let s2 := s1.setR () { s1.rd () with
              seen := some (if (s1.rd ()).vis then some (s1.rd ()).gen else none) }
  let s3 := s2.setR () { s2.rd () with pc := .called, gen := s2.G }
  let s4 := s3.setR () { s3.rd () with pc := .published, buf := true }
  let s5 := s4.setR () { s4.rd () with vis := true, buf := false }
  let s6 := s5.setR () { s5.rd () with pc := .ready }
  let s7 := s6.setR () { s6.rd () with pc := .holding () }
  let s8 : St Unit Unit := { s7 with G := s7.G + 1, erased := upd s7.erased () (some (s7.G + 1)) }
  let s9 : St Unit Unit := { s8 with G := s8.G + 1 }
  let s10 : St Unit Unit := { s9 with gpc := .started, start := s9.G }
  let s11 : St Unit Unit := { s10 with freed := upd s10.freed () true }
  refine ⟨s11, ?_, not_safe_of (by decide) (by decide)⟩
  refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
    (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.refl c0)
    (Step.gcBegin c0 (by decide)))
    (Step.scan s1 () (Or.inr ⟨by decide, by decide⟩) (by decide)))
    (Step.call s2 () (by decide)))
    (Step.publish s3 () (by decide)))
    (Step.drain s4 () (by decide)))
    (Step.confirm s5 () (by decide) (by decide) (by decide) (by decide)))
    (Step.select s6 () () (by decide) (by decide)))
    (Step.erase s7 () (by decide)))
    (Step.bump s8))
    (Step.gcStart s9 (by decide)))
    (Step.reclaim s10 () 1 (by decide) (by intro r; cases r; decide) (by decide)
      (by decide) ?_)
  intro r g hs
  cases r
  have : (s10.rd ()).seen = some none := by decide
  rw [this] at hs; cases hs

end counterexamples

end Mettapedia.Languages.Prolog.SWI.Publish
