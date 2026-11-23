/-
The call port protocol, refined: buffered stores, per-thread barrier
crossings and supervisor lifetimes.

A frame protects what it reads only once clause GC can see it.  Clause GC
reads its start generation, scans the frames below lTop of every thread,
then reclaims a clause erased before the start that is invisible in every
generation it found (ddi_is_garbage()), and frees a supervisor replaced at a
generation below the start and below every generation it found
(cleanDefinition() -> free_lingering()).

The protocol modelled here is the code of revision 14.  In
depart_or_retry_continue, before reading DEF->codes, the frame moves lTop
above itself, and setGenerationFrame() loops: load the global generation,
store it as the frame's, barrier, and load the global generation again;
done when that equals the stored one.

Every store of a reader goes through a store buffer that drains in order for
each address (the frame's generation field; lTop), and in any order across
the two.  This allows the store-store reordering of ARM and contains TSO.
Loads read shared memory in program order (on ARM: acquire loads of the
global generation).  Two ways to order a reader's stores before its loads:
  * `fence`: a full barrier before each load of the generation;
  * `cross`: clause GC makes every thread cross a barrier after reading its
    start generation (membarrier(), FlushProcessWriteBuffers()); each thread
    crosses at its own moment while the others run, and clause GC scans
    once all have crossed.
Revision 3 adds `light`: the call port runs the loop with a compiler barrier
only (setGenerationCallPort()); without a process-wide barrier (ALERT_FENCE)
depart_alerted runs it again with the full barrier before DEF->codes.  A
`light` step leaves a stored generation unvalidated, whatever the
comparison found, and the loop goes round again.

`safe`: with either, re-validation, and DEF->codes read after validation,
no frame ever holds a reclaimed clause or a freed supervisor, with or
without `light` rounds (`fallback_safe`: the fence, after light rounds).  Counter-
examples: `early_codes_unsafe` (DEF->codes read before validating, the
place of the S_TRUSTME use-after-free), `no_recheck_unsafe` (the loaded
generation stored without loading again), `neither_unsafe` (no fence and no
crossing).

Revision 3b: a clause GC that has started may give up without scanning
(`gcAbort`: `processBarrier()` could not reach every thread); it frees
nothing, and the results above include such runs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mettapedia.Languages.Prolog.SWI.CallPort

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def before (g : Nat) : Option Nat → Bool
  | none => true
  | some e => decide (g < e)

/-- The last element of a list, or `d`. -/
def lastD {α : Type} : List α → α → α
  | [], d => d
  | a :: l, _ => lastD l a

theorem lastD_append {α : Type} (l : List α) (a d : α) : lastD (l ++ [a]) d = a := by
  induction l generalizing d with
  | nil => rfl
  | cons b l ih => exact ih b

inductive Pc where
  | idle
  /-- the new frame, still at lTop -/
  | called
  /-- moved lTop above itself (maybe still buffered); next: load G -/
  | storing
  /-- loaded G = `v`; next: store it -/
  | grabbed (v : Nat)
  /-- stored its generation; next: barrier, load G and compare -/
  | stored
  /-- its generation is final -/
  | validated
  /-- read DEF->codes; runs the supervisor and selects clauses -/
  | running
deriving DecidableEq

namespace Pc
/-- lTop was moved above the frame -/
def pub : Pc → Bool
  | idle => false
  | called => false
  | _ => true
def final : Pc → Bool
  | validated => true
  | running => true
  | _ => false
end Pc

inductive GPc where
  | idle
  | begun
  | started
  | scanning
deriving DecidableEq

/-- A reader: the frame of a call. -/
structure RS (K : Type) where
  pc      : Pc
  /-- its generation, as the thread sees it (its last store) -/
  gen     : Nat
  /-- pending stores to the generation field, oldest first -/
  pgen    : List Nat
  /-- pending stores to lTop (above or below the frame), oldest first -/
  ptop    : List Bool
  /-- the generation field in shared memory -/
  mgen    : Nat
  /-- lTop above the frame, in shared memory -/
  vis     : Bool
  /-- the supervisor version it runs -/
  code    : Option Nat
  /-- a clause it selected -/
  hold    : Option K
  /-- crossed the barrier of the running clause GC -/
  crossed : Bool
  /-- what the running clause GC recorded -/
  seen    : Option (Option Nat)

structure St (R K : Type) where
  G      : Nat
  born   : K → Nat
  erased : K → Option Nat
  cfreed : K → Bool
  /-- the current supervisor version (DEF->codes) -/
  cur    : Nat
  /-- generation at which a version was replaced and put on the linger list -/
  dead   : Nat → Option Nat
  vfreed : Nat → Bool
  rd     : R → RS K
  gpc    : GPc
  start  : Nat

structure Proto where
  fence   : Bool
  cross   : Bool
  early   : Bool
  recheck : Bool
  light   : Bool

/-- A full barrier before each load (the reference implementation). -/
def symmetric : Proto := ⟨true, false, false, true, false⟩
/-- membarrier() in clause GC, a compiler barrier in the reader. -/
def asymmetric : Proto := ⟨false, true, false, true, false⟩
/-- No process-wide barrier: the call port's loop with a compiler barrier,
then the loop with a full barrier (ALERT_FENCE in depart_alerted). -/
def fallback : Proto := ⟨true, false, false, true, true⟩
/-- A thread that still has ALERT_FENCE while clause GC uses membarrier()
(the main thread before its next updateAlerted()). -/
def asymmetricLight : Proto := ⟨false, true, false, true, true⟩
/-- Validation inside the supervisor, after DEF->codes was read. -/
def earlyCodes : Proto := ⟨true, false, true, true, false⟩
def noRecheck : Proto := ⟨true, false, false, false, false⟩
def neither : Proto := ⟨false, false, false, true, false⟩

variable {R K : Type} [DecidableEq R] [DecidableEq K]

def St.visAt (s : St R K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

instance (s : St R K) (k : K) (g : Nat) : Decidable (s.visAt k g) := by
  unfold St.visAt; infer_instance

def St.setR (s : St R K) (r : R) (x : RS K) : St R K := { s with rd := upd s.rd r x }

inductive Step (P : Proto) : St R K → St R K → Prop where
  | bump (s : St R K) : Step P s { s with G := s.G + 1 }
  | erase (s : St R K) (k : K) (h : s.erased k = none) :
      Step P s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  /-- Reconsult replaces the supervisor; the old one lingers. -/
  | replace (s : St R K) :
      Step P s { s with dead := upd s.dead s.cur (some s.G), cur := s.cur + 1 }
  /-- normal_call: the new frame, at lTop. -/
  | call (s : St R K) (r : R) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { s.rd r with pc := .called })
  /-- Reading DEF->codes before validating. -/
  | early (s : St R K) (r : R) (hp : P.early = true) (h : (s.rd r).pc = .called)
      (hc : (s.rd r).code = none) :
      Step P s (s.setR r { s.rd r with code := some s.cur })
  /-- depart_or_retry_continue moves lTop above the frame. -/
  | publish (s : St R K) (r : R) (h : (s.rd r).pc = .called) :
      Step P s (s.setR r { s.rd r with pc := .storing,
                                        ptop := (s.rd r).ptop ++ [true] })
  /-- setGenerationFrame(): gen = global_generation() -/
  | grab (s : St R K) (r : R) (h : (s.rd r).pc = .storing) :
      Step P s (s.setR r { s.rd r with pc := .grabbed s.G })
  /-- setGenerationFrameVal(fr, gen), into the store buffer. -/
  | put (s : St R K) (r : R) (v : Nat) (h : (s.rd r).pc = .grabbed v) :
      Step P s (s.setR r { s.rd r with pc := if P.recheck then .stored else .validated,
                                        gen := v, pgen := (s.rd r).pgen ++ [v] })
  /-- The barrier, then `while(gen != global_generation())`. -/
  | check (s : St R K) (r : R) (h : (s.rd r).pc = .stored)
      (hf : P.fence = true → (s.rd r).pgen = [] ∧ (s.rd r).ptop = []) :
      Step P s (s.setR r { s.rd r with
        pc := if s.G = (s.rd r).gen then .validated else .storing })
  /-- The loop with a compiler barrier only; the full one validates. -/
  | light (s : St R K) (r : R) (hp : P.light = true) (h : (s.rd r).pc = .stored) :
      Step P s (s.setR r { s.rd r with pc := .storing })
  /-- Read DEF->codes and run the supervisor. -/
  | dispatch (s : St R K) (r : R) (h : (s.rd r).pc = .validated) :
      Step P s (s.setR r { s.rd r with pc := .running,
                                        code := if (s.rd r).code = none then some s.cur
                                                else (s.rd r).code })
  | select (s : St R K) (r : R) (k : K) (h : (s.rd r).pc = .running)
      (hk : s.visAt k (s.rd r).gen) :
      Step P s (s.setR r { s.rd r with hold := some k })
  | exit (s : St R K) (r : R) (h : (s.rd r).pc = .running) :
      Step P s (s.setR r { s.rd r with pc := .idle, code := none, hold := none,
                                        ptop := (s.rd r).ptop ++ [false] })
  | drainGen (s : St R K) (r : R) (v : Nat) (rest : List Nat)
      (h : (s.rd r).pgen = v :: rest) :
      Step P s (s.setR r { s.rd r with mgen := v, pgen := rest })
  | drainTop (s : St R K) (r : R) (b : Bool) (rest : List Bool)
      (h : (s.rd r).ptop = b :: rest) :
      Step P s (s.setR r { s.rd r with vis := b, ptop := rest })
  | gcBegin (s : St R K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .begun,
                        rd := fun r => { s.rd r with crossed := false, seen := none } }
  | gcStart (s : St R K) (h : s.gpc = .begun) :
      Step P s { s with gpc := .started, start := s.G }
  /-- Thread `r` crosses the process-wide barrier: its buffer drains. -/
  | cross (s : St R K) (r : R) (hp : P.cross = true) (h : s.gpc = .started)
      (hc : (s.rd r).crossed = false) :
      Step P s (s.setR r { s.rd r with mgen := lastD (s.rd r).pgen (s.rd r).mgen,
                                        vis := lastD (s.rd r).ptop (s.rd r).vis,
                                        pgen := [], ptop := [], crossed := true })
  | toScan (s : St R K) (h : s.gpc = .started)
      (hc : P.cross = true → ∀ r, (s.rd r).crossed = true) :
      Step P s { s with gpc := .scanning }
  | scan (s : St R K) (r : R) (h : s.gpc = .scanning) (hn : (s.rd r).seen = none) :
      Step P s (s.setR r { s.rd r with
        seen := some (if (s.rd r).vis then some (s.rd r).mgen else none) })
  | freeClause (s : St R K) (k : K) (e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, (s.rd r).seen ≠ none) (he : s.erased k = some e) (hlt : e < s.start)
      (hinv : ∀ r g, (s.rd r).seen = some (some g) → ¬ s.visAt k g) :
      Step P s { s with cfreed := upd s.cfreed k true }
  | freeCode (s : St R K) (v d : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, (s.rd r).seen ≠ none) (hd : s.dead v = some d) (hlt : d < s.start)
      (hinv : ∀ r g, (s.rd r).seen = some (some g) → d < g) :
      Step P s { s with vfreed := upd s.vfreed v true }
  | gcEnd (s : St R K) (h : s.gpc = .scanning) : Step P s { s with gpc := .idle }
  /-- `processBarrier()` failed: clause GC gives up the run without scanning
  and frees nothing (revision 3b). -/
  | gcAbort (s : St R K) (h : s.gpc = .started) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St R K → St R K → Prop where
  | refl (s : St R K) : Reach P s s
  | tail {s t u : St R K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St R K) : Prop :=
  (∀ r, (s.rd r).pc = .idle ∧ (s.rd r).pgen = [] ∧ (s.rd r).ptop = [] ∧
        (s.rd r).vis = false ∧ (s.rd r).code = none ∧ (s.rd r).hold = none ∧
        (s.rd r).crossed = false ∧ (s.rd r).seen = none ∧
        (s.rd r).mgen = (s.rd r).gen ∧ (s.rd r).gen ≤ s.G) ∧
  s.gpc = .idle ∧ s.start ≤ s.G ∧ (∀ k, s.cfreed k = false) ∧
  (∀ v, s.vfreed v = false) ∧ (∀ v, s.dead v = none)

def Safe (s : St R K) : Prop :=
  ∀ r, (∀ v, (s.rd r).code = some v → s.vfreed v = false) ∧
       (∀ k, (s.rd r).hold = some k → s.cfreed k = false)

/-! ## The invariant -/

structure RInv (P : Proto) (s : St R K) (x : RS K) : Prop where
  gen_le     : x.gen ≤ s.G
  grabbed_le : ∀ v, x.pc = .grabbed v → v ≤ s.G
  last_gen   : lastD x.pgen x.mgen = x.gen
  last_top   : lastD x.ptop x.vis = x.pc.pub
  fenced     : P.fence = true → x.pc.final = true → x.pgen = [] ∧ x.ptop = []
  crossed_final : x.crossed = true → x.pc.final = true →
                (x.pgen = [] ∧ x.ptop = []) ∨ s.start ≤ x.gen
  hold       : ∀ k, x.hold = some k → x.pc = .running ∧ s.visAt k x.gen
  code       : ∀ v, x.code = some v → x.pc = .running ∧ ∀ d, s.dead v = some d → x.gen ≤ d
  freedC     : ∀ k, s.cfreed k = true → x.pc.final = true → ¬ s.visAt k x.gen
  freedV     : ∀ v, s.vfreed v = true → x.code ≠ some v
  scanned_final : s.gpc = .scanning → x.seen ≠ none → x.pc.final = true →
                s.start ≤ x.gen ∨ x.seen = some (some x.gen)
  unscanned  : s.gpc = .begun ∨ s.gpc = .started → x.seen = none
  uncrossed  : s.gpc = .begun → x.crossed = false

structure Inv (P : Proto) (s : St R K) : Prop where
  start_le    : s.start ≤ s.G
  freedC_old  : ∀ k, s.cfreed k = true → ∃ e, s.erased k = some e ∧ e < s.G
  freedV_dead : ∀ v, s.vfreed v = true → s.dead v ≠ none
  fresh       : ∀ v, s.cur ≤ v → s.dead v = none
  all_crossed : P.cross = true → s.gpc = .scanning → ∀ r, (s.rd r).crossed = true
  rd          : ∀ r, RInv P s (s.rd r)

section lemmas

@[simp] theorem setR_same (s : St R K) (r : R) (x : RS K) : (s.setR r x).rd r = x := by
  simp [St.setR, upd]

theorem setR_ne (s : St R K) {r r' : R} (x : RS K) (h : r' ≠ r) :
    (s.setR r x).rd r' = s.rd r' := by
  simp [St.setR, upd, h]

theorem visAt_congr {s t : St R K} (hb : s.born = t.born) (he : s.erased = t.erased)
    (k : K) (g : Nat) : s.visAt k g ↔ t.visAt k g := by
  simp [St.visAt, hb, he]

/-- A reader's invariant depends only on the shared fields. -/
theorem RInv.congr {P : Proto} {s t : St R K} {x : RS K} (hG : s.G = t.G)
    (hb : s.born = t.born) (he : s.erased = t.erased) (hcf : s.cfreed = t.cfreed)
    (hd : s.dead = t.dead) (hvf : s.vfreed = t.vfreed) (hg : s.gpc = t.gpc)
    (hs : s.start = t.start) (h : RInv P s x) : RInv P t x where
  gen_le := hG ▸ h.gen_le
  grabbed_le := fun v hv => hG ▸ h.grabbed_le v hv
  last_gen := h.last_gen
  last_top := h.last_top
  fenced := h.fenced
  crossed_final := fun hc hf => hs ▸ h.crossed_final hc hf
  hold := fun k hk => ⟨(h.hold k hk).1, (visAt_congr hb he k x.gen).1 (h.hold k hk).2⟩
  code := fun v hv => ⟨(h.code v hv).1, fun d hdv => (h.code v hv).2 d (hd ▸ hdv)⟩
  freedC := fun k hk hf hv =>
    h.freedC k (hcf ▸ hk) hf ((visAt_congr hb he k x.gen).2 hv)
  freedV := fun v hv => h.freedV v (hvf ▸ hv)
  scanned_final := fun hgs hn hf => hs ▸ h.scanned_final (hg ▸ hgs) hn hf
  unscanned := fun hgb => h.unscanned (hg ▸ hgb)
  uncrossed := fun hgb => h.uncrossed (hg ▸ hgb)

/-- A step of one reader: the others keep their invariant. -/
theorem inv_setR {P : Proto} {s : St R K} {r : R} {x : RS K} (h : Inv P s)
    (hx : RInv P s x) (hcr : P.cross = true → s.gpc = .scanning → x.crossed = true) :
    Inv P (s.setR r x) where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := by
    intro hp hg r'
    by_cases hr : r' = r
    · subst hr; simp only [setR_same]; exact hcr hp hg
    · rw [setR_ne s x hr]; exact h.all_crossed hp hg r'
  rd := by
    intro r'
    by_cases hr : r' = r
    · subst hr; simp only [setR_same]
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl rfl rfl hx
    · rw [setR_ne s x hr]
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl rfl rfl (h.rd r')

theorem not_visAt_of_erased_lt {s : St R K} {k : K} {e g : Nat}
    (he : s.erased k = some e) (hlt : e ≤ g) : ¬ s.visAt k g := by
  intro hv
  have hb := hv.2
  rw [he] at hb
  simp [before] at hb
  omega

end lemmas

/-! ## Preservation -/

section preservation

variable {P : Proto}

theorem idle_none {s : St R K} {x : RS K} (hx : RInv P s x) (hpc : x.pc ≠ .running) :
    x.code = none ∧ x.hold = none := by
  constructor
  · cases hc : x.code with
    | none => rfl
    | some v => exact absurd (hx.code v hc).1 hpc
  · cases hh : x.hold with
    | none => rfl
    | some k => exact absurd (hx.hold k hh).1 hpc

/-- The fields of a reader that is not final and holds nothing. -/
theorem rinv_nonfinal {s : St R K} {x y : RS K} (hx : RInv P s x)
    (hgen : y.gen ≤ s.G) (hgr : ∀ v, y.pc = .grabbed v → v ≤ s.G)
    (hlg : lastD y.pgen y.mgen = y.gen) (hlt : lastD y.ptop y.vis = y.pc.pub)
    (hnf : y.pc.final = false) (hc : y.code = none) (hh : y.hold = none)
    (hseen : y.seen = x.seen) (hcr : y.crossed = x.crossed) : RInv P s y where
  gen_le := hgen
  grabbed_le := hgr
  last_gen := hlg
  last_top := hlt
  fenced := by intro _ hf; rw [hnf] at hf; cases hf
  crossed_final := by intro _ hf; rw [hnf] at hf; cases hf
  hold := by intro k hk; rw [hh] at hk; cases hk
  code := by intro v hv; rw [hc] at hv; cases hv
  freedC := by intro k _ hf; rw [hnf] at hf; cases hf
  freedV := by intro v _; rw [hc]; simp
  scanned_final := by intro _ _ hf; rw [hnf] at hf; cases hf
  unscanned := fun hg => hseen ▸ hx.unscanned hg
  uncrossed := fun hg => hcr ▸ hx.uncrossed hg

theorem inv_call {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .idle) :
    Inv P (s.setR r { s.rd r with pc := .called }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv) hx.last_gen
    (by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this)
    (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_publish {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .called) :
    Inv P (s.setR r { s.rd r with pc := .storing,
                                   ptop := (s.rd r).ptop ++ [true] }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv) hx.last_gen
    (by simp only; rw [lastD_append]; rfl) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_grab {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .storing) :
    Inv P (s.setR r { s.rd r with pc := .grabbed s.G }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv; omega) hx.last_gen
    (by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this)
    (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_put {s : St R K} {r : R} {v : Nat} (h : Inv P s) (hrc : P.recheck = true)
    (hpc : (s.rd r).pc = .grabbed v) :
    Inv P (s.setR r { s.rd r with pc := if P.recheck then .stored else .validated,
                                   gen := v, pgen := (s.rd r).pgen ++ [v] }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  rw [hrc]
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx (hx.grabbed_le v hpc) (by intro w hw; simp at hw)
    (lastD_append _ _ _)
    (by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this)
    (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_check {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .stored)
    (hf : P.fence = true → (s.rd r).pgen = [] ∧ (s.rd r).ptop = []) :
    Inv P (s.setR r { s.rd r with
      pc := if s.G = (s.rd r).gen then .validated else .storing }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  by_cases heq : s.G = (s.rd r).gen
  · -- the barrier came before this load of the generation, which equals ours
    simp only [heq, ↓reduceIte]
    exact
      { gen_le := hx.gen_le
        grabbed_le := by intro w hw; simp at hw
        last_gen := hx.last_gen
        last_top := by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this
        fenced := fun hp _ => hf hp
        crossed_final := fun _ _ => Or.inr (by simp only; rw [← heq]; exact h.start_le)
        hold := by intro k hk; simp [hn.2] at hk
        code := by intro w hw; simp [hn.1] at hw
        freedC := by
          intro k hk _
          obtain ⟨e, he, hlt⟩ := h.freedC_old k hk
          simp only
          rw [← heq]
          exact not_visAt_of_erased_lt he (Nat.le_of_lt hlt)
        freedV := by intro w _; simp [hn.1]
        scanned_final := fun _ _ _ => Or.inl (by simp only; rw [← heq]; exact h.start_le)
        unscanned := hx.unscanned
        uncrossed := hx.uncrossed }
  · simp only [heq, ↓reduceIte]
    exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_gen
      (by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this)
      (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_light {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .stored) :
    Inv P (s.setR r { s.rd r with pc := .storing }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_gen
    (by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this)
    (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_dispatch {s : St R K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .validated) :
    Inv P (s.setR r { s.rd r with pc := .running,
                                   code := if (s.rd r).code = none then some s.cur
                                           else (s.rd r).code }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  have hcode : (if (s.rd r).code = none then some s.cur else (s.rd r).code) = some s.cur := by
    simp [hn.1]
  rw [hcode]
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
  exact
    { gen_le := hx.gen_le
      grabbed_le := by intro w hw; simp at hw
      last_gen := hx.last_gen
      last_top := by have := hx.last_top; rw [hpc] at this; simpa [Pc.pub] using this
      fenced := fun hp _ => hx.fenced hp hfin
      crossed_final := fun hc _ => hx.crossed_final hc hfin
      hold := by intro k hk; simp [hn.2] at hk
      code := by
        intro w hw
        simp at hw
        subst hw
        refine ⟨rfl, ?_⟩
        intro d hd
        rw [h.fresh s.cur (Nat.le_refl _)] at hd
        cases hd
      freedC := fun k hk _ => hx.freedC k hk hfin
      freedV := by
        intro w hw hcw
        simp at hcw
        subst hcw
        exact h.freedV_dead s.cur hw (h.fresh s.cur (Nat.le_refl _))
      scanned_final := fun hg hs _ => hx.scanned_final hg hs hfin
      unscanned := hx.unscanned
      uncrossed := hx.uncrossed }

theorem inv_select {s : St R K} {r : R} {k : K} (h : Inv P s)
    (hpc : (s.rd r).pc = .running) (hk : s.visAt k (s.rd r).gen) :
    Inv P (s.setR r { s.rd r with hold := some k }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_gen := hx.last_gen
      last_top := hx.last_top, fenced := hx.fenced, crossed_final := hx.crossed_final
      hold := by intro k' hk'; simp at hk'; subst hk'; exact ⟨hpc, hk⟩
      code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_exit {s : St R K} {r : R} (h : Inv P s) :
    Inv P (s.setR r { s.rd r with pc := .idle, code := none, hold := none,
                                   ptop := (s.rd r).ptop ++ [false] }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_gen
    (by simp only; rw [lastD_append]; rfl) (by simp [Pc.final]) rfl rfl rfl rfl

theorem inv_drainGen {s : St R K} {r : R} {v : Nat} {rest : List Nat} (h : Inv P s)
    (hq : (s.rd r).pgen = v :: rest) :
    Inv P (s.setR r { s.rd r with mgen := v, pgen := rest }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
      last_gen := by simp only; rw [← hx.last_gen, hq]; rfl
      last_top := hx.last_top
      fenced := by
        intro hp hst
        have := (hx.fenced hp hst).1
        rw [hq] at this; cases this
      crossed_final := by
        intro hc hfin
        rcases hx.crossed_final hc hfin with ⟨hp, _⟩ | hle
        · rw [hq] at hp; cases hp
        · exact Or.inr hle
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_drainTop {s : St R K} {r : R} {b : Bool} {rest : List Bool} (h : Inv P s)
    (hq : (s.rd r).ptop = b :: rest) :
    Inv P (s.setR r { s.rd r with vis := b, ptop := rest }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
      last_gen := hx.last_gen
      last_top := by simp only; rw [← hx.last_top, hq]; rfl
      fenced := by
        intro hp hst
        have := (hx.fenced hp hst).2
        rw [hq] at this; cases this
      crossed_final := by
        intro hc hfin
        rcases hx.crossed_final hc hfin with ⟨_, hp⟩ | hle
        · rw [hq] at hp; cases hp
        · exact Or.inr hle
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_cross {s : St R K} {r : R} (h : Inv P s) (hg : s.gpc = .started) :
    Inv P (s.setR r { s.rd r with mgen := lastD (s.rd r).pgen (s.rd r).mgen,
                                   vis := lastD (s.rd r).ptop (s.rd r).vis,
                                   pgen := [], ptop := [], crossed := true }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun _ hg' => absurd (hg.symm.trans hg') (by decide))
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
      last_gen := by simp only [lastD]; exact hx.last_gen
      last_top := by simp only [lastD]; exact hx.last_top
      fenced := fun _ _ => ⟨rfl, rfl⟩
      crossed_final := fun _ _ => Or.inl ⟨rfl, rfl⟩
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := by intro hg'; rw [hg] at hg'; cases hg'
      unscanned := hx.unscanned
      uncrossed := by intro hb; rw [hg] at hb; cases hb }

/-- What the scan records of a final frame: with a fence or after crossing,
its buffer is empty, so lTop is above it and memory holds its generation;
or its generation is not older than the start. -/
theorem scan_sees {s : St R K} {x : RS K} (hfc : P.fence = true ∨ P.cross = true)
    (hx : RInv P s x) (hcr : P.cross = true → x.crossed = true)
    (hfin : x.pc.final = true) :
    s.start ≤ x.gen ∨ (x.vis = true ∧ x.mgen = x.gen) := by
  have hempty : (x.pgen = [] ∧ x.ptop = []) ∨ s.start ≤ x.gen := by
    rcases hfc with hf | hc
    · exact Or.inl (hx.fenced hf hfin)
    · exact hx.crossed_final (hcr hc) hfin
  rcases hempty with ⟨hp, ht⟩ | hle
  · right
    have hpub : x.pc.pub = true := by
      cases hpc : x.pc <;> simp [hpc, Pc.final, Pc.pub] at hfin ⊢
    have hv := hx.last_top
    have hg := hx.last_gen
    rw [ht] at hv; rw [hp] at hg
    simp only [lastD] at hv hg
    exact ⟨hv.trans hpub, hg⟩
  · exact Or.inl hle

theorem inv_scan {s : St R K} {r : R} (h : Inv P s) (hfc : P.fence = true ∨ P.cross = true)
    (hg : s.gpc = .scanning) :
    Inv P (s.setR r { s.rd r with
      seen := some (if (s.rd r).vis then some (s.rd r).mgen else none) }) := by
  have hx := h.rd r
  have hcr : P.cross = true → (s.rd r).crossed = true := fun hp => h.all_crossed hp hg r
  refine inv_setR h ?_ (fun hp hg' => ?_)
  rotate_left
  · exact h.all_crossed hp hg' r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_gen := hx.last_gen
      last_top := hx.last_top, fenced := hx.fenced, crossed_final := hx.crossed_final
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := by
        intro _ _ hfin
        rcases scan_sees hfc hx hcr hfin with hle | ⟨hv, hm⟩
        · exact Or.inl hle
        · right; simp [hv, hm]
      unscanned := by intro hb; rw [hg] at hb; rcases hb with hb | hb <;> cases hb
      uncrossed := hx.uncrossed }

theorem inv_bump {s : St R K} (h : Inv P s) : Inv P { s with G := s.G + 1 } where
  start_le := Nat.le_succ_of_le h.start_le
  freedC_old := fun k hk => by
    obtain ⟨e, he, hlt⟩ := h.freedC_old k hk
    exact ⟨e, he, by show e < s.G + 1; omega⟩
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := by show (s.rd r).gen ≤ s.G + 1; have := hx.gen_le; omega
        grabbed_le := fun v hv => by
          show v ≤ s.G + 1; have := hx.grabbed_le v hv; omega
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_erase {s : St R K} {k0 : K} (h : Inv P s) (hk0 : s.erased k0 = none) :
    Inv P { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } := by
  have fne : ∀ k, s.cfreed k = true → k ≠ k0 := by
    intro k hk heq
    obtain ⟨e, he, _⟩ := h.freedC_old k hk
    rw [heq, hk0] at he; cases he
  have vis_ne : ∀ k g, k ≠ k0 →
      (St.visAt { s with G := s.G + 1, erased := upd s.erased k0 (some (s.G + 1)) } k g ↔
        s.visAt k g) := by
    intro k g hne; simp [St.visAt, upd, hne]
  refine
    { start_le := Nat.le_succ_of_le h.start_le
      freedC_old := ?_
      freedV_dead := h.freedV_dead
      fresh := h.fresh
      all_crossed := h.all_crossed
      rd := ?_ }
  · intro k hk
    obtain ⟨e, he, hlt⟩ := h.freedC_old k hk
    exact ⟨e, by simp [upd, fne k hk, he], by show e < s.G + 1; omega⟩
  · intro r
    have hx := h.rd r
    exact
      { gen_le := by show (s.rd r).gen ≤ s.G + 1; have := hx.gen_le; omega
        grabbed_le := fun v hv => by
          show v ≤ s.G + 1; have := hx.grabbed_le v hv; omega
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := by
          intro k hk
          obtain ⟨hpc, hv⟩ := hx.hold k hk
          refine ⟨hpc, ?_⟩
          by_cases hkk : k = k0
          · subst hkk
            have := hx.gen_le
            simp only [St.visAt, upd] at hv ⊢
            exact ⟨hv.1, by simp [before]; omega⟩
          · exact (vis_ne k _ hkk).2 hv
        code := hx.code
        freedC := fun k hk hf hv => hx.freedC k hk hf ((vis_ne k _ (fne k hk)).1 hv)
        freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_replace {s : St R K} (h : Inv P s) :
    Inv P { s with dead := upd s.dead s.cur (some s.G), cur := s.cur + 1 } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := by
    intro v hv
    by_cases hvc : v = s.cur
    · subst hvc; simp [upd]
    · simp [upd, hvc]; exact h.freedV_dead v hv
  fresh := by
    intro v hv
    have hv' : s.cur + 1 ≤ v := hv
    have hne : v ≠ s.cur := by omega
    simp [upd, hne]
    exact h.fresh v (by omega)
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold
        code := by
          intro v hv
          obtain ⟨hpc, hd⟩ := hx.code v hv
          refine ⟨hpc, ?_⟩
          intro d hdv
          by_cases hvc : v = s.cur
          · subst hvc
            simp [upd] at hdv
            subst hdv
            exact hx.gen_le
          · simp [upd, hvc] at hdv
            exact hd d hdv
        freedC := hx.freedC, freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_gcBegin {s : St R K} (h : Inv P s) :
    Inv P { s with gpc := .begun,
                   rd := fun r => { s.rd r with crossed := false, seen := none } } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := by intro _ hg; cases hg
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := by intro hc; cases hc
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg; cases hg
        unscanned := fun _ => rfl
        uncrossed := fun _ => rfl }

theorem inv_gcStart {s : St R K} (h : Inv P s) (hg : s.gpc = .begun) :
    Inv P { s with gpc := .started, start := s.G } where
  start_le := Nat.le_refl _
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := by intro _ hg'; cases hg'
  rd := fun r => by
    have hx := h.rd r
    have hnc := hx.uncrossed hg
    have hns := hx.unscanned (Or.inl hg)
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := by intro hc; rw [hnc] at hc; cases hc
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg'; cases hg'
        unscanned := fun _ => hns
        uncrossed := by intro hb; cases hb }

theorem inv_toScan {s : St R K} (h : Inv P s) (hg : s.gpc = .started)
    (hc : P.cross = true → ∀ r, (s.rd r).crossed = true) :
    Inv P { s with gpc := .scanning } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := fun hp _ => hc hp
  rd := fun r => by
    have hx := h.rd r
    have hns := hx.unscanned (Or.inr hg)
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro _ hs; exact absurd hns hs
        unscanned := by intro hb; rcases hb with hb | hb <;> cases hb
        uncrossed := by intro hb; cases hb }

theorem inv_freeClause {s : St R K} {k0 : K} {e : Nat} (h : Inv P s)
    (hg : s.gpc = .scanning) (hall : ∀ r, (s.rd r).seen ≠ none)
    (he : s.erased k0 = some e) (hlt : e < s.start)
    (hinv : ∀ r g, (s.rd r).seen = some (some g) → ¬ s.visAt k0 g) :
    Inv P { s with cfreed := upd s.cfreed k0 true } where
  start_le := h.start_le
  freedC_old := by
    intro k hk
    by_cases hkk : k = k0
    · subst hkk; exact ⟨e, he, by show e < s.G; have := h.start_le; omega⟩
    · exact h.freedC_old k (by simpa [upd, hkk] using hk)
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code
        freedC := by
          intro k hk hfin
          by_cases hkk : k = k0
          · subst hkk
            rcases hx.scanned_final hg (hall r) hfin with hle | hs
            · exact not_visAt_of_erased_lt he (by show e ≤ (s.rd r).gen; omega)
            · exact hinv r _ hs
          · exact hx.freedC k (by simpa [upd, hkk] using hk) hfin
        freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_freeCode {s : St R K} {v0 d : Nat} (h : Inv P s)
    (hg : s.gpc = .scanning) (hall : ∀ r, (s.rd r).seen ≠ none)
    (hd : s.dead v0 = some d) (hlt : d < s.start)
    (hinv : ∀ r g, (s.rd r).seen = some (some g) → d < g) :
    Inv P { s with vfreed := upd s.vfreed v0 true } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := by
    intro v hv
    by_cases hvv : v = v0
    · subst hvv; rw [hd]; simp
    · exact h.freedV_dead v (by simpa [upd, hvv] using hv)
  fresh := h.fresh
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC
        freedV := by
          intro v hv hcv
          by_cases hvv : v = v0
          · subst hvv
            obtain ⟨hpc, hle⟩ := hx.code v hcv
            have hgd := hle d hd
            have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
            rcases hx.scanned_final hg (hall r) hfin with hst | hs
            · omega
            · have := hinv r _ hs; omega
          · exact hx.freedV v (by simpa [upd, hvv] using hv) hcv
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_gcEnd {s : St R K} (h : Inv P s) : Inv P { s with gpc := .idle } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := by intro _ hg; cases hg
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_gen := hx.last_gen, last_top := hx.last_top, fenced := hx.fenced
        crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg; cases hg
        unscanned := by intro hb; rcases hb with hb | hb <;> cases hb
        uncrossed := by intro hb; cases hb }

theorem step_inv {s t : St R K} (he : P.early = false) (hrc : P.recheck = true)
    (hfc : P.fence = true ∨ P.cross = true) (h : Inv P s) (hst : Step P s t) : Inv P t := by
  cases hst with
  | bump => exact inv_bump h
  | erase k hk => exact inv_erase h hk
  | replace => exact inv_replace h
  | call r hpc => exact inv_call h hpc
  | early r hp _ _ => rw [he] at hp; cases hp
  | publish r hpc => exact inv_publish h hpc
  | grab r hpc => exact inv_grab h hpc
  | put r v hpc => exact inv_put h hrc hpc
  | check r hpc hf => exact inv_check h hpc hf
  | light r _ hpc => exact inv_light h hpc
  | dispatch r hpc => exact inv_dispatch h hpc
  | select r k hpc hk => exact inv_select h hpc hk
  | exit r _ => exact inv_exit h
  | drainGen r v rest hq => exact inv_drainGen h hq
  | drainTop r b rest hq => exact inv_drainTop h hq
  | gcBegin => exact inv_gcBegin h
  | gcStart hg => exact inv_gcStart h hg
  | cross r _ hg _ => exact inv_cross h hg
  | toScan hg hc => exact inv_toScan h hg hc
  | scan r hg _ => exact inv_scan h hfc hg
  | freeClause k e hg hall hek hlt hinv => exact inv_freeClause h hg hall hek hlt hinv
  | freeCode v d hg hall hd hlt hinv => exact inv_freeCode h hg hall hd hlt hinv
  | gcEnd => exact inv_gcEnd h
  | gcAbort => exact inv_gcEnd h

end preservation

theorem init_inv {P : Proto} {s : St R K} (h : Init s) : Inv P s where
  start_le := h.2.2.1
  freedC_old := by intro k hk; rw [h.2.2.2.1 k] at hk; cases hk
  freedV_dead := by intro v hv; rw [h.2.2.2.2.1 v] at hv; cases hv
  fresh := fun v _ => h.2.2.2.2.2 v
  all_crossed := by intro _ hg; rw [h.2.1] at hg; cases hg
  rd := fun r => by
    obtain ⟨hpc, hpg, hpt, hv, hc, hh, hcr, hs, hm, hg⟩ := h.1 r
    exact
      { gen_le := hg
        grabbed_le := by intro v hv'; rw [hpc] at hv'; cases hv'
        last_gen := by rw [hpg]; exact hm
        last_top := by rw [hpt, hpc]; simpa [lastD, Pc.pub] using hv
        fenced := by intro _ hst; rw [hpc] at hst; simp [Pc.final] at hst
        crossed_final := by intro hc'; rw [hcr] at hc'; cases hc'
        hold := by intro k hk; rw [hh] at hk; cases hk
        code := by intro v hv'; rw [hc] at hv'; cases hv'
        freedC := by intro k hk; rw [h.2.2.2.1 k] at hk; cases hk
        freedV := by intro v hv'; rw [h.2.2.2.2.1 v] at hv'; cases hv'
        scanned_final := by intro hg'; rw [h.2.1] at hg'; cases hg'
        unscanned := fun _ => hs
        uncrossed := fun _ => hcr }

theorem Inv.safe {P : Proto} {s : St R K} (h : Inv P s) : Safe s := by
  intro r
  have hx := h.rd r
  refine ⟨?_, ?_⟩
  · intro v hv
    cases hf : s.vfreed v with
    | false => rfl
    | true => exact absurd hv (hx.freedV v hf)
  · intro k hk
    obtain ⟨hpc, hvis⟩ := hx.hold k hk
    have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
    cases hf : s.cfreed k with
    | false => rfl
    | true => exact absurd hvis (hx.freedC k hf hfin)

/-- Publication before setGenerationFrame(), whose loop re-reads after a
barrier, and DEF->codes read after it, with a fence in the reader or a
barrier that clause GC makes every thread cross: no frame ever holds a
reclaimed clause or a freed supervisor. -/
theorem safe (P : Proto) (he : P.early = false) (hrc : P.recheck = true)
    (hfc : P.fence = true ∨ P.cross = true) {s0 s : St R K} (h0 : Init s0)
    (hr : Reach P s0 s) : Safe s := by
  have : Inv P s := by
    induction hr with
    | refl => exact init_inv h0
    | tail _ hst ih => exact step_inv he hrc hfc ih hst
  exact this.safe

theorem symmetric_safe {s0 s : St R K} (h0 : Init s0) (hr : Reach symmetric s0 s) :
    Safe s := safe symmetric rfl rfl (Or.inl rfl) h0 hr

theorem asymmetric_safe {s0 s : St R K} (h0 : Init s0) (hr : Reach asymmetric s0 s) :
    Safe s := safe asymmetric rfl rfl (Or.inr rfl) h0 hr

theorem fallback_safe {s0 s : St R K} (h0 : Init s0) (hr : Reach fallback s0 s) :
    Safe s := safe fallback rfl rfl (Or.inl rfl) h0 hr

theorem asymmetricLight_safe {s0 s : St R K} (h0 : Init s0)
    (hr : Reach asymmetricLight s0 s) : Safe s :=
  safe asymmetricLight rfl rfl (Or.inr rfl) h0 hr

/-! ## Counterexamples (one reader, one clause) -/

section counterexamples

def r0 : RS Unit := ⟨.idle, 0, [], [], 0, false, none, none, false, none⟩

/-- `c0 b`: generation 0, one clause born at `b`, supervisor version 0. -/
def c0 (b : Nat) : St Unit Unit :=
  ⟨0, fun _ => b, fun _ => none, fun _ => false, 0, fun _ => none, fun _ => false,
   fun _ => r0, .idle, 0⟩

theorem c0_init (b : Nat) : Init (c0 b) := by
  refine ⟨fun r => ?_, rfl, Nat.le_refl _, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, Nat.le_refl _⟩

/-- DEF->codes read before validating (validation in the supervisor, as for
S_TRUSTME): reconsult replaces the supervisor, clause GC does not see the
frame and frees the old one, which the frame then runs. -/
theorem early_codes_unsafe : ∃ s, Reach earlyCodes (c0 0) s ∧ ¬ Safe s := by
  let s1 := (c0 0).setR () { (c0 0).rd () with pc := .called }
  let s2 := s1.setR () { s1.rd () with code := some s1.cur }
  let s3 : St Unit Unit := { s2 with dead := upd s2.dead s2.cur (some s2.G), cur := s2.cur + 1 }
  let s4 : St Unit Unit := { s3 with G := s3.G + 1 }
  let s5 : St Unit Unit := { s4 with gpc := .begun, rd := fun r => { s4.rd r with crossed := false, seen := none } }
  let s6 : St Unit Unit := { s5 with gpc := .started, start := s5.G }
  let s7 : St Unit Unit := { s6 with gpc := .scanning }
  let s8 := s7.setR () { s7.rd () with seen := some (if (s7.rd ()).vis then some (s7.rd ()).mgen else none) }
  let s9 : St Unit Unit := { s8 with vfreed := upd s8.vfreed 0 true }
  refine ⟨s9, ?_, ?_⟩
  · refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.tail (Reach.refl (c0 0))
      (Step.call (c0 0) () (by decide)))
      (Step.early s1 () (by decide) (by decide) (by decide)))
      (Step.replace s2))
      (Step.bump s3))
      (Step.gcBegin s4 (by decide)))
      (Step.gcStart s5 (by decide)))
      (Step.toScan s6 (by decide) (by intro h; cases h)))
      (Step.scan s7 () (by decide) (by decide)))
      (Step.freeCode s8 0 0 (by decide) (by intro r; cases r; decide) (by decide)
        (by decide) ?_)
    intro r g hs; cases r
    have : (s8.rd ()).seen = some none := by decide
    rw [this] at hs; cases hs
  · intro hs
    have := (hs ()).1 0 (by decide)
    simp [s9, upd] at this

/-- The loaded generation stored without loading again after the barrier:
clause GC can scan before that store drains and find the previous value of
the field, while the frame selects in the new generation a clause born
after the previous one. -/
theorem no_recheck_unsafe : ∃ s, Reach noRecheck (c0 1) s ∧ ¬ Safe s := by
  let s1 := (c0 1).setR () { (c0 1).rd () with pc := .called }
  let s2 := s1.setR () { s1.rd () with pc := .storing, ptop := (s1.rd ()).ptop ++ [true] }
  let s3 := s2.setR () { s2.rd () with vis := true, ptop := [] }
  let s4 : St Unit Unit := { s3 with G := s3.G + 1 }
  let s5 := s4.setR () { s4.rd () with pc := .grabbed s4.G }
  let s6 := s5.setR () { s5.rd () with pc := if noRecheck.recheck then .stored else .validated, gen := 1, pgen := (s5.rd ()).pgen ++ [1] }
  let s7 := s6.setR () { s6.rd () with pc := .running, code := if (s6.rd ()).code = none then some s6.cur else (s6.rd ()).code }
  let s8 := s7.setR () { s7.rd () with hold := some () }
  let s9 : St Unit Unit := { s8 with G := s8.G + 1, erased := upd s8.erased () (some (s8.G + 1)) }
  let s10 : St Unit Unit := { s9 with G := s9.G + 1 }
  let s11 : St Unit Unit := { s10 with gpc := .begun, rd := fun r => { s10.rd r with crossed := false, seen := none } }
  let s12 : St Unit Unit := { s11 with gpc := .started, start := s11.G }
  let s13 : St Unit Unit := { s12 with gpc := .scanning }
  let s14 := s13.setR () { s13.rd () with seen := some (if (s13.rd ()).vis then some (s13.rd ()).mgen else none) }
  let s15 : St Unit Unit := { s14 with cfreed := upd s14.cfreed () true }
  refine ⟨s15, ?_, ?_⟩
  · refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.tail (Reach.refl (c0 1))
      (Step.call (c0 1) () (by decide)))
      (Step.publish s1 () (by decide)))
      (Step.drainTop s2 () true [] (by decide)))
      (Step.bump s3))
      (Step.grab s4 () (by decide)))
      (Step.put s5 () 1 (by decide)))
      (Step.dispatch s6 () (by decide)))
      (Step.select s7 () () (by decide) (by decide)))
      (Step.erase s8 () (by decide)))
      (Step.bump s9))
      (Step.gcBegin s10 (by decide)))
      (Step.gcStart s11 (by decide)))
      (Step.toScan s12 (by decide) (by intro h; cases h)))
      (Step.scan s13 () (by decide) (by decide)))
      (Step.freeClause s14 () 2 (by decide) (by intro r; cases r; decide) (by decide)
        (by decide) ?_)
    intro r g hs; cases r
    have : (s14.rd ()).seen = some (some 0) := by decide
    rw [this] at hs
    cases hs
    decide
  · intro hs
    have := (hs ()).2 () (by decide)
    simp [s15, upd] at this

/-- No fence and no crossing: the store that moves lTop is still buffered
when clause GC scans. -/
theorem neither_unsafe : ∃ s, Reach neither (c0 0) s ∧ ¬ Safe s := by
  let s1 := (c0 0).setR () { (c0 0).rd () with pc := .called }
  let s2 := s1.setR () { s1.rd () with pc := .storing, ptop := (s1.rd ()).ptop ++ [true] }
  let s3 := s2.setR () { s2.rd () with pc := .grabbed s2.G }
  let s4 := s3.setR () { s3.rd () with pc := if neither.recheck then .stored else .validated, gen := 0, pgen := (s3.rd ()).pgen ++ [0] }
  let s5 := s4.setR () { s4.rd () with pc := if s4.G = (s4.rd ()).gen then .validated else .storing }
  let s6 := s5.setR () { s5.rd () with pc := .running, code := if (s5.rd ()).code = none then some s5.cur else (s5.rd ()).code }
  let s7 := s6.setR () { s6.rd () with hold := some () }
  let s8 : St Unit Unit := { s7 with G := s7.G + 1, erased := upd s7.erased () (some (s7.G + 1)) }
  let s9 : St Unit Unit := { s8 with G := s8.G + 1 }
  let s10 : St Unit Unit := { s9 with gpc := .begun, rd := fun r => { s9.rd r with crossed := false, seen := none } }
  let s11 : St Unit Unit := { s10 with gpc := .started, start := s10.G }
  let s12 : St Unit Unit := { s11 with gpc := .scanning }
  let s13 := s12.setR () { s12.rd () with seen := some (if (s12.rd ()).vis then some (s12.rd ()).mgen else none) }
  let s14 : St Unit Unit := { s13 with cfreed := upd s13.cfreed () true }
  refine ⟨s14, ?_, ?_⟩
  · refine Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail (Reach.tail
      (Reach.tail (Reach.tail (Reach.refl (c0 0))
      (Step.call (c0 0) () (by decide)))
      (Step.publish s1 () (by decide)))
      (Step.grab s2 () (by decide)))
      (Step.put s3 () 0 (by decide)))
      (Step.check s4 () (by decide) (by intro h; cases h)))
      (Step.dispatch s5 () (by decide)))
      (Step.select s6 () () (by decide) (by decide)))
      (Step.erase s7 () (by decide)))
      (Step.bump s8))
      (Step.gcBegin s9 (by decide)))
      (Step.gcStart s10 (by decide)))
      (Step.toScan s11 (by decide) (by intro h; cases h)))
      (Step.scan s12 () (by decide) (by decide)))
      (Step.freeClause s13 () 1 (by decide) (by intro r; cases r; decide) (by decide)
        (by decide) ?_)
    intro r g hs; cases r
    have : (s13.rd ()).seen = some none := by decide
    rw [this] at hs; cases hs
  · intro hs
    have := (hs ()).2 () (by decide)
    simp [s14, upd] at this

end counterexamples

end Mettapedia.Languages.Prolog.SWI.CallPort
