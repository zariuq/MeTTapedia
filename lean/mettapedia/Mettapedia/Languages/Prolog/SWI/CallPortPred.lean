/-
The call port protocol with predicates and last calls.

As Mettapedia.Languages.Prolog.SWI.CallPort, but each clause and each supervisor version belongs to a
predicate, the frame's predicate field is a third store, and clause GC keys
what it registers by that field: a generation found in a frame protects the
clauses and the supervisor versions of the frame's predicate only
(markPredicatesInEnvironments() adds it to the DirtyDefInfo of
fr->predicate).  A last call (I_DEPART) reuses a frame that clause GC can
already see: it stores a new predicate and then passes the call port again.

`safe`: with a fence or crossings, re-validation and DEF->codes read after
validation, no frame ever holds a reclaimed clause or a freed supervisor,
also when a visible frame changes its predicate, and with or without the
`light` rounds of revision 3 (the call port's loop with a compiler barrier
only, before the loop with the full barrier when there is no process-wide
barrier: `fallback_safe`), and with clause GC runs that give up without
scanning (`gcAbort`, revision 3b).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Mettapedia.Languages.Prolog.SWI.CallPortPred

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

def before (g : Nat) : Option Nat → Bool
  | none => true
  | some e => decide (g < e)

def lastD {α : Type} : List α → α → α
  | [], d => d
  | a :: l, _ => lastD l a

theorem lastD_append {α : Type} (l : List α) (a d : α) : lastD (l ++ [a]) d = a := by
  induction l generalizing d with
  | nil => rfl
  | cons b l ih => exact ih b

inductive Pc where
  | idle
  | called
  | storing
  | grabbed (v : Nat)
  | stored
  | validated
  | running
deriving DecidableEq

namespace Pc
/-- lTop was moved above the frame by this call -/
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

structure RS (D K : Type) where
  pc      : Pc
  /-- its predicate and generation, as the thread sees them -/
  pred    : D
  gen     : Nat
  /-- pending stores, oldest first: predicate field, generation field, lTop -/
  ppred   : List D
  pgen    : List Nat
  ptop    : List Bool
  /-- the fields in shared memory -/
  mpred   : D
  mgen    : Nat
  vis     : Bool
  /-- the version of the supervisor of `pred` it runs -/
  code    : Option Nat
  hold    : Option K
  crossed : Bool
  /-- what the running clause GC recorded: nothing, or predicate and generation -/
  seen    : Option (Option (D × Nat))

structure St (R D K : Type) where
  G      : Nat
  owner  : K → D
  born   : K → Nat
  erased : K → Option Nat
  cfreed : K → Bool
  cur    : D → Nat
  dead   : D → Nat → Option Nat
  vfreed : D → Nat → Bool
  rd     : R → RS D K
  gpc    : GPc
  start  : Nat

structure Proto where
  fence   : Bool
  cross   : Bool
  early   : Bool
  recheck : Bool
  light   : Bool

def symmetric : Proto := ⟨true, false, false, true, false⟩
def asymmetric : Proto := ⟨false, true, false, true, false⟩
def fallback : Proto := ⟨true, false, false, true, true⟩
def asymmetricLight : Proto := ⟨false, true, false, true, true⟩

variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

def St.visAt (s : St R D K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ before g (s.erased k) = true

def St.setR (s : St R D K) (r : R) (x : RS D K) : St R D K := { s with rd := upd s.rd r x }

def empties (x : RS D K) : Prop := x.ppred = [] ∧ x.pgen = [] ∧ x.ptop = []

inductive Step (P : Proto) : St R D K → St R D K → Prop where
  | bump (s : St R D K) : Step P s { s with G := s.G + 1 }
  | erase (s : St R D K) (k : K) (h : s.erased k = none) :
      Step P s { s with G := s.G + 1, erased := upd s.erased k (some (s.G + 1)) }
  | replace (s : St R D K) (d : D) :
      Step P s { s with dead := upd s.dead d (upd (s.dead d) (s.cur d) (some s.G)),
                        cur := upd s.cur d (s.cur d + 1) }
  /-- normal_call: a new frame for predicate `p`, at lTop. -/
  | call (s : St R D K) (r : R) (p : D) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { s.rd r with pc := .called, pred := p,
                                        ppred := (s.rd r).ppred ++ [p] })
  /-- I_DEPART: the running frame, which clause GC can see, is reused for
      predicate `p`. -/
  | depart (s : St R D K) (r : R) (p : D) (h : (s.rd r).pc = .running) :
      Step P s (s.setR r { s.rd r with pc := .called, pred := p, code := none,
                                        hold := none, ppred := (s.rd r).ppred ++ [p] })
  | early (s : St R D K) (r : R) (hp : P.early = true) (h : (s.rd r).pc = .called)
      (hc : (s.rd r).code = none) :
      Step P s (s.setR r { s.rd r with code := some (s.cur (s.rd r).pred) })
  | publish (s : St R D K) (r : R) (h : (s.rd r).pc = .called) :
      Step P s (s.setR r { s.rd r with pc := .storing,
                                        ptop := (s.rd r).ptop ++ [true] })
  | grab (s : St R D K) (r : R) (h : (s.rd r).pc = .storing) :
      Step P s (s.setR r { s.rd r with pc := .grabbed s.G })
  | put (s : St R D K) (r : R) (v : Nat) (h : (s.rd r).pc = .grabbed v) :
      Step P s (s.setR r { s.rd r with pc := if P.recheck then .stored else .validated,
                                        gen := v, pgen := (s.rd r).pgen ++ [v] })
  | check (s : St R D K) (r : R) (h : (s.rd r).pc = .stored)
      (hf : P.fence = true → empties (s.rd r)) :
      Step P s (s.setR r { s.rd r with
        pc := if s.G = (s.rd r).gen then .validated else .storing })
  /-- The loop with a compiler barrier only; the full one validates. -/
  | light (s : St R D K) (r : R) (hp : P.light = true) (h : (s.rd r).pc = .stored) :
      Step P s (s.setR r { s.rd r with pc := .storing })
  | dispatch (s : St R D K) (r : R) (h : (s.rd r).pc = .validated) :
      Step P s (s.setR r { s.rd r with pc := .running,
                                        code := if (s.rd r).code = none
                                                then some (s.cur (s.rd r).pred)
                                                else (s.rd r).code })
  | select (s : St R D K) (r : R) (k : K) (h : (s.rd r).pc = .running)
      (ho : s.owner k = (s.rd r).pred) (hk : s.visAt k (s.rd r).gen) :
      Step P s (s.setR r { s.rd r with hold := some k })
  | exit (s : St R D K) (r : R) (h : (s.rd r).pc = .running) :
      Step P s (s.setR r { s.rd r with pc := .idle, code := none, hold := none,
                                        ptop := (s.rd r).ptop ++ [false] })
  | drainPred (s : St R D K) (r : R) (p : D) (rest : List D)
      (h : (s.rd r).ppred = p :: rest) :
      Step P s (s.setR r { s.rd r with mpred := p, ppred := rest })
  | drainGen (s : St R D K) (r : R) (v : Nat) (rest : List Nat)
      (h : (s.rd r).pgen = v :: rest) :
      Step P s (s.setR r { s.rd r with mgen := v, pgen := rest })
  | drainTop (s : St R D K) (r : R) (b : Bool) (rest : List Bool)
      (h : (s.rd r).ptop = b :: rest) :
      Step P s (s.setR r { s.rd r with vis := b, ptop := rest })
  | gcBegin (s : St R D K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .begun,
                        rd := fun r => { s.rd r with crossed := false, seen := none } }
  | gcStart (s : St R D K) (h : s.gpc = .begun) :
      Step P s { s with gpc := .started, start := s.G }
  | cross (s : St R D K) (r : R) (hp : P.cross = true) (h : s.gpc = .started)
      (hc : (s.rd r).crossed = false) :
      Step P s (s.setR r { s.rd r with mpred := lastD (s.rd r).ppred (s.rd r).mpred,
                                        mgen := lastD (s.rd r).pgen (s.rd r).mgen,
                                        vis := lastD (s.rd r).ptop (s.rd r).vis,
                                        ppred := [], pgen := [], ptop := [],
                                        crossed := true })
  | toScan (s : St R D K) (h : s.gpc = .started)
      (hc : P.cross = true → ∀ r, (s.rd r).crossed = true) :
      Step P s { s with gpc := .scanning }
  | scan (s : St R D K) (r : R) (h : s.gpc = .scanning) (hn : (s.rd r).seen = none) :
      Step P s (s.setR r { s.rd r with
        seen := some (if (s.rd r).vis then some ((s.rd r).mpred, (s.rd r).mgen) else none) })
  | freeClause (s : St R D K) (k : K) (e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, (s.rd r).seen ≠ none) (he : s.erased k = some e) (hlt : e < s.start)
      (hinv : ∀ r d g, (s.rd r).seen = some (some (d, g)) → d = s.owner k →
                ¬ s.visAt k g) :
      Step P s { s with cfreed := upd s.cfreed k true }
  | freeCode (s : St R D K) (d : D) (v e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, (s.rd r).seen ≠ none) (hd : s.dead d v = some e) (hlt : e < s.start)
      (hinv : ∀ r d' g, (s.rd r).seen = some (some (d', g)) → d' = d → e < g) :
      Step P s { s with vfreed := upd s.vfreed d (upd (s.vfreed d) v true) }
  | gcEnd (s : St R D K) (h : s.gpc = .scanning) : Step P s { s with gpc := .idle }
  /-- `processBarrier()` failed: clause GC gives up the run without scanning
  and frees nothing (revision 3b). -/
  | gcAbort (s : St R D K) (h : s.gpc = .started) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St R D K → St R D K → Prop where
  | refl (s : St R D K) : Reach P s s
  | tail {s t u : St R D K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St R D K) : Prop :=
  (∀ r, (s.rd r).pc = .idle ∧ empties (s.rd r) ∧ (s.rd r).vis = false ∧
        (s.rd r).code = none ∧ (s.rd r).hold = none ∧ (s.rd r).crossed = false ∧
        (s.rd r).seen = none ∧ (s.rd r).mgen = (s.rd r).gen ∧
        (s.rd r).mpred = (s.rd r).pred ∧ (s.rd r).gen ≤ s.G) ∧
  s.gpc = .idle ∧ s.start ≤ s.G ∧ (∀ k, s.cfreed k = false) ∧
  (∀ d v, s.vfreed d v = false) ∧ (∀ d v, s.dead d v = none)

def Safe (s : St R D K) : Prop :=
  ∀ r, (∀ v, (s.rd r).code = some v → s.vfreed (s.rd r).pred v = false) ∧
       (∀ k, (s.rd r).hold = some k → s.cfreed k = false)

/-! ## The invariant -/

structure RInv (P : Proto) (s : St R D K) (x : RS D K) : Prop where
  gen_le     : x.gen ≤ s.G
  grabbed_le : ∀ v, x.pc = .grabbed v → v ≤ s.G
  last_pred  : lastD x.ppred x.mpred = x.pred
  last_gen   : lastD x.pgen x.mgen = x.gen
  pub_top    : x.pc.pub = true → lastD x.ptop x.vis = true
  fenced     : P.fence = true → x.pc.final = true → empties x
  crossed_final : x.crossed = true → x.pc.final = true → empties x ∨ s.start ≤ x.gen
  hold       : ∀ k, x.hold = some k →
                 x.pc = .running ∧ s.owner k = x.pred ∧ s.visAt k x.gen
  code       : ∀ v, x.code = some v →
                 x.pc = .running ∧ ∀ e, s.dead x.pred v = some e → x.gen ≤ e
  freedC     : ∀ k, s.cfreed k = true → x.pc.final = true → s.owner k = x.pred →
                 ¬ s.visAt k x.gen
  freedV     : ∀ v, s.vfreed x.pred v = true → x.code ≠ some v
  scanned_final : s.gpc = .scanning → x.seen ≠ none → x.pc.final = true →
                 s.start ≤ x.gen ∨ x.seen = some (some (x.pred, x.gen))
  unscanned  : s.gpc = .begun ∨ s.gpc = .started → x.seen = none
  uncrossed  : s.gpc = .begun → x.crossed = false

structure Inv (P : Proto) (s : St R D K) : Prop where
  start_le    : s.start ≤ s.G
  freedC_old  : ∀ k, s.cfreed k = true → ∃ e, s.erased k = some e ∧ e < s.G
  freedV_dead : ∀ d v, s.vfreed d v = true → s.dead d v ≠ none
  fresh       : ∀ d v, s.cur d ≤ v → s.dead d v = none
  all_crossed : P.cross = true → s.gpc = .scanning → ∀ r, (s.rd r).crossed = true
  rd          : ∀ r, RInv P s (s.rd r)

section lemmas

@[simp] theorem setR_same (s : St R D K) (r : R) (x : RS D K) : (s.setR r x).rd r = x := by
  simp [St.setR, upd]

theorem setR_ne (s : St R D K) {r r' : R} (x : RS D K) (h : r' ≠ r) :
    (s.setR r x).rd r' = s.rd r' := by
  simp [St.setR, upd, h]

theorem visAt_congr {s t : St R D K} (hb : s.born = t.born) (he : s.erased = t.erased)
    (k : K) (g : Nat) : s.visAt k g ↔ t.visAt k g := by
  simp [St.visAt, hb, he]

theorem RInv.congr {P : Proto} {s t : St R D K} {x : RS D K} (hG : s.G = t.G)
    (ho : s.owner = t.owner) (hb : s.born = t.born) (he : s.erased = t.erased)
    (hcf : s.cfreed = t.cfreed) (hd : s.dead = t.dead) (hvf : s.vfreed = t.vfreed)
    (hg : s.gpc = t.gpc) (hs : s.start = t.start) (h : RInv P s x) : RInv P t x where
  gen_le := hG ▸ h.gen_le
  grabbed_le := fun v hv => hG ▸ h.grabbed_le v hv
  last_pred := h.last_pred
  last_gen := h.last_gen
  pub_top := h.pub_top
  fenced := h.fenced
  crossed_final := fun hc hf => hs ▸ h.crossed_final hc hf
  hold := fun k hk =>
    ⟨(h.hold k hk).1, ho ▸ (h.hold k hk).2.1, (visAt_congr hb he k x.gen).1 (h.hold k hk).2.2⟩
  code := fun v hv => ⟨(h.code v hv).1, fun e hev => (h.code v hv).2 e (hd ▸ hev)⟩
  freedC := fun k hk hf hown hv =>
    h.freedC k (hcf ▸ hk) hf (ho ▸ hown) ((visAt_congr hb he k x.gen).2 hv)
  freedV := fun v hv => h.freedV v (hvf ▸ hv)
  scanned_final := fun hgs hn hf => hs ▸ h.scanned_final (hg ▸ hgs) hn hf
  unscanned := fun hgb => h.unscanned (hg ▸ hgb)
  uncrossed := fun hgb => h.uncrossed (hg ▸ hgb)

theorem inv_setR {P : Proto} {s : St R D K} {r : R} {x : RS D K} (h : Inv P s)
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
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl rfl rfl rfl hx
    · rw [setR_ne s x hr]
      exact RInv.congr (s := s) rfl rfl rfl rfl rfl rfl rfl rfl rfl (h.rd r')

theorem not_visAt_of_erased_le {s : St R D K} {k : K} {e g : Nat}
    (he : s.erased k = some e) (hle : e ≤ g) : ¬ s.visAt k g := by
  intro hv
  have hb := hv.2
  rw [he] at hb
  simp [before] at hb
  omega

end lemmas

/-! ## Preservation -/

section preservation

variable {P : Proto}

theorem idle_none {s : St R D K} {x : RS D K} (hx : RInv P s x) (hpc : x.pc ≠ .running) :
    x.code = none ∧ x.hold = none := by
  constructor
  · cases hc : x.code with
    | none => rfl
    | some v => exact absurd (hx.code v hc).1 hpc
  · cases hh : x.hold with
    | none => rfl
    | some k => exact absurd (hx.hold k hh).1 hpc

/-- A reader that is not final and holds nothing. -/
theorem rinv_nonfinal {s : St R D K} {x y : RS D K} (hx : RInv P s x)
    (hgen : y.gen ≤ s.G) (hgr : ∀ v, y.pc = .grabbed v → v ≤ s.G)
    (hlp : lastD y.ppred y.mpred = y.pred) (hlg : lastD y.pgen y.mgen = y.gen)
    (hpt : y.pc.pub = true → lastD y.ptop y.vis = true)
    (hnf : y.pc.final = false) (hc : y.code = none) (hh : y.hold = none)
    (hseen : y.seen = x.seen) (hcr : y.crossed = x.crossed) : RInv P s y where
  gen_le := hgen
  grabbed_le := hgr
  last_pred := hlp
  last_gen := hlg
  pub_top := hpt
  fenced := by intro _ hf; rw [hnf] at hf; cases hf
  crossed_final := by intro _ hf; rw [hnf] at hf; cases hf
  hold := by intro k hk; rw [hh] at hk; cases hk
  code := by intro v hv; rw [hc] at hv; cases hv
  freedC := by intro k _ hf; rw [hnf] at hf; cases hf
  freedV := by intro v _; rw [hc]; simp
  scanned_final := by intro _ _ hf; rw [hnf] at hf; cases hf
  unscanned := fun hg => hseen ▸ hx.unscanned hg
  uncrossed := fun hg => hcr ▸ hx.uncrossed hg

theorem pub_of {x : RS D K} {pc : Pc} (hx : x.pc = pc) (hp : pc.pub = true)
    (h : x.pc.pub = true → lastD x.ptop x.vis = true) (y : RS D K)
    (hy : y.pc.pub = true → y.ptop = x.ptop ∧ y.vis = x.vis) :
    y.pc.pub = true → lastD y.ptop y.vis = true := by
  intro hyp
  obtain ⟨h1, h2⟩ := hy hyp
  rw [h1, h2]
  exact h (hx ▸ hp)

theorem inv_call {s : St R D K} {r : R} {p : D} (h : Inv P s) (hpc : (s.rd r).pc = .idle) :
    Inv P (s.setR r { s.rd r with pc := .called, pred := p,
                                   ppred := (s.rd r).ppred ++ [p] }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv) (lastD_append _ _ _)
    hx.last_gen (by intro hp; simp [Pc.pub] at hp) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_depart {s : St R D K} {r : R} {p : D} (h : Inv P s) :
    Inv P (s.setR r { s.rd r with pc := .called, pred := p, code := none, hold := none,
                                   ppred := (s.rd r).ppred ++ [p] }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv) (lastD_append _ _ _)
    hx.last_gen (by intro hp; simp [Pc.pub] at hp) (by simp [Pc.final]) rfl rfl rfl rfl

theorem inv_publish {s : St R D K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .called) :
    Inv P (s.setR r { s.rd r with pc := .storing,
                                   ptop := (s.rd r).ptop ++ [true] }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv) hx.last_pred hx.last_gen
    (by intro _; simp only; rw [lastD_append]) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_grab {s : St R D K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .storing) :
    Inv P (s.setR r { s.rd r with pc := .grabbed s.G }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro v hv; simp at hv; omega) hx.last_pred
    hx.last_gen (fun _ => hx.pub_top (by rw [hpc]; rfl)) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_put {s : St R D K} {r : R} {v : Nat} (h : Inv P s) (hrc : P.recheck = true)
    (hpc : (s.rd r).pc = .grabbed v) :
    Inv P (s.setR r { s.rd r with pc := if P.recheck then .stored else .validated,
                                   gen := v, pgen := (s.rd r).pgen ++ [v] }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  rw [hrc]
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx (hx.grabbed_le v hpc) (by intro w hw; simp at hw) hx.last_pred
    (lastD_append _ _ _) (fun _ => hx.pub_top (by rw [hpc]; rfl)) (by simp [Pc.final])
    hn.1 hn.2 rfl rfl

theorem inv_check {s : St R D K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .stored)
    (hf : P.fence = true → empties (s.rd r)) :
    Inv P (s.setR r { s.rd r with
      pc := if s.G = (s.rd r).gen then .validated else .storing }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  have htop := hx.pub_top (by rw [hpc]; rfl)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  by_cases heq : s.G = (s.rd r).gen
  · simp only [heq, ↓reduceIte]
    exact
      { gen_le := hx.gen_le
        grabbed_le := by intro w hw; simp at hw
        last_pred := hx.last_pred
        last_gen := hx.last_gen
        pub_top := fun _ => htop
        fenced := fun hp _ => hf hp
        crossed_final := fun _ _ => Or.inr (by simp only; rw [← heq]; exact h.start_le)
        hold := by intro k hk; simp [hn.2] at hk
        code := by intro w hw; simp [hn.1] at hw
        freedC := by
          intro k hk _ _
          obtain ⟨e, he, hlt⟩ := h.freedC_old k hk
          simp only
          rw [← heq]
          exact not_visAt_of_erased_le he (Nat.le_of_lt hlt)
        freedV := by intro w _; simp [hn.1]
        scanned_final := fun _ _ _ => Or.inl (by simp only; rw [← heq]; exact h.start_le)
        unscanned := hx.unscanned
        uncrossed := hx.uncrossed }
  · simp only [heq, ↓reduceIte]
    exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_pred hx.last_gen
      (fun _ => htop) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_light {s : St R D K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .stored) :
    Inv P (s.setR r { s.rd r with pc := .storing }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  have htop := hx.pub_top (by rw [hpc]; rfl)
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_pred hx.last_gen
    (fun _ => htop) (by simp [Pc.final]) hn.1 hn.2 rfl rfl

theorem inv_dispatch {s : St R D K} {r : R} (h : Inv P s) (hpc : (s.rd r).pc = .validated) :
    Inv P (s.setR r { s.rd r with pc := .running,
                                   code := if (s.rd r).code = none
                                           then some (s.cur (s.rd r).pred)
                                           else (s.rd r).code }) := by
  have hx := h.rd r
  have hn := idle_none hx (by rw [hpc]; simp)
  have hcode : (if (s.rd r).code = none then some (s.cur (s.rd r).pred) else (s.rd r).code)
      = some (s.cur (s.rd r).pred) := by simp [hn.1]
  rw [hcode]
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
  exact
    { gen_le := hx.gen_le
      grabbed_le := by intro w hw; simp at hw
      last_pred := hx.last_pred
      last_gen := hx.last_gen
      pub_top := fun _ => hx.pub_top (by rw [hpc]; rfl)
      fenced := fun hp _ => hx.fenced hp hfin
      crossed_final := fun hc _ => hx.crossed_final hc hfin
      hold := by intro k hk; simp [hn.2] at hk
      code := by
        intro w hw
        simp at hw
        subst hw
        refine ⟨rfl, ?_⟩
        intro e he
        rw [h.fresh _ _ (Nat.le_refl _)] at he
        cases he
      freedC := fun k hk _ hown => hx.freedC k hk hfin hown
      freedV := by
        intro w hw hcw
        simp at hcw
        subst hcw
        exact h.freedV_dead _ _ hw (h.fresh _ _ (Nat.le_refl _))
      scanned_final := fun hg hs _ => hx.scanned_final hg hs hfin
      unscanned := hx.unscanned
      uncrossed := hx.uncrossed }

theorem inv_select {s : St R D K} {r : R} {k : K} (h : Inv P s)
    (hpc : (s.rd r).pc = .running) (ho : s.owner k = (s.rd r).pred)
    (hk : s.visAt k (s.rd r).gen) :
    Inv P (s.setR r { s.rd r with hold := some k }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_pred := hx.last_pred
      last_gen := hx.last_gen, pub_top := hx.pub_top, fenced := hx.fenced
      crossed_final := hx.crossed_final
      hold := by intro k' hk'; simp at hk'; subst hk'; exact ⟨hpc, ho, hk⟩
      code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_exit {s : St R D K} {r : R} (h : Inv P s) :
    Inv P (s.setR r { s.rd r with pc := .idle, code := none, hold := none,
                                   ptop := (s.rd r).ptop ++ [false] }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact rinv_nonfinal hx hx.gen_le (by intro w hw; simp at hw) hx.last_pred hx.last_gen
    (by intro hp; simp [Pc.pub] at hp) (by simp [Pc.final]) rfl rfl rfl rfl

theorem inv_drainPred {s : St R D K} {r : R} {p : D} {rest : List D} (h : Inv P s)
    (hq : (s.rd r).ppred = p :: rest) :
    Inv P (s.setR r { s.rd r with mpred := p, ppred := rest }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
      last_pred := by simp only; rw [← hx.last_pred, hq]; rfl
      last_gen := hx.last_gen, pub_top := hx.pub_top
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

theorem inv_drainGen {s : St R D K} {r : R} {v : Nat} {rest : List Nat} (h : Inv P s)
    (hq : (s.rd r).pgen = v :: rest) :
    Inv P (s.setR r { s.rd r with mgen := v, pgen := rest }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_pred := hx.last_pred
      last_gen := by simp only; rw [← hx.last_gen, hq]; rfl
      pub_top := hx.pub_top
      fenced := by
        intro hp hst
        have := (hx.fenced hp hst).2.1
        rw [hq] at this; cases this
      crossed_final := by
        intro hc hfin
        rcases hx.crossed_final hc hfin with ⟨_, hp, _⟩ | hle
        · rw [hq] at hp; cases hp
        · exact Or.inr hle
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_drainTop {s : St R D K} {r : R} {b : Bool} {rest : List Bool} (h : Inv P s)
    (hq : (s.rd r).ptop = b :: rest) :
    Inv P (s.setR r { s.rd r with vis := b, ptop := rest }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun hp hg => ?_)
  rotate_left
  · exact h.all_crossed hp hg r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_pred := hx.last_pred
      last_gen := hx.last_gen
      pub_top := by
        intro hp
        have := hx.pub_top hp
        simp only
        rw [hq] at this
        exact this
      fenced := by
        intro hp hst
        have := (hx.fenced hp hst).2.2
        rw [hq] at this; cases this
      crossed_final := by
        intro hc hfin
        rcases hx.crossed_final hc hfin with ⟨_, _, hp⟩ | hle
        · rw [hq] at hp; cases hp
        · exact Or.inr hle
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := hx.scanned_final
      unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_cross {s : St R D K} {r : R} (h : Inv P s) (hg : s.gpc = .started) :
    Inv P (s.setR r { s.rd r with mpred := lastD (s.rd r).ppred (s.rd r).mpred,
                                   mgen := lastD (s.rd r).pgen (s.rd r).mgen,
                                   vis := lastD (s.rd r).ptop (s.rd r).vis,
                                   ppred := [], pgen := [], ptop := [],
                                   crossed := true }) := by
  have hx := h.rd r
  refine inv_setR h ?_ (fun _ hg' => absurd (hg.symm.trans hg') (by decide))
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
      last_pred := by simp only [lastD]; exact hx.last_pred
      last_gen := by simp only [lastD]; exact hx.last_gen
      pub_top := by intro hp; simp only [lastD]; exact hx.pub_top hp
      fenced := fun _ _ => ⟨rfl, rfl, rfl⟩
      crossed_final := fun _ _ => Or.inl ⟨rfl, rfl, rfl⟩
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := by intro hg'; rw [hg] at hg'; cases hg'
      unscanned := hx.unscanned
      uncrossed := by intro hb; rw [hg] at hb; cases hb }

theorem scan_sees {s : St R D K} {x : RS D K} (hfc : P.fence = true ∨ P.cross = true)
    (hx : RInv P s x) (hcr : P.cross = true → x.crossed = true)
    (hfin : x.pc.final = true) :
    s.start ≤ x.gen ∨ (x.vis = true ∧ x.mpred = x.pred ∧ x.mgen = x.gen) := by
  have hempty : empties x ∨ s.start ≤ x.gen := by
    rcases hfc with hf | hc
    · exact Or.inl (hx.fenced hf hfin)
    · exact hx.crossed_final (hcr hc) hfin
  rcases hempty with ⟨hp, hg, ht⟩ | hle
  · right
    have hpub : x.pc.pub = true := by
      cases hpc : x.pc <;> simp [hpc, Pc.final, Pc.pub] at hfin ⊢
    have hv := hx.pub_top hpub
    have hpr := hx.last_pred
    have hge := hx.last_gen
    rw [ht] at hv; rw [hp] at hpr; rw [hg] at hge
    simp only [lastD] at hv hpr hge
    exact ⟨hv, hpr, hge⟩
  · exact Or.inl hle

theorem inv_scan {s : St R D K} {r : R} (h : Inv P s)
    (hfc : P.fence = true ∨ P.cross = true) (hg : s.gpc = .scanning) :
    Inv P (s.setR r { s.rd r with
      seen := some (if (s.rd r).vis then some ((s.rd r).mpred, (s.rd r).mgen)
                    else none) }) := by
  have hx := h.rd r
  have hcr : P.cross = true → (s.rd r).crossed = true := fun hp => h.all_crossed hp hg r
  refine inv_setR h ?_ (fun hp hg' => ?_)
  rotate_left
  · exact h.all_crossed hp hg' r
  exact
    { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le, last_pred := hx.last_pred
      last_gen := hx.last_gen, pub_top := hx.pub_top, fenced := hx.fenced
      crossed_final := hx.crossed_final
      hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
      scanned_final := by
        intro _ _ hfin
        rcases scan_sees hfc hx hcr hfin with hle | ⟨hv, hp, hm⟩
        · exact Or.inl hle
        · right; simp [hv, hp, hm]
      unscanned := by intro hb; rw [hg] at hb; rcases hb with hb | hb <;> cases hb
      uncrossed := hx.uncrossed }

theorem inv_bump {s : St R D K} (h : Inv P s) : Inv P { s with G := s.G + 1 } where
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_erase {s : St R D K} {k0 : K} (h : Inv P s) (hk0 : s.erased k0 = none) :
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := by
          intro k hk
          obtain ⟨hpc, ho, hv⟩ := hx.hold k hk
          refine ⟨hpc, ho, ?_⟩
          by_cases hkk : k = k0
          · subst hkk
            have := hx.gen_le
            simp only [St.visAt, upd] at hv ⊢
            exact ⟨hv.1, by simp [before]; omega⟩
          · exact (vis_ne k _ hkk).2 hv
        code := hx.code
        freedC := fun k hk hf ho hv => hx.freedC k hk hf ho ((vis_ne k _ (fne k hk)).1 hv)
        freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_replace {s : St R D K} {d : D} (h : Inv P s) :
    Inv P { s with dead := upd s.dead d (upd (s.dead d) (s.cur d) (some s.G)),
                   cur := upd s.cur d (s.cur d + 1) } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := by
    intro d' v hv
    by_cases hd : d' = d
    · subst hd
      by_cases hvc : v = s.cur d'
      · subst hvc; simp [upd]
      · simp [upd, hvc]; exact h.freedV_dead d' v hv
    · simp [upd, hd]; exact h.freedV_dead d' v hv
  fresh := by
    intro d' v hv
    by_cases hd : d' = d
    · subst hd
      have hv' : s.cur d' + 1 ≤ v := by simpa [upd] using hv
      have hne : v ≠ s.cur d' := by omega
      simp [upd, hne]
      exact h.fresh d' v (by omega)
    · have hv' : s.cur d' ≤ v := by simpa [upd, hd] using hv
      simp [upd, hd]
      exact h.fresh d' v hv'
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold
        code := by
          intro v hv
          obtain ⟨hpc, hle⟩ := hx.code v hv
          refine ⟨hpc, ?_⟩
          intro e he
          by_cases hd : (s.rd r).pred = d
          · by_cases hvc : v = s.cur d
            · subst hvc
              simp [upd, hd] at he
              subst he
              exact hx.gen_le
            · simp [upd, hd, hvc] at he
              exact hle e (by rw [hd]; exact he)
          · simp [upd, hd] at he
            exact hle e he
        freedC := hx.freedC, freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_gcBegin {s : St R D K} (h : Inv P s) :
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced
        crossed_final := by intro hc; cases hc
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg; cases hg
        unscanned := fun _ => rfl
        uncrossed := fun _ => rfl }

theorem inv_gcStart {s : St R D K} (h : Inv P s) (hg : s.gpc = .begun) :
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced
        crossed_final := by intro hc; rw [hnc] at hc; cases hc
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg'; cases hg'
        unscanned := fun _ => hns
        uncrossed := by intro hb; cases hb }

theorem inv_toScan {s : St R D K} (h : Inv P s) (hg : s.gpc = .started)
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro _ hs; exact absurd hns hs
        unscanned := by intro hb; rcases hb with hb | hb <;> cases hb
        uncrossed := by intro hb; cases hb }

theorem inv_freeClause {s : St R D K} {k0 : K} {e : Nat} (h : Inv P s)
    (hg : s.gpc = .scanning) (hall : ∀ r, (s.rd r).seen ≠ none)
    (he : s.erased k0 = some e) (hlt : e < s.start)
    (hinv : ∀ r d g, (s.rd r).seen = some (some (d, g)) → d = s.owner k0 →
              ¬ s.visAt k0 g) :
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
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code
        freedC := by
          intro k hk hfin hown
          by_cases hkk : k = k0
          · subst hkk
            rcases hx.scanned_final hg (hall r) hfin with hle | hs
            · exact not_visAt_of_erased_le he (by show e ≤ (s.rd r).gen; omega)
            · exact hinv r _ _ hs hown.symm
          · exact hx.freedC k (by simpa [upd, hkk] using hk) hfin hown
        freedV := hx.freedV
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_freeCode {s : St R D K} {d0 : D} {v0 e : Nat} (h : Inv P s)
    (hg : s.gpc = .scanning) (hall : ∀ r, (s.rd r).seen ≠ none)
    (hd : s.dead d0 v0 = some e) (hlt : e < s.start)
    (hinv : ∀ r d' g, (s.rd r).seen = some (some (d', g)) → d' = d0 → e < g) :
    Inv P { s with vfreed := upd s.vfreed d0 (upd (s.vfreed d0) v0 true) } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := by
    intro d v hv
    by_cases hdd : d = d0
    · subst hdd
      by_cases hvv : v = v0
      · subst hvv; rw [hd]; simp
      · exact h.freedV_dead d v (by simpa [upd, hvv] using hv)
    · exact h.freedV_dead d v (by simpa [upd, hdd] using hv)
  fresh := h.fresh
  all_crossed := h.all_crossed
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC
        freedV := by
          intro v hv hcv
          by_cases hdd : (s.rd r).pred = d0
          · by_cases hvv : v = v0
            · subst hvv
              obtain ⟨hpc, hle⟩ := hx.code v hcv
              have hge := hle e (by rw [hdd]; exact hd)
              have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
              rcases hx.scanned_final hg (hall r) hfin with hst | hs
              · omega
              · have := hinv r _ _ hs hdd; omega
            · exact hx.freedV v (by simpa [upd, hdd, hvv] using hv) hcv
          · exact hx.freedV v (by simpa [upd, hdd] using hv) hcv
        scanned_final := hx.scanned_final
        unscanned := hx.unscanned, uncrossed := hx.uncrossed }

theorem inv_gcEnd {s : St R D K} (h : Inv P s) : Inv P { s with gpc := .idle } where
  start_le := h.start_le
  freedC_old := h.freedC_old
  freedV_dead := h.freedV_dead
  fresh := h.fresh
  all_crossed := by intro _ hg; cases hg
  rd := fun r => by
    have hx := h.rd r
    exact
      { gen_le := hx.gen_le, grabbed_le := hx.grabbed_le
        last_pred := hx.last_pred, last_gen := hx.last_gen, pub_top := hx.pub_top
        fenced := hx.fenced, crossed_final := hx.crossed_final
        hold := hx.hold, code := hx.code, freedC := hx.freedC, freedV := hx.freedV
        scanned_final := by intro hg; cases hg
        unscanned := by intro hb; rcases hb with hb | hb <;> cases hb
        uncrossed := by intro hb; cases hb }

theorem step_inv {s t : St R D K} (he : P.early = false) (hrc : P.recheck = true)
    (hfc : P.fence = true ∨ P.cross = true) (h : Inv P s) (hst : Step P s t) : Inv P t := by
  cases hst with
  | bump => exact inv_bump h
  | erase k hk => exact inv_erase h hk
  | replace d => exact inv_replace h
  | call r p hpc => exact inv_call h hpc
  | depart r p _ => exact inv_depart h
  | early r hp _ _ => rw [he] at hp; cases hp
  | publish r hpc => exact inv_publish h hpc
  | grab r hpc => exact inv_grab h hpc
  | put r v hpc => exact inv_put h hrc hpc
  | check r hpc hf => exact inv_check h hpc hf
  | light r _ hpc => exact inv_light h hpc
  | dispatch r hpc => exact inv_dispatch h hpc
  | select r k hpc ho hk => exact inv_select h hpc ho hk
  | exit r _ => exact inv_exit h
  | drainPred r p rest hq => exact inv_drainPred h hq
  | drainGen r v rest hq => exact inv_drainGen h hq
  | drainTop r b rest hq => exact inv_drainTop h hq
  | gcBegin => exact inv_gcBegin h
  | gcStart hg => exact inv_gcStart h hg
  | cross r _ hg _ => exact inv_cross h hg
  | toScan hg hc => exact inv_toScan h hg hc
  | scan r hg _ => exact inv_scan h hfc hg
  | freeClause k e hg hall hek hlt hinv => exact inv_freeClause h hg hall hek hlt hinv
  | freeCode d v e hg hall hd hlt hinv => exact inv_freeCode h hg hall hd hlt hinv
  | gcEnd => exact inv_gcEnd h
  | gcAbort => exact inv_gcEnd h

end preservation

theorem init_inv {P : Proto} {s : St R D K} (h : Init s) : Inv P s where
  start_le := h.2.2.1
  freedC_old := by intro k hk; rw [h.2.2.2.1 k] at hk; cases hk
  freedV_dead := by intro d v hv; rw [h.2.2.2.2.1 d v] at hv; cases hv
  fresh := fun d v _ => h.2.2.2.2.2 d v
  all_crossed := by intro _ hg; rw [h.2.1] at hg; cases hg
  rd := fun r => by
    obtain ⟨hpc, ⟨hpp, hpg, hpt⟩, hv, hc, hh, hcr, hs, hm, hmp, hg⟩ := h.1 r
    exact
      { gen_le := hg
        grabbed_le := by intro v hv'; rw [hpc] at hv'; cases hv'
        last_pred := by rw [hpp]; exact hmp
        last_gen := by rw [hpg]; exact hm
        pub_top := by intro hp; rw [hpc] at hp; simp [Pc.pub] at hp
        fenced := by intro _ hst; rw [hpc] at hst; simp [Pc.final] at hst
        crossed_final := by intro hc'; rw [hcr] at hc'; cases hc'
        hold := by intro k hk; rw [hh] at hk; cases hk
        code := by intro v hv'; rw [hc] at hv'; cases hv'
        freedC := by intro k hk; rw [h.2.2.2.1 k] at hk; cases hk
        freedV := by intro v hv'; rw [h.2.2.2.2.1 _ v] at hv'; cases hv'
        scanned_final := by intro hg'; rw [h.2.1] at hg'; cases hg'
        unscanned := fun _ => hs
        uncrossed := fun _ => hcr }

theorem Inv.safe {P : Proto} {s : St R D K} (h : Inv P s) : Safe s := by
  intro r
  have hx := h.rd r
  refine ⟨?_, ?_⟩
  · intro v hv
    cases hf : s.vfreed (s.rd r).pred v with
    | false => rfl
    | true => exact absurd hv (hx.freedV v hf)
  · intro k hk
    obtain ⟨hpc, ho, hvis⟩ := hx.hold k hk
    have hfin : (s.rd r).pc.final = true := by simp [hpc, Pc.final]
    cases hf : s.cfreed k with
    | false => rfl
    | true => exact absurd hvis (hx.freedC k hf hfin ho)

/-- With predicates and last calls: publication before setGenerationFrame(),
re-validation after a barrier, DEF->codes read after it, and a fence or a
barrier that every thread crosses.  No frame ever holds a reclaimed clause
or a freed supervisor of its predicate. -/
theorem safe (P : Proto) (he : P.early = false) (hrc : P.recheck = true)
    (hfc : P.fence = true ∨ P.cross = true) {s0 s : St R D K} (h0 : Init s0)
    (hr : Reach P s0 s) : Safe s := by
  have : Inv P s := by
    induction hr with
    | refl => exact init_inv h0
    | tail _ hst ih => exact step_inv he hrc hfc ih hst
  exact this.safe

theorem symmetric_safe {s0 s : St R D K} (h0 : Init s0) (hr : Reach symmetric s0 s) :
    Safe s := safe symmetric rfl rfl (Or.inl rfl) h0 hr

theorem asymmetric_safe {s0 s : St R D K} (h0 : Init s0) (hr : Reach asymmetric s0 s) :
    Safe s := safe asymmetric rfl rfl (Or.inr rfl) h0 hr

theorem fallback_safe {s0 s : St R D K} (h0 : Init s0) (hr : Reach fallback s0 s) :
    Safe s := safe fallback rfl rfl (Or.inl rfl) h0 hr

theorem asymmetricLight_safe {s0 s : St R D K} (h0 : Init s0)
    (hr : Reach asymmetricLight s0 s) : Safe s :=
  safe asymmetricLight rfl rfl (Or.inr rfl) h0 hr

end Mettapedia.Languages.Prolog.SWI.CallPortPred
