/-
Lifetime protocol of the static S_TRUSTME / S_LIST supervisors, at
SWI-Prolog 3f6bfd9. Sequential consistency; one predicate and one slot.
The reader's stamp abstracts the guarantee established by CallPort.

Clauses have fixed birth generations, including future births: a clause
with born = G+1 becomes visible when that generation is published. This
also abstracts the added clauses in reconsultFinalizePredicate(). No
reader transition tests visibility or whether an object has been freed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Prolog.SWI.Supervisor.V1

def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

inductive DetachMode where
  | none | inSection | afterPublish
deriving DecidableEq

structure Proto where
  detach : DetachMode
  validate : Bool
  cas : Bool
  hold : Bool

def fixed : Proto := ⟨.inSection, true, true, true⟩
def noDetach : Proto := { fixed with detach := .none }
def lateDetach : Proto := { fixed with detach := .afterPublish }
def unvalidated : Proto := { fixed with validate := false }
def plainSwap : Proto := { fixed with cas := false }
def noHold : Proto := { fixed with hold := false }

inductive Lock where
  | free | writer | creator
deriving DecidableEq

inductive RPc where
  | idle | stamped | running
deriving DecidableEq

structure Reader (K : Type) where
  pc : RPc := .idle
  gen : Nat := 0
  code : Option Nat := none
  run : Option K := none

inductive CPc where
  | idle | scanning | ready | checking | lingering
deriving DecidableEq

/-- One creator, serialized by L_PREDICATE. It keeps acquire_def2() from
the start of the scan until after it lingers the replaced supervisor. -/
structure Creator (K : Type) where
  pc : CPc := .idle
  old : Option Nat := none
  found : List K := []
  ver : Nat := 0
  holds : Bool := false

inductive DPc where
  | idle | loaded | lingering
deriving DecidableEq

structure Detacher where
  pc : DPc := .idle
  old : Option Nat := none

inductive WPc where
  | idle | marking | detached | late
deriving DecidableEq

inductive GPc where
  | idle | scanning
deriving DecidableEq

structure St (R D K : Type) where
  G : Nat
  born : K → Nat
  erased : K → Option Nat
  cl_erased : K → Bool
  cfreed : K → Bool
  /-- Only fresh allocation writes this map; entries are thereafter fixed. -/
  embeds : Nat → List K
  next : Nat
  vfreed : Nat → Bool
  slot : Option Nat
  /-- History of linger insertion, retained also after reclamation. -/
  lingered : Nat → Option Nat
  dup : Bool
  lock : Lock
  wp : WPc
  cr : Creator K
  rd : R → Reader K
  dt : D → Detacher
  gpc : GPc
  start : Nat
  /-- none = not scanned; some none = scanned while idle. -/
  seen : R → Option (Option Nat)

variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

def St.visAt (s : St R D K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ ∀ e, s.erased k = some e → g < e

instance (s : St R D K) (k : K) (g : Nat) : Decidable (s.visAt k g) :=
  match he : s.erased k with
  | none => decidable_of_iff (s.born k ≤ g) (by simp [St.visAt, he])
  | some e => decidable_of_iff (s.born k ≤ g ∧ g < e) (by simp [St.visAt, he])

def St.setR (s : St R D K) (r : R) (x : Reader K) : St R D K :=
  { s with rd := upd s.rd r x }

def St.setD (s : St R D K) (d : D) (x : Detacher) : St R D K :=
  { s with dt := upd s.dt d x }

def St.linger (s : St R D K) : Option Nat → St R D K
  | none => s                         -- S_VIRGIN is statically allocated
  | some v => { s with lingered := upd s.lingered v (some s.G),
                        dup := s.dup || (s.lingered v).isSome }

def St.writerDetach (s : St R D K) (pc : WPc) : St R D K :=
  ({ s with slot := none, wp := pc }).linger s.slot

def St.allocate (s : St R D K) : St R D K :=
  { s with embeds := upd s.embeds s.next s.cr.found, next := s.next + 1,
           cr := { s.cr with pc := .ready, ver := s.next } }

def St.installed (s : St R D K) : St R D K :=
  { s with slot := some s.cr.ver, lock := .free,
           cr := { s.cr with pc := .lingering } }

def St.creatorDone (s : St R D K) : St R D K :=
  { s.linger s.cr.old with cr := {} }

def St.detacherSwap (s : St R D K) (d : D) : St R D K :=
  { s.setD d { s.dt d with pc := .lingering } with slot := none }

def St.detacherDone (s : St R D K) (d : D) : St R D K :=
  (s.linger (s.dt d).old).setD d {}

inductive Step (P : Proto) : St R D K → St R D K → Prop where
  /-- After this step the frame is visible to clause GC (CallPort). -/
  | stamp (s : St R D K) (r : R) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { pc := .stamped, gen := s.G })
  | readSlot (s : St R D K) (r : R) (v : Nat)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = some v) :
      Step P s (s.setR r { s.rd r with pc := .running, code := some v })
  /-- S_VIRGIN waits for creation, retaining the stamped generation. -/
  | wait (s : St R D K) (r : R)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = none) : Step P s s
  /-- S_TRUSTME / S_LIST: deliberately no visibility or liveness check. -/
  | run (s : St R D K) (r : R) (v : Nat) (k : K)
      (h : (s.rd r).pc = .running) (hv : (s.rd r).code = some v)
      (hk : k ∈ s.embeds v) :
      Step P s (s.setR r { s.rd r with run := some k })
  | exit (s : St R D K) (r : R) (h : (s.rd r).pc ≠ .idle) :
      Step P s (s.setR r {})
  | writerLock (s : St R D K) (h : s.lock = .free) (hw : s.wp = .idle) :
      Step P s { s with lock := .writer, wp := .marking }
  /-- Repeat this step for any number of live clauses while holding the lock. -/
  | mark (s : St R D K) (k : K) (h : s.lock = .writer)
      (hw : s.wp = .marking) (hk : s.visAt k s.G) (hf : s.cl_erased k = false) :
      Step P s { s with erased := upd s.erased k (some (s.G + 1)),
                        cl_erased := upd s.cl_erased k true }
  | writerDetach (s : St R D K) (hp : P.detach = .inSection)
      (h : s.lock = .writer) (hw : s.wp = .marking) :
      Step P s (s.writerDetach .detached)
  | skipDetach (s : St R D K) (hp : P.detach ≠ .inSection)
      (h : s.lock = .writer) (hw : s.wp = .marking) :
      Step P s { s with wp := .detached }
  | publish (s : St R D K) (h : s.lock = .writer) (hw : s.wp = .detached) :
      Step P s { s with G := s.G + 1, lock := .free,
                        wp := if P.detach = .afterPublish then .late else .idle }
  | lateDetach (s : St R D K) (hp : P.detach = .afterPublish) (hw : s.wp = .late) :
      Step P s (s.writerDetach .idle)
  | creatorRead (s : St R D K) (h : s.cr.pc = .idle) :
      Step P s { s with cr := { pc := .scanning, old := s.slot, holds := P.hold } }
  /-- getClauses() re-reads G for each candidate. -/
  | scanClause (s : St R D K) (k : K) (h : s.cr.pc = .scanning)
      (hk : s.visAt k s.G) :
      Step P s { s with cr := { s.cr with found := s.cr.found ++ [k] } }
  | allocate (s : St R D K) (h : s.cr.pc = .scanning) : Step P s s.allocate
  | creatorLock (s : St R D K) (h : s.lock = .free) (hc : s.cr.pc = .ready) :
      Step P s { s with lock := .creator, cr := { s.cr with pc := .checking } }
  /-- The check and CAS are in the same L_GENERATION critical section. -/
  | install (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hv : P.validate = true → ∀ k ∈ s.embeds s.cr.ver, s.cl_erased k = false)
      (hs : P.cas = true → s.slot = s.cr.old) : Step P s s.installed
  | retry (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hf : (P.validate = true ∧ ∃ k ∈ s.embeds s.cr.ver, s.cl_erased k = true) ∨
            (P.cas = true ∧ s.slot ≠ s.cr.old)) :
      Step P s { s with lock := .free, cr := {}, vfreed := upd s.vfreed s.cr.ver true }
  /-- freeSupervisor(old, true), after installSupervisor unlocked; use G now. -/
  | creatorLinger (s : St R D K) (h : s.cr.pc = .lingering) :
      Step P s s.creatorDone
  | detacherRead (s : St R D K) (d : D) (h : (s.dt d).pc = .idle) :
      Step P s (s.setD d { pc := .loaded, old := s.slot })
  | detacherCas (s : St R D K) (d : D) (h : (s.dt d).pc = .loaded)
      (hs : P.cas = true → s.slot = (s.dt d).old) :
      Step P s (s.detacherSwap d)
  | detacherRetry (s : St R D K) (d : D) (hp : P.cas = true)
      (h : (s.dt d).pc = .loaded) (hs : s.slot ≠ (s.dt d).old) :
      Step P s (s.setD d {})
  | detacherLinger (s : St R D K) (d : D) (h : (s.dt d).pc = .lingering) :
      Step P s (s.detacherDone d)
  | gcStart (s : St R D K) (h : s.gpc = .idle) :
      Step P s { s with gpc := .scanning, start := s.G, seen := fun _ => none }
  | gcScan (s : St R D K) (r : R) (h : s.gpc = .scanning) (hn : s.seen r = none) :
      Step P s { s with seen := upd s.seen r
                          (some (if (s.rd r).pc = .idle then none else some (s.rd r).gen)) }
  /-- ddi_is_garbage() and gcClauseRefs(): no acquire_def2() holder. -/
  | freeClause (s : St R D K) (k : K) (e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, s.seen r ≠ none) (he : s.erased k = some e)
      (hf : s.cl_erased k = true) (hlt : e < s.start)
      (hinv : ∀ r g, s.seen r = some (some g) → ¬ s.visAt k g)
      (hh : s.cr.holds = false) (hnew : s.cfreed k = false) :
      Step P s { s with cfreed := upd s.cfreed k true }
  /-- free_lingering(min(start, oldest registered generation)), strictly <. -/
  | freeVersion (s : St R D K) (v d : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, s.seen r ≠ none) (hd : s.lingered v = some d) (hlt : d < s.start)
      (hinv : ∀ r g, s.seen r = some (some g) → d < g) (hnew : s.vfreed v = false) :
      Step P s { s with vfreed := upd s.vfreed v true }
  | gcEnd (s : St R D K) (h : s.gpc = .scanning) : Step P s { s with gpc := .idle }

inductive Reach (P : Proto) : St R D K → St R D K → Prop where
  | refl (s : St R D K) : Reach P s s
  | tail {s t u : St R D K} : Reach P s t → Step P t u → Reach P s u

def Init (s : St R D K) : Prop :=
  s.slot = none ∧ s.next = 0 ∧ s.dup = false ∧ s.lock = .free ∧ s.wp = .idle ∧
  s.cr = {} ∧ (∀ r, s.rd r = {}) ∧ (∀ d, s.dt d = {}) ∧
  s.gpc = .idle ∧ s.start ≤ s.G ∧ (∀ r, s.seen r = none) ∧
  (∀ k, s.erased k = none ∧ s.cl_erased k = false ∧ s.cfreed k = false) ∧
  (∀ v, s.embeds v = [] ∧ s.vfreed v = false ∧ s.lingered v = none)

def Safe (s : St R D K) : Prop :=
  (∀ r, (∀ v, (s.rd r).code = some v → s.vfreed v = false) ∧
        (∀ k, (s.rd r).run = some k → s.cfreed k = false)) ∧
  (s.cr.pc = .checking → ∀ k ∈ s.embeds s.cr.ver, s.cfreed k = false) ∧
  s.dup = false ∧
  (∀ v, s.slot = some v → s.lingered v = none ∧ s.vfreed v = false)

/-! ## A reader predating the birth of a newly created supervisor's clause -/

/-- An initially virgin slot and a pool of clauses with prescribed births.
As in CallPort.Init, births need not precede the initial global generation. -/
def initial (birth : K → Nat) : St R D K :=
  { G := 0, born := birth, erased := fun _ => none,
    cl_erased := fun _ => false, cfreed := fun _ => false,
    embeds := fun _ => [], next := 0, vfreed := fun _ => false,
    slot := none, lingered := fun _ => none, dup := false,
    lock := .free, wp := .idle, cr := {}, rd := fun _ => {}, dt := fun _ => {},
    gpc := .idle, start := 0, seen := fun _ => none }

omit [DecidableEq R] [DecidableEq D] [DecidableEq K] in
theorem initial_init (birth : K → Nat) : Init (initial (R := R) (D := D) birth) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    rfl, Nat.le_refl _, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩,
    fun _ => ⟨rfl, rfl, rfl⟩⟩

/-- An old clause (false) born at 0, and a replacement (true) born at 1.
The first writer erases the old clause and publishes the replacement's birth. -/
def init : St Unit Unit Bool := initial (fun k => if k then 1 else 0)

theorem init_init : Init init := initial_init _

/-- All three fixes, including acquire_def2(), are enabled. The reader stamps
0 and subsequently loads a supervisor containing a clause born at 1. After
erasure at 2, GC at 3 sees the reader's 0, in which the clause is invisible,
and frees it. S_TRUSTME / S_LIST nevertheless runs it. -/
theorem fixed_birth_gap : ∃ s, Reach fixed init s ∧ ¬ Safe s ∧
    s.G = 3 ∧ (s.rd ()).gen = 0 ∧ s.born true = 1 ∧ s.erased true = some 2 ∧
    (s.rd ()).code = some 0 ∧ (s.rd ()).run = some true ∧ s.cfreed true = true ∧
    s.dup = false ∧ s.vfreed 0 = false ∧ s.lingered 0 = some 1 := by
  let s1 := init.setR () { pc := .stamped, gen := 0 }
  let s2 : St Unit Unit Bool := { s1 with lock := .writer, wp := .marking }
  let s2m : St Unit Unit Bool :=
    { s2 with erased := upd s2.erased false (some 1),
              cl_erased := upd s2.cl_erased false true }
  let s3 := s2m.writerDetach .detached
  let s4 : St Unit Unit Bool := { s3 with G := 1, lock := .free, wp := .idle }
  let s5 : St Unit Unit Bool :=
    { s4 with cr := { pc := .scanning, old := s4.slot, holds := true } }
  let s6 : St Unit Unit Bool := { s5 with cr := { s5.cr with found := [true] } }
  let s7 := s6.allocate
  let s8 : St Unit Unit Bool :=
    { s7 with lock := .creator, cr := { s7.cr with pc := .checking } }
  let s9 := s8.installed
  let s10 := s9.creatorDone
  let s11 := s10.setR () { s10.rd () with pc := .running, code := some 0 }
  let s12 : St Unit Unit Bool := { s11 with lock := .writer, wp := .marking }
  let s13 : St Unit Unit Bool :=
    { s12 with erased := upd s12.erased true (some 2),
               cl_erased := upd s12.cl_erased true true }
  let s14 := s13.writerDetach .detached
  let s15 : St Unit Unit Bool := { s14 with G := 2, lock := .free, wp := .idle }
  let s16 : St Unit Unit Bool := { s15 with lock := .writer, wp := .marking }
  let s17 := s16.writerDetach .detached
  let s18 : St Unit Unit Bool := { s17 with G := 3, lock := .free, wp := .idle }
  let s19 : St Unit Unit Bool :=
    { s18 with gpc := .scanning, start := 3, seen := fun _ => none }
  let s20 : St Unit Unit Bool := { s19 with seen := upd s19.seen () (some (some 0)) }
  let s21 : St Unit Unit Bool := { s20 with cfreed := upd s20.cfreed true true }
  let s22 := s21.setR () { s21.rd () with run := some true }
  refine ⟨s22, ?_, ?_, by decide⟩
  · have h0 := Reach.refl (P := fixed) init
    have h1 : Reach fixed init s1 :=
      Reach.tail h0 (Step.stamp _ () (by decide))
    have h2 : Reach fixed init s2 :=
      Reach.tail h1 (Step.writerLock _ (by decide) (by decide))
    have h2m : Reach fixed init s2m :=
      Reach.tail h2 (Step.mark _ false (by decide) (by decide) (by decide) (by decide))
    have h3 : Reach fixed init s3 :=
      Reach.tail h2m (Step.writerDetach _ rfl (by decide) (by decide))
    have h4 : Reach fixed init s4 :=
      Reach.tail h3 (Step.publish _ (by decide) (by decide))
    have h5 : Reach fixed init s5 :=
      Reach.tail h4 (Step.creatorRead _ (by decide))
    have h6 : Reach fixed init s6 :=
      Reach.tail h5 (Step.scanClause _ true (by decide) (by decide))
    have h7 : Reach fixed init s7 := Reach.tail h6 (Step.allocate _ (by decide))
    have h8 : Reach fixed init s8 :=
      Reach.tail h7 (Step.creatorLock _ (by decide) (by decide))
    have h9 : Reach fixed init s9 :=
      Reach.tail h8 (Step.install _ (by decide) (by decide)
        (by intro _; decide) (by intro _; decide))
    have h10 : Reach fixed init s10 :=
      Reach.tail h9 (Step.creatorLinger _ (by decide))
    have h11 : Reach fixed init s11 :=
      Reach.tail h10 (Step.readSlot _ () 0 (by decide) (by decide))
    have h12 : Reach fixed init s12 :=
      Reach.tail h11 (Step.writerLock _ (by decide) (by decide))
    have h13 : Reach fixed init s13 :=
      Reach.tail h12 (Step.mark _ true (by decide) (by decide) (by decide) (by decide))
    have h14 : Reach fixed init s14 :=
      Reach.tail h13 (Step.writerDetach _ rfl (by decide) (by decide))
    have h15 : Reach fixed init s15 :=
      Reach.tail h14 (Step.publish _ (by decide) (by decide))
    have h16 : Reach fixed init s16 :=
      Reach.tail h15 (Step.writerLock _ (by decide) (by decide))
    have h17 : Reach fixed init s17 :=
      Reach.tail h16 (Step.writerDetach _ rfl (by decide) (by decide))
    have h18 : Reach fixed init s18 :=
      Reach.tail h17 (Step.publish _ (by decide) (by decide))
    have h19 : Reach fixed init s19 := Reach.tail h18 (Step.gcStart _ (by decide))
    have h20 : Reach fixed init s20 :=
      Reach.tail h19 (Step.gcScan _ () (by decide) (by decide))
    have h21 : Reach fixed init s21 :=
      Reach.tail h20 (Step.freeClause _ true 2 (by decide) (by intro r; cases r; decide)
        (by decide) (by decide) (by decide) ?_ (by decide) (by decide))
    · exact Reach.tail h21 (Step.run _ () 0 true (by decide) (by decide) (by decide))
    · intro r g hg
      cases r
      have hs : s20.seen () = some (some 0) := by decide
      rw [hs] at hg
      cases hg
      decide
  · intro hs
    have hf := (hs.1 ()).2 true (by decide)
    have : s22.cfreed true = true := by decide
    rw [this] at hf
    cases hf

theorem fixed_unsafe : ∃ s, Reach fixed init s ∧ ¬ Safe s := by
  obtain ⟨s, hr, hu, _⟩ := fixed_birth_gap
  exact ⟨s, hr, hu⟩

theorem not_fixed_safe :
    ¬ (∀ (s0 s : St Unit Unit Bool), Init s0 → Reach fixed s0 s → Safe s) := by
  intro h
  obtain ⟨s, hr, hu⟩ := fixed_unsafe
  exact hu (h init s init_init hr)

/-! ## Each removed fix has its own trace, using only clauses born at 0. -/

def unitInit : St Unit Bool Unit := initial (fun _ => 0)

theorem unitInit_init : Init unitInit := initial_init _

def prepared : St Unit Bool Unit :=
  { unitInit with embeds := upd unitInit.embeds 0 [()], next := 1, slot := some 0 }

/-- Creation of version 0, containing the live clause, works for every protocol. -/
theorem prepared_reach (P : Proto) : Reach P unitInit prepared := by
  let s1 : St Unit Bool Unit :=
    { unitInit with cr := { pc := .scanning, old := none, holds := P.hold } }
  let s2 : St Unit Bool Unit := { s1 with cr := { s1.cr with found := [()] } }
  let s3 := s2.allocate
  let s4 : St Unit Bool Unit :=
    { s3 with lock := .creator, cr := { s3.cr with pc := .checking } }
  let s5 := s4.installed
  have h1 : Reach P unitInit s1 :=
    Reach.tail (.refl _) (Step.creatorRead _ (by decide))
  have h2 : Reach P unitInit s2 :=
    Reach.tail h1 (Step.scanClause _ () rfl
      ⟨Nat.le_refl _, by intro e he; cases he⟩)
  have h3 : Reach P unitInit s3 := Reach.tail h2 (Step.allocate _ rfl)
  have h4 : Reach P unitInit s4 :=
    Reach.tail h3 (Step.creatorLock _ rfl rfl)
  have h5 : Reach P unitInit s5 :=
    Reach.tail h4 (Step.install _ rfl rfl
      (by intro _ k _; cases k; rfl) (by intro _; rfl))
  exact Reach.tail h5 (Step.creatorLinger _ rfl)

theorem no_detach_unsafe : ∃ s, Reach noDetach unitInit s ∧ ¬ Safe s := by
  let s1 : St Unit Bool Unit := { prepared with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Unit :=
    { s1 with erased := upd s1.erased () (some 1), cl_erased := upd s1.cl_erased () true }
  let s3 : St Unit Bool Unit := { s2 with wp := .detached }
  let s4 : St Unit Bool Unit := { s3 with G := 1, lock := .free, wp := .idle }
  let s5 := s4.setR () { pc := .stamped, gen := 1 }
  let s6 := s5.setR () { s5.rd () with pc := .running, code := some 0 }
  let s7 : St Unit Bool Unit := { s6 with lock := .writer, wp := .marking }
  let s8 : St Unit Bool Unit := { s7 with wp := .detached }
  let s9 : St Unit Bool Unit := { s8 with G := 2, lock := .free, wp := .idle }
  let s10 : St Unit Bool Unit :=
    { s9 with gpc := .scanning, start := 2, seen := fun _ => none }
  let s11 : St Unit Bool Unit := { s10 with seen := upd s10.seen () (some (some 1)) }
  let s12 : St Unit Bool Unit := { s11 with cfreed := upd s11.cfreed () true }
  let s13 := s12.setR () { s12.rd () with run := some () }
  refine ⟨s13, ?_, ?_⟩
  · have h1 : Reach noDetach unitInit s1 :=
      Reach.tail (prepared_reach _) (Step.writerLock _ (by decide) (by decide))
    have h2 : Reach noDetach unitInit s2 :=
      Reach.tail h1 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
    have h3 : Reach noDetach unitInit s3 :=
      Reach.tail h2 (Step.skipDetach _ (by decide) (by decide) (by decide))
    have h4 : Reach noDetach unitInit s4 :=
      Reach.tail h3 (Step.publish _ (by decide) (by decide))
    have h5 : Reach noDetach unitInit s5 := Reach.tail h4 (Step.stamp _ () (by decide))
    have h6 : Reach noDetach unitInit s6 :=
      Reach.tail h5 (Step.readSlot _ () 0 (by decide) (by decide))
    have h7 : Reach noDetach unitInit s7 :=
      Reach.tail h6 (Step.writerLock _ (by decide) (by decide))
    have h8 : Reach noDetach unitInit s8 :=
      Reach.tail h7 (Step.skipDetach _ (by decide) (by decide) (by decide))
    have h9 : Reach noDetach unitInit s9 :=
      Reach.tail h8 (Step.publish _ (by decide) (by decide))
    have h10 : Reach noDetach unitInit s10 := Reach.tail h9 (Step.gcStart _ (by decide))
    have h11 : Reach noDetach unitInit s11 :=
      Reach.tail h10 (Step.gcScan _ () (by decide) (by decide))
    have h12 : Reach noDetach unitInit s12 :=
      Reach.tail h11 (Step.freeClause _ () 1 (by decide) (by intro r; cases r; decide)
        (by decide) (by decide) (by decide) ?_ (by decide) (by decide))
    · exact Reach.tail h12 (Step.run _ () 0 () (by decide) (by decide) (by decide))
    · intro r g hg; cases r
      have hs : s11.seen () = some (some 1) := by decide
      rw [hs] at hg; cases hg; decide
  · intro hs
    have hf := (hs.1 ()).2 () (by decide)
    have : s13.cfreed () = true := by decide
    rw [this] at hf; cases hf

theorem late_detach_unsafe : ∃ s, Reach lateDetach unitInit s ∧ ¬ Safe s := by
  let s1 : St Unit Bool Unit := { prepared with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Unit :=
    { s1 with erased := upd s1.erased () (some 1), cl_erased := upd s1.cl_erased () true }
  let s3 : St Unit Bool Unit := { s2 with wp := .detached }
  let s4 : St Unit Bool Unit := { s3 with G := 1, lock := .free, wp := .late }
  let s5 := s4.setR () { pc := .stamped, gen := 1 }
  let s6 := s5.setR () { s5.rd () with pc := .running, code := some 0 }
  let s7 := s6.writerDetach .idle
  let s8 : St Unit Bool Unit := { s7 with lock := .writer, wp := .marking }
  let s9 : St Unit Bool Unit := { s8 with wp := .detached }
  let s10 : St Unit Bool Unit := { s9 with G := 2, lock := .free, wp := .late }
  let s11 := s10.writerDetach .idle
  let s12 : St Unit Bool Unit :=
    { s11 with gpc := .scanning, start := 2, seen := fun _ => none }
  let s13 : St Unit Bool Unit := { s12 with seen := upd s12.seen () (some (some 1)) }
  let s14 : St Unit Bool Unit := { s13 with cfreed := upd s13.cfreed () true }
  let s15 := s14.setR () { s14.rd () with run := some () }
  refine ⟨s15, ?_, ?_⟩
  · have h1 : Reach lateDetach unitInit s1 :=
      Reach.tail (prepared_reach _) (Step.writerLock _ (by decide) (by decide))
    have h2 : Reach lateDetach unitInit s2 :=
      Reach.tail h1 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
    have h3 : Reach lateDetach unitInit s3 :=
      Reach.tail h2 (Step.skipDetach _ (by decide) (by decide) (by decide))
    have h4 : Reach lateDetach unitInit s4 :=
      Reach.tail h3 (Step.publish _ (by decide) (by decide))
    have h5 : Reach lateDetach unitInit s5 := Reach.tail h4 (Step.stamp _ () (by decide))
    have h6 : Reach lateDetach unitInit s6 :=
      Reach.tail h5 (Step.readSlot _ () 0 (by decide) (by decide))
    have h7 : Reach lateDetach unitInit s7 :=
      Reach.tail h6 (Step.lateDetach _ rfl (by decide))
    have h8 : Reach lateDetach unitInit s8 :=
      Reach.tail h7 (Step.writerLock _ (by decide) (by decide))
    have h9 : Reach lateDetach unitInit s9 :=
      Reach.tail h8 (Step.skipDetach _ (by decide) (by decide) (by decide))
    have h10 : Reach lateDetach unitInit s10 :=
      Reach.tail h9 (Step.publish _ (by decide) (by decide))
    have h11 : Reach lateDetach unitInit s11 :=
      Reach.tail h10 (Step.lateDetach _ rfl (by decide))
    have h12 : Reach lateDetach unitInit s12 := Reach.tail h11 (Step.gcStart _ (by decide))
    have h13 : Reach lateDetach unitInit s13 :=
      Reach.tail h12 (Step.gcScan _ () (by decide) (by decide))
    have h14 : Reach lateDetach unitInit s14 :=
      Reach.tail h13 (Step.freeClause _ () 1 (by decide) (by intro r; cases r; decide)
        (by decide) (by decide) (by decide) ?_ (by decide) (by decide))
    · exact Reach.tail h14 (Step.run _ () 0 () (by decide) (by decide) (by decide))
    · intro r g hg; cases r
      have hs : s13.seen () = some (some 1) := by decide
      rw [hs] at hg; cases hg; decide
  · intro hs
    have hf := (hs.1 ()).2 () (by decide)
    have : s15.cfreed () = true := by decide
    rw [this] at hf; cases hf

/-- The creator collects while live, the writer erases and detaches, and the
creator installs its now-erased operand. Its hold prevents early reclamation
but is released before the unsafe reader and GC run. -/
theorem unvalidated_install_unsafe : ∃ s, Reach unvalidated unitInit s ∧ ¬ Safe s := by
  let s1 : St Unit Bool Unit :=
    { unitInit with cr := { pc := .scanning, old := none, holds := true } }
  let s2 : St Unit Bool Unit := { s1 with cr := { s1.cr with found := [()] } }
  let s3 := s2.allocate
  let s4 : St Unit Bool Unit := { s3 with lock := .writer, wp := .marking }
  let s5 : St Unit Bool Unit :=
    { s4 with erased := upd s4.erased () (some 1), cl_erased := upd s4.cl_erased () true }
  let s6 := s5.writerDetach .detached
  let s7 : St Unit Bool Unit := { s6 with G := 1, lock := .free, wp := .idle }
  let s8 : St Unit Bool Unit :=
    { s7 with lock := .creator, cr := { s7.cr with pc := .checking } }
  let s9 := s8.installed
  let s10 := s9.creatorDone
  let s11 := s10.setR () { pc := .stamped, gen := 1 }
  let s12 := s11.setR () { s11.rd () with pc := .running, code := some 0 }
  let s13 : St Unit Bool Unit := { s12 with lock := .writer, wp := .marking }
  let s14 := s13.writerDetach .detached
  let s15 : St Unit Bool Unit := { s14 with G := 2, lock := .free, wp := .idle }
  let s16 : St Unit Bool Unit :=
    { s15 with gpc := .scanning, start := 2, seen := fun _ => none }
  let s17 : St Unit Bool Unit := { s16 with seen := upd s16.seen () (some (some 1)) }
  let s18 : St Unit Bool Unit := { s17 with cfreed := upd s17.cfreed () true }
  let s19 := s18.setR () { s18.rd () with run := some () }
  refine ⟨s19, ?_, ?_⟩
  · have h1 : Reach unvalidated unitInit s1 :=
      Reach.tail (.refl _) (Step.creatorRead _ (by decide))
    have h2 : Reach unvalidated unitInit s2 :=
      Reach.tail h1 (Step.scanClause _ () (by decide) (by decide))
    have h3 : Reach unvalidated unitInit s3 := Reach.tail h2 (Step.allocate _ (by decide))
    have h4 : Reach unvalidated unitInit s4 :=
      Reach.tail h3 (Step.writerLock _ (by decide) (by decide))
    have h5 : Reach unvalidated unitInit s5 :=
      Reach.tail h4 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
    have h6 : Reach unvalidated unitInit s6 :=
      Reach.tail h5 (Step.writerDetach _ rfl (by decide) (by decide))
    have h7 : Reach unvalidated unitInit s7 :=
      Reach.tail h6 (Step.publish _ (by decide) (by decide))
    have h8 : Reach unvalidated unitInit s8 :=
      Reach.tail h7 (Step.creatorLock _ (by decide) (by decide))
    have h9 : Reach unvalidated unitInit s9 :=
      Reach.tail h8 (Step.install _ (by decide) (by decide)
        (by intro h; cases h) (by intro _; decide))
    have h10 : Reach unvalidated unitInit s10 :=
      Reach.tail h9 (Step.creatorLinger _ (by decide))
    have h11 : Reach unvalidated unitInit s11 := Reach.tail h10 (Step.stamp _ () (by decide))
    have h12 : Reach unvalidated unitInit s12 :=
      Reach.tail h11 (Step.readSlot _ () 0 (by decide) (by decide))
    have h13 : Reach unvalidated unitInit s13 :=
      Reach.tail h12 (Step.writerLock _ (by decide) (by decide))
    have h14 : Reach unvalidated unitInit s14 :=
      Reach.tail h13 (Step.writerDetach _ rfl (by decide) (by decide))
    have h15 : Reach unvalidated unitInit s15 :=
      Reach.tail h14 (Step.publish _ (by decide) (by decide))
    have h16 : Reach unvalidated unitInit s16 := Reach.tail h15 (Step.gcStart _ (by decide))
    have h17 : Reach unvalidated unitInit s17 :=
      Reach.tail h16 (Step.gcScan _ () (by decide) (by decide))
    have h18 : Reach unvalidated unitInit s18 :=
      Reach.tail h17 (Step.freeClause _ () 1 (by decide) (by intro r; cases r; decide)
        (by decide) (by decide) (by decide) ?_ (by decide) (by decide))
    · exact Reach.tail h18 (Step.run _ () 0 () (by decide) (by decide) (by decide))
    · intro r g hg; cases r
      have hs : s17.seen () = some (some 1) := by decide
      rw [hs] at hg; cases hg; decide
  · intro hs
    have hf := (hs.1 ()).2 () (by decide)
    have : s19.cfreed () = true := by decide
    rw [this] at hf; cases hf

theorem plain_swap_unsafe : ∃ s, Reach plainSwap unitInit s ∧ ¬ Safe s := by
  let s1 := prepared.setD false { pc := .loaded, old := some 0 }
  let s2 := s1.setD true { pc := .loaded, old := some 0 }
  let s3 := s2.detacherSwap false
  let s4 := s3.detacherSwap true
  let s5 := s4.detacherDone false
  let s6 := s5.detacherDone true
  refine ⟨s6, ?_, ?_⟩
  · have h1 : Reach plainSwap unitInit s1 :=
      Reach.tail (prepared_reach _) (Step.detacherRead _ false (by decide))
    have h2 : Reach plainSwap unitInit s2 :=
      Reach.tail h1 (Step.detacherRead _ true (by decide))
    have h3 : Reach plainSwap unitInit s3 :=
      Reach.tail h2 (Step.detacherCas _ false (by decide) (by intro h; cases h))
    have h4 : Reach plainSwap unitInit s4 :=
      Reach.tail h3 (Step.detacherCas _ true (by decide) (by intro h; cases h))
    have h5 : Reach plainSwap unitInit s5 :=
      Reach.tail h4 (Step.detacherLinger _ false (by decide))
    exact Reach.tail h5 (Step.detacherLinger _ true (by decide))
  · intro hs
    have hf := hs.2.2.1
    have : s6.dup = true := by decide
    rw [this] at hf; cases hf

/-- Without the outer acquire_def2(), GC frees the operand retained by the
creator. Taking L_GENERATION afterwards does not make that operand live:
embedsErasedClause() is about to dereference reclaimed memory. -/
theorem no_hold_unsafe : ∃ s, Reach noHold unitInit s ∧ ¬ Safe s := by
  let s1 : St Unit Bool Unit :=
    { unitInit with cr := { pc := .scanning, old := none, holds := false } }
  let s2 : St Unit Bool Unit := { s1 with cr := { s1.cr with found := [()] } }
  let s3 := s2.allocate
  let s4 : St Unit Bool Unit := { s3 with lock := .writer, wp := .marking }
  let s5 : St Unit Bool Unit :=
    { s4 with erased := upd s4.erased () (some 1), cl_erased := upd s4.cl_erased () true }
  let s6 := s5.writerDetach .detached
  let s7 : St Unit Bool Unit := { s6 with G := 1, lock := .free, wp := .idle }
  let s8 : St Unit Bool Unit := { s7 with lock := .writer, wp := .marking }
  let s9 := s8.writerDetach .detached
  let s10 : St Unit Bool Unit := { s9 with G := 2, lock := .free, wp := .idle }
  let s11 : St Unit Bool Unit :=
    { s10 with gpc := .scanning, start := 2, seen := fun _ => none }
  let s12 : St Unit Bool Unit := { s11 with seen := upd s11.seen () (some none) }
  let s13 : St Unit Bool Unit := { s12 with cfreed := upd s12.cfreed () true }
  let s14 : St Unit Bool Unit :=
    { s13 with lock := .creator, cr := { s13.cr with pc := .checking } }
  refine ⟨s14, ?_, ?_⟩
  · have h1 : Reach noHold unitInit s1 :=
      Reach.tail (.refl _) (Step.creatorRead _ (by decide))
    have h2 : Reach noHold unitInit s2 :=
      Reach.tail h1 (Step.scanClause _ () (by decide) (by decide))
    have h3 : Reach noHold unitInit s3 := Reach.tail h2 (Step.allocate _ (by decide))
    have h4 : Reach noHold unitInit s4 :=
      Reach.tail h3 (Step.writerLock _ (by decide) (by decide))
    have h5 : Reach noHold unitInit s5 :=
      Reach.tail h4 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
    have h6 : Reach noHold unitInit s6 :=
      Reach.tail h5 (Step.writerDetach _ rfl (by decide) (by decide))
    have h7 : Reach noHold unitInit s7 :=
      Reach.tail h6 (Step.publish _ (by decide) (by decide))
    have h8 : Reach noHold unitInit s8 :=
      Reach.tail h7 (Step.writerLock _ (by decide) (by decide))
    have h9 : Reach noHold unitInit s9 :=
      Reach.tail h8 (Step.writerDetach _ rfl (by decide) (by decide))
    have h10 : Reach noHold unitInit s10 :=
      Reach.tail h9 (Step.publish _ (by decide) (by decide))
    have h11 : Reach noHold unitInit s11 := Reach.tail h10 (Step.gcStart _ (by decide))
    have h12 : Reach noHold unitInit s12 :=
      Reach.tail h11 (Step.gcScan _ () (by decide) (by decide))
    have h13 : Reach noHold unitInit s13 :=
      Reach.tail h12 (Step.freeClause _ () 1 (by decide) (by intro r; cases r; decide)
        (by decide) (by decide) (by decide) ?_ (by decide) (by decide))
    · exact Reach.tail h13 (Step.creatorLock _ (by decide) (by decide))
    · intro r g hg; cases r
      have hs : s12.seen () = some none := by decide
      rw [hs] at hg; cases hg
  · intro hs
    have hf := hs.2.1 (by decide) () (by decide)
    have : s14.cfreed () = true := by decide
    rw [this] at hf; cases hf

#print axioms initial_init
#print axioms init_init
#print axioms fixed_birth_gap
#print axioms fixed_unsafe
#print axioms not_fixed_safe
#print axioms unitInit_init
#print axioms prepared_reach
#print axioms no_detach_unsafe
#print axioms late_detach_unsafe
#print axioms unvalidated_install_unsafe
#print axioms plain_swap_unsafe
#print axioms no_hold_unsafe

end Mettapedia.Languages.Prolog.SWI.Supervisor.V1
