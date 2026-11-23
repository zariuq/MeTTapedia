import Mettapedia.Languages.Prolog.SWI.SupervisorV1

set_option linter.unusedSectionVars false

/-! ## Supervisor-owned ClauseRefs (65455ce through 8f7019a)

The list reference and each unfreed owning version contribute to a clause's
lifetime. `cfreed` is derived from absence of both kinds of reference. Thus
unlinking a list reference need not free the clause, and freeing a version can
free its operands. No reader transition tests visibility or allocation.
-/

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd DetachMode Lock RPc Reader DPc Detacher WPc GPc)

structure Proto where
  detach : DetachMode
  validate : Bool
  cas : Bool
  hold : Bool
  own : Bool

def fixed : Proto := ⟨.inSection, true, true, true, true⟩
def noOwn : Proto := { fixed with own := false }
def noDetach : Proto := { fixed with detach := .none }
def lateDetach : Proto := { fixed with detach := .afterPublish }
def unvalidated : Proto := { fixed with validate := false }
def plainSwap : Proto := { fixed with cas := false }
def noHold : Proto := { fixed with hold := false }

inductive CPc where
  | idle | scanning | building | ready | checking | lingering
  deriving DecidableEq

def CPc.prototype : CPc → Bool
  | .ready | .checking => true
  | _ => false

def CPc.borrowed : CPc → Bool
  | .scanning | .building => true
  | _ => false

structure Creator (K : Type) where
  pc : CPc := .idle
  old : Option Nat := none
  found : List K := []
  ver : Nat := 0
  holds : Bool := false

structure St (R D K : Type) where
  G : Nat
  born : K → Nat
  erased : K → Option Nat
  cl_erased : K → Bool
  /-- The clause-list ClauseRef has not been dropped. -/
  linked : K → Bool
  embeds : Nat → List K
  /-- This version was built with its own ClauseRefs. -/
  owned : Nat → Bool
  next : Nat
  vfreed : Nat → Bool
  slot : Option Nat
  lingered : Nat → Option Nat
  dup : Bool
  lock : Lock
  wp : WPc
  cr : Creator K
  rd : R → Reader K
  dt : D → Detacher
  gpc : GPc
  start : Nat
  seen : R → Option (Option Nat)

variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

def St.visAt (s : St R D K) (k : K) (g : Nat) : Prop :=
  s.born k ≤ g ∧ ∀ e, s.erased k = some e → g < e

instance (s : St R D K) (k : K) (g : Nat) : Decidable (s.visAt k g) :=
  match he : s.erased k with
  | none => decidable_of_iff (s.born k ≤ g) (by simp [St.visAt, he])
  | some e => decidable_of_iff (s.born k ≤ g ∧ g < e) (by simp [St.visAt, he])

def St.hasOwner (s : St R D K) (k : K) : Bool :=
  (List.range s.next).any fun v => s.owned v && !s.vfreed v && decide (k ∈ s.embeds v)

/-- Last-reference reclamation, not generation-based clause liveness. -/
def St.cfreed (s : St R D K) (k : K) : Bool := !(s.linked k || s.hasOwner k)

def St.touches (s : St R D K) : List K :=
  if s.cr.pc.borrowed then s.cr.found
  else if s.cr.pc.prototype then s.embeds s.cr.ver else []

def St.setR (s : St R D K) (r : R) (x : Reader K) : St R D K :=
  { s with rd := upd s.rd r x }

def St.setD (s : St R D K) (d : D) (x : Detacher) : St R D K :=
  { s with dt := upd s.dt d x }

def St.linger (s : St R D K) : Option Nat → St R D K
  | none => s
  | some v => { s with lingered := upd s.lingered v (some s.G),
                        dup := s.dup || (s.lingered v).isSome }

def St.writerDetach (s : St R D K) (pc : WPc) : St R D K :=
  ({ s with slot := none, wp := pc }).linger s.slot

def St.allocate (s : St R D K) (P : Proto) : St R D K :=
  { s with embeds := upd s.embeds s.next s.cr.found,
           owned := upd s.owned s.next P.own,
           vfreed := upd s.vfreed s.next false,
           lingered := upd s.lingered s.next none, next := s.next + 1,
           cr := { s.cr with pc := .ready, ver := s.next, holds := false } }

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
  | stamp (s : St R D K) (r : R) (h : (s.rd r).pc = .idle) :
      Step P s (s.setR r { pc := .stamped, gen := s.G })
  | readSlot (s : St R D K) (r : R) (v : Nat)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = some v) :
      Step P s (s.setR r { s.rd r with pc := .running, code := some v })
  | wait (s : St R D K) (r : R)
      (h : (s.rd r).pc = .stamped) (hv : s.slot = none) : Step P s s
  | run (s : St R D K) (r : R) (v : Nat) (k : K)
      (h : (s.rd r).pc = .running) (hv : (s.rd r).code = some v)
      (hk : k ∈ s.embeds v) :
      Step P s (s.setR r { s.rd r with run := some k })
  | exit (s : St R D K) (r : R) (h : (s.rd r).pc ≠ .idle) :
      Step P s (s.setR r {})
  | writerLock (s : St R D K) (h : s.lock = .free) (hw : s.wp = .idle) :
      Step P s { s with lock := .writer, wp := .marking }
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
  /-- getClauses() has its own acquire_def2(), even in the no-outer-hold mutant. -/
  | creatorRead (s : St R D K) (h : s.cr.pc = .idle) :
      Step P s { s with cr := { pc := .scanning, old := s.slot, holds := true } }
  | scanClause (s : St R D K) (k : K) (h : s.cr.pc = .scanning)
      (hk : s.visAt k s.G) :
      Step P s { s with cr := { s.cr with found := s.cr.found ++ [k] } }
  /-- getClauses() returned; the outer hold covers the build/ownClause window. -/
  | finishScan (s : St R D K) (h : s.cr.pc = .scanning) :
      Step P s { s with cr := { s.cr with pc := .building, holds := P.hold } }
  /-- ownClause() while protected, then release_def2(); no hold at validation. -/
  | allocate (s : St R D K) (h : s.cr.pc = .building) : Step P s (s.allocate P)
  | creatorLock (s : St R D K) (h : s.lock = .free) (hc : s.cr.pc = .ready) :
      Step P s { s with lock := .creator, cr := { s.cr with pc := .checking } }
  | install (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hv : P.validate = true → ∀ k ∈ s.embeds s.cr.ver, s.cl_erased k = false)
      (hs : P.cas = true → s.slot = s.cr.old) : Step P s s.installed
  | retry (s : St R D K) (h : s.lock = .creator) (hc : s.cr.pc = .checking)
      (hf : (P.validate = true ∧ ∃ k ∈ s.embeds s.cr.ver, s.cl_erased k = true) ∨
            (P.cas = true ∧ s.slot ≠ s.cr.old)) :
      Step P s { s with lock := .free, cr := {}, vfreed := upd s.vfreed s.cr.ver true }
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
  /-- cleanDefinition() and gcClauseRefs() drop the list's reference only. -/
  | unlink (s : St R D K) (k : K) (e : Nat) (h : s.gpc = .scanning)
      (hall : ∀ r, s.seen r ≠ none) (he : s.erased k = some e)
      (hf : s.cl_erased k = true) (hlt : e < s.start)
      (hinv : ∀ r g, s.seen r = some (some g) → ¬ s.visAt k g)
      (hh : s.cr.holds = false) (hlist : s.linked k = true) :
      Step P s { s with linked := upd s.linked k false }
  /-- Releases every ClauseRef owned by the reclaimed supervisor version. -/
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
  (∀ k, s.erased k = none ∧ s.cl_erased k = false ∧ s.linked k = true) ∧
  (∀ v, s.embeds v = [] ∧ s.owned v = false ∧ s.vfreed v = false ∧ s.lingered v = none)

def Mem (s : St R D K) : Prop :=
  (∀ r, (∀ v, (s.rd r).code = some v → s.vfreed v = false) ∧
        (∀ k, (s.rd r).run = some k → s.cfreed k = false)) ∧
  (∀ k ∈ s.touches, s.cfreed k = false) ∧ s.dup = false ∧
  (∀ v, s.slot = some v → s.lingered v = none ∧ s.vfreed v = false)

def LudErase (s : St R D K) : Prop :=
  ∀ r k e, (s.rd r).run = some k → s.erased k = some e → (s.rd r).gen < e

/-! Reserved versions: a slot, a prototype, or a successful swap awaiting linger.
These are derived from program control. They are not transition preconditions. -/

inductive Loc (D : Type) where
  | slot | prototype | creator | detacher (d : D)
  deriving DecidableEq

def St.root (s : St R D K) : Loc D → Option Nat
  | .slot => s.slot
  | .prototype => if s.cr.pc.prototype then some s.cr.ver else none
  | .creator => if s.cr.pc = .lingering then s.cr.old else none
  | .detacher d => if (s.dt d).pc = .lingering then (s.dt d).old else none

structure Roots (f : Loc D → Option Nat) (n : Nat) (dead : Nat → Option Nat)
    (freed : Nat → Bool) : Prop where
  unique : ∀ a b v, f a = some v → f b = some v → a = b
  clean : ∀ a v, f a = some v → v < n ∧ dead v = none ∧ freed v = false

abbrev RootInv (s : St R D K) := Roots s.root s.next s.lingered s.vfreed

structure RInv (s : St R D K) (x : Reader K) : Prop where
  gen_le : x.gen ≤ s.G
  code_bound : ∀ v, x.code = some v → v < s.next
  code_proto : ∀ v, x.code = some v → s.root .prototype ≠ some v
  code_live : ∀ v, x.code = some v → s.vfreed v = false
  retired : ∀ v d, x.code = some v → s.lingered v = some d → x.gen ≤ d
  selected : ∀ k, x.run = some k → ∃ v, x.code = some v ∧ k ∈ s.embeds v
  code_pc : ∀ v, x.code = some v → x.pc = .running

structure Inv (s : St R D K) : Prop where
  roots : RootInv s
  start_le : s.start ≤ s.G
  flag : ∀ k, s.cl_erased k = false ↔ s.erased k = none
  unlinked_old : ∀ k, s.linked k = false → ∃ e, s.erased k = some e ∧ e < s.G
  borrowed_hold : s.cr.pc.borrowed = true → s.cr.holds = true
  borrowed_list : s.cr.pc.borrowed = true → ∀ k ∈ s.cr.found, s.linked k = true
  owned : ∀ v, v < s.next → s.owned v = true
  rd : ∀ r, RInv s (s.rd r)
  scanned : ∀ r, s.gpc = .scanning → s.seen r ≠ none → (s.rd r).pc ≠ .idle →
    s.start ≤ (s.rd r).gen ∨ s.seen r = some (some (s.rd r).gen)
  nodup : s.dup = false

structure EInv (s : St R D K) : Prop where
  writer : s.lock = .writer ↔ s.wp = .marking ∨ s.wp = .detached
  creator : s.lock = .creator ↔ s.cr.pc = .checking
  detached : s.wp = .detached → s.slot = none
  slot : ∀ v k e, s.slot = some v → k ∈ s.embeds v → s.erased k = some e → s.G < e
  reader : ∀ r v k e, (s.rd r).code = some v → k ∈ s.embeds v →
    s.erased k = some e → (s.rd r).gen < e

/-- An unfreed owning version keeps every embedded clause alive. -/
theorem owner_live {s : St R D K} {v : Nat} {k : K} (hb : v < s.next)
    (ho : s.owned v = true) (hf : s.vfreed v = false) (hk : k ∈ s.embeds v) :
    s.cfreed k = false := by
  have h : s.hasOwner k = true := by
    apply List.any_eq_true.mpr
    exact ⟨v, List.mem_range.mpr hb, by simp [ho, hf, hk]⟩
  simp [St.cfreed, h]

theorem linked_live {s : St R D K} {k : K} (hk : s.linked k = true) :
    s.cfreed k = false := by simp [St.cfreed, hk]

theorem Inv.mem {s : St R D K} (h : Inv s) : Mem s := by
  refine ⟨?_, ?_, h.nodup, ?_⟩
  · intro r
    refine ⟨(h.rd r).code_live, ?_⟩
    intro k hk
    obtain ⟨v, hv, he⟩ := (h.rd r).selected k hk
    exact owner_live ((h.rd r).code_bound v hv) (h.owned v ((h.rd r).code_bound v hv))
      ((h.rd r).code_live v hv) he
  · intro k hk
    unfold St.touches at hk
    split at hk
    · exact linked_live (h.borrowed_list (by assumption) k hk)
    · split at hk
      · have hr : s.root .prototype = some s.cr.ver := by simp [St.root, *]
        obtain ⟨hb, _, hf⟩ := h.roots.clean .prototype s.cr.ver hr
        exact owner_live hb (h.owned _ hb) hf hk
      · simp at hk
  · intro v hv
    exact (h.roots.clean .slot v hv).2

theorem EInv.lud {s : St R D K} (h : Inv s) (he : EInv s) : LudErase s := by
  intro r k e hk hd
  obtain ⟨v, hv, hm⟩ := (h.rd r).selected k hk
  exact he.reader r v k e hv hm hd

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd)

variable {D : Type} [DecidableEq D]

/-- Moving a reservation to an empty location is a permutation of locations. -/
def swapLoc (a b x : Loc D) : Loc D := if x = a then b else if x = b then a else x

theorem swapLoc_twice (a b x : Loc D) : swapLoc a b (swapLoc a b x) = x := by
  by_cases ha : x = a
  · subst x
    by_cases hab : a = b
    · subst b; simp [swapLoc]
    · simp [swapLoc, Ne.symm hab]
  · by_cases hb : x = b
    · subst x; simp [swapLoc, ha]
    · simp [swapLoc, ha, hb]

variable {f : Loc D → Option Nat} {n : Nat} {dead : Nat → Option Nat} {freed : Nat → Bool}

theorem Roots.permute (h : Roots f n dead freed) (a b : Loc D) :
    Roots (fun x => f (swapLoc a b x)) n dead freed where
  unique := by
    intro x y v hx hy
    have he := h.unique _ _ v hx hy
    have hh := congrArg (swapLoc a b) he
    simpa only [swapLoc_twice] using hh
  clean := fun x v hx => h.clean _ v hx

theorem clear_back {a x : Loc D} {v : Nat} (hx : upd f a none x = some v) :
    x ≠ a ∧ f x = some v := by
  by_cases hxa : x = a
  · subst x; simp [upd] at hx
  · exact ⟨hxa, by simpa [upd, hxa] using hx⟩

theorem Roots.clear (h : Roots f n dead freed) (a : Loc D) :
    Roots (upd f a none) n dead freed where
  unique := fun x y v hx hy => h.unique x y v (clear_back hx).2 (clear_back hy).2
  clean := fun x v hx => h.clean x v (clear_back hx).2

theorem Roots.retire (h : Roots f n dead freed) {a : Loc D} {v : Nat}
    (ha : f a = some v) (d : Nat) :
    Roots (upd f a none) n (upd dead v (some d)) freed where
  unique := (h.clear a).unique
  clean := by
    intro x w hx
    obtain ⟨hxa, hx0⟩ := clear_back hx
    obtain ⟨hb, hd, hf⟩ := h.clean x w hx0
    have hw : w ≠ v := by
      intro hw; subst w
      exact hxa (h.unique x a v hx0 ha)
    exact ⟨hb, by simpa [upd, hw] using hd, hf⟩

theorem Roots.release (h : Roots f n dead freed) {a : Loc D} {v : Nat}
    (ha : f a = some v) :
    Roots (upd f a none) n dead (upd freed v true) where
  unique := (h.clear a).unique
  clean := by
    intro x w hx
    obtain ⟨hxa, hx0⟩ := clear_back hx
    obtain ⟨hb, hd, hf⟩ := h.clean x w hx0
    have hw : w ≠ v := by
      intro hw; subst w
      exact hxa (h.unique x a v hx0 ha)
    exact ⟨hb, hd, by simpa [upd, hw] using hf⟩

theorem Roots.free_lingering (h : Roots f n dead freed) {v d : Nat}
    (hd : dead v = some d) : Roots f n dead (upd freed v true) where
  unique := h.unique
  clean := by
    intro x w hx
    obtain ⟨hb, hw, hf⟩ := h.clean x w hx
    have hne : w ≠ v := by intro he; subst w; rw [hd] at hw; cases hw
    exact ⟨hb, hw, by simpa [upd, hne] using hf⟩

theorem Roots.allocate (h : Roots f n dead freed) (a : Loc D) :
    Roots (upd f a (some n)) (n+1) (upd dead n none) (upd freed n false) where
  unique := by
    intro x y v hx hy
    by_cases hxa : x = a
    · subst x
      have hv : n = v := by simpa [upd] using hx
      by_cases hya : y = a
      · exact hya.symm
      · have hy0 : f y = some v := by simpa [upd, hya] using hy
        have := (h.clean y v hy0).1
        omega
    · have hx0 : f x = some v := by simpa [upd, hxa] using hx
      by_cases hya : y = a
      · subst y
        have hv : n = v := by simpa [upd] using hy
        have := (h.clean x v hx0).1
        omega
      · exact h.unique x y v hx0 (by simpa [upd, hya] using hy)
  clean := by
    intro x v hx
    by_cases hxa : x = a
    · subst x
      have hv : n = v := by simpa [upd] using hx
      subst v
      exact ⟨Nat.lt_succ_self _, by simp [upd], by simp [upd]⟩
    · have hx0 : f x = some v := by simpa [upd, hxa] using hx
      obtain ⟨hb, hd, hf⟩ := h.clean x v hx0
      have hne : v ≠ n := by omega
      exact ⟨by omega, by simpa [upd, hne] using hd, by simpa [upd, hne] using hf⟩

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd)

variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

def deadAt (dead : Nat → Option Nat) (old : Option Nat) (g : Nat) : Nat → Option Nat :=
  match old with
  | none => dead
  | some v => upd dead v (some g)

theorem roots_cast {f g : Loc D → Option Nat} {n m : Nat}
    {dead dead' : Nat → Option Nat} {freed freed' : Nat → Bool}
    (h : Roots f n dead freed) (hf : g = f) (hn : m = n)
    (hd : dead' = dead) (hv : freed' = freed) : Roots g m dead' freed' := by
  rw [hf, hn, hd, hv]
  exact h

theorem Roots.retire_opt {f : Loc D → Option Nat} {n : Nat}
    {dead : Nat → Option Nat} {freed : Nat → Bool}
    (h : Roots f n dead freed) (a : Loc D) (d : Nat) :
    Roots (upd f a none) n (deadAt dead (f a) d) freed := by
  cases ha : f a with
  | none => simpa [deadAt, ha] using h.clear a
  | some v => simpa [deadAt, ha] using h.retire ha d

@[simp] theorem root_linger (s : St R D K) (old : Option Nat) :
    (s.linger old).root = s.root := by cases old <;> rfl

@[simp] theorem next_linger (s : St R D K) (old : Option Nat) :
    (s.linger old).next = s.next := by cases old <;> rfl

@[simp] theorem freed_linger (s : St R D K) (old : Option Nat) :
    (s.linger old).vfreed = s.vfreed := by cases old <;> rfl

@[simp] theorem dead_linger (s : St R D K) (old : Option Nat) :
    (s.linger old).lingered = deadAt s.lingered old s.G := by cases old <;> rfl

theorem roots_writerDetach {s : St R D K} (h : RootInv s) (pc : V1.WPc) :
    RootInv (s.writerDetach pc) := by
  have hr : (s.writerDetach pc).root = upd s.root .slot none := by
    rw [St.writerDetach, root_linger]
    funext l
    cases l <;> simp [St.root, upd]
  apply roots_cast (h.retire_opt .slot s.G) hr
  · simp [St.writerDetach]
  · simp [St.writerDetach, St.root]
  · simp [St.writerDetach]

theorem roots_creatorDone {s : St R D K} (h : RootInv s) (hc : s.cr.pc = .lingering) :
    RootInv s.creatorDone := by
  have hr : s.creatorDone.root = upd s.root .creator none := by
    funext l
    cases old : s.cr.old <;> cases l <;>
      simp [St.creatorDone, St.linger, St.root, upd, hc, CPc.prototype, old]
  have ho : s.root .creator = s.cr.old := by simp [St.root, hc]
  apply roots_cast (h.retire_opt .creator s.G) hr
  · cases old : s.cr.old <;> simp [St.creatorDone, St.linger, old]
  · simp [St.creatorDone, ho]
  · cases old : s.cr.old <;> simp [St.creatorDone, St.linger, old]

theorem roots_allocate {s : St R D K} (h : RootInv s) (P : Proto)
    (hc : s.cr.pc = .building) : RootInv (s.allocate P) := by
  have hr : (s.allocate P).root = upd s.root .prototype (some s.next) := by
    funext l
    cases l <;> simp [St.root, St.allocate, upd, hc, CPc.prototype] <;> rfl
  exact roots_cast (h.allocate .prototype) hr rfl rfl rfl

theorem roots_installed {s : St R D K} (h : RootInv s)
    (hc : s.cr.pc = .checking) (hs : s.slot = s.cr.old) : RootInv s.installed := by
  have hr : s.installed.root = fun l =>
      s.root (swapLoc .slot .creator (swapLoc .prototype .slot l)) := by
    funext l
    cases l <;> simp [St.root, St.installed, hc, CPc.prototype, swapLoc, hs] <;> rfl
  exact roots_cast ((h.permute .slot .creator).permute .prototype .slot) hr rfl rfl rfl

theorem roots_retry {s : St R D K} (h : RootInv s) (hc : s.cr.pc = .checking) :
    RootInv { s with lock := .free, cr := {}, vfreed := upd s.vfreed s.cr.ver true } := by
  have hp : s.root .prototype = some s.cr.ver := by simp [St.root, hc, CPc.prototype]
  have hr : ({ s with lock := .free, cr := {}, vfreed := upd s.vfreed s.cr.ver true } : St R D K).root =
      upd s.root .prototype none := by
    funext l
    cases l <;> simp [St.root, upd, hc, CPc.prototype]
  exact roots_cast (h.release hp) hr rfl rfl rfl

theorem root_setD_inactive (s : St R D K) (d : D) (x : V1.Detacher)
    (ho : (s.dt d).pc ≠ .lingering) (hn : x.pc ≠ .lingering) :
    (s.setD d x).root = s.root := by
  funext l
  cases l with
  | slot => rfl
  | prototype => rfl
  | creator => rfl
  | detacher e =>
    by_cases he : e = d
    · subst e; simp [St.setD, St.root, upd, ho, hn]
    · simp [St.setD, St.root, upd, he]

theorem roots_detacherSwap {s : St R D K} (h : RootInv s) (d : D)
    (hc : (s.dt d).pc = .loaded) (hs : s.slot = (s.dt d).old) :
    RootInv (s.detacherSwap d) := by
  have hr : (s.detacherSwap d).root = fun l => s.root (swapLoc .slot (.detacher d) l) := by
    funext l
    cases l with
    | slot => simp [St.detacherSwap, St.setD, St.root, swapLoc, hc]
    | prototype => simp [St.detacherSwap, St.setD, St.root, swapLoc] <;> rfl
    | creator => simp [St.detacherSwap, St.setD, St.root, swapLoc] <;> rfl
    | detacher e =>
      by_cases he : e = d
      · subst e; simp [St.detacherSwap, St.setD, St.root, swapLoc, upd, hs]
      · simp [St.detacherSwap, St.setD, St.root, swapLoc, upd, he]
  exact roots_cast (h.permute .slot (.detacher d)) hr rfl rfl rfl

theorem roots_detacherDone {s : St R D K} (h : RootInv s) (d : D)
    (hc : (s.dt d).pc = .lingering) : RootInv (s.detacherDone d) := by
  have hr : (s.detacherDone d).root = upd s.root (.detacher d) none := by
    funext l
    cases old : (s.dt d).old <;> cases l with
    | slot => simp [St.detacherDone, St.setD, St.linger, St.root, upd, old]
    | prototype => simp [St.detacherDone, St.setD, St.linger, St.root, upd, old]
    | creator => simp [St.detacherDone, St.setD, St.linger, St.root, upd, old]
    | detacher e =>
      by_cases he : e = d
      · subst e; simp [St.detacherDone, St.setD, St.linger, St.root, upd, old]
      · simp [St.detacherDone, St.setD, St.linger, St.root, upd, old, he]
  have ho : s.root (.detacher d) = (s.dt d).old := by simp [St.root, hc]
  apply roots_cast (h.retire_opt (.detacher d) s.G) hr
  · cases old : (s.dt d).old <;> simp [St.detacherDone, St.setD, St.linger, old]
  · simp [St.detacherDone, St.setD, ho]
  · cases old : (s.dt d).old <;> simp [St.detacherDone, St.setD, St.linger, old]

/-- CAS is the only protocol flag required for unique supervisor ownership. -/
theorem step_roots {P : Proto} {s t : St R D K} (h : RootInv s) (hp : P.cas = true)
    (st : Step P s t) : RootInv t := by
  cases st with
  | stamp => exact h
  | readSlot => exact h
  | wait => exact h
  | run => exact h
  | exit => exact h
  | writerLock => exact h
  | mark => exact h
  | writerDetach _ _ _ => exact roots_writerDetach h _
  | skipDetach => exact h
  | publish => exact h
  | lateDetach _ _ => exact roots_writerDetach h _
  | creatorRead hc =>
    apply roots_cast h ?_ rfl rfl rfl
    funext l; cases l <;> simp [St.root, hc, CPc.prototype]
  | scanClause => exact h
  | finishScan hc =>
    apply roots_cast h ?_ rfl rfl rfl
    funext l; cases l <;> simp [St.root, hc, CPc.prototype]
  | allocate hc => exact roots_allocate h P hc
  | creatorLock _ hc =>
    apply roots_cast h ?_ rfl rfl rfl
    funext l; cases l <;> simp [St.root, hc, CPc.prototype]
  | install _ hc _ hs => exact roots_installed h hc (hs hp)
  | retry _ hc _ => exact roots_retry h hc
  | creatorLinger hc => exact roots_creatorDone h hc
  | detacherRead d hc =>
    exact roots_cast h (root_setD_inactive s d _ (by simp [hc]) (by simp)) rfl rfl rfl
  | detacherCas d hc hs => exact roots_detacherSwap h d hc (hs hp)
  | detacherRetry d _ hc _ =>
    exact roots_cast h (root_setD_inactive s d _ (by simp [hc]) (by simp)) rfl rfl rfl
  | detacherLinger d hc => exact roots_detacherDone h d hc
  | gcStart => exact h
  | gcScan => exact h
  | unlink => exact h
  | freeVersion v d _ _ hd _ _ _ => exact h.free_lingering hd
  | gcEnd => exact h

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

theorem rinv_empty (s : St R D K) : RInv s ({} : V1.Reader K) where
  gen_le := Nat.zero_le _
  code_bound := by intro v hv; cases hv
  code_proto := by intro v hv; cases hv
  code_live := by intro v hv; cases hv
  retired := by intro v d hv; cases hv
  selected := by intro k hk; cases hk
  code_pc := by intro v hv; cases hv

theorem init_roots {s : St R D K} (hi : Init s) : RootInv s := by
  obtain ⟨hs, _, _, _, _, hc, _, hd, _, _, _, _, _⟩ := hi
  have hn : ∀ l, s.root l = none := by
    intro l
    cases l with
    | slot => exact hs
    | prototype => simp [St.root, hc, CPc.prototype]
    | creator => simp [St.root, hc]
    | detacher d => simp [St.root, hd d]
  exact
    { unique := by intro a b v ha; rw [hn a] at ha; cases ha
      clean := by intro a v ha; rw [hn a] at ha; cases ha }

theorem init_inv {s : St R D K} (hi : Init s) : Inv s := by
  have hroots := init_roots hi
  obtain ⟨_, hn, hdup, _, _, hc, hr, _, hg, hstart, _, hcl, _⟩ := hi
  refine
    { roots := hroots
      start_le := hstart
      flag := ?_
      unlinked_old := ?_
      borrowed_hold := ?_
      borrowed_list := ?_
      owned := ?_
      rd := ?_
      scanned := ?_
      nodup := hdup }
  · intro k; rw [(hcl k).1, (hcl k).2.1]; simp
  · intro k hk; rw [(hcl k).2.2] at hk; cases hk
  · intro hb; simp [hc, CPc.borrowed] at hb
  · intro hb; simp [hc, CPc.borrowed] at hb
  · intro v hv; rw [hn] at hv; omega
  · intro r; rw [hr r]; exact rinv_empty s
  · intro r hscan; rw [hg] at hscan; cases hscan

theorem linger_nodup (s : St R D K) (old : Option Nat) (hd : s.dup = false)
    (hc : ∀ v, old = some v → s.lingered v = none) : (s.linger old).dup = false := by
  cases old with
  | none => exact hd
  | some v => simp [St.linger, hd, hc v rfl]

theorem step_nodup {P : Proto} {s t : St R D K} (h : RootInv s) (hd : s.dup = false)
    (st : Step P s t) : t.dup = false := by
  cases st with
  | stamp => exact hd
  | readSlot => exact hd
  | wait => exact hd
  | run => exact hd
  | exit => exact hd
  | writerLock => exact hd
  | mark => exact hd
  | writerDetach _ _ _ =>
    unfold St.writerDetach
    apply linger_nodup { s with slot := none, wp := .detached } s.slot hd
    intro v hv; exact (h.clean .slot v hv).2.1
  | skipDetach => exact hd
  | publish => exact hd
  | lateDetach _ _ =>
    unfold St.writerDetach
    apply linger_nodup { s with slot := none, wp := .idle } s.slot hd
    intro v hv; exact (h.clean .slot v hv).2.1
  | creatorRead => exact hd
  | scanClause => exact hd
  | finishScan => exact hd
  | allocate => exact hd
  | creatorLock => exact hd
  | install => exact hd
  | retry => exact hd
  | creatorLinger hc =>
    change (s.linger s.cr.old).dup = false
    apply linger_nodup _ _ hd
    intro v hv
    exact (h.clean .creator v (by simp [St.root, hc, hv])).2.1
  | detacherRead => exact hd
  | detacherCas => exact hd
  | detacherRetry => exact hd
  | detacherLinger d hc =>
    change (s.linger (s.dt d).old).dup = false
    apply linger_nodup _ _ hd
    intro v hv
    exact (h.clean (.detacher d) v (by simp [St.root, hc, hv])).2.1
  | gcStart => exact hd
  | gcScan => exact hd
  | unlink => exact hd
  | freeVersion => exact hd
  | gcEnd => exact hd

theorem reach_roots {P : Proto} {s0 s : St R D K} (hi : Init s0)
    (hp : P.cas = true) (hr : Reach P s0 s) : RootInv s ∧ s.dup = false := by
  induction hr with
  | refl => exact ⟨init_roots hi, hi.2.2.1⟩
  | tail _ st ih => exact ⟨step_roots ih.1 hp st, step_nodup ih.1 ih.2 st⟩

theorem cas_slot_safe {P : Proto} {s0 s : St R D K} (hi : Init s0)
    (hp : P.cas = true) (hr : Reach P s0 s) : s.dup = false ∧
    (∀ v, s.slot = some v → s.lingered v = none ∧ s.vfreed v = false) := by
  obtain ⟨h, hd⟩ := reach_roots hi hp hr
  exact ⟨hd, fun v hv => (h.clean .slot v hv).2⟩

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

@[simp] theorem linger_G (s : St R D K) (old : Option Nat) :
    (s.linger old).G = s.G := by cases old <;> rfl

@[simp] theorem linger_born (s : St R D K) (old : Option Nat) :
    (s.linger old).born = s.born := by cases old <;> rfl

@[simp] theorem linger_erased (s : St R D K) (old : Option Nat) :
    (s.linger old).erased = s.erased := by cases old <;> rfl

@[simp] theorem linger_cl_erased (s : St R D K) (old : Option Nat) :
    (s.linger old).cl_erased = s.cl_erased := by cases old <;> rfl

@[simp] theorem linger_linked (s : St R D K) (old : Option Nat) :
    (s.linger old).linked = s.linked := by cases old <;> rfl

@[simp] theorem linger_embeds (s : St R D K) (old : Option Nat) :
    (s.linger old).embeds = s.embeds := by cases old <;> rfl

@[simp] theorem linger_owned (s : St R D K) (old : Option Nat) :
    (s.linger old).owned = s.owned := by cases old <;> rfl

@[simp] theorem linger_slot (s : St R D K) (old : Option Nat) :
    (s.linger old).slot = s.slot := by cases old <;> rfl

@[simp] theorem linger_lock (s : St R D K) (old : Option Nat) :
    (s.linger old).lock = s.lock := by cases old <;> rfl

@[simp] theorem linger_wp (s : St R D K) (old : Option Nat) :
    (s.linger old).wp = s.wp := by cases old <;> rfl

@[simp] theorem linger_cr (s : St R D K) (old : Option Nat) :
    (s.linger old).cr = s.cr := by cases old <;> rfl

@[simp] theorem linger_rd (s : St R D K) (old : Option Nat) :
    (s.linger old).rd = s.rd := by cases old <;> rfl

@[simp] theorem linger_dt (s : St R D K) (old : Option Nat) :
    (s.linger old).dt = s.dt := by cases old <;> rfl

@[simp] theorem linger_gpc (s : St R D K) (old : Option Nat) :
    (s.linger old).gpc = s.gpc := by cases old <;> rfl

@[simp] theorem linger_start (s : St R D K) (old : Option Nat) :
    (s.linger old).start = s.start := by cases old <;> rfl

@[simp] theorem linger_seen (s : St R D K) (old : Option Nat) :
    (s.linger old).seen = s.seen := by cases old <;> rfl

@[simp] theorem linger_cfreed (s : St R D K) (old : Option Nat) :
    (s.linger old).cfreed = s.cfreed := by cases old <;> rfl

@[simp] theorem linger_touches (s : St R D K) (old : Option Nat) :
    (s.linger old).touches = s.touches := by cases old <;> rfl

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor

open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

theorem Step.gen_mono {P : Proto} {s t : St R D K} (st : Step P s t) : s.G ≤ t.G := by
  cases st <;> simp [St.setR, St.setD, St.writerDetach, St.creatorDone,
    St.detacherSwap, St.detacherDone, St.allocate, St.installed]

theorem Step.next_mono {P : Proto} {s t : St R D K} (st : Step P s t) : s.next ≤ t.next := by
  cases st <;> simp [St.setR, St.setD, St.writerDetach, St.creatorDone,
    St.detacherSwap, St.detacherDone, St.allocate, St.installed]

theorem Step.embeds_old {P : Proto} {s t : St R D K} (st : Step P s t)
    {v : Nat} (hv : v < s.next) : t.embeds v = s.embeds v := by
  have hne : v ≠ s.next := by omega
  cases st <;> simp [St.setR, St.setD, St.writerDetach, St.creatorDone,
    St.detacherSwap, St.detacherDone, St.allocate, St.installed, upd, hne]

theorem Step.start_origin {P : Proto} {s t : St R D K} (st : Step P s t) :
    t.start = s.start ∨ t.start = s.G := by
  cases st
  case gcStart => exact Or.inr rfl
  all_goals
    apply Or.inl
    simp [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.allocate, St.installed]

theorem Step.flag_preserved {P : Proto} {s t : St R D K}
    (h : ∀ k, s.cl_erased k = false ↔ s.erased k = none) (st : Step P s t) :
    ∀ k, t.cl_erased k = false ↔ t.erased k = none := by
  cases st
  case mark k _ _ _ _ =>
    intro x
    by_cases hx : x = k
    · subst x; simp [upd]
    · simpa [upd, hx] using h x
  all_goals
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.allocate, St.installed] using h

theorem Step.erased_stable {P : Proto} {s t : St R D K}
    (h : ∀ k, s.cl_erased k = false ↔ s.erased k = none) (st : Step P s t)
    {k : K} {e : Nat} (he : s.erased k = some e) : t.erased k = some e := by
  cases st
  case mark q _ _ _ hf =>
    have hne : k ≠ q := by
      intro hk; subst q
      have hn := (h k).1 hf
      rw [he] at hn; cases hn
    simpa [upd, hne] using he
  all_goals
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.allocate, St.installed] using he

theorem deadAt_origin {dead : Nat → Option Nat} {old : Option Nat} {g v d : Nat}
    (hd : deadAt dead old g v = some d) : dead v = some d ∨ g ≤ d := by
  cases old with
  | none => exact Or.inl hd
  | some w =>
    by_cases hv : v = w
    · subst v
      have hh : g = d := by simpa [deadAt, upd] using hd
      exact Or.inr (Nat.le_of_eq hh)
    · exact Or.inl (by simpa [deadAt, upd, hv] using hd)

theorem Step.dead_origin {P : Proto} {s t : St R D K} (st : Step P s t)
    {v d : Nat} (hd : t.lingered v = some d) : s.lingered v = some d ∨ s.G ≤ d := by
  cases st
  case allocate =>
    by_cases hv : v = s.next
    · subst v; simp [St.allocate, upd] at hd
    · exact Or.inl (by simpa [St.allocate, upd, hv] using hd)
  case writerDetach =>
    apply deadAt_origin (old := s.slot)
    simpa [St.writerDetach] using hd
  case lateDetach =>
    apply deadAt_origin (old := s.slot)
    simpa [St.writerDetach] using hd
  case creatorLinger =>
    apply deadAt_origin (old := s.cr.old)
    simpa [St.creatorDone] using hd
  case detacherLinger d0 _ =>
    apply deadAt_origin (old := (s.dt d0).old)
    simpa [St.detacherDone, St.setD] using hd
  all_goals
    apply Or.inl
    simpa [St.setR, St.setD, St.detacherSwap, St.installed] using hd

theorem Step.proto_origin {P : Proto} {s t : St R D K} (st : Step P s t) :
    t.root .prototype = none ∨ t.root .prototype = s.root .prototype ∨
      t.root .prototype = some s.next := by
  cases st
  case creatorRead => exact Or.inl rfl
  case finishScan => exact Or.inl rfl
  case allocate => exact Or.inr (Or.inr rfl)
  case creatorLock _ hc =>
    exact Or.inr (Or.inl (by simp [St.root, hc, CPc.prototype]))
  case install => exact Or.inl rfl
  case retry => exact Or.inl rfl
  case creatorLinger => exact Or.inl rfl
  all_goals
    apply Or.inr; apply Or.inl
    simp [St.setR, St.setD, St.writerDetach, St.detacherSwap, St.detacherDone, St.root] <;> rfl

theorem Step.link_origin {P : Proto} {s t : St R D K} (st : Step P s t)
    {k : K} (hl : t.linked k = false) : s.linked k = false ∨
      ∃ e, s.erased k = some e ∧ e < s.start := by
  cases st
  case unlink q e _ _ he _ hlt _ _ _ =>
    by_cases hk : k = q
    · subst q; exact Or.inr ⟨e, he, hlt⟩
    · exact Or.inl (by simpa [upd, hk] using hl)
  all_goals
    apply Or.inl
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.allocate, St.installed] using hl

theorem Inv.visible_linked {s : St R D K} (h : Inv s) {k : K} (hv : s.visAt k s.G) :
    s.linked k = true := by
  cases hl : s.linked k with
  | true => rfl
  | false =>
    obtain ⟨e, he, hlt⟩ := h.unlinked_old k hl
    have hgt := hv.2 e he
    omega

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor
open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

theorem Step.reader_live {P : Proto} {s t : St R D K} (h : Inv s)
    (st : Step P s t) (r : R) (v : Nat) (hv : (s.rd r).code = some v) :
    t.vfreed v = false := by
  have hf := (h.rd r).code_live v hv
  cases st
  case allocate =>
    have hn : v ≠ s.next := by have := (h.rd r).code_bound v hv; omega
    simpa [St.allocate, upd, hn] using hf
  case retry _ hc _ =>
    have hn : v ≠ s.cr.ver := by
      intro he
      have hp := (h.rd r).code_proto v hv
      apply hp
      simp [St.root, hc, CPc.prototype, he]
    simpa [upd, hn] using hf
  case freeVersion w d hg hall hd hlt hi _ =>
    have hn : v ≠ w := by
      intro he; subst w
      have hr := (h.rd r).retired v d hv hd
      have hp := (h.rd r).code_pc v hv
      have ha : (s.rd r).pc ≠ .idle := by simp [hp]
      rcases h.scanned r hg (hall r) ha with hs | hs
      · omega
      · have hh := hi r (s.rd r).gen hs; omega
    simpa [upd, hn] using hf
  all_goals
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.installed] using hf

/-- A single transition preserves the resources of each pre-transition reader. -/
theorem Step.reader_frame {P : Proto} {s t : St R D K} (h : Inv s)
    (st : Step P s t) (r : R) : RInv t (s.rd r) where
  gen_le := Nat.le_trans (h.rd r).gen_le st.gen_mono
  code_bound := fun v hv => Nat.lt_of_lt_of_le ((h.rd r).code_bound v hv) st.next_mono
  code_proto := by
    intro v hv hn
    rcases st.proto_origin with he | he | he
    · rw [he] at hn; cases hn
    · exact (h.rd r).code_proto v hv (he.symm.trans hn)
    · have heq : s.next = v := Option.some.inj (he.symm.trans hn)
      have hb := (h.rd r).code_bound v hv
      omega
  code_live := st.reader_live h r
  retired := by
    intro v d hv hd
    rcases st.dead_origin hd with ho | hn
    · exact (h.rd r).retired v d hv ho
    · exact Nat.le_trans (h.rd r).gen_le hn
  selected := by
    intro k hk
    obtain ⟨v, hv, hm⟩ := (h.rd r).selected k hk
    exact ⟨v, hv, by rw [st.embeds_old ((h.rd r).code_bound v hv)]; exact hm⟩
  code_pc := (h.rd r).code_pc

theorem RInv.stamped (s : St R D K) :
    RInv s ({ pc := .stamped, gen := s.G } : V1.Reader K) where
  gen_le := Nat.le_refl _
  code_bound := by intro v hv; cases hv
  code_proto := by intro v hv; cases hv
  code_live := by intro v hv; cases hv
  retired := by intro v d hv; cases hv
  selected := by intro k hk; cases hk
  code_pc := by intro v hv; cases hv

theorem RInv.load {s : St R D K} (h : Inv s) (r : R) (v : Nat)
    (hc : (s.rd r).pc = .stamped) (hs : s.slot = some v) :
    RInv s { s.rd r with pc := .running, code := some v } where
  gen_le := (h.rd r).gen_le
  code_bound := by intro w hw; cases Option.some.inj hw; exact (h.roots.clean .slot _ hs).1
  code_proto := by
    intro w hw hp
    cases Option.some.inj hw
    have he := h.roots.unique .slot .prototype v hs hp
    cases he
  code_live := by intro w hw; cases Option.some.inj hw; exact (h.roots.clean .slot _ hs).2.2
  retired := by
    intro w d hw hd
    cases Option.some.inj hw
    rw [(h.roots.clean .slot v hs).2.1] at hd
    cases hd
  selected := by
    intro k hk
    obtain ⟨w, hw, _⟩ := (h.rd r).selected k hk
    have hp := (h.rd r).code_pc w hw
    rw [hc] at hp; cases hp
  code_pc := by intro w hw; rfl

theorem RInv.run {s : St R D K} {x : V1.Reader K} (h : RInv s x)
    {v : Nat} {k : K} (hv : x.code = some v) (hk : k ∈ s.embeds v) :
    RInv s { x with run := some k } where
  gen_le := h.gen_le
  code_bound := h.code_bound
  code_proto := h.code_proto
  code_live := h.code_live
  retired := h.retired
  selected := by intro q hq; cases Option.some.inj hq; exact ⟨v, hv, hk⟩
  code_pc := h.code_pc

theorem RInv.setR {s : St R D K} {y : V1.Reader K} (h : RInv s y)
    (r : R) (x : V1.Reader K) : RInv (s.setR r x) y where
  gen_le := h.gen_le
  code_bound := h.code_bound
  code_proto := h.code_proto
  code_live := h.code_live
  retired := h.retired
  selected := h.selected
  code_pc := h.code_pc

theorem Step.readers {P : Proto} {s t : St R D K} (h : Inv s)
    (st : Step P s t) : ∀ r, RInv t (t.rd r) := by
  have hf := st.reader_frame h
  cases st
  case stamp q _ =>
    intro r
    by_cases hr : r = q
    · subst r
      simpa [St.setR, upd] using (RInv.stamped s).setR q _
    · simpa [St.setR, upd, hr] using hf r
  case readSlot q v hc hs =>
    intro r
    by_cases hr : r = q
    · subst r
      simpa [St.setR, upd] using (RInv.load h q v hc hs).setR q _
    · simpa [St.setR, upd, hr] using hf r
  case run q v k _ hv hk =>
    intro r
    by_cases hr : r = q
    · subst r
      simpa [St.setR, upd] using ((h.rd q).run hv hk).setR q _
    · simpa [St.setR, upd, hr] using hf r
  case exit q _ =>
    intro r
    by_cases hr : r = q
    · subst r
      simpa [St.setR, upd] using (rinv_empty s).setR q _
    · simpa [St.setR, upd, hr] using hf r
  all_goals
    intro r
    simpa [St.setD, St.writerDetach, St.creatorDone, St.detacherSwap,
      St.detacherDone, St.allocate, St.installed] using hf r

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor
open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

theorem Step.borrowed {P : Proto} {s t : St R D K} (h : Inv s)
    (hp : P.hold = true) (st : Step P s t) :
    (t.cr.pc.borrowed = true → t.cr.holds = true) ∧
    (t.cr.pc.borrowed = true → ∀ k ∈ t.cr.found, t.linked k = true) := by
  cases st
  case creatorRead => simp [CPc.borrowed]
  case scanClause k hc hk =>
    refine ⟨h.borrowed_hold, ?_⟩
    intro hb q hq
    rcases List.mem_append.mp hq with ho | hn
    · exact h.borrowed_list hb q ho
    · have he : q = k := by simpa using hn
      subst q; exact h.visible_linked hk
  case finishScan hc =>
    refine ⟨fun _ => hp, ?_⟩
    exact fun _ => h.borrowed_list (by simp [hc, CPc.borrowed])
  case allocate => simp [St.allocate, CPc.borrowed]
  case creatorLock => simp [CPc.borrowed]
  case install => simp [St.installed, CPc.borrowed]
  case retry => simp [CPc.borrowed]
  case creatorLinger => simp [St.creatorDone, CPc.borrowed]
  case unlink _ _ _ _ _ _ _ _ hh _ =>
    have hn : s.cr.pc.borrowed ≠ true := by
      intro hb; have := h.borrowed_hold hb; rw [hh] at this; cases this
    simp [hn]
  all_goals
    simpa [St.setR, St.setD, St.writerDetach, St.detacherSwap, St.detacherDone] using
      And.intro h.borrowed_hold h.borrowed_list

theorem Step.owned {P : Proto} {s t : St R D K} (h : Inv s)
    (hp : P.own = true) (st : Step P s t) : ∀ v, v < t.next → t.owned v = true := by
  cases st
  case allocate =>
    intro v hv
    by_cases he : v = s.next
    · subst v; simp [St.allocate, upd, hp]
    · have hb : v < s.next := by change v < s.next + 1 at hv; omega
      simpa [St.allocate, upd, he] using h.owned v hb
  all_goals
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.installed] using h.owned

theorem Step.scanned {P : Proto} {s t : St R D K} (h : Inv s)
    (st : Step P s t) : ∀ r, t.gpc = .scanning → t.seen r ≠ none →
    (t.rd r).pc ≠ .idle → t.start ≤ (t.rd r).gen ∨ t.seen r = some (some (t.rd r).gen) := by
  cases st
  case stamp q _ =>
    intro r hg hs ha
    by_cases he : r = q
    · subst r; exact Or.inl (by simpa [St.setR, upd] using h.start_le)
    · simpa [St.setR, upd, he] using h.scanned r hg hs (by simpa [St.setR, upd, he] using ha)
  case readSlot q _ hc _ =>
    intro r hg hs ha
    by_cases he : r = q
    · subst r
      simpa [St.setR, upd] using h.scanned q hg hs (by simp [hc])
    · simpa [St.setR, upd, he] using h.scanned r hg hs (by simpa [St.setR, upd, he] using ha)
  case run q _ _ hc _ _ =>
    intro r hg hs ha
    by_cases he : r = q
    · subst r
      simpa [St.setR, upd] using h.scanned q hg hs (by simp [hc])
    · simpa [St.setR, upd, he] using h.scanned r hg hs (by simpa [St.setR, upd, he] using ha)
  case exit q _ =>
    intro r hg hs ha
    by_cases he : r = q
    · subst r; simp [St.setR, upd] at ha
    · simpa [St.setR, upd, he] using h.scanned r hg hs (by simpa [St.setR, upd, he] using ha)
  case gcStart => intro r _ hs; exact False.elim (hs rfl)
  case gcScan q _ _ =>
    intro r hg hs ha
    by_cases he : r = q
    · subst r; exact Or.inr (by simp [upd, ha])
    · simpa [upd, he] using h.scanned r hg (by simpa [upd, he] using hs) ha
  case gcEnd => intro r hg; cases hg
  all_goals
    simpa [St.setD, St.writerDetach, St.creatorDone, St.detacherSwap,
      St.detacherDone, St.allocate, St.installed] using h.scanned

/-- Memory safety needs CAS, reference acquisition under a hold, and ownership;
    it does not assume the erasure ordering or validated installation. -/
theorem Inv.step {P : Proto} {s t : St R D K} (h : Inv s)
    (hcas : P.cas = true) (hhold : P.hold = true) (hown : P.own = true)
    (st : Step P s t) : Inv t where
  roots := step_roots h.roots hcas st
  start_le := by
    rcases st.start_origin with he | he
    · rw [he]; exact Nat.le_trans h.start_le st.gen_mono
    · rw [he]; exact st.gen_mono
  flag := st.flag_preserved h.flag
  unlinked_old := by
    intro k hk
    rcases st.link_origin hk with ho | ⟨e, he, hlt⟩
    · obtain ⟨e, he, hlt⟩ := h.unlinked_old k ho
      exact ⟨e, st.erased_stable h.flag he, Nat.lt_of_lt_of_le hlt st.gen_mono⟩
    · exact ⟨e, st.erased_stable h.flag he,
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hlt h.start_le) st.gen_mono⟩
  borrowed_hold := (st.borrowed h hhold).1
  borrowed_list := (st.borrowed h hhold).2
  owned := st.owned h hown
  rd := st.readers h
  scanned := st.scanned h
  nodup := step_nodup h.roots h.nodup st

theorem reach_inv {P : Proto} {s0 s : St R D K} (hi : Init s0)
    (hcas : P.cas = true) (hhold : P.hold = true) (hown : P.own = true)
    (hr : Reach P s0 s) : Inv s := by
  induction hr with
  | refl => exact init_inv hi
  | tail _ st ih => exact ih.step hcas hhold hown st

theorem mem_safe {P : Proto} {s0 s : St R D K} (hi : Init s0)
    (hcas : P.cas = true) (hhold : P.hold = true) (hown : P.own = true)
    (hr : Reach P s0 s) : Mem s := (reach_inv hi hcas hhold hown hr).mem

theorem fixed_mem_safe {s0 s : St R D K} (hi : Init s0) (hr : Reach fixed s0 s) : Mem s :=
  mem_safe hi rfl rfl rfl hr

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor
open V1 (upd)
variable {R D K : Type} [DecidableEq R] [DecidableEq D] [DecidableEq K]

theorem Step.erased_origin {P : Proto} {s t : St R D K} (st : Step P s t)
    {k : K} {e : Nat} (he : t.erased k = some e) : s.erased k = some e ∨ e = s.G + 1 := by
  cases st
  case mark q _ _ _ _ =>
    by_cases hk : k = q
    · subst q; exact Or.inr (by simpa [upd] using he.symm)
    · exact Or.inl (by simpa [upd, hk] using he)
  all_goals
    apply Or.inl
    simpa [St.setR, St.setD, St.writerDetach, St.creatorDone,
      St.detacherSwap, St.detacherDone, St.allocate, St.installed] using he

theorem init_einv {s : St R D K} (hi : Init s) : EInv s := by
  obtain ⟨hs, _, _, hl, hw, hc, hr, _, _, _, _, he, _⟩ := hi
  refine ⟨by simp [hl, hw], by simp [hl, hc], ?_, ?_, ?_⟩
  · intro hp; rw [hw] at hp; cases hp
  · intro v k e _ _ hk; rw [(he k).1] at hk; cases hk
  · intro r v k e hv; rw [hr r] at hv; cases hv

theorem EInv.controls {s t : St R D K} (h : EInv s) (st : Step fixed s t) :
    (t.lock = .writer ↔ t.wp = .marking ∨ t.wp = .detached) ∧
    (t.lock = .creator ↔ t.cr.pc = .checking) ∧
    (t.wp = .detached → t.slot = none) := by
  have hw := h.writer
  have hc := h.creator
  have hd := h.detached
  cases st <;> simp_all [St.setR, St.setD, St.writerDetach, St.creatorDone,
    St.detacherSwap, St.detacherDone, St.allocate, St.installed, fixed]

theorem EInv.slot_step {s t : St R D K} (h : Inv s) (he : EInv s)
    (st : Step fixed s t) :
    ∀ v k e, t.slot = some v → k ∈ t.embeds v → t.erased k = some e → t.G < e := by
  cases st
  case mark q _ _ _ _ =>
    intro v k e hs hm hd
    by_cases hk : k = q
    · subst q
      have heq : s.G + 1 = e := by simpa [upd] using hd
      change s.G < e
      omega
    · exact he.slot v k e hs hm (by simpa [upd, hk] using hd)
  case writerDetach =>
    intro v k e hs
    simp [St.writerDetach] at hs
  case skipDetach => simp_all [fixed]
  case publish _ hw =>
    intro v k e hs
    have hn := he.detached hw
    rw [hn] at hs; cases hs
  case lateDetach => simp_all [fixed]
  case allocate =>
    intro v k e hs hm hd
    have hb := (h.roots.clean .slot v hs).1
    have hn : v ≠ s.next := by omega
    exact he.slot v k e hs (by simpa [St.allocate, upd, hn] using hm) hd
  case install _ _ hv _ =>
    intro v k e hs hm hd
    have heq : s.cr.ver = v := Option.some.inj hs
    have hf := hv rfl k (by simpa [St.installed, heq] using hm)
    have hn := (h.flag k).1 hf
    change s.erased k = some e at hd
    rw [hn] at hd; cases hd
  case detacherCas => intro v k e hs; cases hs
  all_goals
    simpa [St.setR, St.setD, St.creatorDone, St.detacherDone] using he.slot

theorem EInv.reader_frame {P : Proto} {s t : St R D K} (h : Inv s) (he : EInv s)
    (st : Step P s t) : ∀ r v k e, (s.rd r).code = some v →
    k ∈ t.embeds v → t.erased k = some e → (s.rd r).gen < e := by
  intro r v k e hv hk hd
  have hm : k ∈ s.embeds v := by rw [← st.embeds_old ((h.rd r).code_bound v hv)]; exact hk
  rcases st.erased_origin hd with ho | hn
  · exact he.reader r v k e hv hm ho
  · have hg := (h.rd r).gen_le; omega

theorem EInv.reader_step {s t : St R D K} (h : Inv s) (he : EInv s)
    (st : Step fixed s t) : ∀ r v k e, (t.rd r).code = some v →
    k ∈ t.embeds v → t.erased k = some e → (t.rd r).gen < e := by
  have hf := he.reader_frame h st
  cases st
  case stamp q _ =>
    intro r v k e hv hm hd
    by_cases hr : r = q
    · subst r; simp [St.setR, upd] at hv
    · simpa [St.setR, upd, hr] using hf r v k e (by simpa [St.setR, upd, hr] using hv) hm hd
  case readSlot q w _ hs =>
    intro r v k e hv hm hd
    by_cases hr : r = q
    · subst r
      have heq : w = v := by simpa [St.setR, upd] using hv
      subst v
      simpa [St.setR, upd] using Nat.lt_of_le_of_lt (h.rd q).gen_le (he.slot w k e hs hm hd)
    · simpa [St.setR, upd, hr] using hf r v k e (by simpa [St.setR, upd, hr] using hv) hm hd
  case run q _ _ _ _ _ =>
    intro r v k e hv hm hd
    by_cases hr : r = q
    · subst r
      simpa [St.setR, upd] using hf q v k e (by simpa [St.setR, upd] using hv) hm hd
    · simpa [St.setR, upd, hr] using hf r v k e (by simpa [St.setR, upd, hr] using hv) hm hd
  case exit q _ =>
    intro r v k e hv hm hd
    by_cases hr : r = q
    · subst r; simp [St.setR, upd] at hv
    · simpa [St.setR, upd, hr] using hf r v k e (by simpa [St.setR, upd, hr] using hv) hm hd
  all_goals
    simpa [St.setD, St.writerDetach, St.creatorDone, St.detacherSwap,
      St.detacherDone, St.allocate, St.installed] using hf

theorem EInv.step {s t : St R D K} (h : Inv s) (he : EInv s)
    (st : Step fixed s t) : EInv t :=
  ⟨(he.controls st).1, (he.controls st).2.1, (he.controls st).2.2,
    he.slot_step h st, he.reader_step h st⟩

theorem reach_einv {s0 s : St R D K} (hi : Init s0) (hr : Reach fixed s0 s) : Inv s ∧ EInv s := by
  induction hr with
  | refl => exact ⟨init_inv hi, init_einv hi⟩
  | tail _ st ih => exact ⟨ih.1.step rfl rfl rfl st, ih.2.step ih.1 st⟩

theorem fixed_lud_safe {s0 s : St R D K} (hi : Init s0) (hr : Reach fixed s0 s) : LudErase s := by
  obtain ⟨h, he⟩ := reach_einv hi hr
  exact he.lud h

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor
open V1 (upd)

/-- Concrete empty state; births may already include clauses of a future
    generation, which become selectable only when that generation is reached. -/
def initial {K : Type} (birth : K → Nat) : St Unit Bool K :=
  { G := 0, born := birth, erased := fun _ => none, cl_erased := fun _ => false,
    linked := fun _ => true, embeds := fun _ => [], owned := fun _ => false,
    next := 0, vfreed := fun _ => false, slot := none, lingered := fun _ => none,
    dup := false, lock := .free, wp := .idle, cr := {}, rd := fun _ => {},
    dt := fun _ => {}, gpc := .idle, start := 0, seen := fun _ => none }

theorem initial_init {K : Type} (birth : K → Nat) : Init (initial birth) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun _ => rfl, fun _ => rfl,
    rfl, Nat.le_refl _, fun _ => rfl, fun _ => ⟨rfl, rfl, rfl⟩,
    fun _ => ⟨rfl, rfl, rfl, rfl⟩⟩

def unitInit : St Unit Bool Unit := initial (fun _ => 0)
theorem unitInit_init : Init unitInit := initial_init _

namespace Witness

def collected : St Unit Bool Unit :=
  { unitInit with cr := { pc := .scanning, old := none, found := [()], holds := true } }
def building (P : Proto) : St Unit Bool Unit :=
  { collected with cr := { collected.cr with pc := .building, holds := P.hold } }
def checking (P : Proto) : St Unit Bool Unit :=
  let s := (building P).allocate P
  { s with lock := .creator, cr := { s.cr with pc := .checking } }
def prepared (P : Proto) : St Unit Bool Unit := (checking P).installed.creatorDone

theorem collected_reach (P : Proto) : Reach P unitInit collected := by
  let s : St Unit Bool Unit := { unitInit with cr := { pc := .scanning, holds := true } }
  have h : Reach P unitInit s := Reach.tail (.refl _) (Step.creatorRead _ rfl)
  exact Reach.tail h (Step.scanClause _ () rfl (by decide))

theorem building_reach (P : Proto) : Reach P unitInit (building P) :=
  Reach.tail (collected_reach P) (Step.finishScan _ rfl)

theorem prepared_reach (P : Proto) : Reach P unitInit (prepared P) := by
  have h1 := Reach.tail (building_reach P) (Step.allocate _ rfl)
  have h2 : Reach P unitInit (checking P) := Reach.tail h1 (Step.creatorLock _ rfl rfl)
  have h3 := Reach.tail h2 (Step.install _ rfl rfl
    (by intro _ k _; cases k; rfl) (by intro _; rfl))
  exact Reach.tail h3 (Step.creatorLinger _ rfl)

end Witness
open Witness

theorem no_detach_lud : ∃ s, Reach noDetach unitInit s ∧ Mem s ∧ ¬ LudErase s := by
  let s1 : St Unit Bool Unit := { prepared noDetach with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Unit :=
    { s1 with erased := upd s1.erased () (some 1), cl_erased := upd s1.cl_erased () true }
  let s3 : St Unit Bool Unit := { s2 with wp := .detached }
  let s4 : St Unit Bool Unit := { s3 with G := 1, lock := .free, wp := .idle }
  let s5 := s4.setR () { pc := .stamped, gen := 1 }
  let s6 := s5.setR () { s5.rd () with pc := .running, code := some 0 }
  let s7 := s6.setR () { s6.rd () with run := some () }
  have h1 : Reach noDetach unitInit s1 :=
    Reach.tail (prepared_reach _) (Step.writerLock _ (by decide) (by decide))
  have h2 : Reach noDetach unitInit s2 :=
    Reach.tail h1 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
  have h3 : Reach noDetach unitInit s3 :=
    Reach.tail h2 (Step.skipDetach _ (by decide) (by decide) (by decide))
  have h4 : Reach noDetach unitInit s4 := Reach.tail h3 (Step.publish _ (by decide) (by decide))
  have h5 : Reach noDetach unitInit s5 := Reach.tail h4 (Step.stamp _ () (by decide))
  have h6 : Reach noDetach unitInit s6 :=
    Reach.tail h5 (Step.readSlot _ () 0 (by decide) (by decide))
  have h7 : Reach noDetach unitInit s7 :=
    Reach.tail h6 (Step.run _ () 0 () (by decide) (by decide) (by decide))
  refine ⟨s7, h7, mem_safe unitInit_init rfl rfl rfl h7, ?_⟩
  intro hl
  have hh : 1 < 1 := hl () () 1 (by decide) (by decide)
  omega

theorem late_detach_lud : ∃ s, Reach lateDetach unitInit s ∧ Mem s ∧ ¬ LudErase s := by
  let s1 : St Unit Bool Unit := { prepared lateDetach with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Unit :=
    { s1 with erased := upd s1.erased () (some 1), cl_erased := upd s1.cl_erased () true }
  let s3 : St Unit Bool Unit := { s2 with wp := .detached }
  let s4 : St Unit Bool Unit := { s3 with G := 1, lock := .free, wp := .late }
  let s5 := s4.setR () { pc := .stamped, gen := 1 }
  let s6 := s5.setR () { s5.rd () with pc := .running, code := some 0 }
  let s7 := s6.writerDetach .idle
  let s8 := s7.setR () { s7.rd () with run := some () }
  have h1 : Reach lateDetach unitInit s1 :=
    Reach.tail (prepared_reach _) (Step.writerLock _ (by decide) (by decide))
  have h2 : Reach lateDetach unitInit s2 :=
    Reach.tail h1 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
  have h3 : Reach lateDetach unitInit s3 :=
    Reach.tail h2 (Step.skipDetach _ (by decide) (by decide) (by decide))
  have h4 : Reach lateDetach unitInit s4 := Reach.tail h3 (Step.publish _ (by decide) (by decide))
  have h5 : Reach lateDetach unitInit s5 := Reach.tail h4 (Step.stamp _ () (by decide))
  have h6 : Reach lateDetach unitInit s6 :=
    Reach.tail h5 (Step.readSlot _ () 0 (by decide) (by decide))
  have h7 : Reach lateDetach unitInit s7 := Reach.tail h6 (Step.lateDetach _ rfl (by decide))
  have h8 : Reach lateDetach unitInit s8 :=
    Reach.tail h7 (Step.run _ () 0 () (by decide) (by decide) (by decide))
  refine ⟨s8, h8, mem_safe unitInit_init rfl rfl rfl h8, ?_⟩
  intro hl
  have hh : 1 < 1 := hl () () 1 (by decide) (by decide)
  omega

theorem unvalidated_install_lud : ∃ s, Reach unvalidated unitInit s ∧ Mem s ∧ ¬ LudErase s := by
  let s1 := (building unvalidated).allocate unvalidated
  let s2 : St Unit Bool Unit := { s1 with lock := .writer, wp := .marking }
  let s3 : St Unit Bool Unit :=
    { s2 with erased := upd s2.erased () (some 1), cl_erased := upd s2.cl_erased () true }
  let s4 := s3.writerDetach .detached
  let s5 : St Unit Bool Unit := { s4 with G := 1, lock := .free, wp := .idle }
  let s6 : St Unit Bool Unit :=
    { s5 with lock := .creator, cr := { s5.cr with pc := .checking } }
  let s7 := s6.installed
  let s8 := s7.creatorDone
  let s9 := s8.setR () { pc := .stamped, gen := 1 }
  let s10 := s9.setR () { s9.rd () with pc := .running, code := some 0 }
  let s11 := s10.setR () { s10.rd () with run := some () }
  have h1 : Reach unvalidated unitInit s1 := Reach.tail (building_reach _) (Step.allocate _ rfl)
  have h2 : Reach unvalidated unitInit s2 := Reach.tail h1 (Step.writerLock _ (by decide) (by decide))
  have h3 : Reach unvalidated unitInit s3 :=
    Reach.tail h2 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
  have h4 : Reach unvalidated unitInit s4 := Reach.tail h3 (Step.writerDetach _ rfl (by decide) (by decide))
  have h5 : Reach unvalidated unitInit s5 := Reach.tail h4 (Step.publish _ (by decide) (by decide))
  have h6 : Reach unvalidated unitInit s6 := Reach.tail h5 (Step.creatorLock _ (by decide) (by decide))
  have h7 : Reach unvalidated unitInit s7 := Reach.tail h6 (Step.install _ (by decide) (by decide)
    (by intro h; cases h) (by intro _; decide))
  have h8 : Reach unvalidated unitInit s8 := Reach.tail h7 (Step.creatorLinger _ (by decide))
  have h9 : Reach unvalidated unitInit s9 := Reach.tail h8 (Step.stamp _ () (by decide))
  have h10 : Reach unvalidated unitInit s10 := Reach.tail h9 (Step.readSlot _ () 0 (by decide) (by decide))
  have h11 : Reach unvalidated unitInit s11 :=
    Reach.tail h10 (Step.run _ () 0 () (by decide) (by decide) (by decide))
  refine ⟨s11, h11, mem_safe unitInit_init rfl rfl rfl h11, ?_⟩
  intro hl
  have hh : 1 < 1 := hl () () 1 (by decide) (by decide)
  omega

theorem plain_swap_unsafe : ∃ s, Reach plainSwap unitInit s ∧ ¬ Mem s := by
  let s1 := (prepared plainSwap).setD false { pc := .loaded, old := some 0 }
  let s2 := s1.setD true { pc := .loaded, old := some 0 }
  let s3 := s2.detacherSwap false
  let s4 := s3.detacherSwap true
  let s5 := s4.detacherDone false
  let s6 := s5.detacherDone true
  refine ⟨s6, ?_, ?_⟩
  · have h1 : Reach plainSwap unitInit s1 :=
      Reach.tail (prepared_reach _) (Step.detacherRead _ false (by decide))
    have h2 : Reach plainSwap unitInit s2 := Reach.tail h1 (Step.detacherRead _ true (by decide))
    have h3 : Reach plainSwap unitInit s3 :=
      Reach.tail h2 (Step.detacherCas _ false (by decide) (by intro h; cases h))
    have h4 : Reach plainSwap unitInit s4 :=
      Reach.tail h3 (Step.detacherCas _ true (by decide) (by intro h; cases h))
    have h5 : Reach plainSwap unitInit s5 := Reach.tail h4 (Step.detacherLinger _ false (by decide))
    exact Reach.tail h5 (Step.detacherLinger _ true (by decide))
  · intro hm
    have hf := hm.2.2.1
    have ht : s6.dup = true := by decide
    rw [ht] at hf; cases hf

theorem no_hold_unsafe : ∃ s, Reach noHold unitInit s ∧ ¬ Mem s := by
  let s1 : St Unit Bool Unit := { building noHold with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Unit :=
    { s1 with erased := upd s1.erased () (some 1), cl_erased := upd s1.cl_erased () true }
  let s3 := s2.writerDetach .detached
  let s4 : St Unit Bool Unit := { s3 with G := 1, lock := .free, wp := .idle }
  let s5 : St Unit Bool Unit := { s4 with lock := .writer, wp := .marking }
  let s6 := s5.writerDetach .detached
  let s7 : St Unit Bool Unit := { s6 with G := 2, lock := .free, wp := .idle }
  let s8 : St Unit Bool Unit := { s7 with gpc := .scanning, start := 2, seen := fun _ => none }
  let s9 : St Unit Bool Unit := { s8 with seen := upd s8.seen () (some none) }
  let s10 : St Unit Bool Unit := { s9 with linked := upd s9.linked () false }
  refine ⟨s10, ?_, ?_⟩
  · have h1 : Reach noHold unitInit s1 :=
      Reach.tail (building_reach _) (Step.writerLock _ (by decide) (by decide))
    have h2 : Reach noHold unitInit s2 :=
      Reach.tail h1 (Step.mark _ () (by decide) (by decide) (by decide) (by decide))
    have h3 : Reach noHold unitInit s3 := Reach.tail h2 (Step.writerDetach _ rfl (by decide) (by decide))
    have h4 : Reach noHold unitInit s4 := Reach.tail h3 (Step.publish _ (by decide) (by decide))
    have h5 : Reach noHold unitInit s5 := Reach.tail h4 (Step.writerLock _ (by decide) (by decide))
    have h6 : Reach noHold unitInit s6 := Reach.tail h5 (Step.writerDetach _ rfl (by decide) (by decide))
    have h7 : Reach noHold unitInit s7 := Reach.tail h6 (Step.publish _ (by decide) (by decide))
    have h8 : Reach noHold unitInit s8 := Reach.tail h7 (Step.gcStart _ (by decide))
    have h9 : Reach noHold unitInit s9 := Reach.tail h8 (Step.gcScan _ () (by decide) (by decide))
    exact Reach.tail h9 (Step.unlink _ () 1 (by decide) (by intro r; cases r; decide)
      (by decide) (by decide) (by decide)
      (by
        intro r g hg
        cases r
        have hs : s9.seen () = some none := by decide
        rw [hs] at hg
        cases hg)
      (by decide) (by decide))
  · intro hm
    have hf := hm.2.1 () (by decide)
    have ht : s10.cfreed () = true := by decide
    rw [ht] at hf; cases hf

end Mettapedia.Languages.Prolog.SWI.Supervisor

namespace Mettapedia.Languages.Prolog.SWI.Supervisor
open V1 (upd)

namespace Birth

def proto (own : Bool) : Proto := { fixed with own := own }
def init : St Unit Bool Bool := initial (fun k => if k then 1 else 0)
theorem init_init : Init init := initial_init _

def stamped := init.setR () { pc := .stamped, gen := 0 }
def marking : St Unit Bool Bool := { stamped with lock := .writer, wp := .marking }
def erased : St Unit Bool Bool :=
  { marking with erased := upd marking.erased false (some 1),
                 cl_erased := upd marking.cl_erased false true }
def detached := erased.writerDetach .detached
def published : St Unit Bool Bool := { detached with G := 1, lock := .free, wp := .idle }
def scanning : St Unit Bool Bool :=
  { published with cr := { pc := .scanning, old := published.slot, holds := true } }
def collected : St Unit Bool Bool := { scanning with cr := { scanning.cr with found := [true] } }
def building : St Unit Bool Bool := { collected with cr := { collected.cr with pc := .building } }
def allocated (own : Bool) := building.allocate (proto own)
def checking (own : Bool) : St Unit Bool Bool :=
  { allocated own with lock := .creator, cr := { (allocated own).cr with pc := .checking } }
def installed (own : Bool) := (checking own).installed
def done (own : Bool) := (installed own).creatorDone
def loaded (own : Bool) := (done own).setR () { (done own).rd () with pc := .running, code := some 0 }
def running (own : Bool) := (loaded own).setR () { (loaded own).rd () with run := some true }

/-- The old reader loads current-generation static code. No visibility test is
    smuggled into either readSlot or run. -/
theorem running_reach (own : Bool) : Reach (proto own) init (running own) := by
  have h1 : Reach (proto own) init stamped := Reach.tail (.refl _) (Step.stamp _ () (by cases own <;> decide))
  have h2 : Reach (proto own) init marking := Reach.tail h1 (Step.writerLock _ (by cases own <;> decide) (by cases own <;> decide))
  have h3 : Reach (proto own) init erased :=
    Reach.tail h2 (Step.mark _ false (by cases own <;> decide) (by cases own <;> decide) (by cases own <;> decide) (by cases own <;> decide))
  have h4 : Reach (proto own) init detached := Reach.tail h3 (Step.writerDetach _ rfl (by cases own <;> decide) (by cases own <;> decide))
  have h5 : Reach (proto own) init published := Reach.tail h4 (Step.publish _ (by cases own <;> decide) (by cases own <;> decide))
  have h6 : Reach (proto own) init scanning := Reach.tail h5 (Step.creatorRead _ (by cases own <;> decide))
  have h7 : Reach (proto own) init collected := Reach.tail h6 (Step.scanClause _ true (by cases own <;> decide) (by cases own <;> decide))
  have h8 : Reach (proto own) init building := Reach.tail h7 (Step.finishScan _ (by cases own <;> decide))
  have h9 : Reach (proto own) init (allocated own) := Reach.tail h8 (Step.allocate _ (by cases own <;> decide))
  have h10 : Reach (proto own) init (checking own) := Reach.tail h9 (Step.creatorLock _ (by cases own <;> decide) (by cases own <;> decide))
  have h11 : Reach (proto own) init (installed own) := Reach.tail h10 (Step.install _ (by cases own <;> decide) (by cases own <;> decide)
    (by
      intro _ k hk
      change k ∈ [true] at hk
      have ht : k = true := by simpa using hk
      subst k
      rfl)
    (by intro _; rfl))
  have h12 : Reach (proto own) init (done own) := Reach.tail h11 (Step.creatorLinger _ (by cases own <;> decide))
  have h13 : Reach (proto own) init (loaded own) := Reach.tail h12 (Step.readSlot _ () 0 (by cases own <;> decide) (by cases own <;> decide))
  exact Reach.tail h13 (Step.run _ () 0 true (by cases own <;> decide) (by cases own <;> decide) (by cases own <;> decide))

end Birth

/-- Memory and erasure safety do not imply the birth side of static-code LUD. -/
theorem birth_side_open : ∃ s, Reach fixed Birth.init s ∧ Mem s ∧
    (s.rd ()).run = some true ∧ (s.rd ()).gen < s.born true := by
  have hr : Reach fixed Birth.init (Birth.running true) := Birth.running_reach true
  exact ⟨Birth.running true, hr, fixed_mem_safe Birth.init_init hr, by decide⟩

/-- Same birth-gap schedule as V1: unlink drops the last reference only when
    the running supervisor owns no reference to its operand. -/
theorem no_own_unsafe : ∃ s, Reach noOwn Birth.init s ∧ ¬ Mem s ∧
    (s.rd ()).gen = 0 ∧ s.born true = 1 ∧ s.erased true = some 2 ∧
    (s.rd ()).run = some true ∧ s.cfreed true = true ∧ s.vfreed 0 = false := by
  let s1 : St Unit Bool Bool := { Birth.running false with lock := .writer, wp := .marking }
  let s2 : St Unit Bool Bool :=
    { s1 with erased := upd s1.erased true (some 2), cl_erased := upd s1.cl_erased true true }
  let s3 := s2.writerDetach .detached
  let s4 : St Unit Bool Bool := { s3 with G := 2, lock := .free, wp := .idle }
  let s5 : St Unit Bool Bool := { s4 with lock := .writer, wp := .marking }
  let s6 := s5.writerDetach .detached
  let s7 : St Unit Bool Bool := { s6 with G := 3, lock := .free, wp := .idle }
  let s8 : St Unit Bool Bool := { s7 with gpc := .scanning, start := 3, seen := fun _ => none }
  let s9 : St Unit Bool Bool := { s8 with seen := upd s8.seen () (some (some 0)) }
  let s10 : St Unit Bool Bool := { s9 with linked := upd s9.linked true false }
  refine ⟨s10, ?_, ?_, by decide⟩
  · have h0 : Reach noOwn Birth.init (Birth.running false) := Birth.running_reach false
    have h1 : Reach noOwn Birth.init s1 := Reach.tail h0 (Step.writerLock _ (by decide) (by decide))
    have h2 : Reach noOwn Birth.init s2 :=
      Reach.tail h1 (Step.mark _ true (by decide) (by decide) (by decide) (by decide))
    have h3 : Reach noOwn Birth.init s3 := Reach.tail h2 (Step.writerDetach _ rfl (by decide) (by decide))
    have h4 : Reach noOwn Birth.init s4 := Reach.tail h3 (Step.publish _ (by decide) (by decide))
    have h5 : Reach noOwn Birth.init s5 := Reach.tail h4 (Step.writerLock _ (by decide) (by decide))
    have h6 : Reach noOwn Birth.init s6 := Reach.tail h5 (Step.writerDetach _ rfl (by decide) (by decide))
    have h7 : Reach noOwn Birth.init s7 := Reach.tail h6 (Step.publish _ (by decide) (by decide))
    have h8 : Reach noOwn Birth.init s8 := Reach.tail h7 (Step.gcStart _ (by decide))
    have h9 : Reach noOwn Birth.init s9 := Reach.tail h8 (Step.gcScan _ () (by decide) (by decide))
    exact Reach.tail h9 (Step.unlink _ true 2 (by decide) (by intro r; cases r; decide)
      (by decide) (by decide) (by decide)
      (by
        intro r g hg
        cases r
        have hs : s9.seen () = some (some 0) := by decide
        rw [hs] at hg
        cases hg
        decide)
      (by decide) (by decide))
  · intro hm
    have hf := (hm.1 ()).2 true (by decide)
    have ht : s10.cfreed true = true := by decide
    rw [ht] at hf; cases hf

end Mettapedia.Languages.Prolog.SWI.Supervisor
