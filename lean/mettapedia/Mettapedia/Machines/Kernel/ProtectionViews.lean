/-!
# Protection views, PCID stale marks, and INVPCID coherency

Abstract model of per-row protection views over a single shared address space:
- `merged` updates a private table copy when its canonical table changes,
  retaining private table links and opened spans while propagating new entries.
- Each program row owns disjoint 2 MiB spans whose page-directory USER bit is
  closed in the canonical tables and in every other view, and open only in the
  owning view. Leaf page tables remain shared across all views.
- Per-core TLB coherency under PCID (stale-mark flush on next entry) and
  INVPCID (immediate invalidation of every entered view, including View 0 when
  PCID is lazily enabled on a core).

This file proves the abstract page-table and TLB-coherency laws only.
Native hardware execution is established separately by host and QEMU evidence.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.ProtectionViews

structure Entry where
  present : Bool
  user : Bool
  huge : Bool
  frame : Nat
  flags : Nat
  deriving DecidableEq, Repr

def merged (canonical priv : Entry) : Entry :=
  if !priv.present then canonical
  else if priv.frame = canonical.frame then
    { canonical with user := canonical.user || priv.user }
  else
    { canonical with frame := priv.frame }

theorem merged_absent_takes_canonical (canonical priv : Entry) (h : priv.present = false) :
    merged canonical priv = canonical := by
  simp [merged, h]

theorem merged_same_frame_preserves_opening (canonical priv : Entry)
    (hp : priv.present = true) (hf : priv.frame = canonical.frame) :
    (merged canonical priv).frame = canonical.frame ∧
    (merged canonical priv).user = (canonical.user || priv.user) := by
  simp [merged, hp, hf]

theorem merged_private_copy_keeps_frame (canonical priv : Entry)
    (hp : priv.present = true) (hf : priv.frame ≠ canonical.frame) :
    (merged canonical priv).frame = priv.frame ∧
    (merged canonical priv).present = canonical.present ∧
    (merged canonical priv).flags = canonical.flags := by
  simp [merged, hp, hf]

theorem merged_closed_stays_closed (canonical priv : Entry)
    (hc : canonical.user = false) (hp : priv.user = false) :
    (merged canonical priv).user = false := by
  unfold merged
  split
  · exact hc
  · split
    · simp [hc, hp]
    · exact hc

/-! ## Single shared address space with per-row 2 MiB span isolation -/

structure ViewSpace (Span Page Leaf : Type) where
  leafOf : Span → Page → Leaf
  canonicalUser : Span → Bool
  viewUser : Nat → Span → Bool

def claimSpan {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (owner : Nat) (s : Span) : ViewSpace Span Page Leaf :=
  { space with
    canonicalUser := fun x => if x = s then false else space.canonicalUser x
    viewUser := fun v x => if x = s then decide (v = owner) else space.viewUser v x }

def openSpan {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (view : Nat) (s : Span) :
    ViewSpace Span Page Leaf × Bool :=
  let wasClosed := !space.viewUser view s
  let next := { space with viewUser := fun v x => if v = view ∧ x = s then true else space.viewUser v x }
  (next, wasClosed)

def writeLeaf {Span Page Leaf : Type} [DecidableEq Span] [DecidableEq Page]
    (space : ViewSpace Span Page Leaf) (s : Span) (p : Page) (entry : Leaf) :
    ViewSpace Span Page Leaf :=
  { space with leafOf := fun x q => if x = s ∧ q = p then entry else space.leafOf x q }

theorem claim_preserves_single_translation {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (owner : Nat) (s x : Span) (p : Page) :
    (claimSpan space owner s).leafOf x p = space.leafOf x p :=
  rfl

theorem open_preserves_single_translation {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (view : Nat) (s x : Span) (p : Page) :
    (openSpan space view s).1.leafOf x p = space.leafOf x p :=
  rfl

theorem claim_isolates_owner_without_pku {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (owner : Nat) (s : Span) :
    let claimed := claimSpan space owner s
    claimed.canonicalUser s = false ∧
    claimed.viewUser owner s = true ∧
    (∀ v, v ≠ owner → claimed.viewUser v s = false) := by
  refine ⟨?_, ?_, ?_⟩
  · simp [claimSpan]
  · simp [claimSpan]
  · intro v hne
    simp [claimSpan, hne]

theorem two_rows_disjoint_isolation {Span Page Leaf : Type} [DecidableEq Span]
    (space : ViewSpace Span Page Leaf) (r1 r2 : Nat) (s1 s2 : Span)
    (hrows : r1 ≠ r2) (hspans : s1 ≠ s2) :
    let after := claimSpan (claimSpan space r1 s1) r2 s2
    after.viewUser r1 s1 = true ∧
    after.viewUser r1 s2 = false ∧
    after.viewUser r2 s2 = true ∧
    after.viewUser r2 s1 = false := by
  have hrows' : r2 ≠ r1 := Ne.symm hrows
  simp [claimSpan, hspans, hrows, hrows']

theorem writeLeaf_preserves_view_isolation {Span Page Leaf : Type} [DecidableEq Span] [DecidableEq Page]
    (space : ViewSpace Span Page Leaf) (s x : Span) (p : Page) (entry : Leaf) (v : Nat) :
    (writeLeaf space s p entry).viewUser v x = space.viewUser v x ∧
    (writeLeaf space s p entry).canonicalUser x = space.canonicalUser x :=
  ⟨rfl, rfl⟩

/-! ## Per-core PCID and INVPCID TLB coherency -/

/-- Abstract per-core TLB state tracking which `(view, addr)` translations
    may remain cached on this core. -/
structure CoreTlb (Addr : Type) where
  current : Nat
  pcid : Bool
  invpcid : Bool
  entered : Nat → Bool
  stale : Nat → Bool
  cached : Nat → Addr → Bool

/-- A core only caches translations for views it has entered. -/
def EnteredCoversCached {Addr : Type} (c : CoreTlb Addr) : Prop :=
  ∀ v a, c.cached v a = true → c.entered v = true

/-- A core is coherent against a set of invalidated addresses `invalid`:
    for any view `v` and invalidated address `a`, either the core does not cache
    `(v, a)` or `v` is non-current and marked stale (or PCID is off) so the core
    must flush `v` before executing user code in `v`. -/
def Coherent {Addr : Type} (c : CoreTlb Addr) (invalid : Addr → Prop) : Prop :=
  ∀ v a, invalid a → c.cached v a = true → v ≠ c.current ∧ (c.pcid = false ∨ c.stale v = true)

def cr3Flushes (pcid stale : Bool) : Bool := !pcid || stale

def enterView {Addr : Type} (c : CoreTlb Addr) (v : Nat) : CoreTlb Addr :=
  let flush := cr3Flushes c.pcid (c.stale v)
  { c with
    current := v
    entered := fun u => if u = v then true else c.entered u
    stale := fun u => if u = v then false else c.stale u
    cached := fun u a => if u = v ∧ flush = true then false else c.cached u a }

def enablePcidOnView0 {Addr : Type} (c : CoreTlb Addr) (_hcur : c.current = 0) : CoreTlb Addr :=
  { c with
    pcid := true
    entered := fun u => if u = 0 then true else c.entered u
    stale := fun u => u != 0 }

def invalidateAddr {Addr : Type} [DecidableEq Addr] (c : CoreTlb Addr) (target : Addr) :
    CoreTlb Addr :=
  if c.pcid && c.invpcid then
    { c with
      cached := fun v a =>
        if a = target ∧ (v = c.current ∨ c.entered v = true) then false else c.cached v a }
  else if c.pcid then
    { c with
      stale := fun v => if v = c.current then c.stale v else true
      cached := fun v a => if v = c.current ∧ a = target then false else c.cached v a }
  else
    { c with
      cached := fun v a => if a = target then false else c.cached v a }

def invalidateAll {Addr : Type} (c : CoreTlb Addr) : CoreTlb Addr :=
  if c.pcid && c.invpcid then
    { c with cached := fun _ _ => false }
  else if c.pcid then
    { c with
      stale := fun v => if v = c.current then c.stale v else true
      cached := fun v a => if v = c.current then false else c.cached v a }
  else
    { c with cached := fun _ _ => false }

theorem enterView_preserves_entered_covers {Addr : Type} (c : CoreTlb Addr) (v : Nat)
    (hcov : EnteredCoversCached c) :
    EnteredCoversCached (enterView c v) := by
  intro u a hcache
  simp only [enterView] at hcache ⊢
  by_cases huv : u = v
  · simp [huv]
  · simp [huv] at hcache ⊢
    exact hcov u a hcache

theorem enterView_preserves_coherent {Addr : Type} (c : CoreTlb Addr) (v : Nat)
    (invalid : Addr → Prop) (hcoh : Coherent c invalid) :
    Coherent (enterView c v) invalid := by
  intro u a hinv hcache
  simp only [enterView, cr3Flushes] at hcache ⊢
  by_cases huv : u = v
  · subst huv
    by_cases hfl : (!c.pcid || c.stale u) = true
    · simp [hfl] at hcache
    · simp [hfl] at hcache
      have ⟨_, hmust⟩ := hcoh u a hinv hcache
      rcases hmust with hpc | hst
      · simp [hpc] at hfl
      · simp [hst] at hfl
  · simp [huv] at hcache ⊢
    exact (hcoh u a hinv hcache).2

theorem enterView_flushes_invalid_for_entered {Addr : Type} (c : CoreTlb Addr) (v : Nat)
    (invalid : Addr → Prop) (hcoh : Coherent c invalid) :
    ∀ a, invalid a → (enterView c v).cached v a = false := by
  intro a hinv
  cases h : (enterView c v).cached v a with
  | false => rfl
  | true =>
    have ⟨hne, _⟩ := enterView_preserves_coherent c v invalid hcoh v a hinv h
    exact absurd rfl hne

theorem invalidateAddr_preserves_entered_covers {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) (target : Addr) (hcov : EnteredCoversCached c) :
    EnteredCoversCached (invalidateAddr c target) := by
  intro v a hcache
  unfold invalidateAddr at hcache ⊢
  cases hpc : c.pcid <;> cases hinv : c.invpcid <;> simp [hpc, hinv] at hcache ⊢
  · exact hcov v a hcache.2
  · exact hcov v a hcache.2
  · exact hcov v a hcache.2
  · exact hcov v a hcache.2

theorem invalidateAddr_sound {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) (target : Addr) (invalid : Addr → Prop)
    (hcov : EnteredCoversCached c) (hcoh : Coherent c invalid) :
    Coherent (invalidateAddr c target) (fun a => invalid a ∨ a = target) := by
  intro v a hinv hcache
  unfold invalidateAddr at hcache ⊢
  cases hpc : c.pcid <;> cases hin : c.invpcid <;> simp [hpc, hin] at hcache ⊢
  · cases hinv with
    | inl hold =>
      have ⟨hne, _⟩ := hcoh v a hold hcache.2
      exact hne
    | inr heq => exact absurd heq hcache.1
  · cases hinv with
    | inl hold =>
      have ⟨hne, _⟩ := hcoh v a hold hcache.2
      exact hne
    | inr heq => exact absurd heq hcache.1
  · cases hinv with
    | inl hold =>
      have ⟨hne, _⟩ := hcoh v a hold hcache.2
      exact ⟨hne, Or.inl hne⟩
    | inr heq =>
      have hne : v ≠ c.current := by
        rcases hcache.1 with h1 | h2
        · exact h1
        · exact absurd heq h2
      exact ⟨hne, Or.inl hne⟩
  · cases hinv with
    | inl hold =>
      have ⟨hne, hmust⟩ := hcoh v a hold hcache.2
      cases hmust with
      | inl hf => simp [hpc] at hf
      | inr hst => exact ⟨hne, hst⟩
    | inr heq =>
      have hent := hcov v a hcache.2
      rcases hcache.1 with h1 | ⟨_, h2⟩
      · exact absurd heq h1
      · simp [hent] at h2

theorem invalidateAddr_with_invpcid_drops_all_views {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) (target : Addr)
    (hpcid : c.pcid = true) (hinvpcid : c.invpcid = true)
    (hcov : EnteredCoversCached c) :
    ∀ v, (invalidateAddr c target).cached v target = false := by
  intro v
  simp only [invalidateAddr, hpcid, hinvpcid, Bool.and_self, ↓reduceIte]
  by_cases hent : c.entered v = true
  · simp [hent]
  · cases hc : c.cached v target with
    | false => split <;> rfl
    | true => exact absurd (hcov v target hc) hent

theorem invalidateAll_with_invpcid_drops_everything {Addr : Type}
    (c : CoreTlb Addr) (hpcid : c.pcid = true) (hinvpcid : c.invpcid = true) :
    ∀ v a, (invalidateAll c).cached v a = false := by
  intro v a
  simp [invalidateAll, hpcid, hinvpcid]

theorem enablePcidOnView0_preserves_entered_covers {Addr : Type}
    (c : CoreTlb Addr) (hcur : c.current = 0)
    (honly0 : ∀ v a, c.cached v a = true → v = 0) :
    EnteredCoversCached (enablePcidOnView0 c hcur) := by
  intro v a hcache
  have hv0 := honly0 v a hcache
  simp [enablePcidOnView0, hv0]

/-!
## 4. Active SMP Cross-Core TLB Shootdown Barrier Soundness

Models `kernel_smp.cesta` (`smp_tlb_generation`, `smp_tlb_served[core]`, `smp_tlb_owed`,
`smp_tlb_page`, `kernel_smp_tlb_service`) over `n` online cores `Fin n`.
-/

inductive ShootdownTarget (Addr : Type) where
  | one (va : Addr)
  | all

def applyTarget {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) : ShootdownTarget Addr → CoreTlb Addr
  | .one va => invalidateAddr c va
  | .all => invalidateAll c

def targetInvalid {Addr : Type} (invalid : Addr → Prop) : ShootdownTarget Addr → (Addr → Prop)
  | .one va => fun a => invalid a ∨ a = va
  | .all => fun _ => True

theorem invalidateAll_sound {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) :
    Coherent (invalidateAll c) (fun _ => True) := by
  intro v a _ hcache
  unfold invalidateAll at hcache ⊢
  cases hpc : c.pcid <;> cases hin : c.invpcid <;> simp [hpc, hin] at hcache ⊢
  exact ⟨hcache.1, Or.inl hcache.1⟩

theorem applyTarget_sound {Addr : Type} [DecidableEq Addr]
    (c : CoreTlb Addr) (tgt : ShootdownTarget Addr) (invalid : Addr → Prop)
    (hcov : EnteredCoversCached c) (hcoh : Coherent c invalid) :
    Coherent (applyTarget c tgt) (targetInvalid invalid tgt) := by
  cases tgt with
  | one va => exact invalidateAddr_sound c va invalid hcov hcoh
  | all => exact invalidateAll_sound c

structure SmpShootdown (n : Nat) (Addr : Type) where
  cores : Fin n → CoreTlb Addr
  served : Fin n → Nat
  generation : Nat
  target : ShootdownTarget Addr
  preInvalid : Addr → Prop

/-- Active-shootdown accounting invariant:
    - every core has `served c ≤ generation`,
    - cores that already served `generation` are coherent wrt `targetInvalid`,
    - cores that have not yet served `generation` are still coherent wrt `preInvalid`,
    - `owed` equals the number of cores with `served c ≠ generation`. -/
def ShootdownInv {n : Nat} {Addr : Type}
    (s : SmpShootdown n Addr) : Prop :=
  s.generation > 0 ∧
  (∀ c, EnteredCoversCached (s.cores c)) ∧
  (∀ c, s.served c ≤ s.generation) ∧
  (∀ c, s.served c = s.generation →
    Coherent (s.cores c) (targetInvalid s.preInvalid s.target)) ∧
  (∀ c, s.served c < s.generation →
    Coherent (s.cores c) s.preInvalid)

def unservedCount {n : Nat} {Addr : Type} (s : SmpShootdown n Addr) : Nat :=
  ((List.finRange n).filter (fun c => decide (s.served c < s.generation))).length

/-- Lock-free `kernel_smp_tlb_service()` on core `me`. -/
def smpService {n : Nat} {Addr : Type} [DecidableEq Addr]
    (s : SmpShootdown n Addr) (me : Fin n) : SmpShootdown n Addr :=
  if s.generation = 0 ∨ s.served me = s.generation then s
  else
    { s with
      cores := fun c => if c = me then applyTarget (s.cores c) s.target else s.cores c
      served := fun c => if c = me then s.generation else s.served c }

theorem smpService_idempotent {n : Nat} {Addr : Type} [DecidableEq Addr]
    (s : SmpShootdown n Addr) (me : Fin n) :
    smpService (smpService s me) me = smpService s me := by
  unfold smpService
  by_cases h : s.generation = 0 ∨ s.served me = s.generation
  · simp [h]
  · simp [h]

theorem smpService_preserves_inv {n : Nat} {Addr : Type} [DecidableEq Addr]
    (s : SmpShootdown n Addr) (me : Fin n) (hinv : ShootdownInv s) :
    ShootdownInv (smpService s me) := by
  rcases hinv with ⟨hgen, hcov, hle, hdone, hpend⟩
  unfold smpService
  by_cases h : s.generation = 0 ∨ s.served me = s.generation
  · simp only [h, ↓reduceIte]
    exact ⟨hgen, hcov, hle, hdone, hpend⟩
  · simp only [h, ↓reduceIte]
    have hlt_me : s.served me < s.generation :=
      Nat.lt_of_le_of_ne (hle me) (fun heq => h (Or.inr heq))
    refine ⟨hgen, ?_, ?_, ?_, ?_⟩
    · intro c
      by_cases hcm : c = me
      · subst hcm; simp only [↓reduceIte]
        cases htg : s.target with
        | one va => exact invalidateAddr_preserves_entered_covers (s.cores c) va (hcov c)
        | all =>
          intro v a hc
          unfold applyTarget invalidateAll at hc ⊢
          cases hpc : (s.cores c).pcid <;> cases hin : (s.cores c).invpcid <;>
            simp [hpc, hin] at hc ⊢
          exact hcov c v a hc.2
      · simp [hcm, hcov c]
    · intro c
      by_cases hcm : c = me
      · simp [hcm]
      · simp [hcm, hle c]
    · intro c hsc
      by_cases hcm : c = me
      · subst hcm; simp only [↓reduceIte]
        exact applyTarget_sound (s.cores c) s.target s.preInvalid (hcov c) (hpend c hlt_me)
      · simp only [hcm, ↓reduceIte] at hsc ⊢
        exact hdone c hsc
    · intro c hsc
      by_cases hcm : c = me
      · simp [hcm] at hsc
      · simp only [hcm, ↓reduceIte] at hsc ⊢
        exact hpend c hsc

/-- Barrier soundness: once `unservedCount s = 0` (`OWED = 0`), every online core `c : Fin n`
    has served `generation` and is coherent with the invalidated address(es). In particular,
    no online core holds a usable stale translation for the retired page(s), even across PCIDs. -/
theorem shootdown_barrier_all_cores_coherent {n : Nat} {Addr : Type}
    (s : SmpShootdown n Addr) (hinv : ShootdownInv s)
    (howed : unservedCount s = 0) :
    ∀ c : Fin n, Coherent (s.cores c) (targetInvalid s.preInvalid s.target) := by
  rcases hinv with ⟨_, _, hle, hdone, _⟩
  intro c
  have hnotlt : ¬ (s.served c < s.generation) := by
    intro hlt
    have hmem : c ∈ (List.finRange n).filter (fun x => decide (s.served x < s.generation)) := by
      rw [List.mem_filter]
      exact ⟨List.mem_finRange c, by simp [hlt]⟩
    have hpos : 0 < ((List.finRange n).filter (fun x => decide (s.served x < s.generation))).length :=
      List.length_pos_of_mem hmem
    unfold unservedCount at howed
    omega
  have heq : s.served c = s.generation := Nat.le_antisymm (hle c) (Nat.not_lt.mp hnotlt)
  exact hdone c heq

/-- Corollary for retired-frame safety: after a shootdown barrier (`OWED = 0`) for `target`,
    no online core `c` can currently hold a cached translation to the invalidated page in its
    active view, and any view entered on core `c` subsequently will flush before use. -/
theorem shootdown_retired_page_unusable_everywhere {n : Nat} {Addr : Type} [DecidableEq Addr]
    (s : SmpShootdown n Addr) (va : Addr) (hinv : ShootdownInv s)
    (htgt : s.target = .one va) (howed : unservedCount s = 0) :
    ∀ (c : Fin n) (v : Nat),
      (enterView (s.cores c) v).cached v va = false := by
  intro c v
  have hcoh := shootdown_barrier_all_cores_coherent s hinv howed c
  have hinv_va : targetInvalid s.preInvalid s.target va := by
    simp [htgt, targetInvalid]
  exact enterView_flushes_invalid_for_entered (s.cores c) v (targetInvalid s.preInvalid s.target)
    hcoh va hinv_va

end Mettapedia.Machines.Kernel.ProtectionViews

#print axioms Mettapedia.Machines.Kernel.ProtectionViews.merged_absent_takes_canonical
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.merged_same_frame_preserves_opening
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.merged_private_copy_keeps_frame
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.merged_closed_stays_closed
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.claim_isolates_owner_without_pku
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.two_rows_disjoint_isolation
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.enterView_flushes_invalid_for_entered
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.invalidateAddr_sound
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.invalidateAddr_with_invpcid_drops_all_views
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.invalidateAll_with_invpcid_drops_everything
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.enablePcidOnView0_preserves_entered_covers
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.smpService_idempotent
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.smpService_preserves_inv
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.shootdown_barrier_all_cores_coherent
#print axioms Mettapedia.Machines.Kernel.ProtectionViews.shootdown_retired_page_unusable_everywhere
