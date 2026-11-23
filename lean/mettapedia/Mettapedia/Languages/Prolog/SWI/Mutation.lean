import Std

set_option autoImplicit false

/-!
# Mutation lifetime and erase-generation obligations

These are protocol models, not C refinement proofs. The lifetime model exposes
post-publication accesses to a Clause separately from accesses to its list
ClauseRef. A local clause reference keeps the Clause alive, but does not own
that list node. It describes the obligation behind PR 1 revision 2 (`ee182ae`)
and the reported post-unlock `retract_clause` use-after-free on `cf6960c`.
The latter fix is not certified here: its acquisition and release sites, error
paths, callers and GC/predicate-access interaction still need a source mapping.
This model permits list disposal after publication and omits generation roots.
A maintained access generation could provide alternative protection; the model
does not explain why the actual C collector missed such protection.

The generation model checks the serialized `>` guard in PR 5 (`1ba322c`),
including idempotence and absence of visibility resurrection. It abstracts the
ordinary branch and the analogous local-transaction comparison as natural
numbers, without overflow, generation-space exhaustion or special discard modes.
-/

namespace Mettapedia.Languages.Prolog.SWI.Mutation

namespace Lifetime

inductive Pc where
  | idle | preparing | published | done
  deriving DecidableEq

structure Proto where
  holdClause : Bool
  readListNode : Bool
  releaseEarly : Bool

def fixed : Proto := ⟨true, false, false⟩
def noHold : Proto := { fixed with holdClause := false }
def borrowedNode : Proto := { fixed with readListNode := true }
def earlyRelease : Proto := { fixed with releaseEarly := true }

structure St where
  pc : Pc := .idle
  /-- The list node is linked, or is awaiting its deferred disposal. -/
  linked : Bool := true
  nodeLive : Bool := true
  owned : Bool := false
  /-- Records an invalid dereference when it occurs, even if ownership changes later. -/
  bad : Bool := false
  deriving DecidableEq

/-- The list node and the local reference are distinct owners of the Clause. -/
def St.clauseLive (s : St) : Bool := s.nodeLive || s.owned

def initial : St := {}

/-- After publish, GC and reentrant callbacks may remove the list owner at any
    time. Protection is acquired during preparation, before that boundary.
    Reads deliberately have no liveness preconditions. -/
inductive Step (P : Proto) : St → St → Prop where
  | prepare (s : St) (h : s.pc = .idle) :
      Step P s { s with pc := .preparing, owned := P.holdClause }
  | publish (s : St) (h : s.pc = .preparing) :
      Step P s { s with pc := .published }
  | unlink (s : St) (h : s.pc = .published ∨ s.pc = .done) (hl : s.linked = true) :
      Step P s { s with linked := false }
  | freeNode (s : St) (h : s.linked = false) (hn : s.nodeLive = true) :
      Step P s { s with nodeLive := false }
  | readClause (s : St) (h : s.pc = .published) :
      Step P s { s with bad := s.bad || !s.clauseLive }
  | readNode (s : St) (h : s.pc = .published) (hp : P.readListNode = true) :
      Step P s { s with bad := s.bad || !s.nodeLive }
  | release (s : St) (h : s.pc = .published) (hp : P.releaseEarly = true) :
      Step P s { s with owned := false }
  | finish (s : St) (h : s.pc = .published) :
      Step P s { s with pc := .done, owned := false }

inductive Reach (P : Proto) : St → St → Prop where
  | refl (s : St) : Reach P s s
  | tail {s t u : St} : Reach P s t → Step P t u → Reach P s u

def Safe (s : St) : Prop := s.bad = false

structure Inv (s : St) : Prop where
  preparing : s.pc = .preparing → s.owned = true
  published : s.pc = .published → s.owned = true
  safe : Safe s

theorem initial_inv : Inv initial := by
  refine ⟨?_, ?_, rfl⟩ <;> intro h <;> cases h

theorem Inv.step {s t : St} (h : Inv s) (st : Step fixed s t) : Inv t := by
  obtain ⟨ha, hp, hs⟩ := h
  cases st with
  | prepare hc =>
    refine ⟨?_, ?_, hs⟩
    · intro _; rfl
    · intro hx; cases hx
  | publish hc =>
    refine ⟨?_, fun _ => ha hc, hs⟩
    intro hx; cases hx
  | unlink _ _ => exact ⟨ha, hp, hs⟩
  | freeNode _ _ => exact ⟨ha, hp, hs⟩
  | readClause hc =>
    refine ⟨ha, hp, ?_⟩
    have ho := hp hc
    simpa [Safe, St.clauseLive, ho] using hs
  | readNode _ hx => cases hx
  | release _ hx => cases hx
  | finish _ =>
    refine ⟨?_, ?_, hs⟩ <;> intro hx <;> cases hx

/-- Holding a local Clause reference until the final access is sufficient in
    this model for every GC/callback interleaving, without reading a borrowed node. -/
theorem fixed_safe {s : St} (hr : Reach fixed initial s) : Safe s := by
  have hi : Inv s := by
    induction hr with
    | refl => exact initial_inv
    | tail _ st ih => exact ih.step st
  exact hi.safe

def published (P : Proto) : St := { pc := .published, owned := P.holdClause }
def unlinked (P : Proto) : St := { published P with linked := false }
def disposed (P : Proto) : St := { unlinked P with nodeLive := false }

theorem published_reach (P : Proto) : Reach P initial (published P) := by
  have h : Reach P initial { initial with pc := .preparing, owned := P.holdClause } :=
    Reach.tail (.refl _) (Step.prepare _ rfl)
  exact Reach.tail h (Step.publish _ rfl)

theorem disposed_reach (P : Proto) : Reach P initial (disposed P) := by
  have h : Reach P initial (unlinked P) :=
    Reach.tail (published_reach P) (Step.unlink _ (Or.inl rfl) rfl)
  exact Reach.tail h (Step.freeNode _ rfl rfl)

/-- Unlink/free/read is admitted when the post-publication reader owns no reference. -/
theorem no_hold_unsafe : ∃ s, Reach noHold initial s ∧ ¬ Safe s := by
  let s : St := { disposed noHold with bad := true }
  refine ⟨s, Reach.tail (disposed_reach noHold) (Step.readClause _ rfl), ?_⟩
  intro h; cases h

/-- Pinning the Clause does not pin its borrowed list ClauseRef. -/
theorem clause_pin_does_not_pin_node : ∃ s, Reach borrowedNode initial s ∧
    s.clauseLive = true ∧ s.nodeLive = false ∧ ¬ Safe s := by
  let s : St := { disposed borrowedNode with bad := true }
  refine ⟨s, Reach.tail (disposed_reach borrowedNode) (Step.readNode _ rfl rfl),
    rfl, rfl, ?_⟩
  intro h; cases h

/-- A reference released before the final metadata/callback access is too early. -/
theorem early_release_unsafe : ∃ s, Reach earlyRelease initial s ∧ ¬ Safe s := by
  let s1 : St := { disposed earlyRelease with owned := false }
  let s2 : St := { s1 with bad := true }
  have h1 : Reach earlyRelease initial s1 :=
    Reach.tail (disposed_reach earlyRelease) (Step.release _ rfl rfl)
  refine ⟨s2, Reach.tail h1 (Step.readClause _ rfl), ?_⟩
  intro h; cases h

/-- The list node may die during postwork while its Clause stays valid. -/
theorem fixed_survives_node_disposal : ∃ s, Reach fixed initial s ∧
    Safe s ∧ s.nodeLive = false ∧ s.clauseLive = true ∧ s.pc = .published := by
  let s : St := { disposed fixed with bad := false }
  have hr : Reach fixed initial s := Reach.tail (disposed_reach fixed) (Step.readClause _ rfl)
  exact ⟨s, hr, fixed_safe hr, rfl, rfl, rfl⟩

/-- Disposing the last owner after finish is permitted: no postwork remains. -/
theorem fixed_can_release_last_owner : ∃ s, Reach fixed initial s ∧
    Safe s ∧ s.clauseLive = false ∧ s.pc = .done := by
  let s : St := { disposed fixed with pc := .done, owned := false }
  have hr : Reach fixed initial s := Reach.tail (disposed_reach fixed) (Step.finish _ rfl)
  exact ⟨s, hr, fixed_safe hr, rfl, rfl⟩

end Lifetime

namespace EraseGeneration

structure St where
  generation : Nat
  erased : Nat
  deriving DecidableEq

/-- The two comparisons changed by 1ba322c, in their respective generation spaces. -/
def fixed (s : St) : St :=
  if s.generation < s.erased then ⟨s.generation + 1, s.generation + 1⟩ else s

def stock (s : St) : St :=
  if s.generation ≤ s.erased then ⟨s.generation + 1, s.generation + 1⟩ else s

def visible (born query : Nat) (s : St) : Prop := born ≤ query ∧ query < s.erased

theorem already_erased_stable (s : St) (he : s.erased ≤ s.generation) : fixed s = s := by
  simp [fixed, Nat.not_lt.mpr he]

theorem fixed_erased_le_generation (s : St) : (fixed s).erased ≤ (fixed s).generation := by
  unfold fixed
  split
  · exact Nat.le_refl _
  · omega

theorem fixed_idempotent (s : St) : fixed (fixed s) = fixed s :=
  already_erased_stable _ (fixed_erased_le_generation s)

theorem fixed_erasure_never_increases (s : St) : (fixed s).erased ≤ s.erased := by
  unfold fixed
  split
  · simp; omega
  · exact Nat.le_refl _

/-- Erasing cannot make a formerly invisible clause visible in any fixed view. -/
theorem fixed_no_resurrection (s : St) (born query : Nat) :
    visible born query (fixed s) → visible born query s := by
  intro h
  exact ⟨h.1, Nat.lt_of_lt_of_le h.2 (fixed_erasure_never_increases s)⟩

/-- A retry at the current erase generation brings the clause back in that view. -/
theorem stock_retry_resurrects :
    let s : St := ⟨1, 1⟩
    ¬ visible 0 1 s ∧ visible 0 1 (stock s) ∧ stock (stock s) ≠ stock s := by
  simp [visible, stock]

/-- Refreshing a frame can invalidate a saved next clause's visibility even
    while an older predicate-access generation still sees and protects it.
    This refutes the visibility inference alone, not physical memory safety. -/
theorem refresh_does_not_preserve_saved_visibility :
    let s : St := ⟨2, 1⟩
    visible 0 0 s ∧ ¬ visible 0 1 s := by simp [visible]


/-- A clause born in the refreshed view is not protected by the older access
    view. Generation-list GC would consider it invisible at that sole root.
    This is a visibility/GC-eligibility witness, not a proved C execution:
    cursor enumeration and every other root must be checked at the source. -/
theorem frame_refresh_can_outgrow_access_pin :
    let clause : St := ⟨3, 2⟩
    visible 1 1 clause ∧ ¬ visible 1 0 clause ∧ clause.erased < clause.generation := by
  simp [visible]

end EraseGeneration
end Mettapedia.Languages.Prolog.SWI.Mutation
