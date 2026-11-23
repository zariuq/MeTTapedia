import Std

/-!
Small independent models of the review invariants. This is not a refinement
proof of SWI's C implementation, its atomics, allocator, GC, or WAM.
Clause occurrences are retained as list entries; equal payloads are not deduplicated.
-/
set_option autoImplicit false

namespace Mettapedia.Languages.Prolog.SWI.SnapshotContracts

section Coverage
variable {α : Type} (kept visible : α → Bool)

/-- Keeping every visible occurrence suffices, including order and multiplicity. -/
theorem filtering_complete (xs : List α)
    (h : ∀ x ∈ xs, visible x = true → kept x = true) :
    (xs.filter kept).filter visible = xs.filter visible := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have tail : ∀ x ∈ xs, visible x = true → kept x = true := by
      intro x hx hv
      exact h x (by simp [hx]) hv
    by_cases hv : visible a = true
    · have hk := h a (by simp) hv
      simp [hv, hk, ih tail]
    · by_cases hk : kept a = true <;> simp [hv, hk, ih tail]

/-- Coverage is necessary as well: a visible omitted occurrence cannot be hidden
by returning other clauses with the same payload. -/
theorem filtering_complete_iff (xs : List α) :
    (xs.filter kept).filter visible = xs.filter visible ↔
      ∀ x ∈ xs, visible x = true → kept x = true := by
  constructor
  · intro eq x hx hv
    have member : x ∈ (xs.filter kept).filter visible := by
      rw [eq]
      simp [hx, hv]
    exact (List.mem_filter.mp (List.mem_filter.mp member).1).2
  · exact filtering_complete kept visible xs

/-- Thus an unaffected bucket needs no fallback. The predicate includes
visibility and the query's bucket/key condition. -/
theorem unaffected_bucket_complete (xs : List α) (query : α → Bool)
    (noMissing : ∀ x ∈ xs, (visible x && query x) = true → kept x = true) :
    (xs.filter kept).filter (fun x => visible x && query x) =
      xs.filter (fun x => visible x && query x) :=
  filtering_complete kept (fun x => visible x && query x) xs noMissing
end Coverage

structure Clause where
  born : Nat
  erased : Nat
deriving DecidableEq, Repr

def visibleAt (g : Nat) (c : Clause) : Prop := c.born ≤ g ∧ g < c.erased

/-- If every omitted clause was erased by E, g ≥ E safely excludes them.
This is sufficient, not the most precise possible coverage criterion. -/
theorem global_cutoff_sound (g E : Nat) (omitted : List Clause)
    (bound : ∀ c ∈ omitted, c.erased ≤ E) (newer : E ≤ g) :
    ∀ c ∈ omitted, ¬ visibleAt g c := by
  intro c hc hv
  have he := bound c hc
  unfold visibleAt at hv
  omega

section Roots
variable {α : Type} (visible : Nat → α → Prop)

def required (roots : Nat → Prop) (c : α) : Prop :=
  ∃ g, roots g ∧ visible g c

def safe (roots : Nat → Prop) (retained : α → Prop) : Prop :=
  ∀ g c, roots g → visible g c → retained c

/-- Visible clauses of live roots are the unique least safe retention set. -/
theorem required_is_safe (roots : Nat → Prop) : safe visible roots (required visible roots) := by
  intro g c hr hv
  exact ⟨g, hr, hv⟩

theorem required_is_least (roots : Nat → Prop) (retained : α → Prop)
    (h : safe visible roots retained) :
    ∀ c, required visible roots c → retained c := by
  intro c hc
  obtain ⟨g, hg, hv⟩ := hc
  exact h g c hg hv

/-- Duplicate handles at one global generation add no visible clauses.
An implementation may coalesce such roots, but must retain their lifetime count. -/
theorem duplicate_generation_root_is_redundant (roots : List Nat) (g : Nat) (c : α) :
    required visible (fun h => h ∈ g :: g :: roots) c ↔
      required visible (fun h => h ∈ g :: roots) c := by
  simp [required]
end Roots

structure Roots where
  handle : Bool
  pending : Bool
  frame : Bool
deriving DecidableEq, Repr

def isRooted (s : Roots) : Bool := s.handle || s.pending || s.frame
def acquirePending (s : Roots) : Roots := { s with pending := true }
def closeHandle (s : Roots) : Roots := { s with handle := false }
def publishFrame (s : Roots) : Roots := { s with frame := true }
def releasePending (s : Roots) : Roots := { s with pending := false }

theorem pending_survives_close (s : Roots) :
    isRooted (closeHandle (acquirePending s)) = true := by
  simp [isRooted, closeHandle, acquirePending]

theorem publish_before_release_safe (s : Roots) :
    isRooted (releasePending (publishFrame (closeHandle (acquirePending s)))) = true := by
  simp [isRooted, releasePending, publishFrame, closeHandle, acquirePending]

/-- Releasing the last old root before publishing the frame has a GC gap. -/
theorem release_before_publish_gap :
    isRooted (releasePending (closeHandle (acquirePending ⟨true,false,false⟩))) = false := by
  decide

theorem pending_is_necessary_before_frame (s : Roots)
    (closed : s.handle = false) (unpublished : s.frame = false)
    (rooted : isRooted s = true) : s.pending = true := by
  simpa [isRooted, closed, unpublished] using rooted

structure Frame where
  captured : Nat
  generation : Nat
  frozen : Bool
deriving DecidableEq, Repr

def refresh (now : Nat) (f : Frame) : Frame :=
  if f.frozen then f else { f with generation := now }

theorem refresh_preserves_frozen (f : Frame) (h : f.frozen = true) (now : Nat) :
    refresh now f = f := by simp [refresh, h]

theorem refresh_sequence_preserves_frozen (f : Frame) (h : f.frozen = true)
    (events : List Nat) : events.foldl (fun frame now => refresh now frame) f = f := by
  induction events with
  | nil => rfl
  | cons a events ih => simpa [List.foldl, refresh_preserves_frozen f h a] using ih

theorem unguarded_refresh_changes_view :
    ({ (⟨1,1,true⟩ : Frame) with generation := 99 }).generation ≠ 1 := by decide

section Retirement
variable {α : Type} (valid : α → Bool)

/-- Atomic insertion and retirement commute for a valid new index. This
models the predicate lock around the complete read/modify/publish step. -/
theorem locked_insert_retire_commute (published : List α) (new : α)
    (hn : valid new = true) :
    (published ++ [new]).filter valid = published.filter valid ++ [new] := by
  simp [List.filter_append, hn]
end Retirement

def oldArray : List Nat := [0]
def invalidIndexRetired : List Nat := oldArray.filter (· != 0)
def staleCopiedArray : List Nat := oldArray ++ [1]

/-- Copy old array; retire index in old array; publish the stale copy.
The retired index reappears. Each step corresponds to the identified
unlocked retirement/concurrent copy publication schedule. -/
theorem unlocked_retirement_loses_update :
    0 ∉ invalidIndexRetired ∧ 0 ∈ staleCopiedArray := by decide

/-- If retirement occurs between copyIndex's count and copy passes,
the allocation count and the number of copied entries differ. -/
theorem unlocked_retirement_breaks_two_pass_count :
    (oldArray ++ [1]).length ≠ (invalidIndexRetired ++ [1]).length := by decide

structure FillWait where
  filling : Bool
  writerHasPredicate : Bool
  fillerNeedsPredicate : Bool
deriving DecidableEq

def waitCycle (s : FillWait) : Bool :=
  s.filling && s.writerHasPredicate && s.fillerNeedsPredicate

theorem taking_retirement_lock_before_finishing_can_deadlock :
    waitCycle ⟨true,true,true⟩ = true := by decide

theorem finishing_before_retirement_breaks_that_cycle (s : FillWait) :
    waitCycle {s with filling := false} = false := by simp [waitCycle]

/-- Owner identity is not necessary for global-root GC coverage, but it
does matter if lookup selects a thread-local namespace. -/
def localValue (owner generation : Nat) : Nat :=
  if owner = 0 then (if generation ≤ 10 then 1 else 2) else 99
theorem equal_generation_does_not_identify_local_namespaces :
    localValue 0 5 ≠ localValue 1 5 := by decide

end Mettapedia.Languages.Prolog.SWI.SnapshotContracts
