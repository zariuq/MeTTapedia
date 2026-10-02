import Mettapedia.GSLT.Causality.ResourceInteraction
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Multiset.Filter

/-!
# Finite resource selection and atomic consumption

Selection enumerates size-`k` subbags of the matches in a fixed snapshot. It
does not choose a traversal order. Equal occurrences retain their combinatorial
multiplicity; use occurrence identifiers in the resource type when their
identity must survive the observation.

Consumption validates an entire selected bag against the current store before
returning a new store. This is a sequential atomic specification, not a proof
of a concurrent native implementation. Predicate bindings are already grounded:
each binding determines its own eligible bag, and one selected bag uses that
same binding throughout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceSelection

open ResourceInteraction

universe u

variable {R : Type u}

/-- All matches of a grounded Boolean predicate in one snapshot. -/
def allMatches (predicate : R → Bool) (snapshot : Multiset R) : Multiset R :=
  snapshot.filter fun resource => predicate resource = true

/-- Every size-`k` choice, retaining multiplicity of equal occurrence choices. -/
def choices (predicate : R → Bool) (k : ℕ) (snapshot : Multiset R) :
    Multiset (Multiset R) :=
  (allMatches predicate snapshot).powersetCard k

/-- Exact selection means availability, exact cardinality, and one predicate
holding of every selected resource. -/
theorem mem_choices (predicate : R → Bool) (k : ℕ)
    (snapshot picked : Multiset R) :
    picked ∈ choices predicate k snapshot ↔
      picked ≤ snapshot ∧ picked.card = k ∧
        ∀ resource ∈ picked, predicate resource = true := by
  simp only [choices, Multiset.mem_powersetCard, allMatches, Multiset.le_filter]
  tauto

/-- Enumeration size is combinatorial even when several choices have equal
payload observations. This counts candidates, not execution time. -/
theorem card_choices (predicate : R → Bool) (k : ℕ) (snapshot : Multiset R) :
    (choices predicate k snapshot).card = (allMatches predicate snapshot).card.choose k :=
  Multiset.card_powersetCard _ _

@[simp] theorem choices_zero (predicate : R → Bool) (snapshot : Multiset R) :
    choices predicate 0 snapshot = {0} :=
  Multiset.powersetCard_zero_left _

/-- Insufficient matches yield no candidate, rather than a smaller take. -/
theorem choices_eq_zero_of_insufficient (predicate : R → Bool) (k : ℕ)
    (snapshot : Multiset R) (short : (allMatches predicate snapshot).card < k) :
    choices predicate k snapshot = 0 := by
  apply Multiset.card_eq_zero.mp
  rw [card_choices]
  exact Nat.choose_eq_zero_of_lt short

theorem allMatches_le (predicate : R → Bool) (snapshot : Multiset R) :
    allMatches predicate snapshot ≤ snapshot :=
  Multiset.filter_le _ _

theorem allMatches_mem_choices (predicate : R → Bool) (snapshot : Multiset R) :
    allMatches predicate snapshot ∈
      choices predicate (allMatches predicate snapshot).card snapshot := by
  exact Multiset.mem_powersetCard.mpr ⟨le_rfl, rfl⟩

/-- At a fixed grounded predicate and snapshot, taking the full match count
has exactly one candidate. Neither premise is implicit in the law. -/
theorem choices_allMatches (predicate : R → Bool) (snapshot : Multiset R) :
    choices predicate (allMatches predicate snapshot).card snapshot =
      {allMatches predicate snapshot} :=
  Multiset.powersetCard_self _

/-- Distinct resource identities make distinct selected bags distinct
candidates. Equal-payload occurrences may still have different identities. -/
theorem choices_nodup (predicate : R → Bool) (k : ℕ) (snapshot : Multiset R)
    (identities : snapshot.Nodup) : (choices predicate k snapshot).Nodup :=
  (identities.filter _).powersetCard

variable [DecidableEq R]

/-- Validate every requested occurrence, then remove the complete bag at once.
`none` has no successor store and therefore performs no partial consumption. -/
def commit (picked current : Multiset R) : Option (Multiset R) :=
  if picked ≤ current then some (current - picked) else none

/-- An explicit caller-facing form keeps the input store on failed validation. -/
def commitOrKeep (picked current : Multiset R) : Bool × Multiset R :=
  match commit picked current with
  | none => (false, current)
  | some remaining => (true, remaining)

theorem commit_eq_some_iff (picked current remaining : Multiset R) :
    commit picked current = some remaining ↔
      picked ≤ current ∧ remaining = current - picked := by
  unfold commit
  split <;> simp_all [eq_comm]

@[simp] theorem commit_eq_none_iff (picked current : Multiset R) :
    commit picked current = none ↔ ¬ picked ≤ current := by
  unfold commit
  split <;> simp_all

theorem commitOrKeep_of_unavailable (picked current : Multiset R)
    (unavailable : ¬ picked ≤ current) :
    commitOrKeep picked current = (false, current) := by
  simp [commitOrKeep, commit, unavailable]

theorem commit_conservation {picked current remaining : Multiset R}
    (success : commit picked current = some remaining) :
    remaining + picked = current := by
  obtain ⟨available, rfl⟩ := (commit_eq_some_iff _ _ _).mp success
  exact tsub_add_cancel_of_le available

theorem commit_count {picked current remaining : Multiset R}
    (success : commit picked current = some remaining) (resource : R) :
    remaining.count resource + picked.count resource = current.count resource := by
  simpa only [Multiset.count_add] using
    congrArg (Multiset.count resource) (commit_conservation success)

theorem commit_card {picked current remaining : Multiset R}
    (success : commit picked current = some remaining) :
    remaining.card + picked.card = current.card := by
  simpa only [Multiset.card_add] using
    congrArg Multiset.card (commit_conservation success)

/-- Positive consumption strictly decreases this finite store's cardinality.
Zero consumption instead needs progress in the caller's control state. -/
theorem commit_strictly_decreases_card {picked current remaining : Multiset R}
    (success : commit picked current = some remaining) (positive : 0 < picked.card) :
    remaining.card < current.card := by
  have size := commit_card success
  omega

@[simp] theorem commit_zero (current : Multiset R) : commit 0 current = some current := by
  simp [commit, Multiset.zero_le]

@[simp] theorem commit_frame (picked frame : Multiset R) :
    commit picked (picked + frame) = some frame := by
  simp [commit, Multiset.zero_le]

/-- Taking all at this snapshot leaves no match of this grounded predicate. -/
theorem allMatches_after_commit (predicate : R → Bool) (snapshot : Multiset R) :
    allMatches predicate (snapshot - allMatches predicate snapshot) = 0 := by
  unfold allMatches
  rw [Multiset.filter_sub]
  simp only [Multiset.filter_filter, and_self]
  apply Multiset.ext.mpr
  intro resource
  simp

theorem commit_allMatches (predicate : R → Bool) (snapshot : Multiset R) :
    commit (allMatches predicate snapshot) snapshot =
      some (snapshot - allMatches predicate snapshot) := by
  simp [commit, allMatches_le]

/-- A fresh frame does not invalidate an already available take. It need not
preserve the stronger claim that a former take-all still takes every match. -/
theorem commit_add_frame {picked current remaining : Multiset R}
    (success : commit picked current = some remaining) (frame : Multiset R) :
    commit picked (current + frame) = some (remaining + frame) := by
  obtain ⟨available, rfl⟩ := (commit_eq_some_iff _ _ _).mp success
  apply (commit_eq_some_iff _ _ _).mpr
  refine ⟨le_trans available (Multiset.le_add_right _ _), ?_⟩
  exact tsub_add_eq_add_tsub available

/-! ## Revalidating a complete match observation

An available selected bag and a current complete match set are different
contracts. The latter also detects newly inserted matches, including changes
to a previously empty result. Unrelated resources need not invalidate it.
-/

/-- Revalidate the captured complete match set, then atomically consume it.
Unlike `commit`, this checks the predicate's whole current observation. -/
def commitAll (predicate : R → Bool) (captured current : Multiset R) :
    Option (Multiset R) :=
  if captured = allMatches predicate current then commit captured current else none

/-- Successful complete-match publication certifies both completeness and
the exact residual store. -/
theorem commitAll_eq_some_iff (predicate : R → Bool)
    (captured current remaining : Multiset R) :
    commitAll predicate captured current = some remaining ↔
      captured = allMatches predicate current ∧ remaining = current - captured := by
  unfold commitAll
  split
  · next currentMatches =>
      rw [commit_eq_some_iff]
      constructor
      · rintro ⟨_, remainingEq⟩
        exact ⟨currentMatches, remainingEq⟩
      · rintro ⟨_, remainingEq⟩
        exact ⟨currentMatches ▸ allMatches_le predicate current, remainingEq⟩
  · next changed => simp [changed]

/-- Stale complete-match observations perform no partial consumption. -/
theorem commitAll_eq_none_iff (predicate : R → Bool) (captured current : Multiset R) :
    commitAll predicate captured current = none ↔
      captured ≠ allMatches predicate current := by
  unfold commitAll
  split
  · next currentMatches =>
      rw [commit_eq_none_iff]
      have available : captured ≤ current := currentMatches ▸ allMatches_le predicate current
      constructor
      · intro unavailable
        exact False.elim (unavailable available)
      · intro changed
        exact False.elim (changed currentMatches)
  · next changed => simp [changed]

/-- A successful complete-match commit leaves no current match. -/
theorem commitAll_leaves_no_match {predicate : R → Bool}
    {captured current remaining : Multiset R}
    (success : commitAll predicate captured current = some remaining) :
    allMatches predicate remaining = 0 := by
  obtain ⟨rfl, rfl⟩ := (commitAll_eq_some_iff _ _ _ _).mp success
  exact allMatches_after_commit predicate current

omit [DecidableEq R] in
/-- Matching snapshots depend only on matching resources, not on a global
revision number. -/
theorem allMatches_add (predicate : R → Bool) (snapshot frame : Multiset R) :
    allMatches predicate (snapshot + frame) =
      allMatches predicate snapshot + allMatches predicate frame := by
  simp [allMatches]

/-- Changes outside the observed predicate preserve a complete-match commit. -/
theorem commitAll_add_irrelevant_frame {predicate : R → Bool}
    {captured current remaining : Multiset R}
    (success : commitAll predicate captured current = some remaining)
    (frame : Multiset R) (irrelevant : allMatches predicate frame = 0) :
    commitAll predicate captured (current + frame) = some (remaining + frame) := by
  obtain ⟨matchCurrent, residual⟩ := (commitAll_eq_some_iff _ _ _ _).mp success
  apply (commitAll_eq_some_iff _ _ _ _).mpr
  constructor
  · rw [allMatches_add, irrelevant, add_zero]
    exact matchCurrent
  · exact ((commit_eq_some_iff _ _ _).mp
      (commit_add_frame ((commit_eq_some_iff _ _ _).mpr
        ⟨matchCurrent ▸ allMatches_le predicate current, residual⟩) frame)).2

/-- A newly inserted matching occurrence invalidates the former complete
match claim, even when every formerly selected occurrence is still present. -/
theorem commitAll_rejects_new_matches (predicate : R → Bool)
    (snapshot frame : Multiset R) (newMatch : allMatches predicate frame ≠ 0) :
    commitAll predicate (allMatches predicate snapshot) (snapshot + frame) = none := by
  apply (commitAll_eq_none_iff _ _ _).mpr
  rw [allMatches_add]
  intro same
  have noNewMatches : allMatches predicate frame = 0 := by
    apply add_left_cancel (a := allMatches predicate snapshot)
    simpa only [add_zero] using same.symm
  exact newMatch noNewMatches

/-- Exploration gives every selected alternative its own residual snapshot.
The alternatives do not successively consume one shared mutable store. -/
def branches (predicate : R → Bool) (k : ℕ) (snapshot : Multiset R) :
    Multiset (Multiset R × Multiset R) :=
  (choices predicate k snapshot).map fun picked => (picked, snapshot - picked)

theorem mem_branches (predicate : R → Bool) (k : ℕ)
    (snapshot picked remaining : Multiset R) :
    (picked, remaining) ∈ branches predicate k snapshot ↔
      picked ∈ choices predicate k snapshot ∧ remaining = snapshot - picked := by
  simp only [branches, Multiset.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨candidate, member, equal, result⟩
    subst candidate
    exact ⟨member, result.symm⟩
  · rintro ⟨member, rfl⟩
    exact ⟨picked, member, rfl, rfl⟩

theorem branch_commit {predicate : R → Bool} {k : ℕ}
    {snapshot picked remaining : Multiset R}
    (branch : (picked, remaining) ∈ branches predicate k snapshot) :
    commit picked snapshot = some remaining := by
  obtain ⟨member, result⟩ := (mem_branches _ _ _ _ _).mp branch
  exact (commit_eq_some_iff _ _ _).mpr ⟨((mem_choices _ _ _ _).mp member).1, result⟩

/-! ## Grounded binding instances in the existing resource firing semantics -/

/-- Each site fixes both a binding and the requested count. Its instances name
the exact matching resource bag to consume. There is no unification algorithm
hidden in the Boolean predicate. -/
def selectionSystem {Binding : Type u} (accepts : Binding → R → Bool) :
    System R where
  Site := Binding × ℕ
  Instance := fun site =>
    {picked : Multiset R // picked.card = site.2 ∧
      ∀ resource ∈ picked, accepts site.1 resource = true}
  consume := fun picked => picked.val
  read := fun _ => 0
  produce := fun _ => 0

variable {Binding : Type u} (accepts : Binding → R → Bool)

omit [DecidableEq R] in
@[simp] theorem selectionSystem_enables {site : Binding × ℕ}
    (firing : (selectionSystem accepts).Instance site) (current : Multiset R) :
    (selectionSystem accepts).Enables current firing ↔ firing.val ≤ current := by
  simp [System.Enables, selectionSystem]

@[simp] theorem selectionSystem_fire {site : Binding × ℕ}
    (firing : (selectionSystem accepts).Instance site) (current : Multiset R) :
    (selectionSystem accepts).fire current firing = current - firing.val := by
  simp [System.fire, selectionSystem]

/-- Exact selection and residual stores agree in both directions with the
existing resource-system firing relation, at a fixed binding and count.
This is relational adequacy. A collective resource type may identify distinct
choices of equal occurrences; preserving those identities requires retaining
them in `R`, as in the accompanying controls. -/
theorem selection_iff_firing (binding : Binding) (k : ℕ)
    (current remaining : Multiset R) :
    (∃ picked ∈ choices (accepts binding) k current,
      remaining = current - picked) ↔
    ∃ firing : (selectionSystem accepts).Instance (binding, k),
      (selectionSystem accepts).Enables current firing ∧
        remaining = (selectionSystem accepts).fire current firing := by
  constructor
  · rintro ⟨picked, member, result⟩
    obtain ⟨available, count, matchAll⟩ := (mem_choices _ _ _ _).mp member
    refine ⟨⟨picked, count, matchAll⟩, ?_, ?_⟩
    · change picked + 0 ≤ current
      simpa using available
    · change remaining = current - picked + 0
      simpa using result
  · rintro ⟨firing, enabled, result⟩
    refine ⟨firing.val, (mem_choices _ _ _ _).mpr ?_, by simpa using result⟩
    exact ⟨by simpa using enabled, firing.property.1, firing.property.2⟩

theorem commit_iff_enabled_firing {site : Binding × ℕ}
    (firing : (selectionSystem accepts).Instance site) (current remaining : Multiset R) :
    commit firing.val current = some remaining ↔
      (selectionSystem accepts).Enables current firing ∧
        remaining = (selectionSystem accepts).fire current firing := by
  simp only [commit_eq_some_iff, selectionSystem_enables, selectionSystem_fire]

omit [DecidableEq R] in
/-- The resource criterion for two independent takes is that both selected
bags fit simultaneously. Merely enabling them separately is insufficient. -/
theorem selectionSystem_concurrent {site₁ site₂ : Binding × ℕ}
    (left : (selectionSystem accepts).Instance site₁)
    (right : (selectionSystem accepts).Instance site₂) (current : Multiset R) :
    (selectionSystem accepts).Concurrent current left right ↔
      left.val + right.val ≤ current := by
  simp [System.Concurrent, selectionSystem]

/-- Independent atomic takes retain availability and commute. -/
theorem independent_takes {site₁ site₂ : Binding × ℕ}
    (left : (selectionSystem accepts).Instance site₁)
    (right : (selectionSystem accepts).Instance site₂) (current : Multiset R)
    (fit : left.val + right.val ≤ current) :
    (selectionSystem accepts).Enables ((selectionSystem accepts).fire current left) right ∧
      (selectionSystem accepts).fire ((selectionSystem accepts).fire current left) right =
      (selectionSystem accepts).fire ((selectionSystem accepts).fire current right) left := by
  have concurrent := (selectionSystem_concurrent accepts left right current).mpr fit
  exact ⟨(selectionSystem accepts).enables_fire concurrent,
    (selectionSystem accepts).fire_comm concurrent⟩

end Mettapedia.GSLT.Causality.ResourceSelection

namespace Mettapedia.GSLT.Causality.ResourceSelection.SnapshotControls

def isSeven (resource : ℕ) : Bool := resource == 7

/-- Inserting an unrelated atom does not invalidate the complete observation. -/
theorem irrelevant_insertion_survives :
    commitAll isSeven {7} ({7, 9} : Multiset ℕ) = some {9} := by
  decide +kernel

/-- An ordinary atomic take still succeeds after a new match appears. It
does not certify that the captured take contains all current matches. -/
theorem availability_does_not_certify_completeness :
    commit {7} ({7, 7} : Multiset ℕ) = some {7} ∧
      commitAll isSeven {7} ({7, 7} : Multiset ℕ) = none := by
  decide +kernel

/-- A captured absence is invalidated by an inserted matching atom. There
are no selected atoms whose disappearance could detect this race. -/
theorem empty_capture_detects_inserted_match :
    commitAll isSeven 0 (0 : Multiset ℕ) = some 0 ∧
      commitAll isSeven 0 ({7} : Multiset ℕ) = none ∧
      commit 0 ({7} : Multiset ℕ) = some {7} := by
  decide +kernel

end Mettapedia.GSLT.Causality.ResourceSelection.SnapshotControls
