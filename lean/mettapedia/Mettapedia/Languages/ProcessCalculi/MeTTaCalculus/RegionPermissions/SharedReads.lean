import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.DelegatedReads
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication.RevisionValidation

/-!
# The shared case of read polarity, on the runtime's revision protocol

`DelegatedReads` splits a universal read of the names `A` (absence, "every row here is like this")
into three cases by what the genesis lets the others reach: **owned** (no other subject can ever
hold `send` at `A`: the read needs no validation, `absence_preserved_iff`), **sealed** (every such
`send` was revoked), and **shared** (otherwise: the read must be validated when its commit fires).
The runtime publishes proposals validated by one revision per space (`SerializedPublication`): a
proposal matched at a snapshot is published as the commit widened by a predicate query of the whole
space (`widen`), over the commit protocol of `CommitProtocol`, whose epoch for the region
`everywhere` is the revision. This module states the shared case on that protocol.

## Shared: validation at commit is the revision, and it is needed

When another subject can reach `send` at a name of `A`, the delegation core can authorize it to
make an occurrence there, and as a transaction of the revision protocol that make commits; the
absence then fails, and the owner's revision-validated transaction that read it commits in no
continuation (`shared_absence_stale_under_revision`). The stale read is never published. Without
the validation it would be: the absence query of the base commit fails at the new store.

## Owned: the revision still aborts

The revision is the epoch of the whole space, so a write outside `A`, which leaves the read true,
still makes the owner's transaction stale (`write_outside_stales_revision`): an abort the owned
case does not need. The read's own region is not spoiled by that write, while its widening is
(`outside_spoils_only_the_widening`); an epoch of the read's region, or a per-space revision as the
interaction kernel keeps, aborts only for writes into what it validates.

## The kernel's per-space revision is this protocol, space by space

The interaction kernel validates by one revision per scanned space
(`KernelCommit.revisionQuery`); in a store with one space it is the runtime's one-revision query
(`kernel_revisionQuery_one_space`).

## Controls

`Controls.shared_instance`: the genesis of `DelegatedReads.Controls` in which the owner may grant
`send` to the other subject, an owner's transaction that read the absence at name `0` validated by
the revision, and the other's make at name `0`: all the hypotheses hold, and the theorem applies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.SharedReads

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication
open Mettapedia.Machines.Kernel

section Protocol

variable {O : Type} [LinearOrder O] {R : Type} {N : Type} [DecidableEq N] {Sub : Type}
  [DecidableEq Sub] {T : Type} [DecidableEq T]
variable {label : O → R} {loc : R → N}

/-- A make of a fresh occurrence begins and commits as a transaction of the protocol. -/
theorem make_commits {txn : T → Commit O R} {σ : ProtocolState O R T}
    (wf : WellFormed label txn σ) {w : T} (idle : σ.phase w = .idle) {o : O}
    (writer : txn w = Commit.makeOne o) (unborn : o ∉ σ.born) :
    ∃ σ₁, Step label txn σ none σ₁ ∧ WellFormed label txn σ₁ ∧
      σ₁.phase = Function.update σ.phase w (.active σ.epoch) ∧
      Step label txn σ₁ (some (w, txn w)) (commitState label txn w σ₁) ∧
      σ₁.store = σ.store := by
  have notStored : o ∉ σ.store := fun stored => unborn (wf.store_born stored)
  have enabled : Enabled label σ.store (txn w) := by
    rw [writer]
    exact ⟨by simp [Commit.makeOne], by simp [Commit.makeOne], by simp [Commit.makeOne],
      by simpa [Commit.makeOne] using notStored, by simp [Commit.makeOne]⟩
  let σ₁ : ProtocolState O R T := { σ with phase := Function.update σ.phase w (.active σ.epoch) }
  have begin : Step label txn σ none σ₁ := .begin σ w idle enabled
  refine ⟨σ₁, begin, begin.wellFormed wf, rfl, ?_, rfl⟩
  refine .commit σ₁ w σ.epoch (by simp [σ₁]) (fun o' taken => ?_) (by simp [writer]) ?_ ?_
  · simp [writer, Commit.makeOne] at taken
  · intro read member
    simp [writer, Commit.makeOne] at member
  · simpa [writer, Commit.makeOne, σ₁] using unborn

/-- **The shared case, on the revision protocol.** If another subject can reach `send` at a name
of `A`, the delegation core can authorize it to make a fresh occurrence there; as a transaction of
the revision protocol the make commits, the absence at `A` fails, and the owner's transaction
validated by the revision commits in no continuation. -/
theorem shared_absence_stale_under_revision {st₀ : Delegation.State Sub (Facet × N)}
    {b : Sub} {A : N → Bool} {n : N} (atA : A n = true)
    (reach : Delegation.CanHold st₀ b (facetAt .send n) false)
    {txn : T → Commit O R} {σ : ProtocolState O R T} (wf : WellFormed label txn σ)
    {t w : T} (different : t ≠ w) {seen : (R → Bool) → ℕ} (active : σ.phase t = .active seen)
    {snapshot : Finset O} (validated : revisionQuery snapshot ∈ (txn t).queries)
    (idle : σ.phase w = .idle) {o : O} (writer : txn w = Commit.makeOne o)
    (unborn : o ∉ σ.born) (atN : loc (label o) = n) :
    (∃ ops, CapFormed label loc (Delegation.run st₀ ops) b (Commit.makeOne o)) ∧
      ∃ σ', Run label txn σ [(w, txn w)] σ' ∧ o ∈ restrict label loc A σ'.store ∧
        ∀ σ'' trace, Run label txn σ' trace σ'' → ∀ entry ∈ trace, entry.1 ≠ t := by
  obtain ⟨ops, -, held⟩ := Delegation.canHold_realized reach
  refine ⟨⟨ops, by simp [Commit.makeOne], by simp [Commit.makeOne], fun p made => ?_,
    by simp [Commit.makeOne]⟩, ?_⟩
  · simp only [Commit.makeOne, Finset.mem_singleton] at made
    subst made
    rw [atN]
    exact held
  obtain ⟨σ₁, begin, wf₁, phase₁, commit, store₁⟩ := make_commits wf idle writer unborn
  have active₁ : σ₁.phase t = .active seen := by
    rw [phase₁, Function.update_of_ne different]
    exact active
  refine ⟨commitState label txn w σ₁, .step begin (.step commit (.refl _)), ?_,
    stale_after_any_write wf₁ different active₁ validated ⟨o, by simp [writer, Commit.makeOne]⟩⟩
  refine mem_restrict.mpr ⟨?_, by rw [atN]; exact atA⟩
  simp [commitState, writer, Commit.makeOne, fire, store₁]

omit [DecidableEq N] in
/-- **A write outside the read's names leaves the read true, and still makes the revision stale.** -/
theorem write_outside_stales_revision {A : N → Bool} {txn : T → Commit O R}
    {σ : ProtocolState O R T} (wf : WellFormed label txn σ) {t w : T} (different : t ≠ w)
    {seen : (R → Bool) → ℕ} (active : σ.phase t = .active seen) {snapshot : Finset O}
    (validated : revisionQuery snapshot ∈ (txn t).queries) (idle : σ.phase w = .idle) {o : O}
    (writer : txn w = Commit.makeOne o) (unborn : o ∉ σ.born) (outside : A (loc (label o)) = false) :
    ∃ σ', Run label txn σ [(w, txn w)] σ' ∧
      restrict label loc A σ'.store = restrict label loc A σ.store ∧
        ∀ σ'' trace, Run label txn σ' trace σ'' → ∀ entry ∈ trace, entry.1 ≠ t := by
  obtain ⟨σ₁, begin, wf₁, phase₁, commit, store₁⟩ := make_commits wf idle writer unborn
  have active₁ : σ₁.phase t = .active seen := by
    rw [phase₁, Function.update_of_ne different]
    exact active
  refine ⟨commitState label txn w σ₁, .step begin (.step commit (.refl _)), ?_,
    stale_after_any_write wf₁ different active₁ validated ⟨o, by simp [writer, Commit.makeOne]⟩⟩
  ext p
  simp only [mem_restrict, commitState, writer, fire, Commit.makeOne, store₁, Finset.sdiff_empty,
    Finset.mem_union, Finset.mem_singleton]
  constructor
  · rintro ⟨inStore | rfl, atA⟩
    · exact ⟨inStore, atA⟩
    · rw [outside] at atA; cases atA
  · rintro ⟨inStore, atA⟩
    exact ⟨Or.inl inStore, atA⟩

omit [LinearOrder O] in
/-- **The read's own region is not spoiled by a write outside it; its widening is.** -/
theorem outside_spoils_only_the_widening [DecidableEq O] {c : Commit O R} {o : O}
    (outside : ∀ read ∈ c.queries, read.region (label o) = false) (snapshot : Finset O) :
    ¬ Spoils label (Commit.makeOne o) c ∧ Spoils label (Commit.makeOne o) (widen snapshot c) := by
  refine ⟨?_, spoils_widen_of_writes ⟨o, by simp [Commit.makeOne]⟩⟩
  rintro (takes | ⟨read, member, p, written, inRegion⟩)
  · exact takes (by simp [Commit.makeOne])
  · simp only [Commit.makeOne, Finset.empty_union, Finset.mem_singleton] at written
    subst written
    rw [outside read member] at inRegion
    cases inRegion

end Protocol

/-! ## The kernel's per-space revision -/

/-- **In a store with one space, the kernel's revision query is the runtime's.** -/
theorem kernel_revisionQuery_one_space {Sp O R : Type} [DecidableEq Sp] [DecidableEq O]
    (spaceOf : R → Sp) (v : KernelCommit.View Sp O) (s : Sp) (only : ∀ r, spaceOf r = s) :
    KernelCommit.revisionQuery spaceOf v s = revisionQuery (v.rows s).toFinset := by
  unfold KernelCommit.revisionQuery revisionQuery everywhere
  congr 1
  funext r
  simp [only r]

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.Controls

/-- Occurrence `5` lives at name `0`; every other at name `1`. -/
def nameOf : ℕ → ℕ := fun o => if o = 5 then 0 else 1

/-- The read's names: name `0`. -/
def atZero : ℕ → Bool := fun n => decide (n = 0)

/-- The owner's commit: the absence at name `0`, validated by the revision at the empty snapshot. -/
def absenceReader : Commit ℕ ℕ := widen ∅ ⟨∅, ∅, ∅, [⟨fun r => atZero r, ∅⟩]⟩

/-- Transaction `true` is the owner's reader, `false` the other's make of `5`. -/
def txn : Bool → Commit ℕ ℕ
  | true => absenceReader
  | false => Commit.makeOne 5

/-- The empty start: nothing stored or born, every transaction idle. -/
def start : ProtocolState ℕ ℕ Bool := ⟨∅, ∅, fun _ => none, fun _ => 0, fun _ => .idle⟩

/-- The owner's reader has begun. -/
def begun : ProtocolState ℕ ℕ Bool :=
  { start with phase := Function.update start.phase true (.active start.epoch) }

theorem begun_wellFormed : WellFormed nameOf txn begun := by
  have initial : Initial start := ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
  have enabled : Enabled nameOf start.store (txn true) := by
    refine ⟨by simp [txn, absenceReader, widen], by simp [txn, absenceReader, widen],
      by simp [txn, absenceReader, widen], by simp [txn, absenceReader, widen], ?_⟩
    intro read member
    simp only [txn, absenceReader, widen_reads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact revisionQuery_holds_iff.mpr rfl
    · decide
  exact (Step.begin start true rfl enabled).wellFormed (wellFormed_of_initial initial)

/-- **The shared case applies**: the other subject can reach `send` at name `0`, so it can be
authorized to make `5` there; the make commits, the absence fails, and the owner's reader commits
in no continuation. -/
theorem shared_instance :
    (∃ ops, CapFormed nameOf id (Delegation.run grantingGenesis ops) false (Commit.makeOne 5)) ∧
      ∃ σ', Run nameOf txn begun [(false, txn false)] σ' ∧ 5 ∈ restrict nameOf id atZero σ'.store ∧
        ∀ σ'' trace, Run nameOf txn σ' trace σ'' → ∀ entry ∈ trace, entry.1 ≠ true :=
  shared_absence_stale_under_revision (loc := id) (A := atZero) (n := 0) (t := true) (w := false)
    (o := 5) (seen := start.epoch) (by decide) other_reaches_send begun_wellFormed (by decide)
    (by simp [begun]) (snapshot := ∅)
    (by simp [txn, absenceReader, widen]) (by simp [begun, start]) rfl (by simp [begun, start])
    (by simp [nameOf])

/-- **A write at name `1` leaves the absence at name `0` true and still makes the reader stale.** -/
theorem outside_instance :
    ∃ σ', Run nameOf (fun t => if t then absenceReader else Commit.makeOne 6) begun
        [(false, Commit.makeOne 6)] σ' ∧
      restrict nameOf id atZero σ'.store = restrict nameOf id atZero begun.store := by
  have wf : WellFormed nameOf (fun t => if t then absenceReader else Commit.makeOne 6) begun := by
    have initial : Initial start := ⟨le_rfl, fun _ => rfl, fun _ => rfl⟩
    have enabled : Enabled nameOf start.store absenceReader := by
      refine ⟨by simp [absenceReader, widen], by simp [absenceReader, widen],
        by simp [absenceReader, widen], by simp [absenceReader, widen], ?_⟩
      intro read member
      simp only [absenceReader, widen_reads, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact revisionQuery_holds_iff.mpr rfl
      · decide
    exact (Step.begin (txn := fun t => if t then absenceReader else Commit.makeOne 6) start true rfl
      enabled).wellFormed (wellFormed_of_initial initial)
  obtain ⟨σ', run, same, -⟩ := write_outside_stales_revision (loc := id) (A := atZero) wf
    (t := true) (w := false) (seen := start.epoch) (by decide) (by simp [begun]) (snapshot := ∅)
    (by simp [absenceReader, widen]) (by simp [begun, start]) (o := 6) rfl (by simp [begun, start])
    (by simp [nameOf, atZero])
  exact ⟨σ', run, same⟩

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.SharedReads
