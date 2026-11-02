import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication.RevisionValidation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.OptimisticRetries
import Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQueryExecution
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceQueryControls
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.ParkedWakeups
import Mathlib.Data.Finset.Sort

/-!
# What a fine-grained publication runtime must refine, and where revision validation stops

`RevisionValidation` models publication validated by one revision per space as the commit
protocol over widened proposals. This module states the obligation a fine-grained runtime must
meet instead, and checks the revision protocol and the per-occurrence protocol against it.

## Invalidation rules

A runtime's validation is summarized by an **invalidation rule** `inv d c`: publishing `d` makes an
open attempt of `c` invalid. Two properties matter.

* **Sound** (`SoundFor`): the rule invalidates whatever serializable validation must invalidate
  (`OptimisticRetries.Invalidates` at `Mode.serializable`). Every runtime must be sound; with
  atomic commit steps this is what `CommitProtocol.Run.refines` turns into serializability.
* **Local** (`LocalTo key`): the rule invalidates only for a reason in the attempt's footprint:
  a common take, a take of a kept occurrence, a common fresh identity, or a write inside the
  epoch key of a region the attempt queries. `key` may be coarser than the regions it
  validates (`Covers`, `localTo_mono`), which adds aborts only among commits that touch one key.

## Results

* Serializable validation is sound and local with the finest keys
  (`serializable_soundFor`, `serializable_localTo`). The per-occurrence protocol keeps a ready
  transaction ready across every commit that neither clashes with it nor spoils it
  (`CommitProtocol.ready_commitState`), and that rule is local (`clashOrSpoils_localTo`). Run over
  widened transactions, the same rule becomes "any write" (`widened_clashOrSpoils_iff`).
* **Revision validation invalidates exactly on any write**: an attempt widened by a revision
  check is invalidated by a commit exactly when that commit takes or makes something
  (`widened_invalidates_iff`). The rule is sound (`revision_soundFor`) and local for no choice of
  keys at all (`revision_not_localTo`).
* Locality is what makes writers on distinct channels never abort each other: a local rule never
  invalidates an attempt whose footprint is apart from the committed one (`localTo_apart`).
* **Progress.** A reader of a token beside a writer of unrelated facts is never invalidated
  under serializable validation (`Controls.base_neverInvalidated`), so by
  `OptimisticRetries.never_aborts` it never aborts in any execution. Widened by revision checks,
  every write of the writer invalidates every open attempt of the reader
  (`Controls.widened_reader_invalidated`), which is the schedule of
  `OptimisticRetries.Controls.optimistic_starvation`.
* **Preparation waves are not commit waves.** On the native preparation footprint the resource
  selector admits exactly the first `workers` tasks of the agenda and defers the rest
  (`preparation_selectWave`, from `CeTTaResourceWave.Preparation.enabled_iff`): the maximal
  admitted wave is a prefix cut by the worker credits, and no read, take or write of the tasks
  enters the decision. Carrying the two rival takers of one token, an admitted wave has no
  executable order (`preparation_wave_not_commit_wave`). Serialized revision-validated
  publication then commits at most one writer per snapshot
  (`RevisionValidation.writers_only_last`).
* **Atomic publication does not supply compound observation.** The existing retained
  query can straddle one atomic descriptor decision and return no snapshot's answer.
  An unchanged decision preserves fixed-view execution; authentic saved cuts additionally
  yield complete read agreement. Rebased stamps and decision-wide false invalidation have
  explicit counterexamples (`DescriptorObservation`).
* **Finite interference witnesses.** `FiniteInterference.reasons` enumerates actual conflicting
  occurrences and matching writes. Its executable check agrees with `Clash ∨ Spoils`, is local
  to the exact semantic regions, and preserves readiness when clear. The supplied footprints
  still need source-level justification and an atomic validation/publication boundary.
* **Executed read dependencies.** `SourceReads` supplies that justification for the existing
  pure adaptive query compiler with a concrete ordered scanner. A clear local check preserves
  its entire observation and source rows; under the matcher laws it also preserves declarative
  absence. Effectful sources and the concrete concurrency boundary remain separate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

/-! ## Invalidation rules -/

section Rules

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- The rule invalidates at least what serializable validation must invalidate. -/
def SoundFor (label : O → R) (inv : Commit O R → Commit O R → Prop) : Prop :=
  ∀ d c, Liveness.Invalidates label Mode.serializable d c → inv d c

/-- The rule invalidates only for a reason inside the attempt's footprint, reading each queried
region through its epoch key. -/
def LocalTo (label : O → R) (key : (R → Bool) → R → Bool)
    (inv : Commit O R → Commit O R → Prop) : Prop :=
  ∀ d c, inv d c → ¬ Disjoint d.taken c.taken ∨ ¬ Disjoint d.taken c.kept ∨
    ¬ Disjoint d.made c.made ∨ ∃ read ∈ c.queries, ∃ o ∈ d.taken ∪ d.made, key read.region (label o) = true

/-- An epoch key contains each region it validates. -/
def Covers (key : (R → Bool) → R → Bool) : Prop :=
  ∀ region x, region x = true → key region x = true

/-- **Serializable validation is sound**, trivially. -/
theorem serializable_soundFor (label : O → R) :
    SoundFor label (Liveness.Invalidates label Mode.serializable) := fun _ _ invalid => invalid

/-- **Serializable validation is local with the finest keys.** -/
theorem serializable_localTo (label : O → R) :
    LocalTo label id (Liveness.Invalidates label Mode.serializable) := by
  intro d c invalid
  rcases invalid with ⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, o, written, inRegion⟩
  · exact Or.inl takes
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, inRegion⟩))

/-- A coarser key keeps a local rule local. -/
theorem localTo_mono {label : O → R} {key key' : (R → Bool) → R → Bool}
    (coarser : ∀ region x, key region x = true → key' region x = true)
    {inv : Commit O R → Commit O R → Prop} (local_ : LocalTo label key inv) :
    LocalTo label key' inv := by
  intro d c invalid
  rcases local_ d c invalid with takes | keeps | made | ⟨read, member, o, written, inKey⟩
  · exact Or.inl takes
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inl made))
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, coarser _ _ inKey⟩))

/-- Every key that covers its regions keeps serializable validation local. -/
theorem serializable_localTo_of_covers (label : O → R) {key : (R → Bool) → R → Bool}
    (covers : Covers key) : LocalTo label key (Liveness.Invalidates label Mode.serializable) :=
  localTo_mono (fun region x inRegion => covers region x inRegion) (serializable_localTo label)

/-- **A local rule never invalidates an attempt apart from the committed footprint**: one that
shares no take, keeps nothing taken, shares no fresh identity and queries no key the
commit writes into. Writers on distinct channels, with channels as keys, never abort each
other. -/
theorem localTo_apart {label : O → R} {key : (R → Bool) → R → Bool}
    {inv : Commit O R → Commit O R → Prop} (local_ : LocalTo label key inv) {d c : Commit O R}
    (takes : Disjoint d.taken c.taken) (keeps : Disjoint d.taken c.kept)
    (made : Disjoint d.made c.made)
    (keysApart : ∀ read ∈ c.queries, ∀ o ∈ d.taken ∪ d.made, key read.region (label o) = false) :
    ¬ inv d c := by
  intro invalid
  rcases local_ d c invalid with clash | spoiled | fresh | ⟨read, member, o, written, inKey⟩
  · exact clash takes
  · exact spoiled keeps
  · exact fresh made
  · rw [keysApart read member o written] at inKey
    exact absurd inKey (by decide)

/-- **An attempt widened by a revision check is invalidated by a commit exactly when that commit
takes or makes something.** -/
theorem widened_invalidates_iff {label : O → R} {snapshot : Finset O} {d c : Commit O R} :
    Liveness.Invalidates label Mode.serializable d (widen snapshot c) ↔ WritesSomething d := by
  constructor
  · rintro (⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, o, written, _⟩)
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp takes
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp keeps
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · exact ⟨o, written⟩
  · rintro ⟨o, written⟩
    exact Or.inr (Or.inr ⟨by simp [Mode.serializable], revisionQuery snapshot, List.mem_cons_self,
      o, written, rfl⟩)

/-- **The per-occurrence protocol's rule is local with the finest keys.** A ready transaction of
`CommitProtocol` stays ready across every commit that neither clashes with it nor spoils it
(`CommitProtocol.ready_commitState`); that rule is local. -/
theorem clashOrSpoils_localTo (label : O → R) :
    LocalTo label id (fun d c => Clash d c ∨ Spoils label d c) := by
  intro d c invalid
  rcases invalid with (takes | made) | (keeps | ⟨read, member, o, written, inRegion⟩)
  · exact Or.inl takes
  · exact Or.inr (Or.inr (Or.inl made))
  · exact Or.inr (Or.inl keeps)
  · exact Or.inr (Or.inr (Or.inr ⟨read, member, o, written, inRegion⟩))

/-- **The same rule on widened transactions is any write.** Run over proposals widened by a
revision check, the per-occurrence protocol keeps a ready transaction ready across a commit
exactly when that commit writes nothing. -/
theorem widened_clashOrSpoils_iff {label : O → R} {snapshot : Finset O} {d c : Commit O R} :
    Clash d (widen snapshot c) ∨ Spoils label d (widen snapshot c) ↔ WritesSomething d := by
  constructor
  · rintro ((takes | made) | (keeps | ⟨_, _, o, written, _⟩))
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp takes
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp made
      exact ⟨o, Finset.mem_union_right _ inD⟩
    · obtain ⟨o, inD, _⟩ := Finset.not_disjoint_iff.mp keeps
      exact ⟨o, Finset.mem_union_left _ inD⟩
    · exact ⟨o, written⟩
  · intro writes
    exact Or.inr (spoils_widen_of_writes writes)

/-- The invalidation rule of revision validation, on the base commits: any write. -/
def revisionRule (d _c : Commit O R) : Prop := WritesSomething d

/-- **Revision validation is sound.** -/
theorem revision_soundFor (label : O → R) : SoundFor label (revisionRule (O := O) (R := R)) := by
  intro d c invalid
  have widened : Liveness.Invalidates label Mode.serializable d (widen ∅ c) := by
    rcases invalid with ⟨member, takes⟩ | ⟨member, keeps⟩ | ⟨member, read, inQueries, o, written, inRegion⟩
    · exact Or.inl ⟨member, takes⟩
    · exact Or.inr (Or.inl ⟨member, keeps⟩)
    · exact Or.inr (Or.inr ⟨member, read, List.mem_cons_of_mem _ inQueries, o, written, inRegion⟩)
  exact widened_invalidates_iff.mp widened

end Rules

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls (Atom)

/-- A reader of the token, emitting a fresh output. -/
def readToken : Commit ℕ Atom := OccurrenceCommits.Controls.reader

/-- A writer of one unrelated fresh fact. -/
def writeFact (n : ℕ) : Commit ℕ Atom := ⟨∅, ∅, {n}, []⟩

/-- **Revision validation is local for no choice of epoch keys**: a write of an unrelated fact
invalidates a reader with which it shares nothing. -/
theorem revision_not_localTo (key : (Atom → Bool) → Atom → Bool) :
    ¬ LocalTo lab key (revisionRule (O := ℕ) (R := Atom)) := by
  intro local_
  rcases local_ (writeFact 10) readToken ⟨10, by simp [writeFact]⟩ with
    takes | keeps | made | ⟨read, member, _⟩
  · exact takes (by simp [writeFact])
  · exact keeps (by simp [writeFact])
  · exact made (by simp [writeFact, readToken, OccurrenceCommits.Controls.reader])
  · simp [readToken, OccurrenceCommits.Controls.reader] at member

/-- The reader is a one-shot transaction; the writer is persistent and may write any fact at an
identity from `10` on. -/
def baseProgram : Liveness.Program Bool ℕ Atom where
  rows := fun t => match t with
    | true => {readToken}
    | false => {c | ∃ n, 10 ≤ n ∧ c = writeFact n}
  persistent := fun t => match t with
    | true => false
    | false => true

/-- The same program with every row widened by a revision check at any snapshot. -/
def widenedProgram : Liveness.Program Bool ℕ Atom where
  rows := fun t => {c | ∃ snapshot base, base ∈ baseProgram.rows t ∧ c = widen snapshot base}
  persistent := baseProgram.persistent

/-- **Positive control.** Under serializable validation no row of the reader-writer program
invalidates another, so by `OptimisticRetries.never_aborts` no execution ever aborts. -/
theorem base_neverInvalidated : Liveness.NeverInvalidated lab Mode.serializable baseProgram := by
  intro t t' d c rowD rowC invalid
  have dWrites : d.taken = ∅ ∧ d.made.Nonempty ∨ d = readToken := by
    cases t with
    | true =>
        right
        simpa [baseProgram] using rowD
    | false =>
        left
        obtain ⟨n, _, rfl⟩ := rowD
        exact ⟨rfl, ⟨n, by simp [writeFact]⟩⟩
  have cQueries : c.queries = [] ∧ c.taken = ∅ := by
    cases t' with
    | true =>
        have : c = readToken := by simpa [baseProgram] using rowC
        subst this
        simp [readToken, OccurrenceCommits.Controls.reader]
    | false =>
        obtain ⟨n, _, rfl⟩ := rowC
        simp [writeFact]
  rcases invalid with ⟨_, takes⟩ | ⟨_, keeps⟩ | ⟨_, read, member, _⟩
  · exact takes (by rw [cQueries.2]; simp)
  · rcases dWrites with ⟨noTake, _⟩ | same
    · exact keeps (by rw [noTake]; simp)
    · subst same
      exact keeps (by simp [readToken, OccurrenceCommits.Controls.reader])
  · rw [cQueries.1] at member
    simp at member

/-- **Negative control.** Widened by revision checks, a write of the writer invalidates an open
attempt of the reader, at every snapshot: under the optimistic semantics the reader's attempt
turns invalid at each of the writer's commits. -/
theorem widened_reader_invalidated (snapshot snapshot' : Finset ℕ) (n : ℕ) (_ : 10 ≤ n) :
    Liveness.Invalidates lab Mode.serializable (widen snapshot' (writeFact n))
        (widen snapshot readToken) ∧
      Liveness.invalidate lab Mode.serializable (widen snapshot' (writeFact n))
        (Liveness.Phase.active (widen snapshot readToken) true) =
        Liveness.Phase.active (widen snapshot readToken) false ∧
      ¬ Liveness.NeverInvalidated lab Mode.serializable widenedProgram := by
  have invalid : Liveness.Invalidates lab Mode.serializable (widen snapshot' (writeFact n))
      (widen snapshot readToken) :=
    widened_invalidates_iff.mpr ⟨n, by simp [writeFact]⟩
  refine ⟨invalid, ?_, ?_⟩
  · simp [Liveness.invalidate, invalid]
  · intro never
    exact never false true (widen snapshot' (writeFact n)) (widen snapshot readToken)
      ⟨snapshot', writeFact n, ⟨n, by assumption, rfl⟩, rfl⟩
      ⟨snapshot, readToken, by simp [baseProgram], rfl⟩ invalid

/-- A taker writes; a reader that makes nothing writes nothing. -/
theorem writesSomething_controls :
    WritesSomething takeFirst ∧ ¬ WritesSomething (Commit.keepOne 0 : Commit ℕ Atom) := by
  refine ⟨⟨0, by simp [takeFirst]⟩, ?_⟩
  rintro ⟨o, written⟩
  simp at written

/-- **A rule that never invalidates is not sound**: serializable validation invalidates the second
of two takers of one token. -/
theorem never_not_soundFor : ¬ SoundFor lab (fun _ _ : Commit ℕ Atom => False) := fun sound =>
  sound takeFirst takeFirst (Or.inl ⟨by simp [Mode.serializable], by simp [takeFirst]⟩)

/-- Revision validation is sound at the controls' labels, as serializable validation is. -/
theorem soundFor_instances :
    SoundFor lab (Liveness.Invalidates lab Mode.serializable) ∧
      SoundFor lab (revisionRule (O := ℕ) (R := Atom)) :=
  ⟨serializable_soundFor lab, revision_soundFor lab⟩

/-- Serializable validation is local with the finest keys, at the controls' labels. -/
theorem serializable_local_instance : LocalTo lab id (Liveness.Invalidates lab Mode.serializable) :=
  serializable_localTo lab

/-- The identity key covers every region; the empty key covers none that holds anything. -/
theorem covers_controls :
    Covers (R := Atom) id ∧ ¬ Covers (R := Atom) (fun _ _ => false) := by
  refine ⟨fun _ _ inRegion => inRegion, fun covers => ?_⟩
  have := covers (fun _ => true) Atom.tok rfl
  simp at this

end Controls

/-! ## Preparation waves are not commit waves -/

section Preparation

open Mettapedia.Languages.MeTTa.Bridges.GSLT.CeTTaResourceWave
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls (Atom)

/-- The commits the two prepared tasks of the control carry: the two rival takers of one
token. -/
def taskCommit : BitVec 64 → Commit ℕ Atom
  | 1 => OccurrenceCommits.Controls.taker
  | _ => OccurrenceCommits.Controls.taker₂

/-- Once the worker credits are used up, the selector defers every further task. -/
theorem preparation_full_defers (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) (done : List (BitVec 64))
    (full : workers ≤ done.length) :
    ∀ rest : List (BitVec 64),
      (Preparation.system owner instanceId revision).selectWaveAux
          (Preparation.supply owner instanceId revision catalogue workers)
          (Preparation.entries owner instanceId revision done)
          (Preparation.entries owner instanceId revision rest) =
        ([], Preparation.entries owner instanceId revision rest)
  | [] => by
      simp [Preparation.entries, Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux]
  | x :: rest => by
      have refused : ¬ (Preparation.system owner instanceId revision).StepEnables
          (Preparation.supply owner instanceId revision catalogue workers)
          ((Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] : List _) : Multiset _) := by
        have appended : Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] =
            Preparation.entries owner instanceId revision (done ++ [x]) := by
          simp [Preparation.entries]
        rw [appended, Preparation.enabled_iff]
        rintro ⟨_, tooMany⟩
        simp at tooMany
        omega
      change (Preparation.system owner instanceId revision).selectWaveAux _ _
          (Preparation.entry owner instanceId revision x ::
            Preparation.entries owner instanceId revision rest) = _
      rw [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux, if_neg refused,
        preparation_full_defers owner instanceId revision catalogue workers done full rest]
      rfl

/-- The scan of the selector over a preparation catalogue, from any prefix already selected. -/
theorem preparation_selectWaveAux (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) :
    ∀ (rest done : List (BitVec 64)), done ++ rest = catalogue → done.length ≤ workers →
      (Preparation.system owner instanceId revision).selectWaveAux
          (Preparation.supply owner instanceId revision catalogue workers)
          (Preparation.entries owner instanceId revision done)
          (Preparation.entries owner instanceId revision rest) =
        (Preparation.entries owner instanceId revision (rest.take (workers - done.length)),
          Preparation.entries owner instanceId revision (rest.drop (workers - done.length)))
  | [], _, _, _ => by
      simp [Preparation.entries, Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux]
  | x :: rest, done, whole, bound => by
      by_cases room : done.length < workers
      · have prefixLe : ((done ++ [x] : List (BitVec 64)) : Multiset (BitVec 64)) ≤ catalogue := by
          rw [← whole]
          exact Multiset.coe_le.mpr
            ((List.Sublist.append_left (List.singleton_sublist.mpr List.mem_cons_self) done).subperm)
        have appended : Preparation.entries owner instanceId revision done ++
            [Preparation.entry owner instanceId revision x] =
            Preparation.entries owner instanceId revision (done ++ [x]) := by
          simp [Preparation.entries]
        have admitted : (Preparation.system owner instanceId revision).StepEnables
            (Preparation.supply owner instanceId revision catalogue workers)
            ((Preparation.entries owner instanceId revision done ++
              [Preparation.entry owner instanceId revision x] : List _) : Multiset _) := by
          rw [appended, Preparation.enabled_iff]
          exact ⟨prefixLe, by simp; omega⟩
        have later := preparation_selectWaveAux owner instanceId revision catalogue workers rest
          (done ++ [x]) (by simpa using whole) (by simp; omega)
        rw [← appended] at later
        obtain ⟨k, hk⟩ : ∃ k, workers - done.length = k + 1 := ⟨workers - done.length - 1, by omega⟩
        have hk' : workers - (done ++ [x]).length = k := by simp; omega
        rw [hk'] at later
        change (Preparation.system owner instanceId revision).selectWaveAux _ _
            (Preparation.entry owner instanceId revision x ::
              Preparation.entries owner instanceId revision rest) = _
        rw [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWaveAux, if_pos admitted,
          later, hk]
        rfl
      · have full : done.length = workers := by omega
        have deferred := preparation_full_defers owner instanceId revision catalogue workers done
          (by omega) (x :: rest)
        rw [deferred, full]
        simp [Preparation.entries]

/-- **The maximal admitted preparation wave is the first `workers` tasks of the agenda.** The
selector, run on the native preparation footprint, admits exactly the prefix of the catalogue
that fits the worker credits and defers the rest; nothing about the tasks' reads, takes or
writes enters the decision. -/
theorem preparation_selectWave (owner instanceId revision : BitVec 64)
    (catalogue : List (BitVec 64)) (workers : ℕ) :
    (Preparation.system owner instanceId revision).selectWave
        (Preparation.supply owner instanceId revision catalogue workers)
        (Preparation.entries owner instanceId revision catalogue) =
      (Preparation.entries owner instanceId revision (catalogue.take workers),
        Preparation.entries owner instanceId revision (catalogue.drop workers)) := by
  have := preparation_selectWaveAux owner instanceId revision catalogue workers catalogue []
    (by simp) (by simp)
  simpa [Mettapedia.GSLT.Causality.ResourceInteraction.System.selectWave,
    Preparation.entries] using this

/-- **A preparation wave is not a commit wave.** The native preparation footprint admits tasks
`1` and `2` together on two worker credits; carrying the two rival takers of one token, their
commits have no executable order at the snapshot where both were matched. -/
theorem preparation_wave_not_commit_wave :
    (Preparation.system 7 9 11).StepEnables (Preparation.supply 7 9 11 [1, 2] 2)
        (Preparation.entries 7 9 11 [1, 2]) ∧
      (∀ c ∈ [1, 2].map taskCommit, Enabled OccurrenceCommits.Controls.label {0} c) ∧
      ¬ ∃ l, l.Perm ([1, 2].map taskCommit) ∧ Executable OccurrenceCommits.Controls.label {0} l := by
  refine ⟨Preparation.occurrence_and_shared_read_controls.1, ?_, ?_⟩
  · simpa [taskCommit] using OccurrenceCommits.Controls.takers_enabled
  · simpa [taskCommit] using OccurrenceCommits.Controls.takers_batch_no_order

end Preparation


/-! ## A publication decision and the reader's observation boundary

A single decision selects the complete before/after store. Each reader step
uses that decision correctly, yet several such steps need not observe one
store. The reader below is the existing adaptive read-only query, including
its complete earned certificate and residual. The model gives publication
one atomic decision step; it deliberately does not claim a C implementation.

An unchanged one-shot decision preserves fixed-view execution from the
supplied residual. Coherence additionally requires an authentic initial
prefix; the construction below derives it for actual captured query cuts.
The proof uses the actual interleaving, not an assumed coherent observation.
Decision validation may refuse a coherent old observation; it is sufficient,
not a necessary test for whether an answer ever held. Multiple descriptors,
publication installation, reclamation and memory ordering remain separate.
-/

namespace DescriptorObservation

open Mettapedia.Machines

abbrev ObserverState (Key : Type u) (Value : Type v) (Answer : Type w) :=
  Bool × ReadOnlyQuery.Retained.State Key Value Answer

inductive Action where
  | read
  | publish
  deriving DecidableEq, Repr

def view {Key : Type u} {Value : Type v} (before after : Key → Value) (committed : Bool) : Key → Value :=
  if committed then after else before

def step {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (action : Action) (state : ObserverState Key Value Answer) : ObserverState Key Value Answer :=
  match action with
  | .read => (state.1, ReadOnlyQuery.Retained.resume (view before after state.1) 1 state.2)
  | .publish => (true, state.2)

def execute {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value) :
    List Action → ObserverState Key Value Answer → ObserverState Key Value Answer
  | [], state => state
  | action :: rest, state => execute before after rest (step before after action state)

/-- Requested read allowance; a completed query may use less. -/
def readBudget : List Action → Nat
  | [] => 0
  | .read :: rest => 1 + readBudget rest
  | .publish :: rest => readBudget rest

/-- Publication is one-shot: administrative or read steps cannot reset it. -/
theorem published_stays_published {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (actions : List Action) (pending : ReadOnlyQuery.Retained.State Key Value Answer) :
    (execute before after actions (true, pending)).1 = true := by
  induction actions generalizing pending with
  | nil => rfl
  | cons action rest ih => cases action <;> simp only [execute, step] <;> apply ih

/-- An actual interleaved prefix whose decision did not change is exactly
one fixed-view run, including all prior reads and the remaining computation. -/
theorem unchanged_decision_preserves_prefix {Key : Type u} {Value : Type v} {Answer : Type w}
    (before after : Key → Value) (actions : List Action)
    (state : ObserverState Key Value Answer)
    (unchanged : (execute before after actions state).1 = state.1) :
    (execute before after actions state).2 =
      ReadOnlyQuery.Retained.resume (view before after state.1) (readBudget actions) state.2 := by
  induction actions generalizing state with
  | nil => simp [execute, readBudget, ReadOnlyQuery.Retained.resume_zero]
  | cons action rest ih =>
      cases action with
      | read =>
          have tail := ih (step before after .read state) unchanged
          simpa only [execute, step, readBudget, ReadOnlyQuery.Retained.resume_add] using tail
      | publish =>
          have already : state.1 = true := by
            have final := published_stays_published before after rest state.2
            change (execute before after rest (true, state.2)).1 = state.1 at unchanged
            exact unchanged.symm.trans final
          have same : step before after .publish state = state := by
            cases state with | mk decision pending => simp_all [step]
          simpa only [execute, same, readBudget] using ih state (by simpa only [execute, same] using unchanged)

def validate {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (actions : List Action) (state : ObserverState Key Value Answer) :
    Option (ReadOnlyQuery.Retained.State Key Value Answer) :=
  let result := execute before after actions state
  if result.1 = state.1 then some result.2 else none

/-- Executable decision validation licenses the entire fixed-view prefix,
not just a value projected from it. This does not replay its earned work. -/
theorem validated_prefix {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (actions : List Action) (state : ObserverState Key Value Answer)
    (result : ReadOnlyQuery.Retained.State Key Value Answer)
    (accepted : validate before after actions state = some result) :
    result = ReadOnlyQuery.Retained.resume (view before after state.1) (readBudget actions) state.2 := by
  dsimp only [validate] at accepted
  split at accepted
  next unchanged =>
    have same := Option.some.inj accepted
    exact same.symm.trans (unchanged_decision_preserves_prefix before after actions state unchanged)
  next => contradiction


/-- An authentic saved cut and its later accepted work compose to the exact
original fixed-view prefix. A copied/rebased stamp alone is not this evidence. -/
theorem validated_authentic_prefix {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (decision : Bool) (program : ReadOnlyQuery.Program Key Value Answer) (prior : Nat)
    (actions : List Action) (result : ReadOnlyQuery.Retained.State Key Value Answer)
    (accepted : validate before after actions
      (decision, ReadOnlyQuery.Retained.resume (view before after decision) prior
        (ReadOnlyQuery.Retained.begin program)) = some result) :
    result = ReadOnlyQuery.Retained.resume (view before after decision)
      (prior + readBudget actions) (ReadOnlyQuery.Retained.begin program) := by
  have exactPrefix := validated_prefix before after actions _ result accepted
  simpa only [ReadOnlyQuery.Retained.resume_add] using exactPrefix

/-- Every read in the accepted authentic prefix agrees with its captured
world, including duplicate reads. No claim about arbitrary prior states is used. -/
theorem validated_authentic_reads {Key : Type u} {Value : Type v} {Answer : Type w} (before after : Key → Value)
    (decision : Bool) (program : ReadOnlyQuery.Program Key Value Answer) (prior : Nat)
    (actions : List Action) (result : ReadOnlyQuery.Retained.State Key Value Answer)
    (accepted : validate before after actions
      (decision, ReadOnlyQuery.Retained.resume (view before after decision) prior
        (ReadOnlyQuery.Retained.begin program)) = some result) :
    ReadOnlyQuery.Agrees (view before after decision) result.1 := by
  rw [validated_authentic_prefix before after decision program prior actions result accepted]
  simpa only [ReadOnlyQuery.Retained.resume, ReadOnlyQuery.Retained.begin, List.nil_append] using
    ReadOnlyQuery.pausePrefix_agrees (view before after decision) (prior + readBudget actions) program

namespace Controls

/-- One genuine occurrence commit publishes both records together. -/
def writer : Commit Nat Unit := ⟨∅, ∅, {0, 1}, []⟩

def before : Nat → Bool := fun key => decide (key ∈ (∅ : Finset Nat))
def after : Nat → Bool := fun key => decide (key ∈ fire ∅ writer)

theorem writer_enabled : Enabled (fun _ : Nat => ()) ∅ writer := by decide

def query : ReadOnlyQuery.Program Nat Bool (Bool × Bool) :=
  .read 0 fun left => .read 1 fun right => .pure (left, right)

def initial : ObserverState Nat Bool (Bool × Bool) := (false, ReadOnlyQuery.Retained.begin query)

def answer (pending : ReadOnlyQuery.Retained.State Nat Bool (Bool × Bool)) : Option (Bool × Bool) :=
  match pending.2 with
  | .pure result => some result
  | .read _ _ => none

/-- Each read uses the actual descriptor decision, but the combined answer
is absent from both instantaneous stores. No partial writer is involved. -/
theorem mixed_read :
    answer (execute before after [.read, .publish, .read] initial).2 = some (false, true) := by
  rfl

theorem mixed_answer_never_in_snapshot :
    ∀ decision : Bool, (ReadOnlyQuery.run (view before after decision) query).answer ≠ (false, true) := by
  decide

theorem mixed_certificate_disagrees_with_every_snapshot :
    ∀ decision : Bool, ReadOnlyQuery.checkReads (view before after decision)
      (execute before after [.read, .publish, .read] initial).2.1 = false := by
  decide

theorem straddling_decision_is_refused :
    validate before after [.read, .publish, .read] initial = none := by rfl

theorem before_publication_is_accepted :
    (validate before after [.read, .read] initial).map answer = some (some (false, false)) := by rfl

theorem after_publication_is_accepted :
    (validate before after [.read, .read] (true, initial.2)).map answer = some (some (true, true)) := by rfl

/-- A late publication invalidates the decision stamp even though both reads
came from one coherent old store. Refusal does not establish incoherence. -/
theorem coherent_old_answer_can_be_refused :
    answer (execute before after [.read, .read, .publish] initial).2 = some (false, false) ∧
      validate before after [.read, .read, .publish] initial = none := by
  exact ⟨rfl, rfl⟩


/-- Checking only at the end can detect a mixed result after the reader has
already computed it. Detection alone supplies no prefix-opacity theorem. -/
theorem final_refusal_does_not_erase_mixed_observation :
    validate before after [.read, .publish, .read] initial = none ∧
      answer (execute before after [.read, .publish, .read] initial).2 = some (false, true) :=
  ⟨straddling_decision_is_refused, mixed_read⟩

/-- The existing incremental validator refuses before consuming the next
read when the earned prefix no longer agrees. The exact residual survives. -/
theorem validate_before_extension_refuses_changed_prefix :
    let pending := (execute before after [.read] initial).2
    ReadOnlyQuery.Retained.resumeValidated after 1 pending = none ∧
      pending.1 = [(0, false)] ∧ answer pending = none := by
  decide


/-- Refreshing the decision while keeping an old read prefix manufactures an
accepted mixed answer. Stamp equality does not authenticate a saved world. -/
theorem rebased_stamp_accepts_mixed_prefix :
    let earned := (execute before after [.read] initial).2
    (validate before after [.read] (true, earned)).map answer = some (some (false, true)) := by
  rfl

def unrelatedQuery : ReadOnlyQuery.Program Nat Bool (Bool × Bool) :=
  .read 2 fun left => .read 2 fun right => .pure (left, right)

/-- A publication outside the actual read coordinates preserves the full
manifest, but a decision-wide check still refuses. Coarse stamps alone do
not implement the locality obligation. -/
theorem unrelated_reads_need_no_global_decision_invalidation :
    let start : ObserverState Nat Bool (Bool × Bool) :=
      (false, ReadOnlyQuery.Retained.begin unrelatedQuery)
    let reached := execute before after [.read, .publish, .read] start
    ReadOnlyQuery.checkReads after reached.2.1 = true ∧
      answer reached.2 = some (ReadOnlyQuery.run after unrelatedQuery).answer ∧
      validate before after [.read, .publish, .read] start = none := by
  decide

/-- The established prefix validator also accepts an unrelated publication;
its policy is determined by the actual observations, not only a stamp. -/
theorem unrelated_prefix_can_resume :
    let pending := ReadOnlyQuery.Retained.resume before 1
      (ReadOnlyQuery.Retained.begin unrelatedQuery)
    (ReadOnlyQuery.Retained.resumeValidated after 1 pending).map answer =
      some (some (false, false)) := by
  rfl

end Controls
end DescriptorObservation


/-! ## Finite interference witnesses for prepared occurrence commits

This checker traverses only the prepared occurrence sets and queried regions.
Its output explains the actual intersection or matching write that prevents
reuse. It does not ask whether a whole Space changed. The source compiler,
view owner and publication protocol must still establish that the supplied
footprints are complete, authentic and validated at the relevant boundary.
-/

namespace FiniteInterference

variable {O : Type u} [LinearOrder O] {R : Type v}

inductive Reason (O : Type u) (R : Type v) where
  | take (occurrence : O)
  | keep (occurrence : O)
  | fresh (occurrence : O)
  | query (read : PredicateQuery O R) (occurrence : O)

def Reason.Valid (label : O → R) (published pending : Commit O R) : Reason O R → Prop
  | .take o => o ∈ published.taken ∧ o ∈ pending.taken
  | .keep o => o ∈ published.taken ∧ o ∈ pending.kept
  | .fresh o => o ∈ published.made ∧ o ∈ pending.made
  | .query read o => read ∈ pending.queries ∧ o ∈ published.writes ∧ read.region (label o) = true

/-- Construct all finite reasons from actual prepared participants. Query
writes include makes even when the query's observed occurrence set was empty. -/
def reasons (label : O → R) (published pending : Commit O R) : List (Reason O R) :=
  ((published.taken ∩ pending.taken).sort (· ≤ ·)).map Reason.take ++
  ((published.taken ∩ pending.kept).sort (· ≤ ·)).map Reason.keep ++
  ((published.made ∩ pending.made).sort (· ≤ ·)).map Reason.fresh ++
  pending.queries.flatMap fun read =>
    ((published.writes.filter fun o => read.region (label o)).sort (· ≤ ·)).map (Reason.query read)

/-- The algorithm's witness membership is equivalent to the independent
occurrence/region conditions; no successful-check premise is built into Valid. -/
theorem mem_reasons_iff (label : O → R) (published pending : Commit O R) (reason : Reason O R) :
    reason ∈ reasons label published pending ↔ reason.Valid label published pending := by
  cases reason <;> simp [reasons, Reason.Valid]

def obstructs (label : O → R) (published pending : Commit O R) : Bool :=
  !(reasons label published pending).isEmpty

theorem obstructs_iff_reason (label : O → R) (published pending : Commit O R) :
    obstructs label published pending = true ↔ ∃ reason : Reason O R, reason.Valid label published pending := by
  have present : obstructs label published pending = true ↔
      ∃ reason, reason ∈ reasons label published pending := by
    cases h : reasons label published pending <;> simp [obstructs, h]
  simpa only [mem_reasons_iff] using present

/-- Exact agreement with the existing directional conflict relation. -/
theorem obstructs_iff (label : O → R) (published pending : Commit O R) :
    obstructs label published pending = true ↔
      Clash published pending ∨ Spoils label published pending := by
  rw [obstructs_iff_reason]
  constructor
  · rintro ⟨reason, valid⟩
    cases reason with
    | take o => exact Or.inl (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, valid.1, valid.2⟩))
    | keep o => exact Or.inr (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, valid.1, valid.2⟩))
    | fresh o => exact Or.inl (Or.inr (Finset.not_disjoint_iff.mpr ⟨o, valid.1, valid.2⟩))
    | query read o => exact Or.inr (Or.inr ⟨read, valid.1, o, valid.2.1, valid.2.2⟩)
  · rintro ((takes | made) | (kept | ⟨read, member, o, written, inRegion⟩))
    · obtain ⟨o, first, second⟩ := Finset.not_disjoint_iff.mp takes
      exact ⟨.take o, first, second⟩
    · obtain ⟨o, first, second⟩ := Finset.not_disjoint_iff.mp made
      exact ⟨.fresh o, first, second⟩
    · obtain ⟨o, first, second⟩ := Finset.not_disjoint_iff.mp kept
      exact ⟨.keep o, first, second⟩
    · exact ⟨.query read o, member, written, inRegion⟩

/-- Soundness also covers the region-read case, not only conflicting takes. -/
theorem soundFor (label : O → R) :
    SoundFor label (fun published pending => obstructs label published pending = true) := by
  intro published pending invalid
  apply (obstructs_iff label published pending).mpr
  rcases Liveness.invalidates_serializable_iff.mp invalid with takes | spoils
  · exact Or.inl (Or.inl takes)
  · exact Or.inr spoils

/-- Every returned reason belongs to the exact semantic footprint. No
physical hash/stripe collision is promoted to a semantic conflict. -/
theorem localTo (label : O → R) :
    LocalTo label id (fun published pending => obstructs label published pending = true) := by
  intro published pending detected
  exact clashOrSpoils_localTo label published pending ((obstructs_iff label published pending).mp detected)

theorem clear_iff (label : O → R) (published pending : Commit O R) :
    obstructs label published pending = false ↔
      ¬ Clash published pending ∧ ¬ Spoils label published pending := by
  rw [Bool.eq_false_iff]
  exact (not_congr (obstructs_iff label published pending)).trans not_or

/-- Two already-enabled commits give a concrete check for whether the pending
one remains enabled after this publication. This is a sequential boundary law,
not an assertion that validation and publication are atomically implemented. -/
theorem clear_iff_enabled_after (label : O → R) (published pending : Commit O R)
    (store : Finset O) (first : Enabled label store published) (second : Enabled label store pending) :
    obstructs label published pending = false ↔ Enabled label (fire store published) pending := by
  rw [clear_iff, enabled_fire_iff second first]
  constructor
  · rintro ⟨apart, preserved⟩
    exact ⟨fun clash => apart clash.symm, preserved⟩
  · rintro ⟨apart, preserved⟩
    exact ⟨fun clash => apart clash.symm, preserved⟩

/-- A clear result preserves the existing protocol's full readiness state. -/
theorem preserves_ready {T : Type w} [DecidableEq T]
    (label : O → R) (transactions : T → Commit O R) (state : ProtocolState O R T)
    (published pending : T) (different : pending ≠ published)
    (ready : Ready (txn := transactions) state pending)
    (clear : obstructs label (transactions published) (transactions pending) = false) :
    Ready (txn := transactions) (commitState label transactions published state) pending := by
  obtain ⟨apart, preserved⟩ := (clear_iff label _ _).mp clear
  exact ready_commitState different ready apart preserved

namespace Controls

/-- The first coordinate is a predicate; the second is its argument. -/
def label (occurrence : Nat) : Nat × Nat := (0, occurrence)
def absence : Commit Nat (Nat × Nat) := ⟨∅, ∅, ∅, [⟨fun x => x == (0, 0), ∅⟩]⟩
def fullRead : Commit Nat (Nat × Nat) := ⟨∅, ∅, ∅, [⟨fun x => x == (0, 0), {0}⟩]⟩

theorem distinct_same_predicate :
    obstructs label (Commit.takeOne 0) (Commit.takeOne 1) = false := by
  rw [clear_iff]
  unfold Clash Spoils WritesInto
  decide

theorem shared_keeps :
    obstructs label (Commit.keepOne 0) (Commit.keepOne 0) = false := by
  rw [clear_iff]
  unfold Clash Spoils WritesInto
  decide

theorem competing_takes :
    obstructs label (Commit.takeOne 0) (Commit.takeOne 0) = true := by
  rw [obstructs_iff]
  unfold Clash Spoils WritesInto
  decide

theorem kept_occurrence_is_protected :
    obstructs label (Commit.takeOne 0) (Commit.keepOne 0) = true := by
  rw [obstructs_iff]
  unfold Clash Spoils WritesInto
  decide

theorem fresh_identity_clash :
    obstructs label (Commit.makeOne 0) (Commit.makeOne 0) = true := by
  rw [obstructs_iff]
  unfold Clash Spoils WritesInto
  decide

theorem matching_insertion_into_empty_query :
    obstructs label (Commit.makeOne 0) absence = true := by
  rw [obstructs_iff]
  unfold Clash Spoils WritesInto
  decide

theorem matching_removal_from_full_query :
    obstructs label (Commit.takeOne 0) fullRead = true := by
  rw [obstructs_iff]
  unfold Clash Spoils WritesInto
  decide

theorem unrelated_same_predicate_query_write :
    obstructs label (Commit.makeOne 1) absence = false := by
  rw [clear_iff]
  unfold Clash Spoils WritesInto
  decide

/-- Equal content is not a common occurrence identity. -/
theorem duplicate_payloads_remain_distinct :
    obstructs (fun _ : Nat => (0, 7)) (Commit.takeOne 0) (Commit.takeOne 1) = false := by
  rw [clear_iff]
  unfold Clash Spoils WritesInto
  decide

#guard obstructs label (Commit.takeOne 0) (Commit.takeOne 1) == false
#guard obstructs label (Commit.keepOne 0) (Commit.keepOne 0) == false
#guard obstructs label (Commit.takeOne 0) (Commit.takeOne 0) == true
#guard obstructs label (Commit.takeOne 0) (Commit.keepOne 0) == true
#guard obstructs label (Commit.makeOne 0) (Commit.makeOne 0) == true
#guard obstructs label (Commit.makeOne 0) absence == true
#guard obstructs label (Commit.takeOne 0) fullRead == true
#guard obstructs label (Commit.makeOne 1) absence == false
#guard obstructs (fun _ : Nat => (0, 7)) (Commit.takeOne 0) (Commit.takeOne 1) == false

end Controls
end FiniteInterference

/-! ## Actual adaptive reads supply the local dependency boundary

The finite reference scanner orders complete region replies by occurrence
identity. This explicit order profile lets exact ordered query observations
use the set-based commit frame law. An arbitrary reordering scanner would
need its own order-preservation law. No native index or allocation cost is
claimed for this reference scanner.
-/

namespace SourceReads

open Mettapedia.Machines

variable {O : Type u} [LinearOrder O] {R : Type v} {Answer : Type w}

def scan (label : O → R) (store : Finset O) (region : R → Bool) : List O :=
  (regionOf label store region).sort (· ≤ ·)

theorem scan_complete (label : O → R) (store : Finset O) :
    Sources.Query.Complete label store (scan label store) := by
  intro region
  simp [scan]

/-- Convert the actual read log, including empty responses and repeated
reads, to the existing commit query format. The original log is retained;
only each query's occurrence membership is represented as a finite set. -/
def dependencyCommit (reads : ReadOnlyQuery.Reads (R → Bool) (List O)) : Commit O R :=
  ⟨∅, ∅, ∅, reads.map fun read => ⟨read.1, read.2.toFinset⟩⟩

/-- A clear local check preserves all actual read responses. The certificate
is supplied by execution; no user-specified footprint fidelity is assumed. -/
theorem clear_reads_agree (label : O → R) (store : Finset O) (published : Commit O R)
    (reads : ReadOnlyQuery.Reads (R → Bool) (List O))
    (authentic : ReadOnlyQuery.Agrees (scan label store) reads)
    (clear : FiniteInterference.obstructs label published (dependencyCommit reads) = false) :
    ReadOnlyQuery.Agrees (scan label (fire store published)) reads := by
  obtain ⟨_, noSpoil⟩ := (FiniteInterference.clear_iff label _ _).mp clear
  intro read member
  have outside : ∀ o ∈ published.taken ∪ published.made, read.1 (label o) = false := by
    intro o written
    apply Bool.eq_false_iff.mpr
    intro inRegion
    apply noSpoil
    exact Or.inr ⟨⟨read.1, read.2.toFinset⟩, List.mem_map.mpr ⟨read, member, rfl⟩,
      o, written, inRegion⟩
  have same := regionOf_fire_of_no_write (store := store) outside
  calc
    scan label (fire store published) read.1 = scan label store read.1 := by
      unfold scan
      rw [same]
    _ = read.2 := authentic read member

/-- Local validation of the reads generated by the program preserves the
whole adaptive execution: answer order, repeated answers and the chosen
sequence of later queries. A guard may return another query as its result. -/
theorem clear_preserves_program (label : O → R) (store : Finset O) (published : Commit O R)
    (program : ReadOnlyQuery.Program (R → Bool) (List O) Answer)
    (clear : FiniteInterference.obstructs label published
      (dependencyCommit (ReadOnlyQuery.run (scan label store) program).reads) = false) :
    ReadOnlyQuery.run (scan label (fire store published)) program =
      ReadOnlyQuery.run (scan label store) program :=
  ReadOnlyQuery.run_eq_of_agrees _ _ program
    (clear_reads_agree label store published _ (ReadOnlyQuery.run_agrees _ _) clear)

/-- The source compiler's complete row bag, including occurrence picks and
multiplicity, survives a publication outside its executed read regions. -/
theorem clear_preserves_source_rows {V P : Type v}
    (L : Sources.TermLayer V R P) (matcher : Sources.Matcher V R P)
    (label : O → R) (store : Finset O) (published : Commit O R)
    (template : List P) (source : Sources.SourceList V R P) (bindings : Sources.Subst V R)
    (clear : FiniteInterference.obstructs label published (dependencyCommit
      (ReadOnlyQuery.run (scan label store)
        (Sources.Query.compile L matcher label template source bindings)).reads) = false) :
    Sources.rows L matcher label (fire store published) template source bindings =
      Sources.rows L matcher label store template source bindings := by
  have same := clear_preserves_program label store published
    (Sources.Query.compile L matcher label template source bindings) clear
  have answers := congrArg (fun observation : ReadOnlyQuery.Observation (R → Bool) (List O)
      (List (Sources.Subst V R × List (Sources.Pick O R))) =>
    (observation.answer : Multiset (Sources.Subst V R × List (Sources.Pick O R)))) same
  simpa only [Sources.Query.run_compile L matcher label _ _ (scan_complete label _)] using answers

/-- With the independent matcher and pure-computation laws, the same local
check preserves absence in the declarative source semantics. -/
theorem clear_preserves_declarative_absence {V P : Type v} [DecidableEq V]
    (L : Sources.TermLayer V R P) (matcher : Sources.Matcher V R P)
    (label : O → R) (store : Finset O) (published : Commit O R)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher) (source : Sources.SourceList V R P)
    (respects : ∀ eval ∈ source.lets, Sources.Respects L eval) (bindings : Sources.Subst V R)
    (clear : FiniteInterference.obstructs label published (dependencyCommit
      (ReadOnlyQuery.run (scan label store)
        (Sources.Query.compile L matcher label [] source bindings)).reads) = false) :
    (¬ ∃ row, Sources.DRow L label (fire store published) [] source bindings row) ↔
      ¬ ∃ row, Sources.DRow L label store [] source bindings row := by
  rw [← Sources.rows_empty_iff_no_declarative sound complete minimal source respects bindings,
    ← Sources.rows_empty_iff_no_declarative sound complete minimal source respects bindings,
    clear_preserves_source_rows L matcher label store published [] source bindings clear]

namespace Controls

/-- The first reply computes the second question. Each second reply is
returned twice, so a support-only result comparison would be insufficient. -/
def adaptive : ReadOnlyQuery.Program (Nat → Bool) (List Nat) (List Nat) :=
  .read (fun n => n < 10) fun headers =>
    .read (fun n => n == headers.headD 0 + 10) fun replies =>
      .pure (replies ++ replies)

theorem actual_reads_include_computed_empty_region :
    ((ReadOnlyQuery.run (scan id {2}) adaptive).reads.map Prod.snd) = [[2], []] := by
  simp [ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_singleton]

theorem complete_dependency_refuses_matching_insertion :
    FiniteInterference.obstructs id (Commit.makeOne 12)
      (dependencyCommit (ReadOnlyQuery.run (scan id {2}) adaptive).reads) = true := by
  rw [FiniteInterference.obstructs_iff]
  simp [Clash, Spoils, WritesInto, dependencyCommit, ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_singleton]

theorem unrelated_write_preserves_duplicate_results :
    FiniteInterference.obstructs id (Commit.makeOne 99)
      (dependencyCommit (ReadOnlyQuery.run (scan id {2, 12}) adaptive).reads) = false ∧
      (ReadOnlyQuery.run (scan id {2, 12}) adaptive).answer = [12, 12] := by
  constructor
  · rw [FiniteInterference.clear_iff]
    simp [Clash, Spoils, WritesInto, dependencyCommit, ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_insert, Finset.filter_singleton]
  · simp [ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_insert, Finset.filter_singleton]

/-- Dropping the actual child read admits a publication that changes the
answer. A parent's valid read cannot authorize a forgotten continuation. -/
theorem missing_computed_read_accepts_changed_answer :
    FiniteInterference.obstructs id (Commit.makeOne 12)
      (dependencyCommit ((ReadOnlyQuery.run (scan id {2}) adaptive).reads.take 1)) = false ∧
      (ReadOnlyQuery.run (scan id {2}) adaptive).answer = [] ∧
      (ReadOnlyQuery.run (scan id {2, 12}) adaptive).answer = [12, 12] := by
  constructor
  · rw [FiniteInterference.clear_iff]
    simp [Clash, Spoils, WritesInto, dependencyCommit, ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_singleton]
  · simp [ReadOnlyQuery.run, scan, regionOf, adaptive, Finset.filter_insert, Finset.filter_singleton]

#guard FiniteInterference.obstructs id (Commit.makeOne 12)
  (dependencyCommit (ReadOnlyQuery.run (scan id {2}) adaptive).reads)
#guard !FiniteInterference.obstructs id (Commit.makeOne 99)
  (dependencyCommit (ReadOnlyQuery.run (scan id {2, 12}) adaptive).reads)

end Controls

/-! ### A retained source query supplies the registration recheck

The source computation may precede registration. Its complete read certificate
is validated in a coherent current view after registration, without repeating
the computation. Unfinished cuts do not justify sleep. A changed certificate
makes the waiter runnable for retry. The publication-to-notification path is
split into producing a notice and delivering it; producing a notice alone is
not a no-lost-wakeup guarantee.

Source-row readiness remains distinct from final commit admission, including
linearity, fresh allocation and current authority. The source guards here are
pure; this recheck cannot discard or replay an effectful earned prefix.
-/

namespace Enrollment

open Liveness.ParkingHandshake

omit [LinearOrder O] in
/-- One completion consumer for the existing retained-query and cursor
interfaces. Validation does not execute a source continuation or reset its
cost account. No completed observation means no decision to arm. -/
def recheckCompleted [DecidableEq O] (current : (R → Bool) → List O) (generation : Nat)
    (ready : Answer → Bool) (cell : Cell)
    (completed : Option (ReadOnlyQuery.Observation (R → Bool) (List O) Answer)) : Cell :=
  if generation = cell.generation ∧ cell.phase = .checking then
    match completed with
    | none => cell
    | some observation =>
        if ReadOnlyQuery.checkReads current observation.reads then
          step cell (.recheck generation (ready observation.answer))
        else step cell (.notify generation)
  else cell

omit [LinearOrder O] in
theorem completed_armed_iff [DecidableEq O] (current : (R → Bool) → List O) (generation : Nat)
    (ready : Answer → Bool)
    (completed : Option (ReadOnlyQuery.Observation (R → Bool) (List O) Answer)) :
    recheckCompleted current generation ready ⟨generation, .checking⟩ completed = ⟨generation, .armed⟩ ↔
      ∃ observation, completed = some observation ∧ ready observation.answer = false ∧
        ReadOnlyQuery.checkReads current observation.reads = true := by
  cases completed with
  | none => simp [recheckCompleted]
  | some observation =>
      cases result : ready observation.answer <;>
        cases valid : ReadOnlyQuery.checkReads current observation.reads <;>
          simp [recheckCompleted, result, valid, step]

/-- Inspect an earned retained cut. Neither an incomplete cut nor a stale
registration is interpreted as a completed false guard. The caller retains
the same cut on every branch; this operation performs no source continuation. -/
def recheck (label : O → R) (current : Finset O) (generation : Nat)
    (ready : Answer → Bool) (cell : Cell)
    (pending : ReadOnlyQuery.Retained.State (R → Bool) (List O) Answer) : Cell :=
  recheckCompleted (scan label current) generation ready cell
    (match pending.2 with
    | .read _ _ => none
    | .pure answer => some ⟨answer, pending.1⟩)

theorem stale_registration_ignored (label : O → R) (current : Finset O) (generation : Nat)
    (ready : Answer → Bool) (cell : Cell)
    (pending : ReadOnlyQuery.Retained.State (R → Bool) (List O) Answer)
    (stale : generation ≠ cell.generation) :
    recheck label current generation ready cell pending = cell := by simp [recheck, recheckCompleted, stale]

theorem unfinished_does_not_arm (label : O → R) (current : Finset O) (generation : Nat)
    (ready : Answer → Bool) (reads : ReadOnlyQuery.Reads (R → Bool) (List O))
    (region : R → Bool) (next : List O → ReadOnlyQuery.Program (R → Bool) (List O) Answer) :
    recheck label current generation ready ⟨generation, .checking⟩ (reads, .read region next) =
      ⟨generation, .checking⟩ := by simp [recheck, recheckCompleted]

/-- A notification received before recheck cannot be overwritten by an old
negative result, and it avoids even the redundant certificate validation. -/
theorem runnable_recheck_is_inert (label : O → R) (current : Finset O) (generation : Nat)
    (ready : Answer → Bool)
    (pending : ReadOnlyQuery.Retained.State (R → Bool) (List O) Answer) :
    recheck label current generation ready ⟨generation, .runnable⟩ pending =
      ⟨generation, .runnable⟩ := by simp [recheck, recheckCompleted]

theorem armed_iff (label : O → R) (current : Finset O) (generation : Nat)
    (ready : Answer → Bool)
    (pending : ReadOnlyQuery.Retained.State (R → Bool) (List O) Answer) :
    recheck label current generation ready ⟨generation, .checking⟩ pending = ⟨generation, .armed⟩ ↔
      ∃ answer, pending.2 = .pure answer ∧ ready answer = false ∧
        ReadOnlyQuery.checkReads (scan label current) pending.1 = true := by
  rcases pending with ⟨reads, residual⟩
  cases residual with
  | read region next => simp [recheck, recheckCompleted]
  | pure answer =>
      cases result : ready answer <;>
        cases valid : ReadOnlyQuery.checkReads (scan label current) reads <;>
          simp [recheck, recheckCompleted, result, valid, step]

/-- The original program, rather than an externally supplied guard bit,
returns false in the current view whenever its authentic cut arms the cell. -/
theorem armed_current_false (label : O → R) (captured current : Finset O) (generation fuel : Nat)
    (program : ReadOnlyQuery.Program (R → Bool) (List O) Answer) (ready : Answer → Bool)
    (armed : recheck label current generation ready ⟨generation, .checking⟩
      (ReadOnlyQuery.Retained.resume (scan label captured) fuel
        (ReadOnlyQuery.Retained.begin program)) = ⟨generation, .armed⟩) :
    ready (ReadOnlyQuery.run (scan label current) program).answer = false := by
  obtain ⟨answer, complete, negative, valid⟩ := (armed_iff label current generation ready _).mp armed
  simp only [ReadOnlyQuery.Retained.resume, ReadOnlyQuery.Retained.begin, List.nil_append] at complete valid
  have exactAnswer := (ReadOnlyQuery.Retained.validated_fresh
    (scan label captured) (scan label current) fuel program valid).1
  rw [complete] at exactAnswer
  change answer = (ReadOnlyQuery.run (scan label current) program).answer at exactAnswer
  rw [← exactAnswer]
  exact negative

/-- Route a completed publication against the actual enrolled reads. The
generation travels with the notice; transport and delivery remain explicit. -/
def notice (label : O → R) (published : Commit O R) (generation : Nat)
    (reads : ReadOnlyQuery.Reads (R → Bool) (List O)) : Option Nat :=
  if FiniteInterference.obstructs label published (dependencyCommit reads) then some generation else none

def deliver (cell : Cell) : Option Nat → Cell
  | none => cell
  | some generation => step cell (.notify generation)

/-- If a publication makes an armed source ready, the concrete local router
must produce its generation's notice. The proof derives its footprint from
the actual retained read path, including computed and empty regions. -/
theorem becomes_ready_requires_notice (label : O → R) (captured current : Finset O)
    (generation fuel : Nat) (program : ReadOnlyQuery.Program (R → Bool) (List O) Answer)
    (ready : Answer → Bool) (published : Commit O R)
    (armed : recheck label current generation ready ⟨generation, .checking⟩
      (ReadOnlyQuery.Retained.resume (scan label captured) fuel
        (ReadOnlyQuery.Retained.begin program)) = ⟨generation, .armed⟩)
    (nowReady : ready (ReadOnlyQuery.run (scan label (fire current published)) program).answer = true) :
    notice label published generation (ReadOnlyQuery.Retained.resume (scan label captured) fuel
      (ReadOnlyQuery.Retained.begin program)).1 = some generation := by
  unfold notice
  split
  · rfl
  · rename_i noNotice
    have clear := Bool.eq_false_iff.mpr noNotice
    obtain ⟨answer, complete, negative, valid⟩ := (armed_iff label current generation ready _).mp armed
    have afterAgrees := clear_reads_agree label current published _
      ((ReadOnlyQuery.checkReads_iff _ _).mp valid) clear
    have afterValid := (ReadOnlyQuery.checkReads_iff _ _).mpr afterAgrees
    simp only [ReadOnlyQuery.Retained.resume, ReadOnlyQuery.Retained.begin, List.nil_append] at complete afterValid
    have exactAnswer := (ReadOnlyQuery.Retained.validated_fresh
      (scan label captured) (scan label (fire current published)) fuel program afterValid).1
    rw [complete] at exactAnswer
    change answer = (ReadOnlyQuery.run (scan label (fire current published)) program).answer at exactAnswer
    rw [← exactAnswer, negative] at nowReady
    contradiction

/-- The source-to-notice law joins the existing arbitrary-suffix handshake
invariant once this notice is delivered. Delayed delivery is not elided. -/
theorem delivered_ready_change_cannot_sleep (label : O → R) (captured current : Finset O)
    (generation fuel : Nat) (program : ReadOnlyQuery.Program (R → Bool) (List O) Answer)
    (ready : Answer → Bool) (published : Commit O R) (later : List Action)
    (armed : recheck label current generation ready ⟨generation, .checking⟩
      (ReadOnlyQuery.Retained.resume (scan label captured) fuel
        (ReadOnlyQuery.Retained.begin program)) = ⟨generation, .armed⟩)
    (nowReady : ready (ReadOnlyQuery.run (scan label (fire current published)) program).answer = true)
    (same : (execute (deliver ⟨generation, .armed⟩ (notice label published generation
      (ReadOnlyQuery.Retained.resume (scan label captured) fuel
        (ReadOnlyQuery.Retained.begin program)).1)) later).generation = generation) :
    (execute (deliver ⟨generation, .armed⟩ (notice label published generation
      (ReadOnlyQuery.Retained.resume (scan label captured) fuel
        (ReadOnlyQuery.Retained.begin program)).1)) later).phase ≠ .asleep := by
  have routed := becomes_ready_requires_notice label captured current generation fuel program ready published armed nowReady
  rw [routed] at same ⊢
  exact notified_never_sleeps ⟨generation, .armed⟩ later (by simp) same

/-- The existing source cursor, including its explicit completion inspection,
supplies the same recheck consumer. Arming implies absence in the independent
source judgment at the current store. Scanner and matcher laws retain their
own scope; no Boolean guard-correctness premise replaces this construction. -/
theorem armed_source_has_no_row {O V T P : Type u} [DecidableEq O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (current : Finset O) (before now : (T → Bool) → List O)
    (scanned : Sources.Query.Complete label current now)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher) (source : Sources.SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Sources.Respects L eval) (bindings : Sources.Subst V T)
    (generation fuel : Nat)
    (armed : recheckCompleted now generation (fun rows => !List.isEmpty rows) ⟨generation, .checking⟩
      (Cursor.ReadOnlyQuery.completed? before
        (Sources.Query.Execution.execute L matcher label before [] source bindings fuel).2) =
        ⟨generation, .armed⟩) :
    ¬ ∃ row, Sources.DRow L label current [] source bindings row := by
  obtain ⟨observation, finished, negative, valid⟩ :=
    (completed_armed_iff now generation (fun rows => !List.isEmpty rows) _).mp armed
  have same := Cursor.ReadOnlyQuery.validated_completion before now fuel
    (Sources.Query.compile L matcher label [] source bindings) observation finished valid
  apply (Sources.Query.run_empty_iff_no_declarative L matcher label current now scanned
    sound complete minimal source respects bindings).mp
  rw [same]
  cases listEq : observation.answer with
  | nil => rfl
  | cons head tail => simp [listEq] at negative

/-- A new independent source row after publication forces a local notice
for the actual completed source cursor that armed the waiter. This joins
source semantics, real cursor completion, validation and routing directly. -/
theorem new_source_row_requires_notice {O V T P : Type u} [LinearOrder O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (current : Finset O) (before : (T → Bool) → List O)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher) (source : Sources.SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Sources.Respects L eval) (bindings : Sources.Subst V T)
    (generation fuel : Nat) (published : Commit O T)
    (armed : recheckCompleted (scan label current) generation (fun rows => !List.isEmpty rows)
      ⟨generation, .checking⟩ (Cursor.ReadOnlyQuery.completed? before
        (Sources.Query.Execution.execute L matcher label before [] source bindings fuel).2) =
        ⟨generation, .armed⟩)
    (appeared : ∃ row, Sources.DRow L label (fire current published) [] source bindings row) :
    ∃ observation, Cursor.ReadOnlyQuery.completed? before
        (Sources.Query.Execution.execute L matcher label before [] source bindings fuel).2 =
          some observation ∧ notice label published generation observation.reads = some generation := by
  obtain ⟨observation, finished, negative, valid⟩ :=
    (completed_armed_iff (scan label current) generation (fun rows => !List.isEmpty rows) _).mp armed
  refine ⟨observation, finished, ?_⟩
  unfold notice
  split
  · rfl
  · rename_i noNotice
    have afterAgrees := clear_reads_agree label current published observation.reads
      ((ReadOnlyQuery.checkReads_iff _ _).mp valid) (Bool.eq_false_iff.mpr noNotice)
    have same := Cursor.ReadOnlyQuery.validated_completion before (scan label (fire current published)) fuel
      (Sources.Query.compile L matcher label [] source bindings) observation finished
      ((ReadOnlyQuery.checkReads_iff _ _).mpr afterAgrees)
    have absent := (Sources.Query.run_empty_iff_no_declarative L matcher label (fire current published)
      (scan label (fire current published)) (scan_complete label _) sound complete minimal source respects bindings).mp
    exfalso
    apply absent ?_ appeared
    rw [same]
    cases listEq : observation.answer with
    | nil => rfl
    | cons head tail => simp [listEq] at negative


/-! ### Source readiness reaches a retained journal and the actual ready queue

The same completed cursor supplies both the registration recheck and the
publication's dependency test. The adapter records a generation-bearing wake
before admission. Its service bound assumes successful admission, a fixed
registration and owner-local queue visits; it does not assume that the new
source row remains enabled until the consumer executes it.
-/

omit [LinearOrder O] in
def recheckQueue [DecidableEq O] (scanner : (R → Bool) → List O)
    (key : Mettapedia.Machines.AsyncWait.Identity) (ready : Answer → Bool)
    (completed : Option (ReadOnlyQuery.Observation (R → Bool) (List O) Answer))
    (state : QueueDelivery.State) : QueueDelivery.State :=
  if state.keys key.owner = some key then
    { state with cells := (Function.update state.cells key.owner
        (recheckCompleted scanner key.generation ready (state.cells key.owner) completed)) }
  else state

omit [LinearOrder O] in
theorem recheckQueue_other_key [DecidableEq O] (scanner : (R → Bool) → List O)
    (key : Mettapedia.Machines.AsyncWait.Identity) (ready : Answer → Bool)
    (completed : Option (ReadOnlyQuery.Observation (R → Bool) (List O) Answer))
    (state : QueueDelivery.State) (unowned : state.keys key.owner ≠ some key) :
    recheckQueue scanner key ready completed state = state := by simp [recheckQueue, unowned]

/-- A source publication routes only against an actually completed read
certificate. Neither unfinished source work nor an unrelated publication
creates a wake in this adapter. Registration identity is retained in full. -/
def routeCompleted (label : O → R) (published : Commit O R)
    (key : Mettapedia.Machines.AsyncWait.Identity) (serial : Nat)
    (completed : Option (ReadOnlyQuery.Observation (R → Bool) (List O) Answer))
    (inbox : Mettapedia.Machines.EventPump.Inbox) (state : QueueDelivery.State) :
    Mettapedia.Machines.EventPump.Inbox × QueueDelivery.State :=
  match completed with
  | none => (inbox, state)
  | some observation =>
      match notice label published key.generation observation.reads with
      | none => (inbox, state)
      | some generation => QueueDelivery.recordAndOffer key inbox
          ⟨serial, { key with generation := generation }, 0⟩ state

theorem unfinished_source_is_not_routed (label : O → R) (published : Commit O R)
    (key : Mettapedia.Machines.AsyncWait.Identity) (serial : Nat)
    (inbox : Mettapedia.Machines.EventPump.Inbox) (state : QueueDelivery.State) :
    routeCompleted (Answer := Answer) label published key serial none inbox state =
      (inbox, state) := rfl

/-- Independent declarative source readiness forces a recorded wake through
executed reads, rechecking, local routing and actual queue admission. The
consumer claim and receipt settle delivery only, not source execution.
Admission fairness, coherent concurrent reads and pointer lifetime remain
separate obligations. -/
theorem new_source_row_recorded_handoff {O V T P : Type u} [LinearOrder O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (current : Finset O) (before : (T → Bool) → List O)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher) (source : Sources.SourceList V T P)
    (respects : ∀ eval ∈ source.lets, Sources.Respects L eval) (bindings : Sources.Subst V T)
    (key : Mettapedia.Machines.AsyncWait.Identity) (serial fuel : Nat) (published : Commit O T)
    (inbox : Mettapedia.Machines.EventPump.Inbox) (state : QueueDelivery.State)
    (tasks : List Nat) (offered : Nat → List Nat)
    (owned : state.keys key.owner = some key)
    (owner : inbox.owner = key) (fresh : inbox.phase serial = none)
    (valid : Mettapedia.Machines.ReadyQueue.invariant state.ready) (empty : state.pending = [])
    (checking : state.cells key.owner = ⟨key.generation, .checking⟩)
    (armed : recheckCompleted (scan label current) key.generation (fun rows => !List.isEmpty rows)
      ⟨key.generation, .checking⟩ (Cursor.ReadOnlyQuery.completed? before
        (Sources.Query.Execution.execute L matcher label before [] source bindings fuel).2) =
        ⟨key.generation, .armed⟩)
    (appeared : ∃ row, Sources.DRow L label (fire current published) [] source bindings row)
    (admitted : Mettapedia.Machines.EventPump.admit state.ready.capacity state.ready.tasks key.owner = some tasks)
    (binding : key.owner ∈ state.ready.tasks → state.bound key.owner = some key.generation) :
    let completed := Cursor.ReadOnlyQuery.completed? before
      (Sources.Query.Execution.execute L matcher label before [] source bindings fuel).2
    let checked := recheckQueue (scan label current) key (fun rows => !List.isEmpty rows) completed state
    let routed := routeCompleted label published key serial completed inbox checked
    let event : Mettapedia.Machines.EventPump.Event := ⟨serial, key, 0⟩
    event ∈ Mettapedia.Machines.EventPump.pending routed.1 ∧
      ∃ slots ≤ routed.2.ready.tasks.length,
        (QueueDelivery.run slots offered routed.2).2.cells key.owner = ⟨key.generation, .claimed⟩ ∧
        (QueueDelivery.acknowledgeClaimed key routed.1 event
          (QueueDelivery.run slots offered routed.2).2).phase serial = some .settled := by
  obtain ⟨observation, finished, noticed⟩ := new_source_row_requires_notice L matcher label current
    before sound complete minimal source respects bindings key.generation fuel published armed appeared
  dsimp only
  simp only [routeCompleted, finished, noticed]
  apply QueueDelivery.recorded_notice_bounded_handoff_and_ack key inbox ⟨serial, key, 0⟩
    (recheckQueue (scan label current) key (fun rows => !List.isEmpty rows) (some observation) state)
    tasks offered (by simp [recheckQueue, owned]) owner rfl rfl fresh (by simpa [recheckQueue, owned] using valid) (by simpa [recheckQueue, owned] using empty)
  · simpa only [recheckQueue, if_pos owned, Function.update_self, checking, finished] using armed
  · simpa only [recheckQueue, if_pos owned] using admitted
  · simpa only [recheckQueue, if_pos owned] using binding

/-! ### Registration-bound acquired source uses

The existing queue keeps the current key; the existing acquired-use owner
keeps the captured source. Old registrations remain addressable for release
and lifetime reads after their queue slot has been re-armed. New operations
must pass both the full-key check and the owner's current exclusive-use check.
This is an owner-local registry construction, not a native pointer/lock proof.
-/

namespace Registration

open Mettapedia.Machines
open ResourceOwnership

variable {Resource Holder Use : Type} [DecidableEq Use]

abbrev Owner (Holder Use Resource : Type) := AcquiredUse.State Holder Use Resource

structure State (Holder Use Resource : Type) where
  queue : QueueDelivery.State
  sources : AsyncWait.Identity → Option (Owner Holder Use Resource)

def empty (capacity : Nat) : State Holder Use Resource :=
  ⟨{ ready := ⟨capacity, []⟩, cells := fun _ => ⟨0, .idle⟩, bound := fun _ => none }, fun _ => none⟩

/-- Only the queue's installer issues the key. Its captured resource is
installed once under that key, without replacing an older acquired owner. -/
def install (holder : Holder) (slot serial : Nat) (resource : Resource) (state : State Holder Use Resource) :
    Option (AsyncWait.Identity × State Holder Use Resource) :=
  (QueueDelivery.install slot serial state.queue).bind fun installed =>
    if (state.sources installed.1).isNone then
      some (installed.1, ⟨installed.2,
        Function.update state.sources installed.1 (some (AcquiredUse.initial holder resource))⟩)
    else none

/-- Acquire through the actual registry before inspecting the captured
source. Registry metadata is the atomic acquired-use boundary. -/
def acquire [DecidableEq Holder] (limit : Nat) (mode : AcquiredUse.Mode) (holder : Holder) (key : AsyncWait.Identity) (use : Use)
    (state : State Holder Use Resource) : Option (State Holder Use Resource) :=
  if state.queue.keys key.owner = some key then
    (state.sources key).bind fun owner =>
      (AcquiredUse.acquire limit mode holder use owner).map fun result =>
        { state with sources := Function.update state.sources key (some result.next) }
  else none

/-- A held lifetime use can still read an old captured resource after its
registration is retired. This alone grants no current operation. -/
def readHeld (key : AsyncWait.Identity) (use : Use) (state : State Holder Use Resource) : Option Resource :=
  (state.sources key).bind (AcquiredUse.readUse use)

/-- An operation uses the current full question key and an actual exclusive
receipt. Retained bytes and a matching generation alone are insufficient. -/
def readCurrent (key : AsyncWait.Identity) (use : Use) (state : State Holder Use Resource) : Option Resource :=
  if state.queue.keys key.owner = some key then
    (state.sources key).bind fun owner =>
      if owner.current = true ∧ AcquiredUse.mayMutate use owner then AcquiredUse.readUse use owner else none
  else none

/-- Retire the wake registration and detach its source owner together.
Outstanding acquired uses stay in the table. Any extracted resource is
returned separately for finalization after this registry transition. -/
def retire (key : AsyncWait.Identity) (inbox : EventPump.Inbox) (state : State Holder Use Resource) :
    Option (EventPump.Inbox × Option Resource × State Holder Use Resource) :=
  if state.queue.keys key.owner = some key then
    (state.sources key).bind fun owner =>
      let retired := QueueDelivery.retireAndRearm key inbox state.queue
      if retired.2.keys key.owner = none then
        let detached := AcquiredUse.detach owner
        some (retired.1, detached.retired,
          ⟨retired.2, Function.update state.sources key (some detached.next)⟩)
      else none
  else none

/-- Revocation ends current source authority immediately while retaining
acquired lifetime edges. The key remains installed until wake retirement. -/
def revoke (key : Mettapedia.Machines.AsyncWait.Identity) (state : State Holder Use Resource) :
    Option (Option Resource × State Holder Use Resource) :=
  if state.queue.keys key.owner = some key then
    (state.sources key).map fun owner =>
      let result := AcquiredUse.detach owner
      (result.retired, ⟨QueueDelivery.cancelCurrent key state.queue,
        Function.update state.sources key (some result.next)⟩)
  else none

/-- Release addresses the original full key even after its queue slot is
reused. It cannot release a use in the new question's owner. -/
def release (key : AsyncWait.Identity) (use : Use) (state : State Holder Use Resource) :
    Option (Option Resource × State Holder Use Resource) :=
  (state.sources key).bind fun owner =>
    (AcquiredUse.releaseUse use owner).map fun result =>
      (result.retired, { state with sources := Function.update state.sources key (some result.next) })

omit [DecidableEq Use] in
theorem install_binds_source (holder : Holder) (slot serial : Nat) (resource : Resource)
    (before after : State Holder Use Resource) (key : AsyncWait.Identity)
    (installed : install holder slot serial resource before = some (key, after)) :
    after.queue.keys key.owner = some key ∧
      after.queue.cells key.owner = ⟨key.generation, .checking⟩ ∧
      after.sources key = some (AcquiredUse.initial holder resource) := by
  unfold install at installed
  obtain ⟨⟨issued, queue⟩, issuedAt, rest⟩ := Option.bind_eq_some_iff.mp installed
  split at rest
  · cases Option.some.inj rest
    obtain ⟨owner, _, held, checking, _, _⟩ := QueueDelivery.install_establishes_key slot serial _ _ issued issuedAt
    exact ⟨owner ▸ held, owner ▸ checking, by simp⟩
  · cases rest

omit [DecidableEq Use] in
theorem install_preserves_existing_source (holder : Holder) (slot serial : Nat) (resource : Resource)
    (before after : State Holder Use Resource) (key other : AsyncWait.Identity) (owner : Owner Holder Use Resource)
    (found : before.sources other = some owner)
    (installed : install holder slot serial resource before = some (key, after)) :
    after.sources other = some owner := by
  unfold install at installed
  obtain ⟨⟨issued, queue⟩, _, rest⟩ := Option.bind_eq_some_iff.mp installed
  split at rest
  · rename_i vacant
    cases Option.some.inj rest
    have different : other ≠ issued := by
      intro same
      subst other
      simp [found] at vacant
    simpa [different] using found
  · cases rest

theorem wrong_holder_cannot_acquire [DecidableEq Holder] (limit : Nat) (mode : AcquiredUse.Mode)
    (holder : Holder) (key : AsyncWait.Identity) (use : Use) (state : State Holder Use Resource)
    (owner : Owner Holder Use Resource) (found : state.sources key = some owner)
    (unheld : holder ∉ owner.holders) : acquire limit mode holder key use state = none := by
  unfold acquire
  split
  · simp [found, AcquiredUse.wrong_holder_refused limit mode owner holder use unheld]
  · rfl

theorem acquire_before_read [DecidableEq Holder] (limit : Nat) (mode : AcquiredUse.Mode) (holder : Holder) (key : AsyncWait.Identity)
    (use : Use) (before after : State Holder Use Resource)
    (acquired : acquire limit mode holder key use before = some after) :
    before.queue.keys key.owner = some key ∧ after.queue = before.queue ∧
      ∃ owner result, before.sources key = some owner ∧
        AcquiredUse.acquire limit mode holder use owner = some result ∧
        after.sources key = some result.next ∧ use ∈ result.next.uses ∧
        result.next.resource = owner.resource := by
  unfold acquire at acquired
  split at acquired
  · rename_i owned
    obtain ⟨owner, found, rest⟩ := Option.bind_eq_some_iff.mp acquired
    obtain ⟨result, accepted, equal⟩ := Option.map_eq_some_iff.mp rest
    cases equal
    refine ⟨owned, rfl, owner, result, found, accepted, by simp, ?_⟩
    unfold AcquiredUse.acquire at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact ⟨Finset.mem_insert_self _ _, rfl⟩
    · cases accepted
  · cases acquired

theorem readCurrent_requires_owned_use (key : AsyncWait.Identity) (use : Use)
    (state : State Holder Use Resource) (resource : Resource)
    (read : readCurrent key use state = some resource) :
    state.queue.keys key.owner = some key ∧
      ∃ owner, state.sources key = some owner ∧ owner.current = true ∧
        AcquiredUse.mayMutate use owner ∧ use ∈ owner.uses ∧ owner.resource = some resource := by
  unfold readCurrent at read
  split at read
  · rename_i owned
    obtain ⟨owner, found, rest⟩ := Option.bind_eq_some_iff.mp read
    split at rest
    · rename_i admitted
      exact ⟨owned, owner, found, admitted.1, admitted.2, admitted.2.1,
        by simpa only [AcquiredUse.readUse, if_pos admitted.2.1] using rest⟩
    · cases rest
  · cases read

theorem wrong_key_cannot_acquire_or_read [DecidableEq Holder] (limit : Nat) (mode : AcquiredUse.Mode)
    (holder : Holder) (key : AsyncWait.Identity) (use : Use) (state : State Holder Use Resource)
    (unowned : state.queue.keys key.owner ≠ some key) :
    acquire limit mode holder key use state = none ∧ readCurrent key use state = none := by
  simp [acquire, readCurrent, unowned]

theorem retire_keeps_acquired_source (key : AsyncWait.Identity) (use : Use)
    (inbox afterInbox : EventPump.Inbox) (before after : State Holder Use Resource)
    (retired : Option Resource) (owner : Owner Holder Use Resource)
    (found : before.sources key = some owner) (issued : use ∈ owner.uses)
    (done : retire key inbox before = some (afterInbox, retired, after)) :
    retired = none ∧ readHeld key use after = owner.resource ∧
      readCurrent key use after = none ∧ after.queue.keys key.owner = none := by
  unfold retire at done
  split at done
  · simp only [found, Option.bind_some] at done
    split at done
    · rename_i cleared
      cases Option.some.inj done
      exact ⟨by rw [AcquiredUse.detach_with_use owner issued],
        by simp only [readHeld, Function.update_self, Option.bind_some]; exact AcquiredUse.detached_read_preserved owner issued,
        by simp [readCurrent, cleared], cleared⟩
    · cases done
  · cases done

theorem release_other_key_preserved (key other : AsyncWait.Identity) (use : Use)
    (before after : State Holder Use Resource) (retired : Option Resource) (different : other ≠ key)
    (released : release key use before = some (retired, after)) :
    after.sources other = before.sources other ∧ after.queue = before.queue := by
  unfold release at released
  obtain ⟨owner, _, rest⟩ := Option.bind_eq_some_iff.mp released
  obtain ⟨result, _, equal⟩ := Option.map_eq_some_iff.mp rest
  cases equal
  exact ⟨by simp [different], rfl⟩

theorem acquire_installed_source [DecidableEq Holder] (holder : Holder) (slot serial limit : Nat) (resource : Resource)
    (before installed : State Holder Use Resource) (key : AsyncWait.Identity) (use : Use)
    (opened : install holder slot serial resource before = some (key, installed)) (room : 0 < limit) :
    ∃ owned, acquire limit .exclusive holder key use installed = some owned ∧
      readCurrent key use owned = some resource ∧ owned.queue = installed.queue := by
  obtain ⟨keyed, _, retained⟩ := install_binds_source holder slot serial resource before installed key opened
  let owner : Owner Holder Use Resource := ⟨true, {holder}, {use}, some use, some resource⟩
  refine ⟨{ installed with sources := Function.update installed.sources key (some owner) }, ?_, ?_, rfl⟩
  · simp [acquire, keyed, retained, AcquiredUse.acquire, AcquiredUse.initial, room, owner]
  · simp [readCurrent, keyed, owner, AcquiredUse.mayMutate, AcquiredUse.readUse]

theorem revoke_preserves_held_but_refuses_current (key : AsyncWait.Identity) (use : Use)
    (before after : State Holder Use Resource) (retired : Option Resource) (owner : Owner Holder Use Resource)
    (found : before.sources key = some owner) (issued : use ∈ owner.uses)
    (revoked : revoke key before = some (retired, after)) :
    retired = none ∧ readHeld key use after = owner.resource ∧ readCurrent key use after = none := by
  unfold revoke at revoked
  split at revoked
  · simp only [found, Option.map_some] at revoked
    cases Option.some.inj revoked
    refine ⟨by rw [AcquiredUse.detach_with_use owner issued], ?_, ?_⟩
    · simp only [readHeld, Function.update_self, Option.bind_some]
      exact AcquiredUse.detached_read_preserved owner issued
    · simp [readCurrent, AcquiredUse.detach_revokes]
  · cases revoked

/-- Release returns an old source exactly once after detachment and its
last use. Its queue state and other source owners are untouched. -/
theorem final_detached_release (holder : Holder) (key : AsyncWait.Identity) (use : Use)
    (state : State Holder Use Resource) (resource : Resource)
    (found : state.sources key = some (⟨false, {holder}, {use}, none, some resource⟩ : Owner Holder Use Resource)) :
    ∃ after, release key use state = some (some resource, after) ∧
      readHeld key use after = none ∧ release key use after = none ∧ after.queue = state.queue := by
  refine ⟨{ state with sources := (Function.update state.sources key
    (some ⟨false, {holder}, ∅, none, none⟩)) }, ?_, ?_, ?_, rfl⟩
  all_goals simp [release, found, readHeld, AcquiredUse.releaseUse, AcquiredUse.extract, AcquiredUse.readUse]

/-- Every stored source obeys the existing current-slot/acquired-use
retention law, including retired entries still carrying lifetime uses. -/
def OwnersValid (state : State Holder Use Resource) : Prop :=
  ∀ key owner, state.sources key = some owner → AcquiredUse.WellFormed owner

omit [DecidableEq Use] in
theorem empty_owners_valid (capacity : Nat) : OwnersValid (empty (Holder := Holder) (Use := Use) (Resource := Resource) capacity) := by
  intro key owner impossible
  cases impossible

omit [DecidableEq Use] in
private theorem update_sources_valid (before : State Holder Use Resource) (queue : QueueDelivery.State)
    (key : AsyncWait.Identity) (owner : Owner Holder Use Resource) (valid : OwnersValid before)
    (newValid : AcquiredUse.WellFormed owner) :
    OwnersValid ⟨queue, Function.update before.sources key (some owner)⟩ := by
  intro other stored found
  by_cases same : other = key
  · subst other
    simp only [Function.update_self, Option.some.injEq] at found
    exact found ▸ newValid
  · exact valid other stored (by simpa [same] using found)

omit [DecidableEq Use] in
theorem install_owners_valid (holder : Holder) (slot serial : Nat) (resource : Resource)
    (before after : State Holder Use Resource) (key : AsyncWait.Identity) (valid : OwnersValid before)
    (installed : install holder slot serial resource before = some (key, after)) : OwnersValid after := by
  unfold install at installed
  obtain ⟨⟨issued, queue⟩, _, rest⟩ := Option.bind_eq_some_iff.mp installed
  split at rest
  · cases Option.some.inj rest
    exact update_sources_valid before queue issued _ valid (AcquiredUse.initial_wellFormed holder resource)
  · cases rest

theorem acquire_owners_valid [DecidableEq Holder] (limit : Nat) (mode : AcquiredUse.Mode) (holder : Holder) (key : AsyncWait.Identity)
    (use : Use) (before after : State Holder Use Resource) (valid : OwnersValid before)
    (acquired : acquire limit mode holder key use before = some after) : OwnersValid after := by
  unfold acquire at acquired
  split at acquired
  · obtain ⟨owner, found, rest⟩ := Option.bind_eq_some_iff.mp acquired
    obtain ⟨result, accepted, equal⟩ := Option.map_eq_some_iff.mp rest
    cases equal
    exact update_sources_valid before before.queue key result.next valid
      (AcquiredUse.acquire_wellFormed limit mode holder use (valid key owner found) accepted)
  · cases acquired

theorem revoke_owners_valid (key : AsyncWait.Identity) (before after : State Holder Use Resource)
    (retired : Option Resource) (valid : OwnersValid before)
    (revoked : revoke key before = some (retired, after)) : OwnersValid after := by
  unfold revoke at revoked
  split at revoked
  · obtain ⟨owner, found, equal⟩ := Option.map_eq_some_iff.mp revoked
    cases equal
    exact update_sources_valid before _ key _ valid (AcquiredUse.detach_wellFormed owner (valid key owner found))
  · cases revoked

theorem retire_owners_valid (key : AsyncWait.Identity) (inbox afterInbox : EventPump.Inbox)
    (before after : State Holder Use Resource) (retired : Option Resource) (valid : OwnersValid before)
    (done : retire key inbox before = some (afterInbox, retired, after)) : OwnersValid after := by
  unfold retire at done
  split at done
  · obtain ⟨owner, found, rest⟩ := Option.bind_eq_some_iff.mp done
    dsimp only at rest
    split at rest
    · cases Option.some.inj rest
      exact update_sources_valid before _ key _ valid (AcquiredUse.detach_wellFormed owner (valid key owner found))
    · cases rest
  · cases done

theorem release_owners_valid (key : AsyncWait.Identity) (use : Use) (before after : State Holder Use Resource)
    (retired : Option Resource) (valid : OwnersValid before)
    (released : release key use before = some (retired, after)) : OwnersValid after := by
  unfold release at released
  obtain ⟨owner, found, rest⟩ := Option.bind_eq_some_iff.mp released
  obtain ⟨result, accepted, equal⟩ := Option.map_eq_some_iff.mp rest
  cases equal
  exact update_sources_valid before before.queue key result.next valid
    (AcquiredUse.releaseUse_wellFormed use (valid key owner found) accepted)

/-- Retiring a source with an acquired use preserves the complete reachable
resource graph's ordered observations, including negative paths and repeats.
The address projection must identify the actual captured-resource root. -/
theorem retire_preserves_acquired_observations {Address Value : Type} [DecidableEq Address]
    (key : AsyncWait.Identity) (use : Use) (inbox afterInbox : EventPump.Inbox)
    (before after : State Holder Use Resource) (retired : Option Resource) (owner : Owner Holder Use Resource)
    (found : before.sources key = some owner) (issued : use ∈ owner.uses)
    (done : retire key inbox before = some (afterInbox, retired, after))
    (address : Resource → Address) (heap : ResourceOwnership.Heap Address Value)
    (outside : ResourceOwnership.Roots (Unit ⊕ Use) Address) (paths : List (Address × List Address))
    (live : ∀ path ∈ paths, ResourceOwnership.Live heap (AcquiredUse.roots owner address ∪ outside) path.1) :
    ∃ held, after.sources key = some held ∧
      ResourceOwnership.RequestBorrow.observe
        (ResourceOwnership.collect heap (AcquiredUse.roots held address ∪ outside)) paths =
      ResourceOwnership.RequestBorrow.observe heap paths := by
  unfold retire at done
  split at done
  · simp only [found, Option.bind_some] at done
    split at done
    · cases Option.some.inj done
      exact ⟨(AcquiredUse.detach owner).next, by simp,
        AcquiredUse.detach_keeps_observations owner address heap outside issued paths live⟩
    · cases done
  · cases done

/-- Fair pending admission delivers the matching generation while preserving
its exact acquired source. This does not run or restart a completed guard;
the outer reactive continuation remains a separate execution obligation. -/
theorem pending_handoff_retains_acquired_source (state : State Holder Use Resource)
    (key : AsyncWait.Identity) (use : Use) (resource : Resource) (offered : Nat → List Nat)
    (valid : QueueDelivery.Admission.Valid state.queue) (positive : 0 < state.queue.ready.capacity)
    (pending : key ∈ state.queue.pending) (retained : readCurrent key use state = some resource) :
    ∃ slots ≤ state.queue.ready.tasks.length + state.queue.pending.length,
      let after := { state with queue := (QueueDelivery.Admission.run slots offered state.queue).2 }
      after.queue.cells key.owner = ⟨key.generation, .claimed⟩ ∧
        readCurrent key use after = some resource ∧ after.sources = state.sources := by
  obtain ⟨slots, bounded, claimed⟩ := QueueDelivery.Admission.pending_gets_bounded_handoff
    state.queue key offered valid positive pending
  refine ⟨slots, bounded, claimed, ?_, rfl⟩
  simpa only [readCurrent, QueueDelivery.Admission.run_keys] using retained

/-- The source registry reuses the existing cursor/context record. -/
abbrev Capture {Key Value Answer : Type} (scanner : Key → Value) (Context : Type) :=
  Cursor.Fold.OwnedSequence.CallbackBoundary.Retained.State
    (Cursor.ReadOnlyQuery.provider scanner) (Cursor.ReadOnlyQuery.client (Answer := Answer)) .unit Context

/-- Rechecking reads the actual acquired source packet from the registry.
No caller-supplied answer, context or alternative packet is accepted here. -/
def recheckSource {O T Answer Context : Type} [DecidableEq O]
    (scanner current : (T → Bool) → List O) (key : AsyncWait.Identity) (use : Use) (ready : Answer → Bool)
    (state : State Holder Use (Capture (Answer := Answer) scanner Context)) :
    Option (State Holder Use (Capture (Answer := Answer) scanner Context)) :=
  (readCurrent key use state).map fun captured =>
    { state with queue := (recheckQueue current key ready
        (Cursor.ReadOnlyQuery.completed? scanner captured.computation.2) state.queue) }

/-- The whole captured computation and context remain in the same owner
when its complete observation is used to recheck the installed waiter. -/
theorem recheckSource_retains_capture {O T Answer Context : Type} [DecidableEq O]
    (scanner current : (T → Bool) → List O) (key : AsyncWait.Identity) (use : Use) (ready : Answer → Bool)
    (before after : State Holder Use (Capture (Answer := Answer) scanner Context))
    (checked : recheckSource scanner current key use ready before = some after) :
    after.sources = before.sources ∧ ∃ captured,
      readCurrent key use before = some captured ∧
      after.queue.cells key.owner = recheckCompleted current key.generation ready
        (before.queue.cells key.owner) (Cursor.ReadOnlyQuery.completed? scanner captured.computation.2) := by
  unfold recheckSource at checked
  obtain ⟨captured, acquired, equal⟩ := Option.map_eq_some_iff.mp checked
  cases equal
  have keyed := (readCurrent_requires_owned_use key use before captured acquired).1
  exact ⟨rfl, captured, acquired, by simp [recheckQueue, keyed]⟩

/-- A post-arm publication routes against the read certificate held by
this exact source registration. It neither accepts a substituted context nor
replays the query. Journal and queue updates preserve the acquired capture. -/
def routeSource {O T Answer Context : Type} [LinearOrder O]
    (label : O → T) (published : Commit O T) (scanner : (T → Bool) → List O)
    (key : AsyncWait.Identity) (serial : Nat) (use : Use) (inbox : EventPump.Inbox)
    (state : State Holder Use (Capture (Answer := Answer) scanner Context)) :
    Option (EventPump.Inbox × State Holder Use (Capture (Answer := Answer) scanner Context)) :=
  (readCurrent key use state).map fun captured =>
    let routed := routeCompleted label published key serial
      (Cursor.ReadOnlyQuery.completed? scanner captured.computation.2) inbox state.queue
    (routed.1, { state with queue := routed.2 })

theorem routeSource_retains_capture {O T Answer Context : Type} [LinearOrder O]
    (label : O → T) (published : Commit O T) (scanner : (T → Bool) → List O)
    (key : AsyncWait.Identity) (serial : Nat) (use : Use) (inbox afterInbox : EventPump.Inbox)
    (before after : State Holder Use (Capture (Answer := Answer) scanner Context))
    (routed : routeSource label published scanner key serial use inbox before = some (afterInbox, after)) :
    after.sources = before.sources ∧ ∃ captured,
      readCurrent key use before = some captured ∧
      (afterInbox, after.queue) = routeCompleted label published key serial
        (Cursor.ReadOnlyQuery.completed? scanner captured.computation.2) inbox before.queue := by
  unfold routeSource at routed
  obtain ⟨captured, acquired, equal⟩ := Option.map_eq_some_iff.mp routed
  cases equal
  exact ⟨rfl, captured, acquired, rfl⟩

/-- Construct a source capture directly from the ordinary source compiler
and its earned execution packet. Binding closures and paid reads are retained
by that packet, and the context is kept in the existing cursor owner. -/
def installSource {O V T P Context : Type} [DecidableEq O]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (scanner : (T → Bool) → List O)
    (source : Sources.SourceList V T P) (bindings : Sources.Subst V T) (context : Context)
    (holder : Holder) (fuel slot serial : Nat)
    (state : State Holder Use (Capture (Answer := List (Sources.Subst V T × List (Sources.Pick O T))) scanner Context)) :=
  install holder slot serial
    ({ computation := Sources.Query.Execution.execute L matcher label scanner [] source bindings fuel
       context := context } : Capture scanner Context) state

/-- The installed key and actual acquired use recover exactly the executed
source packet and its caller context. A copied question key is not a substitute
for this acquisition. The allocation count must permit the first use. -/
theorem installed_source_acquired_exactly [DecidableEq Holder] {O V T P Context : Type} [DecidableEq O]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P)
    (label : O → T) (scanner : (T → Bool) → List O)
    (source : Sources.SourceList V T P) (bindings : Sources.Subst V T) (context : Context)
    (holder : Holder) (fuel slot serial limit : Nat) (use : Use) (key : AsyncWait.Identity)
    (before installed : State Holder Use (Capture (Answer := List (Sources.Subst V T × List (Sources.Pick O T))) scanner Context))
    (opened : installSource L matcher label scanner source bindings context holder fuel slot serial before = some (key, installed))
    (room : 0 < limit) :
    ∃ owned, acquire limit .exclusive holder key use installed = some owned ∧
      readCurrent key use owned = some
        ⟨Sources.Query.Execution.execute L matcher label scanner [] source bindings fuel, context⟩ ∧
      owned.queue = installed.queue :=
  acquire_installed_source holder slot serial limit _ before installed key use opened room

/-! ### Reactive guard recipes after an earned producer prefix

A recipe retains the actual compiled guard and its post-prefix body. The
producer, pure guard attempts and prepared body have separate roles. Refresh
starts only the pure guard again; it never restarts the producer. Selection
returns a proposal, not permission to consume occurrences or publish effects.
-/

section ComputationTransitions

variable {Reply : Type}

/-- Advance the actual acquired payload under the current full registration
key. The generic acquired-use transition retains every reached state; queue
delivery and other owners are unchanged by this computation step. -/
def transitionCurrent (key : AsyncWait.Identity) (use : Use) (step : Resource → Reply × Resource)
    (state : State Holder Use Resource) : Option (Reply × State Holder Use Resource) :=
  if state.queue.keys key.owner = some key then
    (state.sources key).bind fun owner =>
      (AcquiredUse.transitionCurrent use step owner).map fun result =>
        (result.1, { state with sources := Function.update state.sources key (some result.2) })
  else none

theorem transitionCurrent_admitted (key : AsyncWait.Identity) (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply)
    (accepted : transitionCurrent key use step before = some (reply, after)) :
    before.queue.keys key.owner = some key ∧ ∃ owner next,
      before.sources key = some owner ∧ AcquiredUse.transitionCurrent use step owner = some (reply, next) ∧
      after = { before with sources := Function.update before.sources key (some next) } := by
  unfold transitionCurrent at accepted
  split at accepted
  · rename_i current
    obtain ⟨owner, held, rest⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨result, advanced, same⟩ := Option.map_eq_some_iff.mp rest
    cases same
    exact ⟨current, owner, result.2, held, advanced, rfl⟩
  · cases accepted

theorem transitionCurrent_capture (key : AsyncWait.Identity) (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply)
    (accepted : transitionCurrent key use step before = some (reply, after)) :
    ∃ resource, readCurrent key use before = some resource ∧
      readCurrent key use after = some (step resource).2 ∧ reply = (step resource).1 ∧
      after.queue = before.queue ∧
      ∀ other, other ≠ key → after.sources other = before.sources other := by
  obtain ⟨keyed, owner, next, held, advanced, rfl⟩ := transitionCurrent_admitted key use step before after reply accepted
  obtain ⟨current, allowed, resource, payload, answer, rfl⟩ :=
    AcquiredUse.transitionCurrent_admitted use step owner next reply advanced
  refine ⟨resource, ?_, ?_, answer, rfl, ?_⟩
  · simp [readCurrent, keyed, held, current, allowed, AcquiredUse.readUse, allowed.1, payload]
  · simp [readCurrent, keyed, current, AcquiredUse.mayMutate, allowed.1, allowed.2,
      AcquiredUse.readUse]
  · intro other different
    exact Function.update_of_ne different _ _

theorem transitionCurrent_owners_valid (key : AsyncWait.Identity) (use : Use) (step : Resource → Reply × Resource)
    (before after : State Holder Use Resource) (reply : Reply) (valid : OwnersValid before)
    (accepted : transitionCurrent key use step before = some (reply, after)) : OwnersValid after := by
  obtain ⟨_, owner, next, held, advanced, rfl⟩ := transitionCurrent_admitted key use step before after reply accepted
  exact update_sources_valid before before.queue key next valid
    (AcquiredUse.transitionCurrent_wellFormed use step owner next reply (valid key owner held) advanced)

theorem transitionCurrent_identity (key : AsyncWait.Identity) (use : Use) (reply : Reply)
    (before after : State Holder Use Resource)
    (accepted : transitionCurrent key use (fun resource => (reply, resource)) before = some (reply, after)) :
    after = before := by
  obtain ⟨_, owner, next, held, advanced, rfl⟩ := transitionCurrent_admitted key use _ before after reply accepted
  obtain ⟨_, _, resource, payload, _, same⟩ := AcquiredUse.transitionCurrent_admitted use _ owner next reply advanced
  have unchanged : next = owner := by
    rw [same, ← payload]
  rw [unchanged, ← held]
  simp only [Function.update_eq_self]

end ComputationTransitions

namespace Reactive

open _root_.CategoryTheory
open Mettapedia.GSLT.Contracts Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.GSLT.Logic.AbstractSeparationLogic
open Cursor.ReadOnlyQuery

abbrev Row (O V T : Type) := Sources.Subst V T × List (Sources.Pick O T)

structure Recipe (O V T P Entry Answer : Type) (size : Nat) where
  transform : Sources.Transform V T P
  bindings : Sources.Subst V T
  program : ReadOnlyQuery.Program (T → Bool) (List O) (List (Row O V T))
  body : Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer

variable {O V T P Entry World Environment Answer : Type} {size : Nat}
variable [Category.{0} World]

/-- Compile once from the actual produced environment. The body closes over
that same environment; future guard attempts reuse this immutable program. -/
def buildRecipe [DecidableEq O] (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (transform : Environment → Sources.Transform V T P)
    (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (environment : Environment) : Recipe O V T P Entry Answer size :=
  ⟨transform environment, bindings environment,
    Sources.Query.compile L matcher label (transform environment).template (transform environment).sources
      (bindings environment), body environment⟩

variable (authority : IndexedAuthority.{0, 0, 0} World)
  (required : OrderedDependencyStore.Action Entry size → (world : World) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry size),
    Decidable (FrameUpdate point.authority (required action point.world))]

abbrev Attempt (O V T : Type) :=
  (scanner : (T → Bool) → List O) × Sources.Query.Execution.Result O V T scanner

structure State where
  producer : OwnWrite.Saved authority required (Recipe O V T P Entry Answer size)
  attempt : Option (Attempt O V T)
  pastReads : Nat

/-- Attach the recipe constructor to the actual producer cut. Pending source
work, faults, already paid operations and captured service state are retained. -/
def capture (build : Environment → Recipe O V T P Entry Answer size)
    (previous : OwnWrite.Saved authority required Environment) : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required :=
  ⟨OwnWrite.ReturnMap.saved authority required build previous, none, 0⟩

def recipe? (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Option (Recipe O V T P Entry Answer size) :=
  match OwnWrite.completed authority required state.producer with
  | some (.ok recipe) => some recipe
  | some (.error _) | none => none

/-- Counts guard provider reads separately from the producer/body service
invoice. Matcher, compilation, validation and native overhead are not included. -/
def queryInvoice (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) : Nat :=
  state.pastReads + (state.attempt.map fun attempt => attempt.2.1).getD 0

variable (needed : (world : World) → authority.Fibre world)
  [admission : ∀ point : IndexedAuthority.Point authority,
    Decidable (FrameUpdate point.authority (needed point.world))]

/-- Continue the saved producer at the current service entrance. Once guard
work has started this operation is inert. A refused entrance returns the
whole previous driver and never restarts the producer. -/
def resumeProducer (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Except (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :=
  if state.attempt.isSome then .ok state else
    match OwnWrite.Invocation.resume authority required needed live point reader fuel state.producer with
    | .error _ => .error state
    | .ok next => .ok { state with producer := next }

/-- Start a fresh pure guard attempt from the retained recipe. Retired guard
read charges remain accounted. The effectful producer packet is unchanged. -/
def refresh (scanner : (T → Bool) → List O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Option (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :=
  (recipe? authority required state).map fun recipe =>
    { state with pastReads := queryInvoice authority required state
                 attempt := some ⟨scanner,
                   Cursor.advance (Cursor.ReadOnlyQuery.provider scanner) Cursor.ReadOnlyQuery.client
                     (Cursor.ReadOnlyQuery.readCharge scanner) 0 ⟨.unit, recipe.program, []⟩⟩ }

/-- Validate performed guard reads before resuming its actual continuation.
A refusal preserves the old view, packet and both accounts. Zero allowance
performs no validation or service and preserves the entire driver. -/
def resumeGuard [DecidableEq O] (current : (T → Bool) → List O) (fuel : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Except (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :=
  if fuel = 0 then .ok state else
    match state.attempt with
    | none => .error state
    | some ⟨before, packet⟩ =>
        match Cursor.ReadOnlyQuery.resumeValidated before current fuel packet with
        | .error _ => .error state
        | .ok next => .ok { state with attempt := some ⟨current, next⟩ }

inductive Observation (O V T : Type) where
  | producing
  | producerFault (fault : OwnWrite.Fault)
  | unstarted
  | checking
  | stale
  | complete (result : ReadOnlyQuery.Observation (T → Bool) (List O) (List (Row O V T)))

/-- Completion and current validation are distinct from an empty answer.
Faults and unfinished source work cannot masquerade as guard absence. -/
def observe [DecidableEq O] (current : (T → Bool) → List O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) : Observation O V T :=
  match OwnWrite.completed authority required state.producer with
  | none => .producing
  | some (.error fault) => .producerFault fault
  | some (.ok _) =>
      match state.attempt with
      | none => .unstarted
      | some ⟨before, packet⟩ =>
          match Cursor.ReadOnlyQuery.completed? before packet.2 with
          | none => .checking
          | some result =>
              if ReadOnlyQuery.checkReads current result.reads then .complete result else .stale

/-- Keep the selected list occurrence. Only a complete current observation
can yield a proposal; None alone does not establish guard absence. -/
def select [DecidableEq O] (current : (T → Bool) → List O) (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) : Option (Row O V T) :=
  match observe authority required current state with
  | .complete result => result.answer[index]?
  | _ => none

/-- Preparing code is not source-commit or effect authorization. The body is
selected from the actual earned recipe, and the existing closure entrance
uses current service data/authority rather than the capture-time point. -/
def prepareBody [DecidableEq O] (current : (T → Bool) → List O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Option (OwnWrite.Saved authority required Answer) :=
  (select authority required current index state).bind fun row =>
    OwnWrite.CapturedClosure.start authority required live point (index, row)
      (OwnWrite.ReturnMap.saved authority required
        (fun recipe : Recipe O V T P Entry Answer size => fun selected : Nat × Row O V T =>
          recipe.body selected.1 selected.2) state.producer)

/-- Provenance through a return map is an invariant of the actual producer
control, including unfinished cuts, not only of a completed return value. -/
def MappedBy (build : Environment → Recipe O V T P Entry Answer size)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) : Prop :=
  ∃ previous, state.producer = OwnWrite.ReturnMap.saved authority required build previous

/-- Each guard attempt originates in the recipe's actual stored program.
This operational invariant is later linked to independent source judgments. -/
def GuardOrigin (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) : Prop :=
  ∀ scanner packet, state.attempt = some ⟨scanner, packet⟩ →
    ∃ recipe fuel, recipe? authority required state = some recipe ∧
      packet = Cursor.advance (Cursor.ReadOnlyQuery.provider scanner) Cursor.ReadOnlyQuery.client
        (Cursor.ReadOnlyQuery.readCharge scanner) fuel ⟨.unit, recipe.program, []⟩

theorem capture_mapped (build : Environment → Recipe O V T P Entry Answer size)
    (previous : OwnWrite.Saved authority required Environment) :
    MappedBy authority required build (capture authority required build previous) := ⟨previous, rfl⟩

theorem capture_guard_origin (build : Environment → Recipe O V T P Entry Answer size)
    (previous : OwnWrite.Saved authority required Environment) :
    GuardOrigin authority required (capture authority required build previous) := by
  intro scanner packet impossible
  cases impossible

theorem resumeProducer_map (build : Environment → Recipe O V T P Entry Answer size)
    (previous : OwnWrite.Saved authority required Environment)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat) :
    resumeProducer authority required needed live point reader fuel (capture authority required build previous) =
      match OwnWrite.Invocation.resume authority required needed live point reader fuel previous with
      | .error _ => .error (capture authority required build previous)
      | .ok next => .ok (capture authority required build next) := by
  simp only [resumeProducer, capture, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  rw [OwnWrite.ReturnMap.invocation_map authority required needed build live point reader fuel previous]
  cases OwnWrite.Invocation.resume authority required needed live point reader fuel previous <;> rfl

theorem resumeProducer_after_guard_is_inert
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (started : state.attempt.isSome = true) :
    resumeProducer authority required needed live point reader fuel state = .ok state := by
  simp [resumeProducer, started]

theorem refresh_preserves_prefix_and_invoice (scanner : (T → Bool) → List O)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (refreshed : refresh authority required scanner before = some after) :
    after.producer = before.producer ∧
      queryInvoice authority required after = queryInvoice authority required before := by
  unfold refresh at refreshed
  obtain ⟨recipe, _, equal⟩ := Option.map_eq_some_iff.mp refreshed
  cases equal
  exact ⟨rfl, by simp [queryInvoice, Cursor.advance]⟩

theorem refresh_guard_origin (scanner : (T → Bool) → List O)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (refreshed : refresh authority required scanner before = some after) : GuardOrigin authority required after := by
  unfold refresh at refreshed
  obtain ⟨recipe, found, equal⟩ := Option.map_eq_some_iff.mp refreshed
  cases equal
  intro observed packet stored
  cases Option.some.inj stored
  exact ⟨recipe, 0, found, rfl⟩

theorem resumeGuard_zero [DecidableEq O] (current : (T → Bool) → List O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    resumeGuard authority required current 0 state = .ok state := rfl

/-- Preparation retains the actual selected occurrence and the body stored
in its earned recipe. The resulting packet has performed no body operation. -/
theorem prepareBody_source [DecidableEq O] (current : (T → Bool) → List O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority) (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (prepared : OwnWrite.Saved authority required Answer)
    (ready : prepareBody authority required current live point index state = some prepared) :
    ∃ recipe row, recipe? authority required state = some recipe ∧
      select authority required current index state = some row ∧
      prepared = (state.producer.1,
        .paused ⟨.unit, .ok (recipe.body index row), ⟨live, point⟩⟩) := by
  unfold prepareBody at ready
  obtain ⟨row, selected, entered⟩ := Option.bind_eq_some_iff.mp ready
  generalize source : state.producer = saved at entered ⊢
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => cases entered
  | done finished =>
      rcases finished with ⟨⟨⟩, value, captured⟩
      cases value with
      | error fault => cases entered
      | ok recipe =>
          cases Option.some.inj entered
          exact ⟨recipe, row, by simp [recipe?, source, OwnWrite.completed], selected, rfl⟩

theorem prepareBody_current_entrance [DecidableEq O] (current : (T → Bool) → List O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority) (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (prepared : OwnWrite.Saved authority required Answer)
    (ready : prepareBody authority required current live point index state = some prepared) :
    prepared.1 = state.producer.1 ∧ (OwnWrite.current authority required prepared).store = live ∧
      (OwnWrite.current authority required prepared).point = point := by
  obtain ⟨recipe, row, _, _, preparedEq⟩ := prepareBody_source authority required current live point index state prepared ready
  rw [preparedEq]
  exact ⟨rfl, rfl, rfl⟩

/-- Resuming a mapped producer follows the actual unmapped producer and
maps its actual return, even at a newly supplied service entrance. -/
theorem resumeProducer_mapped (build : Environment → Recipe O V T P Entry Answer size)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (mapped : MappedBy authority required build before)
    (resumed : resumeProducer authority required needed live point reader fuel before = .ok after) :
    MappedBy authority required build after := by
  obtain ⟨previous, source⟩ := mapped
  unfold resumeProducer at resumed
  split at resumed
  · cases Except.ok.inj resumed
    exact ⟨previous, source⟩
  · rw [source, OwnWrite.ReturnMap.invocation_map authority required needed build live point reader fuel previous] at resumed
    cases result : OwnWrite.Invocation.resume authority required needed live point reader fuel previous with
    | error refused => simp [result] at resumed
    | ok next =>
        simp only [result, Except.ok.injEq] at resumed
        cases resumed
        exact ⟨next, rfl⟩

theorem resumeProducer_refused
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (fuel : Nat)
    (before refused : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (stopped : resumeProducer authority required needed live point reader fuel before = .error refused) :
    refused = before := by
  unfold resumeProducer at stopped
  split at stopped
  · cases stopped
  · cases result : OwnWrite.Invocation.resume authority required needed live point reader fuel before.producer <;>
      simp_all

theorem resumeGuard_retains_prefix [DecidableEq O] (current : (T → Bool) → List O) (fuel : Nat)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (resumed : resumeGuard authority required current fuel before = .ok after) :
    after.producer = before.producer ∧ after.pastReads = before.pastReads := by
  unfold resumeGuard at resumed
  split at resumed
  · cases Except.ok.inj resumed; exact ⟨rfl, rfl⟩
  · cases attempt : before.attempt with
    | none => simp [attempt] at resumed
    | some packet =>
        rcases packet with ⟨view, saved⟩
        simp only [attempt] at resumed
        cases ran : Cursor.ReadOnlyQuery.resumeValidated view current fuel saved with
        | error refused => simp [ran] at resumed
        | ok next =>
            simp only [ran, Except.ok.injEq] at resumed
            cases resumed
            exact ⟨rfl, rfl⟩

theorem resumeGuard_refused [DecidableEq O] (current : (T → Bool) → List O) (fuel : Nat)
    (before refused : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (stopped : resumeGuard authority required current fuel before = .error refused) : refused = before := by
  unfold resumeGuard at stopped
  split at stopped
  · cases stopped
  · cases attempt : before.attempt with
    | none => simpa only [attempt, Except.error.injEq] using stopped.symm
    | some packet =>
        rcases packet with ⟨view, saved⟩
        simp only [attempt] at stopped
        cases ran : Cursor.ReadOnlyQuery.resumeValidated view current fuel saved <;> simp_all

theorem resumeGuard_origin [DecidableEq O] (current : (T → Bool) → List O) (fuel : Nat)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required before)
    (resumed : resumeGuard authority required current fuel before = .ok after) : GuardOrigin authority required after := by
  unfold resumeGuard at resumed
  split at resumed
  · cases Except.ok.inj resumed; exact origin
  · cases attempt : before.attempt with
    | none => simp [attempt] at resumed
    | some packet =>
        rcases packet with ⟨view, saved⟩
        obtain ⟨recipe, earlier, recipeFound, execution⟩ := origin view saved attempt
        simp only [attempt] at resumed
        cases ran : Cursor.ReadOnlyQuery.resumeValidated view current fuel saved with
        | error refused => simp [ran] at resumed
        | ok next =>
            simp only [ran, Except.ok.injEq] at resumed
            cases resumed
            intro observed stored accepted
            cases Option.some.inj accepted
            have valid : ReadOnlyQuery.checkReads current (Cursor.ReadOnlyQuery.recorded view saved.2) = true := by
              by_contra invalid
              simp [Cursor.ReadOnlyQuery.resumeValidated, invalid] at ran
            have exactResume := Cursor.ReadOnlyQuery.resumeValidated_exact view current earlier fuel recipe.program []
              (by simpa only [execution] using valid)
            rw [execution, exactResume] at ran
            exact ⟨recipe, earlier + fuel, recipeFound, (Except.ok.inj ran).symm⟩

/-- A complete observation exposes its actual completed packet and checked
reads. In particular, neither an unfinished nor a stale packet can supply it. -/
theorem observe_complete [DecidableEq O] (current : (T → Bool) → List O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O) (List (Row O V T)))
    (observed : observe authority required current state = .complete observation) :
    ∃ recipe view packet, recipe? authority required state = some recipe ∧
      state.attempt = some ⟨view, packet⟩ ∧
      Cursor.ReadOnlyQuery.completed? view packet.2 = some observation ∧
      ReadOnlyQuery.checkReads current observation.reads = true := by
  unfold observe at observed
  cases produced : OwnWrite.completed authority required state.producer with
  | none => simp [produced] at observed
  | some value =>
      cases value with
      | error fault => simp [produced] at observed
      | ok recipe =>
          simp only [produced] at observed
          cases attempt : state.attempt with
          | none => simp [attempt] at observed
          | some packet =>
              rcases packet with ⟨view, saved⟩
              simp only [attempt] at observed
              cases finished : Cursor.ReadOnlyQuery.completed? view saved.2 with
              | none => simp [finished] at observed
              | some result =>
                  simp only [finished] at observed
                  split at observed
                  · rename_i valid
                    cases observed
                    exact ⟨recipe, view, saved, by simp [recipe?, produced], rfl, finished, valid⟩
                  · cases observed

/-- Selected proposal positions are those of the independent fresh query
interpreter, with the original recipe and its ordered answer multiplicity. -/
theorem select_origin [DecidableEq O] (current : (T → Bool) → List O) (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required state) (row : Row O V T)
    (selected : select authority required current index state = some row) :
    ∃ recipe, recipe? authority required state = some recipe ∧
      (ReadOnlyQuery.run current recipe.program).answer[index]? = some row := by
  unfold select at selected
  cases observed : observe authority required current state <;> simp only [observed] at selected
  all_goals try cases selected
  rename_i observation
  obtain ⟨_, view, packet, _, stored, finished, valid⟩ := observe_complete authority required current state observation observed
  obtain ⟨recipe, fuel, found, execution⟩ := origin view packet stored
  have same := Cursor.ReadOnlyQuery.validated_completion view current fuel recipe.program observation
    (by simpa only [execution] using finished) valid
  exact ⟨recipe, found, by rw [same]; exact selected⟩

/-- The source compiler, not a footprint or row supplied by the caller,
constructs the executable program in each canonical recipe. -/
def Compiled [DecidableEq O] (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (recipe : Recipe O V T P Entry Answer size) : Prop :=
  recipe.program = Sources.Query.compile L matcher label recipe.transform.template recipe.transform.sources recipe.bindings

theorem buildRecipe_compiled [DecidableEq O]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (transform : Environment → Sources.Transform V T P) (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (environment : Environment) : Compiled L matcher label (buildRecipe L matcher label transform bindings body environment) := rfl

theorem mapped_recipe_value (build : Environment → Recipe O V T P Entry Answer size)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (mapped : MappedBy authority required build state)
    (recipe : Recipe O V T P Entry Answer size) (found : recipe? authority required state = some recipe) :
    ∃ environment, build environment = recipe := by
  obtain ⟨previous, source⟩ := mapped
  unfold recipe? at found
  rw [source, OwnWrite.ReturnMap.completed_map] at found
  cases produced : OwnWrite.completed authority required previous with
  | none => simp [produced] at found
  | some value =>
      cases value with
      | error fault => simp [produced, Except.map] at found
      | ok environment =>
          exact ⟨environment, by simpa only [produced, Option.map_some, Except.map, Option.some.injEq] using found⟩

theorem mapped_recipe_compiled [DecidableEq O]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (transform : Environment → Sources.Transform V T P) (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (mapped : MappedBy authority required (buildRecipe L matcher label transform bindings body) state)
    (recipe : Recipe O V T P Entry Answer size) (found : recipe? authority required state = some recipe) :
    Compiled L matcher label recipe := by
  obtain ⟨environment, rfl⟩ := mapped_recipe_value authority required _ state mapped recipe found
  exact buildRecipe_compiled L matcher label transform bindings body environment

/-- The selected proposal satisfies the independent declarative source
judgment in the validated view. Linear/fresh/commit admission is separate. -/
theorem selected_declarative_row [DecidableEq O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (store : Finset O) (current : (T → Bool) → List O) (scanned : Sources.Query.Complete label store current)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher) (index : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required state)
    (compiled : ∀ recipe, recipe? authority required state = some recipe → Compiled L matcher label recipe)
    (respects : ∀ recipe, recipe? authority required state = some recipe →
      ∀ eval ∈ recipe.transform.sources.lets, Sources.Respects L eval)
    (row : Row O V T) (selected : select authority required current index state = some row) :
    ∃ recipe, recipe? authority required state = some recipe ∧
      Sources.DRow L label store recipe.transform.template recipe.transform.sources recipe.bindings row := by
  obtain ⟨recipe, found, atIndex⟩ := select_origin authority required current index state origin row selected
  have member := List.mem_of_getElem? atIndex
  rw [compiled recipe found] at member
  have rows := Sources.Query.run_compile L matcher label store current scanned
    recipe.transform.template recipe.transform.sources recipe.bindings
  have listed : row ∈ Sources.rows L matcher label store recipe.transform.template recipe.transform.sources recipe.bindings := by
    rw [← rows]
    exact member
  exact ⟨recipe, found, (Sources.agreement (label := label) (S := store) (template := recipe.transform.template)
    sound complete minimal recipe.transform.sources (respects recipe found) recipe.bindings).1 row listed⟩

/-- Canonical recipes completed from a real producer cut retain its actual
environment, transform, initial bindings, compiled guard and body. -/
theorem captured_recipe_source [DecidableEq O]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (transform : Environment → Sources.Transform V T P) (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (producer : Prog (OwnWrite.Request Entry size) OwnWrite.Reply Environment)
    (initial after : OwnWrite.State authority Entry size) (first later paid : Nat)
    (recipe : Recipe O V T P Entry Answer size)
    (finished : Cursor.resume (OwnWrite.provider authority required) (OwnWrite.client _) (fun _ _ => 1) later
      (capture authority required (buildRecipe L matcher label transform bindings body)
        (OwnWrite.advance authority required first producer initial)).producer =
      (paid, .done ⟨.unit, .ok recipe, after⟩)) :
    ∃ environment, producer.Runs (OwnWrite.action authority required) initial environment after ∧
      recipe = buildRecipe L matcher label transform bindings body environment := by
  obtain ⟨environment, produced, same⟩ := OwnWrite.ReturnMap.producer_source authority required
    (buildRecipe L matcher label transform bindings body) producer initial after first later paid recipe finished
  exact ⟨environment, produced, same.symm⟩

/-- A genuinely complete empty guard is absence in the independent source
relation. Unstarted, partial and stale observations cannot prove this result. -/
theorem observed_empty_declarative [DecidableEq O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (store : Finset O) (current : (T → Bool) → List O) (scanned : Sources.Query.Complete label store current)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required state)
    (compiled : ∀ recipe, recipe? authority required state = some recipe → Compiled L matcher label recipe)
    (respects : ∀ recipe, recipe? authority required state = some recipe →
      ∀ eval ∈ recipe.transform.sources.lets, Sources.Respects L eval)
    (observation : ReadOnlyQuery.Observation (T → Bool) (List O) (List (Row O V T)))
    (observed : observe authority required current state = .complete observation)
    (empty : observation.answer = []) :
    ∃ recipe, recipe? authority required state = some recipe ∧
      ¬ ∃ row, Sources.DRow L label store recipe.transform.template recipe.transform.sources recipe.bindings row := by
  obtain ⟨_, view, packet, _, stored, finished, valid⟩ := observe_complete authority required current state observation observed
  obtain ⟨recipe, fuel, found, execution⟩ := origin view packet stored
  have same := Cursor.ReadOnlyQuery.validated_completion view current fuel recipe.program observation
    (by simpa only [execution] using finished) valid
  refine ⟨recipe, found, ?_⟩
  have agreement := Sources.agreement (label := label) (S := store) (template := recipe.transform.template)
    sound complete minimal recipe.transform.sources (respects recipe found) recipe.bindings
  rintro ⟨candidate, derivable⟩
  obtain ⟨representative, listed, _⟩ := agreement.2.1 recipe.bindings
      (Sources.SubstEquiv.refl L.equivalence recipe.bindings) candidate derivable
  have rows := Sources.Query.run_compile L matcher label store current scanned
      recipe.transform.template recipe.transform.sources recipe.bindings
  rw [← rows, ← compiled recipe found, same, empty] at listed
  cases listed

/-- Successful invocation of a prepared body reflects its independent
primitive meaning in the current entrance world. This does not establish a
source-transform commit or permit replaying a prepared activation twice. -/
theorem prepared_body_completed [DecidableEq O]
    (current : (T → Bool) → List O) (live : OrderedDependencyStore.Store Entry size)
    (point : IndexedAuthority.Point authority) (reader : Fin size) (index fuel paid : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (prepared : OwnWrite.Saved authority required Answer) (answer : Answer)
    (after : OwnWrite.State authority Entry size)
    (ready : prepareBody authority required current live point index state = some prepared)
    (finished : OwnWrite.Invocation.resume authority required needed live point reader fuel prepared =
      .ok (paid, .done ⟨.unit, .ok answer, after⟩)) :
    ∃ recipe row, recipe? authority required state = some recipe ∧
      select authority required current index state = some row ∧
      (recipe.body index row).Runs (OwnWrite.action authority required) ⟨live, point⟩ answer after := by
  obtain ⟨recipe, row, found, selected, preparedEq⟩ := prepareBody_source authority required current live point index state prepared ready
  rw [preparedEq] at finished
  refine ⟨recipe, row, found, selected, ?_⟩
  cases fuel with
  | zero => cases finished
  | succ fuel =>
      generalize code : recipe.body index row = program at finished ⊢
      cases program with
      | ret value =>
          apply OwnWrite.slice_ok_runs authority required (fuel + 1) state.producer.1 paid
            (.ret value) ⟨live, point⟩ after answer
          exact Except.ok.inj finished
      | call request next =>
          by_cases allowed : FrameUpdate point.authority (needed point.world)
          · have entered := OwnWrite.Invocation.at_reached_state authority required needed reader (fuel + 1)
              (state.producer.1, .paused ⟨.unit, .ok (.call request next), (⟨live, point⟩ : OwnWrite.State authority Entry size)⟩) allowed
            simp only [OwnWrite.current, Cursor.PrimitiveProgram.readOutcome] at entered
            rw [entered] at finished
            exact OwnWrite.slice_ok_runs authority required (fuel + 1) state.producer.1 paid
              (.call request next) ⟨live, point⟩ after answer (Except.ok.inj finished)
          · simp [OwnWrite.Invocation.resume, allowed] at finished

/-- The raw completion is read from this recipe-bearing attempt. The shared
registration recheck supplies its one fresh validation pass. -/
def completion (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Option (ReadOnlyQuery.Observation (T → Bool) (List O) (List (Row O V T))) :=
  (recipe? authority required state).bind fun _ =>
    state.attempt.bind fun ⟨view, packet⟩ => Cursor.ReadOnlyQuery.completed? view packet.2

/-- Recheck the actual exclusively acquired driver in its installed question.
An absent completion does not arm the waiter. Producer faults are exposed by
observe and remain distinct from a complete empty guard. -/
def recheckOwned [DecidableEq O] (current : (T → Bool) → List O)
    (key : AsyncWait.Identity) (use : Use)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :
    Option (Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :=
  (readCurrent key use pool).map fun driver =>
    { pool with queue := (recheckQueue current key (fun rows => !rows.isEmpty)
        (completion authority required driver) pool.queue) }

def routeOwned [LinearOrder O] (label : O → T) (published : Commit O T)
    (key : AsyncWait.Identity) (serial : Nat) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :
    Option (EventPump.Inbox × Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :=
  (readCurrent key use pool).map fun driver =>
    let routed := routeCompleted label published key serial (completion authority required driver) inbox pool.queue
    (routed.1, { pool with queue := routed.2 })

def prepareOwned [DecidableEq O] (current : (T → Bool) → List O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (index : Nat) (key : AsyncWait.Identity) (use : Use)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :
    Option (OwnWrite.Saved authority required Answer) :=
  (readCurrent key use pool).bind (prepareBody authority required current live point index)

theorem recheckOwned_retains_recipe [DecidableEq O] (current : (T → Bool) → List O)
    (key : AsyncWait.Identity) (use : Use)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (checked : recheckOwned authority required current key use before = some after) :
    after.sources = before.sources ∧ ∃ driver, readCurrent key use before = some driver ∧
      after.queue = recheckQueue current key (fun rows => !rows.isEmpty)
        (completion authority required driver) before.queue := by
  unfold recheckOwned at checked
  obtain ⟨driver, held, equal⟩ := Option.map_eq_some_iff.mp checked
  cases equal
  exact ⟨rfl, driver, held, rfl⟩

theorem routeOwned_retains_recipe [LinearOrder O] (label : O → T) (published : Commit O T)
    (key : AsyncWait.Identity) (serial : Nat) (use : Use) (inbox afterInbox : EventPump.Inbox)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (routed : routeOwned authority required label published key serial use inbox before = some (afterInbox, after)) :
    after.sources = before.sources ∧ ∃ driver, readCurrent key use before = some driver ∧
      (afterInbox, after.queue) = routeCompleted label published key serial
        (completion authority required driver) inbox before.queue := by
  unfold routeOwned at routed
  obtain ⟨driver, held, equal⟩ := Option.map_eq_some_iff.mp routed
  cases equal
  exact ⟨rfl, driver, held, rfl⟩

theorem prepareOwned_current_entrance [DecidableEq O] (current : (T → Bool) → List O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (index : Nat) (key : AsyncWait.Identity) (use : Use)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (prepared : OwnWrite.Saved authority required Answer)
    (accepted : prepareOwned authority required current live point index key use pool = some prepared) :
    ∃ driver, readCurrent key use pool = some driver ∧ prepared.1 = driver.producer.1 ∧
      (OwnWrite.current authority required prepared).store = live ∧
      (OwnWrite.current authority required prepared).point = point := by
  unfold prepareOwned at accepted
  obtain ⟨driver, held, preparedFrom⟩ := Option.bind_eq_some_iff.mp accepted
  exact ⟨driver, held, prepareBody_current_entrance authority required current live point index driver prepared preparedFrom⟩

theorem refresh_mapped (build : Environment → Recipe O V T P Entry Answer size)
    (scanner : (T → Bool) → List O)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (mapped : MappedBy authority required build before)
    (refreshed : refresh authority required scanner before = some after) : MappedBy authority required build after := by
  obtain ⟨previous, original⟩ := mapped
  exact ⟨previous, (refresh_preserves_prefix_and_invoice authority required scanner before after refreshed).1.trans original⟩

theorem resumeGuard_mapped [DecidableEq O] (build : Environment → Recipe O V T P Entry Answer size)
    (current : (T → Bool) → List O) (fuel : Nat)
    (before after : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (mapped : MappedBy authority required build before)
    (resumed : resumeGuard authority required current fuel before = .ok after) : MappedBy authority required build after := by
  obtain ⟨previous, original⟩ := mapped
  exact ⟨previous, (resumeGuard_retains_prefix authority required current fuel before after resumed).1.trans original⟩

/-- Reading an earned recipe identifies its actual completed producer packet;
there is no recipe projected from a pending or failed producer. -/
theorem recipe_some_packet
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (recipe : Recipe O V T P Entry Answer size) (found : recipe? authority required state = some recipe) :
    ∃ paid captured, state.producer = (paid, .done ⟨.unit, .ok recipe, captured⟩) := by
  unfold recipe? at found
  generalize packet : state.producer = saved at found ⊢
  rcases saved with ⟨paid, outcome⟩
  cases outcome with
  | paused packet => simp [OwnWrite.completed] at found
  | done result =>
      rcases result with ⟨⟨⟩, value, captured⟩
      cases value with
      | error fault => simp [OwnWrite.completed] at found
      | ok actual =>
          have same : actual = recipe := by simpa [OwnWrite.completed] using found
          subst actual
          exact ⟨paid, captured, rfl⟩

/-- Join the actual producer execution, current declarative guard row and
current body execution through one retained environment. This is component
correspondence, not a transform-firing theorem: source commit admission and
its concurrent publication protocol remain separate obligations. -/
theorem producer_guard_body_components [DecidableEq O] [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (transform : Environment → Sources.Transform V T P) (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (producer : Prog (OwnWrite.Request Entry size) OwnWrite.Reply Environment)
    (initial : OwnWrite.State authority Entry size) (first later : Nat)
    (store : Finset O) (current : (T → Bool) → List O) (scanned : Sources.Query.Complete label store current)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher)
    (respects : ∀ environment, ∀ eval ∈ (transform environment).sources.lets, Sources.Respects L eval)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (reader : Fin size) (index fuel paid : Nat)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (retained : state.producer = Cursor.resume (OwnWrite.provider authority required) (OwnWrite.client _)
      (fun _ _ => 1) later
      (OwnWrite.ReturnMap.saved authority required (buildRecipe L matcher label transform bindings body)
        (OwnWrite.advance authority required first producer initial)))
    (origin : GuardOrigin authority required state)
    (prepared : OwnWrite.Saved authority required Answer) (answer : Answer)
    (after : OwnWrite.State authority Entry size)
    (ready : prepareBody authority required current live point index state = some prepared)
    (finished : OwnWrite.Invocation.resume authority required needed live point reader fuel prepared =
      .ok (paid, .done ⟨.unit, .ok answer, after⟩)) :
    ∃ environment captured row,
      producer.Runs (OwnWrite.action authority required) initial environment captured ∧
      Sources.DRow L label store (transform environment).template (transform environment).sources
        (bindings environment) row ∧
      (body environment index row).Runs (OwnWrite.action authority required) ⟨live, point⟩ answer after := by
  obtain ⟨recipe, row, found, selected, ran⟩ := prepared_body_completed authority required needed current live point
    reader index fuel paid state prepared answer after ready finished
  obtain ⟨prefixPaid, captured, packet⟩ := recipe_some_packet authority required state recipe found
  obtain ⟨environment, produced, built⟩ := OwnWrite.ReturnMap.producer_source authority required
    (buildRecipe L matcher label transform bindings body) producer initial captured first later prefixPaid recipe
    (retained.symm.trans packet)
  obtain ⟨selectedRecipe, selectedFound, atIndex⟩ := select_origin authority required current index state origin row selected
  have same : selectedRecipe = recipe := Option.some.inj (selectedFound.symm.trans found)
  subst selectedRecipe
  rw [← built] at atIndex ran
  have listed := List.mem_of_getElem? atIndex
  change row ∈ (ReadOnlyQuery.run current
    (Sources.Query.compile L matcher label (transform environment).template (transform environment).sources
      (bindings environment))).answer at listed
  have rows := Sources.Query.run_compile L matcher label store current scanned
    (transform environment).template (transform environment).sources (bindings environment)
  have member : row ∈ Sources.rows L matcher label store (transform environment).template
      (transform environment).sources (bindings environment) := by
    rw [← rows]
    exact listed
  exact ⟨environment, captured, row, produced,
    (Sources.agreement (label := label) (S := store) (template := (transform environment).template)
      sound complete minimal (transform environment).sources (respects environment) (bindings environment)).1 row member,
    ran⟩

namespace Controls

open Sources.AbsenceControls Sources.Commutative

local notation "writeRequirement" => Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls.requirement
local notation "entryRequirement" => Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.InvocationControls.needed
local notation "currentPoint" => Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls.held
local notation "revokedPoint" => Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls.revoked

local instance permissionDecision (point : IndexedAuthority.Point revocationWorlds)
    (change : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate point.authority (writeRequirement change point.world)) :=
  Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.Controls.permissionDecision point change
local instance admissionDecision (point : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate point.authority (entryRequirement point.world)) :=
  Mettapedia.Machines.Cursor.ReadOnlyQuery.OwnWrite.InvocationControls.admissionDecision point

local instance : DecidableEq (Except OwnWrite.Fault Nat)
  | .error .denied, .error .denied => isTrue rfl
  | .error _, .ok _ => isFalse (fun same => nomatch same)
  | .ok _, .error _ => isFalse (fun same => nomatch same)
  | .ok first, .ok second =>
      if same : first = second then isTrue (congrArg Except.ok same)
      else isFalse (fun equal => same (Except.ok.inj equal))

abbrev Driver := State (O := Nat) (V := Nat) (T := Value) (P := Pattern) (Answer := Nat)
  revocationWorlds writeRequirement

def label : Nat → Value
  | 0 => message .b
  | _ => message .a

def beforeView := SourceReads.scan label {0}
def afterView := SourceReads.scan label {0, 1}
def duplicateView := SourceReads.scan label {0, 1, 2}

/-- The finite ordered provider is exactly the sorted-space reference. This
rewrite lets kernel controls compute without reducing merge-sort's proof recursion. -/
theorem duplicateView_eq : duplicateView = Sources.Query.scanList label [0, 1, 2] := by
  funext region
  have sameSet : regionOf label {0, 1, 2} region =
      (Sources.Query.scanList label [0, 1, 2] region).toFinset := by
    ext occurrence
    simp [regionOf, Sources.Query.scanList]
  have unique : (Sources.Query.scanList label [0, 1, 2] region).Nodup :=
    (show ([0, 1, 2] : List Nat).Nodup by decide).filter _
  have sorted : (Sources.Query.scanList label [0, 1, 2] region).Pairwise (· ≤ ·) :=
    (show ([0, 1, 2] : List Nat).Pairwise (· ≤ ·) by decide).filter _
  unfold duplicateView SourceReads.scan
  rw [sameSet]
  exact (List.toFinset_sort (r := (· ≤ ·)) unique).mpr sorted

def transform (_ : Nat) : Sources.Transform Nat Value Pattern :=
  ⟨.cons (.read messagePattern) .done, []⟩
def bindings (environment : Nat) : Sources.Subst Nat Value := fun variableId =>
  if variableId = 0 then some (.leaf (if environment = 42 then .a else .b)) else none

def body (environment index : Nat) (_row : Row Nat Nat Value) :
    Prog (OwnWrite.Request Nat 3) OwnWrite.Reply Nat :=
  .call (.write (.append 2 [environment + index])) fun _ => .ret (environment + index)

def build := buildRecipe layer matcher label transform bindings body

def producer : Prog (OwnWrite.Request Nat 3) OwnWrite.Reply Nat :=
  .call (.write (.append 0 [7])) fun _ =>
    .call (.read 1) fun observed => .ret (observed.2.headD 0)
def initial : OwnWrite.State revocationWorlds Nat 3 :=
  ⟨OrderedDependencyStore.initial 71 (fun reader => if reader = 1 then [42] else []), currentPoint⟩
def producerCut := OwnWrite.advance revocationWorlds writeRequirement 1 producer initial
def captured : Driver := capture revocationWorlds writeRequirement build producerCut

def delivered {A : Type} : Except A A → A
  | .error previous => previous
  | .ok next => next

def isRefusal {A : Type} : Except A A → Bool
  | .error _ => true
  | .ok _ => false

def completed : Driver := delivered (resumeProducer revocationWorlds writeRequirement entryRequirement
  (OwnWrite.current revocationWorlds writeRequirement producerCut).store currentPoint 0 2 captured)
def started : Driver := (refresh revocationWorlds writeRequirement beforeView completed).getD completed
def halfway : Driver := delivered (resumeGuard revocationWorlds writeRequirement beforeView 1 started)
def emptyGuard : Driver := delivered (resumeGuard revocationWorlds writeRequirement beforeView 1 halfway)
def refreshed : Driver := (refresh revocationWorlds writeRequirement afterView emptyGuard).getD emptyGuard
def ready : Driver := delivered (resumeGuard revocationWorlds writeRequirement afterView 2 refreshed)

def answerCount (scanner : (Value → Bool) → List Nat) (state : Driver) : Option Nat :=
  match observe revocationWorlds writeRequirement scanner state with
  | .complete result => some result.answer.length
  | _ => none

def isChecking (scanner : (Value → Bool) → List Nat) (state : Driver) : Bool :=
  match observe revocationWorlds writeRequirement scanner state with | .checking => true | _ => false

def isStale (scanner : (Value → Bool) → List Nat) (state : Driver) : Bool :=
  match observe revocationWorlds writeRequirement scanner state with | .stale => true | _ => false

def live := OrderedDependencyStore.replaceOwn
  (OwnWrite.current revocationWorlds writeRequirement completed.producer).store 1 [99]
def prepared := prepareBody revocationWorlds writeRequirement afterView live currentPoint 0 ready
def invoked := prepared.map fun packet => OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live currentPoint 0 2 packet

def resultView (result : Option (Except (OwnWrite.Saved revocationWorlds writeRequirement Nat)
    (OwnWrite.Saved revocationWorlds writeRequirement Nat))) : Option (Nat × List Nat × List Nat × List Nat × Option (Except OwnWrite.Fault Nat)) :=
  result.map fun outcome =>
    let saved := delivered outcome
    let current := OwnWrite.current revocationWorlds writeRequirement saved
    (saved.1, OrderedDependencyStore.query current.store 0, OrderedDependencyStore.query current.store 1,
      OrderedDependencyStore.query current.store 2, OwnWrite.completed revocationWorlds writeRequirement saved)

theorem unfinished_producer_cannot_start_guard :
    (recipe? revocationWorlds writeRequirement captured).isNone = true ∧
      (refresh revocationWorlds writeRequirement beforeView captured).isNone = true ∧
      captured.producer.1 = 1 ∧
      OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement captured.producer).store 0 = [7] := by decide +kernel

theorem producer_finishes_saved_suffix_once :
    (recipe? revocationWorlds writeRequirement completed).isSome = true ∧ completed.producer.1 = 2 ∧
      OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement completed.producer).store 0 = [7] := by decide +kernel

theorem partial_guard_is_not_absence :
    isChecking beforeView halfway = true ∧ answerCount beforeView halfway = none ∧
      select revocationWorlds writeRequirement beforeView 0 halfway = none ∧
      queryInvoice revocationWorlds writeRequirement halfway = 1 ∧ answerCount beforeView emptyGuard = some 0 := by decide +kernel

theorem zero_guard_allowance_preserves_stale_saved_view :
    isRefusal (resumeGuard revocationWorlds writeRequirement afterView 0 emptyGuard) = false ∧
      answerCount beforeView (delivered (resumeGuard revocationWorlds writeRequirement afterView 0 emptyGuard)) = some 0 ∧
      queryInvoice revocationWorlds writeRequirement (delivered (resumeGuard revocationWorlds writeRequirement afterView 0 emptyGuard)) = 1 := by decide +kernel

theorem stale_negative_requires_fresh_attempt :
    isStale afterView emptyGuard = true ∧
      isRefusal (resumeGuard revocationWorlds writeRequirement afterView 2 emptyGuard) = true ∧
      (prepareBody revocationWorlds writeRequirement afterView live currentPoint 0 emptyGuard).isNone = true ∧
      answerCount afterView ready = some 1 := by decide +kernel

theorem refresh_preserves_earned_prefix_and_read_accounts :
    refreshed.producer.1 = 2 ∧ queryInvoice revocationWorlds writeRequirement refreshed = 1 ∧
      queryInvoice revocationWorlds writeRequirement ready = 2 ∧
      OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement ready.producer).store 0 = [7] := by decide +kernel

theorem preparation_uses_current_world_and_captured_environment :
    prepared.isSome = true ∧
      prepared.map (fun packet => OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement packet).store 1) = some [99] ∧
      resultView invoked = some (3, [7], [99], [42], some (.ok 42)) := by decide +kernel

theorem stale_selection_and_out_of_range_are_not_proposals :
    (prepareBody revocationWorlds writeRequirement beforeView live currentPoint 0 ready).isNone = true ∧
      (prepareBody revocationWorlds writeRequirement afterView live currentPoint 1 ready).isNone = true ∧
      answerCount afterView ready = some 1 := by decide +kernel

theorem revoked_invocation_keeps_prepared_body :
    let planned := prepareBody revocationWorlds writeRequirement afterView live revokedPoint 0 ready
    planned.isSome = true ∧
      (planned.map (fun packet => (OwnWrite.current revocationWorlds writeRequirement packet).point.authority)) = some .none ∧
      (planned.map (fun packet => isRefusal (OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live revokedPoint 0 2 packet))) = some true ∧
      resultView (planned.map fun packet => OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live revokedPoint 0 2 packet) =
        some (2, [7], [99], [], none) := by decide +kernel

theorem fresh_grant_resumes_refused_body_without_replaying_prefix :
    let planned := prepareBody revocationWorlds writeRequirement afterView live revokedPoint 0 ready
    let refused := planned.map fun packet => delivered (OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live revokedPoint 0 2 packet)
    resultView (refused.map fun packet => OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live currentPoint 0 2 packet) =
      some (3, [7], [99], [42], some (.ok 42)) := by decide +kernel

theorem naive_restart_repeats_prefix_and_changes_environment :
    let restarted := OwnWrite.advance revocationWorlds writeRequirement 3 producer (⟨live, currentPoint⟩ : OwnWrite.State revocationWorlds Nat 3)
    OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement restarted).store 0 = [7, 7] ∧
      OwnWrite.completed revocationWorlds writeRequirement restarted = some (.ok 99) ∧
      resultView invoked = some (3, [7], [99], [42], some (.ok 42)) := by decide +kernel

theorem duplicate_occurrences_keep_separate_body_positions :
    let fresh := (refresh revocationWorlds writeRequirement duplicateView emptyGuard).getD emptyGuard
    let twice := delivered (resumeGuard revocationWorlds writeRequirement duplicateView 2 fresh)
    let first := prepareBody revocationWorlds writeRequirement duplicateView live currentPoint 0 twice
    let second := prepareBody revocationWorlds writeRequirement duplicateView live currentPoint 1 twice
    answerCount duplicateView twice = some 2 ∧
      (select revocationWorlds writeRequirement duplicateView 0 twice).map
        (fun row => row.2.filterMap (fun pick => match pick with | .keep occurrence => some occurrence | _ => none)) = some [1] ∧
      (select revocationWorlds writeRequirement duplicateView 1 twice).map
        (fun row => row.2.filterMap (fun pick => match pick with | .keep occurrence => some occurrence | _ => none)) = some [2] ∧
      resultView (first.map fun packet => OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live currentPoint 0 2 packet) =
        some (3, [7], [99], [42], some (.ok 42)) ∧
      resultView (second.map fun packet => OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live currentPoint 0 2 packet) =
        some (3, [7], [99], [43], some (.ok 43)) := by
  dsimp only
  rw [duplicateView_eq]
  repeat' constructor
  all_goals decide +kernel

def latentTransform (choice : Nat) : Sources.Transform Nat Value Pattern :=
  ⟨.cons (.read messagePattern)
    (.cons (.letBind (.var 1) (fun _ => [.leaf (if choice = 1 then .a else .b)])) .done), []⟩
def latentBuild := buildRecipe layer matcher label latentTransform
  (fun (_ : Nat) => Sources.AbsenceControls.empty) body
def noMessages := Sources.Query.scanList label ([] : List Nat)
def oneMessage := Sources.Query.scanList label [1]
def latentCapture (choice : Nat) : Driver :=
  capture revocationWorlds writeRequirement latentBuild
    (OwnWrite.advance revocationWorlds writeRequirement 1 (.ret choice) initial)
def latentEmpty (choice : Nat) : Driver :=
  let fresh := (refresh revocationWorlds writeRequirement noMessages (latentCapture choice)).getD (latentCapture choice)
  delivered (resumeGuard revocationWorlds writeRequirement noMessages 2 fresh)
def latentReady (choice : Nat) : Driver :=
  let fresh := (refresh revocationWorlds writeRequirement oneMessage (latentEmpty choice)).getD (latentEmpty choice)
  delivered (resumeGuard revocationWorlds writeRequirement oneMessage 2 fresh)

/-- The finished guard packets still collide, as in the negative control.
The retained recipes preserve the latent branch and produce distinct later
bindings without guessing the program from the old empty answer. -/
theorem completed_guard_packets_equal_but_recipes_recover_distinct_futures :
    (latentEmpty 1).attempt = (latentEmpty 2).attempt ∧
      (select revocationWorlds writeRequirement oneMessage 0 (latentReady 1)).map (fun row => row.1 1) =
        some (some (.leaf .a)) ∧
      (select revocationWorlds writeRequirement oneMessage 0 (latentReady 2)).map (fun row => row.1 1) =
        some (some (.leaf .b)) := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide +kernel

theorem producer_refusal_retains_the_real_suffix :
    let refused := resumeProducer revocationWorlds writeRequirement entryRequirement
      (OwnWrite.current revocationWorlds writeRequirement producerCut).store revokedPoint 0 2 captured
    isRefusal refused = true ∧ (delivered refused).producer.1 = 1 ∧
      OrderedDependencyStore.query (OwnWrite.current revocationWorlds writeRequirement (delivered refused).producer).store 0 = [7] ∧
      (recipe? revocationWorlds writeRequirement
        (delivered (resumeProducer revocationWorlds writeRequirement entryRequirement
          (OwnWrite.current revocationWorlds writeRequirement producerCut).store currentPoint 0 2 (delivered refused)))).isSome = true := by decide +kernel

theorem producer_fault_is_not_empty_guard :
    let failed : Driver := capture revocationWorlds writeRequirement build
      (OwnWrite.advance revocationWorlds writeRequirement 2 producer ⟨initial.store, revokedPoint⟩)
    (match observe revocationWorlds writeRequirement beforeView failed with
      | .producerFault .denied => true | _ => false) = true ∧
      (refresh revocationWorlds writeRequirement beforeView failed).isNone = true ∧
      answerCount beforeView failed = none := by decide +kernel

abbrev Pool := Registration.State Nat Nat Driver
def ownerKey : AsyncWait.Identity := ⟨7, 1, 501⟩
def waitingPool : Pool :=
  let empty : Pool := Registration.empty 1
  { empty with queue := { empty.queue with ready := ⟨1, [9]⟩ } }
def installedPool : Pool :=
  ((Registration.install 1 7 501 emptyGuard waitingPool).getD (ownerKey, waitingPool)).2
def acquiredPool : Pool :=
  (Registration.acquire 2 .exclusive 1 ownerKey 10 installedPool).getD installedPool
def checkedPool : Pool :=
  (recheckOwned revocationWorlds writeRequirement beforeView ownerKey 10 acquiredPool).getD acquiredPool
def ownedInbox := EventPump.FiniteBurst.initial ownerKey
def postedPool : EventPump.Inbox × Pool :=
  (routeOwned revocationWorlds writeRequirement label (Commit.makeOne 1) ownerKey 800 10 ownedInbox checkedPool).getD (ownedInbox, checkedPool)
def handedPool : Pool :=
  { postedPool.2 with queue := (QueueDelivery.Admission.run 2 (fun _ => [9]) postedPool.2.queue).2 }
def bodyAfterHandoff : Option (OwnWrite.Saved revocationWorlds writeRequirement Nat) :=
  (readCurrent ownerKey 10 handedPool).bind fun driver =>
    (refresh revocationWorlds writeRequirement afterView driver).bind fun fresh =>
      match resumeGuard revocationWorlds writeRequirement afterView 2 fresh with
      | .error _ => none
      | .ok checked => prepareBody revocationWorlds writeRequirement afterView live currentPoint 0 checked

theorem owned_recipe_crosses_real_notification_and_fair_handoff :
    checkedPool.queue.cells 7 = ⟨1, .armed⟩ ∧ postedPool.2.queue.pending = [ownerKey] ∧
      handedPool.queue.cells 7 = ⟨1, .claimed⟩ ∧
      (readCurrent ownerKey 10 handedPool).map (queryInvoice revocationWorlds writeRequirement) = some 1 ∧
      resultView (bodyAfterHandoff.map fun packet =>
        OwnWrite.Invocation.resume revocationWorlds writeRequirement entryRequirement live currentPoint 0 2 packet) =
          some (3, [7], [99], [42], some (.ok 42)) := by decide +kernel

theorem wrong_key_and_revocation_refuse_owned_recipe_access :
    let other : AsyncWait.Identity := { ownerKey with serial := 502 }
    let revoked := (Registration.revoke ownerKey handedPool).getD (none, handedPool)
    (prepareOwned revocationWorlds writeRequirement afterView live currentPoint 0 other 10 handedPool).isNone = true ∧
      (recheckOwned revocationWorlds writeRequirement afterView ownerKey 10 revoked.2).isNone = true ∧
      (readHeld ownerKey 10 revoked.2).map (fun driver => driver.producer.1) = some 2 := by decide +kernel

theorem held_ready_recipe_is_not_current_source_permission :
    let installed := ((Registration.install 1 7 501 ready waitingPool).getD (ownerKey, waitingPool)).2
    let acquired := (Registration.acquire 2 .exclusive 1 ownerKey 10 installed).getD installed
    let closed := (Registration.revoke ownerKey acquired).getD (none, acquired)
    (readHeld ownerKey 10 closed.2).map (queryInvoice revocationWorlds writeRequirement) = some 2 ∧
      (prepareOwned revocationWorlds writeRequirement afterView live currentPoint 0 ownerKey 10 closed.2).isNone = true := by decide +kernel

/-- Matching and preparing a body do not discharge a consuming proposal.
The same occurrence can match both takes, but its footprint is not linear. -/
theorem prepared_code_is_not_source_commit_admission :
    let plan : Nat → Sources.Transform Nat Value Pattern := fun _ =>
      ⟨Sources.Query.Controls.repeatedTake, []⟩
    let started : Driver := capture revocationWorlds writeRequirement
      (buildRecipe layer matcher label plan bindings body)
      (OwnWrite.advance revocationWorlds writeRequirement 1 (.ret 42) initial)
    let fresh := (refresh revocationWorlds writeRequirement afterView started).getD started
    let matching := delivered (resumeGuard revocationWorlds writeRequirement afterView 3 fresh)
    answerCount afterView matching = some 1 ∧
      (select revocationWorlds writeRequirement afterView 0 matching).map
        (fun row => decide (Sources.footprintOf row.2).Linear) = some false ∧
      (prepareBody revocationWorlds writeRequirement afterView live currentPoint 0 matching).isSome = true := by
  dsimp only
  constructor
  · decide +kernel
  · constructor <;> decide +kernel

end Controls

section OwnedGuards

variable [DecidableEq O]

/-- A false reply retains the complete old driver. True records a fresh pure
attempt, not a ready answer and not permission to run a body. -/
def rearmOwned (current : (T → Bool) → List O) (key : AsyncWait.Identity) (use : Use)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :=
  Registration.transitionCurrent key use (fun driver =>
    match refresh authority required current driver with
    | none => (false, driver)
    | some next => (true, next)) pool

/-- Advance the guarded program stored in the acquired entry. Stale reads
return false with the actual refused packet; zero allowance does no query
validation. The reply does not classify readiness or declarative absence. -/
def resumeOwnedGuard (current : (T → Bool) → List O) (fuel : Nat) (key : AsyncWait.Identity) (use : Use)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :=
  Registration.transitionCurrent key use (fun driver =>
    match resumeGuard authority required current fuel driver with
    | .error refused => (false, refused)
    | .ok next => (true, next)) pool

omit [DecidableEq O] in
theorem rearmOwned_actual (current : (T → Bool) → List O) (key : AsyncWait.Identity) (use : Use)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (accepted : rearmOwned authority required current key use before = some (true, after)) :
    ∃ previous next, readCurrent key use before = some previous ∧
      readCurrent key use after = some next ∧ refresh authority required current previous = some next ∧
      next.producer = previous.producer ∧ queryInvoice authority required next = queryInvoice authority required previous ∧
      GuardOrigin authority required next ∧ after.queue = before.queue := by
  obtain ⟨previous, held, reached, answer, queue, _⟩ := Registration.transitionCurrent_capture key use _ before after true accepted
  cases refreshed : refresh authority required current previous with
  | none => simp only [refreshed, Bool.true_eq_false] at answer
  | some next =>
      simp only [refreshed] at reached
      have retained := refresh_preserves_prefix_and_invoice authority required current previous next refreshed
      exact ⟨previous, next, held, reached, refreshed, retained.1, retained.2,
        refresh_guard_origin authority required current previous next refreshed, queue⟩

theorem resumeOwnedGuard_actual (current : (T → Bool) → List O) (fuel : Nat) (key : AsyncWait.Identity) (use : Use)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (accepted : resumeOwnedGuard authority required current fuel key use before = some (true, after)) :
    ∃ previous next, readCurrent key use before = some previous ∧
      readCurrent key use after = some next ∧ resumeGuard authority required current fuel previous = .ok next ∧
      next.producer = previous.producer ∧ after.queue = before.queue := by
  obtain ⟨previous, held, reached, answer, queue, _⟩ := Registration.transitionCurrent_capture key use _ before after true accepted
  cases advanced : resumeGuard authority required current fuel previous with
  | error refused => simp only [advanced, Bool.true_eq_false] at answer
  | ok next =>
      simp only [advanced] at reached
      exact ⟨previous, next, held, reached, advanced,
        (resumeGuard_retains_prefix authority required current fuel previous next advanced).1, queue⟩

theorem resumeOwnedGuard_origin (current : (T → Bool) → List O) (fuel : Nat) (key : AsyncWait.Identity) (use : Use)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (origin : ∀ driver, readCurrent key use before = some driver → GuardOrigin authority required driver)
    (accepted : resumeOwnedGuard authority required current fuel key use before = some (true, after)) :
    ∃ next, readCurrent key use after = some next ∧ GuardOrigin authority required next := by
  obtain ⟨previous, next, held, reached, advanced, _, _⟩ :=
    resumeOwnedGuard_actual authority required current fuel key use before after accepted
  exact ⟨next, reached, resumeGuard_origin authority required current fuel previous next (origin previous held) advanced⟩

theorem resumeOwnedGuard_zero (current : (T → Bool) → List O) (key : AsyncWait.Identity) (use : Use)
    (before after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (accepted : resumeOwnedGuard authority required current 0 key use before = some (true, after)) : after = before :=
  Registration.transitionCurrent_identity key use true before after accepted

/-- Re-arming and bounded execution act on the same acquired entry. Its
producer prefix survives, and the final packet has actual guard provenance. -/
theorem rearm_resume_owned_origin (current : (T → Bool) → List O) (fuel : Nat)
    (key : AsyncWait.Identity) (use : Use)
    (before middle after : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (rearmed : rearmOwned authority required current key use before = some (true, middle))
    (resumed : resumeOwnedGuard authority required current fuel key use middle = some (true, after)) :
    ∃ previous next, readCurrent key use before = some previous ∧ readCurrent key use after = some next ∧
      next.producer = previous.producer ∧ GuardOrigin authority required next ∧ after.queue = before.queue := by
  obtain ⟨previous, fresh, held, installed, refreshed, prefixEq, _, origin, firstQueue⟩ :=
    rearmOwned_actual authority required current key use before middle rearmed
  obtain ⟨actual, next, actualHeld, reached, advanced, samePrefix, nextQueue⟩ :=
    resumeOwnedGuard_actual authority required current fuel key use middle after resumed
  have same : actual = fresh := Option.some.inj (actualHeld.symm.trans installed)
  subst actual
  exact ⟨previous, next, held, reached, samePrefix.trans prefixEq,
    resumeGuard_origin authority required current fuel fresh next origin advanced, nextQueue.trans firstQueue⟩

end OwnedGuards

namespace Admission

variable {O V T P Entry World Answer Holder Use : Type} {size : Nat}
variable [Category.{0} World] [LinearOrder O] [DecidableEq T] [DecidableEq Use]
variable (authority : IndexedAuthority.{0, 0, 0} World)
  (required : OrderedDependencyStore.Action Entry size → (world : World) → authority.Fibre world)
  [permission : ∀ (point : IndexedAuthority.Point authority) (action : OrderedDependencyStore.Action Entry size),
    Decidable (FrameUpdate point.authority (required action point.world))]

/-- The selected occurrence row and the exact issued output identities. -/
structure Selection (O V T : Type) where
  position : Nat
  row : Row O V T
  made : Finset O

/-- All tests are finite. The issued set includes retired identities, so an
output cannot recycle an old identity merely because it is currently absent. -/
def eligible (label : O → T) (store born : Finset O) (selected : Selection O V T) : Prop :=
  let footprint := Sources.footprintOf selected.row.2
  footprint.Linear ∧ footprint.Holds label store ∧
    Disjoint selected.made (store ∪ born) ∧ labels label selected.made = footprint.makes

instance eligibleDecision (label : O → T) (store born : Finset O) (selected : Selection O V T) :
    Decidable (eligible label store born selected) := by
  unfold eligible Sources.Footprint.Holds
  infer_instance

/-- Read the actual completed guard in the current source view, then check
its consuming multiplicities and proposed fresh outputs. No caller-supplied
row or dependency certificate is accepted. Failure leaves the driver intact. -/
def choose (label : O → T) (store born : Finset O) (index : Nat) (made : Finset O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required) :
    Option (Selection O V T) :=
  (select authority required (scan label store) index state).bind fun row =>
    if eligible label store born ⟨index, row, made⟩ then some ⟨index, row, made⟩ else none

theorem choose_iff (label : O → T) (store born : Finset O) (index : Nat) (made : Finset O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (selected : Selection O V T) :
    choose authority required label store born index made state = some selected ↔
      select authority required (scan label store) index state = some selected.row ∧
      selected.position = index ∧ selected.made = made ∧ eligible label store born selected := by
  unfold choose
  constructor
  · intro accepted
    obtain ⟨row, found, rest⟩ := Option.bind_eq_some_iff.mp accepted
    split at rest
    · cases Option.some.inj rest
      exact ⟨found, rfl, rfl, by assumption⟩
    · cases rest
  · rintro ⟨found, positionEq, madeEq, valid⟩
    rcases selected with ⟨position, row, outputs⟩
    cases positionEq
    cases madeEq
    simp only [found, Option.bind_some, if_pos valid]

omit [DecidableEq T] in
/-- The executable proposal is order-free. Reifying its predicate multiset
into the existing list-based commit is a logical witness, not an executable
enumerator or a claimed native publication implementation. -/
theorem eligible_commit (label : O → T) (store born : Finset O)
    (selected : Selection O V T) (valid : eligible label store born selected) :
    ∃ commit : Commit O T,
      Sources.IsCommitOf label store (Sources.footprintOf selected.row.2) commit ∧
      Enabled label store commit ∧ Disjoint commit.made born ∧ commit.made = selected.made := by
  let footprint := Sources.footprintOf selected.row.2
  let commit : Commit O T :=
    ⟨footprint.takes.toFinset, footprint.keeps.toFinset, selected.made, footprint.queries.toList⟩
  have fresh := (Finset.disjoint_union_right.mp valid.2.2.1).1
  have actual : Sources.IsCommitOf label store footprint commit :=
    ⟨rfl, rfl, fun _ => Multiset.mem_toList, fresh, valid.2.2.2⟩
  exact ⟨commit, actual, (actual.enabled_iff fresh).mpr ⟨valid.2.1, valid.1.2⟩,
    (Finset.disjoint_union_right.mp valid.2.2.1).2, rfl⟩

/-- Current membership is derived from actual guard execution. Initial
bindings remain explicit; the source transform's empty-binding convention
must not silently replace an earned environment. -/
theorem choose_source [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (store born : Finset O) (index : Nat) (made : Finset O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required state)
    (compiled : ∀ recipe, recipe? authority required state = some recipe → Compiled L matcher label recipe)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher)
    (respects : ∀ recipe, recipe? authority required state = some recipe →
      ∀ eval ∈ recipe.transform.sources.lets, Sources.Respects L eval)
    (selected : Selection O V T)
    (accepted : choose authority required label store born index made state = some selected) :
    ∃ recipe commit, recipe? authority required state = some recipe ∧
      Sources.DRow L label store recipe.transform.template recipe.transform.sources recipe.bindings selected.row ∧
      (Sources.footprintOf selected.row.2).Linear ∧
      Sources.IsCommitOf label store (Sources.footprintOf selected.row.2) commit ∧
      Enabled label store commit ∧ Disjoint commit.made born ∧ commit.made = made := by
  obtain ⟨found, _, madeEq, valid⟩ := (choose_iff authority required label store born index made state selected).mp accepted
  obtain ⟨recipe, earned, declared⟩ := selected_declarative_row authority required
    L matcher label store (scan label store) (scan_complete label store)
    sound complete minimal index state origin compiled respects selected.row found
  obtain ⟨commit, actual, enabled, fresh, same⟩ := eligible_commit label store born selected valid
  exact ⟨recipe, commit, earned, declared, valid.1, actual, enabled, fresh, same.trans madeEq⟩

/-- Empty initial bindings recover the existing transform firing judgment.
The general retained-environment theorem above does not need this restriction. -/
theorem choose_fires
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (store born : Finset O) (index : Nat) (made : Finset O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (origin : GuardOrigin authority required state)
    (recipe : Recipe O V T P Entry Answer size) (earned : recipe? authority required state = some recipe)
    (compiled : Compiled L matcher label recipe) (empty : recipe.bindings = fun _ => none)
    (selected : Selection O V T)
    (accepted : choose authority required label store born index made state = some selected) :
    ∃ commit, Sources.Fires L matcher label store recipe.transform commit ∧ commit.made = made := by
  obtain ⟨found, _, madeEq, valid⟩ := (choose_iff authority required label store born index made state selected).mp accepted
  obtain ⟨actual, actualFound, indexed⟩ := select_origin authority required (scan label store) index state origin selected.row found
  have same : actual = recipe := Option.some.inj (actualFound.symm.trans earned)
  subst actual
  have listed := List.mem_of_getElem? indexed
  change selected.row ∈ ((ReadOnlyQuery.run (scan label store) recipe.program).answer : Multiset (Row O V T)) at listed
  rw [compiled, Sources.Query.run_compile L matcher label store (scan label store)
    (scan_complete label store) recipe.transform.template recipe.transform.sources recipe.bindings,
    empty] at listed
  obtain ⟨commit, formed, _, _, outputs⟩ := eligible_commit label store born selected valid
  exact ⟨commit, ⟨selected.row, listed, valid.1, formed⟩, outputs.trans madeEq⟩

/-- A checked proposal supplies the enabling evidence for the existing
claim/epoch protocol. This constructs its begin step only; atomic publication
and scheduler progress are not consequences of beginning a transaction. -/
theorem choose_begins_protocol {Task : Type} [DecidableEq Task]
    (label : O → T) (protocol : OccurrenceCommits.ProtocolState O T Task)
    (transactions : Task → Commit O T) (task : Task)
    (idle : protocol.phase task = .idle) (index : Nat) (made : Finset O)
    (state : State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
    (selected : Selection O V T)
    (accepted : choose authority required label protocol.store protocol.born index made state = some selected) :
    ∃ commit, commit.made = made ∧ Disjoint commit.made protocol.born ∧
      OccurrenceCommits.Step label (Function.update transactions task commit) protocol none
        { protocol with phase := Function.update protocol.phase task (.active protocol.epoch) } := by
  obtain ⟨_, _, outputs, valid⟩ := (choose_iff authority required label protocol.store protocol.born index made state selected).mp accepted
  obtain ⟨commit, _, enabled, fresh, same⟩ := eligible_commit label protocol.store protocol.born selected valid
  refine ⟨commit, same.trans outputs, fresh, ?_⟩
  exact OccurrenceCommits.Step.begin protocol task idle (by simpa using enabled)

/-- The source effect, independent of the enumeration of its predicate queries. -/
def applySelection (store : Finset O) (selected : Selection O V T) : Finset O :=
  (store \ (Sources.footprintOf selected.row.2).takes.toFinset) ∪ selected.made

omit [DecidableEq T] in
theorem applySelection_eq_fire (label : O → T) (store : Finset O)
    (selected : Selection O V T) (commit : Commit O T)
    (formed : Sources.IsCommitOf label store (Sources.footprintOf selected.row.2) commit)
    (outputs : commit.made = selected.made) : applySelection store selected = fire store commit := by
  simp only [applySelection, fire, formed.taken, outputs]

omit [DecidableEq T] in
theorem consumed_absent (label : O → T) (store born : Finset O)
    (selected : Selection O V T) (valid : eligible label store born selected)
    (occurrence : O) (taken : occurrence ∈ (Sources.footprintOf selected.row.2).takes) :
    occurrence ∉ applySelection store selected := by
  have present := valid.2.1.1 occurrence taken
  have notMade : occurrence ∉ selected.made := fun produced =>
    Finset.disjoint_left.mp valid.2.2.1 produced (Finset.mem_union_left _ present)
  simp [applySelection, taken, notMade]

/-- The sequential source boundary returns the updated occurrence store,
retired registration and an unexecuted body. This is not the fine-grained
concurrent publication protocol, nor permission to replay copied body code. -/
structure Published where
  store : Finset O
  born : Finset O
  inbox : EventPump.Inbox
  pool : Registration.State Holder Use
    (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)
  selected : Selection O V T
  body : OwnWrite.Saved authority required Answer

/-- One logical source firing consumes the claimed registration. No body
effect runs here. Current world permission is checked by its later invocation.
A cancelled wake cannot publish merely because its source bytes remain held. -/
def publishOnce (label : O → T) (store born : Finset O) (index : Nat) (made : Finset O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (key : AsyncWait.Identity) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required)) :
    Option (Published (Holder := Holder) (Use := Use) (O := O) (V := V) (T := T) (P := P)
      (Answer := Answer) authority required) :=
  (readCurrent key use pool).bind fun driver =>
    if pool.queue.cells key.owner = ⟨key.generation, .claimed⟩ then
      (choose authority required label store born index made driver).bind fun selected =>
        (prepareBody authority required (scan label store) live point index driver).bind fun body =>
          (retire key inbox pool).map fun retired =>
            ⟨applySelection store selected, born ∪ selected.made, retired.1, retired.2.2, selected, body⟩
    else none

theorem publishOnce_admitted (label : O → T) (store born : Finset O) (index : Nat) (made : Finset O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (key : AsyncWait.Identity) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (published : Published (Holder := Holder) (Use := Use) (O := O) (V := V) (T := T) (P := P)
      (Answer := Answer) authority required)
    (accepted : publishOnce authority required label store born index made live point key use inbox pool = some published) :
    ∃ driver, readCurrent key use pool = some driver ∧
      pool.queue.cells key.owner = ⟨key.generation, .claimed⟩ ∧
      choose authority required label store born index made driver = some published.selected ∧
      prepareBody authority required (scan label store) live point index driver = some published.body ∧
      retire key inbox pool = some (published.inbox, none, published.pool) ∧
      published.store = applySelection store published.selected ∧
      published.born = born ∪ published.selected.made ∧
      readHeld key use published.pool = some driver ∧ published.pool.queue.keys key.owner = none := by
  unfold publishOnce at accepted
  obtain ⟨driver, held, rest⟩ := Option.bind_eq_some_iff.mp accepted
  split at rest
  · rename_i claimed
    obtain ⟨selected, chosen, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨body, prepared, rest⟩ := Option.bind_eq_some_iff.mp rest
    obtain ⟨result, retired, same⟩ := Option.map_eq_some_iff.mp rest
    cases same
    obtain ⟨_, owner, found, _, _, issued, payload⟩ := readCurrent_requires_owned_use key use pool driver held
    obtain ⟨noFinalizer, retained, _, cleared⟩ := retire_keeps_acquired_source key use inbox result.1 pool result.2.2
      result.2.1 owner found issued retired
    refine ⟨driver, held, claimed, chosen, prepared, ?_, rfl, rfl, retained.trans payload, cleared⟩
    have resultEq : result = (result.1, none, result.2.2) := by rw [← noFinalizer]
    exact retired.trans (congrArg some resultEq)
  · cases rest

/-- Even a changed store or a copied use token cannot reuse the retired
registration. This is one source firing per key, not once-only external I/O. -/
theorem retired_cannot_publish (label : O → T) (store born : Finset O) (index : Nat) (made : Finset O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (key : AsyncWait.Identity) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (retired : pool.queue.keys key.owner = none) :
    publishOnce authority required label store born index made live point key use inbox pool = none := by
  simp [publishOnce, readCurrent, retired]

/-- The sequential publication is an actual commit of a declarative source
row, and its unexecuted body comes from that same retained recipe. This does
not identify the source occurrence store with the body's service store. -/
theorem publishOnce_source [DecidableEq V]
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher)
    (store born : Finset O) (index : Nat) (made : Finset O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (key : AsyncWait.Identity) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (origin : ∀ driver, readCurrent key use pool = some driver → GuardOrigin authority required driver)
    (compiled : ∀ driver, readCurrent key use pool = some driver →
      ∀ recipe, recipe? authority required driver = some recipe → Compiled L matcher label recipe)
    (respects : ∀ driver, readCurrent key use pool = some driver →
      ∀ recipe, recipe? authority required driver = some recipe →
      ∀ eval ∈ recipe.transform.sources.lets, Sources.Respects L eval)
    (published : Published (Holder := Holder) (Use := Use) (O := O) (V := V) (T := T) (P := P)
      (Answer := Answer) authority required)
    (accepted : publishOnce authority required label store born index made live point key use inbox pool = some published) :
    ∃ driver recipe commit,
      readCurrent key use pool = some driver ∧ recipe? authority required driver = some recipe ∧
      Sources.DRow L label store recipe.transform.template recipe.transform.sources recipe.bindings published.selected.row ∧
      (Sources.footprintOf published.selected.row.2).Linear ∧
      Sources.IsCommitOf label store (Sources.footprintOf published.selected.row.2) commit ∧
      Enabled label store commit ∧ published.store = fire store commit ∧
      published.born = born ∪ commit.made ∧ Disjoint commit.made born ∧
      published.body = (driver.producer.1,
        .paused ⟨.unit, .ok (recipe.body index published.selected.row), ⟨live, point⟩⟩) := by
  obtain ⟨driver, held, _, chosen, prepared, _, storeEq, bornEq, _, _⟩ :=
    publishOnce_admitted authority required label store born index made live point key use inbox pool published accepted
  obtain ⟨recipe, commit, earned, declared, linear, formed, enabled, fresh, madeEq⟩ :=
    choose_source authority required L matcher label store born index made driver (origin driver held)
      (compiled driver held) sound complete minimal (respects driver held) published.selected chosen
  obtain ⟨selected, _, outputEq, _⟩ :=
    (choose_iff authority required label store born index made driver published.selected).mp chosen
  obtain ⟨bodyRecipe, row, bodyEarned, bodyRow, bodyEq⟩ :=
    prepareBody_source authority required (scan label store) live point index driver published.body prepared
  have sameRecipe : bodyRecipe = recipe := Option.some.inj (bodyEarned.symm.trans earned)
  have sameRow : row = published.selected.row := Option.some.inj (bodyRow.symm.trans selected)
  subst bodyRecipe row
  have actualOutputs : commit.made = published.selected.made := madeEq.trans outputEq.symm
  refine ⟨driver, recipe, commit, held, earned, declared, linear, formed, enabled,
    storeEq.trans (applySelection_eq_fire label store published.selected commit formed actualOutputs), ?_, fresh, bodyEq⟩
  simpa only [actualOutputs] using bornEq

/-- Join an actual earned producer, source publication and successful body
execution. The source store and service store remain explicit, distinct
observations; this theorem does not supply their native coherence bridge. -/
theorem publishOnce_producer_source [DecidableEq V] {Environment : Type}
    (L : Sources.TermLayer V T P) (matcher : Sources.Matcher V T P) (label : O → T)
    (sound : Sources.Matcher.Sound L matcher) (complete : Sources.Matcher.Complete L matcher)
    (minimal : Sources.Matcher.Minimal L matcher)
    (transform : Environment → Sources.Transform V T P) (bindings : Environment → Sources.Subst V T)
    (body : Environment → Nat → Row O V T → Prog (OwnWrite.Request Entry size) OwnWrite.Reply Answer)
    (respects : ∀ environment, ∀ eval ∈ (transform environment).sources.lets, Sources.Respects L eval)
    (producer : Prog (OwnWrite.Request Entry size) OwnWrite.Reply Environment)
    (initial : OwnWrite.State authority Entry size) (first later : Nat)
    (store born : Finset O) (index : Nat) (made : Finset O)
    (live : OrderedDependencyStore.Store Entry size) (point : IndexedAuthority.Point authority)
    (key : AsyncWait.Identity) (use : Use) (inbox : EventPump.Inbox)
    (pool : Registration.State Holder Use
      (State (O := O) (V := V) (T := T) (P := P) (Answer := Answer) authority required))
    (origin : ∀ driver, readCurrent key use pool = some driver → GuardOrigin authority required driver)
    (retained : ∀ driver, readCurrent key use pool = some driver →
      driver.producer = Cursor.resume (OwnWrite.provider authority required) (OwnWrite.client _)
        (fun _ _ => 1) later
        (OwnWrite.ReturnMap.saved authority required (buildRecipe L matcher label transform bindings body)
          (OwnWrite.advance authority required first producer initial)))
    (published : Published (Holder := Holder) (Use := Use) (O := O) (V := V) (T := T) (P := P)
      (Answer := Answer) authority required)
    (accepted : publishOnce authority required label store born index made live point key use inbox pool = some published)
    (needed : (world : World) → authority.Fibre world)
    [admission : ∀ atPoint : IndexedAuthority.Point authority,
      Decidable (FrameUpdate atPoint.authority (needed atPoint.world))]
    (reader : Fin size) (fuel paid : Nat) (answer : Answer) (after : OwnWrite.State authority Entry size)
    (finished : OwnWrite.Invocation.resume authority required needed live point reader fuel published.body =
      .ok (paid, .done ⟨.unit, .ok answer, after⟩)) :
    ∃ environment captured commit,
      producer.Runs (OwnWrite.action authority required) initial environment captured ∧
      Sources.DRow L label store (transform environment).template (transform environment).sources
        (bindings environment) published.selected.row ∧
      (Sources.footprintOf published.selected.row.2).Linear ∧
      Sources.IsCommitOf label store (Sources.footprintOf published.selected.row.2) commit ∧
      Enabled label store commit ∧ published.store = fire store commit ∧
      (body environment index published.selected.row).Runs (OwnWrite.action authority required) ⟨live, point⟩ answer after ∧
      published.pool.queue.keys key.owner = none := by
  have built : ∀ driver, readCurrent key use pool = some driver →
      ∀ recipe, recipe? authority required driver = some recipe →
      ∃ environment captured, producer.Runs (OwnWrite.action authority required) initial environment captured ∧
        buildRecipe L matcher label transform bindings body environment = recipe := by
    intro driver held recipe earned
    obtain ⟨prefixPaid, captured, packet⟩ := recipe_some_packet authority required driver recipe earned
    obtain ⟨environment, ran, same⟩ := OwnWrite.ReturnMap.producer_source authority required
      (buildRecipe L matcher label transform bindings body) producer initial captured first later prefixPaid recipe
      ((retained driver held).symm.trans packet)
    exact ⟨environment, captured, ran, same⟩
  have compiled : ∀ driver, readCurrent key use pool = some driver →
      ∀ recipe, recipe? authority required driver = some recipe → Compiled L matcher label recipe := by
    intro driver held recipe earned
    obtain ⟨environment, _, _, same⟩ := built driver held recipe earned
    rw [← same]
    exact buildRecipe_compiled L matcher label transform bindings body environment
  have lawful : ∀ driver, readCurrent key use pool = some driver →
      ∀ recipe, recipe? authority required driver = some recipe →
      ∀ eval ∈ recipe.transform.sources.lets, Sources.Respects L eval := by
    intro driver held recipe earned
    obtain ⟨environment, _, _, same⟩ := built driver held recipe earned
    rw [← same]
    exact respects environment
  obtain ⟨driver, recipe, commit, held, earned, declared, linear, formed, enabled, sourceEq, _, _, _⟩ :=
    publishOnce_source authority required L matcher label sound complete minimal store born index made live point
      key use inbox pool origin compiled lawful published accepted
  obtain ⟨environment, captured, producerRan, same⟩ := built driver held recipe earned
  obtain ⟨actual, actualHeld, _, chosen, prepared, _, _, _, _, cleared⟩ :=
    publishOnce_admitted authority required label store born index made live point key use inbox pool published accepted
  have actualEq : actual = driver := Option.some.inj (actualHeld.symm.trans held)
  subst actual
  obtain ⟨bodyRecipe, row, bodyEarned, bodyRow, bodyRan⟩ :=
    prepared_body_completed authority required needed (scan label store) live point reader index fuel paid driver
      published.body answer after prepared finished
  have recipeEq : bodyRecipe = recipe := Option.some.inj (bodyEarned.symm.trans earned)
  subst bodyRecipe
  have selected := (choose_iff authority required label store born index made driver published.selected).mp chosen
  have rowEq : row = published.selected.row := Option.some.inj (bodyRow.symm.trans selected.1)
  subst row
  rw [← same] at declared bodyRan
  exact ⟨environment, captured, commit, producerRan, declared, linear, formed, enabled, sourceEq, bodyRan, cleared⟩

namespace Controls

open Sources.AbsenceControls Sources.Commutative
open Reactive.Controls

local notation "requirement" => OwnWrite.Controls.requirement
local notation "point" => OwnWrite.Controls.held

local instance permissionDecision (entrance : IndexedAuthority.Point revocationWorlds)
    (action : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate entrance.authority (requirement action entrance.world)) :=
  OwnWrite.Controls.permissionDecision entrance action

def readyFor (sources : Sources.SourceList Nat Value Pattern) (template : List Pattern := []) : Driver :=
  let built := buildRecipe layer matcher Reactive.Controls.label (fun _ => ⟨sources, template⟩) bindings body
  let produced := capture revocationWorlds requirement built
    (OwnWrite.advance revocationWorlds requirement 3 producer initial)
  let fresh := (refresh revocationWorlds requirement afterView produced).getD produced
  delivered (resumeGuard revocationWorlds requirement afterView 4 fresh)

def taking : Driver := readyFor (.cons (.take messagePattern) .done) [messagePattern]
def repeated : Driver := readyFor Sources.Query.Controls.repeatedTake
def mixed : Driver := readyFor (.cons (.take messagePattern) (.cons (.read messagePattern) .done))

theorem actual_take_and_equal_payload_fresh_output :
    (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2} taking).map
      (fun selected => ((Sources.footprintOf selected.row.2).takes, selected.made,
        applySelection {0, 1} selected)) = some ({1}, {2}, {0, 2}) := by decide +kernel

theorem duplicate_take_and_take_read_overlap_refused :
    (prepareBody revocationWorlds requirement afterView live point 0 repeated).isSome = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 ∅ repeated).isNone = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 ∅ mixed).isNone = true := by decide +kernel

theorem allocation_identity_and_label_multiplicity_are_checked :
    (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1, 2} 0 {2} taking).isNone = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {1} taking).isNone = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 ∅ taking).isNone = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2, 3} taking).isNone = true := by decide +kernel

theorem wrong_output_label_refused :
    let different := readyFor (.cons (.take messagePattern) .done) [.leaf .b]
    (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2} different).isNone = true := by decide +kernel

theorem vanished_kept_or_taken_occurrence_refuses :
    (choose revocationWorlds requirement Reactive.Controls.label {0} {0, 1} 0 ∅ ready).isNone = true ∧
      (choose revocationWorlds requirement Reactive.Controls.label {0} {0, 1} 0 {2} taking).isNone = true := by decide +kernel

theorem unrelated_same_predicate_change_preserves_admission :
    (choose revocationWorlds requirement Reactive.Controls.label {1} {0, 1} 0 {2} taking).map
      (fun selected => applySelection {1} selected) = some {2} := by decide +kernel

theorem read_only_selection_preserves_occurrences :
    (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 ∅ ready).map
      (applySelection {0, 1}) = some {0, 1} := by decide +kernel

theorem equal_payload_replacement_is_not_the_selected_occurrence :
    (choose revocationWorlds requirement Reactive.Controls.label {0, 2} {0, 1, 2} 0 {3} taking).isNone = true := by decide +kernel

theorem equal_alternatives_retain_their_selected_position :
    let alternatives := readyFor (.cons (.letBind messagePattern (fun _ => [message .a, message .a])) .done)
    (choose revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 1 ∅ alternatives).map
      (fun selected => (selected.position, selected.row.2.map fun pick =>
        match pick with | .result position => some position | _ => none)) = some (1, [some 1, none]) := by decide +kernel

theorem admission_checks_kept_and_complete_observations :
    let kept : Selection Nat Nat Value := ⟨0, (Sources.AbsenceControls.empty, [.keep 1]), ∅⟩
    let absent : Selection Nat Nat Value :=
      ⟨0, (Sources.AbsenceControls.empty, [.query ⟨fun _ => true, ∅⟩ false]), ∅⟩
    ¬ eligible Reactive.Controls.label {0} {0, 1} kept ∧
      ¬ eligible Reactive.Controls.label {0} {0} absent := by decide +kernel

/-- Installation, acquisition, readiness recheck and actual queue service
produce this claimed registration; no test supplies the claimed phase. -/
def offeredPool (driver : Driver) : Pool :=
  let installed := ((Registration.install 1 7 501 driver waitingPool).getD (ownerKey, waitingPool)).2
  let acquired := (Registration.acquire 2 .exclusive 1 ownerKey 10 installed).getD installed
  let checked := (recheckOwned revocationWorlds requirement afterView ownerKey 10 acquired).getD acquired
  { checked with queue := QueueDelivery.offerCurrent ownerKey checked.queue }

def entered (driver : Driver) : Pool :=
  let offered := offeredPool driver
  { offered with queue := (QueueDelivery.Admission.run 2 (fun _ => [9]) offered.queue).2 }

def published := publishOnce revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2}
  live point ownerKey 10 ownedInbox (entered taking)

theorem publication_consumes_occurrence_and_registration_together :
    published.map (fun result => (result.store, result.born, result.pool.queue.keys 7, result.body.1)) =
      some ({0, 2}, {0, 1, 2}, none, 2) ∧
      (published.bind fun result => readHeld ownerKey 10 result.pool).map (fun driver => driver.producer.1) = some 2 := by
  decide +kernel

theorem copied_registration_cannot_fire_again :
    (published.bind fun result => publishOnce revocationWorlds requirement Reactive.Controls.label
      {0, 1} result.born 0 {3} live point ownerKey 10 result.inbox result.pool).isNone = true := by decide +kernel

theorem cancellation_and_revocation_refuse_before_publication :
    let current := entered taking
    let waiting := offeredPool taking
    let cancelled := { waiting with queue := QueueDelivery.cancelCurrent ownerKey waiting.queue }
    let revoked := (Registration.revoke ownerKey current).getD (none, current)
    (readCurrent ownerKey 10 cancelled).isSome = true ∧
      (publishOnce revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2}
        live point ownerKey 10 ownedInbox cancelled).isNone = true ∧
      (readHeld ownerKey 10 revoked.2).isSome = true ∧
      (publishOnce revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2}
        live point ownerKey 10 ownedInbox revoked.2).isNone = true := by decide +kernel

theorem late_wake_cancellation_is_not_consumer_revocation :
    let current := entered taking
    let late := { current with queue := QueueDelivery.cancelCurrent ownerKey current.queue }
    (publishOnce revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 {2}
      live point ownerKey 10 ownedInbox late).isSome = true := by decide +kernel

theorem invalid_proposal_does_not_retire_its_source :
    let current := entered repeated
    (publishOnce revocationWorlds requirement Reactive.Controls.label {0, 1} {0, 1} 0 ∅
      live point ownerKey 10 ownedInbox current).isNone = true ∧
      (readCurrent ownerKey 10 current).isSome = true ∧ current.queue.keys 7 = some ownerKey := by decide +kernel

local instance : DecidableEq (Except OwnWrite.Fault Nat)
  | .error .denied, .error .denied => isTrue rfl
  | .error _, .ok _ => isFalse (fun same => nomatch same)
  | .ok _, .error _ => isFalse (fun same => nomatch same)
  | .ok first, .ok second =>
      if same : first = second then isTrue (congrArg Except.ok same)
      else isFalse (fun equal => same (Except.ok.inj equal))

local instance admissionDecision (entrance : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate entrance.authority (OwnWrite.InvocationControls.needed entrance.world)) :=
  OwnWrite.InvocationControls.admissionDecision entrance

/-- Retiring a registration does not make the returned code an uncopyable
effect ticket. A body execution owner must retain its actual residual. -/
theorem copied_body_still_requires_an_execution_owner :
    let replay := published.bind fun result =>
      match OwnWrite.Invocation.resume revocationWorlds requirement OwnWrite.InvocationControls.needed
          live point 0 2 result.body with
      | .error _ => none
      | .ok first => some (OwnWrite.Invocation.resume revocationWorlds requirement OwnWrite.InvocationControls.needed
          (OwnWrite.current revocationWorlds requirement first).store point 0 2 result.body)
    resultView replay = some (3, [7], [99], [42, 42], some (.ok 42)) := by decide +kernel

end Controls

end Admission

namespace OwnedGuardControls

open Reactive.Controls

local notation "requirement" => OwnWrite.Controls.requirement
local notation "point" => OwnWrite.Controls.held

local instance permissionDecision (entrance : IndexedAuthority.Point revocationWorlds)
    (action : OrderedDependencyStore.Action Nat 3) :
    Decidable (FrameUpdate entrance.authority (requirement action entrance.world)) :=
  OwnWrite.Controls.permissionDecision entrance action

local instance admissionDecision (entrance : IndexedAuthority.Point revocationWorlds) :
    Decidable (FrameUpdate entrance.authority (OwnWrite.InvocationControls.needed entrance.world)) :=
  OwnWrite.InvocationControls.admissionDecision entrance

local instance : DecidableEq (Except OwnWrite.Fault Nat)
  | .error .denied, .error .denied => isTrue rfl
  | .error _, .ok _ => isFalse (fun same => nomatch same)
  | .ok _, .error _ => isFalse (fun same => nomatch same)
  | .ok first, .ok second =>
      if same : first = second then isTrue (congrArg Except.ok same)
      else isFalse (fun equal => same (Except.ok.inj equal))

def rearmed := rearmOwned revocationWorlds requirement afterView ownerKey 10 handedPool
def freshPool := (rearmed.map Prod.snd).getD handedPool
def first := resumeOwnedGuard revocationWorlds requirement afterView 1 ownerKey 10 freshPool
def partialPool := (first.map Prod.snd).getD freshPool
def second := resumeOwnedGuard revocationWorlds requirement afterView 1 ownerKey 10 partialPool
def readyPool := (second.map Prod.snd).getD partialPool
def published := Admission.publishOnce revocationWorlds requirement label {0, 1} {0, 1}
  0 ∅ live point ownerKey 10 postedPool.1 readyPool

theorem actual_wake_rearms_and_resumes_the_registry_entry :
    handedPool.queue.cells 7 = ⟨1, .claimed⟩ ∧ rearmed.map Prod.fst = some true ∧
      first.map Prod.fst = some true ∧
      (readCurrent ownerKey 10 partialPool).map (isChecking afterView) = some true ∧
      second.map Prod.fst = some true ∧
      (readCurrent ownerKey 10 readyPool).map (fun driver =>
        (answerCount afterView driver, queryInvoice revocationWorlds requirement driver, driver.producer.1)) =
          some (some 1, 2, 2) := by decide +kernel

theorem refreshed_registered_source_publishes_and_runs_its_actual_body :
    published.map (fun result => (result.store, result.pool.queue.keys 7)) = some ({0, 1}, none) ∧
      resultView (published.map fun result =>
        OwnWrite.Invocation.resume revocationWorlds requirement OwnWrite.InvocationControls.needed
          live point 0 2 result.body) = some (3, [7], [99], [42], some (.ok 42)) := by decide +kernel

theorem zero_allowance_keeps_stale_owned_guard_without_validation :
    (resumeOwnedGuard revocationWorlds requirement afterView 0 ownerKey 10 handedPool).map
      (fun result => (result.1, (readCurrent ownerKey 10 result.2).map
        (queryInvoice revocationWorlds requirement))) = some (true, some 1) := by decide +kernel

theorem stale_refusal_keeps_actual_owned_packet :
    (resumeOwnedGuard revocationWorlds requirement afterView 1 ownerKey 10 handedPool).map
      (fun result => (result.1, (readCurrent ownerKey 10 result.2).map
        (fun driver => (driver.producer.1, queryInvoice revocationWorlds requirement driver,
          isStale afterView driver)))) = some (false, some (2, 1, true)) := by decide +kernel

theorem revocation_and_foreign_use_refuse_owned_writeback :
    let revoked := (Registration.revoke ownerKey handedPool).getD (none, handedPool)
    (readHeld ownerKey 10 revoked.2).isSome = true ∧
      (rearmOwned revocationWorlds requirement afterView ownerKey 10 revoked.2).isNone = true ∧
      (resumeOwnedGuard revocationWorlds requirement afterView 1 ownerKey 11 handedPool).isNone = true := by decide +kernel

theorem guard_progress_keeps_pending_admission_ticket :
    (rearmOwned revocationWorlds requirement afterView ownerKey 10 postedPool.2).map
      (fun result => (result.2.queue.pending, result.2.queue.ready.tasks, result.2.queue.cells 7)) =
        some ([ownerKey], [9], ⟨1, .runnable⟩) := by decide +kernel

theorem wrong_current_question_refuses_writeback :
    let other : AsyncWait.Identity := { ownerKey with serial := 502 }
    let mismatched : Pool := { handedPool with queue :=
      { handedPool.queue with keys := Function.update handedPool.queue.keys 7 (some other) } }
    (readHeld ownerKey 10 mismatched).isSome = true ∧
      (rearmOwned revocationWorlds requirement afterView ownerKey 10 mismatched).isNone = true := by decide +kernel

theorem retired_updated_guard_retains_its_reached_packet :
    let revoked := (Registration.revoke ownerKey readyPool).getD (none, readyPool)
    (readHeld ownerKey 10 revoked.2).map (queryInvoice revocationWorlds requirement) = some 2 ∧
      (resumeOwnedGuard revocationWorlds requirement afterView 1 ownerKey 10 revoked.2).isNone = true := by decide +kernel

theorem unfinished_owned_producer_cannot_rearm :
    let installed := ((Registration.install 1 7 501 captured waitingPool).getD (ownerKey, waitingPool)).2
    let acquired := (Registration.acquire 2 .exclusive 1 ownerKey 10 installed).getD installed
    (rearmOwned revocationWorlds requirement afterView ownerKey 10 acquired).map
      (fun result => (result.1, (readCurrent ownerKey 10 result.2).map (fun driver => driver.producer.1))) =
        some (false, some 1) := by decide +kernel

theorem guard_writeback_frames_another_acquired_source :
    let otherKey : AsyncWait.Identity := ⟨8, 1, 701⟩
    let installed := ((Registration.install 2 8 701 captured handedPool).getD (otherKey, handedPool)).2
    let acquired := (Registration.acquire 2 .lifetime 2 otherKey 21 installed).getD installed
    (readHeld otherKey 21 acquired).map (fun driver => driver.producer.1) = some 1 ∧
      (rearmOwned revocationWorlds requirement afterView ownerKey 10 acquired).bind
        (fun result => (readHeld otherKey 21 result.2).map (fun driver => driver.producer.1)) = some 1 := by decide +kernel

end OwnedGuardControls

end Reactive

namespace Controls

open Sources.AbsenceControls Sources.Commutative

/-- Reuse the ordinary correlated message/acknowledgement source fixture. -/
def label : Nat → Value
  | 0 => message .a
  | 2 => acknowledgement .a
  | _ => acknowledgement .b

def scanner := SourceReads.scan label {0, 1}
abbrev Captured := Capture (Answer := List (Sources.Subst Nat Value × List (Sources.Pick Nat Value))) scanner (Nat × Nat)
abbrev Pool := State Nat Nat Captured

def key : AsyncWait.Identity := ⟨7, 1, 99⟩
def otherKey : AsyncWait.Identity := ⟨7, 1, 100⟩
def nextKey : AsyncWait.Identity := ⟨7, 2, 100⟩
def inbox := EventPump.FiniteBurst.initial key

def start (fuel capacity : Nat) (tasks : List Nat := []) : Pool :=
  let initial : Pool := { empty capacity with queue :=
    { ready := ⟨capacity, tasks⟩, cells := fun _ => ⟨0, .idle⟩, bound := fun _ => none } }
  (installSource layer matcher label scanner joined Sources.AbsenceControls.empty (5, 17) 1 fuel 7 99 initial).getD (key, initial) |>.2

def captured (fuel capacity : Nat) (tasks : List Nat := []) : Pool :=
  (acquire 2 .exclusive 1 key 10 (start fuel capacity tasks)).getD (start fuel capacity tasks)
def checked (fuel capacity : Nat) (tasks : List Nat := []) : Pool :=
  (recheckSource scanner scanner key 10 (fun rows => !rows.isEmpty) (captured fuel capacity tasks)).getD (captured fuel capacity tasks)
def posted (capacity : Nat) (tasks : List Nat := []) : EventPump.Inbox × Pool :=
  (routeSource label (Commit.makeOne 2) scanner key 101 10 inbox (checked 3 capacity tasks)).getD (inbox, checked 3 capacity tasks)
def claimed : Pool :=
  { (posted 1).2 with queue := (QueueDelivery.run 1 (fun _ => []) (posted 1).2.queue).2 }
def retired : EventPump.Inbox × Option Captured × Pool :=
  (retire key (posted 1).1 claimed).getD ((posted 1).1, none, claimed)
def next : Pool :=
  ((installSource layer matcher label scanner joined Sources.AbsenceControls.empty (6, 18) 1 3 7 100 retired.2.2).getD (nextKey, retired.2.2)).2
def nextOwned : Pool := (acquire 2 .exclusive 1 nextKey 11 next).getD next

theorem installation_requires_acquisition :
    (start 3 1).queue.keys 7 = some key ∧
      (start 3 1).queue.cells 7 = ⟨1, .checking⟩ ∧
      readCurrent key 10 (start 3 1) = none ∧
      (readCurrent key 10 (captured 3 1)).map (fun source => (source.context, source.computation.1)) =
        some ((5, 17), 2) := by decide +kernel

theorem serial_collision_is_rejected :
    (acquire 2 .exclusive 1 otherKey 11 (captured 3 1)).isNone = true ∧
      readCurrent otherKey 10 (captured 3 1) = none ∧
      (revoke otherKey (captured 3 1)).isNone = true ∧
      (QueueDelivery.recordAndOffer otherKey (EventPump.FiniteBurst.initial otherKey)
        ⟨102, otherKey, 0⟩ claimed.queue).1.phase 102 = none ∧
      (QueueDelivery.acknowledgeClaimed otherKey
        (EventPump.record (EventPump.FiniteBurst.initial otherKey) ⟨102, otherKey, 0⟩)
        ⟨102, otherKey, 0⟩ claimed.queue).phase 102 = some .queued := by decide +kernel

theorem foreign_recheck_and_immediate_offer_are_inert :
    let source := (Sources.Query.Execution.execute layer matcher label scanner [] joined Sources.AbsenceControls.empty 3)
    let current := (start 3 1).queue
    (recheckQueue scanner otherKey (fun rows => !rows.isEmpty)
      (Cursor.ReadOnlyQuery.completed? scanner source.2) current).cells 7 = ⟨1, .checking⟩ ∧
      (QueueDelivery.offerCurrent otherKey (checked 3 1).queue).cells 7 = ⟨1, .armed⟩ := by decide +kernel

theorem question_identity_is_not_holder_authority :
    (acquire 2 .exclusive 2 key 11 (start 3 1)).isNone = true ∧
      readCurrent key 11 (start 3 1) = none ∧
      (installSource layer matcher label scanner joined Sources.AbsenceControls.empty
        (9, 99) 2 3 7 99 (start 3 1)).isNone = true := by decide +kernel

theorem live_source_owner_cannot_replace_queue_identity :
    let original := captured 3 1
    let spliced : Pool := { original with queue := { original.queue with
      keys := Function.update original.queue.keys key.owner (some otherKey) } }
    (readHeld key 10 spliced).isSome = true ∧ readCurrent key 10 spliced = none ∧
      (recheckSource scanner scanner key 10 (fun rows => !rows.isEmpty) spliced).isNone = true := by decide +kernel

theorem lifetime_is_not_current_source_authority :
    let borrowed := (acquire 2 .lifetime 1 key 10 (start 3 1)).getD (start 3 1)
    (readHeld key 10 borrowed).isSome = true ∧ readCurrent key 10 borrowed = none ∧
      (recheckSource scanner scanner key 10 (fun rows => !rows.isEmpty) borrowed).isNone = true := by decide +kernel

theorem actual_source_recheck_routes_to_handoff :
    (recheckSource scanner scanner key 10 (fun rows => !rows.isEmpty) (captured 3 1)).isSome = true ∧
      (checked 3 1).queue.cells 7 = ⟨1, .armed⟩ ∧
      (posted 1).1.phase 101 = some .queued ∧ claimed.queue.cells 7 = ⟨1, .claimed⟩ ∧
      (readCurrent key 10 claimed).map (fun source => (source.context, source.computation.1)) =
        some ((5, 17), 2) := by decide +kernel

theorem partial_source_cannot_arm :
    (checked 2 1).queue.cells 7 = ⟨1, .checking⟩ ∧
      ((routeSource label (Commit.makeOne 2) scanner key 101 10 inbox (checked 2 1)).getD
        (inbox, checked 2 1)).1.phase 101 = none := by decide +kernel

theorem nonjoining_arrival_creates_no_notice :
    ((routeSource label (Commit.makeOne 3) scanner key 101 10 inbox (checked 3 1)).getD
      (inbox, checked 3 1)).1.phase 101 = none := by decide +kernel

theorem changed_view_uses_immediate_retry :
    let retried := (recheckSource scanner (SourceReads.scan label {0, 1, 2}) key 10
      (fun rows => !rows.isEmpty) (captured 3 1)).getD (captured 3 1)
    retried.queue.cells 7 = ⟨1, .runnable⟩ ∧
      (QueueDelivery.offerCurrent key retried.queue).cells 7 = ⟨1, .queued⟩ ∧
      (readCurrent key 10 retried).map (fun source => (source.context, source.computation.1)) =
        some ((5, 17), 2) := by decide +kernel

theorem full_queue_preserves_source_and_notice :
    (posted 1 [9]).1.phase 101 = some .queued ∧
      (posted 1 [9]).2.queue.cells 7 = ⟨1, .runnable⟩ ∧
      (readCurrent key 10 (posted 1 [9]).2).map (fun source => (source.context, source.computation.1)) =
        some ((5, 17), 2) := by decide +kernel

theorem full_source_notification_enters_valid_backlog :
    QueueDelivery.Admission.Valid (posted 1 [9]).2.queue := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  intro registered member
  have backlog : (posted 1 [9]).2.queue.pending = [key] := by decide +kernel
  rw [backlog] at member
  have same := List.mem_singleton.mp member
  subst registered
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- This source reaches handoff under arbitrary continued foreign traffic,
with the same two paid reads and the same captured caller context. -/
theorem actual_source_gets_bounded_handoff (offered : Nat → List Nat) :
    ∃ slots ≤ 2,
      let after : Pool := { (posted 1 [9]).2 with
        queue := (QueueDelivery.Admission.run slots offered (posted 1 [9]).2.queue).2 }
      after.queue.cells 7 = ⟨1, .claimed⟩ ∧
        (readCurrent key 10 after).map (fun source => (source.context, source.computation.1)) =
          some ((5, 17), 2) := by
  obtain ⟨slots, bounded, claimed⟩ := QueueDelivery.Admission.pending_gets_bounded_handoff
    (posted 1 [9]).2.queue key offered full_source_notification_enters_valid_backlog (by decide +kernel) (by decide +kernel)
  have size : (posted 1 [9]).2.queue.ready.tasks.length + (posted 1 [9]).2.queue.pending.length = 2 := by decide +kernel
  refine ⟨slots, by simpa only [size] using bounded, claimed, ?_⟩
  simp only [readCurrent, QueueDelivery.Admission.run_keys]
  decide +kernel

theorem cancellation_disposes_backlog_but_keeps_acquired_capture :
    let revoked := (revoke key (posted 1 [9]).2).getD (none, (posted 1 [9]).2)
    let later : Pool := { revoked.2 with
      queue := (QueueDelivery.Admission.run 4 (fun _ => [9]) revoked.2.queue).2 }
    revoked.2.queue.pending = [] ∧ later.queue.cells 7 = ⟨1, .cancelled⟩ ∧
      readCurrent key 10 later = none ∧
      (readHeld key 10 later).map (fun source => (source.context, source.computation.1)) =
        some ((5, 17), 2) := by decide +kernel

theorem rearm_keeps_old_acquisition_distinct_from_new_source :
    retired.2.1.isNone = true ∧ retired.2.2.queue.keys 7 = none ∧
      retired.2.2.queue.cells 7 = ⟨2, .checking⟩ ∧
      (readHeld key 10 nextOwned).map (fun source => source.context) = some (5, 17) ∧
      readCurrent key 10 nextOwned = none ∧
      (readCurrent nextKey 11 nextOwned).map (fun source => source.context) = some (6, 18) := by decide +kernel

theorem final_old_release_never_releases_new_source :
    let released := (release key 10 nextOwned).getD (none, nextOwned)
    released.1.map (fun source => source.context) = some (5, 17) ∧
      readHeld key 10 released.2 = none ∧ (release key 10 released.2).isNone = true ∧
      (readCurrent nextKey 11 released.2).map (fun source => source.context) = some (6, 18) := by decide +kernel

def recipe (value : Nat) : ReadOnlyQuery.Program Nat Nat (List Nat) :=
  .read 0 fun reply => .pure (if reply = 0 then [] else [value])
def quiet (_ : Nat) : Nat := 0
def arrived (_ : Nat) : Nat := 1
def finishedGuard (value : Nat) : Capture (Answer := List Nat) quiet Unit :=
  ⟨Cursor.advance (Cursor.ReadOnlyQuery.provider quiet) Cursor.ReadOnlyQuery.client
    (Cursor.ReadOnlyQuery.readCharge quiet) 2 ⟨.unit, recipe value, []⟩, ()⟩

/-- Two distinct future behaviors have identical completed negative captures,
including context, read certificate and paid work. The outer driver must keep
its recipe or continuation separately; the finished query cannot recover it. -/
theorem completed_negative_capture_erases_restart_recipe :
    finishedGuard 1 = finishedGuard 2 ∧
      (ReadOnlyQuery.run arrived (recipe 1)).answer = [1] ∧
      (ReadOnlyQuery.run arrived (recipe 2)).answer = [2] := ⟨rfl, rfl, rfl⟩

theorem no_rearm_from_finished_guard_alone
    (rearm : Capture (Answer := List Nat) quiet Unit → List Nat) :
    ¬ (rearm (finishedGuard 1) = (ReadOnlyQuery.run arrived (recipe 1)).answer ∧
      rearm (finishedGuard 2) = (ReadOnlyQuery.run arrived (recipe 2)).answer) := by
  rintro ⟨first, second⟩
  rw [completed_negative_capture_erases_restart_recipe.1] at first
  have impossible := first.symm.trans second
  change [1] = [2] at impossible
  cases impossible

theorem revocation_preserves_memory_and_refuses_work :
    let revoked := (revoke key (checked 3 1)).getD (none, checked 3 1)
    revoked.2.queue.cells 7 = ⟨1, .cancelled⟩ ∧ revoked.1.isNone = true ∧
      (readHeld key 10 revoked.2).map (fun source => source.context) = some (5, 17) ∧
      readCurrent key 10 revoked.2 = none ∧
      (acquire 2 .lifetime 1 key 11 revoked.2).isNone = true ∧
      (routeSource label (Commit.makeOne 2) scanner key 101 10 inbox revoked.2).isNone = true := by decide +kernel

end Controls

end Registration

namespace Controls

def cut (store : Finset Nat) (fuel : Nat) :=
  ReadOnlyQuery.Retained.resume (scan id store) fuel
    (ReadOnlyQuery.Retained.begin SourceReads.Controls.adaptive)

def ready (rows : List Nat) : Bool := !rows.isEmpty

theorem completed_current_absence_arms :
    recheck id {2} 1 ready ⟨1, .checking⟩ (cut {2} 2) = ⟨1, .armed⟩ := by
  simp [recheck, recheckCompleted, cut, ready, ReadOnlyQuery.Retained.resume,
    ReadOnlyQuery.Retained.begin, ReadOnlyQuery.pausePrefix, SourceReads.Controls.adaptive,
    scan, regionOf, Finset.filter_singleton, ReadOnlyQuery.checkReads, step]

theorem unfinished_child_cannot_arm :
    recheck id {2} 1 ready ⟨1, .checking⟩ (cut {2} 1) = ⟨1, .checking⟩ := by
  simp [recheck, recheckCompleted, cut, ReadOnlyQuery.Retained.resume,
    ReadOnlyQuery.Retained.begin, ReadOnlyQuery.pausePrefix, SourceReads.Controls.adaptive,
    scan, regionOf, Finset.filter_singleton]

theorem changed_child_requests_retry :
    recheck id {2, 12} 1 ready ⟨1, .checking⟩ (cut {2} 2) = ⟨1, .runnable⟩ := by
  simp [recheck, recheckCompleted, cut, ReadOnlyQuery.Retained.resume,
    ReadOnlyQuery.Retained.begin, ReadOnlyQuery.pausePrefix, SourceReads.Controls.adaptive,
    scan, regionOf, Finset.filter_singleton, Finset.filter_insert, ReadOnlyQuery.checkReads, step]

theorem unrelated_publication_keeps_local_recheck :
    recheck id {2, 99} 1 ready ⟨1, .checking⟩ (cut {2} 2) = ⟨1, .armed⟩ := by
  simp [recheck, recheckCompleted, cut, ready, ReadOnlyQuery.Retained.resume,
    ReadOnlyQuery.Retained.begin, ReadOnlyQuery.pausePrefix, SourceReads.Controls.adaptive,
    scan, regionOf, Finset.filter_singleton, Finset.filter_insert, ReadOnlyQuery.checkReads, step]

theorem matching_arrival_makes_source_ready :
    ready (ReadOnlyQuery.run (scan id {2, 12}) SourceReads.Controls.adaptive).answer = true := by
  simp [ready, ReadOnlyQuery.run, SourceReads.Controls.adaptive, scan, regionOf,
    Finset.filter_singleton, Finset.filter_insert]

theorem matching_arrival_produces_notice :
    notice id (Commit.makeOne 12) 1 (cut {2} 2).1 = some 1 := by
  apply becomes_ready_requires_notice id {2} {2} 1 2 SourceReads.Controls.adaptive ready
    (Commit.makeOne 12) completed_current_absence_arms
  have afterStore : fire {2} (Commit.makeOne 12 : Commit Nat Nat) = {2, 12} := by decide
  rw [afterStore]
  exact matching_arrival_makes_source_ready

/-- Routing a notice is insufficient if nobody delivers it. The same ready
source leaves the waiter asleep until its notification debt is serviced. -/
theorem notice_creation_is_not_delivery :
    notice id (Commit.makeOne 12) 1 (cut {2} 2).1 = some 1 ∧
      ready (ReadOnlyQuery.run (scan id {2, 12}) SourceReads.Controls.adaptive).answer = true ∧
      step ⟨1, .armed⟩ (.park 1) = ⟨1, .asleep⟩ ∧
      step (deliver ⟨1, .armed⟩ (notice id (Commit.makeOne 12) 1 (cut {2} 2).1)) (.park 1) =
        ⟨1, .runnable⟩ := by
  rw [matching_arrival_produces_notice, matching_arrival_makes_source_ready]
  simp [deliver, step]

theorem old_registration_cannot_arm_reused_cell :
    recheck id {2} 1 ready ⟨2, .checking⟩ (cut {2} 2) = ⟨2, .checking⟩ :=
  stale_registration_ignored id {2} 1 ready ⟨2, .checking⟩ _ (by decide)

#guard notice id (Commit.makeOne 12) 1 (cut {2} 2).1 == some 1
#guard (recheck id {2, 12} 1 ready ⟨1, .checking⟩ (cut {2} 2)).phase == .runnable
#guard (recheck id {2} 1 ready ⟨1, .checking⟩ (cut {2} 1)).phase == .checking
#guard (step (deliver ⟨1, .armed⟩ (notice id (Commit.makeOne 12) 1 (cut {2} 2).1))
  (.park 1)).phase == .runnable

end Controls

end Enrollment

end SourceReads

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SerializedPublication
