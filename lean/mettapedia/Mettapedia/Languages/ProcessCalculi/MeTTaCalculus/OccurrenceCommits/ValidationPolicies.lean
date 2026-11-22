import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# Validation policies: a lattice of checks, what each admits, and "trust me"

A **round** commits proposals that were all matched at one snapshot, one after another. Before a
proposal commits, its **mode** says what is checked against the current store (`Permits`):

* `takes`: everything it takes is still present (a per-occurrence claim);
* `keeps`: everything it keeps is still present;
* `regions`: every predicate query still holds (a per-region epoch).

A fresh identity is always fresh: the allocator is not a policy. A mode is a set of checks, so
the modes form the Boolean lattice of subsets of `{takes, keeps, regions}`, and permission is
antitone in it (`permits_mono`, `Round.mono`): more checks admit fewer rounds. A proposal may also
be dropped (aborted). The chain that matters is the classical one of isolation levels:

| mode | checks | admits |
|---|---|---|
| `unchecked` | none | double takes (`Controls.unchecked_double_take`) |
| `snapshot` | takes | write skew, never a double take (`Controls.snapshot_write_skew`, `no_double_take`) |
| `claims` | takes, keeps | an absence race through predicate queries (`Controls.claims_absence_race`) |
| `serializable` | all | exactly the executable subsequences (`round_serializable_iff`) |

`snapshot` is snapshot isolation at the grain of occurrences; `claims` is the claims wave of
`PatternFootprints.Claims`, which refuses a taker beside a reader of the same occurrence. Each
separating control is a round that the weaker mode admits and the stronger refuses.

## What a snapshot round can produce, exactly

For a clash-free wave, a snapshot round can commit any sub-collection in any order, and reaches
its combined effect (`snapshotOutcome_iff`). A serializable round reaches the combined effect of a
sub-collection exactly when that sub-collection's precedence relation is acyclic
(`serialOutcome_iff`). So, when every proposal makes something (distinct effects):

* **an outcome of a snapshot round is anomalous exactly when the committed sub-collection
  contains a precedence cycle** (`serialOutcome_effect_iff_acyclic`);
* **"trust me", run at the snapshot level, is exact under the obligation that the precedence
  relation is acyclic**: every snapshot outcome is then a serializable outcome
  (`snapshot_refines_of_acyclic`), and conversely the full snapshot outcome is serializable only
  when it is (`acyclic_of_full_snapshot_serial`). A violated promise stays inside the snapshot
  outcomes: no double take (`no_double_take`) and no torn commit (a round commits whole
  proposals).

Counting follows from the characterization (the counts are arithmetic on it, not Lean theorems):
with `n` proposals, a snapshot round has one outcome per sub-collection, and the anomalous ones are
the sub-collections containing a cycle. One write-skew pair among `n` proposals adds `2^(n-2)`
outcomes; `k` disjoint pairs multiply the count of outcomes by `(4/3)^k`. The refinement applies
to waves that are acyclic without being pairwise independent (`Controls.trustMe_instance`,
`Controls.fullSnapshot_instance`).

## Agreement: where a cheaper mode is exact

* **Monotone proposals** (keep and make only): every mode admits the same rounds
  (`round_monotone_of_sublist`). The monotone fragment is a theorem about all modes, not a mode.
* **Proposals that keep nothing and have no predicate query** (job claims, mail `next`): `snapshot`
  permits exactly what `serializable` permits (`permits_snapshot_iff_of_readFree`).
* **Proposals without predicate queries**: `claims` permits exactly what `serializable` permits
  (`permits_claims_iff_of_positive`).
* **Pairwise independent waves** (pre-partitioned work): an unchecked round is a serializable
  round (`unchecked_round_serializable_of_independent`).

## Mixed modes

Each proposal may carry its own mode. A round under mixed modes is a round under the meet of the
modes (`Round.mono`), and no better in general: with one serializable and one snapshot proposal,
write skew still happens when the snapshot proposal commits second
(`Controls.mixed_write_skew`). The serializable proposal itself never commits on a stale read;
the guarantee for the pair is the meet.

## Optimistic validation over-aborts

Validating each commit when it comes refuses the taker-then-reader order of a reader and a taker,
though the pair is a serializable wave (`Controls.optimistic_refuses_serializable_pair`). The
wave-level test, acyclic precedence, is exact; per-commit validation is sound and coarser.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

/-- What a commit may be checked for before it publishes. -/
inductive Check where
  | takes
  | keeps
  | regions
  deriving DecidableEq, Repr

instance : Fintype Check :=
  ⟨{Check.takes, Check.keeps, Check.regions}, fun c => by cases c <;> simp⟩

/-! Named modes. -/
namespace Mode

/-- No validation. -/
def unchecked : Finset Check := ∅

/-- Snapshot isolation at the grain of occurrences: takes only. -/
def snapshot : Finset Check := {Check.takes}

/-- Claims: takes and keeps, not predicate queries. -/
def claims : Finset Check := {Check.takes, Check.keeps}

/-- Everything. -/
def serializable : Finset Check := Finset.univ

theorem chain : unchecked ⊆ snapshot ∧ snapshot ⊆ claims ∧ claims ⊆ serializable :=
  ⟨Finset.empty_subset _, by simp [snapshot, claims], Finset.subset_univ _⟩

end Mode

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- What a mode permits: the checks it makes hold at the current store, and what the commit makes
is fresh there. -/
def Permits (label : O → R) (mode : Finset Check) (store : Finset O) (c : Commit O R) : Prop :=
  (Check.takes ∈ mode → c.taken ⊆ store) ∧ (Check.keeps ∈ mode → c.kept ⊆ store) ∧
    (Check.regions ∈ mode → ∀ read ∈ c.queries, read.Holds label store) ∧ Disjoint c.made store

omit [DecidableEq O] in
/-- More checks permit less. -/
theorem permits_mono {label : O → R} {weaker stronger : Finset Check} (sub : weaker ⊆ stronger)
    {store : Finset O} {c : Commit O R} (permits : Permits label stronger store c) :
    Permits label weaker store c :=
  ⟨fun member => permits.1 (sub member), fun member => permits.2.1 (sub member),
    fun member => permits.2.2.1 (sub member), permits.2.2.2⟩

omit [DecidableEq O] in
/-- Under every check, permission is enabling (for a commit that does not keep what it takes). -/
theorem permits_serializable_iff {label : O → R} {store : Finset O} {c : Commit O R}
    (apart : Disjoint c.taken c.kept) :
    Permits label Mode.serializable store c ↔ Enabled label store c := by
  constructor
  · rintro ⟨takes, keeps, regions, fresh⟩
    exact ⟨takes (by simp [Mode.serializable]), keeps (by simp [Mode.serializable]), apart, fresh,
      regions (by simp [Mode.serializable])⟩
  · intro enabled
    exact ⟨fun _ => enabled.taken_subset, fun _ => enabled.kept_subset,
      fun _ => enabled.queries_hold, enabled.fresh⟩

/-- A round: proposals are committed, when their mode permits it at the current store, or
dropped. `Round label mode store proposals committed final`. -/
inductive Round (label : O → R) (mode : Commit O R → Finset Check) :
    Finset O → List (Commit O R) → List (Commit O R) → Finset O → Prop
  | done (store : Finset O) : Round label mode store [] [] store
  | commit {store : Finset O} {c : Commit O R} {rest committed : List (Commit O R)}
      {final : Finset O} (permits : Permits label (mode c) store c)
      (after : Round label mode (fire store c) rest committed final) :
      Round label mode store (c :: rest) (c :: committed) final
  | drop {store : Finset O} {c : Commit O R} {rest committed : List (Commit O R)}
      {final : Finset O} (after : Round label mode store rest committed final) :
      Round label mode store (c :: rest) committed final

namespace Round

variable {label : O → R} {mode : Commit O R → Finset Check}

theorem final_eq {store final : Finset O} {proposals committed : List (Commit O R)}
    (round : Round label mode store proposals committed final) : final = fireList store committed := by
  induction round with
  | done => rfl
  | commit _ _ ih => exact ih
  | drop _ ih => exact ih

theorem sublist {store final : Finset O} {proposals committed : List (Commit O R)}
    (round : Round label mode store proposals committed final) : committed.Sublist proposals := by
  induction round with
  | done => exact List.Sublist.slnil
  | commit _ _ ih => exact ih.cons_cons _
  | drop _ ih => exact ih.cons _

/-- A round under stronger modes is a round under weaker ones. -/
theorem mono {weaker stronger : Commit O R → Finset Check} (sub : ∀ c, weaker c ⊆ stronger c)
    {store final : Finset O} {proposals committed : List (Commit O R)}
    (round : Round label stronger store proposals committed final) :
    Round label weaker store proposals committed final := by
  induction round with
  | done store => exact .done store
  | commit permits _ ih => exact .commit (permits_mono (sub _) permits) ih
  | drop _ ih => exact .drop ih

end Round

/-- **A serializable round commits exactly an executable subsequence.** -/
theorem round_serializable_iff {label : O → R} {store final : Finset O}
    {proposals committed : List (Commit O R)}
    (apart : ∀ c ∈ proposals, Disjoint c.taken c.kept) :
    Round label (fun _ => Mode.serializable) store proposals committed final ↔
      committed.Sublist proposals ∧ Executable label store committed ∧
        final = fireList store committed := by
  constructor
  · intro round
    refine ⟨round.sublist, ?_, round.final_eq⟩
    induction round with
    | done store => exact .nil store
    | @commit store c rest committed final permits _ ih =>
        exact .cons ((permits_serializable_iff (apart c List.mem_cons_self)).mp permits)
          (ih fun d member => apart d (List.mem_cons_of_mem _ member))
    | drop _ ih => exact ih fun d member => apart d (List.mem_cons_of_mem _ member)
  · rintro ⟨sub, executable, rfl⟩
    induction sub generalizing store with
    | slnil => cases executable; exact .done _
    | cons c _ ih => exact .drop (ih (fun d member => apart d (List.mem_cons_of_mem _ member))
        executable)
    | cons_cons c _ ih =>
        rw [executable_cons_iff] at executable
        exact .commit ((permits_serializable_iff (apart c List.mem_cons_self)).mpr executable.1)
          (ih (fun d member => apart d (List.mem_cons_of_mem _ member)) executable.2)

/-! ## Claims rounds on a wave -/

section SnapshotRounds

variable {label : O → R} {store : Finset O}

/-- **Rounds that commit a subsequence.** If every proposal of a wave is permitted at every
store that a clash-free prefix of the wave reaches, a round can commit any subsequence of the
proposals, in their order. -/
theorem round_of_sublist {mode : Commit O R → Finset Check} {U : List (Commit O R)}
    (permitted : ∀ (pre : List (Commit O R)) (c : Commit O R), c ∈ U → (∀ e ∈ pre, e ∈ U) →
      (∀ e ∈ pre, ¬ Clash e c) → Permits label (mode c) (fireList store pre) c)
    {proposals committed : List (Commit O R)} (inU : ∀ c ∈ proposals, c ∈ U)
    (noClash : proposals.Pairwise (fun e d => ¬ Clash e d))
    (sub : committed.Sublist proposals) :
    Round label mode store proposals committed (fireList store committed) := by
  suffices general : ∀ (pre : List (Commit O R)), (∀ e ∈ pre, e ∈ U) →
      (∀ e ∈ pre, ∀ d ∈ proposals, ¬ Clash e d) →
      Round label mode (fireList store pre) proposals committed
        (fireList (fireList store pre) committed) by
    simpa using general [] (by simp) (by simp)
  induction sub with
  | slnil => intro pre _ _; exact .done _
  | @cons committedTail rest c _ ih =>
      intro pre preU apartPre
      exact .drop (ih (fun d member => inU d (List.mem_cons_of_mem _ member))
        (List.pairwise_cons.mp noClash).2 pre preU
        fun e inPre d inRest => apartPre e inPre d (List.mem_cons_of_mem _ inRest))
  | @cons_cons committedTail rest c _ ih =>
      intro pre preU apartPre
      have permits := permitted pre c (inU c List.mem_cons_self) preU
        fun e inPre => apartPre e inPre c List.mem_cons_self
      have preU' : ∀ e ∈ pre ++ [c], e ∈ U := by
        intro e member
        rcases List.mem_append.mp member with inPre | inC
        · exact preU e inPre
        · rw [List.mem_singleton] at inC; subst inC; exact inU e List.mem_cons_self
      have apartNext : ∀ e ∈ pre ++ [c], ∀ d ∈ rest, ¬ Clash e d := by
        intro e member d inRest
        rcases List.mem_append.mp member with inPre | inC
        · exact apartPre e inPre d (List.mem_cons_of_mem _ inRest)
        · rw [List.mem_singleton] at inC; subst inC
          exact (List.pairwise_cons.mp noClash).1 d inRest
      have step := ih (fun d member => inU d (List.mem_cons_of_mem _ member))
        (List.pairwise_cons.mp noClash).2 (pre ++ [c]) preU' apartNext
      rw [fireList_append] at step
      exact .commit permits (by simpa [fireList_cons] using step)

/-- On a wave, a snapshot check passes at every store a clash-free prefix reaches. -/
theorem permits_snapshot_of_wave {U : List (Commit O R)} (matchedU : MatchedAt store U)
    (pre : List (Commit O R)) (c : Commit O R) (inU : c ∈ U) (preU : ∀ e ∈ pre, e ∈ U)
    (apartPre : ∀ e ∈ pre, ¬ Clash e c) :
    Permits label Mode.snapshot (fireList store pre) c := by
  have matchedPre : MatchedAt store pre := fun e member => matchedU e (preU e member)
  obtain ⟨takenC, freshC⟩ := matchedU c inU
  rw [fireList_eq_fire_effectOf matchedPre]
  refine ⟨fun _ o taken => mem_fire.mpr (Or.inl ⟨takenC taken, fun inEffect => ?_⟩),
    fun member => by simp [Mode.snapshot] at member,
    fun member => by simp [Mode.snapshot] at member, ?_⟩
  · obtain ⟨e, inPre, takenE⟩ := mem_takenOf.mp inEffect
    exact apartPre e inPre (Or.inl (Finset.not_disjoint_iff.mpr ⟨o, takenE, taken⟩))
  · refine Finset.disjoint_left.mpr fun o made inFire => ?_
    rcases mem_fire.mp inFire with ⟨inStore, _⟩ | madeEffect
    · exact Finset.disjoint_left.mp freshC made inStore
    · obtain ⟨e, inPre, madeE⟩ := mem_madeOf.mp madeEffect
      exact apartPre e inPre (Or.inr (Finset.not_disjoint_iff.mpr ⟨o, madeE, made⟩))

/-- **A snapshot round on a clash-free wave can commit any subsequence, in its order.** -/
theorem round_snapshot_of_sublist {proposals committed : List (Commit O R)}
    (matched : MatchedAt store proposals)
    (noClash : proposals.Pairwise (fun e d => ¬ Clash e d))
    (sub : committed.Sublist proposals) :
    Round label (fun _ => Mode.snapshot) store proposals committed (fireList store committed) :=
  round_of_sublist (permits_snapshot_of_wave matched) (fun _ member => member) noClash sub

/-- The outcomes of snapshot rounds over orders of a wave. -/
def SnapshotOutcome (label : O → R) (store : Finset O) (W : List (Commit O R)) (final : Finset O) :
    Prop :=
  ∃ l committed, l.Perm W ∧ Round label (fun _ => Mode.snapshot) store l committed final

/-- The outcomes of serializable rounds over orders of a wave. -/
def SerialOutcome (label : O → R) (store : Finset O) (W : List (Commit O R)) (final : Finset O) :
    Prop :=
  ∃ l committed, l.Perm W ∧ Round label (fun _ => Mode.serializable) store l committed final

theorem pairwise_of_subperm {α : Type*} {rel : α → α → Prop} (symm : ∀ {x y}, rel x y → rel y x)
    {A W : List α} (subperm : A.Subperm W) (pairwise : W.Pairwise rel) : A.Pairwise rel := by
  obtain ⟨A', perm, sub⟩ := subperm
  exact (perm.pairwise_iff symm).mp (pairwise.sublist sub)

/-- A sub-collection of a wave, rearranged, extends to a rearrangement of the whole wave. -/
theorem exists_perm_of_subperm {α : Type*} {A W : List α} (subperm : A.Subperm W) :
    ∃ rest, (A ++ rest).Perm W := by
  obtain ⟨A', perm, sub⟩ := subperm
  obtain ⟨rest, restPerm⟩ := sub.exists_perm_append
  exact ⟨rest, ((perm.symm.append_right rest).trans restPerm.symm)⟩

/-- A round can commit a list and then drop everything else. -/
theorem round_append_drop {label : O → R} {mode : Commit O R → Finset Check} {store final : Finset O}
    {A committed : List (Commit O R)} (round : Round label mode store A committed final)
    (rest : List (Commit O R)) : Round label mode store (A ++ rest) committed final := by
  induction round with
  | done store =>
      induction rest with
      | nil => exact .done store
      | cons c rest ih => exact .drop ih
  | commit permits _ ih => exact .commit permits ih
  | drop _ ih => exact .drop ih

/-- **The outcomes of snapshot rounds on a clash-free wave are the combined effects of its
sub-collections.** -/
theorem snapshotOutcome_iff {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) {final : Finset O} :
    SnapshotOutcome label store W final ↔ ∃ A, A.Subperm W ∧ final = fire store (effectOf A) := by
  constructor
  · rintro ⟨l, committed, perm, round⟩
    have sub := round.sublist
    refine ⟨committed, (sub.subperm).trans perm.subperm, ?_⟩
    rw [round.final_eq]
    exact fireList_eq_fire_effectOf fun c member =>
      (MatchedAt.of_enabled enabled) c (perm.subset (sub.subset member))
  · rintro ⟨A, subperm, rfl⟩
    obtain ⟨rest, perm⟩ := exists_perm_of_subperm subperm
    have matched : MatchedAt store (A ++ rest) := fun c member =>
      (MatchedAt.of_enabled enabled) c (perm.subset member)
    have noClash' : (A ++ rest).Pairwise (fun e d => ¬ Clash e d) :=
      (perm.pairwise_iff fun {x y} noXY clash => noXY clash.symm).mpr noClash
    refine ⟨A ++ rest, A, perm, ?_⟩
    have round := round_snapshot_of_sublist (label := label) matched noClash'
      (List.sublist_append_left A rest)
    rw [fireList_eq_fire_effectOf fun c member => matched c (List.mem_append_left _ member)] at round
    exact round

theorem acyclic_of_subset {label : O → R} {A W : List (Commit O R)} (sub : ∀ c ∈ A, c ∈ W)
    (acyclic : Acyclic label W) : Acyclic label A := by
  intro c cycle
  have lift : ∀ {a b}, Relation.TransGen (BeforeOn label A) a b →
      Relation.TransGen (BeforeOn label W) a b := by
    intro a b path
    induction path with
    | single edge => exact .single ⟨sub _ edge.1, sub _ edge.2.1, edge.2.2⟩
    | tail _ edge ih => exact ih.tail ⟨sub _ edge.1, sub _ edge.2.1, edge.2.2⟩
  exact acyclic c (lift cycle)

theorem acyclic_congr {label : O → R} {A B : List (Commit O R)} (same : ∀ c, c ∈ A ↔ c ∈ B)
    (acyclic : Acyclic label A) : Acyclic label B :=
  acyclic_of_subset (fun c member => (same c).mpr member) acyclic

/-- **The outcomes of serializable rounds are the combined effects of the acyclic
sub-collections.** -/
theorem serialOutcome_iff {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) {final : Finset O} :
    SerialOutcome label store W final ↔
      ∃ A, A.Subperm W ∧ Acyclic label A ∧ final = fire store (effectOf A) := by
  have apart : ∀ {l : List (Commit O R)}, l.Perm W → ∀ c ∈ l, Disjoint c.taken c.kept :=
    fun perm c member => (enabled c (perm.subset member)).apart
  constructor
  · rintro ⟨l, committed, perm, round⟩
    obtain ⟨sub, executable, rfl⟩ := (round_serializable_iff (apart perm)).mp round
    have subperm : committed.Subperm W := sub.subperm.trans perm.subperm
    have enabledA : ∀ c ∈ committed, Enabled label store c := fun c member =>
      enabled c (subperm.subset member)
    refine ⟨committed, subperm, ?_, fireList_eq_fire_effectOf (MatchedAt.of_enabled enabledA)⟩
    exact (exists_executable_perm_iff_acyclic enabledA
      (pairwise_of_subperm (fun noXY clash => noXY clash.symm) subperm noClash)).mp
      ⟨committed, List.Perm.refl _, executable⟩
  · rintro ⟨A, subperm, acyclic, rfl⟩
    have enabledA : ∀ c ∈ A, Enabled label store c := fun c member => enabled c (subperm.subset member)
    obtain ⟨order, orderPerm, executable⟩ := (exists_executable_perm_iff_acyclic enabledA
      (pairwise_of_subperm (fun noXY clash => noXY clash.symm) subperm noClash)).mpr acyclic
    obtain ⟨rest, perm⟩ := exists_perm_of_subperm (orderPerm.subperm.trans subperm)
    refine ⟨order ++ rest, order, perm, ?_⟩
    have enabledOrder : ∀ c ∈ order, Enabled label store c := fun c member =>
      enabledA c (orderPerm.subset member)
    have round := (round_serializable_iff (label := label) (store := store)
      (final := fireList store order) (proposals := order) (committed := order)
      (fun c member => (enabledOrder c member).apart)).mpr ⟨List.Sublist.refl _, executable, rfl⟩
    rw [fireList_eq_fire_effectOf (MatchedAt.of_enabled enabledOrder),
      show effectOf order = effectOf A by
        simp [effectOf, takenOf_perm orderPerm, madeOf_perm orderPerm]] at round
    exact round_append_drop round rest

/-- **"Trust me" is exact under acyclic precedence**: every outcome of a snapshot round is an
outcome of a serializable round. -/
theorem snapshot_refines_of_acyclic {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) (acyclic : Acyclic label W)
    {final : Finset O} (claims : SnapshotOutcome label store W final) :
    SerialOutcome label store W final := by
  obtain ⟨A, subperm, rfl⟩ := (snapshotOutcome_iff enabled noClash).mp claims
  exact (serialOutcome_iff enabled noClash).mpr
    ⟨A, subperm, acyclic_of_subset (fun c member => subperm.subset member) acyclic, rfl⟩

/-- Distinct effects: every proposal makes something. -/
def MakesSomething (W : List (Commit O R)) : Prop := ∀ c ∈ W, c.made.Nonempty

/-- With distinct effects, the combined effect of a sub-collection determines its members. -/
theorem members_of_effect_eq {W A B : List (Commit O R)} (matched : MatchedAt store W)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) (makes : MakesSomething W)
    (subA : A.Subperm W) (subB : B.Subperm W)
    (same : fire store (effectOf A) = fire store (effectOf B)) : ∀ c, c ∈ A ↔ c ∈ B := by
  -- The made part of a combined effect is the part outside the snapshot.
  have madePart : ∀ {X : List (Commit O R)}, X.Subperm W →
      ∀ o, o ∈ madeOf X ↔ o ∈ fire store (effectOf X) ∧ o ∉ store := by
    intro X subX o
    constructor
    · intro made
      obtain ⟨c, inX, madeC⟩ := mem_madeOf.mp made
      exact ⟨mem_fire.mpr (Or.inr made), fun inStore =>
        Finset.disjoint_left.mp (matched c (subX.subset inX)).2 madeC inStore⟩
    · rintro ⟨inFire, notStore⟩
      rcases mem_fire.mp inFire with ⟨inStore, _⟩ | made
      · exact absurd inStore notStore
      · exact made
  have madeEq : ∀ o, o ∈ madeOf A ↔ o ∈ madeOf B := fun o => by
    rw [madePart subA, madePart subB, same]
  -- A proposal whose made part meets the combined made part of a sub-collection belongs to it.
  have belongs : ∀ {X : List (Commit O R)}, X.Subperm W → ∀ c ∈ W, ∀ o ∈ c.made,
      o ∈ madeOf X → c ∈ X := by
    intro X subX c inW o madeC madeX
    obtain ⟨c', inX, madeC'⟩ := mem_madeOf.mp madeX
    by_contra notIn
    have different : c ≠ c' := fun equal => notIn (equal ▸ inX)
    have inW' := subX.subset inX
    have apart : ¬ Clash c c' := noClash_of_mem noClash inW inW' different
    exact apart (Or.inr (Finset.not_disjoint_iff.mpr ⟨o, madeC, madeC'⟩))
  intro c
  constructor
  · intro inA
    obtain ⟨o, madeC⟩ := makes c (subA.subset inA)
    exact belongs subB c (subA.subset inA) o madeC ((madeEq o).mp (mem_madeOf.mpr ⟨c, inA, madeC⟩))
  · intro inB
    obtain ⟨o, madeC⟩ := makes c (subB.subset inB)
    exact belongs subA c (subB.subset inB) o madeC ((madeEq o).mpr (mem_madeOf.mpr ⟨c, inB, madeC⟩))

/-- **Distinct effects decide anomalies.** When every proposal makes something, the combined
effect of a sub-collection is a serializable outcome exactly when that sub-collection's
precedence relation is acyclic. The anomalous outcomes of a snapshot round are the effects of the
sub-collections that contain a precedence cycle. -/
theorem serialOutcome_effect_iff_acyclic {W A : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (noClash : W.Pairwise (fun e d => ¬ Clash e d))
    (makes : MakesSomething W) (subA : A.Subperm W) :
    SerialOutcome label store W (fire store (effectOf A)) ↔ Acyclic label A := by
  constructor
  · intro serial
    obtain ⟨B, subB, acyclicB, same⟩ := (serialOutcome_iff enabled noClash).mp serial
    exact acyclic_congr (fun c => (members_of_effect_eq (MatchedAt.of_enabled enabled) noClash
      makes subA subB same c).symm) acyclicB
  · intro acyclic
    exact (serialOutcome_iff enabled noClash).mpr ⟨A, subA, acyclic, rfl⟩

/-- **The full snapshot outcome is serializable only under acyclic precedence.** With distinct
effects, committing every proposal without validating reads reaches a serializable store exactly
when the wave's precedence relation is acyclic. So acyclicity is the exact obligation of "trust
me" with the snapshot fallback. -/
theorem acyclic_of_full_snapshot_serial {W : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (noClash : W.Pairwise (fun e d => ¬ Clash e d))
    (makes : MakesSomething W)
    (serial : SerialOutcome label store W (fire store (effectOf W))) : Acyclic label W :=
  (serialOutcome_effect_iff_acyclic enabled noClash makes (List.Subperm.refl W)).mp serial

/-- **The bounded fallback: per-occurrence atomicity.** In a round over a wave whose modes all
check takes, no occurrence is taken twice: the committed proposals take apart. -/
theorem no_double_take {mode : Commit O R → Finset Check} {proposals committed : List (Commit O R)}
    {final : Finset O} (matched : MatchedAt store proposals)
    (checksTakes : ∀ c ∈ proposals, Check.takes ∈ mode c)
    (round : Round label mode store proposals committed final) :
    committed.Pairwise (fun e d => Disjoint e.taken d.taken) := by
  suffices general : ∀ (pre : List (Commit O R)) (l committed : List (Commit O R)) (final : Finset O),
      MatchedAt store pre → MatchedAt store l → (∀ c ∈ l, Check.takes ∈ mode c) →
      Round label mode (fireList store pre) l committed final →
      (∀ e ∈ pre, ∀ d ∈ committed, Disjoint e.taken d.taken) ∧
        committed.Pairwise (fun e d => Disjoint e.taken d.taken) by
    exact (general [] proposals committed final (by simp [MatchedAt]) matched checksTakes
      (by simpa using round)).2
  intro pre l
  induction l generalizing pre with
  | nil =>
      intro committed final _ _ _ round
      cases round
      simp
  | cons c rest ih =>
      intro committed final matchedPre matchedL checks round
      have matchedRest : MatchedAt store rest := fun d member => matchedL d (List.mem_cons_of_mem _ member)
      have checksRest : ∀ d ∈ rest, Check.takes ∈ mode d := fun d member =>
        checks d (List.mem_cons_of_mem _ member)
      cases round with
      | drop after => exact ih pre committed final matchedPre matchedRest checksRest after
      | @commit _ _ _ committedTail _ permits after =>
          have matchedNext : MatchedAt store (pre ++ [c]) := by
            intro e member
            rcases List.mem_append.mp member with inPre | inC
            · exact matchedPre e inPre
            · rw [List.mem_singleton] at inC; subst inC; exact matchedL e List.mem_cons_self
          have afterNext : Round label mode (fireList store (pre ++ [c])) rest committedTail final := by
            rw [fireList_append]; simpa using after
          obtain ⟨apartNext, pairwiseTail⟩ :=
            ih (pre ++ [c]) committedTail final matchedNext matchedRest checksRest afterNext
          have takenPresent := permits.1 (checks c List.mem_cons_self)
          rw [fireList_eq_fire_effectOf matchedPre] at takenPresent
          have apartPre : ∀ e ∈ pre, Disjoint e.taken c.taken := by
            intro e inPre
            refine Finset.disjoint_left.mpr fun o takenE takenC => ?_
            rcases mem_fire.mp (takenPresent takenC) with ⟨_, notTaken⟩ | made
            · exact notTaken (mem_takenOf.mpr ⟨e, inPre, takenE⟩)
            · obtain ⟨e', inPre', madeE'⟩ := mem_madeOf.mp made
              exact Finset.disjoint_left.mp (matchedPre e' inPre').2 madeE'
                ((matchedL c List.mem_cons_self).1 takenC)
          refine ⟨?_, List.pairwise_cons.mpr ⟨fun d inTail =>
            apartNext c (List.mem_append_right _ (List.mem_singleton_self c)) d inTail, pairwiseTail⟩⟩
          intro e inPre d member
          rcases List.mem_cons.mp member with rfl | inTail
          · exact apartPre e inPre
          · exact apartNext e (List.mem_append_left _ inPre) d inTail

/-! ## Agreement: where a cheaper mode is exact -/

omit [DecidableEq O] in
/-- For proposals that keep nothing and have no predicate query, `snapshot` permits exactly what
`serializable` permits. -/
theorem permits_snapshot_iff_of_readFree {T : Finset O} {c : Commit O R} (keptEmpty : c.kept = ∅)
    (queriesEmpty : c.queries = []) :
    Permits label Mode.snapshot T c ↔ Permits label Mode.serializable T c := by
  constructor
  · rintro ⟨takes, -, -, fresh⟩
    exact ⟨fun _ => takes (by simp [Mode.snapshot]), fun _ => by simp [keptEmpty],
      fun _ => by simp [queriesEmpty], fresh⟩
  · exact permits_mono (Mode.chain.2.1.trans Mode.chain.2.2)

omit [DecidableEq O] in
/-- For proposals without predicate queries, `claims` permits exactly what `serializable`
permits. -/
theorem permits_claims_iff_of_positive {T : Finset O} {c : Commit O R}
    (queriesEmpty : c.queries = []) :
    Permits label Mode.claims T c ↔ Permits label Mode.serializable T c := by
  constructor
  · rintro ⟨takes, keeps, -, fresh⟩
    exact ⟨fun _ => takes (by simp [Mode.claims]), fun _ => keeps (by simp [Mode.claims]),
      fun _ => by simp [queriesEmpty], fresh⟩
  · exact permits_mono Mode.chain.2.2

/-- Monotone commits keep what is present: firing a prefix of them keeps the snapshot. -/
theorem subset_fireList_of_monotone {pre : List (Commit O R)} (monotone : ∀ e ∈ pre, e.Monotone) :
    store ⊆ fireList store pre := by
  induction pre generalizing store with
  | nil => exact le_rfl
  | cons e rest ih =>
      exact (subset_fire_of_monotone (monotone e List.mem_cons_self)).trans
        (ih fun d member => monotone d (List.mem_cons_of_mem _ member))

/-- **Every mode admits the same rounds of monotone proposals**: any subsequence of a clash-free
monotone wave is a round under every mode. The monotone fragment is a theorem about all modes. -/
theorem round_monotone_of_sublist {mode : Commit O R → Finset Check}
    {proposals committed : List (Commit O R)} (enabled : ∀ c ∈ proposals, Enabled label store c)
    (monotone : ∀ c ∈ proposals, c.Monotone)
    (noClash : proposals.Pairwise (fun e d => ¬ Clash e d))
    (sub : committed.Sublist proposals) :
    Round label mode store proposals committed (fireList store committed) := by
  refine round_of_sublist (U := proposals) ?_ (fun _ member => member) noClash sub
  intro pre c inU preU apartPre
  have matchedPre : MatchedAt store pre := fun e member =>
    (MatchedAt.of_enabled enabled) e (preU e member)
  have grows := subset_fireList_of_monotone (store := store)
    (fun e member => monotone e (preU e member))
  obtain ⟨takenEmpty, queriesEmpty⟩ := monotone c inU
  have claims := permits_snapshot_of_wave (label := label) (MatchedAt.of_enabled enabled) pre c inU
    preU apartPre
  exact ⟨fun _ => by simp [takenEmpty], fun _ => (enabled c inU).kept_subset.trans grows,
    fun _ => by simp [queriesEmpty], claims.2.2.2⟩

/-- **Unchecked is exact on pairwise independent waves**: every unchecked round over a pairwise
independent wave is a serializable round, so pre-partitioned work needs no validation. -/
theorem unchecked_round_serializable_of_independent {proposals committed : List (Commit O R)}
    {final : Finset O} (enabled : ∀ c ∈ proposals, Enabled label store c)
    (independent : proposals.Pairwise (Independent label))
    (round : Round label (fun _ => Mode.unchecked) store proposals committed final) :
    Round label (fun _ => Mode.serializable) store proposals committed final := by
  have sub := round.sublist
  rw [round.final_eq]
  refine round_of_sublist (U := proposals) ?_ (fun _ member => member)
    (independent.imp fun {_ _} indep => indep.1) sub
  intro pre c inU preU apartPre
  have matchedPre : MatchedAt store pre := fun e member =>
    (MatchedAt.of_enabled enabled) e (preU e member)
  refine (permits_serializable_iff (enabled c inU).apart).mpr
    ((enabled_fireList_iff (enabled c inU) matchedPre).mpr fun e inPre => ?_)
  refine ⟨fun clash => apartPre e inPre clash.symm, ?_⟩
  by_cases same : e = c
  · subst same
    exact not_spoils_self_of_not_clash (apartPre e inPre)
  · exact (rel_of_mem_of_pairwise (fun indep => indep.symm) independent (preU e inPre) inU same).2.1


end SnapshotRounds

/-! ## Controls -/

namespace Controls

open Atom

/-- A round that commits both of two proposals cannot have dropped either. -/
theorem round_pair_cases {label : O → R} {mode : Commit O R → Finset Check} {store final : Finset O}
    {a b : Commit O R} (round : Round label mode store [a, b] [a, b] final) :
    Permits label (mode a) store a ∧ Permits label (mode b) (fire store a) b := by
  cases round with
  | commit permitsA after =>
      cases after with
      | commit permitsB _ => exact ⟨permitsA, permitsB⟩
      | drop after' =>
          have := after'.sublist
          simp at this
  | drop after =>
      have := after.sublist.length_le
      simp at this

/-- **Unchecked: a double take.** Both takers of the one token commit; both outputs appear. -/
theorem unchecked_double_take :
    Round label (fun _ => Mode.unchecked) {0} [taker, taker₂] [taker, taker₂]
        (fireList {0} [taker, taker₂]) ∧
      fireList {0} [taker, taker₂] = {6, 11} := by
  refine ⟨.commit ⟨by simp [Mode.unchecked], by simp [Mode.unchecked], by simp [Mode.unchecked],
    by decide⟩ (.commit ⟨by simp [Mode.unchecked], by simp [Mode.unchecked],
      by simp [Mode.unchecked], by decide⟩ (.done _)), by decide⟩

/-- **Snapshot: never a double take.** No snapshot round commits both takers. -/
theorem snapshot_no_double_take (final : Finset ℕ) :
    ¬ Round label (fun _ => Mode.snapshot) {0} [taker, taker₂] [taker, taker₂] final := by
  intro round
  have := (round_pair_cases round).2.1 (by simp [Mode.snapshot])
  revert this
  decide

/-- **Snapshot: write skew.** A snapshot round commits both skew proposals, reaching the store with
both outputs, which no serializable round reaches. The claims mode, which also checks keeps,
refuses both orders. -/
theorem snapshot_write_skew :
    Round skewLabel (fun _ => Mode.snapshot) {30, 31} [skewA, skewB] [skewA, skewB]
        (fireList {30, 31} [skewA, skewB]) ∧
      fireList {30, 31} [skewA, skewB] = {32, 33} ∧
      (∀ final, ¬ Round skewLabel (fun _ => Mode.claims) {30, 31} [skewA, skewB]
        [skewA, skewB] final) ∧
      (∀ final, ¬ Round skewLabel (fun _ => Mode.claims) {30, 31} [skewB, skewA]
        [skewB, skewA] final) := by
  refine ⟨.commit ⟨fun _ => by decide, by simp [Mode.snapshot], by simp [Mode.snapshot], by decide⟩
    (.commit ⟨fun _ => by decide, by simp [Mode.snapshot], by simp [Mode.snapshot], by decide⟩
      (.done _)), by decide, ?_, ?_⟩
  · intro final round
    have := (round_pair_cases round).2.2.1 (by simp [Mode.claims])
    revert this
    decide
  · intro final round
    have := (round_pair_cases round).2.2.1 (by simp [Mode.claims])
    revert this
    decide

/-- **Claims: an absence race.** Checking takes and keeps commits both "add unless
present" proposals; checking regions refuses both orders. -/
theorem claims_absence_race :
    Round label (fun _ => Mode.claims) {0} [addUnlessA, addUnlessB] [addUnlessA, addUnlessB]
        (fireList {0} [addUnlessA, addUnlessB]) ∧
      fireList {0} [addUnlessA, addUnlessB] = {0, 40, 41} ∧
      (∀ final, ¬ Round label (fun _ => Mode.serializable) {0} [addUnlessA, addUnlessB]
        [addUnlessA, addUnlessB] final) ∧
      (∀ final, ¬ Round label (fun _ => Mode.serializable) {0} [addUnlessB, addUnlessA]
        [addUnlessB, addUnlessA] final) := by
  refine ⟨.commit ⟨fun _ => by decide, fun _ => by decide, by simp [Mode.claims], by decide⟩
    (.commit ⟨fun _ => by decide, fun _ => by decide, by simp [Mode.claims], by decide⟩
      (.done _)), by decide, ?_, ?_⟩
  · intro final round
    have := (round_pair_cases round).2.2.2.1 (by simp [Mode.serializable]) ⟨isOut, ∅⟩
      (by simp [addUnlessB])
    revert this
    decide
  · intro final round
    have := (round_pair_cases round).2.2.2.1 (by simp [Mode.serializable]) ⟨isOut, ∅⟩
      (by simp [addUnlessA])
    revert this
    decide

/-- One serializable proposal and one snapshot proposal. -/
def mixedMode (c : Commit ℕ Atom) : Finset Check :=
  if c.made = {32} then Mode.serializable else Mode.snapshot

/-- **Mixed modes keep the weaker guarantee.** With the first skew proposal serializable and the
second on snapshot, the round that commits the serializable one first commits both (write skew);
the other order refuses the serializable one, which never commits on a stale read. -/
theorem mixed_write_skew :
    Round skewLabel mixedMode {30, 31} [skewA, skewB] [skewA, skewB]
        (fireList {30, 31} [skewA, skewB]) ∧
      ∀ final, ¬ Round skewLabel mixedMode {30, 31} [skewB, skewA] [skewB, skewA] final := by
  refine ⟨.commit ⟨fun _ => by decide, fun _ => by decide, fun _ => by simp [skewA], by decide⟩
    (.commit ⟨fun _ => by decide, fun member => by simp [mixedMode, skewB, Mode.snapshot] at member,
      fun member => by simp [mixedMode, skewB, Mode.snapshot] at member, by decide⟩ (.done _)), ?_⟩
  intro final round
  have := (round_pair_cases round).2.2.1 (by simp [mixedMode, skewA, Mode.serializable])
  revert this
  decide

/-- **Per-commit validation over-aborts.** A serializable round refuses the taker-then-reader
order of a reader and a taker, though the pair has an executable order (the reader first). -/
theorem optimistic_refuses_serializable_pair :
    (∀ final, ¬ Round label (fun _ => Mode.serializable) {0} [taker, reader] [taker, reader] final) ∧
      Executable label {0} [reader, taker] := by
  refine ⟨fun final round => ?_, reader_taker_wave.1⟩
  have := (round_pair_cases round).2.2.1 (by simp [Mode.serializable])
  revert this
  decide

/-! ### "Trust me" on a wave that is acyclic and not pairwise independent -/

theorem readerTakerWave_noClash : readerTakerWave.Pairwise (fun e d => ¬ Clash e d) := by
  simp only [readerTakerWave, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq, List.Pairwise.nil, and_true]
  unfold Clash
  simp [reader, taker]

theorem readerTakerWave_acyclic : Acyclic label readerTakerWave := by
  apply acyclic_of_ranked (rank := fun c => c.taken.card)
  rintro e d ⟨inE, inD, ne, spoils⟩
  simp only [readerTakerWave, List.mem_cons, List.not_mem_nil, or_false] at inE inD
  rcases inE with rfl | rfl <;> rcases inD with rfl | rfl
  · exact absurd rfl ne
  · exfalso
    rcases spoils with kept | ⟨read, member, -⟩
    · simp [reader, taker] at kept
    · simp [taker] at member
  · show reader.taken.card < taker.taken.card
    decide
  · exact absurd rfl ne

theorem readerTakerWave_makesSomething : MakesSomething readerTakerWave := by
  intro c member
  simp only [readerTakerWave, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact ⟨6, by simp [taker]⟩
  · exact ⟨5, by simp [reader]⟩

/-- **The trust-me refinement applies to a wave that is not pairwise independent**: the reader and
the taker of one token are acyclic, so every snapshot outcome is a serializable outcome. -/
theorem trustMe_instance (final : Finset ℕ)
    (snapshot : SnapshotOutcome label {0} readerTakerWave final) :
    SerialOutcome label {0} readerTakerWave final :=
  snapshot_refines_of_acyclic readerTakerWave_enabled readerTakerWave_noClash
    readerTakerWave_acyclic snapshot

/-- The converse's hypotheses hold on the same wave: its full snapshot outcome is serializable. -/
theorem fullSnapshot_instance :
    SerialOutcome label {0} readerTakerWave (fire {0} (effectOf readerTakerWave)) :=
  (serialOutcome_effect_iff_acyclic readerTakerWave_enabled readerTakerWave_noClash
    readerTakerWave_makesSomething (List.Subperm.refl _)).mpr readerTakerWave_acyclic

/-! ### What a mode permits -/

/-- **Positive and negative control**: at the empty store the reader of the token is permitted by
`snapshot`, which checks only takes, and not by `claims`, which also checks that the kept token is
present. -/
theorem reader_permitted_snapshot_not_claims :
    Permits label Mode.snapshot ∅ reader ∧ ¬ Permits label Mode.claims ∅ reader := by
  unfold Permits Mode.snapshot Mode.claims
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
