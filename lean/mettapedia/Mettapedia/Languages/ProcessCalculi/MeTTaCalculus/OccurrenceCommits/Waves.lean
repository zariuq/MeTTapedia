import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Exactness

/-!
# Waves: the finest serializable parallelism of one snapshot, and `every`

A **wave** is a set of commits that were all matched at one snapshot: each is enabled at the same
store. This module answers three questions about a wave.

1. **In which orders can its commits run one after another?** Enabling after a prefix depends
   only on pairs (`enabled_fireList_iff`): a commit stays enabled after a prefix exactly when it
   clashes with no commit of the prefix and none of them spoils it. Hence an order is executable
   exactly when no commit spoils a later one and no two clash (`executable_iff_pairwise`).
2. **When does some order exist?** Say `e` *must precede* `d` when `d` spoils `e`
   (`BeforeOn`). Some order of a clash-free wave is executable exactly when that relation is
   acyclic on the wave (`exists_executable_perm_iff_acyclic`), and the executable orders are its
   linear extensions. Every executable order reaches one store, the **wave commit**: the snapshot
   without everything taken, with everything made (`Executable.fireList_eq`). This is the finest
   validation of a wave that keeps the sequential meaning. It is finer than mutual independence:
   a reader and a taker of one occurrence form a wave with exactly one order
   (`Controls.reader_taker_wave`). Mutual independence is the case with no edges, where every
   order runs (`executable_of_pairwise_independent`). Write skew is a two-cycle
   (`Controls.write_skew_no_order`); two "add unless present" commits race through their absence
   reads (`Controls.absence_race_no_order`).
3. **What does `every` mean?** `every` commits all rows of one match at once, as one commit whose
   footprint is the amalgamation of the rows (`amalgamate`). Its predicate queries are judged at the
   snapshot, so rows do not see one another. `every` fires only when every row is enabled, **no two
   rows clash**, and no row keeps what another takes (`EveryEnabled`, `everyEnabled_iff`). Rows
   with a common take are refused (`every_refuses_clash`), as the multiset `every` of
   `TransformQuantifiers` refuses them: amalgamated, they would consume one occurrence once and
   publish both rows' results, a double take that no order of the rows produces
   (`Controls.every_refuses_double_take`). When `every` fires it reaches the wave commit
   (`fire_amalgamate`); it agrees with a serialization of its rows exactly when their precedence
   relation is acyclic (`every_fires_serializable_iff`), and with every serialization exactly when
   they are pairwise independent. With an absence cycle it is a synchronous update that no
   serialization produces (`Controls.every_synchronous_update`). That is the meaning `every`
   should have: its rows are one decision. Separate transactions are not: when a policy commits
   their combined effect without validating reads, it applies an effect that no order of them
   produces whenever their precedence has a cycle (`ValidationPolicies`). With an absence cycle
   that effect is the synchronous update; with a kept-read cycle (write skew) it is not even one
   commit, since the amalgamation would keep and take one occurrence
   (`Controls.write_skew_no_order`).
4. **Batches in full** (`exists_executable_perm_iff_noClash_and_acyclic`): a snapshot batch has an
   executable order exactly when no two of its commits clash and its precedence is acyclic.

## Identity queries decide pairwise; value queries do not

The prefix lemma relies on predicate queries observing identities, which a per-region epoch
validates. For queries of labels only, a commit can be spoiled by one commit and restored by
another (`Controls.value_query_restored`): taking the only `tok` and making a new one leaves the
value query valid after both and invalid after the first. Value validation is exact pair by pair
(`holdsValue_fire_iff`) but not compositional over prefixes, so epoch validation is the finest
validation that is decided pair by pair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v

variable {O : Type u} [DecidableEq O] {R : Type v}

/-! ## Sequences of commits -/

/-- Fire commits in order. -/
def fireList (store : Finset O) : List (Commit O R) → Finset O
  | [] => store
  | c :: rest => fireList (fire store c) rest

@[simp] theorem fireList_nil (store : Finset O) : fireList store ([] : List (Commit O R)) = store :=
  rfl

@[simp] theorem fireList_cons (store : Finset O) (c : Commit O R) (rest : List (Commit O R)) :
    fireList store (c :: rest) = fireList (fire store c) rest :=
  rfl

theorem fireList_append (store : Finset O) (first second : List (Commit O R)) :
    fireList store (first ++ second) = fireList (fireList store first) second := by
  induction first generalizing store with
  | nil => rfl
  | cons c rest ih => exact ih _

/-- A sequence is executable: each commit is enabled when its turn comes. -/
inductive Executable (label : O → R) : Finset O → List (Commit O R) → Prop
  | nil (store : Finset O) : Executable label store []
  | cons {store : Finset O} {c : Commit O R} {rest : List (Commit O R)}
      (enabled : Enabled label store c) (after : Executable label (fire store c) rest) :
      Executable label store (c :: rest)

theorem executable_cons_iff {label : O → R} {store : Finset O} {c : Commit O R}
    {rest : List (Commit O R)} :
    Executable label store (c :: rest) ↔
      Enabled label store c ∧ Executable label (fire store c) rest := by
  constructor
  · intro executable
    cases executable with
    | cons enabled after => exact ⟨enabled, after⟩
  · rintro ⟨enabled, after⟩
    exact .cons enabled after

/-- A sequence followed by another is executable exactly when the first is, and the second is
from where the first ends. -/
theorem executable_append_iff {label : O → R} {store : Finset O} {first second : List (Commit O R)} :
    Executable label store (first ++ second) ↔
      Executable label store first ∧ Executable label (fireList store first) second := by
  induction first generalizing store with
  | nil => exact ⟨fun executable => ⟨.nil _, executable⟩, fun ⟨_, executable⟩ => executable⟩
  | cons c rest ih =>
      simp only [List.cons_append, executable_cons_iff, fireList_cons, ih, and_assoc]

/-- A sequence with one more commit is executable exactly when the sequence is, and the commit is
enabled where it ends. -/
theorem executable_snoc_iff {label : O → R} {store : Finset O} {cs : List (Commit O R)}
    {c : Commit O R} :
    Executable label store (cs ++ [c]) ↔
      Executable label store cs ∧ Enabled label (fireList store cs) c := by
  rw [executable_append_iff, executable_cons_iff]
  exact ⟨fun ⟨first, enabled, _⟩ => ⟨first, enabled⟩,
    fun ⟨first, enabled⟩ => ⟨first, enabled, .nil _⟩⟩

/-! ## The combined effect of a list -/

/-- Everything a list of commits takes. -/
def takenOf : List (Commit O R) → Finset O
  | [] => ∅
  | c :: rest => c.taken ∪ takenOf rest

/-- Everything a list of commits keeps. -/
def keptOf : List (Commit O R) → Finset O
  | [] => ∅
  | c :: rest => c.kept ∪ keptOf rest

/-- Everything a list of commits makes. -/
def madeOf : List (Commit O R) → Finset O
  | [] => ∅
  | c :: rest => c.made ∪ madeOf rest

theorem mem_takenOf {l : List (Commit O R)} {o : O} : o ∈ takenOf l ↔ ∃ c ∈ l, o ∈ c.taken := by
  induction l with
  | nil => simp [takenOf]
  | cons c rest ih => simp [takenOf, ih]

theorem mem_keptOf {l : List (Commit O R)} {o : O} : o ∈ keptOf l ↔ ∃ c ∈ l, o ∈ c.kept := by
  induction l with
  | nil => simp [keptOf]
  | cons c rest ih => simp [keptOf, ih]

theorem mem_madeOf {l : List (Commit O R)} {o : O} : o ∈ madeOf l ↔ ∃ c ∈ l, o ∈ c.made := by
  induction l with
  | nil => simp [madeOf]
  | cons c rest ih => simp [madeOf, ih]

theorem madeOf_append (first second : List (Commit O R)) :
    madeOf (first ++ second) = madeOf first ∪ madeOf second := by
  induction first with
  | nil => simp [madeOf]
  | cons c rest ih => simp [madeOf, ih, Finset.union_assoc]

/-- The combined effect of a list, as one commit that keeps and reads nothing. -/
def effectOf (l : List (Commit O R)) : Commit O R := ⟨takenOf l, ∅, madeOf l, []⟩

/-- A list of commits all matched at one snapshot: each takes from it and makes fresh. -/
def MatchedAt (store : Finset O) (l : List (Commit O R)) : Prop :=
  ∀ c ∈ l, c.taken ⊆ store ∧ Disjoint c.made store

omit [DecidableEq O] in
theorem MatchedAt.of_enabled {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (enabled : ∀ c ∈ l, Enabled label store c) : MatchedAt store l :=
  fun c member => ⟨(enabled c member).taken_subset, (enabled c member).fresh⟩

/-- **The wave formula.** Firing commits matched at one snapshot, in any order, removes all their
takings and adds all their productions; no enabling is needed for the formula. -/
theorem fireList_eq_fire_effectOf {store : Finset O} {l : List (Commit O R)}
    (matched : MatchedAt store l) : fireList store l = fire store (effectOf l) := by
  -- Generalize over a partial firing `(store \ X) ∪ Y` with `Y` fresh.
  suffices general : ∀ (X Y : Finset O), Disjoint Y store →
      fireList ((store \ X) ∪ Y) l = (store \ (X ∪ takenOf l)) ∪ (Y ∪ madeOf l) by
    have := general ∅ ∅ (Finset.disjoint_empty_left _)
    simpa [fire, effectOf] using this
  induction l with
  | nil => intro X Y _; simp [takenOf, madeOf]
  | cons c rest ih =>
      intro X Y freshY
      have matchedRest : MatchedAt store rest := fun d member => matched d (List.mem_cons_of_mem _ member)
      obtain ⟨takenC, freshC⟩ := matched c List.mem_cons_self
      have step : fire ((store \ X) ∪ Y) c = (store \ (X ∪ c.taken)) ∪ (Y ∪ c.made) := by
        ext o
        simp only [mem_fire, Finset.mem_union, Finset.mem_sdiff, not_or]
        constructor
        · rintro (⟨⟨inStore, notX⟩ | inY, notC⟩ | made)
          · exact Or.inl ⟨inStore, notX, notC⟩
          · exact Or.inr (Or.inl inY)
          · exact Or.inr (Or.inr made)
        · rintro (⟨inStore, notX, notC⟩ | inY | made)
          · exact Or.inl ⟨Or.inl ⟨inStore, notX⟩, notC⟩
          · exact Or.inl ⟨Or.inr inY, fun taken =>
              Finset.disjoint_left.mp freshY inY (takenC taken)⟩
          · exact Or.inr made
      rw [fireList_cons, step, ih matchedRest _ _ (Finset.disjoint_union_left.mpr ⟨freshY, freshC⟩)]
      ext o
      simp only [takenOf, madeOf, Finset.mem_union, Finset.mem_sdiff, not_or]
      tauto

theorem enabled_effectOf {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (matched : MatchedAt store l) : Enabled label store (effectOf l) where
  taken_subset := fun o member => by
    obtain ⟨c, inL, taken⟩ := mem_takenOf.mp member
    exact (matched c inL).1 taken
  kept_subset := Finset.empty_subset _
  apart := Finset.disjoint_empty_right _
  fresh := by
    refine Finset.disjoint_left.mpr fun o member inStore => ?_
    obtain ⟨c, inL, made⟩ := mem_madeOf.mp member
    exact Finset.disjoint_left.mp (matched c inL).2 made inStore
  queries_hold := by simp [effectOf]

theorem clash_effectOf_iff {d : Commit O R} {l : List (Commit O R)} :
    Clash d (effectOf l) ↔ ∃ e ∈ l, Clash d e := by
  unfold Clash effectOf
  simp only [Finset.not_disjoint_iff, mem_takenOf, mem_madeOf]
  constructor
  · rintro (⟨o, inD, e, inL, inE⟩ | ⟨o, inD, e, inL, inE⟩)
    · exact ⟨e, inL, Or.inl ⟨o, inD, inE⟩⟩
    · exact ⟨e, inL, Or.inr ⟨o, inD, inE⟩⟩
  · rintro ⟨e, inL, ⟨o, inD, inE⟩ | ⟨o, inD, inE⟩⟩
    · exact Or.inl ⟨o, inD, e, inL, inE⟩
    · exact Or.inr ⟨o, inD, e, inL, inE⟩

theorem spoils_effectOf_iff {label : O → R} {d : Commit O R} {l : List (Commit O R)} :
    Spoils label (effectOf l) d ↔ ∃ e ∈ l, Spoils label e d := by
  unfold Spoils WritesInto effectOf
  simp only [Finset.not_disjoint_iff, mem_takenOf, mem_madeOf, Finset.mem_union]
  constructor
  · rintro (⟨o, ⟨e, inL, inE⟩, kept⟩ | ⟨read, member, o, written, inRegion⟩)
    · exact ⟨e, inL, Or.inl ⟨o, inE, kept⟩⟩
    · rcases written with ⟨e, inL, inE⟩ | ⟨e, inL, inE⟩
      · exact ⟨e, inL, Or.inr ⟨read, member, o, Or.inl inE, inRegion⟩⟩
      · exact ⟨e, inL, Or.inr ⟨read, member, o, Or.inr inE, inRegion⟩⟩
  · rintro ⟨e, inL, ⟨o, inE, kept⟩ | ⟨read, member, o, written, inRegion⟩⟩
    · exact Or.inl ⟨o, ⟨e, inL, inE⟩, kept⟩
    · rcases written with inE | inE
      · exact Or.inr ⟨read, member, o, Or.inl ⟨e, inL, inE⟩, inRegion⟩
      · exact Or.inr ⟨read, member, o, Or.inr ⟨e, inL, inE⟩, inRegion⟩

/-! ## Enabling after a prefix depends only on pairs -/

/-- **The prefix lemma.** A commit matched at a snapshot stays enabled after a prefix of commits
matched at the same snapshot exactly when it clashes with none of them and none of them spoils
it. -/
theorem enabled_fireList_iff {label : O → R} {store : Finset O} {d : Commit O R}
    {pre : List (Commit O R)} (enabledD : Enabled label store d)
    (matched : MatchedAt store pre) :
    Enabled label (fireList store pre) d ↔ ∀ e ∈ pre, ¬ Clash d e ∧ ¬ Spoils label e d := by
  rw [fireList_eq_fire_effectOf matched, enabled_fire_iff enabledD (enabled_effectOf matched),
    clash_effectOf_iff, spoils_effectOf_iff]
  constructor
  · rintro ⟨noClash, noSpoil⟩ e inPrefix
    exact ⟨fun clash => noClash ⟨e, inPrefix, clash⟩, fun spoils => noSpoil ⟨e, inPrefix, spoils⟩⟩
  · intro each
    exact ⟨fun ⟨e, inPrefix, clash⟩ => (each e inPrefix).1 clash,
      fun ⟨e, inPrefix, spoils⟩ => (each e inPrefix).2 spoils⟩

/-- **Executable orders after a prefix.** For commits all matched at one snapshot, a sequence is
executable after a prefix exactly when no commit of it clashes with or is spoiled by a commit of
the prefix or an earlier commit of the sequence. -/
theorem executable_fireList_iff {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (enabled : ∀ c ∈ l, Enabled label store c) :
    ∀ (pre : List (Commit O R)), MatchedAt store pre →
      (Executable label (fireList store pre) l ↔
        (∀ d ∈ l, ∀ e ∈ pre, ¬ Clash d e ∧ ¬ Spoils label e d) ∧
          l.Pairwise (fun e d => ¬ Clash d e ∧ ¬ Spoils label e d)) := by
  induction l with
  | nil => intro pre _; simpa using Executable.nil _
  | cons c rest ih =>
      intro pre matched
      have enabledRest : ∀ d ∈ rest, Enabled label store d := fun d member =>
        enabled d (List.mem_cons_of_mem _ member)
      have matchedC : MatchedAt store (pre ++ [c]) := by
        intro e member
        rcases List.mem_append.mp member with inPrefix | inC
        · exact matched e inPrefix
        · rw [List.mem_singleton] at inC
          subst inC
          exact ⟨(enabled e List.mem_cons_self).taken_subset, (enabled e List.mem_cons_self).fresh⟩
      rw [executable_cons_iff, enabled_fireList_iff (enabled c List.mem_cons_self) matched,
        show fire (fireList store pre) c = fireList store (pre ++ [c]) by
          rw [fireList_append]; rfl,
        ih enabledRest (pre ++ [c]) matchedC, List.pairwise_cons]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨first, later, pairwise⟩
        refine ⟨?_, fun d inRest => later d inRest c (Or.inr rfl), pairwise⟩
        rintro d (rfl | inRest) e inPrefix
        · exact first e inPrefix
        · exact later d inRest e (Or.inl inPrefix)
      · rintro ⟨each, afterC, pairwise⟩
        refine ⟨fun e inPrefix => each c (Or.inl rfl) e inPrefix, ?_, pairwise⟩
        rintro d inRest e (inPrefix | rfl)
        · exact each d (Or.inr inRest) e inPrefix
        · exact afterC d inRest

/-- **Executable orders of a wave.** A sequence of commits all enabled at one snapshot is
executable exactly when no commit clashes with or is spoiled by an earlier one. -/
theorem executable_iff_pairwise {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (enabled : ∀ c ∈ l, Enabled label store c) :
    Executable label store l ↔ l.Pairwise (fun e d => ¬ Clash d e ∧ ¬ Spoils label e d) := by
  have := executable_fireList_iff enabled [] (fun c member => by simp at member)
  simpa using this

/-- **Every executable order reaches the wave commit.** -/
theorem Executable.fireList_eq {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (enabled : ∀ c ∈ l, Enabled label store c) :
    fireList store l = fire store (effectOf l) :=
  fireList_eq_fire_effectOf (MatchedAt.of_enabled enabled)

theorem takenOf_perm {l l' : List (Commit O R)} (perm : l.Perm l') : takenOf l = takenOf l' := by
  ext o
  simp only [mem_takenOf]
  exact ⟨fun ⟨c, inL, taken⟩ => ⟨c, perm.subset inL, taken⟩,
    fun ⟨c, inL, taken⟩ => ⟨c, perm.symm.subset inL, taken⟩⟩

theorem madeOf_perm {l l' : List (Commit O R)} (perm : l.Perm l') : madeOf l = madeOf l' := by
  ext o
  simp only [mem_madeOf]
  exact ⟨fun ⟨c, inL, made⟩ => ⟨c, perm.subset inL, made⟩,
    fun ⟨c, inL, made⟩ => ⟨c, perm.symm.subset inL, made⟩⟩

/-- Two orders of one wave reach the same store. -/
theorem fireList_perm {store : Finset O} {l l' : List (Commit O R)} (matched : MatchedAt store l)
    (perm : l.Perm l') : fireList store l = fireList store l' := by
  have matched' : MatchedAt store l' := fun c member => matched c (perm.symm.subset member)
  rw [fireList_eq_fire_effectOf matched, fireList_eq_fire_effectOf matched']
  simp [effectOf, takenOf_perm perm, madeOf_perm perm]

/-- **Pairwise independent waves run in every order.** -/
theorem executable_of_pairwise_independent {label : O → R} {store : Finset O}
    {l : List (Commit O R)} (enabled : ∀ c ∈ l, Enabled label store c)
    (independent : l.Pairwise (Independent label)) : Executable label store l :=
  (executable_iff_pairwise enabled).mpr
    (independent.imp fun {_ _} indep => ⟨fun clash => indep.1 clash.symm, indep.2.1⟩)

/-! ## When some order exists: acyclic precedence -/

/-- `e` must precede `d` in the wave `W`: both belong to it, they differ, and `d` spoils `e`. -/
def BeforeOn (label : O → R) (W : List (Commit O R)) (e d : Commit O R) : Prop :=
  e ∈ W ∧ d ∈ W ∧ e ≠ d ∧ Spoils label d e

/-- The precedence relation of a wave has no cycle. -/
def Acyclic (label : O → R) (W : List (Commit O R)) : Prop :=
  ∀ c, ¬ Relation.TransGen (BeforeOn label W) c c

/-- A ranking of a wave: precedence strictly increases the rank. -/
def Ranked (label : O → R) (W : List (Commit O R)) (rank : Commit O R → ℕ) : Prop :=
  ∀ e d, BeforeOn label W e d → rank e < rank d

theorem acyclic_of_ranked {label : O → R} {W : List (Commit O R)} {rank : Commit O R → ℕ}
    (ranked : Ranked label W rank) : Acyclic label W := by
  intro c cycle
  have increase : ∀ {a b}, Relation.TransGen (BeforeOn label W) a b → rank a < rank b := by
    intro a b path
    induction path with
    | single edge => exact ranked _ _ edge
    | tail _ edge ih => exact ih.trans (ranked _ _ edge)
  exact lt_irrefl _ (increase cycle)

open Classical in
/-- An acyclic wave has a ranking: the number of commits that must precede a commit,
directly or through others. -/
theorem ranked_of_acyclic {label : O → R} {W : List (Commit O R)} (acyclic : Acyclic label W) :
    ∃ rank, Ranked label W rank := by
  refine ⟨fun c => (W.toFinset.filter fun e => Relation.TransGen (BeforeOn label W) e c).card, ?_⟩
  intro e d edge
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset ?_ |>.mpr ⟨e, ?_, ?_⟩
  · intro x member
    simp only [Finset.mem_filter] at member ⊢
    exact ⟨member.1, member.2.tail edge⟩
  · simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨edge.1, .single edge⟩
  · simp only [Finset.mem_filter, not_and]
    exact fun _ => acyclic e

/-- A commit that does not clash with itself takes and makes nothing, so it spoils nothing,
itself included. -/
theorem not_spoils_self_of_not_clash {label : O → R} {c : Commit O R} (noClash : ¬ Clash c c) :
    ¬ Spoils label c c := by
  unfold Clash at noClash
  push Not at noClash
  have takenEmpty : c.taken = ∅ := Finset.disjoint_self_iff_empty _ |>.mp noClash.1
  have madeEmpty : c.made = ∅ := Finset.disjoint_self_iff_empty _ |>.mp noClash.2
  unfold Spoils WritesInto
  simp [takenEmpty, madeEmpty]

open Classical in
/-- A ranked, clash-free wave has an executable order: sort it by rank. -/
theorem exists_executable_perm_of_ranked {label : O → R} {store : Finset O}
    {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) {rank : Commit O R → ℕ}
    (ranked : Ranked label W rank) : ∃ l, l.Perm W ∧ Executable label store l := by
  let le : Commit O R → Commit O R → Bool := fun a b => decide (rank a ≤ rank b)
  have perm := List.mergeSort_perm W le
  refine ⟨W.mergeSort le, perm, ?_⟩
  have enabledSorted : ∀ c ∈ W.mergeSort le, Enabled label store c := fun c member =>
    enabled c (perm.subset member)
  refine (executable_iff_pairwise enabledSorted).mpr ?_
  have sorted : (W.mergeSort le).Pairwise (fun a b => le a b = true) :=
    List.pairwise_mergeSort (fun a b c hab hbc => by
        simp only [le, decide_eq_true_eq] at hab hbc ⊢; omega)
      (fun a b => by simp only [le, Bool.or_eq_true, decide_eq_true_eq]; omega) W
  have clashFree : (W.mergeSort le).Pairwise (fun e d => ¬ Clash e d) :=
    (perm.pairwise_iff fun {x y} noXY clash => noXY clash.symm).mpr noClash
  have members : (W.mergeSort le).Pairwise (fun e d => e ∈ W ∧ d ∈ W) :=
    List.pairwise_of_forall_mem_list fun a inA b inB => ⟨perm.subset inA, perm.subset inB⟩
  refine ((sorted.and clashFree).and members).imp ?_
  rintro e d ⟨⟨ordered, noClashED⟩, inE, inD⟩
  refine ⟨fun clash => noClashED clash.symm, fun spoils => ?_⟩
  simp only [le, decide_eq_true_eq] at ordered
  by_cases same : d = e
  · subst same
    exact not_spoils_self_of_not_clash noClashED spoils
  · have := ranked d e ⟨inD, inE, same, spoils⟩
    omega

open Classical in
/-- An executable order of a wave ranks it by position. -/
theorem ranked_of_executable_perm {label : O → R} {store : Finset O} {W l : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (perm : l.Perm W)
    (executable : Executable label store l) : ∃ rank, Ranked label W rank := by
  have enabledL : ∀ c ∈ l, Enabled label store c := fun c member => enabled c (perm.subset member)
  have pairwise := (executable_iff_pairwise enabledL).mp executable
  refine ⟨fun c => l.idxOf c, ?_⟩
  rintro e d ⟨inE, inD, different, spoils⟩
  have inEl : e ∈ l := perm.symm.subset inE
  have inDl : d ∈ l := perm.symm.subset inD
  have hi := List.idxOf_lt_length_of_mem inEl
  have hj := List.idxOf_lt_length_of_mem inDl
  have atE : l[l.idxOf e] = e := List.getElem_idxOf hi
  have atD : l[l.idxOf d] = d := List.getElem_idxOf hj
  show l.idxOf e < l.idxOf d
  rcases lt_trichotomy (l.idxOf e) (l.idxOf d) with lt | eq | gt
  · exact lt
  · exact absurd (by rw [← atE, ← atD]; simp only [eq]) different
  · have := (List.pairwise_iff_getElem.mp pairwise) _ _ hj hi gt
    rw [atD, atE] at this
    exact absurd spoils this.2

/-- **Some order of a clash-free wave is executable exactly when its precedence relation is
acyclic.** The executable orders are then the orders that rank it, and all reach the wave
commit. -/
theorem exists_executable_perm_iff_acyclic {label : O → R} {store : Finset O}
    {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c)
    (noClash : W.Pairwise (fun e d => ¬ Clash e d)) :
    (∃ l, l.Perm W ∧ Executable label store l) ↔ Acyclic label W := by
  constructor
  · rintro ⟨l, perm, executable⟩
    obtain ⟨rank, ranked⟩ := ranked_of_executable_perm enabled perm executable
    exact acyclic_of_ranked ranked
  · intro acyclic
    obtain ⟨rank, ranked⟩ := ranked_of_acyclic acyclic
    exact exists_executable_perm_of_ranked enabled noClash ranked

/-- Two distinct members of a list that is pairwise related by a symmetric relation are related. -/
theorem rel_of_mem_of_pairwise {α : Type*} {rel : α → α → Prop} (symm : ∀ {x y}, rel x y → rel y x)
    {W : List α} (pairwise : W.Pairwise rel) {a b : α} (inA : a ∈ W) (inB : b ∈ W)
    (different : a ≠ b) : rel a b := by
  induction W with
  | nil => simp at inA
  | cons x rest ih =>
      obtain ⟨head, tail⟩ := List.pairwise_cons.mp pairwise
      rcases List.mem_cons.mp inA with rfl | inA'
      · rcases List.mem_cons.mp inB with rfl | inB'
        · exact absurd rfl different
        · exact head b inB'
      · rcases List.mem_cons.mp inB with rfl | inB'
        · exact symm (head a inA')
        · exact ih tail inA' inB'

omit [DecidableEq O] in
/-- Two distinct members of a clash-free list do not clash. -/
theorem noClash_of_mem {W : List (Commit O R)} (noClash : W.Pairwise (fun e d => ¬ Clash e d))
    {a b : Commit O R} (inA : a ∈ W) (inB : b ∈ W) (different : a ≠ b) : ¬ Clash a b :=
  rel_of_mem_of_pairwise (fun noXY clash => noXY clash.symm) noClash inA inB different

/-! ## `every`: the amalgamated commit -/

/-- Every predicate query of a list of commits. -/
def queriesOf (l : List (Commit O R)) : List (PredicateQuery O R) := l.flatMap Commit.queries

/-- The amalgamation of rows into one commit. -/
def amalgamate (l : List (Commit O R)) : Commit O R := ⟨takenOf l, keptOf l, madeOf l, queriesOf l⟩

/-- **When the amalgamated footprint is an enabled commit.** The amalgamation of rows enabled at one
snapshot is an enabled commit there exactly when no row keeps what a row takes. Predicate queries
are judged at the snapshot, so rows that write into each other's regions do not disable it. This is
not yet `every`: the union of takes hides a common take (`EveryEnabled` refuses it). -/
theorem amalgamate_enabled_iff {label : O → R} {store : Finset O} {l : List (Commit O R)}
    (enabled : ∀ c ∈ l, Enabled label store c) :
    Enabled label store (amalgamate l) ↔ ∀ e ∈ l, ∀ d ∈ l, Disjoint e.taken d.kept := by
  constructor
  · intro amalgam e inE d inD
    refine Finset.disjoint_left.mpr fun o taken kept => ?_
    exact Finset.disjoint_left.mp amalgam.apart (mem_takenOf.mpr ⟨e, inE, taken⟩)
      (mem_keptOf.mpr ⟨d, inD, kept⟩)
  · intro apart
    refine
      { taken_subset := fun o member => ?_
        kept_subset := fun o member => ?_
        apart := ?_
        fresh := ?_
        queries_hold := ?_ }
    · obtain ⟨c, inL, taken⟩ := mem_takenOf.mp member
      exact (enabled c inL).taken_subset taken
    · obtain ⟨c, inL, kept⟩ := mem_keptOf.mp member
      exact (enabled c inL).kept_subset kept
    · refine Finset.disjoint_left.mpr fun o taken kept => ?_
      obtain ⟨e, inE, takenE⟩ := mem_takenOf.mp taken
      obtain ⟨d, inD, keptD⟩ := mem_keptOf.mp kept
      exact Finset.disjoint_left.mp (apart e inE d inD) takenE keptD
    · refine Finset.disjoint_left.mpr fun o made inStore => ?_
      obtain ⟨c, inL, madeC⟩ := mem_madeOf.mp made
      exact Finset.disjoint_left.mp (enabled c inL).fresh madeC inStore
    · intro read member
      obtain ⟨c, inL, inQueries⟩ := List.mem_flatMap.mp member
      exact (enabled c inL).queries_hold read inQueries

/-- **`every` fires to the wave commit.** -/
theorem fire_amalgamate (store : Finset O) (l : List (Commit O R)) :
    fire store (amalgamate l) = fire store (effectOf l) :=
  rfl

/-- **When `every` fires**: every row is enabled at the snapshot, no two rows clash, and the
amalgamated footprint is an enabled commit (no row keeps what another takes). -/
def EveryEnabled (label : O → R) (store : Finset O) (rows : List (Commit O R)) : Prop :=
  (∀ c ∈ rows, Enabled label store c) ∧ rows.Pairwise (fun e d => ¬ Clash e d) ∧
    Enabled label store (amalgamate rows)

theorem everyEnabled_iff {label : O → R} {store : Finset O} {rows : List (Commit O R)} :
    EveryEnabled label store rows ↔
      (∀ c ∈ rows, Enabled label store c) ∧ rows.Pairwise (fun e d => ¬ Clash e d) ∧
        ∀ e ∈ rows, ∀ d ∈ rows, Disjoint e.taken d.kept := by
  constructor
  · rintro ⟨enabled, noClash, amalgam⟩
    exact ⟨enabled, noClash, (amalgamate_enabled_iff enabled).mp amalgam⟩
  · rintro ⟨enabled, noClash, apart⟩
    exact ⟨enabled, noClash, (amalgamate_enabled_iff enabled).mpr apart⟩

/-- **`every` refuses rows with a common take.** -/
theorem every_refuses_clash {label : O → R} {store : Finset O} {rows : List (Commit O R)}
    {e d : Commit O R} (inE : e ∈ rows) (inD : d ∈ rows) (different : e ≠ d) (clash : Clash e d) :
    ¬ EveryEnabled label store rows := fun ⟨_, noClash, _⟩ =>
  noClash_of_mem noClash inE inD different clash

/-- **`every` agrees with a serialization of its rows exactly when their precedence relation is
acyclic**: then some order of the rows is executable, and it reaches the amalgamated store. -/
theorem every_serializable_iff {label : O → R} {store : Finset O} {W : List (Commit O R)}
    (enabled : ∀ c ∈ W, Enabled label store c) (noClash : W.Pairwise (fun e d => ¬ Clash e d)) :
    (∃ l, l.Perm W ∧ Executable label store l ∧ fireList store l = fire store (amalgamate W)) ↔
      Acyclic label W := by
  rw [← exists_executable_perm_iff_acyclic enabled noClash]
  constructor
  · rintro ⟨l, perm, executable, _⟩
    exact ⟨l, perm, executable⟩
  · rintro ⟨l, perm, executable⟩
    refine ⟨l, perm, executable, ?_⟩
    have enabledL : ∀ c ∈ l, Enabled label store c := fun c member => enabled c (perm.subset member)
    rw [fireList_perm (MatchedAt.of_enabled enabledL) perm, fire_amalgamate,
      fireList_eq_fire_effectOf (MatchedAt.of_enabled enabled)]

/-- **Batches in full.** A snapshot batch has an executable order exactly when no two of its
commits clash and its precedence relation is acyclic. -/
theorem exists_executable_perm_iff_noClash_and_acyclic {label : O → R} {store : Finset O}
    {W : List (Commit O R)} (enabled : ∀ c ∈ W, Enabled label store c) :
    (∃ l, l.Perm W ∧ Executable label store l) ↔
      W.Pairwise (fun e d => ¬ Clash e d) ∧ Acyclic label W := by
  constructor
  · rintro ⟨l, perm, executable⟩
    have enabledL : ∀ c ∈ l, Enabled label store c := fun c member => enabled c (perm.subset member)
    have noClashL : l.Pairwise (fun e d => ¬ Clash e d) :=
      ((executable_iff_pairwise enabledL).mp executable).imp fun pair clash => pair.1 clash.symm
    have noClashW : W.Pairwise (fun e d => ¬ Clash e d) :=
      (perm.pairwise_iff fun {x y} noXY clash => noXY clash.symm).mp noClashL
    exact ⟨noClashW, (exists_executable_perm_iff_acyclic enabled noClashW).mp ⟨l, perm, executable⟩⟩
  · rintro ⟨noClash, acyclic⟩
    exact (exists_executable_perm_iff_acyclic enabled noClash).mpr acyclic

/-- **When `every` fires, it agrees with a serialization of its rows exactly when their
precedence relation is acyclic.** -/
theorem every_fires_serializable_iff {label : O → R} {store : Finset O} {W : List (Commit O R)}
    (fires : EveryEnabled label store W) :
    (∃ l, l.Perm W ∧ Executable label store l ∧ fireList store l = fire store (amalgamate W)) ↔
      Acyclic label W :=
  every_serializable_iff fires.1 fires.2.1

/-! ## Controls -/

namespace Controls

open Atom

/-! ### A reader and a taker of one occurrence: one order -/

/-- The wave of a reader and a taker of the token. -/
def readerTakerWave : List (Commit ℕ Atom) := [taker, reader]

theorem readerTakerWave_enabled : ∀ c ∈ readerTakerWave, Enabled label {0} c := by
  intro c member
  simp only [readerTakerWave, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact taker_enabled
  · exact reader_enabled

/-- **The reader–taker wave has an executable order, the reader first, though the two are not
independent.** Waves are finer than mutual independence. -/
theorem reader_taker_wave :
    Executable label {0} [reader, taker] ∧ ¬ Executable label {0} [taker, reader] ∧
      ¬ Independent label reader taker := by
  refine ⟨?_, ?_, ?_⟩
  · exact .cons reader_enabled (.cons reader_taker.1 (.nil _))
  · intro executable
    rw [executable_cons_iff, executable_cons_iff] at executable
    exact reader_taker.2 executable.2.1
  · intro independent
    exact reader_taker.2 ((independent_iff_both_orders reader_enabled taker_enabled).mp
      independent).2

/-! ### Two takers of one token: `every` refuses -/

theorem takers_enabled : ∀ c ∈ [taker, taker₂], Enabled label {0} c := by
  intro c member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact taker_enabled
  · exact taker₂_enabled

/-- A clashing batch has no executable order. -/
theorem takers_batch_no_order : ¬ ∃ l, l.Perm [taker, taker₂] ∧ Executable label {0} l := by
  intro executable
  have := ((exists_executable_perm_iff_noClash_and_acyclic takers_enabled).mp executable).1
  exact (List.pairwise_cons.mp this).1 taker₂ (by simp) (Or.inl (by simp [taker, taker₂]))

/-- **`every` refuses a double take.** The amalgamated footprint of two takers of one token is an
enabled commit that consumes the token once and publishes both outputs, a store no order of the
rows reaches; `every` does not fire. -/
theorem every_refuses_double_take :
    Enabled label {0} (amalgamate [taker, taker₂]) ∧
      fire {0} (amalgamate [taker, taker₂]) = {6, 11} ∧
      ¬ (∃ l, l.Perm [taker, taker₂] ∧ Executable label {0} l) ∧
      ¬ EveryEnabled label {0} [taker, taker₂] := by
  refine ⟨(amalgamate_enabled_iff takers_enabled).mpr ?_, by decide, takers_batch_no_order,
    every_refuses_clash (e := taker) (d := taker₂) (by simp) (by simp)
      (fun equal => absurd (congrArg Commit.made equal) (by decide)) (Or.inl (by simp [taker, taker₂]))⟩
  intro e inE d inD
  simp only [List.mem_cons, List.not_mem_nil, or_false] at inE inD
  rcases inE with rfl | rfl <;> rcases inD with rfl | rfl <;> decide

/-! ### Write skew: a two-cycle -/

/-- Write-skew labels: occurrence `30` is `x`, `31` is `y`; outputs elsewhere. -/
def skewLabel : ℕ → Atom
  | 30 => tok
  | 31 => lock
  | _ => out

/-- Read `x`, take `y`, make `P`. -/
def skewA : Commit ℕ Atom := ⟨{31}, {30}, {32}, []⟩

/-- Read `y`, take `x`, make `Q`. -/
def skewB : Commit ℕ Atom := ⟨{30}, {31}, {33}, []⟩

theorem skewA_enabled : Enabled skewLabel {30, 31} skewA where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [skewA]

theorem skewB_enabled : Enabled skewLabel {30, 31} skewB where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by simp [skewB]

/-- **Write skew has no executable order**: each commit spoils the other, a cycle of
precedence. Nor is it one `every`: its amalgamation would keep and take one occurrence, which the
identification condition forbids. Only a policy that skips read validation commits both
(`ValidationPolicies`). -/
theorem write_skew_no_order :
    ¬ (∃ l, l.Perm [skewA, skewB] ∧ Executable skewLabel {30, 31} l) ∧
      ¬ Enabled skewLabel {30, 31} (amalgamate [skewA, skewB]) := by
  have enabled : ∀ c ∈ [skewA, skewB], Enabled skewLabel {30, 31} c := by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact skewA_enabled
    · exact skewB_enabled
  have noClash : [skewA, skewB].Pairwise (fun e d => ¬ Clash e d) := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    unfold Clash
    simp [skewA, skewB]
  constructor
  · rw [exists_executable_perm_iff_acyclic enabled noClash]
    intro acyclic
    have edgeAB : BeforeOn skewLabel [skewA, skewB] skewA skewB :=
      ⟨by simp, by simp, by simp [skewA, skewB], Or.inl (by simp [skewA, skewB])⟩
    have edgeBA : BeforeOn skewLabel [skewA, skewB] skewB skewA :=
      ⟨by simp, by simp, by simp [skewA, skewB], Or.inl (by simp [skewA, skewB])⟩
    exact acyclic skewA (.tail (.single edgeAB) edgeBA)
  · intro amalgam
    have := (amalgamate_enabled_iff enabled).mp amalgam skewA (by simp) skewB (by simp)
    revert this
    decide

/-! ### Two "add unless present" commits: an absence race -/

/-- The region of outputs. -/
def isOut : Atom → Bool
  | out => true
  | _ => false

/-- Add output `40` unless an output is present. -/
def addUnlessA : Commit ℕ Atom := ⟨∅, ∅, {40}, [⟨isOut, ∅⟩]⟩

/-- Add output `41` unless an output is present. -/
def addUnlessB : Commit ℕ Atom := ⟨∅, ∅, {41}, [⟨isOut, ∅⟩]⟩

theorem addUnlessA_enabled : Enabled label {0} addUnlessA where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [addUnlessA, List.mem_singleton] at member
    subst member
    decide

theorem addUnlessB_enabled : Enabled label {0} addUnlessB where
  taken_subset := by decide
  kept_subset := by decide
  apart := by decide
  fresh := by decide
  queries_hold := by
    intro read member
    simp only [addUnlessB, List.mem_singleton] at member
    subst member
    decide

/-- **An absence race has no executable order** (each makes inside the other's absence region),
while their amalgamation, a synchronous update, makes both outputs. -/
theorem absence_race_no_order :
    ¬ (∃ l, l.Perm [addUnlessA, addUnlessB] ∧ Executable label {0} l) ∧
      Enabled label {0} (amalgamate [addUnlessA, addUnlessB]) := by
  have enabled : ∀ c ∈ [addUnlessA, addUnlessB], Enabled label {0} c := by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact addUnlessA_enabled
    · exact addUnlessB_enabled
  have noClash : [addUnlessA, addUnlessB].Pairwise (fun e d => ¬ Clash e d) := by
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      List.Pairwise.nil, and_true]
    unfold Clash
    simp [addUnlessA, addUnlessB]
  constructor
  · rw [exists_executable_perm_iff_acyclic enabled noClash]
    intro acyclic
    have edgeAB : BeforeOn label [addUnlessA, addUnlessB] addUnlessA addUnlessB :=
      ⟨by simp, by simp, by simp [addUnlessA, addUnlessB],
        Or.inr ⟨⟨isOut, ∅⟩, by simp [addUnlessA], 41, by simp [addUnlessB], rfl⟩⟩
    have edgeBA : BeforeOn label [addUnlessA, addUnlessB] addUnlessB addUnlessA :=
      ⟨by simp, by simp, by simp [addUnlessA, addUnlessB],
        Or.inr ⟨⟨isOut, ∅⟩, by simp [addUnlessB], 40, by simp [addUnlessA], rfl⟩⟩
    exact acyclic addUnlessA (.tail (.single edgeAB) edgeBA)
  · refine (amalgamate_enabled_iff enabled).mpr ?_
    intro e inE d inD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inE inD
    rcases inE with rfl | rfl <;> rcases inD with rfl | rfl <;> decide

/-- **`every` as a synchronous update.** The amalgamation of the two absence-guarded rows makes
both outputs, a store that no serialization of the rows reaches: run one after the other, the
second is disabled. -/
theorem every_synchronous_update :
    fire {0} (amalgamate [addUnlessA, addUnlessB]) = {0, 40, 41} ∧
      ¬ Enabled label (fire {0} addUnlessA) addUnlessB ∧
      ¬ Enabled label (fire {0} addUnlessB) addUnlessA := by
  refine ⟨by decide, fun enabled => ?_, fun enabled => ?_⟩
  · have holds := enabled.queries_hold ⟨isOut, ∅⟩ (by simp [addUnlessB])
    revert holds
    decide
  · have holds := enabled.queries_hold ⟨isOut, ∅⟩ (by simp [addUnlessA])
    revert holds
    decide

/-! ### Value queries are not decided pair by pair -/

/-- Take the only `tok` (occurrence `20`). -/
def takeTok : Commit ℕ Atom := ⟨{20}, ∅, ∅, []⟩

/-- Make a fresh `tok` (occurrence `21`). -/
def makeTok : Commit ℕ Atom := ⟨∅, ∅, {21}, []⟩

/-- **A value query spoiled by one commit and restored by the next.** At `{20}` the region `tok`
has the labels `{tok}`. After taking `20` it has none; after also making `21` it has `{tok}`
again. An identity query of the region fails after both. -/
theorem value_query_restored :
    ¬ PredicateQuery.HoldsValue cellLabel (fire {20} takeTok) isTok {tok} ∧
      PredicateQuery.HoldsValue cellLabel (fireList {20} [takeTok, makeTok]) isTok {tok} ∧
      ¬ (⟨isTok, {20}⟩ : PredicateQuery ℕ Atom).Holds cellLabel (fireList {20} [takeTok, makeTok]) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold PredicateQuery.HoldsValue labels
    decide
  · unfold PredicateQuery.HoldsValue labels
    decide
  · decide

/-! ### Matched at one snapshot, acyclic precedence, `every` enabled -/

/-- **Positive control**: the taker and the reader are matched at `{0}`: the taker takes from it,
and both make fresh occurrences. -/
theorem taker_reader_matched : MatchedAt {0} [taker, reader] := by
  unfold MatchedAt; decide

/-- **Negative control**: a commit that makes occurrence `0`, already in the snapshot `{0}`, is not
matched there, whatever the other rows do. -/
theorem remake_not_matched : ¬ MatchedAt {0} [reader, (Commit.makeOne 0 : Commit ℕ Atom)] := by
  unfold MatchedAt; decide

/-- **Negative control**: write skew is a precedence cycle. `skewB` takes what `skewA` keeps and
`skewA` takes what `skewB` keeps, so each must precede the other. -/
theorem write_skew_cyclic : ¬ Acyclic skewLabel [skewA, skewB] := by
  intro acyclic
  have different : skewA ≠ skewB := fun same => absurd (congrArg Commit.taken same) (by decide)
  have first : BeforeOn skewLabel [skewA, skewB] skewA skewB :=
    ⟨by simp, by simp, different, by unfold Spoils WritesInto; decide⟩
  have second : BeforeOn skewLabel [skewA, skewB] skewB skewA :=
    ⟨by simp, by simp, Ne.symm different, by unfold Spoils WritesInto; decide⟩
  exact acyclic skewA (Relation.TransGen.tail (Relation.TransGen.single first) second)

/-- **Positive control**: `every` fires two readers of one token at `{0}`: each is enabled, they do
not clash, and their amalgamation keeps the token once and makes both outputs. -/
theorem readers_every_enabled : EveryEnabled label {0} [reader, reader₂] := by
  rw [everyEnabled_iff]
  unfold Clash
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
