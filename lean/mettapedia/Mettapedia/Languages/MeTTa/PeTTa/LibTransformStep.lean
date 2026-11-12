import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.OrderedStore

/-!
# A firing of the library's model is an occurrence commit

`LibTransform` models CeTTa's plain-PeTTa `transform` on a store that is a list of atoms.
The step of the calculus acts on occurrences: distinct identities with labels, of which a
firing takes some, keeps some, and makes new ones (`OccurrenceCommits.Enabled`,
`Selection`, `Interface.OrderedStore.publish`). This module connects the two.

A store of the model is represented by a list of distinct occurrences in the store's order
(`Represents`), so the order `once` and the first validating candidate read is state, and
is kept.

* `realizes_iff`: a footprint has a selection (distinct present occurrences for its takes,
  present occurrences apart from them for its reads, with the footprint's labels) exactly
  when the model's validation holds **and** every atom of the footprint is stored. The
  second half is needed: validation counts takes only (`ghost_read_validates`), and it is
  the candidate walk that finds each read atom in the store (`candidate_stored`). Reads may
  share one occurrence; takes may not (`Controls.two_reads_share_one_copy`,
  `Controls.take_and_read_two_copies`, `Controls.take_and_read_one_copy`).
* `Realizes.enabled`: such a selection is an enabled commit.
* `commit_publishes`: the model's commit leaves a store represented by a permutation of
  the ordered publication `publish rows selection`. It is a permutation and not always the
  publication itself because the plain library removes every copy of a taken atom and
  stores the surplus copies again at the end (`commit_moves_surplus`); with reads alone the
  rows are unchanged (`commit_of_reads_represents`).
* `fire_eq_some_iff_first_realized`: a firing commits the first candidate, in candidate
  order, whose footprint has a selection; `fire_eq_none_iff_unrealized`: it fires nothing
  exactly when no candidate's footprint has one.
* `fire_publishes`: a firing is an enabled commit of the fired candidate's footprint, and
  the store it leaves is represented by a permutation of the ordered publication, whose
  occurrences are those of the occurrence firing.

Scope: this is the occurrence level. The equations a firing tells (its patterns against the
labels it selected) and the admission of the first-order step come on top of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Selection)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.OrderedStore
  (survivors publish publish_present)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)
open LibTransform

variable {O : Type} [DecidableEq O]

/-- A store of the model, as distinct occurrences in the store's order. -/
structure Represents (label : O → Atom) (rows : List O) (s : Store) : Prop where
  distinct : rows.Nodup
  labels : rows.map label = s

/-- A selection realizes a footprint at `rows`: distinct present occurrences for its takes,
present occurrences apart from them for its reads, each with the label the footprint names,
in footprint order; it makes nothing. -/
structure Realizes (label : O → Atom) (rows : List O) (fp : Footprint) (sel : Selection O) :
    Prop where
  taken_distinct : sel.taken.Nodup
  taken_present : ∀ o ∈ sel.taken, o ∈ rows
  read_present : ∀ o ∈ sel.read, o ∈ rows
  apart : ∀ o ∈ sel.read, o ∉ sel.taken
  taken_labels : sel.taken.map label = takes fp
  read_labels : sel.read.map label = reads fp
  made_none : sel.made = []

/-- A realizing selection is an enabled commit. -/
theorem Realizes.enabled {label : O → Atom} {rows : List O} {fp : Footprint} {sel : Selection O}
    (real : Realizes label rows fp sel) :
    Enabled label rows.toFinset (sel.commit (T := Atom)) where
  taken_subset := fun o member =>
    List.mem_toFinset.mpr (real.taken_present o (List.mem_toFinset.mp member))
  kept_subset := fun o member =>
    List.mem_toFinset.mpr (real.read_present o (List.mem_toFinset.mp member))
  apart := Finset.disjoint_left.mpr fun o taken kept =>
    real.apart o (List.mem_toFinset.mp kept) (List.mem_toFinset.mp taken)
  fresh := by simp [Selection.commit, real.made_none]
  queries_hold := by simp [Selection.commit]

/-! ## Choosing occurrences -/

/-- Distinct occurrences for a list of labels that the rows cover with multiplicity. -/
theorem exists_taken {label : O → Atom} :
    ∀ (l : List Atom) (rows : List O), rows.Nodup →
      (l : Multiset Atom) ≤ ((rows.map label : List Atom) : Multiset Atom) →
      ∃ taken : List O, taken.Nodup ∧ (∀ o ∈ taken, o ∈ rows) ∧ taken.map label = l
  | [], _, _, _ => ⟨[], List.nodup_nil, by simp, rfl⟩
  | a :: l, rows, distinct, le => by
      have member : a ∈ rows.map label := by
        have inside : a ∈ ((rows.map label : List Atom) : Multiset Atom) :=
          Multiset.mem_of_le le (by simp)
        simpa using inside
      obtain ⟨o, present, rfl⟩ := List.mem_map.mp member
      have rest : (l : Multiset Atom) ≤
          (((rows.erase o).map label : List Atom) : Multiset Atom) := by
        have erased := Multiset.erase_le_erase (label o) le
        rw [← Multiset.cons_coe, Multiset.erase_cons_head, ← Multiset.map_coe,
          ← Multiset.map_erase_of_mem label (rows : Multiset O) (by simpa using present),
          Multiset.coe_erase, Multiset.map_coe] at erased
        exact erased
      obtain ⟨taken, nodup, sub, labels⟩ := exists_taken l (rows.erase o) (distinct.erase o) rest
      refine ⟨o :: taken, List.nodup_cons.mpr ⟨fun inside => ?_, nodup⟩, ?_, by simp [labels]⟩
      · exact (distinct.mem_erase_iff.mp (sub o inside)).1 rfl
      · intro x inside
        rcases List.mem_cons.mp inside with rfl | inside
        · exact present
        · exact List.mem_of_mem_erase (sub x inside)

omit [DecidableEq O] in
/-- The copies of a label among occurrences, as a filter. -/
theorem count_map_label (label : O → Atom) (l : List O) (b : Atom) :
    (l.map label).count b = (l.filter fun o => decide (label o = b)).length := by
  induction l with
  | nil => rfl
  | cons o l ih =>
      by_cases same : label o = b
      · simp [same, ih]
      · simp [same, ih]

/-- When the rows hold more copies of a label than the taken occurrences do, one of the
rows with that label is not taken. -/
theorem exists_spare {label : O → Atom} {rows taken : List O} (distinct : rows.Nodup) (b : Atom)
    (more : (taken.map label).count b < (rows.map label).count b) :
    ∃ o ∈ rows, o ∉ taken ∧ label o = b := by
  by_contra none
  have sub : (rows.filter fun o => decide (label o = b)) ⊆
      (taken.filter fun o => decide (label o = b)) := by
    intro o inside
    obtain ⟨present, same⟩ := List.mem_filter.mp inside
    have taken' : o ∈ taken := by
      by_contra absent
      exact none ⟨o, present, absent, by simpa using same⟩
    exact List.mem_filter.mpr ⟨taken', same⟩
  have le := (List.subperm_of_subset (distinct.filter _) sub).length_le
  rw [count_map_label, count_map_label] at more
  omega

omit [DecidableEq O] in
/-- Occurrences for a list of labels, each chosen among the rows that are not taken. -/
theorem exists_kept {label : O → Atom} {rows taken : List O} :
    ∀ l : List Atom, (∀ b ∈ l, ∃ o ∈ rows, o ∉ taken ∧ label o = b) →
      ∃ kept : List O, (∀ o ∈ kept, o ∈ rows) ∧ (∀ o ∈ kept, o ∉ taken) ∧ kept.map label = l
  | [], _ => ⟨[], by simp, by simp, rfl⟩
  | b :: l, each => by
      obtain ⟨o, present, free, rfl⟩ := each b (by simp)
      obtain ⟨kept, presents, frees, labels⟩ :=
        exists_kept l fun b inside => each b (List.mem_cons_of_mem _ inside)
      refine ⟨o :: kept, ?_, ?_, by simp [labels]⟩
      · intro x inside
        rcases List.mem_cons.mp inside with rfl | inside
        · exact present
        · exact presents x inside
      · intro x inside
        rcases List.mem_cons.mp inside with rfl | inside
        · exact free
        · exact frees x inside

/-! ## Validation, the walk, and a selection -/

/-- **A footprint has a selection exactly when it validates and all its atoms are stored.**
Validation alone does not give the second half. -/
theorem realizes_iff {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) (fp : Footprint) :
    (∃ sel : Selection O, Realizes label rows fp sel) ↔
      valid s fp = true ∧ ∀ e ∈ fp, e.2 ∈ s := by
  constructor
  · rintro ⟨sel, real⟩
    have covered : ∀ l : List O, l.Nodup → (∀ o ∈ l, o ∈ rows) →
        (l.map label).Subperm s := fun l nodup sub => by
      rw [← rep.labels]
      have le : (l : Multiset O) ≤ (rows : Multiset O) :=
        Multiset.coe_le.mpr (List.subperm_of_subset nodup sub)
      exact Multiset.coe_le.mp (by simpa using Multiset.map_le_map (f := label) le)
    refine ⟨(valid_iff_le s fp).mpr ⟨?_, ?_⟩, ?_⟩
    · have := covered sel.taken real.taken_distinct real.taken_present
      rw [real.taken_labels] at this
      exact Multiset.coe_le.mpr this
    · intro a _ read
      have inside : a ∈ sel.read.map label := by rw [real.read_labels]; exact read
      obtain ⟨o, kept, rfl⟩ := List.mem_map.mp inside
      have nodup : (o :: sel.taken).Nodup :=
        List.nodup_cons.mpr ⟨real.apart o kept, real.taken_distinct⟩
      have sub : ∀ x ∈ o :: sel.taken, x ∈ rows := by
        intro x member
        rcases List.mem_cons.mp member with rfl | member
        · exact real.read_present x kept
        · exact real.taken_present x member
      have le := (covered (o :: sel.taken) nodup sub).count_le (label o)
      rw [List.map_cons, real.taken_labels, List.count_cons_self] at le
      omega
    · rintro ⟨m, a⟩ member
      have stored : ∀ o ∈ rows, label o ∈ s := fun o present => by
        rw [← rep.labels]
        exact List.mem_map_of_mem present
      cases m with
      | take =>
          have inside : a ∈ sel.taken.map label := by
            rw [real.taken_labels]; exact mem_takes.mpr member
          obtain ⟨o, taken, rfl⟩ := List.mem_map.mp inside
          exact stored o (real.taken_present o taken)
      | read =>
          have inside : a ∈ sel.read.map label := by
            rw [real.read_labels]; exact mem_reads.mpr member
          obtain ⟨o, kept, rfl⟩ := List.mem_map.mp inside
          exact stored o (real.read_present o kept)
  · rintro ⟨ok, stored⟩
    obtain ⟨le, spare⟩ := (valid_iff_le s fp).mp ok
    obtain ⟨taken, nodup, present, labels⟩ :=
      exists_taken (label := label) (takes fp) rows rep.distinct (by rw [rep.labels]; exact le)
    have each : ∀ b ∈ reads fp, ∃ o ∈ rows, o ∉ taken ∧ label o = b := by
      intro b read
      by_cases also : b ∈ takes fp
      · refine exists_spare rep.distinct b ?_
        rw [labels, rep.labels]
        exact spare b also read
      · have inside : b ∈ rows.map label := by
          rw [rep.labels]; exact stored (.read, b) (mem_reads.mp read)
        obtain ⟨o, present', rfl⟩ := List.mem_map.mp inside
        refine ⟨o, present', fun taken' => also ?_, rfl⟩
        rw [← labels]
        exact List.mem_map_of_mem taken'
    obtain ⟨kept, presents, frees, keptLabels⟩ := exists_kept (reads fp) each
    exact ⟨⟨taken, kept, []⟩, nodup, present, presents, frees, labels, keptLabels, rfl⟩

/-- Validation counts takes only: a footprint that reads an atom the store does not hold
validates. The walk is what finds each read atom in the store. -/
theorem ghost_read_validates (ghost : Atom) : valid [] [(Mode.read, ghost)] = true := rfl

/-- That footprint has no selection. -/
theorem ghost_read_unrealized {label : O → Atom} (ghost : Atom) :
    ¬ ∃ sel : Selection O, Realizes label [] [(Mode.read, ghost)] sel := by
  intro real
  have stored := ((realizes_iff (label := label) ⟨List.nodup_nil, rfl⟩ _).mp real).2
    (.read, ghost) (by simp)
  simp at stored

/-! ### A take and a read of one atom need two copies -/

namespace Controls

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"

/-- Occurrences `0` and `2` carry `a`, occurrence `1` carries `b`. -/
def label (o : Nat) : Atom := if o = 1 then b else a

/-- With two copies of `a`, one is taken and the other read. -/
theorem take_and_read_two_copies :
    ∃ sel : Selection Nat, Realizes label [0, 1, 2] [(Mode.take, a), (Mode.read, a)] sel :=
  ⟨⟨[0], [2], []⟩, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

/-- With one copy the footprint has no selection: the read needs an occurrence apart from
the taken one. -/
theorem take_and_read_one_copy :
    ¬ ∃ sel : Selection Nat, Realizes label [0, 1] [(Mode.take, a), (Mode.read, a)] sel := by
  intro real
  have ok := ((realizes_iff (label := label) (s := [a, b]) ⟨by decide, by decide⟩ _).mp real).1
  revert ok
  decide

/-- Two reads of `a` share its one occurrence. -/
theorem two_reads_share_one_copy :
    ∃ sel : Selection Nat, Realizes label [0, 1] [(Mode.read, a), (Mode.read, a)] sel :=
  ⟨⟨[], [0, 0], []⟩, by decide, by decide, by decide, by decide, by decide, by decide, rfl⟩

end Controls

/-! ## The commit and the ordered publication -/

/-- A permutation of the image of a list is the image of a permutation of the list. -/
theorem perm_map_lift {β : Type} (f : O → β) :
    ∀ (l : List β) (xs : List O), l.Perm (xs.map f) → ∃ ys : List O, ys.Perm xs ∧ ys.map f = l
  | [], xs, perm => by
      have empty : xs = [] := List.map_eq_nil_iff.mp (List.perm_nil.mp perm.symm)
      exact ⟨[], by rw [empty], rfl⟩
  | a :: l, xs, perm => by
      have inside : a ∈ xs.map f := perm.subset (by simp)
      obtain ⟨x, present, rfl⟩ := List.mem_map.mp inside
      have split : xs.Perm (x :: xs.erase x) := List.perm_cons_erase present
      have rest : l.Perm ((xs.erase x).map f) :=
        List.Perm.cons_inv (perm.trans (split.map f))
      obtain ⟨ys, same, image⟩ := perm_map_lift f l (xs.erase x) rest
      exact ⟨x :: ys, (same.cons x).trans split.symm, by simp [image]⟩

/-- The rows that survive a selection carry the labels the model's commit leaves. -/
theorem survivors_labels {label : O → Atom} {rows : List O} {s : Store} {fp : Footprint}
    {sel : Selection O} (rep : Represents label rows s) (real : Realizes label rows fp sel) :
    (commit fp s).Perm ((survivors rows sel.taken).map label) := by
  have chosen : (rows.filter fun o => decide (o ∈ sel.taken)).Perm sel.taken := by
    refine (List.perm_ext_iff_of_nodup (rep.distinct.filter _) real.taken_distinct).mpr fun o => ?_
    simp only [List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨real.taken_present o h, h⟩⟩
  have split : rows.Perm (sel.taken ++ survivors rows sel.taken) := by
    have parts := List.filter_append_perm (fun o => decide (o ∈ sel.taken)) rows
    refine parts.symm.trans (List.Perm.append chosen ?_)
    simp [survivors]
  have labelled : (s : Multiset Atom) =
      (takes fp : Multiset Atom) + (((survivors rows sel.taken).map label : List Atom) :
        Multiset Atom) := by
    rw [← rep.labels, ← real.taken_labels, Multiset.coe_add, ← List.map_append]
    exact Multiset.coe_eq_coe.mpr (split.map label)
  refine Multiset.coe_eq_coe.mp ?_
  rw [commit_coe, labelled, add_tsub_cancel_left]

/-- **The model's commit is the ordered publication, up to a permutation.** The store the
commit leaves is represented by distinct occurrences that are a permutation of
`publish rows sel`. -/
theorem commit_publishes {label : O → Atom} {rows : List O} {s : Store} {fp : Footprint}
    {sel : Selection O} (rep : Represents label rows s) (real : Realizes label rows fp sel) :
    ∃ rows' : List O, rows'.Perm (publish rows sel) ∧ Represents label rows' (commit fp s) := by
  obtain ⟨rows', same, image⟩ :=
    perm_map_lift label (commit fp s) (survivors rows sel.taken) (survivors_labels rep real)
  have published : publish rows sel = survivors rows sel.taken := by
    simp [publish, real.made_none]
  refine ⟨rows', by rw [published]; exact same, ?_, image⟩
  exact same.nodup_iff.mpr (rep.distinct.filter _)

omit [DecidableEq O] in
/-- With reads alone the commit leaves the rows as they are. -/
theorem commit_of_reads_represents {label : O → Atom} {rows : List O} {s : Store}
    {fp : Footprint} (rep : Represents label rows s) (reads : ∀ e ∈ fp, e.1 = .read) :
    Represents label rows (commit fp s) := by
  rw [commit_of_reads reads]
  exact rep

/-- The permutation is needed: taking one of two copies of `a` in `[a, b, a]` leaves the
model's store as `[b, a]`, where the publication of taking the first occurrence keeps the
order `[b, a]` and that of taking the last would keep `[a, b]`. The model moves the surplus
copy to the end whichever occurrence is taken. -/
theorem commit_moves_surplus (a b : Atom) (different : b ≠ a) :
    commit [(Mode.take, a)] [a, b, a] = [b, a] := by
  have differentB : (b != a) = true := by simpa using different
  have once : List.count a [b, a] = 1 := by simp [different]
  simp [commit, applyTakes, commitOne, differentB, once]

/-! ## Candidates and firings -/

/-- Every atom of a candidate's footprint is stored: the walk found it there. -/
theorem candidate_stored {s : Store} {g : Footprint} {src : Sources} {c : Candidate}
    (member : c ∈ candidates s g src) : ∀ e ∈ c.footprint, e.2 ∈ s := by
  obtain ⟨k, walked, rfl⟩ := List.mem_map.mp member
  intro e inside
  rcases List.mem_append.mp inside with kernel | later
  · exact (walk_sound walked).2 e kernel
  · obtain ⟨row, isRow, inRow⟩ := List.mem_flatMap.mp later
    cases every : src.every with
    | none =>
        simp only [every, List.mem_singleton] at isRow
        subst isRow
        simp at inRow
    | some ext =>
        simp only [every] at isRow
        exact (walk_sound isRow).2 e inRow

/-- For a candidate, validating is having a selection. -/
theorem candidate_valid_iff {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) {g : Footprint} {src : Sources} {c : Candidate}
    (member : c ∈ candidates s g src) :
    valid s c.footprint = true ↔ ∃ sel : Selection O, Realizes label rows c.footprint sel := by
  rw [realizes_iff rep]
  exact ⟨fun ok => ⟨ok, candidate_stored member⟩, fun both => both.1⟩

/-- **A firing commits the first candidate, in candidate order, whose footprint has a
selection.** -/
theorem fire_eq_some_iff_first_realized {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) {g : Footprint} {src : Sources} {emit : Subst → Answers}
    {out : Answers} :
    LibTransform.fire s g src emit = some (s', out) ↔
      ∃ pre c post, candidates s g src = pre ++ c :: post ∧
        (∀ d ∈ pre, ¬ ∃ sel : Selection O, Realizes label rows d.footprint sel) ∧
        (∃ sel : Selection O, Realizes label rows c.footprint sel) ∧
        s' = commit c.footprint s ∧ out = c.instances emit := by
  rw [fire_eq_some_iff]
  constructor
  · rintro ⟨pre, c, post, split, before, ok, store, answers⟩
    have inC : c ∈ candidates s g src := by rw [split]; simp
    refine ⟨pre, c, post, split, fun d inPre real => ?_, (candidate_valid_iff rep inC).mp ok,
      store, answers⟩
    have inD : d ∈ candidates s g src := by rw [split]; simp [inPre]
    have := (candidate_valid_iff rep inD).mpr real
    rw [before d inPre] at this
    exact Bool.false_ne_true this
  · rintro ⟨pre, c, post, split, before, real, store, answers⟩
    have inC : c ∈ candidates s g src := by rw [split]; simp
    refine ⟨pre, c, post, split, fun d inPre => ?_, (candidate_valid_iff rep inC).mpr real,
      store, answers⟩
    have inD : d ∈ candidates s g src := by rw [split]; simp [inPre]
    by_contra notFalse
    exact before d inPre
      ((candidate_valid_iff rep inD).mp (by simpa using notFalse))

/-- **A firing fires nothing exactly when no candidate's footprint has a selection.** -/
theorem fire_eq_none_iff_unrealized {label : O → Atom} {rows : List O} {s : Store}
    (rep : Represents label rows s) {g : Footprint} {src : Sources} {emit : Subst → Answers} :
    LibTransform.fire s g src emit = none ↔
      ∀ c ∈ candidates s g src, ¬ ∃ sel : Selection O, Realizes label rows c.footprint sel := by
  rw [fire_eq_none_iff]
  constructor
  · intro refused c member real
    have := (candidate_valid_iff rep member).mpr real
    rw [refused c member] at this
    exact Bool.false_ne_true this
  · intro none c member
    by_contra notFalse
    exact none c member ((candidate_valid_iff rep member).mp (by simpa using notFalse))

/-- **A firing is an enabled occurrence commit, published in order.** The fired candidate's
footprint has a selection; that selection is an enabled commit; the store the firing leaves
is represented by a permutation of the ordered publication, and its occurrences are those
of the occurrence firing. -/
theorem fire_publishes {label : O → Atom} {rows : List O} {s s' : Store}
    (rep : Represents label rows s) {g : Footprint} {src : Sources} {emit : Subst → Answers}
    {out : Answers} (fired : LibTransform.fire s g src emit = some (s', out)) :
    ∃ c ∈ candidates s g src, ∃ (sel : Selection O) (rows' : List O),
      Realizes label rows c.footprint sel ∧
      Enabled label rows.toFinset (sel.commit (T := Atom)) ∧
      rows'.Perm (publish rows sel) ∧ Represents label rows' s' ∧
      rows'.toFinset =
        Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire
          rows.toFinset (sel.commit (T := Unit)) ∧
      out = c.instances emit := by
  obtain ⟨pre, c, post, split, _, ⟨sel, real⟩, rfl, rfl⟩ :=
    (fire_eq_some_iff_first_realized rep).mp fired
  obtain ⟨rows', same, rep'⟩ := commit_publishes rep real
  refine ⟨c, by rw [split]; simp, sel, rows', real, real.enabled, same, rep', ?_, rfl⟩
  rw [← publish_present]
  exact List.toFinset_eq_of_perm _ _ same

end Mettapedia.Languages.MeTTa.PeTTa.LibTransformStep
