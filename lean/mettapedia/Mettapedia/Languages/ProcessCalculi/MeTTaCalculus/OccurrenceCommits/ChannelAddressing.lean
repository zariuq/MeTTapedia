import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ReactiveTransitions
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

/-!
# Channels as name-scoped regions: what is the same as a space, and what is not

Every occurrence lives at an address, a *name* (`loc : R → N`). A process holds some names, its
**rights** (`held : N → Bool`). A commit is **scoped** to the rights when everything it takes, keeps
or makes lives at a held name and the region of each of its predicate queries lies inside the held
names (`Scoped`). A channel is a region addressed by one name; a process that does not hold the name
cannot reach it. A space region that a pattern addresses may span names that the reader does not
hold: a pattern variable in the name position enumerates every name.

## The weak difference: one kind of commit

Sending, receiving, peeking, persistent receipt, joins and choice are commits of the one
semantic object (`Commits`). Nothing about a channel is a new kind of commit, so exactness, waves,
traces and the policy lattice apply to channels unchanged. On a located network, a scoped take
and a scoped read at one name are exactly the located consume and observe steps of
`SpaceInteraction` (`project_fire_take`, `project_keep`).

## The strong difference: the laws of name-scoped contexts

What changes is the class of processes that can exist beside a program, and with it the laws.

* **Restriction to rights is a graded comonad on stores.** `restrict held S` keeps the occurrences
  at held names. It is deflationary and idempotent (an interior operator: the comonad laws on the
  poset of stores), monotone, a Boolean homomorphism, and graded by rights under meet:
  restricting twice restricts to the meet of the rights, and full rights restrict to nothing
  (`restrict_subset`, `restrict_idem`, `restrict_restrict`, `restrict_top`).
* **Scoped commits factor through it** (`enabled_iff_restrict`, `restrict_fire`,
  `outside_fire`): a scoped commit is enabled at a store exactly when it is enabled at the
  store's held part, its firing on the held part is the held part of its firing, and it leaves
  every unheld occurrence as it was. This is the naturality that presheaf models over finite sets
  of names and injections build in: a process at a stage of known names does not depend on names
  outside its stage.
* **Non-interference for non-holders** (`noninterference`): stores that agree on the held names
  run every list of scoped commits alike, and reach stores that agree on the held names.
* **The ν-garbage law** (`garbage_unobservable`): occurrences at a name nobody holds are
  unobservable: adding them changes no scoped process's run.
* **Stable predicate queries inside a scope** (`scope_read_stable`): an absence, or any other
  predicate query, at a name that only its owner holds stays valid across any run of the other
  processes' scoped commits: the scope closes the query's world. If the name is shared (extruded),
  one send by the other process falsifies it (`Controls.extruded_absence_falsified`).
* **A pattern-addressed region has none of these** (`Controls.wildcard_breaks_noninterference`):
  an absence read over every name tells apart two stores that agree on the reader's names.

So a channel is not a second kind of region: it is a space region together with restricted
rights (no access to an unheld name, no enumeration of names). What must be native is the name
and the rights: a fresh name that no pattern can enumerate, and commits checked against the
holder's rights. Bare nominal equivariance (invariance under renaming every name at once) is
weaker than non-interference: it does not exclude a reader that enumerates names, so it does not
buy these laws by itself; the restriction comonad does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {N : Type w}

section Restriction

variable (label : O → R) (loc : R → N)

/-- The occurrences of a store at held names. -/
def restrict (held : N → Bool) (store : Finset O) : Finset O :=
  store.filter fun o => held (loc (label o)) = true

variable {label loc}

omit [DecidableEq O] in
theorem mem_restrict {held : N → Bool} {store : Finset O} {o : O} :
    o ∈ restrict label loc held store ↔ o ∈ store ∧ held (loc (label o)) = true := by
  simp [restrict]

omit [DecidableEq O] in
/-- **The held part is a region**: restriction to rights is `regionOf` with the region read
through the addresses. Every region law of `Commits` therefore holds of the held part. -/
theorem restrict_eq_regionOf (held : N → Bool) (store : Finset O) :
    restrict label loc held store = regionOf label store (fun r => held (loc r)) := rfl

omit [DecidableEq O] in
/-- Nothing at the held names is the absence read of their region (`AbsenceHolds`). -/
theorem restrict_eq_empty_iff (held : N → Bool) (store : Finset O) :
    restrict label loc held store = ∅ ↔ AbsenceHolds label (fun r => held (loc r)) store :=
  Iff.rfl

omit [DecidableEq O] in
/-- The counit: the held part is part of the store. -/
theorem restrict_subset (held : N → Bool) (store : Finset O) :
    restrict label loc held store ⊆ store :=
  Finset.filter_subset _ _

omit [DecidableEq O] in
/-- Idempotence: restricting the held part changes nothing. -/
theorem restrict_idem (held : N → Bool) (store : Finset O) :
    restrict label loc held (restrict label loc held store) = restrict label loc held store := by
  ext o
  simp [mem_restrict]

omit [DecidableEq O] in
/-- **The grading.** Restricting twice restricts to the meet of the rights. -/
theorem restrict_restrict (held held' : N → Bool) (store : Finset O) :
    restrict label loc held (restrict label loc held' store) =
      restrict label loc (fun n => held n && held' n) store := by
  ext o
  simp only [mem_restrict, Bool.and_eq_true]
  tauto

omit [DecidableEq O] in
/-- Full rights restrict to nothing. -/
theorem restrict_top (store : Finset O) : restrict label loc (fun _ => true) store = store := by
  ext o
  simp [mem_restrict]

omit [DecidableEq O] in
theorem restrict_mono (held : N → Bool) {small large : Finset O} (sub : small ⊆ large) :
    restrict label loc held small ⊆ restrict label loc held large :=
  Finset.filter_subset_filter _ sub

theorem restrict_union (held : N → Bool) (X Y : Finset O) :
    restrict label loc held (X ∪ Y) = restrict label loc held X ∪ restrict label loc held Y :=
  Finset.filter_union _ _ _

theorem restrict_sdiff (held : N → Bool) (X Y : Finset O) :
    restrict label loc held (X \ Y) = restrict label loc held X \ restrict label loc held Y := by
  ext o
  simp only [mem_restrict, Finset.mem_sdiff]
  tauto

end Restriction

/-! ## Writes at a set of names

The frame law of regions (`regionOf_fire_subset_of_no_make`, `regionOf_subset_fire_of_no_take`),
read through the addresses. The laws of a missing `send` or `receive` in `InteractionTypes.Facets`
and the polarity laws of `RegionPermissions.ReadPolarity` are its instances. -/

section Writes

variable (label : O → R) (loc : R → N) (A : N → Bool)

/-- A commit makes nothing at the names of `A`. -/
def MakesOutside (c : Commit O R) : Prop := ∀ o ∈ c.made, A (loc (label o)) = false

/-- A commit takes nothing at the names of `A`. -/
def TakesOutside (c : Commit O R) : Prop := ∀ o ∈ c.taken, A (loc (label o)) = false

variable {label loc A}

/-- A commit that makes nothing at `A` only shrinks what is there. -/
theorem restrict_fire_subset_of_makesOutside {c : Commit O R}
    (outside : MakesOutside label loc A c) (S : Finset O) :
    restrict label loc A (fire S c) ⊆ restrict label loc A S :=
  regionOf_fire_subset_of_no_make (label := label) (region := fun r => A (loc r)) outside

/-- A commit that takes nothing at `A` only grows what is there. -/
theorem restrict_subset_fire_of_takesOutside {c : Commit O R}
    (outside : TakesOutside label loc A c) (S : Finset O) :
    restrict label loc A S ⊆ restrict label loc A (fire S c) :=
  regionOf_subset_fire_of_no_take (label := label) (region := fun r => A (loc r)) outside

/-- Along a run that makes nothing at `A`, what is there only shrinks. -/
theorem restrict_fireList_subset_of_makesOutside {run : List (Commit O R)}
    (outside : ∀ e ∈ run, MakesOutside label loc A e) (S : Finset O) :
    restrict label loc A (fireList S run) ⊆ restrict label loc A S :=
  regionOf_fireList_subset_of_no_make (label := label) (region := fun r => A (loc r)) outside S

/-- Along a run that takes nothing at `A`, what is there only grows. -/
theorem restrict_subset_fireList_of_takesOutside {run : List (Commit O R)}
    (outside : ∀ e ∈ run, TakesOutside label loc A e) (S : Finset O) :
    restrict label loc A S ⊆ restrict label loc A (fireList S run) :=
  regionOf_subset_fireList_of_no_take (label := label) (region := fun r => A (loc r)) outside S

end Writes

/-- A commit is scoped to the rights: it takes, keeps and makes only at held names, and queries
only regions inside the held names. -/
structure Scoped (label : O → R) (loc : R → N) (held : N → Bool) (c : Commit O R) : Prop where
  taken : ∀ o ∈ c.taken, held (loc (label o)) = true
  kept : ∀ o ∈ c.kept, held (loc (label o)) = true
  made : ∀ o ∈ c.made, held (loc (label o)) = true
  queries : ∀ read ∈ c.queries, ∀ r, read.region r = true → held (loc r) = true

section Factorization

variable {label : O → R} {loc : R → N} {held : N → Bool} {c : Commit O R}

omit [DecidableEq O] in
theorem regionOf_restrict {region : R → Bool} (inside : ∀ r, region r = true → held (loc r) = true)
    (store : Finset O) :
    regionOf label (restrict label loc held store) region = regionOf label store region := by
  ext o
  simp only [mem_regionOf, mem_restrict]
  constructor
  · rintro ⟨⟨member, _⟩, inRegion⟩
    exact ⟨member, inRegion⟩
  · rintro ⟨member, inRegion⟩
    exact ⟨⟨member, inside _ inRegion⟩, inRegion⟩

omit [DecidableEq O] in
/-- **A scoped commit is enabled exactly when it is enabled at the held part.** -/
theorem enabled_iff_restrict (inScope : Scoped label loc held c) (store : Finset O) :
    Enabled label store c ↔ Enabled label (restrict label loc held store) c := by
  constructor
  · intro enabled
    exact
      { taken_subset := fun o taken => mem_restrict.mpr ⟨enabled.taken_subset taken, inScope.taken o taken⟩
        kept_subset := fun o kept => mem_restrict.mpr ⟨enabled.kept_subset kept, inScope.kept o kept⟩
        apart := enabled.apart
        fresh := Finset.disjoint_of_subset_right (restrict_subset held store) enabled.fresh
        queries_hold := fun read member => by
          have := enabled.queries_hold read member
          unfold PredicateQuery.Holds at this ⊢
          rw [regionOf_restrict (inScope.queries read member)]
          exact this }
  · intro enabled
    exact
      { taken_subset := fun o taken => (mem_restrict.mp (enabled.taken_subset taken)).1
        kept_subset := fun o kept => (mem_restrict.mp (enabled.kept_subset kept)).1
        apart := enabled.apart
        fresh := by
          refine Finset.disjoint_left.mpr fun o made inStore => ?_
          exact Finset.disjoint_left.mp enabled.fresh made
            (mem_restrict.mpr ⟨inStore, inScope.made o made⟩)
        queries_hold := fun read member => by
          have := enabled.queries_hold read member
          unfold PredicateQuery.Holds at this ⊢
          rw [regionOf_restrict (inScope.queries read member)] at this
          exact this }

/-- **Firing commutes with restriction** for a scoped commit. -/
theorem restrict_fire (inScope : Scoped label loc held c) (store : Finset O) :
    restrict label loc held (fire store c) = fire (restrict label loc held store) c := by
  ext o
  simp only [mem_restrict, mem_fire]
  constructor
  · rintro ⟨⟨inStore, notTaken⟩ | made, isHeld⟩
    · exact Or.inl ⟨⟨inStore, isHeld⟩, notTaken⟩
    · exact Or.inr made
  · rintro (⟨⟨inStore, isHeld⟩, notTaken⟩ | made)
    · exact ⟨Or.inl ⟨inStore, notTaken⟩, isHeld⟩
    · exact ⟨Or.inr made, inScope.made o made⟩

/-- **A scoped commit leaves every unheld occurrence as it was.** -/
theorem outside_fire (inScope : Scoped label loc held c) (store : Finset O) :
    restrict label loc (fun n => !held n) (fire store c) = restrict label loc (fun n => !held n) store := by
  ext o
  simp only [mem_restrict, mem_fire, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨inStore, _⟩ | made, unheld⟩
    · exact ⟨inStore, unheld⟩
    · rw [inScope.made o made] at unheld; exact absurd unheld (by decide)
  · rintro ⟨inStore, unheld⟩
    refine ⟨Or.inl ⟨inStore, fun taken => ?_⟩, unheld⟩
    rw [inScope.taken o taken] at unheld; exact absurd unheld (by decide)

/-- **Non-interference for non-holders.** Two stores that agree on the held names run a list of
scoped commits alike, and reach stores that agree on the held names. -/
theorem noninterference {run : List (Commit O R)} (inScope : ∀ e ∈ run, Scoped label loc held e)
    {first second : Finset O}
    (agree : restrict label loc held first = restrict label loc held second) :
    (Executable label first run ↔ Executable label second run) ∧
      restrict label loc held (fireList first run) = restrict label loc held (fireList second run) := by
  induction run generalizing first second with
  | nil => exact ⟨⟨fun _ => .nil _, fun _ => .nil _⟩, agree⟩
  | cons e rest ih =>
      have scopedE := inScope e List.mem_cons_self
      have scopedRest : ∀ d ∈ rest, Scoped label loc held d := fun d member =>
        inScope d (List.mem_cons_of_mem _ member)
      have agreeNext : restrict label loc held (fire first e) = restrict label loc held (fire second e) := by
        rw [restrict_fire scopedE, restrict_fire scopedE, agree]
      obtain ⟨sameRun, sameEnd⟩ := ih scopedRest agreeNext
      refine ⟨?_, sameEnd⟩
      rw [executable_cons_iff, executable_cons_iff, enabled_iff_restrict scopedE first,
        enabled_iff_restrict scopedE second, agree, sameRun]

/-- **The ν-garbage law.** Occurrences at names that a process does not hold are unobservable to
its scoped commits: adding them changes neither which runs execute nor the held part of where they
end. -/
theorem garbage_unobservable {run : List (Commit O R)} (inScope : ∀ e ∈ run, Scoped label loc held e)
    {store garbage : Finset O} (unheld : ∀ o ∈ garbage, held (loc (label o)) = false) :
    (Executable label store run ↔ Executable label (store ∪ garbage) run) ∧
      restrict label loc held (fireList store run) =
        restrict label loc held (fireList (store ∪ garbage) run) := by
  apply noninterference inScope
  rw [restrict_union]
  have empty : restrict label loc held garbage = ∅ := by
    ext o
    simp only [mem_restrict, Finset.notMem_empty, iff_false, not_and]
    intro member isHeld
    rw [unheld o member] at isHeld
    exact absurd isHeld (by decide)
  rw [empty, Finset.union_empty]

/-- A scoped commit writes nothing inside a region whose names it does not hold. -/
theorem no_write_of_scoped {e : Commit O R} (inScope : Scoped label loc held e) {region : R → Bool}
    (unheldRegion : ∀ r, region r = true → held (loc r) = false) :
    ∀ o ∈ e.taken ∪ e.made, region (label o) = false := by
  intro o written
  by_contra inRegion
  have isUnheld := unheldRegion _ (by simpa using inRegion)
  rcases Finset.mem_union.mp written with taken | made
  · rw [inScope.taken o taken] at isUnheld; exact absurd isUnheld (by decide)
  · rw [inScope.made o made] at isUnheld; exact absurd isUnheld (by decide)

/-- **Stable predicate queries inside a scope.** A predicate query of a region at names the other
processes do not hold stays valid across any run of their scoped commits. -/
theorem scope_read_stable {others : N → Bool} {run : List (Commit O R)}
    (inScope : ∀ e ∈ run, Scoped label loc others e) {read : PredicateQuery O R}
    (private_ : ∀ r, read.region r = true → others (loc r) = false) {store : Finset O}
    (holds : read.Holds label store) : read.Holds label (fireList store run) :=
  holds_fireList_of_no_write (fun e member => no_write_of_scoped (inScope e member) private_) holds

end Factorization

/-! ## The located network: channels and spaces project to the same steps -/

section Projection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.SpaceInteraction

variable {A : Type v} [DecidableEq N] [DecidableEq A] {label : O → N × A}

/-- The located network of a store: at each name, the bag of atoms there. -/
def project (label : O → N × A) (store : Finset O) : Network N A :=
  fun n => ((store.filter fun o => (label o).1 = n).val.map fun o => (label o).2)

theorem project_erase {store : Finset O} {o : O} (member : o ∈ store) :
    project label (store.erase o) = Function.update (project label store) (label o).1
      ((project label store (label o).1).erase (label o).2) := by
  funext n
  by_cases same : n = (label o).1
  · subst same
    simp only [Function.update_self, project]
    have inFilter : o ∈ store.filter fun x => (label x).1 = (label o).1 :=
      Finset.mem_filter.mpr ⟨member, rfl⟩
    obtain ⟨rest, split⟩ := Multiset.exists_cons_of_mem (Finset.mem_def.mp inFilter)
    rw [Finset.filter_erase, Finset.erase_val, split, Multiset.erase_cons_head, Multiset.map_cons,
      Multiset.erase_cons_head]
  · rw [Function.update_of_ne same]
    simp only [project]
    congr 2
    ext x
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨_, inStore⟩, at_⟩
      exact ⟨inStore, at_⟩
    · rintro ⟨inStore, at_⟩
      refine ⟨⟨fun equal => same ?_, inStore⟩, at_⟩
      rw [← at_, equal]

/-- **A take at one name is the located consume step** of the network model. -/
theorem project_fire_take {store : Finset O} {o : O} (member : o ∈ store) :
    LocatedStep .consume (label o).1 (label o).2 (project label store)
      (project label (fire store (Commit.takeOne o : Commit O (N × A)))) := by
  have fireEq : fire store (Commit.takeOne o : Commit O (N × A)) = store.erase o := by
    ext x
    simp [mem_fire, Finset.mem_erase, and_comm]
  have present : (label o).2 ∈ project label store (label o).1 := by
    simp only [project, Multiset.mem_map]
    exact ⟨o, Finset.mem_def.mp (Finset.mem_filter.mpr ⟨member, rfl⟩), rfl⟩
  rw [fireEq, project_erase member]
  exact LocatedStep.consume _ (Multiset.cons_erase present).symm

omit [DecidableEq A] in
/-- **A read at one name is the located observe step**: the network is unchanged. -/
theorem project_keep {store : Finset O} {o : O} (member : o ∈ store) :
    LocatedStep .observe (label o).1 (label o).2 (project label store)
      (project label (fire store (Commit.keepOne o : Commit O (N × A)))) := by
  have fireEq : fire store (Commit.keepOne o : Commit O (N × A)) = store := by
    ext x
    simp [mem_fire]
  rw [fireEq]
  refine LocatedStep.observe ?_
  simp only [project, Multiset.mem_map]
  exact ⟨o, Finset.mem_def.mp (Finset.mem_filter.mpr ⟨member, rfl⟩), rfl⟩

end Projection

/-! ## Controls -/

namespace Controls

open Atom

/-- Occurrence `50` is a message at name `0`, `51` a message at name `1`. -/
def chanLabel : ℕ → ℕ × Atom
  | 50 => (0, out)
  | 51 => (1, out)
  | _ => (2, tok)

/-- Messages at name `0`. -/
def atZero : ℕ × Atom → Bool := fun r => r.1 == 0 && r.2 == out

/-- Messages at any name. -/
def anywhere : ℕ × Atom → Bool := fun r => r.2 == out

/-- The reader holds name `0`. -/
def holdsZero : ℕ → Bool := fun n => n == 0

/-- **A pattern-addressed region breaks non-interference.** The stores `∅` and `{51}` agree on
name `0`, the reader's only name. The scoped absence read at name `0` holds at both; the absence
read over every name holds at the first and fails at the second. -/
theorem wildcard_breaks_noninterference :
    restrict chanLabel Prod.fst holdsZero ∅ = restrict chanLabel Prod.fst holdsZero {51} ∧
      AbsenceHolds chanLabel atZero ∅ ∧ AbsenceHolds chanLabel atZero {51} ∧
      AbsenceHolds chanLabel anywhere ∅ ∧ ¬ AbsenceHolds chanLabel anywhere {51} := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩ <;> unfold AbsenceHolds <;> decide

/-- Send a message on name `0`. -/
def sendZero : Commit ℕ (ℕ × Atom) := ⟨∅, ∅, {50}, []⟩

/-- Send a message on name `1`. -/
def sendOne : Commit ℕ (ℕ × Atom) := ⟨∅, ∅, {51}, []⟩

/-- **Predicate queries are stable in scope, and fall when the name is shared.** A process
holding only name `1` cannot falsify the absence read at name `0`; a process that also holds
name `0` falsifies it with one send. -/
theorem extruded_absence_falsified :
    AbsenceHolds chanLabel atZero (fireList ∅ [sendOne]) ∧
      Scoped chanLabel Prod.fst (fun n => n == 1) sendOne ∧
      Scoped chanLabel Prod.fst holdsZero sendZero ∧
      ¬ AbsenceHolds chanLabel atZero (fireList ∅ [sendZero]) := by
  refine ⟨?_, ?_, ?_, by unfold AbsenceHolds; decide⟩
  · exact scope_read_stable (label := chanLabel) (loc := Prod.fst) (others := fun n => n == 1)
      (fun e member => by
        simp only [List.mem_singleton] at member
        subst member
        exact ⟨by simp [sendOne], by simp [sendOne], by decide, by simp [sendOne]⟩)
      (by intro r inRegion; simp only [atZero, Bool.and_eq_true, beq_iff_eq] at inRegion
          simp [inRegion.1])
      (by unfold PredicateQuery.Holds; decide)
  · exact ⟨by simp [sendOne], by simp [sendOne], by decide, by simp [sendOne]⟩
  · exact ⟨by simp [sendZero], by simp [sendZero], by decide, by simp [sendZero]⟩

/-- **Non-interference, an instance of its hypotheses**: the stores `∅` and `{51}` agree on
name `0`, and a send on name `0` runs alike from both. -/
theorem noninterference_instance :
    (Executable chanLabel ∅ [sendZero] ↔ Executable chanLabel {51} [sendZero]) ∧
      restrict chanLabel Prod.fst holdsZero (fireList ∅ [sendZero]) =
        restrict chanLabel Prod.fst holdsZero (fireList {51} [sendZero]) :=
  noninterference (label := chanLabel) (loc := Prod.fst) (held := holdsZero)
    (fun e member => by
      simp only [List.mem_singleton] at member
      subst member
      exact ⟨by simp [sendZero], by simp [sendZero], by decide, by simp [sendZero]⟩)
    (by decide)

/-! ### Writes outside a set of names -/

/-- **Positive control**: a send on name `1` makes nothing at name `0`. -/
theorem sendOne_makesOutside_zero : MakesOutside chanLabel Prod.fst holdsZero sendOne := by
  unfold MakesOutside; decide

/-- **Negative control**: a send on name `0` makes at name `0`. -/
theorem sendZero_not_makesOutside_zero : ¬ MakesOutside chanLabel Prod.fst holdsZero sendZero := by
  unfold MakesOutside; decide

/-- **Positive control**: taking the message at name `1` takes nothing at name `0`. -/
theorem takeOne_outside_zero : TakesOutside chanLabel Prod.fst holdsZero (Commit.takeOne 51) := by
  unfold TakesOutside; decide

/-- **Negative control**: taking the message at name `0` takes at name `0`. -/
theorem takeZero_not_outside_zero :
    ¬ TakesOutside chanLabel Prod.fst holdsZero (Commit.takeOne 50) := by
  unfold TakesOutside; decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
