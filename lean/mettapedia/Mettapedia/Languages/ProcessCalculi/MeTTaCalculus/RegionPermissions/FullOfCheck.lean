import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit

/-!
# The `full-of` check: a step rechecks every space an absence scanned

A transform of the Prime draft can require that something is absent: `(absent (read $l (msg $x)))`
holds when no message is in the space `$l`. The kernel decides it in two phases. Its **walk** scans
spaces for patterns and computes the answer; later, when the transform fires, its **step** checks
that the answer still holds and makes its changes at one instant. Code may run in between, and
other processes may write to the spaces meanwhile.

The draft records, for every space an absence scanned, an entry `(LOC REV PATTERN)`: the location
it scanned through, the space's revision when the scan began, and the pattern. The step carries
them as `(full-of ((LOC REV PATTERN) …))`, and the kernel checks each entry again when the step
happens (`ia_check_full_of`): the location still names its space through a handle with the
`observe` right, and the space is still at the revision the scan read.

## Words

* A **space** holds occurrences in position order (`View.rows`). Its **revision** (`View.rev`) is a
  counter the runtime moves on every write to it: a message arriving in an empty space at
  revision `0` moves it to `1`.
* A **view** is what the kernel sees at one moment: every space's occurrences and revision.
* A **location** names a space through a **handle**, which carries rights: `send`, `receive`,
  `peek`, `observe` (`resolve`). A space handle with fewer rights names the same space: a channel's
  `peek` handle may look at one message but may not ask whether the channel is empty, which needs
  `observe`.
* A **walk** (`Walk`) is the absence check as the kernel runs it: scan a location for a pattern,
  go on with the occurrences found there, and so on, until it stops with an answer. The scans may
  happen at different moments (`Walk.run`: the `i`-th scan reads the view `views i`), and each
  records its `(LOC REV PATTERN)` entry.
* The **atomic semantics** of the absence (`Walk.eval`) runs the same walk with every scan at one
  view: the absence evaluated at the moment of the step.
* A **predicate query** (`PredicateQuery`) asks which occurrences of a space match a pattern and
  holds while exactly those are there; "nothing of `&plain` matches `$x`" is the query an absence
  makes, and one arriving message spoils it.
* The **revision contract** (`KernelCommit.Tracks`): a space whose revision did not move holds the
  same occurrences in the same positions.

The draft also checks `observe` when the transform is formed and again at each scan. Here a
handle's rights do not change between the scan and the step, so the check at the step gives the
same verdict; the walk below only reads.

## Main results

* `run_atomic_of_fullOfOk` (headline): if a step passes the `full-of` check and the runtime keeps
  the revision contract, the walk gave exactly the answer and the entries that a walk run entirely
  at the moment of the step gives. So the step refines the atomic semantics:
  `step_answer_eq_atomic` says the step's answer is the absence evaluated at the moment of the step.
* `observe_of_fullOfOk` and `formed_of_fullOfOk`: such a step holds `observe` on every space it
  scanned, so the queries it makes are formed under the rights of the handles it holds.
* `absence_holds_at_step`: for `(absent (read LOC PATTERN))`, a step that fires holds, at the
  moment it happens, the specification's predicate query: no occurrence of the space matches.
* `stepOk_formed`: with the absence carried as `full-of` entries instead of `KernelCommit`'s
  `noRows` entry, the whole step (`KernelCommit.check` of its other entries, and the `full-of`
  check) is formed under the rights of the handles it names, the property that
  `KernelCommit.Controls.absence_of_sources_not_formed` shows failing for the `noRows` entry.

## Controls (`Controls`)

On the spaces of `KernelCommit.Controls` (a channel with no `observe`, a plain space with every
right), the walk of `(absent (read &plain $x))` finds the plain space empty at revision `0`:

* **stale revision refused**: a message arrives, the revision moves to `1`, and the step is refused;
  the absence evaluated at that moment is false (`stale_refused`);
* **without the recheck, a stale answer is accepted**: a check of the rights alone passes the same
  step, so the step would fire on an absence that no longer holds (`stale_absence_needs_recheck`);
* **missing `observe` refused**: scanning through the channel's holder or its `peek` handle is
  refused (`missing_observe_refused`); `KernelCommit`'s check, which asks for `observe` only at the
  transform's own location, accepts the second (`bypass_closed`);
* **the revision contract is needed**: a runtime that writes without moving the revision passes the
  check with a stale answer (`revision_contract_needed`);
* **positive**: a write to a space the walk did not scan leaves the step passing, with the answer
  of the moment of the step (`unscanned_write_passes`, `headline_instance`);
* **whole-space revisions**: a moved revision refuses the step even when the write was undone and
  the absence still holds (`undone_write_refused`); the check is safe, not exact.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.FullOfCheck

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit

/-- **An absence check as the kernel's walk runs it**: scan a location for a pattern and go on
with the occurrences found there, in position order; or stop with an answer. A conjunction scans
again for each occurrence found, with patterns made from it. -/
inductive Walk (Lc Pt O Ans : Type) where
  | stop (answer : Ans)
  | scan (loc : Lc) (pattern : Pt) (next : List O → Walk Lc Pt O Ans)

section Walks

variable {Sp O R Lc A Pt Ans : Type}
variable (label : O → R) (L : Labels Sp R A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))

/-- The occurrences of the space `s` that the pattern `p` matches, in position order. -/
def found (v : View Sp O) (s : Sp) (p : Pt) : List O :=
  (v.rows s).filter fun o => L.regionAt s p (label o)

/-- **The walk across moments.** The `i`-th scan reads the view `views i`. Each scan records its
`full-of` entry: the location, the revision of its space when the scan began, and the pattern. -/
def Walk.run (views : ℕ → View Sp O) : ℕ → Walk Lc Pt O Ans → Option (Ans × List (Lc × ℕ × Pt))
  | _, .stop a => some (a, [])
  | i, .scan l p next =>
      match resolve l with
      | some (s, _) =>
          (Walk.run views (i + 1) (next (found label L (views i) s p))).map
            fun r => (r.1, (l, (views i).rev s, p) :: r.2)
      | none => none

/-- **The atomic semantics**: the walk with every scan reading the view `v`. -/
def Walk.eval (v : View Sp O) : Walk Lc Pt O Ans → Option Ans
  | .stop a => some a
  | .scan l p next =>
      match resolve l with
      | some (s, _) => Walk.eval v (next (found label L v s p))
      | none => none

/-- **The `full-of` check at a step** (`ia_check_full_of`): each entry's location names a space
through a handle with the `observe` right, and that space is still at the revision the entry
records. -/
def fullOfOk (v : View Sp O) (parts : List (Lc × ℕ × Pt)) : Bool :=
  parts.all fun x =>
    match resolve x.1 with
    | some (s, ρ) => ρ .observe && decide (v.rev s = x.2.1)
    | none => false

/-- The `full-of` check without its revision part: rights alone. -/
def observeOnly (parts : List (Lc × ℕ × Pt)) : Bool :=
  parts.all fun x =>
    match resolve x.1 with
    | some (_, ρ) => ρ .observe
    | none => false

variable {label L resolve}

theorem fullOfOk_cons {v : View Sp O} {x : Lc × ℕ × Pt} {parts : List (Lc × ℕ × Pt)} :
    fullOfOk resolve v (x :: parts) = true ↔
      (∃ s ρ, resolve x.1 = some (s, ρ) ∧ ρ .observe = true ∧ v.rev s = x.2.1) ∧
        fullOfOk resolve v parts = true := by
  simp only [fullOfOk, List.all_cons, Bool.and_eq_true]
  constructor
  · rintro ⟨head, rest⟩
    refine ⟨?_, rest⟩
    cases hl : resolve x.1 with
    | none => rw [hl] at head; cases head
    | some sρ =>
        obtain ⟨s, ρ⟩ := sρ
        rw [hl] at head
        simp only [Bool.and_eq_true, decide_eq_true_eq] at head
        exact ⟨s, ρ, rfl, head⟩
  · rintro ⟨⟨s, ρ, hl, hobs, hrev⟩, rest⟩
    refine ⟨?_, rest⟩
    rw [hl]
    simp [hobs, hrev]

/-- **What the check establishes**: every scanned location names a space through a handle with
`observe`, at the revision the scan read. -/
theorem observe_of_fullOfOk {v : View Sp O} :
    ∀ {parts : List (Lc × ℕ × Pt)}, fullOfOk resolve v parts = true →
      ∀ x ∈ parts, ∃ s ρ, resolve x.1 = some (s, ρ) ∧ ρ .observe = true ∧ v.rev s = x.2.1
  | [], _, _, member => by cases member
  | _ :: _, ok, x, member => by
      rcases fullOfOk_cons.mp ok with ⟨head, rest⟩
      rcases List.mem_cons.mp member with rfl | inRest
      · exact head
      · exact observe_of_fullOfOk rest x inRest

/-- **A step that passes the `full-of` check is the walk at the moment of the step.** If the
runtime keeps the revision contract between each scan and the step, and the step passes the check,
then the walk across moments gave exactly the answer and the entries of the same walk run entirely
at the view of the step. -/
theorem run_atomic_of_fullOfOk {views : ℕ → View Sp O} {v : View Sp O}
    (tracks : ∀ i, Tracks (views i) v) :
    ∀ (w : Walk Lc Pt O Ans) (i : ℕ) {a : Ans} {parts : List (Lc × ℕ × Pt)},
      Walk.run label L resolve views i w = some (a, parts) →
      fullOfOk resolve v parts = true →
      Walk.run label L resolve (fun _ => v) i w = some (a, parts)
  | .stop b, i, a, parts, ran, _ => by simpa [Walk.run] using ran
  | .scan l p next, i, a, parts, ran, ok => by
      simp only [Walk.run] at ran ⊢
      cases hl : resolve l with
      | none => rw [hl] at ran; cases ran
      | some sρ =>
          obtain ⟨s, ρ⟩ := sρ
          rw [hl] at ran
          simp only at ran ⊢
          obtain ⟨r, hr, hpair⟩ := Option.map_eq_some_iff.mp ran
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
          obtain ⟨⟨s', ρ', hl', -, hrev⟩, rest⟩ := fullOfOk_cons.mp ok
          rw [hl] at hl'
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hl')
          have same : found label L v s p = found label L (views i) s p := by
            simp only [found, tracks i s hrev]
          rw [same, run_atomic_of_fullOfOk tracks _ (i + 1) hr rest]
          simp only [Option.map_some, hrev]

/-- The walk at one view computes the atomic semantics. -/
theorem run_const_eval (v : View Sp O) :
    ∀ (w : Walk Lc Pt O Ans) (i : ℕ),
      (Walk.run label L resolve (fun _ => v) i w).map Prod.fst = Walk.eval label L resolve v w
  | .stop _, _ => rfl
  | .scan l p next, i => by
      simp only [Walk.run, Walk.eval]
      cases resolve l with
      | none => rfl
      | some sρ =>
          simp only [Option.map_map]
          exact run_const_eval v _ (i + 1)

/-- **The step refines the atomic semantics.** A step that passes the `full-of` check gives the
answer of the absence evaluated at the moment of the step. -/
theorem step_answer_eq_atomic {views : ℕ → View Sp O} {v : View Sp O}
    (tracks : ∀ i, Tracks (views i) v) {w : Walk Lc Pt O Ans} {i : ℕ} {a : Ans}
    {parts : List (Lc × ℕ × Pt)} (ran : Walk.run label L resolve views i w = some (a, parts))
    (ok : fullOfOk resolve v parts = true) : Walk.eval label L resolve v w = some a := by
  rw [← run_const_eval v w i, run_atomic_of_fullOfOk tracks w i ran ok]
  rfl

end Walks

/-! ## Rights, and the specification's predicate query -/

section Specification

variable {Sp O R Lc A Pt : Type}
variable (label : O → R) (L : Labels Sp R A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))

/-- The predicate queries the entries of a step denote at a view: for each scanned location, the
occurrences of its space that the pattern matches. -/
def partQueries (v : View Sp O) (parts : List (Lc × ℕ × Pt)) : List (PredicateQuery O R) :=
  parts.filterMap fun x => (resolve x.1).map fun sρ =>
    ⟨L.regionAt sρ.1 x.2.2, regionOf label v.store (L.regionAt sρ.1 x.2.2)⟩

variable {label L resolve}

/-- **A step that passes the check is formed under the rights of its handles.** If every scanned
location is a handle in `H`, the queries of the step are formed under the rights those handles
give: each needs `observe`, and each has it. -/
theorem formed_of_fullOfOk [DecidableEq Sp] {v : View Sp O} {parts : List (Lc × ℕ × Pt)}
    (ok : fullOfOk resolve v parts = true) {H : List Lc} (named : ∀ x ∈ parts, x.1 ∈ H) :
    FormedUnder label L.spaceOf (heldRights resolve H)
      (⟨∅, ∅, ∅, partQueries label L resolve v parts⟩ : Commit O R) := by
  refine ⟨fun o h => absurd h (Finset.notMem_empty o), fun o h => absurd h (Finset.notMem_empty o),
    fun o h => absurd h (Finset.notMem_empty o), fun q inQueries r matched => ?_⟩
  obtain ⟨x, member, hx⟩ := List.mem_filterMap.mp inQueries
  obtain ⟨s, ρ, hl, hobs, -⟩ := observe_of_fullOfOk ok x member
  rw [hl] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  subst hx
  rw [L.regionAt_inside s x.2.2 r matched]
  exact heldRights_of (named x member) hl hobs

/-- `(absent (read LOC PATTERN))`: one scan, and the answer is whether nothing was found. -/
def absentRead {Lc Pt O : Type} (l : Lc) (p : Pt) : Walk Lc Pt O Bool :=
  .scan l p fun xs => .stop xs.isEmpty

/-- At a consistent view, nothing found means the predicate query "nothing of `s` matches `p`"
holds. -/
theorem holds_of_found_nil {v : View Sp O} (cons : v.Consistent label L) {s : Sp} {p : Pt}
    (none_found : found label L v s p = []) :
    (⟨L.regionAt s p, ∅⟩ : PredicateQuery O R).Holds label v.store := by
  unfold PredicateQuery.Holds
  ext o
  simp only [mem_regionOf, Finset.notMem_empty, iff_false, not_and]
  intro inStore matched
  have inRows : o ∈ v.rows s :=
    (cons.mem_rows s o).mpr ⟨inStore, L.regionAt_inside s p _ matched⟩
  have : o ∈ found label L v s p := List.mem_filter.mpr ⟨inRows, matched⟩
  rw [none_found] at this
  cases this

/-- **An absence that fires holds when the step happens.** If the walk of `(absent (read l p))`
answered that nothing is there, the step passes the `full-of` check, and the runtime keeps the
revision contract, then at the moment of the step nothing of the space matches `p`: the
specification's predicate query holds at the step's store. -/
theorem absence_holds_at_step {views : ℕ → View Sp O} {v : View Sp O}
    (cons : v.Consistent label L) (tracks : ∀ i, Tracks (views i) v) {l : Lc} {p : Pt} {i : ℕ}
    {parts : List (Lc × ℕ × Pt)}
    (ran : Walk.run label L resolve views i (absentRead l p) = some (true, parts))
    (ok : fullOfOk resolve v parts = true) {s : Sp} {ρ : Facet → Bool}
    (hl : resolve l = some (s, ρ)) :
    (⟨L.regionAt s p, ∅⟩ : PredicateQuery O R).Holds label v.store := by
  have atomic := step_answer_eq_atomic tracks ran ok
  simp only [absentRead, Walk.eval, hl, Option.some.injEq, List.isEmpty_iff] at atomic
  exact holds_of_found_nil cons atomic

end Specification

section Step

variable {Sp O R Lc A Pt : Type} [DecidableEq Sp] [DecidableEq O] [DecidableEq A]
variable (label : O → R) (L : Labels Sp R A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))

/-- **The step check with `full-of` entries**: `KernelCommit`'s check of the step's other entries,
its seen spaces and its makes, and the `full-of` check of the spaces its absences scanned. -/
def stepOk (v : View Sp O) (seen : List (Lc × ℕ)) (fp : List (Entry Lc A Pt)) (makes : List (Lc × A))
    (parts : List (Lc × ℕ × Pt)) : Bool :=
  check label L resolve v seen fp makes && fullOfOk resolve v parts

/-- **The whole step is formed under the held rights.** Suppose a step passes `stepOk` at the view
`v₁`, carries its absences as `full-of` entries (no `noRows` entry), and names only handles in
`H`. Then the step the entries denote, with the queries of its `full-of` entries added, is formed
under the rights those handles give. -/
theorem stepOk_formed {v₀ v₁ : View Sp O}
    (cons₀ : v₀.Consistent label L) {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    {makes : List (Lc × A)} {parts : List (Lc × ℕ × Pt)}
    (ok : stepOk label L resolve v₁ seen fp makes parts = true)
    (noAbsentSources : ∀ l xs, Entry.noRows l xs ∉ fp) {H : List Lc}
    (named : ∀ e ∈ fp, e.loc ∈ H) (namedMakes : ∀ m ∈ makes, m.1 ∈ H)
    (namedParts : ∀ x ∈ parts, x.1 ∈ H) {c : Commit O R}
    (denotes : Sources.IsCommitOf label v₁.store (decode label L resolve v₀ fp makes) c) :
    FormedUnder label L.spaceOf (heldRights resolve H)
      { c with queries := c.queries ++ partQueries label L resolve v₁ parts } := by
  obtain ⟨checked, fullOf⟩ := Bool.and_eq_true_iff.mp ok
  have old := formedUnder_of_check cons₀ checked noAbsentSources named namedMakes denotes
  have new := formed_of_fullOfOk (label := label) (L := L) fullOf namedParts
  refine ⟨old.taken, old.kept, old.made, fun q inQueries r matched => ?_⟩
  rcases List.mem_append.mp inQueries with inOld | inNew
  · exact old.queries q inOld r matched
  · exact new.queries q inNew r matched

end Step

/-! ## Controls -/

namespace Controls

open KernelCommit.Controls

/-- The plain space with the given occurrences at the given revision; the channel empty at
revision `0`. Occurrence `3` is the atom `0` in the plain space. -/
def plainView (store : Finset ℕ) (rev : ℕ) (rows : List ℕ) : View Space ℕ :=
  ⟨store, fun | .plain => rev | .chan => 0, fun | .plain => rows | .chan => []⟩

/-- `(absent (read &plain $x))`: is the plain space empty? -/
abbrev absentPlain : Walk Loc (Option ℕ) ℕ Bool := absentRead .plain none

/-- The walk's moment: the plain space empty at revision `0`. -/
abbrev before : View Space ℕ := plainView ∅ 0 []

/-- A message arrived in the plain space, and its revision moved to `1`. -/
abbrev arrived : View Space ℕ := plainView {3} 1 [3]

/-- The entry the walk records: the plain space, revision `0`, any atom. -/
abbrev scanned : List (Loc × ℕ × Option ℕ) := [(.plain, 0, none)]

theorem walk_before :
    Walk.run lab labels resolve (fun _ => before) 0 absentPlain = some (true, scanned) := by
  decide

theorem tracks_arrived : Tracks before arrived := by
  intro s
  cases s <;> simp [plainView]

/-- **A stale revision is refused**: after the message arrived, the step is refused, and the
absence evaluated at that moment is false. -/
theorem stale_refused :
    fullOfOk resolve arrived scanned = false ∧
      Walk.eval lab labels resolve arrived absentPlain = some false := by
  decide

/-- **Without the recheck, a stale absence is accepted.** The walk found the plain space empty;
then a message arrived, under the revision contract. The absence at the moment of the step is
false. The check of rights alone passes the step, so it would fire on an absence that no longer
holds; the `full-of` check refuses it. -/
theorem stale_absence_needs_recheck :
    Walk.run lab labels resolve (fun _ => before) 0 absentPlain = some (true, scanned) ∧
      Tracks before arrived ∧
      Walk.eval lab labels resolve arrived absentPlain = some false ∧
      observeOnly resolve scanned = true ∧
      fullOfOk resolve arrived scanned = false :=
  ⟨walk_before, tracks_arrived, stale_refused.2, by decide, stale_refused.1⟩

/-- The entry of one scan through the location `l`, at revision `0`, for any atom. -/
abbrev entryAt (l : Loc) : List (Loc × ℕ × Option ℕ) := [(l, 0, none)]

/-- **A missing `observe` right is refused.** Scanning through the channel's holder, which has no
`observe`, or through its `peek` handle, is refused; scanning the plain space passes. -/
theorem missing_observe_refused :
    fullOfOk resolve noMessage (entryAt .chanHolder) = false ∧
      fullOfOk resolve noMessage (entryAt .chanPeek) = false ∧
      fullOfOk resolve noMessage (entryAt .plain) = true := by
  decide

/-- **The bypass is closed.** `KernelCommit`'s check accepts the absence of a read source on the
channel through its `peek` handle, since it asks for `observe` only at the transform's own location
(`KernelCommit.Controls.absence_of_sources_not_formed`); the walk of the same absence records the
channel's entry, and the `full-of` check refuses it. -/
theorem bypass_closed :
    check lab labels resolve noMessage [(.plain, 0), (.chanPeek, 0)] absenceOfSource [] = true ∧
      Walk.run lab labels resolve (fun _ => noMessage) 0 (absentRead .chanPeek none) =
        some (true, entryAt .chanPeek) ∧
      fullOfOk resolve noMessage (entryAt .chanPeek) = false :=
  ⟨absence_of_sources_not_formed.1, by decide, missing_observe_refused.2.1⟩

/-- A message arrived in the plain space without the revision moving. -/
abbrev untracked : View Space ℕ := plainView {3} 0 [3]

/-- **The revision contract is needed.** A runtime that writes the plain space without moving its
revision passes the check, and the step fires on an absence that no longer holds. -/
theorem revision_contract_needed :
    ¬ Tracks before untracked ∧ fullOfOk resolve untracked scanned = true ∧
      Walk.eval lab labels resolve untracked absentPlain = some false := by
  refine ⟨fun tracks => ?_, by decide, by decide⟩
  have := tracks .plain rfl
  simp [plainView] at this

/-- A message arrived on the channel, a space the walk did not scan. -/
abbrev channelWritten : View Space ℕ :=
  ⟨{0}, fun | .plain => 0 | .chan => 1, fun | .plain => [] | .chan => [0]⟩

/-- **A write elsewhere leaves the step passing**, with the answer of the moment of the step. -/
theorem unscanned_write_passes :
    Tracks before channelWritten ∧ fullOfOk resolve channelWritten scanned = true ∧
      Walk.eval lab labels resolve channelWritten absentPlain = some true := by
  refine ⟨fun s => ?_, by decide, by decide⟩
  cases s <;> simp [plainView]

/-- **Whole-space revisions**: a write to the plain space undone before the step leaves it empty,
and the absence true, but its revision moved, so the step is refused. -/
theorem undone_write_refused :
    fullOfOk resolve (plainView ∅ 2 []) scanned = false ∧
      Walk.eval lab labels resolve (plainView ∅ 2 []) absentPlain = some true := by
  decide

/-- The headline applies: the walk before, the step after a write elsewhere. -/
theorem headline_instance :
    Walk.eval lab labels resolve channelWritten absentPlain = some true :=
  step_answer_eq_atomic (views := fun _ => before) (fun _ => unscanned_write_passes.1) walk_before
    unscanned_write_passes.2.1

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.FullOfCheck
