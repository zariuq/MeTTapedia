import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceChecker

/-!
# The interaction kernel's commit check, against `Enabled`, `Linear` and `FormedUnder`

The interaction kernel of the Prime draft builds a commit in two phases.

* Its **walk** matches a transform's sources against the live store. Each matched source picks an
  occurrence by its position in a space, at a revision of that space, and keeps or takes it; each
  predicate query records its region and the revision it read; and every space the walk scanned is
  listed with its revision (`seen`). Code (`let`) may run between the walk and the commit.
* Its **commit** checks, at one instant, that every listed space is still at the revision the walk
  read, that every picked position still holds the atom the walk read, identification (no position
  taken twice, none both taken and kept; two keeps may share), and rights entry by entry: a take
  needs `receive`, a keep `peek`, a predicate query `observe` and a make `send`, on the handle that
  names the entry's location. Then it fires.

An `every` contributes one row per occurrence. The walk builds only rows that are linear on their
own, the amalgamation refuses rows that take a common occurrence or where one keeps what another
takes, and the whole commit, the kernel's own picks and every row, must pass identification.

This module states that check over a model of what the kernel sees (`View`: the occurrences, and
per space a revision and the occurrences in position order) and relates it to the semantic owners.

## The check, exactly (`check_iff`)

The kernel's check holds exactly when the revisions are current, the entries' rights are held, the
picked positions hold the atoms read, the makes may be sent, and the footprint the entries denote
(`decode`) is linear in the sense of the specification (`Sources.Footprint.Linear`): identification
by position is identification by occurrence (`identified_iff_linear`), because positions of one
view name distinct occurrences.

## Soundness: what the kernel accepts is enabled (`enabled_of_check`)

Suppose the walk built the footprint at a view `v₀` (every space an entry depends on was scanned,
`Scanned`), the runtime keeps the revision contract (`Tracks`: a space whose revision did not move
holds the same occurrences in the same positions), and the check passes at the commit's view `v₁`.
Then the footprint holds at `v₁` and is linear (`holds_of_check`), so every commit of it with fresh
identities is `Enabled` at `v₁` (`IsCommitOf.enabled_iff`). The revision check is a predicate query
of each scanned space (`revisionQuery_holds`), which is the one-revision protocol of
`SerializedPublication` for each space.

The revision contract cannot be dropped: a runtime that writes a space without moving its revision
passes the check for a commit that is not enabled (`Controls.untracked_write_accepted`). With both
the walk and the commit at one view the theorem applies to a real footprint
(`Controls.holder_take_passes`).

## Rights: the check is formation, entry by entry (`formedUnder_of_check`)

For a footprint whose entries are named by handles the process holds, the check implies that every
commit of the footprint is `InteractionTypes.FormedUnder` the rights those handles give
(`Controls.holder_take_formed`). The check is finer than formation under the union of held rights:
a take through a handle without `receive` is refused even when another held handle to the same
region has it (`Controls.per_handle_refused`).

## `every`: what each part checks (`identified_every_iff`)

Identification of a firing with `every` holds exactly when each row is linear on its own, the rows
are pairwise apart, the kernel's own picks are linear, and the kernel's picks are apart from every
row. The walk ensures the first and third, the amalgamation the second; only the commit's own
identification checks the fourth.

## Where the check differs from `Enabled` and from formation

* **Whole-space revisions.** Any write to a scanned space, inside the commit's regions or not, makes
  the commit stale, and so does a write undone before the commit (`Controls.stale_refused`,
  `Controls.undone_write_refused`), while the commit stays enabled. This is the price measured by
  `SerializedPublication.stale_after_any_write` and `revision_not_localTo`.
* **Linearity of the list.** A footprint that lists one take twice is refused; the commit with that
  take once is enabled (`Controls.double_take_refused`). The kernel's identification is the
  specification's `Footprint.Linear`, which `Enabled.apart` alone does not express.
* **The none query of sources bypasses `observe`.** The kernel checks `observe` for `(absent SOURCES)`
  only at the transform's own location, and each source of it for its own use (`peek` or
  `receive`). The commit it accepts is a predicate query of the sources' regions, so it is not
  formed under the process's rights when the process lacks `observe` there
  (`Controls.absence_of_sources_not_formed`). The draft binaries behave so: a none query of a read
  source on a channel, which has no `observe` facet, fires through a `peek` handle, while the
  none query written on the channel itself is refused.

## The trace the kernel prints, and the verified checker (`emit`)

The kernel prints each commit for `OccurrenceCommits.TraceChecker` (`emit`): the identities taken
and kept, the fresh identities made, each predicate query as a printed region with the identities
it matches, and what each `every` row takes. The run-by-run certificate is
`TraceChecker.checkRun_isSome_iff`; this section says what it certifies of the check above.

* **What the kernel accepts, the checker accepts** (`emit_enabledB`), for a footprint without a
  none query of sources and a printer faithful to the entries' regions (`Faithful`); and the printed
  rows pass the row test (`emit_rowsOk`).
* **The printed none query of sources is vacuous.** The kernel prints it as a region of the transform's
  location whose pattern is the source itself, which no stored atom matches; so a commit carrying it
  passes the checker at a store where the none query fails
  (`Controls.Printed.printed_absence_of_source_vacuous`). `Faithful` fails for it, and the checker
  certifies nothing about it.
* **The kernel's own picks are not printed as a row**, so a take shared by the kernel and a row
  shows only as a repeated identity, which decoding to sets merges. The checker's take test
  `TraceChecker.linearCheck` refuses it (`TraceChecker.Controls.kernel_row_double_take`); the
  kernel's own identification refuses it too (the fourth part of `identified_every_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

/-! ## What the kernel sees -/

/-- How labels are read: the space a label lives in, its atom, the label an atom made in a space
carries, and the region of a pattern in a space, which lies in that space. -/
structure Labels (Sp R A Pt : Type) where
  spaceOf : R → Sp
  atomOf : R → A
  make : Sp → A → R
  regionAt : Sp → Pt → R → Bool
  spaceOf_make : ∀ s a, spaceOf (make s a) = s
  regionAt_inside : ∀ s p r, regionAt s p r = true → spaceOf r = s

/-- What the kernel sees of the live store: the occurrences, and for each space its revision and
its occurrences in position order. Occurrence identities are stable (they are the identities a
trace prints); positions are not. -/
structure View (Sp O : Type) where
  store : Finset O
  rev : Sp → ℕ
  rows : Sp → List O

/-- The occurrence at a position of a space. -/
def View.at {Sp O : Type} (v : View Sp O) (s : Sp) (p : ℕ) : Option O := (v.rows s)[p]?

/-- A matched source keeps the occurrence it picks, or takes it. -/
inductive Use where
  | keep
  | take
  deriving DecidableEq, Repr

/-- The facet a use needs. -/
def Use.facet : Use → Facet
  | .keep => .peek
  | .take => .receive

/-- One entry of a footprint, as the walk records it. -/
inductive Entry (Lc A Pt : Type) where
  /-- An occurrence a matched source picked: its use, its location, the revision of its space, its
  position there, and the atom read. -/
  | pick (use : Use) (loc : Lc) (rev pos : ℕ) (atom : A)
  /-- A predicate query (`absent`, `unique`, `all`) of the region of a pattern at a location, with
  the revision read. -/
  | query (loc : Lc) (rev : ℕ) (pattern : Pt)
  /-- The none query of sources, `(absent SOURCES)`: the sources, each a use, a location and a
  pattern, have no row. The kernel records it at the transform's location, with no revision. -/
  | noRows (loc : Lc) (sources : List (Use × Lc × Pt))

/-- The location an entry is checked at. -/
def Entry.loc {Lc A Pt : Type} : Entry Lc A Pt → Lc
  | .pick _ l _ _ _ => l
  | .query l _ _ => l
  | .noRows l _ => l

/-- A list of keys that all name occurrences, under a map injective where defined, has no
duplicate exactly when the occurrences it names have none. -/
theorem nodup_filterMap_iff {K O : Type} {f : K → Option O}
    (inj : ∀ k k' o, f k = some o → f k' = some o → k = k') :
    ∀ {l : List K}, (∀ k ∈ l, (f k).isSome = true) → ((l.filterMap f).Nodup ↔ l.Nodup)
  | [], _ => by simp
  | k :: l, valid => by
      obtain ⟨o, hk⟩ := Option.isSome_iff_exists.mp (valid k List.mem_cons_self)
      have rest : ∀ k' ∈ l, (f k').isSome = true := fun k' m => valid k' (List.mem_cons_of_mem _ m)
      rw [List.filterMap_cons_some hk, List.nodup_cons, List.nodup_cons,
        nodup_filterMap_iff inj rest]
      constructor
      · rintro ⟨notIn, nd⟩
        exact ⟨fun kIn => notIn (List.mem_filterMap.mpr ⟨k, kIn, hk⟩), nd⟩
      · rintro ⟨notIn, nd⟩
        refine ⟨fun oIn => ?_, nd⟩
        obtain ⟨k', k'In, hk'⟩ := List.mem_filterMap.mp oIn
        exact notIn (inj k' k o hk' hk ▸ k'In)

section Check

variable {Sp O R Lc A Pt : Type} [DecidableEq Sp] [DecidableEq O] [DecidableEq A]
variable (label : O → R) (L : Labels Sp R A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))

/-- A view is consistent: each space lists its occurrences once each, and they are exactly the
store's occurrences in that space. -/
structure View.Consistent (v : View Sp O) : Prop where
  nodup : ∀ s, (v.rows s).Nodup
  mem_rows : ∀ s o, o ∈ v.rows s ↔ o ∈ v.store ∧ L.spaceOf (label o) = s

/-- **The revision contract**: a space whose revision did not move holds the same occurrences in
the same positions. A runtime keeps it by moving a space's revision on every write to it. -/
def Tracks (v₀ v₁ : View Sp O) : Prop := ∀ s, v₁.rev s = v₀.rev s → v₁.rows s = v₀.rows s

/-- The position a pick takes, as a space and a position. -/
def Entry.takeKey : Entry Lc A Pt → Option (Sp × ℕ)
  | .pick .take l _ p _ => (resolve l).map fun x => (x.1, p)
  | _ => none

/-- The position a pick keeps. -/
def Entry.keepKey : Entry Lc A Pt → Option (Sp × ℕ)
  | .pick .keep l _ p _ => (resolve l).map fun x => (x.1, p)
  | _ => none

/-- The positions a footprint takes. -/
def takeKeys (fp : List (Entry Lc A Pt)) : List (Sp × ℕ) := fp.filterMap (Entry.takeKey resolve)

/-- The positions a footprint keeps. -/
def keepKeys (fp : List (Entry Lc A Pt)) : List (Sp × ℕ) := fp.filterMap (Entry.keepKey resolve)

/-- **Identification by position**: no position taken twice, none both taken and kept. -/
def Identified (takes keeps : List (Sp × ℕ)) : Prop := takes.Nodup ∧ ∀ k ∈ takes, k ∉ keeps

instance (takes keeps : List (Sp × ℕ)) : Decidable (Identified takes keeps) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- What the kernel checks of one entry at a view: its location names a region through a handle
with the right its use needs, its space is at the revision recorded, and a pick's position holds
the atom read. The none query of sources is checked for `observe` at the transform's location, and
each of its sources for its own use. -/
def entryOk (v : View Sp O) : Entry Lc A Pt → Bool
  | .pick u l r p a =>
      match resolve l with
      | some (s, ρ) =>
          ρ u.facet && decide (v.rev s = r) &&
            match v.at s p with
            | some o => decide (L.atomOf (label o) = a)
            | none => false
      | none => false
  | .query l r _ =>
      match resolve l with
      | some (s, ρ) => ρ .observe && decide (v.rev s = r)
      | none => false
  | .noRows l sources =>
      (match resolve l with
       | some (_, ρ) => ρ .observe
       | none => false) &&
        sources.all fun x =>
          match resolve x.2.1 with
          | some (_, ρ) => ρ x.1.facet
          | none => false

/-- Every scanned space is still at the revision the walk read. -/
def seenOk (v : View Sp O) (seen : List (Lc × ℕ)) : Bool :=
  seen.all fun x =>
    match resolve x.1 with
    | some (s, _) => decide (v.rev s = x.2)
    | none => false

/-- Every make's location names a region through a handle with `send`. -/
def makesOk (makes : List (Lc × A)) : Bool :=
  makes.all fun m =>
    match resolve m.1 with
    | some (_, ρ) => ρ .send
    | none => false

/-- **The kernel's commit check**: revisions, entries, identification, makes. -/
def check (v : View Sp O) (seen : List (Lc × ℕ)) (fp : List (Entry Lc A Pt))
    (makes : List (Lc × A)) : Bool :=
  seenOk resolve v seen && fp.all (entryOk label L resolve v) &&
    decide (Identified (takeKeys resolve fp) (keepKeys resolve fp)) && makesOk resolve makes

/-- The region of a predicate query entry: the pattern's region in its space; for the none query of
sources, the union of its sources' regions. -/
def Entry.region : Entry Lc A Pt → Option (R → Bool)
  | .pick .. => none
  | .query l _ pat => (resolve l).map fun x => L.regionAt x.1 pat
  | .noRows _ sources =>
      some fun r => sources.any fun x =>
        match resolve x.2.1 with
        | some (s, _) => L.regionAt s x.2.2 r
        | none => false

/-- **The footprint the entries denote at a view**: the occurrences at the picked positions, each
predicate query's region with what the view holds there, and the labels made. -/
def decode (v : View Sp O) (fp : List (Entry Lc A Pt)) (makes : List (Lc × A)) :
    Footprint O R where
  takes := ((takeKeys resolve fp).filterMap fun k => v.at k.1 k.2 : List O)
  keeps := ((keepKeys resolve fp).filterMap fun k => v.at k.1 k.2 : List O)
  queries := ((fp.filterMap (Entry.region L resolve)).map fun region =>
    (⟨region, regionOf label v.store region⟩ : PredicateQuery O R) : List (PredicateQuery O R))
  makes := ((makes.filterMap fun m => (resolve m.1).map fun x => L.make x.1 m.2) : List R)

/-- The spaces whose occurrences an entry depends on. -/
def Entry.spaces : Entry Lc A Pt → List Sp
  | .pick _ l _ _ _ => ((resolve l).map Prod.fst).toList
  | .query l _ _ => ((resolve l).map Prod.fst).toList
  | .noRows _ sources => sources.filterMap fun x => (resolve x.2.1).map Prod.fst

/-- **What the walk guarantees**: every space an entry depends on was scanned at `v₀`, so it is
listed in `seen` with its revision there. -/
def Scanned (v₀ : View Sp O) (seen : List (Lc × ℕ)) (fp : List (Entry Lc A Pt)) : Prop :=
  ∀ e ∈ fp, ∀ s ∈ e.spaces resolve, ∃ x ∈ seen,
    (resolve x.1).map Prod.fst = some s ∧ x.2 = v₀.rev s

/-! ### The parts of the check -/

/-- The revisions recorded are current at the view. -/
def RevisionsCurrent (v : View Sp O) (seen : List (Lc × ℕ)) (fp : List (Entry Lc A Pt)) : Prop :=
  (∀ x ∈ seen, ∃ s ρ, resolve x.1 = some (s, ρ) ∧ v.rev s = x.2) ∧
    (∀ u l r p a, Entry.pick u l r p a ∈ fp → ∃ s ρ, resolve l = some (s, ρ) ∧ v.rev s = r) ∧
    ∀ l r pat, Entry.query l r pat ∈ fp → ∃ s ρ, resolve l = some (s, ρ) ∧ v.rev s = r

/-- The rights the entries and makes need are carried by the handles that name them. -/
def RightsHeld (fp : List (Entry Lc A Pt)) (makes : List (Lc × A)) : Prop :=
  (∀ u l r p a, Entry.pick u l r p a ∈ fp → ∃ s ρ, resolve l = some (s, ρ) ∧ ρ u.facet = true) ∧
    (∀ l r pat, Entry.query l r pat ∈ fp → ∃ s ρ, resolve l = some (s, ρ) ∧ ρ .observe = true) ∧
    (∀ l xs, Entry.noRows l xs ∈ fp → (∃ s ρ, resolve l = some (s, ρ) ∧ ρ .observe = true) ∧
      ∀ x ∈ xs, ∃ s ρ, resolve x.2.1 = some (s, ρ) ∧ ρ x.1.facet = true) ∧
    ∀ m ∈ makes, ∃ s ρ, resolve m.1 = some (s, ρ) ∧ ρ .send = true

/-- Every picked position holds the atom read. -/
def Present (v : View Sp O) (fp : List (Entry Lc A Pt)) : Prop :=
  ∀ u l r p a, Entry.pick u l r p a ∈ fp → ∃ s ρ o, resolve l = some (s, ρ) ∧ v.at s p = some o ∧
    L.atomOf (label o) = a

variable {label L resolve}

/-! ### Positions of one view name distinct occurrences -/

omit [DecidableEq Sp] [DecidableEq O] [DecidableEq A] in
theorem View.Consistent.at_mem {v : View Sp O} (cons : v.Consistent label L) {s : Sp} {p : ℕ}
    {o : O} (h : v.at s p = some o) : o ∈ v.store ∧ L.spaceOf (label o) = s :=
  (cons.mem_rows s o).mp (List.mem_of_getElem? h)

omit [DecidableEq Sp] [DecidableEq O] [DecidableEq A] in
theorem View.Consistent.at_inj {v : View Sp O} (cons : v.Consistent label L) {k k' : Sp × ℕ}
    {o : O} (h : v.at k.1 k.2 = some o) (h' : v.at k'.1 k'.2 = some o) : k = k' := by
  obtain ⟨s, p⟩ := k
  obtain ⟨s', p'⟩ := k'
  have hs : s = s' := (cons.at_mem h).2.symm.trans (cons.at_mem h').2
  subst hs
  have lt : p < (v.rows s).length := (List.getElem?_eq_some_iff.mp h).1
  have hp : p = p' := (List.getElem?_inj lt (cons.nodup s)).mp (h.trans h'.symm)
  rw [hp]

omit [DecidableEq Sp] [DecidableEq O] [DecidableEq A] in
/-- **Identification by position is identification by occurrence**: when every picked position
names an occurrence of a consistent view, the kernel's identification holds exactly when the
footprint the entries denote is linear. -/
theorem identified_iff_linear {v : View Sp O} (cons : v.Consistent label L)
    {fp : List (Entry Lc A Pt)} (makes : List (Lc × A))
    (valid : ∀ k ∈ takeKeys resolve fp ++ keepKeys resolve fp, (v.at k.1 k.2).isSome = true) :
    Identified (takeKeys resolve fp) (keepKeys resolve fp) ↔
      (decode label L resolve v fp makes).Linear := by
  have inj : ∀ (k k' : Sp × ℕ) (o : O), v.at k.1 k.2 = some o → v.at k'.1 k'.2 = some o →
      k = k' :=
    fun k k' o h h' => cons.at_inj h h'
  have validT : ∀ k ∈ takeKeys resolve fp, (v.at k.1 k.2).isSome = true :=
    fun k m => valid k (List.mem_append_left _ m)
  have validK : ∀ k ∈ keepKeys resolve fp, (v.at k.1 k.2).isSome = true :=
    fun k m => valid k (List.mem_append_right _ m)
  unfold Identified Footprint.Linear decode
  simp only [Multiset.coe_nodup, Multiset.mem_coe]
  rw [nodup_filterMap_iff (f := fun k : Sp × ℕ => v.at k.1 k.2) inj validT]
  refine and_congr_right fun _ => ?_
  constructor
  · intro apart o inT inK
    obtain ⟨k, kT, hk⟩ := List.mem_filterMap.mp inT
    obtain ⟨k', kK, hk'⟩ := List.mem_filterMap.mp inK
    exact apart k kT (inj k' k o hk' hk ▸ kK)
  · intro apart k kT kK
    obtain ⟨o, hk⟩ := Option.isSome_iff_exists.mp (validT k kT)
    exact apart o (List.mem_filterMap.mpr ⟨k, kT, hk⟩) (List.mem_filterMap.mpr ⟨k, kK, hk⟩)

/-! ### The check, unfolded -/

omit [DecidableEq Sp] [DecidableEq O] in
theorem seenOk_iff {v : View Sp O} {seen : List (Lc × ℕ)} :
    seenOk resolve v seen = true ↔
      ∀ x ∈ seen, ∃ s ρ, resolve x.1 = some (s, ρ) ∧ v.rev s = x.2 := by
  unfold seenOk
  rw [List.all_eq_true]
  refine forall₂_congr fun x _ => ?_
  cases h : resolve x.1 with
  | none => simp
  | some y => obtain ⟨s, ρ⟩ := y; simp

omit [DecidableEq Sp] [DecidableEq A] in
theorem makesOk_iff {makes : List (Lc × A)} :
    makesOk resolve makes = true ↔
      ∀ m ∈ makes, ∃ s ρ, resolve m.1 = some (s, ρ) ∧ ρ .send = true := by
  unfold makesOk
  rw [List.all_eq_true]
  refine forall₂_congr fun m _ => ?_
  cases h : resolve m.1 with
  | none => simp
  | some y => obtain ⟨s, ρ⟩ := y; simp

omit [DecidableEq Sp] [DecidableEq O] in
theorem entryOk_pick_iff {v : View Sp O} {u : Use} {l : Lc} {r p : ℕ} {a : A} :
    entryOk label L resolve v (.pick u l r p a) = true ↔
      ∃ s ρ o, resolve l = some (s, ρ) ∧ ρ u.facet = true ∧ v.rev s = r ∧ v.at s p = some o ∧
        L.atomOf (label o) = a := by
  cases h : resolve l with
  | none => simp [entryOk, h]
  | some y =>
      obtain ⟨s, ρ⟩ := y
      cases h' : v.at s p with
      | none => simp [entryOk, h, h']
      | some o => simp [entryOk, h, h', and_assoc]

omit [DecidableEq Sp] [DecidableEq O] in
theorem entryOk_query_iff {v : View Sp O} {l : Lc} {r : ℕ} {pat : Pt} :
    entryOk label L resolve v (.query l r pat) = true ↔
      ∃ s ρ, resolve l = some (s, ρ) ∧ ρ .observe = true ∧ v.rev s = r := by
  cases h : resolve l with
  | none => simp [entryOk, h]
  | some y => obtain ⟨s, ρ⟩ := y; simp [entryOk, h]

omit [DecidableEq Sp] [DecidableEq O] in
theorem entryOk_noRows_iff {v : View Sp O} {l : Lc} {xs : List (Use × Lc × Pt)} :
    entryOk label L resolve v (.noRows l xs) = true ↔
      (∃ s ρ, resolve l = some (s, ρ) ∧ ρ .observe = true) ∧
        ∀ x ∈ xs, ∃ s ρ, resolve x.2.1 = some (s, ρ) ∧ ρ x.1.facet = true := by
  simp only [entryOk, Bool.and_eq_true, List.all_eq_true]
  refine and_congr ?_ (forall₂_congr fun x _ => ?_)
  · cases h : resolve l with
    | none => simp
    | some y => obtain ⟨s, ρ⟩ := y; simp
  · cases h : resolve x.2.1 with
    | none => simp
    | some y => obtain ⟨s, ρ⟩ := y; simp

omit [DecidableEq O] in
theorem check_eq_true_iff {v : View Sp O} {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    {makes : List (Lc × A)} :
    check label L resolve v seen fp makes = true ↔
      seenOk resolve v seen = true ∧ (∀ e ∈ fp, entryOk label L resolve v e = true) ∧
        Identified (takeKeys resolve fp) (keepKeys resolve fp) ∧ makesOk resolve makes = true := by
  unfold check
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, and_assoc]

omit [DecidableEq Sp] [DecidableEq A] in
theorem mem_takeKeys {fp : List (Entry Lc A Pt)} {k : Sp × ℕ} :
    k ∈ takeKeys resolve fp ↔
      ∃ l r a ρ, Entry.pick .take l r k.2 a ∈ fp ∧ resolve l = some (k.1, ρ) := by
  unfold takeKeys
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, member, he⟩
    cases e with
    | pick u l r p a =>
        cases u with
        | keep => simp [Entry.takeKey] at he
        | take =>
            simp only [Entry.takeKey, Option.map_eq_some_iff] at he
            obtain ⟨⟨s, ρ⟩, hl, rfl⟩ := he
            exact ⟨l, r, a, ρ, member, hl⟩
    | query => simp [Entry.takeKey] at he
    | noRows => simp [Entry.takeKey] at he
  · rintro ⟨l, r, a, ρ, member, hl⟩
    exact ⟨_, member, by simp [Entry.takeKey, hl]⟩

omit [DecidableEq Sp] [DecidableEq A] in
theorem mem_keepKeys {fp : List (Entry Lc A Pt)} {k : Sp × ℕ} :
    k ∈ keepKeys resolve fp ↔
      ∃ l r a ρ, Entry.pick .keep l r k.2 a ∈ fp ∧ resolve l = some (k.1, ρ) := by
  unfold keepKeys
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, member, he⟩
    cases e with
    | pick u l r p a =>
        cases u with
        | take => simp [Entry.keepKey] at he
        | keep =>
            simp only [Entry.keepKey, Option.map_eq_some_iff] at he
            obtain ⟨⟨s, ρ⟩, hl, rfl⟩ := he
            exact ⟨l, r, a, ρ, member, hl⟩
    | query => simp [Entry.keepKey] at he
    | noRows => simp [Entry.keepKey] at he
  · rintro ⟨l, r, a, ρ, member, hl⟩
    exact ⟨_, member, by simp [Entry.keepKey, hl]⟩

omit [DecidableEq Sp] [DecidableEq O] in
/-- Under the check, every picked position names an occurrence. -/
theorem valid_of_entries {v : View Sp O} {fp : List (Entry Lc A Pt)}
    (entries : ∀ e ∈ fp, entryOk label L resolve v e = true) :
    ∀ k ∈ takeKeys resolve fp ++ keepKeys resolve fp, (v.at k.1 k.2).isSome = true := by
  intro k member
  have pick : ∃ u l r a ρ, Entry.pick u l r k.2 a ∈ fp ∧ resolve l = some (k.1, ρ) := by
    rcases List.mem_append.mp member with inT | inK
    · obtain ⟨l, r, a, ρ, m, hl⟩ := mem_takeKeys.mp inT
      exact ⟨.take, l, r, a, ρ, m, hl⟩
    · obtain ⟨l, r, a, ρ, m, hl⟩ := mem_keepKeys.mp inK
      exact ⟨.keep, l, r, a, ρ, m, hl⟩
  obtain ⟨u, l, r, a, ρ, m, hl⟩ := pick
  obtain ⟨s, ρ', o, hl', -, -, ho, -⟩ := entryOk_pick_iff.mp (entries _ m)
  rw [hl] at hl'
  cases hl'
  simp [ho]

omit [DecidableEq O] in
/-- **The check, exactly**: at a consistent view, the kernel's check holds exactly when the
revisions recorded are current, the rights are held, the picked positions hold the atoms read, and
the footprint the entries denote is linear. -/
theorem check_iff {v : View Sp O} (cons : v.Consistent label L) {seen : List (Lc × ℕ)}
    {fp : List (Entry Lc A Pt)} {makes : List (Lc × A)} :
    check label L resolve v seen fp makes = true ↔
      RevisionsCurrent resolve v seen fp ∧ RightsHeld resolve fp makes ∧
        Present label L resolve v fp ∧ (decode label L resolve v fp makes).Linear := by
  rw [check_eq_true_iff, seenOk_iff, makesOk_iff]
  constructor
  · rintro ⟨seen_ok, entries, identified, makes_ok⟩
    have linear := (identified_iff_linear cons makes (valid_of_entries entries)).mp identified
    refine ⟨⟨seen_ok, fun u l r p a m => ?_, fun l r pat m => ?_⟩,
      ⟨fun u l r p a m => ?_, fun l r pat m => ?_, fun l xs m => ?_, makes_ok⟩,
      fun u l r p a m => ?_, linear⟩
    · obtain ⟨s, ρ, o, hl, -, hr, -, -⟩ := entryOk_pick_iff.mp (entries _ m)
      exact ⟨s, ρ, hl, hr⟩
    · obtain ⟨s, ρ, hl, -, hr⟩ := entryOk_query_iff.mp (entries _ m)
      exact ⟨s, ρ, hl, hr⟩
    · obtain ⟨s, ρ, o, hl, hf, -, -, -⟩ := entryOk_pick_iff.mp (entries _ m)
      exact ⟨s, ρ, hl, hf⟩
    · obtain ⟨s, ρ, hl, hf, -⟩ := entryOk_query_iff.mp (entries _ m)
      exact ⟨s, ρ, hl, hf⟩
    · exact entryOk_noRows_iff.mp (entries _ m)
    · obtain ⟨s, ρ, o, hl, -, -, ho, ha⟩ := entryOk_pick_iff.mp (entries _ m)
      exact ⟨s, ρ, o, hl, ho, ha⟩
  · rintro ⟨⟨seen_ok, revPick, revQuery⟩, ⟨rightsPick, rightsQuery, rightsNoRows, makes_ok⟩,
      present, linear⟩
    have entries : ∀ e ∈ fp, entryOk label L resolve v e = true := by
      intro e m
      cases e with
      | pick u l r p a =>
          obtain ⟨s, ρ, o, hl, ho, ha⟩ := present u l r p a m
          obtain ⟨s₁, ρ₁, hl₁, hf⟩ := rightsPick u l r p a m
          obtain ⟨s₂, ρ₂, hl₂, hr⟩ := revPick u l r p a m
          rw [hl] at hl₁ hl₂
          cases hl₁; cases hl₂
          exact entryOk_pick_iff.mpr ⟨s, ρ, o, hl, hf, hr, ho, ha⟩
      | query l r pat =>
          obtain ⟨s₁, ρ₁, hl₁, hf⟩ := rightsQuery l r pat m
          obtain ⟨s₂, ρ₂, hl₂, hr⟩ := revQuery l r pat m
          rw [hl₁] at hl₂
          cases hl₂
          exact entryOk_query_iff.mpr ⟨s₁, ρ₁, hl₁, hf, hr⟩
      | noRows l xs => exact entryOk_noRows_iff.mpr (rightsNoRows l xs m)
    exact ⟨seen_ok, entries,
      (identified_iff_linear cons makes (valid_of_entries entries)).mpr linear, makes_ok⟩

/-! ## Soundness -/

omit [DecidableEq A] [DecidableEq Sp] [DecidableEq O] in
/-- **A scanned space whose revision the check finds current is unchanged.** -/
theorem rows_eq_of_check {v₀ v₁ : View Sp O} {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    (scanned : Scanned resolve v₀ seen fp) (tracks : Tracks v₀ v₁)
    (seen_ok : seenOk resolve v₁ seen = true) :
    ∀ e ∈ fp, ∀ s ∈ e.spaces resolve, v₁.rows s = v₀.rows s := by
  intro e member s inSpaces
  obtain ⟨x, inSeen, hx, hrev⟩ := scanned e member s inSpaces
  obtain ⟨s', ρ, hl, hcur⟩ := seenOk_iff.mp seen_ok x inSeen
  rw [hl] at hx
  simp only [Option.map_some, Option.some.injEq] at hx
  subst hx
  exact tracks s' (hcur.trans hrev)

omit [DecidableEq Sp] [DecidableEq O] [DecidableEq A] in
theorem View.Consistent.regionOf_eq {v₀ v₁ : View Sp O} (cons₀ : v₀.Consistent label L)
    (cons₁ : v₁.Consistent label L) {region : R → Bool} {spaces : List Sp}
    (inside : ∀ r, region r = true → L.spaceOf r ∈ spaces)
    (same : ∀ s ∈ spaces, v₁.rows s = v₀.rows s) :
    regionOf label v₁.store region = regionOf label v₀.store region := by
  ext o
  simp only [mem_regionOf]
  constructor
  · rintro ⟨inStore, inRegion⟩
    have atS := inside _ inRegion
    have inRows : o ∈ v₁.rows (L.spaceOf (label o)) := (cons₁.mem_rows _ o).mpr ⟨inStore, rfl⟩
    rw [same _ atS] at inRows
    exact ⟨((cons₀.mem_rows _ o).mp inRows).1, inRegion⟩
  · rintro ⟨inStore, inRegion⟩
    have atS := inside _ inRegion
    have inRows : o ∈ v₀.rows (L.spaceOf (label o)) := (cons₀.mem_rows _ o).mpr ⟨inStore, rfl⟩
    rw [← same _ atS] at inRows
    exact ⟨((cons₁.mem_rows _ o).mp inRows).1, inRegion⟩

omit [DecidableEq Sp] [DecidableEq A] in
/-- The region of an entry lies in the spaces the entry depends on. -/
theorem Entry.region_inside {e : Entry Lc A Pt} {region : R → Bool}
    (h : e.region L resolve = some region) :
    ∀ r, region r = true → L.spaceOf r ∈ e.spaces resolve := by
  intro r inRegion
  cases e with
  | pick => simp [Entry.region] at h
  | query l rv pat =>
      simp only [Entry.region, Option.map_eq_some_iff] at h
      obtain ⟨⟨s, ρ⟩, hl, rfl⟩ := h
      simp [Entry.spaces, hl, L.regionAt_inside s pat r inRegion]
  | noRows l xs =>
      simp only [Entry.region, Option.some.injEq] at h
      subst h
      obtain ⟨x, member, hx⟩ := List.any_eq_true.mp inRegion
      simp only [Entry.spaces, List.mem_filterMap]
      cases hl : resolve x.2.1 with
      | none => rw [hl] at hx; simp at hx
      | some y =>
          obtain ⟨s, ρ⟩ := y
          rw [hl] at hx
          refine ⟨x, member, ?_⟩
          simp [hl, L.regionAt_inside s x.2.2 r hx]

omit [DecidableEq Sp] [DecidableEq A] in
/-- The space of a pick entry is among its spaces. -/
theorem Entry.pick_space_mem {u : Use} {l : Lc} {r p : ℕ} {a : A} {s : Sp}
    {ρ : Facet → Bool} (hl : resolve l = some (s, ρ)) :
    s ∈ (Entry.pick u l r p a : Entry Lc A Pt).spaces resolve := by
  simp [Entry.spaces, hl]

omit [DecidableEq O] in
/-- **What the kernel accepts holds and is linear.** If the walk built the footprint at `v₀`, the
runtime keeps the revision contract, and the check passes at the commit's view `v₁`, then the
footprint the entries denote at `v₀` holds at `v₁` and is linear. -/
theorem holds_of_check {v₀ v₁ : View Sp O} (cons₀ : v₀.Consistent label L)
    (cons₁ : v₁.Consistent label L) {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    {makes : List (Lc × A)} (scanned : Scanned resolve v₀ seen fp) (tracks : Tracks v₀ v₁)
    (ok : check label L resolve v₁ seen fp makes = true) :
    (decode label L resolve v₀ fp makes).Holds label v₁.store ∧
      (decode label L resolve v₀ fp makes).Linear := by
  obtain ⟨seen_ok, entries, identified, -⟩ := check_eq_true_iff.mp ok
  have same := rows_eq_of_check scanned tracks seen_ok
  -- a picked position names the same occurrence at both views
  have pickSame : ∀ u l r p a s ρ, Entry.pick u l r p a ∈ fp → resolve l = some (s, ρ) →
      v₀.at s p = v₁.at s p := by
    intro u l r p a s ρ m hl
    unfold View.at
    rw [same _ m s (Entry.pick_space_mem hl)]
  have validAt₀ :
      ∀ k ∈ takeKeys resolve fp ++ keepKeys resolve fp, (v₀.at k.1 k.2).isSome = true := by
    intro k member
    have valid₁ := valid_of_entries entries k member
    rcases List.mem_append.mp member with inT | inK
    · obtain ⟨l, r, a, ρ, m, hl⟩ := mem_takeKeys.mp inT
      rw [pickSame _ _ _ _ _ _ _ m hl]; exact valid₁
    · obtain ⟨l, r, a, ρ, m, hl⟩ := mem_keepKeys.mp inK
      rw [pickSame _ _ _ _ _ _ _ m hl]; exact valid₁
  have linear := (identified_iff_linear cons₀ makes validAt₀).mp identified
  refine ⟨⟨fun o inTakes => ?_, fun o inKeeps => ?_, fun q inQueries => ?_⟩, linear⟩
  · obtain ⟨k, kT, hk⟩ := List.mem_filterMap.mp (Multiset.mem_coe.mp inTakes)
    obtain ⟨l, r, a, ρ, m, hl⟩ := mem_takeKeys.mp kT
    rw [pickSame _ _ _ _ _ _ _ m hl] at hk
    exact (cons₁.at_mem hk).1
  · obtain ⟨k, kK, hk⟩ := List.mem_filterMap.mp (Multiset.mem_coe.mp inKeeps)
    obtain ⟨l, r, a, ρ, m, hl⟩ := mem_keepKeys.mp kK
    rw [pickSame _ _ _ _ _ _ _ m hl] at hk
    exact (cons₁.at_mem hk).1
  · obtain ⟨region, inRegions, rfl⟩ := List.mem_map.mp (Multiset.mem_coe.mp inQueries)
    obtain ⟨e, m, he⟩ := List.mem_filterMap.mp inRegions
    exact cons₀.regionOf_eq cons₁ (Entry.region_inside he) (same e m)

/-- **What the kernel accepts is enabled.** Every commit of the footprint the entries denote, with
fresh identities, is enabled at the commit's view. -/
theorem enabled_of_check {v₀ v₁ : View Sp O} (cons₀ : v₀.Consistent label L)
    (cons₁ : v₁.Consistent label L) {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    {makes : List (Lc × A)} (scanned : Scanned resolve v₀ seen fp) (tracks : Tracks v₀ v₁)
    (ok : check label L resolve v₁ seen fp makes = true) {c : Commit O R}
    (commit : IsCommitOf label v₁.store (decode label L resolve v₀ fp makes) c) :
    Enabled label v₁.store c := by
  obtain ⟨holds, linear⟩ := holds_of_check cons₀ cons₁ scanned tracks ok
  exact (commit.enabled_iff commit.fresh).mpr ⟨holds, linear.2⟩

/-- The revision check of one scanned space, as a predicate query: the space holds exactly what the
walk saw there. -/
def revisionQuery (spaceOf : R → Sp) (v₀ : View Sp O) (s : Sp) : PredicateQuery O R :=
  ⟨fun r => decide (spaceOf r = s), (v₀.rows s).toFinset⟩

omit [DecidableEq A] in
/-- **The revision check is a predicate query of each scanned space** (the one-revision protocol of
`SerializedPublication`, for each space): when it passes, every space listed in `seen` holds
exactly what the walk saw there. -/
theorem revisionQuery_holds {v₀ v₁ : View Sp O} (cons₁ : v₁.Consistent label L)
    {seen : List (Lc × ℕ)} (seenAt₀ : ∀ x ∈ seen, ∀ s, (resolve x.1).map Prod.fst = some s →
      x.2 = v₀.rev s) (tracks : Tracks v₀ v₁) (seen_ok : seenOk resolve v₁ seen = true) :
    ∀ x ∈ seen, ∀ s, (resolve x.1).map Prod.fst = some s →
      (revisionQuery L.spaceOf v₀ s).Holds label v₁.store := by
  intro x member s hs
  obtain ⟨s', ρ, hl, hcur⟩ := seenOk_iff.mp seen_ok x member
  rw [hl] at hs
  simp only [Option.map_some, Option.some.injEq] at hs
  subst hs
  have rowsSame := tracks s' (hcur.trans (seenAt₀ x member s' (by simp [hl])))
  unfold PredicateQuery.Holds revisionQuery
  ext o
  simp only [mem_regionOf, decide_eq_true_eq, List.mem_toFinset]
  rw [← rowsSame, cons₁.mem_rows]

/-! ## Rights -/

/-- The rights at each space that the handles in `H` give. -/
def heldRights (resolve : Lc → Option (Sp × (Facet → Bool))) (H : List Lc) (s : Sp)
    (f : Facet) : Bool :=
  H.any fun h =>
    match resolve h with
    | some (s', ρ) => decide (s' = s) && ρ f
    | none => false

theorem heldRights_of {H : List Lc} {h : Lc} (member : h ∈ H) {s : Sp} {ρ : Facet → Bool}
    (hl : resolve h = some (s, ρ)) {f : Facet} (hf : ρ f = true) :
    heldRights resolve H s f = true :=
  List.any_eq_true.mpr ⟨h, member, by simp [hl, hf]⟩

/-- **The check is formation, entry by entry.** For a footprint without a none query of sources whose
entries and makes are named by handles in `H`, every commit of the footprint is formed under the
rights those handles give. -/
theorem formedUnder_of_check {v₀ v₁ : View Sp O} (cons₀ : v₀.Consistent label L)
    {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)} {makes : List (Lc × A)}
    (ok : check label L resolve v₁ seen fp makes = true)
    (noNoRowsEntries : ∀ l xs, Entry.noRows l xs ∉ fp) {H : List Lc}
    (named : ∀ e ∈ fp, e.loc ∈ H) (namedMakes : ∀ m ∈ makes, m.1 ∈ H) {c : Commit O R}
    (commit : IsCommitOf label v₁.store (decode label L resolve v₀ fp makes) c) :
    FormedUnder label L.spaceOf (heldRights resolve H) c := by
  obtain ⟨-, entries, -, makes_ok⟩ := check_eq_true_iff.mp ok
  -- the space of the occurrence a pick names
  have pickRight : ∀ (u : Use) (keys : List (Sp × ℕ)),
      (∀ k ∈ keys, ∃ l r a ρ, Entry.pick u l r k.2 a ∈ fp ∧ resolve l = some (k.1, ρ)) →
      ∀ o ∈ (keys.filterMap fun k => v₀.at k.1 k.2),
        heldRights resolve H (L.spaceOf (label o)) u.facet = true := by
    intro u keys fromPicks o inList
    obtain ⟨k, kIn, hk⟩ := List.mem_filterMap.mp inList
    obtain ⟨l, r, a, ρ, m, hl⟩ := fromPicks k kIn
    obtain ⟨s, ρ', o', hl', hf, -, -, -⟩ := entryOk_pick_iff.mp (entries _ m)
    rw [hl] at hl'
    cases hl'
    rw [(cons₀.at_mem hk).2]
    exact heldRights_of (named _ m) hl hf
  refine ⟨fun o taken => ?_, fun o kept => ?_, fun o made => ?_, fun q inQueries r inRegion => ?_⟩
  · rw [commit.taken, Multiset.mem_toFinset] at taken
    exact pickRight .take _ (fun k kIn => mem_takeKeys.mp kIn) o (Multiset.mem_coe.mp taken)
  · rw [commit.kept, Multiset.mem_toFinset] at kept
    exact pickRight .keep _ (fun k kIn => mem_keepKeys.mp kIn) o (Multiset.mem_coe.mp kept)
  · have inLabels : label o ∈ labels label c.made := Multiset.mem_map_of_mem label made
    rw [commit.made] at inLabels
    obtain ⟨m, mIn, hm⟩ := List.mem_filterMap.mp (Multiset.mem_coe.mp inLabels)
    obtain ⟨s, ρ, hl, hsend⟩ := makesOk_iff.mp makes_ok m mIn
    rw [hl] at hm
    simp only [Option.map_some, Option.some.injEq] at hm
    rw [← hm, L.spaceOf_make]
    exact heldRights_of (namedMakes m mIn) hl hsend
  · obtain ⟨region, inRegions, rfl⟩ :=
      List.mem_map.mp (Multiset.mem_coe.mp ((commit.queries q).mp inQueries))
    obtain ⟨e, m, he⟩ := List.mem_filterMap.mp inRegions
    cases e with
    | pick => simp [Entry.region] at he
    | noRows l xs => exact absurd m (noNoRowsEntries l xs)
    | query l rv pat =>
        simp only [Entry.region, Option.map_eq_some_iff] at he
        obtain ⟨⟨s, ρ⟩, hl, rfl⟩ := he
        obtain ⟨s', ρ', hl', hobs, -⟩ := entryOk_query_iff.mp (entries _ m)
        rw [hl] at hl'
        cases hl'
        rw [L.regionAt_inside s pat r inRegion]
        exact heldRights_of (named _ m) hl hobs

/-! ## `every`: what each part of the kernel checks -/

/-- Two parts of a footprint are **apart**: no position one takes is taken or kept by the other. -/
def Apart (t₁ k₁ t₂ k₂ : List (Sp × ℕ)) : Prop :=
  (∀ x ∈ t₁, x ∉ t₂) ∧ (∀ x ∈ t₁, x ∉ k₂) ∧ ∀ x ∈ t₂, x ∉ k₁

omit [DecidableEq Sp] in
theorem identified_append_iff {t₁ k₁ t₂ k₂ : List (Sp × ℕ)} :
    Identified (t₁ ++ t₂) (k₁ ++ k₂) ↔ Identified t₁ k₁ ∧ Identified t₂ k₂ ∧ Apart t₁ k₁ t₂ k₂ := by
  unfold Identified Apart
  rw [List.nodup_append]
  simp only [List.mem_append, not_or]
  constructor
  · rintro ⟨⟨n₁, n₂, d⟩, h⟩
    exact ⟨⟨n₁, fun x m => (h x (Or.inl m)).1⟩, ⟨n₂, fun x m => (h x (Or.inr m)).2⟩,
      fun x m m' => d x m x m' rfl, fun x m => (h x (Or.inl m)).2, fun x m => (h x (Or.inr m)).1⟩
  · rintro ⟨⟨n₁, h₁⟩, ⟨n₂, h₂⟩, d, a₁, a₂⟩
    refine ⟨⟨n₁, n₂, fun x m y m' e => ?_⟩, fun x m => ?_⟩
    · subst e
      exact d x m m'
    · rcases m with m | m
      · exact ⟨h₁ x m, a₁ x m⟩
      · exact ⟨a₂ x m, h₂ x m⟩

/-- A list of entries is linear on its own. -/
def EntriesIdentified (resolve : Lc → Option (Sp × (Facet → Bool))) (fp : List (Entry Lc A Pt)) :
    Prop :=
  Identified (takeKeys resolve fp) (keepKeys resolve fp)

/-- Two lists of entries are apart. -/
def EntriesApart (resolve : Lc → Option (Sp × (Facet → Bool))) (fp fp' : List (Entry Lc A Pt)) :
    Prop :=
  Apart (takeKeys resolve fp) (keepKeys resolve fp) (takeKeys resolve fp') (keepKeys resolve fp')

omit [DecidableEq Sp] [DecidableEq A] in
theorem takeKeys_append (fp fp' : List (Entry Lc A Pt)) :
    takeKeys resolve (fp ++ fp') = takeKeys resolve fp ++ takeKeys resolve fp' :=
  List.filterMap_append

omit [DecidableEq Sp] [DecidableEq A] in
theorem keepKeys_append (fp fp' : List (Entry Lc A Pt)) :
    keepKeys resolve (fp ++ fp') = keepKeys resolve fp ++ keepKeys resolve fp' :=
  List.filterMap_append

omit [DecidableEq Sp] [DecidableEq A] in
theorem entriesIdentified_append_iff {fp fp' : List (Entry Lc A Pt)} :
    EntriesIdentified resolve (fp ++ fp') ↔
      EntriesIdentified resolve fp ∧ EntriesIdentified resolve fp' ∧
        EntriesApart resolve fp fp' := by
  unfold EntriesIdentified EntriesApart
  rw [takeKeys_append, keepKeys_append]
  exact identified_append_iff

omit [DecidableEq Sp] [DecidableEq A] in
theorem entriesApart_append_iff {fp fp' fp'' : List (Entry Lc A Pt)} :
    EntriesApart resolve fp (fp' ++ fp'') ↔
      EntriesApart resolve fp fp' ∧ EntriesApart resolve fp fp'' := by
  unfold EntriesApart Apart
  rw [takeKeys_append, keepKeys_append]
  simp only [List.mem_append, not_or, or_imp, forall_and]
  tauto

omit [DecidableEq Sp] [DecidableEq A] in
theorem entriesApart_flatten_iff {fp : List (Entry Lc A Pt)} :
    ∀ {rows : List (List (Entry Lc A Pt))},
      EntriesApart resolve fp rows.flatten ↔ ∀ r ∈ rows, EntriesApart resolve fp r
  | [] => by simp [EntriesApart, Apart, takeKeys, keepKeys]
  | r :: rest => by
      rw [List.flatten_cons, entriesApart_append_iff, entriesApart_flatten_iff]
      simp

omit [DecidableEq Sp] [DecidableEq A] in
/-- **What each part of the kernel checks, for `every`.** The commit's identification over the rows
and the kernel's own picks holds exactly when each row is linear on its own (the walk builds only
such rows), the rows are pairwise apart (the amalgamation), the kernel's picks are linear (the
walk), and the kernel's picks are apart from every row, which only the commit's identification
checks. -/
theorem identified_every_iff :
    ∀ (rows : List (List (Entry Lc A Pt))) (base : List (Entry Lc A Pt)),
      EntriesIdentified resolve (rows.flatten ++ base) ↔
        (∀ r ∈ rows, EntriesIdentified resolve r) ∧ rows.Pairwise (EntriesApart resolve) ∧
          EntriesIdentified resolve base ∧ ∀ r ∈ rows, EntriesApart resolve r base
  | [], base => by simp
  | r :: rest, base => by
      rw [List.flatten_cons, List.append_assoc, entriesIdentified_append_iff,
        identified_every_iff rest base, entriesApart_append_iff, entriesApart_flatten_iff,
        List.pairwise_cons]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

end Check

/-! ## The kernel's trace record, and what the verified checker certifies of it -/

section Trace

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceChecker

variable {Sp Lc A Pt : Type} [DecidableEq Sp] [DecidableEq A]
variable {label : ℕ → Lbl} {L : Labels Sp Lbl A Pt} {resolve : Lc → Option (Sp × (Facet → Bool))}

/-- The identities a printed predicate query lists: the occurrences of its location's space that
its printed region matches (`ia_trace_seen`). -/
def printedSeen (label : ℕ → Lbl) (resolve : Lc → Option (Sp × (Facet → Bool))) (v : View Sp ℕ)
    (spec : List (Tm × Tm)) (l : Lc) : List ℕ :=
  match resolve l with
  | some (s, _) => (v.rows s).filter fun o => regionPred spec (label o)
  | none => []

/-- **The record the kernel prints for a commit** (`ia_trace_commit`): the identities taken and
kept, the fresh identities made with their labels, each predicate query as a printed region with
the identities it matches, and what each `every` row takes. -/
def emit (label : ℕ → Lbl) (L : Labels Sp Lbl A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))
    (v : View Sp ℕ) (fp : List (Entry Lc A Pt)) (made : List (ℕ × Lbl))
    (printed : Entry Lc A Pt → List (Tm × Tm)) (rows : List (List (Entry Lc A Pt))) : TCommit where
  taken := (takeKeys resolve fp).filterMap fun k => v.at k.1 k.2
  kept := (keepKeys resolve fp).filterMap fun k => v.at k.1 k.2
  made := made
  queries := fp.filterMap fun e =>
    (e.region L resolve).map fun _ => ⟨printed e, printedSeen label resolve v (printed e) e.loc⟩
  rows := rows.map fun r => (takeKeys resolve r).filterMap fun k => v.at k.1 k.2

/-- The printer is **faithful** to the entries when the region it prints for each predicate query
is the region of the entry. -/
def Faithful (L : Labels Sp Lbl A Pt) (resolve : Lc → Option (Sp × (Facet → Bool)))
    (fp : List (Entry Lc A Pt)) (printed : Entry Lc A Pt → List (Tm × Tm)) : Prop :=
  ∀ e ∈ fp, ∀ region, e.region L resolve = some region → regionPred (printed e) = region


omit [DecidableEq A] [DecidableEq Sp] in
/-- The occurrences of a space that a region inside it holds are the region's occurrences. -/
theorem View.Consistent.filter_rows_toFinset {v : View Sp ℕ} (cons : v.Consistent label L)
    {s : Sp} {region : Lbl → Bool} (inside : ∀ r, region r = true → L.spaceOf r = s) :
    ((v.rows s).filter fun o => region (label o)).toFinset = regionOf label v.store region := by
  ext o
  simp only [List.mem_toFinset, List.mem_filter, mem_regionOf]
  constructor
  · rintro ⟨inRows, inRegion⟩
    exact ⟨((cons.mem_rows s o).mp inRows).1, inRegion⟩
  · rintro ⟨inStore, inRegion⟩
    exact ⟨(cons.mem_rows s o).mpr ⟨inStore, inside _ inRegion⟩, inRegion⟩

omit [DecidableEq A] [DecidableEq Sp] in
/-- **A faithfully printed predicate query decodes to the query the entry denotes.** -/
theorem printed_query_decode {v₀ v₁ : View Sp ℕ} (cons₀ : v₀.Consistent label L)
    (cons₁ : v₁.Consistent label L) {fp : List (Entry Lc A Pt)}
    {printed : Entry Lc A Pt → List (Tm × Tm)} (faithful : Faithful L resolve fp printed)
    (noNoRowsEntries : ∀ l xs, Entry.noRows l xs ∉ fp)
    (same : ∀ e ∈ fp, ∀ s ∈ e.spaces resolve, v₁.rows s = v₀.rows s) {e : Entry Lc A Pt}
    (m : e ∈ fp) {region : Lbl → Bool} (he : e.region L resolve = some region) :
    TQuery.decode ⟨printed e, printedSeen label resolve v₁ (printed e) e.loc⟩ =
      ⟨region, regionOf label v₀.store region⟩ := by
  have printedRegion := faithful e m region he
  cases e with
  | pick => simp [Entry.region] at he
  | noRows l xs => exact absurd m (noNoRowsEntries l xs)
  | query l rv pat =>
      have inside := Entry.region_inside he
      simp only [Entry.region, Option.map_eq_some_iff] at he
      obtain ⟨⟨s, ρ⟩, hl, rfl⟩ := he
      simp only [TQuery.decode, printedRegion, Entry.loc, printedSeen, hl]
      congr 1
      rw [← cons₀.regionOf_eq cons₁ inside (same _ m)]
      exact cons₁.filter_rows_toFinset (L.regionAt_inside s pat)

/-- **What the kernel accepts, the checker accepts.** When the check passes at the commit's view,
the walk built the footprint at `v₀` under the revision contract, the footprint has no none query of
sources, and the printer is faithful, the printed commit passes the checker's enabling test at the
commit's store. -/
theorem emit_enabledB {v₀ v₁ : View Sp ℕ} (cons₀ : v₀.Consistent label L)
    (cons₁ : v₁.Consistent label L) {seen : List (Lc × ℕ)} {fp : List (Entry Lc A Pt)}
    {makes : List (Lc × A)} (scanned : Scanned resolve v₀ seen fp) (tracks : Tracks v₀ v₁)
    (ok : check label L resolve v₁ seen fp makes = true)
    (noNoRowsEntries : ∀ l xs, Entry.noRows l xs ∉ fp)
    {printed : Entry Lc A Pt → List (Tm × Tm)} (faithful : Faithful L resolve fp printed)
    {made : List (ℕ × Lbl)} {storeList : List ℕ} (store : storeList.toFinset = v₁.store)
    (fresh : Disjoint (made.map Prod.fst).toFinset v₁.store) (rows : List (List (Entry Lc A Pt))) :
    enabledB label storeList (emit label L resolve v₁ fp made printed rows) = true := by
  obtain ⟨holds₀, linear₀⟩ := holds_of_check cons₀ cons₁ scanned tracks ok
  obtain ⟨seen_ok, entries, -, -⟩ := check_eq_true_iff.mp ok
  have same := rows_eq_of_check scanned tracks seen_ok
  -- the footprint the entries denote is the same at both views
  have takesSame : (takeKeys resolve fp).filterMap (fun k => v₀.at k.1 k.2) =
      (takeKeys resolve fp).filterMap (fun k => v₁.at k.1 k.2) := by
    refine List.filterMap_congr fun k kIn => ?_
    obtain ⟨l, r, a, ρ, m, hl⟩ := mem_takeKeys.mp kIn
    unfold View.at
    rw [same _ m k.1 (Entry.pick_space_mem hl)]
  have keepsSame : (keepKeys resolve fp).filterMap (fun k => v₀.at k.1 k.2) =
      (keepKeys resolve fp).filterMap (fun k => v₁.at k.1 k.2) := by
    refine List.filterMap_congr fun k kIn => ?_
    obtain ⟨l, r, a, ρ, m, hl⟩ := mem_keepKeys.mp kIn
    unfold View.at
    rw [same _ m k.1 (Entry.pick_space_mem hl)]
  rw [enabledB_iff, store]
  set c := (emit label L resolve v₁ fp made printed rows).decode with hc
  -- the printed commit is a commit of the footprint, with the labels it makes
  let fp' : Footprint ℕ Lbl :=
    { decode label L resolve v₀ fp makes with makes := labels label c.made }
  have commit : IsCommitOf label v₁.store fp' c := by
    refine ⟨?_, ?_, fun q => ?_, ?_, rfl⟩
    · simp only [fp', c, emit, TCommit.decode, decode, takesSame]
      rfl
    · simp only [fp', c, emit, TCommit.decode, decode, keepsSame]
      rfl
    · simp only [fp', c, emit, TCommit.decode, decode, Multiset.mem_coe, List.mem_map,
        List.mem_filterMap, Option.map_eq_some_iff]
      constructor
      · rintro ⟨tq, ⟨e, m, region, he, rfl⟩, rfl⟩
        exact ⟨region, ⟨e, m, he⟩,
          (printed_query_decode cons₀ cons₁ faithful noNoRowsEntries same m he).symm⟩
      · rintro ⟨region, ⟨e, m, he⟩, rfl⟩
        exact ⟨⟨printed e, printedSeen label resolve v₁ (printed e) e.loc⟩, ⟨e, m, region, he, rfl⟩,
          printed_query_decode cons₀ cons₁ faithful noNoRowsEntries same m he⟩
    · simpa [c, emit, TCommit.decode, TCommit.madeIds] using fresh
  exact (commit.enabled_iff commit.fresh).mpr ⟨holds₀, linear₀.2⟩

omit [DecidableEq Sp] [DecidableEq A] in
/-- **The printed rows pass the checker's row test** when the commit's identification holds and
its picked positions name occurrences. -/
theorem emit_rowsOk {v : View Sp ℕ} (cons : v.Consistent label L)
    {rows : List (List (Entry Lc A Pt))} {base : List (Entry Lc A Pt)}
    (identified : EntriesIdentified resolve (rows.flatten ++ base))
    (made : List (ℕ × Lbl)) (printed : Entry Lc A Pt → List (Tm × Tm)) :
    (emit label L resolve v (rows.flatten ++ base) made printed rows).rowsOk = true := by
  obtain ⟨-, pairwise, -, -⟩ := (identified_every_iff rows base).mp identified
  rw [rowsOk_iff]
  simp only [emit]
  refine ⟨?_, ?_⟩
  · rw [List.pairwise_map]
    refine pairwise.imp fun {r r'} apart => ?_
    rw [Finset.disjoint_left]
    intro o inR inR'
    obtain ⟨k, kR, hk⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inR)
    obtain ⟨k', kR', hk'⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inR')
    exact apart.1 k kR (cons.at_inj hk' hk ▸ kR')
  · intro row inRows
    obtain ⟨r, rIn, rfl⟩ := List.mem_map.mp inRows
    intro o inRow
    obtain ⟨k, kR, hk⟩ := List.mem_filterMap.mp (List.mem_toFinset.mp inRow)
    refine List.mem_toFinset.mpr (List.mem_filterMap.mpr ⟨k, ?_, hk⟩)
    rw [takeKeys_append]
    refine List.mem_append_left _ ?_
    unfold takeKeys at kR ⊢
    rw [List.filterMap_flatten]
    exact List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, rIn, rfl⟩, kR⟩

end Trace

/-! ## Controls -/

namespace Controls

/-- Two spaces: a channel region and a plain space. -/
inductive Space where
  | chan
  | plain
  deriving DecidableEq, Repr

/-- Locations: the channel's holder handle, a `peek` handle to the channel, and the plain space. -/
inductive Loc where
  | chanHolder
  | chanPeek
  | plain
  deriving DecidableEq, Repr

/-- A channel's holder may receive, peek and send; a channel has no `observe`. -/
def chanHolderRights : Facet → Bool
  | .observe => false
  | _ => true

/-- Handles name the channel; the plain space has every right. -/
def resolve : Loc → Option (Space × (Facet → Bool))
  | .chanHolder => some (.chan, chanHolderRights)
  | .chanPeek => some (.chan, fun f => decide (f = .peek))
  | .plain => some (.plain, fun _ => true)

/-- Labels are a space and an atom; a pattern is an atom, or `none` for any atom. -/
def labels : Labels Space (Space × ℕ) ℕ (Option ℕ) where
  spaceOf := Prod.fst
  atomOf := Prod.snd
  make := Prod.mk
  regionAt s p r := decide (r.1 = s) && match p with
    | none => true
    | some a => decide (r.2 = a)
  spaceOf_make _ _ := rfl
  regionAt_inside s p r h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

/-- Occurrence `0` is message `7` on the channel, `1` message `9` there, `2` another message `7`;
the rest live in the plain space. -/
def lab : ℕ → Space × ℕ
  | 0 => (.chan, 7)
  | 1 => (.chan, 9)
  | 2 => (.chan, 7)
  | _ => (.plain, 0)

/-- A view with the given channel occurrences and channel revision; the plain space is empty. -/
def chanView (store : Finset ℕ) (rev : ℕ) (rows : List ℕ) : View Space ℕ :=
  ⟨store, fun | .chan => rev | .plain => 0, fun | .chan => rows | .plain => []⟩

/-- Message `0` on the channel, at revision `1`. -/
abbrev oneMessage : View Space ℕ := chanView {0} 1 [0]

theorem chanView_consistent {store : Finset ℕ} {rev : ℕ} {rows : List ℕ} (nodup : rows.Nodup)
    (onChan : ∀ o, o ∈ rows ↔ o ∈ store) (chanOnly : ∀ o ∈ store, (lab o).1 = .chan) :
    (chanView store rev rows).Consistent lab labels where
  nodup s := by cases s <;> simp [chanView, nodup]
  mem_rows s o := by
    cases s with
    | chan =>
        simp only [chanView, labels, onChan]
        exact ⟨fun h => ⟨h, chanOnly o h⟩, fun h => h.1⟩
    | plain =>
        simp only [chanView, labels, List.not_mem_nil, false_iff, not_and]
        intro h
        rw [chanOnly o h]
        decide

theorem oneMessage_consistent : oneMessage.Consistent lab labels :=
  chanView_consistent (by decide) (fun o => by simp) (by decide)

/-- Take message `7` at position `0` of the channel, read at revision `1`, through the holder. -/
def holderTake : List (Entry Loc ℕ (Option ℕ)) := [.pick .take .chanHolder 1 0 7]

/-- The channel scanned at revision `1`. -/
def seenChan : List (Loc × ℕ) := [(.chanHolder, 1)]

/-- The commit that takes occurrence `0`. -/
def takeZero : Commit ℕ (Space × ℕ) := ⟨{0}, ∅, ∅, []⟩

theorem takeZero_of :
    IsCommitOf lab ({0} : Finset ℕ) (decode lab labels resolve oneMessage holderTake []) takeZero :=
  ⟨by decide, by decide, fun _ => by simp [takeZero, decode, holderTake, takeKeys, Entry.region],
    by decide, by decide⟩

/-- **Positive control**: the holder's take passes the check, and `enabled_of_check` applies to it
(the walk and the commit at one view). -/
theorem holder_take_passes :
    check lab labels resolve oneMessage seenChan holderTake [] = true ∧
      Enabled lab ({0} : Finset ℕ) takeZero := by
  refine ⟨by decide, enabled_of_check (v₀ := oneMessage) (v₁ := oneMessage) (seen := seenChan)
    oneMessage_consistent oneMessage_consistent (fun e m s inS => ?_) (fun _ _ => rfl) (by decide)
    takeZero_of⟩
  simp only [holderTake, List.mem_singleton] at m
  subst m
  simp only [Entry.spaces, resolve, Option.map_some, Option.toList_some, List.mem_singleton] at inS
  subst inS
  exact ⟨(.chanHolder, 1), by simp [seenChan], rfl, rfl⟩

/-- **Positive control for formation**: the holder's take is formed under the holder's handle. -/
theorem holder_take_formed :
    FormedUnder lab Prod.fst (heldRights resolve [.chanHolder]) takeZero :=
  formedUnder_of_check (L := labels) (v₀ := oneMessage) (v₁ := oneMessage) oneMessage_consistent
    (seen := seenChan) (makes := []) (by decide) (by simp [holderTake])
    (by simp [holderTake, Entry.loc]) (by simp) takeZero_of

/-- **Whole-space revisions, stale**: message `9` arrived on the channel (revision `2`) after the
walk kept message `0`. The kernel refuses; the commit that keeps `0` is enabled. -/
theorem stale_refused :
    check lab labels resolve (chanView {0, 1} 2 [0, 1]) seenChan
        [.pick .keep .chanHolder 1 0 7] [] = false ∧
      Enabled lab ({0, 1} : Finset ℕ) (⟨∅, {0}, ∅, []⟩ : Commit ℕ (Space × ℕ)) := by
  decide

/-- **Whole-space revisions, an undone write**: a write to the channel was undone before the commit
(revision `3`, the same occurrences). The kernel refuses; the commit is enabled. -/
theorem undone_write_refused :
    check lab labels resolve (chanView {0} 3 [0]) seenChan [.pick .keep .chanHolder 1 0 7] [] =
        false ∧
      Enabled lab ({0} : Finset ℕ) (⟨∅, {0}, ∅, []⟩ : Commit ℕ (Space × ℕ)) := by
  decide

/-- **Linearity of the list**: a footprint that lists the take of position `0` twice is refused and
denotes a footprint that is not linear, while the commit that takes `0` once is enabled. -/
theorem double_take_refused :
    check lab labels resolve oneMessage seenChan
        [.pick .take .chanHolder 1 0 7, .pick .take .chanHolder 1 0 7] [] = false ∧
      ¬ (decode lab labels resolve oneMessage
        [.pick .take .chanHolder 1 0 7, .pick .take .chanHolder 1 0 7] []).Linear ∧
      Enabled lab ({0} : Finset ℕ) takeZero := by
  refine ⟨by decide, fun linear => ?_, by decide⟩
  have := linear.1
  revert this
  decide

/-- **Rights per handle**: a take through the `peek` handle is refused, although the process also
holds the holder's handle, so the commit is formed under the union of its held rights. -/
theorem per_handle_refused :
    check lab labels resolve oneMessage [(.chanPeek, 1)] [.pick .take .chanPeek 1 0 7] [] = false ∧
      FormedUnder lab Prod.fst (heldRights resolve [.chanHolder, .chanPeek]) takeZero := by
  refine ⟨by decide, ⟨fun o m => ?_, by simp [takeZero], by simp [takeZero], by simp [takeZero]⟩⟩
  simp only [takeZero, Finset.mem_singleton] at m
  subst m
  decide

/-- **The revision contract is needed**: a runtime that let message `0` go and message `2` (also
`7`) arrive without moving the channel's revision passes the check for the walk's keep of `0`,
whose commit is not enabled. -/
theorem untracked_write_accepted :
    ¬ Tracks oneMessage (chanView {2} 1 [2]) ∧
      check lab labels resolve (chanView {2} 1 [2]) seenChan [.pick .keep .chanHolder 1 0 7] [] =
        true ∧
      ¬ Enabled lab ({2} : Finset ℕ) (⟨∅, {0}, ∅, []⟩ : Commit ℕ (Space × ℕ)) := by
  refine ⟨fun tracks => ?_, by decide, by decide⟩
  have := tracks .chan rfl
  simp [chanView] at this

/-- The empty channel. -/
abbrev noMessage : View Space ℕ := chanView ∅ 0 []

/-- The none query of a read source on the channel through the `peek` handle, checked at the plain
space, as `(transform &plain (absent (read $p (msg $x))) ...)` records it. -/
def absenceOfSource : List (Entry Loc ℕ (Option ℕ)) := [.noRows .plain [(.keep, .chanPeek, none)]]

/-- The region the none query denotes: the channel's messages, through its one source. -/
def noneRegion : Space × ℕ → Bool := fun r =>
  [((Use.keep, Loc.chanPeek, (none : Option ℕ)) : Use × Loc × Option ℕ)].any fun x =>
    match resolve x.2.1 with
    | some (s, _) => labels.regionAt s x.2.2 r
    | none => false

/-- The commit the kernel's footprint denotes: the predicate query of the channel's messages. -/
def noneCommit : Commit ℕ (Space × ℕ) :=
  ⟨∅, ∅, ∅, [⟨noneRegion, regionOf lab noMessage.store noneRegion⟩]⟩

/-- **The none query of sources bypasses `observe`.** The kernel's check passes for the none query of a
read source on the channel through a `peek` handle, while the same none query written on the channel
is refused for want of `observe`; and the commit the footprint denotes, a predicate query of the
channel's region, is not formed under the rights the process holds. -/
theorem absence_of_sources_not_formed :
    check lab labels resolve noMessage [(.plain, 0), (.chanPeek, 0)] absenceOfSource [] = true ∧
      check lab labels resolve noMessage [(.chanPeek, 0)] [.query .chanPeek 0 none] [] = false ∧
      IsCommitOf lab (∅ : Finset ℕ) (decode lab labels resolve noMessage absenceOfSource [])
        noneCommit ∧
      ¬ FormedUnder lab Prod.fst (heldRights resolve [.plain, .chanPeek]) noneCommit := by
  refine ⟨by decide, by decide, ⟨rfl, rfl, fun _ => Multiset.mem_coe.symm, by simp [noneCommit],
    rfl⟩, fun formed => ?_⟩
  have observes := formed.queries _ (List.mem_singleton_self _) (.chan, 7) (by decide)
  revert observes
  decide

/-! ### The parts of the check, one positive and one negative instance each -/

/-- **Consistent views**: the one-message view is; a view listing occurrence `0` twice is not. -/
theorem consistent_controls :
    oneMessage.Consistent lab labels ∧ ¬ (chanView {0} 1 [0, 0]).Consistent lab labels :=
  ⟨oneMessage_consistent, fun cons => by have := cons.nodup .chan; simp [chanView] at this⟩

/-- **Identification by position**: one take passes; a take and a keep of one position do not. -/
theorem identified_controls :
    Identified [(Space.chan, 0)] [] ∧ ¬ Identified [(Space.chan, 0)] [(Space.chan, 0)] := by
  decide

/-- **What the walk scanned**: listing the channel covers the holder's take; listing nothing does
not. -/
theorem scanned_controls :
    Scanned resolve oneMessage seenChan holderTake ∧ ¬ Scanned resolve oneMessage [] holderTake := by
  refine ⟨fun e m s inS => ?_, fun scanned => ?_⟩
  · simp only [holderTake, List.mem_singleton] at m
    subst m
    simp only [Entry.spaces, resolve, Option.map_some, Option.toList_some, List.mem_singleton] at inS
    subst inS
    exact ⟨(.chanHolder, 1), by simp [seenChan], rfl, rfl⟩
  · obtain ⟨x, inSeen, -⟩ := scanned _ (List.mem_singleton_self _) .chan
      (by simp [Entry.spaces, resolve])
    simp at inSeen

/-- **The parts of the check**: at the one-message view the holder's take has current revisions,
held rights and a present position; after another write its revision is not current, through the
`peek` handle its right is not held, and in the empty channel its position holds nothing. -/
theorem parts_controls :
    (RevisionsCurrent resolve oneMessage seenChan holderTake ∧ RightsHeld resolve holderTake [] ∧
        Present lab labels resolve oneMessage holderTake) ∧
      ¬ RevisionsCurrent resolve (chanView {0, 1} 2 [0, 1]) seenChan holderTake ∧
      ¬ RightsHeld resolve [(.pick .take .chanPeek 1 0 7 : Entry Loc ℕ (Option ℕ))] [] ∧
      ¬ Present lab labels resolve noMessage holderTake := by
  obtain ⟨revisions, rights, present, -⟩ := (check_iff oneMessage_consistent).mp
    (show check lab labels resolve oneMessage seenChan holderTake [] = true by decide)
  refine ⟨⟨revisions, rights, present⟩, fun current => ?_, fun held => ?_, fun present' => ?_⟩
  · obtain ⟨s, ρ, hl, hrev⟩ := current.1 (.chanHolder, 1) (by simp [seenChan])
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [chanView] at hrev
  · obtain ⟨s, ρ, hl, hf⟩ := held.1 .take .chanPeek 1 0 7 (List.mem_singleton_self _)
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [Use.facet] at hf
  · obtain ⟨s, ρ, o, hl, hat, -⟩ := present' .take .chanHolder 1 0 7 (List.mem_singleton_self _)
    simp only [resolve, Option.some.injEq, Prod.mk.injEq] at hl
    obtain ⟨rfl, rfl⟩ := hl
    simp [View.at, chanView] at hat

/-- **Rows apart**: rows that take positions `0` and `1` are apart; two rows that take one position
are not, nor a row that keeps what another takes. Each row is linear on its own. -/
theorem apart_controls :
    EntriesApart resolve [(.pick .take .chanHolder 1 0 7 : Entry Loc ℕ (Option ℕ))]
        [.pick .take .chanHolder 1 1 9] ∧
      ¬ EntriesApart resolve [(.pick .take .chanHolder 1 0 7 : Entry Loc ℕ (Option ℕ))]
        [.pick .take .chanHolder 1 0 7] ∧
      ¬ EntriesApart resolve [(.pick .take .chanHolder 1 0 7 : Entry Loc ℕ (Option ℕ))]
        [.pick .keep .chanHolder 1 0 7] ∧
      EntriesIdentified resolve [(.pick .take .chanHolder 1 0 7 : Entry Loc ℕ (Option ℕ))] ∧
      ¬ EntriesIdentified resolve
        [(.pick .take .chanHolder 1 0 7 : Entry Loc ℕ (Option ℕ)), .pick .keep .chanHolder 1 0 7] := by
  unfold EntriesApart EntriesIdentified Apart
  decide

end Controls

/-! ## Controls on the printed record, with the verified checker -/

namespace Controls.Printed

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.TraceChecker

/-- The region `nm 1` of the channel and `nm 2` of the transform. -/
def chanRegion : Tm := .expr [.sym "nm", .sym "1"]
def plainRegion : Tm := .expr [.sym "nm", .sym "2"]

/-- The query the kernel prints for `(absent (read C (msg $x)))` run at `nm 2` (as in the draft's
trace): the transform's region, with the source itself as the pattern. -/
def printedAbsenceOfSource : TQuery :=
  ⟨[(plainRegion, .expr [.sym "read", chanRegion, .expr [.sym "msg", .var 0]])], []⟩

/-- The query that none query means: no message on the channel. -/
def noMessageQuery : TQuery := ⟨[(chanRegion, .expr [.sym "msg", .var 0])], []⟩

/-- Occurrence `0` is the message `7` on the channel. -/
def msgTable : List (ℕ × Lbl) := [(0, ⟨chanRegion, .expr [.sym "msg", .sym "7"]⟩)]

/-- One message on the channel. -/
def withMessage : CState := ⟨[0], [0], [], []⟩

/-- **The printed none query of sources is vacuous.** With a message on the channel, a commit carrying
the printed query is a valid run for the checker, while the query that none query means fails: the
checker certifies nothing about the none query of sources. -/
theorem printed_absence_of_source_vacuous :
    (checkRun (labelOf msgTable) withMessage
        [.fire ⟨[], [], [], [printedAbsenceOfSource], []⟩]).isSome = true ∧
      (checkRun (labelOf msgTable) withMessage [.fire ⟨[], [], [], [noMessageQuery], []⟩]).isSome
        = false := by
  decide

/-! ### Faithful printing, and the whole chain on one commit -/

/-- Labels of the trace: a label's space is its location term, and a pattern's region at a space is
the labels there whose atom it matches. -/
def traceLabels : Labels Tm Lbl Tm Tm where
  spaceOf := Lbl.loc
  atomOf := Lbl.atom
  make := Lbl.mk
  regionAt s p l := decide (l.loc = s) && (matchTm p l.atom []).isSome
  spaceOf_make _ _ := rfl
  regionAt_inside s p l h := by
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1

/-- Every location term names its space, with every right. -/
def traceResolve : Tm → Option (Tm × (Facet → Bool)) := fun l => some (l, fun _ => true)

/-- The pattern of messages. -/
def msgPat : Tm := .expr [.sym "msg", .var 0]

/-- A predicate query of the channel's messages, read at revision `1`. -/
def channelQuery : Entry Tm Tm Tm := .query chanRegion 1 msgPat

/-- The none query of a read source on the channel, checked at the transform's space. -/
def absenceOfSourceEntry : Entry Tm Tm Tm := .noRows plainRegion [(.keep, chanRegion, msgPat)]

/-- What the kernel prints for a region: a query's own location and pattern; for the none query of
sources, the transform's space with the source itself as the pattern. -/
def printedBy : Entry Tm Tm Tm → List (Tm × Tm)
  | .query l _ p => [(l, p)]
  | .noRows l _ => [(l, .expr [.sym "read", chanRegion, msgPat])]
  | .pick .. => []

/-- **Faithful printing, positive and negative**: a predicate query printed as its own region is
faithful; the none query of sources printed as the kernel prints it is not, at the label of a message
on the channel. -/
theorem faithful_controls :
    Faithful traceLabels traceResolve [channelQuery] printedBy ∧
      ¬ Faithful traceLabels traceResolve [absenceOfSourceEntry] printedBy := by
  refine ⟨fun e m region he => ?_, fun faithful => ?_⟩
  · simp only [List.mem_singleton] at m
    subst m
    simp only [Entry.region, channelQuery, traceResolve, Option.map_some, Option.some.injEq] at he
    subst he
    funext l
    exact regionPred_ground (by decide) msgPat l
  · have := congrFun (faithful _ (List.mem_singleton_self _) _ rfl)
      ⟨chanRegion, .expr [.sym "msg", .sym "7"]⟩
    revert this
    decide

/-- The view of the trace control: message `0` on the channel, every space at revision `1`. -/
def traceView : View Tm ℕ :=
  ⟨{0}, fun _ => 1, fun s => if s = chanRegion then [0] else []⟩

theorem traceView_consistent : traceView.Consistent (labelOf msgTable) traceLabels where
  nodup s := by
    show (if s = chanRegion then [0] else []).Nodup
    split <;> simp
  mem_rows s o := by
    unfold traceView
    by_cases atChan : s = chanRegion
    · subst atChan
      by_cases zero : o = 0
      · subst zero; simp [traceLabels, labelOf, msgTable]
      · simp [zero]
    · by_cases zero : o = 0
      · subst zero
        simp only [atChan, if_false, List.not_mem_nil, Finset.mem_singleton, true_and, false_iff]
        intro same
        exact atChan (by rw [← same]; rfl)
      · simp [atChan, zero]

/-- **The whole chain, on one commit**: the channel query passes the kernel's check, its printed
record passes the checker's enabling test (`emit_enabledB`), and the checker accepts it as a run. -/
theorem emit_instance :
    check (labelOf msgTable) traceLabels traceResolve traceView [(chanRegion, 1)] [channelQuery] [] =
        true ∧
      enabledB (labelOf msgTable) [0]
        (emit (labelOf msgTable) traceLabels traceResolve traceView [channelQuery] [] printedBy []) =
        true ∧
      (checkRun (labelOf msgTable) withMessage
        [.fire (emit (labelOf msgTable) traceLabels traceResolve traceView [channelQuery] [] printedBy
          [])]).isSome = true := by
  have ok : check (labelOf msgTable) traceLabels traceResolve traceView [(chanRegion, 1)]
      [channelQuery] [] = true := by decide
  refine ⟨ok, emit_enabledB traceView_consistent traceView_consistent (fun e m s inS => ?_)
    (fun _ _ => rfl) ok (by simp [channelQuery]) faithful_controls.1 (by decide) (by simp) [], ?_⟩
  · simp only [List.mem_singleton] at m
    subst m
    simp only [Entry.spaces, channelQuery, traceResolve, Option.map_some, Option.toList_some,
      List.mem_singleton] at inS
    subst inS
    exact ⟨(chanRegion, 1), by simp, rfl, rfl⟩
  · decide

end Controls.Printed

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.RegionPermissions.KernelCommit
