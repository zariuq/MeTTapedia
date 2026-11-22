import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.SourceMatching
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves

/-!
# From transform sources to ground commits

A `transform` names what it touches through **sources**, patterns with variables in one of
several modes, and says what it produces through a **template**. This module compiles a
transform and a store into the ground commits of `Commits`, through a matcher (`SourceMatching`).

## Sources

* `read p`: one occurrence whose label `p` solves; it is kept.
* `take p`: one such occurrence; it is taken.
* `absent p`: no occurrence of the region of `p`; a predicate query that saw nothing.
* `unique a p`: exactly one occurrence in the region of `p`; a predicate query that saw it, and
  with `a = take` a take of it.
* `collect a p q fold`: the whole region of `p`, one predicate query (and with `a = take` taken); the
  bag of its labels is folded into one value, which the pattern `q` matches.
* `let p eval` (`letBind`): a computed value matched by `p`; no footprint.
* conjunction: sources in sequence, bindings flowing left to right (`SourceList.cons`).
* absence of sources (`SourceList.absent`): the complete inner query has no row;
  retain its completeness observations and continue without its local bindings.
* `every rest`: from here on, every row fires in one commit (`SourceList.every`).

## Rows and footprints

A row is a substitution and the list of what each source picked (`Pick`). Its **footprint**
(`Footprint`) sums what the picks take, keep, query and make; footprints form a
commutative monoid, and a row's footprint is a monoid homomorphism of its picks
(`footprintOf_cons`). `rows` enumerates the rows of a source list at a store, through the matcher:

* an `each` row ends with the template instantiated under its substitution (`Pick.make`);
* an `every` suffix is one row with one pick, `Pick.amalgam`: the sum of the footprints of all
  the suffix's rows that are linear on their own, plus the **completeness queries**, one predicate
  query of the computed region of each source of the suffix (`complRegions`). The suffix's rows bind
  nothing that later sources see.

A footprint is **linear** when no occurrence is taken twice and none is both taken and kept
(`Footprint.Linear`): the identification condition of double-pushout rewriting, extended to the
rows that `every` amalgamates. A commit is **of** a footprint when it takes and keeps the
footprint's occurrences, makes fresh occurrences with the footprint's labels, and has its
predicate queries (`IsCommitOf`); one exists whenever fresh occurrences of every label exist
(`exists_isCommitOf`). A transform **fires** a commit when the commit is of a linear row
(`Fires`).

## Footprint soundness

* **What the rows touch is in the store** (`holds_of_mem_rows`), so a commit a transform fires is
  enabled there (`Fires.enabled`).
* **The footprint is exactly what the row depends on** (`mem_rows_iff_holds`): a row found at one
  store is a row at another store exactly when the other store contains what the row takes and
  keeps and satisfies its predicate queries. Hence, for a commit of a linear row, being enabled at a
  later store is being a row of the transform there (`enabled_iff_mem_rows`): validating the
  commit (claims, kept occurrences live, region epochs unchanged) is re-running the match. For an
  `every` suffix this needs the completeness queries, through **locality**
  (`rows_congr`): the rows of a source list depend only on the store's occurrences inside its
  computed regions. Both need only that the matcher's answers extend their start and that its
  regions shrink as substitutions grow (`Matcher.RegionMonotone`).
* **What each pick contributes** (`footprint_take`, `footprint_keep`, `footprint_query`,
  `footprint_result`): a take source takes its occurrence, a read source keeps it, the complete
  sources query their region (and take it with `a = take`), `let` contributes nothing.

## `every` refuses rows that take one occurrence, and may be vacuous

The `every` footprint sums its rows' takes as a bag, so when two rows take one occurrence it is not
linear and nothing fires (`everyFootprint_not_linear_of_shared_take`), as the multiset `every` of
`TransformQuantifiers` refuses it. With no row at all it takes, keeps and makes nothing
(`everyFootprint_vacuous`): after a taking kernel the kernel is consumed and nothing produced.

## `every` is the amalgamation

`isCommitOf_every` says the commit of an `every` row is the amalgamation of the commits of its
rows (`Waves.amalgamate`) with the completeness queries added, the form of
`Basis.every_complete_spoiled_by_arrival`. A linear amalgamation has pairwise disjoint takes, so
its rows do not clash (`noClash_of_linear_sum`), and `Waves.every_serializable_iff` applies: the
`every` commit agrees with a serialization of its rows exactly when their precedence relation is
acyclic (`every_commit_serializable_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uV uT uP

variable {O : Type uO} {V : Type uV} {T : Type uT} {P : Type uP}

/-! ## Syntax -/

/-- How a complete source treats the region it saw: read it, or also take it. -/
inductive Access where
  | read
  | take
  deriving DecidableEq, Repr

/-- One source of a transform. -/
inductive Source (V : Type uV) (T : Type uT) (P : Type uP) where
  /-- One occurrence matching `p`, kept. -/
  | read (p : P)
  /-- One occurrence matching `p`, taken. -/
  | take (p : P)
  /-- No occurrence in the region of `p`. -/
  | absent (p : P)
  /-- Exactly one occurrence in the region of `p`. -/
  | unique (access : Access) (p : P)
  /-- The whole region of `p`; its bag of labels, folded, is matched by `coll`. -/
  | collect (access : Access) (p : P) (coll : P) (fold : Multiset T → T)
  /-- A computed value matched by `p` (the `let` source). -/
  | letBind (p : P) (eval : Subst V T → List T)

/-- A list of sources: conjunction, and `every` for the rest. -/
inductive SourceList (V : Type uV) (T : Type uT) (P : Type uP) where
  | done
  | cons (s : Source V T P) (rest : SourceList V T P)
  /-- Continue with the original bindings only if the complete inner query has no row. -/
  | absent (query rest : SourceList V T P)
  /-- From here on, every row fires in one commit. -/
  | every (rest : SourceList V T P)

/-- A transform: its sources and the template it makes. -/
structure Transform (V : Type uV) (T : Type uT) (P : Type uP) where
  sources : SourceList V T P
  template : List P

/-! ## Footprints -/

/-- What a row touches: occurrences taken and kept, predicate queries, labels made. -/
@[ext] structure Footprint (O : Type uO) (T : Type uT) where
  takes : Multiset O
  keeps : Multiset O
  queries : Multiset (PredicateQuery O T)
  makes : Multiset T

namespace Footprint

instance : Zero (Footprint O T) := ⟨⟨0, 0, 0, 0⟩⟩

instance : Add (Footprint O T) :=
  ⟨fun a b => ⟨a.takes + b.takes, a.keeps + b.keeps, a.queries + b.queries, a.makes + b.makes⟩⟩

@[simp] theorem takes_zero : (0 : Footprint O T).takes = 0 := rfl
@[simp] theorem keeps_zero : (0 : Footprint O T).keeps = 0 := rfl
@[simp] theorem queries_zero : (0 : Footprint O T).queries = 0 := rfl
@[simp] theorem makes_zero : (0 : Footprint O T).makes = 0 := rfl
@[simp] theorem takes_add (a b : Footprint O T) : (a + b).takes = a.takes + b.takes := rfl
@[simp] theorem keeps_add (a b : Footprint O T) : (a + b).keeps = a.keeps + b.keeps := rfl
@[simp] theorem queries_add (a b : Footprint O T) : (a + b).queries = a.queries + b.queries := rfl
@[simp] theorem makes_add (a b : Footprint O T) : (a + b).makes = a.makes + b.makes := rfl

instance : AddCommMonoid (Footprint O T) where
  add_assoc a b c := by apply Footprint.ext <;> simp [add_assoc]
  zero_add a := by apply Footprint.ext <;> simp
  add_zero a := by apply Footprint.ext <;> simp
  add_comm a b := by apply Footprint.ext <;> simp [add_comm]
  nsmul := nsmulRec

/-- The takes, as a monoid homomorphism. -/
def takesHom : Footprint O T →+ Multiset O := ⟨⟨takes, rfl⟩, fun _ _ => rfl⟩
/-- The keeps, as a monoid homomorphism. -/
def keepsHom : Footprint O T →+ Multiset O := ⟨⟨keeps, rfl⟩, fun _ _ => rfl⟩
/-- The predicate queries, as a monoid homomorphism. -/
def queriesHom : Footprint O T →+ Multiset (PredicateQuery O T) := ⟨⟨queries, rfl⟩, fun _ _ => rfl⟩
/-- The makes, as a monoid homomorphism. -/
def makesHom : Footprint O T →+ Multiset T := ⟨⟨makes, rfl⟩, fun _ _ => rfl⟩

theorem takes_sum (s : Multiset (Footprint O T)) : s.sum.takes = (s.map takes).sum :=
  map_multiset_sum takesHom s
theorem keeps_sum (s : Multiset (Footprint O T)) : s.sum.keeps = (s.map keeps).sum :=
  map_multiset_sum keepsHom s
theorem queries_sum (s : Multiset (Footprint O T)) : s.sum.queries = (s.map queries).sum :=
  map_multiset_sum queriesHom s
theorem makes_sum (s : Multiset (Footprint O T)) : s.sum.makes = (s.map makes).sum :=
  map_multiset_sum makesHom s

theorem takes_listSum (l : List (Footprint O T)) : l.sum.takes = (l.map takes).sum :=
  map_list_sum takesHom l
theorem keeps_listSum (l : List (Footprint O T)) : l.sum.keeps = (l.map keeps).sum :=
  map_list_sum keepsHom l
theorem queries_listSum (l : List (Footprint O T)) : l.sum.queries = (l.map queries).sum :=
  map_list_sum queriesHom l
theorem makes_listSum (l : List (Footprint O T)) : l.sum.makes = (l.map makes).sum :=
  map_list_sum makesHom l

/-- **Linear**: no occurrence taken twice, none both taken and kept. -/
def Linear (fp : Footprint O T) : Prop := fp.takes.Nodup ∧ ∀ o ∈ fp.takes, o ∉ fp.keeps

instance [DecidableEq O] (fp : Footprint O T) : Decidable fp.Linear :=
  inferInstanceAs (Decidable (_ ∧ _))

section Holds

variable [DecidableEq O]

/-- A footprint **holds** at a store: what it takes and keeps is present, its predicate queries
hold. -/
def Holds (label : O → T) (S : Finset O) (fp : Footprint O T) : Prop :=
  (∀ o ∈ fp.takes, o ∈ S) ∧ (∀ o ∈ fp.keeps, o ∈ S) ∧ ∀ r ∈ fp.queries, r.Holds label S

variable {label : O → T} {S : Finset O}

omit [DecidableEq O] in
@[simp] theorem holds_zero : (0 : Footprint O T).Holds label S := by
  simp [Holds]

omit [DecidableEq O] in
theorem holds_add {a b : Footprint O T} : (a + b).Holds label S ↔ a.Holds label S ∧ b.Holds label S := by
  simp only [Holds, takes_add, keeps_add, queries_add, Multiset.mem_add]
  constructor
  · rintro ⟨t, k, r⟩
    exact ⟨⟨fun o h => t o (Or.inl h), fun o h => k o (Or.inl h), fun x h => r x (Or.inl h)⟩,
      ⟨fun o h => t o (Or.inr h), fun o h => k o (Or.inr h), fun x h => r x (Or.inr h)⟩⟩
  · rintro ⟨⟨t, k, r⟩, ⟨t', k', r'⟩⟩
    exact ⟨fun o h => h.elim (t o) (t' o), fun o h => h.elim (k o) (k' o),
      fun x h => h.elim (r x) (r' x)⟩

omit [DecidableEq O] in
theorem holds_sum {s : Multiset (Footprint O T)} :
    s.sum.Holds label S ↔ ∀ fp ∈ s, fp.Holds label S := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih => simp [Multiset.sum_cons, holds_add, ih]

end Holds

end Footprint

/-- What one source picked. -/
inductive Pick (O : Type uO) (T : Type uT) where
  /-- An occurrence kept by a read source. -/
  | keep (o : O)
  /-- An occurrence taken by a take source. -/
  | take (o : O)
  /-- A predicate query; with `consume`, also a take of what it saw. -/
  | query (q : PredicateQuery O T) (consume : Bool)
  /-- The index of a computed value a `let` source used. -/
  | result (index : ℕ)
  /-- The template's labels, instantiated. -/
  | make (labels : Multiset T)
  /-- The amalgamated footprint of an `every` suffix. -/
  | amalgam (footprint : Footprint O T)

namespace Pick

/-- The footprint of one pick. -/
def footprint : Pick O T → Footprint O T
  | keep o => ⟨0, {o}, 0, 0⟩
  | take o => ⟨{o}, 0, 0, 0⟩
  | query r consume => ⟨if consume then r.seen.val else 0, 0, {r}, 0⟩
  | result _ => 0
  | make labels => ⟨0, 0, 0, labels⟩
  | amalgam fp => fp

end Pick

/-- The footprint of a row's picks. -/
def footprintOf (picks : List (Pick O T)) : Footprint O T := (picks.map Pick.footprint).sum

@[simp] theorem footprintOf_nil : footprintOf ([] : List (Pick O T)) = 0 := rfl

theorem footprintOf_cons (pick : Pick O T) (picks : List (Pick O T)) :
    footprintOf (pick :: picks) = pick.footprint + footprintOf picks := by
  simp [footprintOf]

/-! ## Compilation -/

section Compile

variable [DecidableEq O] (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)

/-- The rows of one source from a substitution: the substitution it reaches and its pick. -/
def stepRows : Source V T P → Subst V T → Multiset (Subst V T × Pick O T)
  | .read p, σ => S.val.bind fun o => ((m p σ (label o) : List _) : Multiset _).map fun τ => (τ, .keep o)
  | .take p, σ => S.val.bind fun o => ((m p σ (label o) : List _) : Multiset _).map fun τ => (τ, .take o)
  | .absent p, σ =>
      if regionOf label S (Matcher.region m σ p) = ∅ then
        {(σ, .query ⟨Matcher.region m σ p, ∅⟩ false)}
      else 0
  | .unique access p, σ =>
      if (regionOf label S (Matcher.region m σ p)).card = 1 then
        (regionOf label S (Matcher.region m σ p)).val.bind fun o =>
          ((m p σ (label o) : List _) : Multiset _).map fun τ =>
            (τ, .query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩
              (access = .take))
      else 0
  | .collect access p coll fold, σ =>
      ((m coll σ (fold ((regionOf label S (Matcher.region m σ p)).val.map label)) : List _) :
          Multiset _).map fun τ =>
        (τ, .query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩
          (access = .take))
  | .letBind p eval, σ =>
      (((eval σ).zipIdx 0 : List (T × ℕ)) : Multiset (T × ℕ)).bind fun (x : T × ℕ) =>
        ((m p σ x.1 : List _) : Multiset _).map fun τ => (τ, .result x.2)

/-- The computed regions a source consults, under a substitution. -/
def Source.regions (m : Matcher V T P) : Source V T P → Subst V T → List (T → Bool)
  | .read p, σ => [Matcher.region m σ p]
  | .take p, σ => [Matcher.region m σ p]
  | .absent p, σ => [Matcher.region m σ p]
  | .unique _ p, σ => [Matcher.region m σ p]
  | .collect _ p _ _, σ => [Matcher.region m σ p]
  | .letBind _ _, _ => []

/-- **The completeness regions of a source list**: the computed regions of all its sources, under
the substitution at its start. -/
def complRegions (m : Matcher V T P) : SourceList V T P → Subst V T → List (T → Bool)
  | .done, _ => []
  | .cons s rest, σ => s.regions m σ ++ complRegions m rest σ
  | .absent query rest, σ => complRegions m query σ ++ complRegions m rest σ
  | .every rest, σ => complRegions m rest σ

/-- The completeness queries at a store: each completeness region, with what the store has there. -/
def complQueries (regions : List (T → Bool)) : Footprint O T :=
  ⟨0, 0, ((regions.map fun r => (⟨r, regionOf label S r⟩ : PredicateQuery O T) : List _) : Multiset _), 0⟩

/-- Instantiate a template. -/
def instTemplate (σ : Subst V T) (template : List P) : Option (List T) :=
  template.mapM (L.inst σ)

/-- **The rows of a source list** at a store, from a substitution, through the matcher. -/
def rows (template : List P) : SourceList V T P → Subst V T → Multiset (Subst V T × List (Pick O T))
  | .done, σ =>
      match instTemplate L σ template with
      | some labels => {(σ, [.make (labels : Multiset T)])}
      | none => 0
  | .cons s rest, σ =>
      (stepRows m label S s σ).bind fun x =>
        (rows template rest x.1).map fun y => (y.1, x.2 :: y.2)
  | .absent query rest, σ =>
      if (rows [] query σ).card = 0 then
        (rows template rest σ).map fun y =>
          (y.1, .amalgam (complQueries label S (complRegions m query σ)) :: y.2)
      else 0
  | .every rest, σ =>
      {(σ, [.amalgam
        ((((rows template rest σ).filter fun y => (footprintOf y.2).Linear).map
            fun y => footprintOf y.2).sum +
          complQueries label S (complRegions m rest σ))])}

/-- The rows of a transform: its sources from the empty substitution. -/
def Transform.rows (t : Transform V T P) : Multiset (Subst V T × List (Pick O T)) :=
  Sources.rows L m label S t.template t.sources (fun _ => none)

end Compile

/-! ## Commits of footprints -/

section Commits

variable [DecidableEq O] (label : O → T) (S : Finset O)

/-- A commit **of** a footprint at a store: it takes and keeps the footprint's occurrences, has its
predicate queries, and makes fresh occurrences carrying exactly the footprint's labels. -/
structure IsCommitOf (fp : Footprint O T) (c : Commit O T) : Prop where
  taken : c.taken = fp.takes.toFinset
  kept : c.kept = fp.keeps.toFinset
  queries : ∀ r, r ∈ c.queries ↔ r ∈ fp.queries
  fresh : Disjoint c.made S
  made : labels label c.made = fp.makes

variable {label S}

/-- Fresh occurrences with given labels exist when every label has occurrences outside any finite
set. -/
theorem exists_fresh_labels (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t)
    (labelsWanted : Multiset T) (X : Finset O) :
    ∃ M : Finset O, Disjoint M X ∧ labels label M = labelsWanted := by
  induction labelsWanted using Multiset.induction_on generalizing X with
  | empty => exact ⟨∅, Finset.disjoint_empty_left _, rfl⟩
  | cons t rest ih =>
      obtain ⟨M, apart, same⟩ := ih X
      obtain ⟨o, notIn, labelled⟩ := supply (X ∪ M) t
      refine ⟨insert o M, ?_, ?_⟩
      · rw [Finset.disjoint_insert_left]
        exact ⟨fun inX => notIn (Finset.mem_union_left _ inX), apart⟩
      · have notInM : o ∉ M := fun inM => notIn (Finset.mem_union_right _ inM)
        unfold labels at same ⊢
        rw [Finset.insert_val_of_notMem notInM, Multiset.map_cons, same, labelled]

/-- **A commit of every footprint exists**, given fresh occurrences of every label. -/
theorem exists_isCommitOf (supply : ∀ (X : Finset O) (t : T), ∃ o, o ∉ X ∧ label o = t)
    (fp : Footprint O T) : ∃ c, IsCommitOf label S fp c := by
  obtain ⟨M, apart, same⟩ := exists_fresh_labels supply fp.makes S
  exact ⟨⟨fp.takes.toFinset, fp.keeps.toFinset, M, fp.queries.toList⟩,
    ⟨rfl, rfl, fun r => Multiset.mem_toList, apart, same⟩⟩

/-- A commit of a footprint, enabled at a store, is enabled exactly when the footprint holds there
and what is taken is not kept. -/
theorem IsCommitOf.enabled_iff {fp : Footprint O T} {c : Commit O T} (commit : IsCommitOf label S fp c)
    {S' : Finset O} (fresh : Disjoint c.made S') :
    Enabled label S' c ↔ fp.Holds label S' ∧ ∀ o ∈ fp.takes, o ∉ fp.keeps := by
  constructor
  · intro enabled
    refine ⟨⟨fun o inTakes => ?_, fun o inKeeps => ?_, fun r inQueries => ?_⟩, fun o inTakes inKeeps => ?_⟩
    · exact enabled.taken_subset (by rw [commit.taken]; exact Multiset.mem_toFinset.mpr inTakes)
    · exact enabled.kept_subset (by rw [commit.kept]; exact Multiset.mem_toFinset.mpr inKeeps)
    · exact enabled.queries_hold r ((commit.queries r).mpr inQueries)
    · exact Finset.disjoint_left.mp enabled.apart
        (by rw [commit.taken]; exact Multiset.mem_toFinset.mpr inTakes)
        (by rw [commit.kept]; exact Multiset.mem_toFinset.mpr inKeeps)
  · rintro ⟨⟨takes, keeps, reads⟩, apart⟩
    refine ⟨fun o member => ?_, fun o member => ?_, ?_, fresh, fun r member => ?_⟩
    · rw [commit.taken] at member
      exact takes o (Multiset.mem_toFinset.mp member)
    · rw [commit.kept] at member
      exact keeps o (Multiset.mem_toFinset.mp member)
    · rw [commit.taken, commit.kept]
      exact Finset.disjoint_left.mpr fun o inT inK =>
        apart o (Multiset.mem_toFinset.mp inT) (Multiset.mem_toFinset.mp inK)
    · exact reads r ((commit.queries r).mp member)

end Commits

/-! ## What each pick contributes -/

section Picks

@[simp] theorem footprint_take (o : O) : (Pick.take o : Pick O T).footprint = ⟨{o}, 0, 0, 0⟩ := rfl
@[simp] theorem footprint_keep (o : O) : (Pick.keep o : Pick O T).footprint = ⟨0, {o}, 0, 0⟩ := rfl
@[simp] theorem footprint_query (r : PredicateQuery O T) (consume : Bool) :
    (Pick.query r consume).footprint = ⟨if consume then r.seen.val else 0, 0, {r}, 0⟩ := rfl
@[simp] theorem footprint_result (i : ℕ) : (Pick.result i : Pick O T).footprint = 0 := rfl
@[simp] theorem footprint_make (ts : Multiset T) :
    (Pick.make ts : Pick O T).footprint = ⟨0, 0, 0, ts⟩ := rfl
@[simp] theorem footprint_amalgam (fp : Footprint O T) : (Pick.amalgam fp).footprint = fp := rfl

end Picks

/-! ## Membership in rows -/

section Membership

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

theorem mem_stepRows_read {p : P} {σ : Subst V T} {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.read p) σ ↔ ∃ o ∈ S, ∃ τ ∈ m p σ (label o), x = (τ, .keep o) := by
  simp only [stepRows, Multiset.mem_bind, Finset.mem_val, Multiset.mem_map, Multiset.mem_coe]
  constructor
  · rintro ⟨o, inS, τ, answer, rfl⟩
    exact ⟨o, inS, τ, answer, rfl⟩
  · rintro ⟨o, inS, τ, answer, rfl⟩
    exact ⟨o, inS, τ, answer, rfl⟩

theorem mem_stepRows_take {p : P} {σ : Subst V T} {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.take p) σ ↔ ∃ o ∈ S, ∃ τ ∈ m p σ (label o), x = (τ, .take o) := by
  simp only [stepRows, Multiset.mem_bind, Finset.mem_val, Multiset.mem_map, Multiset.mem_coe]
  constructor
  · rintro ⟨o, inS, τ, answer, rfl⟩
    exact ⟨o, inS, τ, answer, rfl⟩
  · rintro ⟨o, inS, τ, answer, rfl⟩
    exact ⟨o, inS, τ, answer, rfl⟩

theorem mem_stepRows_absent {p : P} {σ : Subst V T} {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.absent p) σ ↔
      regionOf label S (Matcher.region m σ p) = ∅ ∧
        x = (σ, .query ⟨Matcher.region m σ p, ∅⟩ false) := by
  simp only [stepRows]
  split_ifs with empty <;> simp [empty]

theorem mem_stepRows_unique {access : Access} {p : P} {σ : Subst V T} {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.unique access p) σ ↔
      (regionOf label S (Matcher.region m σ p)).card = 1 ∧
        ∃ o ∈ regionOf label S (Matcher.region m σ p), ∃ τ ∈ m p σ (label o),
          x = (τ, .query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩
            (access = .take)) := by
  simp only [stepRows]
  split_ifs with one
  · simp only [Multiset.mem_bind, Finset.mem_val, Multiset.mem_map, Multiset.mem_coe, one, true_and]
    constructor
    · rintro ⟨o, inX, τ, answer, rfl⟩
      exact ⟨o, inX, τ, answer, rfl⟩
    · rintro ⟨o, inX, τ, answer, rfl⟩
      exact ⟨o, inX, τ, answer, rfl⟩
  · simp [one]

theorem mem_stepRows_collect {access : Access} {p coll : P} {fold : Multiset T → T} {σ : Subst V T}
    {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.collect access p coll fold) σ ↔
      ∃ τ ∈ m coll σ (fold ((regionOf label S (Matcher.region m σ p)).val.map label)),
        x = (τ, .query ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩
          (access = .take)) := by
  simp only [stepRows, Multiset.mem_map, Multiset.mem_coe]
  constructor
  · rintro ⟨τ, answer, rfl⟩
    exact ⟨τ, answer, rfl⟩
  · rintro ⟨τ, answer, rfl⟩
    exact ⟨τ, answer, rfl⟩

theorem mem_stepRows_letBind {p : P} {eval : Subst V T → List T} {σ : Subst V T}
    {x : Subst V T × Pick O T} :
    x ∈ stepRows m label S (.letBind p eval) σ ↔
      ∃ i, ∃ value, (eval σ)[i]? = some value ∧ ∃ τ ∈ m p σ value, x = (τ, .result i) := by
  simp only [stepRows, Multiset.mem_bind, Multiset.mem_coe, Multiset.mem_map]
  constructor
  · rintro ⟨⟨value, i⟩, member, τ, answer, rfl⟩
    exact ⟨i, value, List.mem_zipIdx_iff_getElem?.mp member, τ, answer, rfl⟩
  · rintro ⟨i, value, at_i, τ, answer, rfl⟩
    exact ⟨⟨value, i⟩, List.mem_zipIdx_iff_getElem?.mpr at_i, τ, answer, rfl⟩

theorem mem_rows_cons {template : List P} {s : Source V T P} {rest : SourceList V T P}
    {σ : Subst V T} {x : Subst V T × List (Pick O T)} :
    x ∈ rows L m label S template (.cons s rest) σ ↔
      ∃ y ∈ stepRows m label S s σ, ∃ z ∈ rows L m label S template rest y.1,
        x = (z.1, y.2 :: z.2) := by
  simp only [rows, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · rintro ⟨y, inStep, z, inRest, rfl⟩
    exact ⟨y, inStep, z, inRest, rfl⟩
  · rintro ⟨y, inStep, z, inRest, rfl⟩
    exact ⟨y, inStep, z, inRest, rfl⟩

theorem mem_rows_absent {template : List P} {query rest : SourceList V T P}
    {σ : Subst V T} {x : Subst V T × List (Pick O T)} :
    x ∈ rows L m label S template (.absent query rest) σ ↔
      rows L m label S [] query σ = 0 ∧
        ∃ y ∈ rows L m label S template rest σ,
          x = (y.1, .amalgam (complQueries label S (complRegions m query σ)) :: y.2) := by
  simp only [rows]
  split
  · rename_i empty
    simp only [Multiset.card_eq_zero.mp empty, true_and, Multiset.mem_map]
    constructor <;> rintro ⟨y, member, same⟩ <;> exact ⟨y, member, same.symm⟩
  · rename_i nonempty
    have nonzero : rows L m label S [] query σ ≠ 0 := by
      intro empty
      exact nonempty (by rw [empty]; rfl)
    simp only [Multiset.notMem_zero, nonzero, false_and]

/-- The footprint of an `every` row. -/
def everyFootprint (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)
    (template : List P) (rest : SourceList V T P) (σ : Subst V T) : Footprint O T :=
  (((rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear).map
      fun y => footprintOf y.2).sum +
    complQueries label S (complRegions m rest σ)

theorem rows_every {template : List P} {rest : SourceList V T P} {σ : Subst V T} :
    rows L m label S template (.every rest) σ =
      {(σ, [.amalgam (everyFootprint L m label S template rest σ)])} := rfl

/-- **A vacuous `every`**: when the suffix has no row, the `every` footprint takes, keeps and
makes nothing; it only queries its completeness regions. After a taking kernel the commit then
consumes the kernel's occurrences and produces nothing. -/
theorem everyFootprint_vacuous {L : TermLayer V T P} {m : Matcher V T P} {template : List P}
    {rest : SourceList V T P} {σ : Subst V T} (none : rows L m label S template rest σ = 0) :
    (everyFootprint L m label S template rest σ).takes = 0 ∧
      (everyFootprint L m label S template rest σ).keeps = 0 ∧
      (everyFootprint L m label S template rest σ).makes = 0 := by
  unfold everyFootprint
  simp [none, complQueries]

theorem rows_done {template : List P} {σ : Subst V T} :
    rows L m label S template .done σ =
      match instTemplate L σ template with
      | some labels => {(σ, [.make (labels : Multiset T)])}
      | none => 0 := rfl

end Membership

/-! ## What the rows touch is in the store -/

section Holds

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T} {S : Finset O}

omit [DecidableEq O] in
theorem predicateQuery_holds_regionOf (r : T → Bool) :
    (⟨r, regionOf label S r⟩ : PredicateQuery O T).Holds label S := rfl

omit [DecidableEq O] in
theorem complQueries_holds (regions : List (T → Bool)) :
    (complQueries label S regions).Holds label S := by
  refine ⟨by simp [complQueries], by simp [complQueries], fun read member => ?_⟩
  simp only [complQueries, Multiset.mem_coe, List.mem_map] at member
  obtain ⟨r, -, rfl⟩ := member
  exact predicateQuery_holds_regionOf r

/-- What one source's pick touches is in the store. -/
theorem holds_of_mem_stepRows {s : Source V T P} {σ : Subst V T} {x : Subst V T × Pick O T}
    (member : x ∈ stepRows m label S s σ) : x.2.footprint.Holds label S := by
  cases s with
  | read p =>
      obtain ⟨o, inS, τ, -, rfl⟩ := mem_stepRows_read.mp member
      exact ⟨by simp, by simpa using inS, by simp⟩
  | take p =>
      obtain ⟨o, inS, τ, -, rfl⟩ := mem_stepRows_take.mp member
      exact ⟨by simpa using inS, by simp, by simp⟩
  | absent p =>
      obtain ⟨empty, rfl⟩ := mem_stepRows_absent.mp member
      refine ⟨by simp, by simp, ?_⟩
      intro r inQueries
      simp only [footprint_query, Multiset.mem_singleton] at inQueries
      subst inQueries
      exact empty
  | unique access p =>
      obtain ⟨-, o, -, τ, -, rfl⟩ := mem_stepRows_unique.mp member
      refine ⟨?_, by simp, ?_⟩
      · intro o' inTakes
        simp only [footprint_query] at inTakes
        split_ifs at inTakes
        · exact (mem_regionOf.mp (Finset.mem_val.mp inTakes)).1
        · simp at inTakes
      · intro r inQueries
        simp only [footprint_query, Multiset.mem_singleton] at inQueries
        subst inQueries
        exact predicateQuery_holds_regionOf _
  | collect access p coll fold =>
      obtain ⟨τ, -, rfl⟩ := mem_stepRows_collect.mp member
      refine ⟨?_, by simp, ?_⟩
      · intro o' inTakes
        simp only [footprint_query] at inTakes
        split_ifs at inTakes
        · exact (mem_regionOf.mp (Finset.mem_val.mp inTakes)).1
        · simp at inTakes
      · intro r inQueries
        simp only [footprint_query, Multiset.mem_singleton] at inQueries
        subst inQueries
        exact predicateQuery_holds_regionOf _
  | letBind p eval =>
      obtain ⟨i, value, -, τ, -, rfl⟩ := mem_stepRows_letBind.mp member
      exact Footprint.holds_zero

/-- **What every row touches is in the store.** -/
theorem holds_of_mem_rows {template : List P} :
    ∀ {src : SourceList V T P} {σ : Subst V T} {x : Subst V T × List (Pick O T)},
      x ∈ rows L m label S template src σ → (footprintOf x.2).Holds label S
  | .done, σ, x, member => by
      rw [rows_done] at member
      split at member
      · rw [Multiset.mem_singleton] at member
        subst member
        simp [footprintOf_cons, Footprint.Holds]
      · simp at member
  | .cons s rest, σ, x, member => by
      obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
      rw [footprintOf_cons, Footprint.holds_add]
      exact ⟨holds_of_mem_stepRows inStep, holds_of_mem_rows inRest⟩
  | .absent query rest, σ, x, member => by
      obtain ⟨_, y, inRest, rfl⟩ := mem_rows_absent.mp member
      rw [footprintOf_cons, footprint_amalgam, Footprint.holds_add]
      exact ⟨complQueries_holds _, holds_of_mem_rows inRest⟩
  | .every rest, σ, x, member => by
      rw [rows_every, Multiset.mem_singleton] at member
      subst member
      simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero]
      unfold everyFootprint
      rw [Footprint.holds_add, Footprint.holds_sum]
      refine ⟨fun fp inMap => ?_, complQueries_holds _⟩
      obtain ⟨y, inFilter, rfl⟩ := Multiset.mem_map.mp inMap
      exact holds_of_mem_rows (Multiset.mem_of_mem_filter inFilter)

end Holds

/-! ## Firing -/

section Fires

variable [DecidableEq O] (L : TermLayer V T P) (m : Matcher V T P) (label : O → T) (S : Finset O)

/-- **A transform fires a commit** at a store when the commit is of the footprint of one of its
linear rows. -/
def Fires (t : Transform V T P) (c : Commit O T) : Prop :=
  ∃ x ∈ t.rows L m label S, (footprintOf x.2).Linear ∧ IsCommitOf label S (footprintOf x.2) c

variable {L m label S}

/-- **A commit a transform fires is enabled.** -/
theorem Fires.enabled {t : Transform V T P} {c : Commit O T} (fires : Fires L m label S t c) :
    Enabled label S c := by
  obtain ⟨x, member, linear, commit⟩ := fires
  exact (commit.enabled_iff commit.fresh).mpr ⟨holds_of_mem_rows member, linear.2⟩

end Fires

/-! ## Locality and exactness of the footprint -/

section Exactness

variable [DecidableEq O] {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}

/-- Two stores **agree on a region** when they have the same occurrences there. -/
def AgreeOn (label : O → T) (S S' : Finset O) (r : T → Bool) : Prop :=
  regionOf label S r = regionOf label S' r

/-- A list of regions is **dominated** by another: each lies inside one of the other's. -/
def Dominated (rs rs' : List (T → Bool)) : Prop :=
  ∀ r ∈ rs, ∃ r' ∈ rs', ∀ t, r t = true → r' t = true

omit [DecidableEq O] in
theorem AgreeOn.of_sub {S S' : Finset O} {r r' : T → Bool} (agree : AgreeOn label S S' r')
    (sub : ∀ t, r t = true → r' t = true) : AgreeOn label S S' r := by
  unfold AgreeOn at *
  ext o
  constructor
  · intro member
    obtain ⟨inS, inR⟩ := mem_regionOf.mp member
    have : o ∈ regionOf label S r' := mem_regionOf.mpr ⟨inS, sub _ inR⟩
    rw [agree] at this
    exact mem_regionOf.mpr ⟨(mem_regionOf.mp this).1, inR⟩
  · intro member
    obtain ⟨inS', inR⟩ := mem_regionOf.mp member
    have : o ∈ regionOf label S' r' := mem_regionOf.mpr ⟨inS', sub _ inR⟩
    rw [← agree] at this
    exact mem_regionOf.mpr ⟨(mem_regionOf.mp this).1, inR⟩

omit [DecidableEq O] in
/-- A bind over a store that is empty outside a region is a bind over the region. -/
theorem bind_eq_bind_regionOf {β : Type*} {S : Finset O} {r : T → Bool} {f : O → Multiset β}
    (outside : ∀ o, r (label o) = false → f o = 0) :
    S.val.bind f = (regionOf label S r).val.bind f := by
  have split := Multiset.filter_add_not (fun o => r (label o) = true) S.val
  conv_lhs => rw [← split]
  rw [Multiset.add_bind]
  have zero : (Multiset.filter (fun o => ¬ r (label o) = true) S.val).bind f = 0 := by
    rw [Multiset.bind_congr (g := fun _ => 0) fun o member =>
      outside o (by simpa using (Multiset.mem_filter.mp member).2), Multiset.bind_zero]
  rw [zero, add_zero]
  rfl

theorem matcher_eq_nil_of_region {p : P} {σ : Subst V T} {t : T}
    (outside : Matcher.region m σ p t = false) : m p σ t = [] := by
  unfold Matcher.region at outside
  cases h : m p σ t with
  | nil => rfl
  | cons τ rest => simp [h] at outside

/-- **One source reads only its region**: two stores that agree on it give the same rows. -/
theorem stepRows_congr {S S' : Finset O} {s : Source V T P} {σ : Subst V T}
    (agree : ∀ r ∈ s.regions m σ, AgreeOn label S S' r) :
    stepRows m label S s σ = stepRows m label S' s σ := by
  cases s with
  | read p =>
      have a := agree _ (List.mem_singleton_self _)
      simp only [stepRows]
      rw [bind_eq_bind_regionOf (label := label) (r := Matcher.region m σ p) (fun o out => by
          simp [matcher_eq_nil_of_region out]),
        bind_eq_bind_regionOf (label := label) (S := S') (r := Matcher.region m σ p) (fun o out => by
          simp [matcher_eq_nil_of_region out]), a]
  | take p =>
      have a := agree _ (List.mem_singleton_self _)
      simp only [stepRows]
      rw [bind_eq_bind_regionOf (label := label) (r := Matcher.region m σ p) (fun o out => by
          simp [matcher_eq_nil_of_region out]),
        bind_eq_bind_regionOf (label := label) (S := S') (r := Matcher.region m σ p) (fun o out => by
          simp [matcher_eq_nil_of_region out]), a]
  | absent p =>
      have a : regionOf label S (Matcher.region m σ p) = regionOf label S' (Matcher.region m σ p) :=
        agree _ (List.mem_singleton_self _)
      simp only [stepRows, a]
  | unique access p =>
      have a : regionOf label S (Matcher.region m σ p) = regionOf label S' (Matcher.region m σ p) :=
        agree _ (List.mem_singleton_self _)
      simp only [stepRows, a]
  | collect access p coll fold =>
      have a : regionOf label S (Matcher.region m σ p) = regionOf label S' (Matcher.region m σ p) :=
        agree _ (List.mem_singleton_self _)
      simp only [stepRows, a]
  | letBind p eval => rfl

/-- The answers of a sound matcher extend their start. -/
theorem extends_of_mem_stepRows (sound : Matcher.Sound L m) {S : Finset O} {s : Source V T P}
    {σ : Subst V T} {x : Subst V T × Pick O T} (member : x ∈ stepRows m label S s σ) :
    Extends σ x.1 := by
  cases s with
  | read p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_read.mp member
      exact (sound answer).extends_
  | take p =>
      obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_take.mp member
      exact (sound answer).extends_
  | absent p =>
      obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp member
      exact Extends.refl σ
  | unique access p =>
      obtain ⟨-, o, -, τ, answer, rfl⟩ := mem_stepRows_unique.mp member
      exact (sound answer).extends_
  | collect access p coll fold =>
      obtain ⟨τ, answer, rfl⟩ := mem_stepRows_collect.mp member
      exact (sound answer).extends_
  | letBind p eval =>
      obtain ⟨i, value, -, τ, answer, rfl⟩ := mem_stepRows_letBind.mp member
      exact (sound answer).extends_

theorem source_regions_dominated (monotone : Matcher.RegionMonotone m) {s : Source V T P}
    {σ τ : Subst V T} (grows : Extends σ τ) : Dominated (s.regions m τ) (s.regions m σ) := by
  intro r member
  cases s <;> simp only [Source.regions, List.mem_singleton, List.not_mem_nil] at member ⊢ <;>
    subst member <;> exact ⟨_, rfl, fun t inRegion => monotone grows inRegion⟩

/-- **Completeness regions shrink as the substitution grows**, for a matcher whose regions do. -/
theorem complRegions_dominated (monotone : Matcher.RegionMonotone m) :
    ∀ {src : SourceList V T P} {σ τ : Subst V T}, Extends σ τ →
      Dominated (complRegions m src τ) (complRegions m src σ)
  | .done, _, _, _ => fun r member => by simp [complRegions] at member
  | .cons s rest, σ, τ, grows => by
      intro r member
      simp only [complRegions, List.mem_append] at member
      rcases member with inS | inRest
      · obtain ⟨r', member', sub⟩ := source_regions_dominated monotone grows r inS
        exact ⟨r', by simp [complRegions, member'], sub⟩
      · obtain ⟨r', member', sub⟩ := complRegions_dominated monotone (src := rest) grows r inRest
        exact ⟨r', by simp [complRegions, member'], sub⟩
  | .absent query rest, σ, τ, grows => by
      intro r member
      simp only [complRegions, List.mem_append] at member
      rcases member with first | second
      · obtain ⟨r', member', sub⟩ := complRegions_dominated monotone (src := query) grows r first
        exact ⟨r', by simp [complRegions, member'], sub⟩
      · obtain ⟨r', member', sub⟩ := complRegions_dominated monotone (src := rest) grows r second
        exact ⟨r', by simp [complRegions, member'], sub⟩
  | .every rest, σ, τ, grows => complRegions_dominated monotone (src := rest) grows

/-- **Locality**: the rows of a source list depend only on the store's occurrences inside its
completeness regions. -/
theorem rows_congr (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {template : List P} :
    ∀ {src : SourceList V T P} {σ : Subst V T} {S S' : Finset O},
      (∀ r', (∃ r ∈ complRegions m src σ, ∀ t, r' t = true → r t = true) →
        AgreeOn label S S' r') →
      rows L m label S template src σ = rows L m label S' template src σ
  | .done, σ, S, S', _ => rfl
  | .cons s rest, σ, S, S', agree => by
      have stepSame : stepRows m label S s σ = stepRows m label S' s σ :=
        stepRows_congr fun r member =>
          agree r ⟨r, by simp [complRegions, member], fun _ h => h⟩
      simp only [rows]
      rw [stepSame]
      refine Multiset.bind_congr fun y member => ?_
      have restSame : rows L m label S template rest y.1 = rows L m label S' template rest y.1 := by
        refine rows_congr sound monotone fun r' ⟨r, inRest, sub⟩ => agree r' ?_
        obtain ⟨r₀, member₀, sub₀⟩ :=
          complRegions_dominated monotone (extends_of_mem_stepRows sound member) r inRest
        exact ⟨r₀, by simp [complRegions, member₀], fun t h => sub₀ t (sub t h)⟩
      rw [restSame]
  | .absent query rest, σ, S, S', agree => by
      have querySame : rows L m label S [] query σ = rows L m label S' [] query σ :=
        rows_congr sound monotone fun r' ⟨r, member, sub⟩ =>
          agree r' ⟨r, by simp [complRegions, member], sub⟩
      have restSame : rows L m label S template rest σ = rows L m label S' template rest σ :=
        rows_congr sound monotone fun r' ⟨r, member, sub⟩ =>
          agree r' ⟨r, by simp [complRegions, member], sub⟩
      have queryFootprint : complQueries label S (complRegions m query σ) =
          complQueries label S' (complRegions m query σ) := by
        unfold complQueries
        congr 2
        apply List.map_congr_left
        intro r member
        rw [show regionOf label S r = regionOf label S' r from
          agree r ⟨r, by simp [complRegions, member], fun _ h => h⟩]
      simp only [rows, querySame, restSame, queryFootprint]
  | .every rest, σ, S, S', agree => by
      have restSame : rows L m label S template rest σ = rows L m label S' template rest σ :=
        rows_congr sound monotone agree
      have complSame : complQueries label S (complRegions m rest σ) =
          complQueries label S' (complRegions m rest σ) := by
        unfold complQueries
        congr 2
        refine List.map_congr_left fun r member => ?_
        rw [show regionOf label S r = regionOf label S' r from
          agree r ⟨r, member, fun _ h => h⟩]
      rw [rows_every, rows_every]
      unfold everyFootprint
      rw [restSame, complSame]

/-- **One source's footprint is exactly what its row depends on.** -/
theorem mem_stepRows_iff_holds {S S' : Finset O} {s : Source V T P} {σ : Subst V T}
    {x : Subst V T × Pick O T} (member : x ∈ stepRows m label S s σ) :
    x ∈ stepRows m label S' s σ ↔ x.2.footprint.Holds label S' := by
  constructor
  · exact holds_of_mem_stepRows
  · intro holds
    cases s with
    | read p =>
        obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_read.mp member
        exact mem_stepRows_read.mpr ⟨o, holds.2.1 o (by simp), τ, answer, rfl⟩
    | take p =>
        obtain ⟨o, -, τ, answer, rfl⟩ := mem_stepRows_take.mp member
        exact mem_stepRows_take.mpr ⟨o, holds.1 o (by simp), τ, answer, rfl⟩
    | absent p =>
        obtain ⟨-, rfl⟩ := mem_stepRows_absent.mp member
        have empty := holds.2.2 ⟨Matcher.region m σ p, ∅⟩ (by simp)
        exact mem_stepRows_absent.mpr ⟨empty, rfl⟩
    | unique access p =>
        obtain ⟨one, o, inX, τ, answer, rfl⟩ := mem_stepRows_unique.mp member
        have same : regionOf label S' (Matcher.region m σ p) =
            regionOf label S (Matcher.region m σ p) :=
          holds.2.2 ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩ (by simp)
        refine mem_stepRows_unique.mpr ⟨by rw [same]; exact one, o, by rw [same]; exact inX, τ,
          answer, by rw [same]⟩
    | collect access p coll fold =>
        obtain ⟨τ, answer, rfl⟩ := mem_stepRows_collect.mp member
        have same : regionOf label S' (Matcher.region m σ p) =
            regionOf label S (Matcher.region m σ p) :=
          holds.2.2 ⟨Matcher.region m σ p, regionOf label S (Matcher.region m σ p)⟩ (by simp)
        exact mem_stepRows_collect.mpr ⟨τ, by rw [same]; exact answer, by rw [same]⟩
    | letBind p eval => exact member

/-- **Footprint soundness: the footprint is exactly what the row depends on.** A row found at one
store is a row at another store exactly when the footprint holds there. -/
theorem mem_rows_iff_holds (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {template : List P} :
    ∀ {src : SourceList V T P} {σ : Subst V T} {S S' : Finset O} {x : Subst V T × List (Pick O T)},
      x ∈ rows L m label S template src σ →
        (x ∈ rows L m label S' template src σ ↔ (footprintOf x.2).Holds label S')
  | .done, σ, S, S', x, member => by
      constructor
      · exact holds_of_mem_rows
      · intro _
        exact member
  | .cons s rest, σ, S, S', x, member => by
      constructor
      · exact holds_of_mem_rows
      · intro holds
        obtain ⟨y, inStep, z, inRest, rfl⟩ := mem_rows_cons.mp member
        rw [footprintOf_cons, Footprint.holds_add] at holds
        exact mem_rows_cons.mpr ⟨y, (mem_stepRows_iff_holds inStep).mpr holds.1, z,
          (mem_rows_iff_holds sound monotone inRest).mpr holds.2, rfl⟩
  | .absent query rest, σ, S, S', x, member => by
      constructor
      · exact holds_of_mem_rows
      · intro holds
        obtain ⟨empty, y, inRest, rfl⟩ := mem_rows_absent.mp member
        rw [footprintOf_cons, footprint_amalgam, Footprint.holds_add] at holds
        have agree : ∀ r ∈ complRegions m query σ, AgreeOn label S S' r := by
          intro r member
          have observed := holds.1.2.2 ⟨r, regionOf label S r⟩ (by
            simp only [complQueries, Multiset.mem_coe, List.mem_map]
            exact ⟨r, member, rfl⟩)
          exact observed.symm
        have querySame : rows L m label S [] query σ = rows L m label S' [] query σ :=
          rows_congr sound monotone fun r' ⟨r, member, sub⟩ => (agree r member).of_sub sub
        have queryFootprint : complQueries label S (complRegions m query σ) =
            complQueries label S' (complRegions m query σ) := by
          unfold complQueries
          congr 2
          apply List.map_congr_left
          intro r member
          rw [show regionOf label S r = regionOf label S' r from agree r member]
        apply mem_rows_absent.mpr
        exact ⟨by rwa [← querySame], y, (mem_rows_iff_holds sound monotone inRest).mpr holds.2,
          by rw [queryFootprint]⟩
  | .every rest, σ, S, S', x, member => by
      constructor
      · exact holds_of_mem_rows
      · intro holds
        rw [rows_every, Multiset.mem_singleton] at member
        subst member
        simp only [footprintOf_cons, footprint_amalgam, footprintOf_nil, add_zero] at holds
        unfold everyFootprint at holds
        rw [Footprint.holds_add] at holds
        have agree : ∀ r ∈ complRegions m rest σ, AgreeOn label S S' r := by
          intro r member
          have := holds.2.2.2 ⟨r, regionOf label S r⟩ (by
            simp only [complQueries, Multiset.mem_coe, List.mem_map]
            exact ⟨r, member, rfl⟩)
          exact this.symm
        have restSame : rows L m label S template rest σ = rows L m label S' template rest σ :=
          rows_congr sound monotone fun r' ⟨r, member, sub⟩ => (agree r member).of_sub sub
        have complSame : complQueries label S (complRegions m rest σ) =
            complQueries label S' (complRegions m rest σ) := by
          unfold complQueries
          congr 2
          refine List.map_congr_left fun r member => ?_
          rw [show regionOf label S r = regionOf label S' r from agree r member]
        rw [rows_every, Multiset.mem_singleton]
        unfold everyFootprint
        rw [restSame, complSame]

/-- **Validating a compiled commit is re-running the match.** For a commit of a linear row found at
one store, enabling at another store (where what it makes is fresh) is exactly being a row of the
transform there. -/
theorem enabled_iff_mem_rows (sound : Matcher.Sound L m) (monotone : Matcher.RegionMonotone m)
    {t : Transform V T P} {S S' : Finset O} {x : Subst V T × List (Pick O T)}
    (member : x ∈ t.rows L m label S) (linear : (footprintOf x.2).Linear) {c : Commit O T}
    (commit : IsCommitOf label S (footprintOf x.2) c) (fresh : Disjoint c.made S') :
    Enabled label S' c ↔ x ∈ t.rows L m label S' := by
  rw [commit.enabled_iff fresh, Transform.rows, mem_rows_iff_holds sound monotone member]
  exact ⟨fun h => h.1, fun h => ⟨h, linear.2⟩⟩

end Exactness

/-! ## `every` is the amalgamation of its rows -/

section Every

variable [DecidableEq O] {label : O → T} {S : Finset O}

/-- An element of the right list of a `Forall₂` has a partner on the left. -/
theorem exists_of_forall₂_mem_right {α β : Type*} {rel : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (pairs : List.Forall₂ rel l₁ l₂) {b : β} (member : b ∈ l₂) : ∃ a ∈ l₁, rel a b := by
  induction pairs with
  | nil => simp at member
  | @cons a b' l₁ l₂ head _ ih =>
      rcases List.mem_cons.mp member with rfl | inRest
      · exact ⟨a, List.mem_cons_self, head⟩
      · obtain ⟨a', inL, related⟩ := ih inRest
        exact ⟨a', List.mem_cons_of_mem _ inL, related⟩

theorem takenOf_eq_of_forall₂ {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs) : takenOf cs = fps.sum.takes.toFinset := by
  induction commits with
  | nil => simp [takenOf]
  | cons head _ ih => simp [takenOf, ih, head.taken, Multiset.toFinset_add]

theorem keptOf_eq_of_forall₂ {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs) : keptOf cs = fps.sum.keeps.toFinset := by
  induction commits with
  | nil => simp [keptOf]
  | cons head _ ih => simp [keptOf, ih, head.kept, Multiset.toFinset_add]

theorem mem_queriesOf_iff_of_forall₂ {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs) (r : PredicateQuery O T) :
    r ∈ queriesOf cs ↔ r ∈ fps.sum.queries := by
  induction commits with
  | nil => simp [queriesOf]
  | @cons fp c fps cs head _ ih =>
      have split : queriesOf (c :: cs) = c.queries ++ queriesOf cs := by simp [queriesOf]
      rw [split, List.mem_append, ih, head.queries r]
      simp

theorem madeOf_fresh_of_forall₂ {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs) : Disjoint (madeOf cs) S := by
  induction commits with
  | nil => simp [madeOf]
  | cons head _ ih => exact Finset.disjoint_union_left.mpr ⟨head.fresh, ih⟩

theorem labels_madeOf_of_forall₂ {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs)
    (apart : cs.Pairwise fun c d => Disjoint c.made d.made) :
    labels label (madeOf cs) = fps.sum.makes := by
  induction commits with
  | nil => simp [madeOf, labels]
  | @cons fp c fps cs head _ ih =>
      have apartHead := (List.pairwise_cons.mp apart).1
      have disjoint : Disjoint c.made (madeOf cs) := by
        refine Finset.disjoint_left.mpr fun o inC inRest => ?_
        obtain ⟨d, inCs, inD⟩ := mem_madeOf.mp inRest
        exact Finset.disjoint_left.mp (apartHead d inCs) inC inD
      have : madeOf (c :: cs) = c.made ∪ madeOf cs := rfl
      rw [this, labels_union_of_disjoint label disjoint, head.made,
        ih (List.pairwise_cons.mp apart).2]
      simp

/-- **The commit of an `every` row is the amalgamation of its rows' commits, with the completeness
queries.** For commits of the rows' footprints whose made occurrences are pairwise apart, the
commit `⟨takenOf cs, keptOf cs, madeOf cs, compl ++ queriesOf cs⟩` is a commit of the sum of the
footprints and the completeness queries. -/
theorem isCommitOf_every {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs)
    (apart : cs.Pairwise fun c d => Disjoint c.made d.made) (compl : List (PredicateQuery O T)) :
    IsCommitOf label S (fps.sum + ⟨0, 0, (compl : Multiset _), 0⟩)
      ⟨takenOf cs, keptOf cs, madeOf cs, compl ++ queriesOf cs⟩ := by
  refine ⟨?_, ?_, fun r => ?_, madeOf_fresh_of_forall₂ commits, ?_⟩
  · simp [takenOf_eq_of_forall₂ commits]
  · simp [keptOf_eq_of_forall₂ commits]
  · simp only [List.mem_append, mem_queriesOf_iff_of_forall₂ commits, Footprint.queries_add,
      Multiset.mem_add, Multiset.mem_coe]
    exact Or.comm
  · simp [labels_madeOf_of_forall₂ commits apart]

omit [DecidableEq O] in
theorem takes_le_sum_of_mem {fps : List (Footprint O T)} {b : Footprint O T} (member : b ∈ fps) :
    b.takes ≤ fps.sum.takes := by
  induction fps with
  | nil => simp at member
  | cons a rest ih =>
      rcases List.mem_cons.mp member with rfl | inRest
      · simp
      · simpa using (ih inRest).trans (Multiset.le_add_left _ _)

omit [DecidableEq O] in
/-- A linear sum of footprints takes pairwise disjoint occurrences. -/
theorem takes_disjoint_of_linear_sum {fps : List (Footprint O T)} (linear : fps.sum.Linear) :
    fps.Pairwise fun a b => ∀ o ∈ a.takes, o ∉ b.takes := by
  induction fps with
  | nil => exact List.Pairwise.nil
  | cons a rest ih =>
      have nodup : (a.takes + rest.sum.takes).Nodup := by simpa using linear.1
      refine List.pairwise_cons.mpr ⟨fun b inRest o inA inB => ?_, ih ⟨?_, fun o h k => ?_⟩⟩
      · have inRestTakes : o ∈ rest.sum.takes := Multiset.mem_of_le (takes_le_sum_of_mem inRest) inB
        exact Multiset.disjoint_left.mp (Multiset.nodup_add.mp nodup).2.2 inA inRestTakes
      · exact (Multiset.nodup_add.mp nodup).2.1
      · exact linear.2 o (by simp [h]) (by simp [k])

omit [DecidableEq O] in
/-- Two footprints of a bag that take one occurrence make the bag's sum non-linear. -/
theorem not_linear_of_shared_take {s : Multiset (Footprint O T)} {a b : Footprint O T}
    (sub : a ::ₘ {b} ≤ s) {o : O} (inA : o ∈ a.takes) (inB : o ∈ b.takes) : ¬ s.sum.Linear := by
  intro linear
  obtain ⟨rest, rfl⟩ := Multiset.le_iff_exists_add.mp sub
  have nodup : (a.takes + (b.takes + rest.sum.takes)).Nodup := by
    simpa [Multiset.sum_cons, add_assoc] using linear.1
  exact Multiset.disjoint_left.mp (Multiset.nodup_add.mp nodup).2.2 inA
    (Multiset.mem_add.mpr (Or.inl inB))

/-- **`every` refuses rows that take one occurrence**, as the multiset `every` does
(`TransformQuantifiers.Controls.every_disabled_by_conflict`): when two rows of the suffix that are
linear on their own take a common occurrence, the `every` footprint is not linear, so the
transform fires no commit from it. The two rows may be equal as values and occur twice. -/
theorem everyFootprint_not_linear_of_shared_take {L : TermLayer V T P} {m : Matcher V T P}
    {template : List P} {rest : SourceList V T P} {σ : Subst V T}
    {y₁ y₂ : Subst V T × List (Pick O T)}
    (sub : y₁ ::ₘ {y₂} ≤ (rows L m label S template rest σ).filter fun y => (footprintOf y.2).Linear)
    {o : O} (in₁ : o ∈ (footprintOf y₁.2).takes) (in₂ : o ∈ (footprintOf y₂.2).takes) :
    ¬ (everyFootprint L m label S template rest σ).Linear := by
  intro linear
  have subMap := Multiset.map_le_map (f := fun y : Subst V T × List (Pick O T) => footprintOf y.2) sub
  simp only [Multiset.map_cons, Multiset.map_singleton] at subMap
  refine not_linear_of_shared_take subMap in₁ in₂ ⟨?_, fun o' h k => linear.2 o' ?_ ?_⟩
  · have := linear.1
    unfold everyFootprint at this
    simpa [complQueries] using this
  · unfold everyFootprint
    simpa [complQueries] using h
  · unfold everyFootprint
    simpa [complQueries] using k

/-- **The rows of a linear `every` do not clash**: their commits take pairwise disjoint
occurrences, and their made occurrences are apart by construction. -/
theorem noClash_of_linear_sum {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs)
    (apart : cs.Pairwise fun c d => Disjoint c.made d.made) (linear : fps.sum.Linear) :
    cs.Pairwise fun c d => ¬ Clash c d := by
  have takesApart := takes_disjoint_of_linear_sum linear
  induction commits with
  | nil => exact List.Pairwise.nil
  | @cons fp c fps cs head tail ih =>
      have apartTail := (List.pairwise_cons.mp apart).2
      have apartHead := (List.pairwise_cons.mp apart).1
      have takesTail := (List.pairwise_cons.mp takesApart).2
      have takesHead := (List.pairwise_cons.mp takesApart).1
      have linearTail : fps.sum.Linear := by
        have nodup : (fp.takes + fps.sum.takes).Nodup := by simpa using linear.1
        exact ⟨(Multiset.nodup_add.mp nodup).2.1,
          fun o h k => linear.2 o (by simp [h]) (by simp [k])⟩
      refine List.pairwise_cons.mpr ⟨fun d inCs => ?_, ih apartTail linearTail takesTail⟩
      obtain ⟨fpD, inFps, commitD⟩ := exists_of_forall₂_mem_right tail inCs
      rintro (takenClash | madeClash)
      · obtain ⟨o, inC, inD⟩ := Finset.not_disjoint_iff.mp takenClash
        rw [head.taken] at inC
        rw [commitD.taken] at inD
        exact takesHead fpD inFps o (Multiset.mem_toFinset.mp inC) (Multiset.mem_toFinset.mp inD)
      · exact madeClash (apartHead d inCs)

/-- **`every` agrees with a serialization of its rows exactly when their precedence relation is
acyclic.** The rows' commits are enabled at the store and a linear `every` makes them clash-free,
so `Waves.every_serializable_iff` applies to them. -/
theorem every_commit_serializable_iff {fps : List (Footprint O T)} {cs : List (Commit O T)}
    (commits : List.Forall₂ (IsCommitOf label S) fps cs)
    (apart : cs.Pairwise fun c d => Disjoint c.made d.made) (linear : fps.sum.Linear)
    (enabled : ∀ c ∈ cs, Enabled label S c) :
    (∃ l, l.Perm cs ∧ Executable label S l ∧ fireList S l = fire S (amalgamate cs)) ↔
      Acyclic label cs :=
  every_serializable_iff enabled (noClash_of_linear_sum commits apart linear)

end Every

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
