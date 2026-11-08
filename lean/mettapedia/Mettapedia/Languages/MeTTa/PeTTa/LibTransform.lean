import Mettapedia.Languages.ProcessCalculi.MORK.MatchSpec
import Mettapedia.Languages.MeTTa.PeTTa.Answers
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.Multiset.Filter

/-!
# The laws of PeTTa's transform library

CeTTa's PeTTa library `lib_transform_specs` specifies one operation over a space,
`(transform SPACE SOURCES TEMPLATE [DESTINATION])`; `lib_transform` computes the same
answers and leaves the same store. This module is a first-order model of that
specification and proves the laws it promises.

## The model

* A store is a list of atoms (`Store`): the order is the order in which `match` meets
  them, and its multiset is what validation counts.
* Patterns are `OSLFCore.Atom`s with variables, matched one way by the shared structural
  matcher `MORK.matchAtom`, which threads a substitution: a variable that is already bound
  tests its value (`matchesIn`).
* A conjunct reads or takes a match (`Conj.pat`), or is a condition over a query
  (`Query`): one pattern `p`, or a pattern `(, p1 ... pn)` headed by `,`, which the
  library reads as a conjunction. The joint matches of a query (`jointIn`) are a match of
  `p1`, then a match of `p2` under its bindings, and so on, in that nested order and with
  every copy: the matches `match` gives on the conjunction (`jointIn_fst`). Each has a
  tuple, the atoms matched in part order, and one stored occurrence may be met at several
  parts. A condition requires that there be no joint match (`Conj.absent`), exactly one
  (`Conj.unique`), or collects them as one expression matched against `C`
  (`Conj.collect`): the list of the matched atoms for one pattern, of the tuples
  `(, a1 ... an)` for a conjunction (`Query.collection`). `Conj.as` is the library's
  `(tf:as P A)`, which binds a pattern against an atom; the library writes it into a
  branch's sources. `Sources` holds the conjuncts flattened in order, in three segments:
  the kernel, before the first `all` or `once`; the conjuncts from a `(once c)` on, which
  each firing searches for the first candidate that validates; and the conjuncts from the
  first `all` on, all of whose extensions fire in that commit. `(, k (all e1) e2)` is
  `⟨[k], [], some [e1, e2]⟩` and `(, k (once e))` is `⟨[k], [e], none⟩`; a `once` after the
  first `all` is part of that extension.
* `walk` gives the rows of a conjunction as the library does: one row per match in match
  order, duplicates included, each with its final bindings and its footprint, the read and
  taken atoms in conjunct order. Proposing records the atoms of reads and takes, and the
  parts of each `unique` tuple in order with the conjunct's access mode; firing also takes
  what a take-mode `collect` collects. For one pattern that is each collected atom, as
  matched. Over a conjunction a take-mode `collect` keeps only the tuples that fit (`fits`:
  no atom occurs in the tuple more often than it is stored; order kept), and takes every
  stored copy of each participating atom (`participants`: the distinct atoms of the kept
  tuples, in order of first appearance, each with its stored multiplicity).
* A proposal is the guide of one kernel match against the store at the call: the atoms its
  reads, takes and `unique` conjuncts matched (`proposals`). A branch fires its guided
  kernel (`guided`) from the empty substitution: each read or take of `P` that matched `A`
  is that access of exactly `A` followed by `(tf:as P A)`; each `unique` is evaluated again
  and followed by `(tf:as P A)` for each of its parts `P` and the atom `A` its proposal
  matched with it (`asParts`; the library's one `(tf:as (, p1 ... pn) (, a1 ... an))` is
  the same, `walk_as_tuple`); and each `absent` and `collect` is evaluated again, with its
  own variables free. The firing commits the first candidate whose footprint validates
  (`valid`, the library's count), removing every copy of each taken atom and storing back
  the copies the firing does not take (`commit`).
* The instances of a row are the template under its bindings, split by the template's own
  syntax (`instances`): a template `(, t1 ... tn)` gives its `n` parts, and a value bound to
  a comma expression is one instance.
* Execution is sequential search over a global store (`Trace`, `Search`): each answer is
  produced at a store, and the search resumes from the store the consumer leaves. The
  transform is written in it as the library writes it (`transformWith`): the proposals,
  `superpose`, one firing per branch, then the route. `once` keeps the first answer.

Modelled: one space; `absent`, `unique` and `collect` over one pattern and over a
conjunction; the caller route (`toCaller`), whose instances are observed as data, since the
evaluation of an instance is common to `transform` and `match`; and a destination space that
is the source store itself (`intoStore`), the case in which routing changes what later
branches see. Not modelled: `let` conjuncts (evaluated code), named spaces `[S]`, and
destinations that are functions or other spaces. A condition's pattern headed by `,` is
written `Query.conj` of its parts, and `Query.one p` stands for a pattern `p` not headed by
`,`. A read or take of a pattern headed by `,` is written as one access per part, as the
library splices it into the conjunction it sits in; an access pattern or a stored atom
headed by `,` is otherwise matched structurally, as data. Stored copies are counted by
equality, in `fits` as in validation, which is the library's count on a ground store; the
laws that need it assume a ground store, as the library's access of an atom `A` re-matches
`A` as a pattern.

## The laws

1. Reads alone (`transform_reads`, `transform_reads_eq_match`): on a ground store the
   answers are the instances under the matches of `match` on the same pattern conjunction,
   duplicates and order included, and exactly the answers of `match` when the template is
   not a `,` conjunction; the store is unchanged.
2. Atomicity (`valid_iff_le`, `commit_coe`, `commit_add_takes`, `fire_eq_some_iff`,
   `fire_conserves`, `firing_atomic`): one firing either leaves the store as it is, or
   moves in one step to a store whose multiset is the old one minus exactly the footprint's
   takes; it fires only when that footprint validates against the store at that moment, and
   it commits the first candidate that does. These hold for all sources, joint conditions
   included; for the joint takes (`transform_unique_take`,
   `fire_collect_take_joint_conserves`) the store left, plus exactly the `unique` tuple or
   the stored copies of the participating atoms, is the store found.
3. Branches (`transformWith_drain`, `fire_isSome_iff`, `fire_eq_none_of_gone`): running
   the branches is the fold of single firings; a branch fires iff some candidate of its
   guided sources validates in the store it finds; a branch an atom of whose guide is gone,
   a part of a joint `unique` tuple included, fires nothing.
4. `once` (`once_transformWith`, `once_transformWith_none`, `once_transformInto`,
   `once_transform`): the first proposal that holds at the call fires, and `once` answers
   at the store of that single firing, provided the firing answers. Into a space every
   firing answers; to the caller a firing with no instance does not, and `once` then goes on
   to the next branch.
5. `all` and `collect` takes (`fire_all_take`, `fire_collect_take`, `transform_all_take`,
   `transform_collect_take`): one firing takes every match present and leaves exactly the
   store without them, in order; `collect` binds its variable to their list.
6. Joint conditions. `absent` holds iff `match` on the conjunction answers nothing
   (`walk_absent`, `fire_absent`, `transform_absent`). `unique` proposes iff there is
   exactly one joint tuple, with its parts as the guide (`proposals_unique`); its branch fires
   iff the store it finds has exactly one tuple, that tuple is the guide's, and the parts'
   footprint validates (`fire_unique_joint`, `transform_unique`). Takes need distinct
   occurrences: taking a tuple validates iff it fits (`valid_map_take`); reads may meet one
   occurrence at several parts (`valid_map_read`). A read-mode `collect` binds the list of
   every joint tuple at firing (`fire_collect_read_joint`). A take-mode `collect` over a
   conjunction keeps exactly the tuples that fit, in order (`collected_take_conj`,
   `mem_collected_take_conj`), takes as a multiset every stored copy of each atom of a kept
   tuple and nothing else (`takes_collect_conj`), and leaves exactly the store without those
   atoms (`fire_collect_take_joint`, `transform_collect_take_joint`).
7. One pattern and the one-part conjunction. A one-pattern query has the clauses of the
   single-pattern conditions (`walk_absent_one`, `walk_unique_one`, `walk_collect_one`,
   `guided_unique_one`, `jointIn_one`). `(, p)` is `p` for `absent` and `unique`
   (`walk_absent_conj_single`, `walk_unique_conj_single`, `proposals_conj_single`,
   `candidates_conj_single`); for `collect` it keeps the same matches
   (`collected_conj_single`) and binds the list of the one-part tuples `(, a)` where `p`
   binds the atoms, and in take mode leaves the store `p` leaves
   (`fire_collect_take_conj_single`).

A branch's conditions are those of the store when it fires: `unique` counts its pattern
again and must find the proposal's atom (`fire_unique`, and `fire_unique_joint` for a
tuple), and `collect` binds its variable to the list at firing (`fire_collect_read`,
`fire_collect_read_joint`). The source-level `(once c)` commits only the first match that
validates (`fire_once_take`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.LibTransform

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
  (Subst matchAtom applySubst isGroundAtom MatchAtomRel matchAtom_complete matchAtom_sound
    matchAtom_lookupExtends)

/-! ## Sequential search over a global store -/

/-- The run of a computation under sequential search over a global store. `answer v s k`
produces `v` when the store is `s`; asked for the next answer, the search resumes `k` from
the store the consumer leaves. Effects are not undone when the search backtracks. -/
inductive Trace (S α : Type) where
  | done (final : S)
  | answer (value : α) (now : S) (resume : S → Trace S α)

namespace Trace

variable {S α β : Type}

/-- Run `t`, then continue with `k` from the store `t` ends in. -/
def append : Trace S α → (S → Trace S α) → Trace S α
  | done s, k => k s
  | answer a s r, k => answer a s fun s' => (r s').append k

/-- Run the continuation on every answer, from the store at which it is produced. -/
def bind : Trace S α → (α → S → Trace S β) → Trace S β
  | done s, _ => done s
  | answer a s r, f => (f a s).append fun s' => (r s').bind f

/-- Every answer and the final store, for a consumer that leaves the store as it is. -/
def drain : Trace S α → List α × S
  | done s => ([], s)
  | answer a s r => (a :: ((r s).drain).1, ((r s).drain).2)

@[simp] theorem drain_done (s : S) : (done s : Trace S α).drain = ([], s) := rfl

@[simp] theorem drain_answer (a : α) (s : S) (r : S → Trace S α) :
    (answer a s r).drain = (a :: ((r s).drain).1, ((r s).drain).2) := rfl

/-- The first answer, with the store at which it is produced. -/
def first? : Trace S α → Option (α × S)
  | done _ => none
  | answer a s _ => some (a, s)

theorem drain_append (t : Trace S α) (k : S → Trace S α) :
    (t.append k).drain = (t.drain.1 ++ (k t.drain.2).drain.1, (k t.drain.2).drain.2) := by
  induction t with
  | done s => simp [append]
  | answer a s r ih => simp [append, ih]

end Trace

/-- A computation over a global store of type `S`. -/
abbrev Search (S α : Type) := S → Trace S α

namespace Search

variable {S α β : Type}

/-- Sequential composition: the continuation runs on each answer in turn. -/
def bind (m : Search S α) (f : α → Search S β) : Search S β := fun s => (m s).bind f

/-- The given values as answers, in order, without touching the store. -/
def superpose : List α → Search S α
  | [] => Trace.done
  | a :: as => fun s => .answer a s (superpose as)

/-- The first answer, with the store at which it is produced; nothing after it. -/
def once (m : Search S α) : Search S α := fun s =>
  match m s with
  | .done s' => .done s'
  | .answer a s' _ => .answer a s' .done

/-- `once` keeps the first answer and its store. -/
@[simp] theorem first?_once (m : Search S α) (s : S) : (once m s).first? = (m s).first? := by
  unfold once
  split <;> rename_i h <;> simp [h, Trace.first?]

@[simp] theorem drain_superpose (xs : List α) (s : S) :
    (superpose xs s).drain = (xs, s) := by
  induction xs with
  | nil => rfl
  | cons a as ih => simp [superpose, ih]

/-- One step of the fold of `bind (superpose xs) f`: run `f` on the next value from the
current store and keep its answers. -/
def foldStep (f : α → Search S β) (acc : List β × S) (a : α) : List β × S :=
  (acc.1 ++ ((f a acc.2).drain).1, ((f a acc.2).drain).2)

theorem foldl_foldStep (f : α → Search S β) (xs : List α) (acc : List β) (s : S) :
    xs.foldl (foldStep f) (acc, s) =
      (acc ++ (((superpose xs).bind f s).drain).1, (((superpose xs).bind f s).drain).2) := by
  induction xs generalizing acc s with
  | nil => simp [superpose, bind, Trace.bind]
  | cons a as ih =>
      simp only [List.foldl_cons, foldStep, ih]
      simp [superpose, bind, Trace.bind, Trace.drain_append]

/-- **Sequential search over values is a fold.** Every branch runs to completion from the
store the previous branch left. -/
theorem drain_bind_superpose (f : α → Search S β) (xs : List α) (s : S) :
    ((superpose xs).bind f s).drain = xs.foldl (foldStep f) ([], s) := by
  rw [foldl_foldStep]
  simp

end Search

/-! ## Sources -/

/-- Whether a conjunct reads its atom or consumes it. -/
inductive Mode where
  | read
  | take
  deriving DecidableEq, Repr

/-- What `absent`, `unique` and `collect` range over: one pattern `p`, or a pattern
`(, p1 ... pn)` headed by `,`, which they read as a query over its joint matches. -/
inductive Query where
  | one (pattern : Atom)
  | conj (parts : List Atom)
  deriving Repr

/-- The patterns a query matches jointly, in order. -/
def Query.parts : Query → List Atom
  | .one p => [p]
  | .conj ps => ps

/-- One conjunct of a transform's sources, or of a branch's guided sources. -/
inductive Conj where
  /-- `p`, `(read p)` or `(take p)`: one row per stored atom matching `p`. -/
  | pat (mode : Mode) (pattern : Atom)
  /-- `(absent q)`: the query has no joint match. -/
  | absent (query : Query)
  /-- `(unique c)`: the query has exactly one joint match. -/
  | unique (mode : Mode) (query : Query)
  /-- `(collect c C)`: the joint matches, collected as one expression and matched against
  `C`; in take mode their atoms are taken. -/
  | collect (mode : Mode) (query : Query) (collection : Atom)
  /-- `(tf:as P A)`: the pattern `P` matched against the atom `A` under the bindings so
  far. The library writes it into a branch's sources. -/
  | as (pattern atom : Atom)
  deriving Repr

/-- The sources of a transform, flattened in order. The kernel is the conjuncts before the
first `all` or `once`. `choice` holds the conjuncts from a `(once c)` on, up to the first
`all`: they are plain conjuncts of each branch's one firing, which commits the first of their
matches that validates. `every` holds the conjuncts from the first `all` on, whose matches
all fire in that commit (`none` when there is no `all`). A `once` after the first `all` is
part of that extension, as in the library. -/
structure Sources where
  kernel : List Conj
  choice : List Conj := []
  every : Option (List Conj) := none

/-- A store: its atoms in the order `match` meets them. -/
abbrev Store := List Atom

/-- The read and taken atoms of a row, in conjunct order. -/
abbrev Footprint := List (Mode × Atom)

/-! ## Rows -/

/-- The stored atoms matching `p` under `σ`, each with the extended bindings, in store
order and with every copy. -/
def matchesIn (s : Store) (σ : Subst) (p : Atom) : List (Subst × Atom) :=
  s.filterMap fun b => (matchAtom σ p b).map fun τ => (τ, b)

theorem mem_matchesIn {s : Store} {σ : Subst} {p : Atom} {r : Subst × Atom} :
    r ∈ matchesIn s σ p ↔ r.2 ∈ s ∧ matchAtom σ p r.2 = some r.1 := by
  obtain ⟨τ, b⟩ := r
  simp only [matchesIn, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨b', member, τ', matched, rfl, rfl⟩
    exact ⟨member, matched⟩
  · rintro ⟨member, matched⟩
    exact ⟨b, member, τ, matched, rfl, rfl⟩

/-- The joint matches of the patterns `ps` under `σ`, as `match` reads the conjunction
`(, p1 ... pn)`: a match of `p1`, then a match of `p2` under its bindings, and so on, in that
nested order and with every copy. Each is its final bindings and its tuple, the atoms matched
in part order; one stored occurrence may be met at several parts. -/
def jointIn (s : Store) : Subst → List Atom → List (Subst × List Atom)
  | σ, [] => [(σ, [])]
  | σ, p :: ps =>
      (matchesIn s σ p).flatMap fun r => (jointIn s r.1 ps).map fun t => (t.1, r.2 :: t.2)

/-- A tuple fits the store when no atom occurs in it more often than it is stored (counted
as validation counts), so that its parts can be distinct stored occurrences. -/
def fits (s : Store) (t : List Atom) : Bool :=
  t.all fun a => decide (t.count a ≤ s.count a)

/-- The joint matches a `collect` of `q` collects: all of them, except that a take-mode
`collect` over a conjunction keeps only the tuples that fit, in order. -/
def collected (s : Store) (σ : Subst) (m : Mode) : Query → List (Subst × List Atom)
  | .one p => jointIn s σ [p]
  | .conj ps =>
      match m with
      | .read => jointIn s σ ps
      | .take => (jointIn s σ ps).filter fun t => fits s t.2

/-- The value a `collect` of `q` binds, from its tuples: the list of the matched atoms for
one pattern, and the list of the tuples `(, a1 ... an)` for a conjunction. -/
def Query.collection : Query → List (List Atom) → Atom
  | .one _, ts => .expression ts.flatten
  | .conj _, ts => .expression (ts.map fun t => .expression (.symbol "," :: t))

/-- The atoms that take part in some tuple: the distinct atoms of the tuples, in order of
first appearance. -/
def participants (ts : List (List Atom)) : List Atom := ts.flatten.eraseDups

/-- What a take-mode `collect` of `q` takes when it fires, from its tuples: for one pattern
every collected atom, as matched; over a conjunction every stored copy of each participating
atom. When proposing, and in read mode, it takes nothing. -/
def collectTakes (s : Store) (firing : Bool) (m : Mode) (q : Query) (ts : List (List Atom)) :
    Footprint :=
  match firing, m, q with
  | true, .take, .one _ => ts.flatten.map fun a => (Mode.take, a)
  | true, .take, .conj _ =>
      (participants ts).flatMap fun a => List.replicate (s.count a) (Mode.take, a)
  | _, _, _ => []

/-- The rows of `cs` under the bindings `σ`, each with its final bindings and footprint,
in match order. `firing` is false when proposing at the call and true when a branch fires. -/
def walk (s : Store) (firing : Bool) : Subst → List Conj → List (Subst × Footprint)
  | σ, [] => [(σ, [])]
  | σ, .pat m p :: cs =>
      (matchesIn s σ p).flatMap fun r =>
        (walk s firing r.1 cs).map fun w => (w.1, (m, r.2) :: w.2)
  | σ, .absent q :: cs => if jointIn s σ q.parts = [] then walk s firing σ cs else []
  | σ, .unique m q :: cs =>
      match jointIn s σ q.parts with
      | [t] => (walk s firing t.1 cs).map fun w => (w.1, t.2.map (fun a => (m, a)) ++ w.2)
      | _ => []
  | σ, .collect m q c :: cs =>
      match matchAtom σ c (q.collection ((collected s σ m q).map Prod.snd)) with
      | none => []
      | some τ =>
          (walk s firing τ cs).map fun w =>
            (w.1, collectTakes s firing m q ((collected s σ m q).map Prod.snd) ++ w.2)
  | σ, .as p a :: cs =>
      match matchAtom σ p a with
      | none => []
      | some τ => walk s firing τ cs

/-! ## Validation and the commit -/

/-- The atoms a footprint takes, with multiplicity, in order. -/
def takes (fp : Footprint) : List Atom :=
  fp.filterMap fun e => match e.1 with
    | .take => some e.2
    | .read => none

/-- The atoms a footprint reads. -/
def reads (fp : Footprint) : List Atom :=
  fp.filterMap fun e => match e.1 with
    | .read => some e.2
    | .take => none

/-- The library's validation: each taken atom is stored with at least the multiplicity the
firing takes, plus one more copy when the firing also reads it. -/
def valid (s : Store) (fp : Footprint) : Bool :=
  fp.all fun e => match e.1 with
    | .read => true
    | .take =>
        decide (fp.count (.take, e.2) + (if 0 < fp.count (.read, e.2) then 1 else 0) ≤
          s.count e.2)

/-- `remove-atom` removes every copy of `a`; then `n` of them stay taken and the rest are
stored back at the end. -/
def commitOne (s : Store) (a : Atom) (n : Nat) : Store :=
  s.filter (fun b => b != a) ++ List.replicate (s.count a - n) a

/-- The library's commit: each distinct taken atom, in footprint order. -/
def applyTakes (all : Footprint) : Footprint → List Atom → Store → Store
  | [], _, s => s
  | (m, a) :: more, done, s =>
      if m = .take ∧ a ∉ done then
        applyTakes all more (a :: done) (commitOne s a (all.count (.take, a)))
      else applyTakes all more done s

/-- Commit a footprint. -/
def commit (fp : Footprint) (s : Store) : Store := applyTakes fp fp [] s

/-! ## Branches and firing -/

/-- The proposals: for each match of the kernel against the store at the call, in match
order, its guide, the atoms its reads, takes and `unique` conjuncts matched, in conjunct
order. -/
def proposals (s : Store) (src : Sources) : List Footprint :=
  (walk s false [] src.kernel).map Prod.snd

/-- `(tf:as P A)` for each pattern `P` and the atom `A` matched with it, in order. The
library's `(tf:as (, p1 ... pn) (, a1 ... an))` for a joint `unique` matches part by part,
which is these `n` conjuncts. -/
def asParts (ps atoms : List Atom) : List Conj :=
  (ps.zip atoms).map fun e => .as e.1 e.2

/-- A branch's kernel, guided by its proposal: each read or take of `P` whose proposal
matched `A` becomes that access of `A` followed by `(tf:as P A)`; each `unique` stays,
followed by `(tf:as P A)` for each of its parts and the atom the proposal matched with it;
`absent`, `collect` and `as` stay. -/
def guided : List Conj → Footprint → List Conj
  | [], _ => []
  | .pat m p :: cs, [] => .pat m p :: guided cs []
  | .pat _ p :: cs, (use, a) :: g => .pat use a :: .as p a :: guided cs g
  | .unique m q :: cs, g =>
      .unique m q :: (asParts q.parts ((g.take q.parts.length).map Prod.snd) ++
        guided cs (g.drop q.parts.length))
  | .absent q :: cs, g => .absent q :: guided cs g
  | .collect m q c :: cs, g => .collect m q c :: guided cs g
  | .as p a :: cs, g => .as p a :: guided cs g

/-- A kernel row of a branch with the rows its `all` extends it by. -/
structure Candidate where
  kernel : Footprint
  rows : List (Subst × Footprint)

/-- A candidate's footprint: its kernel's, then each row's, in row order. -/
def Candidate.footprint (c : Candidate) : Footprint := c.kernel ++ c.rows.flatMap Prod.snd

/-- A template is split at a top-level `,` into its components. -/
def split : Atom → List Atom
  | .expression (.symbol "," :: items) => items
  | a => [a]

/-- A candidate's instances: what `emit` makes of each row's bindings, in row order. -/
def Candidate.instances (c : Candidate) (emit : Subst → Answers) : Answers :=
  c.rows.flatMap fun r => emit r.1

/-- The instances of a row: the template under its bindings, split by the template's own
syntax, so a value bound to a comma expression stays one instance. -/
def instances (template : Atom) (ρ : Subst) : Answers :=
  (split template).map (applySubst ρ)

/-- The candidates of the branch with guide `g` against the store `s`: its guided kernel and
its `once` conjuncts, fired from the empty substitution, each with the rows its `all`
extends it by. -/
def candidates (s : Store) (g : Footprint) (src : Sources) : List Candidate :=
  (walk s true [] (guided src.kernel g ++ src.choice)).map fun k =>
    ⟨k.2, match src.every with
      | none => [(k.1, [])]
      | some ext => walk s true k.1 ext⟩

/-- One firing: the first candidate whose footprint validates is committed. -/
def fire (s : Store) (g : Footprint) (src : Sources) (emit : Subst → Answers) :
    Option (Store × Answers) :=
  ((candidates s g src).find? fun c => valid s c.footprint).map fun c =>
    (commit c.footprint s, c.instances emit)

/-- A branch as a computation: one firing, answered once at the committed store, or
nothing with the store unchanged. -/
def firing (src : Sources) (emit : Subst → Answers) (g : Footprint) : Search Store Answers :=
  fun s => match fire s g src emit with
  | none => .done s
  | some (s', out) => .answer out s' .done

/-- The transform, as the library writes it: the proposals at the call, one branch for
each, then the route of each firing's instances. -/
def transformWith {β : Type} (route : Answers → Search Store β) (src : Sources)
    (emit : Subst → Answers) : Search Store β := fun s =>
  ((Search.superpose (proposals s src)).bind fun g => (firing src emit g).bind route) s

/-- Instances go to the caller, one answer each. -/
def toCaller : Answers → Search Store Atom := Search.superpose

/-- Instances are added to the store itself; the answer is how many. -/
def intoStore (out : Answers) : Search Store Nat := fun s =>
  .answer out.length (s ++ out) .done

/-- `(transform SPACE SOURCES TEMPLATE)`. -/
def transform (src : Sources) (template : Atom) : Search Store Atom :=
  transformWith toCaller src (instances template)

/-- `(transform SPACE SOURCES TEMPLATE SPACE)`. -/
def transformInto (src : Sources) (template : Atom) : Search Store Nat :=
  transformWith intoStore src (instances template)

/-- PeTTa's `match` over a pattern conjunction: bindings threaded left to right. -/
def matchConj (s : Store) : Subst → List Atom → List Subst
  | σ, [] => [σ]
  | σ, p :: ps => (matchesIn s σ p).flatMap fun r => matchConj s r.1 ps

/-- The answers of `match` on a pattern conjunction: the template under each match. -/
def matchAnswers (s : Store) (ps : List Atom) (template : Atom) : Answers :=
  (matchConj s [] ps).map fun σ => applySubst σ template

/-! ## Matching against the store -/

theorem rel_lookupExtends {σ τ : Subst} {p a : Atom} (h : MatchAtomRel σ p a τ) :
    Subst.lookupExtends τ σ :=
  matchAtom_lookupExtends (matchAtom_complete h)

theorem lookup_cons_self (v : String) (a : Atom) (σ : Subst) :
    Subst.lookup ((v, a) :: σ) v = some a := by
  simp [Subst.lookup]

/-- A match is stable under its own bindings: under any extension of the bindings it
produced, the pattern matches the same atom and binds nothing more. -/
theorem rel_reapply {σ τ : Subst} {p a : Atom} (h : MatchAtomRel σ p a τ) :
    ∀ {ρ : Subst}, Subst.lookupExtends ρ τ → MatchAtomRel ρ p a ρ := by
  induction h with
  | var_fresh _ => intro ρ ext; exact .var_bound (ext _ _ (lookup_cons_self _ _ _))
  | var_bound found => intro ρ ext; exact .var_bound (ext _ _ found)
  | symbol => intro _ _; exact .symbol
  | grounded => intro _ _; exact .grounded
  | expr_nil => intro _ _; exact .expr_nil
  | expr_cons _ tail headIH tailIH =>
      intro ρ ext
      exact .expr_cons (headIH (Subst.lookupExtends_trans (rel_lookupExtends tail) ext))
        (tailIH ext)

/-- Under any extension of the bindings a match produced, the pattern matches only the
atom it matched, and binds nothing more. -/
theorem rel_determined {σ τ : Subst} {p a : Atom} (h : MatchAtomRel σ p a τ) :
    ∀ {ρ ρ' : Subst} {b : Atom}, Subst.lookupExtends ρ τ → MatchAtomRel ρ p b ρ' →
      b = a ∧ ρ' = ρ := by
  induction h with
  | var_fresh _ =>
      intro ρ ρ' b ext other
      have found := ext _ _ (lookup_cons_self _ _ _)
      cases other with
      | var_fresh fresh => rw [found] at fresh; cases fresh
      | var_bound bound => rw [found] at bound; cases bound; exact ⟨rfl, rfl⟩
  | var_bound found₀ =>
      intro ρ ρ' b ext other
      have found := ext _ _ found₀
      cases other with
      | var_fresh fresh => rw [found] at fresh; cases fresh
      | var_bound bound => rw [found] at bound; cases bound; exact ⟨rfl, rfl⟩
  | symbol => intro _ _ _ _ other; cases other; exact ⟨rfl, rfl⟩
  | grounded => intro _ _ _ _ other; cases other; exact ⟨rfl, rfl⟩
  | expr_nil => intro _ _ _ _ other; cases other; exact ⟨rfl, rfl⟩
  | expr_cons _ tail headIH tailIH =>
      intro ρ ρ' b ext other
      cases other with
      | expr_cons head' tail' =>
          obtain ⟨rfl, rfl⟩ :=
            headIH (Subst.lookupExtends_trans (rel_lookupExtends tail) ext) head'
          obtain ⟨same, rfl⟩ := tailIH ext tail'
          cases same
          exact ⟨rfl, rfl⟩

/-- A ground pattern matches only itself, and binds nothing. -/
theorem rel_ground {σ τ : Subst} {p a : Atom} (h : MatchAtomRel σ p a τ) :
    isGroundAtom p = true → a = p ∧ τ = σ := by
  induction h with
  | var_fresh _ => intro ground; simp [isGroundAtom] at ground
  | var_bound _ => intro ground; simp [isGroundAtom] at ground
  | symbol => intro _; exact ⟨rfl, rfl⟩
  | grounded => intro _; exact ⟨rfl, rfl⟩
  | expr_nil => intro _; exact ⟨rfl, rfl⟩
  | expr_cons _ _ headIH tailIH =>
      intro ground
      simp only [isGroundAtom, isGroundAtom.isGroundList, Bool.and_eq_true] at ground
      obtain ⟨rfl, rfl⟩ := headIH ground.1
      obtain ⟨same, rfl⟩ := tailIH (by simpa [isGroundAtom] using ground.2)
      cases same
      exact ⟨rfl, rfl⟩

/-- A ground atom matches itself under any bindings, binding nothing. -/
theorem matchAtom_ground_self (ρ : Subst) : ∀ a : Atom, isGroundAtom a = true →
    matchAtom ρ a a = some ρ
  | .var _, ground => by simp [isGroundAtom] at ground
  | .symbol _, _ => by simp [matchAtom]
  | .grounded _, _ => by simp [matchAtom]
  | .expression es, ground => by
      simp only [matchAtom]
      exact list es ground
where
  list : ∀ es : List Atom, isGroundAtom.isGroundList es = true →
      matchAtom.matchAtomList ρ es es = some ρ
    | [], _ => rfl
    | a :: as, ground => by
        simp only [isGroundAtom.isGroundList, Bool.and_eq_true] at ground
        simp only [matchAtom.matchAtomList, matchAtom_ground_self ρ a ground.1, list as ground.2]

/-- The stored matches of a ground atom are its copies, binding nothing. -/
theorem mem_matchesIn_ground {s : Store} {σ : Subst} {a : Atom} {r : Subst × Atom}
    (ground : isGroundAtom a = true) : r ∈ matchesIn s σ a ↔ r = (σ, a) ∧ a ∈ s := by
  rw [mem_matchesIn]
  constructor
  · rintro ⟨stored, matched⟩
    obtain ⟨same, bind⟩ := rel_ground (matchAtom_sound matched) ground
    obtain ⟨τ, b⟩ := r
    simp only at same bind stored
    subst same bind
    exact ⟨rfl, stored⟩
  · rintro ⟨rfl, stored⟩
    exact ⟨stored, matchAtom_ground_self σ a ground⟩

/-! ## Joint matches -/

theorem mem_jointIn_cons {s : Store} {σ : Subst} {p : Atom} {ps : List Atom}
    {t : Subst × List Atom} :
    t ∈ jointIn s σ (p :: ps) ↔
      ∃ r ∈ matchesIn s σ p, ∃ u ∈ jointIn s r.1 ps, t = (u.1, r.2 :: u.2) := by
  simp only [jointIn, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨r, hr, u, hu, rfl⟩; exact ⟨r, hr, u, hu, rfl⟩
  · rintro ⟨r, hr, u, hu, rfl⟩; exact ⟨r, hr, u, hu, rfl⟩

/-- Every joint match extends the bindings it starts from, has one atom per part, and its
atoms are stored. -/
theorem jointIn_sound {s : Store} :
    ∀ {ps : List Atom} {σ : Subst} {t : Subst × List Atom}, t ∈ jointIn s σ ps →
      Subst.lookupExtends t.1 σ ∧ t.2.length = ps.length ∧ ∀ a ∈ t.2, a ∈ s
  | [], σ, t, h => by
      simp only [jointIn, List.mem_singleton] at h
      subst h
      exact ⟨Subst.lookupExtends_refl σ, rfl, by simp⟩
  | p :: ps, σ, t, h => by
      obtain ⟨r, hr, u, hu, rfl⟩ := mem_jointIn_cons.mp h
      obtain ⟨stored, matched⟩ := mem_matchesIn.mp hr
      obtain ⟨ext, len, atoms⟩ := jointIn_sound hu
      refine ⟨Subst.lookupExtends_trans (matchAtom_lookupExtends matched) ext, by simp [len], ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact stored
      · exact atoms a ha

/-- **The joint matches are the matches of `match` on the conjunction**, in its order and
with its duplicates. -/
theorem jointIn_fst (s : Store) : ∀ (ps : List Atom) (σ : Subst),
    (jointIn s σ ps).map Prod.fst = matchConj s σ ps
  | [], σ => rfl
  | p :: ps, σ => by
      simp only [jointIn, matchConj, List.map_flatMap, List.map_map]
      congr 1
      funext r
      rw [← jointIn_fst s ps r.1]
      rfl

theorem jointIn_eq_nil_iff {s : Store} {σ : Subst} {ps : List Atom} :
    jointIn s σ ps = [] ↔ matchConj s σ ps = [] := by
  rw [← jointIn_fst, List.map_eq_nil_iff]

/-- The joint matches of one part are the matches of its pattern, each a one-atom tuple. -/
theorem jointIn_one (s : Store) (σ : Subst) (p : Atom) :
    jointIn s σ [p] = (matchesIn s σ p).map fun r => (r.1, [r.2]) := by
  simp [jointIn, List.map_eq_flatMap]

theorem mem_collected {s : Store} {σ : Subst} {m : Mode} {q : Query} {t : Subst × List Atom}
    (h : t ∈ collected s σ m q) : t ∈ jointIn s σ q.parts := by
  cases q with
  | one p => exact h
  | conj ps =>
      cases m with
      | read => exact h
      | take => exact (List.mem_filter.mp h).1

/-- **A take-mode `collect` over a conjunction keeps exactly the joint matches that fit**,
in their order. -/
theorem collected_take_conj (s : Store) (σ : Subst) (ps : List Atom) :
    collected s σ .take (.conj ps) = (jointIn s σ ps).filter fun t => fits s t.2 := rfl

theorem mem_collected_take_conj {s : Store} {σ : Subst} {ps : List Atom}
    {t : Subst × List Atom} :
    t ∈ collected s σ .take (.conj ps) ↔ t ∈ jointIn s σ ps ∧ fits s t.2 = true := by
  rw [collected_take_conj, List.mem_filter]

/-- A tuple of stored atoms with one atom fits. -/
theorem fits_single {s : Store} {a : Atom} (stored : a ∈ s) : fits s [a] = true := by
  simpa [fits] using List.count_pos_iff.mpr stored

/-- Read-mode `collect` and one-pattern `collect` keep every joint match. -/
theorem collected_eq_jointIn {s : Store} {σ : Subst} {m : Mode} {q : Query}
    (h : m = .read ∨ ∃ p, q = .one p) : collected s σ m q = jointIn s σ q.parts := by
  rcases h with rfl | ⟨p, rfl⟩
  · cases q <;> rfl
  · rfl

@[simp] theorem collectTakes_propose (s : Store) (m : Mode) (q : Query) (ts : List (List Atom)) :
    collectTakes s false m q ts = [] := rfl

@[simp] theorem collectTakes_read (s : Store) (firing : Bool) (q : Query)
    (ts : List (List Atom)) : collectTakes s firing .read q ts = [] := by
  cases firing <;> rfl

theorem mem_collectTakes {s : Store} {firing : Bool} {m : Mode} {q : Query}
    {ts : List (List Atom)} {e : Mode × Atom} (h : e ∈ collectTakes s firing m q ts) :
    e.1 = .take ∧ e.2 ∈ ts.flatten := by
  unfold collectTakes at h
  split at h
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp h
    exact ⟨rfl, ha⟩
  · obtain ⟨a, ha, he⟩ := List.mem_flatMap.mp h
    obtain ⟨-, rfl⟩ := List.mem_replicate.mp he
    exact ⟨rfl, List.mem_eraseDups.mp ha⟩
  · simp at h

/-! ## Walks -/

theorem mem_walk_pat {s : Store} {firing : Bool} {σ : Subst} {m : Mode} {p : Atom}
    {cs : List Conj} {w : Subst × Footprint} :
    w ∈ walk s firing σ (.pat m p :: cs) ↔
      ∃ r ∈ matchesIn s σ p, ∃ v ∈ walk s firing r.1 cs, w = (v.1, (m, r.2) :: v.2) := by
  simp only [walk, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨r, hr, v, hv, rfl⟩; exact ⟨r, hr, v, hv, rfl⟩
  · rintro ⟨r, hr, v, hv, rfl⟩; exact ⟨r, hr, v, hv, rfl⟩

/-- Every row extends the bindings it starts from, and its footprint names stored atoms. -/
theorem walk_sound {s : Store} {firing : Bool} :
    ∀ {cs : List Conj} {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ cs → Subst.lookupExtends w.1 σ ∧ ∀ e ∈ w.2, e.2 ∈ s
  | [], σ, w, h => by
      simp only [walk, List.mem_singleton] at h
      subst h
      exact ⟨Subst.lookupExtends_refl σ, by simp⟩
  | .pat m p :: cs, σ, w, h => by
      obtain ⟨r, hr, v, hv, rfl⟩ := mem_walk_pat.mp h
      obtain ⟨stored, matched⟩ := mem_matchesIn.mp hr
      obtain ⟨ext, entries⟩ := walk_sound hv
      refine ⟨Subst.lookupExtends_trans (matchAtom_lookupExtends matched) ext, ?_⟩
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact stored
      · exact entries e he
  | .absent q :: cs, σ, w, h => by
      simp only [walk] at h
      split at h
      · exact walk_sound h
      · simp at h
  | .unique m q :: cs, σ, w, h => by
      simp only [walk] at h
      split at h
      · rename_i t found
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        have ht : t ∈ jointIn s σ q.parts := by rw [found]; exact List.mem_singleton_self t
        obtain ⟨ext₁, -, atoms⟩ := jointIn_sound ht
        obtain ⟨ext, entries⟩ := walk_sound hv
        refine ⟨Subst.lookupExtends_trans ext₁ ext, ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
          exact atoms a ha
        · exact entries e he
      · simp at h
  | .collect m q c :: cs, σ, w, h => by
      simp only [walk] at h
      split at h
      · simp at h
      · rename_i τ matched
        obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
        obtain ⟨ext, entries⟩ := walk_sound hv
        refine ⟨Subst.lookupExtends_trans (matchAtom_lookupExtends matched) ext, ?_⟩
        intro e he
        rcases List.mem_append.mp he with he | he
        · obtain ⟨t, ht, member⟩ := List.mem_flatten.mp (mem_collectTakes he).2
          obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
          exact (jointIn_sound (mem_collected hu)).2.2 _ member
        · exact entries e he
  | .as p a :: cs, σ, w, h => by
      simp only [walk] at h
      split at h
      · simp at h
      · rename_i τ matched
        obtain ⟨ext, entries⟩ := walk_sound h
        exact ⟨Subst.lookupExtends_trans (matchAtom_lookupExtends matched) ext, entries⟩

/-- Rows of a conjunction are the rows of its first part, each extended by the rows of the
second. -/
theorem walk_append (s : Store) (firing : Bool) : ∀ (cs ds : List Conj) (σ : Subst),
    walk s firing σ (cs ++ ds) =
      (walk s firing σ cs).flatMap fun w =>
        (walk s firing w.1 ds).map fun v => (v.1, w.2 ++ v.2)
  | [], ds, σ => by simp [walk]
  | .pat m p :: cs, ds, σ => by
      simp only [List.cons_append, walk, walk_append s firing cs ds, List.flatMap_assoc,
        List.map_flatMap, List.flatMap_map, List.map_map]
      rfl
  | .absent q :: cs, ds, σ => by
      simp only [List.cons_append, walk]
      split
      · exact walk_append s firing cs ds σ
      · simp
  | .unique m q :: cs, ds, σ => by
      simp only [List.cons_append, walk]
      split
      · simp only [walk_append s firing cs ds, List.map_flatMap, List.flatMap_map, List.map_map,
          List.append_assoc]
        rfl
      · simp
  | .collect m q c :: cs, ds, σ => by
      simp only [List.cons_append, walk]
      split
      · simp
      · simp only [walk_append s firing cs ds, List.map_flatMap, List.flatMap_map, List.map_map,
          List.append_assoc]
        rfl
  | .as p a :: cs, ds, σ => by
      simp only [List.cons_append, walk]
      split
      · simp
      · exact walk_append s firing cs ds _

/-! ## Law 7: one pattern, and the one-part conjunction -/

/-- `(absent p)` of one pattern: no stored atom matches it. -/
theorem walk_absent_one (s : Store) (firing : Bool) (σ : Subst) (p : Atom) (cs : List Conj) :
    walk s firing σ (.absent (.one p) :: cs) =
      if matchesIn s σ p = [] then walk s firing σ cs else [] := by
  simp [walk, Query.parts, jointIn_one]

/-- `(unique p)` of one pattern: exactly one stored atom matches it, and it is the footprint's
entry. -/
theorem walk_unique_one (s : Store) (firing : Bool) (σ : Subst) (m : Mode) (p : Atom)
    (cs : List Conj) :
    walk s firing σ (.unique m (.one p) :: cs) =
      match matchesIn s σ p with
      | [r] => (walk s firing r.1 cs).map fun w => (w.1, (m, r.2) :: w.2)
      | _ => [] := by
  simp only [walk, Query.parts, jointIn_one]
  cases matchesIn s σ p with
  | nil => rfl
  | cons r rs =>
      cases rs with
      | nil => simp
      | cons => rfl

theorem flatten_map_singleton {γ : Type} (l : List γ) (f : γ → Atom) :
    (l.map fun r => [f r]).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons r l ih => simp [ih]

/-- `(collect p C)` of one pattern: the list of the stored atoms matching it, each taken in
take mode. -/
theorem walk_collect_one (s : Store) (firing : Bool) (σ : Subst) (m : Mode) (p c : Atom)
    (cs : List Conj) :
    walk s firing σ (.collect m (.one p) c :: cs) =
      match matchAtom σ c (.expression ((matchesIn s σ p).map Prod.snd)) with
      | none => []
      | some τ =>
          (walk s firing τ cs).map fun w =>
            (w.1, (if firing = true ∧ m = .take then
              (matchesIn s σ p).map (fun r => (Mode.take, r.2)) else []) ++ w.2) := by
  have found :
      ((collected s σ m (.one p)).map Prod.snd).flatten = (matchesIn s σ p).map Prod.snd := by
    simp only [collected, jointIn_one, List.map_map, Function.comp_def]
    exact flatten_map_singleton _ _
  simp only [walk, Query.collection, found]
  cases firing <;> cases m <;> simp [collectTakes, found, List.map_map, Function.comp_def]

/-- A one-part conjunction is its pattern for `absent`, at every continuation. -/
theorem walk_absent_conj_single (s : Store) (firing : Bool) (σ : Subst) (p : Atom)
    (cs : List Conj) :
    walk s firing σ (.absent (.conj [p]) :: cs) = walk s firing σ (.absent (.one p) :: cs) := rfl

/-- A one-part conjunction is its pattern for `unique`, at every continuation. -/
theorem walk_unique_conj_single (s : Store) (firing : Bool) (σ : Subst) (m : Mode) (p : Atom)
    (cs : List Conj) :
    walk s firing σ (.unique m (.conj [p]) :: cs) =
      walk s firing σ (.unique m (.one p) :: cs) := rfl

/-- A branch whose kernel starts with `absent` or `unique` of a one-part conjunction has the
candidates of the branch with the one pattern. -/
theorem candidates_conj_single (s : Store) (g : Footprint) (p : Atom) (cs choice : List Conj)
    (every : Option (List Conj)) :
    candidates s g ⟨.absent (.conj [p]) :: cs, choice, every⟩ =
        candidates s g ⟨.absent (.one p) :: cs, choice, every⟩ ∧
      ∀ m, candidates s g ⟨.unique m (.conj [p]) :: cs, choice, every⟩ =
        candidates s g ⟨.unique m (.one p) :: cs, choice, every⟩ :=
  ⟨rfl, fun _ => rfl⟩

/-- A one-part conjunction proposes as its pattern for `absent` and `unique`. -/
theorem proposals_conj_single (s : Store) (p : Atom) (cs choice : List Conj)
    (every : Option (List Conj)) :
    proposals s ⟨.absent (.conj [p]) :: cs, choice, every⟩ =
        proposals s ⟨.absent (.one p) :: cs, choice, every⟩ ∧
      ∀ m, proposals s ⟨.unique m (.conj [p]) :: cs, choice, every⟩ =
        proposals s ⟨.unique m (.one p) :: cs, choice, every⟩ :=
  ⟨rfl, fun _ => rfl⟩

/-- A one-part conjunction collects the joint matches its pattern collects; the value is the
list of the one-part tuples `(, a)`. -/
theorem collected_conj_single (s : Store) (σ : Subst) (m : Mode) (p : Atom) :
    collected s σ m (.conj [p]) = collected s σ m (.one p) := by
  cases m with
  | read => rfl
  | take =>
      simp only [collected]
      rw [List.filter_eq_self]
      intro t ht
      obtain ⟨-, len, atoms⟩ := jointIn_sound ht
      obtain ⟨a, ha⟩ : ∃ a, t.2 = [a] := List.length_eq_one_iff.mp len
      rw [ha]
      exact fits_single (atoms a (by simp [ha]))

/-- A one-pattern `unique` is guided as before: followed by `(tf:as P A)` for the atom its
proposal matched, and unguided when the guide is exhausted. -/
theorem guided_unique_one (m : Mode) (p : Atom) (cs : List Conj) :
    guided (.unique m (.one p) :: cs) [] = .unique m (.one p) :: guided cs [] ∧
      ∀ (u : Mode) (a : Atom) (g : Footprint),
        guided (.unique m (.one p) :: cs) ((u, a) :: g) =
          .unique m (.one p) :: .as p a :: guided cs g := by
  refine ⟨by simp [guided, asParts, Query.parts], fun u a g => ?_⟩
  simp [guided, asParts, Query.parts]

/-! ## Guided firing -/

theorem walk_as_expression (s : Store) (firing : Bool) :
    ∀ (ps atoms : List Atom) (ρ : Subst) (cs : List Conj), ps.length = atoms.length →
      walk s firing ρ (.as (.expression ps) (.expression atoms) :: cs) =
        walk s firing ρ (asParts ps atoms ++ cs)
  | [], [], ρ, cs, _ => by simp [walk, matchAtom, matchAtom.matchAtomList, asParts]
  | [], _ :: _, _, _, len => by simp at len
  | _ :: _, [], _, _, len => by simp at len
  | p :: ps, a :: atoms, ρ, cs, len => by
      have ih := walk_as_expression s firing ps atoms
      have step : asParts (p :: ps) (a :: atoms) ++ cs = .as p a :: (asParts ps atoms ++ cs) := by
        simp [asParts]
      rw [step]
      simp only [walk, matchAtom, matchAtom.matchAtomList] at ih ⊢
      cases matchAtom ρ p a with
      | none => rfl
      | some σ' => exact ih σ' cs (by simpa using len)

/-- **The library's one `(tf:as (, p1 ... pn) (, a1 ... an))` is `asParts`**: matching the
tuple pattern against the tuple of atoms is matching each part against its atom, in order. -/
theorem walk_as_tuple (s : Store) (firing : Bool) (ρ : Subst) (ps atoms : List Atom)
    (cs : List Conj) (len : ps.length = atoms.length) :
    walk s firing ρ
        (.as (.expression (.symbol "," :: ps)) (.expression (.symbol "," :: atoms)) :: cs) =
      walk s firing ρ (asParts ps atoms ++ cs) := by
  rw [walk_as_expression s firing _ _ ρ cs (by simp [len])]
  simp [asParts, walk, matchAtom]

/-- Under the bindings of a joint match, `(tf:as P A)` for each part and a list of atoms holds,
and binds nothing more, exactly when the atoms are the match's tuple. -/
theorem walk_asParts {s s' : Store} {firing : Bool} :
    ∀ {ps : List Atom} {σ : Subst} {t : Subst × List Atom}, t ∈ jointIn s' σ ps →
      ∀ {ρ : Subst}, Subst.lookupExtends ρ t.1 → ∀ (bs : List Atom), bs.length = ps.length →
        ∀ cs : List Conj,
          walk s firing ρ (asParts ps bs ++ cs) = if bs = t.2 then walk s firing ρ cs else []
  | [], σ, t, h, ρ, _, bs, len, cs => by
      simp only [jointIn, List.mem_singleton] at h
      subst h
      obtain rfl : bs = [] := List.eq_nil_of_length_eq_zero len
      simp [asParts]
  | p :: ps, σ, t, h, ρ, ext, bs, len, cs => by
      obtain ⟨r, hr, u, hu, rfl⟩ := mem_jointIn_cons.mp h
      obtain ⟨-, matched⟩ := mem_matchesIn.mp hr
      obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_length_eq_add_one len
      have extR : Subst.lookupExtends ρ r.1 :=
        Subst.lookupExtends_trans (jointIn_sound hu).1 ext
      have rest := walk_asParts (s := s) (firing := firing) hu ext bs
        (by simpa using len) cs
      simp only [asParts, List.zip_cons_cons, List.map_cons, List.cons_append, walk] at rest ⊢
      by_cases hb : b = r.2
      · subst hb
        rw [matchAtom_complete (rel_reapply (matchAtom_sound matched) extR)]
        simp only [rest, List.cons.injEq, true_and]
      · have none : matchAtom ρ p b = none := by
          cases hm : matchAtom ρ p b with
          | none => rfl
          | some τ =>
              exact absurd (rel_determined (matchAtom_sound matched) extR
                (matchAtom_sound hm)).1 hb
        simp [none, hb]

/-- **A branch whose guide names an atom that is gone has no row.** If a ground atom its
proposal matched with a read, take or `unique` is no longer stored, the guided kernel has
no row under any bindings: the access of that atom finds nothing, and a `unique` that finds
another atom fails its `(tf:as P A)`. -/
theorem walk_guided_gone {s₀ s : Store} {a : Atom} (ground : isGroundAtom a = true)
    (gone : a ∉ s) : ∀ (cs : List Conj) (ρ₀ τ : Subst) (g : Footprint) (m : Mode),
      (τ, g) ∈ walk s₀ false ρ₀ cs → (m, a) ∈ g → ∀ ρ, walk s true ρ (guided cs g) = []
  | [], ρ₀, τ, g, m, h, mem, ρ => by
      simp only [walk, List.mem_singleton, Prod.mk.injEq] at h
      rw [h.2] at mem
      cases mem
  | .pat m' p :: cs, ρ₀, τ, g, m, h, mem, ρ => by
      obtain ⟨r, -, v, hv, same⟩ := mem_walk_pat.mp h
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      simp only [guided, walk, List.flatMap_eq_nil_iff, List.map_eq_nil_iff]
      intro r' hr'
      rcases List.mem_cons.mp mem with here | later
      · simp only [Prod.mk.injEq] at here
        obtain ⟨rfl, rfl⟩ := here
        exact absurd ((mem_matchesIn_ground ground).mp hr').2 gone
      · split
        · rfl
        · exact walk_guided_gone ground gone cs r.1 v.1 v.2 m hv later _
  | .absent q :: cs, ρ₀, τ, g, m, h, mem, ρ => by
      simp only [walk] at h
      split at h
      · simp only [guided, walk]
        split
        · exact walk_guided_gone ground gone cs ρ₀ τ g m h mem ρ
        · rfl
      · simp at h
  | .unique m' q :: cs, ρ₀, τ, g, m, h, mem, ρ => by
      simp only [walk] at h
      split at h
      · rename_i t₀ found
        obtain ⟨v, hv, same⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        have ht₀ : t₀ ∈ jointIn s₀ ρ₀ q.parts := by
          rw [found]; exact List.mem_singleton_self t₀
        have len₀ := (jointIn_sound ht₀).2.1
        have entries : (t₀.2.map fun a => (m', a)).length = q.parts.length := by simp [len₀]
        simp only [guided]
        rw [← entries, List.take_left, List.drop_left, List.map_map]
        have back : (Prod.snd ∘ fun a => (m', a)) = fun a : Atom => a := rfl
        rw [back, List.map_id']
        simp only [walk]
        split
        · rename_i t found'
          have ht : t ∈ jointIn s ρ q.parts := by
            rw [found']; exact List.mem_singleton_self t
          rw [walk_asParts ht (Subst.lookupExtends_refl _) t₀.2 len₀]
          split
          · rename_i sameTuple
            rcases List.mem_append.mp mem with here | later
            · obtain ⟨a', ha', eq⟩ := List.mem_map.mp here
              simp only [Prod.mk.injEq] at eq
              obtain ⟨-, rfl⟩ := eq
              exact absurd ((jointIn_sound ht).2.2 _ (sameTuple ▸ ha')) gone
            · rw [walk_guided_gone ground gone cs t₀.1 v.1 v.2 m hv later t.1]
              rfl
          · rfl
        · rfl
      · simp at h
  | .collect m' q c :: cs, ρ₀, τ, g, m, h, mem, ρ => by
      simp only [walk] at h
      split at h
      · simp at h
      · rename_i τ₁ _
        obtain ⟨v, hv, same⟩ := List.mem_map.mp h
        simp only [Prod.mk.injEq, collectTakes_propose, List.nil_append] at same
        obtain ⟨rfl, rfl⟩ := same
        simp only [guided, walk]
        split
        · rfl
        · rename_i τ' _
          rw [walk_guided_gone ground gone cs τ₁ v.1 v.2 m hv mem τ']
          rfl
  | .as p a' :: cs, ρ₀, τ, g, m, h, mem, ρ => by
      simp only [walk] at h
      split at h
      · simp at h
      · rename_i τ₁ _
        simp only [guided, walk]
        split
        · rfl
        · exact walk_guided_gone ground gone cs τ₁ τ g m h mem _

/-- **A read proposal fires again as itself.** On a ground store, the guided kernel of a
pattern conjunction's proposal has, against the same store, exactly that proposal's row: the
same bindings and the same footprint, once for each choice of the stored copies. -/
theorem walk_guided_reads {s : Store} (ground : ∀ a ∈ s, isGroundAtom a = true) :
    ∀ (ps : List Atom) (ρ σ : Subst) (g : Footprint),
      (σ, g) ∈ walk s false ρ (ps.map (.pat .read)) →
        (σ, g) ∈ walk s true ρ (guided (ps.map (.pat .read)) g) ∧
          ∀ w ∈ walk s true ρ (guided (ps.map (.pat .read)) g), w = (σ, g)
  | [], ρ, σ, g, h => by
      simp only [List.map_nil, walk, List.mem_singleton, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [guided, walk]
  | p :: ps, ρ, σ, g, h => by
      obtain ⟨r, hr, v, hv, same⟩ := mem_walk_pat.mp h
      simp only [Prod.mk.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      obtain ⟨stored, matched⟩ := mem_matchesIn.mp hr
      have atomGround := ground _ stored
      obtain ⟨again, only⟩ := walk_guided_reads ground ps r.1 v.1 v.2 hv
      have asStep : walk s true ρ (.as p r.2 :: guided (ps.map (.pat .read)) v.2) =
          walk s true r.1 (guided (ps.map (.pat .read)) v.2) := by
        simp [walk, matched]
      simp only [List.map_cons, guided]
      constructor
      · refine mem_walk_pat.mpr ⟨(ρ, r.2), (mem_matchesIn_ground atomGround).mpr ⟨rfl, stored⟩,
          (v.1, v.2), ?_, rfl⟩
        rw [asStep]
        exact again
      · intro w hw
        obtain ⟨r', hr', v', hv', rfl⟩ := mem_walk_pat.mp hw
        obtain ⟨rfl, -⟩ := (mem_matchesIn_ground atomGround).mp hr'
        rw [asStep] at hv'
        rw [only v' hv']

/-! ## Law 2: validation and the commit -/

/-- Multiset counts are list counts. -/
theorem count_coe (a : Atom) (l : List Atom) :
    Multiset.count a (l : Multiset Atom) = l.count a := by
  rw [Multiset.coe_count]
  congr
  exact lawful_beq_subsingleton _ _

@[simp] theorem takes_nil : takes [] = [] := rfl
@[simp] theorem takes_cons_take (a : Atom) (fp : Footprint) :
    takes ((.take, a) :: fp) = a :: takes fp := rfl
@[simp] theorem takes_cons_read (a : Atom) (fp : Footprint) :
    takes ((.read, a) :: fp) = takes fp := rfl
@[simp] theorem reads_nil : reads [] = [] := rfl
@[simp] theorem reads_cons_read (a : Atom) (fp : Footprint) :
    reads ((.read, a) :: fp) = a :: reads fp := rfl
@[simp] theorem reads_cons_take (a : Atom) (fp : Footprint) :
    reads ((.take, a) :: fp) = reads fp := rfl

@[simp] theorem takes_append (fp fq : Footprint) : takes (fp ++ fq) = takes fp ++ takes fq := by
  simp [takes, List.filterMap_append]

theorem mem_takes {fp : Footprint} {a : Atom} : a ∈ takes fp ↔ (Mode.take, a) ∈ fp := by
  induction fp with
  | nil => simp
  | cons e fp ih =>
      obtain ⟨m, b⟩ := e
      cases m <;> simp [ih]

theorem mem_reads {fp : Footprint} {a : Atom} : a ∈ reads fp ↔ (Mode.read, a) ∈ fp := by
  induction fp with
  | nil => simp
  | cons e fp ih =>
      obtain ⟨m, b⟩ := e
      cases m <;> simp [ih]

theorem count_take_eq (fp : Footprint) (a : Atom) : fp.count (.take, a) = (takes fp).count a := by
  induction fp with
  | nil => rfl
  | cons e fp ih =>
      obtain ⟨m, b⟩ := e
      cases m <;> by_cases h : b = a <;> simp [h, ih]

/-- **Validation, as counts.** A footprint validates when each atom it takes is stored at
least as often as it is taken, and once more when it is also read. -/
theorem valid_iff (s : Store) (fp : Footprint) :
    valid s fp = true ↔
      ∀ a ∈ takes fp, (takes fp).count a + (if a ∈ reads fp then 1 else 0) ≤ s.count a := by
  have readPos : ∀ a, (0 < fp.count (.read, a)) ↔ a ∈ reads fp := fun a => by
    rw [List.count_pos_iff, mem_reads]
  unfold valid
  rw [List.all_eq_true]
  constructor
  · intro h a ha
    have := h (.take, a) (mem_takes.mp ha)
    simpa [count_take_eq, readPos] using this
  · rintro h ⟨m, a⟩ he
    cases m with
    | read => rfl
    | take => simpa [count_take_eq, readPos] using h a (mem_takes.mpr he)

/-- **Validation, as multisets.** The takes are a submultiset of the store, with a spare
copy of every atom the firing also reads. -/
theorem valid_iff_le (s : Store) (fp : Footprint) :
    valid s fp = true ↔
      (takes fp : Multiset Atom) ≤ (s : Multiset Atom) ∧
        ∀ a ∈ takes fp, a ∈ reads fp → (takes fp).count a < s.count a := by
  rw [valid_iff, Multiset.le_iff_count]
  simp only [count_coe]
  constructor
  · intro h
    refine ⟨fun a => ?_, fun a ha hr => ?_⟩
    · by_cases ha : a ∈ takes fp
      · have := h a ha
        split at this <;> omega
      · rw [List.count_eq_zero_of_not_mem ha]
        exact Nat.zero_le _
    · have := h a ha
      rw [if_pos hr] at this
      omega
  · rintro ⟨le, spare⟩ a ha
    split
    · have := spare a ha (by assumption)
      omega
    · simpa using le a

theorem count_commitOne (s : Store) (a : Atom) (n : Nat) (x : Atom) :
    (commitOne s a n).count x = if x = a then s.count a - n else s.count x := by
  unfold commitOne
  rw [List.count_append, List.count_replicate]
  by_cases h : x = a
  · subst h
    simp [List.count_eq_zero]
  · have keep : (x != a) = true := by simpa using h
    rw [List.count_filter (p := fun b => b != a) keep]
    simp [h, Ne.symm h]

theorem count_applyTakes (all : Footprint) :
    ∀ (todo : Footprint) (done : List Atom) (s : Store) (x : Atom),
      (applyTakes all todo done s).count x =
        if x ∉ done ∧ (Mode.take, x) ∈ todo then s.count x - all.count (.take, x)
        else s.count x
  | [], _, _, x => by simp [applyTakes]
  | (m, a) :: more, done, s, x => by
      simp only [applyTakes]
      split
      · rename_i fresh
        obtain ⟨rfl, notDone⟩ := fresh
        rw [count_applyTakes all more (a :: done) _ x, count_commitOne]
        by_cases h : x = a
        · subst h
          simp [notDone]
        · simp [h]
      · rename_i old
        rw [count_applyTakes all more done s x]
        by_cases h : x ∉ done
        · have : (Mode.take, x) ∈ (m, a) :: more ↔ (Mode.take, x) ∈ more := by
            constructor
            · intro mem
              rcases List.mem_cons.mp mem with same | mem
              · cases same
                exact absurd ⟨rfl, h⟩ old
              · exact mem
            · exact List.mem_cons_of_mem _
          simp [h, this]
        · simp [h]

/-- The commit removes from each atom's count exactly what the footprint takes. -/
theorem count_commit (fp : Footprint) (s : Store) (x : Atom) :
    (commit fp s).count x = s.count x - (takes fp).count x := by
  rw [commit, count_applyTakes, ← count_take_eq]
  by_cases h : (Mode.take, x) ∈ fp
  · simp [h]
  · simp [h, List.count_eq_zero_of_not_mem h]

/-- **The commit takes exactly the footprint's takes.** -/
theorem commit_coe (fp : Footprint) (s : Store) :
    (commit fp s : Multiset Atom) = (s : Multiset Atom) - (takes fp : Multiset Atom) := by
  ext x
  rw [Multiset.count_sub, count_coe, count_coe, count_coe, count_commit]

/-- **Conservation.** A validated commit splits the store into what stays and what is
taken: nothing more is removed and nothing less. -/
theorem commit_add_takes {s : Store} {fp : Footprint} (h : valid s fp = true) :
    (s : Multiset Atom) = (commit fp s : Multiset Atom) + (takes fp : Multiset Atom) := by
  rw [commit_coe]
  exact (tsub_add_cancel_of_le ((valid_iff_le s fp).mp h).1).symm

theorem applyTakes_of_reads (all : Footprint) :
    ∀ (todo : Footprint) (done : List Atom) (s : Store),
      (∀ e ∈ todo, e.1 = .read) → applyTakes all todo done s = s
  | [], _, _, _ => rfl
  | (m, a) :: more, done, s, reads => by
      have hm : m = .read := reads _ (List.mem_cons_self ..)
      subst hm
      simp only [applyTakes]
      rw [if_neg (by simp)]
      exact applyTakes_of_reads all more done s
        (fun e he => reads e (List.mem_cons_of_mem _ he))

/-- A footprint that only reads commits nothing. -/
theorem commit_of_reads {fp : Footprint} (reads : ∀ e ∈ fp, e.1 = .read) (s : Store) :
    commit fp s = s :=
  applyTakes_of_reads fp fp [] s reads

theorem takes_eq_nil_of_reads {fp : Footprint} (reads : ∀ e ∈ fp, e.1 = .read) :
    takes fp = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro a ha
  have := reads _ (mem_takes.mp ha)
  cases this

/-- A footprint that only reads validates. -/
theorem valid_of_reads {fp : Footprint} (reads : ∀ e ∈ fp, e.1 = .read) (s : Store) :
    valid s fp = true := by
  rw [valid_iff, takes_eq_nil_of_reads reads]
  simp

/-- **A firing commits the first candidate that validates.** -/
theorem fire_eq_some_iff {s s' : Store} {g : Footprint} {src : Sources} {emit : Subst → Answers}
    {out : Answers} :
    fire s g src emit = some (s', out) ↔
      ∃ pre c post, candidates s g src = pre ++ c :: post ∧
        (∀ d ∈ pre, valid s d.footprint = false) ∧ valid s c.footprint = true ∧
        s' = commit c.footprint s ∧ out = c.instances emit := by
  unfold fire
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, found, same⟩
    obtain ⟨ok, pre, post, split, before⟩ := List.find?_eq_some_iff_append.mp found
    simp only [Prod.mk.injEq] at same
    exact ⟨pre, c, post, split, fun d hd => by simpa using before d hd, ok, same.1.symm,
      same.2.symm⟩
  · rintro ⟨pre, c, post, split, before, ok, rfl, rfl⟩
    refine ⟨c, List.find?_eq_some_iff_append.mpr ⟨ok, pre, post, split, ?_⟩, rfl⟩
    intro d hd
    simp [before d hd]

/-- **A firing fires nothing exactly when no candidate validates.** -/
theorem fire_eq_none_iff {s : Store} {g : Footprint} {src : Sources} {emit : Subst → Answers} :
    fire s g src emit = none ↔ ∀ c ∈ candidates s g src, valid s c.footprint = false := by
  unfold fire
  rw [Option.map_eq_none_iff, List.find?_eq_none]
  simp

/-- A firing whose first candidate validates commits that candidate. -/
theorem fire_of_first {s : Store} {g : Footprint} {src : Sources} {emit : Subst → Answers}
    {c : Candidate} {rest : List Candidate} (cands : candidates s g src = c :: rest)
    (ok : valid s c.footprint = true) :
    fire s g src emit = some (commit c.footprint s, c.instances emit) := by
  simp [fire, cands, ok]

@[simp] theorem toCaller_drain (out : Answers) (s : Store) : (toCaller out s).drain = (out, s) :=
  Search.drain_superpose out s

@[simp] theorem takes_map_take {γ : Type} (l : List γ) (f : γ → Atom) :
    takes (l.map fun r => (Mode.take, f r)) = l.map f := by
  induction l with
  | nil => rfl
  | cons r l ih => simp [ih]

/-- **Atomicity of one firing.** It fires only when its footprint validates against the
store at that moment, and then the store loses exactly the footprint's takes. -/
theorem fire_conserves {s s' : Store} {g : Footprint} {src : Sources} {emit : Subst → Answers}
    {out : Answers} (fired : fire s g src emit = some (s', out)) :
    ∃ c ∈ candidates s g src, valid s c.footprint = true ∧
      (takes c.footprint : Multiset Atom) ≤ (s : Multiset Atom) ∧
      (s : Multiset Atom) = (s' : Multiset Atom) + (takes c.footprint : Multiset Atom) := by
  obtain ⟨pre, c, post, split, -, ok, rfl, -⟩ := fire_eq_some_iff.mp fired
  exact ⟨c, by rw [split]; simp, ok, ((valid_iff_le s _).mp ok).1, commit_add_takes ok⟩

/-- **A branch is one step.** Run as a computation, a firing either leaves the store as it
is and answers nothing, or answers its instances once, at the committed store; no
intermediate store is observable. -/
theorem firing_atomic (src : Sources) (emit : Subst → Answers) (g : Footprint) (s : Store) :
    (fire s g src emit = none ∧ firing src emit g s = .done s) ∨
      ∃ c ∈ candidates s g src, valid s c.footprint = true ∧
        firing src emit g s =
          .answer (c.instances emit) (commit c.footprint s) .done ∧
        (s : Multiset Atom) =
          (commit c.footprint s : Multiset Atom) + (takes c.footprint : Multiset Atom) := by
  cases fired : fire s g src emit with
  | none => exact Or.inl ⟨rfl, by simp [firing, fired]⟩
  | some result =>
      obtain ⟨s', out⟩ := result
      obtain ⟨pre, c, post, split, -, ok, rfl, rfl⟩ := fire_eq_some_iff.mp fired
      exact Or.inr ⟨c, by rw [split]; simp, ok, by simp [firing, fired], commit_add_takes ok⟩


/-! ## Law 3: branches -/

/-- One branch of the fold: the firing at the current store, then its route run to
completion from the committed store. -/
def branchStep {β : Type} (route : Answers → Search Store β) (src : Sources)
    (emit : Subst → Answers) (acc : List β × Store) (g : Footprint) : List β × Store :=
  match fire acc.2 g src emit with
  | none => acc
  | some (s', out) => (acc.1 ++ ((route out s').drain).1, ((route out s').drain).2)

/-- **Running the branches is the fold of single firings.** Each proposal fires against the
store the previous branches left, or fires nothing and leaves it. -/
theorem transformWith_drain {β : Type} (route : Answers → Search Store β) (src : Sources)
    (emit : Subst → Answers) (s : Store) :
    (transformWith route src emit s).drain =
      (proposals s src).foldl (branchStep route src emit) ([], s) := by
  have step : Search.foldStep (fun g => (firing src emit g).bind route) =
      branchStep route src emit := by
    funext acc g
    unfold Search.foldStep branchStep
    cases fired : fire acc.2 g src emit with
    | none => simp [Search.bind, firing, fired, Trace.bind]
    | some r =>
        obtain ⟨s', out⟩ := r
        simp [Search.bind, firing, fired, Trace.bind, Trace.drain_append]
  unfold transformWith
  rw [Search.drain_bind_superpose, step]

/-- **A branch fires iff its proposal still holds**: some candidate of its guided sources,
against the store it finds, takes a submultiset of that store with a spare copy of every atom
it also reads. -/
theorem fire_isSome_iff {s : Store} {g : Footprint} {src : Sources} {emit : Subst → Answers} :
    (fire s g src emit).isSome = true ↔
      ∃ c ∈ candidates s g src, (takes c.footprint : Multiset Atom) ≤ (s : Multiset Atom) ∧
        ∀ a ∈ takes c.footprint, a ∈ reads c.footprint →
          (takes c.footprint).count a < s.count a := by
  unfold fire
  rw [Option.isSome_map, List.find?_isSome]
  simp only [valid_iff_le]

/-- **A branch whose atom is gone fires nothing.** If a ground atom its proposal read, took
or found `unique` is no longer stored when the branch runs (an earlier branch took it), the
branch fires nothing. -/
theorem fire_eq_none_of_gone {s₀ s : Store} {src : Sources} {emit : Subst → Answers}
    {σ : Subst} {g : Footprint} {e : Mode × Atom}
    (proposed : (σ, g) ∈ walk s₀ false [] src.kernel) (mem : e ∈ g)
    (ground : isGroundAtom e.2 = true) (gone : e.2 ∉ s) : fire s g src emit = none := by
  have empty : walk s true [] (guided src.kernel g) = [] :=
    walk_guided_gone ground gone src.kernel [] σ g e.1 proposed mem []
  rw [fire_eq_none_iff]
  intro c hc
  simp [candidates, walk_append, empty] at hc

theorem mem_proposals {s : Store} {src : Sources} {g : Footprint} :
    g ∈ proposals s src ↔ ∃ σ, (σ, g) ∈ walk s false [] src.kernel := by
  simp [proposals]

/-! ## Law 4: `once` -/

theorem bind_superpose_skip {β : Type} (branch : Footprint → Search Store β) (s : Store) :
    ∀ (pre rest : List Footprint), (∀ g ∈ pre, branch g s = .done s) →
      (Search.superpose (pre ++ rest)).bind branch s = (Search.superpose rest).bind branch s
  | [], _, _ => rfl
  | g :: pre, rest, skip => by
      have here : branch g s = .done s := skip g (List.mem_cons_self ..)
      show (branch g s).append (fun s' => (Search.superpose (pre ++ rest) s').bind branch) = _
      rw [here]
      exact bind_superpose_skip branch s pre rest
        (fun g' h => skip g' (List.mem_cons_of_mem _ h))

theorem branch_skip {β : Type} {route : Answers → Search Store β} {src : Sources}
    {emit : Subst → Answers} {s : Store} {g : Footprint} (none : fire s g src emit = none) :
    ((firing src emit g).bind route) s = .done s := by
  simp [Search.bind, firing, none, Trace.bind]

/-- **`once` fires the first proposal that holds at the call.** Branches before it fire
nothing and leave the store; it fires once, and `once` answers its route's first answer
at that store and stops. -/
theorem once_transformWith {β : Type} (route : Answers → Search Store β) (src : Sources)
    (emit : Subst → Answers) (s : Store) {g : Footprint} {s₁ : Store} {out : Answers}
    (first : (proposals s src).find? (fun h => (fire s h src emit).isSome) = some g)
    (fires : fire s g src emit = some (s₁, out))
    {b : β} {s₂ : Store} {k : Store → Trace Store β} (answers : route out s₁ = .answer b s₂ k) :
    Search.once (transformWith route src emit) s = .answer b s₂ .done := by
  obtain ⟨-, pre, post, split, before⟩ := List.find?_eq_some_iff_append.mp first
  have skip : ∀ h ∈ pre, ((firing src emit h).bind route) s = .done s := by
    intro h hh
    have holds : (fire s h src emit).isSome = false := by simpa using before h hh
    have none : fire s h src emit = none := by
      cases fired : fire s h src emit with
      | none => rfl
      | some _ => simp [fired] at holds
    exact branch_skip none
  unfold Search.once transformWith
  rw [split, bind_superpose_skip _ s pre (g :: post) skip]
  simp [Search.superpose, Search.bind, Trace.bind, Trace.append, firing, fires, answers]

/-- **`once` over a transform where no proposal holds fires nothing.** -/
theorem once_transformWith_none {β : Type} (route : Answers → Search Store β) (src : Sources)
    (emit : Subst → Answers) (s : Store)
    (none : ∀ g ∈ proposals s src, fire s g src emit = none) :
    Search.once (transformWith route src emit) s = .done s := by
  have skip : ∀ g ∈ proposals s src, ((firing src emit g).bind route) s = .done s :=
    fun g hg => branch_skip (none g hg)
  unfold Search.once transformWith
  rw [← List.append_nil (proposals s src), bind_superpose_skip _ s _ [] skip]
  rfl

/-- **`once` into the store**: exactly the first proposal that holds fires, and the answer
is how many instances it routed, at the store of that single firing. -/
theorem once_transformInto (src : Sources) (template : Atom) (s : Store) {g : Footprint}
    {s₁ : Store} {out : Answers}
    (first : (proposals s src).find?
      (fun h => (fire s h src (instances template)).isSome) = some g)
    (fires : fire s g src (instances template) = some (s₁, out)) :
    Search.once (transformInto src template) s = .answer out.length (s₁ ++ out) .done :=
  once_transformWith intoStore src (instances template) s first fires rfl

/-- **`once` to the caller**: when the first proposal that holds fires an instance, that
instance is the answer, at the store of that single firing. -/
theorem once_transform (src : Sources) (template : Atom) (s : Store) {g : Footprint}
    {s₁ : Store} {a : Atom} {rest : Answers}
    (first : (proposals s src).find?
      (fun h => (fire s h src (instances template)).isSome) = some g)
    (fires : fire s g src (instances template) = some (s₁, a :: rest)) :
    Search.once (transform src template) s = .answer a s₁ .done :=
  once_transformWith toCaller src (instances template) s first fires rfl

/-! ## Law 1: reads alone -/

/-- Sources that only read: a pattern conjunction, optionally extended by `all`. -/
def readSources (ps : List Atom) (ext : Option (List Atom)) : Sources where
  kernel := ps.map (.pat .read)
  every := ext.map (List.map (.pat .read))

/-- A template headed by `,`: a conjunction of instances. -/
def IsComma (a : Atom) : Prop := ∃ items, a = .expression (.symbol "," :: items)

theorem split_of_not_comma {a : Atom} (plain : ¬ IsComma a) : split a = [a] := by
  rcases a with _ | _ | _ | _ | ⟨head, items⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rcases head with name | _ | _ | _
    · by_cases comma : name = ","
      · subst comma
        exact absurd ⟨items, rfl⟩ plain
      · simp [split, comma]
    all_goals rfl

theorem matchConj_append (s : Store) : ∀ (ps qs : List Atom) (σ : Subst),
    matchConj s σ (ps ++ qs) = (matchConj s σ ps).flatMap fun τ => matchConj s τ qs
  | [], qs, σ => by simp [matchConj]
  | p :: ps, qs, σ => by
      simp only [List.cons_append, matchConj, matchConj_append s ps qs, List.flatMap_assoc]

theorem walk_reads_fst (s : Store) (firing : Bool) : ∀ (ps : List Atom) (σ : Subst),
    (walk s firing σ (ps.map (.pat .read))).map Prod.fst = matchConj s σ ps
  | [], σ => rfl
  | p :: ps, σ => by
      simp only [List.map_cons, walk, List.map_flatMap, List.map_map, matchConj]
      congr 1
      funext r
      rw [← walk_reads_fst s firing ps r.1]
      rfl

theorem walk_reads_entries {s : Store} {firing : Bool} :
    ∀ {ps : List Atom} {σ : Subst} {w : Subst × Footprint},
      w ∈ walk s firing σ (ps.map (.pat .read)) → ∀ e ∈ w.2, e.1 = .read
  | [], σ, w, h => by
      simp only [List.map_nil, walk, List.mem_singleton] at h
      subst h
      simp
  | p :: ps, σ, w, h => by
      obtain ⟨r, -, v, hv, rfl⟩ := mem_walk_pat.mp h
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · rfl
      · exact walk_reads_entries hv e he

/-- On a ground store, a read-only proposal fires at the store it came from, once,
emitting for every extension of its bindings, and leaves the store as it is. -/
theorem fire_reads {s : Store} (ground : ∀ a ∈ s, isGroundAtom a = true) {ps : List Atom}
    {ext : Option (List Atom)} {emit : Subst → Answers} {σ : Subst} {g : Footprint}
    (proposed : (σ, g) ∈ walk s false [] (ps.map (.pat .read))) :
    fire s g (readSources ps ext) emit = some (s, (matchConj s σ (ext.getD [])).flatMap emit) := by
  obtain ⟨again, only⟩ := walk_guided_reads ground ps [] σ g proposed
  obtain ⟨w, ws, cons⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem again)
  have head : w = (σ, g) := only w (by rw [cons]; exact List.mem_cons_self ..)
  subst head
  have entries : ∀ e ∈ g, e.1 = .read := walk_reads_entries proposed
  cases ext with
  | none =>
      have cands : candidates s g (readSources ps none) =
          ⟨g, [(σ, [])]⟩ :: ws.map (fun k => ⟨k.2, [(k.1, [])]⟩) := by
        simp [candidates, readSources, cons]
      have allReads : ∀ x ∈ Candidate.footprint ⟨g, [(σ, [])]⟩, x.1 = .read := by
        simpa [Candidate.footprint] using entries
      rw [fire_of_first cands (valid_of_reads allReads s), commit_of_reads allReads]
      simp [Candidate.instances, matchConj]
  | some e =>
      have cands : candidates s g (readSources ps (some e)) =
          ⟨g, walk s true σ (e.map (.pat .read))⟩ ::
            ws.map (fun k => ⟨k.2, walk s true k.1 (e.map (.pat .read))⟩) := by
        simp [candidates, readSources, cons]
      have allReads : ∀ x ∈ Candidate.footprint ⟨g, walk s true σ (e.map (.pat .read))⟩,
          x.1 = .read := by
        intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact entries x hx
        · obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
          exact walk_reads_entries hv x hx
      rw [fire_of_first cands (valid_of_reads allReads s), commit_of_reads allReads]
      simp only [Candidate.instances, Option.getD_some, ← walk_reads_fst s true e σ,
        List.flatMap_map]

theorem foldl_branchStep_reads {s : Store} (ground : ∀ a ∈ s, isGroundAtom a = true)
    {ps : List Atom} {ext : Option (List Atom)} {emit : Subst → Answers} :
    ∀ (L : List (Subst × Footprint)),
      (∀ w ∈ L, w ∈ walk s false [] (ps.map (.pat .read))) → ∀ acc : Answers,
        (L.map Prod.snd).foldl (branchStep toCaller (readSources ps ext) emit) (acc, s) =
          (acc ++ (L.map Prod.fst).flatMap fun σ => (matchConj s σ (ext.getD [])).flatMap emit,
            s)
  | [], _, acc => by simp
  | w :: L, mem, acc => by
      have fired := fire_reads ground (ext := ext) (emit := emit) (mem w (List.mem_cons_self ..))
      simp only [List.map_cons, List.foldl_cons, branchStep, fired, toCaller_drain]
      rw [foldl_branchStep_reads ground L (fun v hv => mem v (List.mem_cons_of_mem _ hv))]
      simp

/-- **Law 1: reads alone.** On a ground store, a transform whose sources only read answers,
in order and with every duplicate, the instances under the matches `match` gives on the same
pattern conjunction (an `all` extension included); the store is unchanged. -/
theorem transform_reads (s : Store) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (ps : List Atom) (ext : Option (List Atom)) (template : Atom) :
    (transform (readSources ps ext) template s).drain =
      ((matchConj s [] (ps ++ ext.getD [])).flatMap (instances template), s) := by
  rw [transform, transformWith_drain]
  have := foldl_branchStep_reads ground (ext := ext) (emit := instances template)
    (walk s false [] (ps.map (.pat .read))) (fun w hw => hw) []
  simp only [proposals, readSources] at this ⊢
  rw [this, walk_reads_fst, matchConj_append]
  simp [List.flatMap_assoc]

/-- **Law 1, for a template that is not a conjunction**: exactly the answers of `match`,
duplicates and order included, on an unchanged store. -/
theorem transform_reads_eq_match (s : Store) (ground : ∀ a ∈ s, isGroundAtom a = true)
    (ps : List Atom) (ext : Option (List Atom)) (template : Atom) (plain : ¬ IsComma template) :
    (transform (readSources ps ext) template s).drain =
      (matchAnswers s (ps ++ ext.getD []) template, s) := by
  have single : instances template = fun σ => [applySubst σ template] := by
    funext σ
    simp [instances, split_of_not_comma plain]
  rw [transform_reads s ground, matchAnswers, single, ← List.map_eq_flatMap]

/-! ## Law 5: `all` and `collect` takes -/

/-- `(, (all (take p)))`. -/
def allTake (p : Atom) : Sources where
  kernel := []
  every := some [.pat .take p]

/-- `(collect (take p) C)`. -/
def collectTake (p : Atom) (C : String) : Sources where
  kernel := [.collect .take (.one p) (.var C)]

theorem matchesIn_snd (s : Store) (σ : Subst) (p : Atom) :
    (matchesIn s σ p).map Prod.snd = s.filter fun b => (matchAtom σ p b).isSome := by
  induction s with
  | nil => rfl
  | cons b s ih =>
      cases h : matchAtom σ p b with
      | none =>
          simp only [matchesIn, List.filterMap_cons, h, Option.map_none] at ih ⊢
          simp [h, ih]
      | some τ =>
          simp only [matchesIn, List.filterMap_cons, h, Option.map_some] at ih ⊢
          simp [h, ih]

theorem applyTakes_filter (all : Footprint) (s : Store)
    (copies : ∀ a, (Mode.take, a) ∈ all → all.count (.take, a) = s.count a) :
    ∀ (todo : Footprint) (done : List Atom), (∀ e ∈ todo, e ∈ all) →
      applyTakes all todo done (s.filter fun b => decide (b ∉ done)) =
        s.filter fun b => decide (b ∉ done ∧ (Mode.take, b) ∉ todo)
  | [], done, _ => by simp [applyTakes]
  | (m, a) :: more, done, sub => by
      simp only [applyTakes]
      split
      · rename_i fresh
        obtain ⟨rfl, notDone⟩ := fresh
        have here : (Mode.take, a) ∈ all := sub _ (List.mem_cons_self ..)
        have stays : (s.filter fun b => decide (b ∉ done)).count a = s.count a :=
          List.count_filter (p := fun b => decide (b ∉ done)) (by simpa using notDone)
        have step : commitOne (s.filter fun b => decide (b ∉ done)) a (all.count (.take, a)) =
            s.filter fun b => decide (b ∉ a :: done) := by
          unfold commitOne
          rw [stays, copies a here, Nat.sub_self, List.replicate_zero, List.append_nil,
            List.filter_filter]
          apply List.filter_congr
          intro b _
          by_cases h : b = a <;> simp [h]
        rw [step, applyTakes_filter all s copies more (a :: done)
          (fun e he => sub e (List.mem_cons_of_mem _ he))]
        apply List.filter_congr
        intro b _
        by_cases h : b = a <;> simp [h]
      · rename_i old
        rw [applyTakes_filter all s copies more done
          (fun e he => sub e (List.mem_cons_of_mem _ he))]
        apply List.filter_congr
        intro b _
        by_cases h : b ∈ done
        · simp [h]
        · have : (Mode.take, b) ≠ (m, a) := by
            intro same
            simp only [Prod.mk.injEq] at same
            obtain ⟨rfl, rfl⟩ := same
            exact old ⟨rfl, h⟩
          simp [h, this]

/-- A footprint that takes every copy of the atoms satisfying `P`, in any order and with no
reads, validates and leaves exactly the store without them, in order. -/
theorem valid_commit_of_takes_perm {s : Store} {fp : Footprint} {P : Atom → Bool}
    (onlyTakes : ∀ e ∈ fp, e.1 = .take) (taken : (takes fp).Perm (s.filter P)) :
    valid s fp = true ∧ commit fp s = s.filter fun b => !P b := by
  have noReads : reads fp = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro a ha
    have := onlyTakes _ (mem_reads.mp ha)
    cases this
  have copies : ∀ a, (Mode.take, a) ∈ fp → fp.count (.take, a) = s.count a := by
    intro a ha
    have inFilter : a ∈ s.filter P := taken.subset (mem_takes.mpr ha)
    rw [count_take_eq, taken.count_eq]
    exact List.count_filter (List.mem_filter.mp inFilter).2
  constructor
  · rw [valid_iff, noReads]
    intro a ha
    have inFilter : a ∈ s.filter P := taken.subset ha
    rw [taken.count_eq, List.count_filter (List.mem_filter.mp inFilter).2]
    simp
  · have start : s = s.filter fun b => decide (b ∉ ([] : List Atom)) := by simp
    rw [commit]
    conv => lhs; rw [start]
    rw [applyTakes_filter fp s copies fp [] (fun _ h => h)]
    apply List.filter_congr
    intro b hb
    have : (Mode.take, b) ∈ fp ↔ P b = true := by
      rw [← mem_takes, taken.mem_iff, List.mem_filter]
      simp [hb]
    simp only [List.not_mem_nil, not_false_eq_true, true_and, this]
    cases P b <;> rfl

/-- A footprint whose takes are every copy of the atoms satisfying `P`, in store order, and
which reads nothing, validates and leaves exactly the store without them, in order. -/
theorem valid_commit_of_takes_filter {s : Store} {fp : Footprint} {P : Atom → Bool}
    (onlyTakes : ∀ e ∈ fp, e.1 = .take) (taken : takes fp = s.filter P) :
    valid s fp = true ∧ commit fp s = s.filter fun b => !P b :=
  valid_commit_of_takes_perm onlyTakes (taken ▸ List.Perm.refl _)

theorem walk_take (s : Store) (firing : Bool) (σ : Subst) (p : Atom) :
    walk s firing σ [.pat .take p] = (matchesIn s σ p).map fun r => (r.1, [(.take, r.2)]) := by
  simp [walk, List.map_eq_flatMap]

theorem takes_matched (s : Store) (σ : Subst) (p : Atom) :
    takes ((matchesIn s σ p).map fun r => (Mode.take, r.2)) =
      s.filter fun b => (matchAtom σ p b).isSome := by
  rw [takes_map_take, matchesIn_snd]

theorem only_takes_matched (s : Store) (σ : Subst) (p : Atom) :
    ∀ e ∈ (matchesIn s σ p).map (fun r => (Mode.take, r.2)), e.1 = .take := by
  intro e he
  obtain ⟨r, -, rfl⟩ := List.mem_map.mp he
  rfl

/-- **Law 5, `all`.** A firing with `(all (take p))` takes every stored match of `p` in its
one commit, leaving exactly the store without them, and answers one instance per match. -/
theorem fire_all_take (s : Store) (p : Atom) (emit : Subst → Answers) :
    fire s [] (allTake p) emit =
      some (s.filter (fun b => !(matchAtom [] p b).isSome),
        (matchesIn s [] p).flatMap fun r => emit r.1) := by
  have cands : candidates s [] (allTake p) = [⟨[], walk s true [] [.pat .take p]⟩] := rfl
  have fp : Candidate.footprint ⟨[], walk s true [] [.pat .take p]⟩ =
      (matchesIn s [] p).map fun r => (Mode.take, r.2) := by
    simp [Candidate.footprint, walk_take, List.map_eq_flatMap, List.flatMap_assoc]
  obtain ⟨ok, committed⟩ :=
    valid_commit_of_takes_filter (only_takes_matched s [] p) (takes_matched s [] p)
  rw [← fp] at ok committed
  rw [fire_of_first cands ok, committed]
  simp [Candidate.instances, walk_take, List.flatMap_map]

theorem bind_collection (s : Store) (p : Atom) (C : String) :
    matchAtom [] (.var C) (.expression ((matchesIn s [] p).map Prod.snd)) =
      some [(C, .expression ((matchesIn s [] p).map Prod.snd))] := by
  simp [matchAtom, Subst.lookup]

/-- **Law 5, `collect`.** A firing with `(collect (take p) C)` takes every stored match of
`p` in its one commit, leaving exactly the store without them, and binds `C` to their list,
in store order. -/
theorem fire_collect_take (s : Store) (p : Atom) (C : String) (emit : Subst → Answers) :
    fire s [] (collectTake p C) emit =
      some (s.filter (fun b => !(matchAtom [] p b).isSome),
        emit [(C, .expression (s.filter fun b => (matchAtom [] p b).isSome))]) := by
  have cands : candidates s [] (collectTake p C) =
      [⟨(matchesIn s [] p).map (fun r => (Mode.take, r.2)),
        [([(C, .expression ((matchesIn s [] p).map Prod.snd))], [])]⟩] := by
    simp only [candidates, collectTake, guided, List.append_nil, walk_collect_one,
      bind_collection]
    simp [walk]
  have fp : Candidate.footprint ⟨(matchesIn s [] p).map (fun r => (Mode.take, r.2)),
      [([(C, .expression ((matchesIn s [] p).map Prod.snd))], [])]⟩ =
      (matchesIn s [] p).map fun r => (Mode.take, r.2) := by
    simp [Candidate.footprint]
  obtain ⟨ok, committed⟩ :=
    valid_commit_of_takes_filter (only_takes_matched s [] p) (takes_matched s [] p)
  rw [← fp] at ok committed
  rw [fire_of_first cands ok, committed]
  simp [Candidate.instances, matchesIn_snd]

/-- **Law 5 at the call, `all`.** A transform whose sources are `(all (take p))` has one
branch: it takes every stored match of `p`, answers one instance per match, and leaves
exactly the store without them. -/
theorem transform_all_take (s : Store) (p template : Atom) :
    (transform (allTake p) template s).drain =
      ((matchesIn s [] p).flatMap (fun r => instances template r.1),
        s.filter fun b => !(matchAtom [] p b).isSome) := by
  have props : proposals s (allTake p) = [[]] := rfl
  rw [transform, transformWith_drain, props]
  simp only [List.foldl_cons, List.foldl_nil, branchStep, fire_all_take, toCaller_drain,
    List.nil_append]

/-- **Law 5 at the call, `collect`.** A transform whose sources are `(collect (take p) C)`
has one branch: it takes every stored match of `p` and answers the template with `C` bound to
their list, leaving exactly the store without them. -/
theorem transform_collect_take (s : Store) (p template : Atom) (C : String) :
    (transform (collectTake p C) template s).drain =
      (instances template [(C, .expression (s.filter fun b => (matchAtom [] p b).isSome))],
        s.filter fun b => !(matchAtom [] p b).isSome) := by
  have props : proposals s (collectTake p C) = [[]] := by
    simp [proposals, collectTake, walk_collect_one, bind_collection, walk]
  rw [transform, transformWith_drain, props]
  simp only [List.foldl_cons, List.foldl_nil, branchStep, fire_collect_take, toCaller_drain,
    List.nil_append]

/-! ## Law 6: conditions over joint matches -/

/-- **`absent` holds iff its query has no joint match**, that is, iff `match` on the
conjunction of its parts answers nothing. -/
theorem walk_absent (s : Store) (firing : Bool) (σ : Subst) (q : Query) (cs : List Conj) :
    walk s firing σ (.absent q :: cs) =
      if matchConj s σ q.parts = [] then walk s firing σ cs else [] := by
  simp only [walk, jointIn_eq_nil_iff]

/-- A branch whose kernel is `(absent q)` fires, keeping the store, iff `q` has no joint match
in the store it finds. -/
theorem fire_absent (s : Store) (q : Query) (emit : Subst → Answers) :
    fire s [] { kernel := [.absent q] } emit =
      if matchConj s [] q.parts = [] then some (s, emit []) else none := by
  by_cases none : matchConj s [] q.parts = []
  · have cands : candidates s [] { kernel := [.absent q] } = [⟨[], [([], [])]⟩] := by
      simp [candidates, guided, walk_absent, none, walk]
    rw [fire_of_first cands rfl, if_pos none]
    simp [Candidate.footprint, Candidate.instances, commit, applyTakes]
  · have cands : candidates s [] { kernel := [.absent q] } = [] := by
      simp [candidates, guided, walk_absent, none]
    simp [fire, cands, none]

/-- **Law 6, `absent` at the call.** `(absent q)` answers the template once, on an unchanged
store, iff `q` has no joint match; otherwise it answers nothing. -/
theorem transform_absent (s : Store) (q : Query) (template : Atom) :
    (transform { kernel := [.absent q] } template s).drain =
      (if matchConj s [] q.parts = [] then instances template [] else [], s) := by
  rw [transform, transformWith_drain]
  by_cases none : matchConj s [] q.parts = []
  · have props : proposals s { kernel := [.absent q] } = [[]] := by
      rw [proposals, walk_absent, if_pos none]
      rfl
    rw [props, if_pos none]
    simp [branchStep, fire_absent, none]
  · have props : proposals s { kernel := [.absent q] } = [] := by
      rw [proposals, walk_absent, if_neg none]
      rfl
    rw [props, if_neg none]
    rfl

/-- **`unique` proposes iff its query has exactly one joint tuple**, and the proposal's
guide is that tuple's parts in order, with the conjunct's access mode. -/
theorem proposals_unique (s : Store) (m : Mode) (q : Query) :
    proposals s { kernel := [.unique m q] } =
      match jointIn s [] q.parts with
      | [t] => [t.2.map fun a => (m, a)]
      | _ => [] := by
  simp only [proposals, walk]
  cases jointIn s [] q.parts with
  | nil => rfl
  | cons t ts =>
      cases ts with
      | nil => simp
      | cons => rfl

theorem guided_unique (m : Mode) (q : Query) (g : Footprint) (len : g.length = q.parts.length) :
    guided [.unique m q] g = .unique m q :: asParts q.parts (g.map Prod.snd) := by
  simp [guided, ← len]

/-- **A joint `unique` is counted again when its branch fires.** A branch whose kernel is
`(unique q)`, guided by a tuple of atoms, fires iff `q` has exactly one joint tuple in the store
it finds, that tuple is the guide's, and its footprint, the tuple's parts with the conjunct's
access mode, validates. -/
theorem fire_unique_joint (s : Store) (m : Mode) (q : Query) (g : Footprint)
    (emit : Subst → Answers) (len : g.length = q.parts.length) :
    fire s g { kernel := [.unique m q] } emit =
      match jointIn s [] q.parts with
      | [t] =>
          if t.2 = g.map Prod.snd ∧ valid s (t.2.map fun a => (m, a)) = true then
            some (commit (t.2.map fun a => (m, a)) s, emit t.1)
          else none
      | _ => none := by
  have guide := guided_unique m q g len
  cases found : jointIn s [] q.parts with
  | nil => simp [fire, candidates, guide, walk, found]
  | cons t ts =>
      cases ts with
      | cons t' ts => simp [fire, candidates, guide, walk, found]
      | nil =>
          have ht : t ∈ jointIn s [] q.parts := by rw [found]; exact List.mem_singleton_self t
          have chain := walk_asParts (s := s) (firing := true) ht (Subst.lookupExtends_refl _)
            (g.map Prod.snd) (by simp [len]) []
          rw [List.append_nil] at chain
          have cands : candidates s g { kernel := [.unique m q] } =
              if g.map Prod.snd = t.2 then [⟨t.2.map (fun a => (m, a)), [(t.1, [])]⟩]
              else [] := by
            simp only [candidates, guide, List.append_nil, walk, found, chain]
            split <;> simp
          rw [fire, cands]
          by_cases same : g.map Prod.snd = t.2
          · rw [if_pos same]
            by_cases ok : valid s (t.2.map fun a => (m, a)) = true
            · simp [same, ok, Candidate.footprint, Candidate.instances]
            · simp [same, ok, Candidate.footprint]
          · rw [if_neg same]
            simp [Ne.symm same]

@[simp] theorem takes_map_take_self (t : List Atom) :
    takes (t.map fun a => (Mode.take, a)) = t := by
  induction t with
  | nil => rfl
  | cons a t ih => simp [ih]

@[simp] theorem reads_map_take_self (t : List Atom) :
    reads (t.map fun a => (Mode.take, a)) = [] := by
  induction t with
  | nil => rfl
  | cons a t ih => simp [ih]

/-- **Takes need distinct occurrences.** Taking the atoms of a tuple validates exactly when
the tuple fits the store. -/
theorem valid_map_take (s : Store) (t : List Atom) :
    valid s (t.map fun a => (Mode.take, a)) = fits s t := by
  rw [Bool.eq_iff_iff, valid_iff, fits, List.all_eq_true]
  simp

/-- **Reads may meet one occurrence at several parts.** Reading the atoms of a tuple always
validates. -/
theorem valid_map_read (s : Store) (t : List Atom) :
    valid s (t.map fun a => (Mode.read, a)) = true :=
  valid_of_reads (fun e he => by obtain ⟨a, -, rfl⟩ := List.mem_map.mp he; rfl) s

/-- **Law 6, joint `unique` at the call.** `(unique q)` has one branch iff `q` has exactly one
joint tuple; that branch fires at the call iff the tuple's footprint validates, answering the
template under the tuple's bindings and committing exactly that footprint. -/
theorem transform_unique (s : Store) (m : Mode) (q : Query) (template : Atom) :
    (transform { kernel := [.unique m q] } template s).drain =
      match jointIn s [] q.parts with
      | [t] =>
          if valid s (t.2.map fun a => (m, a)) = true then
            (instances template t.1, commit (t.2.map fun a => (m, a)) s)
          else ([], s)
      | _ => ([], s) := by
  rw [transform, transformWith_drain, proposals_unique]
  cases found : jointIn s [] q.parts with
  | nil => rfl
  | cons t ts =>
      cases ts with
      | cons => rfl
      | nil =>
          have ht : t ∈ jointIn s [] q.parts := by rw [found]; exact List.mem_singleton_self t
          have fired := fire_unique_joint s m q (t.2.map fun a => (m, a)) (instances template)
            (by simp [(jointIn_sound ht).2.1])
          rw [found] at fired
          simp only [List.map_map, Function.comp_def, List.map_id', true_and] at fired
          simp only [List.foldl_cons, List.foldl_nil, branchStep, fired]
          by_cases ok : valid s (t.2.map fun a => (m, a)) = true <;> simp [ok]

/-- **Atomicity of a joint `unique` take.** When the query has exactly one joint tuple and it
fits, the transform commits exactly the tuple: the store it leaves, plus the tuple's atoms, is
the store it found. When the tuple does not fit, nothing fires. -/
theorem transform_unique_take (s : Store) (q : Query) (template : Atom)
    {t : Subst × List Atom} (one : jointIn s [] q.parts = [t]) :
    (fits s t.2 = true →
      (transform { kernel := [.unique .take q] } template s).drain =
          (instances template t.1, commit (t.2.map fun a => (Mode.take, a)) s) ∧
        (s : Multiset Atom) =
          (commit (t.2.map fun a => (Mode.take, a)) s : Multiset Atom) + (t.2 : Multiset Atom)) ∧
    (fits s t.2 = false →
      (transform { kernel := [.unique .take q] } template s).drain = ([], s)) := by
  refine ⟨fun fit => ?_, fun unfit => ?_⟩
  · have ok : valid s (t.2.map fun a => (Mode.take, a)) = true := by rw [valid_map_take]; exact fit
    refine ⟨by rw [transform_unique, one]; simp [ok], ?_⟩
    have conserved := commit_add_takes ok
    rwa [takes_map_take_self] at conserved
  · have bad : valid s (t.2.map fun a => (Mode.take, a)) = false := by
      rw [valid_map_take]; exact unfit
    rw [transform_unique, one]
    simp [bad]

/-- **`collect` binds its variable to the joint matches at firing.** A branch whose kernel is
a read-mode `(collect q C)` fires on any store, keeps it, and binds `C` to the joint matches of
`q` in the store it finds, all of them, in order. -/
theorem fire_collect_read_joint (s : Store) (q : Query) (C : String) (emit : Subst → Answers) :
    fire s [] { kernel := [.collect .read q (.var C)] } emit =
      some (s, emit [(C, q.collection ((jointIn s [] q.parts).map Prod.snd))]) := by
  have bind : ∀ v : Atom, matchAtom [] (.var C) v = some [(C, v)] := fun v => by
    simp [matchAtom, Subst.lookup]
  have cands : candidates s [] { kernel := [.collect .read q (.var C)] } =
      [⟨[], [([(C, q.collection ((jointIn s [] q.parts).map Prod.snd))], [])]⟩] := by
    simp only [candidates, guided, List.append_nil, walk, collected_eq_jointIn (Or.inl rfl),
      bind, collectTakes_read]
    simp
  rw [fire_of_first cands rfl]
  simp [Candidate.footprint, Candidate.instances, commit, applyTakes]

theorem count_eraseDups : ∀ (l : List Atom) (x : Atom),
    l.eraseDups.count x = if x ∈ l then 1 else 0
  | [], x => by simp
  | a :: as, x => by
      have : (as.filter fun b => !b == a).length < as.length + 1 :=
        Nat.lt_succ_of_le (List.length_filter_le _ _)
      rw [List.eraseDups_cons, List.count_cons, count_eraseDups _ x]
      by_cases h : x = a
      · subst h
        simp
      · have : (a == x) = false := by simpa using Ne.symm h
        simp [h, this, List.mem_filter]
termination_by l => l.length

theorem count_flatMap_replicate (L : List Atom) (n : Atom → Nat) (x : Atom) :
    (L.flatMap fun a => List.replicate (n a) a).count x = L.count x * n x := by
  induction L with
  | nil => simp
  | cons a L ih =>
      rw [List.flatMap_cons, List.count_append, ih, List.count_replicate, List.count_cons]
      by_cases h : a = x
      · subst h
        simp [Nat.add_mul, Nat.add_comm]
      · have : (a == x) = false := by simpa using h
        simp [this]

theorem takes_replicate_take (n : Nat) (a : Atom) :
    takes (List.replicate n (Mode.take, a)) = List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

/-- **A take-mode `collect` over a conjunction takes every stored copy of each participating
atom, and nothing else**: its takes are, as a multiset, the stored atoms that occur in some
tuple. -/
theorem takes_collect_conj (s : Store) (ps : List Atom) (ts : List (List Atom)) :
    (takes (collectTakes s true .take (.conj ps) ts)).Perm
      (s.filter fun b => decide (b ∈ ts.flatten)) := by
  have shape : ∀ L : List Atom,
      takes (L.flatMap fun a => List.replicate (s.count a) (Mode.take, a)) =
        L.flatMap fun a => List.replicate (s.count a) a := by
    intro L
    induction L with
    | nil => rfl
    | cons a L ih => simp [List.flatMap_cons, ih, takes_replicate_take]
  simp only [collectTakes]
  rw [shape, List.perm_iff_count]
  intro x
  rw [count_flatMap_replicate, participants, count_eraseDups]
  by_cases hx : x ∈ ts.flatten
  · rw [if_pos hx, List.count_filter (by simpa using hx)]
    simp
  · rw [if_neg hx, Nat.zero_mul, eq_comm, List.count_eq_zero]
    intro member
    exact hx (by simpa using (List.mem_filter.mp member).2)

/-- `(collect (take (, p1 ... pn)) C)`. -/
def collectTakeJoint (ps : List Atom) (C : String) : Sources where
  kernel := [.collect .take (.conj ps) (.var C)]

/-- The tuples a take-mode `collect` over `ps` keeps from the store `s`: the joint matches
that fit, in order. -/
def keptTuples (s : Store) (ps : List Atom) : List (List Atom) :=
  (collected s [] .take (.conj ps)).map Prod.snd

/-- **Law 6, joint `collect` take.** A firing with `(collect (take (, p1 ... pn)) C)` keeps the
joint tuples that fit, binds `C` to their list, and takes every stored copy of each atom that
takes part in one of them, leaving exactly the store without those atoms, in order. -/
theorem fire_collect_take_joint (s : Store) (ps : List Atom) (C : String)
    (emit : Subst → Answers) :
    fire s [] (collectTakeJoint ps C) emit =
      some (s.filter (fun b => !decide (b ∈ (keptTuples s ps).flatten)),
        emit [(C, (Query.conj ps).collection (keptTuples s ps))]) := by
  have bind : ∀ v : Atom, matchAtom [] (.var C) v = some [(C, v)] := fun v => by
    simp [matchAtom, Subst.lookup]
  have cands : candidates s [] (collectTakeJoint ps C) =
      [⟨collectTakes s true .take (.conj ps) (keptTuples s ps),
        [([(C, (Query.conj ps).collection (keptTuples s ps))], [])]⟩] := by
    simp only [candidates, collectTakeJoint, guided, List.append_nil, walk, bind, keptTuples]
    simp
  have fp : Candidate.footprint ⟨collectTakes s true .take (.conj ps) (keptTuples s ps),
      [([(C, (Query.conj ps).collection (keptTuples s ps))], [])]⟩ =
      collectTakes s true .take (.conj ps) (keptTuples s ps) := by
    simp [Candidate.footprint]
  obtain ⟨ok, committed⟩ := valid_commit_of_takes_perm (fun e he => (mem_collectTakes he).1)
    (takes_collect_conj s ps (keptTuples s ps))
  rw [← fp] at ok committed
  rw [fire_of_first cands ok, committed]
  simp [Candidate.instances]

/-- **Atomicity of a joint `collect` take.** Its firing moves the store, in one step, to the
old multiset minus exactly the stored copies of the participating atoms. -/
theorem fire_collect_take_joint_conserves (s : Store) (ps : List Atom) (C : String)
    (emit : Subst → Answers) {s' : Store} {out : Answers}
    (fired : fire s [] (collectTakeJoint ps C) emit = some (s', out)) :
    (s : Multiset Atom) =
      (s' : Multiset Atom) +
        (s.filter fun b => decide (b ∈ (keptTuples s ps).flatten) : List Atom) := by
  rw [fire_collect_take_joint] at fired
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj fired)
  rw [Multiset.coe_add, Multiset.coe_eq_coe]
  exact (List.perm_append_comm.trans (List.filter_append_perm _ s)).symm

/-- **Law 6, joint `collect` take at the call.** A transform whose sources are
`(collect (take (, p1 ... pn)) C)` has one branch: it answers the template with `C` bound to
the fitting joint tuples and leaves exactly the store without their atoms. -/
theorem transform_collect_take_joint (s : Store) (ps : List Atom) (template : Atom)
    (C : String) :
    (transform (collectTakeJoint ps C) template s).drain =
      (instances template [(C, (Query.conj ps).collection (keptTuples s ps))],
        s.filter fun b => !decide (b ∈ (keptTuples s ps).flatten)) := by
  have props : proposals s (collectTakeJoint ps C) = [[]] := by
    simp [proposals, collectTakeJoint, walk, matchAtom, Subst.lookup]
  rw [transform, transformWith_drain, props]
  simp only [List.foldl_cons, List.foldl_nil, branchStep, fire_collect_take_joint, toCaller_drain,
    List.nil_append]

/-- A take-mode `collect` over a one-part conjunction `(, p)` leaves the store that
`(collect (take p) C)` leaves (`fire_collect_take`), and binds the list of one-part tuples
`(, a)` of the atoms the pattern collects. -/
theorem fire_collect_take_conj_single (s : Store) (p : Atom) (C : String)
    (emit : Subst → Answers) :
    fire s [] (collectTakeJoint [p] C) emit =
      some (s.filter (fun b => !(matchAtom [] p b).isSome),
        emit [(C, .expression ((s.filter fun b => (matchAtom [] p b).isSome).map
          fun a => .expression [.symbol ",", a]))]) := by
  have kept : keptTuples s [p] = (matchesIn s [] p).map fun r => [r.2] := by
    rw [keptTuples, collected_conj_single]
    simp only [collected, jointIn_one, List.map_map]
    rfl
  have flat : (keptTuples s [p]).flatten = s.filter fun b => (matchAtom [] p b).isSome := by
    rw [kept, flatten_map_singleton, ← matchesIn_snd]
  rw [fire_collect_take_joint, flat]
  congr 2
  · apply List.filter_congr
    intro b hb
    simp [List.mem_filter, hb]
  · rw [kept, ← matchesIn_snd]
    simp [Query.collection, List.map_map, Function.comp_def]

/-! ## Conditions are those of the store at firing -/

theorem valid_single {s : Store} {m : Mode} {a : Atom} (stored : a ∈ s) :
    valid s [(m, a)] = true := by
  cases m with
  | read => rfl
  | take =>
      rw [valid_iff]
      simpa using List.count_pos_iff.mpr stored

/-- **`unique` is counted again when the branch fires.** A branch whose kernel is
`(unique p)` fires exactly when `p` has one match in the store it finds and that match is
the atom of its proposal. -/
theorem fire_unique (s : Store) (m m' : Mode) (p a : Atom) (emit : Subst → Answers) :
    fire s [(m', a)] { kernel := [.unique m (.one p)] } emit =
      match matchesIn s [] p with
      | [r] => if r.2 = a then some (commit [(m, a)] s, emit r.1) else none
      | _ => none := by
  rw [fire_unique_joint s m (.one p) [(m', a)] emit rfl]
  simp only [Query.parts, jointIn_one]
  cases found : matchesIn s [] p with
  | nil => rfl
  | cons r rs =>
      cases rs with
      | cons => rfl
      | nil =>
          have stored : r.2 ∈ s := (mem_matchesIn.mp (found ▸ List.mem_singleton_self r)).1
          by_cases same : r.2 = a
          · subst same
            simp [valid_single (m := m) stored]
          · simp [same]

/-- **`collect` binds its variable to the list at firing.** A branch whose kernel is a
read-mode `(collect p C)` fires on any store, keeps it, and answers with `C` bound to the
matches of `p` in the store it finds. -/
theorem fire_collect_read (s : Store) (p : Atom) (C : String) (emit : Subst → Answers) :
    fire s [] { kernel := [.collect .read (.one p) (.var C)] } emit =
      some (s, emit [(C, .expression (s.filter fun b => (matchAtom [] p b).isSome))]) := by
  rw [fire_collect_read_joint]
  simp only [Query.collection, Query.parts, jointIn_one, List.map_map, Function.comp_def,
    flatten_map_singleton, ← matchesIn_snd]

/-! ## Source-level `once` -/

/-- `(, (once (take p)))`. -/
def onceTake (p : Atom) : Sources where
  kernel := []
  choice := [.pat .take p]

/-- **`(once (take p))` takes one copy of the first match.** Within the firing, the first
match of `p` validates; it alone fires, taking one copy of its atom. -/
theorem fire_once_take (s : Store) (p : Atom) (emit : Subst → Answers) :
    fire s [] (onceTake p) emit =
      match matchesIn s [] p with
      | [] => none
      | r :: _ => some (commitOne s r.2 1, emit r.1) := by
  cases found : matchesIn s [] p with
  | nil => simp [fire, candidates, onceTake, guided, walk_take, found]
  | cons r rs =>
      have stored : r.2 ∈ s := (mem_matchesIn.mp (found ▸ List.mem_cons_self ..)).1
      have cands : candidates s [] (onceTake p) =
          ⟨[(Mode.take, r.2)], [(r.1, [])]⟩ ::
            rs.map (fun r' => ⟨[(Mode.take, r'.2)], [(r'.1, [])]⟩) := by
        simp [candidates, onceTake, guided, walk_take, found]
      have ok : valid s (Candidate.footprint ⟨[(Mode.take, r.2)], [(r.1, [])]⟩) = true := by
        simpa [Candidate.footprint] using valid_single (m := .take) stored
      rw [fire_of_first cands ok]
      simp [Candidate.footprint, Candidate.instances, commit, applyTakes]

end Mettapedia.Languages.MeTTa.PeTTa.LibTransform
