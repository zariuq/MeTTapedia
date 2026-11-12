import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.Dedup
import Mathlib.Logic.Relation
import Mettapedia.Protocols.Agents.EvidenceHandoff

/-!
# A skeleton index of the git checkouts on a machine

A fact store keeps a small, durable set of facts about every git checkout on a machine;
an indexer refreshes it on a timer, and agents query it. It answers where a repo is
checked out, which repo and branches hold a commit, whether one commit is merged into
another, and what changed since a given time. Git stays the truth: diffs, file histories
and searches remain live git calls.

**The model.**
- A commit id is a hash of the commit's content, parents included, so the id fixes the
  parents: `par c`, in every store and at every refresh. Git's ancestry,
  `Ancestor (Parent par)`, is what `git merge-base --is-ancestor` answers.
- The index stores commits and parent facts. A commit is stored with the parents its
  commit object lists; a shallow clone keeps these for its boundary commits too
  (`Faithful`). A stored commit with a parent that is not stored is a *boundary* commit:
  the edge of a shallow clone, or history not read yet.
- Heads are kept as a journal. Each refresh appends one event per ref whose head
  changed, with the old and the new head; either is absent for a ref created or deleted.
  A ref is a branch of a store, or a checkout's `HEAD`.
- A refresh reads a visit: the refs git shows, their heads and the commits it lists.
- The other fields of the facts (a checkout's path and account, a store's repo and
  origin, a commit's time, author and subject) carry no law here and are left out.

**Exactness.** An index yes is a git yes (`Index.sound`). When `b` is stored and no
boundary commit is reachable from it, an index no is a git no (`Index.complete`,
`Index.exact_iff`, `Index.closed_iff`). A shallow clone shows that this hypothesis is
needed (`shallow_answer_changes`).

**Permanence.** Commits and parent facts only accumulate (`Index.subset_refresh`). A yes
stays a yes (`Index.ancestor_mono`). A closed walk stays closed and its answers never
change (`Index.closed_mono`, `Index.answer_stable`). An answer whose walk meets a
boundary commit can change once the missing history is read.

**Generation numbers** (`IsGen`), as git's commit-graph keeps them: a root has generation
1, any other commit one more than the largest among its parents. A proper ancestor has a
smaller generation (`gen_lt_of_ancestor`), so a walk looking for `a` may skip every
commit below `a`'s generation (`prune_sound`, `Index.prune_index`). The generations the
index computes from its own facts are git's on closed walks (`Index.gen_eq`), so they
never change across refreshes (`Index.gen_stable`).

**Snapshots.** The journal replayed from the empty map is exactly the heads of the last
visit (`Index.heads_refresh`, `Index.heads_run`). A refresh appends one event for each
ref whose head changed and no other (`Index.mem_events`, `Index.events_nodup`). The
events since a time `T` turn the heads as of `T` into the current heads, and every ref
whose head differs has one (`replay_since`, `changed_mem_since`, `Index.run_since`).
Force-moves and deletions are included; commit times cannot show them, since a refresh
that reads no new commit leaves the commits as they were (`Index.commits_of_known`).
The events since a later time are a suffix of those since an earlier one
(`since_antitone`).
An answer about a ref is a versioned claim (`Index.claim`): its source is the ref and its
version the head the index recorded. It is about the head of the refresh that recorded
it (`Index.claim_refresh`), holds while the ref has not moved
(`Index.claim_holds_while_unmoved`) and is stale exactly when it has
(`Index.claim_stale_iff_moved`). On a closed walk a merge answer is exactly the claim
(`Index.merged_iff`).

**Refresh laws.** A refresh depends on what it reads only through the stored commits that
result (`Index.refresh_congr`). An incremental refresh asks git only for the commits not
reachable from some stop commits (`git rev-list <heads> --not <stops>`); it equals a full
refresh when the walk from every stop commit is closed (`Index.incremental_eq_full`). A
boundary commit is not a safe stop. A run of safe refreshes equals the run of full ones
(`Index.run_eq_full`), which holds exactly the commits some visit listed, with their
parent facts, and the last visit's heads (`Index.mem_run_full`, `Index.faithful_run`,
`Index.heads_run`). Refreshing again against the same visit changes nothing
(`Index.refresh_idem`). Rebuilding from git restores the heads and every commit git
still lists; the journal, and commits that git no longer has, are the index's own record.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Repos.GitSkeleton

open Relation
open Mettapedia.Protocols.Agents.EvidenceHandoff

/-! ## Commits -/

section Commits

variable {Sha : Type}

/-- `a` is an ancestor of `b` along the parent relation `E` (`E c p`: `p` is a parent of
`c`): following parents from `b` reaches `a`. A commit is its own ancestor, as for
`git merge-base --is-ancestor`. -/
abbrev Ancestor (E : Sha → Sha → Prop) (a b : Sha) : Prop := ReflTransGen E b a

/-- Git's parent relation. A commit id hashes the commit's content, parents included, so
the id fixes the parents: `par c`, in every store and at every refresh. -/
def Parent (par : Sha → Finset Sha) (c p : Sha) : Prop := p ∈ par c

/-- `a` is merged into a ref with head `h`: the ref exists and `a` is a git ancestor of
its head. -/
def Merged (par : Sha → Finset Sha) (a : Sha) (h : Option Sha) : Prop :=
  ∃ b, h = some b ∧ Ancestor (Parent par) a b

/-- Ancestry along a smaller relation is ancestry along a larger one. -/
theorem Ancestor.mono {E F : Sha → Sha → Prop} (hEF : ∀ c p, E c p → F c p) {a b : Sha}
    (h : Ancestor E a b) : Ancestor F a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hcp ih => exact ReflTransGen.tail ih (hEF _ _ hcp)

/-- Along a relation on which `g` strictly decreases, an ancestor is the commit itself or
has a smaller `g`. -/
theorem eq_or_lt_of_ancestor {E : Sha → Sha → Prop} {g : Sha → Nat}
    (hg : ∀ c p, E c p → g p < g c) {a b : Sha} (h : Ancestor E a b) : a = b ∨ g a < g b := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hcp ih =>
    rcases ih with rfl | hlt
    · exact Or.inr (hg _ _ hcp)
    · exact Or.inr ((hg _ _ hcp).trans hlt)

theorem le_of_ancestor {E : Sha → Sha → Prop} {g : Sha → Nat}
    (hg : ∀ c p, E c p → g p < g c) {a b : Sha} (h : Ancestor E a b) : g a ≤ g b := by
  rcases eq_or_lt_of_ancestor hg h with rfl | hlt
  · exact le_rfl
  · exact hlt.le

/-- Pruning by `g` is sound: if `a` is an ancestor of `b`, the walk from `b` still reaches
`a` when it never enters a commit whose `g` is below `a`'s. -/
theorem prune_sound {E : Sha → Sha → Prop} {g : Sha → Nat} (hg : ∀ c p, E c p → g p < g c)
    {a b : Sha} (h : Ancestor E a b) : Ancestor (fun c p => E c p ∧ g a ≤ g p) a b := by
  induction h using ReflTransGen.head_induction_on with
  | refl => exact ReflTransGen.refl
  | head hcd hda ih => exact ReflTransGen.head ⟨hcd, le_of_ancestor hg hda⟩ ih

/-- `gen` is the generation number of git's commit-graph: a root has generation 1, any
other commit one more than the largest generation among its parents. -/
def IsGen (par : Sha → Finset Sha) (gen : Sha → Nat) : Prop :=
  ∀ c, gen c = (par c).sup gen + 1

theorem gen_lt_of_parent {par : Sha → Finset Sha} {gen : Sha → Nat} (hgen : IsGen par gen)
    {c p : Sha} (h : p ∈ par c) : gen p < gen c := by
  rw [hgen c]
  exact Nat.lt_succ_of_le (Finset.le_sup h)

/-- A proper ancestor has a smaller generation. -/
theorem gen_lt_of_ancestor {par : Sha → Finset Sha} {gen : Sha → Nat} (hgen : IsGen par gen)
    {a b : Sha} (h : Ancestor (Parent par) a b) (hne : a ≠ b) : gen a < gen b :=
  (eq_or_lt_of_ancestor (fun _ _ hp => gen_lt_of_parent hgen hp) h).resolve_left hne

end Commits

/-! ## Heads and the journal -/

/-- Heads at one moment: each ref (a branch of a store, or a checkout's `HEAD`) points at
a commit or does not exist. -/
abbrev Heads (Ref Sha : Type) := Ref → Option Sha

/-- A journal event: at the refresh at `time`, the head of `ref` changed from `old` to
`new`. `old = none` records a ref created and `new = none` a ref deleted. -/
structure Event (Ref Sha : Type) where
  ref : Ref
  old : Option Sha
  new : Option Sha
  time : Nat

section Since

variable {Ref Sha : Type}

/-- The journal's events before time `T`. -/
def before (J : List (Event Ref Sha)) (T : Nat) : List (Event Ref Sha) :=
  J.takeWhile fun e => e.time < T

/-- What changed since `T`: the journal from its first event at or after `T`. -/
def since (J : List (Event Ref Sha)) (T : Nat) : List (Event Ref Sha) :=
  J.dropWhile fun e => e.time < T

/-- With refreshes in time order the journal splits at `T` into the events before `T`
and those since. -/
theorem split_at {A B : List (Event Ref Sha)} {T : Nat} (hA : ∀ e ∈ A, e.time < T)
    (hB : ∀ e ∈ B, T ≤ e.time) : before (A ++ B) T = A ∧ since (A ++ B) T = B := by
  have hA' : ∀ e ∈ A, decide (e.time < T) = true := fun e he => decide_eq_true (hA e he)
  constructor
  · rw [before, List.takeWhile_append_of_pos hA']
    cases B with
    | nil => simp
    | cons e B => simp [Nat.not_lt.mpr (hB e List.mem_cons_self)]
  · rw [since, List.dropWhile_append_of_pos hA']
    cases B with
    | nil => simp
    | cons e B => simp [Nat.not_lt.mpr (hB e List.mem_cons_self)]

/-- The events since a later time are a suffix of those since an earlier one. -/
theorem since_antitone (J : List (Event Ref Sha)) {T T' : Nat} (h : T ≤ T') :
    since J T' <:+ since J T := by
  induction J with
  | nil => exact List.suffix_refl _
  | cons e J ih =>
    by_cases h1 : e.time < T
    · have h2 : e.time < T' := lt_of_lt_of_le h1 h
      simpa [since, List.dropWhile_cons, h1, h2] using ih
    · have h0 : since (e :: J) T = e :: J := by simp [since, h1]
      rw [h0]
      exact List.dropWhile_suffix _

end Since

section Replay

variable {Ref Sha : Type} [DecidableEq Ref]

/-- Replaying an event moves its ref to the new head. -/
def replay (H : Heads Ref Sha) (e : Event Ref Sha) : Heads Ref Sha :=
  Function.update H e.ref e.new

/-- The heads a journal records: its events replayed from the empty map. -/
def headsOf (J : List (Event Ref Sha)) : Heads Ref Sha :=
  J.foldl replay fun _ => none

theorem replay_of_not_mem {r : Ref} : ∀ {J : List (Event Ref Sha)} (M : Heads Ref Sha),
    r ∉ J.map Event.ref → J.foldl replay M r = M r
  | [], _, _ => rfl
  | e :: J, M, hr => by
    simp only [List.map_cons, List.mem_cons, not_or] at hr
    rw [List.foldl_cons, replay_of_not_mem _ hr.2, replay, Function.update_of_ne hr.1]

theorem replay_of_new {H' : Heads Ref Sha} : ∀ {J : List (Event Ref Sha)},
    (∀ e ∈ J, e.new = H' e.ref) → ∀ (M : Heads Ref Sha) (r : Ref),
      J.foldl replay M r = if r ∈ J.map Event.ref then H' r else M r
  | [], _, M, r => by simp
  | e :: J, hJ, M, r => by
    rw [List.foldl_cons, replay_of_new (fun e' he' => hJ e' (List.mem_cons_of_mem _ he'))]
    by_cases hr : r = e.ref
    · subst hr
      simp [replay, hJ e List.mem_cons_self]
    · simp only [List.map_cons, List.mem_cons, hr, false_or, replay, Function.update_of_ne hr]

/-- The events since `T` turn the heads as of `T` into the current heads. -/
theorem replay_since (J : List (Event Ref Sha)) (T : Nat) :
    (since J T).foldl replay (headsOf (before J T)) = headsOf J := by
  rw [headsOf, headsOf, ← List.foldl_append, before, since, List.takeWhile_append_dropWhile]

/-- Every ref whose head differs between `T` and now has an event since `T`: a creation,
a deletion or any move, forced or not. -/
theorem changed_mem_since {J : List (Event Ref Sha)} {T : Nat} {r : Ref}
    (h : headsOf (before J T) r ≠ headsOf J r) : r ∈ (since J T).map Event.ref := by
  by_contra hr
  exact h (by rw [← replay_since J T, replay_of_not_mem _ hr])

end Replay

section Diff

variable {Ref Sha : Type} [DecidableEq Sha]

/-- The events of a refresh at time `t`: one for each ref in `refs` whose head changed
from `H` to `H'`, with the old and the new head. -/
def diff (refs : List Ref) (H H' : Heads Ref Sha) (t : Nat) : List (Event Ref Sha) :=
  (refs.filter fun r => H r ≠ H' r).map fun r => ⟨r, H r, H' r, t⟩

theorem mem_diff {refs : List Ref} {H H' : Heads Ref Sha} {t : Nat} {e : Event Ref Sha} :
    e ∈ diff refs H H' t ↔
      e.ref ∈ refs ∧ H e.ref ≠ H' e.ref ∧ e = ⟨e.ref, H e.ref, H' e.ref, t⟩ := by
  simp only [diff, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨r, ⟨hr, hne⟩, rfl⟩
    exact ⟨hr, hne, rfl⟩
  · rintro ⟨hr, hne, he⟩
    exact ⟨e.ref, ⟨hr, hne⟩, he.symm⟩

theorem ref_mem_diff {refs : List Ref} {H H' : Heads Ref Sha} {t : Nat} {r : Ref} :
    r ∈ (diff refs H H' t).map Event.ref ↔ r ∈ refs ∧ H r ≠ H' r := by
  simp [diff, List.map_map, Function.comp_def]

/-- Replaying a refresh's events turns the old heads into the new ones when `refs` names
every ref that changed. -/
theorem replay_diff [DecidableEq Ref] {refs : List Ref} {H H' : Heads Ref Sha} {t : Nat}
    (hcov : ∀ r, H r ≠ H' r → r ∈ refs) : (diff refs H H' t).foldl replay H = H' := by
  funext r
  have hnew : ∀ e ∈ diff refs H H' t, e.new = H' e.ref := fun e he =>
    congrArg Event.new (mem_diff.mp he).2.2
  rw [replay_of_new hnew H r]
  by_cases h : H r = H' r
  · split_ifs <;> simp [h]
  · rw [if_pos (ref_mem_diff.mpr ⟨hcov r h, h⟩)]

end Diff

/-! ## The index -/

/-- What a refresh reads from git at time `time`: the refs that exist, their heads, and
the commits git lists from them (`git rev-list --all` in each store). `refs` names every
ref that has a head. -/
structure Visit (Ref Sha : Type) where
  time : Nat
  refs : List Ref
  heads : Heads Ref Sha
  listed : Finset Sha
  refs_complete : ∀ r, heads r ≠ none → r ∈ refs

/-- The index: stored commits and parent facts, which only accumulate, and the journal of
head changes, which is only appended to. -/
structure Index (Ref Sha : Type) where
  commits : Finset Sha
  links : Finset (Sha × Sha)
  journal : List (Event Ref Sha)

section Links

variable {Sha : Type} [DecidableEq Sha]

/-- The parent facts of the commits `S`: `(c, p)` for each `c` in `S` and each parent `p`
its id fixes. -/
def linksOf (par : Sha → Finset Sha) (S : Finset Sha) : Finset (Sha × Sha) :=
  S.biUnion fun c => (par c).image (Prod.mk c)

theorem mem_linksOf {par : Sha → Finset Sha} {S : Finset Sha} {c p : Sha} :
    (c, p) ∈ linksOf par S ↔ c ∈ S ∧ p ∈ par c := by
  simp [linksOf]

theorem linksOf_union (par : Sha → Finset Sha) (S T : Finset Sha) :
    linksOf par (S ∪ T) = linksOf par S ∪ linksOf par T :=
  Finset.union_biUnion

end Links

namespace Index

variable {Ref Sha : Type} [DecidableEq Sha]

/-- The empty index. -/
def empty : Index Ref Sha := ⟨∅, ∅, []⟩

/-- A parent fact `(c, p)` is stored: the index's parent relation. -/
def Linked (I : Index Ref Sha) (c p : Sha) : Prop := (c, p) ∈ I.links

/-- The parent facts are exactly those of the stored commits. -/
def Faithful (I : Index Ref Sha) (par : Sha → Finset Sha) : Prop :=
  I.links = linksOf par I.commits

/-- Stored commits with a recorded parent that is not stored. -/
def boundary (I : Index Ref Sha) : Finset Sha :=
  I.commits.filter fun c => ∃ l ∈ I.links, l.1 = c ∧ l.2 ∉ I.commits

/-- The walk from `b` stays among stored commits. -/
def Closed (I : Index Ref Sha) (b : Sha) : Prop :=
  ∀ c, Ancestor I.Linked c b → c ∈ I.commits

/-- The parents the index records for `c`. -/
def parentsOf (I : Index Ref Sha) (c : Sha) : Finset Sha :=
  (I.links.filter fun l => l.1 = c).image Prod.snd

/-- `g` is the generation the index computes from its own facts, on every closed walk. -/
def GenFrom (I : Index Ref Sha) (g : Sha → Nat) : Prop :=
  ∀ c, I.Closed c → g c = (I.parentsOf c).sup g + 1

/-! ### Exactness -/

theorem faithful_empty (par : Sha → Finset Sha) : (empty : Index Ref Sha).Faithful par := by
  simp [Faithful, empty, linksOf]

theorem linked_iff {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {c p : Sha} : I.Linked c p ↔ c ∈ I.commits ∧ p ∈ par c := by
  rw [Linked, hI, mem_linksOf]

/-- Soundness: an index yes is a git yes. -/
theorem sound {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par) {a b : Sha}
    (h : Ancestor I.Linked a b) : Ancestor (Parent par) a b :=
  Ancestor.mono (fun _ _ hl => ((linked_iff hI).mp hl).2) h

/-- Completeness: when the walk from `b` is closed, a git yes is an index yes. -/
theorem complete {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {b : Sha} (hb : I.Closed b) {a : Sha} (h : Ancestor (Parent par) a b) :
    Ancestor I.Linked a b := by
  induction h with
  | refl => exact ReflTransGen.refl
  | tail _ hp ih => exact ReflTransGen.tail ih ((linked_iff hI).mpr ⟨hb _ ih, hp⟩)

theorem ancestor_iff {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {b : Sha} (hb : I.Closed b) {a : Sha} :
    Ancestor I.Linked a b ↔ Ancestor (Parent par) a b :=
  ⟨sound hI, complete hI hb⟩

/-- The walk from `b` is closed exactly when `b` is stored and no boundary commit is
reachable from it. -/
theorem closed_iff {I : Index Ref Sha} {b : Sha} :
    I.Closed b ↔ b ∈ I.commits ∧ ∀ c ∈ I.boundary, ¬ Ancestor I.Linked c b := by
  constructor
  · intro h
    refine ⟨h b ReflTransGen.refl, fun c hc hcb => ?_⟩
    obtain ⟨-, ⟨c', p⟩, hl, rfl, hp⟩ := Finset.mem_filter.mp hc
    exact hp (h p (ReflTransGen.tail hcb hl))
  · rintro ⟨hb, hbd⟩ c hcb
    induction hcb with
    | refl => exact hb
    | tail hxb hxy ih =>
      by_contra hy
      exact hbd _ (Finset.mem_filter.mpr ⟨ih, ⟨_, _⟩, hxy, rfl, hy⟩) hxb

/-- Exactness: when no boundary commit is reachable from a stored `b`, the index's
ancestry from `b` is git's. -/
theorem exact_iff {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par) {b : Sha}
    (hb : b ∈ I.commits) (hbd : ∀ c ∈ I.boundary, ¬ Ancestor I.Linked c b) {a : Sha} :
    Ancestor I.Linked a b ↔ Ancestor (Parent par) a b :=
  ancestor_iff hI (closed_iff.mpr ⟨hb, hbd⟩)

/-- A commit whose whole git history is stored has a closed walk. -/
theorem closed_of_history {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {b : Sha} (h : ∀ c, Ancestor (Parent par) c b → c ∈ I.commits) : I.Closed b :=
  fun c hc => h c (sound hI hc)

/-! ### Permanence -/

omit [DecidableEq Sha] in
/-- A yes stays a yes: the index's ancestry only grows with its parent facts. -/
theorem ancestor_mono {I I' : Index Ref Sha} (h : I.links ⊆ I'.links) {a b : Sha}
    (hab : Ancestor I.Linked a b) : Ancestor I'.Linked a b :=
  Ancestor.mono (fun _ _ hl => h hl) hab

/-- A closed walk stays closed. -/
theorem closed_mono {par : Sha → Finset Sha} {I I' : Index Ref Sha} (hI : I.Faithful par)
    (hI' : I'.Faithful par) (h : I.commits ⊆ I'.commits) {b : Sha} (hb : I.Closed b) :
    I'.Closed b :=
  fun c hc => h (hb c (complete hI hb (sound hI' hc)))

/-- Permanence: on a closed walk, an answer never changes. -/
theorem answer_stable {par : Sha → Finset Sha} {I I' : Index Ref Sha} (hI : I.Faithful par)
    (hI' : I'.Faithful par) (h : I.commits ⊆ I'.commits) {b : Sha} (hb : I.Closed b)
    {a : Sha} : Ancestor I'.Linked a b ↔ Ancestor I.Linked a b := by
  rw [ancestor_iff hI' (closed_mono hI hI' h hb), ancestor_iff hI hb]

/-! ### Generation numbers -/

theorem mem_parentsOf {I : Index Ref Sha} {c p : Sha} : p ∈ I.parentsOf c ↔ I.Linked c p := by
  simp only [parentsOf, Finset.mem_image, Finset.mem_filter, Linked]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hl, rfl⟩, rfl⟩
    exact hl
  · intro h
    exact ⟨(c, p), ⟨h, rfl⟩, rfl⟩

theorem parentsOf_eq {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {c : Sha} (hc : c ∈ I.commits) : I.parentsOf c = par c := by
  ext p
  rw [mem_parentsOf, linked_iff hI]
  exact ⟨And.right, fun h => ⟨hc, h⟩⟩

theorem closed_parent {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {c p : Sha} (hc : I.Closed c) (hp : p ∈ par c) : I.Closed p := fun x hx =>
  hc x (ReflTransGen.head ((linked_iff hI).mpr ⟨hc c ReflTransGen.refl, hp⟩) hx)

/-- On a closed walk the generation the index computes is git's. -/
theorem gen_eq {par : Sha → Finset Sha} {gen : Sha → Nat} (hgen : IsGen par gen)
    {I : Index Ref Sha} (hI : I.Faithful par) {g : Sha → Nat} (hg : I.GenFrom g) {c : Sha}
    (hc : I.Closed c) : g c = gen c := by
  suffices h : ∀ n c, gen c = n → I.Closed c → g c = gen c from h _ c rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hn hc
    rw [hg c hc, parentsOf_eq hI (hc c ReflTransGen.refl), hgen c]
    congr 1
    exact Finset.sup_congr rfl fun p hp =>
      ih (gen p) (hn ▸ gen_lt_of_parent hgen hp) p rfl (closed_parent hI hc hp)

/-- The generation the index computes for a commit with a closed walk is the same at
every later refresh. -/
theorem gen_stable {par : Sha → Finset Sha} {gen : Sha → Nat} (hgen : IsGen par gen)
    {I I' : Index Ref Sha} (hI : I.Faithful par) (hI' : I'.Faithful par)
    (h : I.commits ⊆ I'.commits) {g g' : Sha → Nat} (hg : I.GenFrom g) (hg' : I'.GenFrom g')
    {c : Sha} (hc : I.Closed c) : g' c = g c := by
  rw [gen_eq hgen hI' hg' (closed_mono hI hI' h hc), gen_eq hgen hI hg hc]

/-- Pruning the index's walk by generation is sound. -/
theorem prune_index {par : Sha → Finset Sha} {gen : Sha → Nat} (hgen : IsGen par gen)
    {I : Index Ref Sha} (hI : I.Faithful par) {a b : Sha} (h : Ancestor I.Linked a b) :
    Ancestor (fun c p => I.Linked c p ∧ gen a ≤ gen p) a b :=
  prune_sound (E := I.Linked) (g := gen)
    (fun _ _ hl => gen_lt_of_parent hgen ((linked_iff hI).mp hl).2) h

/-! ### Refresh -/

variable [DecidableEq Ref]

/-- The current heads: the journal replayed from the empty map. -/
def heads (I : Index Ref Sha) : Heads Ref Sha := headsOf I.journal

/-- The events a refresh at visit `v` appends: one for each ref whose head changed,
among the refs the journal has named and those git shows. -/
def events (I : Index Ref Sha) (v : Visit Ref Sha) : List (Event Ref Sha) :=
  diff (I.journal.map Event.ref ++ v.refs).dedup I.heads v.heads v.time

/-- A refresh at visit `v` that reads the commits `N`: it stores them with their parent
facts and appends the head events. -/
def refresh (I : Index Ref Sha) (par : Sha → Finset Sha) (N : Finset Sha)
    (v : Visit Ref Sha) : Index Ref Sha :=
  ⟨I.commits ∪ N, I.links ∪ linksOf par N, I.journal ++ I.events v⟩

/-- A run of refreshes: at each visit, read `read I v` from the index `I` found there. -/
def run (par : Sha → Finset Sha) (read : Index Ref Sha → Visit Ref Sha → Finset Sha) :
    Index Ref Sha → List (Visit Ref Sha) → Index Ref Sha
  | I, [] => I
  | I, v :: vs => run par read (I.refresh par (read I v) v) vs

/-- Commits and parent facts only accumulate. -/
theorem subset_refresh (I : Index Ref Sha) (par : Sha → Finset Sha) (N : Finset Sha)
    (v : Visit Ref Sha) :
    I.commits ⊆ (I.refresh par N v).commits ∧ I.links ⊆ (I.refresh par N v).links :=
  ⟨Finset.subset_union_left, Finset.subset_union_left⟩

theorem faithful_refresh {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    (N : Finset Sha) (v : Visit Ref Sha) : (I.refresh par N v).Faithful par := by
  show I.links ∪ linksOf par N = linksOf par (I.commits ∪ N)
  rw [hI, linksOf_union]

/-! ### Snapshots -/

omit [DecidableEq Sha] in
theorem cover (I : Index Ref Sha) (v : Visit Ref Sha) {r : Ref} (h : I.heads r ≠ v.heads r) :
    r ∈ (I.journal.map Event.ref ++ v.refs).dedup := by
  rw [List.mem_dedup, List.mem_append]
  by_cases hj : r ∈ I.journal.map Event.ref
  · exact Or.inl hj
  · refine Or.inr (v.refs_complete r fun hv => h ?_)
    rw [heads, headsOf, replay_of_not_mem _ hj, hv]

/-- After a refresh, the journal replayed from the empty map is exactly the heads git
showed: the snapshot is a function of the journal. -/
theorem heads_refresh (I : Index Ref Sha) (par : Sha → Finset Sha) (N : Finset Sha)
    (v : Visit Ref Sha) : (I.refresh par N v).heads = v.heads := by
  show headsOf (I.journal ++ I.events v) = v.heads
  rw [headsOf, List.foldl_append]
  exact replay_diff fun _ h => cover I v h

/-- A refresh appends one event for each ref whose head changed, and no other: a
creation, a deletion or a move, with the old and the new head. -/
theorem mem_events {I : Index Ref Sha} {v : Visit Ref Sha} {e : Event Ref Sha} :
    e ∈ I.events v ↔
      I.heads e.ref ≠ v.heads e.ref ∧ e = ⟨e.ref, I.heads e.ref, v.heads e.ref, v.time⟩ := by
  rw [events, mem_diff]
  exact ⟨fun h => h.2, fun h => ⟨cover I v h.1, h⟩⟩

theorem events_nodup (I : Index Ref Sha) (v : Visit Ref Sha) :
    ((I.events v).map Event.ref).Nodup := by
  have h : (I.events v).map Event.ref =
      (I.journal.map Event.ref ++ v.refs).dedup.filter fun r => I.heads r ≠ v.heads r := by
    simp [events, diff, List.map_map, Function.comp_def]
  rw [h]
  exact (List.nodup_dedup _).filter _

/-- A refresh that reads no new commit leaves the commits as they were, whatever heads
changed: commit times cannot show a deletion or a move to an older commit. -/
theorem commits_of_known {I : Index Ref Sha} {par : Sha → Finset Sha} {N : Finset Sha}
    (hN : N ⊆ I.commits) (v : Visit Ref Sha) : (I.refresh par N v).commits = I.commits :=
  Finset.union_eq_left.mpr hN

/-- A head denotes itself: a commit id names the commit and its whole history. -/
def headDen : Denotation Ref (Option Sha) (Option Sha) := fun _ h => h

/-- An answer about ref `r`: the property `P` of the head the index recorded. As a claim
its source is the ref and its version that head. -/
def claim (I : Index Ref Sha) (r : Ref) (P : Option Sha → Prop) :
    Claim Ref (Option Sha) (Option Sha) :=
  ⟨r, I.heads r, P⟩

/-- An answer is about the head of the refresh that recorded it. -/
theorem claim_refresh (I : Index Ref Sha) (par : Sha → Finset Sha) (N : Finset Sha)
    (v : Visit Ref Sha) (r : Ref) (P : Option Sha → Prop) :
    ((I.refresh par N v).claim r P).Established headDen ↔ P (v.heads r) := by
  simp only [Claim.Established, claim, headDen, heads_refresh]

/-- An answer still holds while its ref has not moved. -/
theorem claim_holds_while_unmoved {I : Index Ref Sha} {r : Ref} {P : Option Sha → Prop}
    (h : P (I.heads r)) {now : Heads Ref Sha} (hnow : now r = I.heads r) :
    (I.claim r P).Holds headDen now :=
  fresh_claim_holds h (by simp [Claim.fresh, claim, hnow])

/-- An answer is stale exactly when its ref has moved. -/
theorem claim_stale_iff_moved {I : Index Ref Sha} {r : Ref} {P : Option Sha → Prop}
    {now : Heads Ref Sha} : (I.claim r P).fresh now = false ↔ now r ≠ I.heads r :=
  stale_iff_changed

/-- On a closed walk from the recorded head, the index's merge answer is exactly the
claim that `a` is merged into the ref. -/
theorem merged_iff {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {r : Ref} {a b : Sha} (hr : I.heads r = some b) (hb : I.Closed b) :
    (I.claim r (Merged par a)).Established headDen ↔ Ancestor I.Linked a b := by
  simp only [Claim.Established, claim, headDen, Merged, hr, Option.some.injEq,
    exists_eq_left']
  exact (ancestor_iff hI hb).symm

/-! ### Refresh laws -/

/-- A refresh depends on what it reads only through the stored commits that result. -/
theorem refresh_congr {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {N N' : Finset Sha} (h : I.commits ∪ N = I.commits ∪ N') (v : Visit Ref Sha) :
    I.refresh par N v = I.refresh par N' v := by
  have hl : I.links ∪ linksOf par N = I.links ∪ linksOf par N' := by
    rw [hI, ← linksOf_union, ← linksOf_union, h]
  unfold refresh
  rw [h, hl]

omit [DecidableEq Ref] in
/-- What `git rev-list <heads> --not <stops>` leaves out is stored already when the walk
from every stop commit is closed: it leaves out only ancestors of stop commits. -/
theorem stop_safe {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {K N L : Finset Sha} (hK : ∀ k ∈ K, I.Closed k) (hN : N ⊆ L)
    (hL : ∀ c ∈ L, c ∉ N → ∃ k ∈ K, Ancestor (Parent par) c k) :
    I.commits ∪ N = I.commits ∪ L := by
  apply Finset.Subset.antisymm (Finset.union_subset_union (Finset.Subset.refl _) hN)
  intro c hc
  rcases Finset.mem_union.mp hc with h | h
  · exact Finset.mem_union_left _ h
  · by_cases hcN : c ∈ N
    · exact Finset.mem_union_right _ hcN
    · obtain ⟨k, hk, hck⟩ := hL c h hcN
      exact Finset.mem_union_left _ (hK k hk c (complete hI (hK k hk) hck))

/-- An incremental refresh that stops at commits with closed walks equals a full one. -/
theorem incremental_eq_full {par : Sha → Finset Sha} {I : Index Ref Sha}
    (hI : I.Faithful par) {K N : Finset Sha} {v : Visit Ref Sha} (hK : ∀ k ∈ K, I.Closed k)
    (hN : N ⊆ v.listed) (hL : ∀ c ∈ v.listed, c ∉ N → ∃ k ∈ K, Ancestor (Parent par) c k) :
    I.refresh par N v = I.refresh par v.listed v :=
  refresh_congr hI (stop_safe hI hK hN hL) v

/-- Refreshing again against the same visit, reading only stored commits, changes
nothing. -/
theorem refresh_idem {par : Sha → Finset Sha} {I : Index Ref Sha} (hI : I.Faithful par)
    {N N' : Finset Sha} (v : Visit Ref Sha) (hN' : N' ⊆ I.commits ∪ N) :
    (I.refresh par N v).refresh par N' v = I.refresh par N v := by
  have hE : (I.refresh par N v).events v = [] := by
    rw [events, heads_refresh]
    simp [diff]
  have hC : (I.refresh par N v).commits ∪ N' = (I.refresh par N v).commits :=
    Finset.union_eq_left.mpr hN'
  have hL : (I.refresh par N v).links ∪ linksOf par N' = (I.refresh par N v).links := by
    rw [faithful_refresh hI N v, ← linksOf_union, hC]
  show (⟨_, _, _⟩ : Index Ref Sha) = _
  rw [hC, hL, hE, List.append_nil]

theorem faithful_run {par : Sha → Finset Sha} {read : Index Ref Sha → Visit Ref Sha → Finset Sha}
    {I : Index Ref Sha} (hI : I.Faithful par) (vs : List (Visit Ref Sha)) :
    (I.run par read vs).Faithful par := by
  induction vs generalizing I with
  | nil => exact hI
  | cons v vs ih => exact ih (faithful_refresh hI _ _)

theorem run_append (I : Index Ref Sha) (par : Sha → Finset Sha)
    (read : Index Ref Sha → Visit Ref Sha → Finset Sha) (vs : List (Visit Ref Sha))
    (v : Visit Ref Sha) :
    I.run par read (vs ++ [v]) =
      (I.run par read vs).refresh par (read (I.run par read vs) v) v := by
  induction vs generalizing I with
  | nil => rfl
  | cons w vs ih => exact ih _

/-- After a run, the journal replays to the last visit's heads. -/
theorem heads_run (I : Index Ref Sha) (par : Sha → Finset Sha)
    (read : Index Ref Sha → Visit Ref Sha → Finset Sha) (vs : List (Visit Ref Sha))
    (v : Visit Ref Sha) : (I.run par read (vs ++ [v])).heads = v.heads := by
  rw [run_append, heads_refresh]

/-- A run whose every read is safe equals the run of full refreshes. -/
theorem run_eq_full {par : Sha → Finset Sha} {read : Index Ref Sha → Visit Ref Sha → Finset Sha}
    (hread : ∀ I v, I.Faithful par → I.commits ∪ read I v = I.commits ∪ v.listed)
    {I : Index Ref Sha} (hI : I.Faithful par) (vs : List (Visit Ref Sha)) :
    I.run par read vs = I.run par (fun _ v => v.listed) vs := by
  induction vs generalizing I with
  | nil => rfl
  | cons v vs ih =>
    simp only [run]
    rw [refresh_congr hI (hread I v hI) v]
    exact ih (faithful_refresh hI _ _)

/-- A run of full refreshes holds exactly the commits some visit listed. -/
theorem mem_run_full (I : Index Ref Sha) (par : Sha → Finset Sha) (vs : List (Visit Ref Sha))
    (c : Sha) : c ∈ (I.run par (fun _ v => v.listed) vs).commits ↔
      c ∈ I.commits ∨ ∃ v ∈ vs, c ∈ v.listed := by
  induction vs generalizing I with
  | nil => simp [run]
  | cons v vs ih =>
    simp only [run, ih, refresh, Finset.mem_union, List.mem_cons, exists_eq_or_imp]
    tauto

theorem run_journal (I : Index Ref Sha) (par : Sha → Finset Sha)
    (read : Index Ref Sha → Visit Ref Sha → Finset Sha) (vs : List (Visit Ref Sha)) :
    ∃ B, (I.run par read vs).journal = I.journal ++ B ∧ ∀ e ∈ B, ∃ v ∈ vs, e.time = v.time := by
  induction vs generalizing I with
  | nil => exact ⟨[], by simp [run], by simp⟩
  | cons v vs ih =>
    obtain ⟨B, hB, ht⟩ := ih (I.refresh par (read I v) v)
    refine ⟨I.events v ++ B, ?_, fun e he => ?_⟩
    · show (run par read (I.refresh par (read I v) v) vs).journal = _
      rw [hB]
      exact List.append_assoc _ _ _
    rcases List.mem_append.mp he with he | he
    · exact ⟨v, List.mem_cons_self, congrArg Event.time (mem_events.mp he).2⟩
    · obtain ⟨w, hw, hwt⟩ := ht e he
      exact ⟨w, List.mem_cons_of_mem _ hw, hwt⟩

/-- What changed since `T`, read from the journal, is exact for heads. When the index's
events so far are before `T` and the later refreshes are at or after `T`, the events
since `T` are exactly the ones those refreshes appended; replayed onto the heads as of
`T` they give the current heads; and every ref whose head differs has one. -/
theorem run_since {I : Index Ref Sha} {par : Sha → Finset Sha}
    {read : Index Ref Sha → Visit Ref Sha → Finset Sha} {vs : List (Visit Ref Sha)} {T : Nat}
    (hI : ∀ e ∈ I.journal, e.time < T) (hvs : ∀ v ∈ vs, T ≤ v.time) :
    (I.run par read vs).journal = I.journal ++ since (I.run par read vs).journal T ∧
      (since (I.run par read vs).journal T).foldl replay I.heads = (I.run par read vs).heads ∧
      ∀ r, I.heads r ≠ (I.run par read vs).heads r →
        r ∈ (since (I.run par read vs).journal T).map Event.ref := by
  obtain ⟨B, hJ, hB⟩ := run_journal I par read vs
  have hB' : ∀ e ∈ B, T ≤ e.time := fun e he => by
    obtain ⟨v, hv, ht⟩ := hB e he
    rw [ht]
    exact hvs v hv
  have hs : since (I.run par read vs).journal T = B := by
    rw [hJ]
    exact (split_at hI hB').2
  have hh : B.foldl replay I.heads = (I.run par read vs).heads := by
    simp only [heads]
    rw [hJ, headsOf, headsOf, List.foldl_append]
  rw [hs]
  refine ⟨hJ, hh, fun r hr => ?_⟩
  by_contra hm
  exact hr (by rw [← hh, replay_of_not_mem _ hm])

end Index

/-! ## The boundary hypothesis is needed -/

/-- Commits in a line: commit `n + 1` has the single parent `n`. -/
def line : Nat → Finset Nat
  | 0 => ∅
  | n + 1 => {n}

/-- A visit at time 0 that shows no refs and lists the commits `L`. -/
def listing (L : Finset Nat) : Visit Unit Nat := ⟨0, [], fun _ => none, L, by simp⟩

/-- The index after reading commits `0` and `2` but not `1`: an old clone and a shallow
one. -/
def shallowIndex : Index Unit Nat := Index.empty.refresh line {0, 2} (listing {0, 2})

/-- The same index once commit `1` has been read. -/
def deepenedIndex : Index Unit Nat := shallowIndex.refresh line {1} (listing {1})

/-- Without the boundary hypothesis, completeness and permanence fail. Commits `0` and `2`
are stored and `2` is a boundary commit. Git says `0` is an ancestor of `2`; the index
says it is not; once `1` is read, the index says it is. -/
theorem shallow_answer_changes :
    shallowIndex.Faithful line ∧ 0 ∈ shallowIndex.commits ∧ 2 ∈ shallowIndex.boundary ∧
      Ancestor (Parent line) 0 2 ∧ ¬ Ancestor shallowIndex.Linked 0 2 ∧
      Ancestor deepenedIndex.Linked 0 2 := by
  have hS : shallowIndex.Faithful line :=
    Index.faithful_refresh (Index.faithful_empty line) _ _
  have hD : deepenedIndex.Faithful line := Index.faithful_refresh hS _ _
  have hSc : shallowIndex.commits = {0, 2} := by
    simp [shallowIndex, Index.refresh, Index.empty]
  have hDc : deepenedIndex.commits = {0, 2} ∪ {1} := by
    rw [deepenedIndex, Index.refresh]
    simp only [hSc]
  refine ⟨hS, by simp [hSc], ?_, ?_, ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨by simp [hSc], (2, 1), ?_, rfl, by simp [hSc]⟩
    exact (Index.linked_iff hS).mpr ⟨by simp [hSc], by decide⟩
  · exact ReflTransGen.head (show (1 : Nat) ∈ line 2 by decide)
      (ReflTransGen.single (show (0 : Nat) ∈ line 1 by decide))
  · intro h
    have key : ∀ x, ReflTransGen shallowIndex.Linked 2 x → x = 2 ∨ x = 1 := by
      intro x hx
      induction hx with
      | refl => exact Or.inl rfl
      | tail _ hxy ih =>
        obtain ⟨hx, hy⟩ := (Index.linked_iff hS).mp hxy
        rcases ih with rfl | rfl
        · exact Or.inr (Finset.mem_singleton.mp hy)
        · simp [hSc] at hx
    rcases key 0 h with h0 | h0 <;> simp at h0
  · have h21 : deepenedIndex.Linked 2 1 := (Index.linked_iff hD).mpr ⟨by simp [hDc], by decide⟩
    have h10 : deepenedIndex.Linked 1 0 := (Index.linked_iff hD).mpr ⟨by simp [hDc], by decide⟩
    exact ReflTransGen.head h21 (ReflTransGen.single h10)

end Mettapedia.Protocols.Repos.GitSkeleton
