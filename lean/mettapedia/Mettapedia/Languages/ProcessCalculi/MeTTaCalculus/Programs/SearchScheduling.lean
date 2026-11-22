import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.Determinacy
import Mettapedia.GSLT.Coordination.ReplicaMerge

/-!
# Search and scheduling: two different nondeterminisms

A program can be nondeterministic in two ways, and they have different meanings.

* **Search.** An expression has several answers; each alternative runs in a world of its own, and
  `collapse` gathers the bag of answers (`searchBag`). Alternatives never see each other's effects:
  each world fires its branch in its own copy of the store (`worlds`). The bag does not depend on
  the order in which the alternatives are listed (`searchBag_perm`).
* **Scheduling.** Several processes share one history; their commits compete for occurrences, and
  what one fires is irreversible for the others. The outcomes are the answer bags and final stores
  of the maximal runs (`Outcome`). A scheduler picks one.

Today an effectful `superpose` runs its branches one after another on one store and gathers their
answers as if they were alternatives (`scheduled`, `scheduledBag`): it mixes the two. That mix is
why the old idioms race.

## Where the two coincide

For branches that are **monotone** (they take nothing and query nothing), make apart identities,
and never keep what a branch makes, running them in branch order on one store fires exactly the
branches the search enables, in their order (`scheduled_eq_worlds`): the two bags agree
(`scheduledBag_eq_searchBag`), and the shared store is the union of the worlds' stores
(`fireList_scheduled_eq`). Monotone branches are the CALM fragment of `Determinacy`.

## Where the mix breaks the bag

Each condition is needed (`Controls`):

* **a take** (`Controls.taking_branches`): two branches take one token; run in branch order, the
  answers depend on which is listed first, so the mixed semantics is not a bag semantics at all,
  while the search gives both; and when removal does not require presence, as with a removal that
  answers success on an absent atom, both branches write their receipt for the one token
  (`Controls.loose_mix_double_spend`);
* **a predicate query** (`Controls.querying_branches`): "add unless present" beside a maker: the
  query's branch answers or not depending on the listing order;
* **keeping what a sibling makes** (`Controls.causal_branches`): a branch that reads what another
  branch makes answers under the mix and not under search.

## Scheduling outcomes, trace equivalence and determinacy

* Trace-equivalent runs (`OccurrenceCommits.Traces`) have one outcome
  (`Outcome.of_traceEq`): exploring one run per trace loses no outcome, so the worlds of scheduling
  are runs up to trace equivalence.
* A conflict-free system has exactly one outcome (`ConflictFree.outcome_unique`): for the
  determinate regions of `Determinacy`, scheduling nondeterminism is invisible, while search keeps
  all its alternatives.
* The interaction kernel's `choose` is a scheduling choice: one alternative commits and withdraws
  the others (`Equivalence.Agents.Controls.choose_not_par`), whereas `superpose` is a search.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uO uR uA

section Branches

variable {O : Type uO} [DecidableEq O] {R : Type uR} {A : Type uA}
variable (label : O → R) (answer : Commit O R → A)

/-! ## Search -/

/-- **The worlds of a search** at a store: every branch enabled there, each fired in a copy of the
store of its own (its world's store is `fire store b`). -/
def worlds (store : Finset O) (branches : List (Commit O R)) : List (Commit O R) :=
  branches.filter fun b => decide (Enabled label store b)

/-- **The bag of answers of a search**: what `collapse` gathers. -/
def searchBag (store : Finset O) (branches : List (Commit O R)) : Multiset A :=
  ((worlds label store branches).map answer : List A)

/-- **Search is a bag semantics**: listing the alternatives in another order gives the same bag. -/
theorem searchBag_perm {store : Finset O} {branches branches' : List (Commit O R)}
    (perm : branches.Perm branches') :
    searchBag label answer store branches = searchBag label answer store branches' :=
  Multiset.coe_eq_coe.mpr ((perm.filter _).map answer)

/-! ## Branches run in order on one store -/

/-- **Branches run in order on one store**, as an effectful `superpose` runs today: each branch fires
if it is enabled when its turn comes, at the store the earlier branches left. -/
def scheduled : Finset O → List (Commit O R) → List (Commit O R)
  | _, [] => []
  | store, b :: rest =>
      if Enabled label store b then b :: scheduled (fire store b) rest else scheduled store rest

/-- The answers the mixed semantics gathers. -/
def scheduledBag (store : Finset O) (branches : List (Commit O R)) : Multiset A :=
  ((scheduled label store branches).map answer : List A)

variable {label}

/-- What the mixed semantics fires is one executable history. -/
theorem scheduled_executable (store : Finset O) (branches : List (Commit O R)) :
    Executable label store (scheduled label store branches) := by
  induction branches generalizing store with
  | nil => exact .nil _
  | cons b rest ih =>
      unfold scheduled
      split
      · next enabled => exact .cons enabled (ih _)
      · exact ih _

/-- A monotone commit only adds what it makes. -/
theorem fire_of_monotone {store : Finset O} {b : Commit O R} (monotone : b.Monotone) :
    fire store b = store ∪ b.made := by
  simp [fire, monotone.1]

/-- **Enabling of a monotone branch does not see a sibling's makes** that it neither keeps nor
claims. -/
theorem enabled_union_made_iff {store : Finset O} {b b' : Commit O R} (monotone : b'.Monotone)
    (madeApart : Disjoint b.made b'.made) (notKept : Disjoint b.made b'.kept) :
    Enabled label (store ∪ b.made) b' ↔ Enabled label store b' := by
  constructor
  · intro enabled
    refine ⟨by rw [monotone.1]; exact Finset.empty_subset _, ?_, enabled.apart, ?_, ?_⟩
    · intro o kept
      rcases Finset.mem_union.mp (enabled.kept_subset kept) with inStore | made
      · exact inStore
      · exact absurd kept (Finset.disjoint_left.mp notKept made)
    · exact Finset.disjoint_of_subset_right Finset.subset_union_left enabled.fresh
    · intro read member; rw [monotone.2] at member; simp at member
  · intro enabled
    refine ⟨by rw [monotone.1]; exact Finset.empty_subset _,
      enabled.kept_subset.trans Finset.subset_union_left, enabled.apart, ?_, ?_⟩
    · exact Finset.disjoint_union_right.mpr ⟨enabled.fresh, madeApart.symm⟩
    · intro read member; rw [monotone.2] at member; simp at member

/-- **Where search and scheduling coincide.** For monotone branches that make apart identities and
never keep what a branch makes, running them in order on one store fires exactly the branches the
search enables, in their order. -/
theorem scheduled_eq_worlds :
    ∀ {store : Finset O} {branches : List (Commit O R)},
      (∀ b ∈ branches, b.Monotone) → branches.Pairwise (fun b b' => Disjoint b.made b'.made) →
      (∀ b ∈ branches, ∀ b' ∈ branches, Disjoint b.made b'.kept) →
      scheduled label store branches = worlds label store branches
  | _, [], _, _, _ => rfl
  | store, b :: rest, monotone, apart, causal => by
      have monotoneRest : ∀ x ∈ rest, x.Monotone := fun x member =>
        monotone x (List.mem_cons_of_mem _ member)
      have apartRest := (List.pairwise_cons.mp apart).2
      have causalRest : ∀ x ∈ rest, ∀ y ∈ rest, Disjoint x.made y.kept := fun x mx y my =>
        causal x (List.mem_cons_of_mem _ mx) y (List.mem_cons_of_mem _ my)
      unfold scheduled worlds
      by_cases enabled : Enabled label store b
      · rw [if_pos enabled, List.filter_cons_of_pos (by simpa using enabled)]
        congr 1
        rw [scheduled_eq_worlds monotoneRest apartRest causalRest, fire_of_monotone
          (monotone b List.mem_cons_self)]
        unfold worlds
        refine List.filter_congr fun x member => ?_
        have same := enabled_union_made_iff (label := label) (store := store) (monotoneRest x member)
          ((List.pairwise_cons.mp apart).1 x member)
          (causal b List.mem_cons_self x (List.mem_cons_of_mem _ member))
        simp only [same]
      · rw [if_neg enabled, List.filter_cons_of_neg (by simpa using enabled)]
        exact scheduled_eq_worlds monotoneRest apartRest causalRest

/-- **The two bags agree** where search and scheduling coincide. -/
theorem scheduledBag_eq_searchBag {store : Finset O} {branches : List (Commit O R)}
    (monotone : ∀ b ∈ branches, b.Monotone)
    (apart : branches.Pairwise (fun b b' => Disjoint b.made b'.made))
    (causal : ∀ b ∈ branches, ∀ b' ∈ branches, Disjoint b.made b'.kept) :
    scheduledBag label answer store branches = searchBag label answer store branches := by
  unfold scheduledBag searchBag
  rw [scheduled_eq_worlds monotone apart causal]

/-- **The shared store is the union of the worlds' stores** where search and scheduling coincide. -/
theorem fireList_scheduled_eq :
    ∀ {store : Finset O} {branches : List (Commit O R)},
      (∀ b ∈ branches, b.Monotone) → branches.Pairwise (fun b b' => Disjoint b.made b'.made) →
      (∀ b ∈ branches, ∀ b' ∈ branches, Disjoint b.made b'.kept) →
      fireList store (scheduled label store branches) = store ∪ madeOf (worlds label store branches)
  | store, branches, monotone, apart, causal => by
      rw [scheduled_eq_worlds monotone apart causal]
      exact Mettapedia.GSLT.Coordination.ReplicaMerge.fireList_of_monotone store _
        fun b member => monotone b (List.mem_filter.mp member).1

/-! ## Scheduling outcomes -/

/-- **The outcomes of scheduling** a system from a store: the bag of answers and the final store of
each maximal run. -/
def Outcome (label : O → R) (sys : Commit O R → Prop) (answer : Commit O R → A) (store : Finset O)
    (bag : Multiset A) (final : Finset O) : Prop :=
  ∃ run, Maximal label sys store run ∧ bag = (run.map answer : List A) ∧ final = fireList store run

/-- **Trace-equivalent runs have one outcome**: exploring one run per trace loses no outcome. -/
theorem Outcome.of_traceEq {sys : Commit O R → Prop} {store : Finset O}
    {run run' : List (Commit O R)} (maximal : Maximal label sys store run)
    (eq : TraceEq label run run') :
    Maximal label sys store run' ∧
      ((run.map answer : List A) : Multiset A) = (run'.map answer : List A) ∧
      fireList store run = fireList store run' := by
  obtain ⟨executable', same⟩ := eq.executable maximal.1.1
  refine ⟨⟨⟨executable', fun c member => maximal.1.2 c (eq.perm.symm.subset member)⟩, ?_⟩,
    eq.answers_eq answer, same.symm⟩
  rw [same]; exact maximal.2

/-- **A conflict-free system has exactly one outcome**: scheduling nondeterminism is invisible in
the determinate regions. -/
theorem ConflictFree.outcome_unique {sys : Commit O R → Prop} {store : Finset O}
    (free : ConflictFree label sys store) {bag bag' : Multiset A} {final final' : Finset O}
    (outcome : Outcome label sys answer store bag final)
    (outcome' : Outcome label sys answer store bag' final') : bag = bag' ∧ final = final' := by
  obtain ⟨run, maximal, rfl, rfl⟩ := outcome
  obtain ⟨run', maximal', rfl, rfl⟩ := outcome'
  obtain ⟨perm, same⟩ := free.maximal_agree maximal maximal'
  exact ⟨Multiset.coe_eq_coe.mpr (perm.map answer), same⟩

end Branches

/-! ## Controls -/

namespace Controls


/-- The answer of a branch: the sum of the identities it makes (each branch here makes one). -/
def answerOf (c : Commit ℕ Unit) : ℕ := ∑ o ∈ c.made, o

/-- Everything lies at one place. -/
def here (_ : ℕ) : Unit := ()

/-- Take the token `0` and make receipt `1`. -/
def takeOne : Commit ℕ Unit := ⟨{0}, ∅, {1}, []⟩
/-- Take the token `0` and make receipt `2`. -/
def takeTwo : Commit ℕ Unit := ⟨{0}, ∅, {2}, []⟩

/-- **Negative control, a take.** The search gives both alternatives in either listing order; the
mixed semantics gives the answer of whichever branch is listed first. -/
theorem taking_branches :
    searchBag here answerOf {0} [takeOne, takeTwo] = {1, 2} ∧
      searchBag here answerOf {0} [takeTwo, takeOne] = {1, 2} ∧
      scheduledBag here answerOf {0} [takeOne, takeTwo] = {1} ∧
      scheduledBag here answerOf {0} [takeTwo, takeOne] = {2} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- The region of everything. -/
def all (_ : Unit) : Bool := true

/-- Add item `5` unless something is present. -/
def addUnlessPresent : Commit ℕ Unit := ⟨∅, ∅, {5}, [⟨all, ∅⟩]⟩
/-- Make item `6`. -/
def makeSix : Commit ℕ Unit := ⟨∅, ∅, {6}, []⟩

/-- **Negative control, a predicate query.** The search gives both answers; under the mix, the
query's branch answers only when it is listed first. -/
theorem querying_branches :
    searchBag here answerOf ∅ [makeSix, addUnlessPresent] = {6, 5} ∧
      scheduledBag here answerOf ∅ [makeSix, addUnlessPresent] = {6} ∧
      scheduledBag here answerOf ∅ [addUnlessPresent, makeSix] = {5, 6} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Make item `7`. -/
def makeSeven : Commit ℕ Unit := ⟨∅, ∅, {7}, []⟩
/-- Read item `7` and make item `8`. -/
def readSeven : Commit ℕ Unit := ⟨∅, {7}, {8}, []⟩

/-- **Negative control, keeping what a sibling makes.** Both branches are monotone, but one reads
what the other makes: the search does not enable the reader; the mix does when the maker comes
first. -/
theorem causal_branches :
    searchBag here answerOf ∅ [makeSeven, readSeven] = {7} ∧
      scheduledBag here answerOf ∅ [makeSeven, readSeven] = {7, 8} ∧
      scheduledBag here answerOf ∅ [readSeven, makeSeven] = {7} := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- Read item `0` and make `9`; read item `0` and make `10`. -/
def readNine : Commit ℕ Unit := ⟨∅, {0}, {9}, []⟩
def readTen : Commit ℕ Unit := ⟨∅, {0}, {10}, []⟩

/-- **Positive control.** Two monotone readers with apart identities: the mixed semantics and the
search agree in both listing orders, by the coincidence theorem. -/
theorem readers_coincide :
    scheduledBag here answerOf {0} [readNine, readTen] =
        searchBag here answerOf {0} [readNine, readTen] ∧
      scheduledBag here answerOf {0} [readTen, readNine] =
        searchBag here answerOf {0} [readTen, readNine] ∧
      searchBag here answerOf {0} [readNine, readTen] = {9, 10} := by
  have monotone : ∀ b ∈ [readNine, readTen], b.Monotone := by
    intro b member; simp at member; rcases member with rfl | rfl <;> exact ⟨rfl, rfl⟩
  have monotone' : ∀ b ∈ [readTen, readNine], b.Monotone := by
    intro b member; simp at member; rcases member with rfl | rfl <;> exact ⟨rfl, rfl⟩
  refine ⟨scheduledBag_eq_searchBag _ monotone (by decide) ?_,
    scheduledBag_eq_searchBag _ monotone' (by decide) ?_, by decide⟩
  · intro b mb b' mb'; simp at mb mb'
    rcases mb with rfl | rfl <;> rcases mb' with rfl | rfl <;> decide
  · intro b mb b' mb'; simp at mb mb'
    rcases mb with rfl | rfl <;> rcases mb' with rfl | rfl <;> decide

/-- A removal that does not fail when nothing is there: take what is present, make the rest. -/
def looseFire (store : Finset ℕ) (c : Commit ℕ Unit) : Finset ℕ := (store \ c.taken) ∪ c.made

/-- **Negative control, the loose mix.** When removal does not require presence, both alternatives
spend the one token and both receipts are written to the shared store: two receipts for one token.
The search gives two worlds with one receipt each; scheduling gives one receipt. -/
theorem loose_mix_double_spend :
    looseFire (looseFire {0} takeOne) takeTwo = {1, 2} ∧
      fire ({0} : Finset ℕ) takeOne = {1} ∧ fire ({0} : Finset ℕ) takeTwo = {2} ∧
      fireList ({0} : Finset ℕ) (scheduled here {0} [takeOne, takeTwo]) = {1} := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- **The mix is not a bag semantics**: two listings of the same branches give different answer
bags. -/
theorem mix_not_bag :
    [takeOne, takeTwo].Perm [takeTwo, takeOne] ∧
      scheduledBag here answerOf {0} [takeOne, takeTwo] ≠
        scheduledBag here answerOf {0} [takeTwo, takeOne] := by
  refine ⟨List.Perm.swap _ _ _, ?_⟩
  rw [(taking_branches).2.2.1, (taking_branches).2.2.2]
  decide

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
