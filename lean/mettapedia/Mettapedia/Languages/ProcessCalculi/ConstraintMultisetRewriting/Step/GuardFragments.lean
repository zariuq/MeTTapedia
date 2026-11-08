import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SearchSpace
import Mathlib.Logic.Relation
import Mathlib.Data.Set.Finite.Basic

/-!
# Guards graded by polarity: what a firing decides, under a budget, and by a certificate

A guard about a datum's behaviour is a specification over the states the datum can reach. Its
cost at a firing is decided by its **polarity** more than by its connectives.

* A **Pi specification** (`Always succ p d`, the greatest fixed point `νX. p ∧ □X`) is refuted by a
  finite counterexample; it holds only if every reachable state satisfies `p`.
* A **Sigma specification** (`Eventually succ p d`, the least fixed point `μX. p ∨ ◇X`) is
  certified by a finite witness.

## Certificates

* A **path** certifies a Sigma specification, and a path to a failing state refutes a Pi one, on
  every datum (`eventually_iff_exists_checkPath`, `not_always_iff_exists_checkPath`).
* The other half has a finite certificate **exactly on finite-state data**. A certificate for
  `Always` is a finite set holding the datum, inside `p` and closed under successors
  (`Invariant`, a post-fixed point). Checking one is sound with no trust in its maker (Park
  induction, `Invariant.always`), and one exists exactly when the specification holds and the
  datum has finitely many reachable states (`exists_invariant_iff`). Dually for refuting a Sigma
  specification (`exists_invariant_not_iff`).
* **The lowered guard** `checkInvariant` is a decidable check of a candidate certificate
  (`checkInvariant_eq_true_iff`); on finite-state data the specification holds exactly when some
  certificate checks (`always_iff_exists_checkInvariant`). Certificates compose: the intersection
  of certificates certifies the conjunction (`Invariant.inter`).

## A budgeted guard that can certify

`explore succ d n` is the datum and everything within `n` successor rounds, a set with no tree
unfolding. `verdictAlways succ p d n` reads it: **refuted** when an explored state fails `p`,
**commit** when the explored set is closed and inside `p`, **suspended** otherwise.

* Both definite readouts are sound (`always_of_commit`, `not_always_of_refuted`) and never change
  with more budget (`verdictAlways_eq_of_le`).
* Refutation is complete on every datum (`exists_refuted_of_not_always`). Certification is complete
  exactly on finite-state data (`always_iff_exists_commit`); on an infinite-state datum that
  satisfies the specification every budget is suspended (`suspended_of_infinite`). A suspended
  verdict leaves the firing pending: an unproven obligation is a pending communication.

## Symbolic certificates, proved offline

A Pi specification on infinite-state data is lowered by a decidable predicate closed under
successors (`SymbolicInvariant`). Its obligations are one-step and induction-free; the induction
is Park's, proved once here (`SymbolicInvariant.always`, `always_iff_exists_symbolicInvariant`).

## Controls

* **The closure-free lowering is unsound** (`closure_free_unsound`). Replacing the fixed point by
  the finite disjunction it unfolds to on a fragment, without checking that the fragment is closed,
  admits a datum whose successor outside the fragment fails `p`. The closure-based verdict refutes
  it after one round.
* **Depth-bounded tree search never certifies a loop** (`tree_search_never_certifies_loop`). On a
  one-state datum with a self-loop, the tree's own bounded search (`Search.Space`, whose answers
  are here the violations) is cut off at every budget, so its refuted readout, which would certify
  "no violation", never comes. The closure verdict commits at round zero.
* **An infinite-state Pi specification is never certified by exploration, and is lowered exactly by
  an offline proof** (`parity_suspended`, `parity_exact`): states `n ↦ n + 2`, specification "always
  even".
* **A candidate invariant without its closure proof separates** (`unlicensed_invariant_wrong`):
  `n < 10` holds at `0`, is not closed under `n ↦ n + 1`, and `Always (· < 10) 0` fails.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFragments

open Search (Space)
open Search.Outcome (Verdict)

universe u

variable {R : Type u}

/-! ## Specifications about a datum's behaviour -/

section Specifications

variable (succ : R → Finset R)

/-- `e` is reachable from `d` by successor steps. -/
abbrev Reach : R → R → Prop := Relation.ReflTransGen fun a b => b ∈ succ a

/-- **A Pi specification**: every state reachable from the datum satisfies `p`. -/
def Always (p : R → Prop) (d : R) : Prop := ∀ e, Reach succ d e → p e

/-- **A Sigma specification**: some state reachable from the datum satisfies `p`. -/
def Eventually (p : R → Prop) (d : R) : Prop := ∃ e, Reach succ d e ∧ p e

/-- Finitely many states are reachable from the datum. -/
def FiniteState (d : R) : Prop := {e | Reach succ d e}.Finite

/-- **A certificate for `Always`**: a finite set holding the datum, inside `p`, closed under
successors. -/
structure Invariant (p : R → Prop) (d : R) (I : Finset R) : Prop where
  start : d ∈ I
  inside : ∀ e ∈ I, p e
  closed : ∀ e ∈ I, succ e ⊆ I

/-- **A symbolic certificate**: a predicate inside `p`, closed under successors. -/
structure SymbolicInvariant (p : R → Prop) (Inv : R → Prop) : Prop where
  inside : ∀ e, Inv e → p e
  closed : ∀ e, Inv e → ∀ e' ∈ succ e, Inv e'

end Specifications

section Laws

variable {succ : R → Finset R}

/-- **Negation swaps the polarities**: a Pi specification fails exactly when a Sigma one holds. -/
theorem not_always_iff {p : R → Prop} {d : R} :
    ¬ Always succ p d ↔ Eventually succ (fun e => ¬ p e) d := by
  simp only [Always, Eventually, not_forall, exists_prop]

theorem not_eventually_iff {p : R → Prop} {d : R} :
    ¬ Eventually succ p d ↔ Always succ (fun e => ¬ p e) d := by
  simp only [Always, Eventually, not_exists, not_and]

theorem eventually_congr {p q : R → Prop} {d : R} (same : ∀ e, p e ↔ q e) :
    Eventually succ p d ↔ Eventually succ q d :=
  ⟨fun ⟨e, reach, holds⟩ => ⟨e, reach, (same e).mp holds⟩,
    fun ⟨e, reach, holds⟩ => ⟨e, reach, (same e).mpr holds⟩⟩

/-! ## Finite certificates for Pi specifications -/

/-- Every reachable state lies in a certificate. -/
theorem Invariant.mem {p : R → Prop} {d : R} {I : Finset R} (inv : Invariant succ p d I) {e : R}
    (reach : Reach succ d e) : e ∈ I := by
  induction reach with
  | refl => exact inv.start
  | tail _ step ih => exact inv.closed _ ih step

/-- **Park induction**: a checked certificate proves the specification. -/
theorem Invariant.always {p : R → Prop} {d : R} {I : Finset R} (inv : Invariant succ p d I) :
    Always succ p d :=
  fun e reach => inv.inside e (inv.mem reach)

/-- A certificate bounds the reachable states. -/
theorem Invariant.finiteState {p : R → Prop} {d : R} {I : Finset R} (inv : Invariant succ p d I) :
    FiniteState succ d :=
  I.finite_toSet.subset fun e (reach : Reach succ d e) => Finset.mem_coe.mpr (inv.mem reach)

/-- **Certificates compose**: the intersection of two certificates certifies the conjunction. -/
theorem Invariant.inter {p q : R → Prop} {d : R} {I J : Finset R} [DecidableEq R]
    (one : Invariant succ p d I) (two : Invariant succ q d J) :
    Invariant succ (fun e => p e ∧ q e) d (I ∩ J) where
  start := Finset.mem_inter.mpr ⟨one.start, two.start⟩
  inside e member := ⟨one.inside e (Finset.mem_inter.mp member).1, two.inside e (Finset.mem_inter.mp member).2⟩
  closed e member := Finset.subset_inter (one.closed e (Finset.mem_inter.mp member).1)
    (two.closed e (Finset.mem_inter.mp member).2)

/-- The reachable states of a finite-state datum satisfying the specification are a certificate. -/
theorem invariant_reach {p : R → Prop} {d : R} (always : Always succ p d)
    (finite : FiniteState succ d) : Invariant succ p d finite.toFinset where
  start := finite.mem_toFinset.mpr Relation.ReflTransGen.refl
  inside e member := always e (finite.mem_toFinset.mp member)
  closed e member := by
    intro e' step
    exact finite.mem_toFinset.mpr (Relation.ReflTransGen.tail (finite.mem_toFinset.mp member) step)

/-- **A Pi specification has a finite certificate exactly when it holds on a finite-state datum.** -/
theorem exists_invariant_iff {p : R → Prop} {d : R} :
    (∃ I, Invariant succ p d I) ↔ Always succ p d ∧ FiniteState succ d :=
  ⟨fun ⟨_, inv⟩ => ⟨inv.always, inv.finiteState⟩,
    fun ⟨always, finite⟩ => ⟨_, invariant_reach always finite⟩⟩

/-- **A Sigma specification has a finite refutation exactly when it fails on a finite-state
datum.** -/
theorem exists_invariant_not_iff {p : R → Prop} {d : R} :
    (∃ I, Invariant succ (fun e => ¬ p e) d I) ↔ ¬ Eventually succ p d ∧ FiniteState succ d := by
  rw [exists_invariant_iff, not_eventually_iff]

/-! ## Symbolic certificates -/

/-- **Park induction for a symbolic certificate.** -/
theorem SymbolicInvariant.always {p Inv : R → Prop} (ind : SymbolicInvariant succ p Inv) {d : R}
    (start : Inv d) : Always succ p d := by
  intro e reach
  apply ind.inside
  induction reach with
  | refl => exact start
  | tail _ step ih => exact ind.closed _ ih _ step

/-- **Every Pi specification has a symbolic certificate**: reachability itself. -/
theorem always_iff_exists_symbolicInvariant {p : R → Prop} {d : R} :
    Always succ p d ↔ ∃ Inv, SymbolicInvariant succ p Inv ∧ Inv d :=
  ⟨fun always => ⟨Reach succ d,
      ⟨always, fun _ reach _ step => Relation.ReflTransGen.tail reach step⟩,
      Relation.ReflTransGen.refl⟩,
    fun ⟨_, ind, start⟩ => ind.always start⟩

/-- **An exact lowering by an offline proof**: a symbolic certificate that holds of every datum
satisfying the specification decides the specification by one test of the datum. -/
theorem always_iff_of_symbolicInvariant {p Inv : R → Prop} (ind : SymbolicInvariant succ p Inv)
    (complete : ∀ d, Always succ p d → Inv d) (d : R) : Always succ p d ↔ Inv d :=
  ⟨complete d, ind.always⟩

end Laws

/-! ## Checks: the lowered guards -/

section Checks

variable [DecidableEq R] (succ : R → Finset R)

/-- **The lowered Pi guard**: a decidable check of a candidate certificate. It tests the datum's
membership, and for each state of the certificate `p` and the inclusion of its successors. -/
def checkInvariant (p : R → Bool) (d : R) (I : Finset R) : Bool :=
  decide (d ∈ I ∧ ∀ e ∈ I, p e = true ∧ succ e ⊆ I)

/-- **The closure-free lowering**: the fragment holds the datum and lies inside `p`, and nothing
checks that it is closed. -/
def checkFragment (p : R → Bool) (d : R) (I : Finset R) : Bool :=
  decide (d ∈ I ∧ ∀ e ∈ I, p e = true)

/-- **A path certificate**: consecutive successors from the datum, ending at a state where `p`
holds. -/
def checkPath (p : R → Bool) : R → List R → Bool
  | d, [] => p d
  | d, e :: rest => decide (e ∈ succ d) && checkPath p e rest

variable {succ}

theorem checkInvariant_eq_true_iff {p : R → Bool} {d : R} {I : Finset R} :
    checkInvariant succ p d I = true ↔ Invariant succ (fun e => p e = true) d I := by
  rw [checkInvariant, decide_eq_true_iff]
  exact ⟨fun ⟨start, each⟩ => ⟨start, fun e member => (each e member).1, fun e member => (each e member).2⟩,
    fun inv => ⟨inv.start, fun e member => ⟨inv.inside e member, inv.closed e member⟩⟩⟩

/-- **The proof–run interface for a Pi guard**: on finite-state data the specification holds
exactly when some certificate checks, and a checked certificate is sound on every datum. -/
theorem always_iff_exists_checkInvariant {p : R → Bool} {d : R} (finite : FiniteState succ d) :
    Always succ (fun e => p e = true) d ↔ ∃ I, checkInvariant succ p d I = true :=
  ⟨fun always => ⟨_, checkInvariant_eq_true_iff.mpr (invariant_reach always finite)⟩,
    fun ⟨_, checks⟩ => (checkInvariant_eq_true_iff.mp checks).always⟩

/-- A checked path certifies the Sigma specification. -/
theorem eventually_of_checkPath {p : R → Bool} :
    ∀ {d : R} {path : List R}, checkPath succ p d path = true → Eventually succ (fun e => p e = true) d
  | d, [], checks => ⟨d, Relation.ReflTransGen.refl, checks⟩
  | d, e :: rest, checks => by
      simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq] at checks
      obtain ⟨f, reach, holds⟩ := eventually_of_checkPath checks.2
      exact ⟨f, Relation.ReflTransGen.head checks.1 reach, holds⟩

theorem exists_checkPath {p : R → Bool} {d e : R} (reach : Reach succ d e) (holds : p e = true) :
    ∃ path, checkPath succ p d path = true := by
  induction reach using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨[], holds⟩
  | @head a c step _ ih =>
      obtain ⟨path, checks⟩ := ih
      refine ⟨c :: path, ?_⟩
      simp only [checkPath, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨step, checks⟩

/-- **A Sigma specification always has a finite certificate.** -/
theorem eventually_iff_exists_checkPath {p : R → Bool} {d : R} :
    Eventually succ (fun e => p e = true) d ↔ ∃ path, checkPath succ p d path = true :=
  ⟨fun ⟨_, reach, holds⟩ => exists_checkPath reach holds,
    fun ⟨_, checks⟩ => eventually_of_checkPath checks⟩

/-- **A Pi specification is always refuted by a finite certificate**: a path to a failing state. -/
theorem not_always_iff_exists_checkPath {p : R → Bool} {d : R} :
    ¬ Always succ (fun e => p e = true) d ↔ ∃ path, checkPath succ (fun e => !p e) d path = true := by
  rw [not_always_iff, ← eventually_iff_exists_checkPath]
  exact eventually_congr fun e => by cases p e <;> simp

end Checks

/-! ## A budgeted guard that can certify -/

section Budget

variable [DecidableEq R] (succ : R → Finset R)

/-- **The explored set after `n` rounds**: the datum and everything within `n` successor steps. -/
def explore (d : R) : ℕ → Finset R
  | 0 => {d}
  | n + 1 => explore d n ∪ (explore d n).biUnion succ

/-- **The budgeted verdict of a Pi guard**: refuted when an explored state fails `p`, commit when
the explored set is closed and inside `p`, suspended otherwise. -/
def verdictAlways (p : R → Bool) (d : R) (n : ℕ) : Verdict :=
  if ∃ e ∈ explore succ d n, p e = false then .refuted
  else if ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n then .commit
  else .suspended

variable {succ}

theorem explore_subset_succ (d : R) (n : ℕ) : explore succ d n ⊆ explore succ d (n + 1) :=
  Finset.subset_union_left

theorem explore_mono (d : R) : Monotone (explore succ d) :=
  monotone_nat_of_le_succ (explore_subset_succ d)

theorem start_mem_explore (d : R) (n : ℕ) : d ∈ explore succ d n :=
  explore_mono d (Nat.zero_le n) (Finset.mem_singleton_self d)

/-- **Exploration is sound**: what it explores is reachable. -/
theorem reach_of_mem_explore {d e : R} : ∀ {n : ℕ}, e ∈ explore succ d n → Reach succ d e
  | 0, member => by
      simp only [explore, Finset.mem_singleton] at member
      subst member
      exact Relation.ReflTransGen.refl
  | n + 1, member => by
      rcases Finset.mem_union.mp member with old | new
      · exact reach_of_mem_explore old
      · obtain ⟨c, inC, step⟩ := Finset.mem_biUnion.mp new
        exact Relation.ReflTransGen.tail (reach_of_mem_explore inC) step

/-- **Exploration reaches every reachable state at some round.** -/
theorem exists_mem_explore {d e : R} (reach : Reach succ d e) : ∃ n, e ∈ explore succ d n := by
  induction reach with
  | refl => exact ⟨0, Finset.mem_singleton_self d⟩
  | tail _ step ih =>
      obtain ⟨n, member⟩ := ih
      exact ⟨n + 1, Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨_, member, step⟩)⟩

/-- One round covers finitely many reachable states. -/
theorem exists_explore_covers {d : R} (s : Finset R) (each : ∀ e ∈ s, Reach succ d e) :
    ∃ N, ∀ e ∈ s, e ∈ explore succ d N := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun e member => absurd member (Finset.notMem_empty e)⟩
  | insert a s _ ih =>
      obtain ⟨N, covers⟩ := ih fun e member => each e (Finset.mem_insert_of_mem member)
      obtain ⟨n, member⟩ := exists_mem_explore (each a (Finset.mem_insert_self a s))
      refine ⟨max N n, fun e inserted => ?_⟩
      rcases Finset.mem_insert.mp inserted with rfl | old
      · exact explore_mono d (le_max_right N n) member
      · exact explore_mono d (le_max_left N n) (covers e old)

theorem explore_succ_eq_of_closed {d : R} {n : ℕ}
    (closed : ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n) :
    explore succ d (n + 1) = explore succ d n :=
  Finset.union_eq_left.mpr (Finset.biUnion_subset.mpr closed)

/-- A closed explored set never grows again. -/
theorem explore_eq_of_closed {d : R} {n : ℕ}
    (closed : ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n) :
    ∀ m, n ≤ m → explore succ d m = explore succ d n := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
      have closedHere : ∀ e ∈ explore succ d m, succ e ⊆ explore succ d m := by
        rw [ih]
        exact closed
      rw [explore_succ_eq_of_closed closedHere, ih]

theorem verdictAlways_eq_refuted_iff {p : R → Bool} {d : R} {n : ℕ} :
    verdictAlways succ p d n = .refuted ↔ ∃ e ∈ explore succ d n, p e = false := by
  unfold verdictAlways
  by_cases bad : ∃ e ∈ explore succ d n, p e = false
  · rw [if_pos bad]
    exact ⟨fun _ => bad, fun _ => rfl⟩
  · rw [if_neg bad]
    by_cases closed : ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n
    · rw [if_pos closed]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h bad⟩
    · rw [if_neg closed]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h bad⟩

theorem verdictAlways_eq_commit_iff {p : R → Bool} {d : R} {n : ℕ} :
    verdictAlways succ p d n = .commit ↔
      (∀ e ∈ explore succ d n, p e = true) ∧ ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n := by
  have good : (¬ ∃ e ∈ explore succ d n, p e = false) ↔ ∀ e ∈ explore succ d n, p e = true := by
    simp only [not_exists, not_and, Bool.not_eq_false]
  unfold verdictAlways
  by_cases bad : ∃ e ∈ explore succ d n, p e = false
  · rw [if_pos bad]
    exact ⟨fun h => absurd h (by decide), fun h => absurd bad (good.mpr h.1)⟩
  · rw [if_neg bad]
    by_cases closed : ∀ e ∈ explore succ d n, succ e ⊆ explore succ d n
    · rw [if_pos closed]
      exact ⟨fun _ => ⟨good.mp bad, closed⟩, fun _ => rfl⟩
    · rw [if_neg closed]
      exact ⟨fun h => absurd h (by decide), fun h => absurd h.2 closed⟩

/-- **A commit is sound**: the explored set is a certificate. -/
theorem invariant_of_commit {p : R → Bool} {d : R} {n : ℕ}
    (h : verdictAlways succ p d n = .commit) :
    Invariant succ (fun e => p e = true) d (explore succ d n) :=
  ⟨start_mem_explore d n, ((verdictAlways_eq_commit_iff).mp h).1, ((verdictAlways_eq_commit_iff).mp h).2⟩

theorem always_of_commit {p : R → Bool} {d : R} {n : ℕ} (h : verdictAlways succ p d n = .commit) :
    Always succ (fun e => p e = true) d :=
  (invariant_of_commit h).always

/-- **A refutation is sound.** -/
theorem not_always_of_refuted {p : R → Bool} {d : R} {n : ℕ}
    (h : verdictAlways succ p d n = .refuted) : ¬ Always succ (fun e => p e = true) d := by
  obtain ⟨e, member, bad⟩ := (verdictAlways_eq_refuted_iff).mp h
  intro always
  exact Bool.false_ne_true (bad.symm.trans (always e (reach_of_mem_explore member)))

/-- **A definite verdict never changes with more budget.** -/
theorem verdictAlways_eq_of_le {p : R → Bool} {d : R} {n m : ℕ} (le : n ≤ m)
    (definite : verdictAlways succ p d n ≠ .suspended) :
    verdictAlways succ p d m = verdictAlways succ p d n := by
  cases h : verdictAlways succ p d n with
  | commit =>
      have same := explore_eq_of_closed ((verdictAlways_eq_commit_iff).mp h).2 m le
      rw [← h]
      unfold verdictAlways
      rw [same]
  | refuted =>
      obtain ⟨e, member, bad⟩ := (verdictAlways_eq_refuted_iff).mp h
      exact (verdictAlways_eq_refuted_iff).mpr ⟨e, explore_mono d le member, bad⟩
  | suspended => exact absurd h definite

/-- **Refutation is complete on every datum.** -/
theorem exists_refuted_of_not_always {p : R → Bool} {d : R}
    (h : ¬ Always succ (fun e => p e = true) d) : ∃ n, verdictAlways succ p d n = .refuted := by
  obtain ⟨e, reach, bad⟩ := (not_always_iff).mp h
  obtain ⟨n, member⟩ := exists_mem_explore reach
  exact ⟨n, (verdictAlways_eq_refuted_iff).mpr ⟨e, member, by simpa using bad⟩⟩

/-- On a finite-state datum some budget gives a definite verdict. -/
theorem exists_definite {p : R → Bool} {d : R} (finite : FiniteState succ d) :
    ∃ n, verdictAlways succ p d n ≠ .suspended := by
  obtain ⟨N, covers⟩ := exists_explore_covers finite.toFinset fun e member => finite.mem_toFinset.mp member
  have closed : ∀ e ∈ explore succ d N, succ e ⊆ explore succ d N := by
    intro e member e' step
    exact covers e' (finite.mem_toFinset.mpr
      (Relation.ReflTransGen.tail (reach_of_mem_explore member) step))
  refine ⟨N, fun suspended => ?_⟩
  by_cases bad : ∃ e ∈ explore succ d N, p e = false
  · rw [(verdictAlways_eq_refuted_iff).mpr bad] at suspended
    exact absurd suspended (by decide)
  · have good : ∀ e ∈ explore succ d N, p e = true := by
      intro e member
      by_contra no
      exact bad ⟨e, member, by simpa using no⟩
    rw [(verdictAlways_eq_commit_iff).mpr ⟨good, closed⟩] at suspended
    exact absurd suspended (by decide)

/-- **Certification is complete exactly on finite-state data.** -/
theorem always_iff_exists_commit {p : R → Bool} {d : R} (finite : FiniteState succ d) :
    Always succ (fun e => p e = true) d ↔ ∃ n, verdictAlways succ p d n = .commit := by
  constructor
  · intro always
    obtain ⟨n, definite⟩ := exists_definite (p := p) finite
    refine ⟨n, ?_⟩
    cases h : verdictAlways succ p d n with
    | commit => rfl
    | refuted => exact absurd always (not_always_of_refuted h)
    | suspended => exact absurd h definite
  · rintro ⟨n, h⟩
    exact always_of_commit h

/-- **On an infinite-state datum a Pi specification that holds is suspended at every budget.** -/
theorem suspended_of_infinite {p : R → Bool} {d : R} (infinite : ¬ FiniteState succ d)
    (always : Always succ (fun e => p e = true) d) (n : ℕ) :
    verdictAlways succ p d n = .suspended := by
  cases h : verdictAlways succ p d n with
  | commit => exact absurd (invariant_of_commit h).finiteState infinite
  | refuted => exact absurd always (not_always_of_refuted h)
  | suspended => rfl

end Budget

/-! ## Controls -/

namespace Controls

/-- `0` steps to `1`, and `1` to itself. -/
def escape : ℕ → Finset ℕ := fun n => if n = 0 then {1} else {n}

/-- Only `0` is good. -/
def zeroOnly : ℕ → Bool := fun n => n == 0

/-- **The closure-free lowering is unsound**: the fragment `{0}` holds `0` and lies inside the
predicate, the specification fails because `0` reaches `1`, and the closure verdict refutes after
one round. -/
theorem closure_free_unsound :
    checkFragment zeroOnly 0 {0} = true ∧
      ¬ Always escape (fun e => zeroOnly e = true) 0 ∧
      verdictAlways escape zeroOnly 0 1 = .refuted := by
  refine ⟨by decide, fun always => ?_, by decide⟩
  have bad := always 1 (Relation.ReflTransGen.single (by decide : 1 ∈ escape 0))
  exact absurd bad (by decide)

/-- One state with a self-loop. -/
def loop : Unit → Finset Unit := fun _ => {()}

/-- The same datum as a space of the tree's bounded search: its answers are the violations, and
it has none. -/
def loopSpace : Space Unit Empty := ⟨fun _ => [.inr ()]⟩

theorem loopSpace_item : ∀ n : ℕ, loopSpace.item (.inr ()) (List.replicate n 0) = some (.inr ())
  | 0 => rfl
  | n + 1 => by
      rw [List.replicate_succ, Space.item_inr_cons]
      exact loopSpace_item n

theorem loopSpace_cutOff (n : ℕ) : (loopSpace.run n (.inr ())).status = .cutOff :=
  (loopSpace.status_run_eq_cutOff_iff n (.inr ())).mpr
    ⟨List.replicate n 0, (), loopSpace_item n, by simp⟩

/-- **Depth-bounded tree search never certifies a loop; the closure verdict commits at once.** The
tree search's refuted readout ("finished with no violation") never comes, at any budget. -/
theorem tree_search_never_certifies_loop :
    verdictAlways loop (fun _ => true) () 0 = .commit ∧
      ∀ n, (loopSpace.approx n (.inr ())).verdict ≠ .refuted :=
  ⟨by decide, fun n => loopSpace.verdict_ne_refuted_of_cutOff (loopSpace_cutOff n)⟩

/-- Each state steps to the state two above it. -/
def twoStep : ℕ → Finset ℕ := fun n => {n + 2}

theorem twoStep_reach (k : ℕ) : Reach twoStep 0 (2 * k) := by
  induction k with
  | zero => exact Relation.ReflTransGen.refl
  | succ k ih => exact Relation.ReflTransGen.tail ih (Finset.mem_singleton.mpr (by omega))

theorem twoStep_infinite : ¬ FiniteState twoStep 0 := fun finite =>
  Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * k)
    (fun a b (same : 2 * a = 2 * b) => by omega) (fun k => twoStep_reach k) finite

theorem parity_symbolic :
    SymbolicInvariant twoStep (fun n => n % 2 = 0) (fun n => n % 2 = 0) :=
  ⟨fun _ holds => holds, fun e holds e' step => by
    rw [Finset.mem_singleton.mp step]
    omega⟩

/-- **An offline proof lowers an infinite-state Pi specification exactly** to one test. -/
theorem parity_exact (d : ℕ) : Always twoStep (fun n => n % 2 = 0) d ↔ d % 2 = 0 :=
  always_iff_of_symbolicInvariant parity_symbolic
    (fun d always => always d Relation.ReflTransGen.refl) d

/-- **Exploration never certifies it**: every budget is suspended. -/
theorem parity_suspended (n : ℕ) : verdictAlways twoStep (fun e => e % 2 == 0) 0 n = .suspended :=
  suspended_of_infinite twoStep_infinite
    (fun e reach => by simpa using (parity_exact 0).mpr rfl e reach) n

/-- Each state steps to the next. -/
def countUp : ℕ → Finset ℕ := fun n => {n + 1}

theorem countUp_reach : ∀ k : ℕ, Reach countUp 0 k
  | 0 => Relation.ReflTransGen.refl
  | k + 1 => Relation.ReflTransGen.tail (countUp_reach k) (Finset.mem_singleton.mpr rfl)

/-- **A candidate invariant without its closure proof separates**: `n < 10` holds at `0`, is not
closed, and the specification fails. -/
theorem unlicensed_invariant_wrong :
    (0 : ℕ) < 10 ∧ ¬ Always countUp (fun n => n < 10) 0 ∧
      ¬ ∀ e : ℕ, e < 10 → ∀ e' ∈ countUp e, e' < 10 :=
  ⟨by decide, fun always => absurd (always 10 (countUp_reach 10)) (by decide),
    fun closed => absurd (closed 9 (by decide) 10 (Finset.mem_singleton.mpr rfl)) (by decide)⟩

end Controls

#print axioms not_always_iff
#print axioms Invariant.always
#print axioms Invariant.finiteState
#print axioms Invariant.inter
#print axioms exists_invariant_iff
#print axioms exists_invariant_not_iff
#print axioms SymbolicInvariant.always
#print axioms always_iff_exists_symbolicInvariant
#print axioms always_iff_of_symbolicInvariant
#print axioms checkInvariant_eq_true_iff
#print axioms always_iff_exists_checkInvariant
#print axioms eventually_iff_exists_checkPath
#print axioms not_always_iff_exists_checkPath
#print axioms reach_of_mem_explore
#print axioms exists_mem_explore
#print axioms invariant_of_commit
#print axioms always_of_commit
#print axioms not_always_of_refuted
#print axioms verdictAlways_eq_of_le
#print axioms exists_refuted_of_not_always
#print axioms always_iff_exists_commit
#print axioms suspended_of_infinite
#print axioms Controls.closure_free_unsound
#print axioms Controls.tree_search_never_certifies_loop
#print axioms Controls.twoStep_infinite
#print axioms Controls.parity_exact
#print axioms Controls.parity_suspended
#print axioms Controls.unlicensed_invariant_wrong

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardFragments
