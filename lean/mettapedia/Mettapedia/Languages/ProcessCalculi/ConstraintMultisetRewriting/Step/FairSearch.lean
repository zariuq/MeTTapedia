import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.GuardFragments
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Liveness.FairRuns
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Commits

/-!
# Fair search on the step: monotone search firings are complete in the limit, linear ones are not

Search firings run on the step's physical layer: commits over the located store (`Commit`,
`Enabled`, `fire`), the same layer the step's admission and result are stated over. A program of
commits is a system (`commitSystem`); with an idle step its runs are infinite
(`Liveness.LTS.withIdle`), and fairness is the weak and strong fairness of `Liveness.FairRuns`.

## Monotone search is complete in the limit

A commit is monotone when it takes nothing and has no predicate query: it reads and makes.

* Along a run of a monotone program the store only grows (`state_mono`).
* **Under weak fairness of its task, a monotone commit enabled at some time fires, or an occurrence
  it would make appears first** (`fires_or_preempted`). For a commit with one made occurrence, that
  occurrence is eventually present for good (`made_present_eventually`). No finiteness of the
  program and no strong fairness is needed.
* **Branching**: a monotone commit enabled at a store stays enabled at every store reachable from
  it, unless what it makes is there already (`enabled_or_preempted`); so what it makes stays
  reachable from every reachable store (`possibly_made`, the property `AG EF`).

## The certificate is made by search

The exploration of a datum is the monotone program with one commit per edge: read the fact that a
state is reached, make the fact that its successor is (`exploration`). Identities are the states.

* What it makes is reachable (`exploration_sound`), and under weak fairness every reachable state is
  eventually made (`exploration_saturates`).
* **On a finite-state datum that satisfies the Pi specification, the store of every weakly fair run
  is eventually a certificate that the lowered guard checks** (`fair_search_certifies`): the guard
  of `GuardLowering` reads what the search firings made. Budgets are prefixes of the run, and a fact
  found within a budget is found within every larger one (`state_mono`).

## Controls

* **An unfair schedule never certifies** (`starving_unfair`, `starving_never_certifies`): it expands
  `0 → 1` and then idles while `0 → 2` stays enabled.
* **A fair run certifies** (`fork_fair`, `fork_certifies`), through the general theorem.
* **Linear search is not complete under fairness** (`race_stronglyFair`, `race_never_proves`,
  `race_proof_reachable`). Two firings race to take the goal; the dead end wins. The proof is
  reachable, and the run is strongly fair for every task, with unbounded budget, yet never proves.
  Reachability of proofs and completeness of fair search are different statements once search
  firings take. Read instead of take, and every weakly fair run proves (`read_race_proves`), and the
  proof stays reachable from every reachable store (`read_race_always_possible`).
* **Reachability does not decide fair completeness**
  (`reachability_does_not_decide_fair_completeness`). Add a firing that repairs the dead end: the
  two races reach the same stores (`race_reachable_iff`), the take race has a dead end from which no
  proof is reachable (`race_dead_end`), and every weakly fair run of the repaired race proves
  (`repair_fair_proves`). An identity of searches that keeps fair completeness must see the
  branching property `AG EF`, which reachability cannot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearch

open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire made_subset_fire
  subset_fire_of_monotone)
open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run InfinitelyOften)
open MeTTaCalculus.OccurrenceCommits.Liveness.LTS (withIdle liftTask)
open GuardFragments

universe u v

/-! ## Search firings as a system -/

section Systems

variable {O : Type u} [DecidableEq O] {L : Type v} (label : O → L)

/-- **Search firings as a system**: the store moves by firing an enabled commit of the program. -/
def commitSystem (program : Set (Commit O L)) : LTS (Finset O) (Commit O L) where
  Allowed store c := c ∈ program ∧ Enabled label store c
  next store c := fire store c

omit [DecidableEq O] in
/-- The task of one commit: the runs that fire it. -/
def task (c : Commit O L) : Option (Commit O L) → Prop := liftTask (· = c)

variable {label} {program : Set (Commit O L)}

/-- A step idles, or fires an enabled commit of the program. -/
theorem state_succ (r : Run (commitSystem label program).withIdle) (m : ℕ) :
    r.state (m + 1) = r.state m ∨
      ∃ c ∈ program, Enabled label (r.state m) c ∧ r.label m = some c ∧
        r.state (m + 1) = fire (r.state m) c := by
  have allowed := r.allowed m
  have step := r.step m
  cases h : r.label m with
  | none =>
      rw [h] at step
      exact Or.inl step
  | some c =>
      rw [h] at allowed step
      obtain ⟨member, enabled⟩ := allowed
      exact Or.inr ⟨c, member, enabled, rfl, step⟩

theorem state_subset_succ (monotone : ∀ c ∈ program, c.Monotone)
    (r : Run (commitSystem label program).withIdle) (m : ℕ) : r.state m ⊆ r.state (m + 1) := by
  rcases state_succ r m with same | ⟨c, member, -, -, next⟩
  · intro o present
    rw [same]
    exact present
  · rw [next]
    exact subset_fire_of_monotone (monotone c member)

/-- **Along a run of a monotone program the store only grows.** -/
theorem state_mono (monotone : ∀ c ∈ program, c.Monotone)
    (r : Run (commitSystem label program).withIdle) : Monotone r.state :=
  monotone_nat_of_le_succ (state_subset_succ monotone r)

/-- **A persistently enabled monotone commit fires, or is pre-empted** by an occurrence it would
make, under weak fairness of its task. -/
theorem fires_or_preempted (monotone : ∀ c ∈ program, c.Monotone)
    (r : Run (commitSystem label program).withIdle) {c : Commit O L} (fair : r.WeaklyFair (task c))
    (member : c ∈ program) {N : ℕ} (enabled : Enabled label (r.state N) c) :
    ∃ n ≥ N, r.label n = some c ∨ ¬ Disjoint c.made (r.state n) := by
  by_contra never
  push Not at never
  have enabledAt : ∀ n ≥ N, Enabled label (r.state n) c := fun n le =>
    { taken_subset := by
        rw [(monotone c member).1]
        exact Finset.empty_subset _
      kept_subset := enabled.kept_subset.trans (state_mono monotone r le)
      apart := enabled.apart
      fresh := (never n le).2
      queries_hold := by
        rw [(monotone c member).2]
        intro q inQueries
        cases inQueries }
  obtain ⟨n, le, fired⟩ := fair.fires N fun n le _ =>
    ⟨some c, rfl, (⟨member, enabledAt n le⟩ : c ∈ program ∧ Enabled label (r.state n) c)⟩
  have labelled : r.label n = some c := by
    cases h : r.label n with
    | none =>
        rw [h] at fired
        exact (fired : False).elim
    | some c' =>
        rw [h] at fired
        exact congrArg some (fired : c' = c)
  exact (never n le).1 labelled

/-- **What a fairly treated monotone commit makes is eventually present for good**, when it makes
one occurrence. -/
theorem made_present_eventually (monotone : ∀ c ∈ program, c.Monotone)
    (r : Run (commitSystem label program).withIdle) {c : Commit O L} (fair : r.WeaklyFair (task c))
    (member : c ∈ program) {o : O} (single : c.made = {o}) {N : ℕ}
    (enabled : Enabled label (r.state N) c) : ∃ n ≥ N, ∀ m ≥ n, o ∈ r.state m := by
  obtain ⟨n, le, fired | preempted⟩ := fires_or_preempted monotone r fair member enabled
  · refine ⟨n + 1, by omega, fun m later => state_mono monotone r later ?_⟩
    have step := r.step n
    rw [fired] at step
    rw [step]
    exact made_subset_fire (by rw [single]; exact Finset.mem_singleton_self o)
  · rw [single, Finset.disjoint_singleton_left, not_not] at preempted
    exact ⟨n, le, fun m later => state_mono monotone r later preempted⟩

omit [DecidableEq O] in
theorem eq_some_of_task {c : Commit O L} {a : Option (Commit O L)} (fired : task c a) : a = some c := by
  cases a with
  | none => exact (fired : False).elim
  | some c' => exact congrArg some (fired : c' = c)

/-! ### Branching: monotone search keeps every proof possible -/

/-- An execution of a smaller program is an execution of a larger one. -/
theorem exec_of_subset {program' : Set (Commit O L)} (sub : program ⊆ program') {s s' : Finset O}
    {l : List (Commit O L)} (exec : (commitSystem label program).Exec s l s') :
    (commitSystem label program').Exec s l s' := by
  induction exec with
  | nil s => exact .nil s
  | @cons s a l s' allowed _ ih =>
      obtain ⟨member, enabled⟩ := allowed
      exact .cons (⟨sub member, enabled⟩ : a ∈ program' ∧ Enabled label s a) ih

/-- Along an execution of a monotone program the store only grows. -/
theorem exec_superset (monotone : ∀ c ∈ program, c.Monotone) {s s' : Finset O}
    {l : List (Commit O L)} (exec : (commitSystem label program).Exec s l s') : s ⊆ s' := by
  induction exec with
  | nil s => exact Finset.Subset.refl s
  | @cons s a l s' allowed _ ih =>
      obtain ⟨member, -⟩ := allowed
      exact Finset.Subset.trans (subset_fire_of_monotone (monotone a member)) ih

/-- **A monotone commit enabled at a state stays enabled at every state reachable from it**, unless
an occurrence it would make is there already. -/
theorem enabled_or_preempted (monotone : ∀ c ∈ program, c.Monotone) {c : Commit O L}
    (monotoneC : c.Monotone) {s s' : Finset O} {l : List (Commit O L)}
    (enabled : Enabled label s c) (exec : (commitSystem label program).Exec s l s') :
    Enabled label s' c ∨ ¬ Disjoint c.made s' := by
  by_cases fresh : Disjoint c.made s'
  · exact Or.inl
      { taken_subset := by
          rw [monotoneC.1]
          exact Finset.empty_subset _
        kept_subset := enabled.kept_subset.trans (exec_superset monotone exec)
        apart := enabled.apart
        fresh := fresh
        queries_hold := by
          rw [monotoneC.2]
          intro q inQueries
          cases inQueries }
  · exact Or.inr fresh

/-- **Monotone search keeps every proof possible**: once a monotone commit making `o` is enabled,
`o` stays reachable from every state reachable from there (`AG EF`). -/
theorem possibly_made (monotone : ∀ c ∈ program, c.Monotone) {c : Commit O L} (member : c ∈ program)
    {o : O} (single : c.made = {o}) {s : Finset O} (enabled : Enabled label s c) {s' : Finset O}
    (reach : (commitSystem label program).Reachable s s') :
    ∃ s'', (commitSystem label program).Reachable s' s'' ∧ o ∈ s'' := by
  obtain ⟨l, exec⟩ := reach
  rcases enabled_or_preempted monotone (monotone c member) enabled exec with still | preempted
  · refine ⟨fire s' c, ⟨[c], .cons (⟨member, still⟩ : c ∈ program ∧ Enabled label s' c) (.nil _)⟩, ?_⟩
    exact made_subset_fire (by rw [single]; exact Finset.mem_singleton_self o)
  · rw [single, Finset.disjoint_singleton_left, not_not] at preempted
    exact ⟨s', ⟨[], .nil _⟩, preempted⟩

end Systems

/-! ## The exploration program -/

section Exploration

variable {R : Type u} [DecidableEq R] (succ : R → Finset R)

/-- **Expanding an edge**: read the fact that `e` is reached and make the fact that `e'` is. -/
def edge (e e' : R) : Commit R R := ⟨∅, {e}, {e'}, []⟩

/-- **The exploration of a datum**: one search firing per edge. -/
def exploration : Set (Commit R R) := {c | ∃ e, ∃ e' ∈ succ e, c = edge e e'}

omit [DecidableEq R] in
theorem exploration_monotone : ∀ c ∈ exploration succ, c.Monotone := by
  rintro c ⟨e, e', -, rfl⟩
  exact ⟨rfl, rfl⟩

variable {succ}

/-- **The exploration is sound**: it makes only reachable states. -/
theorem exploration_sound {d : R} (r : Run (commitSystem id (exploration succ)).withIdle)
    (start : r.state 0 = {d}) : ∀ n, ∀ e ∈ r.state n, Reach succ d e
  | 0, e, member => by
      rw [start, Finset.mem_singleton] at member
      subst member
      exact Relation.ReflTransGen.refl
  | n + 1, e, member => by
      rcases state_succ r n with same | ⟨c, ⟨a, a', step, rfl⟩, enabled, -, next⟩
      · rw [same] at member
        exact exploration_sound r start n e member
      · rw [next] at member
        rcases mem_fire.mp member with ⟨old, -⟩ | made
        · exact exploration_sound r start n e old
        · rw [Finset.mem_singleton.mp made]
          exact Relation.ReflTransGen.tail
            (exploration_sound r start n a (enabled.kept_subset (Finset.mem_singleton_self a))) step

/-- **Under weak fairness the exploration makes every reachable state**, for good. -/
theorem exploration_saturates {d : R} (r : Run (commitSystem id (exploration succ)).withIdle)
    (start : r.state 0 = {d}) (fair : ∀ c ∈ exploration succ, r.WeaklyFair (task c)) {e : R}
    (reach : Reach succ d e) : ∃ N, ∀ n ≥ N, e ∈ r.state n := by
  induction reach with
  | refl =>
      refine ⟨0, fun n _ => state_mono (exploration_monotone succ) r (Nat.zero_le n) ?_⟩
      rw [start]
      exact Finset.mem_singleton_self d
  | @tail b e' _ step ih =>
      obtain ⟨N, present⟩ := ih
      by_cases already : e' ∈ r.state N
      · exact ⟨N, fun n le => state_mono (exploration_monotone succ) r le already⟩
      · have member : edge b e' ∈ exploration succ := ⟨b, e', step, rfl⟩
        have enabled : Enabled id (r.state N) (edge b e') :=
          { taken_subset := Finset.empty_subset _
            kept_subset := Finset.singleton_subset_iff.mpr (present N le_rfl)
            apart := Finset.disjoint_empty_left _
            fresh := Finset.disjoint_singleton_left.mpr already
            queries_hold := fun _ inQueries => by cases inQueries }
        obtain ⟨n, -, always⟩ :=
          made_present_eventually (exploration_monotone succ) r (fair _ member) member rfl enabled
        exact ⟨n, always⟩

/-- **Fair search makes the certificate.** On a finite-state datum that satisfies the Pi
specification, the store of every weakly fair run of the exploration is eventually, and from then
on, a certificate that the lowered guard checks. -/
theorem fair_search_certifies {d : R} {p : R → Bool} (finite : FiniteState succ d)
    (always : Always succ (fun e => p e = true) d)
    (r : Run (commitSystem id (exploration succ)).withIdle) (start : r.state 0 = {d})
    (fair : ∀ c ∈ exploration succ, r.WeaklyFair (task c)) :
    ∃ N, ∀ n ≥ N, checkInvariant succ p d (r.state n) = true := by
  have covers : ∀ s : Finset R, (∀ e ∈ s, Reach succ d e) → ∃ N, ∀ n ≥ N, ∀ e ∈ s, e ∈ r.state n := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact fun _ => ⟨0, fun _ _ e member => absurd member (Finset.notMem_empty e)⟩
    | insert a s _ ih =>
        intro each
        obtain ⟨N, present⟩ := ih fun e member => each e (Finset.mem_insert_of_mem member)
        obtain ⟨M, here⟩ := exploration_saturates r start fair (each a (Finset.mem_insert_self a s))
        refine ⟨max N M, fun n le e member => ?_⟩
        rcases Finset.mem_insert.mp member with rfl | old
        · exact here n (le_of_max_le_right le)
        · exact present n (le_of_max_le_left le) e old
  obtain ⟨N, present⟩ := covers finite.toFinset fun e member => finite.mem_toFinset.mp member
  refine ⟨N, fun n le => checkInvariant_eq_true_iff.mpr ⟨?_, ?_, ?_⟩⟩
  · exact present n le d (finite.mem_toFinset.mpr Relation.ReflTransGen.refl)
  · intro e member
    exact always e (exploration_sound r start n e member)
  · intro e member e' step
    exact present n le e' (finite.mem_toFinset.mpr
      (Relation.ReflTransGen.tail (exploration_sound r start n e member) step))

end Exploration

/-! ## Controls -/

namespace Controls

/-- `0` steps to `1` and to `2`; nothing else steps. -/
def fork : ℕ → Finset ℕ := fun n => if n = 0 then {1, 2} else ∅

theorem fork_reach_subset {e : ℕ} (reach : Reach fork 0 e) : e ∈ ({0, 1, 2} : Finset ℕ) := by
  induction reach with
  | refl => decide
  | @tail b e' _ step _ =>
      unfold fork at step
      split_ifs at step
      · simp only [Finset.mem_insert, Finset.mem_singleton] at step
        rcases step with rfl | rfl <;> decide
      · simp at step

theorem fork_finite : FiniteState fork 0 :=
  (Finset.finite_toSet {0, 1, 2}).subset fun _ (reach : Reach fork 0 _) =>
    Finset.mem_coe.mpr (fork_reach_subset reach)

theorem edge_ne : edge (0 : ℕ) 1 ≠ edge 0 2 := fun same =>
  absurd (congrArg Commit.made same) (by decide)

theorem edge_two_mem : edge (0 : ℕ) 2 ∈ exploration fork := ⟨0, 2, by decide, rfl⟩

/-- Expand `0 → 1`, then idle. -/
def starving : Run (commitSystem id (exploration fork)).withIdle where
  state n := if n = 0 then {0} else {0, 1}
  label n := if n = 0 then some (edge 0 1) else none
  allowed n := by
    by_cases h : n = 0
    · subst h
      exact (⟨⟨0, 1, by decide, rfl⟩, by decide⟩ :
        edge 0 1 ∈ exploration fork ∧ Enabled id ({0} : Finset ℕ) (edge 0 1))
    · simp only [h, if_false]
      exact trivial
  step n := by
    by_cases h : n = 0
    · subst h
      decide
    · have later : n + 1 ≠ 0 := by omega
      simp only [h, later, if_false]
      rfl

/-- **The starving run is not weakly fair**: `0 → 2` stays enabled and never fires. -/
theorem starving_unfair : ¬ starving.WeaklyFair (task (edge 0 2)) := by
  intro fair
  have enabled : Enabled id (starving.state 1) (edge 0 2) := by decide
  obtain ⟨n, -, fired | preempted⟩ :=
    fires_or_preempted (exploration_monotone fork) starving fair edge_two_mem enabled
  · by_cases h : n = 0
    · subst h
      exact edge_ne (Option.some.inj fired)
    · have idle : starving.label n = none := if_neg h
      rw [idle] at fired
      cases fired
  · apply preempted
    by_cases h : n = 0
    · subst h
      decide
    · have state : starving.state n = {0, 1} := if_neg h
      rw [state]
      decide

/-- **The starving run never certifies**: its store is never closed. -/
theorem starving_never_certifies (n : ℕ) :
    checkInvariant fork (fun _ => true) 0 (starving.state n) = false := by
  by_cases h : n = 0
  · subst h
    decide
  · have state : starving.state n = {0, 1} := if_neg h
    rw [state]
    decide

/-- Expand `0 → 1`, then `0 → 2`, then idle. -/
def fairRun : Run (commitSystem id (exploration fork)).withIdle where
  state n := if n = 0 then {0} else if n = 1 then {0, 1} else {0, 1, 2}
  label n := if n = 0 then some (edge 0 1) else if n = 1 then some (edge 0 2) else none
  allowed n := by
    by_cases h : n = 0
    · subst h
      exact (⟨⟨0, 1, by decide, rfl⟩, by decide⟩ :
        edge 0 1 ∈ exploration fork ∧ Enabled id ({0} : Finset ℕ) (edge 0 1))
    · by_cases h' : n = 1
      · subst h'
        exact (⟨edge_two_mem, by decide⟩ :
          edge 0 2 ∈ exploration fork ∧ Enabled id ({0, 1} : Finset ℕ) (edge 0 2))
      · simp only [h, h', if_false]
        exact trivial
  step n := by
    by_cases h : n = 0
    · subst h
      decide
    · by_cases h' : n = 1
      · subst h'
        decide
      · have later : n + 1 ≠ 0 := by omega
        have later' : n + 1 ≠ 1 := by omega
        simp only [h, h', later, later', if_false]
        rfl

theorem fairRun_late (n : ℕ) (late : 2 ≤ n) : fairRun.state n = {0, 1, 2} := by
  have h : n ≠ 0 := by omega
  have h' : n ≠ 1 := by omega
  show (if n = 0 then {0} else if n = 1 then {0, 1} else {0, 1, 2}) = ({0, 1, 2} : Finset ℕ)
  rw [if_neg h, if_neg h']

/-- A state the late store keeps is reachable. -/
theorem reach_of_kept {e e' : ℕ} (enabledLate : Enabled id ({0, 1, 2} : Finset ℕ) (edge e e')) :
    Reach fork 0 e := by
  have kept : e ∈ ({0, 1, 2} : Finset ℕ) := enabledLate.kept_subset (Finset.mem_singleton_self e)
  simp only [Finset.mem_insert, Finset.mem_singleton] at kept
  rcases kept with rfl | rfl | rfl
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single (by decide : 1 ∈ fork 0)
  · exact Relation.ReflTransGen.single (by decide : 2 ∈ fork 0)

/-- **The fair run is weakly fair for every search firing**: from time two nothing is enabled. -/
theorem fork_fair : ∀ c ∈ exploration fork, fairRun.WeaklyFair (task c) := by
  rintro c ⟨e, e', step, rfl⟩ ⟨N, enabled⟩
  exfalso
  obtain ⟨a, inTask, allowed⟩ := enabled (max N 2) (le_max_left N 2)
  cases a with
  | none => exact (inTask : False)
  | some c =>
      have same : c = edge e e' := inTask
      subst same
      obtain ⟨-, enabledLate⟩ :=
        (allowed : edge e e' ∈ exploration fork ∧ Enabled id (fairRun.state (max N 2)) (edge e e'))
      rw [fairRun_late _ (le_max_right N 2)] at enabledLate
      have made : e' ∈ ({0, 1, 2} : Finset ℕ) :=
        fork_reach_subset (Relation.ReflTransGen.tail (reach_of_kept enabledLate) step)
      exact Finset.disjoint_left.mp enabledLate.fresh (Finset.mem_singleton_self e') made

theorem fairRun_start : fairRun.state 0 = {0} := rfl

/-- **The fair run certifies**, by the general theorem. -/
theorem fork_certifies : ∃ N, ∀ n ≥ N, checkInvariant fork (fun _ => true) 0 (fairRun.state n) = true :=
  fair_search_certifies fork_finite (fun _ _ => rfl) fairRun fairRun_start fork_fair

/-! ### Linear search -/

/-- Take the goal `0`, make the dead end `1`. -/
def wrongTake : Commit ℕ ℕ := ⟨{0}, ∅, {1}, []⟩

/-- Take the goal `0`, make the proof `2`. -/
def rightTake : Commit ℕ ℕ := ⟨{0}, ∅, {2}, []⟩

/-- Two firings race to take the goal. -/
def takeRace : Set (Commit ℕ ℕ) := {wrongTake, rightTake}

/-- The dead end wins, then the run idles. -/
def raceRun : Run (commitSystem id takeRace).withIdle where
  state n := if n = 0 then {0} else {1}
  label n := if n = 0 then some wrongTake else none
  allowed n := by
    by_cases h : n = 0
    · subst h
      exact (⟨Or.inl rfl, by decide⟩ : wrongTake ∈ takeRace ∧ Enabled id ({0} : Finset ℕ) wrongTake)
    · simp only [h, if_false]
      exact trivial
  step n := by
    by_cases h : n = 0
    · subst h
      decide
    · have later : n + 1 ≠ 0 := by omega
      simp only [h, later, if_false]
      rfl

/-- **The race run is strongly fair for every task**: after the first step nothing is enabled. -/
theorem race_stronglyFair (t : Commit ℕ ℕ → Prop) : raceRun.StronglyFair (liftTask t) := by
  intro often
  exfalso
  obtain ⟨n, le, a, inTask, allowed⟩ := often 1
  cases a with
  | none => exact (inTask : False)
  | some c =>
      have state : raceRun.state n = {1} := if_neg (by omega)
      obtain ⟨member, enabled⟩ := (allowed : c ∈ takeRace ∧ Enabled id (raceRun.state n) c)
      rw [state] at enabled
      rcases member with rfl | rfl
      · exact absurd (enabled.taken_subset (Finset.mem_singleton_self 0)) (by decide)
      · exact absurd (enabled.taken_subset (Finset.mem_singleton_self 0)) (by decide)

/-- **The race run never proves.** -/
theorem race_never_proves (n : ℕ) : (2 : ℕ) ∉ raceRun.state n := by
  by_cases h : n = 0
  · subst h
    decide
  · have state : raceRun.state n = {1} := if_neg h
    rw [state]
    decide

/-- **The proof is reachable.** -/
theorem race_proof_reachable :
    ∃ s, (commitSystem id takeRace).Reachable {0} s ∧ (2 : ℕ) ∈ s :=
  ⟨fire {0} rightTake, ⟨[rightTake], .cons (⟨Or.inr rfl, by decide⟩ :
      rightTake ∈ takeRace ∧ Enabled id ({0} : Finset ℕ) rightTake) (.nil _)⟩, by decide⟩

/-- Read the goal, make the dead end. -/
def wrongRead : Commit ℕ ℕ := ⟨∅, {0}, {1}, []⟩

/-- Read the goal, make the proof. -/
def rightRead : Commit ℕ ℕ := ⟨∅, {0}, {2}, []⟩

/-- The same race, reading the goal. -/
def readRace : Set (Commit ℕ ℕ) := {wrongRead, rightRead}

theorem readRace_monotone : ∀ c ∈ readRace, c.Monotone := by
  rintro c (rfl | rfl) <;> exact ⟨rfl, rfl⟩

/-- **Read instead of take, and every weakly fair run proves.** -/
theorem read_race_proves (r : Run (commitSystem id readRace).withIdle) (start : r.state 0 = {0})
    (fair : r.WeaklyFair (task rightRead)) : ∃ n, ∀ m ≥ n, (2 : ℕ) ∈ r.state m := by
  have enabled : Enabled id (r.state 0) rightRead := by
    rw [start]
    decide
  obtain ⟨n, -, always⟩ := made_present_eventually readRace_monotone r fair (Or.inr rfl) rfl enabled
  exact ⟨n, always⟩

/-- **The read race keeps the proof possible from every reachable store.** -/
theorem read_race_always_possible (s : Finset ℕ) (reach : (commitSystem id readRace).Reachable {0} s) :
    ∃ s', (commitSystem id readRace).Reachable s s' ∧ (2 : ℕ) ∈ s' :=
  possibly_made readRace_monotone (Or.inr rfl) rfl (by decide) reach

/-! ### Reachability does not decide fair completeness -/

/-- Take the dead end `1`, make the proof `2`. -/
def repair : Commit ℕ ℕ := ⟨{1}, ∅, {2}, []⟩

/-- The take race with a repair of the dead end. -/
def repairRace : Set (Commit ℕ ℕ) := {wrongTake, rightTake, repair}

/-- The stores the races reach. -/
def RaceStore (s : Finset ℕ) : Prop := s = {0} ∨ s = {1} ∨ s = {2}

theorem repair_step {s : Finset ℕ} {c : Commit ℕ ℕ} (store : RaceStore s) (member : c ∈ repairRace)
    (enabled : Enabled id s c) :
    (s = {0} ∧ (fire s c = {1} ∨ fire s c = {2})) ∨ (s = {1} ∧ fire s c = {2}) := by
  rcases member with rfl | rfl | rfl <;> rcases store with rfl | rfl | rfl <;>
    first
    | exact Or.inl ⟨rfl, by decide⟩
    | exact Or.inr ⟨rfl, by decide⟩
    | exact absurd enabled (by decide)

theorem repair_exec_store {s s' : Finset ℕ} {l : List (Commit ℕ ℕ)}
    (exec : (commitSystem id repairRace).Exec s l s') : RaceStore s → RaceStore s' := by
  induction exec with
  | nil => exact id
  | @cons s c l s' allowed _ ih =>
      intro store
      obtain ⟨member, enabled⟩ := allowed
      apply ih
      rcases repair_step store member enabled with ⟨-, h | h⟩ | ⟨-, h⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inr (Or.inr h)

/-- **The take race and the repaired race reach the same stores.** -/
theorem race_reachable_iff (s : Finset ℕ) :
    (commitSystem id takeRace).Reachable {0} s ↔ (commitSystem id repairRace).Reachable {0} s := by
  constructor
  · rintro ⟨l, exec⟩
    refine ⟨l, exec_of_subset ?_ exec⟩
    rintro c (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  · rintro ⟨l, exec⟩
    rcases repair_exec_store exec (Or.inl rfl) with rfl | rfl | rfl
    · exact ⟨[], .nil _⟩
    · have result : fire {0} wrongTake = {1} := by decide
      rw [← result]
      exact ⟨[wrongTake], .cons (⟨Or.inl rfl, by decide⟩ :
        wrongTake ∈ takeRace ∧ Enabled id ({0} : Finset ℕ) wrongTake) (.nil _)⟩
    · have result : fire {0} rightTake = {2} := by decide
      rw [← result]
      exact ⟨[rightTake], .cons (⟨Or.inr rfl, by decide⟩ :
        rightTake ∈ takeRace ∧ Enabled id ({0} : Finset ℕ) rightTake) (.nil _)⟩

/-- **The take race reaches a dead end**: from `{1}` no store with the proof is reachable. -/
theorem race_dead_end :
    (commitSystem id takeRace).Reachable {0} {1} ∧
      ∀ s, (commitSystem id takeRace).Reachable {1} s → (2 : ℕ) ∉ s := by
  refine ⟨?_, ?_⟩
  · have result : fire {0} wrongTake = {1} := by decide
    rw [← result]
    exact ⟨[wrongTake], .cons (⟨Or.inl rfl, by decide⟩ :
      wrongTake ∈ takeRace ∧ Enabled id ({0} : Finset ℕ) wrongTake) (.nil _)⟩
  · rintro s ⟨l, exec⟩
    cases exec with
    | nil => decide
    | cons allowed _ =>
        obtain ⟨member, enabled⟩ := allowed
        rcases member with rfl | rfl
        · exact absurd enabled (by decide)
        · exact absurd enabled (by decide)

theorem repair_run_store (r : Run (commitSystem id repairRace).withIdle) (start : r.state 0 = {0}) :
    ∀ n, RaceStore (r.state n)
  | 0 => Or.inl start
  | n + 1 => by
      rcases state_succ r n with same | ⟨c, member, enabled, -, next⟩
      · rw [same]
        exact repair_run_store r start n
      · rw [next]
        rcases repair_step (repair_run_store r start n) member enabled with ⟨-, h | h⟩ | ⟨-, h⟩
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inr h)

theorem repair_from_one (r : Run (commitSystem id repairRace).withIdle) (n : ℕ) (one : r.state n = {1}) :
    r.state (n + 1) = {1} ∨ r.state (n + 1) = {2} := by
  rcases state_succ r n with same | ⟨c, member, enabled, -, next⟩
  · exact Or.inl (same.trans one)
  · rw [next]
    rcases repair_step (Or.inr (Or.inl one)) member enabled with ⟨zero, -⟩ | ⟨-, h⟩
    · rw [one] at zero
      exact absurd zero (by decide)
    · exact Or.inr h

theorem repair_from_two (r : Run (commitSystem id repairRace).withIdle) (n : ℕ) (two : r.state n = {2}) :
    r.state (n + 1) = {2} := by
  rcases state_succ r n with same | ⟨c, member, enabled, -, next⟩
  · exact same.trans two
  · rw [two] at enabled
    rcases member with rfl | rfl | rfl
    · exact absurd enabled (by decide)
    · exact absurd enabled (by decide)
    · exact absurd enabled (by decide)

theorem repair_two_stays (r : Run (commitSystem id repairRace).withIdle) {n : ℕ} (two : r.state n = {2}) :
    ∀ m ≥ n, r.state m = {2} := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => exact two
  | succ m _ ih => exact repair_from_two r m ih

/-- **The repaired race proves in every weakly fair run.** -/
theorem repair_fair_proves (r : Run (commitSystem id repairRace).withIdle) (start : r.state 0 = {0})
    (fairRight : r.WeaklyFair (task rightTake)) (fairRepair : r.WeaklyFair (task repair)) :
    ∃ n, ∀ m ≥ n, r.state m = {2} := by
  have moves : ∃ n, r.state n ≠ {0} := by
    by_contra stays
    push Not at stays
    obtain ⟨n, -, fired⟩ := fairRight.fires 0 fun n _ _ => ⟨some rightTake, rfl,
      (⟨Or.inr (Or.inl rfl), by rw [stays n]; decide⟩ :
        rightTake ∈ repairRace ∧ Enabled id (r.state n) rightTake)⟩
    have step := r.step n
    rw [eq_some_of_task fired, stays n] at step
    have result : fire {0} rightTake = {2} := by decide
    exact absurd ((stays (n + 1)).symm.trans (step.trans result)) (by decide)
  obtain ⟨n, moved⟩ := moves
  rcases repair_run_store r start n with zero | one | two
  · exact absurd zero moved
  · obtain ⟨m, -, two⟩ : ∃ m ≥ n, r.state m = {2} := by
      by_contra never
      push Not at never
      have ones : ∀ m ≥ n, r.state m = {1} := by
        intro m le
        induction m, le using Nat.le_induction with
        | base => exact one
        | succ m le ih =>
            rcases repair_from_one r m ih with h | h
            · exact h
            · exact absurd h (never (m + 1) (by omega))
      obtain ⟨m, le, fired⟩ := fairRepair.fires n fun m le _ => ⟨some repair, rfl,
        (⟨Or.inr (Or.inr rfl), by rw [ones m le]; decide⟩ :
          repair ∈ repairRace ∧ Enabled id (r.state m) repair)⟩
      have step := r.step m
      rw [eq_some_of_task fired, ones m le] at step
      have result : fire {1} repair = {2} := by decide
      exact never (m + 1) (by omega) (step.trans result)
    exact ⟨m, repair_two_stays r two⟩
  · exact ⟨n, repair_two_stays r two⟩

/-- **Reachability does not decide fair completeness.** The take race and the repaired race reach
the same stores, and the proof among them; a strongly fair run of the take race never proves, while
every weakly fair run of the repaired race does. What separates them is the branching property
"from every reachable store a proof stays reachable", which the take race's dead end breaks. -/
theorem reachability_does_not_decide_fair_completeness :
    (∀ s, (commitSystem id takeRace).Reachable {0} s ↔ (commitSystem id repairRace).Reachable {0} s) ∧
      (∀ t, raceRun.StronglyFair (liftTask t)) ∧ (∀ n, (2 : ℕ) ∉ raceRun.state n) ∧
      (∀ r : Run (commitSystem id repairRace).withIdle, r.state 0 = {0} →
        r.WeaklyFair (task rightTake) → r.WeaklyFair (task repair) → ∃ n, ∀ m ≥ n, r.state m = {2}) :=
  ⟨race_reachable_iff, race_stronglyFair, race_never_proves, repair_fair_proves⟩

end Controls

#print axioms state_mono
#print axioms fires_or_preempted
#print axioms made_present_eventually
#print axioms exploration_sound
#print axioms exploration_saturates
#print axioms fair_search_certifies
#print axioms Controls.fork_finite
#print axioms Controls.starving_unfair
#print axioms Controls.starving_never_certifies
#print axioms Controls.fork_fair
#print axioms Controls.fork_certifies
#print axioms Controls.race_stronglyFair
#print axioms Controls.race_never_proves
#print axioms Controls.race_proof_reachable
#print axioms Controls.read_race_proves
#print axioms exec_superset
#print axioms enabled_or_preempted
#print axioms possibly_made
#print axioms Controls.read_race_always_possible
#print axioms Controls.race_reachable_iff
#print axioms Controls.race_dead_end
#print axioms Controls.repair_fair_proves
#print axioms Controls.reachability_does_not_decide_fair_completeness

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FairSearch
