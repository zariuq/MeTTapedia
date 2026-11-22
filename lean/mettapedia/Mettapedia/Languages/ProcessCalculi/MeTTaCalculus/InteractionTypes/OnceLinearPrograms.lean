import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Waves
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.BorrowedSteps

/-!
# The fragment that inherits deadlock freedom

Session-typed calculi in the line of propositions as sessions are deadlock free by construction:
every channel joins exactly two parties, each endpoint is used linearly, and the cut rule makes the
communication topology a tree. Encoded in continuation-passing style, each step of a session uses a
fresh name exactly once: one party makes a message there, the other takes it. This module
identifies the commit programs with that shape and proves that, for them, deadlock freedom is
exactly the absence of a cycle in who feeds whom, and exactly the existence of priorities.

## Once-linear programs

A **once-linear program** (`OnceLinear`) is a list of commits, each to fire at most once, with an
initial store, such that:

* no commit has a predicate query (positive);
* no two commits take one occurrence (each linear resource has one consumer);
* no commit takes what any commit keeps (kept occurrences are persistent facts, the `!` of the
  store);
* no two commits make one identity, and nothing made is initially present (one producer per
  occurrence);
* what a commit takes or keeps is initially present or made by a commit of the program.

Joins are allowed: a commit may take several occurrences at once. A commit `d` **feeds** a commit `c`
when `d` makes something `c` takes or keeps (`Feeds`).

## Deadlock freedom, exactly

A run is **maximal** when no unfired commit of the program is enabled after it; a program is
**deadlock free** when every maximal run fires every commit (`DeadlockFree`).

* **Progress** (`progress`): when feeding is acyclic, after any run some unfired commit is enabled,
  as long as one remains. A feeding-minimal unfired commit finds everything it needs.
* **A commit on a feeding cycle never fires** (`cycle_never_fires`): the first member of the cycle
  to fire would need an occurrence that only a later member makes.
* **Maximal runs exist** (`exists_maximal_run`, for every finite program), so:
* **Deadlock free ⟺ feeding acyclic** (`deadlockFree_iff_acyclic`).
* **Priorities**: a priority assignment that increases along feeding (`Prioritized`) exists
  exactly when feeding is acyclic (`exists_prioritized_iff`), so **deadlock free ⟺ typable with
  priorities** (`deadlockFree_iff_prioritized`). The check is local: each commit compares its
  priority with the priorities of the commits that supply it. This is the priority discipline of
  deadlock-free session and linear π-calculus typings, exact on this fragment. The tree discipline
  of the cut rule is a sufficient condition for acyclicity.
* All complete runs end at one store (`complete_runs_agree`).

## Outside the fragment

* **Crossed receives deadlock** (`Controls.crossed_deadlock`): two commits each taking what the
  other makes. **A crossed join** (`Controls.crossedJoin_deadlock`): a join of two messages, one of
  which is made only from the join's own result.
* **Contention breaks the theorem** (`Controls.split_philosophers_deadlock`): two philosophers who
  take their forks one at a time have an acyclic feeding relation, and still deadlock, because each
  fork has two consumers.
* A pipeline with a join and a persistent fact is typed with priorities and completes
  (`Controls.pipeline_complete`).

## Joint takes of returned resources

Contention is not deadlock by itself. At the level of bags, a program whose every rule takes its
process's token together with all the resources it needs, and returns the resources
(`JointProgram`), never deadlocks: in every reachable bag the resources are all present, and a
process waits only while its token is absent (`JointProgram.progress`). Two philosophers taking both
forks in one commit are an instance (`Controls.joint_philosophers_progress`); the same philosophers
taking one fork at a time reach a stuck bag (`Controls.split_philosophers_stuck`).

## Persistent facts

A fact that no rule takes, and that each rule keeps at most once, counts once: a bag with one more
copy of a present fact steps exactly as the bag does (`persistent_copies`). This is the store's
`!a ≅ !a ⊗ !a`. A taken atom's multiplicity is observable (`Controls.takeFork_counts`).

The bag rules and keeping rules here are the positive rules of `OccurrenceCommits.Equivalence`
(`BagRule.toRule`, `KeepRule.toRule`), and their steps are its reductions (`bagStep_iff_reduces`,
`keepStep_iff_reduces`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u v w

/-! ## Acyclic relations on a list: ranks and minimal elements -/

section Ranks

variable {α : Type w} {r : α → α → Prop}

open Classical in
/-- The rank of an element: how many elements of the list reach it. -/
noncomputable def rankIn (r : α → α → Prop) (P : List α) (c : α) : ℕ :=
  (P.toFinset.filter fun d => Relation.TransGen r d c).card

open Classical in
/-- **Ranks increase along an acyclic relation.** -/
theorem rankIn_lt (acyclic : ∀ c, ¬ Relation.TransGen r c c) {P : List α} {d c : α}
    (inP : d ∈ P) (edge : r d c) : rankIn r P d < rankIn r P c := by
  unfold rankIn
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_of_subset (fun e member => ?_) |>.mpr ⟨d, ?_, ?_⟩
  · simp only [Finset.mem_filter] at member ⊢
    exact ⟨member.1, member.2.tail edge⟩
  · simp only [Finset.mem_filter, List.mem_toFinset]
    exact ⟨inP, .single edge⟩
  · simp only [Finset.mem_filter, not_and]
    exact fun _ => acyclic d

/-- **A nonempty part of a list has a minimal element** for an acyclic relation. -/
theorem exists_minimal_of_acyclic (acyclic : ∀ c, ¬ Relation.TransGen r c c) (P : List α)
    (u : α → Prop) (nonempty : ∃ c ∈ P, u c) : ∃ c ∈ P, u c ∧ ∀ d ∈ P, u d → ¬ r d c := by
  obtain ⟨c, ⟨inP, uc⟩, minimal⟩ := (measure (rankIn r P)).wf.has_min {c | c ∈ P ∧ u c}
    (by obtain ⟨c, inP, uc⟩ := nonempty; exact ⟨c, inP, uc⟩)
  refine ⟨c, inP, uc, fun d inD ud edge => minimal d ⟨inD, ud⟩ ?_⟩
  exact rankIn_lt acyclic inD edge

end Ranks

/-! ## Once-linear programs -/

section Programs

variable {O : Type u} [DecidableEq O] {R : Type v}

/-- **A once-linear program** with its initial store. -/
structure OnceLinear (P : List (Commit O R)) (S₀ : Finset O) : Prop where
  nodup : P.Nodup
  positive : ∀ c ∈ P, c.queries = []
  linearTakes : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c.taken d.taken
  persistentKeeps : ∀ c ∈ P, ∀ d ∈ P, Disjoint d.taken c.kept
  uniqueProducers : ∀ c ∈ P, ∀ d ∈ P, c ≠ d → Disjoint c.made d.made
  madeFresh : ∀ c ∈ P, Disjoint c.made S₀
  supplied : ∀ c ∈ P, ∀ o ∈ c.taken ∪ c.kept, o ∈ S₀ ∨ ∃ d ∈ P, o ∈ d.made

/-- `d` **feeds** `c`: it makes something `c` takes or keeps. -/
def Feeds (P : List (Commit O R)) (d c : Commit O R) : Prop :=
  d ∈ P ∧ c ∈ P ∧ ∃ o ∈ d.made, o ∈ c.taken ∪ c.kept

/-- Feeding has no cycle. -/
def FeedAcyclic (P : List (Commit O R)) : Prop := ∀ c, ¬ Relation.TransGen (Feeds P) c c

/-- A run of the program: an executable list of distinct commits of the program. -/
structure IsRun (label : O → R) (P : List (Commit O R)) (S₀ : Finset O) (run : List (Commit O R)) :
    Prop where
  executable : Executable label S₀ run
  nodup : run.Nodup
  subset : ∀ c ∈ run, c ∈ P

/-- A run is **maximal** when no unfired commit of the program is enabled after it. -/
def Maximal (label : O → R) (P : List (Commit O R)) (S₀ : Finset O) (run : List (Commit O R)) : Prop :=
  ∀ c ∈ P, c ∉ run → ¬ Enabled label (fireList S₀ run) c

/-- **Deadlock freedom**: every maximal run fires every commit. -/
def DeadlockFree (label : O → R) (P : List (Commit O R)) (S₀ : Finset O) : Prop :=
  ∀ run, IsRun label P S₀ run → Maximal label P S₀ run → ∀ c ∈ P, c ∈ run

/-- A priority assignment that increases along feeding. -/
def Prioritized (P : List (Commit O R)) (prio : Commit O R → ℕ) : Prop :=
  ∀ d c, Feeds P d c → prio d < prio c

variable {label : O → R}

/-- **What a run leaves**, when what it makes is fresh and made once: an occurrence is present
exactly when it was there or was made, and was not taken. -/
theorem mem_fireList_iff :
    ∀ {S : Finset O} {run : List (Commit O R)}, Executable label S run →
      (∀ d ∈ run, Disjoint d.made S) → run.Pairwise (fun d e => Disjoint d.made e.made) →
      ∀ o, o ∈ fireList S run ↔ (o ∈ S ∨ ∃ d ∈ run, o ∈ d.made) ∧ ∀ d ∈ run, o ∉ d.taken
  | S, [], _, _, _, o => by simp
  | S, c :: rest, exec, fresh, pairwise, o => by
      rw [executable_cons_iff] at exec
      obtain ⟨enabled, after⟩ := exec
      have apartRest := (List.pairwise_cons.mp pairwise).1
      have freshNext : ∀ d ∈ rest, Disjoint d.made (fire S c) := by
        intro d member
        refine Finset.disjoint_left.mpr fun x made inFire => ?_
        rcases mem_fire.mp inFire with ⟨inS, -⟩ | madeC
        · exact Finset.disjoint_left.mp (fresh d (List.mem_cons_of_mem _ member)) made inS
        · exact Finset.disjoint_left.mp (apartRest d member) madeC made
      rw [fireList_cons, mem_fireList_iff after freshNext (List.pairwise_cons.mp pairwise).2 o,
        mem_fire]
      constructor
      · rintro ⟨(⟨inS, notTaken⟩ | made) | ⟨d, inRest, made⟩, notLater⟩
        · exact ⟨Or.inl inS, fun d member => by
            rcases List.mem_cons.mp member with rfl | inRest
            · exact notTaken
            · exact notLater d inRest⟩
        · refine ⟨Or.inr ⟨c, List.mem_cons_self, made⟩, fun d member => ?_⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact fun taken => Finset.disjoint_left.mp (fresh d List.mem_cons_self) made
              (enabled.taken_subset taken)
          · exact notLater d inRest
        · refine ⟨Or.inr ⟨d, List.mem_cons_of_mem _ inRest, made⟩, fun e member => ?_⟩
          rcases List.mem_cons.mp member with rfl | inRest'
          · exact fun taken => Finset.disjoint_left.mp (fresh d (List.mem_cons_of_mem _ inRest)) made
              (enabled.taken_subset taken)
          · exact notLater e inRest'
      · rintro ⟨inS | ⟨d, member, made⟩, notTaken⟩
        · exact ⟨Or.inl (Or.inl ⟨inS, notTaken c List.mem_cons_self⟩),
            fun d inRest => notTaken d (List.mem_cons_of_mem _ inRest)⟩
        · refine ⟨?_, fun d inRest => notTaken d (List.mem_cons_of_mem _ inRest)⟩
          rcases List.mem_cons.mp member with rfl | inRest
          · exact Or.inl (Or.inr made)
          · exact Or.inr ⟨d, inRest, made⟩

variable {P : List (Commit O R)} {S₀ : Finset O}

theorem OnceLinear.pairwise_made (prog : OnceLinear P S₀) {run : List (Commit O R)}
    (nodup : run.Nodup) (subset : ∀ c ∈ run, c ∈ P) :
    run.Pairwise (fun d e => Disjoint d.made e.made) :=
  nodup.pairwise_of_forall_ne fun d inD e inE different =>
    prog.uniqueProducers d (subset d inD) e (subset e inE) different

/-- What a run of the program leaves. -/
theorem OnceLinear.mem_fireList_iff (prog : OnceLinear P S₀) {run : List (Commit O R)}
    (isRun : IsRun label P S₀ run) (o : O) :
    o ∈ fireList S₀ run ↔ (o ∈ S₀ ∨ ∃ d ∈ run, o ∈ d.made) ∧ ∀ d ∈ run, o ∉ d.taken :=
  InteractionTypes.mem_fireList_iff isRun.executable
    (fun d member => prog.madeFresh d (isRun.subset d member))
    (prog.pairwise_made isRun.nodup isRun.subset) o

/-- **Progress.** When feeding is acyclic, after any run some unfired commit is enabled, as long as
one remains. -/
theorem progress (prog : OnceLinear P S₀) (acyclic : FeedAcyclic P) {run : List (Commit O R)}
    (isRun : IsRun label P S₀ run) (remaining : ∃ c ∈ P, c ∉ run) :
    ∃ c ∈ P, c ∉ run ∧ Enabled label (fireList S₀ run) c := by
  obtain ⟨c, inP, unfired, minimal⟩ := exists_minimal_of_acyclic acyclic P (fun c => c ∉ run) remaining
  refine ⟨c, inP, unfired, ?_⟩
  have present : ∀ o ∈ c.taken ∪ c.kept, (∀ d ∈ run, o ∉ d.taken) → o ∈ fireList S₀ run := by
    intro o used notTaken
    refine (prog.mem_fireList_iff isRun o).mpr ⟨?_, notTaken⟩
    rcases prog.supplied c inP o used with initial | ⟨d, inD, made⟩
    · exact Or.inl initial
    · by_cases fired : d ∈ run
      · exact Or.inr ⟨d, fired, made⟩
      · exact absurd ⟨inD, inP, o, made, used⟩ (minimal d inD fired)
  refine ⟨fun o taken => present o (Finset.mem_union_left _ taken) fun d inRun takenD => ?_,
    fun o kept => present o (Finset.mem_union_right _ kept) fun d inRun takenD => ?_,
    prog.persistentKeeps c inP c inP, ?_, fun read member => by
      rw [prog.positive c inP] at member
      simp at member⟩
  · have different : c ≠ d := fun same => unfired (same ▸ inRun)
    exact Finset.disjoint_left.mp (prog.linearTakes c inP d (isRun.subset d inRun) different)
      taken takenD
  · exact Finset.disjoint_left.mp (prog.persistentKeeps c inP d (isRun.subset d inRun)) takenD kept
  · refine Finset.disjoint_left.mpr fun o made inStore => ?_
    obtain ⟨initial | ⟨d, inRun, madeD⟩, -⟩ := (prog.mem_fireList_iff isRun o).mp inStore
    · exact Finset.disjoint_left.mp (prog.madeFresh c inP) made initial
    · have different : c ≠ d := fun same => unfired (same ▸ inRun)
      exact Finset.disjoint_left.mp (prog.uniqueProducers c inP d (isRun.subset d inRun) different)
        made madeD

/-- **Acyclic feeding gives deadlock freedom.** -/
theorem deadlockFree_of_acyclic (prog : OnceLinear P S₀) (acyclic : FeedAcyclic P) :
    DeadlockFree label P S₀ := by
  intro run isRun maximal c inP
  by_contra unfired
  obtain ⟨d, inD, unfiredD, enabled⟩ := progress prog acyclic isRun ⟨c, inP, unfired⟩
  exact maximal d inD unfiredD enabled

/-- An occurrence on a feeding cycle has a predecessor on the cycle. -/
theorem cycle_predecessor {c : Commit O R} (cycle : Relation.TransGen (Feeds P) c c) :
    ∃ d, Feeds P d c ∧ Relation.TransGen (Feeds P) d d := by
  obtain ⟨d, path, edge⟩ := Relation.TransGen.tail'_iff.mp cycle
  exact ⟨d, edge, Relation.TransGen.head'_iff.mpr ⟨c, edge, path⟩⟩

theorem IsRun.prefix {run pre post : List (Commit O R)} {e : Commit O R}
    (isRun : IsRun label P S₀ run) (split : run = pre ++ e :: post) :
    IsRun label P S₀ pre ∧ Enabled label (fireList S₀ pre) e := by
  have exec := isRun.executable
  rw [split, executable_append_iff, executable_cons_iff] at exec
  have sub : pre.Sublist run := by rw [split]; exact List.sublist_append_left _ _
  exact ⟨⟨exec.1, isRun.nodup.sublist sub, fun c member => isRun.subset c (sub.subset member)⟩,
    exec.2.1⟩

/-- **A commit on a feeding cycle never fires.** -/
theorem cycle_never_fires (prog : OnceLinear P S₀) {run : List (Commit O R)}
    (isRun : IsRun label P S₀ run) {c : Commit O R} (cycle : Relation.TransGen (Feeds P) c c) :
    c ∉ run := by
  suffices never : ∀ n (pre post : List (Commit O R)) (e : Commit O R), pre.length = n →
      run = pre ++ e :: post → ¬ Relation.TransGen (Feeds P) e e by
    intro member
    obtain ⟨pre, post, split⟩ := List.append_of_mem member
    exact never _ pre post c rfl split cycle
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro pre post e length split cycleE
      obtain ⟨preRun, enabled⟩ := isRun.prefix split
      obtain ⟨d, ⟨inD, -, o, made, used⟩, cycleD⟩ := cycle_predecessor cycleE
      have inStore : o ∈ fireList S₀ pre := by
        rcases Finset.mem_union.mp used with taken | kept
        · exact enabled.taken_subset taken
        · exact enabled.kept_subset kept
      obtain ⟨initial | ⟨d', inPre, made'⟩, -⟩ := (prog.mem_fireList_iff preRun o).mp inStore
      · exact Finset.disjoint_left.mp (prog.madeFresh d inD) made initial
      · have same : d' = d := by
          by_contra different
          exact Finset.disjoint_left.mp
            (prog.uniqueProducers d' (preRun.subset d' inPre) d inD different) made' made
        subst same
        obtain ⟨pre₁, pre₂, preSplit⟩ := List.append_of_mem inPre
        have shorter : pre₁.length < n := by
          rw [← length, preSplit]
          simp
        exact ih _ shorter pre₁ (pre₂ ++ e :: post) d' rfl
          (by rw [split, preSplit]; simp) cycleD

/-- **Maximal runs exist**, for every finite program. -/
theorem exists_maximal_run :
    ∃ run, IsRun label P S₀ run ∧ Maximal label P S₀ run := by
  suffices grow : ∀ k (run : List (Commit O R)), IsRun label P S₀ run → P.length - run.length = k →
      ∃ run', IsRun label P S₀ run' ∧ Maximal label P S₀ run' by
    exact grow _ [] ⟨.nil _, List.nodup_nil, by simp⟩ rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
      intro run isRun count
      by_cases maximal : Maximal label P S₀ run
      · exact ⟨run, isRun, maximal⟩
      · simp only [Maximal, not_forall, not_not] at maximal
        obtain ⟨c, inP, unfired, enabled⟩ := maximal
        have extended : IsRun label P S₀ (run ++ [c]) := by
          refine ⟨?_, ?_, ?_⟩
          · rw [executable_append_iff]
            exact ⟨isRun.executable, .cons enabled (.nil _)⟩
          · exact List.nodup_append.mpr ⟨isRun.nodup, List.nodup_singleton c, by
              intro a inRun b inC same
              simp only [List.mem_singleton] at inC
              subst inC
              exact unfired (same ▸ inRun)⟩
          · intro d member
            rcases List.mem_append.mp member with inRun | inC
            · exact isRun.subset d inRun
            · simp only [List.mem_singleton] at inC
              exact inC ▸ inP
        have bound : (run ++ [c]).length ≤ P.length :=
          (List.subperm_of_subset extended.nodup extended.subset).length_le
        have shorter : P.length - (run ++ [c]).length < k := by
          rw [← count]
          simp only [List.length_append, List.length_singleton] at bound ⊢
          omega
        exact ih _ shorter _ extended rfl

/-- **Deadlock free ⟺ feeding acyclic**, for once-linear programs. -/
theorem deadlockFree_iff_acyclic (prog : OnceLinear P S₀) :
    DeadlockFree label P S₀ ↔ FeedAcyclic P := by
  refine ⟨fun free c cycle => ?_, deadlockFree_of_acyclic prog⟩
  obtain ⟨run, isRun, maximal⟩ := exists_maximal_run (label := label) (P := P) (S₀ := S₀)
  have inP : c ∈ P := by
    obtain ⟨d, ⟨-, inC, -⟩, -⟩ := cycle_predecessor cycle
    exact inC
  exact cycle_never_fires prog isRun cycle (free run isRun maximal c inP)

/-- Priorities make feeding acyclic. -/
theorem acyclic_of_prioritized {prio : Commit O R → ℕ} (prioritized : Prioritized P prio) :
    FeedAcyclic P := by
  intro c cycle
  have increase : ∀ {a b}, Relation.TransGen (Feeds P) a b → prio a < prio b := by
    intro a b path
    induction path with
    | single edge => exact prioritized _ _ edge
    | tail _ edge ih => exact ih.trans (prioritized _ _ edge)
  exact lt_irrefl _ (increase cycle)

/-- **Priorities exist exactly when feeding is acyclic.** -/
theorem exists_prioritized_iff : (∃ prio, Prioritized P prio) ↔ FeedAcyclic P :=
  ⟨fun ⟨_, prioritized⟩ => acyclic_of_prioritized prioritized, fun acyclic =>
    ⟨rankIn (Feeds P) P, fun _ _ edge => rankIn_lt acyclic edge.1 edge⟩⟩

/-- **Deadlock free ⟺ typable with priorities**, for once-linear programs. -/
theorem deadlockFree_iff_prioritized (prog : OnceLinear P S₀) :
    DeadlockFree label P S₀ ↔ ∃ prio, Prioritized P prio :=
  (deadlockFree_iff_acyclic prog).trans exists_prioritized_iff.symm

/-- **All complete runs end at one store.** -/
theorem complete_runs_agree (prog : OnceLinear P S₀) {run run' : List (Commit O R)}
    (isRun : IsRun label P S₀ run) (isRun' : IsRun label P S₀ run')
    (complete : ∀ c ∈ P, c ∈ run) (complete' : ∀ c ∈ P, c ∈ run') :
    fireList S₀ run = fireList S₀ run' := by
  ext o
  rw [prog.mem_fireList_iff isRun, prog.mem_fireList_iff isRun']
  have same : ∀ d, d ∈ run ↔ d ∈ run' := fun d =>
    ⟨fun member => complete' d (isRun.subset d member),
      fun member => complete d (isRun'.subset d member)⟩
  simp only [same]

end Programs

/-! ## Joint takes of returned resources, over bags -/

section Joint

variable {A : Type u} [DecidableEq A]

/-- A rule over bags: what it takes and what it makes. -/
structure BagRule (A : Type u) where
  take : Multiset A
  make : Multiset A

/-- One step of a list of bag rules. -/
def BagStep (Γ : List (BagRule A)) (M M' : Multiset A) : Prop :=
  ∃ ρ ∈ Γ, ρ.take ≤ M ∧ M' = M - ρ.take + ρ.make

/-- A bag where no rule is enabled. -/
def Stuck (Γ : List (BagRule A)) (M : Multiset A) : Prop := ∀ ρ ∈ Γ, ¬ ρ.take ≤ M

/-- **A program of joint takes**: process `i` has a token `token i` and a need `need i` within the
resources; its rule takes its token with its whole need, and makes its result with the need
returned. Tokens are not resources. -/
structure JointProgram (A : Type u) [DecidableEq A] (ι : Type w) where
  resources : Multiset A
  token : ι → Multiset A
  need : ι → Multiset A
  result : ι → Multiset A
  need_le : ∀ i, need i ≤ resources
  tokens_apart : ∀ i, ∀ a ∈ token i, a ∉ resources

namespace JointProgram

variable {ι : Type w} (J : JointProgram A ι)

/-- The rule of process `i`. -/
def rule (i : ι) : BagRule A := ⟨J.token i + J.need i, J.result i + J.need i⟩

/-- A step of some process's rule. -/
def Step (M M' : Multiset A) : Prop := ∃ i, (J.rule i).take ≤ M ∧ M' = M - (J.rule i).take + (J.rule i).make

theorem token_le_of_le {i : ι} {T : Multiset A} (le : (J.rule i).take ≤ J.resources + T) :
    J.token i ≤ T := by
  rw [Multiset.le_iff_count] at le ⊢
  intro a
  by_cases inToken : a ∈ J.token i
  · have zero : Multiset.count a J.resources = 0 :=
      Multiset.count_eq_zero.mpr (J.tokens_apart i a inToken)
    have := le a
    simp only [rule, Multiset.count_add, zero, zero_add] at this
    omega
  · rw [Multiset.count_eq_zero.mpr inToken]
    exact Nat.zero_le _

/-- **The resources are always all present**: every bag reachable from the resources and some
tokens is the resources plus some tokens and results. -/
theorem reachable_form {T : Multiset A} {M : Multiset A}
    (reach : Relation.ReflTransGen J.Step (J.resources + T) M) : ∃ T', M = J.resources + T' := by
  induction reach with
  | refl => exact ⟨T, rfl⟩
  | tail _ step ih =>
      obtain ⟨T', rfl⟩ := ih
      obtain ⟨i, le, rfl⟩ := step
      have tokenLe := J.token_le_of_le le
      refine ⟨T' - J.token i + J.result i, ?_⟩
      have needLe := J.need_le i
      simp only [rule]
      ext a
      simp only [Multiset.count_add, Multiset.count_sub]
      have h1 := (Multiset.le_iff_count.mp tokenLe) a
      have h2 := (Multiset.le_iff_count.mp needLe) a
      omega

/-- **Progress for joint takes**: in every reachable bag, a process whose token is present can
fire. A process waits only while its token is absent. -/
theorem progress {T M : Multiset A} (reach : Relation.ReflTransGen J.Step (J.resources + T) M)
    (i : ι) (pending : J.token i ≤ M - J.resources) : (J.rule i).take ≤ M := by
  obtain ⟨T', rfl⟩ := J.reachable_form reach
  rw [add_tsub_cancel_left] at pending
  simp only [rule]
  rw [add_comm (J.token i)]
  exact add_le_add (J.need_le i) pending

end JointProgram

/-! ### Persistent facts: the exponential of the store -/

/-- A positive rule over bags that also keeps a bag. -/
structure KeepRule (A : Type u) where
  take : Multiset A
  keep : Multiset A
  make : Multiset A

/-- One step of a list of keeping rules: what is taken and kept is present; what is taken goes,
what is made arrives. -/
def KeepStep (Γ : List (KeepRule A)) (M M' : Multiset A) : Prop :=
  ∃ ρ ∈ Γ, ρ.take + ρ.keep ≤ M ∧ M' = M - ρ.take + ρ.make

/-- A bag rule as a positive rule of the equivalence layer (`Equivalence.Rule`, querying
nothing). -/
def BagRule.toRule (ρ : BagRule A) : Equivalence.Rule A := ⟨ρ.take, 0, ρ.make, fun _ => false⟩

/-- A keeping rule as a positive rule of the equivalence layer. -/
def KeepRule.toRule (ρ : KeepRule A) : Equivalence.Rule A := ⟨ρ.take, ρ.keep, ρ.make, fun _ => false⟩

/-- **Bag steps are reductions of positive rules** (`Equivalence.Reduces`), so the bag programs of
this section are programs of the equivalence layer. -/
theorem bagStep_iff_reduces {Γ : List (BagRule A)} {M M' : Multiset A} :
    BagStep Γ M M' ↔ Equivalence.Reduces (fun ρ => ∃ r ∈ Γ, r.toRule = ρ) M M' := by
  constructor
  · rintro ⟨r, member, le, rfl⟩
    exact ⟨r.toRule, ⟨r, member, rfl⟩,
      (Equivalence.Rule.enabled_iff_of_positive (fun _ => rfl) M).mpr
        (by simpa [Equivalence.Rule.redex, BagRule.toRule] using le), rfl⟩
  · rintro ⟨_, ⟨r, member, rfl⟩, enabled, rfl⟩
    exact ⟨r, member, by simpa [Equivalence.Rule.redex, BagRule.toRule] using enabled.1, rfl⟩

/-- **Keeping steps are reductions of positive rules.** -/
theorem keepStep_iff_reduces {Γ : List (KeepRule A)} {M M' : Multiset A} :
    KeepStep Γ M M' ↔ Equivalence.Reduces (fun ρ => ∃ r ∈ Γ, r.toRule = ρ) M M' := by
  constructor
  · rintro ⟨r, member, le, rfl⟩
    exact ⟨r.toRule, ⟨r, member, rfl⟩,
      (Equivalence.Rule.enabled_iff_of_positive (fun _ => rfl) M).mpr le, rfl⟩
  · rintro ⟨_, ⟨r, member, rfl⟩, enabled, rfl⟩
    exact ⟨r, member, enabled.1, rfl⟩

/-- **A fact that no rule takes, and that each rule keeps at most once, counts once**: a bag with
one more copy of a present fact steps exactly as the bag does, keeping the extra copy aside. This
is `!a ≅ !a ⊗ !a` for facts of the store. -/
theorem persistent_copies {Γ : List (KeepRule A)} {a : A}
    (notTaken : ∀ ρ ∈ Γ, a ∉ ρ.take) (keptOnce : ∀ ρ ∈ Γ, ρ.keep.count a ≤ 1)
    {M : Multiset A} (present : a ∈ M) {N : Multiset A} :
    KeepStep Γ (M + {a}) N ↔ ∃ M', KeepStep Γ M M' ∧ N = M' + {a} := by
  constructor
  · rintro ⟨ρ, inΓ, le, rfl⟩
    have zero : ρ.take.count a = 0 := Multiset.count_eq_zero.mpr (notTaken ρ inΓ)
    have once := keptOnce ρ inΓ
    have countM : 1 ≤ M.count a := Multiset.one_le_count_iff_mem.mpr present
    have leM : ρ.take + ρ.keep ≤ M := by
      rw [Multiset.le_iff_count] at le ⊢
      intro b
      have := le b
      simp only [Multiset.count_add, Multiset.count_singleton] at this ⊢
      by_cases same : b = a
      · subst same
        omega
      · simp only [same, if_false, add_zero] at this
        exact this
    refine ⟨M - ρ.take + ρ.make, ⟨ρ, inΓ, leM, rfl⟩, ?_⟩
    ext b
    have takeLe : ρ.take.count b ≤ M.count b := by
      have := (Multiset.le_iff_count.mp leM) b
      simp only [Multiset.count_add] at this
      omega
    simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_singleton]
    omega
  · rintro ⟨M', ⟨ρ, inΓ, le, rfl⟩, rfl⟩
    refine ⟨ρ, inΓ, le.trans (Multiset.le_add_right _ _), ?_⟩
    ext b
    have takeLe : ρ.take.count b ≤ M.count b := by
      have := (Multiset.le_iff_count.mp le) b
      simp only [Multiset.count_add] at this
      omega
    simp only [Multiset.count_add, Multiset.count_sub, Multiset.count_singleton]
    omega

end Joint

/-! ## Controls -/

namespace Controls

/-- Labels play no part in these controls. -/
def noLabel : ℕ → Unit := fun _ => ()

/-- Take `1`, make `2`. -/
def takeOneMakeTwo : Commit ℕ Unit := ⟨{1}, ∅, {2}, []⟩
/-- Take `2`, make `1`. -/
def takeTwoMakeOne : Commit ℕ Unit := ⟨{2}, ∅, {1}, []⟩

theorem crossed_ne : takeOneMakeTwo ≠ takeTwoMakeOne := by
  intro same
  have := congrArg Commit.taken same
  simp [takeOneMakeTwo, takeTwoMakeOne] at this

/-- The crossed program is once-linear. -/
theorem crossed_onceLinear : OnceLinear [takeOneMakeTwo, takeTwoMakeOne] ∅ := by
  refine ⟨List.nodup_cons.mpr ⟨by simpa using crossed_ne, List.nodup_singleton _⟩, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro c inC d inD different
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl <;> rcases inD with rfl | rfl <;>
      first | exact absurd rfl different | decide
  · intro c inC d inD
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl <;> rcases inD with rfl | rfl <;> decide
  · intro c inC d inD different
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl <;> rcases inD with rfl | rfl <;>
      first | exact absurd rfl different | decide
  · intro c _; exact Finset.disjoint_empty_right _
  · intro c inC o used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inC
    rcases inC with rfl | rfl
    · simp only [takeOneMakeTwo, Finset.union_empty, Finset.mem_singleton] at used
      subst used
      exact Or.inr ⟨takeTwoMakeOne, by simp, by decide⟩
    · simp only [takeTwoMakeOne, Finset.union_empty, Finset.mem_singleton] at used
      subst used
      exact Or.inr ⟨takeOneMakeTwo, by simp, by decide⟩

/-- **Crossed receives deadlock**: each takes what only the other makes; feeding has a cycle, and
the empty run is maximal and fires nothing. -/
theorem crossed_deadlock :
    ¬ FeedAcyclic [takeOneMakeTwo, takeTwoMakeOne] ∧
      Maximal noLabel [takeOneMakeTwo, takeTwoMakeOne] ∅ [] ∧
      ¬ DeadlockFree noLabel [takeOneMakeTwo, takeTwoMakeOne] ∅ := by
  have first : Feeds [takeOneMakeTwo, takeTwoMakeOne] takeOneMakeTwo takeTwoMakeOne :=
    ⟨by simp, by simp, 2, by decide, by decide⟩
  have second : Feeds [takeOneMakeTwo, takeTwoMakeOne] takeTwoMakeOne takeOneMakeTwo :=
    ⟨by simp, by simp, 1, by decide, by decide⟩
  have cycle : Relation.TransGen (Feeds [takeOneMakeTwo, takeTwoMakeOne]) takeOneMakeTwo takeOneMakeTwo :=
    .tail (.single first) second
  refine ⟨fun acyclic => acyclic _ cycle, ?_, fun free => ?_⟩
  · intro c member _ enabled
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact absurd (enabled.taken_subset (by simp [takeOneMakeTwo] : 1 ∈ takeOneMakeTwo.taken)) (by simp)
    · exact absurd (enabled.taken_subset (by simp [takeTwoMakeOne] : 2 ∈ takeTwoMakeOne.taken)) (by simp)
  · exact (deadlockFree_iff_acyclic crossed_onceLinear).mp free _ cycle

/-- A join of `1` and `3` makes `4`. -/
def join : Commit ℕ Unit := ⟨{1, 3}, ∅, {4}, []⟩
/-- From the join's result, make `1`. -/
def feedBack : Commit ℕ Unit := ⟨{4}, ∅, {1}, []⟩

/-- **A crossed join deadlocks**: the join waits for a message made only from its own result. -/
theorem crossedJoin_deadlock :
    Relation.TransGen (Feeds [join, feedBack]) join join ∧
      Maximal noLabel [join, feedBack] {3} [] := by
  have first : Feeds [join, feedBack] join feedBack := ⟨by simp, by simp, 4, by decide, by decide⟩
  have second : Feeds [join, feedBack] feedBack join := ⟨by simp, by simp, 1, by decide, by decide⟩
  refine ⟨.tail (.single first) second, ?_⟩
  intro c member _ enabled
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact absurd (enabled.taken_subset (by simp [join] : 1 ∈ join.taken)) (by simp)
  · exact absurd (enabled.taken_subset (by simp [feedBack] : 4 ∈ feedBack.taken)) (by simp)

/-- Philosopher `0` takes the hungry token `12` and fork `10`, making `14` (holding the left fork). -/
def leftOf0 : Commit ℕ Unit := ⟨{12, 10}, ∅, {14}, []⟩
/-- Philosopher `0`, holding the left fork, takes fork `11` and eats. -/
def rightOf0 : Commit ℕ Unit := ⟨{14, 11}, ∅, {15}, []⟩
/-- Philosopher `1` takes the hungry token `13` and fork `11`. -/
def leftOf1 : Commit ℕ Unit := ⟨{13, 11}, ∅, {16}, []⟩
/-- Philosopher `1`, holding fork `11`, takes fork `10` and eats. -/
def rightOf1 : Commit ℕ Unit := ⟨{16, 10}, ∅, {17}, []⟩

/-- The split philosophers. -/
def splitPhilosophers : List (Commit ℕ Unit) := [leftOf0, rightOf0, leftOf1, rightOf1]

/-- **Contention breaks the theorem**: the split philosophers are not once-linear (fork `10` has two
consumers), and the run where each takes the left fork is maximal and leaves both hungry. -/
theorem split_philosophers_deadlock :
    ¬ OnceLinear splitPhilosophers {10, 11, 12, 13} ∧
      IsRun noLabel splitPhilosophers {10, 11, 12, 13} [leftOf0, leftOf1] ∧
      Maximal noLabel splitPhilosophers {10, 11, 12, 13} [leftOf0, leftOf1] ∧
      rightOf0 ∉ [leftOf0, leftOf1] := by
  have ne01 : leftOf0 ≠ rightOf1 := by
    intro same; exact absurd (congrArg Commit.taken same) (by decide)
  refine ⟨fun prog => ?_, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · have := prog.linearTakes leftOf0 (by simp [splitPhilosophers]) rightOf1
      (by simp [splitPhilosophers]) ne01
    exact absurd this (by decide)
  · refine .cons ⟨by decide, by decide, by decide, by decide, by simp [leftOf0]⟩ ?_
    refine .cons ⟨by decide, by decide, by decide, by decide, by simp [leftOf1]⟩ (.nil _)
  · refine List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro same; exact absurd (congrArg Commit.taken same) (by decide)
  · intro c member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp [splitPhilosophers]
  · intro c member unfired enabled
    simp only [splitPhilosophers, List.mem_cons, List.not_mem_nil, or_false] at member
    have store : fireList {10, 11, 12, 13} [leftOf0, leftOf1] = ({14, 16} : Finset ℕ) := by decide
    rw [store] at enabled
    rcases member with rfl | rfl | rfl | rfl
    · exact unfired (by simp)
    · exact absurd (enabled.taken_subset (by simp [rightOf0] : 11 ∈ rightOf0.taken)) (by decide)
    · exact unfired (by simp)
    · exact absurd (enabled.taken_subset (by simp [rightOf1] : 10 ∈ rightOf1.taken)) (by decide)
  · intro member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with same | same <;> exact absurd (congrArg Commit.taken same) (by decide)

/-- A producer of `1` from `0`. -/
def produce : Commit ℕ Unit := ⟨{0}, ∅, {1}, []⟩
/-- A join of `1` and `2`, reading the persistent fact `5`, making `3`. -/
def joinWithFact : Commit ℕ Unit := ⟨{1, 2}, {5}, {3}, []⟩
/-- A consumer of `3`, reading the fact `5`, making `4`. -/
def consume : Commit ℕ Unit := ⟨{3}, {5}, {4}, []⟩

/-- The pipeline. -/
def pipeline : List (Commit ℕ Unit) := [produce, joinWithFact, consume]

/-- The pipeline's priorities. -/
def pipelinePrio (c : Commit ℕ Unit) : ℕ := if 1 ∈ c.made then 0 else if 3 ∈ c.made then 1 else 2

theorem pipeline_prioritized : Prioritized pipeline pipelinePrio := by
  rintro d c ⟨inD, inC, o, made, used⟩
  simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at inD inC
  rcases inD with rfl | rfl | rfl <;> rcases inC with rfl | rfl | rfl <;>
    simp_all [produce, joinWithFact, consume, pipelinePrio]

theorem pipeline_onceLinear : OnceLinear pipeline {0, 2, 5} := by
  have ne12 : produce ≠ joinWithFact := by
    intro same; have := congrArg Commit.taken same; exact absurd this (by decide)
  have ne13 : produce ≠ consume := by
    intro same; have := congrArg Commit.taken same; exact absurd this (by decide)
  have ne23 : joinWithFact ≠ consume := by
    intro same; have := congrArg Commit.taken same; exact absurd this (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pipeline, ne12, ne13, ne23]
  · intro c member; simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · intro c inC d inD different
    simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl | rfl <;> rcases inD with rfl | rfl | rfl <;>
      first | exact absurd rfl different | decide
  · intro c inC d inD
    simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl | rfl <;> rcases inD with rfl | rfl | rfl <;> decide
  · intro c inC d inD different
    simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at inC inD
    rcases inC with rfl | rfl | rfl <;> rcases inD with rfl | rfl | rfl <;>
      first | exact absurd rfl different | decide
  · intro c member; simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  · intro c inC o used
    simp only [pipeline, List.mem_cons, List.not_mem_nil, or_false] at inC
    rcases inC with rfl | rfl | rfl
    · left; simp only [produce, Finset.union_empty, Finset.mem_singleton] at used; subst used; decide
    · simp only [joinWithFact, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at used
      rcases used with (rfl | rfl) | rfl
      · exact Or.inr ⟨produce, by simp [pipeline], by decide⟩
      · left; decide
      · left; decide
    · simp only [consume, Finset.mem_union, Finset.mem_singleton] at used
      rcases used with rfl | rfl
      · exact Or.inr ⟨joinWithFact, by simp [pipeline], by decide⟩
      · left; decide

/-- **The pipeline completes**: it is typed with priorities, so every maximal run fires all three
commits. -/
theorem pipeline_complete : DeadlockFree noLabel pipeline {0, 2, 5} :=
  (deadlockFree_iff_prioritized pipeline_onceLinear).mpr ⟨_, pipeline_prioritized⟩

/-! ### Philosophers over bags -/

/-- Atoms: hungry, holding the left fork, and fed, for two philosophers; two forks. -/
inductive Phil where
  | hungry0 | hungry1 | holding0 | holding1 | fed0 | fed1 | fork0 | fork1
  deriving DecidableEq, Repr

open Phil

/-- The philosophers taking both forks in one commit. -/
def jointPhilosophers : JointProgram Phil Bool where
  resources := {fork0, fork1}
  token i := if i then {hungry1} else {hungry0}
  need _ := {fork0, fork1}
  result i := if i then {fed1} else {fed0}
  need_le _ := le_refl _
  tokens_apart i a member := by
    cases i <;> simp at member <;> subst member <;> decide

/-- **Joint takes never deadlock**: from both philosophers hungry, in every reachable bag a hungry
philosopher can eat. -/
theorem joint_philosophers_progress {M : Multiset Phil}
    (reach : Relation.ReflTransGen jointPhilosophers.Step
      (jointPhilosophers.resources + {hungry0, hungry1}) M)
    (i : Bool) (pending : jointPhilosophers.token i ≤ M - jointPhilosophers.resources) :
    (jointPhilosophers.rule i).take ≤ M :=
  jointPhilosophers.progress reach i pending

/-- The philosophers taking one fork at a time, as bag rules. -/
def splitRules : List (BagRule Phil) :=
  [⟨{hungry0, fork0}, {holding0}⟩, ⟨{holding0, fork1}, {fed0, fork0, fork1}⟩,
   ⟨{hungry1, fork1}, {holding1}⟩, ⟨{holding1, fork0}, {fed1, fork0, fork1}⟩]

/-- A fact `fork0`, kept by a rule that makes `fed0`. -/
def keepFork : List (KeepRule Phil) := [⟨{hungry0}, {fork0}, {fed0}⟩]

/-- Taking the fact instead. -/
def takeFork : List (KeepRule Phil) := [⟨{fork0}, 0, {fed0}⟩]

/-- **Persistence, positive control**: with one copy of the kept fact or two, the steps agree. -/
theorem keepFork_copies {N : Multiset Phil} :
    KeepStep keepFork ({hungry0, fork0} + {fork0}) N ↔
      ∃ M', KeepStep keepFork {hungry0, fork0} M' ∧ N = M' + {fork0} :=
  persistent_copies (by simp [keepFork]) (by simp [keepFork]) (by simp)

/-- **A taken fact counts**: after one firing, a remaining copy of `fork0` lets the taker fire
again, and without it nothing fires; the multiplicity of a taken atom is observable. -/
theorem takeFork_counts :
    KeepStep takeFork ({fed0, fork0}) {fed0, fed0} ∧ ¬ KeepStep takeFork {fed0} ({fed0, fed0}) := by
  refine ⟨⟨_, List.mem_cons_self, by decide, by decide⟩, ?_⟩
  rintro ⟨ρ, member, le, -⟩
  simp only [takeFork, List.mem_cons, List.not_mem_nil, or_false] at member
  subst member
  exact absurd le (by decide)

/-- **The split philosophers reach a stuck bag** in which both are still waiting. -/
theorem split_philosophers_stuck :
    Relation.ReflTransGen (BagStep splitRules) {hungry0, hungry1, fork0, fork1} {holding0, holding1} ∧
      Stuck splitRules {holding0, holding1} := by
  refine ⟨?_, ?_⟩
  · refine .tail (.tail .refl ⟨⟨{hungry0, fork0}, {holding0}⟩, by simp [splitRules], by decide, rfl⟩)
      ⟨⟨{hungry1, fork1}, {holding1}⟩, by simp [splitRules], by decide, by decide⟩
  · intro ρ member
    simp only [splitRules, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- **Maximal, negative**: the empty run of the one-commit program "take `1`" is not maximal at
`{1}`: the commit is still enabled. (The deadlocked runs above are positive controls.) -/
theorem empty_run_not_maximal :
    ¬ Maximal noLabel [(Commit.takeOne 1 : Commit ℕ Unit)] {1} [] := fun maximal =>
  maximal _ List.mem_cons_self (List.not_mem_nil) (by decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
