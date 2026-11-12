import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.LanguageOnTheStep
import Mettapedia.Machines.ProgressObservation

/-!
# The effect of MM2's exec is a firing of the step; byte-least is a scheduler; MM2.1 staging is productive

MORK's MM2 keeps a **set** of atoms. An atom `(exec <loc> <patterns> <templates>)` is a program:
when it fires, every solution of its pattern conjunction is found, and every solution instantiates
the template sinks, `(+ t)` adding and `(- t)` removing. Read in MORK's source (`kernel/src/space.rs`,
`kernel/src/sinks.rs`):

* the exec with the least key fires next: each round scans from the exec prefix with PathMap's
  depth-first traversal, which descends to the first child first. PathMap documents the traversal
  as depth-first only, so the model keeps the order on keys abstract (`Program.key`);
* the exec is removed from the written space before it is interpreted, while matching reads a copy
  of the space with the exec put back: an exec sees itself;
* additions are written at once, into the written space, and are not seen by the exec's own matching;
* removals are collected and subtracted when the step ends.

So one exec step from a space `S` is `((S \ {e}) ∪ A) \ R`, with `A` and `R` the additions and
removals of every solution on `S` (`Behaviour.step`).

## The instance

* `step_eq_fire`, `commitOf_enabled`: one exec step is one enabled commit of the occurrence layer of
  the step, atoms being their own occurrences: it takes the atoms the step removes, keeps the atoms
  it matched that stay, makes the new ones.
* `effectFiring_admitted`, `effectFiring_result`: **the effect of an exec step is an admitted ground
  firing** of the first-order step over ground atoms (`mm2Step`), from every configuration holding
  the space with trivial knowledge, and its result holds the next space: reads of the pre-state,
  takes and makes for the sinks, and the exec itself among the takes unless it adds itself back.
  The firing is built from the effect: its rule takes, reads and makes exactly the commit's atoms,
  so admission checks only that the effect is enabled. It does not read the exec's patterns and does
  not check that every match was used; "every solution on the pre-state" is a property of
  `Behaviour.step`, not of the step (`Controls.incomplete_matches_admitted`). Only the direction from
  exec steps to firings is proved.

## The scheduler

* `byteLeast`: a `Scheduler` over `mm2Step` whose transition fires the effect firing of the exec with
  the least key. `byteLeast_deterministic`: from each configuration it has at most one successor.
  `byteLeast_refines`: its transitions are steps of the free exec relation (`Fires`), its paths are
  runs of the step (`Scheduler.refines`), and along them knowledge keeps identical sides, so the
  identity solves it.

## MM2.1 as staging

"MM2.1" is not in MORK's source or documentation; it is a meeting proposal for an execution
interface separating program compilation, program execution and iteration over the results, with
the variant `mm21` writing `(exec 0 (,) (0 (exec ...)))`: templates place programs at a stage
instead of into the space. `Staged` models that as a strategy layer over the exec step: an exec's
staged outputs wait at the stage; a compile event installs one into the space (administrative, not
observed); an execute event fires the least exec (observed). `staging_productive`: every infinite
staged execution keeps executing, by `ProgressObservation.nonZeno_of_rank` with the number of
staged programs as rank. Productivity is not fairness: nothing here says which exec runs.

## Controls

* `Controls.free_two_successors`, `Controls.byteLeast_misses`: two execs taking one atom; the free
  relation has two different successors, the scheduler reaches one of them and never a space
  holding the other's output. A deterministic refinement is sound and not complete.
* `Controls.batched_pre_state`: an exec that removes the atom matched by another of its solutions
  still fires that solution: matching is on the pre-state. Applying the first solution's sinks
  before matching again would lose it.
* `Controls.exec_sees_itself`: an exec whose pattern matches itself fires on itself.
* `Controls.removal_wins`: an atom added and removed by one step ends removed.
* `Controls.restaging_not_productive`: if compiling a program could stage it again, staging alone
  runs forever: productivity needs the rank.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies

namespace MM2

open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire)

variable {E : Type*} [DecidableEq E] {Sub : Type*}

/-! ## One exec step -/

/-- **What an exec does**: the solutions of its patterns in a space, the atoms each solution matched,
and the atoms each solution's sinks remove, add, and (MM2.1) stage. -/
structure Behaviour (E Sub : Type*) where
  solutions : Finset E → Finset Sub
  matched : Sub → Finset E
  matched_sub : ∀ (S : Finset E) (σ : Sub), σ ∈ solutions S → matched σ ⊆ S
  removes : Sub → Finset E
  adds : Sub → Finset E
  stages : Sub → Finset E

namespace Behaviour

variable (b : Behaviour E Sub)

/-- The atoms matched by every solution on the pre-state. -/
def read (S : Finset E) : Finset E := (b.solutions S).biUnion b.matched
/-- The atoms removed by every solution's sinks. -/
def removed (S : Finset E) : Finset E := (b.solutions S).biUnion b.removes
/-- The atoms added by every solution's sinks. -/
def added (S : Finset E) : Finset E := (b.solutions S).biUnion b.adds
/-- The programs staged by every solution's sinks (MM2.1). -/
def staged (S : Finset E) : Finset E := (b.solutions S).biUnion b.stages

/-- **One exec step**: every solution on the pre-state; the exec consumed; additions in; removals
subtracted at the end. -/
def step (S : Finset E) (e : E) : Finset E := ((S.erase e) ∪ b.added S) \ b.removed S

theorem read_sub (S : Finset E) : b.read S ⊆ S := by
  intro x member
  obtain ⟨σ, solution, inMatched⟩ := Finset.mem_biUnion.mp member
  exact b.matched_sub S σ solution inMatched

/-- **The commit of an exec step**: it takes what leaves, keeps what it matched and stays, makes
what is new. -/
def commitOf (S : Finset E) (e : E) : Commit E E :=
  ⟨S ∩ (b.removed S ∪ ({e} \ b.added S)), b.read S \ (S ∩ (b.removed S ∪ ({e} \ b.added S))),
    (b.added S \ b.removed S) \ S, []⟩

theorem commitOf_enabled (S : Finset E) (e : E) : Enabled (id : E → E) S (b.commitOf S e) where
  taken_subset := Finset.inter_subset_left
  kept_subset := (Finset.sdiff_subset).trans (b.read_sub S)
  apart := Finset.disjoint_sdiff
  fresh := Finset.sdiff_disjoint
  queries_hold := fun _ member => absurd member List.not_mem_nil

/-- **One exec step is one commit**: firing the commit gives the next space. -/
theorem step_eq_fire (S : Finset E) (e : E) : fire S (b.commitOf S e) = b.step S e := by
  ext x
  simp only [mem_fire, commitOf, step, Finset.mem_inter, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_erase]
  tauto

end Behaviour

/-! ## The exec as a firing of the step -/

/-- Ground terms of any type: the identity is the only solution and equal means identical. -/
def groundOf (E : Type*) : SubstitutionAction E Unit where
  E := Eq
  equivalence := ⟨fun _ => rfl, fun same => same.symm, fun first second => first.trans second⟩
  apply := fun _ t => t
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ _ _ same => same

/-- **The step MM2 runs on**: the first-order step over ground atoms, each atom its own occurrence. -/
abbrev mm2Step (E : Type*) [DecidableEq E] := (AnnotatedRuns.firstOrder (groundOf E) (id : E → E)).toStep

/-- **The effect firing of an exec step**: its takes, reads and makes are the commit's, as patterns
and as occurrences alike. It is built from the effect, not from the exec's patterns. -/
def effectFiring (b : Behaviour E Sub) (S : Finset E) (e : E) : AnnotatedRuns.Firing E Unit E :=
  ⟨⟨(b.commitOf S e).taken.toList, (b.commitOf S e).kept.toList, [], [], (b.commitOf S e).made.toList⟩,
    [], ⟨(b.commitOf S e).taken.toList, (b.commitOf S e).kept.toList, (b.commitOf S e).made.toList⟩⟩

omit [DecidableEq E] in
theorem equations_id : ∀ {l : List E} {q : Equation E},
    q ∈ Selection.equations (id : E → E) l l → q.1 = q.2
  | [], _, member => by simp [Selection.equations] at member
  | _ :: _, _, member => by
      simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with here | later
      · subst here
        rfl
      · exact equations_id later

/-- The knowledge an exec's effect firing leaves: what was there, and equations with identical
sides. -/
theorem problem_trivial (b : Behaviour E Sub) (S : Finset E) (e : E) {C : Configuration E E}
    (trivial : ∀ q ∈ C.equations, q.1 = q.2) :
    ∀ q ∈ (effectFiring b S e).selection.problem id (effectFiring b S e).rule C, q.1 = q.2 := by
  intro q member
  simp only [Selection.problem, List.mem_append, effectFiring, List.not_mem_nil, or_false] at member
  rcases member with (old | taken) | read
  · exact trivial q old
  · exact equations_id taken
  · exact equations_id read

/-- **The effect of an exec step is an admitted ground firing** of the step, from every
configuration holding its space with trivial knowledge. Admission checks that the effect is
enabled; it reads neither the exec's patterns nor whether every match was used
(`Controls.incomplete_matches_admitted`). -/
theorem effectFiring_admitted (b : Behaviour E Sub) (S : Finset E) (e : E) {C : Configuration E E}
    (present : C.present = S) (trivial : ∀ q ∈ C.equations, q.1 = q.2) :
    (mm2Step E).Admits (s := C) (effectFiring b S e) := by
  show PredicateQueryAdmission.Valid (groundOf E) id (effectFiring b S e).rule [] C
    (effectFiring b S e).selection
  apply (PredicateQueryAdmission.valid_empty_iff (groundOf E) id _ C _).mpr
  have enabled := b.commitOf_enabled S e
  refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, rfl, rfl, List.map_id _, ?_,
    ⟨(), problem_trivial b S e trivial⟩, ?_⟩
  · rw [present]
    exact ⟨by simpa [Selection.commit, effectFiring] using enabled.taken_subset,
      by simpa [Selection.commit, effectFiring] using enabled.kept_subset,
      by simpa [Selection.commit, effectFiring] using enabled.apart,
      by simpa [Selection.commit, effectFiring] using enabled.fresh,
      fun _ member => absurd member (by simp [Selection.commit])⟩
  · intro check member
    exact absurd member (by simp [effectFiring])

/-- **The result of an exec's effect firing holds the next space.** -/
theorem effectFiring_result (b : Behaviour E Sub) (S : Finset E) (e : E) {C : Configuration E E}
    (present : C.present = S) (admitted : (mm2Step E).Admits (s := C) (effectFiring b S e)) :
    ((mm2Step E).result (s := C) (effectFiring b S e) admitted).present = b.step S e := by
  show fire C.present ((effectFiring b S e).selection.commit (T := E)) = b.step S e
  rw [present, ← b.step_eq_fire S e]
  simp [Selection.commit, effectFiring, Behaviour.commitOf, fire]

/-! ## Programs and the byte-least scheduler -/

/-- **An MM2 program**: which atoms are execs, with what behaviour, and their keys. Keys are the
atoms' bytes, so distinct execs have distinct keys. -/
structure Program (E K Sub : Type*) [LinearOrder K] where
  exec : E → Option (Behaviour E Sub)
  key : E → K
  key_injective : ∀ a c : E, (exec a).isSome → (exec c).isSome → key a = key c → a = c

variable {K : Type*} [LinearOrder K]

namespace Program

variable (prog : Program E K Sub)

/-- `e` is the exec of the space with the least key. -/
def LeastExec (S : Finset E) (e : E) : Prop :=
  e ∈ S ∧ (prog.exec e).isSome ∧ ∀ e' ∈ S, (prog.exec e').isSome → prog.key e ≤ prog.key e'

omit [DecidableEq E] in
theorem leastExec_unique {S : Finset E} {e e' : E} (first : prog.LeastExec S e)
    (second : prog.LeastExec S e') : e = e' :=
  prog.key_injective e e' first.2.1 second.2.1
    (le_antisymm (first.2.2 e' second.1 second.2.1) (second.2.2 e first.1 first.2.1))

/-- **The free exec relation**: any exec of the space may fire. -/
def Fires (S S' : Finset E) : Prop :=
  ∃ e b, e ∈ S ∧ prog.exec e = some b ∧ S' = b.step S e

end Program

open FragmentsOfTheStep.RefinedScheduler

/-- **The byte-least scheduler**, over the step: it fires the effect firing of the least exec. -/
def byteLeast (prog : Program E K Sub) : Scheduler (mm2Step E) where
  Book := Unit
  fires C _ f _ _ := ∃ e b, prog.LeastExec C.present e ∧ prog.exec e = some b ∧
    f = effectFiring b C.present e
  moves _ _ _ := False

/-- **Byte-least is deterministic**: from each configuration at most one successor. -/
theorem byteLeast_deterministic (prog : Program E K Sub)
    {x y y' : Configuration E E × (byteLeast prog).Book}
    (first : (byteLeast prog).Transition x y) (second : (byteLeast prog).Transition x y') : y = y' := by
  cases first with
  | move impossible => exact impossible.elim
  | fire f admitted chosen =>
      cases second with
      | move impossible => exact impossible.elim
      | fire g admitted' chosen' =>
          obtain ⟨e, b, least, found, rfl⟩ := chosen
          obtain ⟨e', b', least', found', rfl⟩ := chosen'
          obtain rfl := prog.leastExec_unique least least'
          obtain rfl : b = b' := Option.some.inj (found.symm.trans found')
          rfl

/-- **Byte-least refines the free relation**: each transition is an exec step of the space; its paths
are runs of the step (`Scheduler.refines`); and along them knowledge keeps identical sides, so the
identity solves it and soundness (`Scheduler.sound`) holds at the identity. -/
theorem byteLeast_refines (prog : Program E K Sub) :
    (∀ {x y : Configuration E E × (byteLeast prog).Book}, (byteLeast prog).Transition x y →
      prog.Fires x.1.present y.1.present) ∧
    (∀ {x y : Configuration E E × (byteLeast prog).Book},
      Relation.ReflTransGen (byteLeast prog).Transition x y → ∃ r : (mm2Step E).Run x.1, r.last = y.1) ∧
    (∀ {x y : Configuration E E × (byteLeast prog).Book},
      Relation.ReflTransGen (byteLeast prog).Transition x y →
      (∀ q ∈ x.1.equations, q.1 = q.2) → ∀ q ∈ y.1.equations, q.1 = q.2) := by
  refine ⟨fun {x y} transition => ?_, fun path => Scheduler.refines path, fun {x y} path => ?_⟩
  · cases transition with
    | move impossible => exact impossible.elim
    | fire f admitted chosen =>
        obtain ⟨e, b, least, found, rfl⟩ := chosen
        exact ⟨e, b, least.1, found, effectFiring_result b _ e rfl admitted⟩
  · induction path with
    | refl => exact id
    | tail _ step earlier =>
        intro start
        have before := earlier start
        cases step with
        | move impossible => exact impossible.elim
        | fire f admitted chosen =>
            obtain ⟨e, b, least, found, rfl⟩ := chosen
            exact problem_trivial b _ e before

/-! ## MM2.1: staging as a strategy layer -/

/-- A staged configuration: the space, and the programs waiting at the stage. -/
structure Stage (E : Type*) where
  space : Finset E
  staged : Finset E

/-- **Staged events.** `compile` installs one staged program into the space, staging again what
`restage` says (nothing, in the proposal); `execute` fires the least exec, its staged outputs
joining the stage. -/
inductive StageEvent (prog : Program E K Sub) (restage : E → Finset E) : Stage E → Stage E → Type _
  | compile (S q : Finset E) (x : E) (member : x ∈ q) :
      StageEvent prog restage ⟨S, q⟩ ⟨insert x S, q.erase x ∪ restage x⟩
  | execute (S q : Finset E) (e : E) (b : Behaviour E Sub) (least : prog.LeastExec S e)
      (found : prog.exec e = some b) :
      StageEvent prog restage ⟨S, q⟩ ⟨b.step S e, q ∪ b.staged S⟩

/-- The staged configurations of a program, as a quiver of events. -/
def Staged (_prog : Program E K Sub) (_restage : E → Finset E) : Type _ := Stage E

instance (prog : Program E K Sub) (restage : E → Finset E) : Quiver (Staged prog restage) :=
  ⟨StageEvent prog restage⟩

/-- What an event shows: the exec it fires; compiling is administrative. -/
def StageEvent.label {prog : Program E K Sub} {restage : E → Finset E} :
    {a b : Stage E} → StageEvent prog restage a b → Option E
  | _, _, .compile .. => none
  | _, _, .execute _ _ e .. => some e

open Mettapedia.Machines.ProgressObservation in
/-- The observation of a staged execution. -/
def stageRead (prog : Program E K Sub) (restage : E → Finset E) :
    Observation (Staged prog restage) E :=
  fun {_ _} event => StageEvent.label (prog := prog) (restage := restage) event

theorem compile_decreases {prog : Program E K Sub} :
    ∀ {a b : Stage E} (event : StageEvent prog (fun _ => ∅) a b), event.label = none →
      b.staged.card < a.staged.card
  | _, _, .compile _ _ _ member, _ => by
      simp only [Finset.union_empty]
      exact Finset.card_erase_lt_of_mem member
  | _, _, .execute .., observed => absurd observed (by simp [StageEvent.label])

open Mettapedia.Machines.ProgressObservation in
/-- **Staging is productive**: when compiling stages nothing again, every infinite staged execution
fires execs arbitrarily far along. -/
theorem staging_productive (prog : Program E K Sub) : NonZeno (stageRead prog fun _ => ∅) :=
  nonZeno_of_rank (stageRead prog fun _ => ∅) (fun v : Staged prog (fun _ => ∅) => (Stage.staged v).card)
    (fun event erased => compile_decreases event erased)

end MM2

/-! ## Controls -/

namespace MM2.Controls

open FragmentsOfTheStep.RefinedScheduler

/-- An exec taking atom `1` and making `out`, as a behaviour over atoms numbered by `ℕ`. -/
def taker (out : ℕ) : Behaviour ℕ ℕ where
  solutions S := if 1 ∈ S then {1} else ∅
  matched σ := {σ}
  matched_sub S σ solution := by
    by_cases present : 1 ∈ S
    · simp only [present, if_true, Finset.mem_singleton] at solution
      subst solution
      exact Finset.singleton_subset_iff.mpr present
    · simp [present] at solution
  removes _ := {1}
  adds _ := {out}
  stages _ := ∅

/-- Two execs, `100` making `2` and `101` making `3`, both taking `1`. -/
def two : Program ℕ ℕ ℕ where
  exec a := if a = 100 then some (taker 2) else if a = 101 then some (taker 3) else none
  key := id
  key_injective _ _ _ _ same := same

def start : Finset ℕ := {100, 101, 1}

/-- **Negative control: the free relation has two successors.** -/
theorem free_two_successors :
    two.Fires start {101, 2} ∧ two.Fires start {100, 3} ∧ ({101, 2} : Finset ℕ) ≠ {100, 3} :=
  ⟨⟨100, taker 2, by decide, rfl, by decide⟩, ⟨101, taker 3, by decide, rfl, by decide⟩, by decide⟩

theorem least_start : two.LeastExec start 100 := by
  refine ⟨by decide, rfl, ?_⟩
  intro e' member isExec
  simp only [start, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl
  · exact le_rfl
  · show 100 ≤ 101
    omega
  · exact absurd isExec (by decide)

/-- What every byte-least path from `start` keeps: no `3` in the space. -/
theorem byteLeast_step_spaces {S S' : Finset ℕ} (reach : S = start ∨ S = {101, 2} ∨ S = {2})
    {e : ℕ} {b : Behaviour ℕ ℕ} (least : two.LeastExec S e) (found : two.exec e = some b)
    (next : S' = b.step S e) : S' = {101, 2} ∨ S' = {2} := by
  rcases reach with rfl | rfl | rfl
  · obtain rfl := two.leastExec_unique least least_start
    obtain rfl : b = taker 2 := Option.some.inj (found.symm.trans rfl)
    exact Or.inl (by rw [next]; decide)
  · have least101 : two.LeastExec {101, 2} 101 := by
      refine ⟨by decide, rfl, ?_⟩
      intro e' member isExec
      simp only [Finset.mem_insert, Finset.mem_singleton] at member
      rcases member with rfl | rfl
      · exact le_rfl
      · exact absurd isExec (by decide)
    obtain rfl := two.leastExec_unique least least101
    obtain rfl : b = taker 3 := Option.some.inj (found.symm.trans rfl)
    exact Or.inr (by rw [next]; decide)
  · obtain ⟨member, isExec, _⟩ := least
    simp only [Finset.mem_singleton] at member
    subst member
    exact absurd isExec (by decide)

/-- **Negative control: byte-least is not complete.** No path of the scheduler from `start` reaches
a space holding `3`, which the free relation reaches in one step. -/
theorem byteLeast_misses {C : Configuration ℕ ℕ} (atStart : C.present = start)
    (y : Configuration ℕ ℕ × (MM2.byteLeast two).Book)
    (path : Relation.ReflTransGen (MM2.byteLeast two).Transition (C, ()) y) :
    3 ∉ y.1.present := by
  have invariant : y.1.present = start ∨ y.1.present = {101, 2} ∨ y.1.present = {2} := by
    induction path with
    | refl => exact Or.inl atStart
    | tail _ step earlier =>
        cases step with
        | move impossible => exact impossible.elim
        | fire f admitted chosen =>
            obtain ⟨e, b, least, found, rfl⟩ := chosen
            exact Or.inr (byteLeast_step_spaces earlier least found
              (MM2.effectFiring_result b _ e rfl admitted))
  rcases invariant with same | same | same <;> rw [same] <;> decide

/-- Matches `1` and `2`; every solution removes `2` and makes `10 + σ`. -/
def snapshot : Behaviour ℕ ℕ where
  solutions S := S ∩ {1, 2}
  matched σ := {σ}
  matched_sub _ _ solution := Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp solution).1
  removes _ := {2}
  adds σ := {10 + σ}
  stages _ := ∅

/-- **Control: matching is on the pre-state.** The solution at `2` fires although another solution
of the same exec removes `2`: `12` is made. Had the solution at `1` been applied first and the
pattern matched again, `2` would be gone. -/
theorem batched_pre_state :
    snapshot.step {100, 1, 2} 100 = {1, 11, 12} ∧ 12 ∈ snapshot.step {100, 1, 2} 100 ∧
      2 ∉ ((({100, 1, 2} : Finset ℕ).erase 100 ∪ {11}) \ {2}) := by
  refine ⟨by decide, by decide, by decide⟩

/-- `snapshot` with its second solution dropped: it matches only `1`. -/
def snapshotFirst : Behaviour ℕ ℕ where
  solutions S := S ∩ {1}
  matched σ := {σ}
  matched_sub _ _ solution := Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp solution).1
  removes _ := {2}
  adds σ := {10 + σ}
  stages _ := ∅

/-- **Control: admission does not check the matches.** At `{100, 1, 2}` the effect firing of
`snapshot`, which uses both of its matches, and that of `snapshotFirst`, which skips the match at
`2`, are both admitted, and their results (`effectFiring_result`) are different spaces. That an exec
fires over all its matches is a property of `Behaviour.step`, not of the step's admission. -/
theorem incomplete_matches_admitted {C : Configuration ℕ ℕ} (present : C.present = {100, 1, 2})
    (trivial : ∀ q ∈ C.equations, q.1 = q.2) :
    (mm2Step ℕ).Admits (s := C) (effectFiring snapshot {100, 1, 2} 100) ∧
      (mm2Step ℕ).Admits (s := C) (effectFiring snapshotFirst {100, 1, 2} 100) ∧
      snapshot.step {100, 1, 2} 100 = {1, 11, 12} ∧ snapshotFirst.step {100, 1, 2} 100 = {1, 11} :=
  ⟨effectFiring_admitted snapshot _ 100 present trivial,
    effectFiring_admitted snapshotFirst _ 100 present trivial, by decide, by decide⟩

/-- An exec whose pattern matches itself, making `50`. -/
def selfMatch : Behaviour ℕ ℕ where
  solutions S := S ∩ {100}
  matched σ := {σ}
  matched_sub _ _ solution := Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp solution).1
  removes _ := ∅
  adds _ := {50}
  stages _ := ∅

/-- **Control: an exec sees itself.** Consumed from the written space, it is still read. -/
theorem exec_sees_itself : selfMatch.step {100} 100 = {50} ∧ 100 ∈ selfMatch.read {100} := by
  refine ⟨by decide, by decide⟩

/-- Adds and removes `7`. -/
def addRemove : Behaviour ℕ ℕ where
  solutions _ := {0}
  matched _ := ∅
  matched_sub _ _ _ := Finset.empty_subset _
  removes _ := {7}
  adds _ := {7}
  stages _ := ∅

/-- **Control: removal wins.** An atom added and removed in one step ends removed. -/
theorem removal_wins : 7 ∉ addRemove.step {100} 100 := by decide

open Mettapedia.Machines.ProgressObservation in
/-- **Negative control: restaging is not productive.** If compiling a program stages it again, a
staged configuration compiles forever without executing. -/
theorem restaging_not_productive : ¬ NonZeno (stageRead two fun x => {x}) := by
  intro productive
  have wf := (nonZeno_iff_wellFounded _).mp productive
  have event : Administrative (stageRead two fun x => {x})
      (⟨{0}, {0}⟩ : Staged two fun x => {x})
      (⟨insert 0 {0}, ({0} : Finset ℕ).erase 0 ∪ {0}⟩ : Staged two fun x => {x}) :=
    ⟨StageEvent.compile {0} {0} 0 (by decide), rfl⟩
  rw [show insert 0 ({0} : Finset ℕ) = {0} by decide,
    show ({0} : Finset ℕ).erase 0 ∪ {0} = {0} by decide] at event
  have irreflexive : ∀ v : Staged two (fun x => {x}),
      ¬ Administrative (stageRead two fun x => {x}) v v := fun v =>
    wf.induction v (C := fun v => ¬ Administrative (stageRead two fun x => {x}) v v)
      fun v earlier self => earlier v self self
  exact irreflexive _ event

end MM2.Controls

open MM2 in
#print axioms Behaviour.commitOf_enabled
open MM2 in
#print axioms Behaviour.step_eq_fire
#print axioms MM2.effectFiring_admitted
#print axioms MM2.effectFiring_result
#print axioms MM2.Controls.incomplete_matches_admitted
#print axioms MM2.byteLeast_deterministic
#print axioms MM2.byteLeast_refines
#print axioms MM2.staging_productive
#print axioms MM2.Controls.free_two_successors
#print axioms MM2.Controls.byteLeast_misses
#print axioms MM2.Controls.batched_pre_state
#print axioms MM2.Controls.exec_sees_itself
#print axioms MM2.Controls.removal_wins
#print axioms MM2.Controls.restaging_not_productive

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies
