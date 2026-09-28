import Mettapedia.GSLT.LanguageDef.HostGoalDelimiters
import Mettapedia.GSLT.LanguageDef.HostCallControls

/-!
# Controls for host goals evaluated by the machines

Concrete runs over the substitution store, evaluated through
`substitutionStoreByFuel_eq` and checked by `decide`, as in `HostCallControls`.
`(pairs)` is a relation of the program with the equations `(= (pairs) Z)` and
`(= (pairs) (S Z))`, so it answers `Z` and then `(S Z)`, as
`(superpose (Z (S Z)))` does.  It is a host relation of the tier, and its goals
are evaluated by the machines (`referenceHost`, `outputFirstHost`).

* **The same stream as inline** (`pairs_runs`).  `(let $x (pairs) (pair $x
  $x))` delivers `(pair Z Z)` and then `(pair (S Z) (S Z))` in four runs:
  output at return and output first, with `(pairs)` a host goal (each
  exhausted after 8 steps) and with `(pairs)` run inline (after 5).  `pairs_refines`
  instantiates `machines_query_answers_of_moded`.
* **The destination is observable** (`blind_runs`).  `(let (S $y) (pairs)
  $y)` delivers `Z` once in the reference and in the output-first machine with
  its host.  `blindHost` evaluates the goal by the output-first machine but
  ignores its destination: both answers of `(pairs)` resume the tier, whose
  frame does not unify on return, and the run delivers two answers with `$y`
  unbound.  Every other hypothesis of `hosted_query_terminates` holds for it,
  so it meets no specification (`blind_not_correct`).
* **Delimiters** (`pairs_delimiters`).  With no destination both hosts' `once`
  of `(pairs)` is `Z` and both collect `[Z, (S Z)]`.  Against the destination
  `(S $5)` the output-first host collects `[(S Z)]` and its `once` is `(S Z)`,
  while the reference's `once` is `Z`: the case `once_host` excludes.
* **`GoalsModed` is needed.**  `(= (f $x) (let $u (succ $x) (pair $x $u)))`
  with a primitive `succ` that reads its argument through the store, and
  `(f $a)` a host goal against the destination `(pair (S Z) $b)`: the
  reference host exhausts the goal without an answer, the output-first host
  delivers `(pair (S Z) (S (S Z)))` (`prim_host_collect`), and the tier sees
  the difference (`prim_hosted_runs`).  So the two hosts meet no
  specification for this program (`prim_not_correct`); its programs are
  related by `ProgramBindsAhead`, so its host goal is not moded
  (`prim_goals_not_moded`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals.Controls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.LanguageDef.HostCalls.Controls
open Mettapedia.GSLT.LanguageDef.HostGoals
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Two answers, then a continuation -/

/-- `(= (pairs) Z)` and `(= (pairs) (S Z))`: the goal `(pairs)` answers `Z`
and then `(S Z)`, as `(superpose (Z (S Z)))` does. -/
def pairsProgram : EqProgram L HRel Empty :=
  [(.pairs, ⟨0, [], .ret zero⟩), (.pairs, ⟨0, [], .ret (succ zero)⟩)]

/-- The reference with host calls, every host goal evaluated by the
output-at-return machine. -/
abbrev hostedReference (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (hostedAtReturn L store HRel.isHost pairsProgram
    (referenceHost L store pairsProgram))) n (liftState (queryState L query pairFrame start))

/-- The output-first machine with host calls, every host goal evaluated by the
output-first machine against its destination. -/
abbrev hostedOutputFirst (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (hostedFirst L store HRel.isHost pairsProgram
    (outputFirstHost L store pairsProgram))) n (liftState (queryStateOut L query pairFrame start))

/-- The output-at-return machine running `(pairs)` inline. -/
abbrev inlineReference (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (compiled L store pairsProgram)) n (queryState L query pairFrame start)

/-- The output-first machine running `(pairs)` inline. -/
abbrev inlineFirst (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (outputFirst L store pairsProgram)) n (queryStateOut L query pairFrame start)

/-- **The same stream through the hosts as inline.**  `(let $x (pairs) (pair $x
$x))` delivers `(pair Z Z)` and then `(pair (S Z) (S Z))` in all four runs: with
`(pairs)` a host goal evaluated by the machines, each run exhausted after 8
steps, and with `(pairs)` run inline, after 5. -/
theorem pairs_runs :
    (hostedReference pairQuery 8).frontier = [] ∧
      (hostedReference pairQuery 8).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] ∧
      (hostedOutputFirst pairQuery 8).frontier = [] ∧
      (hostedOutputFirst pairQuery 8).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] ∧
      (inlineReference pairQuery 5).frontier = [] ∧
      (inlineReference pairQuery 5).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] ∧
      (inlineFirst pairQuery 5).frontier = [] ∧
      (inlineFirst pairQuery 5).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] := by
  unfold hostedReference hostedOutputFirst inlineReference inlineFirst
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Every task is moded: there are no primitives or tests. -/
theorem every_moded
    (t : Task Unit (Control L HRel Empty (Subst sig × ℕ)) (ReturnFrame L HRel Empty)) :
    Moded L exact t :=
  substitution_moded id noPrim noTest (fun op => op.elim) t

/-- The host goals of `pairsProgram` are moded. -/
theorem pairs_goals_moded : GoalsModed L store exact HRel.isHost pairsProgram :=
  goalsModed_of_moded every_moded

/-- The machines as hosts meet the specification for `pairsProgram`. -/
def pairsCorrect :
    HostCorrect exact HRel.isHost (referenceHost L store pairsProgram)
      (outputFirstHost L store pairsProgram) :=
  machinesCorrect L store exact (programBindsAhead_refl L pairsProgram) pairs_goals_moded

/-- **The law, with the machines as hosts.**  No host hypothesis is left. -/
theorem pairs_refines (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer exact) (hostedReference pairQuery n).emitted
      (hostedOutputFirst pairQuery n').emitted :=
  machines_query_answers_of_moded (programBindsAhead_refl L pairsProgram) every_moded
    (BindsAhead.refl pairQuery) pairFrame start (start_wellFormed noPrim noTest) n

/-! ## A host that ignores the destination -/

/-- The output-first machine evaluating the goal without its destination. -/
def blindHost (PF : EqProgram L HRel Empty) :
    Host (DestCall (Term sig) (Subst sig × ℕ) HRel)
      (List (Task Unit (DestControl L HRel Empty (Subst sig × ℕ)) (DestFrame L HRel Empty)))
      (Answer (Term sig) (Subst sig × ℕ)) :=
  machineHost (outputFirst L store PF) fun c => goalTasksOut L store PF (c.1, c.2.1, c.2.2.1, none)

/-- `(let (S $y) (pairs) $y)`: the host call's pattern `(S $y)` is its
destination. -/
def succQuery : Code L HRel Empty 1 := .letCall (succ (.var 0)) .pairs [] (.ret (.var 0))

/-- The output-first machine with the blind host. -/
abbrev blindRun (n : ℕ) :=
  repeats (step (hostedFirst L store HRel.isHost pairsProgram (blindHost pairsProgram))) n
    (liftState (queryStateOut L succQuery pairFrame start))

/-- An answer read through its store, as a numeral. -/
def readNumeral (a : Unit × Answer (Term sig) (Subst sig × ℕ)) : Option ℕ :=
  numeral (a.2.2.1.applyTerm a.2.1)

/-- **The destination is observable.**  The reference delivers `Z` once: the
answer `Z` of `(pairs)` does not match `(S $y)`.  So does the output-first
machine with its host, which meets the destination when it activates the
equations of `(pairs)`.  The blind host delivers both answers of `(pairs)`,
and an output-first frame does not unify on return, so `$y` is never bound:
two answers, neither a numeral. -/
theorem blind_runs :
    (hostedReference succQuery 8).frontier = [] ∧
      (hostedReference succQuery 8).emitted.map readNumeral = [some 0] ∧
      (hostedOutputFirst succQuery 5).frontier = [] ∧
      (hostedOutputFirst succQuery 5).emitted.map readNumeral = [some 0] ∧
      (blindRun 8).frontier = [] ∧ (blindRun 8).emitted.map readNumeral = [none, none] ∧
      ∀ n < 8, (blindRun n).frontier ≠ [] := by
  unfold hostedReference hostedOutputFirst blindRun
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Once exhausted, the blind run has delivered its 8-step answers. -/
theorem blind_settled (n : ℕ) (done : (blindRun n).frontier = []) :
    (blindRun n).emitted = (blindRun 8).emitted := by
  obtain ⟨-, -, -, -, doneAt8, -, early⟩ := blind_runs
  by_cases below : n < 8
  · exact absurd done (early n below)
  · obtain ⟨m, rfl⟩ : ∃ m, n = 8 + m := ⟨n - 8, by omega⟩
    unfold blindRun at doneAt8 ⊢
    rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add,
      repeats_exhausted _ _ doneAt8]

/-- **The blind host meets no specification.**  Every other hypothesis of
`hosted_query_terminates` holds for it, with the reference host refining
stores (`machinesRefine`), and its conclusion fails: the reference delivers one
answer, the blind host's run two. -/
theorem blind_not_correct :
    ¬ Nonempty (HostCorrect exact HRel.isHost (referenceHost L store pairsProgram)
      (blindHost pairsProgram)) := by
  rintro ⟨spec⟩
  obtain ⟨doneA, readA, -, -, -, readB, -⟩ := blind_runs
  obtain ⟨n', done, answers⟩ := hosted_query_terminates (programBindsAhead_refl L pairsProgram)
    spec (machinesRefine L store exact HRel.isHost pairsProgram) (BindsAhead.refl succQuery)
    pairFrame start (start_wellFormed noPrim noTest) (fun _ t _ => hmoded_of L exact every_moded t)
    8 doneA
  have settled := blind_settled n' done
  unfold blindRun at settled
  rw [settled] at answers
  have one : (hostedReference succQuery 8).emitted.length = 1 := by
    simpa using congrArg List.length readA
  have two : (blindRun 8).emitted.length = 2 := by
    simpa using congrArg List.length readB
  unfold hostedReference at one
  unfold blindRun at two
  have lengths := answers.length_eq
  exact absurd (one.symm.trans (lengths.trans two)) (by decide)

/-! ## Delimiters -/

/-- **`once` and `collapse` over `(pairs)`.**  With no destination, both hosts'
`once` is `Z` and both collect `[Z, (S Z)]`.  Against the destination
`(S $5)` the output-first host collects `[(S Z)]` and its `once` is `(S Z)`,
while the reference's `once` is `Z`: the reference's first answer is omitted,
so the two `once`s differ, and `once_host` excludes exactly this case. -/
theorem pairs_delimiters :
    (once (referenceHost L store pairsProgram).pull 3
        ((referenceHost L store pairsProgram).start (.pairs, [], start))).map
        (Option.map readAnswer) = some (some (some 0)) ∧
      (once (outputFirstHost L store pairsProgram).pull 3
        ((outputFirstHost L store pairsProgram).start (.pairs, [], start, none))).map
        (Option.map readAnswer) = some (some (some 0)) ∧
      (collect (referenceHost L store pairsProgram).pull 4
        ((referenceHost L store pairsProgram).start (.pairs, [], start))).map
        (List.map readAnswer) = some [some 0, some 1] ∧
      (collect (outputFirstHost L store pairsProgram).pull 4
        ((outputFirstHost L store pairsProgram).start (.pairs, [], start, none))).map
        (List.map readAnswer) = some [some 0, some 1] ∧
      (collect (outputFirstHost L store pairsProgram).pull 4
        ((outputFirstHost L store pairsProgram).start
          (.pairs, [], start, some (succ (.var 5))))).map
        (List.map readAnswer) = some [some 1] ∧
      (once (outputFirstHost L store pairsProgram).pull 3
        ((outputFirstHost L store pairsProgram).start
          (.pairs, [], start, some (succ (.var 5))))).map
        (Option.map readAnswer) = some (some (some 1)) := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-! ## A host goal that is not moded -/

/-- The relation of `(= (f $x) (let $u (succ $x) (pair $x $u)))` is a host
relation. -/
def allHost : Unit → Bool := fun _ => true

/-- An answer of a host read through its store, as a pair of numerals. -/
def readHostPair (a : Answer (Term sig) (Subst sig × ℕ)) : Option (Option ℕ × Option ℕ) :=
  numerals (a.2.1.applyTerm a.1)

/-- **A host goal only its destination determines.**  The reference host
exhausts `(f $a)` after 2 pulls without an answer: the primitive `succ` sees
`$x` unbound.  The output-first host, against the destination
`(pair (S Z) $b)`, binds `$x` at activation and delivers
`(pair (S Z) (S (S Z)))`. -/
theorem prim_host_collect :
    (collect (referenceHost L primStore (SProgram.normalize L primProgram)).pull 2
        ((referenceHost L primStore (SProgram.normalize L primProgram)).start
          ((), [.var 0], start))).map (List.map readHostPair) = some [] ∧
      (collect (outputFirstHost L primStore (SProgram.normalizeFirst L primProgram)).pull 4
        ((outputFirstHost L primStore (SProgram.normalizeFirst L primProgram)).start
          ((), [.var 0], start, some (pair (succ zero) (.var 1))))).map
        (List.map readHostPair) = some [some (some 1, some 2)] := by
  rw [show primStore = substitutionStoreByFuel id succPrim noTestUnit 64 from
    (substitutionStoreByFuel_eq id succPrim noTestUnit 64).symm]
  decide

/-- The reference with host calls on `(let (pair (S Z) $b) (f $a) (pair $a
$b))`, with `(f $a)` a host goal. -/
abbrev primReference (n : ℕ) :=
  repeats (step (hostedAtReturn L primStore allHost (SProgram.normalize L primProgram)
    (referenceHost L primStore (SProgram.normalize L primProgram)))) n
    (liftState (queryState L primQuery primFrame start))

/-- The output-first machine with host calls on the same query. -/
abbrev primFirst (n : ℕ) :=
  repeats (step (hostedFirst L primStore allHost (SProgram.normalizeFirst L primProgram)
    (outputFirstHost L primStore (SProgram.normalizeFirst L primProgram)))) n
    (liftState (queryStateOut L primQuery primFrame start))

/-- **Observable through the tier.**  The reference with host calls exhausts
its frontier after 3 steps without an answer; the output-first machine with
host calls after 5, with the answer `(pair (S Z) (S (S Z)))`. -/
theorem prim_hosted_runs :
    (primReference 3).frontier = [] ∧ (primReference 3).emitted = [] ∧
      (primFirst 5).frontier = [] ∧
      (primFirst 5).emitted.map (fun a => numerals (a.2.2.1.applyTerm a.2.1)) =
        [some (some 1, some 2)] := by
  unfold primReference primFirst
  rw [show primStore = substitutionStoreByFuel id succPrim noTestUnit 64 from
    (substitutionStoreByFuel_eq id succPrim noTestUnit 64).symm]
  decide

/-- **The machines meet no specification for this program.**  The reference
exhausts the goal without an answer, so a host meeting the specification would
exhaust it without one too (`collect_host`); the output-first host delivers
one. -/
theorem prim_not_correct :
    ¬ Nonempty (HostCorrect (substitutionExact id succPrim noTestUnit) allHost
      (referenceHost L primStore (SProgram.normalize L primProgram))
      (outputFirstHost L primStore (SProgram.normalizeFirst L primProgram))) := by
  rintro ⟨spec⟩
  obtain ⟨refRead, hostCollected⟩ := prim_host_collect
  obtain ⟨as, refCollected, none⟩ := Option.map_eq_some_iff.mp refRead
  obtain rfl : as = [] := List.map_eq_nil_iff.mp none
  obtain ⟨n', bs, collected, embeds⟩ := collect_host spec 2
    (spec.start (rel := ()) (args := [.var 0]) (dest := some (pair (succ zero) (.var 1)))
      (Q := Set.univ) rfl (start_wellFormed succPrim noTestUnit)
      (start_wellFormed succPrim noTestUnit) (by rw [Set.inter_univ]) rfl) refCollected
  rw [embeds.eq_nil] at collected
  obtain ⟨bs4, collected4, read⟩ := Option.map_eq_some_iff.mp hostCollected
  obtain rfl := collect_unique collected collected4
  simp at read

/-- **`GoalsModed` is needed.**  The programs are related by
`ProgramBindsAhead` (`programBindsAhead_normalize`), the only other hypothesis
of `machinesCorrect`, and its conclusion fails: the host goal's run is not
moded. -/
theorem prim_goals_not_moded :
    ¬ GoalsModed L primStore (substitutionExact id succPrim noTestUnit) allHost
      (SProgram.normalize L primProgram) :=
  fun moded => prim_not_correct
    ⟨machinesCorrect L primStore _ (programBindsAhead_normalize primProgram) moded⟩

end Mettapedia.GSLT.LanguageDef.HostGoals.Controls
