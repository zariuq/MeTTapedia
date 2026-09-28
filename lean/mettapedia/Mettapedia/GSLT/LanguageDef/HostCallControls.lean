import Mettapedia.GSLT.LanguageDef.HostCallRefinement
import Mettapedia.GSLT.LanguageDef.DestinationPassingControls

/-!
# Controls for host calls

Concrete runs over the substitution store of `CompiledTwoSidedHeadProgram`,
evaluated through `substitutionStoreByFuel_eq` and checked by `decide`.  The
host relation `pairs` enumerates `Z` then `(S Z)`, as a `superpose`, and
`nothing` enumerates nothing.  The host is `enumHost`, which unifies each value
with the destination in the host's store; the reference evaluator is
`enumReference`.

* Two answers through a continuation: `(let $x (superpose (Z (S Z))) (pair $x
  $x))` delivers `(pair Z Z)` and then `(pair (S Z) (S Z))` in both machines,
  which exhaust their frontiers after 8 steps (`pair_runs`).  The law holds for
  this query (`pair_refines`).
* The hypothesis is needed: a host delivering `(S Z)` before `Z` makes the same
  continuation deliver the pairs in the other order (`reversed_runs`), not the
  reference's answers (`reversed_differs`).  Every other hypothesis of
  `hosted_query_terminates` holds, so that host meets no specification
  (`reversed_not_correct`).
* A host call with no answers: `(= (q) (let $x (nothing) (S $x)))` with
  `(= (q) Z)`.  The host is exhausted at its first pull, the first alternative
  fails and the second delivers `Z` (`empty_host_runs`); the law holds
  (`empty_refines`).
* Collections: without a destination the host and the reference collect
  `[Z, (S Z)]`; against the destination `(S $5)` the host collects `[(S Z)]`
  (`pairs_collect`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostCalls.Controls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-- Two host relations, enumerating `Z` then `(S Z)` and enumerating nothing,
and one relation of the tier. -/
inductive HRel where
  | pairs
  | nothing
  | q
  deriving DecidableEq

/-- `pairs` and `nothing` are host relations. -/
def HRel.isHost : HRel → Bool
  | .pairs => true
  | .nothing => true
  | .q => false

/-- The values each host relation enumerates. -/
def values : HRel → List (Term sig) → List (Term sig)
  | .pairs, _ => [zero, succ zero]
  | _, _ => []

/-- The same values in the other order. -/
def reversed : HRel → List (Term sig) → List (Term sig)
  | .pairs, _ => [succ zero, zero]
  | _, _ => []

/-- The substitution store without primitives or tests. -/
abbrev store := substitutionStore (σ := sig) id noPrim noTest

/-- The exact reading of that store. -/
abbrev exact := substitutionExact (σ := sig) id noPrim noTest

/-- An answer read through its store. -/
def readPair (a : Unit × Answer (Term sig) (Subst sig × ℕ)) : Option (Option ℕ × Option ℕ) :=
  numerals (a.2.2.1.applyTerm a.2.1)

/-! ## Two answers through a continuation -/

/-- `(let $x (superpose (Z (S Z))) (pair $x $x))`: the host call's pattern is
the query variable `0`, and the continuation builds a pair. -/
def pairQuery : Code L HRel Empty 1 :=
  .letCall (.var 0) .pairs [] (.ret (pair (.var 0) (.var 0)))

/-- The query's slot is the query variable `0`. -/
def pairFrame : Fin 1 → Term sig := fun _ => .var 0

/-- The output-first machine with the enumerating host. -/
abbrev firstRun (values : HRel → List (Term sig) → List (Term sig)) (n : ℕ) :=
  repeats (step (hostedFirst L store HRel.isHost ([] : EqProgram L HRel Empty)
    (enumHost store values))) n (liftState (queryStateOut L pairQuery pairFrame start))

/-- The reference with the enumerating reference evaluator. -/
abbrev referenceRun (n : ℕ) :=
  repeats (step (hostedAtReturn L store HRel.isHost ([] : EqProgram L HRel Empty)
    (enumReference values))) n (liftState (queryState L pairQuery pairFrame start))

/-- **Two answers, in order.**  The host delivers `Z` and then `(S Z)`; each
resumes the continuation, which delivers `(pair Z Z)` and then
`(pair (S Z) (S Z))`; the run has exhausted its frontier after 8 steps.  The
reference delivers the same pairs in the same 8 steps. -/
theorem pair_runs :
    (firstRun values 8).frontier = [] ∧
      (firstRun values 8).emitted.map readPair = [some (some 0, some 0), some (some 1, some 1)] ∧
      (referenceRun 8).frontier = [] ∧
      (referenceRun 8).emitted.map readPair = [some (some 0, some 0), some (some 1, some 1)] := by
  unfold firstRun referenceRun
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Every task of these runs is moded: there are no primitives or tests. -/
theorem all_moded (t : RTask L HRel Empty (Subst sig × ℕ) (List (Term sig) × (Subst sig × ℕ))) :
    HModed L exact t :=
  hmoded_of L exact (fun t => substitution_moded id noPrim noTest (fun op => op.elim) t) t

/-- **The law, instantiated.**  The enumerating host meets its specification
(`enumCorrect`), so after any number of reference steps the output-first run with
the host has delivered corresponding answers. -/
theorem pair_refines (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer exact) (referenceRun n).emitted (firstRun values n').emitted :=
  hosted_query_answers (programBindsAhead_refl L []) (enumCorrect exact values HRel.isHost)
    (enumRefines exact values HRel.isHost) (BindsAhead.refl pairQuery) pairFrame start
    (start_wellFormed noPrim noTest) (fun _ t _ => all_moded t) n

/-! ## A host that changes the order -/

/-- **The order is observable.**  A host that delivers `(S Z)` before `Z` makes
the same continuation deliver the pairs in the other order. -/
theorem reversed_runs :
    (firstRun reversed 8).frontier = [] ∧
      (firstRun reversed 8).emitted.map readPair = [some (some 1, some 1), some (some 0, some 0)] ∧
      ∀ n < 8, (firstRun reversed n).frontier ≠ [] := by
  unfold firstRun
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- The first answers of the two runs, read through their stores. -/
theorem head_facts :
    (referenceRun 8).emitted.head?.map readPair = some (some (some 0, some 0)) ∧
      (referenceRun 8).emitted.head?.map (fun a => (a.2.2.1.applyTerm a.2.1).freeVars) =
        some ∅ ∧
      (firstRun reversed 8).emitted.head?.map readPair = some (some (some 1, some 1)) := by
  unfold firstRun referenceRun
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Corresponding answers over the substitution store read the same through
their stores once one of them reads ground. -/
theorem readthrough_of_sameAnswer {a b : Unit × Answer (Term sig) (Subst sig × ℕ)}
    (same : SameAnswer exact a b) (ground : (a.2.2.1.applyTerm a.2.1).freeVars = ∅) :
    b.2.2.1.applyTerm b.2.1 = a.2.2.1.applyTerm a.2.1 := by
  obtain ⟨value, forward, _⟩ := sameAnswer_instances id noPrim noTest same
  rw [← value, ← forward.applyTerm]
  exact Subst.applyTerm_eq_self fun v member => by simp [ground] at member

theorem forall₂_head {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {a : α} {b : β},
      l₁.head? = some a → l₂.head? = some b → R a b
  | _, _, .nil, _, _, found, _ => by cases found
  | _, _, .cons related _, _, _, foundA, foundB => by
      simp only [List.head?_cons, Option.some.injEq] at foundA foundB
      subst foundA foundB
      exact related

/-- A state with an exhausted frontier does not change. -/
theorem repeats_exhausted {C K Call' F A : Type} (P : Program C K Call' F A)
    (s : State C K F A) (exhausted : s.frontier = []) : ∀ m, repeats (step P) m s = s
  | 0 => rfl
  | m + 1 => by
      have fixed : step P s = s := by
        rcases s with ⟨frontier, emitted⟩
        cases exhausted
        rfl
      simp only [repeats, fixed]
      exact repeats_exhausted P s exhausted m

/-- Once exhausted, the reordering run has delivered its 8-step answers. -/
theorem reversed_settled (n : ℕ) (done : (firstRun reversed n).frontier = []) :
    (firstRun reversed n).emitted = (firstRun reversed 8).emitted := by
  obtain ⟨doneAt8, _, early⟩ := reversed_runs
  by_cases below : n < 8
  · exact absurd done (early n below)
  · obtain ⟨m, rfl⟩ : ∃ m, n = 8 + m := ⟨n - 8, by omega⟩
    unfold firstRun at doneAt8 ⊢
    rw [Mettapedia.GSLT.Dynamics.ContextIndexedSwitching.repeats_add,
      repeats_exhausted _ _ doneAt8]

/-- The reordering run does not deliver the reference's answers. -/
theorem reversed_differs :
    ¬ List.Forall₂ (SameAnswer exact) (referenceRun 8).emitted (firstRun reversed 8).emitted := by
  intro same
  obtain ⟨readA, groundA, readB⟩ := head_facts
  cases foundA : (referenceRun 8).emitted.head? with
  | none =>
      rw [foundA] at readA
      simp at readA
  | some a =>
      cases foundB : (firstRun reversed 8).emitted.head? with
      | none =>
          rw [foundB] at readB
          simp at readB
      | some b =>
          rw [foundA, Option.map_some, Option.some.injEq] at readA groundA
          rw [foundB, Option.map_some, Option.some.injEq] at readB
          have equal := readthrough_of_sameAnswer (forall₂_head same foundA foundB) groundA
          unfold readPair at readA readB
          rw [equal, readA] at readB
          simp at readB

/-- **The per-call hypothesis is needed.**  Every other hypothesis of
`hosted_query_terminates` holds for the reordering host and its conclusion
fails, so that host meets no specification. -/
theorem reversed_not_correct :
    ¬ Nonempty (HostCorrect exact HRel.isHost (enumReference values) (enumHost store reversed)) := by
  rintro ⟨spec⟩
  obtain ⟨n', done, answers⟩ := hosted_query_terminates (programBindsAhead_refl L []) spec
    (enumRefines exact values HRel.isHost) (BindsAhead.refl pairQuery) pairFrame start
    (start_wellFormed noPrim noTest) (fun _ t _ => all_moded t) 8 pair_runs.2.2.1
  have settled := reversed_settled n' done
  unfold firstRun at settled
  rw [settled] at answers
  exact reversed_differs answers

/-! ## A host with no answers -/

/-- `(= (q) (let $x (nothing) (S $x)))` and `(= (q) Z)`. -/
def qProgram : EqProgram L HRel Empty :=
  [(.q, ⟨1, [], .letCall (.var 0) .nothing [] (.ret (succ (.var 0)))⟩), (.q, ⟨0, [], .ret zero⟩)]

/-- The query `(q)`, reporting its answer in the query variable `0`. -/
def qQuery : Code L HRel Empty 1 := .letCall (.var 0) .q [] (.ret (.var 0))

/-- The output-first run of `(q)` with the enumerating host. -/
abbrev qFirst (n : ℕ) :=
  repeats (step (hostedFirst L store HRel.isHost qProgram (enumHost store values))) n
    (liftState (queryStateOut L qQuery pairFrame start))

/-- The reference run of `(q)`. -/
abbrev qReference (n : ℕ) :=
  repeats (step (hostedAtReturn L store HRel.isHost qProgram (enumReference values))) n
    (liftState (queryState L qQuery pairFrame start))

/-- **No answers: the alternative fails and its sibling continues.**  After 3
steps the host has been pulled and is exhausted: the first equation's
alternative is gone, nothing has been delivered, and the second equation's
alternative remains.  After 5 steps the run has delivered `Z` from the second
equation and exhausted its frontier; so has the reference. -/
theorem empty_host_runs :
    (qFirst 3).frontier.length = 1 ∧ (qFirst 3).emitted = [] ∧
      (qFirst 5).frontier = [] ∧
      (qFirst 5).emitted.map (fun a => numeral (a.2.2.1.applyTerm a.2.1)) = [some 0] ∧
      (qReference 5).frontier = [] ∧
      (qReference 5).emitted.map (fun a => numeral (a.2.2.1.applyTerm a.2.1)) = [some 0] := by
  unfold qFirst qReference
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- The law for `(q)`. -/
theorem empty_refines (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer exact) (qReference n).emitted (qFirst n').emitted :=
  hosted_query_answers (programBindsAhead_refl L qProgram) (enumCorrect exact values HRel.isHost)
    (enumRefines exact values HRel.isHost) (BindsAhead.refl qQuery) pairFrame start
    (start_wellFormed noPrim noTest) (fun _ t _ => all_moded t) n

/-! ## Collections -/

/-- An answer read through its store. -/
def readAnswer (a : Answer (Term sig) (Subst sig × ℕ)) : Option ℕ := numeral (a.2.1.applyTerm a.1)

/-- **Collection against a destination.**  With no destination, the reference
and the host collect `[Z, (S Z)]`.  Against the destination `(S $5)` the host
collects `[(S Z)]`: `Z` does not unify with it and is passed over, as
`(let E G E)` passes it over. -/
theorem pairs_collect :
    (collect (enumReference values).pull 4
        ((enumReference (Store := Subst sig × ℕ) values).start (.pairs, [], start))).map
        (List.map readAnswer) = some [some 0, some 1] ∧
      (collect (enumHost store values).pull 4
        ((enumHost store values).start (.pairs, [], start, none))).map
        (List.map readAnswer) = some [some 0, some 1] ∧
      (collect (enumHost store values).pull 4
        ((enumHost store values).start (.pairs, [], start, some (succ (.var 5))))).map
        (List.map readAnswer) = some [some 1] := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

end Mettapedia.GSLT.LanguageDef.HostCalls.Controls
