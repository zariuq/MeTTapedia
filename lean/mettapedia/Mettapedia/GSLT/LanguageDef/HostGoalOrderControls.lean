import Mettapedia.GSLT.LanguageDef.HostGoalDoctrine
import Mettapedia.GSLT.LanguageDef.HostGoalControls

/-!
# Controls for eager host frames and for `once` under the order doctrine

Runs over the substitution store, evaluated through
`substitutionStoreByFuel_eq` and checked by `decide`, on the programs of
`HostGoalControls`.

* **Eager frames, positive** (`eager_pairs_runs`).  With eager host frames
  `(let $x (pairs) (pair $x $x))` delivers `(pair Z Z)` and then
  `(pair (S Z) (S Z))` on both sides and has exhausted its frontier after 7
  steps, where the lazy machines have not: the host node the last answer
  exhausts still waits for its pull.  `eager_pairs_refines` instantiates
  `machines_eager_query_answers`.
* **Eager frames, negative** (`rash_runs`, `rash_unsound`).  A machine that drops
  every host node with its first answer drops one whose next pull still yields
  `(S Z)`, and delivers `(pair Z Z)` alone.  Its exhaustion test is unsound.
* **The doctrine law on `(pairs)`** (`pairs_doctrine_runs`, `pairs_doctrine`).
  Against `(S $5)` the first answers differ (`pairs_delimiters`), but the
  output-first `once` answers `(S Z)`, a witness in the reference's bag and in
  its published collection.  Against `(pair $5 $6)` it answers none, and every
  answer in the reference's bag is omitted.
* **A witness the reference never delivers** (`loop_doctrine`).  The program
  `(= (g) (let $h (loop) (S $h)))`, `(= (g) Z)`, `(= (loop) (loop))`, and the
  goal `(g)` against `Z`.  The reference runs `(loop)` forever and delivers
  nothing within any number of pulls (`loop_reference_silent`).  The
  output-first `once` prunes the first equation at activation and answers `Z`
  (`loop_once`), a witness of the reference's bag.
* **`GoalTreesModed` is needed** (`prim_trees_not_moded`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HostGoals.OrderControls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.GSLT.LanguageDef.DestinationPassing
open Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
open Mettapedia.GSLT.LanguageDef.HostCalls
open Mettapedia.GSLT.LanguageDef.HostCalls.Controls
open Mettapedia.GSLT.LanguageDef.HostGoals
open Mettapedia.GSLT.LanguageDef.HostGoals.Controls
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## Eager host frames -/

/-- The reference with host calls and eager host frames. -/
abbrev eagerReference (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (hostedAtReturnEager L store HRel.isHost pairsProgram
    (referenceHost L store pairsProgram) List.isEmpty)) n
    (liftState (queryState L query pairFrame start))

/-- The output-first machine with host calls and eager host frames. -/
abbrev eagerOutputFirst (query : Code L HRel Empty 1) (n : ℕ) :=
  repeats (step (hostedFirstEager L store HRel.isHost pairsProgram
    (outputFirstHost L store pairsProgram) List.isEmpty)) n
    (liftState (queryStateOut L query pairFrame start))

/-- **Eager frames: the same answers in fewer steps.**  With eager host frames
`(let $x (pairs) (pair $x $x))` delivers `(pair Z Z)` and then
`(pair (S Z) (S Z))` on both sides and has exhausted its frontier after 7
steps; with lazy host frames it has not, the host node exhausted by the last
answer still waiting for its pull. -/
theorem eager_pairs_runs :
    (eagerReference pairQuery 7).frontier = [] ∧
      (eagerReference pairQuery 7).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] ∧
      (eagerOutputFirst pairQuery 7).frontier = [] ∧
      (eagerOutputFirst pairQuery 7).emitted.map readPair =
        [some (some 0, some 0), some (some 1, some 1)] ∧
      (hostedReference pairQuery 7).frontier ≠ [] ∧
      (hostedOutputFirst pairQuery 7).frontier ≠ [] := by
  unfold eagerReference eagerOutputFirst hostedReference hostedOutputFirst
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- The law for the eager machines on both sides. -/
theorem eager_pairs_refines (n : ℕ) :
    ∃ n', List.Forall₂ (SameAnswer exact) (eagerReference pairQuery n).emitted
      (eagerOutputFirst pairQuery n').emitted :=
  machines_eager_query_answers (programBindsAhead_refl L pairsProgram)
    (goalsModed_of_moded every_moded) (BindsAhead.refl pairQuery) pairFrame start
    (start_wellFormed noPrim noTest) (fun _ t _ => hmoded_of L exact every_moded t) n

/-- A machine that drops every host node with its first answer, whether or not
the host is exhausted. -/
abbrev rashReference (n : ℕ) :=
  repeats (step (hostedAtReturnEager L store HRel.isHost pairsProgram
    (referenceHost L store pairsProgram) fun _ => true)) n
    (liftState (queryState L pairQuery pairFrame start))

/-- Whether a pull yields. -/
def yields {HState' Answer' : Type} : Pull HState' Answer' → Bool
  | .yield _ _ => true
  | _ => false

/-- **Dropping a host node whose next pull yields loses an answer.**  After the
first answer of `(pairs)` its host state still yields `(S Z)`; the machine that
drops it has exhausted its frontier after 4 steps with `(pair Z Z)` alone. -/
theorem rash_runs :
    yields ((referenceHost L store pairsProgram).pull
      ((referenceHost L store pairsProgram).start (.pairs, [], start)).tail) = true ∧
      (rashReference 4).frontier = [] ∧
      (rashReference 4).emitted.map readPair = [some (some 0, some 0)] := by
  unfold rashReference
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- That machine's exhaustion test is unsound: it accepts a state whose next
pull yields. -/
theorem rash_unsound :
    ¬ ∀ h, (fun _ => true) h = true → (referenceHost L store pairsProgram).pull h = .done := by
  intro sound
  have yielding := rash_runs.1
  rw [sound _ rfl] at yielding
  exact absurd yielding (by decide)

/-! ## `once` under the order doctrine -/

/-- A decided `once` read through `readAnswer` gives a decided `once`. -/
theorem once_of_read {HState' : Type}
    {pull : HState' → Pull HState' (Answer (Term sig) (Subst sig × ℕ))} {n : ℕ} {h : HState'}
    {k : ℕ}
    (read : (once pull n h).map (Option.map readAnswer) = some (some (some k))) :
    ∃ a', once pull n h = some (some a') ∧ readAnswer a' = some k := by
  cases decided : once pull n h with
  | none => simp [decided] at read
  | some first =>
      cases first with
      | none => simp [decided] at read
      | some a' => exact ⟨a', rfl, by simpa [decided] using read⟩

theorem once_none_of_read {HState' : Type}
    {pull : HState' → Pull HState' (Answer (Term sig) (Subst sig × ℕ))} {n : ℕ} {h : HState'}
    (read : (once pull n h).map (Option.map readAnswer) = some none) :
    once pull n h = some none := by
  cases decided : once pull n h with
  | none => simp [decided] at read
  | some first =>
      cases first with
      | none => rfl
      | some a' => simp [decided] at read

/-- The goal `(pairs)` against the destination `(S $5)`, and against
`(pair $5 $6)`, which none of its answers meets. -/
theorem pairs_doctrine_runs :
    (once (outputFirstHost L store pairsProgram).pull 3
        ((outputFirstHost L store pairsProgram).start
          (.pairs, [], start, some (succ (.var 5))))).map (Option.map readAnswer) =
        some (some (some 1)) ∧
      (collect (referenceHost L store pairsProgram).pull 4
        ((referenceHost L store pairsProgram).start (.pairs, [], start))).map
        (List.map readAnswer) = some [some 0, some 1] ∧
      (once (outputFirstHost L store pairsProgram).pull 3
        ((outputFirstHost L store pairsProgram).start
          (.pairs, [], start, some (pair (.var 5) (.var 6))))).map (Option.map readAnswer) =
        some none := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **The doctrine law on `(pairs)`.**  The first answers differ
(`pairs_delimiters`), yet the output-first host's `once` against `(S $5)`
answers a witness the reference delivers, in its bag and in its collection;
against `(pair $5 $6)` it finds none, and every answer of the reference is
omitted there. -/
theorem pairs_doctrine :
    (∃ a', once (outputFirstHost L store pairsProgram).pull 3
        ((outputFirstHost L store pairsProgram).start
          (.pairs, [], start, some (succ (.var 5)))) = some (some a') ∧
      (∃ a, InBag (compiled L store pairsProgram)
          ((referenceHost L store pairsProgram).start (.pairs, [], start)) ((), a) ∧
        AnswerRel exact Set.univ (some (succ (.var 5))) a a') ∧
      ∃ as, collect (referenceHost L store pairsProgram).pull 4
          ((referenceHost L store pairsProgram).start (.pairs, [], start)) = some as ∧
        ∃ a ∈ as, AnswerRel exact Set.univ (some (succ (.var 5))) a a') ∧
    ∀ a, InBag (compiled L store pairsProgram)
        ((referenceHost L store pairsProgram).start (.pairs, [], start)) ((), a) →
      AnswerOmitted exact Set.univ (some (pair (.var 5) (.var 6))) a := by
  obtain ⟨witnessRead, collectedRead, noneRead⟩ := pairs_doctrine_runs
  obtain ⟨a', found, _⟩ := once_of_read witnessRead
  obtain ⟨as, collected, _⟩ := Option.map_eq_some_iff.mp collectedRead
  have hit : HRel.isHost .pairs = true := rfl
  have good := start_wellFormed noPrim noTest
  refine ⟨⟨a', found, ?_, as, collected, ?_⟩, ?_⟩
  · exact machines_once_witness (programBindsAhead_refl L pairsProgram)
      (goalTreesModed_of_moded every_moded) hit good good (by rw [Set.inter_univ]) rfl found
  · exact once_host_witness pairsCorrect
      (pairsCorrect.start hit good good (by rw [Set.inter_univ]) rfl) collected found
  · exact machines_once_fails (programBindsAhead_refl L pairsProgram)
      (goalTreesModed_of_moded every_moded) hit good good (by rw [Set.inter_univ]) rfl
      (once_none_of_read noneRead)

/-! ## A witness the reference never delivers -/

/-- The relations of the loop control. -/
inductive LRel where
  | g
  | loop
  deriving DecidableEq

/-- `g` is a host relation. -/
def LRel.isHost : LRel → Bool
  | .g => true
  | .loop => false

/-- `(= (g) (let $h (loop) (S $h)))`, `(= (g) Z)` and `(= (loop) (loop))`. -/
def loopProgram : SProgram L LRel Empty :=
  [(.g, ⟨1, [], .letE (.var 0) (.call .loop []) (.ret (succ (.var 0)))⟩),
   (.g, ⟨0, [], .ret zero⟩),
   (.loop, ⟨0, [], .call .loop []⟩)]

/-- A task running `(loop)` in last position. -/
def loopTask (f : Fin 0 → Term sig) (σ : Subst sig × ℕ) (fs : List (ReturnFrame L LRel Empty)) :
    Task Unit (Control L LRel Empty (Subst sig × ℕ)) (ReturnFrame L LRel Empty) :=
  ⟨(), ⟨0, .tail .loop [], f, σ⟩, fs⟩

/-- A loop task expands to a loop task and delivers nothing. -/
theorem loopTask_expand (f : Fin 0 → Term sig) (σ : Subst sig × ℕ)
    (fs : List (ReturnFrame L LRel Empty)) :
    expand (compiled L store (SProgram.normalize L loopProgram)) (loopTask f σ fs) =
      ([loopTask (store.fresh σ 0).1 (store.fresh σ 0).2 fs], []) :=
  rfl

theorem loop_silent : ∀ (n : ℕ) (f : Fin 0 → Term sig) (σ : Subst sig × ℕ)
    (fs : List (ReturnFrame L LRel Empty))
    (rest : List (Task Unit (Control L LRel Empty (Subst sig × ℕ)) (ReturnFrame L LRel Empty))),
    delivered (referenceHost L store (SProgram.normalize L loopProgram)).pull n
      (loopTask f σ fs :: rest) = []
  | 0, _, _, _, _ => rfl
  | n + 1, f, σ, fs, rest => by
      have pulled : (referenceHost L store (SProgram.normalize L loopProgram)).pull
          (loopTask f σ fs :: rest) =
            .suspend (loopTask (store.fresh σ 0).1 (store.fresh σ 0).2 fs :: rest) := by
        change machinePull (compiled L store (SProgram.normalize L loopProgram))
          (loopTask f σ fs :: rest) = _
        rw [machinePull_silent _ rest (by rw [loopTask_expand]), loopTask_expand]
        rfl
      simp only [delivered, pulled]
      exact loop_silent n _ _ fs rest

/-- **The reference delivers nothing.**  Its first equation for `(g)` calls
`(loop)`, which runs forever, so its second equation is never reached. -/
theorem loop_reference_silent (n : ℕ) :
    delivered (referenceHost L store (SProgram.normalize L loopProgram)).pull n
      ((referenceHost L store (SProgram.normalize L loopProgram)).start (.g, [], start)) = [] := by
  cases n with
  | zero => rfl
  | succ n =>
      obtain ⟨f, σ, fs, rest, pulled⟩ : ∃ f σ fs rest,
          (referenceHost L store (SProgram.normalize L loopProgram)).pull
            ((referenceHost L store (SProgram.normalize L loopProgram)).start (.g, [], start)) =
            .suspend (loopTask f σ fs :: rest) :=
        ⟨_, _, _, _, rfl⟩
      simp only [delivered, pulled]
      exact loop_silent n f σ fs rest

/-- The output-first host's `once` of `(g)` against the destination `Z`
answers `Z`: the first equation's exposed output `(S $h)` does not meet `Z`, so
that equation is pruned at activation, before `(loop)` runs. -/
theorem loop_once :
    (once (outputFirstHost L store (SProgram.normalizeFirst L loopProgram)).pull 2
        ((outputFirstHost L store (SProgram.normalizeFirst L loopProgram)).start
          (.g, [], start, some zero))).map (Option.map readAnswer) = some (some (some 0)) := by
  rw [show store = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- **A witness of the bag that the reference never delivers.**  The
output-first `once` of `(g)` against `Z` answers a witness in the bag of the
reference's evaluation of `(g)`, the answer of its second equation, while the
reference, running its first equation forever, delivers no answer at all.  So
the doctrine law holds over the bag, and cannot hold over the reference's
delivered answers. -/
theorem loop_doctrine :
    ∃ a', once (outputFirstHost L store (SProgram.normalizeFirst L loopProgram)).pull 2
        ((outputFirstHost L store (SProgram.normalizeFirst L loopProgram)).start
          (.g, [], start, some zero)) = some (some a') ∧
      (∃ a, InBag (compiled L store (SProgram.normalize L loopProgram))
          ((referenceHost L store (SProgram.normalize L loopProgram)).start (.g, [], start))
          ((), a) ∧ AnswerRel exact Set.univ (some zero) a a') ∧
      ∀ n a, a ∉ delivered (referenceHost L store (SProgram.normalize L loopProgram)).pull n
        ((referenceHost L store (SProgram.normalize L loopProgram)).start (.g, [], start)) := by
  obtain ⟨a', found, _⟩ := once_of_read loop_once
  have good := start_wellFormed noPrim noTest
  refine ⟨a', found, ?_, fun n a member => ?_⟩
  · exact machines_once_witness (programBindsAhead_normalize loopProgram)
      (goalTreesModed_of_moded fun t => substitution_moded id noPrim noTest (fun op => op.elim) t)
      (rel := .g) (isHost := LRel.isHost) rfl good good (by rw [Set.inter_univ]) rfl found
  · rw [loop_reference_silent n] at member
    exact absurd member List.not_mem_nil

/-- **`GoalTreesModed` is needed**: it implies `GoalsModed`, which
`prim_goals_not_moded` refutes for the program with the store-reading
primitive. -/
theorem prim_trees_not_moded :
    ¬ GoalTreesModed L primStore (substitutionExact id succPrim noTestUnit) allHost
      (SProgram.normalize L primProgram) :=
  fun trees => prim_goals_not_moded (goalsModed_of_goalTreesModed trees)

end Mettapedia.GSLT.LanguageDef.HostGoals.OrderControls
