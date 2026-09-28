import Mettapedia.GSLT.LanguageDef.DestinationPassingRefinement

/-!
# Controls for destination passing

Concrete runs of the output-at-return machine (`DefunctionalizedEquationBodies.compiled`
on `SProgram.normalize`) and the output-first machine (`outputFirst` on
`SProgram.normalizeFirst`), both over the substitution store of
`CompiledTwoSidedHeadProgram`, checked by `decide`.  The fresh supply starts at
variable `10`; query variables are `0` and `1`.

**Evaluating the store.**  `unifyTotal` is defined by well-founded recursion and
does not reduce in the kernel.  `unifyBounded` runs the same rules with fuel and
reports exhausted fuel separately; `unifyBounded_sound` shows every answer it
gives is `unifyTotal`'s.  `substitutionStoreByFuel` unifies by `unifyBounded` and
falls back to `unifyTotal` when fuel runs out; `substitutionStoreByFuel_eq`
proves it *is* `substitutionStore`, so each control is stated for the store the
theorems are about and evaluated through this equality.

**Controls.**

* Exposed outputs: `(S (plus $l $r))`, written `letE h (call plus [l, r]) (ret (S h))`,
  exposes `(S h)` (`plusSucc_exposed`).  Extending the heads of `plus` by their
  exposed outputs (`plusZero_head_code`, `plusSucc_head_code`): in
  `(= (plus Z $r) $r)` the output slot `r` is already bound by the head and is
  compiled as a repeated occurrence (`equateSlot`); in the second equation the
  output hole `h` occurs first (`bindSlot`) and takes the destination's subterm.
* The `plus` inverse query `(plus $x (S Z))` against the destination
  `(S (S Z))`: output first has exhausted its frontier after 6 steps with the
  one answer `$x = (S Z)` (`plus_outputFirst_done`); output at return, after the
  same 6 steps, has no answer and two tasks left (`plus_outputAtReturn_running`),
  delivers the same answer at step 7 and is still running at step 40
  (`plus_outputAtReturn_later`).  `plus_refines` instantiates the prefix law for
  this query.
* Negative control: `(= (pick) (if true (let $h (loop) (S $h)) Z))` with
  `(= (loop) (loop))`, against the destination `Z`.  The branch taken exposes
  `(S $h)`, which clashes with `Z`: output first rejects the branch before its
  body runs (`pick_branch_rejected`: the branch's first instruction would be the
  call of `loop`; output first fails instead) and has exhausted its frontier
  after 2 steps, while output at return has entered `loop` and is still running
  at step 30 (`pick_runs`).
* Necessity of `Moded`: `(= (f $x) (let $u (succ $x) (pair $x $u)))` with a
  primitive `succ` that reads its argument through the store, against the
  destination `(pair (S Z) $b)`.  Only the destination binds `$x`.  Output at
  return finishes after 2 steps with no answer; output first finishes after 3
  with the answer `(pair (S Z) (S (S Z)))` (`prim_counterexample`).  Every other
  hypothesis of `outputFirst_terminates` holds, so the run is not moded
  (`prim_counterexample_not_moded`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls

open Mettapedia.Logic.LP
open Mettapedia.GSLT.LanguageDef.CompiledTwoSidedHeadProgram
open Mettapedia.GSLT.LanguageDef.DefunctionalizedEquationBodies
open Mettapedia.Machines.SharedContinuation
open Mettapedia.GSLT.Dynamics.ContextIndexedSwitching (repeats)

/-! ## A kernel-evaluable substitution store -/

section Evaluation

variable {σ : LPSignature} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]

/-- `unifyTotal`'s rules run with fuel: `none` is exhausted fuel, `some none` a
clash or occurs-check failure, `some (some θ)` a unifier. -/
def unifyBounded : ℕ → List (Term σ × Term σ) → Option (Option (Subst σ))
  | _, [] => some (some (Subst.id σ))
  | 0, _ :: _ => none
  | fuel + 1, (source, target) :: rest =>
      match source with
      | .var v =>
          match target with
          | .var other =>
              if v = other then unifyBounded fuel rest
              else (unifyBounded fuel ((Subst.single v (.var other)).applyEqs rest)).map
                fun result => result.map fun θ => θ ∘ₛ Subst.single v (.var other)
          | term =>
              if term.occursIn v then some none
              else (unifyBounded fuel ((Subst.single v term).applyEqs rest)).map
                fun result => result.map fun θ => θ ∘ₛ Subst.single v term
      | .const constant =>
          match target with
          | .var v =>
              (unifyBounded fuel ((Subst.single v (.const constant)).applyEqs rest)).map
                fun result => result.map fun θ => θ ∘ₛ Subst.single v (.const constant)
          | .const other => if constant = other then unifyBounded fuel rest else some none
          | .app _ _ => some none
      | .app function arguments =>
          match target with
          | .var v =>
              if (Term.app function arguments).occursIn v then some none
              else
                (unifyBounded fuel ((Subst.single v (.app function arguments)).applyEqs rest)).map
                  fun result => result.map fun θ => θ ∘ₛ Subst.single v (.app function arguments)
          | .const _ => some none
          | .app other otherArguments =>
              if equal : function = other then
                unifyBounded fuel (finPairsToList arguments (equal ▸ otherArguments) ++ rest)
              else some none

/-- Every answer the fuelled run gives is the total unifier's. -/
theorem unifyBounded_sound :
    ∀ (fuel : ℕ) (equations : List (Term σ × Term σ)) (result : Option (Subst σ)),
      unifyBounded fuel equations = some result → unifyTotal equations = result
  | _, [], result, bounded => by
      simp only [unifyBounded, Option.some.injEq] at bounded
      subst bounded
      simp [unifyTotal]
  | 0, _ :: _, _, bounded => by simp [unifyBounded] at bounded
  | fuel + 1, (source, target) :: rest, result, bounded => by
      rw [unifyTotal.eq_def]
      cases source with
      | var v =>
          cases target with
          | var other =>
              simp only [unifyBounded] at bounded
              by_cases same : v = other
              · simp only [same, if_true] at bounded ⊢
                exact unifyBounded_sound fuel rest result bounded
              · simp only [same, if_false] at bounded ⊢
                rw [Option.map_eq_some_iff] at bounded
                obtain ⟨inner, innerBounded, rfl⟩ := bounded
                rw [unifyBounded_sound fuel _ inner innerBounded]
                cases inner <;> rfl
          | const c =>
              simp only [unifyBounded] at bounded
              split at bounded
              · rename_i occurs
                simp only [Option.some.injEq] at bounded
                subst bounded
                simp [occurs]
              · rename_i notOccurs
                rw [Option.map_eq_some_iff] at bounded
                obtain ⟨inner, innerBounded, rfl⟩ := bounded
                simp only [notOccurs]
                rw [unifyBounded_sound fuel _ inner innerBounded]
                cases inner <;> rfl
          | app f ts =>
              simp only [unifyBounded] at bounded
              split at bounded
              · rename_i occurs
                simp only [Option.some.injEq] at bounded
                subst bounded
                simp [occurs]
              · rename_i notOccurs
                rw [Option.map_eq_some_iff] at bounded
                obtain ⟨inner, innerBounded, rfl⟩ := bounded
                simp only [notOccurs]
                rw [unifyBounded_sound fuel _ inner innerBounded]
                cases inner <;> rfl
      | const c =>
          cases target with
          | var v =>
              simp only [unifyBounded] at bounded
              rw [Option.map_eq_some_iff] at bounded
              obtain ⟨inner, innerBounded, rfl⟩ := bounded
              simp only
              rw [unifyBounded_sound fuel _ inner innerBounded]
              cases inner <;> rfl
          | const d =>
              simp only [unifyBounded] at bounded
              by_cases same : c = d
              · simp only [same, if_true] at bounded ⊢
                exact unifyBounded_sound fuel rest result bounded
              · simp only [same, if_false, Option.some.injEq] at bounded ⊢
                exact bounded
          | app f ts =>
              simp only [unifyBounded, Option.some.injEq] at bounded
              subst bounded
              rfl
      | app f ts =>
          cases target with
          | var v =>
              simp only [unifyBounded] at bounded
              split at bounded
              · rename_i occurs
                simp only [Option.some.injEq] at bounded
                subst bounded
                simp [occurs]
              · rename_i notOccurs
                rw [Option.map_eq_some_iff] at bounded
                obtain ⟨inner, innerBounded, rfl⟩ := bounded
                simp only [notOccurs]
                rw [unifyBounded_sound fuel _ inner innerBounded]
                cases inner <;> rfl
          | const d =>
              simp only [unifyBounded, Option.some.injEq] at bounded
              subst bounded
              rfl
          | app g us =>
              simp only [unifyBounded] at bounded
              by_cases same : f = g
              · subst same
                simp only [dif_pos] at bounded ⊢
                exact unifyBounded_sound fuel _ result bounded
              · simp only [same, dif_neg, not_false_eq_true, Option.some.injEq] at bounded ⊢
                exact bounded

end Evaluation

section Store

variable {σ : LPSignature.{0, 0, 0, 0}} [DecidableEq σ.vars] [DecidableEq σ.constants]
  [DecidableEq σ.functionSymbols]
variable (name : ℕ → σ.vars) {Op : Type}
  (prim : Op → List (Term σ) → Subst σ × ℕ → Option (Term σ))
  (test : Op → List (Term σ) → Subst σ × ℕ → Option Bool)

/-- The substitution store, unifying by `unifyBounded` within `fuel` and by
`unifyTotal` beyond it. -/
def substitutionStoreByFuel (fuel : ℕ) : StoreAlgebra (Term σ) (Subst σ × ℕ) Op where
  unify p a store :=
    match unifyBounded fuel [(store.1.applyTerm p, store.1.applyTerm a)] with
    | some result => result.map fun unifier => (unifier ∘ₛ store.1, store.2)
    | none => (unifyTotal [(store.1.applyTerm p, store.1.applyTerm a)]).map
        fun unifier => (unifier ∘ₛ store.1, store.2)
  fresh store k := (freshVariables name store.2 k, (store.1, store.2 + k))
  prim := prim
  test := test

/-- It is the substitution store. -/
theorem substitutionStoreByFuel_eq (fuel : ℕ) :
    substitutionStoreByFuel name prim test fuel = substitutionStore name prim test := by
  simp only [substitutionStoreByFuel, substitutionStore, StoreAlgebra.mk.injEq, and_true]
  funext p a store
  split
  · rename_i result bounded
    rw [unifyBounded_sound _ _ _ bounded]
  · rfl

end Store

/-! ## Numerals and pairs -/

/-- The successor and a pairing constructor. -/
inductive Fn where
  | succ
  | pair
  deriving DecidableEq

/-- The arity of a constructor. -/
def Fn.arity : Fn → ℕ
  | .succ => 1
  | .pair => 2

/-- String constants (`Z`), natural-number variables, `S` and `pair`. -/
abbrev sig : LPSignature.{0, 0, 0, 0} where
  constants := String
  vars := ℕ
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Fn
  functionArity := Fn.arity

instance : Inhabited (Term sig) := ⟨.const "Z"⟩

/-- Head patterns over `sig` as templates. -/
abbrev L : DefunctionalizedEquationBodies.TemplateLanguage (Term sig) := headTemplates sig

/-- `Z`, over any variables. -/
def zero {V : Type} : Term { sig with vars := V } := .const "Z"

/-- `(S t)`, over any variables. -/
def succ {V : Type} (t : Term { sig with vars := V }) : Term { sig with vars := V } :=
  .app Fn.succ fun _ => t

/-- `(pair t u)`, over any variables. -/
def pair {V : Type} (t u : Term { sig with vars := V }) : Term { sig with vars := V } :=
  .app Fn.pair fun i => if i.val = 0 then t else u

/-- The number a Peano numeral denotes. -/
def numeral : Term sig → Option ℕ
  | .const "Z" => some 0
  | .app Fn.succ children => (numeral (children ⟨0, by decide⟩)).map (· + 1)
  | _ => none

/-- A pair of numerals. -/
def numerals : Term sig → Option (Option ℕ × Option ℕ)
  | .app Fn.pair children =>
      some (numeral (children ⟨0, by decide⟩), numeral (children ⟨1, by decide⟩))
  | _ => none

/-- The substitution store starts empty, with the fresh supply at `10`. -/
def start : Subst sig × ℕ := (Subst.id sig, 10)

theorem start_wellFormed {Op : Type}
    (prim : Op → List (Term sig) → Subst sig × ℕ → Option (Term sig))
    (test : Op → List (Term sig) → Subst sig × ℕ → Option Bool) :
    (substitutionExact id prim test).WellFormed start := fun _ => rfl

/-! ## `plus`: an inverse query -/

section Plus

/-- No primitives. -/
def noPrim : Empty → List (Term sig) → Subst sig × ℕ → Option (Term sig) := fun op => op.elim

/-- No tests. -/
def noTest : Empty → List (Term sig) → Subst sig × ℕ → Option Bool := fun op => op.elim

/-- The substitution store without primitives or tests. -/
abbrev plusStore := substitutionStore (σ := sig) id noPrim noTest

/-- `(S (plus $l $r))` over the slots `l, r, h`: the call's output is the hole `h`. -/
def plusSucc : Source L Unit Empty 3 :=
  .letE (.var 2) (.call () [.var 0, .var 1]) (.ret (succ (.var 2)))

theorem plusSucc_exposed : plusSucc.exposed = some (succ (.var 2)) := rfl

/-- `(= (plus Z $r) $r)` and `(= (plus (S $l) $r) (S (plus $l $r)))`. -/
def plus : SProgram L Unit Empty :=
  [((), ⟨1, [zero, .var 0], .ret (.var 0)⟩), ((), ⟨3, [succ (.var 0), .var 1], plusSucc⟩)]

/-- With the exposed output `$r` as one more head pattern, the output slot is a
repeated occurrence. -/
theorem plusZero_head_code :
    emitHead ([zero, .var 0, .var 0] : List (HeadPattern sig (Fin 1))) =
      [.constant 0 "Z", .bindSlot 1 0, .equateSlot 2 0] := rfl

/-- With the exposed output `(S h)` as one more head pattern, the output hole is
a first occurrence, bound to the destination's subterm. -/
theorem plusSucc_head_code :
    emitHead ([succ (.var 0), .var 1, succ (.var 2)] : List (HeadPattern sig (Fin 3))) =
      [.node 0 .succ 3, .bindSlot 3 0, .bindSlot 1 1, .node 2 .succ 4, .bindSlot 4 2] := rfl

/-- The query `(plus $x (S Z))` against the destination `(S (S Z))`, reporting
`$x`. -/
def plusQuery : Code L Unit Empty 1 :=
  .letCall (succ (succ zero)) () [.var 0, succ zero] (.ret (.var 0))

/-- The query's slot is the query variable `0`. -/
def plusFrame : Fin 1 → Term sig := fun _ => .var 0

/-- Output first has exhausted its frontier after 6 steps, with the one answer
`$x = (S Z)`. -/
theorem plus_outputFirst_done :
    (repeats (step (outputFirst L plusStore (SProgram.normalizeFirst L plus))) 6
        (queryStateOut L plusQuery plusFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L plusStore (SProgram.normalizeFirst L plus))) 6
        (queryStateOut L plusQuery plusFrame start)).emitted.map
          (fun a => numeral (a.2.2.1.applyTerm a.2.1)) = [some 1] := by
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Output at return, after the same 6 steps, has delivered nothing and has two
tasks left. -/
theorem plus_outputAtReturn_running :
    (repeats (step (compiled L plusStore (SProgram.normalize L plus))) 6
        (queryState L plusQuery plusFrame start)).frontier.length = 2 ∧
      (repeats (step (compiled L plusStore (SProgram.normalize L plus))) 6
        (queryState L plusQuery plusFrame start)).emitted = [] := by
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- Output at return delivers the same answer at step 7, and is still running at
step 40 with no other answer. -/
theorem plus_outputAtReturn_later :
    (repeats (step (compiled L plusStore (SProgram.normalize L plus))) 7
        (queryState L plusQuery plusFrame start)).emitted.map
          (fun a => numeral (a.2.2.1.applyTerm a.2.1)) = [some 1] ∧
      (repeats (step (compiled L plusStore (SProgram.normalize L plus))) 40
        (queryState L plusQuery plusFrame start)).frontier.length = 2 ∧
      (repeats (step (compiled L plusStore (SProgram.normalize L plus))) 40
        (queryState L plusQuery plusFrame start)).emitted.length = 1 := by
  rw [show plusStore = substitutionStoreByFuel id noPrim noTest 64 from
    (substitutionStoreByFuel_eq id noPrim noTest 64).symm]
  decide

/-- The prefix law holds for this query: the program has no tests or
primitives. -/
theorem plus_refines (n : ℕ) :
    ∃ n' ≤ n, List.Forall₂ (SameAnswer (substitutionExact id noPrim noTest))
      (repeats (step (compiled L plusStore (SProgram.normalize L plus))) n
        (queryState L plusQuery plusFrame start)).emitted
      (repeats (step (outputFirst L plusStore (SProgram.normalizeFirst L plus))) n'
        (queryStateOut L plusQuery plusFrame start)).emitted :=
  source_outputFirst_answers (substitutionExact id noPrim noTest) plus plusQuery plusFrame start
    (start_wellFormed noPrim noTest)
    (fun _ t _ => substitution_moded id noPrim noTest (fun op => op.elim) t) n

end Plus

/-! ## A branch clashing with the destination -/

section Pick

/-- The relations `pick` and `loop`. -/
inductive PickRel where
  | pick
  | loop
  deriving DecidableEq

/-- The conditional's test: it holds, reading nothing. -/
def alwaysTest : Unit → List (Term sig) → Subst sig × ℕ → Option Bool := fun _ _ _ => some true

/-- No primitives. -/
def noPrimUnit : Unit → List (Term sig) → Subst sig × ℕ → Option (Term sig) := fun _ _ _ => none

/-- The substitution store with the test that holds. -/
abbrev pickStore := substitutionStore (σ := sig) id noPrimUnit alwaysTest

/-- `(= (pick) (if true (let $h (loop) (S $h)) Z))` and `(= (loop) (loop))`. -/
def pickProgram : SProgram L PickRel Unit :=
  [(.pick,
      ⟨1, [], .ite () [] (.letE (.var 0) (.call .loop []) (.ret (succ (.var 0)))) (.ret zero)⟩),
   (.loop, ⟨0, [], .call .loop []⟩)]

/-- The query `(pick)` against the destination `Z`. -/
def pickQuery : Code L PickRel Unit 0 := .letCall zero .pick [] (.ret zero)

/-- The query has no slots. -/
def pickFrame : Fin 0 → Term sig := fun i => i.elim0

/-- The relation an instruction calls, if it is a call. -/
def callee {Frame Answer : Type} {Store : Type} :
    Instruction (Call (Term sig) Store PickRel) Frame Answer → Option PickRel
  | .call c _ => some c.1
  | _ => none

/-- The body of `pick`, activated by the query: the frame is the fresh variable
`10` and the supply stands at `11`. -/
def pickBody : Code L PickRel Unit 1 :=
  .ite () [] (.letCall (.var 0) .loop [] (.ret (succ (.var 0)))) (.ret zero)

theorem pickBody_normalize :
    (SProgram.normalize L pickProgram).equations .pick = [⟨1, [], pickBody⟩] ∧
      (SProgram.normalizeFirst L pickProgram).equations .pick = [⟨1, [], pickBody⟩] :=
  ⟨rfl, rfl⟩

/-- Whether an instruction is failure. -/
def failure {Call Frame Answer : Type} : Instruction Call Frame Answer → Bool
  | .fail => true
  | _ => false

theorem eq_fail_of_failure {Call Frame Answer : Type} {i : Instruction Call Frame Answer}
    (h : failure i = true) : i = .fail := by
  cases i <;> simp_all [failure]

/-- **Rejected before the branch body runs.**  The branch taken would first call
`loop`; output at return makes that call, output first meets the branch's
exposed output `(S $h)` with the destination `Z` and fails. -/
theorem pick_branch_rejected :
    callee (inspectCode L pickStore (fun _ => .var 10) (Subst.id sig, 11) pickBody) =
        some .loop ∧
      inspectOut L pickStore (fun _ => .var 10) (some zero) (Subst.id sig, 11) pickBody =
        .fail := by
  rw [show pickStore = substitutionStoreByFuel id noPrimUnit alwaysTest 64 from
    (substitutionStoreByFuel_eq id noPrimUnit alwaysTest 64).symm]
  refine ⟨by decide, eq_fail_of_failure ?_⟩
  decide

/-- Output first has exhausted its frontier after 2 steps; output at return has
entered `loop` and is still running at step 30, with no answer. -/
theorem pick_runs :
    (repeats (step (outputFirst L pickStore (SProgram.normalizeFirst L pickProgram))) 2
        (queryStateOut L pickQuery pickFrame start)).frontier = [] ∧
      (repeats (step (compiled L pickStore (SProgram.normalize L pickProgram))) 30
        (queryState L pickQuery pickFrame start)).frontier.length = 1 ∧
      (repeats (step (compiled L pickStore (SProgram.normalize L pickProgram))) 30
        (queryState L pickQuery pickFrame start)).emitted = [] := by
  rw [show pickStore = substitutionStoreByFuel id noPrimUnit alwaysTest 64 from
    (substitutionStoreByFuel_eq id noPrimUnit alwaysTest 64).symm]
  decide

end Pick

/-! ## A primitive only the destination determines -/

section Prim

/-- The Peano numeral of a number. -/
def toNumeral : ℕ → Term sig
  | 0 => .const "Z"
  | n + 1 => .app Fn.succ fun _ => toNumeral n

/-- `succ` as a primitive: it reads its argument through the store and succeeds
only on a numeral. -/
def succPrim : Unit → List (Term sig) → Subst sig × ℕ → Option (Term sig)
  | _, [t], store => (numeral (store.1.applyTerm t)).map fun n => toNumeral (n + 1)
  | _, _, _ => none

/-- No tests. -/
def noTestUnit : Unit → List (Term sig) → Subst sig × ℕ → Option Bool := fun _ _ _ => none

/-- The substitution store with the primitive `succ`. -/
abbrev primStore := substitutionStore (σ := sig) id succPrim noTestUnit

/-- `(= (f $x) (let $u (succ $x) (pair $x $u)))`. -/
def primProgram : SProgram L Unit Unit :=
  [((), ⟨2, [.var 0], .letPrim (.var 1) () [.var 0] (.ret (pair (.var 0) (.var 1)))⟩)]

/-- The query `(f $a)` against the destination `(pair (S Z) $b)`, reporting
`(pair $a $b)`. -/
def primQuery : Code L Unit Unit 2 :=
  .letCall (pair (succ zero) (.var 1)) () [.var 0] (.ret (pair (.var 0) (.var 1)))

/-- The query's slots are the query variables `0` and `1`. -/
def primFrame : Fin 2 → Term sig := fun i => .var i.val

/-- **Output first delivers an answer output at return never does.**  Output at
return finishes after 2 steps with no answer: the primitive sees `$x` unbound.
Output first finishes after 3 steps with the answer `(pair (S Z) (S (S Z)))`:
the destination bound `$x` before the primitive ran. -/
theorem prim_counterexample :
    (repeats (step (compiled L primStore (SProgram.normalize L primProgram))) 2
        (queryState L primQuery primFrame start)).frontier = [] ∧
      (repeats (step (compiled L primStore (SProgram.normalize L primProgram))) 2
        (queryState L primQuery primFrame start)).emitted = [] ∧
      (repeats (step (outputFirst L primStore (SProgram.normalizeFirst L primProgram))) 3
        (queryStateOut L primQuery primFrame start)).frontier = [] ∧
      (repeats (step (outputFirst L primStore (SProgram.normalizeFirst L primProgram))) 3
        (queryStateOut L primQuery primFrame start)).emitted.map
          (fun a => numerals (a.2.2.1.applyTerm a.2.1)) = [some (some 1, some 2)] := by
  rw [show primStore = substitutionStoreByFuel id succPrim noTestUnit 64 from
    (substitutionStoreByFuel_eq id succPrim noTestUnit 64).symm]
  decide

/-- Output first has not finished within 2 steps. -/
theorem prim_outputFirst_early :
    ∀ n ≤ 2, (repeats (step (outputFirst L primStore (SProgram.normalizeFirst L primProgram))) n
      (queryStateOut L primQuery primFrame start)).frontier ≠ [] := by
  rw [show primStore = substitutionStoreByFuel id succPrim noTestUnit 64 from
    (substitutionStoreByFuel_eq id succPrim noTestUnit 64).symm]
  decide

/-- **`Moded` is needed.**  Every other hypothesis of `outputFirst_terminates`
holds for this query, and its conclusion fails, so the output-at-return run is
not moded. -/
theorem prim_counterexample_not_moded :
    ¬ ∀ m, ∀ t ∈ (repeats (step (compiled L primStore (SProgram.normalize L primProgram))) m
        (queryState L primQuery primFrame start)).frontier,
      Moded L (substitutionExact id succPrim noTestUnit) t := by
  intro moded
  obtain ⟨doneA, noneA, -, -⟩ := prim_counterexample
  obtain ⟨n', le, doneF, _⟩ := outputFirst_terminates (substitutionExact id succPrim noTestUnit)
    (programBindsAhead_normalize primProgram)
    (simulates_query (substitutionExact id succPrim noTestUnit) (BindsAhead.refl primQuery)
      primFrame start (start_wellFormed succPrim noTestUnit)) moded 2 doneA
  exact prim_outputFirst_early n' le doneF

end Prim

end Mettapedia.GSLT.LanguageDef.DestinationPassing.Controls
