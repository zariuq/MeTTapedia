import Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPrepared

/-!
# Publication of open terms

The same TAKE and MAKE sequence serves both p1 profiles. For a
symbolic firing it leaves surviving labels open and puts the
opened output terms under their reserved identities. The solver's
answer is not substituted into the published store.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPublication

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Derivation (Match Store)
open Derivation.SymbolicFiring (Rules LiveWorld act)
open SymbolicExecution (Code Frame Equations Work storeOf profile)
open SymbolicPortCode (passReg)

universe u p
variable {σ : LPSignature.{u,u,p,u}}

private theorem zip_range {A : Type*} (values : List A) (first : ℕ) :
    (List.range' first values.length).zip values =
      values.zipIdx.map (fun p => (first + p.2, p.1)) := by
  induction values generalizing first with
  | nil => rfl
  | cons initial rest ih =>
    simp only [List.length_cons, List.range'_succ, List.zip_cons_cons, List.zipIdx_cons, List.map_cons, Nat.add_zero]
    rw [ih, List.zipIdx_succ, List.map_map]
    congr 1
    apply List.map_congr_left
    intro pair _
    simp only [Function.comp_apply, Prod.mk.injEq, and_true]
    omega

private theorem store_ext {A : Type*} {s t : Store A} (atoms : s.occurrences = t.occurrences)
    (next : s.fresh = t.fresh) : s = t := by
  cases s
  cases t
  cases atoms
  cases next
  rfl

variable {rules : Rules σ} (before : LiveWorld σ)

theorem storeOf_commit
    (firing : RuleSyntax.Firing ℕ (RuleSyntax.OneFrame.ext (FirstOrder.action σ)) rules.program before.state.frame)
    (shapes : firing.Shapes (act σ) before.state)
    (reserved : firing.selection.made = before.reserve 0 firing.selection.made.length) :
    storeOf (before.commit firing reserved) =
      ((storeOf before).takeAll firing.selection.taken).makeAll (firing.opened (act σ)).produce := by
  let taken := firing.selection.taken
  let outputs := (firing.opened (act σ)).produce
  let made := firing.selection.made
  let old := storeOf before
  let result := firing.result (act σ) before.state
  have takeView := Store.takeAll_occurrences old taken
  have makeView := Store.makeAll_occurrences (old.takeAll taken) outputs
  have width : made.length = outputs.length := by
    change firing.selection.made.length = (firing.rule.body.produce.map _).length
    rw [List.length_map, shapes.2.2.2.2.2.1]
  have oldFresh : old.fresh = before.next := rfl
  apply store_ext
  · change ((before.live.filter fun i => !taken.contains i) ++ made).map (fun i => (i, result.label i)) =
      ((old.takeAll taken).makeAll outputs).occurrences
    rw [List.map_append, makeView.1, takeView.1, takeView.2, oldFresh]
    apply congrArg₂ List.append
    · change ((before.live.filter fun i => !taken.contains i).map (fun i => (i, result.label i))) =
        ((before.live.map fun i => (i, before.state.label i)).filter (fun x => !taken.contains x.1))
      rw [List.filter_map]
      apply List.map_congr_left
      intro identity inRest
      have existing := before.allocated identity (List.mem_filter.mp inRest).1
      have notMade : identity ∉ made := by
        intro fresh
        have allocated : identity ∈ firing.selection.made := fresh
        rw [reserved] at allocated
        have starts := (before.mem_reserve.mp allocated).1
        omega
      have oldLabel := firing.result_label_other (X := act σ) (s := before.state) notMade
      have reads : firing.row (act σ) before.state identity = before.state.label identity :=
        Subst.applyTerm_id _
      exact congrArg (fun term => (identity, term)) (oldLabel.trans reads)
    · have physical : made = List.range' before.next outputs.length := by
        rw [← width]
        simpa only [LiveWorld.reserve, Nat.add_zero] using reserved
      rw [← zip_range outputs before.next, ← physical]
      have source := List.map_fst_zip (l₁ := made) (l₂ := outputs) width.le
      calc
        made.map (fun i => (i, result.label i)) =
            ((made.zip outputs).map Prod.fst).map (fun i => (i, result.label i)) := by rw [source]
        _ = (made.zip outputs).map (fun entry => (entry.1, result.label entry.1)) := List.map_map
        _ = made.zip outputs := by
          conv_rhs => rw [← List.map_id (made.zip outputs)]
          apply List.map_congr_left
          intro entry member
          have ready := firing.result_label_made (X := act σ) (s := before.state) shapes member
          exact Prod.ext rfl ready
  · change before.next + made.length = ((old.takeAll taken).makeAll outputs).fresh
    rw [makeView.2, takeView.2, oldFresh, width]

def emit (level taken made : ℕ) : Code σ :=
  .seq (.fund 1) (.seq (takesFrom level 0 taken)
    (.seq (makesFrom level 0 made) (.ret .completed passReg)))

variable [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]

theorem execute_emit (base : Equations σ) (state : Frame σ) (level taken made : ℕ)
    (takeCount : (state.levels level).taken.length = taken) (makeCount : (state.levels level).made.length = made) :
    if state.machine.budget - state.machine.spent < (1 : Word) then
      SymbolicExecution.execute base state (emit level taken made) = .returned .exhausted ExitStatus.exhausted.word state
    else
      ∃ after, SymbolicExecution.execute base state (emit level taken made) =
          .returned .completed (state.machine.registers passReg) after ∧
        after.levels level = state.levels level ∧
        after.store = ((state.store.takeAll (state.levels level).taken).makeAll (state.levels level).made) ∧
        after.machine.spent = state.machine.spent + 1 := by
  let paid := {state with machine := {state.machine with spent := state.machine.spent + 1}}
  let reduced := {paid with store := paid.store.takeAll (state.levels level).taken}
  let filled := {reduced with store := reduced.store.makeAll (state.levels level).made}
  have money : (1 : BitVec 32).zeroExtend 64 = (1 : Word) := by decide
  have start :
      SymbolicExecution.execute base state (emit level taken made) =
        (fund state 1).thenContinue (fun now =>
          SymbolicExecution.execute base now (.seq (takesFrom level 0 taken)
            (.seq (makesFrom level 0 made) (.ret .completed passReg)))) := rfl
  by_cases exhausted : state.machine.budget - state.machine.spent < (1 : Word)
  · rw [if_pos exhausted, start, fund, money, if_pos exhausted]
    rfl
  · have takes : SymbolicExecution.execute base paid (takesFrom level 0 taken) = .continuing reduced :=
      takesFrom_execute (profile base) level (state.levels level) taken 0 paid rfl (by simpa using takeCount)
    have makes : SymbolicExecution.execute base reduced (makesFrom level 0 made) = .continuing filled :=
      makesFrom_execute (profile base) level (state.levels level) made 0 reduced rfl (by simpa using makeCount)
    rw [if_neg exhausted]
    refine ⟨filled, ?_, rfl, rfl, rfl⟩
    rw [start, fund, money, if_neg exhausted]
    change (SymbolicExecution.execute base paid (takesFrom level 0 taken)).thenContinue
      (fun next => SymbolicExecution.execute base next (.seq (makesFrom level 0 made) (.ret .completed passReg))) = _
    rw [takes, Flow.thenContinue]
    change (SymbolicExecution.execute base reduced (makesFrom level 0 made)).thenContinue
      (fun next => SymbolicExecution.execute base next (.ret .completed passReg)) = _
    rw [makes]
    rfl

end Mettapedia.Machines.TIsa.StoreInstructions.SymbolicPublication
