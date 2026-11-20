import Mettapedia.Languages.MeTTa.PrimeCandidates.Strategies.NativeEquationNeed

/-!
# Kernel-checked runs of the authored-equation Need machine

Concrete answer, closure and budget checks for the authored equation programs of
`NativeEquationNeed.Controls`. Each run is reduced by the kernel; the 3000-step
runs are certified through kernel-checked checkpoints of the existing core runner.
-/

set_option autoImplicit false
set_option Elab.async false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed
open Mettapedia.GSLT.Core.BranchingTemporal
open Mettapedia.GSLT.Core.InferenceControl

namespace Controls

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

example : (values program (call "twice" [call "coin"]) 4 400).length = 2 := by
  rw [values_eq_coreValues]
  decide +kernel
example : values program (call "twice" [call "coin"]) 4 400 =
    [call "Pair" [integer 0, integer 0], call "Pair" [integer 1, integer 1]] := by
  rw [values_eq_coreValues]
  decide +kernel
example : (values program (call "Pair" [call "coin", call "coin"]) 4 400).length = 4 := by
  rw [values_eq_coreValues]
  decide +kernel

private abbrev CoreState := Mettapedia.GSLT.Core.DemandExecution.State
  (WorkOccurrence (NeedExecution.CoreMachine Origin Local Resume Rule Atom Empty String Empty))
  (Outcome × List Nat) Unit

private def coreStart (term : Atom) : CoreState :=
  Mettapedia.GSLT.Core.InferenceControl.Snapshot.initial
    (Controller.fixed Scheduler.breadthFirst)
    [WorkOccurrence.root (NeedExecution.eraseMachine (initial term))]

private def coreRun (fuel : Nat) (state : CoreState) : CoreState :=
  Mettapedia.GSLT.Core.DemandExecution.run
    (NeedInferenceControl.Erasure.coreOccurrenceSystem (specification program))
    (Controller.fixed Scheduler.breadthFirst)
    (Mettapedia.GSLT.Core.DemandExecution.atLeast 7) fuel state

private def coreStopped (state : CoreState) : Bool :=
  Mettapedia.GSLT.Core.DemandExecution.stopped
    (Mettapedia.GSLT.Core.DemandExecution.atLeast 7) state

private theorem coreRun_add (first second : Nat) (state : CoreState) :
    coreRun (first + second) state = coreRun second (coreRun first state) :=
  Mettapedia.GSLT.Core.DemandExecution.run_add _ _ _ _ _ _

private theorem coreRun_of_stopped (fuel : Nat) (state : CoreState)
    (done : coreStopped state = true) : coreRun fuel state = state :=
  Mettapedia.GSLT.Core.DemandExecution.run_of_stopped _ _ _ _ _ done

private def coreObservation (state : CoreState) : List Atom :=
  state.search.events.filterMap fun event =>
    match event.value.1 with
    | .value value => some value
    | _ => none

private theorem values_observation_head (source : Program) (term : Atom) (requested : Nat) :
    values source term requested =
      fun fuel => coreObservation (executeCore source term requested fuel) := by
  funext fuel
  exact values_eq_coreValues source term requested fuel

private theorem execution_head (term : Atom) :
    executeCore program term 7 = fun fuel => coreRun fuel (coreStart term) := rfl

private theorem values_head (term : Atom) :
    values program term 7 = fun fuel => coreObservation (coreRun fuel (coreStart term)) :=
  (values_observation_head program term 7).trans
    (congrArg (fun runner => fun fuel => coreObservation (runner fuel)) (execution_head term))

private theorem checkpoint_observation (term : Atom) (fuel : Nat) (state : CoreState)
    (same : coreRun fuel (coreStart term) = state) :
    values program term 7 fuel = coreObservation state :=
  (congrFun (values_head term) fuel).trans (congrArg coreObservation same)

open Lean Meta Elab Command Term

local elab "checked_need_checkpoint " checkpoint:ident " := " expression:term : command => do
  let name := mkPrivateName (← getEnv) ((← getCurrNamespace) ++ checkpoint.getId)
  liftTermElabM do
    let original ← elabTermEnsuringType expression (mkConst ``CoreState)
    synthesizeSyntheticMVarsNoPostponing
    let original ← instantiateMVars original
    let arguments := original.getAppArgs
    unless original.isAppOfArity ``coreRun 2 do
      throwError "A Need checkpoint must use the existing core runner"
    let stoppedExpression := mkApp (mkConst ``coreStopped) arguments[1]!
    let stopped ← whnf stoppedExpression
    let (result, proof) ← if stopped.isConstOf ``Bool.true then do
        let proof ← mkAppM ``coreRun_of_stopped
          #[arguments[0]!, arguments[1]!, ← mkEqRefl (mkConst ``Bool.true)]
        pure (arguments[1]!, proof)
      else do
        let reduced ← Lean.Meta.Tactic.Cbv.cbvEntry original
        let proof ← match reduced with
          | .rfl .. => mkEqRefl original
          | .step _ proof .. => pure proof
        pure (reduced.getResultExpr original, proof)
    let type ← inferType original
    let environment ← getEnv
    if type.hasMVar || result.hasMVar || proof.hasMVar || type.hasFVar ||
        result.hasFVar || proof.hasFVar || type.hasSorry || result.hasSorry || proof.hasSorry ||
        environment.hasUnsafe type || environment.hasUnsafe result || environment.hasUnsafe proof then
      throwError "A Need checkpoint requires a closed safe proof"
    withOptions (fun options => debug.skipKernelTC.set (Elab.async.set options false) false) do
      addDecl <| .defnDecl {
        name, levelParams := [], type, value := result,
        hints := .regular 0, safety := .safe }
      addDecl <| .thmDecl {
        name := name ++ `checked, levelParams := [],
        type := ← mkEq original (mkConst name), value := proof }

/-- Emit separate kernel-checked lemmas, then compose the existing split-run
law. This controls proof reduction without changing the evaluator or budget. -/
local macro "checked_need_run " final:ident " from " initial:term:max " fuel " allowance:num :
    command => do
  let startName := Lean.mkIdent (final.getId ++ `start)
  let startProof := Lean.mkIdent (final.getId ++ `startPrefix)
  let start ← `(command| private def $startName : CoreState := $initial)
  let startReceipt ← `(command|
    private theorem $startProof : coreRun 0 $startName = $startName := rfl)
  let mut commands := #[start, startReceipt]
  let mut previous := startName
  let mut previousProof := startProof
  let mut used := 0
  let mut index := 0
  let total := allowance.getNat
  while used < total do
    let count := min (if used < 1500 then 50 else 10) (total - used)
    index := index + 1
    let checkpoint := Lean.mkIdent (Lean.Name.str final.getId ("checkpoint" ++ toString index))
    let checked := Lean.mkIdent (checkpoint.getId ++ `checked)
    let prefixName := Lean.mkIdent (checkpoint.getId ++ `prefix)
    let beforeSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString used)⟩
    let countSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString count)⟩
    let totalSyntax : Lean.TSyntax `num := ⟨Lean.Syntax.mkNumLit (toString (used + count))⟩
    let computed ← `(command|
      checked_need_checkpoint $checkpoint := coreRun $countSyntax $previous)
    let receipt ← `(command|
      private theorem $prefixName : coreRun $totalSyntax $startName = $checkpoint := by
        calc
          coreRun $totalSyntax $startName =
            coreRun $countSyntax (coreRun $beforeSyntax $startName) :=
              coreRun_add $beforeSyntax $countSyntax $startName
          _ = coreRun $countSyntax $previous := congrArg (coreRun $countSyntax) $previousProof
          _ = $checkpoint := $checked)
    commands := commands.push computed |>.push receipt
    previous := checkpoint
    previousProof := prefixName
    used := used + count
  let value ← `(command| private noncomputable def $final : CoreState := $previous)
  let finalProof := Lean.mkIdent (final.getId ++ `checked)
  let receipt ← `(command|
    private theorem $finalProof : coreRun $allowance $startName = $final := $previousProof)
  commands := commands.push value |>.push receipt
  return ⟨Lean.mkNullNode (commands.map (·.raw))⟩


private def integerQuery : Atom := call "integers" [integer 0]
private def additionQuery : Atom := call "+" [integer 10, integerQuery]

checked_need_run integerRun from (coreStart integerQuery) fuel 3000
checked_need_run additionRun from (coreStart additionQuery) fuel 3000

/-- Recursive-first equations retain the original seven-answer budget. -/
theorem recursive_integers_seven :
    (values program (call "integers" [integer 0]) 7 3000).length = 7 := by
  exact (congrArg List.length
    (checkpoint_observation integerQuery 3000 integerRun integerRun.checked)).trans
    (by decide +kernel)

example : (values program (call "trees") 7 3000).length = 7 := by
  rw [values_eq_coreValues]
  decide +kernel

/-- A non-tail return adds ten after recursive answer production. -/
theorem recursive_addition_seven :
    values program (call "+" [integer 10, call "integers" [integer 0]]) 7 3000 =
      (List.range 7).map (fun n => integer (Int.ofNat n + 10)) := by
  exact (checkpoint_observation additionQuery 3000 additionRun additionRun.checked).trans
    (by decide +kernel)

/-- Two physical authored equations, with their arithmetic left unevaluated. -/
def argumentChoiceEquations : Program :=
  [⟨"region-pick", [], call "+" [integer 2, integer 3]⟩,
   ⟨"region-pick", [], call "+" [integer 4, integer 5]⟩]

def sharedArgumentProgram : Program := argumentChoiceEquations ++
  [⟨"region-shared-argument", ["x"], call "Pair" [.var "x", .var "x"]⟩]

def independentArgumentsProgram : Program := argumentChoiceEquations ++
  [⟨"region-independent-arguments", ["x", "y"], call "Pair" [.var "x", .var "y"]⟩]

def sharedArgumentQuery : Atom :=
  call "region-shared-argument" [call "region-pick"]

def independentArgumentsQuery : Atom :=
  call "region-independent-arguments" [call "region-pick", call "region-pick"]

/-- One allocated argument is used twice; the two coherent occurrences remain. -/
theorem shared_argument_equations_answers :
    values sharedArgumentProgram sharedArgumentQuery 3 400 =
      [call "Pair" [integer 5, integer 5], call "Pair" [integer 9, integer 9]] := by
  rw [values_eq_coreValues]
  decide +kernel

/-- Identical source syntax at distinct argument positions allocates distinct choices. -/
theorem independent_argument_equations_answers :
    values independentArgumentsProgram independentArgumentsQuery 5 400 =
      [call "Pair" [integer 5, integer 5], call "Pair" [integer 5, integer 9],
       call "Pair" [integer 9, integer 5], call "Pair" [integer 9, integer 9]] := by
  rw [values_eq_coreValues]
  decide +kernel

/-- The shared answer check exhausts the rich source's complete frontier. -/
theorem shared_argument_equations_closed :
    (execute sharedArgumentProgram sharedArgumentQuery 3 400).search.frontier = [] := by
  apply (execute_frontier_closed_iff _ _ _ _).mp
  decide +kernel

/-- The independent answers leave no pending branch in the rich source. -/
theorem independent_argument_equations_closed :
    (execute independentArgumentsProgram independentArgumentsQuery 5 400).search.frontier = [] := by
  apply (execute_frontier_closed_iff _ _ _ _).mp
  decide +kernel

/-- Coherent printed pairs alone cannot equate shared and independently supplied arguments. -/
theorem shared_and_independent_argument_answers_differ :
    values sharedArgumentProgram sharedArgumentQuery 3 400 ≠
      values independentArgumentsProgram independentArgumentsQuery 5 400 := by
  rw [shared_argument_equations_answers, independent_argument_equations_answers]
  decide


end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.NativeEquationNeed
