import Mettapedia.GSLT.LanguageDef.Gauthier.OEISSequenceSemantics

/-!
# Compositional list-state semantics for the Gauthier E2 evaluator

The memo profile uses lists as an explicit history store.  This file exposes
successful executions as relations and gives compositional rules for the
arithmetic, stack, and iteration primitives.  The relational formulation is
intentional: partial operations such as `pop` have no invented default value.
-/

namespace Mettapedia.GSLT.LanguageDef.GauthierE2ListSemantics

open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierE2Fuel
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

abbrev Program := Mettapedia.GSLT.LanguageDef.GauthierE1.Prog

/-- Successful E2 execution on explicit list-valued registers. -/
def ListEval (program : Program) (x y value : List Int) : Prop :=
  ∃ fuel, eval fuel orgMemoSignature program x y defaultWorld = some value

theorem listEval_mono {program : Program} {x y value : List Int}
    (result : ListEval program x y value) {fuel : Nat}
    (enoughFuel : result.choose ≤ fuel) :
    eval fuel orgMemoSignature program x y defaultWorld = some value :=
  eval_mono_of_some enoughFuel result.choose_spec

theorem list_zero (x y : List Int) : ListEval P.z x y [0] :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem list_one (x y : List Int) : ListEval P.o x y [1] :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem list_two (x y : List Int) : ListEval P.tw x y [2] :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem list_x (x y : List Int) : ListEval P.X x y x :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem list_y (x y : List Int) : ListEval P.Y x y y :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

private theorem list_binary
    (operator : Program → Program → Program)
    (combine : Int → Int → Option Int)
    (operatorEquation : ∀ fuel left right x y,
      eval (fuel + 1) orgMemoSignature (operator left right) x y defaultWorld = (do
        let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
        let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
        mkE combine leftValue rightValue))
    {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead value : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail))
    (combined : combine leftHead rightHead = some value) :
    ListEval (operator left right) x y (value :: leftTail) := by
  obtain ⟨leftFuel, leftSuccess⟩ := leftResult
  obtain ⟨rightFuel, rightSuccess⟩ := rightResult
  let commonFuel := max leftFuel rightFuel
  have leftAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) leftSuccess
  have rightAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) rightSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [operatorEquation]
  simp [leftAtCommon, rightAtCommon, mkE, combined]

private theorem eval_addi_equation (fuel : Nat) (left right : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.addi left right) x y defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
      let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
      mkE add? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_diff_equation (fuel : Nat) (left right : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.diff left right) x y defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
      let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
      mkE sub? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_mult_equation (fuel : Nat) (left right : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.mult left right) x y defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
      let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
      mkE mul? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_divi_equation (fuel : Nat) (left right : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.divi left right) x y defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
      let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
      mkE Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_modu_equation (fuel : Nat) (left right : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.modu left right) x y defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left x y defaultWorld
      let rightValue ← eval fuel orgMemoSignature right x y defaultWorld
      mkE Mettapedia.GSLT.LanguageDef.GauthierE1.smod leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

theorem list_addi {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail)) :
    ListEval (P.addi left right) x y ((leftHead + rightHead) :: leftTail) :=
  list_binary P.addi add? eval_addi_equation leftResult rightResult rfl

theorem list_diff {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail)) :
    ListEval (P.diff left right) x y ((leftHead - rightHead) :: leftTail) :=
  list_binary P.diff sub? eval_diff_equation leftResult rightResult rfl

theorem list_mult {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail)) :
    ListEval (P.mult left right) x y ((leftHead * rightHead) :: leftTail) :=
  list_binary P.mult mul? eval_mult_equation leftResult rightResult rfl

theorem list_divi {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail))
    (nonzero : rightHead ≠ 0) :
    ListEval (P.divi left right) x y
      ((Int.fdiv leftHead rightHead) :: leftTail) :=
  list_binary P.divi Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv
    eval_divi_equation leftResult rightResult (by
      simp [Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv, nonzero])

theorem list_modu {left right : Program} {x y leftTail rightTail : List Int}
    {leftHead rightHead : Int}
    (leftResult : ListEval left x y (leftHead :: leftTail))
    (rightResult : ListEval right x y (rightHead :: rightTail))
    (nonzero : rightHead ≠ 0) :
    ListEval (P.modu left right) x y
      ((Int.fmod leftHead rightHead) :: leftTail) :=
  list_binary P.modu Mettapedia.GSLT.LanguageDef.GauthierE1.smod
    eval_modu_equation leftResult rightResult (by
      simp [Mettapedia.GSLT.LanguageDef.GauthierE1.smod, nonzero])

private theorem eval_cond_equation (fuel : Nat) (condition thenBranch elseBranch : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature
        (P.cond condition thenBranch elseBranch) x y defaultWorld = (do
      let conditionValues ← eval fuel orgMemoSignature condition x y defaultWorld
      let conditionHead ← head? conditionValues
      if conditionHead ≤ 0 then
        eval fuel orgMemoSignature thenBranch x y defaultWorld
      else
        eval fuel orgMemoSignature elseBranch x y defaultWorld) := by
  rw [eval.eq_def]
  rfl

theorem list_cond_nonpositive {condition thenBranch elseBranch : Program}
    {x y conditionTail result : List Int} {conditionHead : Int}
    (conditionResult : ListEval condition x y (conditionHead :: conditionTail))
    (nonpositive : conditionHead ≤ 0)
    (thenResult : ListEval thenBranch x y result) :
    ListEval (P.cond condition thenBranch elseBranch) x y result := by
  obtain ⟨conditionFuel, conditionSuccess⟩ := conditionResult
  obtain ⟨thenFuel, thenSuccess⟩ := thenResult
  let commonFuel := max conditionFuel thenFuel
  have conditionAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) conditionSuccess
  have thenAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) thenSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_cond_equation]
  simp [conditionAtCommon, head?, nonpositive, thenAtCommon]

theorem list_cond_positive {condition thenBranch elseBranch : Program}
    {x y conditionTail result : List Int} {conditionHead : Int}
    (conditionResult : ListEval condition x y (conditionHead :: conditionTail))
    (positive : 0 < conditionHead)
    (elseResult : ListEval elseBranch x y result) :
    ListEval (P.cond condition thenBranch elseBranch) x y result := by
  obtain ⟨conditionFuel, conditionSuccess⟩ := conditionResult
  obtain ⟨elseFuel, elseSuccess⟩ := elseResult
  let commonFuel := max conditionFuel elseFuel
  have conditionAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) conditionSuccess
  have elseAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) elseSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_cond_equation]
  simp [conditionAtCommon, head?, Int.not_le.mpr positive, elseAtCommon]

private theorem eval_push_equation (fuel : Nat) (headProgram tailProgram : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.push headProgram tailProgram) x y defaultWorld = (do
      let headValues ← eval fuel orgMemoSignature headProgram x y defaultWorld
      let tailValues ← eval fuel orgMemoSignature tailProgram x y defaultWorld
      let headValue ← head? headValues
      some (headValue :: tailValues)) := by
  rw [eval.eq_def]
  rfl

private theorem eval_pop_equation (fuel : Nat) (program : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.pop program) x y defaultWorld = (do
      let values ← eval fuel orgMemoSignature program x y defaultWorld
      match values with
      | [] => none
      | [value] => some [value]
      | _ :: tail => some tail) := by
  rw [eval.eq_def]
  rfl

theorem list_push {headProgram tailProgram : Program}
    {x y headTail tailValue : List Int} {head : Int}
    (headResult : ListEval headProgram x y (head :: headTail))
    (tailResult : ListEval tailProgram x y tailValue) :
    ListEval (P.push headProgram tailProgram) x y (head :: tailValue) := by
  obtain ⟨headFuel, headSuccess⟩ := headResult
  obtain ⟨tailFuel, tailSuccess⟩ := tailResult
  let commonFuel := max headFuel tailFuel
  have headAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) headSuccess
  have tailAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) tailSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_push_equation]
  simp [headAtCommon, tailAtCommon, head?]

theorem list_pop_singleton {program : Program} {x y : List Int} {value : Int}
    (result : ListEval program x y [value]) :
    ListEval (P.pop program) x y [value] := by
  obtain ⟨fuel, success⟩ := result
  refine ⟨fuel + 1, ?_⟩
  rw [eval_pop_equation]
  simp [success]

theorem list_pop_cons {program : Program} {x y tail : List Int}
    {first second : Int}
    (result : ListEval program x y (first :: second :: tail)) :
    ListEval (P.pop program) x y (second :: tail) := by
  obtain ⟨fuel, success⟩ := result
  refine ⟨fuel + 1, ?_⟩
  rw [eval_pop_equation]
  simp [success]

/--
Finite reverse-chronological history of a stream, including position zero.
This is the list representation used by stateful sequence generators whose
newest observation is stored at the head.
-/
def reverseHistory {α : Type*} (stream : Nat → α) : Nat → List α
  | 0 => [stream 0]
  | last + 1 => stream (last + 1) :: reverseHistory stream last

@[simp] theorem reverseHistory_length {α : Type*} (stream : Nat → α)
    (last : Nat) :
    (reverseHistory stream last).length = last + 1 := by
  induction last with
  | zero => rfl
  | succ last inductionHypothesis =>
      simp [reverseHistory, inductionHypothesis]

@[simp] theorem reverseHistory_head {α : Type*} (stream : Nat → α)
    (last : Nat) :
    (reverseHistory stream last).head? = some (stream last) := by
  cases last <;> simp [reverseHistory]

/-- Dropping recent entries exposes the corresponding earlier history. -/
theorem reverseHistory_drop {α : Type*} {stream : Nat → α} :
    ∀ {last count : Nat}, count ≤ last →
      (reverseHistory stream last).drop count =
        reverseHistory stream (last - count) := by
  intro last count bound
  induction count generalizing last with
  | zero => simp
  | succ count inductionHypothesis =>
      cases last with
      | zero => omega
      | succ last =>
          simp only [reverseHistory, List.drop_succ_cons]
          rw [inductionHypothesis (by omega), Nat.succ_sub_succ_eq_sub]

/-- Repeated `pop`, retaining the final singleton exactly as E2 does. -/
def stickyDrop : Nat → List Int → List Int
  | 0, values => values
  | _ + 1, [] => []
  | _ + 1, [value] => [value]
  | iterations + 1, _ :: second :: tail =>
      stickyDrop iterations (second :: tail)

@[simp] theorem stickyDrop_singleton (iterations : Nat) (value : Int) :
    stickyDrop iterations [value] = [value] := by
  cases iterations <;> rfl

@[simp] theorem stickyDrop_nil (iterations : Nat) :
    stickyDrop iterations [] = [] := by
  cases iterations <;> rfl

theorem stickyDrop_nonempty : ∀ {iterations : Nat} {values : List Int},
    values ≠ [] → stickyDrop iterations values ≠ [] := by
  intro iterations
  induction iterations with
  | zero => simp [stickyDrop]
  | succ iterations inductionHypothesis =>
      intro values nonempty
      cases values with
      | nil => exact (nonempty rfl).elim
      | cons first tail =>
          cases tail with
          | nil => simp
          | cons second tail =>
              exact inductionHypothesis (by simp)

theorem stickyDrop_add : ∀ (first second : Nat) (values : List Int),
    stickyDrop first (stickyDrop second values) =
      stickyDrop (first + second) values := by
  intro first second
  induction second with
  | zero => intro values; simp [stickyDrop]
  | succ second inductionHypothesis =>
      intro values
      cases values with
      | nil => simp [stickyDrop]
      | cons head tail =>
          cases tail with
          | nil => simp
          | cons next tail =>
              rw [show first + (second + 1) = (first + second) + 1 by omega]
              simp only [stickyDrop]
              exact inductionHypothesis (next :: tail)

theorem list_pop_x {values y : List Int} (nonempty : values ≠ []) :
    ListEval (P.pop P.X) values y (stickyDrop 1 values) := by
  cases values with
      | nil => exact (nonempty rfl).elim
      | cons first tail =>
          cases tail with
          | nil =>
              change ListEval (P.pop P.X) [first] y [first]
              exact list_pop_singleton (list_x [first] y)
          | cons second tail =>
              change ListEval (P.pop P.X) (first :: second :: tail) y (second :: tail)
              exact list_pop_cons (list_x (first :: second :: tail) y)

/-- Relational closure of a one-register loop body. -/
inductive Iterates (body : Program) : Nat → List Int → Int → List Int → Prop
  | zero (state : List Int) (counter : Int) : Iterates body 0 state counter state
  | succ {iterations : Nat} {state next final : List Int} {counter : Int}
      (step : ListEval body state [counter] next)
      (rest : Iterates body iterations next (counter + 1) final) :
      Iterates body (iterations + 1) state counter final

theorem pop_iterates : ∀ {iterations values counter}, values ≠ [] →
    Iterates (P.pop P.X) iterations values counter (stickyDrop iterations values) := by
  intro iterations
  induction iterations with
  | zero =>
      intro values counter nonempty
      exact Iterates.zero values counter
  | succ iterations inductionHypothesis =>
      intro values counter nonempty
      cases values with
      | nil => exact (nonempty rfl).elim
      | cons first tail =>
          cases tail with
          | nil =>
              have rest := inductionHypothesis (values := [first])
                (counter := counter + 1) (by simp)
              simpa [stickyDrop] using Iterates.succ
                (list_pop_singleton (list_x [first] [counter])) rest
          | cons second tail =>
              have rest := inductionHypothesis (values := second :: tail)
                (counter := counter + 1) (by simp)
              simpa [stickyDrop] using Iterates.succ
                (list_pop_cons (list_x (first :: second :: tail) [counter])) rest

theorem stickyDrop_eq_drop {iterations : Nat} {values : List Int}
    (beforeLast : iterations < values.length) :
    stickyDrop iterations values = values.drop iterations := by
  induction iterations generalizing values with
  | zero => rfl
  | succ iterations inductionHypothesis =>
      cases values with
      | nil => simp at beforeLast
      | cons first tail =>
          cases tail with
          | nil => simp at beforeLast
          | cons second tail =>
              simp only [stickyDrop, List.drop_succ_cons]
              apply inductionHypothesis
              simpa using beforeLast

theorem loopIter_of_iterates {body : Program} :
    ∀ {iterations state counter final},
      Iterates body iterations state counter final →
      ∃ fuel, loopIter fuel orgMemoSignature body iterations state [counter]
        defaultWorld = some final := by
  intro iterations state counter final execution
  induction execution with
  | zero state counter =>
      exact ⟨1, by simp [loopIter]⟩
  | @succ iterations state next final counter step rest inductionHypothesis =>
      obtain ⟨stepFuel, stepSuccess⟩ := step
      obtain ⟨restFuel, restSuccess⟩ := inductionHypothesis
      let commonFuel := max stepFuel restFuel
      have stepAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) stepSuccess
      have restAtCommon := loopIter_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) restSuccess
      refine ⟨commonFuel + 1, ?_⟩
      rw [loopIter]
      simp [stepAtCommon, restAtCommon, singletonHeadIncr]

private theorem eval_loop_equation (fuel : Nat) (body count initial : Program)
    (x y : List Int) :
    eval (fuel + 1) orgMemoSignature (P.loop body count initial) x y defaultWorld = (do
      let countValues ← eval fuel orgMemoSignature count x y defaultWorld
      let initialValues ← eval fuel orgMemoSignature initial x y defaultWorld
      let countValue ← head? countValues
      if countValue < 0 then some initialValues
      else
        loopIter fuel orgMemoSignature body countValue.toNat initialValues [1]
          defaultWorld) := by
  rw [eval.eq_def]
  rfl

theorem list_loop {body count initial : Program} {x y countTail initialValue final : List Int}
    {iterations : Nat}
    (countResult : ListEval count x y (Int.ofNat iterations :: countTail))
    (initialResult : ListEval initial x y initialValue)
    (execution : Iterates body iterations initialValue 1 final) :
    ListEval (P.loop body count initial) x y final := by
  obtain ⟨countFuel, countSuccess⟩ := countResult
  obtain ⟨initialFuel, initialSuccess⟩ := initialResult
  obtain ⟨loopFuel, loopSuccess⟩ := loopIter_of_iterates execution
  let commonFuel := max countFuel (max initialFuel loopFuel)
  have countAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) countSuccess
  have initialAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) initialSuccess
  have loopAtCommon := loopIter_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) loopSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_loop_equation]
  simp [countAtCommon, initialAtCommon, head?, loopAtCommon]

theorem list_loop_negative {body count initial : Program}
    {x y countTail initialValue : List Int} {countValue : Int}
    (countResult : ListEval count x y (countValue :: countTail))
    (negative : countValue < 0)
    (initialResult : ListEval initial x y initialValue) :
    ListEval (P.loop body count initial) x y initialValue := by
  obtain ⟨countFuel, countSuccess⟩ := countResult
  obtain ⟨initialFuel, initialSuccess⟩ := initialResult
  let commonFuel := max countFuel initialFuel
  have countAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) countSuccess
  have initialAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) initialSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_loop_equation]
  simp [countAtCommon, initialAtCommon, head?, negative]

/-- Relational closure of a simultaneous two-register loop body. -/
inductive Iterates2 (first second : Program) :
    Nat → List Int → List Int → List Int → Prop
  | zero (firstState secondState : List Int) :
      Iterates2 first second 0 firstState secondState firstState
  | succ {iterations : Nat}
      {firstState secondState nextFirst nextSecond final : List Int}
      (firstStep : ListEval first firstState secondState nextFirst)
      (secondStep : ListEval second firstState secondState nextSecond)
      (rest : Iterates2 first second iterations nextFirst nextSecond final) :
      Iterates2 first second (iterations + 1) firstState secondState final

theorem loop2Iter_of_iterates {first second : Program} :
    ∀ {iterations firstState secondState final},
      Iterates2 first second iterations firstState secondState final →
      ∃ fuel, loop2Iter fuel orgMemoSignature first second iterations
        firstState secondState defaultWorld = some final := by
  intro iterations firstState secondState final execution
  induction execution with
  | zero firstState secondState =>
      exact ⟨1, by simp [loop2Iter]⟩
  | @succ iterations firstState secondState nextFirst nextSecond final
      firstStep secondStep rest inductionHypothesis =>
      obtain ⟨firstFuel, firstSuccess⟩ := firstStep
      obtain ⟨secondFuel, secondSuccess⟩ := secondStep
      obtain ⟨restFuel, restSuccess⟩ := inductionHypothesis
      let commonFuel := max firstFuel (max secondFuel restFuel)
      have firstAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) firstSuccess
      have secondAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) secondSuccess
      have restAtCommon := loop2Iter_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) restSuccess
      refine ⟨commonFuel + 1, ?_⟩
      rw [loop2Iter]
      simp [firstAtCommon, secondAtCommon, restAtCommon]

private theorem eval_loop2_equation (fuel : Nat)
    (first second count firstInitial secondInitial : Program) (x y : List Int) :
    eval (fuel + 1) orgMemoSignature
        (P.loop2 first second count firstInitial secondInitial) x y defaultWorld = (do
      let countValues ← eval fuel orgMemoSignature count x y defaultWorld
      let firstValues ← eval fuel orgMemoSignature firstInitial x y defaultWorld
      let secondValues ← eval fuel orgMemoSignature secondInitial x y defaultWorld
      let countValue ← head? countValues
      if countValue < 0 then some firstValues
      else
        loop2Iter fuel orgMemoSignature first second countValue.toNat
          firstValues secondValues defaultWorld) := by
  rw [eval.eq_def]
  rfl

theorem list_loop2 {first second count firstInitial secondInitial : Program}
    {x y countTail firstValue secondValue final : List Int} {iterations : Nat}
    (countResult : ListEval count x y (Int.ofNat iterations :: countTail))
    (firstInitialResult : ListEval firstInitial x y firstValue)
    (secondInitialResult : ListEval secondInitial x y secondValue)
    (execution : Iterates2 first second iterations firstValue secondValue final) :
    ListEval (P.loop2 first second count firstInitial secondInitial) x y final := by
  obtain ⟨countFuel, countSuccess⟩ := countResult
  obtain ⟨firstFuel, firstSuccess⟩ := firstInitialResult
  obtain ⟨secondFuel, secondSuccess⟩ := secondInitialResult
  obtain ⟨loopFuel, loopSuccess⟩ := loop2Iter_of_iterates execution
  let commonFuel := max countFuel (max firstFuel (max secondFuel loopFuel))
  have countAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) countSuccess
  have firstAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) firstSuccess
  have secondAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) secondSuccess
  have loopAtCommon := loop2Iter_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) loopSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_loop2_equation]
  simp [countAtCommon, firstAtCommon, secondAtCommon, head?, loopAtCommon]

theorem listEval_emits {program : Program} {position : Nat} {value : Int}
    (result : ListEval program [Int.ofNat position] [0] [value]) :
    Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics.Emits
      program position value := by
  obtain ⟨fuel, success⟩ := result
  exact ⟨fuel, by
    unfold term termWithWorld
    rw [success]
    rfl⟩

theorem listEval_head_emits {program : Program} {position : Nat}
    {value : Int} {tail : List Int}
    (result : ListEval program [Int.ofNat position] [0] (value :: tail)) :
    Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics.Emits
      program position value := by
  obtain ⟨fuel, success⟩ := result
  exact ⟨fuel, by
    unfold term termWithWorld
    rw [success]
    rfl⟩

#print axioms list_addi
#print axioms list_push
#print axioms list_pop_cons
#print axioms list_loop
#print axioms list_cond_nonpositive
#print axioms list_cond_positive
#print axioms list_loop2

end Mettapedia.GSLT.LanguageDef.GauthierE2ListSemantics
