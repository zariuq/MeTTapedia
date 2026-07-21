import Mettapedia.GSLT.LanguageDef.Gauthier.OEISSequenceSemantics

namespace Mettapedia.GSLT.LanguageDef.GauthierE2ScalarSemantics

open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierE2Fuel
open Mettapedia.GSLT.LanguageDef.GauthierSkeleton

abbrev Program := Mettapedia.GSLT.LanguageDef.GauthierE1.Prog

/-- Successful scalar-list execution, existentially hiding the sufficient fuel. -/
def ScalarEval (program : Program) (x y value : Int) : Prop :=
  ∃ fuel, eval fuel orgMemoSignature program [x] [y] defaultWorld = some [value]

theorem scalarEval_congr {program : Program} {x y firstValue secondValue : Int}
    (valuesEqual : firstValue = secondValue)
    (result : ScalarEval program x y firstValue) :
    ScalarEval program x y secondValue := by
  simpa [valuesEqual] using result

theorem scalar_zero (x y : Int) : ScalarEval P.z x y 0 :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem scalar_one (x y : Int) : ScalarEval P.o x y 1 :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem scalar_two (x y : Int) : ScalarEval P.tw x y 2 :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem scalar_x (x y : Int) : ScalarEval P.X x y x :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

theorem scalar_y (x y : Int) : ScalarEval P.Y x y y :=
  ⟨1, by rw [eval.eq_def]; rfl⟩

private theorem scalar_binary
    (operator : Program → Program → Program)
    (combine : Int → Int → Option Int)
    (operatorEquation : ∀ fuel left right x y,
      eval (fuel + 1) orgMemoSignature (operator left right) [x] [y] defaultWorld = (do
        let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
        let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
        mkE combine leftValue rightValue))
    {left right : Program} {x y leftValue rightValue value : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue)
    (combined : combine leftValue rightValue = some value) :
    ScalarEval (operator left right) x y value := by
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

private theorem eval_addi_equation (fuel : Nat) (left right : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.addi left right) [x] [y] defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
      let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
      mkE add? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_diff_equation (fuel : Nat) (left right : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.diff left right) [x] [y] defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
      let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
      mkE sub? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_mult_equation (fuel : Nat) (left right : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.mult left right) [x] [y] defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
      let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
      mkE mul? leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_divi_equation (fuel : Nat) (left right : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.divi left right) [x] [y] defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
      let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
      mkE Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

private theorem eval_modu_equation (fuel : Nat) (left right : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.modu left right) [x] [y] defaultWorld = (do
      let leftValue ← eval fuel orgMemoSignature left [x] [y] defaultWorld
      let rightValue ← eval fuel orgMemoSignature right [x] [y] defaultWorld
      mkE Mettapedia.GSLT.LanguageDef.GauthierE1.smod leftValue rightValue) := by
  rw [eval.eq_def]
  rfl

theorem scalar_addi {left right : Program} {x y leftValue rightValue : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue) :
    ScalarEval (P.addi left right) x y (leftValue + rightValue) :=
  scalar_binary P.addi add? eval_addi_equation leftResult rightResult rfl

theorem scalar_diff {left right : Program} {x y leftValue rightValue : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue) :
    ScalarEval (P.diff left right) x y (leftValue - rightValue) :=
  scalar_binary P.diff sub? eval_diff_equation leftResult rightResult rfl

theorem scalar_mult {left right : Program} {x y leftValue rightValue : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue) :
    ScalarEval (P.mult left right) x y (leftValue * rightValue) :=
  scalar_binary P.mult mul? eval_mult_equation leftResult rightResult rfl

theorem scalar_divi {left right : Program} {x y leftValue rightValue : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue)
    (nonzero : rightValue ≠ 0) :
    ScalarEval (P.divi left right) x y (Int.fdiv leftValue rightValue) :=
  scalar_binary P.divi Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv eval_divi_equation
    leftResult rightResult (by
      simp [Mettapedia.GSLT.LanguageDef.GauthierE1.sdiv, nonzero])

theorem scalar_modu {left right : Program} {x y leftValue rightValue : Int}
    (leftResult : ScalarEval left x y leftValue)
    (rightResult : ScalarEval right x y rightValue)
    (nonzero : rightValue ≠ 0) :
    ScalarEval (P.modu left right) x y (Int.fmod leftValue rightValue) :=
  scalar_binary P.modu Mettapedia.GSLT.LanguageDef.GauthierE1.smod eval_modu_equation
    leftResult rightResult (by
      simp [Mettapedia.GSLT.LanguageDef.GauthierE1.smod, nonzero])

/-- Pure recurrence corresponding to the memo evaluator's one-register loop. -/
def iterateWithCounter (step : Int → Int → Int) : Nat → Int → Int → Int
  | 0, accumulator, _ => accumulator
  | iterations + 1, accumulator, counter =>
      iterateWithCounter step iterations (step accumulator counter) (counter + 1)

theorem iterateWithCounter_mul_const (constant : Int) :
    ∀ iterations accumulator counter,
      iterateWithCounter (fun value _ => constant * value) iterations accumulator counter =
        constant ^ iterations * accumulator := by
  intro iterations
  induction iterations with
  | zero => simp [iterateWithCounter]
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      rw [iterateWithCounter, inductionHypothesis, pow_succ]
      ring

theorem iterateWithCounter_replace (step : Int → Int) :
    ∀ iterations accumulator counter,
      iterateWithCounter (fun _ currentCounter => step currentCounter) (iterations + 1)
          accumulator counter = step (counter + Int.ofNat iterations) := by
  intro iterations
  induction iterations with
  | zero => simp [iterateWithCounter]
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      rw [iterateWithCounter, inductionHypothesis]
      congr 1
      change counter + 1 + (iterations : Int) =
        counter + ((iterations + 1 : Nat) : Int)
      push_cast
      ring

/-- Sum of the successive loop counters `counter, ..., counter + iterations - 1`. -/
def counterSum : Nat → Int → Int
  | 0, _ => 0
  | iterations + 1, counter => counter + counterSum iterations (counter + 1)

theorem iterateWithCounter_add_affine (coefficient constant : Int) :
    ∀ iterations accumulator counter,
      iterateWithCounter
          (fun value currentCounter => value + coefficient * currentCounter + constant)
          iterations accumulator counter =
        accumulator + coefficient * counterSum iterations counter +
          constant * Int.ofNat iterations := by
  intro iterations
  induction iterations with
  | zero => simp [iterateWithCounter, counterSum]
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      rw [iterateWithCounter, inductionHypothesis]
      simp only [counterSum]
      change accumulator + coefficient * counter + constant +
          coefficient * counterSum iterations (counter + 1) +
          constant * (iterations : Int) =
        accumulator + coefficient *
            (counter + counterSum iterations (counter + 1)) +
          constant * ((iterations + 1 : Nat) : Int)
      push_cast
      ring

theorem two_mul_counterSum :
    ∀ iterations counter,
      2 * counterSum iterations counter =
        Int.ofNat iterations * (2 * counter + Int.ofNat iterations - 1) := by
  intro iterations
  induction iterations with
  | zero => simp [counterSum]
  | succ iterations inductionHypothesis =>
      intro counter
      rw [counterSum]
      calc
        2 * (counter + counterSum iterations (counter + 1)) =
            2 * counter + 2 * counterSum iterations (counter + 1) := by ring
        _ = 2 * counter + Int.ofNat iterations *
            (2 * (counter + 1) + Int.ofNat iterations - 1) := by
              rw [inductionHypothesis]
        _ = Int.ofNat (iterations + 1) *
            (2 * counter + Int.ofNat (iterations + 1) - 1) := by
              change 2 * counter + (iterations : Int) *
                  (2 * (counter + 1) + (iterations : Int) - 1) =
                ((iterations + 1 : Nat) : Int) *
                  (2 * counter + ((iterations + 1 : Nat) : Int) - 1)
              push_cast
              ring

theorem iterateWithCounter_succ_last (step : Int → Int → Int) :
    ∀ iterations accumulator counter,
      iterateWithCounter step (iterations + 1) accumulator counter =
        step (iterateWithCounter step iterations accumulator counter)
          (counter + Int.ofNat iterations) := by
  intro iterations
  induction iterations with
  | zero => simp [iterateWithCounter]
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      rw [iterateWithCounter, inductionHypothesis]
      have counterEquality : counter + 1 + Int.ofNat iterations =
          counter + Int.ofNat (iterations + 1) := by
        change counter + 1 + (iterations : Int) =
          counter + ((iterations + 1 : Nat) : Int)
        push_cast
        ring
      rw [counterEquality]
      rw [iterateWithCounter]

theorem loopIter_scalar (body : Program) (step : Int → Int → Int)
    (bodyResult : ∀ accumulator counter,
      ScalarEval body accumulator counter (step accumulator counter)) :
    ∀ iterations accumulator counter,
      ∃ fuel, loopIter fuel orgMemoSignature body iterations [accumulator] [counter]
        defaultWorld = some [iterateWithCounter step iterations accumulator counter] := by
  intro iterations
  induction iterations with
  | zero =>
      intro accumulator counter
      exact ⟨1, by simp [GauthierE2.loopIter, iterateWithCounter]⟩
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      obtain ⟨bodyFuel, bodySuccess⟩ := bodyResult accumulator counter
      obtain ⟨loopFuel, loopSuccess⟩ :=
        inductionHypothesis (step accumulator counter) (counter + 1)
      let commonFuel := max bodyFuel loopFuel
      have bodyAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) bodySuccess
      have loopAtCommon := loopIter_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) loopSuccess
      refine ⟨commonFuel + 1, ?_⟩
      rw [loopIter]
      simp [bodyAtCommon, loopAtCommon, singletonHeadIncr, iterateWithCounter]

private theorem eval_loop_equation (fuel : Nat) (body count initial : Program)
    (x y : Int) :
    eval (fuel + 1) orgMemoSignature (P.loop body count initial) [x] [y] defaultWorld = (do
      let countValues ← eval fuel orgMemoSignature count [x] [y] defaultWorld
      let initialValues ← eval fuel orgMemoSignature initial [x] [y] defaultWorld
      let countValue ← head? countValues
      if countValue < 0 then some initialValues
      else loopIter fuel orgMemoSignature body countValue.toNat initialValues [1] defaultWorld) := by
  rw [GauthierE2.eval.eq_def]
  rfl

theorem scalar_loop {body count initial : Program} {x y : Int} {iterations : Nat}
    {initialValue : Int} (step : Int → Int → Int)
    (countResult : ScalarEval count x y (Int.ofNat iterations))
    (initialResult : ScalarEval initial x y initialValue)
    (bodyResult : ∀ accumulator counter,
      ScalarEval body accumulator counter (step accumulator counter)) :
    ScalarEval (P.loop body count initial) x y
      (iterateWithCounter step iterations initialValue 1) := by
  obtain ⟨countFuel, countSuccess⟩ := countResult
  obtain ⟨initialFuel, initialSuccess⟩ := initialResult
  obtain ⟨loopFuel, loopSuccess⟩ :=
    loopIter_scalar body step bodyResult iterations initialValue 1
  let commonFuel := max countFuel (max initialFuel loopFuel)
  have countAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) countSuccess
  have initialAtCommon := eval_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) initialSuccess
  have loopAtCommon := loopIter_mono_of_some (larger := commonFuel)
    (by simp [commonFuel]) loopSuccess
  refine ⟨commonFuel + 1, ?_⟩
  rw [eval_loop_equation]
  simp [countAtCommon, initialAtCommon, GauthierE2.head?, loopAtCommon]

theorem scalar_loop_int_count {body count initial : Program} {x y countValue initialValue : Int}
    (step : Int → Int → Int)
    (countResult : ScalarEval count x y countValue)
    (countNonnegative : 0 ≤ countValue)
    (initialResult : ScalarEval initial x y initialValue)
    (bodyResult : ∀ accumulator counter,
      ScalarEval body accumulator counter (step accumulator counter)) :
    ScalarEval (P.loop body count initial) x y
      (iterateWithCounter step countValue.toNat initialValue 1) := by
  apply scalar_loop step
    (scalarEval_congr (Int.toNat_of_nonneg countNonnegative).symm countResult)
    initialResult bodyResult

theorem scalar_loop_mul_const {constant count initial : Program}
    {x y countValue constantValue initialValue : Int}
    (countResult : ScalarEval count x y countValue)
    (countNonnegative : 0 ≤ countValue)
    (constantResult : ∀ accumulator counter,
      ScalarEval constant accumulator counter constantValue)
    (initialResult : ScalarEval initial x y initialValue) :
    ScalarEval (P.loop (P.mult constant P.X) count initial) x y
      (constantValue ^ countValue.toNat * initialValue) := by
  have loopResult := scalar_loop_int_count (fun accumulator _ => constantValue * accumulator)
    countResult countNonnegative initialResult
    (fun accumulator counter =>
      scalar_mult (constantResult accumulator counter) (scalar_x accumulator counter))
  exact scalarEval_congr
    (iterateWithCounter_mul_const constantValue countValue.toNat initialValue 1) loopResult

theorem scalar_loop_mul_value {body count initial : Program}
    {x y countValue constantValue initialValue : Int}
    (countResult : ScalarEval count x y countValue)
    (countNonnegative : 0 ≤ countValue)
    (initialResult : ScalarEval initial x y initialValue)
    (bodyResult : ∀ accumulator counter,
      ScalarEval body accumulator counter (constantValue * accumulator)) :
    ScalarEval (P.loop body count initial) x y
      (constantValue ^ countValue.toNat * initialValue) := by
  have loopResult := scalar_loop_int_count (fun accumulator _ => constantValue * accumulator)
    countResult countNonnegative initialResult bodyResult
  exact scalarEval_congr
    (iterateWithCounter_mul_const constantValue countValue.toNat initialValue 1) loopResult

theorem scalar_loop_mul_value_nat {body count initial : Program}
    {x y initialValue constantValue : Int} {iterations : Nat}
    (countResult : ScalarEval count x y (Int.ofNat iterations))
    (initialResult : ScalarEval initial x y initialValue)
    (bodyResult : ∀ accumulator counter,
      ScalarEval body accumulator counter (constantValue * accumulator)) :
    ScalarEval (P.loop body count initial) x y
      (constantValue ^ iterations * initialValue) := by
  have loopResult := scalar_loop (fun accumulator _ => constantValue * accumulator)
    countResult initialResult bodyResult
  exact scalarEval_congr
    (iterateWithCounter_mul_const constantValue iterations initialValue 1) loopResult

/-- Pure recurrence corresponding to the memo evaluator's two-register loop. -/
def iteratePair (firstStep secondStep : Int → Int → Int) :
    Nat → Int × Int → Int × Int
  | 0, state => state
  | iterations + 1, (first, second) =>
      iteratePair firstStep secondStep iterations
        (firstStep first second, secondStep first second)

theorem iteratePair_mul_fixed :
    ∀ iterations first second,
      iteratePair (fun a b => a * b) (fun _ b => b) iterations (first, second) =
        (first * second ^ iterations, second) := by
  intro iterations
  induction iterations with
  | zero => simp [iteratePair]
  | succ iterations inductionHypothesis =>
      intro first second
      rw [iteratePair, inductionHypothesis, pow_succ]
      congr 1
      ring

theorem iteratePair_add_fixed (increment : Int → Int) :
    ∀ iterations first second,
      iteratePair (fun a b => a + increment b) (fun _ b => b)
          iterations (first, second) =
        (first + Int.ofNat iterations * increment second, second) := by
  intro iterations
  induction iterations with
  | zero => simp [iteratePair]
  | succ iterations inductionHypothesis =>
      intro first second
      rw [iteratePair, inductionHypothesis]
      congr 1
      change first + increment second + (iterations : Int) * increment second =
        first + ((iterations + 1 : Nat) : Int) * increment second
      push_cast
      ring

theorem iteratePair_succ_last (firstStep secondStep : Int → Int → Int) :
    ∀ iterations state,
      iteratePair firstStep secondStep (iterations + 1) state =
        (firstStep (iteratePair firstStep secondStep iterations state).1
            (iteratePair firstStep secondStep iterations state).2,
          secondStep (iteratePair firstStep secondStep iterations state).1
            (iteratePair firstStep secondStep iterations state).2) := by
  intro iterations
  induction iterations with
  | zero => intro state; cases state; simp [iteratePair]
  | succ iterations inductionHypothesis =>
      intro state
      cases state with
      | mk first second =>
        rw [iteratePair, inductionHypothesis]
        rfl

theorem loop2Iter_scalar (first second : Program)
    (firstStep secondStep : Int → Int → Int)
    (firstResult : ∀ x y, ScalarEval first x y (firstStep x y))
    (secondResult : ∀ x y, ScalarEval second x y (secondStep x y)) :
    ∀ iterations firstValue secondValue,
      ∃ fuel, loop2Iter fuel orgMemoSignature first second iterations
        [firstValue] [secondValue] defaultWorld =
          some [(iteratePair firstStep secondStep iterations
            (firstValue, secondValue)).1] := by
  intro iterations
  induction iterations with
  | zero =>
      intro firstValue secondValue
      exact ⟨1, by simp [GauthierE2.loop2Iter, iteratePair]⟩
  | succ iterations inductionHypothesis =>
      intro firstValue secondValue
      obtain ⟨firstFuel, firstSuccess⟩ := firstResult firstValue secondValue
      obtain ⟨secondFuel, secondSuccess⟩ := secondResult firstValue secondValue
      obtain ⟨loopFuel, loopSuccess⟩ := inductionHypothesis
        (firstStep firstValue secondValue) (secondStep firstValue secondValue)
      let commonFuel := max firstFuel (max secondFuel loopFuel)
      have firstAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) firstSuccess
      have secondAtCommon := eval_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) secondSuccess
      have loopAtCommon := loop2Iter_mono_of_some (larger := commonFuel)
        (by simp [commonFuel]) loopSuccess
      refine ⟨commonFuel + 1, ?_⟩
      rw [loop2Iter]
      simp [firstAtCommon, secondAtCommon, loopAtCommon, iteratePair]

private theorem eval_loop2_equation (fuel : Nat)
    (first second count initialFirst initialSecond : Program) (x y : Int) :
    eval (fuel + 1) orgMemoSignature
        (P.loop2 first second count initialFirst initialSecond) [x] [y] defaultWorld = (do
      let countValues ← eval fuel orgMemoSignature count [x] [y] defaultWorld
      let firstValues ← eval fuel orgMemoSignature initialFirst [x] [y] defaultWorld
      let secondValues ← eval fuel orgMemoSignature initialSecond [x] [y] defaultWorld
      let countValue ← head? countValues
      if countValue < 0 then some firstValues
      else
        loop2Iter fuel orgMemoSignature first second countValue.toNat firstValues
          secondValues defaultWorld) := by
  rw [GauthierE2.eval.eq_def]
  rfl

theorem scalar_loop2 {first second count initialFirst initialSecond : Program}
    {x y : Int} {iterations : Nat} {firstValue secondValue : Int}
    (firstStep secondStep : Int → Int → Int)
    (countResult : ScalarEval count x y (Int.ofNat iterations))
    (initialFirstResult : ScalarEval initialFirst x y firstValue)
    (initialSecondResult : ScalarEval initialSecond x y secondValue)
    (firstResult : ∀ a b, ScalarEval first a b (firstStep a b))
    (secondResult : ∀ a b, ScalarEval second a b (secondStep a b)) :
    ScalarEval (P.loop2 first second count initialFirst initialSecond) x y
      ((iteratePair firstStep secondStep iterations (firstValue, secondValue)).1) := by
  obtain ⟨countFuel, countSuccess⟩ := countResult
  obtain ⟨firstFuel, firstSuccess⟩ := initialFirstResult
  obtain ⟨secondFuel, secondSuccess⟩ := initialSecondResult
  obtain ⟨loopFuel, loopSuccess⟩ := loop2Iter_scalar first second firstStep secondStep
    firstResult secondResult iterations firstValue secondValue
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
  simp [countAtCommon, firstAtCommon, secondAtCommon, GauthierE2.head?,
    loopAtCommon]

theorem scalar_loop2_int_count {first second count initialFirst initialSecond : Program}
    {x y countValue firstValue secondValue : Int}
    (firstStep secondStep : Int → Int → Int)
    (countResult : ScalarEval count x y countValue)
    (countNonnegative : 0 ≤ countValue)
    (initialFirstResult : ScalarEval initialFirst x y firstValue)
    (initialSecondResult : ScalarEval initialSecond x y secondValue)
    (firstResult : ∀ a b, ScalarEval first a b (firstStep a b))
    (secondResult : ∀ a b, ScalarEval second a b (secondStep a b)) :
    ScalarEval (P.loop2 first second count initialFirst initialSecond) x y
      ((iteratePair firstStep secondStep countValue.toNat (firstValue, secondValue)).1) := by
  apply scalar_loop2 firstStep secondStep
    (scalarEval_congr (Int.toNat_of_nonneg countNonnegative).symm countResult)
    initialFirstResult initialSecondResult firstResult secondResult

theorem scalarEval_emits {program : Program} {position : Nat} {value : Int}
    (result : ScalarEval program (Int.ofNat position) 0 value) :
    GauthierOEISSequenceSemantics.Emits program position value := by
  obtain ⟨fuel, success⟩ := result
  refine ⟨fuel, ?_⟩
  unfold GauthierE2.term GauthierE2.termWithWorld
  rw [success]
  rfl

#print axioms scalar_addi
#print axioms scalar_loop
#print axioms scalar_loop2
#print axioms scalarEval_emits

end Mettapedia.GSLT.LanguageDef.GauthierE2ScalarSemantics
