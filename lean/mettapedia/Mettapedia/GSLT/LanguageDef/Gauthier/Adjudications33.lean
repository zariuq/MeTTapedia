import Mettapedia.GSLT.LanguageDef.Gauthier.E2ScalarSemantics
import Mettapedia.GSLT.LanguageDef.Gauthier.FrozenCandidates49

namespace Mettapedia.GSLT.LanguageDef.GauthierAdjudications33

open Mettapedia.GSLT.LanguageDef.GauthierE2
open Mettapedia.GSLT.LanguageDef.GauthierE2ScalarSemantics
open Mettapedia.GSLT.LanguageDef.GauthierOEISSequenceSemantics
open Mettapedia.GSLT.LanguageDef.GauthierFrozenCandidates49
open Mettapedia.Sequences.OEIS
open Mettapedia.Sequences.OEIS.Elementary49

private theorem realizes_of_scalar {spec : Mettapedia.Sequences.OEIS.SequenceSpec}
    {candidate : FrozenCandidate}
    (result : ∀ position, spec.Domain (spec.index position) →
      ScalarEval candidate.program (Int.ofNat position) 0
        (spec.value (spec.index position))) :
    CandidateRealizes spec candidate := by
  intro position indexInDomain
  exact emits_implies_eventuallyEmits
    (scalarEval_emits (result position indexInDomain))

private theorem scalar_square (x y : Int) :
    ScalarEval (P.mult P.X P.X) x y (x ^ 2) := by
  simpa [pow_two] using scalar_mult (scalar_x x y) (scalar_x x y)

private theorem scalar_cube (x y : Int) :
    ScalarEval (P.mult (P.mult P.X P.X) P.X) x y (x ^ 3) := by
  have square := scalar_mult (scalar_x x y) (scalar_x x y)
  simpa [pow_succ] using scalar_mult square (scalar_x x y)

private theorem scalar_square_loop_one {initial : GauthierE2ScalarSemantics.Program}
    {x y value : Int}
    (initialResult : ScalarEval initial x y value) :
    ScalarEval (P.loop (P.mult P.X P.X) P.o initial) x y (value ^ 2) := by
  have loopResult := scalar_loop (x := x) (y := y)
    (fun accumulator _ => accumulator ^ 2)
    (scalar_one _ _) initialResult (fun accumulator counter => scalar_square accumulator counter)
  apply scalarEval_congr (result := loopResult)
  simp [iterateWithCounter]

private theorem scalar_square_loop_two {initial : GauthierE2ScalarSemantics.Program}
    {x y value : Int}
    (initialResult : ScalarEval initial x y value) :
    ScalarEval (P.loop (P.mult P.X P.X) P.tw initial) x y (value ^ 4) := by
  have loopResult := scalar_loop (x := x) (y := y)
    (fun accumulator _ => accumulator ^ 2)
    (scalar_two _ _) initialResult (fun accumulator counter => scalar_square accumulator counter)
  apply scalarEval_congr (result := loopResult)
  simp [iterateWithCounter, pow_succ]
  ring

private theorem scalar_cube_loop_two {initial : GauthierE2ScalarSemantics.Program}
    {x y value : Int}
    (initialResult : ScalarEval initial x y value) :
    ScalarEval (P.loop (P.mult (P.mult P.X P.X) P.X) P.tw initial) x y (value ^ 9) := by
  have loopResult := scalar_loop (x := x) (y := y)
    (fun accumulator _ => accumulator ^ 3)
    (scalar_two _ _) initialResult (fun accumulator counter => scalar_cube accumulator counter)
  apply scalarEval_congr (result := loopResult)
  simp [iterateWithCounter, pow_succ]
  ring

private theorem scalar_cube_loop_one {initial : GauthierE2ScalarSemantics.Program}
    {x y value : Int} (initialResult : ScalarEval initial x y value) :
    ScalarEval (P.loop (P.mult (P.mult P.X P.X) P.X) P.o initial) x y (value ^ 3) := by
  have loopResult := scalar_loop (x := x) (y := y)
    (fun accumulator _ => accumulator ^ 3)
    (scalar_one _ _) initialResult (fun accumulator counter => scalar_cube accumulator counter)
  apply scalarEval_congr (result := loopResult)
  simp [iterateWithCounter]

private theorem alternatingTenInvariant :
    ∀ iterations accumulator counter,
      11 * iterateWithCounter (fun value _ => 1 - 10 * value)
          iterations accumulator counter =
        (-10 : Int) ^ iterations * (11 * accumulator - 1) + 1 := by
  intro iterations
  induction iterations with
  | zero => simp [iterateWithCounter]
  | succ iterations inductionHypothesis =>
      intro accumulator counter
      rw [iterateWithCounter_succ_last]
      calc
        11 * (1 - 10 * iterateWithCounter (fun value _ => 1 - 10 * value)
            iterations accumulator counter) =
            -10 * (11 * iterateWithCounter (fun value _ => 1 - 10 * value)
              iterations accumulator counter - 1) + 1 := by ring
        _ = -10 * (((-10 : Int) ^ iterations * (11 * accumulator - 1) + 1) - 1) + 1 := by
          rw [inductionHypothesis]
        _ = (-10 : Int) ^ (iterations + 1) * (11 * accumulator - 1) + 1 := by
          rw [pow_succ]
          ring

private theorem pair194Closed : ∀ iterations,
    iteratePair (fun first second => 16 + 2 * first - second) (fun first _ => first)
        iterations (1, 2) =
      (8 * (Int.ofNat iterations) ^ 2 + 7 * Int.ofNat iterations + 1,
        8 * (Int.ofNat iterations) ^ 2 - 9 * Int.ofNat iterations + 2) := by
  intro iterations
  induction iterations with
  | zero => norm_num [iteratePair]
  | succ iterations inductionHypothesis =>
      rw [iteratePair_succ_last, inductionHypothesis]
      apply Prod.ext
      · simp only [Int.ofNat_eq_natCast]
        push_cast
        ring
      · simp only [Int.ofNat_eq_natCast]
        push_cast
        ring

private theorem pair047Closed : ∀ iterations,
    iteratePair (fun first second => first * second) (fun _ second => 3 * second)
        iterations (1, 1) =
      ((3 : Int) ^ iterations.choose 2, (3 : Int) ^ iterations) := by
  intro iterations
  induction iterations with
  | zero => norm_num [iteratePair]
  | succ iterations inductionHypothesis =>
      rw [iteratePair_succ_last, inductionHypothesis]
      apply Prod.ext
      · change (3 : Int) ^ iterations.choose 2 * 3 ^ iterations =
          3 ^ (iterations + 1).choose 2
        rw [← pow_add]
        congr 1
        simp [Nat.choose_succ_succ, Nat.add_comm]
      · change (3 : Int) * 3 ^ iterations = 3 ^ (iterations + 1)
        rw [pow_succ]
        ring

private theorem triangularExponentToNat (n : Nat) :
    ((Int.ofNat n ^ 2 - Int.ofNat n) / 2).toNat = n.choose 2 := by
  cases n with
  | zero => norm_num
  | succ n =>
      rw [Nat.choose_two_right]
      have positive : 1 ≤ n + 1 := by omega
      have castEquality :
          Int.ofNat ((n + 1) * ((n + 1) - 1) / 2) =
            (Int.ofNat (n + 1) ^ 2 - Int.ofNat (n + 1)) / 2 := by
        simp only [Int.ofNat_eq_natCast]
        rw [Int.natCast_ediv, Int.natCast_mul, Int.natCast_sub positive]
        norm_num
        ring_nf
      rw [← castEquality]
      exact Int.toNat_natCast _

private theorem factorialIteration : ∀ iterations,
    iterateWithCounter (fun value counter => 11 * value * counter)
        iterations 1 1 =
      11 ^ iterations * Int.ofNat iterations.factorial := by
  intro iterations
  induction iterations with
  | zero => norm_num [iterateWithCounter]
  | succ iterations inductionHypothesis =>
      rw [iterateWithCounter_succ_last, inductionHypothesis, pow_succ,
        Nat.factorial_succ]
      simp only [Int.ofNat_eq_natCast]
      push_cast
      ring

private theorem elevenThirdIdentity (value : Int) :
    Int.fdiv (2 * value) 3 + 3 * value = 11 * value / 3 := by
  rw [Int.fdiv_eq_ediv_of_nonneg _ (by norm_num : (0 : Int) ≤ 3)]
  calc
    (2 * value) / 3 + 3 * value =
        (2 * value + (3 * value) * 3) / 3 :=
      (Int.add_mul_ediv_right (2 * value) (3 * value)
        (by norm_num : (3 : Int) ≠ 0)).symm
    _ = (11 * value) / 3 := by
      congr 1
      ring

theorem A070439_candidate45_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A070439.spec candidate45 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate45, Mettapedia.Sequences.OEIS.Elementary49.A070439.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have numerator : ScalarEval (P.mult P.X P.X) (Int.ofNat position) 0
      (Int.ofNat position * Int.ofNat position) :=
    scalar_mult (scalar_x _ _) (scalar_x _ _)
  have denominator : ScalarEval (P.loop (P.mult P.X P.X) P.tw P.tw)
      (Int.ofNat position) 0 16 := by
    have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
      (fun accumulator _ => accumulator * accumulator)
      (scalar_two _ _) (scalar_two _ _)
      (fun accumulator counter =>
        scalar_mult (scalar_x accumulator counter) (scalar_x accumulator counter))
    simpa [iterateWithCounter] using loopResult
  have result := scalar_modu numerator denominator (by norm_num)
  simpa [pow_two, Int.fmod_eq_emod] using result

theorem A070478_candidate46_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A070478.spec candidate46 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate46, Mettapedia.Sequences.OEIS.Elementary49.A070478.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have square : ScalarEval (P.mult P.X P.X) (Int.ofNat position) 0
      (Int.ofNat position * Int.ofNat position) :=
    scalar_mult (scalar_x _ _) (scalar_x _ _)
  have numerator : ScalarEval (P.mult (P.mult P.X P.X) P.X)
      (Int.ofNat position) 0
      ((Int.ofNat position * Int.ofNat position) * Int.ofNat position) :=
    scalar_mult square (scalar_x _ _)
  have denominator : ScalarEval (P.loop (P.mult P.X P.X) P.tw P.tw)
      (Int.ofNat position) 0 16 := by
    have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
      (fun accumulator _ => accumulator * accumulator)
      (scalar_two _ _) (scalar_two _ _)
      (fun accumulator counter =>
        scalar_mult (scalar_x accumulator counter) (scalar_x accumulator counter))
    simpa [iterateWithCounter] using loopResult
  have result := scalar_modu numerator denominator (by norm_num)
  simpa [pow_succ, Int.fmod_eq_emod] using result

theorem A070512_candidate47_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A070512.spec candidate47 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate47, Mettapedia.Sequences.OEIS.Elementary49.A070512.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have fourthPower : ScalarEval (P.loop (P.mult P.X P.X) P.tw P.X)
      (Int.ofNat position) 0 (Int.ofNat position ^ 4) := by
    have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
      (fun accumulator _ => accumulator * accumulator)
      (scalar_two _ _) (scalar_x _ _)
      (fun accumulator counter =>
        scalar_mult (scalar_x accumulator counter) (scalar_x accumulator counter))
    apply scalarEval_congr (result := loopResult)
    simp [iterateWithCounter, pow_succ]
    ring
  have seven : ScalarEval (P.addi P.o (P.addi P.tw (P.addi P.tw P.tw)))
      (Int.ofNat position) 0 7 :=
    scalar_addi (scalar_one _ _)
      (scalar_addi (scalar_two _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _)))
  have result := scalar_modu fourthPower seven (by norm_num)
  simpa [Int.fmod_eq_emod] using result

theorem A016779_candidate28_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A016779.spec candidate28 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate28, Mettapedia.Sequences.OEIS.Elementary49.A016779.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have doubled := scalar_addi (scalar_x (Int.ofNat position) 0) (scalar_x _ _)
  have tripled := scalar_addi doubled (scalar_x _ _)
  have base := scalar_addi (scalar_one _ _) tripled
  have result := scalar_cube_loop_one (x := Int.ofNat position) (y := 0)
    (initial := P.addi P.o (P.addi (P.addi P.X P.X) P.X)) base
  apply scalarEval_congr (result := result)
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A016780_candidate29_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A016780.spec candidate29 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate29, Mettapedia.Sequences.OEIS.Elementary49.A016780.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have three := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_two _ _)
  have tripled := scalar_mult three (scalar_x _ _)
  have base := scalar_addi (scalar_one _ _) tripled
  have result := scalar_square_loop_two (x := Int.ofNat position) (y := 0)
    (initial := P.addi P.o (P.mult (P.addi P.o P.tw) P.X)) base
  apply scalarEval_congr (result := result)
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A016814_candidate30_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A016814.spec candidate30 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate30, Mettapedia.Sequences.OEIS.Elementary49.A016814.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have four := scalar_addi (scalar_two (Int.ofNat position) 0) (scalar_two _ _)
  have quadrupled := scalar_mult four (scalar_x _ _)
  have base := scalar_addi (scalar_one _ _) quadrupled
  have result := scalar_square_loop_one (x := Int.ofNat position) (y := 0)
    (initial := P.addi P.o (P.mult (P.addi P.tw P.tw) P.X)) base
  apply scalarEval_congr (result := result)
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A010807_candidate17_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A010807.spec candidate17 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate17, Mettapedia.Sequences.OEIS.Elementary49.A010807.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have initial := scalar_square (Int.ofNat position) 0
  have eighteenthPower := scalar_cube_loop_two (x := Int.ofNat position) (y := 0)
    (initial := P.mult P.X P.X) initial
  have result := scalar_mult eighteenthPower (scalar_x _ _)
  apply scalarEval_congr (result := result)
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A089081_candidate49_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A089081.spec candidate49 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate49, Mettapedia.Sequences.OEIS.Elementary49.A089081.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have outerLoop := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator _ => accumulator ^ 5)
    (scalar_two _ _) (scalar_x _ _)
    (fun accumulator counter => by
      have fourthPower := scalar_square_loop_two (x := accumulator) (y := counter)
        (initial := P.X) (scalar_x _ _)
      have fifthPower := scalar_mult fourthPower (scalar_x _ _)
      apply scalarEval_congr (result := fifthPower)
      ring)
  have multiplied := scalar_mult outerLoop (scalar_x (Int.ofNat position) 0)
  apply scalarEval_congr (result := multiplied)
  simp only [iterateWithCounter, Int.ofNat_eq_natCast]
  ring

theorem A244630_candidate69_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A244630.spec candidate69 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate69, Mettapedia.Sequences.OEIS.Elementary49.A244630.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator _ => 4 * accumulator)
    (scalar_two _ _) (scalar_x _ _)
    (fun accumulator counter => by
      have doubled := scalar_addi (scalar_x accumulator counter) (scalar_x _ _)
      have result := scalar_mult (scalar_two _ _) doubled
      apply scalarEval_congr (result := result)
      ring)
  have added := scalar_addi loopResult (scalar_x (Int.ofNat position) 0)
  have multiplied := scalar_mult added (scalar_x _ _)
  apply scalarEval_congr (result := multiplied)
  simp [iterateWithCounter]
  ring

theorem A022521_candidate31_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A022521.spec candidate31 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate31, Mettapedia.Sequences.OEIS.Elementary49.A022521.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => second ^ 5 - first) (fun _ second => 1 + second)
    (scalar_two _ _) (scalar_zero _ _) (scalar_x _ _)
    (fun first second => by
      have fourthPower := scalar_square_loop_two (x := first) (y := second)
        (initial := P.Y) (scalar_y _ _)
      have fifthPower := scalar_mult fourthPower (scalar_y _ _)
      have fifthPower' : ScalarEval (P.mult (P.loop (P.mult P.X P.X) P.tw P.Y) P.Y)
          first second (second ^ 5) := by
        apply scalarEval_congr (result := fifthPower)
        ring
      exact scalar_diff fifthPower' (scalar_x _ _))
    (fun first second => scalar_addi (scalar_one _ _) (scalar_y _ _))
  apply scalarEval_congr (result := loopResult)
  simp only [iteratePair, Int.ofNat_eq_natCast]
  ring

theorem A036087_candidate38_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A036087.spec candidate38 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate38, Mettapedia.Sequences.OEIS.Elementary49.A036087.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => second ^ 9 + first) (fun _ second => 1 + second)
    (scalar_two _ _) (scalar_zero _ _) (scalar_x _ _)
    (fun first second => by
      have ninthPower := scalar_cube_loop_two (x := first) (y := second)
        (initial := P.Y) (scalar_y _ _)
      exact scalar_addi ninthPower (scalar_x _ _))
    (fun first second => scalar_addi (scalar_one _ _) (scalar_y _ _))
  apply scalarEval_congr (result := loopResult)
  simp only [iteratePair, Int.ofNat_eq_natCast]
  ring

theorem A099762_candidate50_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A099762.spec candidate50 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate50, Mettapedia.Sequences.OEIS.Elementary49.A099762.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have initialFirst := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_x _ _)
  have loopResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => first * second * second) (fun first _ => first)
    (scalar_two _ _) initialFirst (scalar_x _ _)
    (fun first second =>
      scalar_mult (scalar_mult (scalar_x _ _) (scalar_y _ _)) (scalar_y _ _))
    (fun first second => scalar_x _ _)
  apply scalarEval_congr (result := loopResult)
  simp only [iteratePair, Int.ofNat_eq_natCast]
  ring

theorem A002063_candidate00_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A002063.spec candidate00 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate00, Mettapedia.Sequences.OEIS.Elementary49.A002063.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have three := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_two _ _)
  have inner := scalar_loop_mul_value_nat (iterations := position) (constantValue := 2)
    (scalar_x _ _) three
    (fun accumulator counter => by
      have doubled := scalar_addi (scalar_x accumulator counter) (scalar_x _ _)
      apply scalarEval_congr (result := doubled)
      ring)
  have squared := scalar_square_loop_one (x := Int.ofNat position) (y := 0)
    (initial := P.loop (P.addi P.X P.X) P.X (P.addi P.o P.tw)) inner
  have powerIdentity : (4 : Int) ^ position = 2 ^ position * 2 ^ position := by
    rw [show (4 : Int) = 2 * 2 by norm_num, mul_pow]
  apply scalarEval_congr (result := squared)
  simp only [Int.toNat_natCast]
  rw [powerIdentity]
  ring

theorem A013710_candidate24_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A013710.spec candidate24 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate24, Mettapedia.Sequences.OEIS.Elementary49.A013710.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have doubled := scalar_addi (scalar_x (Int.ofNat position) 0) (scalar_x _ _)
  have rawCount := scalar_addi (scalar_one _ _) doubled
  have countResult : ScalarEval (P.addi P.o (P.addi P.X P.X))
      (Int.ofNat position) 0 (Int.ofNat (2 * position + 1)) := by
    apply scalarEval_congr (result := rawCount)
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have fiveAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o (P.addi P.tw P.tw)) accumulator counter 5 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _))
  have loopResult := scalar_loop_mul_value_nat (iterations := 2 * position + 1)
    (constantValue := 5) countResult (scalar_one _ _)
    (fun accumulator counter => scalar_mult (fiveAt _ _) (scalar_x _ _))
  rw [Int.toNat_natCast]
  simpa only [← Int.ofNat_eq_natCast, mul_one] using loopResult

theorem A024064_candidate32_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A024064.spec candidate32 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate32, Mettapedia.Sequences.OEIS.Elementary49.A024064.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have sixAt : ∀ accumulator counter,
      ScalarEval (P.addi P.tw (P.addi P.tw P.tw)) accumulator counter 6 := by
    intro accumulator counter
    exact scalar_addi (scalar_two _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _))
  have power := scalar_loop_mul_value_nat (x := Int.ofNat position) (y := 0)
    (iterations := position) (constantValue := 6)
    (scalar_x _ _) (scalar_one _ _)
    (fun accumulator counter => scalar_mult (sixAt _ _) (scalar_x _ _))
  have result := scalar_diff power (scalar_square (Int.ofNat position) 0)
  apply scalarEval_congr (result := result)
  simp only [Int.toNat_natCast]
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A064751_candidate44_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A064751.spec candidate44 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate44, Mettapedia.Sequences.OEIS.Elementary49.A064751.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  have rawIndex := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_x _ _)
  have indexResult : ScalarEval (P.addi P.o P.X) (Int.ofNat position) 0
      (Int.ofNat (position + 1)) := by
    apply scalarEval_congr (result := rawIndex)
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have fiveAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o (P.addi P.tw P.tw)) accumulator counter 5 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _))
  have power := scalar_loop_mul_value_nat (iterations := position + 1) (constantValue := 5)
    indexResult indexResult
    (fun accumulator counter => scalar_mult (fiveAt _ _) (scalar_x _ _))
  have result := scalar_diff power (scalar_one _ _)
  apply scalarEval_congr (result := result)
  have indexCastEquality : 1 + (position : Int) = Int.ofNat (position + 1) := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have toNatIndex : (Int.ofNat (position + 1)).toNat = position + 1 := by
    simpa only [Int.ofNat_eq_natCast] using Int.toNat_natCast (position + 1)
  rw [indexCastEquality, toNatIndex]
  simp only [Int.ofNat_eq_natCast]
  push_cast
  ring

theorem A116156_candidate54_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A116156.spec candidate54 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate54, Mettapedia.Sequences.OEIS.Elementary49.A116156.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have initial := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_x _ _)
  have fiveAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o (P.addi P.tw P.tw)) accumulator counter 5 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _))
  have power := scalar_loop_mul_value_nat (iterations := position) (constantValue := 5)
    (scalar_x _ _) initial
    (fun accumulator counter => scalar_mult (fiveAt _ _) (scalar_x _ _))
  have result := scalar_mult power (scalar_x _ _)
  apply scalarEval_congr (result := result)
  simp only [Int.toNat_natCast]
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A212697_candidate67_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A212697.spec candidate67 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate67, Mettapedia.Sequences.OEIS.Elementary49.A212697.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  have initial := scalar_addi (scalar_one (Int.ofNat position) 0) (scalar_x _ _)
  have threeAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o P.tw) accumulator counter 3 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _) (scalar_two _ _)
  have power := scalar_loop_mul_value_nat (iterations := position) (constantValue := 3)
    (scalar_x _ _) initial
    (fun accumulator counter => scalar_mult (threeAt _ _) (scalar_x _ _))
  have result := scalar_mult power (scalar_two _ _)
  apply scalarEval_congr (result := result)
  have indexEquality : 1 + Int.ofNat position = Int.ofNat (position + 1) := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  simp only [← Int.ofNat_eq_natCast]
  rw [indexEquality]
  norm_num [Int.toNat_natCast]
  ring

theorem A155957_candidate59_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A155957.spec candidate59 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate59, Mettapedia.Sequences.OEIS.Elementary49.A155957.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have square := scalar_square (Int.ofNat position) 0
  have initialSecond := scalar_mult (scalar_two _ _) square
  have loopResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => first * second) (fun _ second => second)
    (scalar_x _ _) (scalar_one _ _) initialSecond
    (fun first second => scalar_mult (scalar_x _ _) (scalar_y _ _))
    (fun first second => scalar_y _ _)
  apply scalarEval_congr (result := loopResult)
  rw [iteratePair_mul_fixed]
  simp only [Int.toNat_natCast]
  simp only [Int.ofNat_eq_natCast]
  simp only [one_mul]

theorem A008790_candidate14_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A008790.spec candidate14 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate14, Mettapedia.Sequences.OEIS.Elementary49.A008790.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have fourthPower := scalar_square_loop_two (x := Int.ofNat position) (y := 0)
    (initial := P.X) (scalar_x _ _)
  have pairResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => first * second) (fun _ second => second)
    (scalar_x _ _) fourthPower (scalar_x _ _)
    (fun first second => scalar_mult (scalar_x _ _) (scalar_y _ _))
    (fun first second => scalar_y _ _)
  have divided := scalar_divi pairResult (scalar_one _ _) (by norm_num)
  apply scalarEval_congr (result := divided)
  rw [iteratePair_mul_fixed]
  simp only [Int.fdiv_one, Int.toNat_natCast, Int.ofNat_eq_natCast]
  rw [← pow_add]
  rw [add_comm]

theorem A085473_candidate48_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A085473.spec candidate48 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate48, Mettapedia.Sequences.OEIS.Elementary49.A085473.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have rawCount := scalar_addi (scalar_x (Int.ofNat position) 0) (scalar_x _ _)
  have countResult : ScalarEval (P.addi P.X P.X) (Int.ofNat position) 0
      (Int.ofNat (2 * position)) := by
    apply scalarEval_congr (result := rawCount)
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => accumulator + 3 * counter)
    countResult (scalar_one _ _)
    (fun accumulator counter => by
      have three := scalar_addi (scalar_one accumulator counter)
        (scalar_two accumulator counter)
      have product := scalar_mult three (scalar_y accumulator counter)
      have result := scalar_addi product (scalar_x accumulator counter)
      apply scalarEval_congr (result := result)
      ring)
  apply scalarEval_congr (result := loopResult)
  have recurrence :
      iterateWithCounter (fun accumulator counter => accumulator + 3 * counter)
          (2 * position) 1 1 = 1 + 3 * counterSum (2 * position) 1 := by
    simpa using iterateWithCounter_add_affine 3 0 (2 * position) 1 1
  rw [recurrence]
  have counterIdentity := two_mul_counterSum (2 * position) 1
  simp only [Int.ofNat_eq_natCast] at counterIdentity ⊢
  push_cast at counterIdentity ⊢
  nlinarith

theorem A236267_candidate68_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A236267.spec candidate68 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate68, Mettapedia.Sequences.OEIS.Elementary49.A236267.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have rawCount := scalar_addi (scalar_x (Int.ofNat position) 0) (scalar_x _ _)
  have countResult : ScalarEval (P.addi P.X P.X) (Int.ofNat position) 0
      (Int.ofNat (2 * position)) := by
    apply scalarEval_congr (result := rawCount)
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => accumulator + 4 * counter)
    countResult (scalar_one _ _)
    (fun accumulator counter => by
      have doubled := scalar_addi (scalar_y accumulator counter)
        (scalar_y accumulator counter)
      have quadrupled := scalar_mult (scalar_two accumulator counter) doubled
      have result := scalar_addi quadrupled (scalar_x accumulator counter)
      apply scalarEval_congr (result := result)
      ring)
  have result := scalar_diff loopResult (scalar_x _ _)
  apply scalarEval_congr (result := result)
  have recurrence :
      iterateWithCounter (fun accumulator counter => accumulator + 4 * counter)
          (2 * position) 1 1 = 1 + 4 * counterSum (2 * position) 1 := by
    simpa using iterateWithCounter_add_affine 4 0 (2 * position) 1 1
  rw [recurrence]
  have counterIdentity := two_mul_counterSum (2 * position) 1
  simp only [Int.ofNat_eq_natCast] at counterIdentity ⊢
  push_cast at counterIdentity ⊢
  nlinarith

theorem A132754_candidate55_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A132754.spec candidate55 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate55, Mettapedia.Sequences.OEIS.Elementary49.A132754.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => accumulator + counter + 10)
    (scalar_x _ _) (scalar_x _ _)
    (fun accumulator counter => by
      have inner := scalar_loop (x := accumulator) (y := counter)
        (fun value innerCounter => value + innerCounter)
        (scalar_addi (scalar_two _ _) (scalar_two _ _)) (scalar_x _ _)
        (fun value innerCounter => scalar_addi (scalar_x _ _) (scalar_y _ _))
      have inner' : ScalarEval (P.loop (P.addi P.X P.Y) (P.addi P.tw P.tw) P.X)
          accumulator counter (accumulator + 10) := by
        apply scalarEval_congr (result := inner)
        simp [iterateWithCounter]
        ring
      have added := scalar_addi inner' (scalar_y accumulator counter)
      apply scalarEval_congr (result := added)
      ring)
  apply scalarEval_congr (result := loopResult)
  have recurrence :
      iterateWithCounter (fun accumulator counter => accumulator + counter + 10)
          position (Int.ofNat position) 1 =
        Int.ofNat position + counterSum position 1 + 10 * Int.ofNat position := by
    simpa using iterateWithCounter_add_affine 1 10 position (Int.ofNat position) 1
  rw [recurrence]
  have counterIdentity := two_mul_counterSum position 1
  have numeratorIdentity :
      Int.ofNat position * (Int.ofNat position + 23) =
        (Int.ofNat position + counterSum position 1 + 10 * Int.ofNat position) * 2 := by
    nlinarith
  have divisionIdentity := Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : Int) ≠ 0)
    numeratorIdentity
  exact divisionIdentity.symm

theorem A140689_candidate56_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A140689.spec candidate56 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate56, Mettapedia.Sequences.OEIS.Elementary49.A140689.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => accumulator + 6 * counter + 16)
    (scalar_x _ _) (scalar_x _ _)
    (fun accumulator counter => by
      have four := scalar_addi (scalar_two accumulator counter)
        (scalar_two accumulator counter)
      have fourPlusCounter := scalar_addi four (scalar_y accumulator counter)
      have twiceFirst := scalar_mult (scalar_two accumulator counter) fourPlusCounter
      have plusCounter := scalar_addi twiceFirst (scalar_y accumulator counter)
      have twiceSecond := scalar_mult (scalar_two accumulator counter) plusCounter
      have result := scalar_addi twiceSecond (scalar_x accumulator counter)
      apply scalarEval_congr (result := result)
      ring)
  apply scalarEval_congr (result := loopResult)
  have recurrence :
      iterateWithCounter (fun accumulator counter => accumulator + 6 * counter + 16)
          position (Int.ofNat position) 1 =
        Int.ofNat position + 6 * counterSum position 1 + 16 * Int.ofNat position := by
    simpa using iterateWithCounter_add_affine 6 16 position (Int.ofNat position) 1
  rw [recurrence]
  have counterIdentity := two_mul_counterSum position 1
  simp only [Int.ofNat_eq_natCast] at counterIdentity ⊢
  nlinarith

theorem A209294_candidate66_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A209294.spec candidate66 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate66, Mettapedia.Sequences.OEIS.Elementary49.A209294.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  have sevenAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o (P.addi P.tw (P.addi P.tw P.tw))) accumulator counter 7 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _)
      (scalar_addi (scalar_two _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _)))
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => accumulator + 7 * counter)
    (scalar_x _ _) (scalar_two _ _)
    (fun accumulator counter => by
      have product := scalar_mult (sevenAt accumulator counter)
        (scalar_y accumulator counter)
      have result := scalar_addi product (scalar_x accumulator counter)
      apply scalarEval_congr (result := result)
      ring)
  apply scalarEval_congr (result := loopResult)
  have recurrence :
      iterateWithCounter (fun accumulator counter => accumulator + 7 * counter)
          position 2 1 = 2 + 7 * counterSum position 1 := by
    simpa using iterateWithCounter_add_affine 7 0 position 2 1
  rw [recurrence]
  have counterIdentity := two_mul_counterSum position 1
  have numeratorIdentity :
      7 * (1 + Int.ofNat position) ^ 2 - 7 * (1 + Int.ofNat position) + 4 =
        (2 + 7 * counterSum position 1) * 2 := by
    nlinarith
  have divisionIdentity := Int.ediv_eq_of_eq_mul_left (by norm_num : (2 : Int) ≠ 0)
    numeratorIdentity
  exact divisionIdentity.symm

theorem A008455_candidate13_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A008455.spec candidate13 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate13, Mettapedia.Sequences.OEIS.Elementary49.A008455.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have loopResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => first + second ^ 10) (fun _ second => second)
    (scalar_x _ _) (scalar_zero _ _) (scalar_x _ _)
    (fun first second => by
      have ninthPower := scalar_cube_loop_two (x := first) (y := second)
        (initial := P.Y) (scalar_y _ _)
      have tenthPower := scalar_mult ninthPower (scalar_y _ _)
      have tenthPower' : ScalarEval
          (P.mult (P.loop (P.mult (P.mult P.X P.X) P.X) P.tw P.Y) P.Y)
          first second (second ^ 10) := by
        apply scalarEval_congr (result := tenthPower)
        ring
      have added := scalar_addi tenthPower' (scalar_x first second)
      apply scalarEval_congr (result := added)
      ring)
    (fun first second => scalar_y _ _)
  apply scalarEval_congr (result := loopResult)
  rw [iteratePair_add_fixed]
  simp only [Int.ofNat_eq_natCast]
  ring

theorem A009975_candidate15_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A009975.spec candidate15 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate15, Mettapedia.Sequences.OEIS.Elementary49.A009975.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have outerResult := scalar_loop_mul_value_nat (x := Int.ofNat position) (y := 0)
    (iterations := position) (constantValue := 31)
    (scalar_x _ _) (scalar_one _ _)
    (fun accumulator counter => by
      have inner := scalar_loop (x := accumulator) (y := counter)
        (fun value innerCounter => (4 + innerCounter) * value)
        (scalar_two _ _) (scalar_x _ _)
        (fun value innerCounter => by
          have fourPlus := scalar_addi (scalar_two value innerCounter)
            (scalar_addi (scalar_two value innerCounter) (scalar_y value innerCounter))
          have fourPlus' : ScalarEval (P.addi P.tw (P.addi P.tw P.Y))
              value innerCounter (4 + innerCounter) := by
            apply scalarEval_congr (result := fourPlus)
            ring
          exact scalar_mult fourPlus' (scalar_x value innerCounter))
      have inner' : ScalarEval
          (P.loop (P.mult (P.addi P.tw (P.addi P.tw P.Y)) P.X) P.tw P.X)
          accumulator counter (30 * accumulator) := by
        apply scalarEval_congr (result := inner)
        simp [iterateWithCounter]
        ring
      have added := scalar_addi inner' (scalar_x accumulator counter)
      apply scalarEval_congr (result := added)
      ring)
  rw [Int.toNat_natCast]
  simpa only [mul_one, ← Int.ofNat_eq_natCast] using outerResult

theorem A009992_candidate16_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A009992.spec candidate16 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate16, Mettapedia.Sequences.OEIS.Elementary49.A009992.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have sevenAt : ∀ accumulator counter,
      ScalarEval (P.addi P.o (P.addi P.tw (P.addi P.tw P.tw))) accumulator counter 7 := by
    intro accumulator counter
    exact scalar_addi (scalar_one _ _)
      (scalar_addi (scalar_two _ _) (scalar_addi (scalar_two _ _) (scalar_two _ _)))
  have outerResult := scalar_loop_mul_value_nat (x := Int.ofNat position) (y := 0)
    (iterations := position) (constantValue := 48)
    (scalar_x _ _) (scalar_one _ _)
    (fun accumulator counter => by
      have inner := scalar_loop_mul_value_nat (iterations := 2) (constantValue := 7)
        (x := accumulator) (y := counter) (scalar_two _ _) (scalar_x _ _)
        (fun value innerCounter => scalar_mult (sevenAt _ _) (scalar_x _ _))
      have subtracted := scalar_diff inner (scalar_x accumulator counter)
      apply scalarEval_congr (result := subtracted)
      norm_num
      ring)
  rw [Int.toNat_natCast]
  simpa only [mul_one, ← Int.ofNat_eq_natCast] using outerResult

theorem A014992_candidate27_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A014992.spec candidate27 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate27, Mettapedia.Sequences.OEIS.Elementary49.A014992.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  have bodyResult : ∀ accumulator counter,
      ScalarEval
        (P.diff P.o
          (P.mult P.tw (P.addi (P.mult P.tw (P.addi P.X P.X)) P.X)))
        accumulator counter (1 - 10 * accumulator) := by
    intro accumulator counter
    have doubled := scalar_addi (scalar_x accumulator counter) (scalar_x accumulator counter)
    have fourTimes := scalar_mult (scalar_two accumulator counter) doubled
    have fiveTimes := scalar_addi fourTimes (scalar_x accumulator counter)
    have tenTimes := scalar_mult (scalar_two accumulator counter) fiveTimes
    have result := scalar_diff (scalar_one accumulator counter) tenTimes
    apply scalarEval_congr (result := result)
    ring
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator _ => 1 - 10 * accumulator)
    (scalar_x _ _) (scalar_one _ _) bodyResult
  apply scalarEval_congr (result := loopResult)
  have invariant := alternatingTenInvariant position 1 1
  have indexCastEquality : 1 + (position : Int) = Int.ofNat (position + 1) := by
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  rw [indexCastEquality]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]
  have numeratorIdentity :
      1 - (-10 : Int) ^ (position + 1) =
        iterateWithCounter (fun value _ => 1 - 10 * value) position 1 1 * 11 := by
    rw [pow_succ]
    nlinarith
  exact (Int.ediv_eq_of_eq_mul_left (by norm_num : (11 : Int) ≠ 0)
    numeratorIdentity).symm

theorem A047656_candidate39_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A047656.spec candidate39 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate39, Mettapedia.Sequences.OEIS.Elementary49.A047656.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have pairResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => first * second) (fun _ second => 3 * second)
    (scalar_x _ _) (scalar_one _ _) (scalar_one _ _)
    (fun first second => scalar_mult (scalar_x first second) (scalar_y first second))
    (fun first second => by
      have three := scalar_addi (scalar_one first second) (scalar_two first second)
      exact scalar_mult three (scalar_y first second))
  apply scalarEval_congr (result := pairResult)
  rw [pair047Closed]
  exact congrArg (fun exponent : Nat => (3 : Int) ^ exponent)
    (triangularExponentToNat position).symm

theorem A194268_candidate64_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A194268.spec candidate64 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate64, Mettapedia.Sequences.OEIS.Elementary49.A194268.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have firstBody : ∀ first second,
      ScalarEval
        (P.diff (P.mult P.tw (P.addi (P.mult P.tw (P.addi P.tw P.tw)) P.X)) P.Y)
        first second (16 + 2 * first - second) := by
    intro first second
    have four := scalar_addi (scalar_two first second) (scalar_two first second)
    have eight := scalar_mult (scalar_two first second) four
    have eightPlusFirst := scalar_addi eight (scalar_x first second)
    have sixteenPlusTwiceFirst := scalar_mult (scalar_two first second) eightPlusFirst
    have result := scalar_diff sixteenPlusTwiceFirst (scalar_y first second)
    apply scalarEval_congr (result := result)
    ring
  have pairResult := scalar_loop2 (x := Int.ofNat position) (y := 0)
    (fun first second => 16 + 2 * first - second) (fun first _ => first)
    (scalar_x _ _) (scalar_one _ _) (scalar_two _ _) firstBody
    (fun first second => scalar_x first second)
  apply scalarEval_congr (result := pairResult)
  rw [pair194Closed]
  simp only [Int.ofNat_eq_natCast]

theorem A196258_candidate65_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A196258.spec candidate65 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate65, Mettapedia.Sequences.OEIS.Elementary49.A196258.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have bodyResult : ∀ accumulator counter,
      ScalarEval
        (P.mult
          (P.addi (P.mult P.tw (P.addi (P.mult P.tw (P.addi P.X P.X)) P.X)) P.X)
          P.Y)
        accumulator counter (11 * accumulator * counter) := by
    intro accumulator counter
    have doubled := scalar_addi (scalar_x accumulator counter) (scalar_x accumulator counter)
    have fourTimes := scalar_mult (scalar_two accumulator counter) doubled
    have fiveTimes := scalar_addi fourTimes (scalar_x accumulator counter)
    have tenTimes := scalar_mult (scalar_two accumulator counter) fiveTimes
    have elevenTimes := scalar_addi tenTimes (scalar_x accumulator counter)
    have result := scalar_mult elevenTimes (scalar_y accumulator counter)
    apply scalarEval_congr (result := result)
    ring
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun accumulator counter => 11 * accumulator * counter)
    (scalar_x _ _) (scalar_one _ _) bodyResult
  apply scalarEval_congr (result := loopResult)
  rw [factorialIteration]
  simp only [Int.ofNat_eq_natCast, Int.toNat_natCast]

theorem A343028_candidate71_correct :
    CandidateRealizes Mettapedia.Sequences.OEIS.Elementary49.A343028.spec candidate71 := by
  apply realizes_of_scalar
  intro position indexInDomain
  dsimp [candidate71, Mettapedia.Sequences.OEIS.Elementary49.A343028.spec,
    Mettapedia.Sequences.OEIS.Elementary49.specOf,
    Mettapedia.Sequences.OEIS.SequenceSpec.index]
  simp only [zero_add]
  have countResult : ScalarEval (P.addi P.X P.X) (Int.ofNat position) 0
      (Int.ofNat (2 * position)) := by
    have doubled := scalar_addi (scalar_x (Int.ofNat position) 0)
      (scalar_x (Int.ofNat position) 0)
    apply scalarEval_congr (result := doubled)
    simp only [Int.ofNat_eq_natCast]
    push_cast
    ring
  have bodyResult : ∀ accumulator counter,
      ScalarEval (P.addi (P.divi P.Y (P.addi P.o P.tw)) P.Y)
        accumulator counter (Int.fdiv counter 3 + counter) := by
    intro accumulator counter
    have three := scalar_addi (scalar_one accumulator counter) (scalar_two accumulator counter)
    have quotient := scalar_divi (scalar_y accumulator counter) three (by norm_num)
    exact scalar_addi quotient (scalar_y accumulator counter)
  have loopResult := scalar_loop (x := Int.ofNat position) (y := 0)
    (fun _ counter => Int.fdiv counter 3 + counter)
    countResult (scalar_zero _ _) bodyResult
  have result := scalar_addi loopResult (scalar_x (Int.ofNat position) 0)
  apply scalarEval_congr (result := result)
  cases position with
  | zero => norm_num [iterateWithCounter]
  | succ position =>
      have countEquality : 2 * (position + 1) = (2 * position + 1) + 1 := by omega
      rw [countEquality, iterateWithCounter_replace]
      have counterEquality :
          1 + Int.ofNat (2 * position + 1) = 2 * Int.ofNat (position + 1) := by
        simp only [Int.ofNat_eq_natCast]
        push_cast
        ring
      rw [counterEquality]
      calc
        Int.fdiv (2 * Int.ofNat (position + 1)) 3 +
              2 * Int.ofNat (position + 1) + Int.ofNat (position + 1) =
            Int.fdiv (2 * Int.ofNat (position + 1)) 3 +
              3 * Int.ofNat (position + 1) := by ring
        _ = 11 * Int.ofNat (position + 1) / 3 :=
          elevenThirdIdentity (Int.ofNat (position + 1))

/-- One frozen synthesized program, its pinned OEIS formalization, and an extensional proof. -/
structure CertifiedAdjudication where
  formalization : Formalization
  candidate : FrozenCandidate
  correctness : CandidateRealizes formalization.spec candidate

/-- The first proof-carrying adjudication tranche, with source revision and entry hash attached. -/
def certifiedAdjudications : List CertifiedAdjudication :=
  [ { formalization := A070439.formalization, candidate := candidate45,
      correctness := A070439_candidate45_correct }
  , { formalization := A070478.formalization, candidate := candidate46,
      correctness := A070478_candidate46_correct }
  , { formalization := A070512.formalization, candidate := candidate47,
      correctness := A070512_candidate47_correct }
  , { formalization := A016779.formalization, candidate := candidate28,
      correctness := A016779_candidate28_correct }
  , { formalization := A016780.formalization, candidate := candidate29,
      correctness := A016780_candidate29_correct }
  , { formalization := A016814.formalization, candidate := candidate30,
      correctness := A016814_candidate30_correct }
  , { formalization := A010807.formalization, candidate := candidate17,
      correctness := A010807_candidate17_correct }
  , { formalization := A089081.formalization, candidate := candidate49,
      correctness := A089081_candidate49_correct }
  , { formalization := A244630.formalization, candidate := candidate69,
      correctness := A244630_candidate69_correct }
  , { formalization := A022521.formalization, candidate := candidate31,
      correctness := A022521_candidate31_correct }
  , { formalization := A036087.formalization, candidate := candidate38,
      correctness := A036087_candidate38_correct }
  , { formalization := A099762.formalization, candidate := candidate50,
      correctness := A099762_candidate50_correct }
  , { formalization := A002063.formalization, candidate := candidate00,
      correctness := A002063_candidate00_correct }
  , { formalization := A013710.formalization, candidate := candidate24,
      correctness := A013710_candidate24_correct }
  , { formalization := A024064.formalization, candidate := candidate32,
      correctness := A024064_candidate32_correct }
  , { formalization := A064751.formalization, candidate := candidate44,
      correctness := A064751_candidate44_correct }
  , { formalization := A116156.formalization, candidate := candidate54,
      correctness := A116156_candidate54_correct }
  , { formalization := A212697.formalization, candidate := candidate67,
      correctness := A212697_candidate67_correct }
  , { formalization := A155957.formalization, candidate := candidate59,
      correctness := A155957_candidate59_correct }
  , { formalization := A008790.formalization, candidate := candidate14,
      correctness := A008790_candidate14_correct }
  , { formalization := A085473.formalization, candidate := candidate48,
      correctness := A085473_candidate48_correct }
  , { formalization := A236267.formalization, candidate := candidate68,
      correctness := A236267_candidate68_correct }
  , { formalization := A132754.formalization, candidate := candidate55,
      correctness := A132754_candidate55_correct }
  , { formalization := A140689.formalization, candidate := candidate56,
      correctness := A140689_candidate56_correct }
  , { formalization := A209294.formalization, candidate := candidate66,
      correctness := A209294_candidate66_correct }
  , { formalization := A008455.formalization, candidate := candidate13,
      correctness := A008455_candidate13_correct }
  , { formalization := A009975.formalization, candidate := candidate15,
      correctness := A009975_candidate15_correct }
  , { formalization := A009992.formalization, candidate := candidate16,
      correctness := A009992_candidate16_correct }
  , { formalization := A014992.formalization, candidate := candidate27,
      correctness := A014992_candidate27_correct }
  , { formalization := A047656.formalization, candidate := candidate39,
      correctness := A047656_candidate39_correct }
  , { formalization := A194268.formalization, candidate := candidate64,
      correctness := A194268_candidate64_correct }
  , { formalization := A196258.formalization, candidate := candidate65,
      correctness := A196258_candidate65_correct }
  , { formalization := A343028.formalization, candidate := candidate71,
      correctness := A343028_candidate71_correct }
  ]

def adjudicatedOEISIds : List String :=
  certifiedAdjudications.map (fun adjudication => adjudication.formalization.source.oeisId)

theorem certifiedAdjudication_count : certifiedAdjudications.length = 33 := by
  decide

theorem certifiedAdjudication_ids_nodup : adjudicatedOEISIds.Nodup := by
  decide

#print axioms A070439_candidate45_correct
#print axioms A070478_candidate46_correct
#print axioms A070512_candidate47_correct
#print axioms A016779_candidate28_correct
#print axioms A016780_candidate29_correct
#print axioms A016814_candidate30_correct
#print axioms A010807_candidate17_correct
#print axioms A089081_candidate49_correct
#print axioms A244630_candidate69_correct
#print axioms A022521_candidate31_correct
#print axioms A036087_candidate38_correct
#print axioms A099762_candidate50_correct
#print axioms A002063_candidate00_correct
#print axioms A013710_candidate24_correct
#print axioms A024064_candidate32_correct
#print axioms A064751_candidate44_correct
#print axioms A116156_candidate54_correct
#print axioms A212697_candidate67_correct
#print axioms A155957_candidate59_correct
#print axioms A008790_candidate14_correct
#print axioms A085473_candidate48_correct
#print axioms A236267_candidate68_correct
#print axioms A132754_candidate55_correct
#print axioms A140689_candidate56_correct
#print axioms A209294_candidate66_correct
#print axioms A008455_candidate13_correct
#print axioms A009975_candidate15_correct
#print axioms A009992_candidate16_correct
#print axioms A014992_candidate27_correct
#print axioms A047656_candidate39_correct
#print axioms A194268_candidate64_correct
#print axioms A196258_candidate65_correct
#print axioms A343028_candidate71_correct
#print axioms certifiedAdjudications
#print axioms certifiedAdjudication_count
#print axioms certifiedAdjudication_ids_nodup

end Mettapedia.GSLT.LanguageDef.GauthierAdjudications33
