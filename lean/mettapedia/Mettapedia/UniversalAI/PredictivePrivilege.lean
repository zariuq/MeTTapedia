import Mettapedia.Computability.KolmogorovComplexity.ReferenceMachine
import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.UniversalAI.UniversalMachineBoundary
import Mettapedia.UniversalAI.UniversalPrediction.Convergence
import Mettapedia.UniversalAI.UniversalPrediction.HutterEnumerationTheorem
import Mettapedia.UniversalAI.BadUniversalPriors
import Mathlib.Computability.RE

/-!
# What simplicity and the true distribution privilege

Two candidates for a privileged view of the world are examined here: the
simplest description, relative to a reference machine, and the true
distribution `μ`, if it were known.

## Simplicity privileges a reference machine only up to a constant

The invariance theorem ranges over effective reference machines, which exist.
A reference machine is an effective conditional prefix machine that uniformly
simulates every effective one (`IsReferenceMachine`); the trimmed indexed host
is a concrete instance (`isReferenceMachine_trimmedIndexedHost`). Simulation
of every set-theoretic prefix machine is impossible
(`UniversalMachineBoundary.no_unrestrictedSimulation`).

* **A graded translation.**  `Translates U V n` says that `U` runs every program
  of `V` behind a compiler prefix of length at most `n`.  Translations compose
  with the grades added (`Translates.trans`), every machine translates itself at
  grade zero (`Translates.refl`), and a translation bounds complexity by its
  grade (`Translates.complexity_le`).  Any two reference machines translate into
  each other (`IsReferenceMachine.translates`), so their complexities are within
  a constant (`IsReferenceMachine.invariance`).
* **No reference machine is privileged with constant zero.**  For every
  reference machine `U` there is another, `favour U x`, which gives a one-bit
  program to a string `x` that `U` cannot produce with a program of length at
  most one (`favour`, `unfavoured_not_produced`), and which is again a reference
  machine (`favour_isReferenceMachine`).  `U` does not translate it at grade
  zero and has strictly larger complexity at `x` (`not_privileged`), so no
  reference machine translates every other at grade zero
  (`not_privilegedWithConstantZero`).

## Predictions converge, programs do not

When the mixture dominates the true measure, the total squared prediction
error is bounded (`UniversalPrediction.Convergence.convergence_bound`), so the
predictions converge to those of `μ`.  The hypotheses behind them do not single
out a program:

* every reference machine has two distinct programs with one output
  (`programs_not_singled_out`), so every view of programs computed from their
  outputs, the measures they induce included, has a non-trivial fibre
  (`induced_not_singled_out`);
* two hypotheses with one measure keep the ratio of their prior weights in the
  posterior after every history (`posteriorWeight_ratio_of_eq`): no data
  separate them.

**Control: at finite time the prior is not innocent.**  Built from one
environment, the dogmatic mixtures of `BadUniversalPriors` for two different
actions prefer different actions at horizon one (`dogmatic_priors_disagree`,
from `BadUniversalPriors.dogmaticMixture_prefers_target_horizon1`).

## Knowing μ fixes the predictive view, not the generator

With the evaluation "the conditional law of the next bit under `μ`", the
privileged view of histories in the sense of
`Mettapedia.GSLT.Logic.PrivilegedView` is the causal state (`causalState`): the
coarsest view, stable under extending the history, that keeps the prediction
(`factors_causalState`).  It is defined from `μ` alone.

The generator is not fixed by `μ`.  A finite hidden-state generator
(`HiddenGenerator`) emits a bit and moves at each step; its law is a prefix
measure (`HiddenGenerator.toPrefixMeasure`).  A fair coin with one state
(`fairCoin`) and a two-state generator whose state is the next bit and is
redrawn fairly after each emission (`hiddenBit`) have the same law, the uniform
measure (`fairCoin_law`, `hiddenBit_law`), so the map from generators to laws
has a non-trivial fibre (`generator_not_fixed`).  Both have one causal state
(`causalState_uniform`), while the hidden states of `hiddenBit` predict
differently from each other (`hiddenBit_states_predict_differently`): the hidden
state is a finer view than prediction needs, and `μ` does not fix it.

This is underdetermination as a theorem at a small instance: realist about the
converging predictions, agnostic about generators, plural about presentations.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.UniversalAI.PredictivePrivilege

open KolmogorovComplexity
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.PrivilegedView
open scoped ENNReal

/-! ## No reference machine is privileged with constant zero -/

/-- `U` with one more program: the one-bit program `[false]` outputs `x`, and
`true :: program` runs `program` on `U`. -/
def favour (U : ConditionalPrefixFreeMachine) (x : BinString) : ConditionalPrefixFreeMachine where
  compute := fun program condition =>
    match program with
    | [false] => some x
    | true :: rest => U.compute rest condition
    | _ => none
  prefix_free := by
    intro condition program extension isPrefix distinct halts
    obtain ⟨suffix, rfl⟩ := isPrefix
    have nonempty : suffix ≠ [] := fun empty => distinct (by simp [empty])
    match program, halts with
    | [false], _ =>
        obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
        rfl
    | true :: rest, halts =>
        exact U.prefix_free condition rest (rest ++ suffix) ⟨suffix, rfl⟩
          (fun same => nonempty (List.append_right_eq_self.mp same.symm)) halts

theorem favour_compute_true (U : ConditionalPrefixFreeMachine) (x program condition : BinString) :
    (favour U x).compute (true :: program) condition = U.compute program condition :=
  rfl

/-- The machine `favour U x` translates `U` at grade one. -/
def favourSimulates (U : ConditionalPrefixFreeMachine) (x : BinString) :
    UniformlySimulates (favour U x) U where
  compilerPrefix := [true]
  compute_eq := fun _ _ => rfl

theorem favour_effective {U : ConditionalPrefixFreeMachine} (effective : Effective U)
    (x : BinString) : Effective (favour U x) := by
  unfold Effective at effective ⊢
  have isFavoured : Computable fun input : BinString × BinString => decide (input.1 = [false]) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const [false])).decide.to_comp
  have isTrue : Computable fun input : BinString × BinString =>
      decide (input.1.head? = some true) :=
    (Primrec.eq.comp (Primrec.list_head?.comp Primrec.fst)
      (Primrec.const (some true))).decide.to_comp
  have runRest : Partrec fun input : BinString × BinString =>
      Part.ofOption (U.compute input.1.tail input.2) :=
    effective.comp (Primrec.list_tail.to_comp.comp Computable.fst) Computable.snd
  refine (Partrec.cond isFavoured (Partrec.const' (Part.some x))
    (Partrec.cond isTrue runRest Partrec.none)).of_eq ?_
  rintro ⟨program, condition⟩
  match program with
  | [] => rfl
  | [false] => rfl
  | false :: _ :: _ => rfl
  | true :: rest => rfl

/-- **`favour U x` is a reference machine** when `U` is. -/
theorem favour_isReferenceMachine {U : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) (x : BinString) : IsReferenceMachine (favour U x) :=
  ⟨favour_effective reference.1 x, fun M effective => by
    obtain ⟨simulation⟩ := reference.2 M effective
    exact ⟨(favourSimulates U x).trans simulation⟩⟩

/-- A string that no program of length at most one produces on `U` without
condition. -/
def unfavoured (U : ConditionalPrefixFreeMachine) : BinString :=
  UniversalMachineBoundary.freshBoundedOutput (conditionalSlice U []) 1

theorem unfavoured_not_produced (U : ConditionalPrefixFreeMachine) {program : BinString}
    (short : program.length ≤ 1) : ¬ IsProgram U program [] (unfavoured U) := fun produces =>
  UniversalMachineBoundary.freshBoundedOutput_not_produced (conditionalSlice U []) 1 program
    short produces

/-- A reference machine is **privileged with constant zero** when it translates
every reference machine at grade zero. -/
def PrivilegedWithConstantZero (U : ConditionalPrefixFreeMachine) : Prop :=
  ∀ V, IsReferenceMachine V → Translates U V 0

/-- **No reference machine is privileged with constant zero**: another reference
machine gives some string a strictly shorter description. -/
theorem not_privileged {U : ConditionalPrefixFreeMachine} (reference : IsReferenceMachine U) :
    ∃ V, IsReferenceMachine V ∧ ¬ Translates U V 0 ∧
      ∃ x, HasProgram U [] x ∧ Kc[V](x | []) < Kc[U](x | []) := by
  let x := unfavoured U
  refine ⟨favour U x, favour_isReferenceMachine reference x, ?_, x, ?_⟩
  · rintro ⟨simulation, bound⟩
    have empty : simulation.compilerPrefix = [] := List.eq_nil_of_length_eq_zero (by omega)
    have runs := simulation.compute_eq [false] []
    rw [empty, List.nil_append] at runs
    exact unfavoured_not_produced U (program := [false]) le_rfl runs
  · have favoured : IsProgram (favour U x) [false] [] x := rfl
    obtain ⟨simulation⟩ := reference.2 (favour U x) (favour_isReferenceMachine reference x).1
    have hasProgram : HasProgram U [] x := simulation.hasProgram ⟨_, favoured⟩
    refine ⟨hasProgram, ?_⟩
    obtain ⟨shortest, produces, length⟩ := exists_program_of_conditionalComplexity U [] x hasProgram
    have long : 1 < shortest.length := by
      by_contra notLong
      exact unfavoured_not_produced U (by omega) produces
    have short := conditionalComplexity_le_program_length (favour U x) [] x [false] favoured
    simp only [List.length_singleton] at short
    omega

/-- **No reference machine is privileged with constant zero.** -/
theorem not_privilegedWithConstantZero {U : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) : ¬ PrivilegedWithConstantZero U := by
  intro privileged
  obtain ⟨_, referenceV, notTranslates, _⟩ := not_privileged reference
  exact notTranslates (privileged _ referenceV)

/-! ## Predictions converge, programs do not -/

/-- Two one-bit programs with one output. -/
def twinMachine : ConditionalPrefixFreeMachine where
  compute := fun program _ => if program.length = 1 then some [] else none
  prefix_free := by
    intro condition program extension isPrefix distinct halts
    have programLength : program.length = 1 := by
      by_contra notOne
      exact halts (by simp [notOne])
    obtain ⟨suffix, rfl⟩ := isPrefix
    have nonempty : suffix ≠ [] := fun empty => distinct (by simp [empty])
    have positive : 0 < suffix.length := List.length_pos_iff.mpr nonempty
    have notOne : (program ++ suffix).length ≠ 1 := by
      rw [List.length_append]
      omega
    show (if (program ++ suffix).length = 1 then some [] else none) = none
    rw [if_neg notOne]

theorem twinMachine_effective : Effective twinMachine := by
  have computable : Primrec fun input : BinString × BinString =>
      if input.1.length = 1 then (some [] : Option BinString) else none :=
    Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp Primrec.fst) (Primrec.const 1))
      (Primrec.const _) (Primrec.const _)
  exact (Computable.ofOption computable.to_comp).of_eq fun _ => rfl

/-- **Every reference machine has two distinct programs with one output.** -/
theorem programs_not_singled_out {U : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) :
    ∃ fiber : NonTrivialFiber (fun program => U.compute program []) id,
      U.compute fiber.left [] ≠ none := by
  obtain ⟨simulation⟩ := reference.2 twinMachine twinMachine_effective
  have runsFalse := simulation.compute_eq [false] []
  have runsTrue := simulation.compute_eq [true] []
  refine ⟨⟨simulation.compilerPrefix ++ [false], simulation.compilerPrefix ++ [true],
    runsFalse.trans runsTrue.symm, fun same => ?_⟩, ?_⟩
  · have := List.append_cancel_left same
    simp at this
  · change U.compute (simulation.compilerPrefix ++ [false]) [] ≠ none
    rw [runsFalse]
    simp [twinMachine]

/-- **Every view of programs computed from their outputs**, such as the measure
a program induces, **has a non-trivial fibre.** -/
theorem induced_not_singled_out {U : ConditionalPrefixFreeMachine}
    (reference : IsReferenceMachine U) {Induced : Sort*} (induced : Option BinString → Induced) :
    Nonempty (NonTrivialFiber (fun program => induced (U.compute program [])) id) := by
  obtain ⟨fiber, _⟩ := programs_not_singled_out reference
  exact ⟨NonTrivialFiber.coarsen (fine := fun program => U.compute program [])
    (coarsen := induced) (fun _ => rfl) fiber⟩

open UniversalPrediction in
/-- **Two hypotheses with one measure keep the ratio of their prior weights in
the posterior after every history.** -/
theorem posteriorWeight_ratio_of_eq {ι : Type*} (ν : ι → Semimeasure) (w : ι → ℝ≥0∞)
    {i j : ι} (same : ν i = ν j) (history : List Bool) :
    posteriorWeight ν w history i * w j = posteriorWeight ν w history j * w i := by
  unfold posteriorWeight
  split_ifs
  · simp
  · rw [same, div_eq_mul_inv, div_eq_mul_inv]
    ring

/-! ## Control: at finite time the prior is not innocent -/

open BayesianAgents BadUniversalPriors in
theorem optimalQValue_heaven (γ : DiscountFactor) (action : Action) :
    optimalQValue heavenEnvironment γ [] action 1 = 1 := by
  rw [optimalQValue_horizon1_eq]
  cases action <;>
    simp [heavenEnvironment, History.wellFormed, Percept.rewardBit, ENNReal.toReal_inv] <;>
    norm_num

open BayesianAgents BadUniversalPriors in
/-- **The dogmatic mixtures for two different actions, built from one
environment, prefer different actions at horizon one.** -/
theorem dogmatic_priors_disagree (γ : DiscountFactor) {first second : Action}
    (different : first ≠ second) :
    optimalQValue (dogmaticMixture heavenEnvironment first (1 / 2) (by norm_num) (by norm_num))
        γ [] second 1 <
      optimalQValue (dogmaticMixture heavenEnvironment first (1 / 2) (by norm_num) (by norm_num))
        γ [] first 1 ∧
    optimalQValue (dogmaticMixture heavenEnvironment second (1 / 2) (by norm_num) (by norm_num))
        γ [] first 1 <
      optimalQValue (dogmaticMixture heavenEnvironment second (1 / 2) (by norm_num) (by norm_num))
        γ [] second 1 := by
  have large : ∀ action, optimalQValue heavenEnvironment γ [] action 1 > 1 / 2 := fun action => by
    rw [optimalQValue_heaven]
    norm_num
  exact ⟨dogmaticMixture_prefers_target_horizon1 _ γ first _ _ _ (large first) second
      (Ne.symm different),
    dogmaticMixture_prefers_target_horizon1 _ γ second _ _ _ (large second) first different⟩

/-! ## Knowing μ: the predictive view and the generator -/

section KnowingMu

open UniversalPrediction

/-- The conditional law of the next bit under `μ` after a history. -/
def prediction (μ : PrefixMeasure) (history : List Bool) : Bool → ℝ≥0∞ :=
  Distances.condENN μ history

/-- The **causal state** of a history: the predictions after each continuation,
the word behaviour of histories for the evaluation `prediction μ`. -/
def causalState (μ : PrefixMeasure) : List Bool → List Bool → Bool → ℝ≥0∞ :=
  wordBehaviour extend (prediction μ)

/-- **The causal state is the privileged view for prediction**: it factors
through every view of histories, stable under extending the history, that
keeps the prediction. -/
theorem factors_causalState (μ : PrefixMeasure) {V : Sort*} {view : List Bool → V}
    (stable : StableUnder extend view) (keeps : Factors view (prediction μ)) :
    Factors view (causalState μ) :=
  factors_wordBehaviour stable keeps

/-- A finite hidden-state generator of bits: from each state it emits a bit and
moves to a next state, with probability `move state bit next`. -/
structure HiddenGenerator where
  State : Type
  [fintype : Fintype State]
  start : State → ℝ≥0∞
  move : State → Bool → State → ℝ≥0∞
  start_sum : ∑ state, start state = 1
  move_sum : ∀ state, ∑ bit, ∑ next, move state bit next = 1

attribute [instance] HiddenGenerator.fintype

namespace HiddenGenerator

variable (generator : HiddenGenerator)

/-- The probability of emitting a word from a state. -/
def emitFrom : generator.State → List Bool → ℝ≥0∞
  | _, [] => 1
  | state, bit :: word => ∑ next, generator.move state bit next * emitFrom next word

theorem emitFrom_append (state : generator.State) (word : List Bool) :
    generator.emitFrom state (word ++ [false]) + generator.emitFrom state (word ++ [true]) =
      generator.emitFrom state word := by
  induction word generalizing state with
  | nil =>
      have total := generator.move_sum state
      simp only [Fintype.sum_bool] at total
      simpa [emitFrom, add_comm] using total
  | cons bit word inductionHypothesis =>
      simp only [List.cons_append, emitFrom]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun next _ => ?_
      rw [← mul_add, inductionHypothesis]

/-- The law of the emitted bits. -/
def law (word : List Bool) : ℝ≥0∞ :=
  ∑ state, generator.start state * generator.emitFrom state word

/-- **The law of a hidden-state generator is a prefix measure.** -/
def toPrefixMeasure : PrefixMeasure where
  toFun := generator.law
  root_eq_one' := by simp [law, emitFrom, generator.start_sum]
  additive' := fun word => by
    simp only [law]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun state _ => ?_
    rw [← mul_add, emitFrom_append]

/-- The prediction of the next bit from a hidden state. -/
def nextBitFrom (state : generator.State) (bit : Bool) : ℝ≥0∞ :=
  ∑ next, generator.move state bit next

end HiddenGenerator

theorem prefixMeasure_ext {μ ν : PrefixMeasure} (same : ∀ word, μ word = ν word) : μ = ν := by
  obtain ⟨toFunμ, _, _⟩ := μ
  obtain ⟨toFunν, _, _⟩ := ν
  obtain rfl : toFunμ = toFunν := funext same
  rfl

theorem half_add_half : (2⁻¹ : ℝ≥0∞) + 2⁻¹ = 1 :=
  ENNReal.inv_two_add_inv_two

/-- A fair coin with one state. -/
def fairCoin : HiddenGenerator where
  State := Unit
  start := fun _ => 1
  move := fun _ _ _ => 2⁻¹
  start_sum := by simp
  move_sum := fun _ => by
    show ∑ _bit : Bool, ∑ _next : Unit, (2⁻¹ : ℝ≥0∞) = 1
    rw [Fintype.sum_bool, Fintype.sum_unique, half_add_half]

/-- Two states; the state is the next bit, and after each emission the next
state is drawn fairly. -/
def hiddenBit : HiddenGenerator where
  State := Bool
  start := fun _ => 2⁻¹
  move := fun state bit _ => if bit = state then 2⁻¹ else 0
  start_sum := by
    show ∑ _state : Bool, (2⁻¹ : ℝ≥0∞) = 1
    rw [Fintype.sum_bool, half_add_half]
  move_sum := fun state => by
    show ∑ bit : Bool, ∑ _next : Bool, (if bit = state then (2⁻¹ : ℝ≥0∞) else 0) = 1
    cases state <;> simp only [Fintype.sum_bool] <;> simp [half_add_half]

theorem fairCoin_emitFrom (word : List Bool) : fairCoin.emitFrom () word = 2⁻¹ ^ word.length := by
  induction word with
  | nil => simp [HiddenGenerator.emitFrom]
  | cons bit word inductionHypothesis =>
      show ∑ next : Unit, (2⁻¹ : ℝ≥0∞) * fairCoin.emitFrom next word = 2⁻¹ ^ (word.length + 1)
      rw [Fintype.sum_unique]
      change (2⁻¹ : ℝ≥0∞) * fairCoin.emitFrom () word = _
      rw [inductionHypothesis, pow_succ, mul_comm]

/-- **The fair coin has the uniform law.** -/
theorem fairCoin_law :
    fairCoin.toPrefixMeasure = HutterEnumerationTheorem.uniformPrefixMeasure :=
  prefixMeasure_ext fun word => by
    show ∑ state : Unit, (1 : ℝ≥0∞) * fairCoin.emitFrom state word = 2⁻¹ ^ word.length
    rw [Fintype.sum_unique, one_mul]
    exact fairCoin_emitFrom word

theorem hiddenBit_sum_emitFrom (word : List Bool) :
    ∑ state : Bool, hiddenBit.emitFrom state word = 2 * 2⁻¹ ^ word.length := by
  induction word with
  | nil =>
      show ∑ _state : Bool, (1 : ℝ≥0∞) = 2 * 2⁻¹ ^ 0
      rw [Fintype.sum_bool, pow_zero, mul_one, one_add_one_eq_two]
  | cons bit word inductionHypothesis =>
      show (∑ state : Bool, ∑ next : Bool,
        (if bit = state then (2⁻¹ : ℝ≥0∞) else 0) * hiddenBit.emitFrom next word) =
          2 * 2⁻¹ ^ (word.length + 1)
      have collapse : ∀ next : Bool, (∑ state : Bool,
          (if bit = state then (2⁻¹ : ℝ≥0∞) else 0) * hiddenBit.emitFrom next word) =
            2⁻¹ * hiddenBit.emitFrom next word := fun next => by
        cases bit <;> simp
      rw [Finset.sum_comm]
      simp only [collapse]
      rw [← Finset.mul_sum, inductionHypothesis, pow_succ]
      ring

/-- **The two-state generator has the uniform law as well.** -/
theorem hiddenBit_law :
    hiddenBit.toPrefixMeasure = HutterEnumerationTheorem.uniformPrefixMeasure :=
  prefixMeasure_ext fun word => by
    show ∑ state : Bool, (2⁻¹ : ℝ≥0∞) * hiddenBit.emitFrom state word = 2⁻¹ ^ word.length
    rw [← Finset.mul_sum, hiddenBit_sum_emitFrom, ← mul_assoc,
      ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]

/-- **The generator is not fixed by the law**: the fair coin and the two-state
generator have one law and different numbers of hidden states. -/
def generator_not_fixed :
    NonTrivialFiber HiddenGenerator.toPrefixMeasure fun generator => Fintype.card generator.State where
  left := fairCoin
  right := hiddenBit
  sameShadow := fairCoin_law.trans hiddenBit_law.symm
  differentValue := by
    change Fintype.card Unit ≠ Fintype.card Bool
    simp

theorem prediction_uniform (history : List Bool) (bit : Bool) :
    prediction HutterEnumerationTheorem.uniformPrefixMeasure history bit = 2⁻¹ := by
  change HutterEnumerationTheorem.uniformPrefixMeasure.toFun (history ++ [bit]) /
      HutterEnumerationTheorem.uniformPrefixMeasure.toFun history = 2⁻¹
  change (2⁻¹ : ℝ≥0∞) ^ (history ++ [bit]).length / 2⁻¹ ^ history.length = 2⁻¹
  rw [List.length_append, List.length_singleton, pow_succ, mul_comm,
    ENNReal.mul_div_cancel_right (pow_ne_zero _ (by simp)) (ENNReal.pow_ne_top (by simp))]

/-- **The uniform law has one causal state**: every history has the causal
state of the empty history. -/
theorem causalState_uniform (history : List Bool) :
    causalState HutterEnumerationTheorem.uniformPrefixMeasure history =
      causalState HutterEnumerationTheorem.uniformPrefixMeasure [] :=
  funext fun word => funext fun bit => by
    simp only [causalState, wordBehaviour, prediction_uniform]

/-- **The hidden states of the two-state generator predict differently**: the
state `false` emits `false` surely, the state `true` emits `true` surely. -/
theorem hiddenBit_states_predict_differently :
    hiddenBit.nextBitFrom false false = 1 ∧ hiddenBit.nextBitFrom true false = 0 ∧
      ∀ history, prediction HutterEnumerationTheorem.uniformPrefixMeasure history false = 2⁻¹ := by
  refine ⟨?_, ?_, fun history => prediction_uniform history false⟩
  · show ∑ _next : Bool, (if false = false then (2⁻¹ : ℝ≥0∞) else 0) = 1
    rw [Fintype.sum_bool, if_pos rfl, half_add_half]
  · show ∑ _next : Bool, (if false = true then (2⁻¹ : ℝ≥0∞) else 0) = 0
    simp

end KnowingMu

/-! ## Axiom audit -/

#print axioms isReferenceMachine_trimmedIndexedHost
#print axioms Translates.trans
#print axioms Translates.complexity_le
#print axioms IsReferenceMachine.invariance
#print axioms favour_isReferenceMachine
#print axioms not_privileged
#print axioms not_privilegedWithConstantZero
#print axioms programs_not_singled_out
#print axioms induced_not_singled_out
#print axioms posteriorWeight_ratio_of_eq
#print axioms dogmatic_priors_disagree
#print axioms factors_causalState
#print axioms fairCoin_law
#print axioms hiddenBit_law
#print axioms generator_not_fixed
#print axioms causalState_uniform
#print axioms hiddenBit_states_predict_differently

end Mettapedia.UniversalAI.PredictivePrivilege
