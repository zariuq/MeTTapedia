import Mathlib.Analysis.PSeries
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mettapedia.UniversalAI.SolomonoffPrior
import Mettapedia.UniversalAI.WeaknessPrior

/-!
# Zeta rank laws and program priors

Eray Ozkural, *Zeta Distribution and Transfer Learning Problem*
(arXiv:1806.08908, 2018), proposes the zeta law

`P(k) = 1 / (k ^ s * zeta(s))`, for positive integer ranks `k` and `s > 1`,

as an analytically tractable approximation to program probability.  He obtains a
program rank by binary arithmetization and uses `(phi(program) + 1) ^ (-(1+epsilon))`
in the induced approximation (Definition 1, equation 12).

This file separates three mathematical layers which should not be conflated:

* `RankLaw` is the normalized zeta distribution on positive integer ranks;
* `ProgramEnumeration` transports that distribution through a genuine bijective
  enumeration of a program type, preserving normalization;
* `binaryArithmetization` records Ozkural's source-level rank map, without falsely
  claiming that arbitrary bit strings form a bijective enumeration.  Leading-zero
  strings give an explicit negative control.

The final canary compares three genuinely different preferences on the same
hypotheses: Ozkural's rank law, Solomonoff's length weight `2 ^ (-|program|)`,
and Michael Timothy Bennett's normalized finite weakness prior.  Each selects a
different hypothesis.  This is a comparison theorem, not an identification of
the three research programmes.
-/

set_option autoImplicit false

namespace Mettapedia.UniversalAI.ZetaProgramPrior

open scoped BigOperators

/-! ## Normalized zeta law on positive integer ranks -/

/-- A zeta exponent together with the exact convergence condition `1 < s`. -/
structure Exponent where
  value : ℝ
  one_lt : 1 < value

namespace Exponent

/-- The unnormalized weight of zero-based rank `n`, corresponding to the
positive integer `n + 1` in the usual zeta distribution. -/
noncomputable def rawWeight (s : Exponent) (n : ℕ) : ℝ :=
  1 / |(n : ℝ) + 1| ^ s.value

theorem rawWeight_pos (s : Exponent) (n : ℕ) : 0 < s.rawWeight n := by
  unfold rawWeight
  positivity

theorem summable_rawWeight (s : Exponent) : Summable s.rawWeight := by
  change Summable (fun n : ℕ ↦ 1 / |(n : ℝ) + 1| ^ s.value)
  simpa only using
    (Real.summable_one_div_nat_add_rpow 1 s.value).2 s.one_lt

/-- The real zeta normalizer `sum_(n >= 0) (n+1)^(-s)`. -/
noncomputable def normalizer (s : Exponent) : ℝ :=
  ∑' n : ℕ, s.rawWeight n

theorem normalizer_pos (s : Exponent) : 0 < s.normalizer := by
  exact (summable_rawWeight s).tsum_pos
    (fun n ↦ (rawWeight_pos s n).le) 0 (rawWeight_pos s 0)

/-- Ozkural's normalized zeta probability of zero-based rank `n`. -/
noncomputable def prior (s : Exponent) (n : ℕ) : ℝ :=
  s.rawWeight n / s.normalizer

theorem prior_pos (s : Exponent) (n : ℕ) : 0 < s.prior n := by
  exact div_pos (rawWeight_pos s n) (normalizer_pos s)

theorem summable_prior (s : Exponent) : Summable s.prior := by
  exact (summable_rawWeight s).div_const s.normalizer

/-- The zeta rank prior is a genuine probability distribution. -/
theorem tsum_prior (s : Exponent) : ∑' n : ℕ, s.prior n = 1 := by
  rw [show (∑' n : ℕ, s.prior n) = (∑' n : ℕ, s.rawWeight n) / s.normalizer by
    simpa only [prior] using (tsum_div_const :
      (∑' n : ℕ, s.rawWeight n / s.normalizer) =
        (∑' n : ℕ, s.rawWeight n) / s.normalizer)]
  exact div_self (ne_of_gt (normalizer_pos s))

/-- The normalized real-valued zeta law packaged as mathlib's discrete
probability mass function. -/
noncomputable def pmf (s : Exponent) : PMF ℕ :=
  ⟨fun n ↦ ENNReal.ofReal (s.prior n), by
    rw [ENNReal.summable.hasSum_iff]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n ↦ (prior_pos s n).le) (summable_prior s), tsum_prior]
    simp⟩

@[simp]
theorem pmf_apply (s : Exponent) (n : ℕ) :
    s.pmf n = ENNReal.ofReal (s.prior n) := rfl

end Exponent

/-! ## Transport to program spaces -/

/-- A complete, duplicate-free enumeration of a program representation.
Transport through an equivalence is the condition under which the rank law is
already a normalized program prior, without a second normalization step. -/
structure ProgramEnumeration (Program : Type*) where
  rankEquiv : Program ≃ ℕ

namespace ProgramEnumeration

variable {Program : Type*}

/-- The normalized zeta program prior induced by a bijective enumeration. -/
noncomputable def prior (code : ProgramEnumeration Program)
    (s : Exponent) (program : Program) : ℝ :=
  s.prior (code.rankEquiv program)

/-- PMF-level transport of the zeta rank law to a program enumeration. -/
noncomputable def pmf (code : ProgramEnumeration Program)
    (s : Exponent) : PMF Program :=
  s.pmf.map code.rankEquiv.symm

theorem tsum_prior (code : ProgramEnumeration Program) (s : Exponent) :
    ∑' program : Program, code.prior s program = 1 := by
  rw [show (∑' program : Program, code.prior s program) =
      ∑' n : ℕ, s.prior n by
    simpa only [prior] using code.rankEquiv.tsum_eq (fun n : ℕ ↦ s.prior n)]
  exact s.tsum_prior

end ProgramEnumeration

/-! ## Ozkural's binary arithmetization and its representation boundary -/

abbrev BinString := Mettapedia.UniversalAI.SolomonoffPrior.BinString

/-- The value of one source bit in binary arithmetization. -/
def bitValue (bit : Bool) : ℕ := if bit then 1 else 0

/-- Binary arithmetization with the first bit most significant, matching equation
(3) of Ozkural (2018). -/
def binaryArithmetization : BinString → ℕ :=
  List.foldl (fun accumulator bit ↦ 2 * accumulator + bitValue bit) 0

@[simp]
theorem binaryArithmetization_nil : binaryArithmetization [] = 0 := rfl

@[simp]
theorem binaryArithmetization_cons_false_zero :
    binaryArithmetization [false] = 0 := by
  decide

@[simp]
theorem binaryArithmetization_two_false_zero :
    binaryArithmetization [false, false] = 0 := by
  decide

/-- Negative representation control: raw bit strings with leading zeros are not
a duplicate-free program enumeration.  Their zeta scores may still be useful,
but normalization cannot be transported through this map by bijectivity. -/
theorem binaryArithmetization_not_injective :
    ¬ Function.Injective binaryArithmetization := by
  intro injective
  have equalStrings : ([false] : BinString) = [false, false] :=
    injective (by simp)
  cases equalStrings

/-- Ozkural's `(phi(program)+1)` zeta score, before any representation-specific
normalization. -/
noncomputable def arithmetizationScore (s : Exponent) (program : BinString) : ℝ :=
  s.rawWeight (binaryArithmetization program)

/-! ## Three distinct prior orderings -/

namespace ComparisonCanary

open Mettapedia.Enactive.Finite.Canary
open Mettapedia.UniversalAI.WeaknessPrior

/-- A hypothesis equipped with the three pieces of information used by the
three compared programmes.  No field is derived from another. -/
structure Hypothesis where
  zetaRank : ℕ
  program : BinString
  statement : boolLayer.Statement

/-- A concrete convergent zeta law.  The choice `s = 2` makes the canary exact;
Ozkural's general proposal remains parameterized by every real `s > 1`. -/
def squareExponent : Exponent := ⟨2, by norm_num⟩

noncomputable def zetaScore (hypothesis : Hypothesis) : ℝ :=
  squareExponent.prior hypothesis.zetaRank

/-- Solomonoff's primitive fair-bit program weight from equation (1), kept
separate from output-level algorithmic probability, which sums all producing
programs. -/
noncomputable def solomonoffProgramWeight (hypothesis : Hypothesis) : ℝ :=
  (2 : ℝ) ^ (-(hypothesis.program.length : ℤ))

/-- Bennett's normalized finite weakness prior on the statement component. -/
noncomputable def bennettScore (hypothesis : Hypothesis) : ℚ :=
  Layer.normalizedWeaknessPrior boolLayer hypothesis.statement

/-- Chosen first by the zeta rank law. -/
def zetaPreferred : Hypothesis :=
  ⟨0, [true, false], trueStatement⟩

/-- Chosen first by the Solomonoff program-length weight. -/
def solomonoffPreferred : Hypothesis :=
  ⟨1, [], trueStatement⟩

/-- Chosen first by Bennett's semantic-freedom weight. -/
def bennettPreferred : Hypothesis :=
  ⟨2, [true], emptyStatement⟩

private theorem square_rawWeight_zero : squareExponent.rawWeight 0 = 1 := by
  norm_num [Exponent.rawWeight, squareExponent, Real.rpow_two]

private theorem square_rawWeight_one : squareExponent.rawWeight 1 = 1 / 4 := by
  norm_num [Exponent.rawWeight, squareExponent, Real.rpow_two]

private theorem square_rawWeight_two : squareExponent.rawWeight 2 = 1 / 9 := by
  norm_num [Exponent.rawWeight, squareExponent, Real.rpow_two]

theorem zeta_selects_zetaPreferred :
    zetaScore zetaPreferred > zetaScore solomonoffPreferred ∧
      zetaScore zetaPreferred > zetaScore bennettPreferred := by
  have normalizerPositive := Exponent.normalizer_pos squareExponent
  constructor <;>
    simp only [zetaScore, zetaPreferred, solomonoffPreferred, bennettPreferred,
      Exponent.prior]
  · rw [square_rawWeight_zero, square_rawWeight_one]
    exact div_lt_div_of_pos_right (by norm_num) normalizerPositive
  · rw [square_rawWeight_zero, square_rawWeight_two]
    exact div_lt_div_of_pos_right (by norm_num) normalizerPositive

theorem solomonoff_selects_solomonoffPreferred :
    solomonoffProgramWeight solomonoffPreferred >
        solomonoffProgramWeight zetaPreferred ∧
      solomonoffProgramWeight solomonoffPreferred >
        solomonoffProgramWeight bennettPreferred := by
  norm_num [solomonoffProgramWeight, solomonoffPreferred, zetaPreferred,
    bennettPreferred]

private theorem normalized_true_lt_empty :
    Layer.normalizedWeaknessPrior boolLayer trueStatement <
      Layer.normalizedWeaknessPrior boolLayer emptyStatement := by
  apply lt_of_not_ge
  rw [Layer.normalizedWeaknessPrior_le_iff]
  simp [trueStatement_weakness, emptyStatement_weakness]

theorem bennett_selects_bennettPreferred :
    bennettScore bennettPreferred > bennettScore zetaPreferred ∧
      bennettScore bennettPreferred > bennettScore solomonoffPreferred := by
  exact ⟨normalized_true_lt_empty, normalized_true_lt_empty⟩

/-- Explicit three-way disagreement: on one common hypothesis space, each
programme has a distinct maximizer among the three witnesses. -/
theorem three_prior_orderings_disagree :
    (zetaScore zetaPreferred > zetaScore solomonoffPreferred ∧
      zetaScore zetaPreferred > zetaScore bennettPreferred) ∧
    (solomonoffProgramWeight solomonoffPreferred >
        solomonoffProgramWeight zetaPreferred ∧
      solomonoffProgramWeight solomonoffPreferred >
        solomonoffProgramWeight bennettPreferred) ∧
    (bennettScore bennettPreferred > bennettScore zetaPreferred ∧
      bennettScore bennettPreferred > bennettScore solomonoffPreferred) :=
  ⟨zeta_selects_zetaPreferred, solomonoff_selects_solomonoffPreferred,
    bennett_selects_bennettPreferred⟩

end ComparisonCanary

#print axioms Exponent.tsum_prior
#print axioms ProgramEnumeration.tsum_prior
#print axioms binaryArithmetization_not_injective
#print axioms ComparisonCanary.three_prior_orderings_disagree

end Mettapedia.UniversalAI.ZetaProgramPrior
