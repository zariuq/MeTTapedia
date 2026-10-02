import Mettapedia.Computability.KolmogorovComplexity.Prefix
import Mathlib.Topology.Instances.ENNReal.Lemmas

set_option autoImplicit false

namespace KolmogorovComplexity

open scoped ENNReal BigOperators Classical

/-- Length weight of a binary program, in the extended nonnegative reals. -/
noncomputable def prefixProgramWeight (program : BinString) : ENNReal :=
  ENNReal.ofReal ((2 : Real) ^ (-(program.length : Int)))

/-- Weight of a set of programs. A prefix-free set has mass at most one. -/
noncomputable def prefixProgramMass (domain : Set BinString) : ENNReal :=
  ∑' program, if program ∈ domain then prefixProgramWeight program else 0

theorem prefixProgramMass_le_one (domain : Set BinString) (free : PrefixFree domain) :
    prefixProgramMass domain ≤ 1 := by
  unfold prefixProgramMass
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun finite => ?_
  let selected := finite.filter fun program => program ∈ domain
  have selectedFree : PrefixFree (selected : Set BinString) := by
    intro first firstMember second secondMember different
    exact free first (Finset.mem_filter.mp firstMember).2
      second (Finset.mem_filter.mp secondMember).2 different
  have bound : (∑ program ∈ selected, (2 : Real) ^ (-(program.length : Int))) ≤ 1 :=
    kraft_inequality selected selectedFree
  have nonnegative : ∀ program ∈ selected, 0 ≤ (2 : Real) ^ (-(program.length : Int)) :=
    fun _ _ => zpow_nonneg (by norm_num) _
  calc
    (∑ program ∈ finite, if program ∈ domain then prefixProgramWeight program else 0)
        = ∑ program ∈ selected, prefixProgramWeight program := by
          rw [Finset.sum_filter]
    _ = ENNReal.ofReal (∑ program ∈ selected, (2 : Real) ^ (-(program.length : Int))) :=
        (ENNReal.ofReal_sum_of_nonneg nonnegative).symm
    _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal bound
    _ = 1 := by simp

/-- Push program length weight forward along a partial output map. This is
a discrete output mass; it does not describe probabilities of future prefixes. -/
noncomputable def prefixOutputMass {Output : Type*}
    (compute : BinString → Option Output) (output : Output) : ENNReal :=
  ∑' program, if compute program = some output then prefixProgramWeight program else 0

/-- Each terminating program contributes to exactly one output. -/
theorem prefixOutputMass_total {Output : Type*} (compute : BinString → Option Output) :
    (∑' output, prefixOutputMass compute output) =
      prefixProgramMass {program | compute program ≠ none} := by
  unfold prefixOutputMass prefixProgramMass
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro program
  cases computed : compute program with
  | none => simp [computed]
  | some result =>
      simp only [computed, Option.some.injEq, Set.mem_ofPred_eq, ne_eq,
        reduceCtorEq, not_false_eq_true, ite_true]
      rw [tsum_eq_single result]
      · exact if_pos rfl
      · intro other different
        exact if_neg different.symm

theorem prefixOutputMass_total_le_one {Output : Type*}
    (compute : BinString → Option Output)
    (free : PrefixFree {program | compute program ≠ none}) :
    (∑' output, prefixOutputMass compute output) ≤ 1 := by
  rw [prefixOutputMass_total]
  exact prefixProgramMass_le_one _ free

end KolmogorovComplexity
