import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mettapedia.Logic.PLNMarkovLogicAbstract

/-!
# Countable MLN Semantics

This module specializes the abstract MLN layer to countable worlds.

The semantics remains world-weight based:
- query mass is a countable sum over satisfying worlds,
- total mass is the countable sum of all world weights.

We also provide the standard log-weight wrapper

`w ↦ exp(w)`

as an ENNReal clause potential. This keeps the core semantics positive and
factor-graph-friendly while preserving the classical MLN reading.
-/

namespace Mettapedia.Logic.PLNMarkovLogicCountable

open scoped ENNReal
open Mettapedia.Logic.PLNMarkovLogicAbstract

/-- Countable MLN semantics over an `Encodable` world space. -/
structure CountableMLNSemantics (World Query Feature : Type*) [Encodable World]
    extends AbstractMLNSemantics World Query Feature where
  totalMass_ne_top : (∑' w : World, worldWeight w) ≠ ⊤

namespace CountableMLNSemantics

variable {World Query Feature : Type*} [Encodable World]
variable (M : CountableMLNSemantics World Query Feature)

/-- Query mass: countable sum of the weights of satisfying worlds. -/
noncomputable def queryMass (q : Query) : ENNReal :=
  by
    classical
    exact ∑' w : World, if M.queryHolds q w then M.worldWeight w else 0

/-- Total mass of the countable semantics. -/
noncomputable def totalMass : ENNReal :=
  ∑' w : World, M.worldWeight w

theorem queryMass_le_totalMass (q : Query) :
    CountableMLNSemantics.queryMass M q ≤ CountableMLNSemantics.totalMass M := by
  classical
  unfold queryMass totalMass
  refine ENNReal.tsum_le_tsum ?_
  intro w
  by_cases hq : M.queryHolds q w
  · simp [hq]
  · simp [hq]

/-- Package the countable semantics as a mass semantics object. -/
noncomputable def toMassSemantics : MassSemantics Query where
  queryMass := CountableMLNSemantics.queryMass M
  totalMass := CountableMLNSemantics.totalMass M
  queryMass_le_total := M.queryMass_le_totalMass
  totalMass_ne_top := M.totalMass_ne_top

theorem queryProb_def (q : Query) :
    (M.toMassSemantics.queryProb q) =
      if CountableMLNSemantics.totalMass M = 0 then 0 else
        CountableMLNSemantics.queryMass M q / CountableMLNSemantics.totalMass M := by
  rfl

end CountableMLNSemantics

/-- Classical MLN clause potential from a real log-weight. -/
noncomputable def logWeightPotential (w : ℝ) (holds : Prop) [Decidable holds] : ENNReal :=
  if holds then ENNReal.ofReal (Real.exp w) else 1

theorem logWeightPotential_ne_top (w : ℝ) (holds : Prop) [Decidable holds] :
    logWeightPotential w holds ≠ ⊤ := by
  unfold logWeightPotential
  split_ifs with h
  · exact ENNReal.ofReal_ne_top
  · simp

theorem logWeightPotential_pos (w : ℝ) (holds : Prop) [Decidable holds] :
    0 < logWeightPotential w holds := by
  unfold logWeightPotential
  split_ifs with h
  · exact ENNReal.ofReal_pos.mpr (Real.exp_pos _)
  · simp

end Mettapedia.Logic.PLNMarkovLogicCountable
