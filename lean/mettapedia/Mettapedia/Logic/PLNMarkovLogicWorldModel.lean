import Mettapedia.Logic.PLNMarkovLogicFactorGraph

/-!
# MLN Factor Graphs as World Models

This module closes the semantic bridge:

- finite-support countable MLNs reduce to finite restrictions,
- finite restrictions compile to factor graphs,
- the compiled factor graphs induce singleton semantic WM states,
- therefore `queryStrength` matches the MLN query probability.
-/

namespace Mettapedia.Logic.PLNMarkovLogicWorldModel

open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNMarkovLogicAbstract
open Mettapedia.Logic.PLNMarkovLogicCountable
open Mettapedia.Logic.PLNMarkovLogicFiniteRestriction
open Mettapedia.Logic.PLNMarkovLogicFactorGraph

variable {World Query Feature : Type*} [Encodable World] [DecidableEq World]

omit [DecidableEq World] in
theorem wm_queryStrength_eq_restricted_queryProb
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    BinaryWorldModel.queryStrength
      ({compiledMassSemantics M hs} : MassState Query) q =
      (restrictedMassSemantics M hs).queryProb q := by
  rw [MassState.queryStrength_singleton_eq_queryProb]
  exact compiled_queryProb_eq_restricted_queryProb M hs q

omit [DecidableEq World] in
theorem wm_queryStrength_eq_full_queryProb_of_finite_support
    (M : CountableMLNSemantics World Query Feature)
    {support : Finset World} (hs : FiniteSupportWitness M support) (q : Query) :
    BinaryWorldModel.queryStrength
      ({compiledMassSemantics M hs} : MassState Query) q =
      (M.toMassSemantics.queryProb q) := by
  rw [wm_queryStrength_eq_restricted_queryProb M hs q]
  exact restricted_queryProb_eq_full_queryProb_of_finite_support M hs q

end Mettapedia.Logic.PLNMarkovLogicWorldModel
