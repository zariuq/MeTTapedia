import Mettapedia.Logic.WMMarkov
import Mettapedia.Logic.WMMarkovCanonical
import Mettapedia.Logic.MarkovPathXi
import Mettapedia.Logic.MarkovTransitionXi
import Mettapedia.Logic.MarkovTransitionXiExamples
import Mettapedia.Logic.MarkovPredictiveChaining

/-!
# Narrow Public Interface for Markov WM / Xi / Predictive Chaining

This file is a small import-and-alias facade for the current Markov WM/PLN
integration work:

* row-conditioned WM sufficient statistics,
* direct Xi transition atoms for single-step semantics,
* direct Xi path atoms for multi-step predictive semantics,
* concrete examples and consumer theorems,
* honest multi-step predictive chaining.
-/

namespace Mettapedia.Logic.MarkovXi

abbrev TransitionState := Mettapedia.Logic.WMMarkovCanonical.MarkovTransitionWMState
abbrev TransitionQuery := Mettapedia.Logic.WMMarkovCanonical.MarkovTransitionQuery

abbrev transitionAtomName := Mettapedia.Logic.MarkovTransitionXi.markovTransitionAtomName
abbrev transitionAtomPattern := @Mettapedia.Logic.MarkovTransitionXi.markovTransitionAtomPattern
abbrev transitionQueryOfAtom := @Mettapedia.Logic.MarkovTransitionXi.markovTransitionQueryOfAtom
abbrev transitionXiPLN := @Mettapedia.Logic.MarkovTransitionXi.markovTransitionXiPLN

abbrev transitionAtomQueryJudgment :=
  @Mettapedia.Logic.MarkovTransitionXiExamples.markovTransitionAtom_queryJudgment
abbrev transitionAtomQueryJudgment_of_summary :=
  @Mettapedia.Logic.MarkovTransitionXiExamples.markovTransitionAtom_queryJudgment_of_summary

abbrev PathQuery := Mettapedia.Logic.MarkovPathXi.MarkovTransitionPathQuery
abbrev PathState := Mettapedia.Logic.MarkovPathXi.MarkovTransitionPathState

abbrev pathAtomName := Mettapedia.Logic.MarkovPathXi.markovTransitionPathAtomName
abbrev pathAtomPattern := @Mettapedia.Logic.MarkovPathXi.markovTransitionPathAtomPattern
abbrev pathQueryOfAtom := @Mettapedia.Logic.MarkovPathXi.markovTransitionPathQueryOfAtom
abbrev pathXiPLN := @Mettapedia.Logic.MarkovPathXi.markovTransitionPathXiPLN
noncomputable abbrev pathStateOfWM := @Mettapedia.Logic.MarkovPathXi.markovTransitionPathStateOfWM
abbrev pathAtomSemE_eq_chainEvidence :=
  @Mettapedia.Logic.MarkovPathXi.markovTransitionPathAtom_semE_eq_chainEvidence
abbrev pathAtomQueryStrength_eq_chain :=
  @Mettapedia.Logic.MarkovPathXi.markovTransitionPathAtom_queryStrength_eq_chain
abbrev pathAtomQueryStrength_transitionMultiset_eq_of_summary :=
  @Mettapedia.Logic.MarkovPathXi.markovTransitionPathAtom_queryStrength_transitionMultiset_eq_of_summary
abbrev bit001Pattern := Mettapedia.Logic.MarkovPathXi.bit001Pattern
abbrev bit011Pattern := Mettapedia.Logic.MarkovPathXi.bit011Pattern
abbrev bit001Path_queryStrength_transitionMultiset_eq_of_summary :=
  @Mettapedia.Logic.MarkovPathXi.bit001_queryStrength_transitionMultiset_eq_of_summary
abbrev bit011Path_queryStrength_transitionMultiset_eq_of_summary :=
  @Mettapedia.Logic.MarkovPathXi.bit011_queryStrength_transitionMultiset_eq_of_summary

noncomputable abbrev predictiveChain :=
  @Mettapedia.Logic.MarkovPredictiveChaining.markovWMPosteriorChain
abbrev predictiveChain_eq_prefixAux :=
  @Mettapedia.Logic.MarkovPredictiveChaining.markovWMPosteriorChain_eq_prefixAux
noncomputable abbrev twoStepArrivalMass :=
  @Mettapedia.Logic.MarkovPredictiveChaining.markovTwoStepArrivalMass
abbrev twoStepArrivalMass_eq_posteriorMean_sum :=
  @Mettapedia.Logic.MarkovPredictiveChaining.markovTwoStepArrivalMass_eq_posteriorMean_sum

end Mettapedia.Logic.MarkovXi
