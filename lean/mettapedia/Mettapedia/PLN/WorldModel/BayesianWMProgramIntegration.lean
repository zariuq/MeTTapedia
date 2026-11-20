import Mettapedia.PLN.WorldModel.BayesianObservationLedgerControls
import Mettapedia.PLN.WorldModel.ProgramObservationDenotation
import Mettapedia.PLN.WorldModel.WeightedSourceControls
import Mettapedia.PLN.WorldModel.WeightedSourceAdequacy
import Mettapedia.PLN.Bridges.GSLT.BayesianInferenceControllerControls
import Mettapedia.PLN.Bridges.GSLT.BayesianProofSearchControls
import Mettapedia.PLN.WorldModel.BayesianLearningDynamicsControls
import Mettapedia.PLN.WorldModel.ProbabilisticWitnessCompositionControls
import Mettapedia.PLN.WorldModel.ProbabilisticWitnessJointEvidence

/-!
# Bayesian world programs, controlled inference, and compositional queries

This entry point joins measurable observation updates and replay-aware program
execution, a finite weighted source/BDD realization, Bayesian proof-search
guidance, temporal filtering and learning, and local factor/witness composition.

The interfaces retain distinct obligations: likelihood semantics and event
identity; explicit finite random-choice valuation; checking proof certificates;
fair scheduling; support and evidence margins; and factor/separator coherence.
The finite source specialization is exhaustive and may be exponential. It is
not a weighted interpreter for every reflective source-language construct.

`scripts/audit_bayesian_wm_programs.lean` checks the transitive axioms of the
owned declarations in this collection, including the negative controls.
-/
