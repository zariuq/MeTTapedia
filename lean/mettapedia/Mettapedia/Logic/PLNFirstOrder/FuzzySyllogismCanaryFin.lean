import Mettapedia.Logic.PLNFirstOrder.FuzzySyllogismCanary
import Mettapedia.Logic.PLNFirstOrder.FuzzyQuantifierWorkedExamplesFin

/-!
# Finite Fuzzy Syllogism Canary Suite

Finite/counting QFM and Chapter-11 syllogism canaries.
-/

namespace Mettapedia.Logic.PLNFirstOrder

abbrev qfm_syllogism_intervalFin := @qfm_syllogism_interval
abbrev qfm_syllogism_most_mostFin := @qfm_syllogism_most_most
abbrev qfm_syllogism_few_mostFin := @qfm_syllogism_few_most
noncomputable abbrev qfm_selector_bundle_most_mostFin := @qfm_selector_bundle_most_most
noncomputable abbrev qfm_selector_bundle_few_mostFin := @qfm_selector_bundle_few_most
abbrev zadeh_syllogism_most_mostFin := @zadeh_syllogism_most_most
abbrev zadeh_syllogism_few_mostFin := @zadeh_syllogism_few_most
abbrev qfmMin_syllogism_most_mostFin := @qfmMin_syllogism_most_most
abbrev qfmMin_syllogism_few_mostFin := @qfmMin_syllogism_few_most
abbrev qfmLukasiewicz_syllogism_most_mostFin := @qfmLukasiewicz_syllogism_most_most
abbrev qfmLukasiewicz_syllogism_few_mostFin := @qfmLukasiewicz_syllogism_few_most
abbrev qfmProbSum_syllogism_most_mostFin := @qfmProbSum_syllogism_most_most
abbrev qfmProbSum_syllogism_few_mostFin := @qfmProbSum_syllogism_few_most
abbrev qfm_instance_comparison_most_mostFin := @qfm_instance_comparison_most_most
abbrev qfm_instance_comparison_few_mostFin := @qfm_instance_comparison_few_most
abbrev canary_qfm_monotonicity_mostFin := @canary_qfm_monotonicity_most
abbrev canary_qfm_forall_monotonicity_mostFin := @canary_qfm_forall_monotonicity_most
abbrev canary_qfm_conservativity_same_nearOne_signatureFin :=
  @canary_qfm_conservativity_same_nearOne_signature
abbrev canary_zadeh_most_most_fixtureFin := @canary_zadeh_most_most_fixture
abbrev canary_zadeh_few_most_fixtureFin := @canary_zadeh_few_most_fixture

end Mettapedia.Logic.PLNFirstOrder
