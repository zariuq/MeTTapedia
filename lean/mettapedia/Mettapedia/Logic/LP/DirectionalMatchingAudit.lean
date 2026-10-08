import Mettapedia.Logic.LP.MatchingControls
import Mettapedia.Logic.LP.RigidUnificationControls
import Mettapedia.Logic.LP.VariantMatchingControls
import Mettapedia.Logic.LP.ClauseSubsumptionControls
import Mettapedia.Logic.LP.ClauseSubsumptionEnumeration
import Mettapedia.Logic.LP.DirectionalMatchingScope
import Mettapedia.Logic.LP.DirectionalMatchingSearch

/-!
# Dependency audit for directional matching

These are laws about the executable first-order models. The native graph
implementation has separate correspondence and ownership tests; importing this
module does not prove a C translation or a garbage collector correct.
-/

#print axioms Mettapedia.Logic.LP.matchTerm_sound
#print axioms Mettapedia.Logic.LP.matchAtom_sound
#print axioms Mettapedia.Logic.LP.matchTerm_complete
#print axioms Mettapedia.Logic.LP.matchAtom_complete
#print axioms Mettapedia.Logic.LP.RigidUnification.solve_sound
#print axioms Mettapedia.Logic.LP.RigidUnification.solve_complete
#print axioms Mettapedia.Logic.LP.RigidUnification.solve_mgu
#print axioms Mettapedia.Logic.LP.RigidUnification.sequential_joint_success
#print axioms Mettapedia.Logic.LP.RigidUnification.sequential_joint_observations
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_sound
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_complete
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_none_iff
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matching_images_unique
#print axioms Mettapedia.Logic.LP.DirectionalMatching.converse_matches
#print axioms Mettapedia.Logic.LP.DirectionalMatching.rule_match_rewrites
#print axioms Mettapedia.Logic.LP.DirectionalMatching.permitted_matching_rename_iff
#print axioms Mettapedia.Logic.LP.DirectionalMatching.matchMany_rename_images
#print axioms Mettapedia.Logic.LP.DirectionalMatching.join_eq_exhaustive
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_exact
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_residual_exact
#print axioms Mettapedia.Logic.LP.DirectionalMatching.run_add
#print axioms Mettapedia.Logic.LP.VariantMatching.solve_sound
#print axioms Mettapedia.Logic.LP.VariantMatching.solve_complete
#print axioms Mettapedia.Logic.LP.VariantMatching.solve_none_iff
#print axioms Mettapedia.Logic.LP.VariantMatching.solve_round_trip
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.check_sound
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.check_complete
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.covers_entails
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.searchAll_sound
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.searchAll_alignment_complete
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.searchAll_set_complete
#print axioms Mettapedia.Logic.LP.ClauseSubsumption.searchAll_set_empty_iff
