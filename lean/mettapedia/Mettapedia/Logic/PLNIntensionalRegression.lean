import Mettapedia.Logic.PLNIntensionalWorldModel
import Mettapedia.Logic.IntensionalInheritanceSolomonoffBridge
import Mettapedia.Logic.PLNCanonicalAPI
import Mettapedia.Logic.PLNIntensionalAssocPatClosure
import Mettapedia.Logic.PLNIntensionalCanary

/-!
# Chapter 12 Regression Target

Single-entry build target for Chapter-12 intensional inheritance:

- WM typed inheritance channels
- Solomonoff log-ratio bridge
- canonical one-call API composition
- executable positive/negative canaries

Build command:

```bash
cd /home/zar/claude/lean-projects/mettapedia
ulimit -Sv 6291456 && export LAKE_JOBS=3 && nice -n 19 \
  lake build Mettapedia.Logic.PLNIntensionalRegression
```
-/

namespace Mettapedia.Logic.PLNIntensionalRegression

/-! ## Chapter 12 Surface -/

abbrev ch12_inheritanceSort :=
  PLNIntensionalWorldModel.InheritanceSort

abbrev ch12_inheritanceQueryFamily :=
  PLNIntensionalWorldModel.InheritanceQueryFamily

abbrev ch12_inheritanceQueryBuilder :=
  PLNIntensionalWorldModel.InheritanceQueryBuilder

abbrev ch12_extensional_evidence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence

abbrev ch12_assoc_evidence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence

abbrev ch12_pat_evidence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalPATEvidence

abbrev ch12_mixed_evidence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedEvidence

abbrev ch12_assocPatSemanticModel :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocPatSemanticModel

abbrev ch12_assoc_score_correspondence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence

abbrev ch12_pat_score_correspondence :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.PATScoreCorrespondence

abbrev ch12_assoc_score_lift :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.assocEvidence_eq_scoreToEvidence_of_assocScore_eq

abbrev ch12_pat_score_lift :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.patEvidence_eq_scoreToEvidence_of_patScore_eq

abbrev ch12_goertzel_formula :=
  @Mettapedia.Logic.IntensionalInheritance.goertzel_formula

abbrev ch12_singleton_reduction :=
  @Mettapedia.Logic.IntensionalInheritance.singleton_reduction

abbrev ch12_mixed_assoc_rewrite_apply :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc_apply

abbrev ch12_mixed_assocPat_rewrite_apply :=
  @PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc_pat_apply

abbrev ch12_solomonoff_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromConditional_eq_log2_ratio

abbrev ch12_solomonoff_xiSemimeasure_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromXiSemimeasure_eq_log2_ratio

abbrev ch12_solomonoff_xiGeom_log2_ratio :=
  @Mettapedia.Logic.IntensionalInheritance.intensionalFromXiGeom_eq_log2_ratio

abbrev ch12_assocPat_mixed_policy :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.mixedPolicy_assocPat

abbrev ch12_pat_channel_nontrivial :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.pat_channel_nontrivial

abbrev ch12_mixed_not_assoc_only :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.mixed_not_assoc_only

abbrev ch12_binary_mixed_policy_collapse_no_go :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.binary_mixed_policy_collapse_no_go

abbrev ch12_assocPat_bayesNormal_lower :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.end_to_end_assocPat_bayesNormal_lower

abbrev ch12_assocPat_bayesExact_lower :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.end_to_end_assocPat_bayesExact_lower

abbrev ch12_assocPat_walley_lower :=
  Mettapedia.Logic.PLNIntensionalAssocPatConcrete.end_to_end_assocPat_walley_lower

abbrev ch12_mixed_projection_non_equivalent :=
  PLNIntensionalCanary.canary_ch12_mixed_projection_non_equivalent

abbrev ch12_mixed_extensional_projection :=
  PLNIntensionalCanary.canary_ch12_mixed_extensional_projection

abbrev ch12_mixed_assoc_projection :=
  PLNIntensionalCanary.canary_ch12_mixed_assoc_projection

abbrev ch12_solomonoff_threshold_bayesNormal :=
  @Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_bayesNormal_of_solomonoff_semantic_linked_strong

abbrev ch12_solomonoff_threshold_bayesExact :=
  @Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_bayesExact_of_solomonoff_semantic_linked_strong

abbrev ch12_solomonoff_threshold_walley :=
  @Mettapedia.Logic.PLNCanonical.intensional_mixed_assoc_threshold_atom_walley_of_solomonoff_semantic_linked_strong

end Mettapedia.Logic.PLNIntensionalRegression
