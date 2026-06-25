import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules

/-!
# BN Topology Regression Suite

Build canary: one OSLF evidence bridge per elementary Bayesian network topology.
If any upstream change (PLNBNCompilation, PLNWMOSLFBridge, PLNXiDerivedBNRules)
breaks the BN → WM → OSLF pipeline, this module will fail to build.

| Topology | Rule | Regression |
|----------|------|------------|
| Chain (A→B→C) | Deduction | `chain_oslfEvidence` |
| Fork (A←B→C) | Source / Induction | `fork_oslfEvidence` |
| Collider (A→C←B) | Sink / Abduction | `collider_oslfEvidence` |
| Collider (negative) | — | `collider_not_exact` |
-/

namespace Mettapedia.PLN.RuleFamilies.FirstOrder.BNTopologyRegression

/-! ## Chain: A→B→C (Deduction) -/

noncomputable abbrev chain_oslfEvidence :=
  @PLNXiDerivedBNRules.xi_deduction_semE_atom_of_chainBN

/-! ## Fork: A←B→C (Source / Induction) -/

noncomputable abbrev fork_oslfEvidence :=
  @PLNXiDerivedBNRules.xi_sourceRule_semE_atom_of_forkBN

/-! ## Collider: A→C←B (Sink / Abduction) -/

noncomputable abbrev collider_oslfEvidence :=
  @PLNXiDerivedBNRules.xi_sinkRule_semE_atom_of_colliderBN

/-! ## Collider Non-Exactness (Negative Result)

The PLN abduction formula is NOT exact for a general collider:
on an OR-gate collider with uniform priors, it gives 2/3 instead of 1/2. -/

noncomputable abbrev collider_not_exact :=
  @PLNXiDerivedBNRules.plnAbductionStrength_not_exact_collider

end Mettapedia.PLN.RuleFamilies.FirstOrder.BNTopologyRegression
