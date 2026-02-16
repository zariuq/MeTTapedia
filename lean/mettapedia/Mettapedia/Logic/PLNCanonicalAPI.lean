import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNXiRuleRegistry
import Mettapedia.Logic.PLNXiCarrierScreening
import Mettapedia.Logic.PLNXiDerivedBNRules

/-!
# PLN Canonical API (Lean)

Small facade module that exposes the recommended, semantically grounded entry points:

- Correct strength formulas from `PLNDerivation`
- Categorical naming (`SourceRule` / `SinkRule`) as first-class aliases
- NB bridge theorem location: `PLNBayesNetInference`
- WM-calculus rewrite/query-equivalence types from `PLNWorldModelCalculus`
- OSLF bridge: `XiPLN`, `wmEvidenceAtomSemQ`, derivation soundness (`PLNWMOSLFBridge`)
- **Derived BN rules**: fully proved deduction (chain) + source rule (fork) from local Markov + d-separation (`PLNXiDerivedBNRules`)
- Schema-level templates in `Schema` namespace (for building new derived rules)

## Canonical vs Schema

**Canonical** (top-level): Rules whose side conditions are derived from concrete
model semantics. No free soundness hypothesis arguments.

**Schema** (under `Schema` namespace): Rule templates parameterized by abstract
side conditions. Use these to build new derived rules for other BN structures,
but do not cite them as "proved inference rules."

This file is intentionally lightweight: it is an index with stable names, not a new semantics layer.
-/

namespace Mettapedia.Logic.PLNCanonical

open Mettapedia.Logic

/-! ## Canonical rule-strength names -/

noncomputable abbrev deductionStrength := PLN.plnDeductionStrength
noncomputable abbrev inductionStrength := PLN.plnInductionStrength
noncomputable abbrev abductionStrength := PLN.plnAbductionStrength

noncomputable abbrev sourceRuleStrength := PLN.plnSourceRuleStrength
noncomputable abbrev sinkRuleStrength := PLN.plnSinkRuleStrength

theorem sourceRule_eq_induction (s_BA s_BC s_A s_B s_C : ℝ) :
    sourceRuleStrength s_BA s_BC s_A s_B s_C =
      inductionStrength s_BA s_BC s_A s_B s_C := rfl

theorem sinkRule_eq_abduction (s_AB s_CB s_A s_B s_C : ℝ) :
    sinkRuleStrength s_AB s_CB s_A s_B s_C =
      abductionStrength s_AB s_CB s_A s_B s_C := rfl

/-! ## WM-calculus canonical type aliases -/

abbrev WMQueryEq {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMQueryEq (State := State) (Query := Query)

abbrev WMRewriteRule (State Query : Type*)
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWorldModel.WMRewriteRule State Query

/-! ## OSLF Bridge canonical aliases -/

abbrev XiPLN {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWMOSLFBridge.XiPLN (State := State) (Query := Query)

noncomputable abbrev wmEvidenceAtomSemQ {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State Query] :=
  PLNWMOSLFBridge.wmEvidenceAtomSemQ (State := State) (Query := Query)

/-! ## Derived BN Rules (canonical — no free side-condition hypotheses)

Fully derived PLN inference rules for BN structures. All side conditions
are derived from local Markov + d-separation — no free `hSO` arguments.

Import `Mettapedia.Logic.PLNXiDerivedBNRules` and use directly:

### Deduction: Chain BN (A→B→C) — §1

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ChainBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_deduction_rewrite_of_chainBN` — WMRewriteRule (NO free hSO)
- `xi_deduction_admissible_of_chainBN` — query judgment from derivable WM state
- `xi_deduction_semE_atom_of_chainBN` — OSLF evidence = derived evidence
- `xi_deduction_threshold_of_chainBN` — threshold Prop from strength bound
- `xi_deduction_strength_eq_of_chainBN` — linkCond strength = link strength

**Tier A→B Composition** (end-to-end queryStrength → plnDeductionStrength)
- `xi_deduction_queryStrength_eq_plnDeduction_of_chainBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))`
  Consumes: singleton bridge + VEBridge + Tier B.

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `toStrength_evidenceOfProb` — `Evidence.toStrength ∘ evidenceOfProb = id` (for p ≤ 1)
- `xi_deduction_plnStrength_exact_of_chainBN` — P(C|A) = plnDeductionStrength(...)

**Tier C**: Beta-Bernoulli (computable from evidence counts)
- `plnStrength_lt_one` — `s_B < 1` when `nB_neg ≠ 0` (denominator safety)
- `plnDeductionStrength_denom_pos` — `0 < 1 - s_B` (denominator positivity)
- `plnDeductionStrength_of_plnStrength` — unfolds plnStrength in deduction formula
- `plnDeductionStrength_of_plnStrength_full` — all four arguments unfolded
- `evidence_hplus_is_conjugate` — Beta conjugate update for evidence aggregation

**Guardrail**: Beta is a modeling choice, not forced by exchangeability.
See `EvidenceBeta.not_beta_from_exchangeability_example`.

### Source Rule (Induction): Fork BN (A←B→C) — §4

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ForkBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sourceRule_rewrite_of_forkBN` — WMRewriteRule (NO free hSO)
- `xi_sourceRule_admissible_of_forkBN` — query judgment from derivable WM state
- `xi_sourceRule_semE_atom_of_forkBN` — OSLF evidence = derived evidence
- `xi_sourceRule_threshold_of_forkBN` — threshold Prop from strength bound
- `xi_sourceRule_strength_eq_of_forkBN` — linkCond strength = link strength

The fork BN has edges B→A and B→C. The source rule derives link A→C from
links B→A and B→C via the same conditional independence A ⊥ C | B. The
screening-off WMQueryEq has the same form as the chain BN deduction case;
the structural difference is the BN graph topology.

Tier A→B composition for the fork BN (connecting to `plnInductionStrength`)
requires a fork-specific FastRules decomposition, which is not yet in scope.

### Sink Rule (Abduction): Not Yet Derived

The collider BN side condition needs investigation (see §5 in PLNXiDerivedBNRules).

These require BN instances (Fintype, DecidableEq, etc.) which are
provided by `open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples`. -/

/-! ## Schema namespace

Rule templates parameterized by abstract side conditions. These are building
blocks for constructing new derived rules from other BN structures (fork,
collider, etc.), NOT standalone inference rules.

To build a derived rule from a schema template:
1. Prove the side condition from your model semantics
2. Instantiate the schema with the proved side condition
3. Add admissibility + OSLF bridge theorems
4. Export the derived rule (not the schema) as canonical -/

namespace Schema

/-! ### Screening-off side condition templates -/

abbrev DeductionScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.DeductionScreeningOff (Atom := Atom) (State := State)

abbrev SourceRuleScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.SourceRuleScreeningOff (Atom := Atom) (State := State)

abbrev SinkRuleScreeningOff {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiRuleRegistry.SinkRuleScreeningOff (Atom := Atom) (State := State)

/-! ### Carrier family template -/

abbrev CarrierFamily {Atom State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModel State (PLNWorldModel.PLNQuery Atom)] :=
  PLNXiCarrierScreening.CarrierFamily (Atom := Atom) (State := State)

end Schema

end Mettapedia.Logic.PLNCanonical
