import Mettapedia.Logic.PLNDerivation
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNXiRuleRegistry
import Mettapedia.Logic.PLNXiCarrierScreening
import Mettapedia.Logic.PLNXiDerivedBNRules
import Mettapedia.Logic.PLNColliderSingletonBridge
import Mettapedia.Logic.PLNEndToEnd

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

**Tier A→B Composition** (end-to-end queryStrength → plnInductionStrength)
- `xi_source_queryStrength_eq_plnInduction_of_forkBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnInductionStrength(P(A|B), P(C|B), P(A), P(B), P(C))`
  Uses `bayesInversion(P(A|B), P(A), P(B)) = P(B|A)` + fork screening-off + PLN deduction formula.
  Consumes: `forkBN_plnDeductionStrength_exact` (PLNBayesNetFastRules).

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `forkBN_plnDeductionStrength_exact` — P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
  from CondIndepVertices (local Markov at C). ~30 lines vs ~900 for chain case.
- `forkBN_pos_screeningOff` / `forkBN_neg_screeningOff` — screening-off from CondIndepVertices
  via `condIndep_eventEq_mul_cond` + `real_ratio_of_ennreal_mul_eq`

### Sink Rule (Abduction): Collider BN (A→C←B) — §5

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ColliderBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sinkRule_rewrite_of_colliderBN` — WMRewriteRule (NO free hSO)
- `xi_sinkRule_admissible_of_colliderBN` — query judgment from derivable WM state
- `xi_sinkRule_semE_atom_of_colliderBN` — OSLF evidence = derived evidence
- `xi_sinkRule_threshold_of_colliderBN` — threshold Prop from strength bound
- `xi_sinkRule_strength_eq_of_colliderBN` — link strength = prop strength

The collider BN has edges A→C and B→C. The sink rule derives link A→B from
links A→C and B→C. The side condition is marginal independence A ⊥ B | ∅,
which holds because A and B have no active path when C is not conditioned on.

Variable mapping: (A_rule, B_rule, C_rule) = (Three.A, Three.C, Three.B).
Sink center = Three.C. The WMQueryEq rewrites `link ⟨A,valA⟩ ⟨B,valB⟩`
to `prop ⟨B,valB⟩` (marginal independence: P(B|A) = P(B)).

These require BN instances (Fintype, DecidableEq, etc.) which are
provided by `open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples`.

**Tier A→B Composition: NOT EXACT (approximation)**
- `plnAbductionStrength_not_exact_collider` — counterexample showing PLN abduction
  formula gives 2/3 ≠ 1/2 for an OR-gate collider. The PLN abduction formula
  requires B ⊥ A | C, but conditioning on the collider C *opens* the explaining-away
  path, making A and B dependent given C.

### Generic tools (§6)

- `real_ratio_of_ennreal_mul_eq` — convert ENNReal multiplicative screening-off
  `a * d = b * c` to `.real` ratio form `a/b = c/d` (PLNBayesNetFastRules)
- `eventEq_false_eq_compl_true_of_bool` — Bool complement bridge for event sets (EventSets) -/

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

/-! ## Exactness Matrix

Summary of formula-level exactness across BN topologies:

| Rule | BN Topology | Tier A (WM/OSLF) | Tier A→B (formula) | Notes |
|------|-------------|-------------------|---------------------|-------|
| Deduction | Chain A→B→C | exact | exact | `plnDeductionStrength` via total probability + C ⊥ A given B |
| Source/Induction | Fork A←B→C | exact | exact | `plnInductionStrength` = Bayes inversion + deduction; C ⊥ A given B holds |
| Sink/Abduction | Collider A→C←B | exact (marginal) | **NOT exact** | Structural: P(B given A) = P(B); formula: explaining-away violates B ⊥ A given C |

### Key theorems

- Chain exact: `chainBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (measure): `forkBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (queryStrength): `xi_source_queryStrength_eq_plnInduction_of_forkBN` (`PLNXiDerivedBNRules`)
- Collider structural exact: `xi_sinkRule_strength_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider .toReal exact: `xi_sink_queryStrength_toReal_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider singleton short-name re-exports:
  `sinkLinkEqPropToReal`, `singletonPropToReal` (`PLNColliderSingletonBridge`)
- Collider formula counterexample: `plnAbductionStrength_not_exact_collider` (`PLNXiDerivedBNRules`)
- Error framework: `Comparison/ErrorCharacterization.lean` (decomposition + bounds + decision criteria)

### When is a PLN rule exact?

A PLN rule is exact when its internal screening-off assumption holds:
- **Deduction/Source**: requires C ⊥ A | B (holds in chain and fork by d-separation)
- **Abduction**: requires B ⊥ A | C (FAILS in collider: conditioning on C opens the explaining-away path)

The `ErrorCharacterization` module provides quantitative bounds on the error when
screening-off is violated (`error_bound_by_max_violation`, `conservative_estimate_is_bound`).

### Collider singleton composition pattern

Use this exact two-step composition:
```lean
have h1 := PLNColliderSingletonBridge.sinkLinkEqPropToReal
  valA valB hPos hLMarkov hDSep ({cpt} : BNWorldModel.State (bn := colliderBN))
have h2 := PLNColliderSingletonBridge.singletonPropToReal
  cpt Three.B valB
exact Eq.trans h1 h2
```
-/

/-! ## End-to-End Theorem Index

The `PLNEndToEnd` module provides short-name aliases for the complete
BN→WM→OSLF pipeline across all three topologies.

| Alias | Source | Topology |
|-------|--------|----------|
| `chainDeductionFormula` | `xi_deduction_queryStrength_eq_plnDeduction_of_chainBN` | Chain |
| `forkInductionFormula` | `xi_source_queryStrength_eq_plnInduction_of_forkBN` | Fork |
| `colliderStructural` | `xi_sinkRule_strength_eq_of_colliderBN` | Collider |
| `colliderFormulaNotExact` | `plnAbductionStrength_not_exact_collider` | Collider |
| `colliderFormulaExactWhenScreeningOff` | `plnAbductionStrength_exact_of_screeningOff` | Collider |

Context lifts: `wmRewriteRule_e2e_ctx` (generic), `oslfEvidenceSoundCtx`, `oslfThresholdSoundCtx`.

See `Mettapedia.Logic.PLNEndToEnd` for full listing and usage patterns. -/

namespace EndToEnd

/-- See `PLNEndToEnd` for the full E2E theorem index.

Concrete re-exports that don't depend on BN instance resolution: -/

noncomputable abbrev colliderFormulaNotExact := PLNEndToEnd.colliderFormulaNotExact

/-
All other E2E theorems depend on BN typeclass instances and must be invoked
with explicit instance resolution at the call site. Use the fully qualified names:

### Formula-level
- `PLNEndToEnd.chainDeductionFormula` — chain qS = plnDeductionStrength
- `PLNEndToEnd.forkInductionFormula` — fork qS = plnInductionStrength
- `PLNEndToEnd.colliderStructural` — collider qS(link) = qS(prop)
- `PLNEndToEnd.colliderStructuralToReal` — same at ℝ level

### Admissibility
- `PLNEndToEnd.chainDeductionAdmissible` — chain WM judgment
- `PLNEndToEnd.forkInductionAdmissible` — fork WM judgment
- `PLNEndToEnd.colliderAbductionAdmissible` — collider WM judgment

### OSLF bridges
- `PLNEndToEnd.chainDeductionOSLFEvidence` / `...Threshold`
- `PLNEndToEnd.forkInductionOSLFEvidence` / `...Threshold`
- `PLNEndToEnd.colliderAbductionOSLFEvidence` / `...Threshold`

### Context lifts
- `PLNEndToEnd.wmRewriteRule_e2e_ctx` — generic context lift
- `PLNEndToEnd.oslfEvidenceSoundCtx` — OSLF evidence under context
- `PLNEndToEnd.oslfThresholdSoundCtx` — OSLF threshold under context

### Exactness
- `PLNEndToEnd.colliderFormulaExactWhenScreeningOff` — exact when screening-off holds
- `PLNEndToEnd.colliderFormulaNotExact` — OR-gate counterexample
-/

end EndToEnd

end Mettapedia.Logic.PLNCanonical
