import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNBayesNetFastRules
import Mettapedia.Logic.EvidenceBeta

/-!
# PLN Xi Derived BN Rules (No-Sly Admissibility)

Concrete, fully derived PLN inference rules for the chain Bayesian network model.
Every rule's side condition is derived from **model semantics** (local Markov property
+ d-separation), not taken as a free hypothesis.

## Architecture: 5-Shape Derived Rule Block

Each rule family provides all 5 shapes:

1. **Side condition derivation** — derive Σ from BN model semantics
2. **WMRewriteRule** — the concrete rule (NO free `hSO` argument)
3. **Admissibility** — query judgment from derivable WM state
4. **OSLF evidence bridge** — `semE` equals derived evidence
5. **Threshold bridge** — strength-threshold Prop holds

## Scope

Currently covers:
- **Deduction** (chain A→B→C) — full 5-shape block + Tier B/C composition
- **Source rule / Induction** (fork A←B→C) — full 5-shape block
- **Sink rule / Abduction** (collider A→C←B) — full 5-shape block

## Concrete Proofs Used

All building blocks are fully proved (0 sorry):
- `chain_screeningOff_wmqueryeq_of_dsep` (PLNBNCompilation)
- `chain_screeningOff_strength_eq_of_dsep` (PLNBNCompilation)
- `queryStrength_singleton_eq_queryProb` (PLNBNCompilation)
- `linkProbVE_eq_jointMeasure_eventEq` / `propProbVE_eq_jointMeasure_eventEq` (VEBridge)
- `chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules)
- `evidence_aggregation_is_conjugate_update` (EvidenceBeta)

0 sorry. All theorems fully proved.
-/

namespace Mettapedia.Logic.PLNXiDerivedBNRules

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWMOSLFBridge
open Mettapedia.Logic.OSLFEvidenceSemantics
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.Logic.PLNBNCompilation.ChainExample
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open Mettapedia.OSLF.Formula
open Mettapedia.OSLF.MeTTaIL.Syntax

open scoped Classical ENNReal

/-! ## §0 Type Aliases -/

/-- All CPTs in the chain BN satisfy the local Markov property. -/
abbrev ChainBNLocalMarkovAll
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace] :=
  ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure

/-! ## §1 Deduction: Chain BN (A→B→C)

All arguments are model-semantic:
- `hLMarkov` : every CPT satisfies the local Markov property (a BN model axiom)
- `hDSep` : A and C are d-separated given B (a graph-theoretic property)

Neither is "assume the conclusion." The screening-off equality is a
**consequence** of these, proved in PLNBNCompilation. -/

section ChainBNDeduction

variable
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
  [StandardBorelSpace chainBN.JointSpace]

/-! ### Shape 1: Side condition derivation -/

/-- The screening-off query equivalence for the chain BN deduction case,
derived from local Markov + d-separation. -/
theorem deduction_wmqueryeq_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN)) :
    WMQueryEq (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      (PLNQuery.linkCond
        [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
        ⟨Three.C, valC⟩)
      (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  chain_screeningOff_wmqueryeq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep

/-! ### Shape 2: Derived WMRewriteRule (NO free hSO argument) -/

/-- Deduction rewrite rule for the chain BN, derived from local Markov +
d-separation. The rule rewrites `linkCond [A,B] C` to `link B C`.

Arguments are model-semantic:
- `hLMarkov` : local Markov property (BN model axiom)
- `hDSep` : d-separation A ⊥ C | B (graph property)

There is NO abstract screening-off hypothesis. -/
noncomputable def xi_deduction_rewrite_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (PLNQuery (BNQuery.Atom (bn := chainBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := chainBN))
    (Atom := BNQuery.Atom (bn := chainBN))
    (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩)
    (PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    ((CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN))
    (fun h => (deduction_wmqueryeq_of_chainBN valA valB valC hLMarkov h).symm)

/-- The derived rule's side condition is exactly d-separation. -/
theorem xi_deduction_rewrite_of_chainBN_side
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN)) :
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).side :=
  hDSep

/-! ### Shape 3: Admissibility (actual inference theorem) -/

/-- Admissibility: for any derivable WM state, the deduction rule produces
a valid query judgment. This is the "PLN deduction is sound in chain BNs"
theorem. -/
theorem xi_deduction_admissible_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (W : BNWorldModel.State (bn := chainBN))
    (hW : ⊢wm W) :
    ⊢q W ⇓
      (PLNQuery.linkCond
        ([ (⟨Three.A, valA⟩ : BNQuery.Atom (bn := chainBN))
         , (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN)) ])
        (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN))) ↦
      (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W :=
  WMRewriteRule.apply
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep) hW

/-! ### Shape 4: OSLF evidence bridge -/

/-- OSLF evidence bridge: if the OSLF atom encodes the deduction conclusion,
its evidence equals the derived rule's output. -/
theorem xi_deduction_semE_atom_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := chainBN))
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩) :
    semE R
      (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)
    W enc a p hEnc

/-! ### Shape 5: Threshold bridge -/

/-- Threshold bridge: if the derived strength exceeds `tau`, the atom
holds under strength-threshold semantics. -/
theorem xi_deduction_threshold_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := chainBN))
    (tau : ℝ≥0∞)
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    (hTau : tau ≤ Evidence.toStrength
      ((xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-! ### Bonus: Strength equality (re-export from PLNBNCompilation) -/

/-- Strength equality: under d-separation, the linkCond and link queries
have identical strength in every WM state. -/
theorem xi_deduction_strength_eq_of_chainBN
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (W : BNWorldModel.State (bn := chainBN)) :
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      W (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
      =
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
      W (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  chain_screeningOff_strength_eq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep W

end ChainBNDeduction

/-! ## §2 Tier B: Bernoulli-PLN Bridge (Measure → Formula)

Connects the measure-level conditional probability `P(C|A)` to the
`plnDeductionStrength` formula. This is a re-export of
`chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules) with Xi naming,
plus the foundational lemma `toStrength_evidenceOfProb` that links the
WM evidence layer to probability values.

### Evidence ↔ Probability Bridge

`BNWorldModel` stores evidence as `evidenceOfProb(p) = ⟨p, 1-p⟩` where
`p` is the conditional probability (ENNReal). `Evidence.toStrength` recovers
`p` when `p ≤ 1` (proved: `toStrength_evidenceOfProb`).

**Note**: The full singleton-CPT bridge (`queryStrength {cpt} q = queryProb cpt q`)
requires composing multiset singleton lemmas with `toStrength_evidenceOfProb`.
This is proved in PLNBNCompilation as `queryStrength_singleton_eq_queryProb`.

### PLN Deduction Strength Exactness

Under the chain BN screening-off conditions (derived from d-sep + local Markov):

```
P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
```

This is `chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules.lean). -/

section TierB

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNBayesNetFastRules
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN.Deduction
open MeasureTheory

/-- Evidence ↔ Probability bridge: `toStrength` of `evidenceOfProb p` recovers `p`
when `p ≤ 1`. This is the foundational lemma connecting WM evidence to probability. -/
theorem toStrength_evidenceOfProb (p : ℝ≥0∞) (hp : p ≤ 1) :
    Evidence.toStrength (evidenceOfProb p) = p := by
  unfold Evidence.toStrength evidenceOfProb Evidence.total
  simp only
  split
  · rename_i h
    have : p + (1 - p) = 1 := by rw [add_comm]; exact tsub_add_cancel_of_le hp
    rw [this] at h; exact absurd h one_ne_zero
  · have : p + (1 - p) = 1 := by rw [add_comm]; exact tsub_add_cancel_of_le hp
    rw [this]; exact div_one p

/-- Tier B: In the chain BN, the conditional probability `P(C|A)` equals the PLN
deduction formula applied to the component conditional probabilities.

This is the measure-level bridge connecting BN semantics to the algebraic
`plnDeductionStrength` formula. Re-exported from `chainBN_plnDeductionStrength_exact`
with Xi naming for the 3-tier theorem spine.

Arguments:
- `cpt` : a discrete CPT for the chain BN
- Positivity conditions on events A, B, A∩B, A∩Bᶜ (non-degeneracy)
- `hB_lt1` : P(B) < 1 (ensures P(Bᶜ) > 0) -/
theorem xi_deduction_plnStrength_exact_of_chainBN
    (cpt : PLNBayesNetFastRules.ChainBN.DiscreteCPT)
    (hA_pos : (μ (cpt := cpt)) (A : Set ChainBN.JointSpace) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0)
    (hB_lt1 : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) < 1)
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    (μ (cpt := cpt)).real (C ∩ (A : Set ChainBN.JointSpace)) /
        (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace) =
      plnDeductionStrength
        ((μ (cpt := cpt)).real ((B : Set ChainBN.JointSpace) ∩ A) /
            (μ (cpt := cpt)).real (A : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C ∩ (B : Set ChainBN.JointSpace)) /
            (μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (B : Set ChainBN.JointSpace))
        ((μ (cpt := cpt)).real (C : Set ChainBN.JointSpace)) :=
  chainBN_plnDeductionStrength_exact (cpt := cpt) hA_pos hB_pos hB_lt1 hAB_pos hABc_pos

end TierB

/-! ## §2b Tier A→B Composition: queryStrength → plnDeductionStrength

End-to-end composition connecting the WM queryStrength layer (ENNReal) to the
algebraic plnDeductionStrength formula (ℝ) for the chain BN.

### Bridge Chain

```
queryStrength {cpt} q  (ENNReal)
  ↓ singleton bridge (queryStrength_singleton_eq_queryProb)
queryProb cpt q  (ENNReal)
  ↓ VEBridge (linkProbVE/propProbVE_eq_jointMeasure_eventEq)
μ(event₁ ∩ event₂) / μ(event₁)  (ENNReal)
  ↓ ENNReal.toReal_div + Measure.real
μ.real ratios  (ℝ)
  ↓ chainBN_plnDeductionStrength_exact
plnDeductionStrength(s_AB, s_BC, s_B, s_C)  (ℝ)
```

**Consumes**: singleton bridge, VEBridge, Tier B. -/

section TierAB

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNBayesNetFastRules
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN
open Mettapedia.Logic.PLNBayesNetFastRules.ChainBN.Deduction
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open MeasureTheory

variable
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
  [StandardBorelSpace chainBN.JointSpace]

/-! ### §2a Bool-generic bridge lemmas

The 6 Bool-generic queryProb/queryStrength lemmas live in **PLNBNCompilation**
(shared layer) so that source/sink derivations can reuse them:

- `queryProb_prop_eq_jointMeasure` / `queryProb_link_eq_jointMeasure`
- `queryProb_prop_le_one` / `queryProb_link_le_one`
- `queryStrength_singleton_prop_toReal` / `queryStrength_singleton_link_toReal`

These work for any BN and any state value. -/

/-! ### §2b Bridge lemmas: VEBridge types ↔ FastRules types (true-specialized)

These are corollaries of the Bool-generic helpers for `val = true`,
bridging to `eventTrue` used in `chainBN_plnDeductionStrength_exact`. -/

/-- `eventEq v true` (VEBridge) equals `eventTrue v` (FastRules). -/
private lemma eventEq_true_eq_eventTrue (v : Three) :
    eventEq (bn := chainBN) v true = eventTrue v := by
  ext ω; simp [eventEq, eventTrue, Set.mem_preimage]

/-! ### Bridge lemmas: queryProb → jointMeasure -/

/-- queryProb for prop at `true` = marginal measure μ(event). -/
private lemma queryProb_prop_true_eq
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.prop ⟨v, true⟩) =
      (μ (cpt := cpt)) (eventTrue v) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq, eventEq_true_eq_eventTrue]
  rfl

/-- queryProb for link at `true` = conditional probability ratio μ(a∩b)/μ(a). -/
private lemma queryProb_link_true_eq
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    queryProb (bn := chainBN) cpt (PLNQuery.link ⟨a, true⟩ ⟨b, true⟩) =
      (μ (cpt := cpt)) (eventTrue a ∩ eventTrue b) /
        (μ (cpt := cpt)) (eventTrue a) := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  simp only [eventEq_true_eq_eventTrue]
  split_ifs with h
  · exact absurd h ha
  · rfl

/-! ### Probability bounds (needed by singleton bridge) -/

private lemma queryProb_prop_true_le_one
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.prop ⟨v, true⟩) ≤ 1 := by
  rw [queryProb_prop_true_eq]; exact prob_le_one

private lemma queryProb_link_true_le_one
    (cpt : ChainBN.DiscreteCPT) (a b : Three) :
    queryProb (bn := chainBN) cpt (PLNQuery.link ⟨a, true⟩ ⟨b, true⟩) ≤ 1 := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  simp only [eventEq_true_eq_eventTrue]
  split
  · exact zero_le_one
  · exact le_trans (ENNReal.div_le_div_right (measure_mono Set.inter_subset_left) _)
      ENNReal.div_self_le_one

/-! ### ENNReal → ℝ bridge: queryStrength.toReal = μ.real -/

/-- Singleton prop queryStrength.toReal = μ.real(event). -/
private lemma queryStrength_singleton_prop_toReal
    (cpt : ChainBN.DiscreteCPT) (v : Three) :
    (WorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (PLNQuery.prop (⟨v, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    (μ (cpt := cpt)).real (eventTrue v) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_prop_true_le_one cpt v)]
  rw [queryProb_prop_true_eq]
  simp [Measure.real]

/-- Singleton link queryStrength.toReal = μ.real(b∩a)/μ.real(a).
Note: intersection order is b∩a (not a∩b) to match Tier B convention. -/
private lemma queryStrength_singleton_link_toReal
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    (WorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (PLNQuery.link (⟨a, true⟩ : BNQuery.Atom (bn := chainBN))
                     (⟨b, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    (μ (cpt := cpt)).real (eventTrue b ∩ eventTrue a) /
      (μ (cpt := cpt)).real (eventTrue a) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_link_true_le_one cpt a b)]
  rw [queryProb_link_true_eq cpt a b ha]
  rw [Set.inter_comm (eventTrue a) (eventTrue b)]
  rw [ENNReal.toReal_div]
  simp [Measure.real]

/-! ### Composition theorem -/

/-- **Tier A→B Composition**: For the chain BN with singleton CPT state,
the PLN deduction probability identity holds at the queryStrength level:

```
P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
```

where each probability is `(queryStrength {cpt} q).toReal`.

**Consumes**:
- `queryStrength_singleton_eq_queryProb` (singleton bridge)
- `linkProbVE_eq_jointMeasure_eventEq` / `propProbVE_eq_jointMeasure_eventEq` (VEBridge)
- `chainBN_plnDeductionStrength_exact` (Tier B) -/
theorem xi_deduction_queryStrength_eq_plnDeduction_of_chainBN
    (cpt : ChainBN.DiscreteCPT)
    (hA_pos : (μ (cpt := cpt)) (A : Set ChainBN.JointSpace) ≠ 0)
    (hB_pos : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) ≠ 0)
    (hB_lt1 : (μ (cpt := cpt)) (B : Set ChainBN.JointSpace) < 1)
    (hAB_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)) ≠ 0)
    (hABc_pos : (μ (cpt := cpt)) (A ∩ (B : Set ChainBN.JointSpace)ᶜ) ≠ 0) :
    let W : BNWorldModel.State (bn := chainBN) := {cpt}
    (WorldModel.queryStrength W
      (PLNQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                     (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    plnDeductionStrength
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal := by
  intro W
  -- Bridge: convert each queryStrength to μ.real
  rw [queryStrength_singleton_link_toReal cpt Three.A Three.C hA_pos]
  rw [queryStrength_singleton_link_toReal cpt Three.A Three.B hA_pos]
  rw [queryStrength_singleton_link_toReal cpt Three.B Three.C hB_pos]
  rw [queryStrength_singleton_prop_toReal cpt Three.B]
  rw [queryStrength_singleton_prop_toReal cpt Three.C]
  -- Now goal is in μ.real terms, matching Tier B exactly
  exact chainBN_plnDeductionStrength_exact (cpt := cpt) hA_pos hB_pos hB_lt1 hAB_pos hABc_pos

end TierAB

/-! ## §3 Tier C: Beta-Bernoulli Computational Layer

When evidence is represented as discrete counts `(n⁺, n⁻)`, the PLN strength
function `plnStrength` computes `n⁺/(n⁺+n⁻)`. Substituting these into
`plnDeductionStrength` gives a fully computable expression.

**Guardrail**: The Beta distribution is a *modeling choice*, not forced by
exchangeability. See `EvidenceBeta.not_beta_from_exchangeability_example`
for an explicit counterexample: an exchangeable sequence whose de Finetti
mixing measure is NOT Beta. -/

section TierC

open Mettapedia.Logic.PLN
open Mettapedia.Logic.EvidenceBeta

/-! ### Denominator safety -/

/-- `plnStrength n⁺ n⁻ < 1` when `n⁻ ≠ 0`. This ensures the denominator
`(1 - s_B)` in `plnDeductionStrength` is positive. -/
theorem plnStrength_lt_one (n_pos n_neg : ℕ) (hNeg : n_neg ≠ 0) :
    plnStrength n_pos n_neg < 1 := by
  unfold plnStrength Mettapedia.Logic.EvidenceCounts.plnStrength
  split
  · exact zero_lt_one
  · rename_i hTotal
    rw [div_lt_one (by positivity : (0 : ℝ) < ↑n_pos + ↑n_neg)]
    have : (0 : ℝ) < ↑n_neg := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hNeg)
    linarith

/-- The denominator `(1 - s_B)` in `plnDeductionStrength` is positive
when `nB_neg ≠ 0`. -/
theorem plnDeductionStrength_denom_pos (n_pos n_neg : ℕ) (hNeg : n_neg ≠ 0) :
    0 < 1 - plnStrength n_pos n_neg :=
  sub_pos.mpr (plnStrength_lt_one n_pos n_neg hNeg)

/-! ### Count-based unfolding -/

/-- Tier C: `plnDeductionStrength` applied to `plnStrength` count values
unfolds to the same formula with rational arguments `n⁺/(n⁺+n⁻)`.

This makes PLN deduction fully computable from evidence counts alone.
The proof is definitional unfolding of `plnStrength`. -/
theorem plnDeductionStrength_of_plnStrength
    (nAB_pos nAB_neg nBC_pos nBC_neg nB_pos nB_neg nC_pos nC_neg : ℕ)
    (hAB : nAB_pos + nAB_neg ≠ 0) (hBC : nBC_pos + nBC_neg ≠ 0)
    (hB : nB_pos + nB_neg ≠ 0) :
    plnDeductionStrength
      (plnStrength nAB_pos nAB_neg)
      (plnStrength nBC_pos nBC_neg)
      (plnStrength nB_pos nB_neg)
      (plnStrength nC_pos nC_neg) =
    plnDeductionStrength
      ((nAB_pos : ℝ) / (↑nAB_pos + ↑nAB_neg))
      ((nBC_pos : ℝ) / (↑nBC_pos + ↑nBC_neg))
      ((nB_pos : ℝ) / (↑nB_pos + ↑nB_neg))
      (plnStrength nC_pos nC_neg) := by
  rw [plnStrength_eq_improper_mean nAB_pos nAB_neg hAB]
  rw [plnStrength_eq_improper_mean nBC_pos nBC_neg hBC]
  rw [plnStrength_eq_improper_mean nB_pos nB_neg hB]

/-- Tier C (full unfold): All four `plnStrength` values unfolded. -/
theorem plnDeductionStrength_of_plnStrength_full
    (nAB_pos nAB_neg nBC_pos nBC_neg nB_pos nB_neg nC_pos nC_neg : ℕ)
    (hAB : nAB_pos + nAB_neg ≠ 0) (hBC : nBC_pos + nBC_neg ≠ 0)
    (hB : nB_pos + nB_neg ≠ 0) (hC : nC_pos + nC_neg ≠ 0) :
    plnDeductionStrength
      (plnStrength nAB_pos nAB_neg)
      (plnStrength nBC_pos nBC_neg)
      (plnStrength nB_pos nB_neg)
      (plnStrength nC_pos nC_neg) =
    plnDeductionStrength
      ((nAB_pos : ℝ) / (↑nAB_pos + ↑nAB_neg))
      ((nBC_pos : ℝ) / (↑nBC_pos + ↑nBC_neg))
      ((nB_pos : ℝ) / (↑nB_pos + ↑nB_neg))
      ((nC_pos : ℝ) / (↑nC_pos + ↑nC_neg)) := by
  rw [plnStrength_eq_improper_mean nAB_pos nAB_neg hAB]
  rw [plnStrength_eq_improper_mean nBC_pos nBC_neg hBC]
  rw [plnStrength_eq_improper_mean nB_pos nB_neg hB]
  rw [plnStrength_eq_improper_mean nC_pos nC_neg hC]

/-- Tier C connection to conjugate update: evidence aggregation (hplus) is
Beta conjugate update. See `EvidenceBeta.evidence_aggregation_is_conjugate_update`.

**Guardrail**: Beta is a modeling choice. See
`EvidenceBeta.not_beta_from_exchangeability_example` for a counterexample
showing exchangeability does NOT force the Beta distribution. -/
theorem evidence_hplus_is_conjugate :
    ∀ (prior_param : ℝ) (hprior : 0 < prior_param)
      (n₁_pos n₁_neg n₂_pos n₂_neg : ℕ),
    let params₁ := { prior_param := prior_param, prior_pos := hprior,
                     evidence_pos := n₁_pos, evidence_neg := n₁_neg :
                     EvidenceBetaParams }
    let params_combined := { prior_param := prior_param, prior_pos := hprior,
                             evidence_pos := n₁_pos + n₂_pos,
                             evidence_neg := n₁_neg + n₂_neg :
                             EvidenceBetaParams }
    params_combined.alpha = params₁.alpha + ↑n₂_pos ∧
    params_combined.beta = params₁.beta + ↑n₂_neg :=
  evidence_aggregation_is_conjugate_update

end TierC

/-! ## §4 Source Rule: Fork BN (A ← B → C)

The fork BN has edges B→A and B→C. The source rule (induction) derives
link A→C from links B→A and B→C.

The screening-off condition is A ⊥ C | B, which holds in the fork because
B is a non-collider on the path A-B-C. The WMQueryEq identity

  `linkCond [A,B] C = link B C`

is exactly the screening-off content: knowing A in addition to B doesn't
help predict C. This is proved in PLNBNCompilation.ForkExample.

### Differences from Chain BN Deduction (§1)

| Property | Chain (§1) | Fork (§4) |
|----------|-----------|-----------|
| Graph | A → B → C | A ← B → C |
| Input links | A→B, B→C | B→A, B→C |
| Output link | A→C | A→C |
| Rule type | Deduction | Source (Induction) |
| Side condition | A ⊥ C \| B | A ⊥ C \| B |
| WMQueryEq | same form | same form |

The d-sep condition is identical; the structural difference is the BN graph. -/

section ForkBNSourceRule

open Mettapedia.Logic.PLNBNCompilation.ForkExample

variable
  [∀ v : Three, Fintype (forkBN.stateSpace v)]
  [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
  [∀ v : Three, Inhabited (forkBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
  [StandardBorelSpace forkBN.JointSpace]

/-- All CPTs in the fork BN satisfy the local Markov property. -/
abbrev ForkBNLocalMarkovAll
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace] :=
  ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure

/-! ### Shape 1: Side condition derivation -/

/-- The screening-off query equivalence for the fork BN source rule case,
derived from local Markov + d-separation. -/
theorem sourceRule_wmqueryeq_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN)) :
    WMQueryEq (State := BNWorldModel.State (bn := forkBN))
      (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
      (PLNQuery.linkCond
        [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
        ⟨Three.C, valC⟩)
      (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  fork_screeningOff_wmqueryeq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep

/-! ### Shape 2: Derived WMRewriteRule (NO free hSO argument) -/

/-- Source rule (induction) rewrite rule for the fork BN, derived from
local Markov + d-separation. The rule rewrites `linkCond [A,B] C` to `link B C`.

Arguments are model-semantic:
- `hLMarkov` : local Markov property (BN model axiom)

There is NO abstract screening-off hypothesis.
The d-separation condition is the rule's side condition. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (PLNQuery (BNQuery.Atom (bn := forkBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := forkBN))
    (Atom := BNQuery.Atom (bn := forkBN))
    (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩)
    (PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    ((CompiledPlan.inductionSide Three.A Three.B Three.C).holds (bn := forkBN))
    (fun h => (sourceRule_wmqueryeq_of_forkBN valA valB valC hLMarkov h).symm)

/-- The derived rule's side condition is exactly d-separation (induction side). -/
theorem xi_sourceRule_rewrite_of_forkBN_side
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN)) :
    (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov).side :=
  hDSep

/-! ### Shape 3: Admissibility (actual inference theorem) -/

/-- Admissibility: for any derivable WM state, the source rule produces
a valid query judgment. This is the "PLN source rule (induction) is sound
in fork BNs" theorem. -/
theorem xi_sourceRule_admissible_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN))
    (W : BNWorldModel.State (bn := forkBN))
    (hW : ⊢wm W) :
    ⊢q W ⇓
      (PLNQuery.linkCond
        ([ (⟨Three.A, valA⟩ : BNQuery.Atom (bn := forkBN))
         , (⟨Three.B, valB⟩ : BNQuery.Atom (bn := forkBN)) ])
        (⟨Three.C, valC⟩ : BNQuery.Atom (bn := forkBN))) ↦
      (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov).derive W :=
  WMRewriteRule.apply
    (xi_sourceRule_rewrite_of_forkBN_side valA valB valC hLMarkov hDSep) hW

/-! ### Shape 4: OSLF evidence bridge -/

/-- OSLF evidence bridge: if the OSLF atom encodes the source rule conclusion,
its evidence equals the derived rule's output. -/
theorem xi_sourceRule_semE_atom_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := forkBN))
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := forkBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩) :
    semE R
      (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov)
    (xi_sourceRule_rewrite_of_forkBN_side valA valB valC hLMarkov hDSep)
    W enc a p hEnc

/-! ### Shape 5: Threshold bridge -/

/-- Threshold bridge: if the derived strength exceeds `tau`, the atom
holds under strength-threshold semantics. -/
theorem xi_sourceRule_threshold_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := forkBN))
    (tau : ℝ≥0∞)
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := forkBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    (hTau : tau ≤ Evidence.toStrength
      ((xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov)
    (xi_sourceRule_rewrite_of_forkBN_side valA valB valC hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-! ### Bonus: Strength equality (re-export from PLNBNCompilation.ForkExample) -/

/-- Strength equality: under d-separation, the linkCond and link queries
have identical strength in every WM state. -/
theorem xi_sourceRule_strength_eq_of_forkBN
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN))
    (W : BNWorldModel.State (bn := forkBN)) :
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := forkBN))
      (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
      W (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
      =
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := forkBN))
      (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
      W (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  fork_screeningOff_strength_eq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep W

end ForkBNSourceRule

/-! ## §4b Source Rule Tier A→B Composition (Fork BN)

Connects `queryStrength` at the WM level to `plnInductionStrength` at the
formula level. The key algebraic step: `bayesInversion(P(A|B), P(A), P(B)) = P(B|A)`,
which converts the induction formula into the deduction formula applied to the fork.

**Consumes**:
- `queryStrength_singleton_link_toReal` / `queryStrength_singleton_prop_toReal` (PLNBNCompilation)
- `forkBN_plnDeductionStrength_exact` (PLNBayesNetFastRules)
- `bayesInversion` (PLNDerivation)
-/

section ForkBNSourceRuleTierAB

open Mettapedia.Logic.PLN
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.Logic.PLNBayesNetFastRules
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open MeasureTheory

instance : DecidableRel forkBN.graph.edges := by
  intro u v; dsimp [forkBN, forkGraph, DirectedGraph.edges]; infer_instance

instance (v : Three) : MeasurableSingletonClass (forkBN.stateSpace v) := by
  dsimp [forkBN]; infer_instance

instance (v : Three) : Nonempty (forkBN.stateSpace v) := by
  dsimp [forkBN]; infer_instance

-- Abbreviations for fork event sets (matching PLNBayesNetFastRules)
private abbrev fA' := eventEq (bn := forkBN) Three.A true
private abbrev fB' := eventEq (bn := forkBN) Three.B true
private abbrev fC' := eventEq (bn := forkBN) Three.C true

-- Local bridge helpers (fork-specific, avoiding name clash with chain's private helpers)
private lemma fork_qS_link_toReal (cpt : forkBN.DiscreteCPT) (a b : Three)
    (ha : cpt.jointMeasure (eventEq (bn := forkBN) a true) ≠ 0) :
    (WorldModel.queryStrength ({cpt} : BNWorldModel.State (bn := forkBN))
      (PLNQuery.link (⟨a, true⟩ : BNQuery.Atom (bn := forkBN))
                     (⟨b, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal =
    cpt.jointMeasure.real (eventEq (bn := forkBN) b true ∩ eventEq (bn := forkBN) a true) /
      cpt.jointMeasure.real (eventEq (bn := forkBN) a true) := by
  rw [queryStrength_singleton_eq_queryProb]
  · rw [queryProb_link_eq_jointMeasure cpt a b true true ha]
    rw [Set.inter_comm]; rw [ENNReal.toReal_div]; simp [Measure.real]
  · simp only [queryProb]; rw [linkProbVE_eq_jointMeasure_eventEq]
    split
    · exact zero_le_one
    · exact le_trans (ENNReal.div_le_div_right (measure_mono Set.inter_subset_left) _)
        ENNReal.div_self_le_one

private lemma fork_qS_prop_toReal (cpt : forkBN.DiscreteCPT) (v : Three) :
    (WorldModel.queryStrength ({cpt} : BNWorldModel.State (bn := forkBN))
      (PLNQuery.prop (⟨v, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal =
    cpt.jointMeasure.real (eventEq (bn := forkBN) v true) := by
  rw [queryStrength_singleton_eq_queryProb]
  · rw [queryProb_prop_eq_jointMeasure]; simp [Measure.real]
  · rw [queryProb_prop_eq_jointMeasure]; exact prob_le_one

/-- **Tier A→B Composition for Source Rule (Fork BN)**:
For the fork BN `A ← B → C` with singleton CPT state,
the PLN induction strength formula is exact at the queryStrength level:

```
qS(link A C).toReal = plnInductionStrength(qS(link B A), qS(link B C), qS(prop A), qS(prop B), qS(prop C))
```

**Mathematical content**: `plnInductionStrength` unfolds as
`plnDeductionStrength(bayesInversion(P(A|B), P(A), P(B)), P(C|B), P(B), P(C))`.
Since `bayesInversion(P(A|B), P(A), P(B)) = P(B|A)` (Bayes' rule), and the fork's
conditional independence C ⊥ A | B gives the screening-off conditions, this equals
`P(C|A)` by the PLN deduction formula. -/
theorem xi_source_queryStrength_eq_plnInduction_of_forkBN
    (cpt : forkBN.DiscreteCPT)
    [HasLocalMarkovProperty forkBN cpt.jointMeasure]
    (hA_pos : cpt.jointMeasure fA' ≠ 0)
    (hB_pos : cpt.jointMeasure fB' ≠ 0)
    (hB_lt1 : cpt.jointMeasure fB' < 1)
    (hAB_pos : cpt.jointMeasure (fA' ∩ fB') ≠ 0)
    (hABc_pos : cpt.jointMeasure (fA' ∩ fB'ᶜ) ≠ 0) :
    let W : BNWorldModel.State (bn := forkBN) := {cpt}
    (WorldModel.queryStrength W
      (PLNQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN))
                     (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal =
    plnInductionStrength
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN))
                       (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN))
                       (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (WorldModel.queryStrength W
        (PLNQuery.prop (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal := by
  intro W
  -- Step 1: Bridge queryStrength to μ.real via local fork helpers
  rw [fork_qS_link_toReal cpt Three.A Three.C hA_pos]
  rw [fork_qS_link_toReal cpt Three.B Three.A hB_pos]
  rw [fork_qS_link_toReal cpt Three.B Three.C hB_pos]
  rw [fork_qS_prop_toReal cpt Three.A]
  rw [fork_qS_prop_toReal cpt Three.B]
  rw [fork_qS_prop_toReal cpt Three.C]
  -- Step 2: Unfold plnInductionStrength to bayesInversion + plnDeductionStrength
  unfold plnInductionStrength
  -- Step 3: Simplify bayesInversion(P(A|B), P(A), P(B)) = P(B|A)
  -- bayesInversion(μ.real(A∩B)/μ.real(B), μ.real(A), μ.real(B))
  -- = (μ.real(A∩B)/μ.real(B)) * μ.real(B) / μ.real(A)
  -- = μ.real(A∩B) / μ.real(A)
  -- = μ.real(B∩A) / μ.real(A)  (by inter_comm)
  unfold bayesInversion
  have hB_real_pos : cpt.jointMeasure.real fB' ≠ 0 := by
    simp only [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hB_pos, measure_ne_top _ _⟩
  have hA_real_pos : cpt.jointMeasure.real fA' ≠ 0 := by
    simp only [Measure.real, ENNReal.toReal_ne_zero]
    exact ⟨hA_pos, measure_ne_top _ _⟩
  -- (μ.real(A∩B)/μ.real(B)) * μ.real(B) / μ.real(A) = μ.real(A∩B) / μ.real(A)
  rw [div_mul_cancel₀ (cpt.jointMeasure.real (fA' ∩ fB')) hB_real_pos]
  -- Now goal has μ.real(A∩B)/μ.real(A) where we need μ.real(B∩A)/μ.real(A)
  rw [Set.inter_comm fA' fB']
  -- Step 4: Apply the fork measure-level exact theorem
  exact forkBN_plnDeductionStrength_exact cpt hA_pos hB_pos hB_lt1 hAB_pos hABc_pos

end ForkBNSourceRuleTierAB

/-! ## §5 Sink Rule: Collider BN (A → C ← B)

The collider BN has edges A→C and B→C. The sink rule (abduction) derives
link A→B from links A→C and B→C.

**Variable mapping**: (A_rule, B_rule, C_rule) = (Three.A, Three.C, Three.B).
The sink center is Three.C (the collider node). The side condition is

  `abductionSide Three.A Three.C Three.B = ⟨{Three.A}, {Three.B}, ∅⟩`

which requires marginal independence A ⊥ B | ∅. This holds in the collider
because A and B have no active path when C (the common effect) is not
conditioned on.

The WMQueryEq identity rewrites `link ⟨A, valA⟩ ⟨B, valB⟩` to `prop ⟨B, valB⟩`,
which is the marginal independence content: P(B|A) = P(B).

### Differences from Chain BN Deduction (§1) and Fork Source (§4)

| Property | Chain (§1) | Fork (§4) | Collider (§5) |
|----------|-----------|-----------|--------------|
| Graph | A → B → C | A ← B → C | A → C ← B |
| Input links | A→B, B→C | B→A, B→C | A→C, B→C |
| Output link | A→C | A→C | A→B |
| Rule type | Deduction | Source | Sink (Abduction) |
| Side condition | A ⊥ C \| B | A ⊥ C \| B | A ⊥ B \| ∅ |
| WMQueryEq | linkCond→link | linkCond→link | link→prop | -/

section ColliderBNSinkRule

open Mettapedia.Logic.PLNBNCompilation.ColliderExample

variable
  [∀ v : Three, Fintype (colliderBN.stateSpace v)]
  [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
  [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace]

/-- All CPTs in the collider BN satisfy the local Markov property. -/
abbrev ColliderBNLocalMarkovAll
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace] :=
  ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure

/-! ### Shape 1: Side condition derivation -/

/-- The screening-off query equivalence for the collider BN sink rule case,
derived from local Markov + d-separation. Under A ⊥ B | ∅,
`link ⟨A, valA⟩ ⟨B, valB⟩` is evidence-equivalent to `prop ⟨B, valB⟩`. -/
theorem sinkRule_wmqueryeq_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN)) :
    WMQueryEq (State := BNWorldModel.State (bn := colliderBN))
      (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
      (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
      (PLNQuery.prop ⟨Three.B, valB⟩) :=
  collider_screeningOff_wmqueryeq_of_dsep
    (valA := valA) (valB := valB) hLMarkov hDSep

/-! ### Shape 2: Derived WMRewriteRule (NO free hSO argument) -/

/-- Sink rule (abduction) rewrite rule for the collider BN, derived from
local Markov + d-separation. The rule rewrites `link ⟨A,valA⟩ ⟨B,valB⟩`
to `prop ⟨B,valB⟩` (marginal independence).

Arguments are model-semantic:
- `hLMarkov` : local Markov property (BN model axiom)

There is NO abstract screening-off hypothesis.
The d-separation condition is the rule's side condition. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (PLNQuery (BNQuery.Atom (bn := colliderBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := colliderBN))
    (Atom := BNQuery.Atom (bn := colliderBN))
    (PLNQuery.prop ⟨Three.B, valB⟩)
    (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
    ((CompiledPlan.abductionSide Three.A Three.C Three.B).holds (bn := colliderBN))
    (fun h => (sinkRule_wmqueryeq_of_colliderBN valA valB hLMarkov h).symm)

/-- The derived rule's side condition is exactly d-separation (abduction side). -/
theorem xi_sinkRule_rewrite_of_colliderBN_side
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN)) :
    (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov).side :=
  hDSep

/-! ### Shape 3: Admissibility (actual inference theorem) -/

/-- Admissibility: for any derivable WM state, the sink rule produces
a valid query judgment. This is the "PLN sink rule (abduction) is sound
in collider BNs" theorem. -/
theorem xi_sinkRule_admissible_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (W : BNWorldModel.State (bn := colliderBN))
    (hW : ⊢wm W) :
    ⊢q W ⇓
      (PLNQuery.link
        (⟨Three.A, valA⟩ : BNQuery.Atom (bn := colliderBN))
        (⟨Three.B, valB⟩ : BNQuery.Atom (bn := colliderBN))) ↦
      (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov).derive W :=
  WMRewriteRule.apply
    (xi_sinkRule_rewrite_of_colliderBN_side valA valB hLMarkov hDSep) hW

/-! ### Shape 4: OSLF evidence bridge -/

/-- OSLF evidence bridge: if the OSLF atom encodes the sink rule conclusion,
its evidence equals the derived rule's output. -/
theorem xi_sinkRule_semE_atom_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := colliderBN))
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := colliderBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.link
      ⟨Three.A, valA⟩ ⟨Three.B, valB⟩) :
    semE R
      (wmEvidenceAtomSemQ W enc) (.atom a) p =
      (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov).derive W :=
  wmRewriteRule_semE_atom_eq_derive R
    (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov)
    (xi_sinkRule_rewrite_of_colliderBN_side valA valB hLMarkov hDSep)
    W enc a p hEnc

/-! ### Shape 5: Threshold bridge -/

/-- Threshold bridge: if the derived strength exceeds `tau`, the atom
holds under strength-threshold semantics. -/
theorem xi_sinkRule_threshold_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (R : Pattern → Pattern → Prop)
    (W : BNWorldModel.State (bn := colliderBN))
    (tau : ℝ≥0∞)
    (enc : String → Pattern → PLNQuery (BNQuery.Atom (bn := colliderBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = PLNQuery.link
      ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
    (hTau : tau ≤ Evidence.toStrength
      ((xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov)
    (xi_sinkRule_rewrite_of_colliderBN_side valA valB hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-! ### Bonus: Strength equality (re-export from PLNBNCompilation.ColliderExample) -/

/-- Strength equality: under d-separation, the link and prop queries
have identical strength in every WM state (marginal independence). -/
theorem xi_sinkRule_strength_eq_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (W : BNWorldModel.State (bn := colliderBN)) :
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
      W (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
      =
    WorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
      W (PLNQuery.prop ⟨Three.B, valB⟩) :=
  collider_screeningOff_strength_eq_of_dsep
    (valA := valA) (valB := valB) hLMarkov hDSep W

/-- `.toReal` corollary: the exact collider result at the real-valued level.
In collider topology, `qS(link A B).toReal = qS(prop B).toReal = P(B)`. -/
theorem xi_sink_queryStrength_toReal_eq_of_colliderBN
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (W : BNWorldModel.State (bn := colliderBN)) :
    (WorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
      W (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)).toReal
      =
    (WorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
      W (PLNQuery.prop ⟨Three.B, valB⟩)).toReal :=
  congr_arg ENNReal.toReal
    (xi_sinkRule_strength_eq_of_colliderBN valA valB hLMarkov hDSep W)

/-! ### Singleton bridge: collider exact at measure level

Following the chain bridge pattern: collider-specific queryProb helpers, then
compose with the `.toReal` corollary via `linarith`. -/

instance : DecidableRel colliderBN.graph.edges := by
  intro u v; dsimp [colliderBN, colliderGraph, DirectedGraph.edges]; infer_instance

instance (v : Three) : MeasurableSingletonClass (colliderBN.stateSpace v) := by
  dsimp [colliderBN]; infer_instance

instance (v : Three) : Nonempty (colliderBN.stateSpace v) := by
  dsimp [colliderBN]; infer_instance

omit
  [(v : Three) → Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace] in
private lemma collider_queryProb_prop_eq
    (cpt : colliderBN.DiscreteCPT) (v : Three) (val : Bool) :
    queryProb (bn := colliderBN) cpt (PLNQuery.prop ⟨v, val⟩) =
      cpt.jointMeasure (eventEq (bn := colliderBN) v val) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq]

omit
  [(v : Three) → Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace] in
private lemma collider_queryProb_prop_le_one
    (cpt : colliderBN.DiscreteCPT) (v : Three) (val : Bool) :
    queryProb (bn := colliderBN) cpt (PLNQuery.prop ⟨v, val⟩) ≤ 1 := by
  rw [collider_queryProb_prop_eq]; exact MeasureTheory.prob_le_one

omit
  [(v : Three) → Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace] in
private lemma collider_queryStrength_singleton_prop_toReal
    (cpt : colliderBN.DiscreteCPT) (v : Three) (val : Bool) :
    (WorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := colliderBN))
      (PLNQuery.prop (⟨v, val⟩ : BNQuery.Atom (bn := colliderBN)))).toReal =
    cpt.jointMeasure.real (eventEq (bn := colliderBN) v val) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (collider_queryProb_prop_le_one cpt v val)]
  rw [collider_queryProb_prop_eq]
  simp [MeasureTheory.Measure.real]

/-
Singleton-collider marginal corollary is obtained by transitivity from:
1) `xi_sink_queryStrength_toReal_eq_of_colliderBN`
2) `collider_queryStrength_singleton_prop_toReal`.

We intentionally keep it as a two-lemma composition in this module: a direct
single theorem statement triggers deterministic `whnf` heartbeat timeouts in the
full `ColliderBNSinkRule` section despite the two component lemmas being proved.
-/

end ColliderBNSinkRule

/-! ## §6 Collider Abduction: Approximation, Not Exact

The PLN abduction formula `plnAbductionStrength` is NOT in general equal to the
true conditional probability P(B|A) in a collider BN. This is because abduction
internally applies the deduction formula (via Bayes inversion), but the deduction
formula requires B ⊥ A | C (conditional independence given the middle variable).
In a collider A→C←B, conditioning on C **opens** the path (explaining away),
making A and B dependent given C. Therefore the screening-off assumption fails.

This does **not** contradict the PLN book's high-level framing: induction/abduction
there are presented as heuristic/fallible inference patterns derived via inversion +
deduction and expected to be used in combination with other rules and context.
Formally here, we pin down one concrete regime where the algebraic abduction
formula is approximate rather than exact.

This section provides a formal counterexample. -/

/-- The PLN abduction formula does not in general compute the correct conditional
probability for collider BNs.

Counterexample (OR-gate collider): P(A=1) = P(B=1) = 1/2, C = A OR B.
- True: P(B=1|A=1) = 1/2 (marginal independence)
- Formula: plnAbductionStrength 1 1 (1/2) (3/4) (1/2) = 2/3
- The formula overestimates by 1/6. -/
theorem plnAbductionStrength_not_exact_collider :
    PLN.plnAbductionStrength 1 1 (1/2 : ℝ) (3/4 : ℝ) (1/2 : ℝ) ≠ (1/2 : ℝ) := by
  unfold PLN.plnAbductionStrength PLN.bayesInversion PLN.plnDeductionStrength
  norm_num

/-! ## §7 Abduction Exactness Envelope

The abduction formula IS exact when the screening-off it internally requires holds.
Since `plnAbductionStrength` = Bayes inversion + `plnDeductionStrength`, and deduction
is exact under total-probability screening-off (C ⊥ A | B), abduction is exact when
we can supply those conditions with the appropriate variable mapping.

This theorem characterizes the **exactness envelope**: the set of distributions for
which the algebraic abduction formula correctly computes the conditional probability.
Combined with the counterexample above, we get:
- Abduction exact ← screening-off holds (this theorem)
- Abduction not exact ← collider topology violates screening-off (counterexample)
-/

open MeasureTheory in
/-- The PLN abduction formula IS exact when the required screening-off holds.

Given premises P(B|A) and P(B|C), and screening-off C ⊥ A | B (positive and negative),
`plnAbductionStrength` correctly computes P(C|A).

This is `pln_deduction_from_total_probability` composed with Bayes inversion:
the abduction formula internally does `deduction(P(B|A), bayesInversion(P(B|C)) = P(C|B), P(B), P(C))`,
which is exact when C ⊥ A | B. -/
theorem plnAbductionStrength_exact_of_screeningOff
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {A B C : Set Ω} (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hA_pos : μ A ≠ 0) (hB_pos : μ B ≠ 0) (hB_lt1 : μ B < 1)
    (hAB_pos : μ (A ∩ B) ≠ 0) (hABc_pos : μ (A ∩ Bᶜ) ≠ 0)
    (hC_pos : μ C ≠ 0)
    -- Screening-off: C ⊥ A | B (positive and negative)
    (h_pos_indep : μ.real (C ∩ (A ∩ B)) / μ.real (A ∩ B) = μ.real (C ∩ B) / μ.real B)
    (h_neg_indep : μ.real (C ∩ (A ∩ Bᶜ)) / μ.real (A ∩ Bᶜ) = μ.real (C ∩ Bᶜ) / μ.real Bᶜ) :
    μ.real (C ∩ A) / μ.real A =
      PLN.plnAbductionStrength
        (μ.real (B ∩ A) / μ.real A)       -- s_AB = P(B|A)
        (μ.real (B ∩ C) / μ.real C)       -- s_CB = P(B|C)
        (μ.real A)                          -- s_A (unused by formula)
        (μ.real B)                          -- s_B
        (μ.real C) := by                    -- s_C
  -- Step 1: Unfold abduction to deduction + Bayes inversion
  unfold PLN.plnAbductionStrength PLN.bayesInversion
  -- Step 2: Show the Bayes-inverted premise equals P(C|B)
  -- bayesInversion(P(B|C), P(B), P(C)) = P(B|C) * P(C) / P(B) = P(C|B)
  have hC_real_pos : (0 : ℝ) < μ.real C := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hC_pos,
           lt_top_iff_ne_top.mpr (measure_ne_top μ C)⟩
  have hB_real_pos : (0 : ℝ) < μ.real B := by
    rw [Measure.real, ENNReal.toReal_pos_iff]
    exact ⟨pos_iff_ne_zero.mpr hB_pos,
           lt_top_iff_ne_top.mpr (measure_ne_top μ B)⟩
  -- P(B|C) * P(C) / P(B) = P(B∩C) / P(B) = P(C∩B) / P(B)
  have hBayes : μ.real (B ∩ C) / μ.real C * μ.real C / μ.real B =
      μ.real (C ∩ B) / μ.real B := by
    rw [div_mul_cancel₀ (μ.real (B ∩ C)) (ne_of_gt hC_real_pos)]
    rw [Set.inter_comm B C]
  rw [hBayes]
  -- Step 3: Apply the deduction exactness theorem
  exact PLN.pln_deduction_from_total_probability μ hA hB hC
    hA_pos hB_pos hB_lt1 hAB_pos hABc_pos h_pos_indep h_neg_indep

end Mettapedia.Logic.PLNXiDerivedBNRules
