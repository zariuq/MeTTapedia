import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNWMOSLFBridge
import Mettapedia.Logic.PLNBayesNetFastRules
import Mettapedia.Logic.EvidenceBeta
import Mettapedia.Logic.PLNWorldModelITV

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
      (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
      (AtomQuery.linkCond
        [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
        ⟨Three.C, valC⟩)
      (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
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
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := chainBN))
    (Atom := BNQuery.Atom (bn := chainBN))
    (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩)
    (AtomQuery.linkCond
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
      (AtomQuery.linkCond
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.linkCond
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := chainBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_deduction_rewrite_of_chainBN valA valB valC hLMarkov)
    (xi_deduction_rewrite_of_chainBN_side valA valB valC hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-- Concrete Chapter-9 fixture (chain BN, all events `true`, fixed atom label/pattern):
single-call WM→OSLF threshold endpoint with no generic language/query parameters. -/
theorem xi_deduction_threshold_concrete_true_fixture
    [EventPos (bn := chainBN) Three.B true]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, true⟩, ⟨Three.B, true⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    (hDSep : (CompiledPlan.deductionSide Three.A Three.B Three.C).holds
      (bn := chainBN))
    (W : BNWorldModel.State (bn := chainBN))
    (tau : ℝ≥0∞)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_deduction_rewrite_of_chainBN true true true hLMarkov).derive W)) :
    sem (fun _ _ => False)
      (thresholdAtomSemOfWMQ W tau
        (fun (_ : String) (_ : Pattern) =>
          AtomQuery.linkCond
            [ (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
            , (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)) ]
            (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN))))
      (.atom "q")
      (Pattern.fvar "x") :=
  xi_deduction_threshold_of_chainBN true true true hLMarkov hDSep
    (fun _ _ => False) W tau
    (fun (_ : String) (_ : Pattern) =>
      AtomQuery.linkCond
        [ (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
        , (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)) ]
        (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))
    "q" (Pattern.fvar "x") rfl hTau

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
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
      W (AtomQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
      =
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := chainBN))
      (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
      W (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
  chain_screeningOff_strength_eq_of_dsep
    (valA := valA) (valB := valB) (valC := valC) hLMarkov hDSep W

end ChainBNDeduction

/-! ## §2 Tier B: Bernoulli-PLN Bridge (Measure → Formula)

Connects the measure-level conditional probability `P(C|A)` to the
`plnDeductionStrength` formula. This is a re-export of
`chainBN_plnDeductionStrength_exact` (PLNBayesNetFastRules) with Xi naming,
plus the foundational lemma `toStrength_evidenceOfProb` that links the
WM evidence layer to probability values.

### BinaryEvidence ↔ Probability Bridge

`BNWorldModel` stores evidence as `evidenceOfProb(p) = ⟨p, 1-p⟩` where
`p` is the conditional probability (ENNReal). `BinaryEvidence.toStrength` recovers
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

/-- BinaryEvidence ↔ Probability bridge: `toStrength` of `evidenceOfProb p` recovers `p`
when `p ≤ 1`. This is the foundational lemma connecting WM evidence to probability. -/
theorem toStrength_evidenceOfProb (p : ℝ≥0∞) (hp : p ≤ 1) :
    BinaryEvidence.toStrength (evidenceOfProb p) = p := by
  unfold BinaryEvidence.toStrength evidenceOfProb BinaryEvidence.total
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
    queryProb (bn := chainBN) cpt (AtomQuery.prop ⟨v, true⟩) =
      (μ (cpt := cpt)) (eventTrue v) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq, eventEq_true_eq_eventTrue]
  rfl

/-- queryProb for link at `true` = conditional probability ratio μ(a∩b)/μ(a). -/
private lemma queryProb_link_true_eq
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    queryProb (bn := chainBN) cpt (AtomQuery.link ⟨a, true⟩ ⟨b, true⟩) =
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
    queryProb (bn := chainBN) cpt (AtomQuery.prop ⟨v, true⟩) ≤ 1 := by
  rw [queryProb_prop_true_eq]; exact prob_le_one

private lemma queryProb_link_true_le_one
    (cpt : ChainBN.DiscreteCPT) (a b : Three) :
    queryProb (bn := chainBN) cpt (AtomQuery.link ⟨a, true⟩ ⟨b, true⟩) ≤ 1 := by
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
    (BinaryWorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (AtomQuery.prop (⟨v, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    (μ (cpt := cpt)).real (eventTrue v) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_prop_true_le_one cpt v)]
  rw [queryProb_prop_true_eq]
  simp [Measure.real]

/-- Singleton link queryStrength.toReal = μ.real(b∩a)/μ.real(a).
Note: intersection order is b∩a (not a∩b) to match Tier B convention. -/
private lemma queryStrength_singleton_link_toReal
    (cpt : ChainBN.DiscreteCPT) (a b : Three)
    (ha : (μ (cpt := cpt)) (eventTrue a) ≠ 0) :
    (BinaryWorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := chainBN))
      (AtomQuery.link (⟨a, true⟩ : BNQuery.Atom (bn := chainBN))
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
    (BinaryWorldModel.queryStrength W
      (AtomQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                     (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal =
    plnDeductionStrength
      (BinaryWorldModel.queryStrength W
        (AtomQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN))
                       (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.prop (⟨Three.B, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.prop (⟨Three.C, true⟩ : BNQuery.Atom (bn := chainBN)))).toReal := by
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
      (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
      (AtomQuery.linkCond
        [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
        ⟨Three.C, valC⟩)
      (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
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
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := forkBN))
    (Atom := BNQuery.Atom (bn := forkBN))
    (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩)
    (AtomQuery.linkCond
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
      (AtomQuery.linkCond
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := forkBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.linkCond
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := forkBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.linkCond
      [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]
      ⟨Three.C, valC⟩)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sourceRule_rewrite_of_forkBN valA valB valC hLMarkov)
    (xi_sourceRule_rewrite_of_forkBN_side valA valB valC hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-- Concrete Chapter-9 fixture (fork BN, all events `true`, fixed atom label/pattern):
single-call WM→OSLF threshold endpoint with no generic language/query parameters. -/
theorem xi_sourceRule_threshold_concrete_true_fixture
    [EventPos (bn := forkBN) Three.B true]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, true⟩, ⟨Three.B, true⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    (hDSep : (CompiledPlan.inductionSide Three.A Three.B Three.C).holds
      (bn := forkBN))
    (W : BNWorldModel.State (bn := forkBN))
    (tau : ℝ≥0∞)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sourceRule_rewrite_of_forkBN true true true hLMarkov).derive W)) :
    sem (fun _ _ => False)
      (thresholdAtomSemOfWMQ W tau
        (fun (_ : String) (_ : Pattern) =>
          AtomQuery.linkCond
            [ (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN))
            , (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN)) ]
            (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN))))
      (.atom "q")
      (Pattern.fvar "x") :=
  xi_sourceRule_threshold_of_forkBN true true true hLMarkov hDSep
    (fun _ _ => False) W tau
    (fun (_ : String) (_ : Pattern) =>
      AtomQuery.linkCond
        [ (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN))
        , (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN)) ]
        (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))
    "q" (Pattern.fvar "x") rfl hTau

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
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := forkBN))
      (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
      W (AtomQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
      =
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := forkBN))
      (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
      W (AtomQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) :=
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
    (BinaryWorldModel.queryStrength ({cpt} : BNWorldModel.State (bn := forkBN))
      (AtomQuery.link (⟨a, true⟩ : BNQuery.Atom (bn := forkBN))
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
    (BinaryWorldModel.queryStrength ({cpt} : BNWorldModel.State (bn := forkBN))
      (AtomQuery.prop (⟨v, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal =
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
    (BinaryWorldModel.queryStrength W
      (AtomQuery.link (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN))
                     (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal =
    plnInductionStrength
      (BinaryWorldModel.queryStrength W
        (AtomQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN))
                       (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.link (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN))
                       (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.prop (⟨Three.A, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.prop (⟨Three.B, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal
      (BinaryWorldModel.queryStrength W
        (AtomQuery.prop (⟨Three.C, true⟩ : BNQuery.Atom (bn := forkBN)))).toReal := by
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
      (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
      (AtomQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
      (AtomQuery.prop ⟨Three.B, valB⟩) :=
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
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  dsep_rewrite
    (State := BNWorldModel.State (bn := colliderBN))
    (Atom := BNQuery.Atom (bn := colliderBN))
    (AtomQuery.prop ⟨Three.B, valB⟩)
    (AtomQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
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
      (AtomQuery.link
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := colliderBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link
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
    (enc : String → Pattern → AtomQuery (BNQuery.Atom (bn := colliderBN)))
    (a : String) (p : Pattern)
    (hEnc : enc a p = AtomQuery.link
      ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov).derive W)) :
    sem R
      (thresholdAtomSemOfWMQ W tau enc) (.atom a) p :=
  wmRewriteRule_threshold_atom R
    (xi_sinkRule_rewrite_of_colliderBN valA valB hLMarkov)
    (xi_sinkRule_rewrite_of_colliderBN_side valA valB hLMarkov hDSep)
    W tau enc a p hEnc hTau

/-- Concrete Chapter-9 fixture (collider BN, all events `true`, fixed atom label/pattern):
single-call WM→OSLF threshold endpoint with no generic language/query parameters. -/
theorem xi_sinkRule_threshold_concrete_true_fixture
    [EventPos (bn := colliderBN) Three.A true]
    (hLMarkov : ColliderBNLocalMarkovAll)
    (hDSep : (CompiledPlan.abductionSide Three.A Three.C Three.B).holds
      (bn := colliderBN))
    (W : BNWorldModel.State (bn := colliderBN))
    (tau : ℝ≥0∞)
    (hTau : tau ≤ BinaryEvidence.toStrength
      ((xi_sinkRule_rewrite_of_colliderBN true true hLMarkov).derive W)) :
    sem (fun _ _ => False)
      (thresholdAtomSemOfWMQ W tau
        (fun (_ : String) (_ : Pattern) =>
          AtomQuery.link
            (⟨Three.A, true⟩ : BNQuery.Atom (bn := colliderBN))
            (⟨Three.B, true⟩ : BNQuery.Atom (bn := colliderBN))))
      (.atom "q")
      (Pattern.fvar "x") :=
  xi_sinkRule_threshold_of_colliderBN true true hLMarkov hDSep
    (fun _ _ => False) W tau
    (fun (_ : String) (_ : Pattern) =>
      AtomQuery.link
        (⟨Three.A, true⟩ : BNQuery.Atom (bn := colliderBN))
        (⟨Three.B, true⟩ : BNQuery.Atom (bn := colliderBN)))
    "q" (Pattern.fvar "x") rfl hTau

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
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
      W (AtomQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
      =
    BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
      W (AtomQuery.prop ⟨Three.B, valB⟩) :=
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
    (BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
      W (AtomQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)).toReal
      =
    (BinaryWorldModel.queryStrength
      (State := BNWorldModel.State (bn := colliderBN))
      (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
      W (AtomQuery.prop ⟨Three.B, valB⟩)).toReal :=
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
    queryProb (bn := colliderBN) cpt (AtomQuery.prop ⟨v, val⟩) =
      cpt.jointMeasure (eventEq (bn := colliderBN) v val) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq]

omit
  [(v : Three) → Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace] in
private lemma collider_queryProb_prop_le_one
    (cpt : colliderBN.DiscreteCPT) (v : Three) (val : Bool) :
    queryProb (bn := colliderBN) cpt (AtomQuery.prop ⟨v, val⟩) ≤ 1 := by
  rw [collider_queryProb_prop_eq]; exact MeasureTheory.prob_le_one

omit
  [(v : Three) → Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
  [StandardBorelSpace colliderBN.JointSpace] in
private lemma collider_queryStrength_singleton_prop_toReal
    (cpt : colliderBN.DiscreteCPT) (v : Three) (val : Bool) :
    (BinaryWorldModel.queryStrength
      ({cpt} : BNWorldModel.State (bn := colliderBN))
      (AtomQuery.prop (⟨v, val⟩ : BNQuery.Atom (bn := colliderBN)))).toReal =
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


namespace Mettapedia.Logic.PLNXiDerivedBNRules.Typed

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNBNCompilation
open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

noncomputable section

/-! ## Generic Unit-Sort Lift -/

instance instWorldModelSigmaUnit
    (State Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State PUnit (fun _ : PUnit => Query) where
  evidence W q := BinaryWorldModel.evidence W q.2
  evidence_add W₁ W₂ q := BinaryWorldModel.evidence_add W₁ W₂ q.2
  evidence_zero q := BinaryWorldModel.evidence_zero q.2

/-- Lift an untyped WM rewrite rule into the typed WM layer with one sort. -/
noncomputable def wmRewriteRuleToSigmaUnit
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (r : WMRewriteRule State Query) :
    WorldModelSigma.WMRewriteRuleSigma State PUnit (fun _ : PUnit => Query) where
  side := r.side
  conclusion := ⟨PUnit.unit, r.conclusion⟩
  derive := r.derive
  sound := by
    intro hSide W
    simpa using (r.sound hSide W)

@[simp] theorem wmRewriteRuleToSigmaUnit_side
    {State Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (r : WMRewriteRule State Query) :
    (wmRewriteRuleToSigmaUnit r).side = r.side := rfl

/-! ## Generic Constant-Family Lift (non-`PUnit`) -/

/-- Constant-family typed WM adapter from an untyped WM.
This is kept as a non-instance to avoid global instance-coherence pressure. -/
def worldModelSigmaConstFromUntyped
    (State Srt Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Srt (fun _ : Srt => Query) where
  evidence W q := BinaryWorldModel.evidence W q.2
  evidence_add W₁ W₂ q := BinaryWorldModel.evidence_add W₁ W₂ q.2
  evidence_zero q := BinaryWorldModel.evidence_zero q.2

/-- Convenience type alias for non-`PUnit` constant-family typed rewrite rules. -/
abbrev WMRewriteRuleSigmaConst
    (State Srt Query : Type*)
    [EvidenceType State] [BinaryWorldModel State Query] : Type _ :=
  @WorldModelSigma.WMRewriteRuleSigma
    State Srt (fun _ : Srt => Query)
    (inferInstance : EvidenceType State)
    (worldModelSigmaConstFromUntyped (State := State) (Srt := Srt) (Query := Query))

/-- Lift an untyped WM rewrite rule into any fixed-sort constant-family WMΣ layer. -/
noncomputable def wmRewriteRuleToSigmaConst
    {State Srt Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Srt)
    (r : WMRewriteRule State Query) :
    WMRewriteRuleSigmaConst State Srt Query := by
  letI : WorldModelSigma State Srt (fun _ : Srt => Query) :=
    worldModelSigmaConstFromUntyped (State := State) (Srt := Srt) (Query := Query)
  exact
    { side := r.side
      conclusion := ⟨s0, r.conclusion⟩
      derive := r.derive
      sound := by
        intro hSide W
        simpa using (r.sound hSide W) }

@[simp] theorem wmRewriteRuleToSigmaConst_side
    {State Srt Query : Type*}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Srt)
    (r : WMRewriteRule State Query) :
    letI : WorldModelSigma State Srt (fun _ : Srt => Query) :=
      worldModelSigmaConstFromUntyped (State := State) (Srt := Srt) (Query := Query)
    (wmRewriteRuleToSigmaConst (State := State) (Srt := Srt) (Query := Query) s0 r).side = r.side := rfl

/-! ## Generic Indexed Dependent Lift (non-constant family) -/

/-- Sort-indexed wrapper with a genuinely dependent codomain. -/
inductive IndexedQuery (Srt Query : Type) : Srt → Type where
  | mk : Query → IndexedQuery Srt Query s

namespace IndexedQuery

def erase {Srt Query : Type} : {s : Srt} → IndexedQuery Srt Query s → Query
  | _, .mk q => q

def ofIndex {Srt Query : Type} (s : Srt) (q : Query) : IndexedQuery Srt Query s :=
  .mk q

end IndexedQuery

/-- Local dependent WMΣ adapter over an arbitrary sort index from an untyped WM. -/
def worldModelSigmaIndexedFromUntyped
    (State Srt Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Srt (IndexedQuery Srt Query) where
  evidence W q := BinaryWorldModel.evidence W (IndexedQuery.erase q.2)
  evidence_add W₁ W₂ q := BinaryWorldModel.evidence_add W₁ W₂ (IndexedQuery.erase q.2)
  evidence_zero q := BinaryWorldModel.evidence_zero (IndexedQuery.erase q.2)

instance instWorldModelSigmaIndexed
    (State Srt Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Srt (IndexedQuery Srt Query) :=
  worldModelSigmaIndexedFromUntyped (State := State) (Srt := Srt) (Query := Query)

/-- Convenience type alias for indexed-dependent typed rewrite rules. -/
abbrev WMRewriteRuleSigmaIndexed
    (State Srt Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] : Type _ :=
  @WorldModelSigma.WMRewriteRuleSigma
    State Srt (IndexedQuery Srt Query)
    (inferInstance : EvidenceType State)
    (worldModelSigmaIndexedFromUntyped (State := State) (Srt := Srt) (Query := Query))

/-- Lift an untyped WM rewrite rule into index-dependent WMΣ form. -/
noncomputable def wmRewriteRuleToSigmaIndexed
    {State Srt Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Srt)
    (r : WMRewriteRule State Query) :
    WMRewriteRuleSigmaIndexed State Srt Query := by
  letI : WorldModelSigma State Srt (IndexedQuery Srt Query) :=
    worldModelSigmaIndexedFromUntyped (State := State) (Srt := Srt) (Query := Query)
  exact
    { side := r.side
      conclusion := ⟨s0, IndexedQuery.ofIndex s0 r.conclusion⟩
      derive := r.derive
      sound := by
        intro hSide W
        simpa [IndexedQuery.ofIndex, worldModelSigmaIndexedFromUntyped,
          IndexedQuery.erase] using (r.sound hSide W) }

@[simp] theorem wmRewriteRuleToSigmaIndexed_side
    {State Srt Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Srt)
    (r : WMRewriteRule State Query) :
    letI : WorldModelSigma State Srt (IndexedQuery Srt Query) :=
      worldModelSigmaIndexedFromUntyped (State := State) (Srt := Srt) (Query := Query)
    (wmRewriteRuleToSigmaIndexed (State := State) (Srt := Srt) (Query := Query) s0 r).side = r.side := rfl

/-! ## Native Three-Sort Dependent Prototype (no `erase` bridge) -/

/-- Native query family indexed by `Three` (prototype):
same payload type at each sort, but with a true dependent family and no erase helper. -/
def ThreeNativeQueryFamily (Query : Type) : Three → Type
  | .A => Query
  | .B => Query
  | .C => Query

namespace ThreeNativeQueryFamily

def ofSort {Query : Type} (s : Three) (q : Query) : ThreeNativeQueryFamily Query s :=
  match s with
  | .A => q
  | .B => q
  | .C => q

end ThreeNativeQueryFamily

/-- Native `WorldModelSigma` over `ThreeNativeQueryFamily` (prototype, no erase). -/
def worldModelSigmaThreeNativeFromUntyped
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Three (ThreeNativeQueryFamily Query) where
  evidence W q := by
    cases q with
    | mk s qs =>
        cases s <;>
          exact BinaryWorldModel.evidence (State := State) (Query := Query) W qs
  evidence_add W₁ W₂ q := by
    cases q with
    | mk s qs =>
        cases s <;>
          simpa using (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ qs)
  evidence_zero q := by
    cases q with
    | mk s qs =>
        cases s <;>
          simpa using (BinaryWorldModel.evidence_zero (State := State) (Query := Query) qs)

/-- Global native `Three`-indexed WMΣ instance (no erase bridge). -/
instance instWorldModelSigmaThreeNative
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Three (ThreeNativeQueryFamily Query) :=
  worldModelSigmaThreeNativeFromUntyped (State := State) (Query := Query)

/-- Native `Three`-sorted typed rewrite-rule alias (prototype, no erase). -/
abbrev WMRewriteRuleSigmaThreeNative
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] : Type _ :=
  @WorldModelSigma.WMRewriteRuleSigma
    State Three (ThreeNativeQueryFamily Query)
    (inferInstance : EvidenceType State)
    (worldModelSigmaThreeNativeFromUntyped (State := State) (Query := Query))

/-- Lift an untyped rewrite rule into native `Three`-sorted WMΣ form (prototype). -/
noncomputable def wmRewriteRuleToSigmaThreeNative
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Three)
    (r : WMRewriteRule State Query) :
    WMRewriteRuleSigmaThreeNative State Query := by
  letI : WorldModelSigma State Three (ThreeNativeQueryFamily Query) :=
    worldModelSigmaThreeNativeFromUntyped (State := State) (Query := Query)
  exact
    { side := r.side
      conclusion := ⟨s0, ThreeNativeQueryFamily.ofSort s0 r.conclusion⟩
      derive := r.derive
      sound := by
        intro hSide W
        cases s0 <;>
          simpa [ThreeNativeQueryFamily.ofSort, worldModelSigmaThreeNativeFromUntyped] using
            (r.sound hSide W) }

@[simp] theorem wmRewriteRuleToSigmaThreeNative_side
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Three)
    (r : WMRewriteRule State Query) :
    letI : WorldModelSigma State Three (ThreeNativeQueryFamily Query) :=
      worldModelSigmaThreeNativeFromUntyped (State := State) (Query := Query)
    (wmRewriteRuleToSigmaThreeNative (State := State) (Query := Query) s0 r).side = r.side := rfl

/-! ## Native Three-Sort Tagged Prototype (no adapter bridge) -/

/-- Native sort-distinguished query family over `Three`:
the codomain is genuinely dependent and constructor-distinguished by sort. -/
inductive ThreeNativeTaggedQueryFamily (Query : Type) : Three → Type where
  | atA : Query → ThreeNativeTaggedQueryFamily Query .A
  | atB : Query → ThreeNativeTaggedQueryFamily Query .B
  | atC : Query → ThreeNativeTaggedQueryFamily Query .C

namespace ThreeNativeTaggedQueryFamily

def ofSort {Query : Type} (s : Three) (q : Query) : ThreeNativeTaggedQueryFamily Query s :=
  match s with
  | .A => .atA q
  | .B => .atB q
  | .C => .atC q

end ThreeNativeTaggedQueryFamily

/-- Native `WorldModelSigma` over `ThreeNativeTaggedQueryFamily` (no erase bridge). -/
def worldModelSigmaThreeNativeTaggedFromUntyped
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Three (ThreeNativeTaggedQueryFamily Query) where
  evidence W q := by
    cases q with
    | mk _ qs =>
        cases qs with
        | atA qa => exact BinaryWorldModel.evidence (State := State) (Query := Query) W qa
        | atB qb => exact BinaryWorldModel.evidence (State := State) (Query := Query) W qb
        | atC qc => exact BinaryWorldModel.evidence (State := State) (Query := Query) W qc
  evidence_add W₁ W₂ q := by
    cases q with
    | mk _ qs =>
        cases qs with
        | atA qa =>
            simpa using
              (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ qa)
        | atB qb =>
            simpa using
              (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ qb)
        | atC qc =>
            simpa using
              (BinaryWorldModel.evidence_add (State := State) (Query := Query) W₁ W₂ qc)
  evidence_zero q := by
    cases q with
    | mk _ qs =>
        cases qs with
        | atA qa =>
            simpa using
              (BinaryWorldModel.evidence_zero (State := State) (Query := Query) qa)
        | atB qb =>
            simpa using
              (BinaryWorldModel.evidence_zero (State := State) (Query := Query) qb)
        | atC qc =>
            simpa using
              (BinaryWorldModel.evidence_zero (State := State) (Query := Query) qc)

/-- Global native `Three`-indexed WMΣ instance for `ThreeNativeTaggedQueryFamily`. -/
instance instWorldModelSigmaThreeNativeTagged
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State Three (ThreeNativeTaggedQueryFamily Query) :=
  worldModelSigmaThreeNativeTaggedFromUntyped (State := State) (Query := Query)

/-- Native `Three`-sorted typed rewrite-rule alias for `ThreeNativeTaggedQueryFamily`. -/
abbrev WMRewriteRuleSigmaThreeNativeTagged
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] : Type _ :=
  @WorldModelSigma.WMRewriteRuleSigma
    State Three (ThreeNativeTaggedQueryFamily Query)
    (inferInstance : EvidenceType State)
    (worldModelSigmaThreeNativeTaggedFromUntyped (State := State) (Query := Query))

/-- Lift an untyped rewrite rule into native tagged `Three`-sorted WMΣ form. -/
noncomputable def wmRewriteRuleToSigmaThreeNativeTagged
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Three)
    (r : WMRewriteRule State Query) :
    WMRewriteRuleSigmaThreeNativeTagged State Query := by
  letI : WorldModelSigma State Three (ThreeNativeTaggedQueryFamily Query) :=
    worldModelSigmaThreeNativeTaggedFromUntyped (State := State) (Query := Query)
  exact
    { side := r.side
      conclusion := ⟨s0, ThreeNativeTaggedQueryFamily.ofSort s0 r.conclusion⟩
      derive := r.derive
      sound := by
        intro hSide W
        cases s0 <;>
          simpa [ThreeNativeTaggedQueryFamily.ofSort,
            worldModelSigmaThreeNativeTaggedFromUntyped] using
            (r.sound hSide W) }

@[simp] theorem wmRewriteRuleToSigmaThreeNativeTagged_side
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : Three)
    (r : WMRewriteRule State Query) :
    letI : WorldModelSigma State Three (ThreeNativeTaggedQueryFamily Query) :=
      worldModelSigmaThreeNativeTaggedFromUntyped (State := State) (Query := Query)
    (wmRewriteRuleToSigmaThreeNativeTagged (State := State) (Query := Query) s0 r).side = r.side := rfl

/-! ## Generic Sort-Tagged Dependent Lift (non-constant family) -/

abbrev MeTTaSortTag := Mettapedia.Logic.PLNWMOSLFBridgeTyped.MeTTaTypeOf.SortTag

/-- Sort-indexed wrapper with genuinely dependent codomain (one constructor per sort). -/
inductive SortTaggedQuery (Query : Type) : MeTTaSortTag → Type where
  | state : Query → SortTaggedQuery Query .state
  | instr : Query → SortTaggedQuery Query .instr
  | atom : Query → SortTaggedQuery Query .atom
  | space : Query → SortTaggedQuery Query .space

namespace SortTaggedQuery

def erase {Query : Type} : {s : MeTTaSortTag} → SortTaggedQuery Query s → Query
  | _, .state q => q
  | _, .instr q => q
  | _, .atom q => q
  | _, .space q => q

def ofSort {Query : Type} (s : MeTTaSortTag) (q : Query) : SortTaggedQuery Query s :=
  match s with
  | .state => .state q
  | .instr => .instr q
  | .atom => .atom q
  | .space => .space q

end SortTaggedQuery

/-- Local dependent WMΣ adapter over OSLF sort tags from an untyped WM. -/
def worldModelSigmaSortTaggedFromUntyped
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State MeTTaSortTag (SortTaggedQuery Query) where
  evidence W q := BinaryWorldModel.evidence W (SortTaggedQuery.erase q.2)
  evidence_add W₁ W₂ q := BinaryWorldModel.evidence_add W₁ W₂ (SortTaggedQuery.erase q.2)
  evidence_zero q := BinaryWorldModel.evidence_zero (SortTaggedQuery.erase q.2)

/-- Global OSLF sort-tagged dependent WMΣ instance from an untyped WM. -/
instance instWorldModelSigmaSortTagged
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] :
    WorldModelSigma State MeTTaSortTag (SortTaggedQuery Query) :=
  worldModelSigmaSortTaggedFromUntyped (State := State) (Query := Query)

/-- Convenience type alias for sort-tagged dependent typed rewrite rules. -/
abbrev WMRewriteRuleSigmaSortTagged
    (State Query : Type)
    [EvidenceType State] [BinaryWorldModel State Query] : Type _ :=
  @WorldModelSigma.WMRewriteRuleSigma
    State MeTTaSortTag (SortTaggedQuery Query)
    (inferInstance : EvidenceType State)
    (worldModelSigmaSortTaggedFromUntyped (State := State) (Query := Query))

/-- Lift an untyped WM rewrite rule into sort-tagged dependent WMΣ form. -/
noncomputable def wmRewriteRuleToSigmaSortTagged
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : MeTTaSortTag)
    (r : WMRewriteRule State Query) :
    WMRewriteRuleSigmaSortTagged State Query := by
  letI : WorldModelSigma State MeTTaSortTag (SortTaggedQuery Query) :=
    worldModelSigmaSortTaggedFromUntyped (State := State) (Query := Query)
  exact
    { side := r.side
      conclusion := ⟨s0, SortTaggedQuery.ofSort s0 r.conclusion⟩
      derive := r.derive
      sound := by
        intro hSide W
        cases s0 <;>
          simpa [SortTaggedQuery.ofSort, worldModelSigmaSortTaggedFromUntyped,
            SortTaggedQuery.erase] using (r.sound hSide W) }

@[simp] theorem wmRewriteRuleToSigmaSortTagged_side
    {State Query : Type}
    [EvidenceType State] [BinaryWorldModel State Query]
    (s0 : MeTTaSortTag)
    (r : WMRewriteRule State Query) :
    letI : WorldModelSigma State MeTTaSortTag (SortTaggedQuery Query) :=
      worldModelSigmaSortTaggedFromUntyped (State := State) (Query := Query)
    (wmRewriteRuleToSigmaSortTagged (State := State) (Query := Query) s0 r).side = r.side := rfl

/-! ## Chain BN Deduction -/

section ChainBNDeduction

local instance : DecidableRel chainBN.graph.edges := fun a b =>
  Classical.propDecidable (chainBN.graph.edges a b)

variable
  [∀ v : Three, Inhabited (chainBN.stateSpace v)]
  [∀ v : Three, Fintype (chainBN.stateSpace v)]
  [∀ v : Three, DecidableEq (chainBN.stateSpace v)]

/-- Lift a chain-BN untyped rewrite rule into one-sort typed WM form. -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := chainBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaUnit r

/-- Lift a chain-BN untyped rewrite rule into direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_three
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := chainBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaConst
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    s0 r

/-- Lift a chain-BN untyped rewrite rule into native `Three`-indexed WMΣ form
(prototype, no erase bridge). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_threeNative
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaThreeNative
    (State := BNWorldModel.State (bn := chainBN))
    (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    s0 r

/-- Lift a chain-BN untyped rewrite rule into native tagged `Three`-indexed WMΣ form
(prototype, no adapter bridge). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_threeNativeTagged
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaThreeNativeTagged
    (State := BNWorldModel.State (bn := chainBN))
    (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    s0 r

/-- Lift a chain-BN untyped rewrite rule into direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_dep
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := chainBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaIndexed
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    s0 r

/-- Lift a chain-BN untyped rewrite rule into OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_sortTag
    (s0 : MeTTaSortTag)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN)))) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  wmRewriteRuleToSigmaSortTagged
    (State := BNWorldModel.State (bn := chainBN))
    (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    s0 r

/-- Concrete typed chain-BN deduction rewrite, obtained directly from the
untyped BN constructor and lifted to one-sort WMΣ form. -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := chainBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed chain-BN deduction rewrite in direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete_three
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := chainBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma_three s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed chain-BN deduction rewrite in native `Three`-indexed WMΣ form
(prototype, no erase bridge). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma_threeNative s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed chain-BN deduction rewrite in native tagged `Three`-indexed WMΣ form
(prototype, no adapter bridge). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma_threeNativeTagged s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed chain-BN deduction rewrite in direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := chainBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma_dep s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed chain-BN deduction rewrite in OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
    (s0 : MeTTaSortTag)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))) :=
  xi_deduction_rewrite_of_chainBN_sigma_sortTag s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_deduction_rewrite_of_chainBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete chain-BN typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_applyITV_bayesExact95
    (ctx : BinaryContext)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN)))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete
          (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN)))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN)))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete
          (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := chainBN)))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN indexed-dependent typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_dep_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN indexed-dependent typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_dep_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN native-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN native-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN native-tagged-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN native-tagged-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := chainBN)}
    (hSide :
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN sort-tagged typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : MeTTaSortTag)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    letI : WorldModelSigma
      (BNWorldModel.State (bn := chainBN))
      MeTTaSortTag
      (SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN)))) :=
      worldModelSigmaSortTaggedFromUntyped
        (State := BNWorldModel.State (bn := chainBN))
        (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    ∀ {W : BNWorldModel.State (bn := chainBN)},
      (hSide :
        (xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side) →
      (hW : WMJudgment W) →
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := MeTTaSortTag)
      (Query := SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) := by
  intro W hSide hW
  letI : WorldModelSigma
      (BNWorldModel.State (bn := chainBN))
      MeTTaSortTag
      (SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN)))) :=
    worldModelSigmaSortTaggedFromUntyped
      (State := BNWorldModel.State (bn := chainBN))
      (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
  exact WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := MeTTaSortTag)
    (Query := SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete chain-BN sort-tagged typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : MeTTaSortTag)
    (valA valB valC : Bool)
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ChainBNLocalMarkovAll) :
    letI : WorldModelSigma
      (BNWorldModel.State (bn := chainBN))
      MeTTaSortTag
      (SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN)))) :=
      worldModelSigmaSortTaggedFromUntyped
        (State := BNWorldModel.State (bn := chainBN))
        (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
    ∀ {W : BNWorldModel.State (bn := chainBN)},
      (hSide :
        (xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side) →
      (hW : WMJudgment W) →
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := chainBN))
      (Srt := MeTTaSortTag)
      (Query := SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) := by
  intro W hSide hW
  letI : WorldModelSigma
      (BNWorldModel.State (bn := chainBN))
      MeTTaSortTag
      (SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN)))) :=
    worldModelSigmaSortTaggedFromUntyped
      (State := BNWorldModel.State (bn := chainBN))
      (Query := AtomQuery (BNQuery.Atom (bn := chainBN)))
  exact WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := chainBN))
    (Srt := MeTTaSortTag)
    (Query := SortTaggedQuery (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (r := xi_deduction_rewrite_of_chainBN_sigma_concrete_sortTag
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

omit [∀ v : Three, Inhabited (chainBN.stateSpace v)] in
theorem xi_deduction_rewrite_of_chainBN_sigma_side
    (r : WMRewriteRule
      (BNWorldModel.State (bn := chainBN))
      (AtomQuery (BNQuery.Atom (bn := chainBN))))
    (hSide : r.side) :
    (xi_deduction_rewrite_of_chainBN_sigma r).side := by
  simpa [xi_deduction_rewrite_of_chainBN_sigma] using hSide

end ChainBNDeduction

/-! ## Fork BN Source Rule -/

section ForkBNSourceRule

local instance : DecidableRel forkBN.graph.edges := fun a b =>
  Classical.propDecidable (forkBN.graph.edges a b)

variable
  [∀ v : Three, Fintype (forkBN.stateSpace v)]
  [∀ v : Three, DecidableEq (forkBN.stateSpace v)]

/-- Lift a fork-BN untyped rewrite rule into one-sort typed WM form. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := forkBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaUnit r

/-- Lift a fork-BN untyped rewrite rule into direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_three
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := forkBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaConst
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
    s0 r

/-- Lift a fork-BN untyped rewrite rule into native `Three`-indexed WMΣ form
(no erase bridge). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_threeNative
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaThreeNative
    (State := BNWorldModel.State (bn := forkBN))
    (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
    s0 r

/-- Lift a fork-BN untyped rewrite rule into native tagged `Three`-indexed WMΣ form
(no adapter bridge). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_threeNativeTagged
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaThreeNativeTagged
    (State := BNWorldModel.State (bn := forkBN))
    (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
    s0 r

/-- Lift a fork-BN untyped rewrite rule into direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_dep
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := forkBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaIndexed
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
    s0 r

/-- Lift a fork-BN untyped rewrite rule into OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_sortTag
    (s0 : MeTTaSortTag)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN)))) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  wmRewriteRuleToSigmaSortTagged
    (State := BNWorldModel.State (bn := forkBN))
    (Query := AtomQuery (BNQuery.Atom (bn := forkBN)))
    s0 r

/-- Concrete typed fork-BN source-rule rewrite, obtained directly from the
untyped BN constructor and lifted to one-sort WMΣ form. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := forkBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed fork-BN source-rule rewrite in direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete_three
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := forkBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma_three s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed fork-BN source-rule rewrite in native `Three`-indexed WMΣ form
(no erase bridge). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma_threeNative s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed fork-BN source-rule rewrite in native tagged `Three`-indexed WMΣ form
(no adapter bridge). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma_threeNativeTagged s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed fork-BN source-rule rewrite in direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := forkBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma_dep s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete typed fork-BN source-rule rewrite in OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_sourceRule_rewrite_of_forkBN_sigma_concrete_sortTag
    (s0 : MeTTaSortTag)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))) :=
  xi_sourceRule_rewrite_of_forkBN_sigma_sortTag s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sourceRule_rewrite_of_forkBN
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)

/-- Concrete fork-BN typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_applyITV_bayesExact95
    (ctx : BinaryContext)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN)))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete
          (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN)))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN)))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete
        (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete
          (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := forkBN)))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete
      (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN indexed-dependent typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN indexed-dependent typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN native-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN native-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN native-tagged-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

/-- Concrete fork-BN native-tagged-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB valC : Bool)
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLMarkov : ForkBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := forkBN)}
    (hSide :
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := forkBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := forkBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (r := xi_sourceRule_rewrite_of_forkBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) (valC := valC) hLMarkov)
    ctx hSide hW

theorem xi_sourceRule_rewrite_of_forkBN_sigma_side
    (r : WMRewriteRule
      (BNWorldModel.State (bn := forkBN))
      (AtomQuery (BNQuery.Atom (bn := forkBN))))
    (hSide : r.side) :
    (xi_sourceRule_rewrite_of_forkBN_sigma r).side := by
  simpa [xi_sourceRule_rewrite_of_forkBN_sigma] using hSide

end ForkBNSourceRule

/-! ## Collider BN Sink Rule -/

section ColliderBNSinkRule

local instance : DecidableRel colliderBN.graph.edges := fun a b =>
  Classical.propDecidable (colliderBN.graph.edges a b)

variable
  [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
  [∀ v : Three, Fintype (colliderBN.stateSpace v)]
  [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]

/-- Lift a collider-BN untyped rewrite rule into one-sort typed WM form. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := colliderBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaUnit r

/-- Lift a collider-BN untyped rewrite rule into direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_three
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := colliderBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaConst
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
    s0 r

/-- Lift a collider-BN untyped rewrite rule into native `Three`-indexed WMΣ form
(no erase bridge). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_threeNative
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaThreeNative
    (State := BNWorldModel.State (bn := colliderBN))
    (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
    s0 r

/-- Lift a collider-BN untyped rewrite rule into native tagged `Three`-indexed WMΣ form
(no adapter bridge). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_threeNativeTagged
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaThreeNativeTagged
    (State := BNWorldModel.State (bn := colliderBN))
    (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
    s0 r

/-- Lift a collider-BN untyped rewrite rule into direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_dep
    (s0 : Three)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := colliderBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaIndexed
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
    s0 r

/-- Lift a collider-BN untyped rewrite rule into OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_sortTag
    (s0 : MeTTaSortTag)
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN)))) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  wmRewriteRuleToSigmaSortTagged
    (State := BNWorldModel.State (bn := colliderBN))
    (Query := AtomQuery (BNQuery.Atom (bn := colliderBN)))
    s0 r

/-- Concrete typed collider-BN sink-rule rewrite, obtained directly from the
untyped BN constructor and lifted to one-sort WMΣ form. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WorldModelSigma.WMRewriteRuleSigma
      (BNWorldModel.State (bn := colliderBN))
      PUnit
      (fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete typed collider-BN sink-rule rewrite in direct sort-indexed WMΣ form
(`Srt = Three`, constant query family). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_three
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRuleSigmaConst
      (BNWorldModel.State (bn := colliderBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma_three s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete typed collider-BN sink-rule rewrite in native `Three`-indexed WMΣ form
(no erase bridge). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNative
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma_threeNative s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete typed collider-BN sink-rule rewrite in native tagged `Three`-indexed WMΣ form
(no adapter bridge). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRuleSigmaThreeNativeTagged
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma_threeNativeTagged s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete typed collider-BN sink-rule rewrite in direct index-dependent WMΣ form
(`Srt = Three`, dependent family via `IndexedQuery`). -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRuleSigmaIndexed
      (BNWorldModel.State (bn := colliderBN))
      Three
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma_dep s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete typed collider-BN sink-rule rewrite in OSLF sort-tagged dependent WMΣ form. -/
noncomputable def xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_sortTag
    (s0 : MeTTaSortTag)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll) :
    WMRewriteRuleSigmaSortTagged
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))) :=
  xi_sinkRule_rewrite_of_colliderBN_sigma_sortTag s0
    (Mettapedia.Logic.PLNXiDerivedBNRules.xi_sinkRule_rewrite_of_colliderBN
      (valA := valA) (valB := valB) hLMarkov)

/-- Concrete collider-BN typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_applyITV_bayesExact95
    (ctx : BinaryContext)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
        (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN)))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
        (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
          (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN)))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
      (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
        (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := PUnit)
      (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN)))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
        (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
          (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := PUnit)
    (Query := fun _ : PUnit => AtomQuery (BNQuery.Atom (bn := colliderBN)))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete
      (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN indexed-dependent typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN indexed-dependent typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := IndexedQuery Three (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_dep
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN native-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN native-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := ThreeNativeQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNative
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN native-tagged-Three typed rewrite admits an exact-Bayes ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged_applyITV_bayesExact95
    (ctx : BinaryContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.bayesCredibleExact95 ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.bayesCredibleExact95.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_bayesExact95
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

/-- Concrete collider-BN native-tagged-Three typed rewrite admits a Walley-IDM ITV judgment lift. -/
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged_applyITV_walleyIDM
    (ctx : IDMPredictiveContext)
    (s0 : Three)
    (valA valB : Bool)
    [EventPos (bn := colliderBN) Three.A valA]
    (hLMarkov : ColliderBNLocalMarkovAll)
    {W : BNWorldModel.State (bn := colliderBN)}
    (hSide :
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).side)
    (hW : WMJudgment W) :
    WorldModelSigma.WMITVJudgmentSigma
      (State := BNWorldModel.State (bn := colliderBN))
      (Srt := Three)
      (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
      ITVSemantics.walleyIDMPredictive ctx
      W
      (xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
        (s0 := s0) (valA := valA) (valB := valB) hLMarkov).conclusion
      (ITVSemantics.walleyIDMPredictive.eval ctx
        ((xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
          (s0 := s0) (valA := valA) (valB := valB) hLMarkov).derive W)) :=
  WorldModelSigma.WMRewriteRuleSigma.applyITV_walleyIDM
    (State := BNWorldModel.State (bn := colliderBN))
    (Srt := Three)
    (Query := ThreeNativeTaggedQueryFamily (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (r := xi_sinkRule_rewrite_of_colliderBN_sigma_concrete_threeNativeTagged
      (s0 := s0) (valA := valA) (valB := valB) hLMarkov)
    ctx hSide hW

omit [∀ v : Three, Inhabited (colliderBN.stateSpace v)] in
theorem xi_sinkRule_rewrite_of_colliderBN_sigma_side
    (r : WMRewriteRule
      (BNWorldModel.State (bn := colliderBN))
      (AtomQuery (BNQuery.Atom (bn := colliderBN))))
    (hSide : r.side) :
    (xi_sinkRule_rewrite_of_colliderBN_sigma r).side := by
  simpa [xi_sinkRule_rewrite_of_colliderBN_sigma] using hSide

end ColliderBNSinkRule

end

end Mettapedia.Logic.PLNXiDerivedBNRules.Typed
