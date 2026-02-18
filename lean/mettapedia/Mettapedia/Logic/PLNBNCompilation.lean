import Mettapedia.Logic.PLNLinkCalculus
import Mettapedia.Logic.PLNWorldModelCalculus
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.VEBridge
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness
import Mettapedia.ProbabilityTheory.BayesianNetworks.ScreeningOffFromCondIndep
import Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-!
# PLN → BN Compilation (Query Plans + Structural Side Conditions)

This module defines a **compilation layer** that turns classic PLN rule patterns
into **Bayesian-network query plans**, together with explicit **d-separation side
conditions** (Σ obligations).

Key idea:
- We do **not** claim global link-level completeness.
- Instead, we compile PLN rules into *BN queries* plus *structural* conditions
  (d-sep / Markov) that, when discharged, justify the fast rule rewrites.

References:
- Pearl, *Probabilistic Reasoning in Intelligent Systems*, Ch. 3 (d-separation)
- Koller & Friedman, *Probabilistic Graphical Models*, Ch. 3
- Goertzel et al., *Probabilistic Logic Networks* (PLN rule patterns)
-/

namespace Mettapedia.Logic.PLNBNCompilation

open scoped Classical ENNReal

open MeasureTheory ProbabilityTheory

open Mettapedia.Logic.PLNLinkCalculus
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

variable {V : Type*}

/-! ## BN Queries -/

/-- A BN query used by compiled PLN rules: propositions and links at concrete values. -/
inductive BNQuery (bn : BayesianNetwork V) where
  | prop : (v : V) → bn.stateSpace v → BNQuery bn
  | link : (a b : V) → bn.stateSpace a → bn.stateSpace b → BNQuery bn

namespace BNQuery

variable (bn : BayesianNetwork V)

/-- Evaluate a BN query via variable elimination (exact for the BN model class). -/
noncomputable def evalVE (cpt : bn.DiscreteCPT) [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    BNQuery bn → ENNReal
  | .prop v val => BayesianNetwork.propProbVE (bn := bn) cpt v val
  | .link a b valA valB => BayesianNetwork.linkProbVE (bn := bn) cpt a b valA valB

/-- BN value-labeled atom (vertex + concrete value). -/
abbrev Atom : Type _ := Σ v : V, bn.stateSpace v

/-- BNQuery as a PLNQuery over value-labeled atoms. -/
def toPLNQuery : BNQuery bn → PLNQuery (Atom bn)
  | .prop v val => PLNQuery.prop ⟨v, val⟩
  | .link a b valA valB => PLNQuery.link ⟨a, valA⟩ ⟨b, valB⟩

end BNQuery

/-! ## Structural side conditions (Σ obligations) -/

/-- A d-separation obligation packaged as data (later discharged structurally). -/
structure DSeparationCond (V : Type*) where
  X : Set V
  Y : Set V
  Z : Set V

namespace DSeparationCond

variable (bn : BayesianNetwork V)

/-- Interpretation: the condition holds in `bn` when `X ⟂ Y | Z` by d-separation. -/
def holds (cond : DSeparationCond V) : Prop :=
  DSeparatedFull bn.graph cond.X cond.Y cond.Z

/-- Full trail-based side condition. -/
def holdsFull (cond : DSeparationCond V) : Prop :=
  cond.holds (bn := bn)

end DSeparationCond

/-! ## BN World-Model: VE-based evidence extraction -/

namespace BNWorldModel

variable {bn : BayesianNetwork V}
variable [DecidableRel bn.graph.edges]
variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]

abbrev Atom : Type _ := BNQuery.Atom (bn := bn)

abbrev State : Type _ := Multiset (bn.DiscreteCPT)

noncomputable def evidenceOfProb (p : ℝ≥0∞) : Evidence :=
  ⟨p, 1 - p⟩

noncomputable def queryProb [Fintype V] [DecidableEq V] (cpt : bn.DiscreteCPT) :
    PLNQuery (BNQuery.Atom (bn := bn)) → ℝ≥0∞
  | .prop ⟨v, val⟩ =>
      BayesianNetwork.propProbVE (bn := bn) cpt v val
  | .link ⟨a, valA⟩ ⟨b, valB⟩ =>
      BayesianNetwork.linkProbVE (bn := bn) cpt a b valA valB
  | .linkCond as ⟨b, valB⟩ =>
      BayesianNetwork.linkProbVECond (bn := bn) cpt as ⟨b, valB⟩

noncomputable def queryEvidence [Fintype V] [DecidableEq V] (cpt : bn.DiscreteCPT)
    (q : PLNQuery (BNQuery.Atom (bn := bn))) : Evidence :=
  evidenceOfProb (queryProb (bn := bn) cpt q)

noncomputable def evidence [Fintype V] [DecidableEq V] (W : State (bn := bn))
    (q : PLNQuery (BNQuery.Atom (bn := bn))) : Evidence :=
  (W.map (fun cpt => queryEvidence (bn := bn) cpt q)).sum

instance : AddCommMonoid (State (bn := bn)) := by
  dsimp [State]
  infer_instance

instance : EvidenceType (State (bn := bn)) :=
  { toAddCommMonoid := inferInstance }

noncomputable instance [Fintype V] [DecidableEq V] :
    WorldModel (State (bn := bn)) (PLNQuery (BNQuery.Atom (bn := bn))) where
  evidence W q := evidence (bn := bn) W q
  evidence_add W₁ W₂ q := by
    classical
    let f := fun cpt => queryEvidence (bn := bn) cpt q
    have h :
        (Multiset.map f (W₁ + W₂)).sum =
          (Multiset.map f W₁).sum + (Multiset.map f W₂).sum := by
      rw [Multiset.map_add, Multiset.sum_add]
    dsimp [evidence]
    exact h

/-! ### Singleton-CPT bridge -/

/-- For a singleton-CPT state, evidence reduces to the single CPT's evidence. -/
lemma evidence_singleton [Fintype V] [DecidableEq V]
    (cpt : bn.DiscreteCPT)
    (q : PLNQuery (BNQuery.Atom (bn := bn))) :
    evidence (bn := bn) ({cpt} : Multiset (bn.DiscreteCPT)) q =
      queryEvidence (bn := bn) cpt q := by
  unfold evidence
  simp [Multiset.map_singleton, Multiset.sum_singleton]

/-- For a singleton-CPT state, `queryStrength` equals `queryProb`.
This bridges the WM evidence layer to the probability layer.
Requires `queryProb cpt q ≤ 1` (a probability bound). -/
theorem queryStrength_singleton_eq_queryProb [Fintype V] [DecidableEq V]
    (cpt : bn.DiscreteCPT) (q : PLNQuery (BNQuery.Atom (bn := bn)))
    (hq : queryProb (bn := bn) cpt q ≤ 1) :
    WorldModel.queryStrength
      ({cpt} : Multiset (bn.DiscreteCPT)) q =
      queryProb (bn := bn) cpt q := by
  unfold WorldModel.queryStrength
  have hev : WorldModel.evidence ({cpt} : Multiset (bn.DiscreteCPT)) q =
      queryEvidence (bn := bn) cpt q := by
    show evidence (bn := bn) ({cpt} : Multiset (bn.DiscreteCPT)) q = _
    exact evidence_singleton cpt q
  rw [hev]
  show Evidence.toStrength (evidenceOfProb (queryProb (bn := bn) cpt q)) = _
  -- toStrength (evidenceOfProb p) = p when p ≤ 1
  unfold Evidence.toStrength evidenceOfProb Evidence.total
  simp only
  split
  · rename_i h
    have : queryProb (bn := bn) cpt q + (1 - queryProb (bn := bn) cpt q) = 1 := by
      rw [add_comm]; exact tsub_add_cancel_of_le hq
    rw [this] at h; exact absurd h one_ne_zero
  · have : queryProb (bn := bn) cpt q + (1 - queryProb (bn := bn) cpt q) = 1 := by
      rw [add_comm]; exact tsub_add_cancel_of_le hq
    rw [this]; exact div_one _

/-! ### Bool-generic queryProb ↔ jointMeasure bridge lemmas

These work for *any* BN and any state values, using `eventEq` throughout.
They connect `queryProb` (VE-based) to `cpt.jointMeasure` (measure-based). -/

-- These lemmas provide their own type-class params to be maximally generic
/-- `queryProb` for prop at any `val` = marginal measure. -/
lemma queryProb_prop_eq_jointMeasure [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v) :
    queryProb (bn := bn) cpt (PLNQuery.prop ⟨v, val⟩) =
      cpt.jointMeasure (eventEq (bn := bn) v val) := by
  simp only [queryProb]
  rw [propProbVE_eq_jointMeasure_eventEq]

/-- `queryProb` for link at any `valA`, `valB` = conditional probability ratio. -/
lemma queryProb_link_eq_jointMeasure [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    (ha : cpt.jointMeasure (eventEq (bn := bn) a valA) ≠ 0) :
    queryProb (bn := bn) cpt (PLNQuery.link ⟨a, valA⟩ ⟨b, valB⟩) =
      cpt.jointMeasure (eventEq (bn := bn) a valA ∩ eventEq (bn := bn) b valB) /
        cpt.jointMeasure (eventEq (bn := bn) a valA) := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  split_ifs with h
  · exact absurd h ha
  · rfl

/-- `queryProb` for prop is at most 1. -/
lemma queryProb_prop_le_one [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [IsProbabilityMeasure cpt.jointMeasure] :
    queryProb (bn := bn) cpt (PLNQuery.prop ⟨v, val⟩) ≤ 1 := by
  rw [queryProb_prop_eq_jointMeasure]; exact prob_le_one

/-- `queryProb` for link is at most 1. -/
lemma queryProb_link_le_one [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b) :
    queryProb (bn := bn) cpt (PLNQuery.link ⟨a, valA⟩ ⟨b, valB⟩) ≤ 1 := by
  simp only [queryProb]
  rw [linkProbVE_eq_jointMeasure_eventEq]
  split
  · exact zero_le_one
  · exact le_trans (ENNReal.div_le_div_right (measure_mono Set.inter_subset_left) _)
      ENNReal.div_self_le_one

/-- Singleton prop `queryStrength.toReal` = `μ.real(eventEq v val)`. -/
lemma queryStrength_singleton_prop_toReal [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (v : V) (val : bn.stateSpace v)
    [IsProbabilityMeasure cpt.jointMeasure] :
    (WorldModel.queryStrength
      ({cpt} : State (bn := bn))
      (PLNQuery.prop (⟨v, val⟩ : BNQuery.Atom (bn := bn)))).toReal =
    cpt.jointMeasure.real (eventEq (bn := bn) v val) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_prop_le_one cpt v val)]
  rw [queryProb_prop_eq_jointMeasure]
  simp [Measure.real]

/-- Singleton link `queryStrength.toReal` = μ.real ratio.
Note: intersection order is `eventEq b valB ∩ eventEq a valA` to match
the convention where the numerator event is listed first. -/
lemma queryStrength_singleton_link_toReal [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]
    [∀ v, MeasurableSingletonClass (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [DecidableRel bn.graph.edges]
    (cpt : bn.DiscreteCPT) (a b : V) (valA : bn.stateSpace a) (valB : bn.stateSpace b)
    (ha : cpt.jointMeasure (eventEq (bn := bn) a valA) ≠ 0) :
    (WorldModel.queryStrength
      ({cpt} : State (bn := bn))
      (PLNQuery.link (⟨a, valA⟩ : BNQuery.Atom (bn := bn))
                     (⟨b, valB⟩ : BNQuery.Atom (bn := bn)))).toReal =
    cpt.jointMeasure.real (eventEq (bn := bn) b valB ∩ eventEq (bn := bn) a valA) /
      cpt.jointMeasure.real (eventEq (bn := bn) a valA) := by
  rw [queryStrength_singleton_eq_queryProb _ _ (queryProb_link_le_one cpt a b valA valB)]
  rw [queryProb_link_eq_jointMeasure cpt a b valA valB ha]
  rw [Set.inter_comm (eventEq (bn := bn) a valA) (eventEq (bn := bn) b valB)]
  rw [ENNReal.toReal_div]
  simp [Measure.real]

lemma wmqueryeq_of_prob_eq
    [Fintype V] [DecidableEq V]
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    (h : ∀ cpt : bn.DiscreteCPT, queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂) :
    WMQueryEq (State := State (bn := bn))
      (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro W
  classical
  let f₁ := fun cpt => queryEvidence (bn := bn) cpt q₁
  let f₂ := fun cpt => queryEvidence (bn := bn) cpt q₂
  have hmap : Multiset.map f₁ W = Multiset.map f₂ W := by
    refine Multiset.map_congr rfl ?_
    intro cpt _hcpt
    have : queryEvidence (bn := bn) cpt q₁ = queryEvidence (bn := bn) cpt q₂ := by
      simp [queryEvidence, evidenceOfProb, h cpt]
    dsimp [f₁, f₂]
    exact this
  simp [WorldModel.evidence, evidence, f₁, f₂, hmap]

lemma wmqueryeq_of_dsep
    [Fintype V] [DecidableEq V]
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    (h : cond.holds (bn := bn) → ∀ cpt : bn.DiscreteCPT,
      queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂) :
    cond.holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn) q₁ q₂ (h hcond)

lemma wmqueryeq_of_dsepFull
    [Fintype V] [DecidableEq V]
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    (h : cond.holdsFull (bn := bn) → ∀ cpt : bn.DiscreteCPT,
      queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂) :
    cond.holdsFull (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn) q₁ q₂ (h hcond)

end BNWorldModel

/-! ## WM rewrite bridge (Σ = d-separation) -/

namespace WMRewriteBridge

variable (bn : BayesianNetwork V)

abbrev BNAtom : Type _ := BNQuery.Atom (bn := bn)

variable {State : Type*} [Mettapedia.Logic.EvidenceClass.EvidenceType State]
  [WorldModel State (PLNQuery (BNAtom bn))]

/-- D-separation condition as a Σ side-condition for WM rewrites. -/
def SigmaOfDsep (cond : DSeparationCond V) : Prop :=
  cond.holds (bn := bn)

/-- Turn a d-separation condition into a WM rewrite rule (query-equivalence form). -/
def rewrite_of_dsep
    (cond : DSeparationCond V) (q₁ q₂ : PLNQuery (BNAtom bn))
    (h : SigmaOfDsep (bn := bn) cond →
      WMQueryEq (State := State) (Query := PLNQuery (BNAtom bn)) q₁ q₂) :
    WMRewriteRule State (PLNQuery (BNAtom bn)) :=
  dsep_rewrite (State := State) (Atom := BNAtom bn) q₁ q₂ (SigmaOfDsep (bn := bn) cond) h

end WMRewriteBridge

/-! ## PLN rule patterns (fast rules) -/

/-- The classic PLN rule kinds. -/
inductive RuleKind
  | deduction
  | induction
  | abduction
  deriving DecidableEq, Repr

/-- A concrete rule instance over a BN: variables and their target values. -/
structure RuleInstance (bn : BayesianNetwork V) where
  kind : RuleKind
  A : V
  B : V
  C : V
  valA : bn.stateSpace A
  valB : bn.stateSpace B
  valC : bn.stateSpace C

/-! ## Compiled query plans -/

/-- A compiled BN query plan with explicit Σ side conditions. -/
structure CompiledPlan (bn : BayesianNetwork V) where
  queries : List (BNQuery bn)
  sideCond : DSeparationCond V

namespace CompiledPlan

variable {bn : BayesianNetwork V}

/-- Deduction side condition: A and C are d-separated by {B}. -/
def deductionSide (A B C : V) : DSeparationCond V :=
  ⟨{A}, {C}, {B}⟩

/-- Induction (SourceRule) side condition: A and C are d-separated by {B}. -/
def inductionSide (A B C : V) : DSeparationCond V :=
  ⟨{A}, {C}, {B}⟩

/-- Abduction (SinkRule) side condition: A and C are d-separated by ∅. -/
def abductionSide (A _B C : V) : DSeparationCond V :=
  ⟨{A}, {C}, ∅⟩

/-- Compile a PLN rule instance into a BN query plan and Σ side condition. -/
def compile (bn : BayesianNetwork V) (inst : RuleInstance bn) : CompiledPlan bn :=
  match inst.kind with
  | .deduction =>
      { queries :=
          [ BNQuery.prop (bn := bn) inst.A inst.valA
          , BNQuery.prop (bn := bn) inst.B inst.valB
          , BNQuery.prop (bn := bn) inst.C inst.valC
          , BNQuery.link (bn := bn) inst.A inst.B inst.valA inst.valB
          , BNQuery.link (bn := bn) inst.B inst.C inst.valB inst.valC
          ]
        sideCond := deductionSide inst.A inst.B inst.C }
  | .induction =>
      { queries :=
          [ BNQuery.prop (bn := bn) inst.A inst.valA
          , BNQuery.prop (bn := bn) inst.B inst.valB
          , BNQuery.prop (bn := bn) inst.C inst.valC
          , BNQuery.link (bn := bn) inst.B inst.A inst.valB inst.valA
          , BNQuery.link (bn := bn) inst.B inst.C inst.valB inst.valC
          ]
        sideCond := inductionSide inst.A inst.B inst.C }
  | .abduction =>
      { queries :=
          [ BNQuery.prop (bn := bn) inst.A inst.valA
          , BNQuery.prop (bn := bn) inst.B inst.valB
          , BNQuery.prop (bn := bn) inst.C inst.valC
          , BNQuery.link (bn := bn) inst.A inst.B inst.valA inst.valB
          , BNQuery.link (bn := bn) inst.C inst.B inst.valC inst.valB
          ]
        sideCond := abductionSide inst.A inst.B inst.C }

end CompiledPlan

/-! ## Evaluating compiled plans (exact VE) -/

namespace CompiledPlan

variable {bn : BayesianNetwork V}

noncomputable def evalVE (plan : CompiledPlan bn) (cpt : bn.DiscreteCPT)
    [Fintype V] [DecidableEq V]
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : List ENNReal :=
  plan.queries.map (BNQuery.evalVE (bn := bn) cpt)

end CompiledPlan

/-! ## Compiled-plan rewrites (BN WorldModel instance) -/

namespace BNCompiledRewrite

open BNWorldModel
open WMRewriteBridge

variable {bn : BayesianNetwork V}
variable [Fintype V] [DecidableEq V]
variable [DecidableRel bn.graph.edges]
variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)]

/-- Turn a compiled BN plan into a WM rewrite rule for a chosen conclusion query. -/
noncomputable def fromPlan
    (plan : CompiledPlan bn)
    (conclusion : BNQuery bn)
    (h :
      plan.sideCond.holds (bn := bn) →
        WMQueryEq
          (State := State (bn := bn))
          (Query := PLNQuery (BNQuery.Atom (bn := bn)))
          (BNQuery.toPLNQuery (bn := bn) conclusion)
          (BNQuery.toPLNQuery (bn := bn) conclusion)) :
    WMRewriteRule (State (bn := bn)) (PLNQuery (BNQuery.Atom (bn := bn))) :=
  rewrite_of_dsep (bn := bn) (State := State (bn := bn))
    plan.sideCond
    (BNQuery.toPLNQuery (bn := bn) conclusion)
    (BNQuery.toPLNQuery (bn := bn) conclusion)
    h

end BNCompiledRewrite

/-! ## Discharging Σ via d-separation soundness -/

namespace DSeparationCond

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {bn : BayesianNetwork V}
variable [Fintype V] [DecidableEq V]
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
variable [HasLocalMarkovProperty bn μ]
variable [DSeparationSoundness bn μ]

/-- If the d-separation obligation holds, we can discharge it as conditional independence. -/
theorem discharge
    (cond : DSeparationCond V)
    (hcond : cond.holds (bn := bn)) :
    CondIndepVertices bn μ cond.X cond.Y cond.Z :=
  dsepFull_implies_condIndepVertices (bn := bn) (μ := μ) hcond

/-- Full trail-based discharge. -/
theorem dischargeFull
    (cond : DSeparationCond V)
    (hcond : cond.holdsFull (bn := bn)) :
    CondIndepVertices bn μ cond.X cond.Y cond.Z :=
  dsepFull_implies_condIndepVertices (bn := bn) (μ := μ) hcond

/-- d-separation discharge specialized to a BN CPT's joint measure. -/
theorem discharge_cpt
    (cond : DSeparationCond V) (cpt : bn.DiscreteCPT)
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
    [HasLocalMarkovProperty bn cpt.jointMeasure]
    [DSeparationSoundness bn cpt.jointMeasure]
    (hcond : cond.holds (bn := bn)) :
    CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z :=
  dsepFull_implies_condIndepVertices (bn := bn) (μ := cpt.jointMeasure) hcond

end DSeparationCond

/-! ## WMQueryEq from d-separation discharge -/

namespace BNWorldModel

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {bn : BayesianNetwork V}
variable [Fintype V] [DecidableEq V]
variable [DecidableRel bn.graph.edges]
variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
variable [∀ v, DecidableEq (bn.stateSpace v)]
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
variable [HasLocalMarkovProperty bn μ]
variable [DSeparationSoundness bn μ]

/-! ## CondIndep → QueryEq (parameterized interface) -/

/-- A parameterized interface: conditional independence implies query equality.

This keeps bridge lemmas **explicitly assumption-bound** and avoids conflating
PLN-typicality with classical quantifier readings. -/
class CondIndepQueryEq
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn))) : Prop where
  prob_eq :
    ∀ cpt : bn.DiscreteCPT,
      CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z →
        queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂

instance condIndepQueryEq_refl
    (cond : DSeparationCond V)
    (q : PLNQuery (BNQuery.Atom (bn := bn))) :
    CondIndepQueryEq (bn := bn) cond q q :=
  ⟨by intro _cpt _c; rfl⟩

/-! ## Screening-off instance (explicit assumptions)

This is the **non-degenerate** template we can wire into `WMRewriteRule`s.
It is intentionally *assumption-guarded*: providing an instance amounts to
supplying the semantic proof (typically using conditional independence +
positivity of the conditioning event).

This keeps the ontological layers distinct:
- `CondIndepVertices` is the semantic side condition (d-sep discharge);
- `ScreeningOffProbEq` is the explicit proof obligation linking that condition
  to the query equality we want.
- The rewrite layer then becomes executable when such an instance exists.
-/

class ScreeningOffProbEq
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C) : Prop where
  /-- Under conditional independence (and any necessary positivity assumptions),
  the conditional-link queries agree. -/
  prob_eq :
    ∀ cpt : bn.DiscreteCPT,
      CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V) →
        queryProb (bn := bn) cpt
          (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
        queryProb (bn := bn) cpt
          (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)

instance condIndepQueryEq_screeningOff
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [ScreeningOffProbEq (bn := bn) A B C valA valB valC] :
    CondIndepQueryEq (bn := bn)
      (cond := CompiledPlan.deductionSide A B C)
      (q₁ := PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
      (q₂ := PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) :=
  ⟨by
    intro cpt hci
    exact ScreeningOffProbEq.prob_eq (bn := bn) (A := A) (B := B) (C := C)
      (valA := valA) (valB := valB) (valC := valC) cpt hci⟩

/-- Use d-separation discharge to obtain a WMQueryEq, given a cond-indep ⇒ prob-eq lemma. -/
theorem wmqueryeq_of_dsep_discharge
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    (hprob :
      ∀ cpt : bn.DiscreteCPT,
        CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z →
          queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂)
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        cond.holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z) :
    cond.holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn) q₁ q₂ (fun cpt =>
    hprob cpt (hci cpt hcond))

theorem wmqueryeq_of_dsepFull_discharge
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    (hprob :
      ∀ cpt : bn.DiscreteCPT,
        CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z →
          queryProb (bn := bn) cpt q₁ = queryProb (bn := bn) cpt q₂)
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        cond.holdsFull (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z) :
    cond.holdsFull (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn) q₁ q₂ (fun cpt =>
    hprob cpt (hci cpt hcond))

/-! ## WMQueryEq from d-sep + CondIndepQueryEq instance -/

theorem wmqueryeq_of_dsep_discharge_class
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    [CondIndepQueryEq (bn := bn) cond q₁ q₂]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        cond.holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z) :
    cond.holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn) q₁ q₂ (fun cpt =>
    CondIndepQueryEq.prob_eq (bn := bn) (cond := cond) cpt (hci cpt hcond))

theorem wmqueryeq_of_dsep_discharge_via_soundness
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    [CondIndepQueryEq (bn := bn) cond q₁ q₂]
    [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
    (hLM : ∀ cpt : bn.DiscreteCPT, HasLocalMarkovProperty bn cpt.jointMeasure)
    (hSound : ∀ cpt : bn.DiscreteCPT, DSeparationSoundness bn cpt.jointMeasure) :
    cond.holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn))) q₁ q₂ := by
  exact wmqueryeq_of_dsep_discharge_class (bn := bn) (cond := cond) (q₁ := q₁) (q₂ := q₂)
    (hci := fun cpt hcond => by
      letI : HasLocalMarkovProperty bn cpt.jointMeasure := hLM cpt
      letI : DSeparationSoundness bn cpt.jointMeasure := hSound cpt
      exact DSeparationCond.discharge_cpt (bn := bn) (cond := cond) (cpt := cpt) hcond)

/-! ## Concrete cond-indep → linkProb equality (degenerate equality) -/

/-! ## Explicit event-independence assumptions (non-degenerate rewrite) -/

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

section EventIndep

/-- Positivity assumption for a conditioning event. -/
class EventPos
    (A : V) (valA : bn.stateSpace A) : Prop where
  pos :
    ∀ cpt : bn.DiscreteCPT,
      cpt.jointMeasure (eventEq (bn := bn) A valA) ≠ 0

/-- Positivity assumption for a list of constraints. -/
class EventPosConstraints
    (cs : List (Σ v : V, bn.stateSpace v)) : Prop where
  pos :
    ∀ cpt : bn.DiscreteCPT,
      cpt.jointMeasure (eventOfConstraints (bn := bn) cs) ≠ 0

/-- Explicit screening-off equality on joint measures. -/
class ScreeningOffEventEq
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C) : Prop where
  mul_eq :
    ∀ cpt : bn.DiscreteCPT,
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩
            eventEq (bn := bn) C valC ∩
            eventEq (bn := bn) B valB) *
        cpt.jointMeasure (eventEq (bn := bn) B valB) =
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩
            eventEq (bn := bn) B valB) *
        cpt.jointMeasure
          (eventEq (bn := bn) C valC ∩
            eventEq (bn := bn) B valB)

lemma linkProbVE_eq_propProbVE_of_condIndep
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A C : V) (valA : bn.stateSpace A) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    (hci : CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ∅)
    (hpos : cpt.jointMeasure (eventEq (bn := bn) A valA) ≠ 0) :
    queryProb (bn := bn) cpt
      (PLNQuery.link ⟨A, valA⟩ ⟨C, valC⟩) =
    queryProb (bn := bn) cpt
      (PLNQuery.prop ⟨C, valC⟩) := by
  -- Rewrite VE queries to joint-measure form.
  have hlink :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.linkProbVE_eq_jointMeasure_eventEq
      (bn := bn) (cpt := cpt) A C valA valC
  have hprop :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.propProbVE_eq_jointMeasure_eventEq
      (bn := bn) (cpt := cpt) C valC
  have hindep :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.condIndepVertices_eventEq_mul
      (bn := bn) (μ := cpt.jointMeasure) A C valA valC hci
  have hne_top :
      cpt.jointMeasure (eventEq (bn := bn) A valA) ≠ ∞ :=
    MeasureTheory.measure_ne_top (μ := cpt.jointMeasure) (s := eventEq (bn := bn) A valA)
  -- Compute the ratio under independence and positivity.
  dsimp [queryProb]
  calc
    BayesianNetwork.linkProbVE (bn := bn) cpt A C valA valC
        =
      if cpt.jointMeasure (eventEq (bn := bn) A valA) = 0 then 0 else
        cpt.jointMeasure
            (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) C valC) /
          cpt.jointMeasure (eventEq (bn := bn) A valA) := hlink
    _ =
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) C valC) /
        cpt.jointMeasure (eventEq (bn := bn) A valA) := by
          simp [hpos]
    _ =
      (cpt.jointMeasure (eventEq (bn := bn) A valA) *
        cpt.jointMeasure (eventEq (bn := bn) C valC)) /
        cpt.jointMeasure (eventEq (bn := bn) A valA) := by
          simp [hindep]
    _ =
      cpt.jointMeasure (eventEq (bn := bn) C valC) := by
          -- Use commutativity to cancel the conditioning event.
          have := ENNReal.mul_div_cancel_right
            (a := cpt.jointMeasure (eventEq (bn := bn) C valC))
            (b := cpt.jointMeasure (eventEq (bn := bn) A valA)) hpos hne_top
          simpa [mul_comm] using this
    _ = BayesianNetwork.propProbVE (bn := bn) cpt C valC := hprop.symm

omit [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma linkProbVECond_eq_linkProbVE_of_mul_eq
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    (hmul :
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩
            eventEq (bn := bn) C valC ∩
            eventEq (bn := bn) B valB) *
        cpt.jointMeasure (eventEq (bn := bn) B valB) =
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩
            eventEq (bn := bn) B valB) *
        cpt.jointMeasure
          (eventEq (bn := bn) C valC ∩
            eventEq (bn := bn) B valB)) :
    queryProb (bn := bn) cpt
      (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
    queryProb (bn := bn) cpt
      (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  have hlinkCond :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.linkProbVECond_eq_jointMeasure_eventOfConstraints
        (bn := bn) (cpt := cpt)
        (constraints := [⟨A, valA⟩, ⟨B, valB⟩]) (b := ⟨C, valC⟩)
  have hlink :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.linkProbVE_eq_jointMeasure_eventEq
      (bn := bn) (cpt := cpt) B C valB valC
  have hposB := EventPos.pos (bn := bn) (A := B) (valA := valB) cpt
  have hposAB :=
    EventPosConstraints.pos (bn := bn) (cs := [⟨A, valA⟩, ⟨B, valB⟩]) cpt
  have hposAB' :
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) B valB) ≠ 0 := by
    simpa [BayesianNetwork.eventOfConstraints_cons, BayesianNetwork.eventOfConstraints_nil,
      Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hposAB
  have hB_top :
      cpt.jointMeasure (eventEq (bn := bn) B valB) ≠ ∞ :=
    MeasureTheory.measure_ne_top (μ := cpt.jointMeasure) (s := eventEq (bn := bn) B valB)
  have hAB_top :
      cpt.jointMeasure
          (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) B valB) ≠ ∞ := by
    exact
      MeasureTheory.measure_ne_top (μ := cpt.jointMeasure)
        (s := eventEq (bn := bn) A valA ∩ eventEq (bn := bn) B valB)
  dsimp [queryProb]
  have hlinkCond' :
      BayesianNetwork.linkProbVECond (bn := bn) cpt [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩ =
        cpt.jointMeasure
            (eventEq (bn := bn) A valA ∩
              eventEq (bn := bn) B valB ∩
              eventEq (bn := bn) C valC) /
          cpt.jointMeasure
            (eventEq (bn := bn) A valA ∩
              eventEq (bn := bn) B valB) := by
    have h' := hlinkCond
    simp [hposAB', BayesianNetwork.eventOfConstraints_cons, BayesianNetwork.eventOfConstraints_nil] at h'
    simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using h'
  have hlink' :
      BayesianNetwork.linkProbVE (bn := bn) cpt B C valB valC =
        cpt.jointMeasure
            (eventEq (bn := bn) B valB ∩
              eventEq (bn := bn) C valC) /
          cpt.jointMeasure (eventEq (bn := bn) B valB) := by
    have h' := hlink
    simp [hposB] at h'
    simpa [Set.inter_comm] using h'
  calc
    BayesianNetwork.linkProbVECond (bn := bn) cpt [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩
        = cpt.jointMeasure
            (eventEq (bn := bn) A valA ∩
              eventEq (bn := bn) B valB ∩
              eventEq (bn := bn) C valC) /
          cpt.jointMeasure
            (eventEq (bn := bn) A valA ∩
              eventEq (bn := bn) B valB) := hlinkCond'
    _ =
        cpt.jointMeasure
            (eventEq (bn := bn) B valB ∩
              eventEq (bn := bn) C valC) /
          cpt.jointMeasure (eventEq (bn := bn) B valB) := by
          have hmul' :
              cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB ∩
                    eventEq (bn := bn) C valC) *
                cpt.jointMeasure (eventEq (bn := bn) B valB) =
              cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB) *
                cpt.jointMeasure
                  (eventEq (bn := bn) B valB ∩
                    eventEq (bn := bn) C valC) := by
            simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm] using hmul
          have hcancel₁ :=
            ENNReal.mul_div_mul_right
              (a := cpt.jointMeasure
                (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) B valB ∩ eventEq (bn := bn) C valC))
              (b := cpt.jointMeasure (eventEq (bn := bn) A valA ∩ eventEq (bn := bn) B valB))
              (hc := hposB) (hc' := hB_top)
          have hcancel₂ :=
            ENNReal.mul_div_mul_left
              (a := cpt.jointMeasure (eventEq (bn := bn) B valB ∩ eventEq (bn := bn) C valC))
              (b := cpt.jointMeasure (eventEq (bn := bn) B valB))
              (hc := hposAB') (hc' := hAB_top)
          calc
            cpt.jointMeasure
                (eventEq (bn := bn) A valA ∩
                  eventEq (bn := bn) B valB ∩
                  eventEq (bn := bn) C valC) /
              cpt.jointMeasure
                (eventEq (bn := bn) A valA ∩
                  eventEq (bn := bn) B valB)
                =
              (cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB ∩
                    eventEq (bn := bn) C valC) *
                cpt.jointMeasure (eventEq (bn := bn) B valB)) /
              (cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB) *
                cpt.jointMeasure (eventEq (bn := bn) B valB)) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel₁.symm
            _ =
              (cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB) *
                cpt.jointMeasure
                  (eventEq (bn := bn) B valB ∩
                    eventEq (bn := bn) C valC)) /
              (cpt.jointMeasure
                  (eventEq (bn := bn) A valA ∩
                    eventEq (bn := bn) B valB) *
                cpt.jointMeasure (eventEq (bn := bn) B valB)) := by
                simp [hmul']
            _ =
              cpt.jointMeasure
                  (eventEq (bn := bn) B valB ∩
                    eventEq (bn := bn) C valC) /
                cpt.jointMeasure (eventEq (bn := bn) B valB) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hcancel₂
    _ = BayesianNetwork.linkProbVE (bn := bn) cpt B C valB valC := by
          simp [hlink']

omit [∀ v : V, StandardBorelSpace (bn.stateSpace v)] in
lemma linkProbVECond_eq_linkProbVE_of_eventEq_mul
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    [ScreeningOffEventEq (bn := bn) A B C valA valB valC] :
    queryProb (bn := bn) cpt
      (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
    queryProb (bn := bn) cpt
      (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  have hmul :=
    ScreeningOffEventEq.mul_eq (bn := bn) (A := A) (B := B) (C := C)
      (valA := valA) (valB := valB) (valC := valC) cpt
  exact linkProbVECond_eq_linkProbVE_of_mul_eq (bn := bn)
    (A := A) (B := B) (C := C)
    (valA := valA) (valB := valB) (valC := valC)
    (cpt := cpt) hmul

lemma linkProbVECond_eq_linkProbVE_of_condIndepVertices
    [∀ v : V, Inhabited (bn.stateSpace v)]
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    (hci : CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    queryProb (bn := bn) cpt
      (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
    queryProb (bn := bn) cpt
      (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  have hcond :
      Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.CondIndepOn
        (bn := bn) (μ := cpt.jointMeasure) A B C := by
    simpa [Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.CondIndepOn,
      Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.CondIndepVertices] using hci
  have hmul :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.condIndep_eventEq_mul_cond
      (bn := bn) (μ := cpt.jointMeasure)
      (A := A) (B := B) (C := C)
      (valA := valA) (valB := valB) (valC := valC) hcond
  exact linkProbVECond_eq_linkProbVE_of_mul_eq (bn := bn)
    (A := A) (B := B) (C := C)
    (valA := valA) (valB := valB) (valC := valC)
    (cpt := cpt) hmul

lemma linkProbVECond_eq_linkProbVE_of_condIndepVertices_CA
    [∀ v : V, Inhabited (bn.stateSpace v)]
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    (hciCA : CondIndepVertices bn cpt.jointMeasure ({C} : Set V) ({A} : Set V) ({B} : Set V)) :
    queryProb (bn := bn) cpt
      (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
    queryProb (bn := bn) cpt
      (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  have hci :
      CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V) :=
    condIndepVertices_symm (bn := bn) (μ := cpt.jointMeasure) hciCA
  exact linkProbVECond_eq_linkProbVE_of_condIndepVertices (bn := bn)
    (A := A) (B := B) (C := C)
    (valA := valA) (valB := valB) (valC := valC)
    (cpt := cpt) hci

instance screeningOffProbEq_of_eventEq_mul
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    [ScreeningOffEventEq (bn := bn) A B C valA valB valC] :
    ScreeningOffProbEq (bn := bn) A B C valA valB valC :=
  ⟨by
    intro cpt _hci
    exact linkProbVECond_eq_linkProbVE_of_eventEq_mul
      (bn := bn) (A := A) (B := B) (C := C)
      (valA := valA) (valB := valB) (valC := valC) (cpt := cpt)⟩

theorem screeningOffMulEq_of_condIndepVertices_CA
    [∀ v : V, Inhabited (bn.stateSpace v)]
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (cpt : bn.DiscreteCPT)
    (hciCA : CondIndepVertices bn cpt.jointMeasure ({C} : Set V) ({A} : Set V) ({B} : Set V)) :
    cpt.jointMeasure
        (eventEq (bn := bn) A valA ∩
          eventEq (bn := bn) C valC ∩
          eventEq (bn := bn) B valB) *
      cpt.jointMeasure (eventEq (bn := bn) B valB) =
    cpt.jointMeasure
        (eventEq (bn := bn) A valA ∩
          eventEq (bn := bn) B valB) *
      cpt.jointMeasure
        (eventEq (bn := bn) C valC ∩
          eventEq (bn := bn) B valB) := by
  have hciCA' :
      Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.CondIndepOn
        (bn := bn) (μ := cpt.jointMeasure) C B A := by
    simpa [Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.CondIndepOn] using
      hciCA
  have hmulCA :=
    Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork.condIndep_eventEq_mul_cond
      (bn := bn) (μ := cpt.jointMeasure)
      (A := C) (B := B) (C := A)
      (valA := valC) (valB := valB) (valC := valA) hciCA'
  simpa [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm, mul_comm, mul_left_comm, mul_assoc]
    using hmulCA

instance condIndepQueryEq_abduction_link_prop
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valC : bn.stateSpace C)
    [EventPos (bn := bn) A valA] :
    CondIndepQueryEq (bn := bn)
      (cond := CompiledPlan.abductionSide A B C)
      (q₁ := PLNQuery.link ⟨A, valA⟩ ⟨C, valC⟩)
      (q₂ := PLNQuery.prop ⟨C, valC⟩) :=
  ⟨by
    intro cpt hci
    exact linkProbVE_eq_propProbVE_of_condIndep (bn := bn)
      (A := A) (C := C) (valA := valA) (valC := valC)
      (cpt := cpt) hci (EventPos.pos (bn := bn) (A := A) (valA := valA) cpt)⟩

instance condIndepQueryEq_deduction_linkCond_link
    [∀ v : V, Inhabited (bn.stateSpace v)]
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]] :
    CondIndepQueryEq (bn := bn)
      (cond := CompiledPlan.deductionSide A B C)
      (q₁ := PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
      (q₂ := PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) :=
  ⟨by
    intro cpt hci
    have hciCA :
        CondIndepVertices bn cpt.jointMeasure ({C} : Set V) ({A} : Set V) ({B} : Set V) :=
      condIndepVertices_symm (bn := bn) (μ := cpt.jointMeasure) hci
    have hmul :=
      screeningOffMulEq_of_condIndepVertices_CA (bn := bn)
        (A := A) (B := B) (C := C) (valA := valA) (valB := valB) (valC := valC)
        (cpt := cpt) hciCA
    exact linkProbVECond_eq_linkProbVE_of_mul_eq (bn := bn)
      (A := A) (B := B) (C := C)
      (valA := valA) (valB := valB) (valC := valC)
      (cpt := cpt) hmul⟩

end EventIndep

omit [∀ v, Nonempty (bn.stateSpace v)] in
theorem condIndep_linkProb_eq_of_eq
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (hAB : A = B) (hval : HEq valB valA) :
    CondIndepVertices bn μ ({A} : Set V) ({C} : Set V) ({B} : Set V) →
      ∀ cpt : bn.DiscreteCPT,
        queryProb (bn := bn) cpt
          (PLNQuery.link ⟨A, valA⟩ ⟨C, valC⟩) =
        queryProb (bn := bn) cpt
          (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  intro _hci cpt
  cases hAB
  cases hval
  rfl

/-! ## Screening-off WMQueryEq (d-sep discharge + concrete lemma) -/

theorem wmqueryeq_screeningOff_of_dsep
    (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
    [HasLocalMarkovProperty bn μ] [DSeparationSoundness bn μ]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [ScreeningOffProbEq (bn := bn) A B C valA valB valC]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    (CompiledPlan.deductionSide A B C).holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn)))
        (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
        (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  exact wmqueryeq_of_dsep_discharge_class (bn := bn)
    (cond := CompiledPlan.deductionSide A B C)
    (q₁ := PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
    (q₂ := PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)
    hci

/-- Deduction-pattern WMQueryEq: d-sep discharge + a cond-indep ⇒ prob-eq lemma. -/
theorem wmqueryeq_screeningOff_of_dsep_with
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    (hprob :
      ∀ cpt : bn.DiscreteCPT,
        CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V) →
          queryProb (bn := bn) cpt
            (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩) =
          queryProb (bn := bn) cpt
            (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩))
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    (CompiledPlan.deductionSide A B C).holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn)))
        (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
        (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn)
    (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
    (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)
    (fun cpt => hprob cpt (hci cpt hcond))

theorem wmqueryeq_screeningOff_of_dsep_CA
    [∀ v : V, Inhabited (bn.stateSpace v)]
    [∀ v : V, MeasurableSingletonClass (bn.stateSpace v)]
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [EventPos (bn := bn) B valB]
    [EventPosConstraints (bn := bn) [⟨A, valA⟩, ⟨B, valB⟩]]
    (hciCA :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({C} : Set V) ({A} : Set V) ({B} : Set V)) :
    (CompiledPlan.deductionSide A B C).holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn)))
        (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
        (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := bn)
    (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
    (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)
    (fun cpt =>
      linkProbVECond_eq_linkProbVE_of_condIndepVertices_CA (bn := bn)
        (A := A) (B := B) (C := C)
        (valA := valA) (valB := valB) (valC := valC)
        (cpt := cpt) (hciCA cpt hcond))

/-! ## Screening-off WMQueryEq (d-sep discharge + ScreeningOffProbEq instance) -/

theorem wmqueryeq_screeningOff_of_dsep_class
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [ScreeningOffProbEq (bn := bn) A B C valA valB valC]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    (CompiledPlan.deductionSide A B C).holds (bn := bn) →
      WMQueryEq (State := State (bn := bn))
        (Query := PLNQuery (BNQuery.Atom (bn := bn)))
        (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
        (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩) :=
  wmqueryeq_of_dsep_discharge_class (bn := bn)
    (cond := CompiledPlan.deductionSide A B C)
    (q₁ := PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
    (q₂ := PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)
    hci

end BNWorldModel

/-! ## BN-specific rewrite example (screening-off via d-sep) -/

namespace BNCompiledRewrite

open BNWorldModel
open WMRewriteBridge

variable {bn : BayesianNetwork V}
variable [Fintype V] [DecidableEq V]
variable [DecidableRel bn.graph.edges]
variable [∀ v, Fintype (bn.stateSpace v)] [∀ v, Nonempty (bn.stateSpace v)]
variable [∀ v, DecidableEq (bn.stateSpace v)]
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
variable [HasLocalMarkovProperty bn μ]
variable [DSeparationSoundness bn μ]

/-! ## Screening-off rewrite (non-degenerate, via explicit assumptions) -/

/-- Screening-off rewrite using a **proof obligation** instance.
This is the version to use for sound PLN rules (when the semantic lemma exists). -/
noncomputable def screeningOffRewrite_class
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [BNWorldModel.ScreeningOffProbEq (bn := bn) A B C valA valB valC]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    WMRewriteRule (State (bn := bn)) (PLNQuery (BNQuery.Atom (bn := bn))) :=
  WMRewriteBridge.rewrite_of_dsep (bn := bn) (State := State (bn := bn))
    (CompiledPlan.deductionSide A B C)
    (PLNQuery.link ⟨B, valB⟩ ⟨C, valC⟩)
    (PLNQuery.linkCond [⟨A, valA⟩, ⟨B, valB⟩] ⟨C, valC⟩)
    (fun hcond =>
      (BNWorldModel.wmqueryeq_screeningOff_of_dsep_class (bn := bn)
        A B C valA valB valC hci hcond).symm)

/-- Screening-off rewrite for BN queries, guarded by d-separation. -/
noncomputable def screeningOffRewrite
    (A B C : V) (valA : bn.stateSpace A) (valB : bn.stateSpace B) (valC : bn.stateSpace C)
    [BNWorldModel.ScreeningOffProbEq (bn := bn) A B C valA valB valC]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        (CompiledPlan.deductionSide A B C).holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure ({A} : Set V) ({C} : Set V) ({B} : Set V)) :
    WMRewriteRule (State (bn := bn)) (PLNQuery (BNQuery.Atom (bn := bn))) :=
  screeningOffRewrite_class (bn := bn) (A := A) (B := B) (C := C)
    (valA := valA) (valB := valB) (valC := valC) hci

/-! ## Class-based d-sep rewrite (safe default) -/

noncomputable def rewrite_of_dsep_class
    (cond : DSeparationCond V)
    (q₁ q₂ : PLNQuery (BNQuery.Atom (bn := bn)))
    [BNWorldModel.CondIndepQueryEq (bn := bn) cond q₁ q₂]
    (hci :
      ∀ cpt : bn.DiscreteCPT,
        cond.holds (bn := bn) →
          CondIndepVertices bn cpt.jointMeasure cond.X cond.Y cond.Z) :
    WMRewriteRule (State (bn := bn)) (PLNQuery (BNQuery.Atom (bn := bn))) :=
  WMRewriteBridge.rewrite_of_dsep (bn := bn) (State := State (bn := bn))
    cond q₁ q₂
    (fun hcond =>
      BNWorldModel.wmqueryeq_of_dsep_discharge_class
        (bn := bn) cond q₁ q₂ hci hcond)

end BNCompiledRewrite

/-! ## BN side conditions as PLNLinkCalculus parameters -/

namespace PLNLinkSide

variable {bn : BayesianNetwork V}

/-- Deduction side condition for the link calculus, ignoring WTV payloads. -/
def DedSide
    (A B C : V) (_tA _tB _tC _tAB _tBC : PLNWeightTV.WTV) : Prop :=
  (CompiledPlan.deductionSide A B C).holds (bn := bn)

/-- Induction (SourceRule) side condition for the link calculus. -/
def SourceSide
    (A B C : V) (_tA _tB _tC _tBA _tBC : PLNWeightTV.WTV) : Prop :=
  (CompiledPlan.inductionSide A B C).holds (bn := bn)

/-- Abduction (SinkRule) side condition for the link calculus. -/
def SinkSide
    (A B C : V) (_tA _tB _tC _tAB _tCB : PLNWeightTV.WTV) : Prop :=
  (CompiledPlan.abductionSide A B C).holds (bn := bn)

end PLNLinkSide

/-! ## BN-instantiated PLN Link Calculus (value-labeled atoms)

We instantiate the PLN link calculus with **value-labeled atoms** (`Σ v, stateSpace v`)
so that BN queries (which are value-specific) can be reflected in link judgments.
Side conditions ignore values and depend only on the underlying BN vertices.
-/

namespace LinkCalculusBN

open Mettapedia.Logic.PLNLinkCalculus

variable {bn : BayesianNetwork V}

/-- A value-labeled atom: a BN vertex and a concrete value. -/
abbrev Atom (bn : BayesianNetwork V) : Type _ :=
  Σ v : V, bn.stateSpace v

abbrev Judgment (bn : BayesianNetwork V) := PLNLinkCalculus.Judgment (Atom bn)
abbrev Context (bn : BayesianNetwork V) := PLNLinkCalculus.Context (Atom bn)

private def vertex (a : Atom bn) : V := a.1

def DedSideAtom
    (A B C : Atom bn) (tA tB tC tAB tBC : PLNWeightTV.WTV) : Prop :=
  PLNLinkSide.DedSide (bn := bn) (vertex A) (vertex B) (vertex C) tA tB tC tAB tBC

def SourceSideAtom
    (A B C : Atom bn) (tA tB tC tBA tBC : PLNWeightTV.WTV) : Prop :=
  PLNLinkSide.SourceSide (bn := bn) (vertex A) (vertex B) (vertex C) tA tB tC tBA tBC

def SinkSideAtom
    (A B C : Atom bn) (tA tB tC tAB tCB : PLNWeightTV.WTV) : Prop :=
  PLNLinkSide.SinkSide (bn := bn) (vertex A) (vertex B) (vertex C) tA tB tC tAB tCB

/-- BN-instantiated PLN derivations with structural side conditions from d-separation. -/
abbrev BNDerivation
    (Indep : Judgment bn → Judgment bn → Prop)
    (Γ : Context bn) : Judgment bn → Type _ :=
  PLNLinkCalculus.Derivation Indep
    (DedSideAtom (bn := bn))
    (SourceSideAtom (bn := bn))
    (SinkSideAtom (bn := bn))
    Γ

/-- Lift a rule instance to value-labeled atoms. -/
def atomA (inst : RuleInstance bn) : Atom bn := ⟨inst.A, inst.valA⟩
def atomB (inst : RuleInstance bn) : Atom bn := ⟨inst.B, inst.valB⟩
def atomC (inst : RuleInstance bn) : Atom bn := ⟨inst.C, inst.valC⟩

theorem compiled_deduction_side
    (inst : RuleInstance bn) (tA tB tC tAB tBC : PLNWeightTV.WTV)
    (hkind : inst.kind = .deduction) :
    DedSideAtom (bn := bn) (atomA inst) (atomB inst) (atomC inst) tA tB tC tAB tBC ↔
      (CompiledPlan.compile bn inst).sideCond.holds (bn := bn) := by
  cases inst with
  | mk kind A B C valA valB valC =>
      cases hkind
      rfl

theorem compiled_induction_side
    (inst : RuleInstance bn) (tA tB tC tBA tBC : PLNWeightTV.WTV)
    (hkind : inst.kind = .induction) :
    SourceSideAtom (bn := bn) (atomA inst) (atomB inst) (atomC inst) tA tB tC tBA tBC ↔
      (CompiledPlan.compile bn inst).sideCond.holds (bn := bn) := by
  cases inst with
  | mk kind A B C valA valB valC =>
      cases hkind
      rfl

theorem compiled_abduction_side
    (inst : RuleInstance bn) (tA tB tC tAB tCB : PLNWeightTV.WTV)
    (hkind : inst.kind = .abduction) :
    SinkSideAtom (bn := bn) (atomA inst) (atomB inst) (atomC inst) tA tB tC tAB tCB ↔
      (CompiledPlan.compile bn inst).sideCond.holds (bn := bn) := by
  cases inst with
  | mk kind A B C valA valB valC =>
      cases hkind
      rfl

end LinkCalculusBN

/-! ## Concrete chain example: structural discharge (no ad-hoc `hci`) -/

namespace ChainExample

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open BNWorldModel

theorem chain_hciCA_of_dsep
    (cpt : chainBN.DiscreteCPT)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [HasLocalMarkovProperty chainBN cpt.jointMeasure]
    (hcond :
      (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN)) :
    CondIndepVertices chainBN cpt.jointMeasure
      ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  exact Mettapedia.ProbabilityTheory.BayesianNetworks.Examples.chain_dsepFull_to_condIndep_CA_given_B
    (μ := cpt.jointMeasure) hcond

theorem chain_hciCA_of_dsepFull
    (cpt : chainBN.DiscreteCPT)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [HasLocalMarkovProperty chainBN cpt.jointMeasure]
    (hcondFull :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three)) :
    CondIndepVertices chainBN cpt.jointMeasure
      ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  exact Mettapedia.ProbabilityTheory.BayesianNetworks.Examples.chain_dsepFull_to_condIndep_CA_given_B
    (μ := cpt.jointMeasure) hcondFull

theorem chain_hciCA_from_hLM
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    ∀ cpt : chainBN.DiscreteCPT,
      (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN) →
        CondIndepVertices chainBN cpt.jointMeasure
          ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro cpt hcond
  letI : HasLocalMarkovProperty chainBN cpt.jointMeasure := hLM cpt
  exact chain_hciCA_of_dsep (cpt := cpt) hcond

theorem chain_hciCA_from_hLM_full
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure)
    (hcondFull :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three)) :
    ∀ cpt : chainBN.DiscreteCPT,
      CondIndepVertices chainBN cpt.jointMeasure
        ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro cpt
  letI : HasLocalMarkovProperty chainBN cpt.jointMeasure := hLM cpt
  exact chain_hciCA_of_dsepFull (cpt := cpt) hcondFull

theorem chain_screeningOff_wmqueryeq_of_dsep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN) →
      WMQueryEq (State := State (bn := chainBN))
        (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
        (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
        (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hcond
  exact wmqueryeq_screeningOff_of_dsep_CA (bn := chainBN)
    (A := Three.A) (B := Three.B) (C := Three.C)
    (valA := valA) (valB := valB) (valC := valC)
    (hciCA := chain_hciCA_from_hLM (hLM := hLM))
    hcond

theorem chain_screeningOff_rewrite_applies_of_dsep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN) →
      ∀ W : State (bn := chainBN),
        ⊢q W ⇓
          (PLNQuery.linkCond
            ([ (⟨Three.A, valA⟩ : BNQuery.Atom (bn := chainBN))
             , (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN)) ])
            (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN))) ↦
          (WorldModel.evidence
            (State := State (bn := chainBN))
            (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
            W
            (PLNQuery.link
              (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN))
              (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN)))) := by
  intro hcond W
  let qLink : PLNQuery (BNQuery.Atom (bn := chainBN)) :=
    PLNQuery.link
      (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN))
      (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN))
  let qLinkCond : PLNQuery (BNQuery.Atom (bn := chainBN)) :=
    PLNQuery.linkCond
      ([ (⟨Three.A, valA⟩ : BNQuery.Atom (bn := chainBN))
       , (⟨Three.B, valB⟩ : BNQuery.Atom (bn := chainBN)) ])
      (⟨Three.C, valC⟩ : BNQuery.Atom (bn := chainBN))
  let r : WMRewriteRule (State (bn := chainBN)) (PLNQuery (BNQuery.Atom (bn := chainBN))) :=
    WMRewriteBridge.rewrite_of_dsep (bn := chainBN) (State := State (bn := chainBN))
      (CompiledPlan.deductionSide Three.A Three.B Three.C) qLink qLinkCond
      (fun h =>
        (chain_screeningOff_wmqueryeq_of_dsep
          (valA := valA) (valB := valB) (valC := valC) hLM h).symm)
  have hW : ⊢wm W := WMJudgment.axiom W
  have happly := WMRewriteRule.apply (r := r) (W := W) hcond hW
  simpa [r, qLink, qLinkCond] using happly

theorem chain_screeningOff_strength_eq_of_dsep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := chainBN) →
      ∀ W : State (bn := chainBN),
        WorldModel.queryStrength
          (State := State (bn := chainBN))
          (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
          W (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
          =
        WorldModel.queryStrength
          (State := State (bn := chainBN))
          (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
          W (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hcond W
  have hEq :=
    chain_screeningOff_wmqueryeq_of_dsep
      (valA := valA) (valB := valB) (valC := valC) hLM hcond
  simpa [WorldModel.queryStrength] using congrArg Evidence.toStrength (hEq W)

theorem chain_screeningOff_wmqueryeq_of_dsepFull
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
      chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      WMQueryEq (State := State (bn := chainBN))
        (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
        (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
        (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hcondFull
  exact wmqueryeq_screeningOff_of_dsep_CA (bn := chainBN)
    (A := Three.A) (B := Three.B) (C := Three.C)
    (valA := valA) (valB := valB) (valC := valC)
    (hciCA := fun cpt _hc => chain_hciCA_from_hLM_full (hLM := hLM)
      (hcondFull := hcondFull) cpt)
    hcondFull

theorem chain_screeningOff_wmqueryeq_of_moralSep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.SeparatedInMoral
      chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      WMQueryEq (State := State (bn := chainBN))
        (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
        (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
        (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hSep
  have hFull :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) :=
    (Mettapedia.ProbabilityTheory.BayesianNetworks.Examples.chain_dsepFull_iff_separatedInMoral_A_C_given_B).2 hSep
  exact chain_screeningOff_wmqueryeq_of_dsepFull
    (valA := valA) (valB := valB) (valC := valC) hLM hFull

theorem chain_screeningOff_wmqueryeq_of_moralSepAncestral
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [EventPos (bn := chainBN) Three.B valB]
    [EventPosConstraints (bn := chainBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.SeparatedInMoralAncestral
      chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) →
      WMQueryEq (State := State (bn := chainBN))
        (Query := PLNQuery (BNQuery.Atom (bn := chainBN)))
        (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
        (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hSepAnc
  have hFull :
      Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation.DSeparatedFull
        chainGraph ({Three.A} : Set Three) ({Three.C} : Set Three) ({Three.B} : Set Three) :=
    (Mettapedia.ProbabilityTheory.BayesianNetworks.Examples.chain_dsepFull_iff_sep_moral_ancestral_A_C_B).2 hSepAnc
  exact chain_screeningOff_wmqueryeq_of_dsepFull
    (valA := valA) (valB := valB) (valC := valC) hLM hFull

end ChainExample

/-! ## Fork BN Example (A ← B → C) -/

namespace ForkExample

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open BNWorldModel

theorem fork_hciCA_from_hLM
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    (hLM : ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure) :
    ∀ cpt : forkBN.DiscreteCPT,
      (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := forkBN) →
        CondIndepVertices forkBN cpt.jointMeasure
          ({Three.C} : Set Three) ({Three.A} : Set Three) ({Three.B} : Set Three) := by
  intro cpt _hcond
  letI : HasLocalMarkovProperty forkBN cpt.jointMeasure := hLM cpt
  exact fork_condIndep_CA_given_B_of_localMarkov (μ := cpt.jointMeasure)

theorem fork_screeningOff_wmqueryeq_of_dsep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure) :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := forkBN) →
      WMQueryEq (State := State (bn := forkBN))
        (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
        (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
        (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hcond
  exact wmqueryeq_screeningOff_of_dsep_CA (bn := forkBN)
    (A := Three.A) (B := Three.B) (C := Three.C)
    (valA := valA) (valB := valB) (valC := valC)
    (hciCA := fork_hciCA_from_hLM (hLM := hLM))
    hcond

theorem fork_screeningOff_strength_eq_of_dsep
    (valA valB valC : Bool)
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    [EventPos (bn := forkBN) Three.B valB]
    [EventPosConstraints (bn := forkBN) [⟨Three.A, valA⟩, ⟨Three.B, valB⟩]]
    (hLM : ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure) :
    (CompiledPlan.deductionSide Three.A Three.B Three.C).holds (bn := forkBN) →
      ∀ W : State (bn := forkBN),
        WorldModel.queryStrength
          (State := State (bn := forkBN))
          (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
          W (PLNQuery.linkCond [⟨Three.A, valA⟩, ⟨Three.B, valB⟩] ⟨Three.C, valC⟩)
          =
        WorldModel.queryStrength
          (State := State (bn := forkBN))
          (Query := PLNQuery (BNQuery.Atom (bn := forkBN)))
          W (PLNQuery.link ⟨Three.B, valB⟩ ⟨Three.C, valC⟩) := by
  intro hcond W
  have hEq :=
    fork_screeningOff_wmqueryeq_of_dsep
      (valA := valA) (valB := valB) (valC := valC) hLM hcond
  simpa [WorldModel.queryStrength] using congrArg Evidence.toStrength (hEq W)

end ForkExample

/-! ## Collider BN Example (A → C ← B) — Sink Rule / Abduction

Variable mapping: (A_rule, B_rule, C_rule) = (Three.A, Three.C, Three.B).
Sink center = Three.C (the collider node, receives edges from A and B).

Side condition: `abductionSide Three.A Three.C Three.B = ⟨{Three.A}, {Three.B}, ∅⟩`
requires marginal independence A ⊥ B | ∅, which holds in collider BNs because A and B
have no active path when the common effect C is not conditioned on. -/

namespace ColliderExample

open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples
open BNWorldModel

theorem collider_hciAB_from_hLM
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    (hLM : ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure) :
    ∀ cpt : colliderBN.DiscreteCPT,
      (CompiledPlan.abductionSide Three.A Three.C Three.B).holds (bn := colliderBN) →
        CondIndepVertices colliderBN cpt.jointMeasure
          ({Three.A} : Set Three) ({Three.B} : Set Three) ∅ := by
  intro cpt _hcond
  letI : HasLocalMarkovProperty colliderBN cpt.jointMeasure := hLM cpt
  exact collider_condIndep_AB_given_empty_of_localMarkov (μ := cpt.jointMeasure)

theorem collider_screeningOff_wmqueryeq_of_dsep
    (valA valB : Bool)
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    [EventPos (bn := colliderBN) Three.A valA]
    (hLM : ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure) :
    (CompiledPlan.abductionSide Three.A Three.C Three.B).holds (bn := colliderBN) →
      WMQueryEq (State := State (bn := colliderBN))
        (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
        (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
        (PLNQuery.prop ⟨Three.B, valB⟩) := by
  intro hcond
  exact wmqueryeq_of_prob_eq (bn := colliderBN)
    (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
    (PLNQuery.prop ⟨Three.B, valB⟩)
    (fun cpt =>
      linkProbVE_eq_propProbVE_of_condIndep (bn := colliderBN)
        (A := Three.A) (C := Three.B) (valA := valA) (valC := valB)
        (cpt := cpt)
        (collider_hciAB_from_hLM hLM cpt hcond)
        (EventPos.pos (bn := colliderBN) (A := Three.A) (valA := valA) cpt))

theorem collider_screeningOff_strength_eq_of_dsep
    (valA valB : Bool)
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    [EventPos (bn := colliderBN) Three.A valA]
    (hLM : ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure) :
    (CompiledPlan.abductionSide Three.A Three.C Three.B).holds (bn := colliderBN) →
      ∀ W : State (bn := colliderBN),
        WorldModel.queryStrength
          (State := State (bn := colliderBN))
          (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
          W (PLNQuery.link ⟨Three.A, valA⟩ ⟨Three.B, valB⟩)
          =
        WorldModel.queryStrength
          (State := State (bn := colliderBN))
          (Query := PLNQuery (BNQuery.Atom (bn := colliderBN)))
          W (PLNQuery.prop ⟨Three.B, valB⟩) := by
  intro hcond W
  have hEq :=
    collider_screeningOff_wmqueryeq_of_dsep
      (valA := valA) (valB := valB) hLM hcond
  simpa [WorldModel.queryStrength] using congrArg Evidence.toStrength (hEq W)

end ColliderExample

end Mettapedia.Logic.PLNBNCompilation
