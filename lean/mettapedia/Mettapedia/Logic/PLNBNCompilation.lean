import Mettapedia.Logic.PLNLinkCalculus
import Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
import Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparationSoundness

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

open scoped Classical

open MeasureTheory ProbabilityTheory

open Mettapedia.Logic.PLNLinkCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.DSeparation
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## BN Queries -/

/-- A BN query used by compiled PLN rules: propositions and links at concrete values. -/
inductive BNQuery (bn : BayesianNetwork V) where
  | prop : (v : V) → bn.stateSpace v → BNQuery bn
  | link : (a b : V) → bn.stateSpace a → bn.stateSpace b → BNQuery bn

namespace BNQuery

variable (bn : BayesianNetwork V)

/-- Evaluate a BN query via variable elimination (exact for the BN model class). -/
noncomputable def evalVE (cpt : bn.DiscreteCPT)
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] :
    BNQuery bn → ENNReal
  | .prop v val => BayesianNetwork.propProbVE (bn := bn) cpt v val
  | .link a b valA valB => BayesianNetwork.linkProbVE (bn := bn) cpt a b valA valB

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
  DSeparated bn.graph cond.X cond.Y cond.Z

end DSeparationCond

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
    [∀ v, Fintype (bn.stateSpace v)] [∀ v, DecidableEq (bn.stateSpace v)] : List ENNReal :=
  plan.queries.map (BNQuery.evalVE (bn := bn) cpt)

end CompiledPlan

/-! ## Discharging Σ via d-separation soundness -/

namespace DSeparationCond

open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

variable {bn : BayesianNetwork V}
variable [∀ v : V, StandardBorelSpace (bn.stateSpace v)]
variable (μ : Measure bn.JointSpace) [IsFiniteMeasure μ]
variable [HasLocalMarkovProperty bn μ]
variable [DSeparationSoundness bn μ]

/-- If the d-separation obligation holds, we can discharge it as conditional independence. -/
theorem discharge
    (cond : DSeparationCond V)
    (hcond : cond.holds (bn := bn)) :
    CondIndepVertices bn μ cond.X cond.Y cond.Z :=
  dsep_implies_condIndepVertices (bn := bn) (μ := μ) hcond

end DSeparationCond

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

omit [Fintype V] [DecidableEq V] in
theorem compiled_deduction_side
    (inst : RuleInstance bn) (tA tB tC tAB tBC : PLNWeightTV.WTV)
    (hkind : inst.kind = .deduction) :
    DedSideAtom (bn := bn) (atomA inst) (atomB inst) (atomC inst) tA tB tC tAB tBC ↔
      (CompiledPlan.compile bn inst).sideCond.holds (bn := bn) := by
  cases inst with
  | mk kind A B C valA valB valC =>
      cases hkind
      rfl

omit [Fintype V] [DecidableEq V] in
theorem compiled_induction_side
    (inst : RuleInstance bn) (tA tB tC tBA tBC : PLNWeightTV.WTV)
    (hkind : inst.kind = .induction) :
    SourceSideAtom (bn := bn) (atomA inst) (atomB inst) (atomC inst) tA tB tC tBA tBC ↔
      (CompiledPlan.compile bn inst).sideCond.holds (bn := bn) := by
  cases inst with
  | mk kind A B C valA valB valC =>
      cases hkind
      rfl

omit [Fintype V] [DecidableEq V] in
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

end Mettapedia.Logic.PLNBNCompilation
