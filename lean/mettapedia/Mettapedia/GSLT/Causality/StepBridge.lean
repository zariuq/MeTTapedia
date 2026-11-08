import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CausalNetworksStep
import Mettapedia.GSLT.Causality.DoCalculus.RegimeModel
import Mettapedia.GSLT.Causality.DoCalculus.MultiIntervention
import Mettapedia.GSLT.Causality.DoCalculus.GeneralControls
import Mettapedia.GSLT.Causality.DoCalculus.FrontDoor

/-!
# Grok's do-calculus on the step

The network program of `CausalNetworksStep` with a table of weights read by its firings
(`tableWeight`) has, on the step, the history likelihood the cell identity gives
(`stepLikelihood_eq`): the sum over the linearizations of the history of `x` of `Race.traceProb`
from the store with every variable pending and the regimes installed.

## Regimes: an intervention is conditioning on a regime atom

Install the regime atom `(reg v force)` at the variables of `Z` and `(reg v idle)` elsewhere
(`regimeOn`). The firings of an idle variable weigh the conditional probability table; those of a
forced variable weigh the point mass at `z v` (`regimeTable`).
* **The step's history likelihood is the g-formula** `truncatedWeight (doFinset Z z)`
  (`step_regime_likelihood`), for every table: the regime overrides the mechanism.
* **It is the conditional of Grok's augmented network given the regimes**
  (`regime_is_conditioning`, from `RegimeModel.aug_weight_force`): the augmented joint at
  `(x, regimeOn Z)` over the regimes' prior `2⁻¹ ^ |V|`.
* **The do at the handles is the same intervention** (`do_is_regime`): the restriction of
  `CausalNetworksStep.step_do_likelihood` and the regime atom give one likelihood, when the set
  values have positive probability on the history's rows.
* **The g-formula for a set** (`step_gformula`): the joint of `MultiIntervention`'s mutilated
  network.

## Controls

* **Conditioning against do on a confounded pair** (`step_fork_control`): on Grok's fork
  `response ← confounder → copied`, with both children copying the confounder, the step's
  history masses give the response ratio `1/2` when `copied` is forced and `1` when it is
  observed (`GeneralControls.fork_rule2_fails`).
* **Restriction is not override** (`restriction_starves`): on the same fork, the restriction do
  at `copied` leaves the race at `copied`, on the row `confounder = false`, with total `0`; the
  forced regime gives that race total `1`.
* **The front door on the step** (`step_frontDoor`): the step's interventional mass on the smoking
  graph is Grok's front-door expression in the step's observational masses.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.Causality.StepBridge

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open CausalCells CausalNetworks CausalNetworksStep
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.ProbabilityTheory.BayesianNetworks
open AnnotatedRuns (Firing)
open scoped ENNReal

universe uS

variable {V β : Type}
variable [Fintype V] [DecidableEq V]
variable [Fintype β] [DecidableEq β] [MeasurableSpace β]
variable (graph : DirectedGraph V)
variable (acyclic : graph.IsAcyclic)
variable [DecidableRel graph.edges]
variable {R : Type} [Fintype R] [DecidableEq R]
variable {S : Type uS}

/-! ## The step likelihood of a table -/

/-- The weight a firing reads from a table. -/
def tableWeight (table : Event (β := β) (R := R) graph → ℝ)
    (f : Firing (Atom V β R) S (Atom V β R)) : ℝ := by
  classical
  exact if h : ∃ e, firing graph e = f then table (Classical.choose h) else 0

/-- **The step's history likelihood of an assignment**: the sum, over the linearizations of its
history, of the step's trace distribution from the start store. -/
def stepLikelihood (A : SubstitutionAction (Atom V β R) S) (regime : V → R)
    (table : Event (β := β) (R := R) graph → ℝ) (x : V → β) : ℝ :=
  ∑ l ∈ (cells graph regime table).lins (historyOf graph regime x) ∅,
    Race.traceProb A id (realization (S := S) graph regime table).alphabet id
      (tableWeight graph table) (l.map (realization (S := S) graph regime table).firing)
      (start graph regime)

omit [DecidableEq β] [MeasurableSpace β] [DecidableEq R] in
theorem tableWeight_firing (table : Event (β := β) (R := R) graph → ℝ)
    (e : Event (β := β) (R := R) graph) :
    tableWeight (S := S) graph table (firing graph e) = table e := by
  have found : ∃ e', firing (S := S) graph e' = firing graph e := ⟨e, rfl⟩
  unfold tableWeight
  rw [dif_pos found, firing_injective (Classical.choose_spec found)]

include acyclic in
/-- **The step likelihood is the cell identity's product.** -/
theorem stepLikelihood_eq (A : SubstitutionAction (Atom V β R) S) (regime : V → R)
    (table : Event (β := β) (R := R) graph → ℝ) (x : V → β)
    (positive : ∀ v, 0 < ∑ b, table ⟨v, (parentFunOf graph x v, regime v, b)⟩) :
    stepLikelihood graph A regime table x =
      ∏ v, table (assignmentEvent graph regime x v) /
        ∑ b, table ⟨v, (parentFunOf graph x v, regime v, b)⟩ := by
  obtain ⟨order, horder⟩ := (network (β := β) graph acyclic).exists_topological_order
  have bridge : ∀ l ∈ (cells graph regime table).lins (historyOf graph regime x) ∅,
      Race.traceProb A id (realization (S := S) graph regime table).alphabet id
          (tableWeight graph table) (l.map (realization (S := S) graph regime table).firing)
          (start graph regime) =
        (cells graph regime table).pathProb ∅ l := by
    intro l member
    exact (realization (S := S) graph regime table).traceProb_eq A (tableWeight_firing graph table)
      (((cells graph regime table).mem_lins _ _ l).mp member) _ rfl Race.reflexive_nil
  unfold stepLikelihood
  rw [Finset.sum_congr rfl bridge]
  exact likelihood acyclic regime table x order horder positive

omit [DecidableEq V] [Fintype β] in
theorem truncatedWeight_ne_top (cpt : (network (β := β) graph acyclic).DiscreteCPT)
    (assignment : V → Option β) (x : V → β) :
    truncatedWeight graph acyclic cpt assignment x ≠ ⊤ := by
  unfold truncatedWeight
  apply ENNReal.prod_ne_top
  intro v _
  unfold truncatedFactor
  cases assignment v with
  | none => exact PMF.apply_ne_top _ _
  | some a =>
      dsimp only
      split_ifs <;> simp

/-! ## Regimes -/

/-- **The regime installed on `Z`**: force there, idle elsewhere. -/
def regimeOn (Z : Finset V) (v : V) : Regime := if v ∈ Z then .force else .idle

/-- **The regime table**: an idle variable weighs its conditional probability table, a forced one
the point mass at `z`. -/
def regimeTable (cpt : (network (β := β) graph acyclic).DiscreteCPT) (z : V → β)
    (e : Event (β := β) (R := Regime) graph) : ℝ :=
  match e.2.2.1 with
  | .idle => (cptAt graph acyclic cpt e.1 e.2.1 e.2.2.2).toReal
  | .force => if e.2.2.2 = z e.1 then 1 else 0

omit [DecidableEq V] in
theorem regimeTable_total (cpt : (network (β := β) graph acyclic).DiscreteCPT) (z : V → β)
    (v : V) (row : ParentFun (β := β) graph v) (r : Regime) :
    ∑ b, regimeTable graph acyclic cpt z ⟨v, (row, r, b)⟩ = 1 := by
  cases r with
  | idle => exact sum_cptAt acyclic cpt v row
  | force => simp [regimeTable]

/-- **With the regime atoms of `Z` installed, the step's history likelihood is the g-formula**,
for every table. -/
theorem step_regime_likelihood (A : SubstitutionAction (Atom V β Regime) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (Z : Finset V) (z x : V → β) :
    stepLikelihood graph A (regimeOn Z) (regimeTable graph acyclic cpt z) x =
      (truncatedWeight graph acyclic cpt (doFinset Z z) x).toReal := by
  rw [stepLikelihood_eq graph acyclic A _ _ x
    (fun v => by rw [regimeTable_total]; exact one_pos)]
  unfold truncatedWeight
  rw [ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [regimeTable_total, div_one]
  unfold truncatedFactor
  by_cases member : v ∈ Z
  · rw [doFinset_eq_some member]
    simp only [regimeTable, assignmentEvent, regimeOn, if_pos member]
    split_ifs <;> simp
  · rw [doFinset_eq_none member]
    simp only [regimeTable, assignmentEvent, regimeOn, if_neg member]

/-- **The g-formula for a set of variables on the step**: the joint of the mutilated network. -/
theorem step_gformula (A : SubstitutionAction (Atom V β Regime) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (Z : Finset V) (z x : V → β) :
    stepLikelihood graph A (regimeOn Z) (regimeTable graph acyclic cpt z) x =
      ((intervenedFinsetCPT graph acyclic cpt Z z).jointWeight x).toReal := by
  rw [step_regime_likelihood, intervenedFinset_jointWeight_eq_truncatedWeight]

/-- **The do at the handles and the regime atom are one intervention**, when the set values have
positive probability on the history's rows. -/
theorem do_is_regime (A : SubstitutionAction (Atom V β Unit) S)
    (A' : SubstitutionAction (Atom V β Regime) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (Z : Finset V) (z x : V → β)
    (setPositive : ∀ v ∈ Z, 0 < (cptAt graph acyclic cpt v (parentFunOf graph x v) (z v)).toReal) :
    ∑ l ∈ (cells graph plain (cptWeight graph acyclic cpt)).lins (historyOf graph plain x) ∅,
        Race.traceProb A id (realization (S := S) graph plain (cptWeight graph acyclic cpt)).alphabet
          id (Intervention.restrictWeight (doKeep (S := S) (doFinset Z z))
            (stepWeight graph acyclic cpt))
          (l.map (realization (S := S) graph plain (cptWeight graph acyclic cpt)).firing)
          (start graph plain) =
      stepLikelihood graph A' (regimeOn Z) (regimeTable graph acyclic cpt z) x := by
  obtain ⟨order, horder⟩ := (network (β := β) graph acyclic).exists_topological_order
  rw [step_regime_likelihood, step_do_likelihood acyclic A cpt _ x order horder]
  intro v a set
  by_cases member : v ∈ Z
  · rw [doFinset_eq_some member, Option.some.injEq] at set
    rw [← set]
    exact setPositive v member
  · rw [doFinset_eq_none member] at set
    cases set

section Conditioning

omit [Fintype V] [Fintype β] [DecidableEq β] [MeasurableSpace β] in
theorem doFinset_merge_empty (Z : Finset V) (x z : V → β) :
    doFinset (∅ ∪ Z) (mergeAssign ∅ x z) = doFinset Z z := by
  funext v
  simp [doFinset, mergeAssign]

/-- **The regime program is conditioning on the regimes in Grok's augmented network**: the step's
history likelihood is the augmented joint at `(x, regimeOn Z)` over the regimes' prior
`2⁻¹ ^ |V|`. -/
theorem regime_is_conditioning (A : SubstitutionAction (Atom V β Regime) S)
    (cpt : (network (β := β) graph acyclic).DiscreteCPT) (Z : Finset V) (z x : V → β) :
    stepLikelihood graph A (regimeOn Z) (regimeTable graph acyclic cpt z) x =
      2 ^ Fintype.card V *
        ((augCPT β graph acyclic cpt ∅ Z x z).jointWeight (joinAug β (x, regimeOn Z))).toReal := by
  have forced : ∀ v ∈ Z, regimeOf β (joinAug β (x, regimeOn Z)) v = Regime.force := by
    intro v member
    simp [regimeOf, joinAug, regimeOn, member]
  rw [aug_weight_force β graph acyclic cpt (Finset.disjoint_empty_left Z) x z _ forced,
    doFinset_merge_empty, step_regime_likelihood, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_inv]
  have obsSame : obsOf β (joinAug β (x, regimeOn Z)) = x := rfl
  rw [obsSame, ← mul_assoc, ← mul_pow]
  norm_num

end Conditioning

/-! ## Controls -/

section Fork

variable (A : SubstitutionAction (Atom ForkV Bool Regime) S)

/-- The step's history masses on the fork, with the regime atoms of `Z` installed and the forced
value `true`. -/
def stepForkMass (Z : Finset ForkV) (keep : (ForkV → Bool) → Bool) : ℝ≥0∞ :=
  ∑ f, if keep f = true then
    ENNReal.ofReal (stepLikelihood forkGraph A (regimeOn Z)
      (regimeTable forkGraph forkAcyclic forkCPT fun _ => true) f) else 0

theorem stepForkMass_eq (Z : Finset ForkV) (keep : (ForkV → Bool) → Bool) :
    stepForkMass A Z keep = forkMass (doFinset Z fun _ => true) keep := by
  unfold stepForkMass forkMass
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [step_regime_likelihood, ENNReal.ofReal_toReal (truncatedWeight_ne_top _ _ _ _ _)]

/-- **Conditioning and do differ on the step's histories of a confounded pair**: forcing `copied`
gives the response ratio `1/2`, observing it gives `1`. -/
theorem step_fork_control :
    stepForkMass A {.copied} (fun f => f .response && f .copied) /
        stepForkMass A {.copied} (fun f => f .copied) ≠
      stepForkMass A ∅ (fun f => f .response && f .copied) /
        stepForkMass A ∅ (fun f => f .copied) := by
  rw [stepForkMass_eq, stepForkMass_eq, stepForkMass_eq, stepForkMass_eq, ← forkDoZ_eq,
    ← forkDoNone_eq]
  exact fork_rule2_fails.2

/-- The row of `copied` on which the confounder is `false`. -/
def falseRow : ParentFun (β := Bool) forkGraph .copied := fun _ => false

/-- **Restriction is not override**: the restriction do at `copied` leaves the race of `copied`
on the row `confounder = false` with total `0`, where the forced regime gives it total `1`. -/
theorem restriction_starves :
    (cells forkGraph plain (doWeight forkGraph forkAcyclic forkCPT forkDoZ)).cellTotal
        ⟨.copied, (falseRow, ())⟩ = 0 ∧
      (cells forkGraph (regimeOn {.copied})
          (regimeTable forkGraph forkAcyclic forkCPT fun _ => true)).cellTotal
        ⟨.copied, (falseRow, .force)⟩ = 1 := by
  refine ⟨?_, ?_⟩
  · rw [cellTotal_eq]
    simp [doWeight, forkDoZ, cptWeight, cptAt, forkCPT, toParentAssignment, falseRow]
  · rw [cellTotal_eq]
    exact regimeTable_total forkGraph forkAcyclic forkCPT _ _ _ _

end Fork

section FrontDoor

variable (A : SubstitutionAction (Atom Smoke β Unit) S)
  (A' : SubstitutionAction (Atom Smoke β Regime) S)

/-- The step's observational history masses on the smoking graph. -/
def stepObs (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] : ℝ≥0∞ :=
  ∑ f, if pred f then
    ENNReal.ofReal (∑ l ∈ (cells smokeGraph plain (cptWeight smokeGraph smokeAcyclic cpt)).lins
        (historyOf smokeGraph plain f) ∅,
      Race.traceProb A id
        (realization (S := S) smokeGraph plain (cptWeight smokeGraph smokeAcyclic cpt)).alphabet id
        (stepWeight smokeGraph smokeAcyclic cpt)
        (l.map (realization (S := S) smokeGraph plain (cptWeight smokeGraph smokeAcyclic cpt)).firing)
        (start smokeGraph plain)) else 0

/-- The step's interventional mass: the regime atom forces smoking to `s0`. -/
def stepDoMass (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (s0 c0 : β) : ℝ≥0∞ :=
  ∑ f, if f .c = c0 then
    ENNReal.ofReal (stepLikelihood smokeGraph A' (regimeOn {.s})
      (regimeTable smokeGraph smokeAcyclic cpt fun _ => s0) f) else 0

theorem stepObs_eq (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] :
    stepObs A cpt pred = obs cpt pred := by
  unfold stepObs obs
  refine Finset.sum_congr rfl fun f _ => ?_
  obtain ⟨order, horder⟩ := (network (β := β) smokeGraph smokeAcyclic).exists_topological_order
  rw [step_likelihood_eq_jointWeight smokeAcyclic A cpt f order horder,
    ENNReal.ofReal_toReal (by
      rw [← truncatedWeight_none_eq_jointWeight]
      exact truncatedWeight_ne_top _ _ _ _ _)]

omit [Fintype β] [DecidableEq β] [MeasurableSpace β] in
theorem doFinset_smoke (s0 : β) : doFinset ({.s} : Finset Smoke) (fun _ => s0) = doSmoke s0 := by
  funext v
  cases v <;> simp [doFinset, doSmoke]

theorem stepDoMass_eq (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT) (s0 c0 : β) :
    stepDoMass A' cpt s0 c0 = doMass cpt s0 c0 := by
  unfold stepDoMass doMass
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [step_regime_likelihood, ENNReal.ofReal_toReal (truncatedWeight_ne_top _ _ _ _ _),
    doFinset_smoke]

/-- **The front door on the step**: the step's interventional mass is Grok's front-door expression
in the step's observational masses. -/
theorem step_frontDoor (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (s0 c0 : β)
    (hposS : obs cpt (fun f => f .s = s0) ≠ 0)
    (hposT : ∀ bs bt, pt cpt bs bt ≠ 0) :
    stepDoMass A' cpt s0 c0 =
      ∑ bt, (stepObs A cpt (fun f => f .s = s0 ∧ f .t = bt) /
          stepObs A cpt (fun f => f .s = s0)) *
        (∑ bs, (stepObs A cpt (fun f => f .c = c0 ∧ f .t = bt ∧ f .s = bs) /
            stepObs A cpt (fun f => f .s = bs ∧ f .t = bt)) *
          stepObs A cpt (fun f => f .s = bs)) := by
  simp only [stepObs_eq, stepDoMass_eq]
  exact frontDoor cpt s0 c0 hposS hposT

end FrontDoor

#print axioms stepLikelihood_eq
#print axioms step_regime_likelihood
#print axioms step_gformula
#print axioms do_is_regime
#print axioms regime_is_conditioning
#print axioms step_fork_control
#print axioms restriction_starves
#print axioms step_frontDoor

end Mettapedia.GSLT.Causality.StepBridge

end
