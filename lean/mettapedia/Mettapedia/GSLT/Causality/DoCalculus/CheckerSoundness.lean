import Mettapedia.GSLT.Causality.DoCalculus.LanguageDef
import Mettapedia.GSLT.Causality.DoCalculus.MultiIntervention
import Mettapedia.GSLT.Causality.DoCalculus.Rule1Mass
import Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation

/-!
# Rule 1 discharged by the finite d-separation checker

`rule1Rule` has a d-separation premise. On the supported profile the checker
accepts that premise if and only if the endpoints are fully d-separated in the
graph with the arrows into the intervention deleted. `rule1_condMass` turns
that separation into equality of the atomic conditional masses.

A `false` answer from the checker can mean that the sets fall outside the
supported profile, where the endpoints are required to be disjoint from the
conditioning set. It is not, by itself, a proof that an active trail exists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DirectedGraph
open DSeparation
open MeasureTheory
open scoped ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]
variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- The finite profile submitted to the checker for rule 1: the outcome, the
covariate, and the conditioning set. -/
def rule1Profile (outcome covariate conditioning : Finset V) :
    FiniteDSeparation.Condition V where
  X := outcome
  Y := covariate
  Z := conditioning

omit [Inhabited β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] in
/-- Checker acceptance is full d-separation on the supported profile, in the
graph with the arrows into the intervention deleted. -/
theorem rule1_check_iff
    (hAcyclic : graph.IsAcyclic)
    (intervention : V) (outcome covariate conditioning : Finset V) :
    FiniteDSeparation.check (deleteIncoming graph {intervention})
        (rule1Profile outcome covariate conditioning) = true ↔
      (rule1Profile outcome covariate conditioning).Meaning
          (deleteIncoming graph {intervention}) ∧
        (rule1Profile outcome covariate conditioning).Supported :=
  FiniteDSeparation.check_eq_true_iff
    (deleteIncoming graph {intervention})
    (rule1Profile outcome covariate conditioning)
    (deleteIncoming_acyclic graph hAcyclic {intervention})
    (fun vertex => DirectedGraph.isAcyclic_irrefl _
      (deleteIncoming_acyclic graph hAcyclic {intervention}) vertex)

omit [DecidableEq β] in
/-- Rule 1 for conditional masses, with the separation premise discharged by
the checker. -/
theorem rule1_of_check
    [StandardBorelSpace (V → β)]
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (intervention : V) (value : β)
    (outcome covariate conditioning : Finset V)
    (outcomeAssign :
      ∀ p : ((outcome : Finset V) : Set V),
        (intervenedNet graph hAcyclic intervention).stateSpace p.1)
    (covariateAssign :
      ∀ p : ((covariate : Finset V) : Set V),
        (intervenedNet graph hAcyclic intervention).stateSpace p.1)
    (conditioningAssign :
      ∀ p : ((conditioning : Finset V) : Set V),
        (intervenedNet graph hAcyclic intervention).stateSpace p.1)
    (hintervention : intervention ∈ conditioning)
    (hcheck : FiniteDSeparation.check (deleteIncoming graph {intervention})
      (rule1Profile outcome covariate conditioning) = true)
    (hpos :
      (intervenedCPT graph hAcyclic cpt intervention value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic intervention) covariate
            covariateAssign ∩
          assignEvent (bn := intervenedNet graph hAcyclic intervention) conditioning
            conditioningAssign) ≠ 0) :
    (intervenedCPT graph hAcyclic cpt intervention value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic intervention) outcome
            outcomeAssign ∩
          assignEvent (bn := intervenedNet graph hAcyclic intervention) covariate
            covariateAssign ∩
          assignEvent (bn := intervenedNet graph hAcyclic intervention) conditioning
            conditioningAssign) /
      (intervenedCPT graph hAcyclic cpt intervention value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic intervention) covariate
            covariateAssign ∩
          assignEvent (bn := intervenedNet graph hAcyclic intervention) conditioning
            conditioningAssign) =
    (intervenedCPT graph hAcyclic cpt intervention value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic intervention) outcome
            outcomeAssign ∩
          assignEvent (bn := intervenedNet graph hAcyclic intervention) conditioning
            conditioningAssign) /
      (intervenedCPT graph hAcyclic cpt intervention value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic intervention) conditioning
            conditioningAssign) := by
  have haccepted := (rule1_check_iff graph hAcyclic intervention outcome covariate
    conditioning).1 hcheck
  have hsep : DSeparatedFull (deleteIncoming graph {intervention})
      (outcome : Set V) (covariate : Set V) (conditioning : Set V) :=
    haccepted.1.2
  have hoverlap : (outcome : Set V) ∩ (covariate : Set V) ⊆ (conditioning : Set V) := by
    rw [← Finset.coe_inter]
    exact haccepted.1.1
  exact rule1_condMass graph hAcyclic cpt intervention value outcome covariate conditioning
    outcomeAssign covariateAssign conditioningAssign hintervention hoverlap hsep hpos

/-! ## The checker accepts an isolated covariate -/

inductive ChainV
  | treatment
  | outcome
  | covariate
  deriving DecidableEq

instance : Fintype ChainV where
  elems := {ChainV.treatment, ChainV.outcome, ChainV.covariate}
  complete := by intro vertex; cases vertex <;> simp

/-- One arrow, from the treatment to the outcome. The covariate is isolated. -/
def rule1ChainGraph : DirectedGraph ChainV where
  edges source target := source = .treatment ∧ target = .outcome

instance : DecidableRel rule1ChainGraph.edges := fun _ _ => by
  unfold rule1ChainGraph
  infer_instance

/-- After the arrows into the treatment are deleted, the checker accepts
separation of the outcome from the isolated covariate by the treatment. -/
theorem chain_rule1_checked :
    FiniteDSeparation.check (deleteIncoming rule1ChainGraph {ChainV.treatment})
      (rule1Profile {ChainV.outcome} {ChainV.covariate} {ChainV.treatment}) = true := by
  decide

end Mettapedia.GSLT.Causality.DoCalculus
