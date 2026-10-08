import Mettapedia.GSLT.Causality.DoCalculus.CondMass
import Mettapedia.GSLT.Causality.DoCalculus.DoRules

/-!
# Rule 1 as equality of conditional masses

Pearl's rule 1 is conditional independence in the intervened joint. On a finite
discrete joint that independence is an equality of atomic conditional masses:
when the mass of the covariate together with the conditioning set is positive,

`P(y | do(x), z, w) = P(y | do(x), w)`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open MeasureTheory
open BayesianNetwork
open DirectedGraph
open DSeparation
open scoped ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]

variable (hAcyclic : graph.IsAcyclic)
variable {β : Type} [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]

/-- The Bayesian network of `do(treatment)`, arrows into the treatment deleted.

The measurable-space field is `MeasurableSpace β` by name. Unfolding `network`
would ask for that instance before the state space has been filled in.
-/
abbrev intervenedNet (treatment : V) : BayesianNetwork V where
  graph := deleteIncoming graph {treatment}
  acyclic := deleteIncoming_acyclic graph hAcyclic {treatment}
  stateSpace := fun _ => β
  measurableSpace := fun _ => (inferInstance : MeasurableSpace β)

omit [DecidableRel graph.edges] [DecidableEq β] in
/-- **Do-calculus, rule 1, for conditional masses.**

Full d-separation of `outcome` and `covariate` by `conditioning` in the graph
with the arrows into `treatment` deleted, with `treatment` in `conditioning`,
gives equality of the atomic conditional masses in the intervened joint. The
hypothesis `hpos` is positivity of the covariate together with the conditioning
set.
-/
theorem rule1_condMass
    [StandardBorelSpace (V → β)]
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (treatment : V) (value : β)
    (outcome covariate conditioning : Finset V)
    (y : ∀ p : ((outcome : Finset V) : Set V),
      (intervenedNet graph hAcyclic treatment).stateSpace p.1)
    (z : ∀ p : ((covariate : Finset V) : Set V),
      (intervenedNet graph hAcyclic treatment).stateSpace p.1)
    (w : ∀ p : ((conditioning : Finset V) : Set V),
      (intervenedNet graph hAcyclic treatment).stateSpace p.1)
    (hTreat : treatment ∈ conditioning)
    (hOverlap : (outcome : Set V) ∩ (covariate : Set V) ⊆ (conditioning : Set V))
    (hsep : DSeparatedFull (deleteIncoming graph {treatment})
      (outcome : Set V) (covariate : Set V) (conditioning : Set V))
    (hpos :
      (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate z ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning w) ≠ 0) :
    (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) outcome y ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate z ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning w) /
      (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate z ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning w) =
    (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) outcome y ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning w) /
      (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning w) := by
  let net := network (β := β) (deleteIncoming graph {treatment})
    (deleteIncoming_acyclic graph hAcyclic {treatment})
  let μ : Measure net.JointSpace :=
    (intervenedCPT graph hAcyclic cpt treatment value).jointMeasure
  let _ : StandardBorelSpace net.JointSpace := by
    simpa [net, network, BayesianNetwork.JointSpace] using
      (inferInstance : StandardBorelSpace (V → β))
  have hTreatSet : treatment ∈ (conditioning : Set V) := Finset.mem_coe.mpr hTreat
  have hci :=
    rule1_condIndep graph hAcyclic cpt treatment value
      (outcome : Set V) (covariate : Set V) (conditioning : Set V)
      hTreatSet hOverlap hsep
  exact condIndepVertices_condMass (bn := net) (μ := μ)
    outcome covariate conditioning y z w hci hpos

end Mettapedia.GSLT.Causality.DoCalculus
