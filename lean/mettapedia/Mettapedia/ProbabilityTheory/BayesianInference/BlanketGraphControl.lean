import Mettapedia.ProbabilityTheory.BayesianInference.BlanketFactorization
import Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork

/-! # The fork blanket in the existing Bayesian-network graph interface -/

namespace Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket.GraphControl

open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.InformationTheory
open Mettapedia.InformationTheory.FiniteRV

/-- Node zero is the blanket; nodes one and two are external and internal. -/
def graph : DirectedGraph (Fin 3) where
  edges u v := u = 0 ∧ (v = 1 ∨ v = 2)

theorem acyclic : graph.IsAcyclic := by
  intro v ⟨u, edge, back⟩
  obtain ⟨rfl, leaf⟩ := edge
  cases back with
  | refl => simp at leaf
  | step next _ =>
      have zero : u = 0 := next.1
      subst u
      simp at leaf

noncomputable def network : BayesianNetwork (Fin 3) where
  graph := graph
  acyclic := acyclic
  stateSpace _ := Bool
  measurableSpace _ := ⊤

/-- The queried external node and the internal node are absent from the
conditioning set. Its sole blanket member is the common parent. -/
theorem external_blanket : network.markovBlanket 1 = {0} := by
  ext node
  fin_cases node <;> simp [BayesianNetwork.markovBlanket, BayesianNetwork.parents,
    BayesianNetwork.children, DirectedGraph.parents, DirectedGraph.children, network, graph]

theorem internal_blanket : network.markovBlanket 2 = {0} := by
  ext node
  fin_cases node <;> simp [BayesianNetwork.markovBlanket, BayesianNetwork.parents,
    BayesianNetwork.children, DirectedGraph.parents, DirectedGraph.children, network, graph]

/-- Arbitrary normalized Boolean CPTs generate a genuine fork factorization.
Its conditional-information statement is the existing finite CI theorem. -/
theorem factorized_interface (blanket : Prob Bool) (external internal : Bool → Prob Bool) :
    network.markovBlanket 1 = {0} ∧ network.markovBlanket 2 = {0} ∧
      CondIndep (forkLaw blanket external internal).1 Prod.fst
        (fun x => x.2.1) (fun x => x.2.2) ∧
      condMutualInfo (forkLaw blanket external internal).1 Prod.fst
        (fun x => x.2.1) (fun x => x.2.2) = 0 :=
  ⟨external_blanket, internal_blanket, fork_conditionalIndependent blanket external internal,
    fork_conditionalInformation_zero blanket external internal⟩

end Mettapedia.ProbabilityTheory.BayesianInference.FiniteMarkovBlanket.GraphControl
