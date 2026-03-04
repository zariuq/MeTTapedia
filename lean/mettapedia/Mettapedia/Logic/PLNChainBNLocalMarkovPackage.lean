import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNXiDerivedBNRules

/-!
# Chain-BN Local-Markov Package

Semantic packaging for the chain BN (`A → B → C`) local-Markov assumption family.
-/

namespace Mettapedia.Logic.PLNChainBNLocalMarkovPackage

open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-- Package assumption: every chain-BN discrete CPT satisfies local Markov. -/
class ChainBNLocalMarkovPackage
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace] : Prop where
  allLocalMarkov :
    ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure

/-- Build the package from an explicit family of local-Markov witnesses. -/
theorem chainBNLocalMarkovPackage_of
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    (hLM : ∀ cpt : chainBN.DiscreteCPT, HasLocalMarkovProperty chainBN cpt.jointMeasure) :
    ChainBNLocalMarkovPackage := ⟨hLM⟩

/-- Canonical bridge: chain-BN package implies generic BN compilation class. -/
instance
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [ChainBNLocalMarkovPackage] :
    AllDiscreteCPTLocalMarkov (bn := chainBN) where
  localMarkov := ChainBNLocalMarkovPackage.allLocalMarkov

/-- Compatibility bridge from the Xi-derived alias family. -/
theorem chainBNLocalMarkovPackage_of_xiAlias
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    (hLM : Mettapedia.Logic.PLNXiDerivedBNRules.ChainBNLocalMarkovAll) :
    ChainBNLocalMarkovPackage := by
  exact chainBNLocalMarkovPackage_of (hLM := hLM)

/-- Compatibility bridge back to the Xi-derived alias family. -/
theorem xiAlias_of_chainBNLocalMarkovPackage
    [∀ v : Three, Fintype (chainBN.stateSpace v)]
    [∀ v : Three, DecidableEq (chainBN.stateSpace v)]
    [∀ v : Three, Inhabited (chainBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (chainBN.stateSpace v)]
    [StandardBorelSpace chainBN.JointSpace]
    [ChainBNLocalMarkovPackage] :
    Mettapedia.Logic.PLNXiDerivedBNRules.ChainBNLocalMarkovAll :=
  ChainBNLocalMarkovPackage.allLocalMarkov

end Mettapedia.Logic.PLNChainBNLocalMarkovPackage
