import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNXiDerivedBNRules

/-!
# Fork-BN Local-Markov Package

Semantic packaging for the fork BN (`A ← B → C`) local-Markov assumption family.
-/

namespace Mettapedia.Logic.PLNForkBNLocalMarkovPackage

open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-- Package assumption: every fork-BN discrete CPT satisfies local Markov. -/
class ForkBNLocalMarkovPackage
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace] : Prop where
  allLocalMarkov :
    ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure

/-- Build the package from an explicit family of local-Markov witnesses. -/
theorem forkBNLocalMarkovPackage_of
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    (hLM : ∀ cpt : forkBN.DiscreteCPT, HasLocalMarkovProperty forkBN cpt.jointMeasure) :
    ForkBNLocalMarkovPackage := ⟨hLM⟩

/-- Canonical bridge: fork-BN package implies generic BN compilation class. -/
instance
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    [ForkBNLocalMarkovPackage] :
    AllDiscreteCPTLocalMarkov (bn := forkBN) where
  localMarkov := ForkBNLocalMarkovPackage.allLocalMarkov

/-- Compatibility bridge from the Xi-derived alias family. -/
theorem forkBNLocalMarkovPackage_of_xiAlias
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    (hLM : Mettapedia.Logic.PLNXiDerivedBNRules.ForkBNLocalMarkovAll) :
    ForkBNLocalMarkovPackage := by
  exact forkBNLocalMarkovPackage_of (hLM := hLM)

/-- Compatibility bridge back to the Xi-derived alias family. -/
theorem xiAlias_of_forkBNLocalMarkovPackage
    [∀ v : Three, Fintype (forkBN.stateSpace v)]
    [∀ v : Three, DecidableEq (forkBN.stateSpace v)]
    [∀ v : Three, Inhabited (forkBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (forkBN.stateSpace v)]
    [StandardBorelSpace forkBN.JointSpace]
    [ForkBNLocalMarkovPackage] :
    Mettapedia.Logic.PLNXiDerivedBNRules.ForkBNLocalMarkovAll :=
  ForkBNLocalMarkovPackage.allLocalMarkov

end Mettapedia.Logic.PLNForkBNLocalMarkovPackage
