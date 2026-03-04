import Mettapedia.Logic.PLNBNCompilation
import Mettapedia.Logic.PLNXiDerivedBNRules

/-!
# Collider-BN Local-Markov Package

Semantic packaging for the collider BN (`A → C ← B`) local-Markov assumption family.
-/

namespace Mettapedia.Logic.PLNColliderBNLocalMarkovPackage

open Mettapedia.Logic.PLNBNCompilation.BNWorldModel
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-- Package assumption: every collider-BN discrete CPT satisfies local Markov. -/
class ColliderBNLocalMarkovPackage
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace] : Prop where
  allLocalMarkov :
    ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure

/-- Build the package from an explicit family of local-Markov witnesses. -/
theorem colliderBNLocalMarkovPackage_of
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    (hLM : ∀ cpt : colliderBN.DiscreteCPT, HasLocalMarkovProperty colliderBN cpt.jointMeasure) :
    ColliderBNLocalMarkovPackage := ⟨hLM⟩

/-- Canonical bridge: collider-BN package implies generic BN compilation class. -/
instance
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    [ColliderBNLocalMarkovPackage] :
    AllDiscreteCPTLocalMarkov (bn := colliderBN) where
  localMarkov := ColliderBNLocalMarkovPackage.allLocalMarkov

/-- Compatibility bridge from the Xi-derived alias family. -/
theorem colliderBNLocalMarkovPackage_of_xiAlias
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    (hLM : Mettapedia.Logic.PLNXiDerivedBNRules.ColliderBNLocalMarkovAll) :
    ColliderBNLocalMarkovPackage := by
  exact colliderBNLocalMarkovPackage_of (hLM := hLM)

/-- Compatibility bridge back to the Xi-derived alias family. -/
theorem xiAlias_of_colliderBNLocalMarkovPackage
    [∀ v : Three, Fintype (colliderBN.stateSpace v)]
    [∀ v : Three, DecidableEq (colliderBN.stateSpace v)]
    [∀ v : Three, Inhabited (colliderBN.stateSpace v)]
    [∀ v : Three, StandardBorelSpace (colliderBN.stateSpace v)]
    [StandardBorelSpace colliderBN.JointSpace]
    [ColliderBNLocalMarkovPackage] :
    Mettapedia.Logic.PLNXiDerivedBNRules.ColliderBNLocalMarkovAll :=
  ColliderBNLocalMarkovPackage.allLocalMarkov

end Mettapedia.Logic.PLNColliderBNLocalMarkovPackage
