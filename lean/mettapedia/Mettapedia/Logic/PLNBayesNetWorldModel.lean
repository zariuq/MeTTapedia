import Mettapedia.Logic.PLNWorldModel
import Mettapedia.Logic.PLNJointEvidence
import Mettapedia.ProbabilityTheory.BayesianNetworks.DirectedGraph

/-!
# Bayesian-Network-Style World Models for PLN (Boolean CPT Evidence)

This module adds a first tractable sublayer under the `PLNWorldModel.WorldModel` interface:

* A Bayesian-network-style posterior state is represented by **CPT evidence**:
  for each node `v` and each configuration of its parents, we store binary `Evidence`
  (counts supporting `v=true` vs `v=false` under that parent configuration).

This is still *evidence-first*: revision is additive (monoid `+`), and queries extract
`Evidence`.  The key bridge to the complete joint layer is an additive projection:

* from `JointEvidence n` (Dirichlet pseudo-counts over all `2^n` worlds),
  we can extract CPT evidence for any fixed BN graph by summing over compatible worlds.

This projection is a genuine monoid homomorphism at the evidence level, but it is not
information-preserving: it forgets correlations not captured by the BN factorization.
-/

namespace Mettapedia.Logic.PLNBayesNetWorldModel

open scoped Classical ENNReal

open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.CompletePLN
open Mettapedia.Logic.PLNJointEvidence
open Mettapedia.Logic.PLNJointEvidence.JointEvidence
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-! ## Boolean Bayesian-network graph (over propositional atoms `Fin n`) -/

/-- A Boolean BN structure over `n` propositional atoms: just a DAG on `Fin n`. -/
structure BoolBayesNet (n : ℕ) where
  graph : DirectedGraph (Fin n)
  acyclic : graph.IsAcyclic

namespace BoolBayesNet

variable {n : ℕ} (bn : BoolBayesNet n)

/-! ## Parent configurations -/

variable [DecidableRel bn.graph.edges]

/-- A parent configuration for a node `v`: an assignment of Booleans to its parents. -/
abbrev ParentConfig (v : Fin n) : Type :=
  ({ u : Fin n // u ∈ bn.graph.parents v } → Bool)

/-- A query for a single Boolean CPT entry: a node `v` plus a parent configuration. -/
abbrev CPTQuery : Type :=
  Σ v : Fin n, ParentConfig (bn := bn) v

/-! ## CPT evidence states -/

/-- A Bayesian-network-style posterior state: evidence for each CPT entry. -/
abbrev CPTState : Type :=
  CPTQuery (bn := bn) → Evidence

noncomputable instance : EvidenceType (CPTState (bn := bn)) where

/-! ## World-model instance (lookup) -/

noncomputable instance : WorldModel (CPTState (bn := bn)) (CPTQuery (bn := bn)) where
  evidence W q := W q
  evidence_add := by
    intro W₁ W₂ q
    rfl

/-! ## Extracting CPT evidence from complete joint evidence -/

/-- Do the parents of `v` in world `w` match the supplied parent configuration `pa`? -/
def parentsMatch (v : Fin n) (pa : ParentConfig (bn := bn) v) (w : Fin (2 ^ n)) : Bool :=
  decide (∀ u : { u : Fin n // u ∈ bn.graph.parents v }, worldToAssignment n w u.val = pa u)

/-- CPT evidence for a node `v` under a parent configuration `pa`, extracted from joint evidence. -/
noncomputable def cptEvidenceOfJoint (E : JointEvidence n) (v : Fin n)
    (pa : ParentConfig (bn := bn) v) : Evidence :=
  ⟨countWorld (n := n) (E := E) (fun w => parentsMatch (bn := bn) v pa w && worldToAssignment n w v),
   countWorld (n := n) (E := E)
      (fun w => parentsMatch (bn := bn) v pa w && !(worldToAssignment n w v))⟩

theorem cptEvidenceOfJoint_add (E₁ E₂ : JointEvidence n) (v : Fin n)
    (pa : ParentConfig (bn := bn) v) :
    cptEvidenceOfJoint (bn := bn) (n := n) (E := E₁ + E₂) v pa =
      cptEvidenceOfJoint (bn := bn) (n := n) (E := E₁) v pa +
        cptEvidenceOfJoint (bn := bn) (n := n) (E := E₂) v pa := by
  ext <;> simp [cptEvidenceOfJoint, countWorld_add, Evidence.hplus_def]

/-- Project a complete joint-evidence state to BN CPT evidence by marginalization. -/
noncomputable def toCPTState (E : JointEvidence n) : CPTState (bn := bn) :=
  fun q => cptEvidenceOfJoint (bn := bn) (n := n) (E := E) q.1 q.2

theorem toCPTState_add (E₁ E₂ : JointEvidence n) :
    toCPTState (bn := bn) (n := n) (E := E₁ + E₂) =
      toCPTState (bn := bn) (n := n) (E := E₁) + toCPTState (bn := bn) (n := n) (E := E₂) := by
  funext q
  simpa [toCPTState, Pi.add_apply] using cptEvidenceOfJoint_add (bn := bn) (n := n) (E₁ := E₁)
    (E₂ := E₂) q.1 q.2

/-! ## Joint evidence as a world model for CPT queries -/

noncomputable instance : WorldModel (JointEvidence n) (CPTQuery (bn := bn)) where
  evidence E q := cptEvidenceOfJoint (bn := bn) (n := n) (E := E) q.1 q.2
  evidence_add E₁ E₂ q := by
    simpa using cptEvidenceOfJoint_add (bn := bn) (n := n) (E₁ := E₁) (E₂ := E₂) q.1 q.2

end BoolBayesNet

end Mettapedia.Logic.PLNBayesNetWorldModel
