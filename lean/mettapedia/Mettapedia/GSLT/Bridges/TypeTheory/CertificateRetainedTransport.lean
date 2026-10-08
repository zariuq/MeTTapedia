import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceCoherence

/-!
# Native dependent transport of actual authored certificates

Forgetting a ledger from the observed goal need not erase it from the
dependent certificate. The native dependent sum retains the exact source
goal-and-ledger point and its open derivation. Equal-labeled assumptions
remain distinct; direct observation of their goals cannot recover them.
The original operational route is still computed from the retained proof.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Bridges.TypeTheory.CertificateRetainedTransport

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafEvidenceTransport

def forgetLedger (definition : ValidatedCalculusLanguageDef) :
    goalLedgerFace definition ⟶ goalFace definition where
  app _ := TypeCat.ofHom Prod.fst
  naturality _ _ _ := rfl

def retainedProofFamily (definition : ValidatedCalculusLanguageDef) :
    DisplayedFamily (goalFace definition) :=
  transport (forgetLedger definition) (exactDerivationDisplayedFamily definition)

def carryProof (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) (goal : Pattern)
    (proof : OpenDerivation definition context.judgments goal) :
    (retainedProofFamily definition).obj ⟨Opposite.op context, goal⟩ :=
  (unit (forgetLedger definition) (exactDerivationDisplayedFamily definition)).app
    ⟨Opposite.op context, (goal, OpenSearchMachine.holeOccurrences proof)⟩
    ⟨⟨goal, proof⟩, rfl⟩

theorem carryProof_exact_ledger (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) (goal : Pattern)
    (proof : OpenDerivation definition context.judgments goal) :
    (carryProof definition context goal proof).val.1.2 =
      OpenSearchMachine.holeOccurrences proof := rfl

theorem carryProof_exact_derivation (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) (goal : Pattern)
    (proof : OpenDerivation definition context.judgments goal) :
    (carryProof definition context goal proof).val.2.val = ⟨goal, proof⟩ := rfl

/-- The operational receipt is made from the supplied proof, and inversion
of that receipt returns the same derivation. -/
theorem retained_route_recovers_proof (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) (goal : Pattern)
    (proof : OpenDerivation definition context.judgments goal) :
    OpenSearchMachine.derivationOfCompleteRoute
        (OpenSearchMachine.completeRouteReceipt
          (carryProof definition context goal proof).val.2.val.2).2 = proof :=
  OpenSearchMachine.derivationOfCompleteRoute_runToCompletion proof

theorem duplicate_premises_distinct (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) :
    carryProof definition ⟨[goal, goal]⟩ goal
        (.assumption (context := [goal, goal]) (0 : Fin 2)) ≠
      carryProof definition ⟨[goal, goal]⟩ goal
        (.assumption (context := [goal, goal]) (1 : Fin 2)) := by
  intro same
  have ledgers := congrArg (fun receipt => receipt.val.1.2) same
  change [(0 : Fin 2)] = [(1 : Fin 2)] at ledgers
  exact Fin.zero_ne_one (List.singleton_injective ledgers)

/-- Erased observation has no inverse recovering the supplied certificate. -/
theorem goal_alone_cannot_recover (definition : ValidatedCalculusLanguageDef)
    (goal : Pattern) :
    ¬ ∃ recover : Pattern →
        (retainedProofFamily definition).obj ⟨Opposite.op ⟨[goal, goal]⟩, goal⟩,
      recover goal = carryProof definition ⟨[goal, goal]⟩ goal
        (.assumption (context := [goal, goal]) (0 : Fin 2)) ∧
        recover goal = carryProof definition ⟨[goal, goal]⟩ goal
          (.assumption (context := [goal, goal]) (1 : Fin 2)) := by
  rintro ⟨_, first, second⟩
  exact duplicate_premises_distinct definition goal (first.symm.trans second)

end Mettapedia.GSLT.Bridges.TypeTheory.CertificateRetainedTransport
