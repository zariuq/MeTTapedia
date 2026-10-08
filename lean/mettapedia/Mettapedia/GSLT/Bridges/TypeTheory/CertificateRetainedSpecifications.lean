import Mettapedia.GSLT.Bridges.TypeTheory.CertificateRetainedTransport
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

/-!
# Universal readout of actual ordered premise-use certificates

The target specification records the complete premise ledger of the
supplied authored proof. Its map is constructed by native sum elimination
and computes on that proof; distinct equally labelled assumptions still
have distinct readouts. No proof checker is claimed to execute in rho.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Bridges.TypeTheory.CertificateRetainedSpecifications

open _root_.CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafSliceSubstitution
open DisplayedPresheafEvidenceUniversal CertificateRetainedTransport

def ledgerSpecification (definition : ValidatedCalculusLanguageDef) :
    DisplayedFamily (goalFace definition) := observationFibreFamily (forgetLedger definition)

def sourceLedgerReadout (definition : ValidatedCalculusLanguageDef) :
    exactDerivationDisplayedFamily definition ⟶
      reindexDisplayed (forgetLedger definition) (ledgerSpecification definition) where
  app point := TypeCat.ofHom (fun _ => ⟨point.2, rfl⟩)
  naturality _ _ arrow := by
    ext evidence
    apply Subtype.ext
    exact arrow.property.symm

def ledgerReadout (definition : ValidatedCalculusLanguageDef) :
    retainedProofFamily definition ⟶ ledgerSpecification definition :=
  descend (forgetLedger definition) (sourceLedgerReadout definition)

/-- The target specification reports exactly the ordered ledger produced
by the original derivation, including repeated labels and use positions. -/
theorem ledgerReadout_exact (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition) (goal : Pattern)
    (proof : OpenDerivation definition context.judgments goal) :
    ((ledgerReadout definition).app ⟨Opposite.op context, goal⟩
      (carryProof definition context goal proof)).val.2 =
        OpenSearchMachine.holeOccurrences proof := by
  have computes := descend_unit (forgetLedger definition) (sourceLedgerReadout definition)
    ⟨Opposite.op context, (goal, OpenSearchMachine.holeOccurrences proof)⟩ ⟨⟨goal, proof⟩, rfl⟩
  exact congrArg (fun receipt => receipt.val.2) computes

theorem ledgerReadout_unique (definition : ValidatedCalculusLanguageDef)
    (candidate : retainedProofFamily definition ⟶ ledgerSpecification definition)
    (computes : DisplayedPresheafEvidenceUniversal.restrict (forgetLedger definition) candidate =
      sourceLedgerReadout definition) : candidate = ledgerReadout definition :=
  descend_unique (forgetLedger definition) (sourceLedgerReadout definition) candidate computes

theorem duplicate_readouts_distinct (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :
    (ledgerReadout definition).app ⟨Opposite.op ⟨[goal, goal]⟩, goal⟩
        (carryProof definition ⟨[goal, goal]⟩ goal (.assumption (context := [goal, goal]) (0 : Fin 2))) ≠
      (ledgerReadout definition).app ⟨Opposite.op ⟨[goal, goal]⟩, goal⟩
        (carryProof definition ⟨[goal, goal]⟩ goal (.assumption (context := [goal, goal]) (1 : Fin 2))) := by
  intro same
  have ledgers := congrArg (fun receipt => receipt.val.2) same
  rw [ledgerReadout_exact, ledgerReadout_exact] at ledgers
  exact Fin.zero_ne_one (List.singleton_injective ledgers)

end Mettapedia.GSLT.Bridges.TypeTheory.CertificateRetainedSpecifications
