import Mettapedia.TypeTheory.DisplayedPresheafCwf
import Mettapedia.TypeTheory.DisplayedPresheafSupport
import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily

/-!
# Exact certificate proofs in the displayed-presheaf CwF

The proof-relevant exact-ledger family is a type of the semantic presheaf
CwF. Its dependent last variable reads the actual authored proof retained
in the context extension. This is not yet an interpretation of authored
Prime dependent syntax or a source-faithful HOL/HOTG adequacy theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DisplayedPresheafCwf
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.GSLT.Topos
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- The actual checked derivation is recovered by the CwF's dependent
last variable, after inserting that derivation in the extended context. -/
theorem exactProof_displayedCwfVariable_retains
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    (exactDerivationDisplayedFamily_at definition context goal ledger)
      (((presheafCwf (ClassifyingContext definition)).vz
        (exactDerivationDisplayedFamily definition)).val
          ⟨Opposite.op context,
            ⟨(goal, ledger),
              (exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩⟩) =
        proof := by
  exact (exactDerivationDisplayedFamily_at definition context goal ledger).apply_symm_apply proof

/-- The predicate support of the actual coherent proof family is exactly
the closure-modal completion observation, at the same goal and ledger. -/
theorem exactProof_support_iff_closureDiamond
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length)) :
    (goal, ledger) ∈ (support (exactDerivationDisplayedFamily definition)).obj
        (Opposite.op context) ↔
      gsltDiamond
        (OpenSearchModalAdequacy.theory definition context.judgments).closure
        (fun candidate => candidate =
          (⟨[], ledger⟩ : OpenSearchMachine.State context.judgments))
        ⟨[goal], []⟩ := by
  rw [← exactDerivationFibre_nonempty_iff_closureDiamond]
  constructor
  · rintro ⟨evidence⟩
    exact ⟨exactDerivationDisplayedFamily_at definition context goal ledger evidence⟩
  · rintro ⟨proof⟩
    exact ⟨(exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩

/-- A supplied authored proof inhabits the predicate support, while the
CwF variable continues to recover that very proof in the retained layer. -/
theorem exactProof_support_and_retained_variable
    (definition : ValidatedCalculusLanguageDef)
    (context : ClassifyingContext definition)
    (goal : Pattern)
    (ledger : List (Fin context.judgments.length))
    (proof : exactDerivationFibre definition context goal ledger) :
    (goal, ledger) ∈ (support (exactDerivationDisplayedFamily definition)).obj
        (Opposite.op context) ∧
      (exactDerivationDisplayedFamily_at definition context goal ledger)
        (((presheafCwf (ClassifyingContext definition)).vz
          (exactDerivationDisplayedFamily definition)).val
            ⟨Opposite.op context,
              ⟨(goal, ledger),
                (exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩⟩) =
          proof :=
  ⟨⟨(exactDerivationDisplayedFamily_at definition context goal ledger).symm proof⟩,
    exactProof_displayedCwfVariable_retains definition context goal ledger proof⟩

#print axioms exactProof_displayedCwfVariable_retains
#print axioms exactProof_support_iff_closureDiamond
#print axioms exactProof_support_and_retained_variable

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
