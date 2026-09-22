import Mettapedia.GSLT.LanguageDef.CertificateGSLTOccurrencePreservingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenSearchModalAdequacy

/-!
# Exact-completion modal transport under ordered-linear interpretation

A derivation-valued theory interpretation need not preserve operational
resource use. When each rule template is ordered-linear, however, the
certificate translation retains the exact premise-use ledger. The modal
adequacy theorem then transports the closure diamond of an exact completed
state forward. This is a one-way claim at completed proof states, not a
general equivalence of operational GSLTs or their modal predicate theories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open OpenSearchMachine

/-- Ordered-linear proof translation preserves closure-modal reachability
of an exactly specified completed premise ledger. Target-only derivations
are not reflected, and primitive one-step modalities are not identified. -/
theorem preservesExactCompletionDiamond
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    (context : List Pattern) (goal : Pattern)
    (discharged : List (Fin context.length)) :
    gsltDiamond
        (OpenSearchModalAdequacy.theory source.definition context).closure
        (fun candidate => candidate =
          (⟨[], discharged⟩ : OpenSearchMachine.State context))
        ⟨[goal], []⟩ →
      gsltDiamond
        (OpenSearchModalAdequacy.theory target.definition context).closure
        (fun candidate => candidate =
          (⟨[], discharged⟩ : OpenSearchMachine.State context))
        ⟨[goal], []⟩ := by
  intro sourceReachable
  obtain ⟨⟨derivation, uses⟩⟩ :=
    (OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
      source.definition context goal discharged).mpr sourceReachable
  apply (OpenSearchModalAdequacy.exactDischarge_iff_closureDiamond
    target.definition context goal discharged).mp
  exact ⟨⟨interpretation.mapOpen derivation,
    (holeOccurrences_mapOpen interpretation linear derivation).trans uses⟩⟩

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation

#print axioms Mettapedia.GSLT.LanguageDef.CertificateGSLT.Interpretation.preservesExactCompletionDiamond
