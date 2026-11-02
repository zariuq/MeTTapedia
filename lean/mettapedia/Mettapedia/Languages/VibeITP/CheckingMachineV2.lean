import Mettapedia.Languages.VibeITP.Presentation.SimultaneousCompleteness
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTBorrowedCursor
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable

/-! Realizations of the static v2 calculus through the existing portable
calculus reader, proof category and retained graph checker. The selected
theory's axioms and definitions remain explicit. Execution observations and
native implementation refinement are separate obligations. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.CheckingMachineV2

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.OSLF.MeTTaIL.Syntax
open Presentation Presentation.SimultaneousPresentation Spec

def kernelModule (T : Theory) (allocated : Nat) : String :=
  ModuleFormat.Portable.renderCalculus (validatedV2 T allocated).val

theorem kernelModule_read (T : Theory) (allocated : Nat) :
    ModuleFormat.Portable.readValidatedCalculus? (kernelModule T allocated) =
      some (validatedV2 T allocated) :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

theorem derives_iff_classifyingArrow {T : Theory} {allocated : Nat}
    (hosted : Hosted T allocated) (claim : Term) :
    DerivesV2 T claim ↔
      Nonempty ((⟨[]⟩ : CertificateGSLT.ClassifyingContext (validatedV2 T allocated)) ⟶
        ⟨[jThm (encTerm T.sig claim)]⟩) := by
  let comparison := CertificateGSLT.ClassifyingContext.closedDerivationEquiv
    (validatedV2 T allocated) (jThm (encTerm T.sig claim))
  constructor
  · intro original
    obtain ⟨article, accepted⟩ := (derivesV2_iff_checkRaw hosted claim).mp original
    obtain ⟨proof⟩ := checkRaw_soundness accepted
    exact ⟨comparison proof⟩
  · rintro ⟨arrow⟩
    let proof := comparison.symm arrow
    exact checkRaw_soundV2 hosted (checkRaw_erase proof)

def kernelCheckingObject (T : Theory) (allocated : Nat)
    (source : CertificateGSLT.BorrowedCursor.Source) :=
  CertificateGSLT.BorrowedCursor.checkingObject (validatedV2 T allocated) source

theorem derives_iff_graph {T : Theory} {allocated : Nat}
    (hosted : Hosted T allocated) (claim : Term) :
    DerivesV2 T claim ↔
      ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node Pattern
          (CertificateGSLT.BorrowedCursor.AdmittedInstance (validatedV2 T allocated)) Nat))
        (cache : Array Pattern) (root : Nat),
        Mettapedia.Logic.DerivationGraph.replay
          (CertificateGSLT.BorrowedCursor.presentation (validatedV2 T allocated)).ruleWitness nodes = some cache ∧
          cache[root]? = some (jThm (encTerm T.sig claim)) := by
  rw [derivesV2_iff_checkRaw hosted claim]
  constructor
  · rintro ⟨article, accepted⟩
    exact (CertificateGSLT.BorrowedCursor.authored_source_and_graph
      ⟨validatedV2 T allocated⟩ _).2.mp (checkRaw_soundness accepted)
  · intro graph
    obtain ⟨derivation⟩ := (CertificateGSLT.BorrowedCursor.authored_source_and_graph
      ⟨validatedV2 T allocated⟩ _).2.mpr graph
    exact ⟨derivation.erase, checkRaw_erase derivation⟩

theorem checked_root_derives {T : Theory} {allocated : Nat}
    (hosted : Hosted T allocated) (source : CertificateGSLT.BorrowedCursor.Source)
    (cursor : CertificateGSLT.BorrowedCursor.Cursor (validatedV2 T allocated) source)
    (address : Nat) (claim : Term)
    (found : Mettapedia.Logic.DerivationGraph.BorrowedCursor.rootAt cursor.state address =
      some (jThm (encTerm T.sig claim))) : DerivesV2 T claim := by
  obtain ⟨article, accepted⟩ := CertificateGSLT.BorrowedCursor.checked_root_has_source_certificate
    (validatedV2 T allocated) source cursor address _ found
  exact checkRaw_soundV2 hosted accepted

theorem finished_iff_licensed (T : Theory) (allocated : Nat)
    (source : CertificateGSLT.BorrowedCursor.Source)
    (cursor : CertificateGSLT.BorrowedCursor.Cursor (validatedV2 T allocated) source)
    (schedule : List Nat) :
    (∃ fuel events report, (kernelCheckingObject T allocated source).machine.run fuel
      (Mettapedia.Machines.Cursor.ProofChecking.start cursor schedule) =
        (events, .finished report) ∧ report.accepted = true) ↔
      ∃ after, CertificateGSLT.BorrowedCursor.LicensedRun
        (validatedV2 T allocated) source cursor.state schedule after :=
  CertificateGSLT.BorrowedCursor.finished_iff_licensed (validatedV2 T allocated) source cursor schedule

#print axioms kernelModule_read
#print axioms derives_iff_classifyingArrow
#print axioms derives_iff_graph
#print axioms checked_root_derives

end Mettapedia.Languages.VibeITP.CheckingMachineV2
