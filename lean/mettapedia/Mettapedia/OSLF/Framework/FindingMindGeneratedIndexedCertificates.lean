import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedPresheafReadout
import Mettapedia.TypeTheory.DisplayedPresheafSlice
import Mettapedia.OSLF.Framework.FindingMindNativeInteraction

/-!
# Generated indexed types retain actual scoped interaction certificates

The original map is the comprehension projection of the independent
scoped event-certificate family. Its generated indexed type recovers the
whole certificate, including the actual occurrence and dependent target
witness. The complete future section transports those same receipts.
The initial empty fibre and distinct equal-endpoint occurrences are checked.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.Framework.FindingMindGeneratedIndexedCertificates

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open RepresentableIndexedDeclarations
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.DisplayedPresheafSlice
open FindingMindNativeInteraction

noncomputable section

abbrev certificateFamily := scopedEvents.certificates postcondition
abbrev certificateValues := totalSpace certificateFamily
abbrev certificateProjection := totalProjection certificateFamily
abbrev indexed := PresheafReadout.indexed certificateProjection
abbrev Base := PresheafReadout.Base Stages

abbrev NativeCertificate (stage : Nat) :=
  PresheafReadout.NativeFibre certificateProjection (op stage) source

def certificateEquiv (stage : Nat) :
    NativeCertificate stage ≃ certificateFamily.obj ⟨world stage, source⟩ :=
  (PresheafReadout.pointFibreEquiv certificateProjection (op stage) source).trans
    (projectionFibreEquiv certificateFamily ⟨world stage, source⟩).symm

def nativeCertificate (stage : Nat) (certificate : certificateFamily.obj ⟨world stage, source⟩) :
    NativeCertificate stage :=
  PresheafReadout.encodePoint certificateProjection (op stage) source ⟨source, certificate⟩ rfl

theorem complete_current_readout (stage : Nat)
    (certificate : certificateFamily.obj ⟨world stage, source⟩) :
    certificateEquiv stage (nativeCertificate stage certificate) = certificate := by
  change (projectionFibreEquiv certificateFamily ⟨world stage, source⟩).symm
    (PresheafReadout.decodePoint certificateProjection (op stage) source
      (nativeCertificate stage certificate)) = certificate
  rw [nativeCertificate, PresheafReadout.decode_encode]
  rfl

def generatedType :
    Derivation (signature Base) (.type (objectContext indexed.target) (fibreType indexed (.var 0))) :=
  genericFibreFormed indexed

theorem generated_type_reads_the_actual_certificate_fibre :
    (model Base).evaluateType (objectScope indexed.target) (fibreType indexed (.var 0)) =
      some (fibreMeaning indexed) := generic_fibre_read indexed

theorem generated_forget_reads_the_actual_certificate_section :
    (model Base).evaluateTerm (fibreScope indexed) (genericForget indexed) =
      some ⟨forgetType indexed, forgetValue indexed⟩ := generic_forget_read indexed

theorem initial_generated_fibre_is_empty : IsEmpty (NativeCertificate 0) :=
  ⟨fun supplied => no_scoped_certificate_initial ⟨certificateEquiv 0 supplied⟩⟩

def firstScoped (stage : Nat) (witness : Fin (stage + 2)) :
    certificateFamily.obj ⟨world (stage + 1), source⟩ :=
  scopedEvents.introduce postcondition (world (stage + 1))
    ⟨⟨source, firstEvent⟩, ⟨rfl, Nat.zero_lt_succ _⟩⟩ ⟨⟨rfl⟩, witness⟩

def secondScoped (stage : Nat) (witness : Fin (stage + 2)) :
    certificateFamily.obj ⟨world (stage + 1), source⟩ :=
  scopedEvents.introduce postcondition (world (stage + 1))
    ⟨⟨source, secondEvent⟩, ⟨rfl, Nat.zero_lt_succ _⟩⟩ ⟨⟨rfl⟩, witness⟩

theorem every_future_generated_fibre_is_inhabited (stage : Nat) :
    Nonempty (NativeCertificate (stage + 1)) :=
  ⟨nativeCertificate (stage + 1) (firstScoped stage ⟨0, Nat.zero_lt_succ _⟩)⟩

theorem equal_endpoints_retain_distinct_generated_values (stage : Nat) (witness : Fin (stage + 2)) :
    nativeCertificate (stage + 1) (firstScoped stage witness) ≠
      nativeCertificate (stage + 1) (secondScoped stage witness) := by
  intro same
  have certificates := congrArg (certificateEquiv (stage + 1)) same
  rw [complete_current_readout, complete_current_readout] at certificates
  have positions := congrArg (fun certificate : certificateFamily.obj
    ⟨world (stage + 1), source⟩ => certificate.val.1.val.2.evidence.selected.outputIndex) certificates
  exact Nat.zero_ne_one positions

theorem actual_endpoint_readouts_agree (stage : Nat) (witness : Fin (stage + 2)) :
    (scopedEvents.resultReadout postcondition).app (world (stage + 1))
      ⟨source, certificateEquiv (stage + 1) (nativeCertificate (stage + 1) (firstScoped stage witness))⟩ =
    (scopedEvents.resultReadout postcondition).app (world (stage + 1))
      ⟨source, certificateEquiv (stage + 1) (nativeCertificate (stage + 1) (secondScoped stage witness))⟩ := by
  rw [complete_current_readout, complete_current_readout]
  rfl

theorem complete_future_section_readout (stage : Nat)
    (certificate : certificateFamily.obj ⟨world stage, source⟩) :
    ((decode indexed (op (PresheafReadout.worldObject (op stage)))
      (PresheafReadout.argument certificateProjection (op stage) source)
      (nativeCertificate stage certificate)).val.down.app (world (stage + 1)))
        (advance stage).unop = certificateValues.map (advance stage) ⟨source, certificate⟩ := by
  have futureRead := PresheafReadout.complete_future_readout certificateProjection
    (op stage) (op (stage + 1)) (advance stage).unop source (nativeCertificate stage certificate)
  have initialRead := congrArg Subtype.val
    (PresheafReadout.decode_encode certificateProjection (op stage) source ⟨source, certificate⟩ rfl)
  exact futureRead.trans (congrArg (fun value => certificateValues.map (advance stage) value) initialRead)

theorem wrong_complete_current_certificate_cannot_encode (stage : Nat)
    (first second : certificateFamily.obj ⟨world stage, source⟩) (different : first ≠ second) :
    certificateEquiv stage (nativeCertificate stage first) ≠ second := by
  rw [complete_current_readout]
  exact different

end

end Mettapedia.OSLF.Framework.FindingMindGeneratedIndexedCertificates
