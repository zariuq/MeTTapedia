import Mettapedia.GSLT.LanguageDef.LF.FirstOrderCertifiedNormalization
import Mettapedia.GSLT.LanguageDef.LF.DTTBenchConversionReplay

/-!
# Proof-carrying conversion replay for DTTBench calibration

This calibration fixture applies the generic constant-free LF proof producer
uniformly to the frozen 31-entry replay corpus.  It adds no benchmark-specific
conversion rule: every candidate and goal is reduced by the same leftmost
beta/eta producer, each path is compiled to the validated first-order
conversion language, and acceptance requires a common terminal normal form.

The corpus is known during development.  Consequently this file establishes a
calibration replay, not the independent-family or unopened-endpoint gate.
-/

namespace Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingConversionReplay

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFDTTBenchConversionReplay
open Mettapedia.GSLT.LanguageDef.LFFirstOrderCertifiedNormalization

abbrev ReplayCase :=
  LFDTTBenchConversionReplay.ReplayCase

abbrev Certificate :=
  LFFirstOrderCertifiedNormalization.NormalFormCertificatePair

def certificationFuel : Nat := 512

/-- Uniformly produce independently checked normal-form paths for the raw
candidate and raw goal. -/
def certificateAt? (fuel : Nat) (entry : ReplayCase) :
    Option Certificate :=
  normalFormCertificatePair? fuel entry.candidate entry.goal

def certificate? (entry : ReplayCase) : Option Certificate :=
  certificateAt? certificationFuel entry

/-- Boolean projection used only to state a finite corpus result. -/
def certifiedAt (fuel : Nat) (entry : ReplayCase) : Bool :=
  (certificateAt? fuel entry).isSome

def certified (entry : ReplayCase) : Bool :=
  certifiedAt certificationFuel entry

theorem certificateAt?_sound
    (fuel : Nat) (entry : ReplayCase) (certificate : Certificate)
    (hcertificate : certificateAt? fuel entry = some certificate) :
    certificate.left.source = entry.candidate ∧
      certificate.right.source = entry.goal ∧
      certificate.left.Accepted ∧
      certificate.right.Accepted ∧
      firstStep? certificate.left.target = none ∧
      firstStep? certificate.right.target = none := by
  exact
    normalFormCertificatePair?_sound
      fuel entry.candidate entry.goal certificate hcertificate

/-- All 31 known replay entries independently produce proof-carrying beta/eta
paths for the raw term and raw type. -/
theorem all_cases_certified :
    LFDTTBenchConversionReplay.cases.all certified = true := by
  decide

/-- Producing normal-form paths is deliberately weaker than typing.  Even a
malformed candidate can normalize; the independent indexed typing proof still
rejects it. -/
theorem normalization_does_not_imply_typing :
    certified LFDTTBenchConversionReplay.malformed = true ∧
      LFDTTBenchConversionReplay.accepts
        LFDTTBenchConversionReplay.malformed = false := by
  exact ⟨by decide, LFDTTBenchConversionReplay.malformed_rejected⟩

/-- The same separation holds for a de-Bruijn capture mutation. -/
theorem normalization_does_not_hide_binder_capture :
    certified LFDTTBenchConversionReplay.binderCaptureMutation = true ∧
      LFDTTBenchConversionReplay.accepts
        LFDTTBenchConversionReplay.binderCaptureMutation = false := by
  exact
    ⟨by decide,
      LFDTTBenchConversionReplay.binderCaptureMutation_rejected⟩

/-- A deliberately tiny fuel budget is not silently accepted as a completed
conversion on a nontrivial replay. -/
theorem insufficient_fuel_not_certified :
    certifiedAt 1 LFDTTBenchConversionReplay.replay_Eq_symm = false := by
  decide

#print axioms certificateAt?_sound
#print axioms all_cases_certified
#print axioms normalization_does_not_imply_typing
#print axioms normalization_does_not_hide_binder_capture
#print axioms insufficient_fuel_not_certified

end Mettapedia.GSLT.LanguageDef.LFDTTBenchProofCarryingConversionReplay
