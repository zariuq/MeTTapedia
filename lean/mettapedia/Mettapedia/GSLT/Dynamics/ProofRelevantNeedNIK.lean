import Mettapedia.GSLT.Dynamics.ProofRelevantNeedValuation
import Mettapedia.GSLT.LanguageDef.InteractionEventAuthority

/-!
# NIK authorities for modular proof-relevant Need

The generic interaction-event authority applies directly to the Need cell
protocol and to every selected operator fragment.  Local certificates retain
the exact event and indexed protocol evidence; finite-trace closure is supplied
once by NIK.

These are Lean-native certificates.  A serialized Prime/CeTTa certificate
still requires a checked codec and lowering into this authority; byte-level
adequacy is not asserted here.
-/

namespace Mettapedia.GSLT.Dynamics.ProofRelevantNeed

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.InteractionEvent
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.InteractionEventAuthority

universe uAuthority uCell uOrigin uValue uStableFault uRetryableFault

local instance cellTheoryTermDecidableEq
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    DecidableEq
      (cellTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell).Term := by
  change DecidableEq (CellState Origin Value StableFault)
  infer_instance

local instance fragmentTheoryTermDecidableEq
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    DecidableEq
      (fragmentTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) operators RetryableFault cell).Term := by
  change DecidableEq (CellState Origin Value StableFault)
  infer_instance

/-- Local NIK authority for the complete proof-relevant Need protocol. -/
abbrev nikStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (RetryableFault : Type uRetryableFault) (cell : Cell) :=
  Mettapedia.GSLT.LanguageDef.InteractionEventAuthority.stepAuthority authorityId
    (interactionPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell)

theorem nikStepAuthority_complete {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (RetryableFault : Type uRetryableFault) (cell : Cell) :
    (nikStepAuthority (Cell := Cell) (Origin := Origin) (Value := Value)
      (StableFault := StableFault) authorityId RetryableFault cell).Complete :=
  Mettapedia.GSLT.LanguageDef.InteractionEventAuthority.stepAuthority_complete authorityId
    (interactionPresentation_complete (Origin := Origin) (Value := Value)
      (StableFault := StableFault) RetryableFault cell)

/-- The same construction for a language-selected operator fragment. -/
abbrev fragmentNIKStepAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) :=
  Mettapedia.GSLT.LanguageDef.InteractionEventAuthority.stepAuthority authorityId
    (fragmentPresentation (Origin := Origin) (Value := Value)
      (StableFault := StableFault) operators RetryableFault cell)

theorem fragmentNIKStepAuthority_complete
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (operators : OperatorSet) (RetryableFault : Type uRetryableFault)
    (cell : Cell) :
    (fragmentNIKStepAuthority (Cell := Cell) (Origin := Origin)
      (Value := Value) (StableFault := StableFault) authorityId operators
      RetryableFault cell).Complete :=
  Mettapedia.GSLT.LanguageDef.InteractionEventAuthority.stepAuthority_complete authorityId
    (fragmentPresentation_complete (Origin := Origin) (Value := Value)
      (StableFault := StableFault) operators RetryableFault cell)

/-- Free NIK finite-trace closure of the complete protocol. -/
abbrev nikFiniteTraceAuthority {AuthorityId : Type uAuthority}
    (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (RetryableFault : Type uRetryableFault) (cell : Cell) :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLT.finiteTraceAuthority
    (nikStepAuthority (Cell := Cell) (Origin := Origin) (Value := Value)
      (StableFault := StableFault) authorityId RetryableFault cell)

/-- Lean-native certificate existence is exactly finite Need reachability. -/
theorem nikFiniteTraceAuthority_correspondence
    {AuthorityId : Type uAuthority} (authorityId : AuthorityId)
    {Cell : Type uCell} {Origin : Type uOrigin} {Value : Type uValue}
    {StableFault : Type uStableFault}
    [DecidableEq Origin] [DecidableEq Value] [DecidableEq StableFault]
    (RetryableFault : Type uRetryableFault) (cell : Cell)
    (claim : TraceClaim
      (cellTheory (Origin := Origin) (Value := Value)
        (StableFault := StableFault) RetryableFault cell)) :
    (Exists fun certificate :
        (nikFiniteTraceAuthority (Cell := Cell) (Origin := Origin)
          (Value := Value) (StableFault := StableFault) authorityId
          RetryableFault cell).Certificate =>
      (nikFiniteTraceAuthority (Cell := Cell) (Origin := Origin)
        (Value := Value) (StableFault := StableFault) authorityId
        RetryableFault cell).check
        claim certificate = true) ↔ claim.Meaning :=
  Mettapedia.GSLT.LanguageDef.CertificateGSLT.finiteTraceAuthority_correspondence
    (nikStepAuthority (Cell := Cell) (Origin := Origin) (Value := Value)
      (StableFault := StableFault) authorityId RetryableFault cell)
    (nikStepAuthority_complete (Cell := Cell) (Origin := Origin)
      (Value := Value) (StableFault := StableFault) authorityId
      RetryableFault cell) claim

/-! ## Positive and negative canaries -/

namespace NIKCanary

inductive AuthorityId where
  | need
deriving DecidableEq, Repr

abbrev DemoTheory :=
  cellTheory (Origin := Nat) (Value := Nat) (StableFault := Nat) Nat 0

abbrev DemoPresentation :=
  interactionPresentation (Origin := Nat) (Value := Nat)
    (StableFault := Nat) Nat 0

abbrev demoStepAuthority :=
  nikStepAuthority (Cell := Nat) (Origin := Nat) (Value := Nat)
    (StableFault := Nat) AuthorityId.need Nat 0

abbrev demoFiniteTraceAuthority :=
  nikFiniteTraceAuthority (Cell := Nat) (Origin := Nat) (Value := Nat)
    (StableFault := Nat) AuthorityId.need Nat 0

def allocateCertificate : EventCertificate DemoPresentation where
  source := .absent
  event :=
    { site := .allocate 0 7
      target := .suspended 7
      evidence := .allocate 7 }

def beginCertificate : EventCertificate DemoPresentation where
  source := .suspended 7
  event :=
    { site := .beginEvaluation 0 7
      target := .evaluating 7
      evidence := .beginEvaluation 7 }

def commitCertificate : EventCertificate DemoPresentation where
  source := .evaluating 7
  event :=
    { site := .commitValue 0 7 11
      target := .cachedValue 7 11
      evidence := .commitValue 7 11 }

theorem allocation_is_accepted :
    demoStepAuthority.check
      { source := .absent, target := .suspended 7 }
      allocateCertificate = true := by
  decide

/-- Negative canary: valid occurrence evidence cannot be replayed under a
different submitted target. -/
theorem allocation_wrong_target_is_rejected :
    demoStepAuthority.check
      { source := .absent, target := .evaluating 7 }
      allocateCertificate = false := by
  decide

def successfulCertificate :
    TraceCertificate DemoTheory
      demoStepAuthority.Certificate where
  links :=
    [ { target := .suspended 7, evidence := allocateCertificate }
    , { target := .evaluating 7, evidence := beginCertificate }
    , { target := .cachedValue 7 11, evidence := commitCertificate } ]

theorem finite_success_is_accepted :
    demoFiniteTraceAuthority.check
      { source := .absent, target := .cachedValue 7 11 }
      successfulCertificate = true := by
  decide

end NIKCanary

end Mettapedia.GSLT.Dynamics.ProofRelevantNeed
