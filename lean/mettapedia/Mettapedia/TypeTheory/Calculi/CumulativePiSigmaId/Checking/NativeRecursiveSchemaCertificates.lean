import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeStructuralCertificateProposal
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.NativeCheckedJudgmentPresheaf

/-!
# Checked finite certificates for the recursive native schemas

The two existing open recursive right-hand sides have actual finite typing
certificates, independently checked at their previously authored result types
and contexts. The proposal computation is only a source of finite data.
The trusted replay checker validates the entire context and derivation.

These fixed receipts are inputs to the existing checked substitution action;
they do not assume typing of arbitrary instantiated recursive results.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.RecursiveSchemaCertificates

open Presentation NativeIndexedFamilies NativeCheckedSubstitution

set_option maxRecDepth 10000 in
def listContext : Context where
  arity := 6
  raw := Intrinsic.contextAPZSHeadTail
  code := (CertificateProposal.context Intrinsic.contextAPZSHeadTail).get (by decide +kernel)
  accepted := by decide +kernel

set_option maxRecDepth 10000 in
def listCons : JudgmentReceipt listContext where
  subject := Intrinsic.consIotaRight
  type := Intrinsic.consIotaResultType
  code := ((CertificateProposal.term 64 Intrinsic.contextAPZSHeadTail Intrinsic.consIotaRight).get
    (by decide +kernel)).2
  accepted := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def relationContext : Context where
  arity := 12
  raw := IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
  code := (CertificateProposal.context
    IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail).get (by decide +kernel)
  accepted := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
def relCons : JudgmentReceipt relationContext where
  subject := IntrinsicRelator.consIotaRight
  type := IntrinsicRelator.consIotaResultType
  code := ((CertificateProposal.term 64
    IntrinsicRelator.contextABRPZSSourceTargetHeadSourceTargetTailHeadTail
    IntrinsicRelator.consIotaRight).get (by decide +kernel)).2
  accepted := by decide +kernel

set_option maxRecDepth 10000 in
/-- A recursive-branch certificate is not a certificate for the unapplied
branch variable, even though that variable is independently well typed. -/
theorem list_missing_recursive_application_rejected :
    check listContext.raw (.var (2 : Fin 6)) listCons.type listContext.code listCons.code = false := by
  decide +kernel

set_option maxRecDepth 10000 in
theorem rel_missing_recursive_application_rejected :
    check relationContext.raw (.var (6 : Fin 12)) relCons.type relationContext.code relCons.code = false := by
  decide +kernel

#print axioms listContext
#print axioms listCons
#print axioms relationContext
#print axioms relCons
#print axioms list_missing_recursive_application_rejected
#print axioms rel_missing_recursive_application_rejected

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeJudgmentReplay.RecursiveSchemaCertificates
