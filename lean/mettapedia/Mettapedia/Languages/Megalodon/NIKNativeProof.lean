import Mettapedia.GSLT.LanguageDef.NIKMetalogic
import Mettapedia.Languages.Megalodon.MathdataKernel

/-!
# Megalodon native proof objects at the NIK boundary

This module presents the executable Mathdata proof kernel as a proof-relevant
NIK authority.  The native certificate is Megalodon's own `Pf`, not an
expanded trace.  The judgment exposes the normal form synthesized by the
proof and required by the source proposition.

Conversion is the current fuel-bounded beta/eta/delta conversion implemented
by `MathdataKernel.normalize`.  Failure to normalize is rejection; two
resource failures are not convertible.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NIKNativeProof

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.Megalodon.MathdataKernel

/-- A complete query to the native Mathdata proof kernel. -/
structure Claim where
  environment : Environment
  fuel : Nat
  typeDepth : Nat
  termContext : List Tp
  proofContext : List Tm
  proposition : Tm
deriving DecidableEq, Repr

/-- The independent relational reading of the executable Mathdata boundary:
the submitted proposition normalizes, and the native proof synthesizes that
same normal form. -/
def Judges (proof : Pf) (claim : Claim) : Prop :=
  ∃ normalized,
    normalize claim.environment claim.fuel claim.proposition = some normalized ∧
      inferProof claim.environment claim.fuel claim.typeDepth
        claim.termContext claim.proofContext proof = some normalized

/-- Megalodon's own proof term is the retained native proof object. -/
def proofSystem : NativeProofSystem Claim where
  ProofObject := Pf
  Judges := Judges

/-- The computing native proof kernel is exactly Mathdata's source-level
proof checker. -/
def nativeKernel : NativeProofKernel proofSystem where
  decide claim proof :=
    checkProof claim.environment claim.fuel claim.typeDepth
      claim.termContext claim.proofContext proof claim.proposition
  correct claim proof := by
    change
      checkProof claim.environment claim.fuel claim.typeDepth
          claim.termContext claim.proofContext proof claim.proposition = true ↔
        Judges proof claim
    cases normalization :
        normalize claim.environment claim.fuel claim.proposition with
    | none =>
        simp [checkProof, Judges, normalization]
    | some normalized =>
        simp [checkProof, checkNormalizedProof, Judges, normalization]

/-- The canonical Mathdata certificate format has exact proof-fibre parity:
accepted certificates are precisely judged native Megalodon proof terms. -/
def certificateEquivalence :
    CertificateEquivalence nativeKernel.toChecker proofSystem :=
  nativeKernel.certificateEquivalence

/-- Consequently the direct Mathdata checker is a proof-relevant NIK
authority, not merely a trace replayer. -/
theorem authority :
    nativeKernel.toChecker.Authority
      (fun claim => Nonempty (proofSystem.ProofFibre claim)) :=
  nativeKernel.authority

/-! ## Decided beta/eta/delta conversion -/

/-- Fuel-bounded conversion through a common successful normal form. -/
def Converts (environment : Environment) (fuel : Nat) (left right : Tm) : Prop :=
  ∃ normal,
    normalize environment fuel left = some normal ∧
      normalize environment fuel right = some normal

/-- Executable conversion rejects either normalization failure rather than
treating two failures as equal. -/
def decideConversion (environment : Environment) (fuel : Nat)
    (left right : Tm) : Bool :=
  match normalize environment fuel left, normalize environment fuel right with
  | some leftNormal, some rightNormal => decide (leftNormal = rightNormal)
  | _, _ => false

/-- The current Mathdata conversion procedure decides exactly the explicit
fuel-bounded conversion relation. -/
def decidedConversion (environment : Environment) (fuel : Nat) :
    DecidedRelation Tm (Converts environment fuel) where
  decide := decideConversion environment fuel
  correct left right := by
    unfold decideConversion Converts
    cases leftNormalization : normalize environment fuel left with
    | none =>
        simp
    | some leftNormal =>
        cases rightNormalization : normalize environment fuel right with
        | none =>
            simp
        | some rightNormal =>
            simp [eq_comm]

/-! ## Positive and negative source-shaped witnesses -/

def definitionConversionClaim : Claim where
  environment := definitionConversionEnvironment
  fuel := 16
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := definitionConversionGoal

/-- The real definition-bearing identity specimen is accepted through the
native proof-object boundary. -/
theorem definition_conversion_native_accepted :
    nativeKernel.toChecker.check definitionConversionClaim
      definitionConversionProof = true :=
  definition_conversion_accepted

def opaqueIdentityClaim : Claim where
  environment := opaqueIdentityEnvironment
  fuel := 16
  typeDepth := 0
  termContext := []
  proofContext := []
  proposition := definitionConversionGoal

/-- The same proof syntax is rejected when the definition needed by delta
conversion is absent. -/
theorem opaque_identity_native_rejected :
    nativeKernel.toChecker.check opaqueIdentityClaim
      definitionConversionProof = false :=
  opaque_identity_rejected

def betaRedex : Tm :=
  .app (.lam (.base 0) (.db 0)) (.named "x")

@[simp] theorem betaRedex_normalizes :
    MathdataKernel.normalize {} 4 betaRedex = some (.named "x") := by
  simp [betaRedex, MathdataKernel.normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?, Tm.normalize,
    Tm.normalizeOne, Tm.instantiate, Tm.instantiateAt, Tm.shift]

@[simp] theorem opaque_x_normalizes :
    MathdataKernel.normalize {} 4 (.named "x") = some (.named "x") := by
  simp [MathdataKernel.normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?]

@[simp] theorem opaque_y_normalizes :
    MathdataKernel.normalize {} 4 (.named "y") = some (.named "y") := by
  simp [MathdataKernel.normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?]

@[simp] theorem opaque_f_normalizes :
    MathdataKernel.normalize {} 4 (.named "f") = some (.named "f") := by
  simp [MathdataKernel.normalize, deltaNormalize, Tm.normalize,
    Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?]

@[simp] theorem betaRedex_zeroFuel_fails :
    MathdataKernel.normalize {} 0 betaRedex = none := by
  simp [betaRedex, MathdataKernel.normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?, Tm.normalize,
    Tm.normalizeOne]

def etaRedex : Tm :=
  .lam (.base 0) (.app (.named "f") (.db 0))

@[simp] theorem etaRedex_normalizes :
    MathdataKernel.normalize {} 4 etaRedex = some (.named "f") := by
  simp [etaRedex, MathdataKernel.normalize, deltaNormalize,
    Environment.lookupTerm?, lookupTermList?, Tm.normalize,
    Tm.normalizeOne, Tm.dropAt?]

@[simp] theorem definitionDomain_normalizes :
    MathdataKernel.normalize definitionConversionEnvironment 16
      definitionConversionDomain = some (.named "p") := by
  simp [definitionConversionEnvironment, definitionConversionDomain,
    MathdataKernel.normalize, deltaNormalize, Environment.lookupTerm?,
    lookupTermList?, Tm.normalize, Tm.normalizeOne, Tm.instantiate,
    Tm.instantiateAt, Tm.shift]

@[simp] theorem definitionP_normalizes :
    MathdataKernel.normalize definitionConversionEnvironment 16
      (.named "p") = some (.named "p") := by
  simp [definitionConversionEnvironment, MathdataKernel.normalize,
    deltaNormalize, Environment.lookupTerm?, lookupTermList?,
    Tm.normalize, Tm.normalizeOne]

/-- Positive conversion witness: beta reduction is computed, not serialized
as a certificate trace. -/
theorem beta_conversion_accepted :
    (decidedConversion {} 4).decide betaRedex (.named "x") = true := by
  simp [decidedConversion, decideConversion]

/-- Eta contraction is part of the same computed conversion relation. -/
theorem eta_conversion_accepted :
    (decidedConversion {} 4).decide etaRedex (.named "f") = true := by
  change decideConversion {} 4 etaRedex (.named "f") = true
  unfold decideConversion
  rw [etaRedex_normalizes, opaque_f_normalizes]
  rfl

/-- Named definitions participate by delta conversion. -/
theorem delta_conversion_accepted :
    (decidedConversion definitionConversionEnvironment 16).decide
      definitionConversionDomain (.named "p") = true := by
  change decideConversion definitionConversionEnvironment 16
    definitionConversionDomain (.named "p") = true
  unfold decideConversion
  rw [definitionDomain_normalizes, definitionP_normalizes]
  rfl

/-- Negative conversion witness: opaque named constants with different names
remain distinct. -/
theorem distinct_opaque_names_rejected :
    (decidedConversion {} 4).decide (.named "x") (.named "y") = false := by
  simp [decidedConversion, decideConversion]

/-- Resource failure is fail-closed, including when both endpoints exhaust
their fuel. -/
theorem dual_resource_failure_rejected :
    decideConversion {} 0 betaRedex betaRedex = false := by
  simp [decideConversion]

/-! ## Axiom audit -/

#print axioms nativeKernel
#print axioms certificateEquivalence
#print axioms authority
#print axioms decidedConversion
#print axioms definition_conversion_native_accepted
#print axioms opaque_identity_native_rejected
#print axioms beta_conversion_accepted
#print axioms eta_conversion_accepted
#print axioms delta_conversion_accepted
#print axioms distinct_opaque_names_rejected
#print axioms dual_resource_failure_rejected

end Mettapedia.Languages.Megalodon.NIKNativeProof
