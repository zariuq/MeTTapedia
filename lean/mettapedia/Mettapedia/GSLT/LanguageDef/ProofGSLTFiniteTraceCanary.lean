import Mettapedia.GSLT.LanguageDef.ProofGSLTFiniteTraceAuthority

/-!
# Separating examples for finite ProofGSLT trace authority

A finite trace through a cyclic transition system is an ordinary finite
reachability certificate.  No guarded cyclic proof principle is needed merely
because the underlying graph contains a cycle.  By contrast, sound replay and
certificate completeness are distinct obligations: a checker may reject every
certificate without ever accepting a false edge.

This module exercises both distinctions with an explicit two-state GSLT.
-/

namespace Mettapedia.GSLT.LanguageDef.ProofGSLT.FiniteTraceCanary

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.ProofGSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.OSLFProofGSLTAuthority

inductive ToggleStep : Bool → Bool → Prop where
  | up : ToggleStep false true
  | down : ToggleStep true false

@[reducible] def toggleTheory : GSLT where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := ToggleStep
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

inductive ToggleEvidence where
  | up
  | down
deriving Repr, DecidableEq

def checkToggleEdge (claim : StepClaim toggleTheory)
    (evidence : ToggleEvidence) : Bool :=
  match claim.source, claim.target, evidence with
  | false, true, .up => true
  | true, false, .down => true
  | _, _, _ => false

theorem checkToggleEdge_sound {claim : StepClaim toggleTheory}
    {evidence : ToggleEvidence}
    (accepted : checkToggleEdge claim evidence = true) : claim.Meaning := by
  rcases claim with ⟨source, target⟩
  cases source <;> cases target <;> cases evidence <;>
    simp [checkToggleEdge] at accepted
  · exact ToggleStep.up
  · exact ToggleStep.down

def toggleStepAuthority : StepAuthority String toggleTheory where
  id := "toggle-step-v1"
  Certificate := ToggleEvidence
  check := checkToggleEdge
  sound := checkToggleEdge_sound

/-! ## Operational steps as rich OSLF native judgments -/

/-- The real upward edge inhabits the automatically generated exact-target
native type. -/
def upwardNativeClaim : NativeClaim (gsltOSLF toggleTheory) :=
  exactStepNativeClaim toggleTheory false true

theorem upwardNativeClaim_meaning : upwardNativeClaim.Meaning :=
  (exactStepNativeClaim_meaning_iff_step toggleTheory false true).2
    ToggleStep.up

/-- The absent self-edge does not inhabit that exact-target native type. -/
def absentSelfNativeClaim : NativeClaim (gsltOSLF toggleTheory) :=
  exactStepNativeClaim toggleTheory false false

theorem absentSelfNativeClaim_not_meaning :
    ¬ absentSelfNativeClaim.Meaning := by
  intro meaning
  have step : ToggleStep false false :=
    (exactStepNativeClaim_meaning_iff_step toggleTheory false false).1 meaning
  cases step

theorem toggleStepAuthority_complete : toggleStepAuthority.Complete := by
  intro claim meaning
  rcases claim with ⟨source, target⟩
  cases meaning with
  | up => exact ⟨.up, rfl⟩
  | down => exact ⟨.down, rfl⟩

def loopClaim : TraceClaim toggleTheory :=
  ⟨false, true⟩

/-- The trace crosses the cycle once and then takes one more edge. -/
def loopCertificate : TraceCertificate toggleTheory ToggleEvidence :=
  ⟨[
    ⟨true, .up⟩,
    ⟨false, .down⟩,
    ⟨true, .up⟩
  ]⟩

/-- A finite certificate through a cyclic graph is accepted normally. -/
theorem loopCertificate_accepted :
    (finiteTraceAuthority toggleStepAuthority).check
      loopClaim loopCertificate = true :=
  rfl

/-- Acceptance of the cyclic finite trace entails actual GSLT reachability. -/
theorem loopCertificate_reaches :
    toggleTheory.MultiStep false true :=
  (finiteTraceAuthority toggleStepAuthority).sound loopCertificate_accepted

/-- Replacing the first edge witness with the witness for the opposite edge is
detected locally and rejects the whole trace. -/
def corruptedLoopCertificate : TraceCertificate toggleTheory ToggleEvidence :=
  ⟨[
    ⟨true, .down⟩,
    ⟨false, .down⟩,
    ⟨true, .up⟩
  ]⟩

theorem corruptedLoopCertificate_rejected :
    (finiteTraceAuthority toggleStepAuthority).check
      loopClaim corruptedLoopCertificate = false :=
  rfl

/-- For the complete local checker, checkable trace existence is exactly
finite reachability. -/
theorem toggle_trace_correspondence (claim : TraceClaim toggleTheory) :
    (∃ certificate : (finiteTraceAuthority toggleStepAuthority).Certificate,
        (finiteTraceAuthority toggleStepAuthority).check claim certificate =
          true) ↔
      claim.Meaning :=
  finiteTraceAuthority_correspondence toggleStepAuthority
    toggleStepAuthority_complete claim

/-! ## Sound replay does not imply evidence completeness -/

/-- A deliberately rejecting checker is sound because it accepts nothing.
It is a negative canary, not a usable authority for certificate production. -/
def rejectingStepAuthority : StepAuthority Unit toggleTheory where
  id := ()
  Certificate := Unit
  check := fun _ _ => false
  sound := by simp

/-- The rejecting checker cannot certify the real `false → true` edge. -/
theorem rejectingStepAuthority_not_complete :
    ¬ rejectingStepAuthority.Complete := by
  intro complete
  obtain ⟨certificate, accepted⟩ :=
    complete ⟨false, true⟩ ToggleStep.up
  cases certificate
  simp [rejectingStepAuthority] at accepted

#print axioms upwardNativeClaim_meaning
#print axioms absentSelfNativeClaim_not_meaning
#print axioms loopCertificate_reaches
#print axioms toggle_trace_correspondence
#print axioms rejectingStepAuthority_not_complete

end Mettapedia.GSLT.LanguageDef.ProofGSLT.FiniteTraceCanary
