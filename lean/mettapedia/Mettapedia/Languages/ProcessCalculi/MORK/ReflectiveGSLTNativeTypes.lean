import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# OSLF native types for reflective MM2 execution

Compilers that stage executable MM2 rules as captured data use the reflective
execution presentation.  This module applies OSLF to that exact GSLT rather
than silently reusing the narrower ground-output execution family.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open WQComputable
open ReflectiveComputable

/-- Native types generated from the actual reflective MM2 profile selected by
the Metamath-to-MM2 compiler. -/
abbrev ReflectiveSourceExecNativeType : Type :=
  GSLTNativeType (reflectiveSourceExecGSLT .leaveInert)

/-- Exact one-step target type for reflective MM2 execution. -/
noncomputable def reflectiveSourceExecExactTargetNativeType
    (target : Space) : ReflectiveSourceExecNativeType :=
  exactTargetNativeType (reflectiveSourceExecGSLT .leaveInert) target

/-- Inhabiting the generated target type is exactly a reflective MM2
work-queue step. -/
theorem satisfies_reflectiveSourceExecExactTargetNativeType_iff_step
    (source target : Space) :
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred ↔
      (reflectiveSourceExecGSLT .leaveInert).Step source target :=
  satisfies_exactTargetNativeType_iff_step
    (reflectiveSourceExecGSLT .leaveInert) source target

/-- Every selected reflective MM2 event inhabits the exact native type of the
space it computes. -/
theorem reflective_event_inhabits_exact_target
    {source target : Space}
    (event : ReflectiveScheduledEvent source target) :
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
      (reflectiveSourceExecExactTargetNativeType target).pred := by
  apply (satisfies_reflectiveSourceExecExactTargetNativeType_iff_step
    source target).2
  exact (reflectiveScheduledEvent_nonempty_iff_step source target).1 ⟨event⟩

/-- A duplicate-free finite presentation whose computable supported-candidate
list is a singleton selects that same directive in the support-level
reflective semantics.  Compiler proofs use this bridge to turn concrete
phase lists into actual GSLT steps. -/
theorem reflective_selects_of_computable_supported_singleton
    (atoms : List Atom) (directive : SourceExecFact)
    (nodup : atoms.Nodup)
    (candidates : cSupportedSourceExecFacts atoms = [directive]) :
    selectNextScheduled
        (supportedSourceExecFactsOfSpace atoms.toFinset) = some directive := by
  have keyInjective : KeyInjective (cSupportedSourceExecFacts atoms) := by
    rw [candidates]
    simp [KeyInjective]
  have agreement :=
    cSourceWorkQueueStep_selectSupported_eq atoms nodup keyInjective
  rw [candidates] at agreement
  rw [← agreement]
  rfl

/-- The same singleton-candidate condition directly produces an inhabitant of
the OSLF native type of the exact reflective successor. -/
theorem computable_supported_singleton_inhabits_exact_target
    (atoms : List Atom) (directive : SourceExecFact)
    (nodup : atoms.Nodup)
    (candidates : cSupportedSourceExecFacts atoms = [directive]) :
    (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies atoms.toFinset
      (reflectiveSourceExecExactTargetNativeType
        (fireReflectiveSourceExecFact atoms.toFinset directive)).pred := by
  exact reflective_event_inhabits_exact_target
    (reflectiveEventOfSelected
      (reflective_selects_of_computable_supported_singleton atoms directive
        nodup candidates))

/-- An empty supported work queue cannot inhabit an exact target native type.
This rejects invented target behavior at the same operational boundary used
by the compiler. -/
theorem no_reflective_native_target_of_no_supported
    {source target : Space}
    (empty :
      selectNextScheduled (supportedSourceExecFactsOfSpace source) = none) :
    ¬ (gsltOSLF (reflectiveSourceExecGSLT .leaveInert)).satisfies source
        (reflectiveSourceExecExactTargetNativeType target).pred := by
  intro inhabited
  have step :=
    (satisfies_reflectiveSourceExecExactTargetNativeType_iff_step
      source target).1 inhabited
  have event :=
    (reflectiveScheduledEvent_nonempty_iff_step source target).2 step
  exact not_nonempty_iff.mpr (no_reflective_event_of_no_supported empty) event

/-! ## Native types for the executable list realization -/

/-- OSLF-generated native types for the direct executable realization.  This
does not identify list execution with the authored support semantics; that
separate realization theorem retains its explicit scheduler and row-alignment
premises. -/
abbrev ReflectiveNativeListExecNativeType
    (policy : UnsupportedExecPolicy) : Type :=
  GSLTNativeType (reflectiveNativeListExecGSLT policy)

/-- Exact one-step target type generated from the executable realization
GSLT. -/
noncomputable def reflectiveNativeListExactTargetNativeType
    (policy : UnsupportedExecPolicy) (target : List Atom) :
    ReflectiveNativeListExecNativeType policy :=
  exactTargetNativeType (reflectiveNativeListExecGSLT policy) target

/-- Inhabiting the executable realization's exact target type is equivalent
to one concrete list-machine step. -/
theorem satisfies_reflectiveNativeListExactTargetNativeType_iff_step
    (policy : UnsupportedExecPolicy) (source target : List Atom) :
    (gsltOSLF (reflectiveNativeListExecGSLT policy)).satisfies source
        (reflectiveNativeListExactTargetNativeType policy target).pred ↔
      cReflectiveSourceWorkQueueStep policy source = some target := by
  change
    (gsltOSLF (reflectiveNativeListExecGSLT policy)).satisfies source
        (exactTargetNativeType (reflectiveNativeListExecGSLT policy) target).pred ↔
      cReflectiveSourceWorkQueueStep policy source = some target
  exact
    (satisfies_exactTargetNativeType_iff_step
      (reflectiveNativeListExecGSLT policy) source target).trans
      (reflectiveNativeListExecGSLT_step_iff policy source target)

/-- A proof-relevant sequence whose every concrete transition inhabits the
exact OSLF-generated native target type for its successor. -/
inductive ReflectiveNativeTypeTrace (policy : UnsupportedExecPolicy) :
    Nat → List Atom → List Atom → Type where
  | refl {fuel : Nat} {source : List Atom} :
      ReflectiveNativeTypeTrace policy fuel source source
  | step {fuel source middle target} :
      (gsltOSLF (reflectiveNativeListExecGSLT policy)).satisfies source
        (reflectiveNativeListExactTargetNativeType policy middle).pred →
      ReflectiveNativeTypeTrace policy fuel middle target →
      ReflectiveNativeTypeTrace policy (fuel + 1) source target

/-- OSLF classifies every step retained by a concrete reflective trace. -/
def CReflectiveTrace.toNativeTypeTrace
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CReflectiveTrace policy fuel source target) :
    ReflectiveNativeTypeTrace policy fuel source target :=
  match trace with
  | .refl => .refl
  | .step moved tail =>
      .step
        ((satisfies_reflectiveNativeListExactTargetNativeType_iff_step
          policy _ _).2 moved)
        tail.toNativeTypeTrace

/-- Every exact-fuel direct execution therefore has an OSLF-classified,
proof-relevant trace to its returned state. -/
def cReflectiveSourceWorkQueueRunN_nativeTypeTrace
    (policy : UnsupportedExecPolicy) (fuel : Nat) (source : List Atom) :
    ReflectiveNativeTypeTrace policy fuel source
      (cReflectiveSourceWorkQueueRunN policy fuel source).1 :=
  (cReflectiveSourceWorkQueueRunN_trace policy fuel source).toNativeTypeTrace

/-- Proof-relevant OSLF classification of a path in the authored
support-valued reflective MM2 GSLT. -/
inductive ReflectiveSupportNativeTypeTrace
    (policy : UnsupportedExecPolicy) : Space → Space → Type where
  | refl {source : Space} :
      ReflectiveSupportNativeTypeTrace policy source source
  | step {source middle target : Space} :
      (gsltOSLF (reflectiveSourceExecGSLT policy)).satisfies source
        (exactTargetNativeType (reflectiveSourceExecGSLT policy) middle).pred →
      ReflectiveSupportNativeTypeTrace policy middle target →
      ReflectiveSupportNativeTypeTrace policy source target

/-- Every authored support-level rewrite path is classified step-by-step by
OSLF. -/
def reflectiveSupportRewritePathToNativeTypeTrace
    {policy : UnsupportedExecPolicy} {source target : Space}
    (path : (reflectiveSourceExecGSLT policy).RewritePath source target) :
    ReflectiveSupportNativeTypeTrace policy source target :=
  match path with
  | .nil _ => .refl
  | .cons moved tail =>
      .step
        ((satisfies_exactTargetNativeType_iff_step
          (reflectiveSourceExecGSLT policy) _ _).2 moved)
        (reflectiveSupportRewritePathToNativeTypeTrace tail)

/-- A concrete trace that discharges every scheduler and row-alignment
obligation is therefore classified by OSLF over the authored support-valued
MM2 GSLT, not only over the list realization. -/
def CReflectiveAdequateTrace.toSupportNativeTypeTrace
    {policy : UnsupportedExecPolicy} {fuel : Nat}
    {source target : List Atom}
    (trace : CReflectiveAdequateTrace policy fuel source target) :
    ReflectiveSupportNativeTypeTrace policy source.toFinset target.toFinset :=
  reflectiveSupportRewritePathToNativeTypeTrace trace.toSupportRewritePath

section AxiomAudit

#print axioms satisfies_reflectiveSourceExecExactTargetNativeType_iff_step
#print axioms reflective_event_inhabits_exact_target
#print axioms reflective_selects_of_computable_supported_singleton
#print axioms computable_supported_singleton_inhabits_exact_target
#print axioms no_reflective_native_target_of_no_supported
#print axioms satisfies_reflectiveNativeListExactTargetNativeType_iff_step
#print axioms CReflectiveAdequateTrace.toSupportNativeTypeTrace

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK
