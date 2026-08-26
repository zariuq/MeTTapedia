import Mettapedia.Languages.ProcessCalculi.MORK.GSLTSemantics
import Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority

/-!
# OSLF native types for the MM2 GSLT family

The MM2 work-queue family already fixes `(T, E, R)`.  This module applies the
generic OSLF construction to that family; it does not introduce an MM2-specific
type semantics.  An exact target type is the singleton-target diamond generated
from the selected MM2 profile, and its meaning is definitionally the profile's
one-step relation.

The same native claim is also the input to the generic CertificateGSLT authority.
A concrete wire presentation and native lowering remain separate realization
obligations; no checker is postulated here.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.OSLFCertificateGSLTAuthority

/-! ## Generated native types -/

/-- The rich predicate-valued OSLF native-type carrier generated for one MM2
source-exec profile. -/
abbrev SourceExecNativeType (policy : UnsupportedExecPolicy) : Type :=
  GSLTNativeType (sourceExecGSLT policy)

/-- Exact one-step target type generated from one member of the MM2 family. -/
noncomputable def sourceExecExactTargetNativeType
    (policy : UnsupportedExecPolicy) (target : Space) :
    SourceExecNativeType policy :=
  exactTargetNativeType (sourceExecGSLT policy) target

/-- Native inhabitation of an exact MM2 target is precisely that profile's
work-queue transition. -/
theorem satisfies_sourceExecExactTargetNativeType_iff_step
    (policy : UnsupportedExecPolicy) (source target : Space) :
    (gsltOSLF (sourceExecGSLT policy)).satisfies source
        (sourceExecExactTargetNativeType policy target).pred ↔
      (sourceExecGSLT policy).Step source target :=
  satisfies_exactTargetNativeType_iff_step
    (sourceExecGSLT policy) source target

/-! ## CertificateGSLT authority claims -/

/-- The exact MM2 edge as a rich OSLF native claim suitable for the generic
CertificateGSLT authority path. -/
noncomputable def sourceExecStepNativeClaim (policy : UnsupportedExecPolicy)
    (source target : Space) :
    NativeClaim (gsltOSLF (sourceExecGSLT policy)) :=
  exactStepNativeClaim (sourceExecGSLT policy) source target

/-- The generated claim has no second meaning: it means exactly one MM2 step. -/
theorem sourceExecStepNativeClaim_meaning_iff_step
    (policy : UnsupportedExecPolicy) (source target : Space) :
    (sourceExecStepNativeClaim policy source target).Meaning ↔
      (sourceExecGSLT policy).Step source target :=
  exactStepNativeClaim_meaning_iff_step
    (sourceExecGSLT policy) source target

/-! ## Positive and negative boundary canaries -/

/-- A supported raw directive selected by the consuming envelope inhabits the
native type of its computed target. -/
theorem supported_exec_inhabits_consuming_native_type
    {space : Space} {raw : RawExecFact} {directive : SourceExecFact}
    (selected : selectNextScheduled (rawExecFactsOfSpace space) = some raw)
    (decoded : decodeSupportedSourceExec raw = some directive) :
    (gsltOSLF (sourceExecGSLT .consume)).satisfies space
      (sourceExecExactTargetNativeType .consume
        (fireSourceExecFact space directive)).pred := by
  apply (satisfies_sourceExecExactTargetNativeType_iff_step
    .consume space (fireSourceExecFact space directive)).2
  exact supported_exec_is_consuming_step selected decoded

/-- The same unsupported shell has different generated native judgments at
the two explicit policy indices: no exact erased-target edge exists in the
open-world member, while that edge exists in the consuming member. -/
theorem unsupported_exec_native_type_separation
    {space : Space} {raw : RawExecFact}
    (noSupported :
      selectNextScheduled (supportedSourceExecFactsOfSpace space) = none)
    (rawSelected : selectNextScheduled (rawExecFactsOfSpace space) = some raw)
    (unsupported : decodeSupportedSourceExec raw = none) :
    ¬ (gsltOSLF (sourceExecGSLT .leaveInert)).satisfies space
        (sourceExecExactTargetNativeType .leaveInert
          (space.erase raw.atom)).pred ∧
      (gsltOSLF (sourceExecGSLT .consume)).satisfies space
        (sourceExecExactTargetNativeType .consume
          (space.erase raw.atom)).pred := by
  have separated := unsupported_exec_separates_source_profiles
    noSupported rawSelected unsupported
  constructor
  · intro inhabited
    have step :=
      (satisfies_sourceExecExactTargetNativeType_iff_step
        .leaveInert space (space.erase raw.atom)).1 inhabited
    exact separated.1 ⟨space.erase raw.atom, step⟩
  · exact
      (satisfies_sourceExecExactTargetNativeType_iff_step
        .consume space (space.erase raw.atom)).2 separated.2

section AxiomAudit

#print axioms unsupported_exec_native_type_separation

end AxiomAudit

end Mettapedia.Languages.ProcessCalculi.MORK
