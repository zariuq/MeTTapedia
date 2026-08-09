import Mettapedia.GSLT.LanguageDef.ReflectiveCanonicalSection
import Mettapedia.GSLT.LanguageDef.ReflectiveConstructorSupport

/-!
# Constructor-fragment stability of open canonical sections

An open canonical section preserves a constructor fragment when normalizing a
typed term in any free-variable, binder, and result-sort fiber cannot introduce
a constructor outside that fragment.  The property is about the authored
normalizer itself; it is deliberately independent of Cost and can be proved by
any canonicalization algorithm.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace ComputableContextualOpenSection

/-- Exact constructor-fragment stability in every typed open fiber. -/
def PreservesConstructors {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort} (term : OpenTerm theory free bound sort),
    ConstructorsWithin allowed term.1 →
      ConstructorsWithin allowed (canonical.normalize term).1

/-- Exact declaration-aware constructor-fragment stability in every typed
open fiber.  This strengthens raw support precisely at bare collection
representations, whose authored constructor label is not stored in
`Pattern`. -/
def PreservesTypedConstructors {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort} (term : OpenTerm theory free bound sort),
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound term.1
      (.base sort.1) →
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound
      (canonical.normalize term).1 (.base sort.1)

/-- The identity open canonicalizer preserves every constructor fragment. -/
theorem preservesConstructors_id {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory)
    (identity : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort), canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

/-- The identity open canonicalizer preserves every declaration-aware
constructor fragment. -/
theorem preservesTypedConstructors_id {theory : IGSLT}
    (canonical : ComputableContextualOpenSection theory)
    (identity : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort), canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

/-- Reflective canonicalization preserves every fragment containing the
declaration's quote, drop, and parallel-unit constructors. -/
theorem preservesConstructors_reflective
    {theory : IGSLT} (canonical : ComputableContextualOpenSection theory)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  rw [rawAgreement term]
  exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
    term.1).mpr supported

/-- Reflective canonicalization preserves typed constructor support whenever
its reflective constructors and every authored bare collection constructor
belong to the selected fragment. -/
theorem preservesTypedConstructors_reflective
    {theory : IGSLT} (canonical : ComputableContextualOpenSection theory)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration)
    (bareAllowed : ∀ rule ∈
        theory.presentation.presentation.language.terms,
      WellSorted.UsesBareCollection rule → allowed rule.label) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  apply (canonical.normalize term).2.1.withConstructors
  · rw [rawAgreement term]
    exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
      term.1).mpr supported.constructorsWithin
  · exact bareAllowed

end ComputableContextualOpenSection

namespace ComputableReflectiveContextualOpenSection

/-- Constructor-fragment stability for a normalizer whose equation theory is
selected by an explicit reflection extension. -/
def PreservesConstructors {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort} (term : OpenTerm theory free bound sort),
    ConstructorsWithin allowed term.1 →
      ConstructorsWithin allowed (canonical.normalize term).1

/-- Declaration-aware constructor stability for a reflection-indexed
normalizer. -/
def PreservesTypedConstructors {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort} (term : OpenTerm theory free bound sort),
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound term.1
      (.base sort.1) →
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound
      (canonical.normalize term).1 (.base sort.1)

theorem preservesConstructors_id {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (identity : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort), canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

theorem preservesTypedConstructors_id {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (identity : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort), canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

theorem preservesConstructors_reflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  rw [rawAgreement term]
  exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
    term.1).mpr supported

theorem preservesTypedConstructors_reflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveContextualOpenSection theory reflection)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : OpenTerm theory free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration)
    (bareAllowed : ∀ rule ∈
        theory.presentation.presentation.language.terms,
      WellSorted.UsesBareCollection rule → allowed rule.label) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  apply (canonical.normalize term).2.1.withConstructors
  · rw [rawAgreement term]
    exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
      term.1).mpr supported.constructorsWithin
  · exact bareAllowed

end ComputableReflectiveContextualOpenSection

namespace ComputableReflectiveFiberContextualSection

/-- Constructor-fragment stability for a normalizer whose domain and
codomain are the admitted reflective fibre. -/
def PreservesConstructors {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort}
    (term : ReflectiveWellSorted.OpenTerm reflection.1
      theory.presentation.presentation.language free bound sort),
    ConstructorsWithin allowed term.1 →
      ConstructorsWithin allowed (canonical.normalize term).1

/-- Declaration-aware constructor stability inside the admitted reflective
fibre.  This is the reflective-fibre counterpart of
`ComputableContextualOpenSection.PreservesTypedConstructors`; no core-typed
term is silently promoted to the reflective domain. -/
def PreservesTypedConstructors {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (allowed : String → Prop) : Prop :=
  ∀ {free bound sort}
    (term : ReflectiveWellSorted.OpenTerm reflection.1
      theory.presentation.presentation.language free bound sort),
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound term.1
        (.base sort.1) →
    WellSorted.HasTypeWithConstructors
      theory.presentation.presentation.language allowed free bound
        (canonical.normalize term).1 (.base sort.1)

/-- The identity reflective-fibre canonicalizer preserves every constructor
fragment. -/
theorem preservesConstructors_id {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (identity : ∀ {free bound sort}
      (term : ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort),
      canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

/-- The identity reflective-fibre canonicalizer preserves every
declaration-aware constructor fragment. -/
theorem preservesTypedConstructors_id {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (identity : ∀ {free bound sort}
      (term : ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort),
      canonical.normalize term = term)
    (allowed : String → Prop) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  simpa [identity term] using supported

/-- Reflective canonicalization preserves a constructor fragment on the
reflection-certified fibre whenever the declaration's distinguished
constructors belong to that fragment. -/
theorem preservesConstructors_reflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration) :
    canonical.PreservesConstructors allowed := by
  intro free bound sort term supported
  rw [rawAgreement term]
  exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
    term.1).mpr supported

/-- Typed constructor-fragment preservation on the reflection-certified
fibre.  Bare collection constructors are named separately because their raw
patterns do not expose a constructor label. -/
theorem preservesTypedConstructors_reflective {theory : IGSLT}
    {reflection : ReflectionExtension.AdmittedProfile
      theory.presentation.presentation.language}
    (canonical : ComputableReflectiveFiberContextualSection theory reflection)
    (declaration : ReflectivePresentationDecl)
    (rawAgreement : ∀ {free bound sort}
      (term : ReflectiveWellSorted.OpenTerm reflection.1
        theory.presentation.presentation.language free bound sort),
      (canonical.normalize term).1 = canonicalize declaration term.1)
    (allowed : String → Prop)
    (reflectiveAllowed : ReflectiveConstructorsAllowed allowed declaration)
    (bareAllowed : ∀ rule ∈
        theory.presentation.presentation.language.terms,
      WellSorted.UsesBareCollection rule → allowed rule.label) :
    canonical.PreservesTypedConstructors allowed := by
  intro free bound sort term supported
  apply (canonical.normalize term).2.1.1.withConstructors
  · rw [rawAgreement term]
    exact (constructorsWithin_canonicalize_iff declaration reflectiveAllowed
      term.1).mpr supported.constructorsWithin
  · exact bareAllowed

end ComputableReflectiveFiberContextualSection

end Mettapedia.GSLT.LanguageDef
