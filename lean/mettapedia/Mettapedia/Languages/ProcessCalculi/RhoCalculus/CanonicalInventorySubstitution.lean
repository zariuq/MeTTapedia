import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventorySupport

/-!
# Source substitution laws from the rho declaration inventory

Drop exposure is proved in the authored source language. This law is not
asserted for arbitrary generated mixed-color Cost syntax, where it is false.
Extra source process constructors, including synchronous output, remain in
the inventory and the typing domain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Canonical

/-- The actual normalized source typing/support derivation supplies the
Name exposed by Drop, rather than assuming a normalizer closure record. -/
theorem dropCanonicalSupportStable {language : LanguageDef}
    (inventory : CanonicalInventory language) :
    ReflectiveDropCanonicalSupportStable (profile := rhoReflectionProfile) language := by
  intro declaration selected free support bound available pattern name binderImage
    typed safe object canonicalEquality
  have same : declaration = rhoReflectivePresentation := by
    simpa [rhoReflectionProfile] using selected
  subst declaration
  change Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
    rhoReflectivePresentation pattern = .apply "PDrop" [name] at canonicalEquality
  rw [CanonicalMatch.derivedCanonicalize_eq] at canonicalEquality
  have normalized := inventory.canonicalize_supportSafe typed safe (by trivial) object
  rw [canonicalEquality] at normalized
  obtain ⟨dropTyped, dropSafe⟩ := normalized
  obtain ⟨nameTyped, nameSafe⟩ := inventory.drop_argument_supportSafe dropTyped dropSafe
  have nameObject : isObjectPattern name = true := by
    have normalizedObject := LanguageDefCanonicalSection.canonicalize_isObjectPattern object
    rw [canonicalEquality] at normalizedObject
    simpa [isObjectPattern, isObjectPatternList] using normalizedObject
  exact ⟨nameTyped, nameSafe, nameObject⟩

/-- Source canonicalization before a supported term-valued substitution is
neutral in the source's authored equation relation. The output relation is
raw here; no claim about typed intermediate vertices is inferred. -/
theorem substitute_canonicalize_equationEquiv {language : LanguageDef}
    (inventory : CanonicalInventory language) (valid : language.validate = [])
    (reflectionValid : Mettapedia.OSLF.MeTTaIL.Reflection.validate
      language rhoReflectionProfile = [])
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (assignment : SupportedOpenAssignment rhoReflectionProfile language source target support)
    (typed : HasType language source bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available binderImage)
    (object : isObjectPattern pattern = true) :
    ReflectiveEquationSemantics.ReflectiveEquationEquiv rhoReflectionProfile
      defaultBasePremises language
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment available.length pattern)
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment available.length (canonicalize pattern)) := by
  simpa only [CanonicalMatch.derivedCanonicalize_eq] using
    substituteAt_canonicalize_equationEquiv_of_resultsQuoted language valid reflectionValid
      inventory.nameResultsSealed.resultsQuoted inventory.dropCanonicalSupportStable
      assignment rhoReflectivePresentation (by simp [rhoReflectionProfile]) typed safe object

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalInventory
