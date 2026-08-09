import Mettapedia.GSLT.LanguageDef.EquationSubstitution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport

/-!
# Supported equation substitution for rho

The generic reflective substitution law is not a consequence of sorting and
type-indexed support alone: a language may return a name from a constructor
whose argument introduces another name binder.  Pure rho has no such
constructor.  This file records the syntax-directed facts that make the rho
instance admissible without strengthening the authored equation relation or
adding a second semantic presentation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.EquationSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectiveEquationSemantics
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalSupport

private theorem equationEquiv_refl (pattern : Pattern) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      pattern pattern :=
  Relation.EqvGen.refl pattern

private theorem equationEquiv_symm {left right : Pattern}
    (equivalent : ReflectiveEquationEquiv rhoReflectionProfile
      defaultBasePremises rhoCalc left right) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      right left :=
  Relation.EqvGen.symm _ _ equivalent

private theorem equationEquiv_trans {left middle right : Pattern}
    (first : ReflectiveEquationEquiv rhoReflectionProfile
      defaultBasePremises rhoCalc left middle)
    (second : ReflectiveEquationEquiv rhoReflectionProfile
      defaultBasePremises rhoCalc middle right) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      left right :=
  Relation.EqvGen.trans _ _ _ first second

/-- The exact rho signature seals every authored name result behind the sole
quotation constructor.  In particular, no ordinary binder-bearing constructor
can return `Name`, which is the structural feature needed by supported
substitution below quote/drop cancellation. -/
theorem rho_reflectiveNameResultSealed :
    ReflectiveNameResultSealed (profile := rhoReflectionProfile) rhoCalc := by
  intro declaration declarationMembership rule ruleMembership categoryEquality
  have declarationEquality :
      declaration =
        rhoReflectivePresentation.toReflectivePresentationDecl := by
    simpa [rhoReflectionProfile] using declarationMembership
  subst declaration
  simp [rhoCalc] at ruleMembership
  rcases ruleMembership with rfl | rfl | rfl | rfl | rfl | rfl
  · simp [rhoReflectivePresentation] at categoryEquality
  · simp [rhoReflectivePresentation] at categoryEquality
  · exact ⟨rfl, by
      simp [UsesBareCollection, TypeExpr.proc, TypeExpr.baseType]⟩
  · simp [rhoReflectivePresentation] at categoryEquality
  · simp [rhoReflectivePresentation] at categoryEquality
  · simp [rhoReflectivePresentation] at categoryEquality

/-- Rho canonicalization can expose `PDrop` only with a name argument that
remains in the original typing and reflective-support fiber. -/
theorem rho_reflectiveDropCanonicalSupportStable :
    ReflectiveDropCanonicalSupportStable
      (profile := rhoReflectionProfile) rhoCalc := by
  intro declaration declarationMembership free support bound available pattern
    name binderImage typed safe object canonicalEquality
  have declarationEquality :
      declaration =
        rhoReflectivePresentation.toReflectivePresentationDecl := by
    simpa [rhoReflectionProfile] using declarationMembership
  subst declaration
  change
    Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.canonicalize
        rhoReflectivePresentation pattern =
      .apply rhoReflectivePresentation.dropConstructor [name]
    at canonicalEquality
  rw [CanonicalMatch.derivedCanonicalize_eq] at canonicalEquality
  have canonicalEquality' :
      canonicalize pattern = .apply "PDrop" [name] := by
    simpa [rhoReflectivePresentation] using canonicalEquality
  have canonicalResult := canonicalize_supportSafe typed safe (by trivial) object
  rw [canonicalEquality'] at canonicalResult
  have dropResult :
      ∃ dropTyped : HasType rhoCalc free bound (.apply "PDrop" [name])
          TypeExpr.proc,
        dropTyped.ReflectiveSupportSafeAt rhoReflectionProfile support available
          binderImage := by
    simpa [rhoReflectivePresentation, TypeExpr.proc, TypeExpr.baseType] using
      canonicalResult
  obtain ⟨dropTyped, dropSafe⟩ := dropResult
  obtain ⟨nameTyped, nameSafe⟩ :=
    drop_argument_supportSafe dropTyped dropSafe
  have canonicalObject : isObjectPattern (canonicalize pattern) = true :=
    LanguageDefCanonicalSection.canonicalize_isObjectPattern object
  have nameObject : isObjectPattern name = true := by
    rw [canonicalEquality'] at canonicalObject
    simpa [isObjectPattern, isObjectPatternList] using canonicalObject
  exact ⟨nameTyped, nameSafe, nameObject⟩

/-- A rho name that is legal immediately below a quotation boundary is
insensitive to the ambient reflective-support depth.

The free-name case is load-bearing: support safety at the empty context forces
the declared support to be empty, and the assigned term is therefore closed
with respect to de Bruijn indices.  A bound name is rejected by the zero-depth
scope witness.  The only authored name constructor is `NQuote`, which resets
the child depth on both sides. -/
theorem name_substituteAt_eq_of_safeAt_zero
    {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {name : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (assignment : SupportedOpenAssignment rhoReflectionProfile rhoCalc source
      target support)
    (typed : HasType rhoCalc source bound name resultType)
    (resultType_eq : resultType = TypeExpr.name)
    (safeAtZero : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      binderImage)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment 0 name =
      ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment availableDepth name := by
  apply nameResult_substituteAt_eq_of_safeAt_zero
    rho_reflectiveNameResultSealed assignment
    rhoReflectivePresentation.toReflectivePresentationDecl
    (by simp [rhoReflectionProfile]) typed
  · simpa [rhoReflectivePresentation, TypeExpr.name, TypeExpr.baseType] using
      resultType_eq
  · exact safeAtZero
  · exact object

/-- The load-bearing rho Quote/Drop generator survives support-aware
substitution at every ambient depth.  The proof does not assume generic
canonicalizer naturality: it derives depth-independence from the exact rho
name grammar and then emits one edge of the authored reflective relation. -/
theorem quote_drop_substituteAt_equationEquiv
    {source target : FreeTypeContext}
    {support : ContextSupport.Support}
    {bound : List TypeExpr} {name : Pattern} {resultType : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (assignment : SupportedOpenAssignment rhoReflectionProfile rhoCalc source
      target support)
    (typed : HasType rhoCalc source bound name resultType)
    (resultType_eq : resultType = TypeExpr.name)
    (safeAtZero : typed.ReflectiveSupportSafeAt rhoReflectionProfile support []
      binderImage)
    (object : isObjectPattern name = true)
    (availableDepth : Nat) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment availableDepth
        (.apply "NQuote" [.apply "PDrop" [name]]))
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment availableDepth name) := by
  have membership :
      rhoReflectivePresentation.toReflectivePresentationDecl ∈
        rhoReflectionProfile.presentations := by
    simp [rhoReflectionProfile]
  simpa [rhoReflectivePresentation] using
    (quoteDrop_substituteAt_equationEquiv_of_resultsQuoted
      rho_reflectiveNameResultSealed.resultsQuoted assignment
      rhoReflectivePresentation.toReflectivePresentationDecl membership
      (by simp [rhoReflectivePresentation]) typed
      (by
        simpa [rhoReflectivePresentation, TypeExpr.name, TypeExpr.baseType]
          using resultType_eq)
      safeAtZero object availableDepth)

/-! ## Rho canonicalization is substitution-natural in the authored quotient -/

/-- Supported substitution of a well-sorted rho object is contextually
equivalent to substituting its computed canonical representative.

The conclusion is deliberately an `EquationEquiv`, not raw equality.  A
substitution may introduce parallel bags, units, or new structural sort keys;
the preceding ACU lemma proves those changes invisible in exactly the authored
rho quotient.  Quote/drop cancellation uses `rho_reflectiveNameResultSealed`
to rule out the equal-typed binder-occurrence counterexample. -/
theorem substituteAt_canonicalize_equationEquiv
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound available : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
    {binderImage : TypeExpr → TypeExpr}
    (assignment : SupportedOpenAssignment rhoReflectionProfile rhoCalc source
      target support)
    (typed : HasType rhoCalc source bound pattern type)
    (safe : typed.ReflectiveSupportSafeAt rhoReflectionProfile support available
      binderImage)
    (object : isObjectPattern pattern = true) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment available.length pattern)
      (ReflectiveContextSupport.substituteAt rhoReflectionProfile support
        assignment.assignment available.length (canonicalize pattern)) := by
  have transported :=
    substituteAt_canonicalize_equationEquiv_of_resultsQuoted
        (profile := rhoReflectionProfile)
          rhoCalc LanguageDefAdequacy.rhoCalc_validate
          rhoCalcValidatedReflective.admittedReflection.2
          rho_reflectiveNameResultSealed.resultsQuoted
          rho_reflectiveDropCanonicalSupportStable assignment
          rhoReflectivePresentation.toReflectivePresentationDecl
          (by simp [rhoReflectionProfile]) typed safe object
  simpa only [CanonicalMatch.derivedCanonicalize_eq] using transported

/-- Root specialization of `substituteAt_canonicalize_equationEquiv` to the
support-safe open carrier used by the generic substitution interface. -/
theorem supportSafe_substitute_canonicalize_equationEquiv
    {source target : FreeTypeContext} {support : ContextSupport.Support}
    {bound : List TypeExpr} {type : TypeExpr}
    (assignment : SupportedOpenAssignment rhoReflectionProfile rhoCalc source
      target support)
    (pattern : SupportSafeOpenPattern rhoReflectionProfile rhoCalc source support
      bound type) :
    ReflectiveEquationEquiv rhoReflectionProfile defaultBasePremises rhoCalc
      (pattern.substitute assignment).1
      (ReflectiveContextSupport.substitute rhoReflectionProfile support
        assignment.assignment bound (canonicalize pattern.term.1)) := by
  simpa [SupportSafeOpenPattern.substitute_pattern,
    ReflectiveContextSupport.substitute] using
    substituteAt_canonicalize_equationEquiv assignment pattern.term.2.1.1
      pattern.safe pattern.term.2.1.2.2.1

/-- Pure rho's sole reflective presentation is stable under every supported
substitution on the exact typed/support-safe carrier.

The proof is not an admission of the desired conclusion as structure.  Its
content is the syntax-directed canonicalization theorem above, whose
quote/drop case is discharged by `rho_reflectiveNameResultSealed` and whose
parallel case is discharged in the authored ACU quotient. -/
theorem rho_reflectiveEquationSubstitutionStable :
    ReflectiveEquationSubstitutionStable
      (profile := rhoReflectionProfile) rhoCalc := by
  intro source target support bound type assignment declaration membership
    left right representatives
  have declarationEquality :
      declaration =
        rhoReflectivePresentation.toReflectivePresentationDecl := by
    simpa [rhoReflectionProfile] using membership
  subst declaration
  have canonicalEquality :
      canonicalize left.term.1 = canonicalize right.term.1 := by
    simpa only [CanonicalMatch.derivedCanonicalize_eq] using representatives
  have leftStep :=
    supportSafe_substitute_canonicalize_equationEquiv assignment left
  have rightStep :=
    supportSafe_substitute_canonicalize_equationEquiv assignment right
  have middleStep : ReflectiveEquationEquiv rhoReflectionProfile
      defaultBasePremises rhoCalc
      (ReflectiveContextSupport.substitute rhoReflectionProfile support
        assignment.assignment bound (canonicalize left.term.1))
      (ReflectiveContextSupport.substitute rhoReflectionProfile support
        assignment.assignment bound (canonicalize right.term.1)) := by
    rw [canonicalEquality]
    exact equationEquiv_refl _
  exact equationEquiv_trans leftStep
    (equationEquiv_trans middleStep (equationEquiv_symm rightStep))

/-- Rho's ordinary authored equation instances are stable under supported
substitution as well.  This is derived from the already proved completeness
of the sole authored rho canonical section: an ordinary contextual equation
edge has equal rho representatives, after which the reflective stability
theorem above transports it. -/
theorem rho_authoredEquationSubstitutionStable :
    AuthoredEquationSubstitutionStable
      (profile := rhoReflectionProfile) rhoCalc := by
  intro source target support bound type assignment left right witness
  obtain ⟨context, redex, contractum, equationWitness, leftEquality,
    rightEquality⟩ := witness
  have generator : ReflectiveEquationContextStep rhoReflectionProfile
      defaultBasePremises rhoCalc
      left.term.1 right.term.1 := by
    rw [leftEquality, rightEquality]
    exact .core (.inContext context equationWitness)
  have canonicalEquality :
      canonicalize left.term.1 = canonicalize right.term.1 :=
    LanguageDefSemanticAgreement.rhoEquationContextStep_canonicalize_eq
      generator
  apply rho_reflectiveEquationSubstitutionStable assignment
    (declaration :=
      rhoReflectivePresentation.toReflectivePresentationDecl)
    (by simp [rhoReflectionProfile]) left right
  simpa only [CanonicalMatch.derivedCanonicalize_eq] using canonicalEquality

/-- The complete M1 admission theorem for pure rho: both generator families
of the sole authored contextual equation relation survive supported
substitution. -/
theorem rho_supportedEquationSubstitutionStable :
    SupportedEquationSubstitutionStable
      (profile := rhoReflectionProfile) rhoCalc :=
  ⟨rho_authoredEquationSubstitutionStable,
    rho_reflectiveEquationSubstitutionStable⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.EquationSubstitution
