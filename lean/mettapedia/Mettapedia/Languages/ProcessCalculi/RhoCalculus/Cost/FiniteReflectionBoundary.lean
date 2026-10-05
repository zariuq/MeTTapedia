import Mettapedia.GSLT.LanguageDef.Cost.FiniteReflection
import Mettapedia.GSLT.LanguageDef.WellSortedChecker
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
import Mettapedia.OSLF.MeTTaIL.ReflectiveEngine

/-!
# The explicit reflection boundary of the finite Cost fragment

The selected finite Cost language has an ordinary matcher and no static
equations. A well-sorted funded rho redex whose channels differ only by
parallel units therefore has no ordinary step. The existing complete Cost
language, with its separately validated reflection profile, admits that same
redex through the reflective engine. Its reflection profile is not admitted
by the selected finite fragment: the required static equations are absent.

This comparison does not install reflection in the finite generator and
does not identify the ordinary matcher with reflective COMM.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteReflectionBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveEngine
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open LanguageDefContinuedInteraction

abbrev profile := ContinuationDecorationProfile.ofRetypingPlan rhoCIGSLT.continuationRetyping

def baseZero : Pattern := .apply (costBaseConstructorName "PZero") []
def wrappedZero : Pattern := .apply (costWrappedConstructorName "PZero") []
def canonicalChannel : Pattern := .apply (costBaseConstructorName "NQuote") [baseZero]
def expandedChannel : Pattern := .apply (costBaseConstructorName "NQuote")
  [.collection .hashBag [baseZero, baseZero] none]
def unitSignature : Pattern := .apply costSignatureUnitConstructorName []
def emptyStack : Pattern := .apply costTokenStackEmptyConstructorName []

def candidate : Pattern := .apply costContactConstructorName
  [.apply costSignedConstructorName
    [.collection .hashBag
      [.apply (costBaseConstructorName "PInput")
        [expandedChannel, .lambda none (.apply (costWrappedConstructorName "PDrop") [.bvar 0])],
       .apply (costBaseConstructorName "POutput") [canonicalChannel, wrappedZero]] none,
      unitSignature],
    .apply costFundingConstructorName
      [.apply costTokenStackConsConstructorName [unitSignature, emptyStack]]]

theorem finite_language_valid : profile.costWholeRedexLanguage.validate = [] :=
  profile.costWholeRedexLanguage_validate rhoCIGSLT.continuationRetyping.noDuplicates
    ((ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      rhoCIGSLT.redexRetypable)
    ((ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr rhoCIGSLT.wrappable)

theorem finite_equations_empty : profile.costWholeRedexLanguage.equations = [] := rfl

/-- The comparison uses the same authored funded rewrite in both runtimes. -/
theorem same_funded_rule : profile.costWholeRedexRewrite = rhoCIGSLT.costWholeRedexRewrite :=
  ContinuationDecorationProfile.ofRetypingPlan_costWholeRedexRewrite rhoCIGSLT

theorem candidate_typed : HasSort profile.costWholeRedexLanguage FreeTypeContext.empty []
    candidate costWrappedSortName := checkHasType_sound (by decide +kernel)

theorem candidate_typed_in_reflective_language : HasSort rhoCIGSLT.costWholeLanguage
    FreeTypeContext.empty [] candidate costWrappedSortName :=
  checkHasType_sound (by decide +kernel)

theorem ordinary_match_empty : matchPatternForRule profile.costWholeRedexLanguage
    profile.costWholeRedexRewrite candidate = [] := by
  decide +kernel

theorem ordinary_no_step (base : BasePremiseEvaluator) (result : Pattern) :
    ¬ Step base profile.costWholeRedexLanguage candidate result := by
  apply not_step_of_matchPatternForRule_eq_nil
  intro rule member
  obtain rfl := List.mem_singleton.mp member
  exact ordinary_match_empty

theorem full_reflection_admitted : Mettapedia.OSLF.MeTTaIL.Reflection.validate
    rhoCIGSLT.costWholeLanguage rhoCIGSLT.costWholeReflectionProfile = [] :=
  rhoCIGSLT.costWholeReflectionProfile_validate

theorem reflective_reducts_nonempty : rewriteStepWithReflection
    rhoCIGSLT.costWholeReflectionProfile rhoCIGSLT.costWholeLanguage candidate ≠ [] := by
  decide +kernel

theorem full_reflection_not_admitted_by_finite_fragment :
    Mettapedia.OSLF.MeTTaIL.Reflection.validate profile.costWholeRedexLanguage
      rhoCIGSLT.costWholeReflectionProfile ≠ [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.FiniteReflectionBoundary
