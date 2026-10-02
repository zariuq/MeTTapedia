import Mettapedia.Languages.ProcessCalculi.Ambient.Interaction
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.GSLT.LanguageDef.Continued.Presentation

/-!
# Mobile ambients are a continued interactive GSLT in the sense of the three clauses

Dissolution is an interaction cut; the bag normal form is a section of the
static equivalence; and the contractum is covered by the continuation
signature and has the wrapped sort.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Mobile

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BagNormalForm

/-- The static laws of mobile ambients are those of one bag with unit. -/
theorem ambient_bagTheory :
    BagTheory ambientCalc ambientPresentation.contactConstructor.1 (some "AZero") :=
  bagTheory_of_check (by decide +kernel)

/-- The bag normal form is a section of the static equivalence. -/
def ambientCanonicalSection : ComputableCanonicalSection ambientIGSLT :=
  bagCanonicalSection ambientIGSLT ambient_bagTheory

/-- The three clauses for mobile ambients. -/
def ambientContinuedPresentation : ContinuedPresentation ambientIGSLT where
  cut := dissolutionCut
  canonical := ambientCanonicalSection
  retyping := ContinuationDecorationProfile.ofRetypingPlan dissolutionRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      dissolutionRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr dissolutionRetyping_wrappable

/-- **Mobile ambients are continued.** -/
theorem ambient_isContinued : IsContinued ambientIGSLT := ⟨ambientContinuedPresentation⟩

end Mettapedia.Languages.ProcessCalculi.Ambient.Mobile
