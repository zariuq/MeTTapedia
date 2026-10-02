import Mettapedia.GSLT.LanguageDef.ReflectiveEffectiveSection
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalCode

/-!
# The canonical section of the rho calculus is effective

The closed canonical section of the rho calculus is a section of its
reflective static equivalence: parallel composition is a bag with unit, and a
quoted drop is the name dropped.  Its normal-form function is the canonical
form compiled from the reflective presentation, which is primitive recursive
on codes.  So the section is effective, and the reflective static equivalence
is decidable along every computable family of closed processes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ReflectionExtension
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalMatch
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT

/-- **The canonical section of the rho calculus is effective.** -/
theorem rhoCanonicalSection_effective : rhoCanonicalSection.Effective :=
  ⟨ReflectiveCanonical.canonicalizeCode rhoReflectivePresentation,
    (ReflectiveCanonical.canonicalizeCode_primrec _).to_comp, fun term => by
      rw [ReflectiveCanonical.canonicalizeCode_patternCode, derivedCanonicalize_eq]
      rfl⟩

/-- **The reflective static equivalence of the rho calculus is decidable**
along every family of closed processes whose codes are computable.  This
applies the general statement for effective sections to rho. -/
theorem rho_equivalence_computablePred {left right : ℕ → rhoIGSLT.toGSLT.Term}
    (leftComputable : Computable fun index => rhoIGSLT.termCode (left index))
    (rightComputable : Computable fun index => rhoIGSLT.termCode (right index)) :
    ComputablePred fun index =>
      (reflectiveClosedEquationSetoid rhoIGSLT
        rhoCalcValidatedReflective.admittedReflection).r (left index) (right index) :=
  rhoCanonicalSection_effective.computablePred leftComputable rightComputable

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefCanonicalSection
