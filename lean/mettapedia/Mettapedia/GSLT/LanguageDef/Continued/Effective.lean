import Mettapedia.GSLT.LanguageDef.EffectiveSection
import Mettapedia.GSLT.LanguageDef.Continued.Presentation

/-!
# Effectively continued theories

The three clauses of a continued interactive theory are a cut, a section of
the static equivalence, and wrappability.  The record of a section asks for a
function with two laws, and a choice of representatives supplies one for
every theory, so the second clause as recorded excludes nothing.  A theory is
effectively continued when the section of some continued presentation is
tracked by a computable function on term codes.  That is the second clause
with its computability restored, and it is a restriction: an effectively
continued theory has a static equivalence decidable along every computable
family of terms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

/-- Some continued presentation of the theory has an effective section. -/
def IsEffectivelyContinued (theory : IGSLT) : Prop :=
  ∃ continued : ContinuedPresentation theory, continued.canonical.Effective

/-- An effectively continued theory is continued. -/
theorem IsEffectivelyContinued.isContinued {theory : IGSLT}
    (effective : IsEffectivelyContinued theory) : IsContinued theory :=
  ⟨effective.choose⟩

/-- **The static equivalence of an effectively continued theory is decidable**
along every family of terms whose codes are computable. -/
theorem IsEffectivelyContinued.computablePred {theory : IGSLT}
    (effective : IsEffectivelyContinued theory) {left right : ℕ → theory.toGSLT.Term}
    (leftComputable : Computable fun index => theory.termCode (left index))
    (rightComputable : Computable fun index => theory.termCode (right index)) :
    ComputablePred fun index => theory.toGSLT.equations.r (left index) (right index) := by
  obtain ⟨continued, tracked⟩ := effective
  exact tracked.computablePred leftComputable rightComputable

/-- **The lambda calculus is effectively continued**: its static equivalence
is equality and the identity is its section. -/
theorem lambda_isEffectivelyContinued :
    IsEffectivelyContinued LambdaContinuedInteraction.lambdaIGSLT :=
  ⟨LambdaContinuedInteraction.lambdaCIGSLT.toContinuedPresentation rfl,
    ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => Subtype.ext rfl⟩

end Mettapedia.GSLT.LanguageDef
