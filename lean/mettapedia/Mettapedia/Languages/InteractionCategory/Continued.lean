import Mettapedia.Languages.InteractionCategory.Interaction
import Mettapedia.Languages.InteractionCategory.Decoration
import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.Continued.Effective

/-!
# Silent and visible composition are effectively continued

Under the silent reading the three clauses hold: the composition rule is an
interaction cut, the presentation authors no static equation so equality is
its section, and the contractum is covered and has the wrapped sort.

Under the visible reading the decorated constructor closure includes the
action prefix rebuilt by the actual composition rule. This types its redex
and contractum, while excluding the prefix still fails the restrictive
non-principal sorting problem. Both readings have an identity section on
their actual equation-free carrier; its code tracking is checked separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.InteractionCategory

open Mettapedia.GSLT.LanguageDef

/-- Neither reading generates a static equation. -/
theorem interactionCategory_equationFree (reading : Reading) :
    (interactionCategory reading).isEquationFree = true := by
  cases reading <;> decide

/-- Equality is the section of both readings. -/
def canonicalSection (reading : Reading) : ComputableCanonicalSection (theory reading) :=
  ComputableCanonicalSection.ofEquationFree (theory reading)
    (interactionCategory_equationFree reading)

/-- The three clauses for silent composition. -/
def silentContinuedPresentation : ContinuedPresentation (theory .silent) where
  cut := cut .silent
  canonical := canonicalSection .silent
  retyping := ContinuationDecorationProfile.ofRetypingPlan silentRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr
      silentRetyping_redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr silentRetyping_wrappable

/-- **Silent composition is continued.** -/
theorem silent_isContinued : IsContinued (theory .silent) := ⟨silentContinuedPresentation⟩

/-- The actual visible composition rule with its constructive quotient
section and independent decorated constructor closure. -/
def visibleContinuedPresentation : ContinuedPresentation (theory .visible) where
  cut := cut .visible
  canonical := canonicalSection .visible
  retyping := visibleDecoration
  redexRetypable := visibleDecoration_redexRetypable
  wrappable := visibleDecoration_wrappable

/-- Visible composition satisfies the algebraic continued clauses. -/
theorem visible_isContinued : IsContinued (theory .visible) :=
  ⟨visibleContinuedPresentation⟩

/-- The identity section of either equation-free reading has a computable
tracking function on the actual structural codes. -/
theorem canonicalSection_effective (reading : Reading) :
    (canonicalSection reading).Effective :=
  ComputableCanonicalSection.effective_of_normalize_eq _ fun _ => rfl

/-- The visible composition witness has the independent effectiveness law. -/
theorem visible_isEffectivelyContinued : IsEffectivelyContinued (theory .visible) :=
  ⟨visibleContinuedPresentation, canonicalSection_effective .visible⟩

end Mettapedia.Languages.InteractionCategory
