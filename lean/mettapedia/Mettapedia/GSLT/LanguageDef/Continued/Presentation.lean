import Mettapedia.GSLT.LanguageDef.ContinuedCategory
import Mettapedia.GSLT.LanguageDef.Continued.ContinuationDecoration
import Mettapedia.GSLT.LanguageDef.LambdaContinuedInteraction
import Mettapedia.GSLT.LanguageDef.Interaction.Controls.ContactContinued

/-!
# A continued interactive GSLT as the three clauses state it

The definition of a continued interactive GSLT has three clauses: a
presentation of the dynamics in interaction-cut form, a section of the static
equivalence on the interacting sort, and wrappability of the contraction.
`ContinuedPresentation` records these over one iGSLT. Continuation decoration
can select a finite bundle on each operand, and its constructor closure is
independent of that selection. Both the redex and contractum sorting laws
are checked for that exact generated signature.

The category `CIGSLT` asks for more: a reflection profile, sections on every
open fibre with support laws, and the stability laws that let the cost
construction be iterated.  For a continued theory that authors no reflection,
that richer structure restricts to a `ContinuedPresentation`.

A theory with no static equation has exactly one section, the identity.  Two
different sections over one iGSLT therefore need a theory whose static
equivalence identifies distinct terms.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open EquationSemantics
open WellSorted

/-- The three clauses, over one iGSLT. -/
structure ContinuedPresentation (theory : IGSLT) where
  /-- (i) The selected rule in interaction-cut form. -/
  cut : InteractionCutPresentation theory
  /-- (ii) A section of the static equivalence of the interacting fibre. -/
  canonical : ComputableCanonicalSection theory
  /-- (iii) The finite continuation bundle and its declaration-derived
  constructor closure. -/
  retyping : ContinuationDecorationProfile cut
  /-- ...the redex stays sorted when its continuations are wrapped... -/
  redexRetypable : retyping.RedexRetypable
  /-- ...and the contractum has the wrapped sort. -/
  wrappable : retyping.Wrappable

/-- The theory satisfies the three clauses for some choice of the data. -/
def IsContinued (theory : IGSLT) : Prop := Nonempty (ContinuedPresentation theory)

/-- When a presentation generates no static equation, equality is a section
of its static equivalence. -/
def ComputableCanonicalSection.ofEquationFree (theory : IGSLT)
    (equationFree : theory.presentation.presentation.language.isEquationFree = true) :
    ComputableCanonicalSection theory where
  normalize := id
  equivalent := fun term => theory.toGSLT.equations.iseqv.refl term
  complete := by
    intro left right equivalent
    exact (presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises
      theory.presentation equationFree left right).mp equivalent

/-! ## From a reflection-free continued theory -/

namespace CIGSLT

/-- The continued theory authors no reflective presentation. -/
def ReflectionFree (theory : CIGSLT) : Prop :=
  theory.reflection.1.presentations = []

variable (theory : CIGSLT)

/-- A closed term of the interacting fibre in the canonical carrier. -/
def closedToCarrier (free : theory.ReflectionFree)
    (term : theory.theory.toGSLT.Term) : theory.CanonicalCarrier :=
  ⟨term.1, (closedTermToOpen term).2, by
    intro presentation membership
    rw [free] at membership
    cases membership⟩

/-- An element of the canonical carrier as a closed term. -/
def carrierToClosed (term : theory.CanonicalCarrier) : theory.theory.toGSLT.Term :=
  openTermEmptyToClosed term.toCore

@[simp] theorem carrierToClosed_pattern (term : theory.CanonicalCarrier) :
    (theory.carrierToClosed term).1 = term.1 :=
  rfl

@[simp] theorem closedToCarrier_pattern (free : theory.ReflectionFree)
    (term : theory.theory.toGSLT.Term) :
    (theory.closedToCarrier free term).1 = term.1 :=
  rfl

/-- With no reflective presentation, a reflective equation step is an
ordinary one. -/
theorem contextStep_of_reflective (free : theory.ReflectionFree) {left right : Pattern}
    (step : ReflectiveEquationSemantics.ReflectiveEquationContextStep theory.reflection.1
      defaultBasePremises theory.theory.presentation.presentation.language left right) :
    EquationContextStep defaultBasePremises
      theory.theory.presentation.presentation.language left right := by
  cases step with
  | core ordinary => exact ordinary
  | reflectiveInContext context membership _ =>
      rw [free] at membership
      cases membership

/-- **The closed section of a reflection-free continued theory.**  Its
canonicalization on the closed interacting fibre is a section of the static
equivalence of the underlying iGSLT. -/
def closedSection (free : theory.ReflectionFree) :
    ComputableCanonicalSection theory.theory where
  normalize := fun term =>
    theory.carrierToClosed (theory.canonical.normalize (theory.closedToCarrier free term))
  equivalent := by
    intro term
    have fibre := theory.canonical.equivalent (theory.closedToCarrier free term)
    generalize theory.canonical.normalize (theory.closedToCarrier free term) = normal at fibre
    have transported : ∀ {first second : theory.CanonicalCarrier},
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid theory.reflection.1
          defaultBasePremises theory.theory.presentation.presentation.language
          FreeTypeContext.empty []
          (.base theory.theory.presentation.interactingLangSort.1)).r first second →
        theory.theory.toGSLT.equations.r (theory.carrierToClosed first)
          (theory.carrierToClosed second) := by
      intro first second related
      induction related with
      | rel first second step =>
          exact Relation.EqvGen.rel _ _ (theory.contextStep_of_reflective free step)
      | refl vertex => exact Relation.EqvGen.refl _
      | symm first second _ recurse => exact Relation.EqvGen.symm _ _ recurse
      | trans first middle second _ _ firstStep secondStep =>
          exact Relation.EqvGen.trans _ _ _ firstStep secondStep
    have closed := transported fibre
    have same : theory.carrierToClosed (theory.closedToCarrier free term) = term :=
      Subtype.ext rfl
    rwa [same] at closed
  complete := by
    intro left right equivalent
    have lifted :
        (ReflectiveEquationSemantics.reflectiveOpenPatternEquationSetoid theory.reflection.1
          defaultBasePremises theory.theory.presentation.presentation.language
          FreeTypeContext.empty []
          (.base theory.theory.presentation.interactingLangSort.1)).r
          (theory.closedToCarrier free left) (theory.closedToCarrier free right) := by
      induction equivalent with
      | rel left right step =>
          exact Relation.EqvGen.rel _ _
            (ReflectiveEquationSemantics.ReflectiveEquationContextStep.core step)
      | refl vertex => exact Relation.EqvGen.refl _
      | symm left right _ recurse => exact Relation.EqvGen.symm _ _ recurse
      | trans left middle right _ _ firstStep secondStep =>
          exact Relation.EqvGen.trans _ _ _ firstStep secondStep
    exact congrArg theory.carrierToClosed (theory.canonical.complete lifted)

/-- **A reflection-free continued theory satisfies the three clauses.** -/
def toContinuedPresentation (free : theory.ReflectionFree) :
    ContinuedPresentation theory.theory where
  cut := theory.cut
  canonical := theory.closedSection free
  retyping := ContinuationDecorationProfile.ofRetypingPlan theory.continuationRetyping
  redexRetypable :=
    (ContinuationDecorationProfile.ofRetypingPlan_redexRetypable_iff _).mpr theory.redexRetypable
  wrappable :=
    (ContinuationDecorationProfile.ofRetypingPlan_wrappable_iff _).mpr theory.wrappable

end CIGSLT

/-! ## Instances -/

/-- The lambda calculus satisfies the three clauses. -/
theorem lambda_isContinued :
    IsContinued LambdaContinuedInteraction.lambdaIGSLT :=
  ⟨LambdaContinuedInteraction.lambdaCIGSLT.toContinuedPresentation rfl⟩

/-- The law-free contact theory satisfies the three clauses. -/
theorem bare_isContinued :
    IsContinued Interaction.Controls.EquationalContact.bare :=
  ⟨Interaction.Controls.EquationalContact.bareContinued.toContinuedPresentation rfl⟩

/-! ## A theory without equations has one section -/

/-- When the static equivalence of the interacting fibre is equality, every
section is the identity. -/
theorem ComputableCanonicalSection.normalize_eq_self_of_equality {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (equality : ∀ left right : theory.toGSLT.Term,
      theory.toGSLT.equations.r left right → left = right)
    (term : theory.toGSLT.Term) : canonical.normalize term = term :=
  equality _ _ (canonical.equivalent term)

/-- The lambda calculus on this carrier has exactly one section. -/
theorem lambda_section_unique
    (first second : ComputableCanonicalSection LambdaContinuedInteraction.lambdaIGSLT) :
    first = second := by
  apply ComputableCanonicalSection.ext
  funext term
  have equality : ∀ left right : LambdaContinuedInteraction.lambdaIGSLT.toGSLT.Term,
      LambdaContinuedInteraction.lambdaIGSLT.toGSLT.equations.r left right → left = right :=
    fun left right related =>
      (presentedEquationSetoid_iff_eq_of_no_generators defaultBasePremises
        LambdaContinuedInteraction.lambdaInteractivePresentation (by rfl) left right).mp related
  rw [first.normalize_eq_self_of_equality equality,
    second.normalize_eq_self_of_equality equality]

end Mettapedia.GSLT.LanguageDef
