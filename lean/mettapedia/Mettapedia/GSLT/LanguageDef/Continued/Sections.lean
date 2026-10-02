import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.Languages.ProcessCalculi.CCS.Continued

/-!
# The section is a choice

A section of the static equivalence picks one representative per class, and
where a class has more than one member there is more than one way to pick.
Any section followed by a re-choice of representative within the class is
again a section.  For a bag theory, listing the components of the outermost
bag in the opposite order is such a re-choice.

CCS therefore carries two different sections, and so two different continued
presentations over the one iGSLT.  Passing from continued presentations to
their underlying iGSLTs is not injective: being continued is structure added
to an interactive theory, and the continued theories are not a subcollection
of the interactive ones.

The lambda calculus on the locally nameless carrier sits at both levels with
a single section: its static equivalence is equality, so no second choice
exists there.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open EquationSemantics
open WellSorted

/-- A section followed by a re-choice of representative within each class is
a section. -/
def ComputableCanonicalSection.rerepresent {theory : IGSLT}
    (canonical : ComputableCanonicalSection theory)
    (choice : theory.toGSLT.Term → theory.toGSLT.Term)
    (sound : ∀ term, theory.toGSLT.equations.r (choice term) term) :
    ComputableCanonicalSection theory where
  normalize := fun term => choice (canonical.normalize term)
  equivalent := fun term =>
    theory.toGSLT.equations.iseqv.trans (sound _) (canonical.equivalent term)
  complete := fun equivalent => congrArg choice (canonical.complete equivalent)

namespace BagNormalForm

variable {language : LanguageDef} {bag : GrammarRule} {unit : Option String}

/-- List the components of an outermost closed bag in the opposite order;
leave every other pattern as it is. -/
def reverseTop : Pattern → Pattern
  | .collection .hashBag elements none => .collection .hashBag elements.reverse none
  | pattern => pattern

/-- Reversing the outermost bag is one step of the static equivalence, or
none. -/
theorem path_reverseTop (laws : BagTheory language bag unit) (base : BasePremiseEvaluator)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    Path base language pattern (reverseTop pattern) := by
  match pattern, admissible with
  | .collection .hashBag elements none, admissible =>
      obtain ⟨parameterName, shape⟩ := laws.bagShape
      exact path_of_derived (DerivedInstance.bagPerm (rule := bag)
        ⟨laws.bagAuthored, parameterName, _, shape⟩
        (sortedAt_of_admissible laws admissible collectionless)
        (List.reverse_perm elements).symm)
  | .collection .hashBag _ (some _), _ => exact .refl
  | .collection .vec _ _, _ => exact .refl
  | .collection .hashSet _ _, _ => exact .refl
  | .bvar _, _ => exact .refl
  | .fvar _, _ => exact .refl
  | .apply _ _, _ => exact .refl
  | .lambda _ _, _ => exact .refl
  | .multiLambda _ _ _, _ => exact .refl
  | .subst _ _, _ => exact .refl

/-- The same re-choice on the closed interacting fibre. -/
def reverseTopClosed (theory : IGSLT)
    (laws : BagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) : theory.toGSLT.Term :=
  ⟨reverseTop term.1,
    (presented_of_path laws
      (path_reverseTop laws defaultBasePremises (admissible_of_closed term.2) rfl)
      term.2).choose⟩

/-- It stays within the class. -/
theorem reverseTopClosed_equivalent (theory : IGSLT)
    (laws : BagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) :
    theory.toGSLT.equations.r (reverseTopClosed theory laws term) term :=
  theory.toGSLT.equations.iseqv.symm
    (presented_of_path laws
      (path_reverseTop laws defaultBasePremises (admissible_of_closed term.2) rfl)
      term.2).choose_spec

/-- **A second section of a bag theory**: the bag normal form with the
outermost bag listed in the opposite order. -/
def reversedBagSection (theory : IGSLT)
    (laws : BagTheory theory.presentation.presentation.language bag unit) :
    ComputableCanonicalSection theory :=
  (bagCanonicalSection theory laws).rerepresent (reverseTopClosed theory laws)
    (reverseTopClosed_equivalent theory laws)

@[simp] theorem reversedBagSection_normalize_val (theory : IGSLT)
    (laws : BagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) :
    ((reversedBagSection theory laws).normalize term).1 =
      reverseTop (normalForm unit term.1) :=
  rfl

end BagNormalForm

/-! ## Two sections, two continued presentations, one iGSLT -/

section CCS

open Mettapedia.Languages.ProcessCalculi.CCS
open BagNormalForm

/-- The second section of CCS. -/
def ccsReversedSection : ComputableCanonicalSection ccsIGSLT :=
  reversedBagSection ccsIGSLT ccs_bagTheory

/-- The two sections choose different representatives of the handshake. -/
theorem ccs_sections_differ : ccsCanonicalSection ≠ ccsReversedSection := by
  intro same
  have first := handshake_representative.1
  have second : (ccsReversedSection.normalize handshakeTerm).1 = handshakeSwapped := by
    show reverseTop (normalForm (some "CNil") handshakeTerm.1) = handshakeSwapped
    have normal : normalForm (some "CNil") handshakeTerm.1 = handshake := first
    rw [normal]
    rfl
  rw [same, second] at first
  revert first
  decide

/-- The three clauses for CCS with the second section. -/
def ccsReversedContinuedPresentation : ContinuedPresentation ccsIGSLT :=
  { ccsContinuedPresentation with canonical := ccsReversedSection }

/-- **Two continued presentations over one iGSLT.** -/
theorem ccs_two_continuedPresentations :
    ccsContinuedPresentation ≠ ccsReversedContinuedPresentation := by
  intro same
  exact ccs_sections_differ (congrArg ContinuedPresentation.canonical same)

/-- **Continued is added structure.**  Passing from a continued presentation
to its iGSLT is not injective. -/
theorem continuedPresentation_underlying_not_injective :
    ¬ Function.Injective
      (Sigma.fst : (Σ theory : IGSLT, ContinuedPresentation theory) → IGSLT) := by
  intro injective
  have same : (⟨ccsIGSLT, ccsContinuedPresentation⟩ :
      Σ theory : IGSLT, ContinuedPresentation theory) =
        ⟨ccsIGSLT, ccsReversedContinuedPresentation⟩ :=
    injective rfl
  exact ccs_two_continuedPresentations (eq_of_heq (Sigma.mk.inj same).2)

end CCS

/-! ## Lambda at both levels -/

/-- The lambda calculus is the underlying iGSLT of a continued theory, and on
this carrier its section is the only one. -/
theorem lambda_at_both_levels :
    CIGSLT.forget.obj LambdaContinuedInteraction.lambdaCIGSLT =
        LambdaContinuedInteraction.lambdaIGSLT ∧
      ∀ first second :
          ComputableCanonicalSection LambdaContinuedInteraction.lambdaIGSLT,
        first = second :=
  ⟨rfl, lambda_section_unique⟩

end Mettapedia.GSLT.LanguageDef
