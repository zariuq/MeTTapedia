import Mettapedia.GSLT.LanguageDef.Continued.Presentation
import Mettapedia.GSLT.LanguageDef.BagNormalFormSection
import Mettapedia.Languages.ProcessCalculi.CCS.Continued

/-!
# The section is a choice

A section of the static equivalence picks one representative per class, and
where a class has more than one member there is more than one way to pick.
Any section followed by a re-choice of representative within the class is
again a section.  For a bag theory, and for a calculus with restriction,
listing the components of the outermost bag in the opposite order is such a
re-choice.

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
theorem path_reverseTop (laws : BareBagTheory language bag unit) (base : BasePremiseEvaluator)
    {free : FreeTypeContext} {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern}
    (admissible : Admissible language free bound type pattern)
    (collectionless : collectionFree type = true) :
    Path base language pattern (reverseTop pattern) := by
  match pattern, admissible with
  | .collection .hashBag elements none, admissible =>
      exact path_of_derived (DerivedInstance.bagPerm_of_sorted (category := bag.category)
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
    (laws : BareBagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) : theory.toGSLT.Term :=
  ⟨reverseTop term.1,
    (presented_of_path laws
      (path_reverseTop laws defaultBasePremises (admissible_of_closed term.2) rfl)
      term.2).choose⟩

/-- It stays within the class. -/
theorem reverseTopClosed_equivalent (theory : IGSLT)
    (laws : BareBagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) :
    theory.toGSLT.equations.r (reverseTopClosed theory laws term) term :=
  theory.toGSLT.equations.iseqv.symm
    (presented_of_path laws
      (path_reverseTop laws defaultBasePremises (admissible_of_closed term.2) rfl)
      term.2).choose_spec

/-- **A second section of a bag theory**: the bag normal form with the
outermost bag listed in the opposite order. -/
def reversedBagSection (theory : IGSLT)
    (laws : BareBagTheory theory.presentation.presentation.language bag unit) :
    ComputableCanonicalSection theory :=
  (bagCanonicalSection theory laws).rerepresent (reverseTopClosed theory laws)
    (reverseTopClosed_equivalent theory laws)

@[simp] theorem reversedBagSection_normalize_val (theory : IGSLT)
    (laws : BareBagTheory theory.presentation.presentation.language bag unit)
    (term : theory.toGSLT.Term) :
    ((reversedBagSection theory laws).normalize term).1 =
      reverseTop (normalForm unit term.1) :=
  rfl

end BagNormalForm

/-! ## A second section of a calculus with restriction -/

namespace RestrictionBlocks

variable {language : LanguageDef} {block : Block} [laws : BlockLanguage language block]

include laws in
/-- Reversing the outermost bag of a process is a chain of laws through processes, or none. -/
theorem reverseTop_sorted {free : FreeTypeContext} {bound : List TypeExpr} {pattern : Pattern} {sort : String}
    (typed : HasType language free bound pattern (.base sort)) :
    SortedEquiv language free bound (.base sort) pattern (BagNormalForm.reverseTop pattern) := by
  match pattern, typed with
  | .collection .hashBag elements none, typed =>
      obtain ⟨-, rfl, -⟩ := laws.bag_members typed
      have members := members_of_bag (block := block) typed
      have reversedTyped : HasType language free bound (.collection .hashBag elements.reverse none)
          (.base block.proc) :=
        bag_typed (block := block) fun element member => members element (List.mem_reverse.mp member)
      obtain ⟨bag, presented, category⟩ := laws.bag
      exact SortedEquiv.ofDerived
        (DerivedInstance.bagPerm_of_sorted (category := bag.category) ⟨free, bound, by rwa [category]⟩
          (List.reverse_perm elements).symm) typed reversedTyped
  | .collection .hashBag _ (some _), _ => exact Relation.EqvGen.refl _
  | .collection .vec _ _, _ => exact Relation.EqvGen.refl _
  | .collection .hashSet _ _, _ => exact Relation.EqvGen.refl _
  | .bvar _, _ => exact Relation.EqvGen.refl _
  | .fvar _, _ => exact Relation.EqvGen.refl _
  | .apply _ _, _ => exact Relation.EqvGen.refl _
  | .lambda _ _, _ => exact Relation.EqvGen.refl _
  | .multiLambda _ _ _, _ => exact Relation.EqvGen.refl _
  | .subst _ _, _ => exact Relation.EqvGen.refl _

end RestrictionBlocks

open RestrictionBlocks (Block BlockLanguage)

/-- Reversing the outermost bag of a closed process of a calculus with restriction keeps it closed. -/
def reverseTopBlockClosed (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block]
    (term : theory.toGSLT.Term) : theory.toGSLT.Term :=
  ⟨BagNormalForm.reverseTop term.1,
    RestrictionBlocks.closed_of_sorted (block := block) term.2
      (RestrictionBlocks.reverseTop_sorted (block := block) term.2.1)⟩

/-- It stays within the class. -/
theorem reverseTopBlockClosed_equivalent (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block]
    (term : theory.toGSLT.Term) :
    theory.toGSLT.equations.r (reverseTopBlockClosed theory block term) term :=
  theory.toGSLT.equations.iseqv.symm
    (presented_of_sorted (block := block) (RestrictionBlocks.reverseTop_sorted (block := block) term.2.1)
      term.2 _)

/-- **A second section of a calculus with restriction**: the canonical form with the outermost bag listed in the
opposite order. -/
def reversedBlockSection (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] :
    ComputableCanonicalSection theory :=
  (blockCanonicalSection theory block).rerepresent (reverseTopBlockClosed theory block)
    (reverseTopBlockClosed_equivalent theory block)

@[simp] theorem reversedBlockSection_normalize_val (theory : IGSLT) (block : Block)
    [laws : BlockLanguage theory.presentation.presentation.language block] (term : theory.toGSLT.Term) :
    ((reversedBlockSection theory block).normalize term).1 =
      BagNormalForm.reverseTop (RestrictionBlocks.canon block term.1) :=
  rfl

/-! ## Two sections, two continued presentations, one iGSLT -/

section CCS

open Mettapedia.Languages.ProcessCalculi.CCS

/-- The second section of CCS. -/
def ccsReversedSection : ComputableCanonicalSection ccsIGSLT :=
  reversedBlockSection (laws := Mettapedia.Languages.ProcessCalculi.CCS.Blocks.ccsBlockLanguage) ccsIGSLT
    Mettapedia.Languages.ProcessCalculi.CCS.Blocks.ccsBlock

/-- **The two sections choose different representatives** of `τ.0 | τ.τ.0`. -/
theorem ccs_sections_differ : ccsCanonicalSection ≠ ccsReversedSection := by
  intro same
  have first : (ccsCanonicalSection.normalize silentPairTerm).1 = par [silentOnce, silentTwice] := by
    decide +kernel
  have second : (ccsReversedSection.normalize silentPairTerm).1 = par [silentTwice, silentOnce] := by
    decide +kernel
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
