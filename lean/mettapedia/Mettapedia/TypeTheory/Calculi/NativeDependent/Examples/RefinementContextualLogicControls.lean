import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualImages
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementContextualRefinementControls
import Mettapedia.TypeTheory.ContextualPredicateComprehension

/-!
# Generated logical guards and equal raw presentations

The generic ordinary proposition predicate admits quoted truth and rejects
quoted falsehood in the actual generated dependent model. Refinement retains
the admitted complete value. Separately, quoting and reading a predicate
changes its raw presentation while giving a genuine generated equation and
an isomorphism between its data contexts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.LogicControls

open _root_.CategoryTheory
open ContextualPredicatePropositions ContextualProductComparison

noncomputable section

abbrev signature := Controls.signature
abbrev context := RefinementControls.context
abbrev qcontext := RefinementControls.qcontext
abbrev core := QuotientCwf.cwf signature
abbrev doctrine := predicateDoctrine signature
abbrev propositions := PropositionModel.operations signature
abbrev refinements := RefinementModel.operations signature

local instance : HeytingAlgebra (doctrine.Predicate qcontext) :=
  Logic.predicateHeytingAlgebra context

def truthValue : QuotientCwf.Tm qcontext (propositions.omega qcontext) := propositions.quote ⊤
def falseValue : QuotientCwf.Tm qcontext (propositions.omega qcontext) := propositions.quote ⊥
def genericGuard := genericPredicate propositions qcontext

theorem quoted_truth_admitted :
    doctrine.reindex (selfExtend core truthValue) genericGuard = ⊤ :=
  genericPredicate_at_quote propositions ⊤

theorem quoted_false_rejected :
    doctrine.reindex (selfExtend core falseValue) genericGuard ≠ ⊤ := by
  have read := genericPredicate_at_quote propositions (⊥ : doctrine.Predicate qcontext)
  intro collapsed
  exact RefinementControls.predicates_remain_distinct (read.symm.trans collapsed).symm

def refinedTruth := refinements.intro (propositions.omega qcontext)
  genericGuard truthValue quoted_truth_admitted

theorem selected_truth_retained :
    refinements.forget (propositions.omega qcontext) genericGuard refinedTruth = truthValue :=
  refinements.beta _ _ _ _

theorem no_refined_false_readout :
    ¬ ∃ term : QuotientCwf.Tm qcontext
      (refinements.refined (propositions.omega qcontext) genericGuard),
      refinements.forget (propositions.omega qcontext) genericGuard term = falseValue := by
  rintro ⟨term, readout⟩
  have guard := refinements.forget_guard (propositions.omega qcontext) genericGuard term
  rw [readout] at guard
  exact quoted_false_rejected guard

def rawDomain : TypeOver context := propositionsType context
def firstGuard : PredicateOver (extend context rawDomain) := Logic.truth _
def secondGuard : PredicateOver (extend context rawDomain) :=
  holdsProposition (quotePredicate firstGuard)
def firstAnnotation : TypeOver context := Refinements.rawType rawDomain firstGuard
def secondAnnotation : TypeOver context := Refinements.rawType rawDomain secondGuard

theorem annotation_equation :
    Holds signature (.typeEq context.raw firstAnnotation.code secondAnnotation.code) :=
  conclude (.comprehensionCongruence context.raw rawDomain.code rawDomain.code
    firstGuard.code secondGuard.code)
    ⟨typeEquality_refl rawDomain,
      predicateEquality_symm (conclude (.holdsQuote (extend context rawDomain).raw firstGuard.code)
        ⟨firstGuard.formed, trivial⟩), secondGuard.formed, trivial⟩

theorem annotation_classes_agree : QType.mk firstAnnotation = QType.mk secondAnnotation :=
  _root_.Quotient.sound annotation_equation

theorem raw_extended_presentations_differ :
    (extend context firstAnnotation).raw ≠ (extend context secondAnnotation).raw := by
  intro equality
  cases equality

def presentationComparison : extend context firstAnnotation ≅ extend context secondAnnotation :=
  extensionComparison firstAnnotation secondAnnotation annotation_equation

theorem presentation_comparison_preserves_projection :
    presentationComparison.hom ≫ projectionHom context secondAnnotation =
      projectionHom context firstAnnotation :=
  extensionComparison_projection _ _ _

end
end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.LogicControls
