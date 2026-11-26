import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundnessFormation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPredicateInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPredicateCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionReadout
import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessLogic

/-!
# Actual native proposition and refinement rule interpretations

Formation uses actual contextual subobjects. Quote and holds read the ordinary
native proposition type in both directions. Refine preserves its supplied
inhabitant only when the actual predicate holds throughout the satisfying
context; forgetting and its computation laws retain that complete inhabitant.
Proof-tree identity is separate from these semantic value equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory NativeLocalTypeFormers PresheafNativePropositionReadout
open Mettapedia.GSLT.Topos
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open DisplayedPresheafComprehension
open External (bindResult)
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {D : Signature S}

namespace ModelData

variable (model : ModelData S C) {n : Nat}

theorem evaluate_refine (Γ : Scope C n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n) (A : NativeType Γ.1)
    (φ : Subfunctor (totalSpace A.decoded)) (value : A.decoded.sections)
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ)
    (termRead : model.evaluateTerm Γ term = some ⟨A, value⟩)
    (satisfies : ∀ world (base : Γ.1.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ φ.obj world) :
    model.evaluateTerm Γ (.refine domain predicate term) =
      some ⟨PresheafNativeStableRefinement.chosen A φ,
        PresheafNativeStableRefinement.intro A φ value satisfies⟩ := by
  simp only [evaluateTerm, domainRead, bindResult]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  change refine? A φ (model.evaluateTerm Γ term) = _
  rw [termRead]
  exact refine?_supplied A φ value satisfies

theorem evaluate_forget (Γ : Scope C n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n) (A : NativeType Γ.1)
    (φ : Subfunctor (totalSpace A.decoded))
    (value : (PresheafNativeStableRefinement.chosen A φ).decoded.sections)
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ)
    (termRead : model.evaluateTerm Γ term = some ⟨PresheafNativeStableRefinement.chosen A φ, value⟩) :
    model.evaluateTerm Γ (.forget domain predicate term) =
      some ⟨A, PresheafNativeStableRefinement.forget A φ value⟩ := by
  simp only [evaluateTerm, domainRead, bindResult]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  change forget? A φ (model.evaluateTerm Γ term) = _
  rw [termRead]
  exact forget?_supplied A φ value

theorem predicatePrimitive_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (arguments : Substitution S (S.predicateArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.predicateParameters symbol) arguments)) :
    Interprets model (.predicate context (.atom symbol arguments)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicatePrimitive_sound model.toAbstract realization.toAbstract context symbol
      arguments contextInterpreted.toAbstract argumentsInterpreted.toAbstract)

theorem truthFormation_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.predicate context .truth) :=
  model.interprets_of_abstract
    (Abstract.ModelData.truthFormation_sound model.toAbstract context contextInterpreted.toAbstract)

theorem falsehoodFormation_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.predicate context .falsehood) :=
  model.interprets_of_abstract
    (Abstract.ModelData.falsehoodFormation_sound model.toAbstract context contextInterpreted.toAbstract)

theorem conjunctionFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.and first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.conjunctionFormation_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem disjunctionFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.or first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.disjunctionFormation_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem implicationFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.implies first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.implicationFormation_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem universalFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.predicate context (.all domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.universalFormation_sound model.toAbstract context domain predicate
      domainInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem existentialFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.predicate context (.exists domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.existentialFormation_sound model.toAbstract context domain predicate
      domainInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem quote_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.term context (.quote predicate) .propositions) :=
  model.interprets_of_abstract
    (Abstract.ModelData.quote_sound model.toAbstract context predicate predicateInterpreted.toAbstract)

theorem holdsFormation_sound (context : ContextExpr S n) (term : TermExpr S n)
    (termInterpreted : Interprets model (.term context term .propositions)) :
    Interprets model (.predicate context (.holds term)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.holdsFormation_sound model.toAbstract context term termInterpreted.toAbstract)

theorem imageFormation_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (typeInterpreted : Interprets model (.type context type)) :
    Interprets model (.predicate context (.image type)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.imageFormation_sound model.toAbstract context type typeInterpreted.toAbstract)

theorem holdsQuote_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.predicateEq context (.holds (.quote predicate)) predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.holdsQuote_sound model.toAbstract context predicate
      predicateInterpreted.toAbstract)

theorem quoteHolds_sound (context : ContextExpr S n) (term : TermExpr S n)
    (termInterpreted : Interprets model (.term context term .propositions)) :
    Interprets model (.termEq context (.quote (.holds term)) term .propositions) :=
  model.interprets_of_abstract
    (Abstract.ModelData.quoteHolds_sound model.toAbstract context term termInterpreted.toAbstract)

theorem truthIntroduction_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.entails context .truth) :=
  model.interprets_of_abstract
    (Abstract.ModelData.truthIntroduction_sound model.toAbstract context contextInterpreted.toAbstract)

theorem falsehoodElimination_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate))
    (falseInterpreted : Interprets model (.entails context .falsehood)) :
    Interprets model (.entails context predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.falsehoodElimination_sound model.toAbstract context predicate
      predicateInterpreted.toAbstract falseInterpreted.toAbstract)

theorem conjunctionIntroduction_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.entails context first))
    (secondInterpreted : Interprets model (.entails context second)) :
    Interprets model (.entails context (.and first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.conjunctionIntroduction_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem conjunctionFirst_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (togetherInterpreted : Interprets model (.entails context (.and first second))) :
    Interprets model (.entails context first) :=
  model.interprets_of_abstract
    (Abstract.ModelData.conjunctionFirst_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract togetherInterpreted.toAbstract)

theorem conjunctionSecond_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (togetherInterpreted : Interprets model (.entails context (.and first second))) :
    Interprets model (.entails context second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.conjunctionSecond_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract togetherInterpreted.toAbstract)

theorem disjunctionFirst_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context (.or first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.disjunctionFirst_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract heldInterpreted.toAbstract)

theorem disjunctionSecond_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (heldInterpreted : Interprets model (.entails context second)) :
    Interprets model (.entails context (.or first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.disjunctionSecond_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract heldInterpreted.toAbstract)

theorem implicationElimination_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (implicationInterpreted : Interprets model (.entails context (.implies first second)))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.implicationElimination_sound model.toAbstract context first second
      firstInterpreted.toAbstract secondInterpreted.toAbstract implicationInterpreted.toAbstract
      heldInterpreted.toAbstract)

theorem transportPredicate_sound (first second : ContextExpr S n) (predicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicateInterpreted : Interprets model (.predicate first predicate)) :
    Interprets model (.predicate second predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportPredicate_sound model.toAbstract first second predicate
      contextsInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem transportEntailment_sound (first second : ContextExpr S n) (predicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicateInterpreted : Interprets model (.entails first predicate)) :
    Interprets model (.entails second predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.transportEntailment_sound model.toAbstract first second predicate
      contextsInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem predicatePrimitiveCongruence_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (first second : Substitution S (S.predicateArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitutionEq context (D.predicateParameters symbol) first second)) :
    Interprets model (.predicateEq context (.atom symbol first) (.atom symbol second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicatePrimitiveCongruence_sound model.toAbstract realization.toAbstract context
      symbol first second argumentsInterpreted.toAbstract)

theorem universalIntroduction_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (heldInterpreted : Interprets model (.entails (.snoc context domain) predicate)) :
    Interprets model (.entails context (.all domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.universalIntroduction_sound model.toAbstract context domain predicate
      domainInterpreted.toAbstract predicateInterpreted.toAbstract heldInterpreted.toAbstract)

theorem imageIntroduction_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (term : TermExpr S n) (typeInterpreted : Interprets model (.type context type))
    (termInterpreted : Interprets model (.term context term type)) :
    Interprets model (.entails context (.image type)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.imageIntroduction_sound model.toAbstract context type term
      typeInterpreted.toAbstract termInterpreted.toAbstract)

theorem predicateReflexivity_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.predicateEq context predicate predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicateReflexivity_sound model.toAbstract context predicate
      predicateInterpreted.toAbstract)

theorem predicateSymmetry_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second)) :
    Interprets model (.predicateEq context second first) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicateSymmetry_sound model.toAbstract context first second
      predicatesInterpreted.toAbstract)

theorem predicateTransitivity_sound (context : ContextExpr S n) (first middle last : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first middle))
    (secondInterpreted : Interprets model (.predicateEq context middle last)) :
    Interprets model (.predicateEq context first last) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicateTransitivity_sound model.toAbstract context first middle last
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem entailmentConversion_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.entailmentConversion_sound model.toAbstract context first second
      predicatesInterpreted.toAbstract heldInterpreted.toAbstract)

theorem contextAssumeEquality_sound (first second : ContextExpr S n)
    (firstPredicate secondPredicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicatesInterpreted : Interprets model (.predicateEq first firstPredicate secondPredicate)) :
    Interprets model (.contextEq (.assume first firstPredicate) (.assume second secondPredicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.contextAssumeEquality_sound model.toAbstract first second firstPredicate
      secondPredicate contextsInterpreted.toAbstract predicatesInterpreted.toAbstract)

theorem quoteCongruence_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second)) :
    Interprets model (.termEq context (.quote first) (.quote second) .propositions) :=
  model.interprets_of_abstract
    (Abstract.ModelData.quoteCongruence_sound model.toAbstract context first second
      predicatesInterpreted.toAbstract)

theorem holdsCongruence_sound (context : ContextExpr S n) (first second : TermExpr S n)
    (termsInterpreted : Interprets model (.termEq context first second .propositions)) :
    Interprets model (.predicateEq context (.holds first) (.holds second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.holdsCongruence_sound model.toAbstract context first second
      termsInterpreted.toAbstract)

theorem imageCongruence_sound (context : ContextExpr S n) (first second : TypeExpr S n)
    (typesInterpreted : Interprets model (.typeEq context first second)) :
    Interprets model (.predicateEq context (.image first) (.image second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.imageCongruence_sound model.toAbstract context first second
      typesInterpreted.toAbstract)

theorem conjunctionCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.and first third) (.and second fourth)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.conjunctionCongruence_sound model.toAbstract context first second third fourth
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem disjunctionCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.or first third) (.or second fourth)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.disjunctionCongruence_sound model.toAbstract context first second third fourth
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem implicationCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.implies first third) (.implies second fourth)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.implicationCongruence_sound model.toAbstract context first second third fourth
      firstInterpreted.toAbstract secondInterpreted.toAbstract)

theorem universalCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.predicateEq context (.all firstDomain firstPredicate) (.all secondDomain secondPredicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.universalCongruence_sound model.toAbstract context firstDomain secondDomain
      firstPredicate secondPredicate domainsInterpreted.toAbstract predicatesInterpreted.toAbstract)

theorem existentialCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.predicateEq context (.exists firstDomain firstPredicate) (.exists secondDomain secondPredicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.existentialCongruence_sound model.toAbstract context firstDomain secondDomain
      firstPredicate secondPredicate domainsInterpreted.toAbstract predicatesInterpreted.toAbstract)

theorem comprehensionCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.typeEq context (.comprehension firstDomain firstPredicate)
      (.comprehension secondDomain secondPredicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionCongruence_sound model.toAbstract context firstDomain secondDomain
      firstPredicate secondPredicate domainsInterpreted.toAbstract predicatesInterpreted.toAbstract)

theorem comprehensionElimination_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.term context (.forget domain predicate term) domain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionElimination_sound model.toAbstract context domain predicate term
      domainInterpreted.toAbstract predicateInterpreted.toAbstract termInterpreted.toAbstract)

theorem comprehensionEta_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.termEq context (.refine domain predicate (.forget domain predicate term))
      term (.comprehension domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionEta_sound model.toAbstract context domain predicate term
      domainInterpreted.toAbstract predicateInterpreted.toAbstract termInterpreted.toAbstract)

theorem forgetCongruence_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (first second : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termsInterpreted : Interprets model (.termEq context first second (.comprehension domain predicate))) :
    Interprets model (.termEq context (.forget domain predicate first) (.forget domain predicate second) domain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.forgetCongruence_sound model.toAbstract context domain predicate first second
      domainInterpreted.toAbstract predicateInterpreted.toAbstract termsInterpreted.toAbstract)

theorem forgetAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstPredicate secondPredicate : PropExpr S (n + 1))
    (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate))
    (termsInterpreted : Interprets model (.termEq context first second (.comprehension firstDomain firstPredicate))) :
    Interprets model (.termEq context (.forget firstDomain firstPredicate first)
      (.forget secondDomain secondPredicate second) firstDomain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.forgetAnnotationCongruence_sound model.toAbstract context firstDomain secondDomain
      firstPredicate secondPredicate first second domainsInterpreted.toAbstract
      predicatesInterpreted.toAbstract termsInterpreted.toAbstract)

theorem suppliedGuard_membership (Γ : Scope C n) (A : NativeType Γ.1)
    (φ : Subfunctor (Γ.snoc A).1) (value : A.decoded.sections)
    (guard : φ.preimage (selfExtend (NativeModel C).toCwf value) = ⊤) :
    ∀ world (base : Γ.1.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ φ.obj world := by
  change φ.preimage (sectionLift A.decoded value) = ⊤ at guard
  intro world base
  have member : base ∈ (φ.preimage (sectionLift A.decoded value)).obj world := guard.symm ▸ trivial
  exact member

theorem suppliedGuard_truth (Γ : Scope C n) (A : NativeType Γ.1)
    (φ : Subfunctor (Γ.snoc A).1) (value : A.decoded.sections)
    (guard : ∀ world (base : Γ.1.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ φ.obj world) :
    φ.preimage (selfExtend (NativeModel C).toCwf value) = ⊤ := by
  change φ.preimage (sectionLift A.decoded value) = ⊤
  ext world base
  constructor
  · intro _
    trivial
  · intro _
    exact guard world base

theorem comprehensionIntroduction_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.term context (.refine domain predicate term) (.comprehension domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionIntroduction_sound model.toAbstract (model.stable_toAbstract stable)
      context domain predicate term domainInterpreted.toAbstract predicateInterpreted.toAbstract
      termInterpreted.toAbstract guardInterpreted.toAbstract)

theorem comprehensionBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.termEq context (.forget domain predicate (.refine domain predicate term)) term domain) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionBeta_sound model.toAbstract (model.stable_toAbstract stable) context
      domain predicate term domainInterpreted.toAbstract predicateInterpreted.toAbstract
      termInterpreted.toAbstract guardInterpreted.toAbstract)

theorem comprehensionGuard_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.entails context
      (predicate.substitute (instantiate (.forget domain predicate term)))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.comprehensionGuard_sound model.toAbstract (model.stable_toAbstract stable) context
      domain predicate term domainInterpreted.toAbstract predicateInterpreted.toAbstract
      termInterpreted.toAbstract)

theorem refineCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termsInterpreted : Interprets model (.termEq context first second domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate first)))) :
    Interprets model (.termEq context (.refine domain predicate first) (.refine domain predicate second)
      (.comprehension domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.refineCongruence_sound model.toAbstract (model.stable_toAbstract stable) context
      domain predicate first second domainInterpreted.toAbstract predicateInterpreted.toAbstract
      termsInterpreted.toAbstract guardInterpreted.toAbstract)

theorem refineAnnotationCongruence_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1)) (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model
      (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate))
    (termsInterpreted : Interprets model (.termEq context first second firstDomain))
    (guardInterpreted : Interprets model (.entails context (firstPredicate.substitute (instantiate first)))) :
    Interprets model (.termEq context (.refine firstDomain firstPredicate first)
      (.refine secondDomain secondPredicate second) (.comprehension firstDomain firstPredicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.refineAnnotationCongruence_sound model.toAbstract (model.stable_toAbstract stable)
      context firstDomain secondDomain firstPredicate secondPredicate first second
      domainsInterpreted.toAbstract predicatesInterpreted.toAbstract termsInterpreted.toAbstract
      guardInterpreted.toAbstract)

theorem universalElimination_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (universalInterpreted : Interprets model (.entails context (.all domain predicate)))
    (termInterpreted : Interprets model (.term context term domain)) :
    Interprets model (.entails context (predicate.substitute (instantiate term))) :=
  model.interprets_of_abstract
    (Abstract.ModelData.universalElimination_sound model.toAbstract (model.stable_toAbstract stable)
      context domain predicate term domainInterpreted.toAbstract predicateInterpreted.toAbstract
      universalInterpreted.toAbstract termInterpreted.toAbstract)

theorem existentialIntroduction_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.entails context (.exists domain predicate)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.existentialIntroduction_sound model.toAbstract (model.stable_toAbstract stable)
      context domain predicate term domainInterpreted.toAbstract predicateInterpreted.toAbstract
      termInterpreted.toAbstract guardInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
