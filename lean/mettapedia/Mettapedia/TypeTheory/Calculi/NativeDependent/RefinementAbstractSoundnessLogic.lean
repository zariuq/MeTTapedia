import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessFormation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPredicateCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSubstitutionReadout
import Mettapedia.TypeTheory.ContextualPredicateLogic

/-!
# Proposition and refinement rules in local predicate models

Formation uses the model predicates. Quote and holds read the ordinary
proposition type in both directions. Refine preserves its supplied
inhabitant only when the actual predicate holds throughout the satisfying
context; forgetting and its computation laws retain that complete inhabitant.
Proof-tree identity is separate from these semantic value equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open External (bindResult)
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPredicateLogic

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C} {D : Signature S}

namespace ModelData

variable (model : ModelData S C localModel) {n : Nat}

theorem evaluate_refine (Γ : ModelScope C localModel n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n) (A : C.toCwf.Ty Γ.1)
    (φ : localModel.doctrine.Predicate (C.toCwf.ext Γ.1 A)) (value : C.toCwf.Tm Γ.1 A)
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ)
    (termRead : model.evaluateTerm Γ term = some ⟨A, value⟩)
    (guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤) :
    model.evaluateTerm Γ (.refine domain predicate term) =
      some ⟨localModel.refinements.refined A φ, localModel.refinements.intro A φ value guard⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => refine? localModel A φ (model.evaluateTerm Γ term))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  change refine? localModel A φ (model.evaluateTerm Γ term) = _
  rw [termRead]
  exact refine?_supplied A φ value guard

theorem evaluate_forget (Γ : ModelScope C localModel n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n) (A : C.toCwf.Ty Γ.1)
    (φ : localModel.doctrine.Predicate (C.toCwf.ext Γ.1 A))
    (value : C.toCwf.Tm Γ.1 (localModel.refinements.refined A φ))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ)
    (termRead : model.evaluateTerm Γ term = some ⟨localModel.refinements.refined A φ, value⟩) :
    model.evaluateTerm Γ (.forget domain predicate term) =
      some ⟨A, localModel.refinements.forget A φ value⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => forget? localModel A φ (model.evaluateTerm Γ term))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  change forget? localModel A φ (model.evaluateTerm Γ term) = _
  rw [termRead]
  exact forget?_supplied A φ value

theorem predicatePrimitive_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (arguments : Substitution S (S.predicateArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.predicateParameters symbol) arguments)) :
    Interprets model (.predicate context (.atom symbol arguments)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases argumentsInterpreted.substitutionAt Γ (model.predicateParameters symbol)
    contextRead (realization.predicateHeader symbol) with ⟨σ, argumentsRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_predicateAtom Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)⟩

theorem truthFormation_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.predicate context .truth) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, ⊤, contextRead, rfl⟩

theorem falsehoodFormation_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.predicate context .falsehood) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, ⊥, contextRead, rfl⟩

theorem conjunctionFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.and first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_and Γ first second φ ψ firstRead secondRead⟩

theorem disjunctionFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.or first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_or Γ first second φ ψ firstRead secondRead⟩

theorem implicationFormation_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second)) :
    Interprets model (.predicate context (.implies first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_implies Γ first second φ ψ firstRead secondRead⟩

theorem universalFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.predicate context (.all domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_all Γ domain predicate A φ domainRead predicateRead⟩

theorem existentialFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.predicate context (.exists domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_exists Γ domain predicate A φ domainRead predicateRead⟩

theorem quote_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.term context (.quote predicate) .propositions) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  exact ⟨Γ, _, localModel.propositions.quote φ, contextRead, rfl, model.evaluate_quote Γ predicate φ predicateRead⟩

theorem holdsFormation_sound (context : ContextExpr S n) (term : TermExpr S n)
    (termInterpreted : Interprets model (.term context term .propositions)) :
    Interprets model (.predicate context (.holds term)) := by
  rcases termInterpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
  have same : localModel.propositions.omega Γ.1 = A := Option.some.inj typeRead
  cases same
  exact ⟨Γ, localModel.propositions.holds value, contextRead, model.evaluate_holds Γ term value termRead⟩

theorem imageFormation_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (typeInterpreted : Interprets model (.type context type)) :
    Interprets model (.predicate context (.image type)) := by
  rcases typeInterpreted with ⟨Γ, A, contextRead, typeRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_image Γ type A typeRead⟩

theorem holdsQuote_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.predicateEq context (.holds (.quote predicate)) predicate) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  refine ⟨Γ, φ, contextRead, ?_, predicateRead⟩
  rw [model.evaluate_holds Γ (.quote predicate) (localModel.propositions.quote φ)
    (model.evaluate_quote Γ predicate φ predicateRead), localModel.propositions.holds_quote]

theorem quoteHolds_sound (context : ContextExpr S n) (term : TermExpr S n)
    (termInterpreted : Interprets model (.term context term .propositions)) :
    Interprets model (.termEq context (.quote (.holds term)) term .propositions) := by
  rcases termInterpreted with ⟨Γ, A, value, contextRead, typeRead, termRead⟩
  have same : localModel.propositions.omega Γ.1 = A := Option.some.inj typeRead
  cases same
  refine ⟨Γ, _, value, contextRead, rfl, ?_, termRead⟩
  rw [model.evaluate_quote Γ (.holds term) (localModel.propositions.holds value)
    (model.evaluate_holds Γ term value termRead), localModel.propositions.quote_holds]

theorem truthIntroduction_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.entails context .truth) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, contextRead, rfl⟩

theorem falsehoodElimination_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate))
    (falseInterpreted : Interprets model (.entails context .falsehood)) :
    Interprets model (.entails context predicate) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  have equality : (⊥ : localModel.doctrine.Predicate Γ.1) = ⊤ := Option.some.inj (falseInterpreted.entailsAt Γ contextRead)
  have topBelow : (⊤ : localModel.doctrine.Predicate Γ.1) ≤ φ := equality ▸ bot_le
  exact ⟨Γ, contextRead, predicateRead.trans (congrArg some (le_antisymm le_top topBelow))⟩

theorem conjunctionIntroduction_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.entails context first))
    (secondInterpreted : Interprets model (.entails context second)) :
    Interprets model (.entails context (.and first second)) := by
  rcases firstInterpreted with ⟨Γ, contextRead, firstRead⟩
  exact ⟨Γ, contextRead, by
    rw [model.evaluate_and Γ first second ⊤ ⊤ firstRead
      (secondInterpreted.entailsAt Γ contextRead), inf_idem]⟩

theorem conjunctionFirst_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (togetherInterpreted : Interprets model (.entails context (.and first second))) :
    Interprets model (.entails context first) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have together : φ ⊓ ψ = ⊤ := Option.some.inj
    ((model.evaluate_and Γ first second φ ψ firstRead secondRead).symm.trans
      (togetherInterpreted.entailsAt Γ contextRead))
  have above : (⊤ : localModel.doctrine.Predicate Γ.1) ≤ φ := by
    rw [← together]
    exact inf_le_left
  exact ⟨Γ, contextRead, firstRead.trans (congrArg some (le_antisymm le_top above))⟩

theorem conjunctionSecond_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (togetherInterpreted : Interprets model (.entails context (.and first second))) :
    Interprets model (.entails context second) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have together : φ ⊓ ψ = ⊤ := Option.some.inj
    ((model.evaluate_and Γ first second φ ψ firstRead secondRead).symm.trans
      (togetherInterpreted.entailsAt Γ contextRead))
  have above : (⊤ : localModel.doctrine.Predicate Γ.1) ≤ ψ := by
    rw [← together]
    exact inf_le_right
  exact ⟨Γ, contextRead, secondRead.trans (congrArg some (le_antisymm le_top above))⟩

theorem disjunctionFirst_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context (.or first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have held : φ = ⊤ := Option.some.inj
    (firstRead.symm.trans (heldInterpreted.entailsAt Γ contextRead))
  refine ⟨Γ, contextRead, ?_⟩
  rw [model.evaluate_or Γ first second φ ψ firstRead secondRead, held]
  simp only [top_sup_eq]

theorem disjunctionSecond_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (heldInterpreted : Interprets model (.entails context second)) :
    Interprets model (.entails context (.or first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have held : ψ = ⊤ := Option.some.inj
    (secondRead.symm.trans (heldInterpreted.entailsAt Γ contextRead))
  refine ⟨Γ, contextRead, ?_⟩
  rw [model.evaluate_or Γ first second φ ψ firstRead secondRead, held]
  simp only [sup_top_eq]

theorem implicationElimination_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (implicationInterpreted : Interprets model (.entails context (.implies first second)))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context second) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have antecedent : φ = ⊤ := Option.some.inj
    (firstRead.symm.trans (heldInterpreted.entailsAt Γ contextRead))
  have implication : φ ⇨ ψ = ⊤ := Option.some.inj
    ((model.evaluate_implies Γ first second φ ψ firstRead secondRead).symm.trans
      (implicationInterpreted.entailsAt Γ contextRead))
  have consequent : ψ = ⊤ := by
    simpa only [antecedent, top_himp] using implication
  exact ⟨Γ, contextRead, secondRead.trans (congrArg some consequent)⟩

theorem transportPredicate_sound (first second : ContextExpr S n) (predicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicateInterpreted : Interprets model (.predicate first predicate)) :
    Interprets model (.predicate second predicate) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  exact ⟨Γ, φ, contextsInterpreted.contextEqAt Γ contextRead, predicateRead⟩

theorem transportEntailment_sound (first second : ContextExpr S n) (predicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicateInterpreted : Interprets model (.entails first predicate)) :
    Interprets model (.entails second predicate) := by
  rcases predicateInterpreted with ⟨Γ, contextRead, predicateRead⟩
  exact ⟨Γ, contextsInterpreted.contextEqAt Γ contextRead, predicateRead⟩

theorem predicatePrimitiveCongruence_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.PredicateSymbol)
    (first second : Substitution S (S.predicateArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitutionEq context (D.predicateParameters symbol) first second)) :
    Interprets model (.predicateEq context (.atom symbol first) (.atom symbol second)) := by
  rcases argumentsInterpreted with ⟨Γ, Δ, σ, contextRead, headerRead, firstRead, secondRead⟩
  cases Option.some.inj (headerRead.symm.trans (realization.predicateHeader symbol))
  exact ⟨Γ, _, contextRead,
    model.evaluate_predicateAtom Γ symbol first σ
      ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead),
    model.evaluate_predicateAtom Γ symbol second σ
      ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead)⟩

theorem universalIntroduction_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (heldInterpreted : Interprets model (.entails (.snoc context domain) predicate)) :
    Interprets model (.entails context (.all domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  have extendedRead := model.evaluateContext_snoc context domain Γ A contextRead domainRead
  rcases predicateInterpreted.predicateAt (Γ.snoc A) extendedRead with ⟨φ, predicateRead⟩
  have held : φ = ⊤ := Option.some.inj
    (predicateRead.symm.trans (heldInterpreted.entailsAt (Γ.snoc A) extendedRead))
  refine ⟨Γ, contextRead, ?_⟩
  rw [model.evaluate_all Γ domain predicate A φ domainRead predicateRead, held]
  exact congrArg some (universal_top localModel.doctrine A)

theorem imageIntroduction_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (term : TermExpr S n) (typeInterpreted : Interprets model (.type context type))
    (termInterpreted : Interprets model (.term context term type)) :
    Interprets model (.entails context (.image type)) := by
  rcases typeInterpreted with ⟨Γ, A, contextRead, typeRead⟩
  rcases termInterpreted.termAt Γ A contextRead typeRead with ⟨value, _termRead⟩
  have support := image_section localModel.doctrine A value
  exact ⟨Γ, contextRead, (model.evaluate_image Γ type A typeRead).trans (congrArg some support)⟩

theorem predicateReflexivity_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.predicateEq context predicate predicate) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  exact ⟨Γ, φ, contextRead, predicateRead, predicateRead⟩

theorem predicateSymmetry_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second)) :
    Interprets model (.predicateEq context second first) := by
  rcases predicatesInterpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
  exact ⟨Γ, φ, contextRead, secondRead, firstRead⟩

theorem predicateTransitivity_sound (context : ContextExpr S n) (first middle last : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first middle))
    (secondInterpreted : Interprets model (.predicateEq context middle last)) :
    Interprets model (.predicateEq context first last) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead, middleRead⟩
  exact ⟨Γ, φ, contextRead, firstRead, secondInterpreted.predicateEqAt Γ φ contextRead middleRead⟩

theorem entailmentConversion_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second))
    (heldInterpreted : Interprets model (.entails context first)) :
    Interprets model (.entails context second) := by
  rcases heldInterpreted with ⟨Γ, contextRead, firstRead⟩
  exact ⟨Γ, contextRead, predicatesInterpreted.predicateEqAt Γ ⊤ contextRead firstRead⟩

theorem contextAssumeEquality_sound (first second : ContextExpr S n)
    (firstPredicate secondPredicate : PropExpr S n)
    (contextsInterpreted : Interprets model (.contextEq first second))
    (predicatesInterpreted : Interprets model (.predicateEq first firstPredicate secondPredicate)) :
    Interprets model (.contextEq (.assume first firstPredicate) (.assume second secondPredicate)) := by
  rcases contextsInterpreted with ⟨Γ, firstContextRead, secondContextRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans firstContextRead)
  exact ⟨Γ.assume φ, model.evaluateContext_assume first firstPredicate Γ φ firstContextRead firstRead,
    model.evaluateContext_assume second secondPredicate Γ φ secondContextRead secondRead⟩

theorem quoteCongruence_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (predicatesInterpreted : Interprets model (.predicateEq context first second)) :
    Interprets model (.termEq context (.quote first) (.quote second) .propositions) := by
  rcases predicatesInterpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
  exact ⟨Γ, _, localModel.propositions.quote φ, contextRead, rfl,
    model.evaluate_quote Γ first φ firstRead, model.evaluate_quote Γ second φ secondRead⟩

theorem holdsCongruence_sound (context : ContextExpr S n) (first second : TermExpr S n)
    (termsInterpreted : Interprets model (.termEq context first second .propositions)) :
    Interprets model (.predicateEq context (.holds first) (.holds second)) := by
  rcases termsInterpreted with ⟨Γ, A, value, contextRead, typeRead, firstRead, secondRead⟩
  have same : localModel.propositions.omega Γ.1 = A := Option.some.inj typeRead
  cases same
  exact ⟨Γ, localModel.propositions.holds value, contextRead,
    model.evaluate_holds Γ first value firstRead, model.evaluate_holds Γ second value secondRead⟩

theorem imageCongruence_sound (context : ContextExpr S n) (first second : TypeExpr S n)
    (typesInterpreted : Interprets model (.typeEq context first second)) :
    Interprets model (.predicateEq context (.image first) (.image second)) := by
  rcases typesInterpreted with ⟨Γ, A, contextRead, firstRead, secondRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_image Γ first A firstRead, model.evaluate_image Γ second A secondRead⟩

theorem conjunctionCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.and first third) (.and second fourth)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
  rcases secondInterpreted with ⟨actual, ψ, actualRead, thirdRead, fourthRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  exact ⟨Γ, _, contextRead, model.evaluate_and Γ first third φ ψ firstRead thirdRead,
    model.evaluate_and Γ second fourth φ ψ secondRead fourthRead⟩

theorem disjunctionCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.or first third) (.or second fourth)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
  rcases secondInterpreted with ⟨actual, ψ, actualRead, thirdRead, fourthRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  exact ⟨Γ, _, contextRead, model.evaluate_or Γ first third φ ψ firstRead thirdRead,
    model.evaluate_or Γ second fourth φ ψ secondRead fourthRead⟩

theorem implicationCongruence_sound (context : ContextExpr S n) (first second third fourth : PropExpr S n)
    (firstInterpreted : Interprets model (.predicateEq context first second))
    (secondInterpreted : Interprets model (.predicateEq context third fourth)) :
    Interprets model (.predicateEq context (.implies first third) (.implies second fourth)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead, secondRead⟩
  rcases secondInterpreted with ⟨actual, ψ, actualRead, thirdRead, fourthRead⟩
  cases Option.some.inj (actualRead.symm.trans contextRead)
  exact ⟨Γ, _, contextRead, model.evaluate_implies Γ first third φ ψ firstRead thirdRead,
    model.evaluate_implies Γ second fourth φ ψ secondRead fourthRead⟩

theorem universalCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.predicateEq context (.all firstDomain firstPredicate) (.all secondDomain secondPredicate)) := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  exact ⟨Γ, _, contextRead,
    model.evaluate_all Γ firstDomain firstPredicate A φ firstDomainRead firstRead,
    model.evaluate_all Γ secondDomain secondPredicate A φ secondDomainRead secondRead⟩

theorem existentialCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.predicateEq context (.exists firstDomain firstPredicate) (.exists secondDomain secondPredicate)) := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  exact ⟨Γ, _, contextRead,
    model.evaluate_exists Γ firstDomain firstPredicate A φ firstDomainRead firstRead,
    model.evaluate_exists Γ secondDomain secondPredicate A φ secondDomainRead secondRead⟩

theorem comprehensionCongruence_sound (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1))
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate)) :
    Interprets model (.typeEq context (.comprehension firstDomain firstPredicate)
      (.comprehension secondDomain secondPredicate)) := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  exact ⟨Γ, _, contextRead,
    model.evaluate_comprehension Γ firstDomain firstPredicate A φ firstDomainRead firstRead,
    model.evaluate_comprehension Γ secondDomain secondPredicate A φ secondDomainRead secondRead⟩

theorem comprehensionElimination_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.term context (.forget domain predicate term) domain) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ (localModel.refinements.refined A φ) contextRead
    (model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead) with ⟨value, termRead⟩
  exact ⟨Γ, A, localModel.refinements.forget A φ value, contextRead, domainRead,
    model.evaluate_forget Γ domain predicate term A φ value domainRead predicateRead termRead⟩

theorem comprehensionEta_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (term : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.termEq context (.refine domain predicate (.forget domain predicate term))
      term (.comprehension domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  have refinementRead := model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead
  rcases termInterpreted.termAt Γ (localModel.refinements.refined A φ) contextRead
    refinementRead with ⟨value, termRead⟩
  refine ⟨Γ, _, value, contextRead, refinementRead, ?_, termRead⟩
  have actual := model.evaluate_refine Γ domain predicate (.forget domain predicate term) A φ
    (localModel.refinements.forget A φ value) domainRead predicateRead
    (model.evaluate_forget Γ domain predicate term A φ value domainRead predicateRead termRead)
    (localModel.refinements.forget_guard A φ value)
  exact actual.trans (congrArg
    (fun returned => some (⟨localModel.refinements.refined A φ, returned⟩ : Value C.toCwf Γ.1))
      (localModel.refinements.eta A φ value))

theorem forgetCongruence_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (first second : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termsInterpreted : Interprets model (.termEq context first second (.comprehension domain predicate))) :
    Interprets model (.termEq context (.forget domain predicate first) (.forget domain predicate second) domain) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termsInterpreted.termEqAt Γ (localModel.refinements.refined A φ) contextRead
    (model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead) with ⟨value, firstRead, secondRead⟩
  exact ⟨Γ, A, localModel.refinements.forget A φ value, contextRead, domainRead,
    model.evaluate_forget Γ domain predicate first A φ value domainRead predicateRead firstRead,
    model.evaluate_forget Γ domain predicate second A φ value domainRead predicateRead secondRead⟩

theorem forgetAnnotationCongruence_sound (context : ContextExpr S n)
    (firstDomain secondDomain : TypeExpr S n) (firstPredicate secondPredicate : PropExpr S (n + 1))
    (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate))
    (termsInterpreted : Interprets model (.termEq context first second (.comprehension firstDomain firstPredicate))) :
    Interprets model (.termEq context (.forget firstDomain firstPredicate first)
      (.forget secondDomain secondPredicate second) firstDomain) := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstPredicateRead, secondPredicateRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  rcases termsInterpreted.termEqAt Γ (localModel.refinements.refined A φ) contextRead
    (model.evaluate_comprehension Γ firstDomain firstPredicate A φ firstDomainRead firstPredicateRead)
    with ⟨value, firstRead, secondRead⟩
  exact ⟨Γ, A, localModel.refinements.forget A φ value, contextRead, firstDomainRead,
    model.evaluate_forget Γ firstDomain firstPredicate first A φ value firstDomainRead firstPredicateRead firstRead,
    model.evaluate_forget Γ secondDomain secondPredicate second A φ value secondDomainRead secondPredicateRead secondRead⟩

theorem comprehensionIntroduction_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.term context (.refine domain predicate term) (.comprehension domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ A contextRead domainRead with ⟨value, termRead⟩
  have guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤ := Option.some.inj
    ((model.evaluatePredicate_instantiate stable Γ A predicate φ term value predicateRead termRead).symm.trans
      (guardInterpreted.entailsAt Γ contextRead))
  have satisfies := guard
  exact ⟨Γ, _, localModel.refinements.intro A φ value satisfies, contextRead,
    model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead,
    model.evaluate_refine Γ domain predicate term A φ value domainRead predicateRead termRead satisfies⟩

theorem comprehensionBeta_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.termEq context (.forget domain predicate (.refine domain predicate term)) term domain) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ A contextRead domainRead with ⟨value, termRead⟩
  have guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤ := Option.some.inj
    ((model.evaluatePredicate_instantiate stable Γ A predicate φ term value predicateRead termRead).symm.trans
      (guardInterpreted.entailsAt Γ contextRead))
  have satisfies := guard
  have introduced := model.evaluate_refine Γ domain predicate term A φ value
    domainRead predicateRead termRead satisfies
  have forgotten := model.evaluate_forget Γ domain predicate (.refine domain predicate term) A φ
    (localModel.refinements.intro A φ value satisfies) domainRead predicateRead introduced
  exact ⟨Γ, A, value, contextRead, domainRead,
    forgotten.trans (congrArg (fun returned => some (⟨A, returned⟩ : Value C.toCwf Γ.1))
      (localModel.refinements.beta A φ value satisfies)), termRead⟩

theorem comprehensionGuard_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term (.comprehension domain predicate))) :
    Interprets model (.entails context
      (predicate.substitute (instantiate (.forget domain predicate term)))) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ (localModel.refinements.refined A φ) contextRead
    (model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead) with ⟨value, termRead⟩
  have forgotten := model.evaluate_forget Γ domain predicate term A φ value
    domainRead predicateRead termRead
  exact ⟨Γ, contextRead,
    (model.evaluatePredicate_instantiate stable Γ A predicate φ (.forget domain predicate term)
      (localModel.refinements.forget A φ value) predicateRead forgotten).trans
        (congrArg some (localModel.refinements.forget_guard A φ value))⟩

theorem refineCongruence_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termsInterpreted : Interprets model (.termEq context first second domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate first)))) :
    Interprets model (.termEq context (.refine domain predicate first) (.refine domain predicate second)
      (.comprehension domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termsInterpreted.termEqAt Γ A contextRead domainRead with ⟨value, firstRead, secondRead⟩
  have guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤ := Option.some.inj
    ((model.evaluatePredicate_instantiate stable Γ A predicate φ first value predicateRead firstRead).symm.trans
      (guardInterpreted.entailsAt Γ contextRead))
  have satisfies := guard
  exact ⟨Γ, _, localModel.refinements.intro A φ value satisfies, contextRead,
    model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead,
    model.evaluate_refine Γ domain predicate first A φ value domainRead predicateRead firstRead satisfies,
    model.evaluate_refine Γ domain predicate second A φ value domainRead predicateRead secondRead satisfies⟩

theorem refineAnnotationCongruence_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (firstDomain secondDomain : TypeExpr S n)
    (firstPredicate secondPredicate : PropExpr S (n + 1)) (first second : TermExpr S n)
    (domainsInterpreted : Interprets model (.typeEq context firstDomain secondDomain))
    (predicatesInterpreted : Interprets model
      (.predicateEq (.snoc context firstDomain) firstPredicate secondPredicate))
    (termsInterpreted : Interprets model (.termEq context first second firstDomain))
    (guardInterpreted : Interprets model (.entails context (firstPredicate.substitute (instantiate first)))) :
    Interprets model (.termEq context (.refine firstDomain firstPredicate first)
      (.refine secondDomain secondPredicate second) (.comprehension firstDomain firstPredicate)) := by
  rcases domainsInterpreted with ⟨Γ, A, contextRead, firstDomainRead, secondDomainRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstPredicateRead, secondPredicateRead⟩
  cases Option.some.inj (actualRead.symm.trans
    (model.evaluateContext_snoc context firstDomain Γ A contextRead firstDomainRead))
  rcases termsInterpreted.termEqAt Γ A contextRead firstDomainRead with ⟨value, firstRead, secondRead⟩
  have guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤ := Option.some.inj
    ((model.evaluatePredicate_instantiate stable Γ A firstPredicate φ first value firstPredicateRead firstRead).symm.trans
      (guardInterpreted.entailsAt Γ contextRead))
  have satisfies := guard
  exact ⟨Γ, _, localModel.refinements.intro A φ value satisfies, contextRead,
    model.evaluate_comprehension Γ firstDomain firstPredicate A φ firstDomainRead firstPredicateRead,
    model.evaluate_refine Γ firstDomain firstPredicate first A φ value firstDomainRead firstPredicateRead firstRead satisfies,
    model.evaluate_refine Γ secondDomain secondPredicate second A φ value secondDomainRead secondPredicateRead secondRead satisfies⟩

theorem universalElimination_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (universalInterpreted : Interprets model (.entails context (.all domain predicate)))
    (termInterpreted : Interprets model (.term context term domain)) :
    Interprets model (.entails context (predicate.substitute (instantiate term))) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ A contextRead domainRead with ⟨value, termRead⟩
  have universal : localModel.doctrine.all A φ = ⊤ := Option.some.inj
    ((model.evaluate_all Γ domain predicate A φ domainRead predicateRead).symm.trans
      (universalInterpreted.entailsAt Γ contextRead))
  exact ⟨Γ, contextRead,
    (model.evaluatePredicate_instantiate stable Γ A predicate φ term value predicateRead termRead).trans
      (congrArg some (universal_section localModel.doctrine A φ value universal))⟩

theorem existentialIntroduction_sound (stable : StrictPiSubstitution localModel.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (term : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (termInterpreted : Interprets model (.term context term domain))
    (guardInterpreted : Interprets model (.entails context (predicate.substitute (instantiate term)))) :
    Interprets model (.entails context (.exists domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  rcases termInterpreted.termAt Γ A contextRead domainRead with ⟨value, termRead⟩
  have guard : localModel.doctrine.reindex (selfExtend C.toCwf value) φ = ⊤ := Option.some.inj
    ((model.evaluatePredicate_instantiate stable Γ A predicate φ term value predicateRead termRead).symm.trans
      (guardInterpreted.entailsAt Γ contextRead))
  have covered := existential_section localModel.doctrine A φ value guard
  exact ⟨Γ, contextRead, (model.evaluate_exists Γ domain predicate A φ domainRead predicateRead).trans
    (congrArg some covered)⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
