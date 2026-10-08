import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementConstructorInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSubstitutionEvaluation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingReadout
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPairContextInterpretation

/-!
# Native refinement formation and introduction readouts

Each rule constructs actual interpreted scopes, varying native types or full
supplied sections from its interpreted local premises. Proposition assumptions
select their satisfying context. These local theorems contain no whole-model
soundness or evaluator compatibility field.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory NativeLocalTypeFormers PresheafNativePropositionReadout
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {D : Signature S}

namespace ModelData

variable (model : ModelData S C) {n k : Nat}

theorem contextNil_sound : Interprets model (.context (.nil : ContextExpr S 0)) :=
  ⟨Scope.nil C, rfl⟩

theorem contextExtend_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (contextInterpreted : Interprets model (.context context))
    (typeInterpreted : Interprets model (.type context type)) :
    Interprets model (.context (.snoc context type)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases typeInterpreted.typeAt Γ contextRead with ⟨A, typeRead⟩
  exact ⟨Γ.snoc A, model.evaluateContext_snoc context type Γ A contextRead typeRead⟩

theorem contextAssume_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (contextInterpreted : Interprets model (.context context))
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.context (.assume context predicate)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases predicateInterpreted.predicateAt Γ contextRead with ⟨φ, predicateRead⟩
  exact ⟨Γ.assume φ, model.evaluateContext_assume context predicate Γ φ contextRead predicateRead⟩

theorem propositionType_sound (context : ContextExpr S n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.type context .propositions) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, nativeOmega Γ.1, contextRead, rfl⟩

theorem variable_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (index : Fin n)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.term context (.var index) (context.lookup index)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, (Γ.2.lookup index).1, (Γ.2.lookup index).2, contextRead,
    model.evaluateContext_lookup stable context Γ contextRead index, rfl⟩

theorem family_sound (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TypeSymbol)
    (arguments : Substitution S (S.typeArity symbol) n)
    (contextInterpreted : Interprets model (.context context))
    (argumentsInterpreted : Interprets model (.substitution context (D.typeParameters symbol) arguments)) :
    Interprets model (.type context (.family symbol arguments)) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  rcases argumentsInterpreted.substitutionAt Γ (model.typeParameters symbol)
    contextRead (realization.typeHeader symbol) with ⟨σ, argumentsRead⟩
  exact ⟨Γ, model.familyAt symbol σ, contextRead, model.evaluate_family Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)⟩

theorem primitive_sound (stable : StrictPiSubstitution model.products)
    (realization : SignatureRealization model D)
    (context : ContextExpr S n) (symbol : S.TermSymbol)
    (arguments : Substitution S (S.termArity symbol) n)
    (argumentsInterpreted : Interprets model
      (.substitution context (D.termParameters symbol) arguments)) :
    Interprets model (.term context (.primitive symbol arguments)
      ((D.termResult symbol).substitute arguments)) := by
  rcases argumentsInterpreted with ⟨Γ, Δ, σ, contextRead, headerRead, argumentsRead⟩
  cases Option.some.inj (headerRead.symm.trans (realization.termHeader symbol))
  have resultRead := model.evaluateType_substitute stable (D.termResult symbol)
    Γ (model.termParameters symbol) arguments
      (ModelSubstitution.ofEvaluated model Γ (model.termParameters symbol) arguments σ argumentsRead)
        (model.termType symbol) (realization.termResult symbol)
  refine ⟨Γ, (model.primitiveAt symbol σ).1, (model.primitiveAt symbol σ).2,
    contextRead, resultRead, ?_⟩
  exact model.evaluate_primitive Γ symbol arguments σ
    ((model.evaluateSubstitution_eq_some_iff _ _ _ _).mp argumentsRead)

theorem piFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body)) :
    Interprets model (.type context (.pi domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  exact ⟨Γ, model.products.pi A B, contextRead,
    model.evaluate_pi Γ domain body A B domainRead bodyRead⟩

theorem sigmaFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body)) :
    Interprets model (.type context (.sigma domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  exact ⟨Γ, model.sums.operations.sigma A B, contextRead,
    model.evaluate_sigma Γ domain body A B domainRead bodyRead⟩

theorem lambda_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (term : TermExpr S (n + 1))
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (termInterpreted : Interprets model (.term (.snoc context domain) term body)) :
    Interprets model (.term context (.lam domain body term) (.pi domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases termInterpreted.termAt (Γ.snoc A) B
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) bodyRead with ⟨value, termRead⟩
  exact ⟨Γ, _, model.products.lam value, contextRead,
    model.evaluate_pi Γ domain body A B domainRead bodyRead,
    model.evaluate_lambda Γ domain body A B domainRead bodyRead term value termRead⟩

theorem application_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (function argument : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (functionInterpreted : Interprets model (.term context function (.pi domain body)))
    (argumentInterpreted : Interprets model (.term context argument domain)) :
    Interprets model (.term context (.app domain body function argument)
      (body.substitute (instantiate argument))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases functionInterpreted.termAt Γ (model.products.pi A B) contextRead
    (model.evaluate_pi Γ domain body A B domainRead bodyRead) with ⟨f, functionRead⟩
  rcases argumentInterpreted.termAt Γ A contextRead domainRead with ⟨a, argumentRead⟩
  exact ⟨Γ, _, model.products.app f a, contextRead,
    model.evaluateType_instantiate stable Γ A body B argument a bodyRead argumentRead,
    model.evaluate_application Γ domain body A B domainRead bodyRead function argument f a functionRead argumentRead⟩

theorem pairIntroduction_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.term context (.pair domain body first second) (.sigma domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases firstInterpreted.termAt Γ A contextRead domainRead with ⟨a, firstRead⟩
  rcases secondInterpreted.termAt Γ ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a))
    contextRead (model.evaluateType_instantiate stable Γ A body B first a bodyRead firstRead)
      with ⟨b, secondRead⟩
  exact ⟨Γ, _, model.sums.operations.pair a b, contextRead,
    model.evaluate_sigma Γ domain body A B domainRead bodyRead,
    model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead⟩

theorem firstProjection_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.fst domain body pair) domain) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases pairInterpreted.termAt Γ (model.sums.operations.sigma A B) contextRead
    (model.evaluate_sigma Γ domain body A B domainRead bodyRead) with ⟨p, pairRead⟩
  exact ⟨Γ, A, model.sums.operations.fst p, contextRead, domainRead,
    model.evaluate_first Γ domain body A B domainRead bodyRead pair p pairRead⟩

theorem secondProjection_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (pair : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.snd domain body pair)
      (body.substitute (instantiate (.fst domain body pair)))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases pairInterpreted.termAt Γ (model.sums.operations.sigma A B) contextRead
    (model.evaluate_sigma Γ domain body A B domainRead bodyRead) with ⟨p, pairRead⟩
  exact ⟨Γ, _, model.sums.operations.snd p, contextRead,
    model.evaluateType_instantiate stable Γ A body B (.fst domain body pair)
      (model.sums.operations.fst p) bodyRead
      (model.evaluate_first Γ domain body A B domainRead bodyRead pair p pairRead),
    model.evaluate_second Γ domain body A B domainRead bodyRead pair p pairRead⟩

theorem sigmaElimination_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (branchInterpreted : Interprets model (.term (.snoc (.snoc context domain) body) branch
      (motive.substitute (packSubstitution domain body))))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.term context (.sigmaElim domain body motive branch pair)
      (motive.substitute (instantiate pair))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  have sumRead := model.evaluate_sigma Γ domain body A B domainRead bodyRead
  have sumContextRead := model.evaluateContext_snoc context (.sigma domain body) Γ _ contextRead sumRead
  rcases motiveInterpreted.typeAt (Γ.snoc (model.sums.operations.sigma A B)) sumContextRead with ⟨M, motiveRead⟩
  have tupleContextRead := model.evaluateContext_snoc (.snoc context domain) body (Γ.snoc A) B
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) bodyRead
  have branchTypeRead := model.evaluateType_pack stable Γ domain body motive A B M domainRead bodyRead motiveRead
  rcases branchInterpreted.termAt ((Γ.snoc A).snoc B) _ tupleContextRead branchTypeRead with ⟨b, branchRead⟩
  rcases pairInterpreted.termAt Γ _ contextRead sumRead with ⟨p, pairRead⟩
  exact ⟨Γ, _, (NativeModel C).toCwf.tmSub (eliminate model.sums A B M b)
      (selfExtend (NativeModel C).toCwf p), contextRead,
    model.evaluateType_instantiate stable Γ (model.sums.operations.sigma A B) motive M pair p motiveRead pairRead,
    model.evaluate_sumElimination Γ domain body A B domainRead bodyRead motive branch pair M b p
      motiveRead branchRead pairRead⟩

theorem comprehensionFormation_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1))
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate)) :
    Interprets model (.type context (.comprehension domain predicate)) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  rcases predicateInterpreted.predicateAt (Γ.snoc A)
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) with ⟨φ, predicateRead⟩
  exact ⟨Γ, _, contextRead, model.evaluate_comprehension Γ domain predicate A φ domainRead predicateRead⟩

theorem termConversion_sound (context : ContextExpr S n) (term : TermExpr S n)
    (first second : TypeExpr S n) (termInterpreted : Interprets model (.term context term first))
    (typesInterpreted : Interprets model (.typeEq context first second)) :
    Interprets model (.term context term second) := by
  rcases termInterpreted with ⟨Γ, A, value, contextRead, firstRead, termRead⟩
  exact ⟨Γ, A, value, contextRead, typesInterpreted.typeEqAt Γ A contextRead firstRead, termRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
