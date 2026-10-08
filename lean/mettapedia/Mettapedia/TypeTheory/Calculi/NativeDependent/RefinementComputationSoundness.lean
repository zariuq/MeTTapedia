import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementCongruenceSoundness

/-!
# Computational equations of the independent dependent presentation

Product and sum beta/eta are interpreted using the supplied local operation
equations. Full pair-elimination equations use the actual packing/opening
arrows, whose agreement follows from authored substitution and the earned
model component readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

attribute [local irreducible] products sums TypeOver.extensionSubstitution
  ContextualSumComprehension.normalize ContextualSumComprehension.reindexBody

variable (model : ModelData S C) {n : Nat}

set_option backward.isDefEq.respectTransparency false in
theorem piBeta_sound (stable : StrictPiSubstitution model.products) (beta : PiBeta model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (term : TermExpr S (n + 1)) (argument : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (termInterpreted : Interprets model (.term (.snoc context domain) term body))
    (argumentInterpreted : Interprets model (.term context argument domain)) :
    Interprets model (.termEq context (.app domain body (.lam domain body term) argument)
      (term.substitute (instantiate argument)) (body.substitute (instantiate argument))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases termInterpreted.termAt (Γ.snoc A) B
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) bodyRead with ⟨value, termRead⟩
  rcases argumentInterpreted.termAt Γ A contextRead domainRead with ⟨a, argumentRead⟩
  exact ⟨Γ, _, (NativeModel C).toCwf.tmSub value (selfExtend (NativeModel C).toCwf a), contextRead,
    model.evaluateType_instantiate stable Γ A body B argument a bodyRead argumentRead,
    model.evaluated_lambda_beta Γ domain body A B domainRead bodyRead beta term argument value a termRead argumentRead,
    model.evaluateTerm_instantiate stable Γ A term ⟨B, value⟩ argument a termRead argumentRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem piEta_sound (stable : StrictPiSubstitution model.products)
    (eta : PiEta model.products stable.1)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (function : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (functionInterpreted : Interprets model (.term context function (.pi domain body))) :
    Interprets model (.termEq context (.lam domain body (.app (domain.rename Fin.succ)
      (body.rename (liftRenaming Fin.succ)) (function.rename Fin.succ) (.var 0))) function (.pi domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  have productRead := model.evaluate_pi Γ domain body A B domainRead bodyRead
  rcases functionInterpreted.termAt Γ _ contextRead productRead with ⟨f, functionRead⟩
  let weaken := ModelRenaming.weaken Γ A
  have weakDomain := model.evaluateType_rename stable domain (Γ.snoc A) Γ Fin.succ weaken A domainRead
  have weakBody := model.evaluateType_rename stable body
    ((Γ.snoc A).snoc ((NativeModel C).toCwf.tySub A ((NativeModel C).toCwf.wk A))) (Γ.snoc A)
    (liftRenaming Fin.succ) (weaken.lift A) B bodyRead
  have weakFunction := model.evaluateTerm_rename stable function (Γ.snoc A) Γ Fin.succ weaken _ functionRead
  rw [model.product_value_substitute stable] at weakFunction
  have applicationRead := model.evaluate_application (Γ.snoc A) (domain.rename Fin.succ)
    (body.rename (liftRenaming Fin.succ)) ((NativeModel C).toCwf.tySub A ((NativeModel C).toCwf.wk A))
    ((NativeModel C).toCwf.tySub B (TypeOver.extensionSubstitution (C := (NativeModel C).toCwf) ((NativeModel C).toCwf.wk A) A)) weakDomain weakBody
    (function.rename Fin.succ) (.var 0) (reindexFunction model.products stable.1 ((NativeModel C).toCwf.wk A) f)
    ((NativeModel C).toCwf.vz A) weakFunction rfl
  have applicationValue : model.evaluateTerm (Γ.snoc A)
      (.app (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ))
        (function.rename Fin.succ) (.var 0)) = some ⟨B, genericSection model.products stable.1 f⟩ := by
    rw [applicationRead]
    exact congrArg some (Sigma.ext
      (generic_result_type (C := (NativeModel C).toCwf) A B)
      (genericSection_heq model.products stable.1 f).symm)
  have lambdaRead := model.evaluate_lambda Γ domain body A B domainRead bodyRead _
    (genericSection model.products stable.1 f) applicationValue
  rw [eta] at lambdaRead
  exact ⟨Γ, _, f, contextRead, productRead, lambdaRead, functionRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaFirstBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.fst domain body (.pair domain body first second)) first domain) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases firstInterpreted.termAt Γ A contextRead domainRead with ⟨a, firstRead⟩
  rcases secondInterpreted.termAt Γ _ contextRead
    (model.evaluateType_instantiate stable Γ A body B first a bodyRead firstRead) with ⟨b, secondRead⟩
  have pairRead := model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead
  have projection := model.evaluate_first Γ domain body A B domainRead bodyRead
    (.pair domain body first second) (model.sums.operations.pair a b) pairRead
  rw [model.sums.beta.1] at projection
  exact ⟨Γ, A, a, contextRead, domainRead, projection, firstRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaSecondBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (first second : TermExpr S n) (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.snd domain body (.pair domain body first second)) second
      (body.substitute (instantiate first))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  rcases firstInterpreted.termAt Γ A contextRead domainRead with ⟨a, firstRead⟩
  have resultTypeRead := model.evaluateType_instantiate stable Γ A body B first a bodyRead firstRead
  rcases secondInterpreted.termAt Γ _ contextRead resultTypeRead with ⟨b, secondRead⟩
  have pairRead := model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead
  have projection := model.evaluate_second Γ domain body A B domainRead bodyRead
    (.pair domain body first second) (model.sums.operations.pair a b) pairRead
  have projectedValue : (⟨_, model.sums.operations.snd (model.sums.operations.pair a b)⟩ : Value (NativeModel C).toCwf Γ.1) =
      ⟨_, b⟩ := Sigma.ext (congrArg (fun first => (NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf first))
        (model.sums.beta.1 a b)) (model.sums.beta.2 a b)
  rw [projectedValue] at projection
  exact ⟨Γ, _, b, contextRead, resultTypeRead, projection, secondRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaEta_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (body : TypeExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.termEq context (.pair domain body (.fst domain body pair) (.snd domain body pair))
      pair (.sigma domain body)) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  have sumRead := model.evaluate_sigma Γ domain body A B domainRead bodyRead
  rcases pairInterpreted.termAt Γ _ contextRead sumRead with ⟨p, pairRead⟩
  have reconstructed := model.evaluate_pair Γ domain body A B domainRead bodyRead
    (.fst domain body pair) (.snd domain body pair) (model.sums.operations.fst p) (model.sums.operations.snd p)
    (model.evaluate_first Γ domain body A B domainRead bodyRead pair p pairRead)
    (model.evaluate_second Γ domain body A B domainRead bodyRead pair p pairRead)
  rw [model.sums.eta] at reconstructed
  exact ⟨Γ, _, p, contextRead, sumRead, reconstructed, pairRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem pack_openComponents (stable : StrictPiSubstitution model.products)
    (Γ : Scope C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
    (first second : TermExpr S n) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (b : (NativeModel C).toCwf.Tm Γ.1 ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a)))
    (domainRead : model.evaluateType Γ domain = some A)
    (bodyRead : model.evaluateType (Γ.snoc A) body = some B)
    (firstRead : model.evaluateTerm Γ first = some ⟨A, a⟩)
    (secondRead : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    (NativeModel C).toCwf.compS (pack model.sums A B) ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b) =
      selfExtend (NativeModel C).toCwf (model.sums.operations.pair a b) := by
  let packMap := ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead
  let componentsMap := ModelSubstitution.openComponents Γ A B first second a b firstRead secondRead
  let combined := packMap.compose stable componentsMap
  let supplied := ModelSubstitution.openBinder Γ (model.sums.operations.sigma A B)
    (.pair domain body first second) (model.sums.operations.pair a b)
    (model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead)
  have composedRead := combined.evaluate
  change model.evaluateSubstitution Γ (Γ.snoc (model.sums.operations.sigma A B))
    (composeSubstitution (packSubstitution domain body) (instantiateComponents first second)) =
      some ((NativeModel C).toCwf.compS (pack model.sums A B)
        ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b)) at composedRead
  rw [packSubstitution_instantiate] at composedRead
  exact Option.some.inj (composedRead.symm.trans supplied.evaluate)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaEliminationBeta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (first second : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (branchInterpreted : Interprets model (.term (.snoc (.snoc context domain) body) branch
      (motive.substitute (packSubstitution domain body))))
    (firstInterpreted : Interprets model (.term context first domain))
    (secondInterpreted : Interprets model (.term context second (body.substitute (instantiate first)))) :
    Interprets model (.termEq context (.sigmaElim domain body motive branch (.pair domain body first second))
      (branch.substitute (instantiateComponents first second))
        (motive.substitute (instantiate (.pair domain body first second)))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  have sumRead := model.evaluate_sigma Γ domain body A B domainRead bodyRead
  rcases motiveInterpreted.typeAt (Γ.snoc (model.sums.operations.sigma A B))
    (model.evaluateContext_snoc context (.sigma domain body) Γ _ contextRead sumRead) with ⟨M, motiveRead⟩
  have tupleContextRead := model.evaluateContext_snoc (.snoc context domain) body (Γ.snoc A) B
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) bodyRead
  have branchTypeRead := model.evaluateType_substitute stable motive ((Γ.snoc A).snoc B)
    (Γ.snoc (model.sums.operations.sigma A B)) (packSubstitution domain body)
    (ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead) M motiveRead
  rcases branchInterpreted.termAt ((Γ.snoc A).snoc B) _ tupleContextRead branchTypeRead with ⟨branchValue, branchRead⟩
  change (NativeModel C).toCwf.Tm (tupleContext A B) ((NativeModel C).toCwf.tySub M (pack model.sums A B)) at branchValue
  rcases firstInterpreted.termAt Γ A contextRead domainRead with ⟨a, firstRead⟩
  rcases secondInterpreted.termAt Γ _ contextRead
    (model.evaluateType_instantiate stable Γ A body B first a bodyRead firstRead) with ⟨b, secondRead⟩
  have pairRead := model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead
  have pointSquare := model.pack_openComponents stable Γ domain body A B first second a b
    domainRead bodyRead firstRead secondRead
  have instantiatedBranch := model.evaluateTerm_substitute stable branch Γ ((Γ.snoc A).snoc B)
    (instantiateComponents first second) (ModelSubstitution.openComponents Γ A B first second a b firstRead secondRead)
    ⟨_, branchValue⟩ branchRead
  have eliminationRead := model.evaluate_sumElimination Γ domain body A B domainRead bodyRead
    motive branch (.pair domain body first second) M branchValue (model.sums.operations.pair a b)
    motiveRead branchRead pairRead
  have sameValue : (⟨_, (NativeModel C).toCwf.tmSub (eliminate model.sums A B M branchValue)
      (selfExtend (NativeModel C).toCwf (model.sums.operations.pair a b))⟩ : Value (NativeModel C).toCwf Γ.1) =
      ⟨_, (NativeModel C).toCwf.tmSub branchValue ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b)⟩ := by
    apply Sigma.ext
    · change (NativeModel C).toCwf.tySub M (selfExtend (NativeModel C).toCwf (model.sums.operations.pair a b)) =
        (NativeModel C).toCwf.tySub ((NativeModel C).toCwf.tySub M (pack model.sums A B))
          ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b)
      rw [← pointSquare, (NativeModel C).toCwf.tySub_comp]
    · rw [← pointSquare]
      exact (TypeOver.tmSub_comp_heq (eliminate model.sums A B M branchValue) _ _).trans
        (heq_of_eq (congrArg (fun term => (NativeModel C).toCwf.tmSub term
          ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b)) (eliminate_beta model.sums A B M branchValue)))
  rw [sameValue] at eliminationRead
  have declaredType := model.evaluateType_instantiate stable Γ (model.sums.operations.sigma A B)
    motive M (.pair domain body first second) (model.sums.operations.pair a b) motiveRead pairRead
  rw [← pointSquare, (NativeModel C).toCwf.tySub_comp] at declaredType
  exact ⟨Γ, _, (NativeModel C).toCwf.tmSub branchValue ((NativeModel C).toCwf.pair (selfExtend (NativeModel C).toCwf a) B b), contextRead,
    declaredType, eliminationRead, instantiatedBranch⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaEliminationEta_sound (stable : StrictPiSubstitution model.products)
    (context : ContextExpr S n) (domain : TypeExpr S n) (body motive : TypeExpr S (n + 1))
    (term : TermExpr S (n + 1)) (pair : TermExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (bodyInterpreted : Interprets model (.type (.snoc context domain) body))
    (motiveInterpreted : Interprets model (.type (.snoc context (.sigma domain body)) motive))
    (termInterpreted : Interprets model (.term (.snoc context (.sigma domain body)) term motive))
    (pairInterpreted : Interprets model (.term context pair (.sigma domain body))) :
    Interprets model (.termEq context (.sigmaElim domain body motive
      (term.substitute (packSubstitution domain body)) pair)
        (term.substitute (instantiate pair)) (motive.substitute (instantiate pair))) := by
  rcases Interprets.dependentTypes domainInterpreted bodyInterpreted with ⟨Γ, A, B, contextRead, domainRead, bodyRead⟩
  have sumRead := model.evaluate_sigma Γ domain body A B domainRead bodyRead
  have sumContextRead := model.evaluateContext_snoc context (.sigma domain body) Γ _ contextRead sumRead
  rcases motiveInterpreted.typeAt (Γ.snoc (model.sums.operations.sigma A B)) sumContextRead with ⟨M, motiveRead⟩
  rcases termInterpreted.termAt (Γ.snoc (model.sums.operations.sigma A B)) M sumContextRead motiveRead with ⟨value, termRead⟩
  rcases pairInterpreted.termAt Γ _ contextRead sumRead with ⟨p, pairRead⟩
  have branchRead := model.evaluateTerm_substitute stable term ((Γ.snoc A).snoc B)
    (Γ.snoc (model.sums.operations.sigma A B)) (packSubstitution domain body)
    (ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead) ⟨M, value⟩ termRead
  have eliminationRead := model.evaluate_sumElimination Γ domain body A B domainRead bodyRead motive
    (term.substitute (packSubstitution domain body)) pair M ((NativeModel C).toCwf.tmSub value (pack model.sums A B)) p
    motiveRead branchRead pairRead
  rw [eliminate_eta] at eliminationRead
  exact ⟨Γ, _, (NativeModel C).toCwf.tmSub value (selfExtend (NativeModel C).toCwf p), contextRead,
    model.evaluateType_instantiate stable Γ (model.sums.operations.sigma A B) motive M pair p motiveRead pairRead,
    eliminationRead, model.evaluateTerm_instantiate stable Γ (model.sums.operations.sigma A B)
      term ⟨M, value⟩ pair p termRead pairRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
