import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractPairContextInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractCongruenceSoundness

/-!
# Computational equations of the independent dependent presentation

Product and sum beta/eta are interpreted using the supplied local operation
equations. Full pair-elimination equations use the actual packing/opening
arrows, whose agreement follows from authored substitution and the earned
model component readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.TypeTheory.ContextualPredicateModel
open Mettapedia.TypeTheory.ContextualPredicateModelScopes
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualPiEta
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe a c s t m p

variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
  {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

attribute [local irreducible] TypeOver.extensionSubstitution
  ContextualSumComprehension.normalize ContextualSumComprehension.reindexBody

variable (model : ModelData S C localModel) {n : Nat}

set_option backward.isDefEq.respectTransparency false in
theorem piBeta_sound (stable : StrictPiSubstitution localModel.products) (beta : PiBeta localModel.products)
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
  exact ⟨Γ, _, C.toCwf.tmSub value (selfExtend C.toCwf a), contextRead,
    model.evaluateType_instantiate stable Γ A body B argument a bodyRead argumentRead,
    (by
      rw [model.evaluate_application Γ domain body A B domainRead bodyRead _ _ _ a
        (model.evaluate_lambda Γ domain body A B domainRead bodyRead term value termRead)
        argumentRead, beta]),
    model.evaluateTerm_instantiate stable Γ A term ⟨B, value⟩ argument a termRead argumentRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem piEta_sound (stable : StrictPiSubstitution localModel.products)
    (eta : PiEta localModel.products stable.1)
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
    ((Γ.snoc A).snoc (C.toCwf.tySub A (C.toCwf.wk A))) (Γ.snoc A)
    (liftRenaming Fin.succ) (weaken.lift A) B bodyRead
  have weakFunction := model.evaluateTerm_rename stable function (Γ.snoc A) Γ Fin.succ weaken _ functionRead
  rw [product_value_substitute localModel stable] at weakFunction
  have applicationRead := model.evaluate_application (Γ.snoc A) (domain.rename Fin.succ)
    (body.rename (liftRenaming Fin.succ)) (C.toCwf.tySub A (C.toCwf.wk A))
    (C.toCwf.tySub B (TypeOver.extensionSubstitution (C := C.toCwf) (C.toCwf.wk A) A)) weakDomain weakBody
    (function.rename Fin.succ) (.var 0) (reindexFunction localModel.products stable.1 (C.toCwf.wk A) f)
    (C.toCwf.vz A) weakFunction rfl
  have applicationValue : model.evaluateTerm (Γ.snoc A)
      (.app (domain.rename Fin.succ) (body.rename (liftRenaming Fin.succ))
        (function.rename Fin.succ) (.var 0)) = some ⟨B, genericSection localModel.products stable.1 f⟩ := by
    rw [applicationRead]
    exact congrArg some (Sigma.ext
      (generic_result_type (C := C.toCwf) A B)
      (genericSection_heq localModel.products stable.1 f).symm)
  have lambdaRead := model.evaluate_lambda Γ domain body A B domainRead bodyRead _
    (genericSection localModel.products stable.1 f) applicationValue
  rw [eta] at lambdaRead
  exact ⟨Γ, _, f, contextRead, productRead, lambdaRead, functionRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaFirstBeta_sound (stable : StrictPiSubstitution localModel.products)
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
    (.pair domain body first second) (localModel.sums.operations.pair a b) pairRead
  rw [localModel.sums.beta.1] at projection
  exact ⟨Γ, A, a, contextRead, domainRead, projection, firstRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaSecondBeta_sound (stable : StrictPiSubstitution localModel.products)
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
    (.pair domain body first second) (localModel.sums.operations.pair a b) pairRead
  have projectedValue : (⟨_, localModel.sums.operations.snd (localModel.sums.operations.pair a b)⟩ : Value C.toCwf Γ.1) =
      ⟨_, b⟩ := Sigma.ext (congrArg (fun first => C.toCwf.tySub B (selfExtend C.toCwf first))
        (localModel.sums.beta.1 a b)) (localModel.sums.beta.2 a b)
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
    (.fst domain body pair) (.snd domain body pair) (localModel.sums.operations.fst p) (localModel.sums.operations.snd p)
    (model.evaluate_first Γ domain body A B domainRead bodyRead pair p pairRead)
    (model.evaluate_second Γ domain body A B domainRead bodyRead pair p pairRead)
  rw [localModel.sums.eta] at reconstructed
  exact ⟨Γ, _, p, contextRead, sumRead, reconstructed, pairRead⟩

set_option backward.isDefEq.respectTransparency false in
theorem pack_openComponents (stable : StrictPiSubstitution localModel.products)
    (Γ : ModelScope C localModel n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : C.toCwf.Ty Γ.1) (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A))
    (first second : TermExpr S n) (a : C.toCwf.Tm Γ.1 A)
    (b : C.toCwf.Tm Γ.1 (C.toCwf.tySub B (selfExtend C.toCwf a)))
    (domainRead : model.evaluateType Γ domain = some A)
    (bodyRead : model.evaluateType (Γ.snoc A) body = some B)
    (firstRead : model.evaluateTerm Γ first = some ⟨A, a⟩)
    (secondRead : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    C.toCwf.compS (pack localModel.sums A B) (C.toCwf.pair (selfExtend C.toCwf a) B b) =
      selfExtend C.toCwf (localModel.sums.operations.pair a b) := by
  let packMap := ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead
  let componentsMap := ModelSubstitution.openComponents Γ A B first second a b firstRead secondRead
  let combined := packMap.compose stable componentsMap
  let supplied := ModelSubstitution.openBinder Γ (localModel.sums.operations.sigma A B)
    (.pair domain body first second) (localModel.sums.operations.pair a b)
    (model.evaluate_pair Γ domain body A B domainRead bodyRead first second a b firstRead secondRead)
  have composedRead := combined.evaluate
  change model.evaluateSubstitution Γ (Γ.snoc (localModel.sums.operations.sigma A B))
    (composeSubstitution (packSubstitution domain body) (instantiateComponents first second)) =
      some (C.toCwf.compS (pack localModel.sums A B)
        (C.toCwf.pair (selfExtend C.toCwf a) B b)) at composedRead
  rw [packSubstitution_instantiate] at composedRead
  exact Option.some.inj (composedRead.symm.trans supplied.evaluate)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaEliminationBeta_sound (stable : StrictPiSubstitution localModel.products)
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
  rcases motiveInterpreted.typeAt (Γ.snoc (localModel.sums.operations.sigma A B))
    (model.evaluateContext_snoc context (.sigma domain body) Γ _ contextRead sumRead) with ⟨M, motiveRead⟩
  have tupleContextRead := model.evaluateContext_snoc (.snoc context domain) body (Γ.snoc A) B
    (model.evaluateContext_snoc context domain Γ A contextRead domainRead) bodyRead
  have branchTypeRead := model.evaluateType_substitute stable motive ((Γ.snoc A).snoc B)
    (Γ.snoc (localModel.sums.operations.sigma A B)) (packSubstitution domain body)
    (ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead) M motiveRead
  rcases branchInterpreted.termAt ((Γ.snoc A).snoc B) _ tupleContextRead branchTypeRead with ⟨branchValue, branchRead⟩
  change C.toCwf.Tm (tupleContext A B) (C.toCwf.tySub M (pack localModel.sums A B)) at branchValue
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
    motive branch (.pair domain body first second) M branchValue (localModel.sums.operations.pair a b)
    motiveRead branchRead pairRead
  have sameValue : (⟨_, C.toCwf.tmSub (eliminate localModel.sums A B M branchValue)
      (selfExtend C.toCwf (localModel.sums.operations.pair a b))⟩ : Value C.toCwf Γ.1) =
      ⟨_, C.toCwf.tmSub branchValue (C.toCwf.pair (selfExtend C.toCwf a) B b)⟩ := by
    apply Sigma.ext
    · change C.toCwf.tySub M (selfExtend C.toCwf (localModel.sums.operations.pair a b)) =
        C.toCwf.tySub (C.toCwf.tySub M (pack localModel.sums A B))
          (C.toCwf.pair (selfExtend C.toCwf a) B b)
      rw [← pointSquare, C.toCwf.tySub_comp]
    · rw [← pointSquare]
      exact (TypeOver.tmSub_comp_heq (eliminate localModel.sums A B M branchValue) _ _).trans
        (heq_of_eq (congrArg (fun term => C.toCwf.tmSub term
          (C.toCwf.pair (selfExtend C.toCwf a) B b)) (eliminate_beta localModel.sums A B M branchValue)))
  rw [sameValue] at eliminationRead
  have declaredType := model.evaluateType_instantiate stable Γ (localModel.sums.operations.sigma A B)
    motive M (.pair domain body first second) (localModel.sums.operations.pair a b) motiveRead pairRead
  rw [← pointSquare, C.toCwf.tySub_comp] at declaredType
  exact ⟨Γ, _, C.toCwf.tmSub branchValue (C.toCwf.pair (selfExtend C.toCwf a) B b), contextRead,
    declaredType, eliminationRead, instantiatedBranch⟩

set_option backward.isDefEq.respectTransparency false in
theorem sigmaEliminationEta_sound (stable : StrictPiSubstitution localModel.products)
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
  rcases motiveInterpreted.typeAt (Γ.snoc (localModel.sums.operations.sigma A B)) sumContextRead with ⟨M, motiveRead⟩
  rcases termInterpreted.termAt (Γ.snoc (localModel.sums.operations.sigma A B)) M sumContextRead motiveRead with ⟨value, termRead⟩
  rcases pairInterpreted.termAt Γ _ contextRead sumRead with ⟨p, pairRead⟩
  have branchRead := model.evaluateTerm_substitute stable term ((Γ.snoc A).snoc B)
    (Γ.snoc (localModel.sums.operations.sigma A B)) (packSubstitution domain body)
    (ModelSubstitution.packPair stable Γ domain body A B domainRead bodyRead) ⟨M, value⟩ termRead
  have eliminationRead := model.evaluate_sumElimination Γ domain body A B domainRead bodyRead motive
    (term.substitute (packSubstitution domain body)) pair M (C.toCwf.tmSub value (pack localModel.sums A B)) p
    motiveRead branchRead pairRead
  rw [eliminate_eta] at eliminationRead
  exact ⟨Γ, _, C.toCwf.tmSub value (selfExtend C.toCwf p), contextRead,
    model.evaluateType_instantiate stable Γ (localModel.sums.operations.sigma A B) motive M pair p motiveRead pairRead,
    eliminationRead, model.evaluateTerm_instantiate stable Γ (localModel.sums.operations.sigma A B)
      term ⟨M, value⟩ pair p termRead pairRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
