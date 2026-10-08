import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractScope
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementJudgmentInterpretation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractJudgmentInterpretation

/-!
# The native refinement interpreter as a local-model instance

Primitive declarations keep their exact supplied meanings and complete
mixed parameter scopes. Mutual structural recursion compares all authored
types, terms and predicates, including guarded refinement, higher-order
propositions and full dependent sum motives. Context and substitution
evaluation are then compared through actual guarded assembly. Declaration
realization transfers only after these comparisons have been proved.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open ContextualModelTelescopes NativeLocalTypeFormers
open ContextualProductComparison (selfExtend)
open Mettapedia.GSLT.Topos
open DisplayedPresheafComprehension
open External (bindResult)

universe u v x y
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

private theorem compareBindings {Input : Type x} {Output : Type y}
    {first second : Option Input} {left right : Input → Option Output}
    (inputs : first = second) (continuations : ∀ value, left value = right value) :
    bindResult first left = bindResult second right := by
  cases inputs
  exact congrArg (bindResult first) (funext continuations)

/-- Header conversion retains the exact primitive family, section and
predicate. The independent parser is not a field of these data. -/
noncomputable def toAbstract (model : ModelData S C) :
    Abstract.ModelData S (NativeModel C) (PresheafNativePredicateModel.model C) where
  typeParameters symbol := NativeAbstractScope.toGeneric (model.typeParameters symbol)
  typeFamily := model.typeFamily
  termParameters symbol := NativeAbstractScope.toGeneric (model.termParameters symbol)
  termType := model.termType
  termValue := model.termValue
  predicateParameters symbol := NativeAbstractScope.toGeneric (model.predicateParameters symbol)
  predicateValue := model.predicateValue

private theorem lambda_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (body : Option (NativeValue ((NativeModel C).toCwf.ext P A))) :
    Abstract.ModelData.lambda? (PresheafNativePredicateModel.model C) A B body =
      model.lambda? A B body := rfl

private theorem application_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (function argument : Option (NativeValue P)) :
    Abstract.ModelData.application? (PresheafNativePredicateModel.model C) A B function argument =
      model.application? A B function argument := rfl

private theorem pair_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (first second : Option (NativeValue P)) :
    Abstract.ModelData.pair? (PresheafNativePredicateModel.model C) A B first second =
      model.pair? A B first second := rfl

private theorem first_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (pair : Option (NativeValue P)) :
    Abstract.ModelData.first? (PresheafNativePredicateModel.model C) A B pair =
      model.first? A B pair := rfl

private theorem second_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (pair : Option (NativeValue P)) :
    Abstract.ModelData.second? (PresheafNativePredicateModel.model C) A B pair =
      model.second? A B pair := rfl

section SumComparison

attribute [local irreducible] NativeLocalSumElimination.stableSums
  ContextualSumComprehension.pack ContextualSumComprehension.eliminate

private theorem sumEliminate_compare (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (M : NativeType ((NativeModel C).toCwf.ext P (model.sums.operations.sigma A B)))
    (branch : Option (NativeValue ((NativeModel C).toCwf.ext
      ((NativeModel C).toCwf.ext P A) B))) (pair : Option (NativeValue P)) :
    Abstract.ModelData.sumEliminate? (PresheafNativePredicateModel.model C) A B M branch pair =
      model.sumEliminate? A B M branch pair := rfl

end SumComparison

set_option backward.isDefEq.respectTransparency false in
/-- The local guard is equivalent to actual section membership at every
world, so the two checkers retain exactly the same inhabitant. -/
theorem refine_compare {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (result : Option (NativeValue P)) :
    Abstract.ModelData.refine? (PresheafNativePredicateModel.model C) A predicate result =
      refine? A predicate result := by
  classical
  change bindResult (check? result A) (fun value =>
      if guard : predicate.preimage (selfExtend (NativeModel C).toCwf value) = ⊤ then
        some (⟨PresheafNativeStableRefinement.chosen A predicate,
          PresheafNativeStableRefinement.intro A predicate value
            ((PresheafNativePredicateCapabilities.section_guard_iff A predicate value).mp guard)⟩ : NativeValue P)
      else none) =
    bindResult (check? result A) (fun value =>
      if satisfies : ∀ world (base : P.obj world),
          (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world then
        some (⟨PresheafNativeStableRefinement.chosen A predicate,
          PresheafNativeStableRefinement.intro A predicate value satisfies⟩ : NativeValue P) else none)
  apply congrArg (bindResult (check? result A))
  funext value
  by_cases guard : predicate.preimage (selfExtend (NativeModel C).toCwf value) = ⊤
  · have satisfies := (PresheafNativePredicateCapabilities.section_guard_iff A predicate value).mp guard
    rw [dif_pos guard, dif_pos satisfies]
  · have absent : ¬ ∀ world (base : P.obj world),
        (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world := by
      intro satisfies
      exact guard ((PresheafNativePredicateCapabilities.section_guard_iff A predicate value).mpr satisfies)
    rw [dif_neg guard, dif_neg absent]

private theorem forget_compare {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded)) (result : Option (NativeValue P)) :
    Abstract.ModelData.forget? (PresheafNativePredicateModel.model C) A predicate result =
      forget? A predicate result := rfl

set_option backward.isDefEq.respectTransparency false in
mutual

theorem evaluateType_compare (model : ModelData S C) : {n : Nat} →
    (type : TypeExpr S n) → (scope : Scope C n) →
      model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) type =
        model.evaluateType scope type
  | _, .family symbol arguments, scope => by
      change bindResult ((NativeAbstractScope.toGenericData (model.typeParameters symbol).2).assemble?
        (fun index => model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) (arguments index)))
        (fun arguments => some (model.familyAt symbol arguments)) = _
      have argumentReads : (fun index => model.toAbstract.evaluateTerm
          (NativeAbstractScope.toGeneric scope) (arguments index)) =
          (fun index => model.evaluateTerm scope (arguments index)) := by
        funext index
        exact evaluateTerm_compare model (arguments index) scope
      rw [argumentReads, NativeAbstractScope.assembly_compare]
      rfl
  | _, .propositions, scope => rfl
  | _, .pi domain body, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => some (model.products.pi A B))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rfl
  | _, .sigma domain body, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => some (model.sums.operations.sigma A B))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rfl
  | _, .comprehension domain predicate, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluatePredicate
          ((NativeAbstractScope.toGeneric scope).snoc A) predicate)
          (fun φ => some (PresheafNativeStableRefinement.chosen A φ))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluatePredicate_compare model predicate (scope.snoc A))
      intro predicate
      rfl

theorem evaluateTerm_compare (model : ModelData S C) : {n : Nat} →
    (term : TermExpr S n) → (scope : Scope C n) →
      model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) term =
        model.evaluateTerm scope term
  | _, .var index, scope => by
      change some ((NativeAbstractScope.toGenericData scope.2).lookup index) = some (scope.2.lookup index)
      rw [NativeAbstractScope.lookup_compare]
  | _, .primitive symbol arguments, scope => by
      change bindResult ((NativeAbstractScope.toGenericData (model.termParameters symbol).2).assemble?
        (fun index => model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) (arguments index)))
        (fun arguments => some (model.primitiveAt symbol arguments)) = _
      have argumentReads : (fun index => model.toAbstract.evaluateTerm
          (NativeAbstractScope.toGeneric scope) (arguments index)) =
          (fun index => model.evaluateTerm scope (arguments index)) := by
        funext index
        exact evaluateTerm_compare model (arguments index) scope
      rw [argumentReads, NativeAbstractScope.assembly_compare]
      rfl
  | _, .lam domain body term, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => Abstract.ModelData.lambda? (PresheafNativePredicateModel.model C) A B
            (model.toAbstract.evaluateTerm ((NativeAbstractScope.toGeneric scope).snoc A) term))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      exact (congrArg (Abstract.ModelData.lambda? (PresheafNativePredicateModel.model C) A B)
        (evaluateTerm_compare model term (scope.snoc A))).trans (lambda_compare model A B _)
  | _, .app domain body function argument, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => Abstract.ModelData.application? (PresheafNativePredicateModel.model C) A B
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) function)
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) argument))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rw [evaluateTerm_compare model function, evaluateTerm_compare model argument, application_compare]
  | _, .pair domain body first second, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => Abstract.ModelData.pair? (PresheafNativePredicateModel.model C) A B
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) first)
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) second))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rw [evaluateTerm_compare model first, evaluateTerm_compare model second, pair_compare]
  | _, .fst domain body pair, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => Abstract.ModelData.first? (PresheafNativePredicateModel.model C) A B
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) pair))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rw [evaluateTerm_compare model pair, first_compare]
  | _, .snd domain body pair, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body)
          (fun B => Abstract.ModelData.second? (PresheafNativePredicateModel.model C) A B
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) pair))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      rw [evaluateTerm_compare model pair, second_compare]
  | _, .sigmaElim domain body motive branch pair, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluateType
          ((NativeAbstractScope.toGeneric scope).snoc A) body) (fun B =>
          bindResult (model.toAbstract.evaluateType
            ((NativeAbstractScope.toGeneric scope).snoc (model.sums.operations.sigma A B)) motive)
            (fun M => Abstract.ModelData.sumEliminate? (PresheafNativePredicateModel.model C) A B M
              (model.toAbstract.evaluateTerm (((NativeAbstractScope.toGeneric scope).snoc A).snoc B) branch)
              (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) pair)))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluateType_compare model body (scope.snoc A))
      intro B
      apply compareBindings
        (evaluateType_compare model motive (scope.snoc (model.sums.operations.sigma A B)))
      intro M
      exact (congrArg₂ (Abstract.ModelData.sumEliminate? (PresheafNativePredicateModel.model C) A B M)
        (evaluateTerm_compare model branch ((scope.snoc A).snoc B))
        (evaluateTerm_compare model pair scope)).trans (sumEliminate_compare model A B M _ _)
  | _, .quote predicate, scope => by
      change bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) predicate)
        (fun φ => some (⟨PresheafNativePropositionReadout.nativeOmega scope.1,
          PresheafNativePropositionReadout.nativeQuote φ⟩ : NativeValue scope.1)) = _
      rw [evaluatePredicate_compare model predicate]
      rfl
  | _, .refine domain predicate term, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluatePredicate
          ((NativeAbstractScope.toGeneric scope).snoc A) predicate)
          (fun φ => Abstract.ModelData.refine? (PresheafNativePredicateModel.model C) A φ
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) term))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluatePredicate_compare model predicate (scope.snoc A))
      intro φ
      rw [evaluateTerm_compare model term, refine_compare]
  | _, .forget domain predicate term, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluatePredicate
          ((NativeAbstractScope.toGeneric scope).snoc A) predicate)
          (fun φ => Abstract.ModelData.forget? (PresheafNativePredicateModel.model C) A φ
            (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) term))) = _
      rw [evaluateType_compare model domain scope]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluatePredicate_compare model predicate (scope.snoc A))
      intro φ
      rw [evaluateTerm_compare model term, forget_compare]

theorem evaluatePredicate_compare (model : ModelData S C) : {n : Nat} →
    (predicate : PropExpr S n) → (scope : Scope C n) →
      model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) predicate =
        model.evaluatePredicate scope predicate
  | _, .atom symbol arguments, scope => by
      change bindResult ((NativeAbstractScope.toGenericData (model.predicateParameters symbol).2).assemble?
        (fun index => model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) (arguments index)))
        (fun arguments => some (model.predicateAt symbol arguments)) = _
      have argumentReads : (fun index => model.toAbstract.evaluateTerm
          (NativeAbstractScope.toGeneric scope) (arguments index)) =
          (fun index => model.evaluateTerm scope (arguments index)) := by
        funext index
        exact evaluateTerm_compare model (arguments index) scope
      rw [argumentReads, NativeAbstractScope.assembly_compare]
      rfl
  | _, .truth, scope => rfl
  | _, .falsehood, scope => rfl
  | _, .and first second, scope => by
      change bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) first)
        (fun φ => bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) second)
          (fun ψ => some (φ ⊓ ψ))) = _
      rw [evaluatePredicate_compare model first]
      apply congrArg (bindResult (model.evaluatePredicate scope first))
      funext φ
      rw [evaluatePredicate_compare model second]
      rfl
  | _, .or first second, scope => by
      change bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) first)
        (fun φ => bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) second)
          (fun ψ => some (φ ⊔ ψ))) = _
      rw [evaluatePredicate_compare model first]
      apply congrArg (bindResult (model.evaluatePredicate scope first))
      funext φ
      rw [evaluatePredicate_compare model second]
      rfl
  | _, .implies first second, scope => by
      change bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) first)
        (fun φ => bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) second)
          (fun ψ => some (φ ⇨ ψ))) = _
      rw [evaluatePredicate_compare model first]
      apply congrArg (bindResult (model.evaluatePredicate scope first))
      funext φ
      rw [evaluatePredicate_compare model second]
      apply congrArg (bindResult (model.evaluatePredicate scope second))
      funext ψ
      exact congrArg some (himpPointwise_eq_himp φ ψ).symm
  | _, .all domain predicate, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluatePredicate
          ((NativeAbstractScope.toGeneric scope).snoc A) predicate)
          (fun φ => some (forallAlong ((NativeModel C).toCwf.wk A) φ))) = _
      rw [evaluateType_compare model domain]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluatePredicate_compare model predicate (scope.snoc A))
      intro predicate
      rfl
  | _, .exists domain predicate, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) domain)
        (fun A => bindResult (model.toAbstract.evaluatePredicate
          ((NativeAbstractScope.toGeneric scope).snoc A) predicate)
          (fun φ => some (φ.image ((NativeModel C).toCwf.wk A)))) = _
      rw [evaluateType_compare model domain]
      apply congrArg (bindResult (model.evaluateType scope domain))
      funext A
      apply compareBindings (evaluatePredicate_compare model predicate (scope.snoc A))
      intro predicate
      rfl
  | _, .holds term, scope => by
      change bindResult (check? (model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric scope) term)
        (PresheafNativePropositionReadout.nativeOmega scope.1))
        (fun term => some (PresheafNativePropositionReadout.nativeHolds term)) = _
      rw [evaluateTerm_compare model term]
      rfl
  | _, .image type, scope => by
      change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) type)
        (fun A => some ((⊤ : Subfunctor (totalSpace A.decoded)).image ((NativeModel C).toCwf.wk A))) = _
      rw [evaluateType_compare model type]
      apply congrArg (bindResult (model.evaluateType scope type))
      funext A
      exact congrArg some (Subfunctor.image_top ((NativeModel C).toCwf.wk A))

end

set_option backward.isDefEq.respectTransparency false in
theorem evaluateContext_compare (model : ModelData S C) : {n : Nat} →
    (context : ContextExpr S n) → model.toAbstract.evaluateContext context =
      (model.evaluateContext context).map NativeAbstractScope.toGeneric
  | _, .nil => rfl
  | _, .snoc previous type => by
      change bindResult (model.toAbstract.evaluateContext previous) (fun scope =>
        bindResult (model.toAbstract.evaluateType scope type) (fun A => some (scope.snoc A))) =
        (bindResult (model.evaluateContext previous) (fun scope =>
          bindResult (model.evaluateType scope type) (fun A => some (scope.snoc A)))).map
            NativeAbstractScope.toGeneric
      rw [evaluateContext_compare]
      cases previousRead : model.evaluateContext previous with
      | none => rfl
      | some scope =>
          change bindResult (model.toAbstract.evaluateType (NativeAbstractScope.toGeneric scope) type)
            (fun A => some (NativeAbstractScope.toGeneric (scope.snoc A))) =
            (bindResult (model.evaluateType scope type) (fun A => some (scope.snoc A))).map
              NativeAbstractScope.toGeneric
          rw [evaluateType_compare]
          cases model.evaluateType scope type <;> rfl
  | _, .assume previous predicate => by
      change bindResult (model.toAbstract.evaluateContext previous) (fun scope =>
        bindResult (model.toAbstract.evaluatePredicate scope predicate) (fun φ => some (scope.assume φ))) =
        (bindResult (model.evaluateContext previous) (fun scope =>
          bindResult (model.evaluatePredicate scope predicate) (fun φ => some (scope.assume φ)))).map
            NativeAbstractScope.toGeneric
      rw [evaluateContext_compare]
      cases previousRead : model.evaluateContext previous with
      | none => rfl
      | some scope =>
          change bindResult (model.toAbstract.evaluatePredicate (NativeAbstractScope.toGeneric scope) predicate)
            (fun φ => some (NativeAbstractScope.toGeneric (scope.assume φ))) =
            (bindResult (model.evaluatePredicate scope predicate) (fun φ => some (scope.assume φ))).map
              NativeAbstractScope.toGeneric
          rw [evaluatePredicate_compare]
          cases model.evaluatePredicate scope predicate <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem evaluateSubstitution_compare (model : ModelData S C) {n k : Nat}
    (source : Scope C n) (target : Scope C k) (substitution : Substitution S k n) :
    model.toAbstract.evaluateSubstitution (NativeAbstractScope.toGeneric source)
      (NativeAbstractScope.toGeneric target) substitution =
        model.evaluateSubstitution source target substitution := by
  change (NativeAbstractScope.toGenericData target.2).assemble?
    (fun index => model.toAbstract.evaluateTerm (NativeAbstractScope.toGeneric source) (substitution index)) = _
  have argumentReads : (fun index => model.toAbstract.evaluateTerm
      (NativeAbstractScope.toGeneric source) (substitution index)) =
      (fun index => model.evaluateTerm source (substitution index)) := by
    funext index
    exact model.evaluateTerm_compare (substitution index) source
  rw [argumentReads, NativeAbstractScope.assembly_compare]
  rfl

end ModelData

namespace SignatureRealization

theorem toAbstract {model : ModelData S C} {D : Signature S}
    (realization : SignatureRealization model D) :
    Abstract.SignatureRealization model.toAbstract D where
  typeHeader symbol := by
    rw [model.evaluateContext_compare, realization.typeHeader, Option.map_some]
    rfl
  termHeader symbol := by
    rw [model.evaluateContext_compare, realization.termHeader, Option.map_some]
    rfl
  predicateHeader symbol := by
    rw [model.evaluateContext_compare, realization.predicateHeader, Option.map_some]
    rfl
  termResult symbol := by
    change model.toAbstract.evaluateType
      (NativeAbstractScope.toGeneric (model.termParameters symbol)) (D.termResult symbol) = _
    rw [model.evaluateType_compare, realization.termResult]
    rfl

end SignatureRealization

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
