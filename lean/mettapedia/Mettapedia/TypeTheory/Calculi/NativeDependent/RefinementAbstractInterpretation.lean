import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalInterpretation

/-!
# Evaluation of authored syntax in local predicate models

The interpreter traverses the independent mutually defined type, term and
predicate syntax. Ordered primitive arguments are checked through actual
mixed semantic scopes. Conditional refinement checks its exact guard;
assumption contexts restrict evaluation through their model inclusion.
The internal lifts align independently sized semantic carriers and add no
object-language universe. Soundness and substitution are separate theorems.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualSumComprehension ContextualProductComparison
open External (bindResult)

universe a c s t m p
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
variable {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

noncomputable def check? {context : C.toCwf.Ctx} (result : Option (Value C.toCwf context))
    (type : C.toCwf.Ty context) : Option (C.toCwf.Tm context type) :=
  bindResult result (fun value => value.atType? type)

@[simp] theorem check?_supplied {context : C.toCwf.Ctx} (type : C.toCwf.Ty context)
    (term : C.toCwf.Tm context type) : check? (some ⟨type, term⟩) type = some term :=
  Value.atType?_supplied type term

theorem check?_eq_some_iff {context : C.toCwf.Ctx} (result : Option (Value C.toCwf context))
    (type : C.toCwf.Ty context) (term : C.toCwf.Tm context type) :
    check? result type = some term ↔ result = some ⟨type, term⟩ := by
  cases result with
  | none => simp only [check?, bindResult, reduceCtorEq]
  | some value =>
      change value.atType? type = some term ↔ some value = some ⟨type, term⟩
      rw [Option.some.injEq]
      exact Value.atType?_eq_some_iff value type term

noncomputable def lambda? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (body : Option (Value C.toCwf (C.toCwf.ext context A))) : Option (Value C.toCwf context) :=
  bindResult (check? body B) (fun value => some ⟨localModel.products.pi A B, localModel.products.lam value⟩)

noncomputable def application? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (function argument : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? function (localModel.products.pi A B)) (fun function =>
    bindResult (check? argument A) (fun argument =>
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf argument), localModel.products.app function argument⟩))

noncomputable def pair? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (first second : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? first A) (fun first =>
    bindResult (check? second (C.toCwf.tySub B (selfExtend C.toCwf first))) (fun second =>
      some ⟨localModel.sums.operations.sigma A B, localModel.sums.operations.pair first second⟩))

noncomputable def first? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (pair : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? pair (localModel.sums.operations.sigma A B))
    (fun pair => some ⟨A, localModel.sums.operations.fst pair⟩)

noncomputable def second? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (pair : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? pair (localModel.sums.operations.sigma A B)) (fun pair =>
    some ⟨C.toCwf.tySub B (selfExtend C.toCwf (localModel.sums.operations.fst pair)),
      localModel.sums.operations.snd pair⟩)

noncomputable def sumEliminate? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context) (B : C.toCwf.Ty (C.toCwf.ext context A))
    (M : C.toCwf.Ty (C.toCwf.ext context (localModel.sums.operations.sigma A B)))
    (branch : Option (Value C.toCwf (C.toCwf.ext (C.toCwf.ext context A) B)))
    (pair : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? branch (C.toCwf.tySub M (pack localModel.sums A B))) (fun branch =>
    bindResult (check? pair (localModel.sums.operations.sigma A B)) (fun pair =>
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate localModel.sums A B M branch) (selfExtend C.toCwf pair)⟩))

noncomputable def refine? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext context A))
    (result : Option (Value C.toCwf context)) : Option (Value C.toCwf context) := by
  classical
  exact bindResult (check? result A) (fun value =>
    if guard : localModel.doctrine.reindex (selfExtend C.toCwf value) predicate = ⊤ then
      some ⟨localModel.refinements.refined A predicate,
        localModel.refinements.intro A predicate value guard⟩ else none)

noncomputable def forget? (localModel : LocalModel.{c, s, t, m, p} C)
    {context : C.toCwf.Ctx} (A : C.toCwf.Ty context)
    (predicate : localModel.doctrine.Predicate (C.toCwf.ext context A))
    (result : Option (Value C.toCwf context)) : Option (Value C.toCwf context) :=
  bindResult (check? result (localModel.refinements.refined A predicate)) (fun value =>
    some ⟨A, localModel.refinements.forget A predicate value⟩)

mutual

noncomputable def evaluateTypeLift (model : ModelData S C localModel) : {n : Nat} →
    (scope : ModelScope C localModel n) → TypeExpr S n → ULift.{max t m p} (Option (C.toCwf.Ty scope.1))
  | _, scope, .family symbol arguments =>
      ⟨bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => (model.evaluateTermLift scope (arguments index)).down))
        (fun arguments => some (model.familyAt symbol arguments))⟩
  | _, scope, .propositions => ⟨some (localModel.propositions.omega scope.1)⟩
  | _, scope, .pi domain body =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => some (localModel.products.pi A B)))⟩
  | _, scope, .sigma domain body =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => some (localModel.sums.operations.sigma A B)))⟩
  | _, scope, .comprehension domain predicate =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (localModel.refinements.refined A predicate)))⟩

noncomputable def evaluateTermLift (model : ModelData S C localModel) : {n : Nat} →
    (scope : ModelScope C localModel n) → TermExpr S n → ULift.{max t m p} (Option (Value C.toCwf scope.1))
  | _, scope, .var index => ⟨some (scope.2.lookup index)⟩
  | _, scope, .primitive symbol arguments =>
      ⟨bindResult ((model.termParameters symbol).2.assemble?
        (fun index => (model.evaluateTermLift scope (arguments index)).down))
        (fun arguments => some (model.primitiveAt symbol arguments))⟩
  | _, scope, .lam domain codomain body =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) codomain).down
          (fun B => lambda? localModel A B (model.evaluateTermLift (scope.snoc A) body).down))⟩
  | _, scope, .app domain body function argument =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => application? localModel A B (model.evaluateTermLift scope function).down
            (model.evaluateTermLift scope argument).down))⟩
  | _, scope, .pair domain body first second =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => pair? localModel A B (model.evaluateTermLift scope first).down
            (model.evaluateTermLift scope second).down))⟩
  | _, scope, .fst domain body pair =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => first? localModel A B (model.evaluateTermLift scope pair).down))⟩
  | _, scope, .snd domain body pair =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down
          (fun B => second? localModel A B (model.evaluateTermLift scope pair).down))⟩
  | _, scope, .sigmaElim domain body motive branch pair =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluateTypeLift (scope.snoc A) body).down (fun B =>
          bindResult (model.evaluateTypeLift (scope.snoc (localModel.sums.operations.sigma A B)) motive).down
            (fun M => sumEliminate? localModel A B M
              (model.evaluateTermLift ((scope.snoc A).snoc B) branch).down
              (model.evaluateTermLift scope pair).down)))⟩
  | _, scope, .quote predicate =>
      ⟨bindResult (model.evaluatePredicateLift scope predicate).down
        (fun predicate => some ⟨localModel.propositions.omega scope.1,
          localModel.propositions.quote predicate⟩)⟩
  | _, scope, .refine domain predicate term =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => refine? localModel A predicate (model.evaluateTermLift scope term).down))⟩
  | _, scope, .forget domain predicate term =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => forget? localModel A predicate (model.evaluateTermLift scope term).down))⟩

noncomputable def evaluatePredicateLift (model : ModelData S C localModel) : {n : Nat} →
    (scope : ModelScope C localModel n) → PropExpr S n →
      ULift.{max t m p} (Option (localModel.doctrine.Predicate scope.1))
  | _, scope, .atom symbol arguments =>
      ⟨bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => (model.evaluateTermLift scope (arguments index)).down))
        (fun arguments => some (model.predicateAt symbol arguments))⟩
  | _, _, .truth => ⟨some ⊤⟩
  | _, _, .falsehood => ⟨some ⊥⟩
  | _, scope, .and first second =>
      ⟨bindResult (model.evaluatePredicateLift scope first).down (fun first =>
        bindResult (model.evaluatePredicateLift scope second).down (fun second => some (first ⊓ second)))⟩
  | _, scope, .or first second =>
      ⟨bindResult (model.evaluatePredicateLift scope first).down (fun first =>
        bindResult (model.evaluatePredicateLift scope second).down (fun second => some (first ⊔ second)))⟩
  | _, scope, .implies first second =>
      ⟨bindResult (model.evaluatePredicateLift scope first).down (fun first =>
        bindResult (model.evaluatePredicateLift scope second).down (fun second => some (first ⇨ second)))⟩
  | _, scope, .all domain predicate =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (localModel.doctrine.all A predicate)))⟩
  | _, scope, .exists domain predicate =>
      ⟨bindResult (model.evaluateTypeLift scope domain).down (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (localModel.doctrine.some A predicate)))⟩
  | _, scope, .holds term =>
      ⟨bindResult (check? (model.evaluateTermLift scope term).down (localModel.propositions.omega scope.1))
        (fun term => some (localModel.propositions.holds term))⟩
  | _, scope, .image type =>
      ⟨bindResult (model.evaluateTypeLift scope type).down
        (fun A => some (localModel.doctrine.some A ⊤))⟩

end

noncomputable def evaluateType (model : ModelData S C localModel) {n : Nat}
    (scope : ModelScope C localModel n) (type : TypeExpr S n) : Option (C.toCwf.Ty scope.1) :=
  (model.evaluateTypeLift scope type).down

noncomputable def evaluateTerm (model : ModelData S C localModel) {n : Nat}
    (scope : ModelScope C localModel n) (term : TermExpr S n) : Option (Value C.toCwf scope.1) :=
  (model.evaluateTermLift scope term).down

noncomputable def evaluatePredicate (model : ModelData S C localModel) {n : Nat}
    (scope : ModelScope C localModel n) (predicate : PropExpr S n) :
    Option (localModel.doctrine.Predicate scope.1) :=
  (model.evaluatePredicateLift scope predicate).down

noncomputable def evaluateContext (model : ModelData S C localModel) : {n : Nat} →
    ContextExpr S n → Option (ModelScope C localModel n)
  | _, .nil => some (Scope.nil C localModel.doctrine localModel.assumptions)
  | _, .snoc previous type =>
      bindResult (model.evaluateContext previous) (fun scope =>
        bindResult (model.evaluateType scope type) (fun A => some (scope.snoc A)))
  | _, .assume previous predicate =>
      bindResult (model.evaluateContext previous) (fun scope =>
        bindResult (model.evaluatePredicate scope predicate) (fun predicate => some (scope.assume predicate)))

noncomputable def evaluateSubstitution (model : ModelData S C localModel) {n k : Nat}
    (source : ModelScope C localModel n) (target : ModelScope C localModel k)
    (substitution : Fin k → TermExpr S n) : Option (C.toCwf.Sub source.1 target.1) :=
  target.2.assemble? (fun index => model.evaluateTerm source (substitution index))

theorem evaluateContext_snoc (model : ModelData S C localModel) {n : Nat}
    (context : ContextExpr S n) (type : TypeExpr S n) (scope : ModelScope C localModel n)
    (A : C.toCwf.Ty scope.1) (contextRead : model.evaluateContext context = some scope)
    (typeRead : model.evaluateType scope type = some A) :
    model.evaluateContext (.snoc context type) = some (scope.snoc A) := by
  simp only [evaluateContext, contextRead, bindResult, typeRead]

theorem evaluateContext_assume (model : ModelData S C localModel) {n : Nat}
    (context : ContextExpr S n) (predicate : PropExpr S n) (scope : ModelScope C localModel n)
    (φ : localModel.doctrine.Predicate scope.1) (contextRead : model.evaluateContext context = some scope)
    (predicateRead : model.evaluatePredicate scope predicate = some φ) :
    model.evaluateContext (.assume context predicate) = some (scope.assume φ) := by
  simp only [evaluateContext, contextRead, bindResult, predicateRead]

theorem evaluateSubstitution_eq_some_iff (model : ModelData S C localModel) {n k : Nat}
    (source : ModelScope C localModel n) (target : ModelScope C localModel k)
    (substitution : Fin k → TermExpr S n) (arrow : C.toCwf.Sub source.1 target.1) :
    model.evaluateSubstitution source target substitution = some arrow ↔
      ∀ index, model.evaluateTerm source (substitution index) = some (target.2.components arrow index) :=
  ScopeData.assemble?_eq_some_iff _ _ _

@[simp] theorem evaluateSubstitution_identity (model : ModelData S C localModel) {n : Nat}
    (scope : ModelScope C localModel n) :
    model.evaluateSubstitution scope scope TermExpr.var = some (C.toCwf.idS scope.1) := by
  apply (model.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro index
  simp only [evaluateTerm, evaluateTermLift, ScopeData.components]
  exact congrArg some (Value.substitute_identity (scope.2.lookup index)).symm

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
