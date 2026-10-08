import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModel
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalInterpretation

/-!
# Interpretation of mixed native refinement syntax

The evaluator traverses independent raw types, terms and predicates.
Dependent term annotations and mixed primitive arguments are checked against
their actual native meanings. Predicate assumptions select their satisfying
subobject; implication and universal quantification retain all future arrows.
Refinement introduction additionally checks the interpreted predicate.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.GSLT.Topos
open NativeLocalTypeFormers PresheafNativePropositionReadout
open DisplayedPresheafComprehension
open External (bindResult bindResult_eq_some_iff)

universe u v a
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

noncomputable def check? {P : Cᵒᵖ ⥤ Type u} (result : Option (NativeValue P))
    (type : NativeType P) : Option type.decoded.sections :=
  bindResult result (fun value => value.atType? type)

@[simp] theorem check?_supplied {P : Cᵒᵖ ⥤ Type u} (type : NativeType P)
    (term : type.decoded.sections) : check? (some ⟨type, term⟩) type = some term := by
  exact Value.atType?_supplied (K := (NativeModel C).toCwf) type term

theorem check?_eq_some_iff {P : Cᵒᵖ ⥤ Type u} (result : Option (NativeValue P))
    (type : NativeType P) (term : type.decoded.sections) :
    check? result type = some term ↔ result = some ⟨type, term⟩ := by
  cases result with
  | none => simp only [check?, bindResult, reduceCtorEq]
  | some value =>
      change Value.atType? (K := (NativeModel C).toCwf) value type = some term ↔
        some value = some ⟨type, term⟩
      rw [Option.some.injEq]
      exact Value.atType?_eq_some_iff (K := (NativeModel C).toCwf) value type term

noncomputable def lambda? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (body : Option (NativeValue ((NativeModel C).toCwf.ext P A))) : Option (NativeValue P) :=
  bindResult (check? body B) (fun value => some ⟨model.products.pi A B, model.products.lam value⟩)

noncomputable def application? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (function argument : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? function (model.products.pi A B)) (fun function =>
    bindResult (check? argument A) (fun argument =>
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf argument),
        model.products.app function argument⟩))

noncomputable def pair? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (first second : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? first A) (fun first =>
    bindResult (check? second ((NativeModel C).toCwf.tySub B
      (selfExtend (NativeModel C).toCwf first))) (fun second =>
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair first second⟩))

noncomputable def first? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (pair : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? pair (model.sums.operations.sigma A B))
    (fun pair => some ⟨A, model.sums.operations.fst pair⟩)

noncomputable def second? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (pair : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? pair (model.sums.operations.sigma A B)) (fun pair =>
    some ⟨(NativeModel C).toCwf.tySub B
      (selfExtend (NativeModel C).toCwf (model.sums.operations.fst pair)),
      model.sums.operations.snd pair⟩)

noncomputable def sumEliminate? (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u}
    (A : NativeType P) (B : NativeType ((NativeModel C).toCwf.ext P A))
    (M : NativeType ((NativeModel C).toCwf.ext P (model.sums.operations.sigma A B)))
    (branch : Option (NativeValue ((NativeModel C).toCwf.ext
      ((NativeModel C).toCwf.ext P A) B)))
    (pair : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? branch ((NativeModel C).toCwf.tySub M (pack model.sums A B))) (fun branch =>
    bindResult (check? pair (model.sums.operations.sigma A B)) (fun pair =>
      some ⟨(NativeModel C).toCwf.tySub M (selfExtend (NativeModel C).toCwf pair),
        (NativeModel C).toCwf.tmSub (eliminate model.sums A B M branch)
          (selfExtend (NativeModel C).toCwf pair)⟩))

/-- Introduction preserves the supplied inhabitant and checks its full
predicate at every point of the interpreted context. -/
noncomputable def refine? {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (result : Option (NativeValue P)) : Option (NativeValue P) := by
  classical
  exact bindResult (check? result A) (fun value =>
    if satisfies : ∀ world (base : P.obj world),
      (⟨base, value.val ⟨world, base⟩⟩ : (totalSpace A.decoded).obj world) ∈ predicate.obj world then
      some ⟨PresheafNativeStableRefinement.chosen A predicate,
        PresheafNativeStableRefinement.intro A predicate value satisfies⟩ else none)

noncomputable def forget? {P : Cᵒᵖ ⥤ Type u} (A : NativeType P)
    (predicate : Subfunctor (totalSpace A.decoded))
    (result : Option (NativeValue P)) : Option (NativeValue P) :=
  bindResult (check? result (PresheafNativeStableRefinement.chosen A predicate)) (fun value =>
    some ⟨A, PresheafNativeStableRefinement.forget A predicate value⟩)

mutual

noncomputable def evaluateType (model : ModelData S C) : {n : Nat} →
    (scope : Scope C n) → TypeExpr S n → Option (NativeType scope.1)
  | _, scope, .family symbol arguments =>
      bindResult ((model.typeParameters symbol).2.assemble?
        (fun index => model.evaluateTerm scope (arguments index)))
        (fun arguments => some (model.familyAt symbol arguments))
  | _, scope, .propositions => some (nativeOmega scope.1)
  | _, scope, .pi domain body =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => some (model.products.pi A B)))
  | _, scope, .sigma domain body =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => some (model.sums.operations.sigma A B)))
  | _, scope, .comprehension domain predicate =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (PresheafNativeStableRefinement.chosen A predicate)))

noncomputable def evaluateTerm (model : ModelData S C) : {n : Nat} →
    (scope : Scope C n) → TermExpr S n → Option (NativeValue scope.1)
  | _, scope, .var index => some (scope.2.lookup index)
  | _, scope, .primitive symbol arguments =>
      bindResult ((model.termParameters symbol).2.assemble?
        (fun index => model.evaluateTerm scope (arguments index)))
        (fun arguments => some (model.primitiveAt symbol arguments))
  | _, scope, .lam domain codomain body =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) codomain)
          (fun B => model.lambda? A B (model.evaluateTerm (scope.snoc A) body)))
  | _, scope, .app domain body function argument =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => model.application? A B (model.evaluateTerm scope function)
            (model.evaluateTerm scope argument)))
  | _, scope, .pair domain body first second =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => model.pair? A B (model.evaluateTerm scope first)
            (model.evaluateTerm scope second)))
  | _, scope, .fst domain body pair =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => model.first? A B (model.evaluateTerm scope pair)))
  | _, scope, .snd domain body pair =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body)
          (fun B => model.second? A B (model.evaluateTerm scope pair)))
  | _, scope, .sigmaElim domain body motive branch pair =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluateType (scope.snoc A) body) (fun B =>
          bindResult (model.evaluateType (scope.snoc (model.sums.operations.sigma A B)) motive)
            (fun M => model.sumEliminate? A B M
              (model.evaluateTerm ((scope.snoc A).snoc B) branch)
              (model.evaluateTerm scope pair))))
  | _, scope, .quote predicate =>
      bindResult (model.evaluatePredicateLift scope predicate).down
        (fun predicate => some ⟨nativeOmega scope.1, nativeQuote predicate⟩)
  | _, scope, .refine domain predicate term =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => refine? A predicate (model.evaluateTerm scope term)))
  | _, scope, .forget domain predicate term =>
      bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => forget? A predicate (model.evaluateTerm scope term)))

noncomputable def evaluatePredicateLift (model : ModelData S C) : {n : Nat} →
    (scope : Scope C n) → PropExpr S n → ULift.{u+1} (Option (Subfunctor scope.1))
  | _, scope, .atom symbol arguments =>
      ⟨bindResult ((model.predicateParameters symbol).2.assemble?
        (fun index => model.evaluateTerm scope (arguments index)))
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
        bindResult (model.evaluatePredicateLift scope second).down
          (fun second => some (himpPointwise first second)))⟩
  | _, scope, .all domain predicate =>
      ⟨bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (forallAlong ((NativeModel C).toCwf.wk A) predicate)))⟩
  | _, scope, .exists domain predicate =>
      ⟨bindResult (model.evaluateType scope domain) (fun A =>
        bindResult (model.evaluatePredicateLift (scope.snoc A) predicate).down
          (fun predicate => some (predicate.image ((NativeModel C).toCwf.wk A))))⟩
  | _, scope, .holds term =>
      ⟨bindResult (check? (model.evaluateTerm scope term) (nativeOmega scope.1))
        (fun term => some (nativeHolds term))⟩
  | _, scope, .image type =>
      ⟨bindResult (model.evaluateType scope type)
        (fun A => some (Subfunctor.range ((NativeModel C).toCwf.wk A)))⟩

end

noncomputable def evaluatePredicate (model : ModelData S C) {n : Nat}
    (scope : Scope C n) (predicate : PropExpr S n) : Option (Subfunctor scope.1) :=
  (model.evaluatePredicateLift scope predicate).down

noncomputable def evaluateContext (model : ModelData S C) : {n : Nat} →
    ContextExpr S n → Option (Scope C n)
  | _, .nil => some (Scope.nil C)
  | _, .snoc previous type =>
      bindResult (model.evaluateContext previous) (fun scope =>
        bindResult (model.evaluateType scope type) (fun A => some (scope.snoc A)))
  | _, .assume previous predicate =>
      bindResult (model.evaluateContext previous) (fun scope =>
        bindResult (model.evaluatePredicate scope predicate) (fun predicate => some (scope.assume predicate)))

noncomputable def evaluateSubstitution (model : ModelData S C) {n k : Nat}
    (source : Scope C n) (target : Scope C k) (substitution : Fin k → TermExpr S n) :
    Option (source.1 ⟶ target.1) :=
  target.2.assemble? (fun index => model.evaluateTerm source (substitution index))

theorem evaluateContext_snoc (model : ModelData S C) {n : Nat}
    (context : ContextExpr S n) (type : TypeExpr S n) (scope : Scope C n)
    (A : NativeType scope.1) (contextRead : model.evaluateContext context = some scope)
    (typeRead : model.evaluateType scope type = some A) :
    model.evaluateContext (.snoc context type) = some (scope.snoc A) := by
  simp only [evaluateContext, contextRead, bindResult, typeRead]

theorem evaluateContext_assume (model : ModelData S C) {n : Nat}
    (context : ContextExpr S n) (predicate : PropExpr S n) (scope : Scope C n)
    (φ : Subfunctor scope.1) (contextRead : model.evaluateContext context = some scope)
    (predicateRead : model.evaluatePredicate scope predicate = some φ) :
    model.evaluateContext (.assume context predicate) = some (scope.assume φ) := by
  simp only [evaluateContext, contextRead, bindResult, predicateRead]

theorem evaluateSubstitution_eq_some_iff (model : ModelData S C) {n k : Nat}
    (source : Scope C n) (target : Scope C k) (substitution : Fin k → TermExpr S n)
    (arrow : source.1 ⟶ target.1) : model.evaluateSubstitution source target substitution = some arrow ↔
    ∀ index, model.evaluateTerm source (substitution index) = some (target.2.components arrow index) :=
  ScopeData.assemble?_eq_some_iff _ _ _

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem evaluateSubstitution_identity (model : ModelData S C) {n : Nat}
    (scope : Scope C n) : model.evaluateSubstitution scope scope TermExpr.var = some (𝟙 scope.1) := by
  apply (model.evaluateSubstitution_eq_some_iff _ _ _ _).2
  intro index
  simp only [evaluateTerm, ScopeData.components]
  exact congrArg some (Value.substitute_identity (K := (NativeModel C).toCwf)
    (scope.2.lookup index)).symm

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
