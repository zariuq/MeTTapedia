import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementInterpretation

/-!
# Constructor interpretation and dependent readouts

Successful child evaluations earn the corresponding independently authored
constructor's model readout. Primitive arguments are interpreted by actual
dependent telescope checking. These are local realization theorems; the
simultaneous theorem for all generated equality and judgment derivations
requires declaration-header agreement and conversion coherence separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers PresheafNativePropositionReadout
open External (bindResult)
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v a

variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

theorem dependentAnnotations_eq_some_iff {Result : Type a} (model : ModelData S C)
    {n : Nat} (Γ : Scope C n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (continuation : (A : NativeType Γ.1) → NativeType (Γ.snoc A).1 → Option Result)
    (value : Result) :
    bindResult (model.evaluateType Γ domain) (fun A =>
      bindResult (model.evaluateType (Γ.snoc A) body) (fun B => continuation A B)) = some value ↔
      ∃ A B, model.evaluateType Γ domain = some A ∧
        model.evaluateType (Γ.snoc A) body = some B ∧ continuation A B = some value := by
  constructor
  · intro read
    rcases (External.bindResult_eq_some_iff _ _ _).mp read with ⟨A, first, rest⟩
    rcases (External.bindResult_eq_some_iff _ _ _).mp rest with ⟨B, second, last⟩
    exact ⟨A, B, first, second, last⟩
  · rintro ⟨A, B, first, second, last⟩
    rw [first]
    change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
    rw [second]
    exact last

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem lambda?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (body : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext Γ A) B) :
    model.lambda? A B (some ⟨B, body⟩) =
      some ⟨model.products.pi A B, model.products.lam body⟩ := by
  simp only [lambda?, check?_supplied, bindResult]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem application?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (function : (NativeModel C).toCwf.Tm Γ (model.products.pi A B)) (argument : (NativeModel C).toCwf.Tm Γ A) :
    model.application? A B (some ⟨_, function⟩) (some ⟨A, argument⟩) =
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf argument), model.products.app function argument⟩ := by
  simp only [application?, check?_supplied, bindResult]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pair?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A)) (first : (NativeModel C).toCwf.Tm Γ A)
    (second : (NativeModel C).toCwf.Tm Γ ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf first))) :
    model.pair? A B (some ⟨A, first⟩) (some ⟨_, second⟩) =
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair first second⟩ := by
  simp only [pair?, check?_supplied, bindResult]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem first?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.first? A B (some ⟨_, pair⟩) = some ⟨A, model.sums.operations.fst pair⟩ := by
  simp only [first?, check?_supplied, bindResult]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem second?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.second? A B (some ⟨_, pair⟩) =
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf (model.sums.operations.fst pair)),
        model.sums.operations.snd pair⟩ := by
  simp only [second?, check?_supplied, bindResult]

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem sumEliminate?_supplied (model : ModelData S C) {Γ : Cᵒᵖ ⥤ Type u}
    (A : (NativeModel C).toCwf.Ty Γ) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ A))
    (M : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ (model.sums.operations.sigma A B)))
    (branch : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext ((NativeModel C).toCwf.ext Γ A) B)
      ((NativeModel C).toCwf.tySub M (pack model.sums A B)))
    (pair : (NativeModel C).toCwf.Tm Γ (model.sums.operations.sigma A B)) :
    model.sumEliminate? A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩) =
      some ⟨(NativeModel C).toCwf.tySub M (selfExtend (NativeModel C).toCwf pair),
        (NativeModel C).toCwf.tmSub (eliminate model.sums A B M branch) (selfExtend (NativeModel C).toCwf pair)⟩ := by
  simp only [sumEliminate?, check?_supplied, bindResult]

variable (model : ModelData S C) {n : Nat} (Γ : Scope C n)

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_family (symbol : S.TypeSymbol)
    (arguments : Fin (S.typeArity symbol) → TermExpr S n)
    (σ : (NativeModel C).toCwf.Sub Γ.1 (model.typeParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.typeParameters symbol).2.components σ index)) :
    model.evaluateType Γ (.family symbol arguments) = some (model.familyAt symbol σ) := by
  have assembled := (ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated
  simp only [evaluateType, assembled, bindResult]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_primitive (symbol : S.TermSymbol)
    (arguments : Fin (S.termArity symbol) → TermExpr S n)
    (σ : (NativeModel C).toCwf.Sub Γ.1 (model.termParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.termParameters symbol).2.components σ index)) :
    model.evaluateTerm Γ (.primitive symbol arguments) = some (model.primitiveAt symbol σ) := by
  have assembled := (ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated
  simp only [evaluateTerm, assembled, bindResult]

variable (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
  (A : (NativeModel C).toCwf.Ty Γ.1) (B : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 A))
  (domainEvaluated : model.evaluateType Γ domain = some A)
  (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B)

include domainEvaluated bodyEvaluated

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_pi : model.evaluateType Γ (.pi domain body) = some (model.products.pi A B) := by
  simp only [evaluateType, domainEvaluated,
    bindResult, bodyEvaluated]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_sigma : model.evaluateType Γ (.sigma domain body) =
    some (model.sums.operations.sigma A B) := by
  simp only [evaluateType, domainEvaluated,
    bindResult, bodyEvaluated]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_lambda (term : TermExpr S (n + 1))
    (value : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext Γ.1 A) B)
    (evaluated : model.evaluateTerm (Γ.snoc A) term = some ⟨B, value⟩) :
    model.evaluateTerm Γ (.lam domain body term) =
      some ⟨model.products.pi A B, model.products.lam value⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated, evaluated,
    ]
  exact model.lambda?_supplied A B value

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_application (function argument : TermExpr S n)
    (f : (NativeModel C).toCwf.Tm Γ.1 (model.products.pi A B)) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (functionEvaluated : model.evaluateTerm Γ function = some ⟨_, f⟩)
    (argumentEvaluated : model.evaluateTerm Γ argument = some ⟨_, a⟩) :
    model.evaluateTerm Γ (.app domain body function argument) =
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a), model.products.app f a⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated,
    functionEvaluated, argumentEvaluated, application?_supplied]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_pair (first second : TermExpr S n) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (b : (NativeModel C).toCwf.Tm Γ.1 ((NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a)))
    (firstEvaluated : model.evaluateTerm Γ first = some ⟨_, a⟩)
    (secondEvaluated : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    model.evaluateTerm Γ (.pair domain body first second) =
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair a b⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated,
    firstEvaluated, secondEvaluated, pair?_supplied]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_first (pair : TermExpr S n)
    (p : (NativeModel C).toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (evaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.fst domain body pair) = some ⟨A, model.sums.operations.fst p⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated, evaluated,
    first?_supplied]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_second (pair : TermExpr S n)
    (p : (NativeModel C).toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (evaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.snd domain body pair) =
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf (model.sums.operations.fst p)),
        model.sums.operations.snd p⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated, evaluated,
    second?_supplied]

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_sumElimination (motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (pair : TermExpr S n)
    (M : (NativeModel C).toCwf.Ty ((NativeModel C).toCwf.ext Γ.1 (model.sums.operations.sigma A B)))
    (b : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext ((NativeModel C).toCwf.ext Γ.1 A) B)
      ((NativeModel C).toCwf.tySub M (pack model.sums A B)))
    (p : (NativeModel C).toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (motiveEvaluated : model.evaluateType (Γ.snoc (model.sums.operations.sigma A B)) motive = some M)
    (branchEvaluated : model.evaluateTerm ((Γ.snoc A).snoc B) branch = some ⟨_, b⟩)
    (pairEvaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.sigmaElim domain body motive branch pair) =
      some ⟨(NativeModel C).toCwf.tySub M (selfExtend (NativeModel C).toCwf p),
        (NativeModel C).toCwf.tmSub (eliminate model.sums A B M b) (selfExtend (NativeModel C).toCwf p)⟩ := by
  simp only [evaluateTerm, domainEvaluated,
    bindResult, bodyEvaluated,
    motiveEvaluated, branchEvaluated, pairEvaluated,
    ]
  exact model.sumEliminate?_supplied A B M b p

/- Local product beta is sufficient to validate the actual evaluated
application of a supplied lambda body. -/
set_option backward.isDefEq.respectTransparency false in
theorem evaluated_lambda_beta (beta : PiBeta model.products)
    (term : TermExpr S (n + 1)) (argument : TermExpr S n)
    (value : (NativeModel C).toCwf.Tm ((NativeModel C).toCwf.ext Γ.1 A) B) (a : (NativeModel C).toCwf.Tm Γ.1 A)
    (termEvaluated : model.evaluateTerm (Γ.snoc A) term = some ⟨B, value⟩)
    (argumentEvaluated : model.evaluateTerm Γ argument = some ⟨A, a⟩) :
    model.evaluateTerm Γ (.app domain body (.lam domain body term) argument) =
      some ⟨(NativeModel C).toCwf.tySub B (selfExtend (NativeModel C).toCwf a), (NativeModel C).toCwf.tmSub value (selfExtend (NativeModel C).toCwf a)⟩ := by
  rw [model.evaluate_application Γ domain body A B domainEvaluated bodyEvaluated _ _ _ a
    (model.evaluate_lambda Γ domain body A B domainEvaluated bodyEvaluated term value termEvaluated)
    argumentEvaluated, beta]

set_option backward.isDefEq.respectTransparency false in
omit domainEvaluated bodyEvaluated in
theorem evaluate_comprehension (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : NativeType Γ.1) (φ : Subfunctor ((NativeModel C).toCwf.ext Γ.1 A))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluateType Γ (.comprehension domain predicate) =
      some (PresheafNativeStableRefinement.chosen A φ) := by
  simp only [evaluateType, domainRead, bindResult]
  exact congrArg (fun result => bindResult result
    (fun φ => some (PresheafNativeStableRefinement.chosen A φ))) predicateRead

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
