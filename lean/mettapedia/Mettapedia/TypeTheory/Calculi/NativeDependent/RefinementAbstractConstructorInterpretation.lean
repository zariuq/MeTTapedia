import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractInterpretation

/-!
# Complete constructor readouts in local predicate models

Each readout computes the independently evaluated annotated constructor from
its supplied domain, codomain and complete component sections. Dependent sum
elimination retains the full pair-context motive and branch. No whole-program
interpretation or substitution theorem is an input.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateModel ContextualPredicateModelScopes ContextualModelTelescopes
open ContextualSumComprehension ContextualProductComparison ContextualTypeOperations
open External (bindResult)

universe a c s t m p r
variable {S : Symbols.{a}} {C : CwfWithTerminal.{c, s, t, m}}
variable {localModel : LocalModel.{c, s, t, m, p} C}

namespace ModelData

theorem dependentAnnotations_eq_some_iff {Result : Type r} (model : ModelData S C localModel)
    {n : Nat} (Γ : ModelScope C localModel n) (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (continuation : (A : C.toCwf.Ty Γ.1) → C.toCwf.Ty (C.toCwf.ext Γ.1 A) → Option Result)
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

@[simp] theorem lambda?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (body : C.toCwf.Tm (C.toCwf.ext Γ A) B) :
    lambda? localModel A B (some ⟨B, body⟩) =
      some ⟨localModel.products.pi A B, localModel.products.lam body⟩ := by
  simp only [lambda?, check?_supplied, bindResult]

@[simp] theorem application?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (function : C.toCwf.Tm Γ (localModel.products.pi A B)) (argument : C.toCwf.Tm Γ A) :
    application? localModel A B (some ⟨_, function⟩) (some ⟨A, argument⟩) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf argument), localModel.products.app function argument⟩ := by
  simp only [application?, check?_supplied, bindResult]

@[simp] theorem pair?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (first : C.toCwf.Tm Γ A) (second : C.toCwf.Tm Γ (C.toCwf.tySub B (selfExtend C.toCwf first))) :
    pair? localModel A B (some ⟨A, first⟩) (some ⟨_, second⟩) =
      some ⟨localModel.sums.operations.sigma A B, localModel.sums.operations.pair first second⟩ := by
  simp only [pair?, check?_supplied, bindResult]

@[simp] theorem first?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    first? localModel A B (some ⟨_, pair⟩) = some ⟨A, localModel.sums.operations.fst pair⟩ := by
  simp only [first?, check?_supplied, bindResult]

@[simp] theorem second?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    second? localModel A B (some ⟨_, pair⟩) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf (localModel.sums.operations.fst pair)),
        localModel.sums.operations.snd pair⟩ := by
  simp only [second?, check?_supplied, bindResult]

@[simp] theorem sumEliminate?_supplied (localModel : LocalModel.{c, s, t, m, p} C)
    {Γ : C.toCwf.Ctx} (A : C.toCwf.Ty Γ) (B : C.toCwf.Ty (C.toCwf.ext Γ A))
    (M : C.toCwf.Ty (C.toCwf.ext Γ (localModel.sums.operations.sigma A B)))
    (branch : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ A) B) (C.toCwf.tySub M (pack localModel.sums A B)))
    (pair : C.toCwf.Tm Γ (localModel.sums.operations.sigma A B)) :
    sumEliminate? localModel A B M (some ⟨_, branch⟩) (some ⟨_, pair⟩) =
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf pair),
        C.toCwf.tmSub (eliminate localModel.sums A B M branch) (selfExtend C.toCwf pair)⟩ := by
  simp only [sumEliminate?, check?_supplied, bindResult]

variable (model : ModelData S C localModel) {n : Nat} (Γ : ModelScope C localModel n)

theorem evaluate_family (symbol : S.TypeSymbol)
    (arguments : Fin (S.typeArity symbol) → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 (model.typeParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.typeParameters symbol).2.components σ index)) :
    model.evaluateType Γ (.family symbol arguments) = some (model.familyAt symbol σ) := by
  change bindResult ((model.typeParameters symbol).2.assemble?
    (fun index => model.evaluateTerm Γ (arguments index))) _ = _
  rw [(ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated]
  rfl

theorem evaluate_primitive (symbol : S.TermSymbol)
    (arguments : Fin (S.termArity symbol) → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 (model.termParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.termParameters symbol).2.components σ index)) :
    model.evaluateTerm Γ (.primitive symbol arguments) = some (model.primitiveAt symbol σ) := by
  change bindResult ((model.termParameters symbol).2.assemble?
    (fun index => model.evaluateTerm Γ (arguments index))) _ = _
  rw [(ScopeData.assemble?_eq_some_iff _ _ σ).mpr evaluated]
  rfl

variable (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
    (A : C.toCwf.Ty Γ.1) (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A))
    (domainRead : model.evaluateType Γ domain = some A)
    (bodyRead : model.evaluateType (Γ.snoc A) body = some B)

include domainRead bodyRead

theorem evaluate_pi : model.evaluateType Γ (.pi domain body) = some (localModel.products.pi A B) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body) (fun B => some (localModel.products.pi A B))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  rfl

theorem evaluate_sigma : model.evaluateType Γ (.sigma domain body) =
    some (localModel.sums.operations.sigma A B) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body) (fun B => some (localModel.sums.operations.sigma A B))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  rfl

theorem evaluate_lambda (term : TermExpr S (n + 1))
    (value : C.toCwf.Tm (C.toCwf.ext Γ.1 A) B)
    (termRead : model.evaluateTerm (Γ.snoc A) term = some ⟨B, value⟩) :
    model.evaluateTerm Γ (.lam domain body term) =
      some ⟨localModel.products.pi A B, localModel.products.lam value⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body)
      (fun B => lambda? localModel A B (model.evaluateTerm (Γ.snoc A) term))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change lambda? localModel A B (model.evaluateTerm (Γ.snoc A) term) = _
  rw [termRead]
  simp only [lambda?, check?_supplied, bindResult]

theorem evaluate_application (function argument : TermExpr S n)
    (f : C.toCwf.Tm Γ.1 (localModel.products.pi A B)) (value : C.toCwf.Tm Γ.1 A)
    (functionRead : model.evaluateTerm Γ function = some ⟨_, f⟩)
    (argumentRead : model.evaluateTerm Γ argument = some ⟨_, value⟩) :
    model.evaluateTerm Γ (.app domain body function argument) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf value), localModel.products.app f value⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body) (fun B => application? localModel A B
      (model.evaluateTerm Γ function) (model.evaluateTerm Γ argument))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change application? localModel A B (model.evaluateTerm Γ function) (model.evaluateTerm Γ argument) = _
  rw [functionRead, argumentRead]
  simp only [application?, check?_supplied, bindResult]

theorem evaluate_pair (first second : TermExpr S n) (value : C.toCwf.Tm Γ.1 A)
    (witness : C.toCwf.Tm Γ.1 (C.toCwf.tySub B (selfExtend C.toCwf value)))
    (firstRead : model.evaluateTerm Γ first = some ⟨_, value⟩)
    (secondRead : model.evaluateTerm Γ second = some ⟨_, witness⟩) :
    model.evaluateTerm Γ (.pair domain body first second) =
      some ⟨localModel.sums.operations.sigma A B, localModel.sums.operations.pair value witness⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body) (fun B => pair? localModel A B
      (model.evaluateTerm Γ first) (model.evaluateTerm Γ second))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change pair? localModel A B (model.evaluateTerm Γ first) (model.evaluateTerm Γ second) = _
  rw [firstRead, secondRead]
  simp only [pair?, check?_supplied, bindResult]

theorem evaluate_first (pair : TermExpr S n)
    (value : C.toCwf.Tm Γ.1 (localModel.sums.operations.sigma A B))
    (pairRead : model.evaluateTerm Γ pair = some ⟨_, value⟩) :
    model.evaluateTerm Γ (.fst domain body pair) = some ⟨A, localModel.sums.operations.fst value⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body)
      (fun B => first? localModel A B (model.evaluateTerm Γ pair))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change first? localModel A B (model.evaluateTerm Γ pair) = _
  rw [pairRead]
  simp only [first?, check?_supplied, bindResult]

theorem evaluate_second (pair : TermExpr S n)
    (value : C.toCwf.Tm Γ.1 (localModel.sums.operations.sigma A B))
    (pairRead : model.evaluateTerm Γ pair = some ⟨_, value⟩) :
    model.evaluateTerm Γ (.snd domain body pair) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf (localModel.sums.operations.fst value)),
        localModel.sums.operations.snd value⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body)
      (fun B => second? localModel A B (model.evaluateTerm Γ pair))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change second? localModel A B (model.evaluateTerm Γ pair) = _
  rw [pairRead]
  simp only [second?, check?_supplied, bindResult]

theorem evaluate_sumElimination (motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (pair : TermExpr S n)
    (M : C.toCwf.Ty (C.toCwf.ext Γ.1 (localModel.sums.operations.sigma A B)))
    (suppliedBranch : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ.1 A) B)
      (C.toCwf.tySub M (pack localModel.sums A B)))
    (value : C.toCwf.Tm Γ.1 (localModel.sums.operations.sigma A B))
    (motiveRead : model.evaluateType (Γ.snoc (localModel.sums.operations.sigma A B)) motive = some M)
    (branchRead : model.evaluateTerm ((Γ.snoc A).snoc B) branch = some ⟨_, suppliedBranch⟩)
    (pairRead : model.evaluateTerm Γ pair = some ⟨_, value⟩) :
    model.evaluateTerm Γ (.sigmaElim domain body motive branch pair) =
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf value),
        C.toCwf.tmSub (eliminate localModel.sums A B M suppliedBranch) (selfExtend C.toCwf value)⟩ := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluateType (Γ.snoc A) body) (fun B =>
      bindResult (model.evaluateType (Γ.snoc (localModel.sums.operations.sigma A B)) motive)
        (fun M => sumEliminate? localModel A B M
          (model.evaluateTerm ((Γ.snoc A).snoc B) branch) (model.evaluateTerm Γ pair)))) = _
  rw [domainRead]
  change bindResult (model.evaluateType (Γ.snoc A) body) _ = _
  rw [bodyRead]
  change bindResult (model.evaluateType (Γ.snoc (localModel.sums.operations.sigma A B)) motive) _ = _
  rw [motiveRead]
  change sumEliminate? localModel A B M
    (model.evaluateTerm ((Γ.snoc A).snoc B) branch) (model.evaluateTerm Γ pair) = _
  rw [branchRead, pairRead]
  simp only [sumEliminate?, check?_supplied, bindResult]

omit domainRead bodyRead in
theorem evaluate_comprehension (domain : TypeExpr S n) (predicate : PropExpr S (n + 1))
    (A : C.toCwf.Ty Γ.1) (φ : localModel.doctrine.Predicate (C.toCwf.ext Γ.1 A))
    (domainRead : model.evaluateType Γ domain = some A)
    (predicateRead : model.evaluatePredicate (Γ.snoc A) predicate = some φ) :
    model.evaluateType Γ (.comprehension domain predicate) = some (localModel.refinements.refined A φ) := by
  change bindResult (model.evaluateType Γ domain) (fun A =>
    bindResult (model.evaluatePredicate (Γ.snoc A) predicate)
      (fun φ => some (localModel.refinements.refined A φ))) = _
  rw [domainRead]
  change bindResult (model.evaluatePredicate (Γ.snoc A) predicate) _ = _
  rw [predicateRead]
  rfl

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Abstract
