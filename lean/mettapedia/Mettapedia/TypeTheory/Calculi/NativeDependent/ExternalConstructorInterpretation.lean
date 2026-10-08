import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalInterpretation

/-!
# Constructor interpretation and dependent readouts

Successful child evaluations earn the corresponding independently authored
constructor's model readout. Primitive arguments are interpreted by actual
dependent telescope checking. These are local realization theorems; the
simultaneous theorem for all generated equality and judgment derivations
requires declaration-header agreement and conversion coherence separately.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u c s t m

variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

variable (model : ModelData S C) {n : Nat} (Γ : Context C n)

theorem evaluate_family (symbol : S.TypeSymbol)
    (arguments : Fin (S.typeArity symbol) → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 (model.typeParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.typeParameters symbol).2.components σ index)) :
    model.evaluateType Γ (.family symbol arguments) = some (model.familyAt symbol σ) := by
  apply (model.evaluateType_eq_some_iff _ _ _).mpr
  have assembled := (Telescope.assemble?_eq_some_iff _ _ σ).mpr evaluated
  simp only [evaluateTypeLifted, assembled, bindResult_some]

theorem evaluate_primitive (symbol : S.TermSymbol)
    (arguments : Fin (S.termArity symbol) → TermExpr S n)
    (σ : C.toCwf.Sub Γ.1 (model.termParameters symbol).1)
    (evaluated : ∀ index, model.evaluateTerm Γ (arguments index) =
      some ((model.termParameters symbol).2.components σ index)) :
    model.evaluateTerm Γ (.primitive symbol arguments) = some (model.primitiveAt symbol σ) := by
  have assembled := (Telescope.assemble?_eq_some_iff _ _ σ).mpr evaluated
  simp only [evaluateTerm, assembled, bindResult_some]

variable (domain : TypeExpr S n) (body : TypeExpr S (n + 1))
  (A : C.toCwf.Ty Γ.1) (B : C.toCwf.Ty (C.toCwf.ext Γ.1 A))
  (domainEvaluated : model.evaluateType Γ domain = some A)
  (bodyEvaluated : model.evaluateType (Γ.snoc A) body = some B)

include domainEvaluated bodyEvaluated

theorem evaluate_pi : model.evaluateType Γ (.pi domain body) = some (model.products.pi A B) := by
  apply (model.evaluateType_eq_some_iff _ _ _).mpr
  simp only [evaluateTypeLifted, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated]

theorem evaluate_sigma : model.evaluateType Γ (.sigma domain body) =
    some (model.sums.operations.sigma A B) := by
  apply (model.evaluateType_eq_some_iff _ _ _).mpr
  simp only [evaluateTypeLifted, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated]

theorem evaluate_lambda (term : TermExpr S (n + 1))
    (value : C.toCwf.Tm (C.toCwf.ext Γ.1 A) B)
    (evaluated : model.evaluateTerm (Γ.snoc A) term = some ⟨B, value⟩) :
    model.evaluateTerm Γ (.lam domain body term) =
      some ⟨model.products.pi A B, model.products.lam value⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated, evaluated,
    ]
  exact model.lambda?_supplied A B value

theorem evaluate_application (function argument : TermExpr S n)
    (f : C.toCwf.Tm Γ.1 (model.products.pi A B)) (a : C.toCwf.Tm Γ.1 A)
    (functionEvaluated : model.evaluateTerm Γ function = some ⟨_, f⟩)
    (argumentEvaluated : model.evaluateTerm Γ argument = some ⟨_, a⟩) :
    model.evaluateTerm Γ (.app domain body function argument) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf a), model.products.app f a⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated,
    functionEvaluated, argumentEvaluated, application?_supplied]

theorem evaluate_pair (first second : TermExpr S n) (a : C.toCwf.Tm Γ.1 A)
    (b : C.toCwf.Tm Γ.1 (C.toCwf.tySub B (selfExtend C.toCwf a)))
    (firstEvaluated : model.evaluateTerm Γ first = some ⟨_, a⟩)
    (secondEvaluated : model.evaluateTerm Γ second = some ⟨_, b⟩) :
    model.evaluateTerm Γ (.pair domain body first second) =
      some ⟨model.sums.operations.sigma A B, model.sums.operations.pair a b⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated,
    firstEvaluated, secondEvaluated, pair?_supplied]

theorem evaluate_first (pair : TermExpr S n)
    (p : C.toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (evaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.fst domain body pair) = some ⟨A, model.sums.operations.fst p⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated, evaluated,
    first?_supplied]

theorem evaluate_second (pair : TermExpr S n)
    (p : C.toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (evaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.snd domain body pair) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf (model.sums.operations.fst p)),
        model.sums.operations.snd p⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated, evaluated,
    second?_supplied]

theorem evaluate_sumElimination (motive : TypeExpr S (n + 1))
    (branch : TermExpr S (n + 2)) (pair : TermExpr S n)
    (M : C.toCwf.Ty (C.toCwf.ext Γ.1 (model.sums.operations.sigma A B)))
    (b : C.toCwf.Tm (C.toCwf.ext (C.toCwf.ext Γ.1 A) B)
      (C.toCwf.tySub M (pack model.sums A B)))
    (p : C.toCwf.Tm Γ.1 (model.sums.operations.sigma A B))
    (motiveEvaluated : model.evaluateType (Γ.snoc (model.sums.operations.sigma A B)) motive = some M)
    (branchEvaluated : model.evaluateTerm ((Γ.snoc A).snoc B) branch = some ⟨_, b⟩)
    (pairEvaluated : model.evaluateTerm Γ pair = some ⟨_, p⟩) :
    model.evaluateTerm Γ (.sigmaElim domain body motive branch pair) =
      some ⟨C.toCwf.tySub M (selfExtend C.toCwf p),
        C.toCwf.tmSub (eliminate model.sums A B M b) (selfExtend C.toCwf p)⟩ := by
  simp only [evaluateTerm, (model.evaluateType_eq_some_iff _ _ _).mp domainEvaluated,
    bindResult_some, ULift.down_up, (model.evaluateType_eq_some_iff _ _ _).mp bodyEvaluated,
    (model.evaluateType_eq_some_iff _ _ _).mp motiveEvaluated, branchEvaluated, pairEvaluated,
    ]
  exact model.sumEliminate?_supplied A B M b p

/-- Local product beta is sufficient to validate the actual evaluated
application of a supplied lambda body. -/
theorem evaluated_lambda_beta (beta : PiBeta model.products)
    (term : TermExpr S (n + 1)) (argument : TermExpr S n)
    (value : C.toCwf.Tm (C.toCwf.ext Γ.1 A) B) (a : C.toCwf.Tm Γ.1 A)
    (termEvaluated : model.evaluateTerm (Γ.snoc A) term = some ⟨B, value⟩)
    (argumentEvaluated : model.evaluateTerm Γ argument = some ⟨A, a⟩) :
    model.evaluateTerm Γ (.app domain body (.lam domain body term) argument) =
      some ⟨C.toCwf.tySub B (selfExtend C.toCwf a), C.toCwf.tmSub value (selfExtend C.toCwf a)⟩ := by
  rw [model.evaluate_application Γ domain body A B domainEvaluated bodyEvaluated _ _ _ a
    (model.evaluate_lambda Γ domain body A B domainEvaluated bodyEvaluated term value termEvaluated)
    argumentEvaluated, beta]

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
