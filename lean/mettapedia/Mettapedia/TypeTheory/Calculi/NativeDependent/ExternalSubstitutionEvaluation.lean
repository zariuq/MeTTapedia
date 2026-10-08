import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSubstitutionInterpretation

/-!
# Interpretation commutes with authored substitution

Mutual induction traverses every external type and term constructor. A
successful source evaluation commutes with an actual model substitution whose
component sections are evaluated. Binder maps, dependent pair witnesses and
full sum motives use their earned contextual substitution equations.
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

mutual

theorem evaluateType_substitute (model : ModelData S C) (stable : StrictPiSubstitution model.products) :
    {n k : Nat} → (type : TypeExpr S n) → (Γ : Context C k) → (Δ : Context C n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (A : C.toCwf.Ty Δ.1) → model.evaluateType Δ type = some A →
    model.evaluateType Γ (type.substitute substitution) = some (C.toCwf.tySub A modelMap.arrow)
  | _, _, .family symbol arguments, Γ, Δ, substitution, modelMap, A, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [evaluateTypeLifted] at lifted
      rcases (bindResult_eq_some_iff _ _ _).mp lifted with ⟨actual, assembled, last⟩
      have sourceType : model.familyAt symbol actual = A :=
        congrArg ULift.down (Option.some.inj last)
      have argumentsRead := Telescope.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.typeParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [Telescope.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TypeExpr.substitute, ← sourceType, model.familyAt_substitution]
      exact model.evaluate_family Γ _ _ _ targetRead
  | _, _, .pi domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (ULift.up (model.products.pi A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : model.products.pi A B = result := congrArg ULift.down (Option.some.inj last)
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, stable.1]
      exact model.evaluate_pi Γ _ _ _ _ domainSubstituted bodySubstituted
  | _, _, .sigma domain body, Γ, Δ, substitution, modelMap, result, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => some (ULift.up (model.sums.operations.sigma A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have sourceType : model.sums.operations.sigma A B = result :=
        congrArg ULift.down (Option.some.inj last)
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      rw [TypeExpr.substitute, ← sourceType, model.sums.substitution.1]
      exact model.evaluate_sigma Γ _ _ _ _ domainSubstituted bodySubstituted

theorem evaluateTerm_substitute (model : ModelData S C) (stable : StrictPiSubstitution model.products) :
    {n k : Nat} → (term : TermExpr S n) → (Γ : Context C k) → (Δ : Context C n) →
    (substitution : Substitution S n k) → (modelMap : ModelSubstitution model Γ Δ substitution) →
    (value : Value C.toCwf Δ.1) → model.evaluateTerm Δ term = some value →
    model.evaluateTerm Γ (term.substitute substitution) = some (value.substitute modelMap.arrow)
  | _, _, .var index, Γ, Δ, substitution, modelMap, value, evaluated => by
      have actual : Δ.2.lookup index = value := Option.some.inj evaluated
      rw [TermExpr.substitute, ← actual]
      exact modelMap.readout index
  | _, _, .primitive symbol arguments, Γ, Δ, substitution, modelMap, value, evaluated => by
      rw [evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨actual, assembled, last⟩
      have actualValue : model.primitiveAt symbol actual = value := Option.some.inj last
      have argumentsRead := Telescope.assemble?_sound _ _ actual assembled
      have targetRead : ∀ index, model.evaluateTerm Γ ((arguments index).substitute substitution) =
          some ((model.termParameters symbol).2.components
            (C.toCwf.compS actual modelMap.arrow) index) := by
        intro index
        rw [Telescope.components_composition]
        exact evaluateTerm_substitute model stable (arguments index) Γ Δ substitution modelMap _
          (argumentsRead index)
      rw [TermExpr.substitute, ← actualValue, model.primitiveAt_substitution]
      exact model.evaluate_primitive Γ _ _ _ targetRead
  | _, _, .lam domain body term, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.lambda? A B (model.evaluateTerm (Δ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨bodyValue, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have termSubstituted := evaluateTerm_substitute model stable term _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) ⟨B, bodyValue⟩ termRead
      have target := model.evaluate_lambda Γ _ _ _ _ domainSubstituted bodySubstituted _ _ termSubstituted
      have commute := model.lambda?_substitution stable modelMap.arrow A B bodyValue
      rw [termRead] at last
      rw [last, Option.map_some, lambda?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .app domain body function argument, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.application? A B (model.evaluateTerm Δ function)
          (model.evaluateTerm Δ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (check?_eq_some_iff _ _ _).mp argumentChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have functionSubstituted := evaluateTerm_substitute model stable function Γ Δ substitution modelMap _ functionRead
      rw [model.product_value_substitute stable modelMap.arrow A B f] at functionSubstituted
      have argumentSubstituted := evaluateTerm_substitute model stable argument Γ Δ substitution modelMap _ argumentRead
      have target := model.evaluate_application Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _
        functionSubstituted argumentSubstituted
      have commute := model.application?_substitution stable modelMap.arrow A B f a
      rw [functionRead, argumentRead] at last
      rw [last, Option.map_some, application?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .pair domain body first second, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.pair? A B (model.evaluateTerm Δ first)
          (model.evaluateTerm Δ second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (check?_eq_some_iff _ _ _).mp secondChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have firstSubstituted := evaluateTerm_substitute model stable first Γ Δ substitution modelMap _ firstRead
      have secondSubstituted := evaluateTerm_substitute model stable second Γ Δ substitution modelMap _ secondRead
      rw [second_value_substitute modelMap.arrow A B a b] at secondSubstituted
      have target := model.evaluate_pair Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _
        firstSubstituted secondSubstituted
      have commute := model.pair?_substitution modelMap.arrow A B a b
      rw [firstRead, secondRead] at last
      rw [last, Option.map_some, pair?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .fst domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.first? A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_first Γ _ _ _ _ domainSubstituted bodySubstituted _ _ pairSubstituted
      have commute := model.first?_substitution modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, first?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .snd domain body pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => model.second? A B (model.evaluateTerm Δ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_second Γ _ _ _ _ domainSubstituted bodySubstituted _ _ pairSubstituted
      have commute := model.second?_substitution modelMap.arrow A B p
      rw [pairRead] at last
      rw [last, Option.map_some, second?_supplied] at commute
      exact target.trans commute.symm
  | _, _, .sigmaElim domain body motive branch pair, Γ, Δ, substitution, modelMap, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Δ domain body
        (fun A B => bindResult (model.evaluateTypeLifted
          (Δ.snoc (model.sums.operations.sigma A B)) motive) (fun M =>
          model.sumEliminate? A B M.down (model.evaluateTerm ((Δ.snoc A).snoc B) branch)
            (model.evaluateTerm Δ pair))) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, motiveStep⟩
      rcases (bindResult_eq_some_iff _ _ _).mp motiveStep with ⟨liftedM, motiveRead, last⟩
      let M := liftedM.down
      have motiveEvaluated : model.evaluateType (Δ.snoc (model.sums.operations.sigma A B)) motive = some M :=
        (model.evaluateType_eq_some_iff _ _ _).mpr motiveRead
      have checked := last
      rw [sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨p, pairChecked, _⟩
      have branchRead := (check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      have domainSubstituted := evaluateType_substitute model stable domain Γ Δ substitution modelMap A domainRead
      have bodySubstituted := evaluateType_substitute model stable body _ _ (liftSubstitution substitution)
        (modelMap.lift stable A) B bodyRead
      let newSum := model.sums.operations.sigma (C.toCwf.tySub A modelMap.arrow)
        (C.toCwf.tySub B (TypeOver.extensionSubstitution modelMap.arrow A))
      let motiveMap := modelMap.liftAlong stable (model.sums.operations.sigma A B) newSum
        (model.sums.substitution.1 modelMap.arrow A B)
      have motiveArrow : motiveMap.arrow = sumReindex model.sums modelMap.arrow A B :=
        modelMap.liftAlong_arrow stable _ _ _
      have motiveSubstituted := evaluateType_substitute model stable motive _ _ (liftSubstitution substitution)
        motiveMap M motiveEvaluated
      rw [motiveArrow] at motiveSubstituted
      have branchSubstituted := evaluateTerm_substitute model stable branch _ _
        (liftSubstitution (liftSubstitution substitution)) ((modelMap.lift stable A).lift stable B) _ branchRead
      have branchValue : Value.substitute
          (⟨_, b⟩ : Value C.toCwf ((Δ.snoc A).snoc B).1)
          (tupleReindex modelMap.arrow A B) =
          ⟨_, reindexBody model.sums modelMap.arrow A B M b⟩ :=
        Sigma.ext (reindexBody_type model.sums modelMap.arrow A B M)
          (reindexBody_heq _ _ _ _ _ _).symm
      change model.evaluateTerm
        ((Γ.snoc (C.toCwf.tySub A modelMap.arrow)).snoc
          (C.toCwf.tySub B (TypeOver.extensionSubstitution modelMap.arrow A)))
        (branch.substitute (liftSubstitution (liftSubstitution substitution))) =
        some (Value.substitute (⟨_, b⟩ : Value C.toCwf ((Δ.snoc A).snoc B).1)
          (tupleReindex modelMap.arrow A B)) at branchSubstituted
      rw [branchValue] at branchSubstituted
      have pairSubstituted := evaluateTerm_substitute model stable pair Γ Δ substitution modelMap _ pairRead
      rw [model.sum_value_substitute modelMap.arrow A B p] at pairSubstituted
      have target := model.evaluate_sumElimination Γ _ _ _ _ domainSubstituted bodySubstituted _ _ _ _ _ _
        motiveSubstituted branchSubstituted pairSubstituted
      have commute := model.sumEliminate?_substitution modelMap.arrow A B M b p
      rw [branchRead, pairRead] at last
      rw [last, Option.map_some, sumEliminate?_supplied] at commute
      exact target.trans commute.symm

end

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
