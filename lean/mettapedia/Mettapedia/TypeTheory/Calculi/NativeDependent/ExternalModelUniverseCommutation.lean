import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelUniverseLift

/-!
# Authored expression readouts through carrier lifts

Mutual induction visits every primitive argument and dependent annotation,
including the complete sum motive and both branch variables. Successful
readouts retain their actual types and supplied sections on lifted carriers.
No interpretation of a generated judgment is an assumption of this proof.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualSumComprehension
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

universe u c s t m uc vs wt ms
variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}}

namespace ModelData

mutual

theorem evaluateType_universeLift (model : ModelData S C) :
    {n : Nat} → (type : TypeExpr S n) → (Γ : Context C n) → (A : C.toCwf.Ty Γ.1) →
    model.evaluateType Γ type = some A →
    (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).evaluateType
      (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) type = some (ULift.up A)
  | _, .family symbol arguments, Γ, A, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rw [evaluateTypeLifted] at lifted
      rcases (bindResult_eq_some_iff _ _ _).mp lifted with ⟨σ, assembled, last⟩
      have actual : model.familyAt symbol σ = A := congrArg ULift.down (Option.some.inj last)
      rw [← actual]
      apply model.universeLift.evaluate_family (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) symbol arguments (ULift.up σ)
      intro index
      have read := Telescope.assemble?_sound _ _ σ assembled index
      exact (evaluateTerm_universeLift model (arguments index) Γ _ read).trans
        (congrArg some (liftTelescope_components.{c, s, t, m, uc, vs, wt, ms} (model.typeParameters symbol).2 σ index).symm)
  | _, .pi domain body, Γ, result, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (ULift.up (model.products.pi A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actual : model.products.pi A B = result := congrArg ULift.down (Option.some.inj last)
      rw [← actual]
      exact model.universeLift.evaluate_pi (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead)
  | _, .sigma domain body, Γ, result, evaluated => by
      have lifted := (model.evaluateType_eq_some_iff _ _ _).mp evaluated
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => some (ULift.up (model.sums.operations.sigma A B))) (ULift.up result)).mp lifted with
        ⟨A, B, domainRead, bodyRead, last⟩
      have actual : model.sums.operations.sigma A B = result := congrArg ULift.down (Option.some.inj last)
      rw [← actual]
      exact model.universeLift.evaluate_sigma (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead)

theorem evaluateTerm_universeLift (model : ModelData S C) :
    {n : Nat} → (term : TermExpr S n) → (Γ : Context C n) → (value : Value C.toCwf Γ.1) →
    model.evaluateTerm Γ term = some value →
    (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).evaluateTerm
      (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) term = some (liftValue.{c, s, t, m, uc, vs, wt, ms} value)
  | _, .var index, Γ, value, evaluated => by
      have actual : Γ.2.lookup index = value := Option.some.inj evaluated
      rw [← actual]
      exact congrArg some (liftTelescope_lookup Γ.2 index)
  | _, .primitive symbol arguments, Γ, value, evaluated => by
      rw [evaluateTerm] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨σ, assembled, last⟩
      have actual : model.primitiveAt symbol σ = value := Option.some.inj last
      rw [← actual]
      apply model.universeLift.evaluate_primitive (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) symbol arguments (ULift.up σ)
      intro index
      have read := Telescope.assemble?_sound _ _ σ assembled index
      exact (evaluateTerm_universeLift model (arguments index) Γ _ read).trans
        (congrArg some (liftTelescope_components.{c, s, t, m, uc, vs, wt, ms} (model.termParameters symbol).2 σ index).symm)
  | _, .lam domain body term, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => model.lambda? A B (model.evaluateTerm (Γ.snoc A) term)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [lambda?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, bodyChecked, _⟩
      have termRead := (check?_eq_some_iff _ _ _).mp bodyChecked
      rw [termRead, lambda?_supplied] at last
      have actual : (⟨model.products.pi A B, model.products.lam b⟩ : Value C.toCwf Γ.1) = value :=
        Option.some.inj last
      rw [← actual]
      exact model.universeLift.evaluate_lambda (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) term (ULift.up b)
        (evaluateTerm_universeLift model term (Γ.snoc A) _ termRead)
  | _, .app domain body function argument, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => model.application? A B (model.evaluateTerm Γ function)
          (model.evaluateTerm Γ argument)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [application?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨f, functionChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨a, argumentChecked, _⟩
      have functionRead := (check?_eq_some_iff _ _ _).mp functionChecked
      have argumentRead := (check?_eq_some_iff _ _ _).mp argumentChecked
      rw [functionRead, argumentRead, application?_supplied] at last
      rw [← Option.some.inj last]
      exact (model.universeLift.evaluate_application (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) function argument
        (ULift.up f) (ULift.up a)
        (evaluateTerm_universeLift model function Γ _ functionRead)
        (evaluateTerm_universeLift model argument Γ _ argumentRead)).trans
          (congrArg some (model.universeLift_application_value A B f a))
  | _, .pair domain body first second, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => model.pair? A B (model.evaluateTerm Γ first)
          (model.evaluateTerm Γ second)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [pair?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨a, firstChecked, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨b, secondChecked, _⟩
      have firstRead := (check?_eq_some_iff _ _ _).mp firstChecked
      have secondRead := (check?_eq_some_iff _ _ _).mp secondChecked
      rw [firstRead, secondRead, pair?_supplied] at last
      rw [← Option.some.inj last]
      rcases liftedValue_at_type.{c, s, t, m, uc, vs, wt, ms} (C.toCwf.tySub B (selfExtend C.toCwf a)) b
        ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up B) (selfExtend (Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf) (ULift.up a)))
        (congrArg (C.toCwf.tySub B) (selfExtend_readout.{c, s, t, m, uc, vs, wt, ms} (C := C.toCwf) (context := ULift.up Γ.1) (ULift.up a))) with ⟨b', valueRead, bodies⟩
      have secondImage := (evaluateTerm_universeLift model second Γ _ secondRead).trans
        (congrArg some valueRead)
      exact (model.universeLift.evaluate_pair (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) first second (ULift.up a) b'
        (evaluateTerm_universeLift model first Γ _ firstRead) secondImage).trans
          (congrArg some (model.universeLift_pair_value A B a b b' bodies))
  | _, .fst domain body pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => model.first? A B (model.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [first?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, first?_supplied] at last
      rw [← Option.some.inj last]
      exact model.universeLift.evaluate_first (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) pair (ULift.up p)
        (evaluateTerm_universeLift model pair Γ _ pairRead)
  | _, .snd domain body pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => model.second? A B (model.evaluateTerm Γ pair)) value).mp evaluated with
        ⟨A, B, domainRead, bodyRead, last⟩
      have checked := last
      rw [second?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨p, pairChecked, _⟩
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [pairRead, second?_supplied] at last
      rw [← Option.some.inj last]
      exact (model.universeLift.evaluate_second (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) pair (ULift.up p)
        (evaluateTerm_universeLift model pair Γ _ pairRead)).trans
          (congrArg some (model.universeLift_second_value A B p))
  | _, .sigmaElim domain body motive branch pair, Γ, value, evaluated => by
      rcases (model.dependentAnnotations_eq_some_iff Γ domain body
        (fun A B => bindResult
          (model.evaluateTypeLifted (Γ.snoc (model.sums.operations.sigma A B)) motive)
          (fun M => model.sumEliminate? A B M.down
            (model.evaluateTerm ((Γ.snoc A).snoc B) branch) (model.evaluateTerm Γ pair))) value).mp
              evaluated with ⟨A, B, domainRead, bodyRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨liftedM, motiveRead, last⟩
      let M := liftedM.down
      have motiveEvaluated := (model.evaluateType_eq_some_iff _ _ _).mpr motiveRead
      have checked := last
      rw [sumEliminate?] at checked
      rcases (bindResult_eq_some_iff _ _ _).mp checked with ⟨b, branchChecked, remaining⟩
      rcases (bindResult_eq_some_iff _ _ _).mp remaining with ⟨p, pairChecked, _⟩
      have branchRead := (check?_eq_some_iff _ _ _).mp branchChecked
      have pairRead := (check?_eq_some_iff _ _ _).mp pairChecked
      rw [branchRead, pairRead, sumEliminate?_supplied] at last
      rw [← Option.some.inj last]
      rcases liftedValue_at_type.{c, s, t, m, uc, vs, wt, ms} (C.toCwf.tySub M (pack model.sums A B)) b
        ((Raised.{c, s, t, m, uc, vs, wt, ms} C.toCwf).tySub (ULift.up M)
          (pack (Γ := ULift.up Γ.1) (liftStableSums model.sums) (ULift.up A) (ULift.up B)))
        (congrArg (C.toCwf.tySub M) (pack_down.{c, s, t, m, uc, vs, wt, ms} (C := C.toCwf) (Γ := ULift.up Γ.1) model.sums (ULift.up A) (ULift.up B))) with
          ⟨b', valueRead, branches⟩
      have branchImage := (evaluateTerm_universeLift model branch ((Γ.snoc A).snoc B) _ branchRead).trans
        (congrArg some valueRead)
      exact (model.universeLift.evaluate_sumElimination (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) domain body (ULift.up A) (ULift.up B)
        (evaluateType_universeLift model domain Γ A domainRead)
        (evaluateType_universeLift model body (Γ.snoc A) B bodyRead) motive branch pair (ULift.up M) b'
        (ULift.up p)
        (evaluateType_universeLift model motive (Γ.snoc (model.sums.operations.sigma A B)) M motiveEvaluated)
        branchImage (evaluateTerm_universeLift model pair Γ _ pairRead)).trans
          (congrArg some (model.universeLift_elimination_value A B M b b' branches p))

end

end ModelData
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
