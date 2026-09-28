import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalClosedInterpretation
import Mettapedia.OSLF.Syntax.IntrinsicLambdaFourRulePresentation
import Mettapedia.OSLF.Syntax.BindingFunctionArgumentComparison

/-!
# The lambda congruence premise as a nontrivial function pair

The authored abstraction-congruence rule places its child step under one
bound variable. A beta redex there and its contractum become two distinct
points of the appropriate presheaf function object. The operational step
relates them without quotienting their source syntax by beta.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.Chapter7ClosedBindingControl

open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.IntrinsicLambdaFourRulePresentation
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalClosedInterpretation
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.BindingFunctionArgumentComparison

private abbrev A := BindingCloneAlgebra.terms sig

/-- A beta redex using the abstraction variable. -/
def openRedex : Term sig [.term] .term :=
  appT (lamT (.var .zero)) (.var .zero)

/-- The child step of LamCong, retaining distinct source and target code. -/
def sampleValuation :
    Mettapedia.OSLF.Binding.SemanticContextualMetavariables.Valuation
      (M := metas) A [] :=
  valuationOf [] openRedex (.var .zero)
    (lamT (.var .zero)) (lamT (.var .zero)) (lamT (.var .zero))

def samplePremise :=
  (lamCong.premises.get ⟨0, by decide⟩)

def sampleFunctions :=
  premiseFunctions A sampleValuation
    (fun _ var => nomatch var :
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
        sig A.substitution.Carrier [] [])
    samplePremise

/-- The same open beta step is the actual authored child judgment. -/
theorem sample_child :
    Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation.interpretPremise
        A sampleValuation
        (fun _ var => nomatch var :
          Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
            sig A.substitution.Carrier [] [])
        samplePremise =
      ⟨[.term], .term, openRedex, (.var .zero : Term sig [.term] .term)⟩ := by
  change Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial.childJudgment
      rules A (lamCongOccurrence [] sampleValuation) ⟨0, by decide⟩ = _
  rw [lamCongChild]
  rfl

/-- The represented functions are distinct even though the source calculus
has a beta step between their bodies. -/
theorem sample_functions_distinct : sampleFunctions.1 ≠ sampleFunctions.2 := by
  intro same
  have bodySame := congrArg
    (scopedBodyEquiv A
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
        A.substitution.toClone []) [.term] .term) same
  have leftBody := (premiseFunctions_body A sampleValuation
    (fun _ var => nomatch var :
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
        sig A.substitution.Carrier [] []) samplePremise).1
  have rightBody := (premiseFunctions_body A sampleValuation
    (fun _ var => nomatch var :
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
        sig A.substitution.Carrier [] []) samplePremise).2
  have bodyEq :
      (Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation.interpretPremise
        A sampleValuation
        (fun _ var => nomatch var :
          Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
            sig A.substitution.Carrier [] [])
        samplePremise).2.2.1 =
      (Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation.interpretPremise
        A sampleValuation
        (fun _ var => nomatch var :
          Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
            sig A.substitution.Carrier [] [])
        samplePremise).2.2.2 :=
    leftBody.symm.trans (bodySame.trans rightBody)
  rw [sample_child] at bodyEq
  cases bodyEq

/-- The source reduction still relates those distinct bodies. -/
theorem sample_body_step : LambdaContextualRung.Step [.term]
    openRedex (.var .zero) :=
  open_beta_uses_bound_variable

/-- The source of LamCong as an actual authored lambda constructor applied
to a contextual function argument. -/
def sampleLamSource : FunctionArgs A (sig.arity Op.lam) [] :=
  .cons sampleFunctions.1 .nil

/-- The target retains the separate firing endpoint. -/
def sampleLamTarget : FunctionArgs A (sig.arity Op.lam) [] :=
  .cons sampleFunctions.2 .nil

theorem sampleLamSource_code :
    applyFunctionArgs A Op.lam sampleLamSource = lamT openRedex := by
  have hBody := (premiseFunctions_body A sampleValuation
    (fun _ var => nomatch var :
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
        sig A.substitution.Carrier [] []) samplePremise).1
  have hEndpoint :
      (Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation.interpretPremise
        A sampleValuation
        (fun _ var => nomatch var :
          Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
            sig A.substitution.Carrier [] []) samplePremise).2.2.1 =
      openRedex := by rfl
  change lamT
    ((scopedBodyEquiv A
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
        A.substitution.toClone []) [.term] .term) sampleFunctions.1) = _
  exact congrArg lamT (hBody.trans hEndpoint)

theorem sampleLamTarget_code :
    applyFunctionArgs A Op.lam sampleLamTarget =
      lamT (.var .zero : Term sig [.term] .term) := by
  have hBody := (premiseFunctions_body A sampleValuation
    (fun _ var => nomatch var :
      Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
        sig A.substitution.Carrier [] []) samplePremise).2
  have hEndpoint :
      (Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation.interpretPremise
        A sampleValuation
        (fun _ var => nomatch var :
          Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra.Environment
            sig A.substitution.Carrier [] []) samplePremise).2.2.2 =
      (.var .zero : Term sig [.term] .term) := by rfl
  change lamT
    ((scopedBodyEquiv A
      (Mettapedia.GSLT.LanguageDef.MultiSortedClone.ContextObject.ofList
        A.substitution.toClone []) [.term] .term) sampleFunctions.2) = _
  exact congrArg lamT (hBody.trans hEndpoint)

/-- The operational LamCong event relates two distinct interpreted lambda
programs; it is not an equation imposed by semantic currying. -/
theorem sampleLam_function_step :
    LambdaContextualRung.Step []
      (applyFunctionArgs A Op.lam sampleLamSource)
      (applyFunctionArgs A Op.lam sampleLamTarget) := by
  rw [sampleLamSource_code, sampleLamTarget_code]
  exact .lamCong sample_body_step

#print axioms sample_functions_distinct
#print axioms sample_body_step
#print axioms sampleLam_function_step

end Mettapedia.OSLF.Binding.Chapter7ClosedBindingControl
