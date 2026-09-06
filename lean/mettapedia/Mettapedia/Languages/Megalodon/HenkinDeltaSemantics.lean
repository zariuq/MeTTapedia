import Mettapedia.Languages.Megalodon.HenkinDeltaInterpretation
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# Henkin semantics of successful native definition unfolding

Native body checking supplies an intrinsic term, not an equation in every model.
The independent declaration equations below identify each defined constant with
its checked body in a chosen Henkin model. They imply literal denotation
preservation for every successful finite-fuel unfolding, including open terms.

Only closure under typed terms is needed; the admissible function domains may be
proper Henkin domains. No termination, acyclicity, or success assertion is made.
At fixed fuel the exact preservation criterion concerns successful replacements
only, and therefore does not silently assert equations for unavailable bodies.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation

open MathdataKernel
open Mettapedia.Logic.HOL

universe w

variable {environment : Environment} {Γ : Ctx Base} {τ : Ty Base}

/-- The denotation of each eligible defined name is independently required to
equal its checked body's denotation. This is a model condition, not a typing rule. -/
structure DefinitionEquations (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment)) : Prop where
  equation : ∀ {type : Ty Base} (name : Name) (declaration : TermDecl)
    (lookup : environment.lookupTerm? name = some declaration)
    (typed : declaration.type = reifyType type) (body : Tm)
    (defined : declaration.definition = some body),
    M.constDen (.named name declaration lookup typed) =
      M.denote (checked.interpretBody name declaration lookup typed body defined)
        (fun v => nomatch v)

/-- Finite-fuel expansion of one constant preserves its denotation whenever it
succeeds, using the declaration equation at each actual unfolding. -/
theorem denote_deltaConstants
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M) (fuel : Nat)
    {type : Ty Base} (constant : Constant environment type)
    (result : ClosedTerm (Constant environment) type)
    (success : deltaConstants checked fuel constant = some result) :
    M.denote result (fun v => nomatch v) = M.constDen constant := by
  induction fuel generalizing type with
  | zero =>
      cases constant with
      | primitive index lookup =>
          simp only [deltaConstants, Option.some.injEq] at success
          subst result
          rfl
      | named name declaration lookup typed =>
          cases defined : declaration.definition with
          | none =>
              simp only [deltaConstants, defined, Option.some.injEq] at success
              subst result
              rfl
          | some body => simp [deltaConstants, defined] at success
  | succ fuel ih =>
      cases constant with
      | primitive index lookup =>
          simp only [deltaConstants, Option.some.injEq] at success
          subst result
          rfl
      | named name declaration lookup typed =>
          simp only [deltaConstants] at success
          split at success
          next defined =>
            cases Option.some.inj success
            rfl
          next body defined =>
              have compared := M.denote_substConst?_of_constantAgreement
                (deltaConstants checked fuel)
                (fun constant replacement available =>
                  (M.denote_closed_valuation_eq replacement _ _).trans
                    (ih constant replacement available))
                (checked.interpretBody name declaration lookup typed body defined)
                result success (fun v => nomatch v)
              exact compared.trans
                ((M.denote_closed_valuation_eq _ _ _).trans
                  (equations.equation name declaration lookup typed body defined).symm)

/-- Successful native delta interpretation preserves literal denotation in the
chosen model. Neither full function domains nor admissibility of the valuation
is needed for this syntactic substitution comparison. -/
theorem denote_deltaInterpretation
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M) (fuel : Nat)
    (term result : Term (Constant environment) Γ τ)
    (success : deltaInterpretation checked fuel term = some result)
    (valuation : M.Valuation Γ) : M.denote result valuation = M.denote term valuation :=
  M.denote_substConst?_of_constantAgreement (deltaConstants checked fuel)
    (fun constant replacement available =>
      (M.denote_closed_valuation_eq replacement _ _).trans
        (denote_deltaConstants checked M equations fuel constant replacement available))
    term result success valuation

/-- At proposition type, successful unfolding preserves satisfaction exactly. -/
theorem models_deltaInterpretation
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment))
    (equations : DefinitionEquations checked M) (fuel : Nat)
    (formula result : ClosedFormula (Constant environment))
    (success : deltaInterpretation checked fuel formula = some result) :
    M.models result ↔ M.models formula := by
  change (M.denote result _).down ↔ (M.denote formula _).down
  apply Eq.to_iff
  apply congrArg ULift.down
  exact (M.denote_closed_valuation_eq result _ _).trans
    ((denote_deltaInterpretation checked M equations fuel formula result success
      (fun v => nomatch v)).trans (M.denote_closed_valuation_eq formula _ _))

/-- The exact fixed-fuel criterion tests individual successful constant
replacements. It does not infer declaration equations from typing or failure. -/
theorem deltaInterpretation_preserves_denotation_iff
    (checked : CheckedPlainDefinitions environment)
    (M : HenkinModel.{0, 0, w} Base (Constant environment)) (fuel : Nat) :
    (∀ {context : Ctx Base} {type : Ty Base}
      (term result : Term (Constant environment) context type),
      deltaInterpretation checked fuel term = some result →
        ∀ valuation : M.Valuation context, M.denote result valuation = M.denote term valuation) ↔
    (∀ {type : Ty Base} (constant : Constant environment type)
      (result : ClosedTerm (Constant environment) type),
      deltaConstants checked fuel constant = some result →
        M.denote result (fun v => nomatch v) = M.constDen constant) := by
  constructor
  · intro preserves type constant result success
    apply preserves (.const constant) result _ (fun v => nomatch v)
    simp [deltaInterpretation, substConst?, success, weakenCtx]
  · intro constants context type term result success valuation
    exact M.denote_substConst?_of_constantAgreement (deltaConstants checked fuel)
      (fun constant replacement available =>
        (M.denote_closed_valuation_eq replacement _ _).trans
          (constants constant replacement available)) term result success valuation

#print axioms denote_deltaConstants
#print axioms denote_deltaInterpretation
#print axioms models_deltaInterpretation
#print axioms deltaInterpretation_preserves_denotation_iff

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation
