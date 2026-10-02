import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningApplication

/-!
# Representatives of generalized program valuations

The actual equation quotient supplies representatives for every program
assignment and every ordinary-variable environment. These independent
representatives support the evaluator computation at every classifier stage.
-/

set_option autoImplicit false

noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoricalBindingModel SecondOrderContext IntrinsicScopedLocalActedClassifier
open IntrinsicScopedLocalPolynomial
universe w
variable {S : Signature} {K : List (MetaArity S)}

/-- Every equation-class term arrow has an actual raw term representative,
for every coherent equation presentation. -/
theorem quotientTerm_representative (P : EquationPresentation S K)
    (X : Object S) (Γ : Ctx S) (s : S.Srt)
    (f : P.quotientFunctor.obj X ⟶ P.quotientFunctor.obj (oneObj Γ s)) :
    ∃ term : Term (withMetas S X.arities) Γ s,
      P.quotientFunctor.map (termArrow term) = f := by
  let : P.quotientFunctor.Full := _root_.CategoryTheory.Quotient.full_functor P.homRel
  let raw : X ⟶ oneObj Γ s := P.quotientFunctor.preimage f
  let term : Term (withMetas S X.arities) Γ s := raw ⟨0, Nat.zero_lt_one⟩
  have same : termArrow term = raw := oneObj_hom_ext rfl
  exact ⟨term, (congrArg P.quotientFunctor.map same).trans (P.quotientFunctor.map_preimage f)⟩

variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- The independent representatives needed by the application computation
exist for every generalized valuation and at every operational stage. -/
theorem programRestrictionData_meaning_representatives
    (X : Object S) {Z : Presheaf.{w} R equations} {Γ : Ctx S}
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a)) :
    ∃ (assignment : a.base.as ⟶ X)
      (env : Sub (withMetas S a.base.as.arities) Γ []),
      (((programData R equations).famIso
        X.arities).inv.app (Opposite.op a) (assignmentPoint.app (Opposite.op a) z)).down.base =
          (authoredEquationPresentation S equations).quotientFunctor.map assignment ∧
      ∀ r (v : Var Γ r),
        ((environment r v).app (Opposite.op a) z).down.base =
          (authoredEquationPresentation S equations).quotientFunctor.map
            (termArrow (env r v)) := by
  let P := authoredEquationPresentation S equations
  let : P.quotientFunctor.Full := _root_.CategoryTheory.Quotient.full_functor P.homRel
  let point := ((programData R equations).famIso
    X.arities).inv.app (Opposite.op a) (assignmentPoint.app (Opposite.op a) z)
  let assignment : a.base.as ⟶ X := P.quotientFunctor.preimage point.down.base
  let env : Sub (withMetas S a.base.as.arities) Γ [] := fun r v =>
    Classical.choose (quotientTerm_representative P a.base.as [] r
      ((environment r v).app (Opposite.op a) z).down.base)
  refine ⟨assignment, env, ?_, ?_⟩
  · exact (P.quotientFunctor.map_preimage point.down.base).symm
  · intro r v
    exact (Classical.choose_spec (quotientTerm_representative P a.base.as [] r
      ((environment r v).app (Opposite.op a) z).down.base)).symm

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
