import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramBinderSubstitution

/-!
# Independent representatives of partially filled program bodies

The existing quotient projection preserves retained-binder substitution.
Consequently the raw representative of a partially filled body is obtained
by the established capture-avoiding substitution, with local binders kept.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
universe w u
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- Restricting the freely extended signature leaves partial ordinary
substitution unchanged. -/
theorem partialSubstitute_restrict (X : Object S)
    (A : BindingCloneAlgebra.Algebra.{u} (withMetas S X.arities))
    {Γ : Ctx S} (bs : Ctx S)
    (environment : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [])
    {s : S.Srt} (body : A.substitution.Carrier (bs ++ Γ) s) :
    partialSubstitute (restrictAlgebra X A) bs environment body =
      partialSubstitute A bs environment body := by
  unfold partialSubstitute liftClosedEnvironment
  change A.substitution.substitute
    (fun r v => (List.append_nil bs) ▸
      (restrictSubstitution X A).liftEnvironment environment bs r v) body = _
  rw [restrict_liftEnvironment]

/-- The actual quotient projection preserves partial substitution beneath
all authored binder lists. -/
theorem partialSubstitute_quotient_mk
    {T : Signature} {M : List (MetaArity T)} (E : List (EqAxiom T M))
    {Γ : Ctx T} (bs : Ctx T) (environment : Sub T Γ []) {s : T.Srt}
    (body : Term T (bs ++ Γ) s) :
    partialSubstitute (BindingEquationQuotientModel.algebra E) bs
      (fun r v => Quotient.mk _ (environment r v)) (Quotient.mk _ body) =
      (Quotient.mk _ (partialSubstitute (BindingCloneAlgebra.terms T) bs environment body) :
        TermQ E bs s) :=
  (partialSubstitute_map (BindingEquationQuotientModel.projection E) bs environment body).symm

/-- The restricted authored stage has the same representative computation
as its full freely extended equation quotient. -/
theorem partialSubstitute_authored_mk (X : Object S)
    {Γ : Ctx S} (bs : Ctx S) (environment : Sub (withMetas S X.arities) Γ [])
    {s : S.Srt} (body : Term (withMetas S X.arities) (bs ++ Γ) s) :
    partialSubstitute (authoredEquationModelAt S equations X).algebra bs
      (fun r v => Quotient.mk _ (environment r v)) (Quotient.mk _ body) =
      (Quotient.mk _ (partialSubstitute (BindingCloneAlgebra.terms (withMetas S X.arities))
        bs environment body) : TermQ ((authoredEquationPresentation S equations).axioms X) bs s) :=
  (partialSubstitute_restrict X _ bs _ _).trans
    (partialSubstitute_quotient_mk ((authoredEquationPresentation S equations).axioms X)
      bs environment body)

/-- Read a partial program map using arbitrary independent representatives
of the body and each ordinary ambient coordinate. -/
theorem partialSubstitutionMap_apply_representative
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} (bs : Ctx S) {s : S.Srt}
    (body : Z ⟶ program R equations (bs ++ Γ) s)
    (environment : ∀ r, Var Γ r → (Z ⟶ program R equations [] r))
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (term : Term (withMetas S a.base.as.arities) (bs ++ Γ) s)
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (bodyRead : programClassEquiv R equations a (bs ++ Γ) s
      (body.app (Opposite.op a) z) = Quotient.mk _ term)
    (envRead : ∀ r (v : Var Γ r), programClassEquiv R equations a [] r
      ((environment r v).app (Opposite.op a) z) = Quotient.mk _ (env r v)) :
    (partialSubstitutionMap R equations bs body environment).app (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (partialSubstitute (BindingCloneAlgebra.terms
            (withMetas S a.base.as.arities)) bs env term)))) := by
  apply (programClassEquiv R equations a bs s).injective
  have read : (fun r v => programClassEquiv R equations a [] r
      ((environment r v).app (Opposite.op a) z)) = fun r v => Quotient.mk _ (env r v) :=
    funext fun r => funext fun v => envRead r v
  have substituteRead := congrArg₂
    (fun (environment : BindingSubstitutionAlgebra.Environment S
      (authoredEquationModelAt S equations a.base.as).algebra.substitution.Carrier Γ [])
      (value : (authoredEquationModelAt S equations a.base.as).algebra.substitution.Carrier
        (bs ++ Γ) s) =>
      partialSubstitute (authoredEquationModelAt S equations a.base.as).algebra bs environment value)
    read bodyRead
  exact ((programClassEquiv R equations a bs s).apply_symm_apply _).trans
    (substituteRead.trans ((partialSubstitute_authored_mk equations a.base.as bs env term).trans
      (programClassEquiv_termArrow.{w} R equations a _).symm))

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
