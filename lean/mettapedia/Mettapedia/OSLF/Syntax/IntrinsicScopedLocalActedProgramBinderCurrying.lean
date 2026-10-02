import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramDataProjections
import Mettapedia.OSLF.Syntax.CategoricalBindingPresheaf
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramData
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramBinderSubstitution
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramPartialSubstitutionLaws
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramPartialRepresentatives
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramMeaningRepresentatives

/-!
# Evaluation comparisons beneath authored binders

Actual evaluator and substitution comparisons retain the binder arguments
and ambient ordinary values as separate ordered context blocks. The pointed
meaning comparison supplies the ordinary evaluation part of binder currying.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

section ExtendedPoints
variable {C : Type*} [Category C] (M : Model S (Cᵒᵖ ⥤ Type w))

/-- Extended ordinary environments read the binder tuple first and then the
original ambient tuple, at every generalized stage. -/
theorem extendEnv_apply_join {Z : Cᵒᵖ ⥤ Type w} {Γ : Ctx S}
    (environment : M.Env Z Γ) (a : Cᵒᵖ) (z : Z.obj a) :
    ∀ (bs : Ctx S) (arguments : (M.ctx bs).obj a),
      (fun r v => (M.extendEnv bs environment r v).app a (arguments, z)) =
      SemanticContextualMetavariables.joinEnvironment
        (F := fun _ r => (M.sort r).obj a) (Δ := [])
        (fun _r v => (projectVar M.sort v).app a arguments)
        (fun r v => (environment r v).app a z)
  | [], _ => rfl
  | _ :: bs, arguments => by
      funext r v
      cases v with
      | zero => rfl
      | succ old =>
          exact congrFun (congrFun
            (extendEnv_apply_join environment a z bs arguments.2) r) old

/-- Reading a joined environment commutes with any sort-indexed map of
closed values. -/
theorem joinEnvironment_read
    {F G : Ctx S → S.Srt → Type*} {Δ : Ctx S}
    (read : ∀ r, F Δ r → G Δ r)
    {Γ : Ctx S} (environment : ∀ r, Var Γ r → F Δ r) :
    ∀ (bs : Ctx S) (arguments : ∀ r, Var bs r → F Δ r),
      (fun r v => read r (SemanticContextualMetavariables.joinEnvironment
        (F := F) (Δ := Δ) arguments environment r v)) =
      SemanticContextualMetavariables.joinEnvironment
        (F := G) (Δ := Δ) (fun r v => read r (arguments r v))
          (fun r v => read r (environment r v))
  | [], _ => rfl
  | _ :: bs, arguments => by
      funext r v
      cases v with
      | zero => rfl
      | succ old => exact congrFun (congrFun
          (joinEnvironment_read read environment bs (fun r v => arguments r (.succ v))) r) old
end ExtendedPoints

/-- Actual evaluation supplies ordinary substitution when its tuple has
the declared ordered coordinates. -/
theorem programEvaluation_partial
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} {s : S.Srt}
    (body : Z ⟶ program R equations Γ s)
    (environment : ∀ r, Var Γ r → (Z ⟶ program R equations [] r))
    (tuple : Z ⟶ contextOf (program R equations []) Γ)
    (coordinates : ∀ r (v : Var Γ r),
      tuple ≫ projectVar (program R equations []) v = environment r v) :
    lift tuple body ≫ (programExponential R equations Γ s).eval =
      partialSubstitutionMap R equations [] body environment := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro z
  apply (programClassEquiv.{w} R equations a.unop [] s).injective
  have evaluated := programExponential_eval_class R equations a.unop Γ s
    (tuple.app a z) (body.app a z)
  have envEq :
      (fun r (v : Var Γ r) => programClassEquiv.{w} R equations a.unop [] r
        ((projectVar (program R equations []) v).app a
          (tuple.app a z))) =
      (fun r v => programClassEquiv.{w} R equations a.unop [] r ((environment r v).app a z)) := by
    funext r v
    exact congrArg (programClassEquiv.{w} R equations a.unop [] r)
      (ConcreteCategory.congr_hom
        (NatTrans.congr_app (coordinates r v) a) z)
  change _ = (programClassEquiv.{w} R equations a.unop [] s)
    ((programClassEquiv.{w} R equations a.unop [] s).symm _)
  exact evaluated.trans ((congrArg (fun env =>
    (authoredEquationModelAt S equations a.unop.base.as).algebra.substitution.substitute
      env (programClassEquiv.{w} R equations a.unop Γ s (body.app a z))) envEq).trans
      ((programClassEquiv.{w} R equations a.unop [] s).apply_symm_apply _).symm)

section MeaningProjection
variable {D : Type*} [Category D] [CartesianMonoidalCategory D]
variable {F : Object S ⥤ D}

/-- The general meaning is its declared tuple-and-body evaluation. -/
theorem meaning_evaluation (data : PreservingData F)
    (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s) {Z : D}
    (assignment : Z ⟶ data.toModel.family X.arities)
    (environment : data.toModel.Env Z Γ) :
    (data.meaning term).value Z assignment environment =
      lift (data.toModel.tupleEnv environment)
        (assignment ≫ (data.famIso X.arities).inv ≫ F.map (termArrow term)) ≫
      data.toModel.eval Γ s := rfl
end MeaningProjection

/-- The assigned body reads as its independent raw instantiation. -/
theorem programRestrictionData_body_read
    (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s)
    {Z : Presheaf.{w} R equations}
    (assignment : Z ⟶ (programData R equations).toModel.family X.arities)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (raw : a.base.as ⟶ X)
    (read : (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
      (assignment.app (Opposite.op a) z)).down.base =
      (authoredEquationPresentation S equations).quotientFunctor.map raw) :
    programClassEquiv R equations a Γ s
      ((assignment ≫ ((programData R equations).famIso X.arities).inv ≫
        (programRestriction R equations).map (termArrow term)).app (Opposite.op a) z) =
      Quotient.mk _ (instInto raw term) := by
  have represented :
      (assignment ≫ ((programData R equations).famIso X.arities).inv ≫
        (programRestriction R equations).map (termArrow term)).app (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (instInto raw term)))) := by
    apply ULift.ext
    apply (programHomEquiv R equations a _).injective
    change (((programData R equations).famIso X.arities).inv.app (Opposite.op a)
      (assignment.app (Opposite.op a) z)).down.base ≫
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow term) = _
    rw [read]
    let Q := (authoredEquationPresentation S equations).quotientFunctor
    exact (Q.map_comp raw (termArrow term)).symm.trans
      (congrArg Q.map (assignment_comp_termArrow raw term))
  exact (congrArg (programClassEquiv R equations a Γ s) represented).trans
    (programClassEquiv_termArrow.{w} R equations a _)

/-- The actual meaning fills the supplied ordinary environment into the
independently assigned scoped program, in the genuine quotient clone. -/
theorem programRestrictionData_meaning_partial_apply
    (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s)
    {Z : Presheaf.{w} R equations}
    (assignment : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a)) :
    (((programData R equations).meaning term).value Z assignment environment).app (Opposite.op a) z =
      (partialSubstitutionMap R equations []
        (assignment ≫ ((programData R equations).famIso X.arities).inv ≫
          (programRestriction R equations).map (termArrow term)) environment).app (Opposite.op a) z := by
  obtain ⟨raw, env, assignmentRead, envRead⟩ :=
    programRestrictionData_meaning_representatives R equations X assignment environment a z
  have meaningRead := programRestrictionData_meaning_apply R equations X term
    assignment environment a z raw env assignmentRead envRead
  have bodyRead := programRestrictionData_body_read R equations X term assignment a z raw
    assignmentRead
  have environmentRead : ∀ r (v : Var Γ r),
      programClassEquiv.{w} R equations a [] r ((environment r v).app (Opposite.op a) z) =
        Quotient.mk _ (env r v) := by
    intro r v
    exact (congrArg (equationTermsRepresented (authoredEquationPresentation S equations)
      a.base.as [] r) (envRead r v)).trans rfl
  have partialRead := partialSubstitutionMap_apply_representative R equations []
    (assignment ≫ ((programData R equations).famIso X.arities).inv ≫
      (programRestriction R equations).map (termArrow term)) environment a z
      (instInto raw term) env bodyRead environmentRead
  exact meaningRead.trans partialRead.symm

/-- Uncurrying the partially filled scoped body supplies exactly the joined
binder and ambient environment. -/
theorem programEvaluation_uncurry_partial
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} (bs : Ctx S) {s : S.Srt}
    (body : Z ⟶ program R equations (bs ++ Γ) s)
    (environment : ∀ r, Var Γ r → (Z ⟶ program R equations [] r))
    (extended : ∀ r, Var (bs ++ Γ) r →
      (contextOf (program R equations []) bs ⊗ Z ⟶ program R equations [] r))
    (points : ∀ (a : (Classifier R equations)ᵒᵖ)
      (arguments : (contextOf (program R equations []) bs).obj a) (z : Z.obj a),
      (fun r v => programClassEquiv.{w} R equations a.unop [] r
        ((extended r v).app a (arguments, z))) =
      SemanticContextualMetavariables.joinEnvironment
        (F := (authoredEquationModelAt S equations a.unop.base.as).algebra.substitution.Carrier)
        (fun r v => programClassEquiv.{w} R equations a.unop [] r
          ((projectVar (program R equations []) v).app a arguments))
        (fun r v => programClassEquiv.{w} R equations a.unop [] r
          ((environment r v).app a z))) :
    (contextOf (program R equations []) bs ◁
      partialSubstitutionMap R equations bs body environment) ≫
        (programExponential R equations bs s).eval =
    partialSubstitutionMap R equations [] (snd _ _ ≫ body)
      extended := by
  apply NatTrans.ext
  funext a
  apply ConcreteCategory.hom_ext
  intro point
  rcases point with ⟨arguments, z⟩
  apply (programClassEquiv.{w} R equations a.unop [] s).injective
  let A := (authoredEquationModelAt S equations a.unop.base.as).algebra
  let read : ∀ r, (program R equations [] r).obj a → A.substitution.Carrier [] r :=
    fun r => programClassEquiv.{w} R equations a.unop [] r
  let ambient : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier Γ [] :=
    fun r v => read r ((environment r v).app a z)
  let argumentsEnv : BindingSubstitutionAlgebra.Environment S A.substitution.Carrier bs [] :=
    fun r v => read r ((projectVar (program R equations []) v).app a arguments)
  let value : A.substitution.Carrier (bs ++ Γ) s :=
    programClassEquiv.{w} R equations a.unop (bs ++ Γ) s (body.app a z)
  have evaluated := programExponential_eval_class R equations a.unop bs s arguments
    ((partialSubstitutionMap R equations bs body environment).app a z)
  have bodyRead : programClassEquiv.{w} R equations a.unop bs s
      ((partialSubstitutionMap R equations bs body environment).app a z) =
        partialSubstitute A bs ambient value :=
    (programClassEquiv.{w} R equations a.unop bs s).apply_symm_apply _
  have joined := points a arguments z
  have left := evaluated.trans ((congrArg (A.substitution.substitute argumentsEnv) bodyRead).trans
    (partialSubstitute_then_apply A bs ambient argumentsEnv value))
  have right : programClassEquiv.{w} R equations a.unop [] s
      ((partialSubstitutionMap R equations [] (snd _ _ ≫ body) extended).app a (arguments, z)) =
      A.substitution.substitute
        (fun r v => read r ((extended r v).app a (arguments, z))) value :=
    (programClassEquiv.{w} R equations a.unop [] s).apply_symm_apply _
  exact left.trans ((congrArg (fun env => A.substitution.substitute env value) joined).symm.trans
    right.symm)

/-- The actual binder extension supplies the ordered coordinates required
by the general retained-binder evaluation comparison. -/
theorem programData_extended_points
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} (bs : Ctx S)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : (Classifier R equations)ᵒᵖ)
    (arguments : (contextOf (program R equations []) bs).obj a) (z : Z.obj a) :
    (fun r v => programClassEquiv.{w} R equations a.unop [] r
      (((programData R equations).toModel.extendEnv bs environment r v).app a (arguments, z))) =
    SemanticContextualMetavariables.joinEnvironment
      (F := (authoredEquationModelAt S equations a.unop.base.as).algebra.substitution.Carrier)
      (fun r v => programClassEquiv.{w} R equations a.unop [] r
        ((projectVar (program R equations []) v).app a arguments))
      (fun r v => programClassEquiv.{w} R equations a.unop [] r
        ((environment r v).app a z)) := by
  let A := (authoredEquationModelAt S equations a.unop.base.as).algebra
  let read : ∀ r, (program R equations [] r).obj a → A.substitution.Carrier [] r :=
    fun r => programClassEquiv.{w} R equations a.unop [] r
  exact (congrArg (fun env => fun r v => read r (env r v))
    (extendEnv_apply_join (programData R equations).toModel environment a z bs arguments)).trans
    (joinEnvironment_read (F := fun _ r => (program R equations [] r).obj a)
      (G := A.substitution.Carrier) (Δ := []) read (fun r v => (environment r v).app a z) bs
      (fun r v => (projectVar (program R equations []) v).app a arguments))


/-- The actual meaning fills the supplied ordinary environment into the
independently assigned scoped program, as an equality of presheaf arrows. -/
theorem programRestrictionData_meaning_partial
    (X : Object S) {Γ : Ctx S} {s : S.Srt}
    (term : Term (withMetas S X.arities) Γ s)
    {Z : Presheaf.{w} R equations}
    (assignment : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ) :
    ((programData R equations).meaning term).value Z assignment environment =
      partialSubstitutionMap R equations []
        (assignment ≫ ((programData R equations).famIso X.arities).inv ≫
          (programRestriction R equations).map (termArrow term)) environment :=
  presheafHom_ext
    (programRestrictionData_meaning_partial_apply R equations X term assignment environment)


/-- Uncurrying the partially substituted body supplies the canonical extended
binder environment, with the retained binder block in its original order. -/
theorem partialSubstitutionMap_uncurry
    {Z : Presheaf.{w} R equations} {Γ : Ctx S} (bs : Ctx S) {s : S.Srt}
    (body : Z ⟶ program R equations (bs ++ Γ) s)
    (environment : (programData R equations).toModel.Env Z Γ) :
    ((programData R equations).toModel.ctx bs ◁
      partialSubstitutionMap R equations bs body environment) ≫
        (programExponential R equations bs s).eval =
    partialSubstitutionMap R equations [] (snd _ _ ≫ body)
      ((programData R equations).toModel.extendEnv bs environment) :=
  programEvaluation_uncurry_partial R equations bs body environment
    ((programData R equations).toModel.extendEnv bs environment)
    (programData_extended_points R equations bs environment)

/-- Currying the actual meaning under a binder extension is precisely the
partially substituted equation-class body. -/
theorem programRestrictionData_curry_meaning
    (X : Object S) {Γ : Ctx S} (bs : Ctx S) {s : S.Srt}
    (term : Term (withMetas S X.arities) (bs ++ Γ) s)
    {Z : Presheaf.{w} R equations}
    (assignment : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ) :
    (programData R equations).toModel.curry
      (((programData R equations).meaning term).value
        ((programData R equations).toModel.ctx bs ⊗ Z) (snd _ _ ≫ assignment)
        ((programData R equations).toModel.extendEnv bs environment)) =
      partialSubstitutionMap R equations bs
        (assignment ≫ ((programData R equations).famIso X.arities).inv ≫
          (programRestriction R equations).map (termArrow term)) environment := by
  apply (programData R equations).toModel.curry_unique
  rw [programRestrictionData_meaning_partial]
  exact partialSubstitutionMap_uncurry R equations bs _ environment

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
