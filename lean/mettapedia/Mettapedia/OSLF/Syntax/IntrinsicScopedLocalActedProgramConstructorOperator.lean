import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramArgumentProjection
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedProgramBinderCurrying

/-!
# Authored operator construction in the operational Yoneda interpretation

Each actual semantic argument component is the meaning of its authored body
curried under that body's own binder list. Reading all ordered components
identifies the complete tuple with the generic argument assignment. Applying
the actual generic operator arrow then gives the authored operator constructor.

The comparison uses independent representatives of metavariable assignments
and ordinary environments at every generalized presheaf stage. These reads
cover every valuation, including stages that contain operational event variables.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open CategoricalBindingModel SecondOrderContext
open IntrinsicScopedLocalCongruence (getArg)
open IntrinsicScopedLocalPolynomial IntrinsicScopedLocalActedClassifier
universe w
variable {S : Signature} {K : List (MetaArity S)}
variable (R : List (LocalRule S)) (equations : List (EqAxiom S K))

/-- Every ordinary coordinate reads as its chosen representative class. -/
theorem programEnvironment_representative_class
    {Z : Presheaf.{w} R equations} {Γ : Ctx S}
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (read : ∀ r (var : Var Γ r), ((environment r var).app (Opposite.op a) z).down.base =
      (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env r var))) :
    ∀ r (var : Var Γ r), programClassEquiv R equations a [] r
      ((environment r var).app (Opposite.op a) z) = Quotient.mk _ (env r var) := by
  intro r var
  have pointEq : (environment r var).app (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (env r var)))) := by
    apply ULift.ext
    apply (programHomEquiv R equations a _).injective
    exact read r var
  exact (congrArg (programClassEquiv R equations a [] r) pointEq).trans
    (programClassEquiv_termArrow.{w} R equations a (env r var))

/-- The actual argument tuple's ordered component reads as the body
filled beneath its own binder list, with the old assignment independent. -/
theorem programTupleArgs_component_representative
    (X : Object S) {Γ : Ctx S} {arity : List (MetaArity S)}
    (args : Args (withMetas S X.arities) arity Γ)
    {Z : Presheaf.{w} R equations}
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (assignment : a.base.as ⟶ X)
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (readAssignment : (((programData R equations).famIso X.arities).inv.app
      (Opposite.op a) (assignmentPoint.app (Opposite.op a) z)).down.base =
      (authoredEquationPresentation S equations).quotientFunctor.map assignment)
    (readEnvironment : ∀ r (var : Var Γ r),
      ((environment r var).app (Opposite.op a) z).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env r var)))
    (i : Fin arity.length) :
    ((programData R equations).toModel.tupleArgs
      (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args)) Z assignmentPoint environment ≫
      (programData R equations).toModel.familyProj arity i).app (Opposite.op a) z =
    ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow ((closedArgsAssignment (bindArgs env (instIntoArgs assignment args))) i)))) := by
  let bs := (arity.get i).1
  let body := getArg args i
  let actualBody := assignmentPoint ≫ ((programData R equations).famIso X.arities).inv ≫
    (programRestriction R equations).map (termArrow body)
  have projected := tupleArgs_meaning_proj (programData R equations) X args Z
    assignmentPoint environment i
  have curried := programRestrictionData_curry_meaning R equations X bs body
    assignmentPoint environment
  have bodyRead := programRestrictionData_body_read R equations X body assignmentPoint a z
    assignment readAssignment
  have envRead := programEnvironment_representative_class R equations environment a z env
    readEnvironment
  have partialRead := partialSubstitutionMap_apply_representative R equations bs actualBody environment
    a z (instInto assignment body) env bodyRead envRead
  have rawBody : partialSubstitute (BindingCloneAlgebra.terms (withMetas S a.base.as.arities))
      bs env (instInto assignment body) =
      (closedArgsAssignment (bindArgs env (instIntoArgs assignment args))) i := by
    change _ = unScope (S := withMetas S a.base.as.arities) bs
      (getArg (bindArgs env (instIntoArgs assignment args)) i)
    rw [getArg_bindArgs, getArg_instIntoArgs]
    exact partialSubstitute_terms_unScope (T := withMetas S a.base.as.arities)
      bs env (instInto assignment body)
  have arrowEquality := projected.trans curried
  have atPoint := ConcreteCategory.congr_hom (NatTrans.congr_app arrowEquality (Opposite.op a)) z
  exact atPoint.trans (partialRead.trans (congrArg
    (fun term => ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)))) rawBody))

/-- Reading a represented raw assignment at an arity coordinate returns
the represented assigned body in that exact local context. -/
theorem programAssignment_family_component
    (arity : List (MetaArity S)) (a : Classifier R equations)
    (assignment : a.base.as ⟶ (⟨arity⟩ : Object S)) (i : Fin arity.length) :
    ((programData.{w} R equations).toModel.familyProj arity i).app (Opposite.op a)
      (((programData R equations).famIso arity).hom.app (Opposite.op a)
        (ULift.up ((programHomEquiv R equations a _).symm
          ((authoredEquationPresentation S equations).quotientFunctor.map assignment)))) =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (assignment i)))) := by
  have projected := famIso_image_project (programData R equations) arity i (Opposite.op a)
    (ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map assignment)))
  refine projected.trans ?_
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  change (authoredEquationPresentation S equations).quotientFunctor.map assignment ≫
      (authoredEquationPresentation S equations).quotientFunctor.map (slot arity i) = _
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  exact (Q.map_comp assignment (slot arity i)).symm.trans
    (congrArg Q.map (comp_slot arity assignment i))

/-- The whole semantic argument tuple is the actual represented
assignment of the filled, ordered binder bodies. -/
theorem programTupleArgs_representative
    (X : Object S) {Γ : Ctx S} {arity : List (MetaArity S)}
    (args : Args (withMetas S X.arities) arity Γ)
    {Z : Presheaf.{w} R equations}
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a))
    (assignment : a.base.as ⟶ X)
    (env : Sub (withMetas S a.base.as.arities) Γ [])
    (readAssignment : (((programData R equations).famIso X.arities).inv.app
      (Opposite.op a) (assignmentPoint.app (Opposite.op a) z)).down.base =
      (authoredEquationPresentation S equations).quotientFunctor.map assignment)
    (readEnvironment : ∀ r (var : Var Γ r),
      ((environment r var).app (Opposite.op a) z).down.base =
        (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (env r var))) :
    ((programData R equations).toModel.tupleArgs
      (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args)) Z assignmentPoint environment).app (Opposite.op a) z =
    ((programData R equations).famIso arity).hom.app (Opposite.op a)
      (ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (closedArgsAssignment (bindArgs env (instIntoArgs assignment args)))))) := by
  apply familyPoint_ext (programData R equations).toModel (Opposite.op a) arity
  intro i
  have actual := programTupleArgs_component_representative R equations X args
    assignmentPoint environment a z assignment env readAssignment readEnvironment i
  have represented := programAssignment_family_component R equations arity a
    (closedArgsAssignment (bindArgs env (instIntoArgs assignment args))) i
  exact actual.trans represented.symm

/-- The declared semantic operator is the actual image of its generic
authored operator arrow, through the existing family comparison. -/
theorem programData_opTerm {s : S.Srt} (o : S.Op s) :
    ((programData.{w} R equations).famIso (S.arity o)).hom ≫
      (programData R equations).toModel.op o =
    (programRestriction R equations).map (termArrow (opTerm o)) :=
  programRestriction_opTerm R equations (programExponential R equations) o

/-- Applying the semantic operator to represented ordered bodies returns
the represented authored operator on those very bodies. -/
theorem programData_operator_apply {s : S.Srt} (o : S.Op s)
    (a : Classifier R equations)
    (args : Args (withMetas S a.base.as.arities) (S.arity o) []) :
    ((programData.{w} R equations).toModel.op o).app (Opposite.op a)
      (((programData R equations).famIso (S.arity o)).hom.app (Opposite.op a)
        (ULift.up ((programHomEquiv R equations a _).symm
          ((authoredEquationPresentation S equations).quotientFunctor.map
            (closedArgsAssignment args))))) =
    ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (termArrow (Term.op (Sum.inl o) args)))) := by
  let point : ((programRestriction.{w} R equations).obj ⟨S.arity o⟩).obj (Opposite.op a) :=
    ULift.up ((programHomEquiv R equations a _).symm
      ((authoredEquationPresentation S equations).quotientFunctor.map
        (closedArgsAssignment args)))
  have actual :
      ((programData R equations).toModel.op o).app (Opposite.op a)
        (((programData R equations).famIso (S.arity o)).hom.app (Opposite.op a) point) =
      ((programRestriction R equations).map (termArrow (opTerm o))).app (Opposite.op a) point :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (programData_opTerm.{w} R equations o) (Opposite.op a)) point
  refine actual.trans ?_
  apply ULift.ext
  apply (programHomEquiv R equations a _).injective
  change (authoredEquationPresentation S equations).quotientFunctor.map
      (closedArgsAssignment args) ≫
      (authoredEquationPresentation S equations).quotientFunctor.map (termArrow (opTerm o)) = _
  let Q := (authoredEquationPresentation S equations).quotientFunctor
  exact (Q.map_comp (closedArgsAssignment args) (termArrow (opTerm o))).symm.trans
    (congrArg Q.map (closedArgsAssignment_opTerm o args))

/-- Authored operator meaning agrees with actual semantic operator
application at every point of every generalized presheaf stage. -/
theorem programRestrictionData_meaning_op_apply
    (X : Object S) {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S X.arities) (S.arity o) Γ)
    {Z : Presheaf.{w} R equations}
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ)
    (a : Classifier R equations) (z : Z.obj (Opposite.op a)) :
    (((programData R equations).meaning (Term.op (Sum.inl o) args)).value
      Z assignmentPoint environment).app (Opposite.op a) z =
    (((programData R equations).toModel.opElem o
      (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args))).value Z assignmentPoint environment).app
          (Opposite.op a) z := by
  obtain ⟨assignment, env, readAssignment, readEnvironment⟩ :=
    programRestrictionData_meaning_representatives R equations X assignmentPoint environment a z
  have meaning := programRestrictionData_meaning_apply R equations X
    (Term.op (Sum.inl o) args) assignmentPoint environment a z
      assignment env readAssignment readEnvironment
  have tuple := programTupleArgs_representative R equations X args assignmentPoint environment
    a z assignment env readAssignment readEnvironment
  have right :
      (((programData R equations).toModel.opElem o
        (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
          (FreeBindingTerms.syntaxToFamily args))).value Z assignmentPoint environment).app
        (Opposite.op a) z =
      ULift.up ((programHomEquiv R equations a _).symm
        ((authoredEquationPresentation S equations).quotientFunctor.map
          (termArrow (Term.op (Sum.inl o) (bindArgs env (instIntoArgs assignment args)))))) := by
    change ((programData R equations).toModel.op o).app (Opposite.op a)
      (((programData R equations).toModel.tupleArgs _ Z assignmentPoint environment).app
        (Opposite.op a) z) = _
    rw [tuple]
    exact programData_operator_apply R equations o a (bindArgs env (instIntoArgs assignment args))
  have raw : bind env (instInto assignment
      (Term.op (S := withMetas S X.arities) (Sum.inl o) args)) =
      Term.op (S := withMetas S a.base.as.arities) (Sum.inl o)
        (bindArgs env (instIntoArgs (S := S) assignment args)) := rfl
  exact meaning.trans ((congrArg (fun term => ULift.up ((programHomEquiv R equations a _).symm
    ((authoredEquationPresentation S equations).quotientFunctor.map (termArrow term)))) raw).trans
      right.symm)

/-- The actual operator constructor law as equality of natural meanings,
including every ordered body under its own binder list. -/
theorem programRestrictionData_meaning_op_value
    (X : Object S) {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S X.arities) (S.arity o) Γ)
    (Z : Presheaf.{w} R equations)
    (assignmentPoint : Z ⟶ (programData R equations).toModel.family X.arities)
    (environment : (programData R equations).toModel.Env Z Γ) :
    ((programData R equations).meaning (Term.op (Sum.inl o) args)).value
      Z assignmentPoint environment =
    ((programData R equations).toModel.opElem o
      (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
        (FreeBindingTerms.syntaxToFamily args))).value Z assignmentPoint environment :=
  presheafHom_ext (programRestrictionData_meaning_op_apply R equations X o args
    assignmentPoint environment)

/-- The genuine Yoneda program interpretation preserves authored operator
construction, with no restriction on generalized valuations. -/
theorem programRestrictionData_meaning_op
    (X : Object S) {Γ : Ctx S} {s : S.Srt} (o : S.Op s)
    (args : Args (withMetas S X.arities) (S.arity o) Γ) :
    (programData.{w} R equations).meaning (Term.op (Sum.inl o) args) =
      (programData R equations).toModel.opElem o
        (FreeBindingTerms.FamilyArgs.map (fun term => (programData R equations).meaning term)
          (FreeBindingTerms.syntaxToFamily args)) := by
  apply Model.ElemOver.ext
  funext Z assignment environment
  exact programRestrictionData_meaning_op_value R equations X o args Z assignment environment

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedPresheaf
end
