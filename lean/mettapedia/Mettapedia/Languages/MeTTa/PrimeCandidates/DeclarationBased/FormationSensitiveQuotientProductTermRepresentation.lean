import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientProductRepresentation

/-!
# Argument and lambda representatives across formed comprehension

The canonical comprehension comparison retains variable codes while changing
an independently formed binder annotation by native conversion. An actual
argument therefore instantiates a transported dependent family at its exact
native section. A semantic lambda also retains the body represented in the
submitted binder, up to the unchanged native conversion relation.

These are comparisons in the existing formed quotient CwF. They do not
identify raw context annotations, recover original syntax from a quotient,
assume a total identity eliminator, or assert a full native model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientProductTermRepresentation

open _root_.CategoryTheory FormationSensitive QuotientComprehensionSyntax
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

noncomputable section

variable {Head : Type} {rules : Rules Head}

/-- The argument has its original admitted annotation. Only the intermediate
representative is converted to the chosen annotation, without changing code. -/
theorem section_through_presentation {context : Context rules} (domain : TypeOver context)
    (actual : Term context domain)
    (argument : QuotientCwf.Tm ((quotientProjection rules).obj context) (QType.mk domain))
    (same : QTerm.mk actual = argument.val) :
    selfExtend (QuotientCwf.cwf rules) argument ≫
        (QuotientCwf.extPresentation context domain).hom =
      QuotientCwf.project (nativeSection actual) := by
  let selected := QuotientCwf.typeRepresentative (QType.mk domain)
  have converted := (QType.mk_eq_iff selected domain).mp
    (QuotientCwf.typeRepresentative_class (QType.mk domain))
  let admitted := actual.convertType selected converted.symm
  have admittedClass : QTerm.mk admitted = argument.val := by
    refine Eq.trans ?_ same
    exact Quotient.sound ⟨converted, .refl _⟩
  have sections : nativeSection admitted ≫ (extensionComparison selected domain converted).hom =
      nativeSection actual := by
    apply Hom.ext
    change subComp (nativeSection admitted).substitution ids = _
    rw [subComp_ids_right, nativeSection_substitution, nativeSection_substitution]
    rfl
  calc
    _ = QuotientCwf.project (nativeSection admitted) ≫
        (QuotientCwf.extPresentation context domain).hom := by
      exact (congrArg (fun morphism : (quotientProjection rules).obj context ⟶
          QuotientCwf.ext ((quotientProjection rules).obj context) (QType.mk domain) =>
        morphism ≫ (QuotientCwf.extPresentation context domain).hom)
          (nativeSection_projects_of_class argument admitted admittedClass)).symm
    _ = QuotientCwf.project
        (nativeSection admitted ≫ (extensionComparison selected domain converted).hom) :=
      ((quotientProjection rules).map_comp _ _).symm
    _ = _ := congrArg QuotientCwf.project sections

/-- A transported dependent family is instantiated at the actual argument,
not at an unrelated representative or a constant-family approximation. -/
theorem type_at_argument {context : Context rules} (domain : TypeOver context)
    (codomain : TypeOver (extend context domain)) (actual : Term context domain)
    (argument : QuotientCwf.Tm ((quotientProjection rules).obj context) (QType.mk domain))
    (same : QTerm.mk actual = argument.val) :
    QuotientCwf.tySub
        (QuotientCwf.tySub (QType.mk codomain)
          (QuotientCwf.extPresentation context domain).hom)
        (selfExtend (QuotientCwf.cwf rules) argument) =
      QType.mk (codomain.reindex (nativeSection actual)) := by
  exact (QuotientCwf.tySub_comp (QType.mk codomain)
    (selfExtend (QuotientCwf.cwf rules) argument)
    (QuotientCwf.extPresentation context domain).hom).symm.trans
      (congrArg (QuotientCwf.tySub (QType.mk codomain))
        (section_through_presentation domain actual argument same))

/-- The comparison changes the binder's type, not the body's variable codes.
The reindexed body is still independently admitted before taking its class. -/
theorem chosenTerm_through_presentation {context : Context rules} (domain : TypeOver context)
    {codomain : QuotientCwf.Ty
      (QuotientCwf.ext ((quotientProjection rules).obj context) (QType.mk domain))}
    (body : QuotientCwf.Tm
      (QuotientCwf.ext ((quotientProjection rules).obj context) (QType.mk domain)) codomain) :
    Conv rules.headEq
      (chosenTerm (QuotientCwf.tmSub body (QuotientCwf.extPresentation context domain).inv)).code
      (chosenTerm body).code rules.computation := by
  let selected := QuotientCwf.typeRepresentative (QType.mk domain)
  have converted := (QType.mk_eq_iff selected domain).mp
    (QuotientCwf.typeRepresentative_class (QType.mk domain))
  let inverse := (extensionComparison selected domain converted).inv
  have represented : QTerm.mk ((chosenTerm body).reindex inverse) =
      (QuotientCwf.tmSub body (QuotientCwf.extPresentation context domain).inv).val := by
    change (QTerm.mk (chosenTerm body)).reindex inverse = body.val.reindex inverse
    rw [chosenTerm_class]
  have result := chosenTerm_represents
    (QuotientCwf.tmSub body (QuotientCwf.extPresentation context domain).inv)
    ((chosenTerm body).reindex inverse) represented
  change Conv rules.headEq _ (subst ids (chosenTerm body).code) rules.computation at result
  rw [subst_ids] at result
  exact result

variable {signature : Declaration.Signature Tower.Head}

/-- Native lambda syntax agrees after the canonical binder comparison. The
semantic codomain is arbitrary; no constant-motive restriction is used. -/
theorem lam_through_presentation {context : QuotientProducts.NativeContext signature}
    (domain : TypeOver context)
    {codomain : QuotientCwf.Ty
      (QuotientCwf.ext ((quotientProjection _).obj context) (QType.mk domain))}
    (body : QuotientCwf.Tm
      (QuotientCwf.ext ((quotientProjection _).obj context) (QType.mk domain)) codomain) :
    Conv (OpaqueRelatorExtension.rules signature).headEq
      (chosenTerm (QuotientProducts.lam body)).code
      (.lam (chosenTerm
        (QuotientCwf.tmSub body (QuotientCwf.extPresentation context domain).inv)).code)
      (OpaqueRelatorExtension.rules signature).computation :=
  .trans _ _ _ (QuotientProducts.lam_represents body)
    (Conv.congLam (chosenTerm_through_presentation domain body).symm)

namespace Controls

/-- A genuine mixed HOL-list/wire projection can serve as the semantic
argument while the submitted native section uses its converted result.
The family is the actual endpoint-dependent native identity type. -/
theorem dependent_family_at_projected_argument (wire : NativeWireData.Wire) :
    QuotientCwf.tySub
        (QuotientCwf.tySub (QType.mk ComparisonControls.variableIdentity)
          (QuotientCwf.extPresentation Common.context Common.wireType).hom)
        (selfExtend (QuotientCwf.cwf HOLNativeRelatorCompatibility.rules)
          (QuotientCwf.Controls.projected wire)) =
      QType.mk (QuotientProducts.Controls.expectedType wire) :=
  type_at_argument Common.wireType ComparisonControls.variableIdentity (Common.result wire)
    (QuotientCwf.Controls.projected wire)
    (congrArg Subtype.val (QuotientCwf.Controls.projected_is_result wire).symm)

/-- The preceding comparison genuinely uses conversion, not raw-code
equality of its two admitted arguments. -/
theorem projected_argument_raw_distinct :
    (Common.projected (.natural 7)).code ≠ (Common.result (.natural 7)).code := by
  intro same
  simp only [Common.projected, Common.result, NativeWireData.encode] at same
  cases same

/-- Altering the represented argument is not licensed by the comparison. -/
theorem altered_argument_not_represented :
    QTerm.mk (Common.result (.natural 7)) ≠ (QuotientCwf.Controls.result (.natural 8)).val :=
  FibreControls.seven_eight_distinct

/-- The actual dependent lambda is formed at the submitted annotation and
represents the very same semantic lambda after the binder comparison. -/
theorem dependent_lambda_admitted_and_represented :
    Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
        (.lam (.refl (.var (0 : Fin 1))))
        (.pi NativeWireData.dataType
          (.id NativeWireData.dataType (.var (0 : Fin 1)) (.var (0 : Fin 1)))) ∧
      Conv HOLNativeRelatorCompatibility.rules.headEq
        (chosenTerm (QuotientProducts.lam QuotientProducts.Controls.reflexivityBody)).code
        (.lam (.refl (.var (0 : Fin 1)))) HOLNativeRelatorCompatibility.rules.computation := by
  have body := chosenTerm_represents QuotientProducts.Controls.reflexivityBody
    (ComparisonControls.variableReflexivity.reindex QuotientProducts.Controls.wireBinder.hom) rfl
  change Conv _ _ (subst ids (.refl (.var (0 : Fin 1)))) _ at body
  rw [subst_ids] at body
  have inSubmitted : Conv HOLNativeRelatorCompatibility.rules.headEq
      (chosenTerm (QuotientCwf.tmSub QuotientProducts.Controls.reflexivityBody
        (QuotientCwf.extPresentation Common.context Common.wireType).inv)).code
      (.refl (.var (0 : Fin 1))) HOLNativeRelatorCompatibility.rules.computation :=
    .trans _ _ _ (chosenTerm_through_presentation Common.wireType
      QuotientProducts.Controls.reflexivityBody) body
  exact ⟨(QuotientProducts.nativeLambda ComparisonControls.variableReflexivity).judgment,
    .trans _ _ _ (lam_through_presentation Common.wireType QuotientProducts.Controls.reflexivityBody)
      (Conv.congLam inSubmitted)⟩

end Controls

end

end FormationSensitiveContextual.QuotientProductTermRepresentation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
