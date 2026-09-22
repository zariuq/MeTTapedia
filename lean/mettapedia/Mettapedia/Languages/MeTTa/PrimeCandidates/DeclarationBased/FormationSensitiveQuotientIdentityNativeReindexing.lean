import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityReindexing
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityInputCoherence

/-!
# Canonical and retained native based-context reindexing

Every admitted native substitution has its actual double binder lift.
The retained native presentation conjugates that lift into the quotient
CwF. Its projection, endpoint and path equations identify it with the
independently constructed canonical map. Native J substitution is then
transported along this proved map equality, retaining the motive function
and all other submitted parameters.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientIdentityNativeReindexing

open _root_.CategoryTheory
open QuotientCwf QuotientIdentity
open Mettapedia.TypeTheory.ContextualBasedIdentityOperations
  (basedContext baseProjection rightEndpoint witnessType)

variable {signature : Declaration.Signature Tower.Head}

/-- Actual substitution retains the original formation-level witness;
this is not an equality between independently chosen representatives. -/
theorem element_reindex {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    (input.reindex substitution).element = input.element.reindex substitution := rfl

theorem left_reindex_value {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    QTerm.mk (input.reindex substitution).leftTerm =
      (tmSub (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)
        (project substitution)).val := rfl

theorem source_context_eq {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    (input.reindex substitution).chosenContext =
      basedContext (formation (OpaqueRelatorExtension.rules signature))
        (tmSub (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)
          (project substitution)) := rfl

private theorem schema_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    subComp substitution.substitution
        (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
          input.type input.left input.motive input.method) =
      NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
        (input.reindex substitution).type (input.reindex substitution).left
        (input.reindex substitution).motive (input.reindex substitution).method := by
  funext index
  fin_cases index <;> rfl

/-- The submitted motive function retains its actual dependent Pi
annotation, rather than being reconstructed from an applied body. -/
theorem motive_function_type_reindex
    {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    QType.mk (QuotientIdentityInputCoherence.motiveFunctionType (input.reindex substitution)) =
      tySub (QType.mk (QuotientIdentityInputCoherence.motiveFunctionType input))
        (project substitution) := by
  apply (QType.mk_eq_iff _ _).mpr
  change Conv _
    (subst (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
      (input.reindex substitution).type (input.reindex substitution).left
      (input.reindex substitution).motive (input.reindex substitution).method) _)
    (subst substitution.substitution (subst
      (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
        input.type input.left input.motive input.method) _)) _
  rw [subst_subComp, schema_substitution]
  exact .refl _

theorem motive_function_reindex
    {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    QTerm.mk (QuotientIdentityInputCoherence.motiveFunction (input.reindex substitution)) =
      totalSub (QTerm.mk (QuotientIdentityInputCoherence.motiveFunction input))
        (project substitution) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨(QType.mk_eq_iff _ _).mp (motive_function_type_reindex input substitution), .refl _⟩

private theorem conjugate_base
    {source target nativeSource nativeTarget sourceBase targetBase :
      QContext (OpaqueRelatorExtension.rules signature)}
    (sourcePresentation : source ≅ nativeSource) (targetPresentation : target ≅ nativeTarget)
    (native : nativeSource ⟶ nativeTarget) (substitution : sourceBase ⟶ targetBase)
    (sourceProjection : source ⟶ sourceBase) (targetProjection : target ⟶ targetBase)
    (nativeSourceProjection : nativeSource ⟶ sourceBase)
    (nativeTargetProjection : nativeTarget ⟶ targetBase)
    (sourceEquation : sourcePresentation.inv ≫ sourceProjection = nativeSourceProjection)
    (targetEquation : targetPresentation.inv ≫ targetProjection = nativeTargetProjection)
    (nativeSquare : native ≫ nativeTargetProjection = nativeSourceProjection ≫ substitution) :
    (sourcePresentation.hom ≫ native ≫ targetPresentation.inv) ≫ targetProjection =
      sourceProjection ≫ substitution := by
  simp only [Category.assoc]
  rw [targetEquation, nativeSquare, ← sourceEquation]
  simp only [← Category.assoc, sourcePresentation.hom_inv_id, Category.id_comp]

private theorem conjugate_value
    {source target nativeSource nativeTarget : QContext (OpaqueRelatorExtension.rules signature)}
    (sourcePresentation : source ≅ nativeSource) (targetPresentation : target ≅ nativeTarget)
    (native : nativeSource ⟶ nativeTarget) (sourceValue : QTerm source.as) (targetValue : QTerm target.as)
    (nativeSquare : totalSub (totalSub targetValue targetPresentation.inv) native =
      totalSub sourceValue sourcePresentation.inv) :
    totalSub targetValue (sourcePresentation.hom ≫ native ≫ targetPresentation.inv) = sourceValue :=
  (totalSub_comp targetValue sourcePresentation.hom (native ≫ targetPresentation.inv)).trans
    ((congrArg (fun value => totalSub value sourcePresentation.hom)
      (totalSub_comp targetValue native targetPresentation.inv)).trans
      ((congrArg (fun value => totalSub value sourcePresentation.hom) nativeSquare).trans
        ((totalSub_comp sourceValue sourcePresentation.hom sourcePresentation.inv).symm.trans
          ((congrArg (totalSub sourceValue) sourcePresentation.hom_inv_id).trans
            (totalSub_id sourceValue)))))

theorem chosen_base_projection {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    input.chosenMap substitution ≫
        baseProjection (formation (OpaqueRelatorExtension.rules signature))
          (context := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm) =
      baseProjection (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj source) (TermFibre.mk (input.reindex substitution).leftTerm) ≫
        project substitution := by
  obtain ⟨sourceTyped, sourceEquation⟩ :=
    QuotientBasedContextRepresentation.admitted_projection_meaning (input.reindex substitution)
  obtain ⟨targetTyped, targetEquation⟩ :=
    QuotientBasedContextRepresentation.admitted_projection_meaning input
  let sourceProjection : (input.reindex substitution).basedContext ⟶ source :=
    ⟨renSub (fun index => index.succ.succ), sourceTyped⟩
  let targetProjection : input.basedContext ⟶ target :=
    ⟨renSub (fun index => index.succ.succ), targetTyped⟩
  have square : input.basedMap substitution ≫ targetProjection = sourceProjection ≫ substitution := by
    apply Hom.ext
    funext index
    change rename wk (rename wk (substitution.substitution index)) =
      subst (renSub (fun index => index.succ.succ)) (substitution.substitution index)
    rw [subst_renSub, rename_comp]
    rfl
  exact conjugate_base (input.reindex substitution).presentation input.presentation
    (project (input.basedMap substitution)) (project substitution) _ _
    (project sourceProjection) (project targetProjection) sourceEquation.symm targetEquation.symm
    (((quotientProjection _).map_comp _ _).symm.trans
      ((congrArg project square).trans ((quotientProjection _).map_comp _ _)))

theorem chosen_endpoint_value {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    (tmSub (rightEndpoint (formation (OpaqueRelatorExtension.rules signature))
      (context := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm))
      (input.chosenMap substitution)).val =
      (rightEndpoint (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj source) (TermFibre.mk (input.reindex substitution).leftTerm)).val := by
  obtain ⟨sourceType, sourceAnnotation, sourceTerm, sourceCode, _, sourceValue⟩ :=
    QuotientBasedContextRepresentation.admitted_right_meaning (input.reindex substitution)
  obtain ⟨targetType, targetAnnotation, targetTerm, targetCode, _, targetValue⟩ :=
    QuotientBasedContextRepresentation.admitted_right_meaning input
  have nativeSquare : QTerm.mk (targetTerm.reindex (input.basedMap substitution)) =
      QTerm.mk sourceTerm := by
    apply (QTerm.mk_eq_iff _ _).mpr
    constructor
    · change Conv _ (subst (liftSub (liftSub substitution.substitution)) targetType.code)
        sourceType.code _
      rw [targetAnnotation, sourceAnnotation]
      simp only [FormationSensitiveBasedIdentity.doubleWeaken, subst_liftSub_wk, Based.Admitted.reindex]
      exact .refl _
    · change Conv _ (subst (liftSub (liftSub substitution.substitution)) targetTerm.code)
        sourceTerm.code _
      rw [targetCode, sourceCode]
      exact .refl _
  exact conjugate_value (input.reindex substitution).presentation input.presentation
    (project (input.basedMap substitution)) _ _
    ((congrArg (fun value => totalSub value (project (input.basedMap substitution)))
      targetValue.symm).trans (nativeSquare.trans sourceValue))

theorem chosen_witness_value {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    (tmSub (vz (witnessType (formation (OpaqueRelatorExtension.rules signature))
      (context := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)))
      (input.chosenMap substitution)).val =
      (vz (witnessType (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj source) (TermFibre.mk (input.reindex substitution).leftTerm))).val := by
  obtain ⟨sourceType, sourceAnnotation, sourceTerm, sourceCode, _, sourceValue⟩ :=
    QuotientBasedContextRepresentation.admitted_witness_meaning (input.reindex substitution)
  obtain ⟨targetType, targetAnnotation, targetTerm, targetCode, _, targetValue⟩ :=
    QuotientBasedContextRepresentation.admitted_witness_meaning input
  have nativeSquare : QTerm.mk (targetTerm.reindex (input.basedMap substitution)) =
      QTerm.mk sourceTerm := by
    apply (QTerm.mk_eq_iff _ _).mpr
    constructor
    · change Conv _ (subst (liftSub (liftSub substitution.substitution)) targetType.code)
        sourceType.code _
      rw [targetAnnotation, sourceAnnotation]
      simp only [subst, FormationSensitiveBasedIdentity.doubleWeaken, subst_liftSub_wk,
        Based.Admitted.reindex]
      exact .refl _
    · change Conv _ (subst (liftSub (liftSub substitution.substitution)) targetTerm.code)
        sourceTerm.code _
      rw [targetCode, sourceCode]
      exact .refl _
  exact conjugate_value (input.reindex substitution).presentation input.presentation
    (project (input.basedMap substitution)) _ _
    ((congrArg (fun value => totalSub value (project (input.basedMap substitution)))
      targetValue.symm).trans (nativeSquare.trans sourceValue))

/-- The comparison retains each native input and each independently typed
substitution. No chosen representative of an admitted input class is used. -/
theorem chosenMap_eq_canonical {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    input.chosenMap substitution =
      QuotientIdentityReindexing.map (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm) := by
  apply QuotientBasedContextRepresentation.based_map_unique
    (context := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)
  · exact (chosen_base_projection input substitution).trans
      (QuotientIdentityReindexing.base_projection (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)).symm
  · exact (chosen_endpoint_value input substitution).trans
      (QuotientIdentityReindexing.endpoint_value (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)).symm
  · exact (chosen_witness_value input substitution).trans
      (QuotientIdentityReindexing.witness_value (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)).symm

theorem canonical_presentation_square {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    QuotientIdentityReindexing.map (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm) ≫
        input.presentation.hom =
      (input.reindex substitution).presentation.hom ≫ project (input.basedMap substitution) := by
  have retained : input.chosenMap substitution ≫ input.presentation.hom =
      (input.reindex substitution).presentation.hom ≫ project (input.basedMap substitution) := by
    change ((input.reindex substitution).presentation.hom ≫
      project (input.basedMap substitution) ≫ input.presentation.inv) ≫ input.presentation.hom = _
    simp only [Category.assoc, input.presentation.inv_hom_id, Category.comp_id]
  exact (congrArg (fun arrow => arrow ≫ input.presentation.hom)
    (chosenMap_eq_canonical input substitution).symm).trans retained

/-- The motive's type transport is proved from the native family
substitution and presentation square, independently of the J term law. -/
theorem canonical_motive_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    tySub (tySub (QType.mk input.motiveType) input.presentation.hom)
        (QuotientIdentityReindexing.map (project substitution)
          (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm)) =
      tySub (QType.mk (input.reindex substitution).motiveType)
        (input.reindex substitution).presentation.hom :=
  (tySub_comp (QType.mk input.motiveType)
    (QuotientIdentityReindexing.map (project substitution)
      (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm))
    input.presentation.hom).symm.trans
    ((congrArg (tySub (QType.mk input.motiveType))
      (canonical_presentation_square input substitution)).trans
      ((tySub_comp (QType.mk input.motiveType) (input.reindex substitution).presentation.hom
        (project (input.basedMap substitution))).trans
        (congrArg (fun type => tySub type (input.reindex substitution).presentation.hom)
          (input.motive_substitution substitution))))

theorem canonical_j_substitution_value {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    (tmSub input.chosenJ (QuotientIdentityReindexing.map (project substitution)
      (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm))).val =
      (input.reindex substitution).chosenJ.val :=
  (congrArg (fun arrow => (tmSub input.chosenJ arrow).val)
    (chosenMap_eq_canonical input substitution).symm).trans (input.chosen_j_substitution substitution)

/-- Typed equality uses the independently derived family transport, not
an implicit change of output annotation. Every submitted motive is retained. -/
theorem canonical_j_substitution {source target : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted target) (substitution : source ⟶ target) :
    TermFibre.compare (canonical_motive_substitution input substitution)
      (tmSub input.chosenJ (QuotientIdentityReindexing.map (project substitution)
        (target := (quotientProjection _).obj target) (TermFibre.mk input.leftTerm))) =
      (input.reindex substitution).chosenJ :=
  Subtype.ext (canonical_j_substitution_value input substitution)

/-! ## Instantiating the actual native declaration telescope -/

namespace Controls

/-- All four variables of the actual declaration telescope are
instantiated with the existing full-motive mixed HOL/list/wire workload. -/
def instantiate (wire : NativeWireData.Wire) :
    Common.context ⟶ QuotientIdentityInputCoherence.Controls.parameterContext :=
  ⟨NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution
    (QuotientIdentity.Controls.mixedInput wire).type (QuotientIdentity.Controls.mixedInput wire).left
    (QuotientIdentity.Controls.mixedInput wire).motive (QuotientIdentity.Controls.mixedInput wire).method,
    (QuotientIdentity.Controls.mixedInput wire).typed⟩

theorem instantiated_input (wire : NativeWireData.Wire) :
    QuotientIdentityInputCoherence.Controls.variableInput.reindex (instantiate wire) =
      QuotientIdentity.Controls.mixedInput wire := rfl

theorem instantiated_endpoint (wire : NativeWireData.Wire) :
    (tmSub
      (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
      (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
      (project (instantiate wire))).val = QTerm.mk (Common.result wire) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  exact ⟨.refl _, Common.projected_converts_result wire⟩

theorem variable_j_substitution_crown (wire : NativeWireData.Wire) :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
        QuotientIdentityInputCoherence.Controls.parameterContext.raw Common.context.raw
        (instantiate wire).substitution ∧
      QuotientIdentityInputCoherence.Controls.variableInput.chosenMap (instantiate wire) =
        QuotientIdentityReindexing.map (project (instantiate wire))
          (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm) ∧
      (tmSub QuotientIdentityInputCoherence.Controls.variableInput.chosenJ
        (QuotientIdentityReindexing.map (project (instantiate wire))
          (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm))).val =
        (QuotientIdentity.Controls.mixedInput wire).chosenJ.val :=
  ⟨(instantiate wire).typed, chosenMap_eq_canonical _ _, canonical_j_substitution_value _ _⟩

theorem transported_endpoint (wire : NativeWireData.Wire) :
    totalSub (QTerm.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
      ((QuotientIdentityGeometry.reflSection
        (tmSub (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
          (project (instantiate wire))) ≫
        QuotientIdentityReindexing.map (project (instantiate wire))
          (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)) ≫
        baseProjection (formation HOLNativeRelatorCompatibility.rules)
          (context := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)) =
      QTerm.mk (Common.result wire) :=
  (congrArg (totalSub (QTerm.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm))
    (QuotientIdentityReindexing.reflexivity_base (project (instantiate wire))
      (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
      (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm))).trans
    (instantiated_endpoint wire)

theorem changed_value_rejected :
    (tmSub
      (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
      (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
      (project (instantiate (.natural 7)))).val ≠ QTerm.mk (Common.result (.natural 8)) := by
  intro same
  exact FibreControls.seven_eight_distinct ((instantiated_endpoint (.natural 7)).symm.trans same)

theorem changed_transport_rejected :
    totalSub (QTerm.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
      ((QuotientIdentityGeometry.reflSection
        (tmSub (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)
          (project (instantiate (.natural 7)))) ≫
        QuotientIdentityReindexing.map (project (instantiate (.natural 7)))
          (target := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)) ≫
        baseProjection (formation HOLNativeRelatorCompatibility.rules)
          (context := (quotientProjection _).obj QuotientIdentityInputCoherence.Controls.parameterContext)
          (TermFibre.mk QuotientIdentityInputCoherence.Controls.variableInput.leftTerm)) ≠
      QTerm.mk (Common.result (.natural 8)) := by
  intro same
  exact FibreControls.seven_eight_distinct ((transported_endpoint (.natural 7)).symm.trans same)

theorem changed_instantiation_independently_admitted :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules
      QuotientIdentityInputCoherence.Controls.parameterContext.raw Common.context.raw
      (instantiate (.natural 8)).substitution := (instantiate (.natural 8)).typed

end Controls

#print axioms chosenMap_eq_canonical
#print axioms motive_function_type_reindex
#print axioms motive_function_reindex
#print axioms canonical_presentation_square
#print axioms canonical_motive_substitution
#print axioms canonical_j_substitution
#print axioms Controls.variable_j_substitution_crown
#print axioms Controls.changed_value_rejected
#print axioms Controls.changed_transport_rejected

end FormationSensitiveContextual.QuotientIdentityNativeReindexing
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
