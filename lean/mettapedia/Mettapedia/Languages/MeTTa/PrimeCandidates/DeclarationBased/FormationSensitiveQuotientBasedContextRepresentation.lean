import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientInterpretation
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeQuotientInterpretationControls

/-!
# Representation of the actual based endpoint and identity context

The existing comparison between the chosen quotient based context and the
submitted double native telescope preserves the base projection, right
endpoint, and newest identity witness. The terms retain their independently
formed native annotations. The comparison is not an equality of raw contexts.

These laws concern based-context geometry only. They construct no identity
eliminator, motive coverage restriction, additional conversion, or global
identity policy.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientBasedContextRepresentation

open _root_.CategoryTheory FormationSensitive QuotientIdentity
open Mettapedia.TypeTheory.ContextualBasedIdentityOperations

noncomputable section

variable {Head : Type} {rules : Rules Head}

abbrev nativeContext {context : Context rules} (type : TypeOver context)
    (left : Term context type) : Context rules :=
  extend (extend context type) (nativeWitness type left)

def nativeBaseProjection {context : Context rules} (type : TypeOver context)
    (left : Term context type) : nativeContext type left ⟶ context :=
  projectionHom (extend context type) (nativeWitness type left) ≫ projectionHom context type

def nativeRight {context : Context rules} (type : TypeOver context) (left : Term context type) :
    Term (nativeContext type left)
      ((type.reindex (projectionHom context type)).reindex
        (projectionHom (extend context type) (nativeWitness type left))) :=
  (newest context type).reindex (projectionHom (extend context type) (nativeWitness type left))

def nativePath {context : Context rules} (type : TypeOver context) (left : Term context type) :
    Term (nativeContext type left)
      ((nativeWitness type left).reindex
        (projectionHom (extend context type) (nativeWitness type left))) :=
  newest (extend context type) (nativeWitness type left)

theorem base_projection {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    (basedPresentation type left).inv ≫
      baseProjection (formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left) =
      QuotientCwf.project (nativeBaseProjection type left) := by
  let chosen := QuotientCwf.typeRepresentative (QType.mk type)
  let witness := chosenWitness type left
  let comparison := doubleExtensionComparison chosen type witness (nativeWitness type left)
    ((QType.mk_eq_iff _ _).mp (QuotientCwf.typeRepresentative_class (QType.mk type)))
    (chosenWitness_conversion type left)
  have nativeSame : comparison.inv ≫
      (projectionHom (extend context chosen) witness ≫ projectionHom context chosen) =
      nativeBaseProjection type left := Hom.ext (subComp_ids_left _)
  have inner := (quotientProjection rules).map_comp
    (projectionHom (extend context chosen) witness) (projectionHom context chosen)
  have outer := (quotientProjection rules).map_comp comparison.inv
    (projectionHom (extend context chosen) witness ≫ projectionHom context chosen)
  exact (congrArg (fun morphism => QuotientCwf.project comparison.inv ≫ morphism) inner.symm).trans
    (outer.symm.trans (congrArg QuotientCwf.project nativeSame))

/-- Total term equality includes the transported annotation as well as
the value. Its proof uses the actual chosen-domain conversion twice. -/
theorem right_value {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    (QuotientCwf.tmSub
      (rightEndpoint (formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left))
      (basedPresentation type left).inv).val = QTerm.mk (nativeRight type left) := by
  let chosen := QuotientCwf.typeRepresentative (QType.mk type)
  have converted := (QType.mk_eq_iff chosen type).mp
    (QuotientCwf.typeRepresentative_class (QType.mk type))
  apply Quotient.sound
  constructor
  · change Conv rules.headEq
      (subst ids (subst projection (subst projection chosen.code)))
      (subst projection (subst projection type.code)) rules.computation
    rw [subst_ids]
    exact (converted.substitute projection).substitute projection
  · change Conv rules.headEq (subst ids (.var (1 : Fin (context.arity + 2))))
      (.var (1 : Fin (context.arity + 2))) rules.computation
    rw [subst_ids]
    exact .refl _

/-- The newest path is retained with its actual dependent identity
annotation, using the independently proved witness conversion. -/
theorem witness_value {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    (QuotientCwf.tmSub
      (QuotientCwf.vz (witnessType (formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left)))
      (basedPresentation type left).inv).val = QTerm.mk (nativePath type left) := by
  apply Quotient.sound
  constructor
  · change Conv rules.headEq (subst ids (subst projection (chosenWitness type left).code))
      (subst projection (nativeWitness type left).code) rules.computation
    rw [subst_ids]
    exact (chosenWitness_conversion type left).substitute projection
  · change Conv rules.headEq (subst ids (.var (0 : Fin (context.arity + 2))))
      (.var (0 : Fin (context.arity + 2))) rules.computation
    rw [subst_ids]
    exact .refl _

theorem right_type {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QuotientCwf.tySub
      (QuotientCwf.tySub (QuotientCwf.tySub (QType.mk type) (QuotientCwf.wk (QType.mk type)))
        (QuotientCwf.wk (witnessType (formation rules)
          (context := (quotientProjection rules).obj context) (TermFibre.mk left))))
      (basedPresentation type left).inv =
      QType.mk ((type.reindex (projectionHom context type)).reindex
        (projectionHom (extend context type) (nativeWitness type left))) := by
  have property := (QuotientCwf.tmSub
    (rightEndpoint (formation rules)
      (context := (quotientProjection rules).obj context) (TermFibre.mk left))
    (basedPresentation type left).inv).property
  exact property.symm.trans (congrArg QTerm.type (right_value type left))

theorem witness_type {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QuotientCwf.tySub
      (QuotientCwf.tySub
        (witnessType (formation rules)
          (context := (quotientProjection rules).obj context) (TermFibre.mk left))
        (QuotientCwf.wk (witnessType (formation rules)
          (context := (quotientProjection rules).obj context) (TermFibre.mk left))))
      (basedPresentation type left).inv =
      QType.mk ((nativeWitness type left).reindex
        (projectionHom (extend context type) (nativeWitness type left))) := by
  have property := (QuotientCwf.tmSub
    (QuotientCwf.vz (witnessType (formation rules)
      (context := (quotientProjection rules).obj context) (TermFibre.mk left)))
    (basedPresentation type left).inv).property
  exact property.symm.trans (congrArg QTerm.type (witness_value type left))

theorem base_projection_meaning {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QuotientInterpretation.SubstitutionMeaning context (nativeContext type left)
      (renSub (fun index => index.succ.succ))
      ((basedPresentation type left).inv ≫ baseProjection (formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left)) :=
  ⟨(nativeBaseProjection type left).typed, (base_projection type left).symm⟩

theorem right_meaning {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QuotientInterpretation.TermMeaning (nativeContext type left)
      (.var (1 : Fin (context.arity + 2))) (rename wk (rename wk type.code))
      (QuotientCwf.tySub
        (QuotientCwf.tySub (QuotientCwf.tySub (QType.mk type) (QuotientCwf.wk (QType.mk type)))
          (QuotientCwf.wk (witnessType (formation rules)
            (context := (quotientProjection rules).obj context) (TermFibre.mk left))))
        (basedPresentation type left).inv)
      (QuotientCwf.tmSub
        (rightEndpoint (formation rules)
          (context := (quotientProjection rules).obj context) (TermFibre.mk left))
        (basedPresentation type left).inv) := by
  refine ⟨_, ?_, nativeRight type left, rfl, (right_type type left).symm,
    (right_value type left).symm⟩
  change subst projection (subst projection type.code) = _
  rw [subst_projection, subst_projection]

theorem witness_meaning {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QuotientInterpretation.TermMeaning (nativeContext type left)
      (.var (0 : Fin (context.arity + 2)))
      (.id (rename wk (rename wk type.code)) (rename wk (rename wk left.code)) (.var 1))
      (QuotientCwf.tySub
        (QuotientCwf.tySub
          (witnessType (formation rules)
            (context := (quotientProjection rules).obj context) (TermFibre.mk left))
          (QuotientCwf.wk (witnessType (formation rules)
            (context := (quotientProjection rules).obj context) (TermFibre.mk left))))
        (basedPresentation type left).inv)
      (QuotientCwf.tmSub
        (QuotientCwf.vz (witnessType (formation rules)
          (context := (quotientProjection rules).obj context) (TermFibre.mk left)))
        (basedPresentation type left).inv) := by
  refine ⟨_, ?_, nativePath type left, rfl, (witness_type type left).symm,
    (witness_value type left).symm⟩
  change subst projection
    (.id (subst projection type.code) (subst projection left.code) (.var 0)) = _
  have successor : (0 : Fin (context.arity + 1)).succ = (1 : Fin (context.arity + 2)) := by
    apply Fin.ext
    simp
  simp only [subst_projection, rename, wk, successor]

/-- Projection, endpoint and path together determine the actual based
context map. The endpoint equation alone does not discard path evidence. -/
theorem based_map_unique {source context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty context} (left : QuotientCwf.Tm context type)
    (first second : source ⟶ basedContext (formation rules) left)
    (sameBase : first ≫ baseProjection (formation rules) left =
      second ≫ baseProjection (formation rules) left)
    (sameRight : (QuotientCwf.tmSub (rightEndpoint (formation rules) left) first).val =
      (QuotientCwf.tmSub (rightEndpoint (formation rules) left) second).val)
    (sameWitness : (QuotientCwf.tmSub
        (QuotientCwf.vz (witnessType (formation rules) left)) first).val =
      (QuotientCwf.tmSub (QuotientCwf.vz (witnessType (formation rules) left)) second).val) :
    first = second := by
  apply QuotientCwf.pair_unique (witnessType (formation rules) left) first second
  · apply QuotientCwf.pair_unique type
    · exact (Category.assoc first (QuotientCwf.wk (witnessType (formation rules) left))
        (QuotientCwf.wk type)).trans
        (sameBase.trans (Category.assoc second
          (QuotientCwf.wk (witnessType (formation rules) left)) (QuotientCwf.wk type)).symm)
    · exact (QuotientCwf.totalSub_comp (QuotientCwf.vz type).val first
        (QuotientCwf.wk (witnessType (formation rules) left))).trans
        (sameRight.trans (QuotientCwf.totalSub_comp (QuotientCwf.vz type).val second
          (QuotientCwf.wk (witnessType (formation rules) left))).symm)
  · exact sameWitness

/-! ## The actual admitted-input telescope -/

/-- These are two constructions of the same submitted native telescope.
This equality does not identify it with the chosen semantic telescope. -/
theorem input_context_eq {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    nativeContext input.element input.leftTerm = input.basedContext := by
  simp only [nativeContext, extend, nativeWitness, nativeId, TypeOver.reindex, Term.reindex,
    projectionHom, newest, Based.Admitted.element, Based.Admitted.leftTerm,
    subst_projection, Based.Admitted.basedContext, FormationSensitiveBasedIdentity.basedContext]

theorem input_presentation_eq {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    input.presentation = (basedPresentation input.element input.leftTerm).trans
      (eqToIso (congrArg (quotientProjection _).obj (input_context_eq input))) := rfl

private theorem substitution_change_target {source target other : Context rules}
    (same : target = other) {substitution : Sub Head source.arity target.arity}
    {arrow : (quotientProjection rules).obj target ⟶ (quotientProjection rules).obj source}
    (meaning : QuotientInterpretation.SubstitutionMeaning source target substitution arrow) :
    QuotientInterpretation.SubstitutionMeaning source other
      (fun index => cast (congrArg (fun context : Context rules => Tm Head context.arity) same)
        (substitution index))
      ((eqToIso (congrArg (quotientProjection rules).obj same)).inv ≫ arrow) := by
  cases same
  simpa only [eqToIso_refl, Iso.refl_inv, Category.id_comp, cast_eq] using meaning

private theorem term_change_context {source target : Context rules}
    (same : source = target) {code annotation : Tm Head source.arity}
    {type : QType source} {value : TermFibre type}
    (meaning : QuotientInterpretation.TermMeaning source code annotation type value) :
    QuotientInterpretation.TermMeaning target
      (cast (congrArg (fun context : Context rules => Tm Head context.arity) same) code)
      (cast (congrArg (fun context : Context rules => Tm Head context.arity) same) annotation)
      (QuotientCwf.tySub type (eqToIso (congrArg (quotientProjection rules).obj same)).inv)
      (QuotientCwf.tmSub value (eqToIso (congrArg (quotientProjection rules).obj same)).inv) := by
  cases same
  simp only [eqToIso_refl, Iso.refl_inv, cast_eq]
  obtain ⟨actualType, annotationSame, actual, codeSame, typeSame, valueSame⟩ := meaning
  refine ⟨actualType, annotationSame, actual, codeSame, ?_, ?_⟩
  · exact typeSame.trans
      (QuotientCwf.tySub_id (context := (quotientProjection rules).obj source) type).symm
  · exact valueSame.trans
      (QuotientCwf.totalSub_id (context := (quotientProjection rules).obj source) value.val).symm

private theorem term_meaning_of_value_eq {context : Context rules}
    {code annotation : Tm Head context.arity} {firstType secondType : QType context}
    {first : TermFibre firstType} {second : TermFibre secondType}
    (meaning : QuotientInterpretation.TermMeaning context code annotation firstType first)
    (same : first.val = second.val) :
    QuotientInterpretation.TermMeaning context code annotation secondType second := by
  obtain ⟨actualType, annotationSame, actual, codeSame, typeSame, valueSame⟩ := meaning
  refine ⟨actualType, annotationSame, actual, codeSame, ?_, valueSame.trans same⟩
  exact typeSame.trans (first.property.symm.trans
    ((congrArg QTerm.type same).trans second.property))

theorem admitted_projection_meaning {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    QuotientInterpretation.SubstitutionMeaning context input.basedContext
      (renSub (fun index => index.succ.succ))
      (input.presentation.inv ≫ baseProjection (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm)) := by
  have transported := substitution_change_target (input_context_eq input)
    (base_projection_meaning input.element input.leftTerm)
  obtain ⟨typed, same⟩ := transported
  refine ⟨typed, ?_⟩
  exact same.trans (Category.assoc _ _ _).symm

theorem admitted_right_meaning {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    QuotientInterpretation.TermMeaning input.basedContext
      (.var (1 : Fin (context.arity + 2))) (FormationSensitiveBasedIdentity.doubleWeaken input.type)
      (QuotientCwf.tySub
        (QuotientCwf.tySub
          (QuotientCwf.tySub (QType.mk input.element) (QuotientCwf.wk (QType.mk input.element)))
          (QuotientCwf.wk (witnessType (formation (OpaqueRelatorExtension.rules signature))
            (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))))
        input.presentation.inv)
      (QuotientCwf.tmSub
        (rightEndpoint (formation (OpaqueRelatorExtension.rules signature))
          (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))
        input.presentation.inv) := by
  have transported := term_change_context (input_context_eq input)
    (right_meaning input.element input.leftTerm)
  apply term_meaning_of_value_eq transported
  exact (QuotientCwf.totalSub_comp
    (rightEndpoint (formation (OpaqueRelatorExtension.rules signature))
      (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm)).val
    (eqToIso (congrArg (quotientProjection _).obj (input_context_eq input))).inv
    (basedPresentation input.element input.leftTerm).inv).symm

theorem admitted_witness_meaning {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    QuotientInterpretation.TermMeaning input.basedContext
      (.var (0 : Fin (context.arity + 2)))
      (.id (FormationSensitiveBasedIdentity.doubleWeaken input.type)
        (FormationSensitiveBasedIdentity.doubleWeaken input.left)
        (.var (1 : Fin (context.arity + 2))))
      (QuotientCwf.tySub
        (QuotientCwf.tySub
          (witnessType (formation (OpaqueRelatorExtension.rules signature))
            (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))
          (QuotientCwf.wk (witnessType (formation (OpaqueRelatorExtension.rules signature))
            (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))))
        input.presentation.inv)
      (QuotientCwf.tmSub
        (QuotientCwf.vz (witnessType (formation (OpaqueRelatorExtension.rules signature))
          (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm)))
        input.presentation.inv) := by
  have transported := term_change_context (input_context_eq input)
    (witness_meaning input.element input.leftTerm)
  apply term_meaning_of_value_eq transported
  exact (QuotientCwf.totalSub_comp
    (QuotientCwf.vz (witnessType (formation (OpaqueRelatorExtension.rules signature))
      (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))).val
    (eqToIso (congrArg (quotientProjection _).obj (input_context_eq input))).inv
    (basedPresentation input.element input.leftTerm).inv).symm

private theorem parallel_variable {n : Nat} {index : Fin n} {target : Tower.Tm n}
    (steps : NativeRelatorConversionParallel.ParStar (.var index) target) :
    target = .var index := by
  induction steps with
  | refl => rfl
  | tail previous finalStep ih =>
      subst_vars
      cases finalStep
      rfl

/-- The authored opaque-declaration conversion does not confuse the
endpoint variable with the separately retained identity witness. -/
theorem admitted_right_ne_witness {signature : Declaration.Signature Tower.Head}
    (opacity : OpaqueRelatorExtension.Opacity signature)
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : Based.Admitted context) :
    (QuotientCwf.tmSub
      (rightEndpoint (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))
      input.presentation.inv).val ≠
    (QuotientCwf.tmSub
      (QuotientCwf.vz (witnessType (formation (OpaqueRelatorExtension.rules signature))
        (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm)))
      input.presentation.inv).val := by
  intro same
  obtain ⟨_, _, actualRight, rightCode, _, rightValue⟩ := admitted_right_meaning input
  obtain ⟨_, _, actualPath, pathCode, _, pathValue⟩ := admitted_witness_meaning input
  have converted := ((QTerm.mk_eq_iff actualRight actualPath).mp
    (rightValue.trans (same.trans pathValue.symm))).2
  rw [rightCode, pathCode] at converted
  obtain ⟨_, fromRight, fromPath⟩ := NativeRelatorConversionParallel.conversion_join
    ((OpaqueRelatorExtension.conversion_iff opacity).mp converted)
  have indices := Tm.var.inj ((parallel_variable fromRight).symm.trans
    (parallel_variable fromPath))
  exact Nat.one_ne_zero (congrArg Fin.val indices)

namespace Controls

/-- Both variables are represented for the actual mixed HOL/list/wire
input, with its submitted projected left endpoint and dependent path type. -/
theorem mixed_variables_represented (wire : NativeWireData.Wire) :
    let input := QuotientIdentity.Controls.mixedInput wire
    ∃ endpointType : TypeOver input.basedContext,
      ∃ endpoint : Term input.basedContext endpointType,
        ∃ pathType : TypeOver input.basedContext, ∃ path : Term input.basedContext pathType,
          endpointType.code = FormationSensitiveBasedIdentity.doubleWeaken input.type ∧
          endpoint.code = .var (1 : Fin 2) ∧
          QTerm.mk endpoint = (QuotientCwf.tmSub
            (rightEndpoint (formation HOLNativeRelatorCompatibility.rules)
              (context := (quotientProjection _).obj Common.context) (TermFibre.mk input.leftTerm))
            input.presentation.inv).val ∧
          pathType.code = .id (FormationSensitiveBasedIdentity.doubleWeaken input.type)
            (FormationSensitiveBasedIdentity.doubleWeaken input.left) (.var (1 : Fin 2)) ∧
          path.code = .var (0 : Fin 2) ∧
          QTerm.mk path = (QuotientCwf.tmSub
            (QuotientCwf.vz (witnessType (formation HOLNativeRelatorCompatibility.rules)
              (context := (quotientProjection _).obj Common.context) (TermFibre.mk input.leftTerm)))
            input.presentation.inv).val := by
  intro input
  obtain ⟨rightType, rightAnnotation, right, rightCode, _, rightValue⟩ :=
    admitted_right_meaning input
  obtain ⟨pathType, pathAnnotation, path, pathCode, _, pathValue⟩ :=
    admitted_witness_meaning input
  exact ⟨rightType, right, pathType, path, rightAnnotation, rightCode, rightValue,
    pathAnnotation, pathCode, pathValue⟩

theorem mixed_endpoint_is_not_path (wire : NativeWireData.Wire) :
    let input := QuotientIdentity.Controls.mixedInput wire
    (QuotientCwf.tmSub
      (rightEndpoint (formation HOLNativeRelatorCompatibility.rules)
        (context := (quotientProjection _).obj Common.context) (TermFibre.mk input.leftTerm))
      input.presentation.inv).val ≠
    (QuotientCwf.tmSub
      (QuotientCwf.vz (witnessType (formation HOLNativeRelatorCompatibility.rules)
        (context := (quotientProjection _).obj Common.context) (TermFibre.mk input.leftTerm)))
      input.presentation.inv).val :=
  admitted_right_ne_witness HOLNativeRelatorCompatibility.opacity
    (QuotientIdentity.Controls.mixedInput wire)

end Controls

end

#print axioms base_projection
#print axioms right_value
#print axioms witness_value
#print axioms base_projection_meaning
#print axioms right_meaning
#print axioms witness_meaning
#print axioms based_map_unique
#print axioms admitted_projection_meaning
#print axioms admitted_right_meaning
#print axioms admitted_witness_meaning
#print axioms admitted_right_ne_witness
#print axioms Controls.mixed_variables_represented
#print axioms Controls.mixed_endpoint_is_not_path

end FormationSensitiveContextual.QuotientBasedContextRepresentation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
