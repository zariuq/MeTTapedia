import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientComprehensionSyntax
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientBasedContextRepresentation

/-!
# Reflexivity geometry of the formed quotient identity

The based reflexivity section is constructed from actual comprehension,
identity formation and reflexivity. Its dependent witness type is transported
using the proved identity-substitution law. No identity elimination operation
or motive coverage is needed to construct this geometry.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientIdentityGeometry

open _root_.CategoryTheory
open QuotientCwf
open Mettapedia.TypeTheory
open _root_.Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)
open _root_.Mettapedia.TypeTheory.ContextualBasedIdentityOperations
  (witnessType basedContext baseProjection rightEndpoint)
open QuotientComprehensionSyntax (nativeSection)

variable {Head : Type} {rules : Rules Head}

private theorem idTy_congr {context : QContext rules} {first second : Ty context}
    {left right : QuotientCwf.Tm context first} {nextLeft nextRight : QuotientCwf.Tm context second}
    (types : first = second) (lefts : HEq left nextLeft) (rights : HEq right nextRight) :
    QuotientIdentity.idTy first left right = QuotientIdentity.idTy second nextLeft nextRight := by
  cases types
  cases eq_of_heq lefts
  cases eq_of_heq rights
  rfl

/-- The witness fibre at the actual self-extension is the reflexive
identity type. The calculation uses the constructed substitution laws. -/
theorem witness_at_self {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    tySub (witnessType (QuotientIdentity.formation rules) left)
        (selfExtend (cwf rules) left) = QuotientIdentity.idTy type left left := by
  have sectionEq : selfExtend (cwf rules) left ≫ QuotientCwf.wk type = 𝟙 context :=
    ContextualTypeOperations.wk_selfExtend (C := cwf rules) left
  have types : tySub (tySub type (QuotientCwf.wk type))
      (selfExtend (cwf rules) left) = type :=
    (tySub_comp _ _ _).symm.trans
      ((congrArg (tySub type) sectionEq).trans (tySub_id type))
  have lefts : HEq (tmSub (tmSub left (QuotientCwf.wk type))
      (selfExtend (cwf rules) left)) left := by
    apply QuotientComprehensionSyntax.heq_of_value
    change totalSub (totalSub left.val (QuotientCwf.wk type))
      (selfExtend (cwf rules) left) = left.val
    exact (totalSub_comp _ _ _).symm.trans
      ((congrArg (totalSub left.val) sectionEq).trans (totalSub_id left.val))
  have rights : HEq (tmSub (vz type) (selfExtend (cwf rules) left)) left :=
    QuotientComprehensionSyntax.heq_of_value
      (QuotientComprehensionSyntax.selfExtend_value left)
  change tySub (QuotientIdentity.idTy (tySub type (QuotientCwf.wk type))
      (tmSub left (QuotientCwf.wk type)) (vz type)) (selfExtend (cwf rules) left) = _
  exact (QuotientIdentity.idTy_substitution _ _ _ _).trans (idTy_congr types lefts rights)

noncomputable def reflexivityAtSelf {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    QuotientCwf.Tm context
      (tySub (witnessType (QuotientIdentity.formation rules) left) (selfExtend (cwf rules) left)) :=
  cast (by rw [witness_at_self left]) (QuotientIdentity.refl left)

theorem reflexivityAtSelf_heq {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    HEq (reflexivityAtSelf left) (QuotientIdentity.refl left) := cast_heq _ _

/-- A genuine double-comprehension section, independent of any J field. -/
noncomputable def reflSection {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    context ⟶ basedContext (QuotientIdentity.formation rules) left :=
  (cwf rules).pair (selfExtend (cwf rules) left)
    (witnessType (QuotientIdentity.formation rules) left) (reflexivityAtSelf left)

theorem endpoint {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    (cwf rules).compS ((cwf rules).wk (witnessType (QuotientIdentity.formation rules) left))
        (reflSection left) = selfExtend (cwf rules) left :=
  (cwf rules).wk_pair _ _ _

theorem witness {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    HEq ((cwf rules).tmSub ((cwf rules).vz (witnessType (QuotientIdentity.formation rules) left))
      (reflSection left)) ((QuotientIdentity.reflexivity rules).refl left) :=
  (heq_of_eq ((cwf rules).vz_pair _ _ _)).trans
    ((cast_heq _ _).trans (reflexivityAtSelf_heq left))

theorem base {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    reflSection left ≫ baseProjection (QuotientIdentity.formation rules) left = 𝟙 context := by
  change reflSection left ≫ QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) left) ≫
    QuotientCwf.wk type = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun morphism => morphism ≫ QuotientCwf.wk type) (endpoint left)).trans
      (ContextualTypeOperations.wk_selfExtend (C := cwf rules) left))

theorem right_value {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    (tmSub (rightEndpoint (QuotientIdentity.formation rules) left) (reflSection left)).val =
      left.val := by
  change totalSub (totalSub (vz type).val
    (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) left))) (reflSection left) = _
  exact (totalSub_comp _ _ _).symm.trans
    ((congrArg (totalSub (vz type).val) (endpoint left)).trans
      (QuotientComprehensionSyntax.selfExtend_value left))

theorem witness_value {context : QContext rules} {type : Ty context}
    (left : QuotientCwf.Tm context type) :
    (tmSub (vz (witnessType (QuotientIdentity.formation rules) left)) (reflSection left)).val =
      (QuotientIdentity.refl left).val := by
  exact (vz_pair_value _ _ _).trans
    (cast_term_val (witness_at_self left).symm _ _)

theorem nativeWitness_at_self {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    (QuotientIdentity.nativeWitness type left).reindex (nativeSection left) =
      QuotientIdentity.nativeId type left left := by
  apply TypeOver.ext
  · change subst (nativeSection left).substitution
        (.id (subst projection type.code) (subst projection left.code) (.var 0)) =
      .id type.code left.code left.code
    rw [QuotientComprehensionSyntax.nativeSection_substitution]
    simp only [subst_projection, subst]
    change Presentation.Tm.id (inst0 left.code (rename Presentation.wk type.code))
      (inst0 left.code (rename Presentation.wk left.code)) left.code = _
    rw [inst0_rename_wk, inst0_rename_wk]
  · rfl

def nativeReflSection {context : Context rules} (type : TypeOver context) (left : Term context type) :
    context ⟶ extend (extend context type) (QuotientIdentity.nativeWitness type left) :=
  FormationSensitiveContextual.pair (nativeSection left)
    ((QuotientIdentity.nativeRefl left).cast (nativeWitness_at_self type left).symm)

theorem nativeReflSection_substitution {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    (nativeReflSection type left).substitution = consSub (.refl left.code) (consSub left.code ids) := by
  change consSub
    (((QuotientIdentity.nativeRefl left).cast (nativeWitness_at_self type left).symm).code)
    (nativeSection left).substitution = _
  rw [Term.cast_code, QuotientComprehensionSyntax.nativeSection_substitution]
  rfl

theorem native_base {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    nativeReflSection type left ≫
      QuotientBasedContextRepresentation.nativeBaseProjection type left = 𝟙 context :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun morphism => morphism ≫ projectionHom context type)
      (FormationSensitiveContextual.pair_projection _ _)).trans
        (QuotientComprehensionSyntax.nativeSection_projection left))

theorem native_right_value {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QTerm.mk ((QuotientBasedContextRepresentation.nativeRight type left).reindex
      (nativeReflSection type left)) = QTerm.mk left := by
  change ((QTerm.mk (newest context type)).reindex
    (projectionHom (extend context type) (QuotientIdentity.nativeWitness type left))).reindex
      (nativeReflSection type left) = _
  calc
    _ = (QTerm.mk (newest context type)).reindex
        (nativeReflSection type left ≫
          projectionHom (extend context type) (QuotientIdentity.nativeWitness type left)) :=
      (QTerm.reindex_comp _ _ _).symm
    _ = (QTerm.mk (newest context type)).reindex (nativeSection left) :=
      congrArg (QTerm.reindex (QTerm.mk (newest context type)))
        (FormationSensitiveContextual.pair_projection _ _)
    _ = _ := (raw_newest_pair _ _ _).trans (QuotientComprehensionSyntax.mk_cast _ _)

theorem native_witness_value {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    QTerm.mk ((QuotientBasedContextRepresentation.nativePath type left).reindex
      (nativeReflSection type left)) = QTerm.mk (QuotientIdentity.nativeRefl left) :=
  (raw_newest_pair _ _ _).trans (QuotientComprehensionSyntax.mk_cast _ _)

/-- The section uses the original admitted type and term, even when the
CwF's independently chosen representatives have different raw syntax. -/
theorem native_comparison {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    project (nativeReflSection type left) ≫ (QuotientIdentity.basedPresentation type left).inv =
      reflSection (context := (quotientProjection rules).obj context) (TermFibre.mk left) := by
  apply QuotientBasedContextRepresentation.based_map_unique (TermFibre.mk left)
  · exact (Category.assoc _ _ _).trans
      ((congrArg (fun morphism => project (nativeReflSection type left) ≫ morphism)
        (QuotientBasedContextRepresentation.base_projection type left)).trans
        (((quotientProjection rules).map_comp _ _).symm.trans
          ((congrArg project (native_base type left)).trans
            (((quotientProjection rules).map_id context).trans (base (TermFibre.mk left)).symm))))
  · exact (totalSub_comp
      (rightEndpoint (QuotientIdentity.formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left)).val
      (project (nativeReflSection type left)) (QuotientIdentity.basedPresentation type left).inv).trans
      ((congrArg (fun term => totalSub term (project (nativeReflSection type left)))
        (QuotientBasedContextRepresentation.right_value type left)).trans
          ((native_right_value type left).trans (right_value (TermFibre.mk left)).symm))
  · exact (totalSub_comp
      (vz (witnessType (QuotientIdentity.formation rules)
        (context := (quotientProjection rules).obj context) (TermFibre.mk left))).val
      (project (nativeReflSection type left)) (QuotientIdentity.basedPresentation type left).inv).trans
      ((congrArg (fun term => totalSub term (project (nativeReflSection type left)))
        (QuotientBasedContextRepresentation.witness_value type left)).trans
          ((native_witness_value type left).trans
            ((QuotientIdentity.refl_eq_native (TermFibre.mk left) type left rfl rfl).symm.trans
              (witness_value (TermFibre.mk left)).symm)))

theorem native_comparison_hom {context : Context rules} (type : TypeOver context)
    (left : Term context type) :
    reflSection (context := (quotientProjection rules).obj context) (TermFibre.mk left) ≫
        (QuotientIdentity.basedPresentation type left).hom = project (nativeReflSection type left) :=
  (congrArg (fun morphism => morphism ≫ (QuotientIdentity.basedPresentation type left).hom)
    (native_comparison type left).symm).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun morphism => project (nativeReflSection type left) ≫ morphism)
        (QuotientIdentity.basedPresentation type left).inv_hom_id).trans (Category.comp_id _)))

private theorem postcompose_eqToHom_substitution {source target other : Context rules}
    (same : target = other) (morphism : source ⟶ target) (index : Fin other.arity) :
    (morphism ≫ eqToHom same).substitution index =
      morphism.substitution
        (cast (congrArg (fun context : Context rules => Fin context.arity) same.symm) index) := by
  cases same
  rfl

/-- The native section retained in an admitted J input is the same typed
substitution as the canonical native section, after the proved telescope equality. -/
theorem admitted_native_section {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : QuotientIdentity.Based.Admitted context) :
    nativeReflSection input.element input.leftTerm ≫
      eqToHom (QuotientBasedContextRepresentation.input_context_eq input) = input.reflSection := by
  apply Hom.ext
  funext index
  rw [postcompose_eqToHom_substitution, nativeReflSection_substitution]
  rfl

/-- No J operation is used in this comparison: the independently retained
native reflexivity section agrees with the constructed CwF section. -/
theorem admitted_comparison {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : QuotientIdentity.Based.Admitted context) :
    input.chosenReflSection =
      reflSection (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm) := by
  have projected : project (nativeReflSection input.element input.leftTerm) ≫
      (eqToIso (congrArg (quotientProjection _).obj
        (QuotientBasedContextRepresentation.input_context_eq input))).hom =
      project input.reflSection := by
    calc
      _ = project (nativeReflSection input.element input.leftTerm ≫
          eqToHom (QuotientBasedContextRepresentation.input_context_eq input)) :=
        (congrArg (fun morphism => project (nativeReflSection input.element input.leftTerm) ≫ morphism)
          (eqToHom_map (quotientProjection (OpaqueRelatorExtension.rules signature))
            (QuotientBasedContextRepresentation.input_context_eq input)).symm).trans
          ((quotientProjection _).map_comp _ _).symm
      _ = _ := congrArg project (admitted_native_section input)
  have first := congrArg (fun morphism => morphism ≫ input.presentation.inv) projected.symm
  have cancellation :
      (eqToIso (congrArg (quotientProjection _).obj
        (QuotientBasedContextRepresentation.input_context_eq input))).hom ≫
        input.presentation.inv = (QuotientIdentity.basedPresentation input.element input.leftTerm).inv :=
    (Category.assoc
      (eqToIso (congrArg (quotientProjection _).obj
        (QuotientBasedContextRepresentation.input_context_eq input))).hom
      (eqToIso (congrArg (quotientProjection _).obj
        (QuotientBasedContextRepresentation.input_context_eq input))).inv
      (QuotientIdentity.basedPresentation input.element input.leftTerm).inv).symm.trans
      ((congrArg (fun morphism => morphism ≫
        (QuotientIdentity.basedPresentation input.element input.leftTerm).inv)
        (eqToIso (congrArg (quotientProjection _).obj
          (QuotientBasedContextRepresentation.input_context_eq input))).hom_inv_id).trans
        (Category.id_comp _))
  exact first.trans ((Category.assoc _ _ _).trans
    ((congrArg (fun morphism => project (nativeReflSection input.element input.leftTerm) ≫ morphism)
      cancellation).trans (native_comparison input.element input.leftTerm)))

/-- Every actually admitted motive retains its reflexivity fibre after
replacing the submitted section by the canonical geometric section. -/
theorem admitted_motive_reflexivity {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : QuotientIdentity.Based.Admitted context) :
    tySub (tySub (QType.mk input.motiveType) input.presentation.hom)
        (reflSection (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm)) =
      QType.mk input.methodType :=
  (congrArg (tySub (tySub (QType.mk input.motiveType) input.presentation.hom))
    (admitted_comparison input).symm).trans input.chosen_motive_reflexivity

theorem admitted_beta_value {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : QuotientIdentity.Based.Admitted context) :
    (tmSub input.chosenJ
      (reflSection (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))).val =
      input.base.val :=
  (congrArg (fun morphism => (tmSub input.chosenJ morphism).val)
    (admitted_comparison input).symm).trans input.chosen_beta_value

theorem admitted_beta {signature : Declaration.Signature Tower.Head}
    {context : Context (OpaqueRelatorExtension.rules signature)}
    (input : QuotientIdentity.Based.Admitted context) :
    TermFibre.compare (admitted_motive_reflexivity input)
      (tmSub input.chosenJ
        (reflSection (context := (quotientProjection _).obj context) (TermFibre.mk input.leftTerm))) =
      input.base := Subtype.ext (admitted_beta_value input)

/-! ## Mixed native controls and the elimination-scope boundary -/

namespace Controls

/-- The motive depends on both the varying endpoint and its path. The
ambient declaration environment contains the actual HOL/list/wire package. -/
theorem mixed_motive_and_beta (wire : NativeWireData.Wire) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules
        (QuotientIdentity.Controls.mixedInput wire).basedContext.raw
        (QuotientIdentity.Controls.mixedInput wire).nativeJ.code
        (QuotientIdentity.Controls.mixedInput wire).motiveType.code ∧
      tySub (tySub (QType.mk (QuotientIdentity.Controls.mixedInput wire).motiveType)
          (QuotientIdentity.Controls.mixedInput wire).presentation.hom)
        (reflSection (context := (quotientProjection _).obj Common.context)
          (TermFibre.mk (QuotientIdentity.Controls.mixedInput wire).leftTerm)) =
        QType.mk (QuotientIdentity.Controls.mixedInput wire).methodType ∧
      (tmSub (QuotientIdentity.Controls.mixedInput wire).chosenJ
        (reflSection (context := (quotientProjection _).obj Common.context)
          (TermFibre.mk (QuotientIdentity.Controls.mixedInput wire).leftTerm))).val =
        (QuotientIdentity.Controls.mixedInput wire).base.val :=
  ⟨(QuotientIdentity.Controls.mixedInput wire).nativeJ.judgment,
    admitted_motive_reflexivity _, admitted_beta_value _⟩

/-- The section returns 7, not 8; both values remain independently
admitted at the same native Data type. -/
theorem changed_endpoint :
    (tmSub (rightEndpoint (QuotientIdentity.formation HOLNativeRelatorCompatibility.rules)
      (QuotientCwf.Controls.result (.natural 7)))
      (reflSection (QuotientCwf.Controls.result (.natural 7)))).val ≠
        QTerm.mk (Common.result (.natural 8)) := by
  intro same
  exact FibreControls.seven_eight_distinct
    ((right_value (QuotientCwf.Controls.result (.natural 7))).symm.trans same)

theorem changed_endpoint_still_admitted :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules Common.context.raw
      (Common.result (.natural 8)).code Common.wireType.code :=
  (Common.result (.natural 8)).judgment

/-- Geometry at this domain is constructed, while the actual fixed J
declaration still rejects that same domain. No total J is inferred. -/
theorem geometry_beyond_fixed_j :
    project (nativeReflSection (QuotientIdentity.LevelBoundary.largeDomain Common.context)
        (QuotientIdentity.LevelBoundary.largePoint Common.context)) ≫
      (QuotientIdentity.basedPresentation
        (QuotientIdentity.LevelBoundary.largeDomain Common.context)
        (QuotientIdentity.LevelBoundary.largePoint Common.context)).inv =
      reflSection (context := (quotientProjection _).obj Common.context)
        (TermFibre.mk (QuotientIdentity.LevelBoundary.largePoint Common.context)) ∧
      ¬ ∃ input : QuotientIdentity.Based.Admitted
          (signature := HOLNativeRelatorCompatibility.signature) Common.context,
        input.type = (QuotientIdentity.LevelBoundary.largeDomain Common.context).code :=
  ⟨native_comparison _ _,
    (QuotientIdentity.LevelBoundary.identity_exists_beyond_fixed_j
      HOLNativeRelatorCompatibility.opacity Common.context).2⟩

end Controls

#print axioms witness_at_self
#print axioms endpoint
#print axioms witness
#print axioms native_comparison
#print axioms admitted_comparison
#print axioms admitted_motive_reflexivity
#print axioms admitted_beta
#print axioms Controls.mixed_motive_and_beta
#print axioms Controls.changed_endpoint
#print axioms Controls.geometry_beyond_fixed_j

end FormationSensitiveContextual.QuotientIdentityGeometry
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
