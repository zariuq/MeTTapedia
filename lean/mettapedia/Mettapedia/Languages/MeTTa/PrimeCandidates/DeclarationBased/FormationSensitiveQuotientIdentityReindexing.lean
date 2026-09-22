import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.FormationSensitiveQuotientIdentityGeometry

/-!
# Reindexing the formed quotient based-identity context

The endpoint lift is the existing comprehension lift. Identity formation
and its proved substitution law identify the dependent witness fibre;
a second comprehension pair supplies the based-context map. Its geometry
and reflexivity square do not require an identity eliminator.
In particular, these maps make no claim about J descending from motive-body
classes, and introduce no eta or identity conversion equation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientIdentityReindexing

open _root_.CategoryTheory
open QuotientCwf
open Mettapedia.TypeTheory.ContextualBasedIdentityOperations
  (witnessType basedContext baseProjection rightEndpoint Reindexing)
open Mettapedia.GSLT.Core.ContextualLadder.TypeOver
  (extensionSubstitution wk_extensionSubstitution)
open QuotientIdentityGeometry (reflSection)

variable {Head : Type} {rules : Rules Head}

private theorem idTy_congr {context : QContext rules} {first second : Ty context}
    {left right : QuotientCwf.Tm context first} {nextLeft nextRight : QuotientCwf.Tm context second}
    (types : first = second) (lefts : HEq left nextLeft) (rights : HEq right nextRight) :
    QuotientIdentity.idTy first left right = QuotientIdentity.idTy second nextLeft nextRight := by
  cases types
  cases eq_of_heq lefts
  cases eq_of_heq rights
  rfl

/-- The entire endpoint-dependent witness fibre is stable under the
actual comprehension lift, including the substituted fixed endpoint. -/
theorem witness_substitution {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    tySub (witnessType (QuotientIdentity.formation rules) left)
        (extensionSubstitution (C := cwf rules) morphism type) =
      witnessType (QuotientIdentity.formation rules) (tmSub left morphism) := by
  have projectionEq : extensionSubstitution (C := cwf rules) morphism type ≫ QuotientCwf.wk type =
      QuotientCwf.wk (tySub type morphism) ≫ morphism :=
    wk_extensionSubstitution (C := cwf rules) morphism type
  have types : tySub (tySub type (QuotientCwf.wk type))
      (extensionSubstitution (C := cwf rules) morphism type) =
      tySub (tySub type morphism) (QuotientCwf.wk (tySub type morphism)) :=
    (tySub_comp _ _ _).symm.trans
      ((congrArg (tySub type) projectionEq).trans (tySub_comp _ _ _))
  have lefts : HEq (tmSub (tmSub left (QuotientCwf.wk type))
      (extensionSubstitution (C := cwf rules) morphism type))
      (tmSub (tmSub left morphism) (QuotientCwf.wk (tySub type morphism))) := by
    apply QuotientComprehensionSyntax.heq_of_value
    exact (totalSub_comp left.val
      (extensionSubstitution (C := cwf rules) morphism type) (QuotientCwf.wk type)).symm.trans
      ((congrArg (totalSub left.val) projectionEq).trans (totalSub_comp _ _ _))
  have rights : HEq
      (tmSub (vz type) (extensionSubstitution (C := cwf rules) morphism type))
      (vz (tySub type morphism)) :=
    QuotientComprehensionSyntax.heq_of_value
      (QuotientComprehensionSyntax.extensionSubstitution_value morphism type)
  exact (QuotientIdentity.idTy_substitution
    (extensionSubstitution (C := cwf rules) morphism type)
    (tySub type (QuotientCwf.wk type)) (tmSub left (QuotientCwf.wk type)) (vz type)).trans
      (idTy_congr types lefts rights)

theorem pathType_substitution {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    tySub (witnessType (QuotientIdentity.formation rules) left)
        (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)) ≫
          extensionSubstitution (C := cwf rules) morphism type) =
      tySub (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))
        (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))) :=
  (tySub_comp _ _ _).trans
    (congrArg (fun next => tySub next
      (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))))
      (witness_substitution morphism left))

noncomputable def transportedPath {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    QuotientCwf.Tm (basedContext (QuotientIdentity.formation rules) (tmSub left morphism))
      (tySub (witnessType (QuotientIdentity.formation rules) left)
        (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)) ≫
          extensionSubstitution (C := cwf rules) morphism type)) :=
  cast (congrArg (QuotientCwf.Tm _) (pathType_substitution morphism left).symm)
    (vz (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)))

theorem transportedPath_value {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    (transportedPath morphism left).val =
      (vz (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))).val :=
  cast_term_val (pathType_substitution morphism left).symm _ _

/-- Two actual comprehension lifts, with only their dependent annotation
transported by the previously proved identity-substitution equation. -/
noncomputable def map {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    (cwf rules).Sub
      (basedContext (QuotientIdentity.formation rules) (tmSub left morphism))
      (basedContext (QuotientIdentity.formation rules) left) :=
  QuotientCwf.pair
    (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)) ≫
      extensionSubstitution (C := cwf rules) morphism type)
    (witnessType (QuotientIdentity.formation rules) left) (transportedPath morphism left)

noncomputable def reindexing (rules : Rules Head) : Reindexing (QuotientIdentity.formation rules) where
  map := map

theorem endpoint_projection {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    map morphism left ≫ QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) left) =
      QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)) ≫
        extensionSubstitution (C := cwf rules) morphism type :=
  wk_pair _ _ _

theorem witness_value {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    (tmSub (vz (witnessType (QuotientIdentity.formation rules) left)) (map morphism left)).val =
      (vz (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))).val :=
  (vz_pair_value _ _ _).trans (transportedPath_value morphism left)

theorem base_projection {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    map morphism left ≫ baseProjection (QuotientIdentity.formation rules) left =
      baseProjection (QuotientIdentity.formation rules) (tmSub left morphism) ≫ morphism :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun next => next ≫ QuotientCwf.wk type) (endpoint_projection morphism left)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun next =>
          QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)) ≫ next)
          (wk_extensionSubstitution (C := cwf rules) morphism type)).trans
          (Category.assoc _ _ _).symm)))

theorem endpoint_value {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    (tmSub (rightEndpoint (QuotientIdentity.formation rules) left) (map morphism left)).val =
      (rightEndpoint (QuotientIdentity.formation rules) (tmSub left morphism)).val :=
  (totalSub_comp (vz type).val (map morphism left)
    (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) left))).symm.trans
    ((congrArg (totalSub (vz type).val) (endpoint_projection morphism left)).trans
      ((totalSub_comp (vz type).val
        (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism)))
        (extensionSubstitution (C := cwf rules) morphism type)).trans
        (congrArg (fun next => totalSub next
          (QuotientCwf.wk (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))))
          (QuotientComprehensionSyntax.extensionSubstitution_value morphism type))))

theorem endpoint {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    HEq (tmSub (rightEndpoint (QuotientIdentity.formation rules) left) (map morphism left))
      (rightEndpoint (QuotientIdentity.formation rules) (tmSub left morphism)) :=
  QuotientComprehensionSyntax.heq_of_value (endpoint_value morphism left)

theorem witness {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    HEq (tmSub (vz (witnessType (QuotientIdentity.formation rules) left)) (map morphism left))
      (vz (witnessType (QuotientIdentity.formation rules) (tmSub left morphism))) :=
  QuotientComprehensionSyntax.heq_of_value (witness_value morphism left)

theorem reflexivity_base {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    (reflSection (tmSub left morphism) ≫ map morphism left) ≫
      baseProjection (QuotientIdentity.formation rules) left = morphism :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun next => reflSection (tmSub left morphism) ≫ next)
      (base_projection morphism left)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun next => next ≫ morphism)
          (QuotientIdentityGeometry.base (tmSub left morphism))).trans (Category.id_comp _))))

/-- The square is a theorem about the constructed frame maps. It neither
requires an `Elimination` record nor supplies a J operation. -/
theorem reflexivity_square {source target : QContext rules}
    (morphism : source ⟶ target) {type : Ty target} (left : QuotientCwf.Tm target type) :
    reflSection (tmSub left morphism) ≫ map morphism left = morphism ≫ reflSection left := by
  apply QuotientBasedContextRepresentation.based_map_unique left
  · have second : (morphism ≫ reflSection left) ≫
        baseProjection (QuotientIdentity.formation rules) left = morphism :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun next => morphism ≫ next) (QuotientIdentityGeometry.base left)).trans
          (Category.comp_id _))
    exact (reflexivity_base morphism left).trans second.symm
  · have first : totalSub (rightEndpoint (QuotientIdentity.formation rules) left).val
        (reflSection (tmSub left morphism) ≫ map morphism left) = (tmSub left morphism).val :=
      (totalSub_comp _ _ _).trans
        ((congrArg (fun next => totalSub next (reflSection (tmSub left morphism)))
          (endpoint_value morphism left)).trans
          (QuotientIdentityGeometry.right_value (tmSub left morphism)))
    have second : totalSub (rightEndpoint (QuotientIdentity.formation rules) left).val
        (morphism ≫ reflSection left) = (tmSub left morphism).val :=
      (totalSub_comp _ _ _).trans
        (congrArg (fun next => totalSub next morphism) (QuotientIdentityGeometry.right_value left))
    exact first.trans second.symm
  · have first : totalSub (vz (witnessType (QuotientIdentity.formation rules) left)).val
        (reflSection (tmSub left morphism) ≫ map morphism left) =
        (QuotientIdentity.refl (tmSub left morphism)).val :=
      (totalSub_comp _ _ _).trans
        ((congrArg (fun next => totalSub next (reflSection (tmSub left morphism)))
          (witness_value morphism left)).trans
          (QuotientIdentityGeometry.witness_value (tmSub left morphism)))
    have second : totalSub (vz (witnessType (QuotientIdentity.formation rules) left)).val
        (morphism ≫ reflSection left) = (QuotientIdentity.refl (tmSub left morphism)).val :=
      (totalSub_comp _ _ _).trans
        ((congrArg (fun next => totalSub next morphism) (QuotientIdentityGeometry.witness_value left)).trans
          (QuotientIdentity.refl_substitution_value morphism left))
    exact first.trans second.symm

/-! ## A real free-variable substitution in the common native environment -/

namespace Controls

def variableContext : Context HOLNativeRelatorCompatibility.rules :=
  extend Common.context Common.wireType

def variableType : TypeOver variableContext :=
  Common.wireType.reindex (projectionHom Common.context Common.wireType)

def nativeVariable : Term variableContext variableType :=
  newest Common.context Common.wireType

def point : QuotientCwf.Tm ((quotientProjection _).obj variableContext) (QType.mk variableType) :=
  TermFibre.mk nativeVariable

/-- The substituted value is submitted native syntax, not a decoder for
semantic classes. Its context contains a genuine free Data variable. -/
def nativeSubstitution (wire : NativeWireData.Wire) : Common.context ⟶ variableContext :=
  QuotientComprehensionSyntax.nativeSection (Common.result wire)

def substitution (wire : NativeWireData.Wire) :
    (quotientProjection _).obj Common.context ⟶ (quotientProjection _).obj variableContext :=
  project (nativeSubstitution wire)

theorem variable_substitution (wire : NativeWireData.Wire) :
    (tmSub point (substitution wire)).val = QTerm.mk (Common.result wire) :=
  (raw_newest_pair _ _ _).trans (QuotientComprehensionSyntax.mk_cast _ _)

theorem instantiated_reflexivity (wire : NativeWireData.Wire) :
    (QuotientIdentity.refl (tmSub point (substitution wire))).val =
      QTerm.mk (QuotientIdentity.nativeRefl (Common.result wire)) := by
  apply QuotientIdentity.refl_eq_native _ Common.wireType (Common.result wire)
  · exact (congrArg QTerm.type (variable_substitution wire)).symm.trans
      (tmSub point (substitution wire)).property
  · exact (variable_substitution wire).symm

/-- The square and resulting native reflexivity are proved for every
supplied wire value, not only an identity substitution or a closed point. -/
theorem actual_substitution_crown (wire : NativeWireData.Wire) :
    FormationSensitive.Judgment HOLNativeRelatorCompatibility.rules variableContext.raw
        nativeVariable.code variableType.code ∧
      reflSection (tmSub point (substitution wire)) ≫ map (substitution wire) point =
        substitution wire ≫ reflSection point ∧
      (QuotientIdentity.refl (tmSub point (substitution wire))).val =
        QTerm.mk (QuotientIdentity.nativeRefl (Common.result wire)) :=
  ⟨nativeVariable.judgment, reflexivity_square _ _, instantiated_reflexivity wire⟩

theorem transported_variable (wire : NativeWireData.Wire) :
    totalSub point.val
      ((reflSection (tmSub point (substitution wire)) ≫ map (substitution wire) point) ≫
        baseProjection (QuotientIdentity.formation HOLNativeRelatorCompatibility.rules) point) =
      QTerm.mk (Common.result wire) :=
  (congrArg (totalSub point.val) (reflexivity_base (substitution wire) point)).trans
    (variable_substitution wire)

theorem changed_value_rejected :
    totalSub point.val
      ((reflSection (tmSub point (substitution (.natural 7))) ≫
        map (substitution (.natural 7)) point) ≫
        baseProjection (QuotientIdentity.formation HOLNativeRelatorCompatibility.rules) point) ≠
      QTerm.mk (Common.result (.natural 8)) := by
  intro same
  exact FibreControls.seven_eight_distinct
    ((transported_variable (.natural 7)).symm.trans same)

theorem changed_substitution_is_independently_admitted :
    FormationSensitive.CtxMor HOLNativeRelatorCompatibility.rules variableContext.raw Common.context.raw
      (nativeSubstitution (.natural 8)).substitution :=
  (nativeSubstitution (.natural 8)).typed

end Controls

#print axioms witness_substitution
#print axioms base_projection
#print axioms endpoint
#print axioms witness
#print axioms reflexivity_square
#print axioms Controls.actual_substitution_crown
#print axioms Controls.changed_value_rejected
end FormationSensitiveContextual.QuotientIdentityReindexing
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
