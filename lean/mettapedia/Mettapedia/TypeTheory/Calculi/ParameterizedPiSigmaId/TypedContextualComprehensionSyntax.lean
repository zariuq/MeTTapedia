import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualComparison
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Authored sections and lifts represent typed quotient comprehension

The native section is the actual single-variable substitution. The native
lift retains the supplied substitution underneath the binder and retypes the
source annotation through typed equality. Their quotient maps are compared
to the shared contextual self-extension and extension-substitution operations
using comprehension uniqueness. No reconstruction of original syntax from
a quotient point is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual.QuotientComprehensionSyntax

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable {levels : LevelModel rules L}

theorem transport_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty levels context} (same : first = second)
    (term : QuotientCwf.Tm levels context first) : (same ▸ term).val = term.val := by
  cases same
  rfl

theorem heq_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty levels context}
    {left : QuotientCwf.Tm levels context first} {right : QuotientCwf.Tm levels context second}
    (sameType : first = second) (same : HEq left right) : left.val = right.val := by
  cases sameType
  exact congrArg Subtype.val (eq_of_heq same)

theorem heq_of_value {context : QuotientCwf.QContext rules}
    {first second : QuotientCwf.Ty levels context}
    {left : QuotientCwf.Tm levels context first} {right : QuotientCwf.Tm levels context second}
    (same : left.val = right.val) : HEq left right := by
  have types : first = second := left.property.symm.trans
    ((congrArg (QTerm.type levels) same).trans right.property)
  cases types
  exact heq_of_eq (Subtype.ext same)

noncomputable def chosenTerm {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (term : QuotientCwf.Tm levels context type) :
    Term context.as (QuotientCwf.typeRepresentative type) :=
  QuotientCwf.termRepresentative _ term.val
    (term.property.trans (QuotientCwf.typeRepresentative_class type).symm)

theorem chosenTerm_class {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (term : QuotientCwf.Tm levels context type) :
    QTerm.mk levels (chosenTerm term) = term.val := QuotientCwf.termRepresentative_class _ _ _

theorem chosenTerm_represents {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (term : QuotientCwf.Tm levels context type)
    {annotation : TypeOver context.as} (actual : Term context.as annotation)
    (same : QTerm.mk levels actual = term.val) :
    Equal rules context.as.raw (chosenTerm term).code actual.code
      (QuotientCwf.typeRepresentative type).code :=
  ((QTerm.mk_eq_iff levels _ _).mp ((chosenTerm_class term).trans same.symm)).2

def nativeSection {context : Context rules} {type : TypeOver context} (argument : Term context type) :
    context ⟶ extend context type :=
  TypedContextual.pair (𝟙 context) (argument.cast type.reindex_id.symm)

theorem nativeSection_substitution {context : Context rules} {type : TypeOver context}
    (argument : Term context type) : (nativeSection argument).substitution = subst0 argument.code := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  exact Term.cast_code _ _

theorem nativeSection_projection {context : Context rules} {type : TypeOver context}
    (argument : Term context type) : nativeSection argument ≫ projectionHom context type = 𝟙 context :=
  TypedContextual.pair_projection _ _

theorem selfExtend_value {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (argument : QuotientCwf.Tm levels context type) :
    (QuotientCwf.tmSub (QuotientCwf.vz type) (selfExtend (QuotientCwf.cwf levels) argument)).val =
      argument.val := by
  change (QuotientCwf.tmSub (QuotientCwf.vz type)
    (QuotientCwf.pair (𝟙 context) type ((QuotientCwf.tySub_id type).symm ▸ argument))).val = _
  rw [QuotientCwf.vz_pair_value]
  exact transport_value _ _

set_option backward.isDefEq.respectTransparency false in
theorem nativeSection_projects {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (argument : QuotientCwf.Tm levels context type) :
    QuotientCwf.project (nativeSection (chosenTerm argument)) =
      selfExtend (QuotientCwf.cwf levels) argument := by
  apply QuotientCwf.pair_unique type
  · have rightBase : selfExtend (QuotientCwf.cwf levels) argument ≫ QuotientCwf.wk type = 𝟙 context :=
      QuotientCwf.wk_pair (𝟙 context) type ((QuotientCwf.tySub_id type).symm ▸ argument)
    exact ((quotientProjection rules).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeSection_projection (chosenTerm argument))).trans
        (((quotientProjection rules).map_id context.as).trans rightBase.symm))
  · rw [selfExtend_value]
    change QTerm.mk levels ((newest context.as (QuotientCwf.typeRepresentative type)).reindex
      (nativeSection (chosenTerm argument))) = argument.val
    rw [nativeSection, QuotientCwf.raw_newest_pair, QTerm.mk_cast]
    exact chosenTerm_class argument

theorem type_at_argument {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    (codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm levels context domain) :
    QType.mk levels ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection (chosenTerm argument))) =
      QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf levels) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk levels (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeSection_projects]; rfl

theorem term_at_argument {context : QuotientCwf.QContext rules}
    {domain : QuotientCwf.Ty levels context}
    {codomain : QuotientCwf.Ty levels (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm levels (QuotientCwf.ext context domain) codomain)
    (argument : QuotientCwf.Tm levels context domain) :
    QTerm.mk levels ((chosenTerm body).reindex (nativeSection (chosenTerm argument))) =
      (QuotientCwf.tmSub body (selfExtend (QuotientCwf.cwf levels) argument)).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk levels (chosenTerm body))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [chosenTerm_class, nativeSection_projects]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem nativeSection_projects_of_class {context : QuotientCwf.QContext rules}
    {type : QuotientCwf.Ty levels context} (argument : QuotientCwf.Tm levels context type)
    (actual : Term context.as (QuotientCwf.typeRepresentative type))
    (same : QTerm.mk levels actual = argument.val) :
    QuotientCwf.project (nativeSection actual) = selfExtend (QuotientCwf.cwf levels) argument := by
  have equal := (chosenTerm_represents argument actual same).symm
  have sections : QuotientCwf.project (nativeSection actual) =
      QuotientCwf.project (nativeSection (chosenTerm argument)) := by
    apply quotientProjection_pair_eq (homTypedEquality_refl _)
    rw [Term.cast_code, Term.cast_code]
    change Equal rules context.as.raw actual.code (chosenTerm argument).code
      (subst ids (QuotientCwf.typeRepresentative type).code)
    rw [subst_ids]
    exact equal
  exact sections.trans (nativeSection_projects argument)

/-- The unconverted lift lands in the target's actual supplied binder. -/
def rawLift {source target : Context rules} (morphism : source ⟶ target) (type : TypeOver target) :
    extend source (type.reindex morphism) ⟶ extend target type :=
  ⟨liftSub morphism.substitution, morphism.typed.lift type.code⟩

def convertedLift {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) (sourceType : TypeOver source)
    (same : TypeEq rules source.raw (subst morphism.substitution type.code) sourceType.code) :
    extend source sourceType ⟶ extend target type :=
  (extensionComparison sourceType (type.reindex morphism) same.symm).hom ≫ rawLift morphism type

set_option backward.isDefEq.respectTransparency false in
theorem convertedLift_substitution {source target : Context rules} (morphism : source ⟶ target)
    (type : TypeOver target) (sourceType : TypeOver source)
    (same : TypeEq rules source.raw (subst morphism.substitution type.code) sourceType.code) :
    (convertedLift morphism type sourceType same).substitution = liftSub morphism.substitution := by
  change subComp (extensionComparison sourceType (type.reindex morphism) same.symm).hom.substitution
    (liftSub morphism.substitution) = liftSub morphism.substitution
  rw [extensionComparison_hom_substitution]
  exact subComp_ids_left _

theorem reindexed_domain_equality {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    TypeEq rules source.as.raw
      (subst (QuotientCwf.representative morphism).substitution (QuotientCwf.typeRepresentative type).code)
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code :=
  (QType.mk_eq_iff levels _ _).mp ((QuotientCwf.represented_type_reindex type morphism).trans
    (QuotientCwf.typeRepresentative_class (QuotientCwf.tySub type morphism)).symm)

noncomputable def nativeLift {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as ⟶ (QuotientCwf.ext target type).as :=
  convertedLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative type)
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)) (reindexed_domain_equality morphism type)

theorem nativeLift_substitution {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    (nativeLift morphism type).substitution = liftSub (QuotientCwf.representative morphism).substitution :=
  convertedLift_substitution _ _ _ _

theorem nativeLift_projection {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    nativeLift morphism type ≫ projectionHom target.as (QuotientCwf.typeRepresentative type) =
      projectionHom source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)) ≫
        QuotientCwf.representative morphism := by
  apply Hom.ext
  change subComp (nativeLift morphism type).substitution projection =
    subComp projection (QuotientCwf.representative morphism).substitution
  rw [nativeLift_substitution]
  funext index
  change rename Presentation.wk ((QuotientCwf.representative morphism).substitution index) =
    subst projection ((QuotientCwf.representative morphism).substitution index)
  exact (subst_projection _).symm

set_option backward.isDefEq.respectTransparency false in
theorem nativeLift_newest {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    QTerm.mk levels ((newest target.as (QuotientCwf.typeRepresentative type)).reindex (nativeLift morphism type)) =
      QTerm.mk levels (newest source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))) := by
  apply (QTerm.mk_eq_iff levels _ _).mpr
  constructor
  · change TypeEq rules (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as.raw
      (subst (nativeLift morphism type).substitution (subst projection (QuotientCwf.typeRepresentative type).code))
      (subst projection (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code)
    rw [nativeLift_substitution, subst_projection, subst_projection, subst_liftSub_wk]
    exact (reindexed_domain_equality morphism type).rename
      (CtxRen.wk source.as.raw (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code)
  · let left := (newest target.as (QuotientCwf.typeRepresentative type)).reindex (nativeLift morphism type)
    have sameCode : left.code = Tm.var (0 : Fin (source.as.arity + 1)) := by
      change subst (nativeLift morphism type).substitution (.var (0 : Fin (target.as.arity + 1))) = _
      rw [nativeLift_substitution]
      rfl
    change Equal rules (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as.raw
      left.code (.var (0 : Fin (source.as.arity + 1)))
      (((QuotientCwf.typeRepresentative type).reindex
        (projectionHom target.as (QuotientCwf.typeRepresentative type))).reindex (nativeLift morphism type)).code
    rw [← sameCode]
    exact .refl left.typed

theorem extensionSubstitution_value {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    (QuotientCwf.tmSub (QuotientCwf.vz type)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism type)).val =
      (QuotientCwf.vz (QuotientCwf.tySub type morphism)).val := by
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf levels) morphism type
  have bases : lifted ≫ QuotientCwf.wk type = QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ morphism :=
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution (C := QuotientCwf.cwf levels) morphism type
  apply heq_value
  · exact (QuotientCwf.tySub_comp type lifted (QuotientCwf.wk type)).symm.trans
      ((congrArg (QuotientCwf.tySub type) bases).trans
        (QuotientCwf.tySub_comp type (QuotientCwf.wk (QuotientCwf.tySub type morphism)) morphism))
  · exact Mettapedia.GSLT.Core.ContextualLadder.TypeOver.vz_extensionSubstitution
      (C := QuotientCwf.cwf levels) morphism type

theorem nativeLift_projects {source target : QuotientCwf.QContext rules}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty levels target) :
    QuotientCwf.project (nativeLift morphism type) =
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf levels) morphism type := by
  apply QuotientCwf.pair_unique type
  · have rightBase := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
      (C := QuotientCwf.cwf levels) morphism type
    exact ((quotientProjection rules).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeLift_projection morphism type)).trans
        (((quotientProjection rules).map_comp _ _).trans
          ((congrArg (fun later => QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ later)
            (QuotientCwf.project_representative morphism)).trans rightBase.symm)))
  · exact (nativeLift_newest morphism type).trans (extensionSubstitution_value morphism type).symm

end TypedContextual.QuotientComprehensionSyntax
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
