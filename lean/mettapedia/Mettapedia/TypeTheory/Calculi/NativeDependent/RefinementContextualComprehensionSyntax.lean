import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualComparison
import Mettapedia.TypeTheory.ContextualTypeOperations

/-!
# Mixed generated sections and selected contextual lifts

The native section is the actual single-variable substitution. The native
lift retains the supplied substitution underneath the binder and retypes the
source annotation through typed equality. Their quotient maps are compared
to the shared contextual self-extension and extension-substitution operations
using comprehension uniqueness. No reconstruction of original syntax from
a quotient point is used.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.QuotientComprehensionSyntax

open _root_.CategoryTheory

universe u
open Mettapedia.TypeTheory.ContextualProductComparison (selfExtend)

variable {S : Symbols.{u}} {D : Signature S}

theorem transport_value {context : QuotientCwf.QContext D}
    {first second : QuotientCwf.Ty context} (same : first = second)
    (term : QuotientCwf.Tm context first) : (same ▸ term).val = term.val := by
  cases same
  rfl

theorem heq_value {context : QuotientCwf.QContext D}
    {first second : QuotientCwf.Ty context}
    {left : QuotientCwf.Tm context first} {right : QuotientCwf.Tm context second}
    (sameType : first = second) (same : HEq left right) : left.val = right.val := by
  cases sameType
  exact congrArg Subtype.val (eq_of_heq same)

theorem heq_of_value {context : QuotientCwf.QContext D}
    {first second : QuotientCwf.Ty context}
    {left : QuotientCwf.Tm context first} {right : QuotientCwf.Tm context second}
    (same : left.val = right.val) : HEq left right := by
  have types : first = second := left.property.symm.trans
    ((congrArg (QTerm.type) same).trans right.property)
  cases types
  exact heq_of_eq (Subtype.ext same)

noncomputable def chosenTerm {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    Term context.as (QuotientCwf.typeRepresentative type) :=
  QuotientCwf.termRepresentative _ term.val
    (term.property.trans (QuotientCwf.typeRepresentative_class type).symm)

theorem chosenTerm_class {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type) :
    QTerm.mk (chosenTerm term) = term.val := QuotientCwf.termRepresentative_class _ _ _

theorem chosenTerm_represents {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (term : QuotientCwf.Tm context type)
    {annotation : TypeOver context.as} (actual : Term context.as annotation)
    (same : QTerm.mk actual = term.val) :
    Holds D (.termEq context.as.raw (chosenTerm term).code actual.code
      (QuotientCwf.typeRepresentative type).code) :=
  ((QTerm.mk_eq_iff _ _).mp ((chosenTerm_class term).trans same.symm)).2

def nativeSection {context : Context D} {type : TypeOver context} (argument : Term context type) :
    context ⟶ extend context type :=
  Contextual.pair (𝟙 context) (argument.cast type.reindex_id.symm)

theorem nativeSection_substitution {context : Context D} {type : TypeOver context}
    (argument : Term context type) : (nativeSection argument).substitution = instantiate argument.code := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  exact Term.cast_code _ _

theorem nativeSection_projection {context : Context D} {type : TypeOver context}
    (argument : Term context type) : nativeSection argument ≫ projectionHom context type = 𝟙 context :=
  Contextual.pair_projection _ _

theorem selfExtend_value {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type) :
    (QuotientCwf.tmSub (QuotientCwf.vz type) (selfExtend (QuotientCwf.cwf D) argument)).val =
      argument.val := by
  change (QuotientCwf.tmSub (QuotientCwf.vz type)
    (QuotientCwf.pair (𝟙 context) type ((QuotientCwf.tySub_id type).symm ▸ argument))).val = _
  rw [QuotientCwf.vz_pair_value]
  exact transport_value _ _

set_option backward.isDefEq.respectTransparency false in
theorem nativeSection_projects {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type) :
    QuotientCwf.project (nativeSection (chosenTerm argument)) =
      selfExtend (QuotientCwf.cwf D) argument := by
  apply QuotientCwf.pair_unique type
  · have rightBase : selfExtend (QuotientCwf.cwf D) argument ≫ QuotientCwf.wk type = 𝟙 context :=
      QuotientCwf.wk_pair (𝟙 context) type ((QuotientCwf.tySub_id type).symm ▸ argument)
    exact ((quotientProjection D).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeSection_projection (chosenTerm argument))).trans
        (((quotientProjection D).map_id context.as).trans rightBase.symm))
  · rw [selfExtend_value]
    change QTerm.mk ((newest context.as (QuotientCwf.typeRepresentative type)).reindex
      (nativeSection (chosenTerm argument))) = argument.val
    rw [nativeSection, QuotientCwf.raw_newest_pair, QTerm.mk_cast]
    exact chosenTerm_class argument

theorem type_at_argument {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    (codomain : QuotientCwf.Ty (QuotientCwf.ext context domain))
    (argument : QuotientCwf.Tm context domain) :
    QType.mk ((QuotientCwf.typeRepresentative codomain).reindex (nativeSection (chosenTerm argument))) =
      QuotientCwf.tySub codomain (selfExtend (QuotientCwf.cwf D) argument) := by
  calc
    _ = QuotientCwf.tySub (QType.mk (QuotientCwf.typeRepresentative codomain))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [QuotientCwf.typeRepresentative_class, nativeSection_projects]; rfl

theorem term_at_argument {context : QuotientCwf.QContext D}
    {domain : QuotientCwf.Ty context}
    {codomain : QuotientCwf.Ty (QuotientCwf.ext context domain)}
    (body : QuotientCwf.Tm (QuotientCwf.ext context domain) codomain)
    (argument : QuotientCwf.Tm context domain) :
    QTerm.mk ((chosenTerm body).reindex (nativeSection (chosenTerm argument))) =
      (QuotientCwf.tmSub body (selfExtend (QuotientCwf.cwf D) argument)).val := by
  calc
    _ = QuotientCwf.totalSub (QTerm.mk (chosenTerm body))
        (QuotientCwf.project (nativeSection (chosenTerm argument))) := rfl
    _ = _ := by rw [chosenTerm_class, nativeSection_projects]; rfl

set_option backward.isDefEq.respectTransparency false in
theorem nativeSection_projects_of_class {context : QuotientCwf.QContext D}
    {type : QuotientCwf.Ty context} (argument : QuotientCwf.Tm context type)
    (actual : Term context.as (QuotientCwf.typeRepresentative type))
    (same : QTerm.mk actual = argument.val) :
    QuotientCwf.project (nativeSection actual) = selfExtend (QuotientCwf.cwf D) argument := by
  have equal := termEquality_symm (chosenTerm_represents argument actual same)
  have sections : QuotientCwf.project (nativeSection actual) =
      QuotientCwf.project (nativeSection (chosenTerm argument)) := by
    apply (quotientProjection_map_eq_iff _ _).mpr
    apply homEquality_pair (homEquality_refl _)
    rw [Term.cast_code, Term.cast_code]
    change Holds D (.termEq context.as.raw actual.code (chosenTerm argument).code
      ((QuotientCwf.typeRepresentative type).code.substitute TermExpr.var))
    rw [TypeExpr.substitute_identity]
    exact equal
  exact sections.trans (nativeSection_projects argument)

/-- The unconverted lift lands in the target's actual supplied binder. -/
def rawLift {source target : Context D} (morphism : source ⟶ target) (type : TypeOver target) :
    extend source (type.reindex morphism) ⟶ extend target type :=
  Contextual.pair (projectionHom source (type.reindex morphism) ≫ morphism)
    ((newest source (type.reindex morphism)).cast
      (type.reindex_comp (projectionHom source (type.reindex morphism)) morphism).symm)

theorem rawLift_substitution {source target : Context D} (morphism : source ⟶ target)
    (type : TypeOver target) :
    (rawLift morphism type).substitution = liftSubstitution morphism.substitution := by
  funext index
  cases index using Fin.cases with
  | zero => exact Term.cast_code _ _
  | succ index =>
      change (morphism.substitution index).substitute (fun i => .var i.succ) =
        (morphism.substitution index).rename Fin.succ
      exact TermExpr.substitute_variables _ _

def convertedLift {source target : Context D} (morphism : source ⟶ target)
    (type : TypeOver target) (sourceType : TypeOver source)
    (same : Holds D (.typeEq source.raw (type.code.substitute morphism.substitution) sourceType.code)) :
    extend source sourceType ⟶ extend target type :=
  (extensionComparison sourceType (type.reindex morphism) (typeEquality_symm same)).hom ≫ rawLift morphism type

set_option backward.isDefEq.respectTransparency false in
theorem convertedLift_substitution {source target : Context D} (morphism : source ⟶ target)
    (type : TypeOver target) (sourceType : TypeOver source)
    (same : Holds D (.typeEq source.raw (type.code.substitute morphism.substitution) sourceType.code)) :
    (convertedLift morphism type sourceType same).substitution = liftSubstitution morphism.substitution := by
  change composeSubstitution (rawLift morphism type).substitution
    (extensionComparison sourceType (type.reindex morphism) (typeEquality_symm same)).hom.substitution = _
  rw [extensionComparison_hom_substitution, composeSubstitution_identity]
  exact rawLift_substitution morphism type

theorem reindexed_domain_equality {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    Holds D (.typeEq source.as.raw
      ((QuotientCwf.typeRepresentative type).code.substitute (QuotientCwf.representative morphism).substitution)
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code) :=
  (QType.mk_eq_iff _ _).mp ((QuotientCwf.represented_type_reindex type morphism).trans
    (QuotientCwf.typeRepresentative_class (QuotientCwf.tySub type morphism)).symm)

noncomputable def nativeLift {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as ⟶ (QuotientCwf.ext target type).as :=
  convertedLift (QuotientCwf.representative morphism) (QuotientCwf.typeRepresentative type)
    (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)) (reindexed_domain_equality morphism type)

theorem nativeLift_substitution {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    (nativeLift morphism type).substitution = liftSubstitution (QuotientCwf.representative morphism).substitution :=
  convertedLift_substitution _ _ _ _

theorem nativeLift_projection {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    nativeLift morphism type ≫ projectionHom target.as (QuotientCwf.typeRepresentative type) =
      projectionHom source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)) ≫
        QuotientCwf.representative morphism := by
  apply Hom.ext
  change composeSubstitution (fun index => .var index.succ) (nativeLift morphism type).substitution =
    composeSubstitution (QuotientCwf.representative morphism).substitution (fun index => .var index.succ)
  rw [nativeLift_substitution]
  funext index
  change ((QuotientCwf.representative morphism).substitution index).rename Fin.succ =
    ((QuotientCwf.representative morphism).substitution index).substitute (fun index => .var index.succ)
  exact (TermExpr.substitute_variables _ _).symm

set_option backward.isDefEq.respectTransparency false in
theorem nativeLift_newest {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    QTerm.mk ((newest target.as (QuotientCwf.typeRepresentative type)).reindex (nativeLift morphism type)) =
      QTerm.mk (newest source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))) := by
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · change Holds D (.typeEq (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as.raw
      (((QuotientCwf.typeRepresentative type).code.substitute (fun index => .var index.succ)).substitute
        (nativeLift morphism type).substitution)
      ((QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)).code.substitute
        (fun index => .var index.succ)))
    rw [nativeLift_substitution, TypeExpr.substitute_variables, TypeExpr.substitute_variables,
      TypeExpr.substitute_weaken]
    change Holds D (.typeEq (extend source.as
      (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism))).raw _ _)
    simpa only [projectionHom, TypeExpr.substitute_variables] using
      reindex_typeEquality (reindexed_domain_equality morphism type)
        (projectionHom source.as (QuotientCwf.typeRepresentative (QuotientCwf.tySub type morphism)))
  · let left := (newest target.as (QuotientCwf.typeRepresentative type)).reindex (nativeLift morphism type)
    have sameCode : left.code = TermExpr.var (0 : Fin (source.as.arity + 1)) := by
      change (.var (0 : Fin (target.as.arity + 1)) : TermExpr S _).substitute
        (nativeLift morphism type).substitution = _
      rw [nativeLift_substitution]
      rfl
    change Holds D (.termEq (QuotientCwf.ext source (QuotientCwf.tySub type morphism)).as.raw
      left.code (.var (0 : Fin (source.as.arity + 1)))
      (((QuotientCwf.typeRepresentative type).reindex
        (projectionHom target.as (QuotientCwf.typeRepresentative type))).reindex (nativeLift morphism type)).code)
    rw [← sameCode]
    exact termEquality_refl left

theorem extensionSubstitution_value {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    (QuotientCwf.tmSub (QuotientCwf.vz type)
      (Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism type)).val =
      (QuotientCwf.vz (QuotientCwf.tySub type morphism)).val := by
  let lifted := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
    (C := QuotientCwf.cwf D) morphism type
  have bases : lifted ≫ QuotientCwf.wk type = QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ morphism :=
    Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution (C := QuotientCwf.cwf D) morphism type
  apply heq_value
  · exact (QuotientCwf.tySub_comp type lifted (QuotientCwf.wk type)).symm.trans
      ((congrArg (QuotientCwf.tySub type) bases).trans
        (QuotientCwf.tySub_comp type (QuotientCwf.wk (QuotientCwf.tySub type morphism)) morphism))
  · exact Mettapedia.GSLT.Core.ContextualLadder.TypeOver.vz_extensionSubstitution
      (C := QuotientCwf.cwf D) morphism type

theorem nativeLift_projects {source target : QuotientCwf.QContext D}
    (morphism : source ⟶ target) (type : QuotientCwf.Ty target) :
    QuotientCwf.project (nativeLift morphism type) =
      Mettapedia.GSLT.Core.ContextualLadder.TypeOver.extensionSubstitution
        (C := QuotientCwf.cwf D) morphism type := by
  apply QuotientCwf.pair_unique type
  · have rightBase := Mettapedia.GSLT.Core.ContextualLadder.TypeOver.wk_extensionSubstitution
      (C := QuotientCwf.cwf D) morphism type
    exact ((quotientProjection D).map_comp _ _).symm.trans
      ((congrArg QuotientCwf.project (nativeLift_projection morphism type)).trans
        (((quotientProjection D).map_comp _ _).trans
          ((congrArg (fun later => QuotientCwf.wk (QuotientCwf.tySub type morphism) ≫ later)
            (QuotientCwf.project_representative morphism)).trans rightBase.symm)))
  · exact (nativeLift_newest morphism type).trans (extensionSubstitution_value morphism type).symm

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.QuotientComprehensionSyntax
