import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualCwf

/-!
# Generated-equal external annotations compare context extensions

The comparison pairs the actual projection with the newest variable after
generated type conversion. It retains typed admissions even when the two
annotations are different syntax. Its naturality and selected-comprehension
comparison do not require literal equality of annotation representatives.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual

open _root_.CategoryTheory

universe u
variable {S : Symbols.{u}} {D : Signature S}

def extensionArrow {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) : extend context first ⟶ extend context second :=
  Contextual.pair (projectionHom context first)
    ((newest context first).convertType (second.reindex (projectionHom context first))
      (reindex_typeEquality same (projectionHom context first)))

@[simp] theorem extensionArrow_substitution {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (extensionArrow first second same).substitution = TermExpr.var := by
  funext index
  cases index using Fin.cases <;> rfl

def extensionComparison {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) : extend context first ≅ extend context second where
  hom := extensionArrow first second same
  inv := extensionArrow second first (typeEquality_symm same)
  hom_inv_id := by
    apply Hom.ext
    change composeSubstitution (extensionArrow second first (typeEquality_symm same)).substitution
      (extensionArrow first second same).substitution = TermExpr.var
    rw [extensionArrow_substitution, extensionArrow_substitution]
    exact composeSubstitution_identity TermExpr.var
  inv_hom_id := by
    apply Hom.ext
    change composeSubstitution (extensionArrow first second same).substitution
      (extensionArrow second first (typeEquality_symm same)).substitution = TermExpr.var
    rw [extensionArrow_substitution, extensionArrow_substitution]
    exact composeSubstitution_identity TermExpr.var

@[simp] theorem extensionComparison_hom_substitution {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (extensionComparison first second same).hom.substitution = TermExpr.var :=
  extensionArrow_substitution first second same

@[simp] theorem extensionComparison_inv_substitution {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (extensionComparison first second same).inv.substitution = TermExpr.var :=
  extensionArrow_substitution second first (typeEquality_symm same)

theorem extensionComparison_projection {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (extensionComparison first second same).hom ≫ projectionHom context second = projectionHom context first := by
  apply Hom.ext
  change composeSubstitution (fun index => .var index.succ)
    (extensionComparison first second same).hom.substitution = (fun index => .var index.succ)
  rw [extensionComparison_hom_substitution]
  exact composeSubstitution_identity _

theorem extensionComparison_refl {context : Context D} (type : TypeOver context) :
    extensionComparison type type (typeEquality_refl type) = Iso.refl (extend context type) := by
  apply Iso.ext
  exact Hom.ext (extensionComparison_hom_substitution _ _ _)

theorem extensionComparison_symm {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    (extensionComparison first second same).symm = extensionComparison second first (typeEquality_symm same) := by
  apply Iso.ext
  exact Hom.ext rfl

theorem extensionComparison_trans {context : Context D} (first middle last : TypeOver context)
    (earlier : Holds D (.typeEq context.raw first.code middle.code))
    (later : Holds D (.typeEq context.raw middle.code last.code)) :
    (extensionComparison first middle earlier).trans (extensionComparison middle last later) =
      extensionComparison first last (typeEquality_trans earlier later) := by
  apply Iso.ext
  apply Hom.ext
  change composeSubstitution (extensionComparison middle last later).hom.substitution
    (extensionComparison first middle earlier).hom.substitution =
    (extensionComparison first last (typeEquality_trans earlier later)).hom.substitution
  rw [extensionComparison_hom_substitution, extensionComparison_hom_substitution,
    extensionComparison_hom_substitution]
  exact composeSubstitution_identity TermExpr.var

theorem extensionComparison_type_code {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second same).hom).code = type.code := by
  change type.code.substitute (extensionComparison first second same).hom.substitution = type.code
  rw [extensionComparison_hom_substitution, TypeExpr.substitute_identity]

theorem extensionComparison_term_code {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) {type : TypeOver (extend context second)}
    (term : Term (extend context second) type) :
    (term.reindex (extensionComparison first second same).hom).code = term.code := by
  change term.code.substitute (extensionComparison first second same).hom.substitution = term.code
  rw [extensionComparison_hom_substitution, TermExpr.substitute_identity]

theorem extensionComparison_type_roundtrip {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second same).hom).reindex
      (extensionComparison first second same).inv = type := by
  rw [← TypeOver.reindex_comp, (extensionComparison first second same).inv_hom_id]
  exact type.reindex_id

theorem extensionComparison_newest_typeEquality {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    Holds D (.typeEq (extend context first).raw
      (((second.reindex (projectionHom context second)).reindex
        (extensionComparison first second same).hom).code)
      (first.reindex (projectionHom context first)).code) := by
  change Holds D (.typeEq (extend context first).raw
    ((second.code.substitute (fun index => .var index.succ)).substitute
      (extensionComparison first second same).hom.substitution)
    (first.code.substitute (fun index => .var index.succ)))
  rw [extensionComparison_hom_substitution, TypeExpr.substitute_identity]
  exact reindex_typeEquality (typeEquality_symm same) (projectionHom context first)

theorem extensionComparison_newest {context : Context D} (first second : TypeOver context)
    (same : Holds D (.typeEq context.raw first.code second.code)) :
    ((newest context second).reindex (extensionComparison first second same).hom).convertType
      (first.reindex (projectionHom context first))
      (extensionComparison_newest_typeEquality first second same) = newest context first := by
  apply Term.ext
  rw [Term.convertType_code, extensionComparison_term_code]
  rfl

theorem extensionComparison_pair {source target : Context D} (first second : TypeOver target)
    (same : Holds D (.typeEq target.raw first.code second.code)) (morphism : source ⟶ target)
    (term : Term source (first.reindex morphism)) :
    Contextual.pair morphism term ≫ (extensionComparison first second same).hom =
      Contextual.pair morphism (term.convertType (second.reindex morphism) (reindex_typeEquality same morphism)) := by
  apply Hom.ext
  change composeSubstitution (extensionComparison first second same).hom.substitution
    (extendSubstitution morphism.substitution term.code) =
    extendSubstitution morphism.substitution
      (term.convertType (second.reindex morphism) (reindex_typeEquality same morphism)).code
  rw [extensionComparison_hom_substitution]
  rfl

namespace QuotientCwf

noncomputable def extPresentation (context : Context D) (type : TypeOver context) :
    ext ((quotientProjection D).obj context) (QType.mk type) ≅ (quotientProjection D).obj (extend context type) :=
  (quotientProjection D).mapIso (extensionComparison (typeRepresentative (QType.mk type)) type
    ((QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type))))

theorem extPresentation_projection (context : Context D) (type : TypeOver context) :
    (extPresentation context type).hom ≫ project (projectionHom context type) = wk (QType.mk type) := by
  let same := (QType.mk_eq_iff _ _).mp (typeRepresentative_class (QType.mk type))
  exact ((quotientProjection D).map_comp
      (extensionComparison (typeRepresentative (QType.mk type)) type same).hom
      (projectionHom context type)).symm.trans
    (congrArg project (extensionComparison_projection _ _ same))

end QuotientCwf
end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual
