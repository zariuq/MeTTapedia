import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualCwf

/-!
# Typed-equal annotations compare the actual context extensions

Both extensions are formed in the typed judgment. The forward map is built
by pairing the actual projection with the newest variable after typed
conversion. Its substitution code is the identity, but the source and target
annotations need not be equal or raw-convertible. Reindexing and pairing
compatibilities consume the same earned conversion.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedContextual

open _root_.CategoryTheory TypedEquality TypedEquality.Normalization

variable {Head : Type} {rules : Rules Head}

def extensionArrow {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) : extend context first ⟶ extend context second :=
  TypedContextual.pair (projectionHom context first)
    ((newest context first).convertType (second.reindex (projectionHom context first))
      (reindex_typeEquality same (projectionHom context first)))

@[simp] theorem extensionArrow_substitution {context : Context rules}
    (first second : TypeOver context) (same : TypeEq rules context.raw first.code second.code) :
    (extensionArrow first second same).substitution = ids := by
  funext index
  refine Fin.cases ?_ (fun _ => rfl) index
  rfl

def extensionComparison {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) : extend context first ≅ extend context second where
  hom := extensionArrow first second same
  inv := extensionArrow second first same.symm
  hom_inv_id := by
    apply Hom.ext
    change subComp (extensionArrow first second same).substitution
      (extensionArrow second first same.symm).substitution = ids
    rw [extensionArrow_substitution, extensionArrow_substitution]
    exact subComp_ids_left ids
  inv_hom_id := by
    apply Hom.ext
    change subComp (extensionArrow second first same.symm).substitution
      (extensionArrow first second same).substitution = ids
    rw [extensionArrow_substitution, extensionArrow_substitution]
    exact subComp_ids_left ids

@[simp] theorem extensionComparison_hom_substitution {context : Context rules}
    (first second : TypeOver context) (same : TypeEq rules context.raw first.code second.code) :
    (extensionComparison first second same).hom.substitution = ids := extensionArrow_substitution first second same

@[simp] theorem extensionComparison_inv_substitution {context : Context rules}
    (first second : TypeOver context) (same : TypeEq rules context.raw first.code second.code) :
    (extensionComparison first second same).inv.substitution = ids := extensionArrow_substitution second first same.symm

theorem extensionComparison_projection {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    (extensionComparison first second same).hom ≫ projectionHom context second = projectionHom context first := by
  apply Hom.ext
  change subComp (extensionComparison first second same).hom.substitution projection = projection
  rw [extensionComparison_hom_substitution]
  exact subComp_ids_left projection

theorem extensionComparison_inverse_projection {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    (extensionComparison first second same).inv ≫ projectionHom context first = projectionHom context second :=
  extensionComparison_projection second first same.symm

theorem extensionComparison_refl {context : Context rules} (type : TypeOver context) :
    extensionComparison type type type.isType.refl = Iso.refl (extend context type) := by
  apply Iso.ext
  exact Hom.ext (extensionComparison_hom_substitution _ _ _)

theorem extensionComparison_symm {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    (extensionComparison first second same).symm = extensionComparison second first same.symm := by
  apply Iso.ext
  exact Hom.ext rfl

theorem extensionComparison_trans {L : Type} [UniverseLevel.LevelOrder L]
    (levels : LevelModel rules L) {context : Context rules} (first middle last : TypeOver context)
    (earlier : TypeEq rules context.raw first.code middle.code)
    (later : TypeEq rules context.raw middle.code last.code) :
    (extensionComparison first middle earlier).trans (extensionComparison middle last later) =
      extensionComparison first last (earlier.trans levels later) := by
  apply Iso.ext
  apply Hom.ext
  change subComp (extensionComparison first middle earlier).hom.substitution
    (extensionComparison middle last later).hom.substitution =
      (extensionComparison first last (earlier.trans levels later)).hom.substitution
  rw [extensionComparison_hom_substitution, extensionComparison_hom_substitution,
    extensionComparison_hom_substitution]
  exact subComp_ids_left ids

theorem extensionComparison_type_code {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second same).hom).code = type.code := by
  change subst (extensionComparison first second same).hom.substitution type.code = type.code
  rw [extensionComparison_hom_substitution, subst_ids]

theorem extensionComparison_type_level {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second same).hom).level = type.level := rfl

theorem extensionComparison_term_code {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) {type : TypeOver (extend context second)}
    (term : Term (extend context second) type) :
    (term.reindex (extensionComparison first second same).hom).code = term.code := by
  change subst (extensionComparison first second same).hom.substitution term.code = term.code
  rw [extensionComparison_hom_substitution, subst_ids]

theorem extensionComparison_type_roundtrip {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second same).hom).reindex
      (extensionComparison first second same).inv = type := by
  rw [← TypeOver.reindex_comp, (extensionComparison first second same).inv_hom_id]
  exact type.reindex_id

theorem extensionComparison_newest_typeEquality {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    TypeEq rules (extend context first).raw
      (((second.reindex (projectionHom context second)).reindex
        (extensionComparison first second same).hom).code)
      (first.reindex (projectionHom context first)).code := by
  change TypeEq rules (extend context first).raw
    (subst (extensionComparison first second same).hom.substitution (subst projection second.code))
    (subst projection first.code)
  rw [extensionComparison_hom_substitution, subst_ids]
  exact reindex_typeEquality same.symm (projectionHom context first)

theorem extensionComparison_newest {context : Context rules} (first second : TypeOver context)
    (same : TypeEq rules context.raw first.code second.code) :
    ((newest context second).reindex (extensionComparison first second same).hom).convertType
      (first.reindex (projectionHom context first))
      (extensionComparison_newest_typeEquality first second same) = newest context first := by
  apply Term.ext
  rw [Term.convertType_code, extensionComparison_term_code]
  rfl

theorem extensionComparison_pair {source target : Context rules} (first second : TypeOver target)
    (same : TypeEq rules target.raw first.code second.code) (morphism : source ⟶ target)
    (term : Term source (first.reindex morphism)) :
    TypedContextual.pair morphism term ≫ (extensionComparison first second same).hom =
      TypedContextual.pair morphism (term.convertType (second.reindex morphism)
        (reindex_typeEquality same morphism)) := by
  apply Hom.ext
  change subComp (consSub term.code morphism.substitution)
      (extensionComparison first second same).hom.substitution =
    consSub (term.convertType (second.reindex morphism) (reindex_typeEquality same morphism)).code
      morphism.substitution
  rw [extensionComparison_hom_substitution]
  exact subComp_ids_right _

namespace QuotientCwf

variable {L : Type} [UniverseLevel.LevelOrder L] {levels : LevelModel rules L}

/-- Chosen comprehension and any supplied typed annotation are compared by
an actual context isomorphism, without equating their raw codes. -/
noncomputable def extPresentation (context : Context rules) (type : TypeOver context) :
    ext ((quotientProjection rules).obj context) (QType.mk levels type) ≅
      (quotientProjection rules).obj (extend context type) :=
  (quotientProjection rules).mapIso
    (extensionComparison (typeRepresentative (QType.mk levels type)) type
      ((QType.mk_eq_iff levels _ _).mp (typeRepresentative_class (QType.mk levels type))))

theorem extPresentation_projection (context : Context rules) (type : TypeOver context) :
    (extPresentation (levels := levels) context type).hom ≫ project (projectionHom context type) =
      wk (QType.mk levels type) := by
  let same := (QType.mk_eq_iff levels _ _).mp (typeRepresentative_class (QType.mk levels type))
  exact ((quotientProjection rules).map_comp
      (extensionComparison (typeRepresentative (QType.mk levels type)) type same).hom
      (projectionHom context type)).symm.trans
    (congrArg project (extensionComparison_projection _ _ same))

end QuotientCwf
end TypedContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
