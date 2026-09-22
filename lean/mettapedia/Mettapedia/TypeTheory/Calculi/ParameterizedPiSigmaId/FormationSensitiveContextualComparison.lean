import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualCategory
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextConversion

/-! # Comparison of convertible formed context extensions

The construction is parameterized by the declared rules and uses the existing
formation, substitution and conversion judgments. Concrete language controls
are separate consumers, not premises of these laws.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual

open _root_.CategoryTheory FormationSensitive

variable {Head : Type} {rules : Rules Head}

/-- Conversion of the annotation uses the independently formed target type;
the term's native syntax is unchanged. -/
def Term.convertType {context : Context rules} {first : TypeOver context}
    (term : Term context first) (second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    Term context second :=
  ⟨term.code, .conv term.typed second.formed second.universeWitness converted⟩

@[simp] theorem Term.convertType_code {context : Context rules} {first second : TypeOver context}
    (term : Term context first)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (term.convertType second converted).code = term.code := rfl

theorem Term.convertType_refl {context : Context rules} {type : TypeOver context}
    (term : Term context type) : term.convertType type (.refl type.code) = term :=
  Term.ext rfl

theorem Term.convertType_roundtrip {context : Context rules} {first second : TypeOver context}
    (term : Term context first)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (term.convertType second converted).convertType first converted.symm = term := Term.ext rfl

theorem Term.convertType_trans {context : Context rules} {first middle last : TypeOver context}
    (term : Term context first)
    (earlier : Conv rules.headEq first.code middle.code rules.computation)
    (later : Conv rules.headEq middle.code last.code rules.computation) :
    (term.convertType middle earlier).convertType last later =
      term.convertType last (.trans _ _ _ earlier later) :=
  Term.ext rfl

/-- Both sides use the same actual simultaneous substitution. -/
theorem Term.reindex_convertType {source target : Context rules}
    {first second : TypeOver target} (term : Term target first)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (morphism : source ⟶ target) :
    (term.convertType second converted).reindex morphism =
      (term.reindex morphism).convertType (second.reindex morphism)
        (converted.substitute morphism.substitution) :=
  Term.ext rfl

/-- The source and target are formed independently. The forward arrow
checks the target binder in the source telescope, hence uses reverse
conversion in `CtxMor.convertNewest`. -/
def extensionComparison {context : Context rules} (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    extend context first ≅ extend context second where
  hom := ⟨ids, CtxMor.convertNewest second.formed second.universeWitness converted.symm⟩
  inv := ⟨ids, CtxMor.convertNewest first.formed first.universeWitness converted⟩
  hom_inv_id := Hom.ext (subComp_ids_left ids)
  inv_hom_id := Hom.ext (subComp_ids_left ids)

@[simp] theorem extensionComparison_hom_substitution {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (extensionComparison first second converted).hom.substitution = ids := rfl

@[simp] theorem extensionComparison_inv_substitution {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (extensionComparison first second converted).inv.substitution = ids := rfl

theorem extensionComparison_projection {context : Context rules} (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (extensionComparison first second converted).hom ≫ projectionHom context second =
      projectionHom context first := Hom.ext (subComp_ids_left projection)

theorem extensionComparison_inverse_projection {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (extensionComparison first second converted).inv ≫ projectionHom context first =
      projectionHom context second := Hom.ext (subComp_ids_left projection)

theorem extensionComparison_refl {context : Context rules} (type : TypeOver context) :
    extensionComparison type type (.refl type.code) = Iso.refl (extend context type) := by
  apply Iso.ext
  exact Hom.ext rfl

theorem extensionComparison_symm {context : Context rules} (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    (extensionComparison first second converted).symm =
      extensionComparison second first converted.symm := by
  apply Iso.ext
  exact Hom.ext rfl

theorem extensionComparison_trans {context : Context rules} (first middle last : TypeOver context)
    (earlier : Conv rules.headEq first.code middle.code rules.computation)
    (later : Conv rules.headEq middle.code last.code rules.computation) :
    (extensionComparison first middle earlier).trans (extensionComparison middle last later) =
      extensionComparison first last (.trans _ _ _ earlier later) := by
  apply Iso.ext
  exact Hom.ext (subComp_ids_left ids)

theorem extensionComparison_reindex_type_code {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second converted).hom).code = type.code :=
  subst_ids type.code

theorem extensionComparison_reindex_type_level {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second converted).hom).level = type.level := rfl

theorem extensionComparison_reindex_term_code {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    {type : TypeOver (extend context second)} (term : Term (extend context second) type) :
    (term.reindex (extensionComparison first second converted).hom).code = term.code :=
  subst_ids term.code

theorem extensionComparison_type_roundtrip {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (type : TypeOver (extend context second)) :
    (type.reindex (extensionComparison first second converted).hom).reindex
      (extensionComparison first second converted).inv = type := by
  rw [← TypeOver.reindex_comp, (extensionComparison first second converted).inv_hom_id]
  exact type.reindex_id

theorem extensionComparison_term_roundtrip {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    {type : TypeOver (extend context second)} (term : Term (extend context second) type) :
    ((term.reindex (extensionComparison first second converted).hom).reindex
      (extensionComparison first second converted).inv).cast
        (extensionComparison_type_roundtrip first second converted type) = term := by
  apply Term.ext
  rw [Term.cast_code]
  change subst ids (subst ids term.code) = term.code
  rw [subst_ids, subst_ids]

theorem extensionComparison_type_inverse_roundtrip {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    (type : TypeOver (extend context first)) :
    (type.reindex (extensionComparison first second converted).inv).reindex
      (extensionComparison first second converted).hom = type := by
  rw [← TypeOver.reindex_comp, (extensionComparison first second converted).hom_inv_id]
  exact type.reindex_id

theorem extensionComparison_term_inverse_roundtrip {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation)
    {type : TypeOver (extend context first)} (term : Term (extend context first) type) :
    ((term.reindex (extensionComparison first second converted).inv).reindex
      (extensionComparison first second converted).hom).cast
        (extensionComparison_type_inverse_roundtrip first second converted type) = term := by
  apply Term.ext
  rw [Term.cast_code]
  change subst ids (subst ids term.code) = term.code
  rw [subst_ids, subst_ids]

/-- The newest type annotations are convertible, not equal raw types. -/
theorem extensionComparison_newest_type_conversion {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    Conv rules.headEq
      ((second.reindex (projectionHom context second)).reindex
        (extensionComparison first second converted).hom).code
      (first.reindex (projectionHom context first)).code rules.computation := by
  change Conv rules.headEq (subst ids (subst projection second.code))
    (subst projection first.code) rules.computation
  rw [subst_ids]
  exact Conv.substitute projection converted.symm

theorem extensionComparison_newest {context : Context rules}
    (first second : TypeOver context)
    (converted : Conv rules.headEq first.code second.code rules.computation) :
    ((newest context second).reindex (extensionComparison first second converted).hom).convertType
      (first.reindex (projectionHom context first))
      (extensionComparison_newest_type_conversion first second converted) = newest context first :=
  Term.ext rfl


end FormationSensitiveContextual
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
