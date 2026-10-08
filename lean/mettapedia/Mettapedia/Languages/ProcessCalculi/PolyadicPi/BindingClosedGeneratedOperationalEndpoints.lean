import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalModel

/-!
# Complete operational endpoint comparisons

Sequential declaration inclusions and the composed native category map can
choose differently presented objects. Equality of their full typed arrow
codes earns the endpoint squares. The generator equations then give genuine
edges of the actual target category, with both independently authored ends.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalEndpoints

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory

universe k u v a

private theorem raw_square {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
    {signature : Signature (C := C) (symbols := symbols)}
    {source target nextSource nextTarget : Object signature}
    (before : RawHom source target) (after : RawHom nextSource nextTarget)
    (sourceSame : source = nextSource) (targetSame : target = nextTarget)
    (codeSame : before.code = after.code) :
    eqToHom sourceSame ≫ classOf after = classOf before ≫ eqToHom targetSame := by
  cases sourceSame
  cases targetSame
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact congrArg classOf (RawHom.ext codeSame).symm

abbrev vertex := BindingClosedGeneratedOperational.vertex.{k}
abbrev categoryMap := BindingClosedGeneratedOperational.categoryMap.{k}
abbrev declarations := BindingClosedGeneratedOperational.declaration.{k}
abbrev arrowInclusion := RelativeClosedInternalCategory.RulePresentation.arrowInclusion
  vertex.{k} categoryMap declarations
abbrev equationInclusion := RelativeClosedInternalCategory.RulePresentation.equationInclusion
  vertex.{k} categoryMap declarations
abbrev extendedCategoryMap := RelativeClosedInternalCategory.RulePresentation.extendedCategoryMap
  vertex.{k} categoryMap declarations
abbrev category := BindingClosedGeneratedOperationalModel.category.{k}
abbrev programs := RelativeClosedInternalCategory.RulePresentation.programs vertex.{k} categoryMap declarations
abbrev edges := RelativeClosedInternalCategory.RulePresentation.edges vertex.{k} categoryMap declarations

def vertexComparison : programs.{k} ≅ category.vertex :=
  eqToIso (RelativeClosedInternalCategory.RulePresentation.programs_read vertex categoryMap declarations)

def edgeComparison : edges.{k} ≅ category.edge :=
  eqToIso (RelativeClosedInternalCategory.RulePresentation.edges_read vertex categoryMap declarations)

private theorem source_code :
    (RelativeClosedInternalCategory.RulePresentation.edgeSource vertex.{k} categoryMap declarations).code =
      (RelativeClosedInternalCategory.NativeCategory.source vertex extendedCategoryMap).code := by
  let original := (RelativeClosedInternalCategory.Presentation.inclusion vertex).rawArrow
    (RelativeClosedInternalCategory.Endpoints.source vertex)
  exact (congrArg (fun code => code.map equationInclusion.base equationInclusion.objects equationInclusion.arrows)
    (SignatureMap.arrow_code_compose categoryMap arrowInclusion original)).trans
      (SignatureMap.arrow_code_compose (categoryMap.compose arrowInclusion) equationInclusion original)

private theorem target_code :
    (RelativeClosedInternalCategory.RulePresentation.edgeTarget vertex.{k} categoryMap declarations).code =
      (RelativeClosedInternalCategory.NativeCategory.target vertex extendedCategoryMap).code := by
  let original := (RelativeClosedInternalCategory.Presentation.inclusion vertex).rawArrow
    (RelativeClosedInternalCategory.Endpoints.target vertex)
  exact (congrArg (fun code => code.map equationInclusion.base equationInclusion.objects equationInclusion.arrows)
    (SignatureMap.arrow_code_compose categoryMap arrowInclusion original)).trans
      (SignatureMap.arrow_code_compose (categoryMap.compose arrowInclusion) equationInclusion original)

theorem complete_source_square : edgeComparison.{k}.hom ≫ category.source =
    classOf (RelativeClosedInternalCategory.RulePresentation.edgeSource vertex categoryMap declarations) ≫
      vertexComparison.hom :=
  raw_square _ _ (RelativeClosedInternalCategory.RulePresentation.edges_read vertex categoryMap declarations)
    (RelativeClosedInternalCategory.RulePresentation.programs_read vertex categoryMap declarations) source_code

theorem complete_target_square : edgeComparison.{k}.hom ≫ category.target =
    classOf (RelativeClosedInternalCategory.RulePresentation.edgeTarget vertex categoryMap declarations) ≫
      vertexComparison.hom :=
  raw_square _ _ (RelativeClosedInternalCategory.RulePresentation.edges_read vertex categoryMap declarations)
    (RelativeClosedInternalCategory.RulePresentation.programs_read vertex categoryMap declarations) target_code

def firing (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    RelativeClosedInternalCategory.RulePresentation.ruleDomain vertex categoryMap declarations origin ⟶ category.edge :=
  classOf (BindingClosedGeneratedOperational.fire origin) ≫ edgeComparison.hom

theorem firing_source (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    firing origin ≫ category.source =
      classOf (RelativeClosedInternalCategory.RulePresentation.before vertex categoryMap declarations origin) ≫
        vertexComparison.hom := by
  rw [firing, Category.assoc, complete_source_square, ← Category.assoc, ← classOf_compose]
  rw [BindingClosedGeneratedOperational.authored_source]

theorem firing_target (origin : ULift.{k} BindingClosedGeneratedOperational.Origin) :
    firing origin ≫ category.target =
      classOf (RelativeClosedInternalCategory.RulePresentation.after vertex categoryMap declarations origin) ≫
        vertexComparison.hom := by
  rw [firing, Category.assoc, complete_target_square, ← Category.assoc, ← classOf_compose]
  rw [BindingClosedGeneratedOperational.authored_target]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedGeneratedOperationalEndpoints
