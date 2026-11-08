import Mettapedia.Languages.MeTTa.HE.ClosedNumericTypePackages
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeArgumentQueryTransport

/-!
# Independent type-package evidence for range's comparison read

The completed scoped reader returns one Bool type for the actual comparison.
Its same ordered observation has an independent source-package derivation.
No equality between the complete internal and public type services is used.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredSourcePackages

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type Spec.Type.Presentation Spec.Type.Presentation.Exact
open HERangeSourceProgram (space)

theorem comparison_declaration : AnnotationTypesRel (.symbol ">=") space.atoms
    [ClosedNumeric.arrow "Bool"] := by
  have rows : space.atoms.filterMap (annotationType? (.symbol ">=")) = [ClosedNumeric.arrow "Bool"] := rfl
  rw [←rows]
  exact AnnotationTypesRel.complete (.symbol ">=") space.atoms

theorem comparison_no_annotation (left right : Int) :
    AnnotationTypesRel (ClosedNumeric.call ">=" left right) space.atoms [] := by
  have rows : space.atoms.filterMap (annotationType? (ClosedNumeric.call ">=" left right)) = [] := rfl
  rw [←rows]
  exact AnnotationTypesRel.complete (ClosedNumeric.call ">=" left right) space.atoms

theorem comparison_source (left right : Int) :
    RuntimeTypePackagesRel space (HEIfSourceSelection.Range.condition left right)
      [publishedPackage (.symbol "Bool")] := by
  simpa [HEIfSourceSelection.Range.condition, HEFreshEquationFrames.Range.number, ClosedNumeric.call] using
    ClosedNumeric.binary space ">=" "Bool" left right (by decide)
      comparison_declaration (comparison_no_annotation left right)

theorem completed_comparison_read_has_source
    (world : RetainedTypePayloads.ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (scope : List String) (before : Spec.Eval.Completed.Frame) (left right : Int) (expected : Atom)
    (types : List Atom)
    (queried : HERangeArgumentQueryTransport.inferredRead
      (HERangeTypeReadApplications.ops world active primitive unobservedClosure) world scope
      before.bindings (HEIfSourceSelection.Range.condition left right) expected types) :
    types = [.symbol "Bool"] ∧
      RuntimeTypePackagesRel space (HEIfSourceSelection.Range.condition left right)
        (types.map publishedPackage) := by
  have exactTypes := HERangeArgumentQueryTransport.comparison_read_unique world active primitive unobservedClosure
    scope before left right expected types queried
  refine ⟨exactTypes, ?_⟩
  rw [exactTypes]
  exact comparison_source left right

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredSourcePackages
