import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeMatcher
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeNormalizationScope
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeScopeClosure

/-!
# Joining source matching, normalization and completed read plans

This joins the source components, not a new default type evaluator. The
ordered source-row driver uses concrete first-order matching and the
source-shaped normalization dispatcher. Their world independence is derived
separately and then composed. The same law holds for the independently
specified demand plan in `NativeTypeDemand`.

The annotation-only operand instance derives child-read closure from the
actual HE annotation reader. Recursive inferred child views, nested wildcard
and numeric-promotion matching, complete native primitive codecs, and the
native effective-row capture are not silently included in that instance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyClosure

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines.ReadOnlyQuery
open TypeDependencyAdmission TypeNormalizationScope NativeTypeViews
open RetainedTypePayloads (ExternalView)

def sourceOps (world : ExternalView) (active : String → Bool) (primitive : Primitive)
    (subtypes : List Atom → List Atom) : Ops Atom TypeScopeMatcher.State Atom :=
  TypeScopeMatcher.ops world
    (InertTypeDependencies.normalize active (observed world primitive)) subtypes

theorem sourceRows_world (first second : ExternalView) (active : String → Bool)
    (primitive : Primitive) (closed : ResultsClosed active primitive)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values rows : List Atom) (valuesSafe : TypeScopeMatcher.ReadsSafe reads values)
    (rowsSafe : resourceFreeList rows = true) :
    sourceRows (sourceOps first active primitive subtypes) reads values rows =
      sourceRows (sourceOps second active primitive subtypes) reads values rows := by
  unfold sourceOps
  exact (TypeScopeMatcher.sourceRows_world first second _ subtypes reads values valuesSafe rows rowsSafe).trans
    (TypeScopeMatcher.sourceRows_normalizer_congr second _ _
      (fun atom safe => TypeNormalizationScope.normalize_world active first second primitive closed atom safe)
      subtypes reads values valuesSafe rows rowsSafe)

theorem sourceRows_closed (world : ExternalView) (active : String → Bool)
    (primitive : Primitive) (closed : ResultsClosed active primitive)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values rows : List Atom) (valuesSafe : TypeScopeMatcher.ReadsSafe reads values)
    (rowsSafe : resourceFreeList rows = true) :
    resourceFreeList (sourceRows (sourceOps world active primitive subtypes) reads values rows) = true :=
  TypeScopeMatcher.sourceRows_preserves world _
    (normalize_preserves active _ (observed_closed active world primitive closed))
    subtypes reads values valuesSafe rows rowsSafe

/-- The demand plan shares the derived world-independence. No premise says
its complete execution already equals the source answer. -/
theorem demandRows_world (first second : ExternalView) (active : String → Bool)
    (primitive : Primitive) (closed : ResultsClosed active primitive)
    (subtypes : List Atom → List Atom) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values rows : List Atom) (valuesSafe : TypeScopeMatcher.ReadsSafe reads values)
    (rowsSafe : resourceFreeList rows = true) :
    (run (NativeTypeDemand.sourceStore reads)
      (NativeTypeDemand.rowsPlan (sourceOps first active primitive subtypes) values rows)).answer =
    (run (NativeTypeDemand.sourceStore reads)
      (NativeTypeDemand.rowsPlan (sourceOps second active primitive subtypes) values rows)).answer := by
  rw [NativeTypeDemand.rowsPlan_exact, NativeTypeDemand.rowsPlan_exact,
    sourceRows_world first second active primitive closed subtypes reads values rows valuesSafe rowsSafe]

def annotationOperands (space : Space) (reads : NativeTypeViews.Reads Atom Atom Atom) :
    NativeTypeViews.Reads Atom Atom Atom :=
  { reads with inferred := getAnnotatedTypes space }

theorem annotationOperands_safe (space : Space) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (rowsSafe : resourceFreeList space.atoms = true) (values : List Atom) :
    TypeScopeMatcher.ReadsSafe (annotationOperands space reads) values := by
  intro value _
  apply (resourceFreeList_iff _).mpr
  intro type_ member
  exact annotation_resourceFree rowsSafe value member

/-- In the declaration-read operand fragment the child closure premise is
discharged by the captured source rows, not by a claim that inference is pure. -/
theorem annotation_operand_rows_world (first second : ExternalView) (active : String → Bool)
    (primitive : Primitive) (closed : ResultsClosed active primitive)
    (subtypes : List Atom → List Atom) (space : Space) (reads : NativeTypeViews.Reads Atom Atom Atom)
    (values rows : List Atom) (spaceSafe : resourceFreeList space.atoms = true)
    (rowsSafe : resourceFreeList rows = true) :
    sourceRows (sourceOps first active primitive subtypes) (annotationOperands space reads) values rows =
      sourceRows (sourceOps second active primitive subtypes) (annotationOperands space reads) values rows :=
  sourceRows_world first second active primitive closed subtypes (annotationOperands space reads)
    values rows (annotationOperands_safe space reads spaceSafe values) rowsSafe

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeDependencyClosure
