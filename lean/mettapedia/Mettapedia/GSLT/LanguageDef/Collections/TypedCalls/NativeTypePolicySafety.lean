import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeAnnotationPolicy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphSafety

/-! # Resource-safe adaptive inference under either annotation policy -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicySafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuerySafety
open TypeDependencyAdmission NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView)
open NativeTypeViews

theorem supplement_safe (same : Atom → Atom → Bool) (annotations derived : List Atom)
    (annotationSafe : resourceFreeList annotations = true)
    (derivedSafe : resourceFreeList derived = true) :
    resourceFreeList (supplement same annotations derived) = true := by
  apply (resourceFreeList_iff _).mpr
  intro type_ member
  rcases List.mem_append.mp member with own | additional
  · exact (resourceFreeList_iff _).mp annotationSafe type_ own
  · exact (resourceFreeList_iff _).mp derivedSafe type_ (List.mem_of_mem_filter additional)

theorem annotated (world : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (policy : AnnotationPolicy Atom)
    (head : Atom) (values annotations : List Atom) (safe : resourceFreeList annotations = true) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.annotated
        { TypeScopeMatcher.ops world normalize subtypes with annotationPolicy := policy }
        head values annotations) := by
  cases policy with
  | historicalOverride => exact closeTypes annotations safe
  | supplement same =>
      apply typesRead (.inl (.closure annotations)) safe
      intro closed closedSafe
      apply typesRead (.inr (.operatorRows head)) trivial
      intro rows rowsSafe
      split
      · rw [NativeTypeAnnotationPolicy.rowsPlan_policy]
        apply map_guarantees KeySafe ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
        · exact liftViews _ _ (rowsPlan world normalize normalizeSafe subtypes values rows rowsSafe)
        · intro answer answerSafe
          cases answer with
          | error _ => trivial
          | ok derived => exact supplement_safe same closed derived closedSafe answerSafe
      · exact finishTypes closed closedSafe

theorem node (world : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (policy : AnnotationPolicy Atom)
    (direct : Bool) (head : Atom) (values : List Atom) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.node
        { TypeScopeMatcher.ops world normalize subtypes with annotationPolicy := policy }
        direct head values) := by
  apply Guarantees.read trivial
  intro reply replySafe
  cases reply with
  | types _ | kind _ => exact .pure trivial
  | class_ kind =>
      cases kind with
      | nativeMork | listValue => exact finishTypes _ rfl
      | ordinary =>
          cases direct with
          | false =>
              rw [NativeTypeAnnotationPolicy.ordinary_policy]
              exact ordinary world normalize normalizeSafe subtypes head values
          | true =>
              apply typesRead (.inl (.annotations (.expression (head :: values)))) trivial
              intro types typesSafe
              split
              · rw [NativeTypeAnnotationPolicy.ordinary_policy]
                exact ordinary world normalize normalizeSafe subtypes head values
              · exact annotated world normalize normalizeSafe subtypes policy head values types typesSafe

theorem body (world : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (policy : AnnotationPolicy Atom)
    (call : NativeTypeCallGraph.Call) :
    Guarantees KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.body
        { TypeScopeMatcher.ops world normalize subtypes with annotationPolicy := policy } call) := by
  cases call with
  | infer direct atom =>
      cases atom with
      | symbol name =>
          exact NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes (.infer direct (.symbol name))
      | grounded value =>
          exact NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes (.infer direct (.grounded value))
      | var _ => exact finishTypes _ rfl
      | expression children =>
          cases children with
          | nil => exact finishTypes _ rfl
          | cons head values => exact node world normalize normalizeSafe subtypes policy direct head values
  | tuplePart atHead atom =>
      exact NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes (.tuplePart atHead atom)
  | operatorRows atom =>
      exact NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes (.operatorRows atom)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicySafety
