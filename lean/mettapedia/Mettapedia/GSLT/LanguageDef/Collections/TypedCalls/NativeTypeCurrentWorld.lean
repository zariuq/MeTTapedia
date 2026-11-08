import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePolicySafety
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld

/-!
# External-world independence of the current application reader

The annotation-prefix overlap comparison observes its operands. Resource-free
source admission makes those observations stable. The proof follows the
actual adaptive read plans and their occurrence-scoped recursion, including
annotation-bearing applications; it does not assume completed inference.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentWorld

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQueryRelation
open Mettapedia.Machines.ReadOnlyQuerySafety (OnSuccess)
open TypeDependencyAdmission NativeTypeCallGraphSafety
open RetainedTypePayloads (ExternalView observe)
open NativeTypeViews
open TypeReadSupply (Supply)

theorem any_observe (world : ExternalView) (type_ : Atom) (typeSafe : resourceFree type_ = true)
    (types : List Atom) (safe : resourceFreeList types = true) :
    types.any (fun other => observe world other == observe world type_) =
      types.any (fun other => other == type_) := by
  induction types with
  | nil => rfl
  | cons other types ih =>
      simp only [resourceFreeList, Bool.and_eq_true] at safe
      rw [List.any_cons, List.any_cons, ih safe.2,
        observe_resourceFree world other safe.1, observe_resourceFree world type_ typeSafe]

theorem supplement_observe (world : ExternalView) (annotations derived : List Atom)
    (annotationSafe : resourceFreeList annotations = true) (derivedSafe : resourceFreeList derived = true) :
    supplement (fun left right => observe world left == observe world right) annotations derived =
      supplement (· == ·) annotations derived := by
  unfold supplement
  congr 1
  apply List.filter_congr
  intro type_ member
  rw [any_observe world type_ ((resourceFreeList_iff _).mp derivedSafe type_ member) annotations annotationSafe]

theorem annotated (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom)
    (head : Atom) (values annotations : List Atom) (safe : resourceFreeList annotations = true) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.annotated (TypeScopeMatcher.currentOps first normalizeFirst subtypesFirst)
        head values annotations)
      (NativeTypeCallGraph.annotated (TypeScopeMatcher.currentOps second normalizeSecond subtypesSecond)
        head values annotations) := by
  apply NativeTypePlanRelated.typesRead (.inl (.closure annotations)) safe
  intro closed closedSafe
  apply NativeTypePlanRelated.typesRead (.inr (.operatorRows head)) trivial
  intro rows rowsSafe
  have arrowEq : (rows.any fun row => ((TypeScopeMatcher.currentOps first normalizeFirst subtypesFirst).arrow row).isSome) =
      (rows.any fun row => ((TypeScopeMatcher.currentOps second normalizeSecond subtypesSecond).arrow row).isSome) := rfl
  simp only [← arrowEq]
  split
  · simp only [TypeScopeMatcher.currentOps, NativeTypeAnnotationPolicy.rowsPlan_policy]
    apply map_related_of_agree KeySafe ReplySafe (OnSuccess (fun types => resourceFreeList types = true))
    · exact NativeTypePlanRelated.liftViews _ _ _
        (NativeTypePlanRelated.rowsPlan first second normalizeFirst normalizeSecond normalizeSafe normalizers
          subtypesFirst subtypesSecond values rows rowsSafe)
    · intro answer answerSafe
      cases answer with
      | error _ => rfl
      | ok types =>
          simp only [Except.map]
          rw [supplement_observe first closed types closedSafe answerSafe,
            supplement_observe second closed types closedSafe answerSafe]
    · intro answer answerSafe
      cases answer with
      | error _ => trivial
      | ok types => exact NativeTypePolicySafety.supplement_safe _ closed types closedSafe answerSafe
  · exact refl_of_guarantees _ _ _ _ (finishTypes closed closedSafe)

theorem node (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom)
    (direct : Bool) (head : Atom) (values : List Atom) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.node (TypeScopeMatcher.currentOps first normalizeFirst subtypesFirst) direct head values)
      (NativeTypeCallGraph.node (TypeScopeMatcher.currentOps second normalizeSecond subtypesSecond) direct head values) := by
  apply Related.read trivial
  intro reply replySafe
  cases reply with
  | types _ | kind _ => exact .pure trivial
  | class_ kind =>
      cases kind with
      | nativeMork | listValue => exact .pure rfl
      | ordinary =>
          have ordinary := NativeTypePlanRelated.ordinary first second normalizeFirst normalizeSecond
            normalizeSafe normalizers subtypesFirst subtypesSecond head values
          cases direct with
          | false =>
              simpa only [Bool.false_eq_true, if_false, TypeScopeMatcher.currentOps,
                NativeTypeAnnotationPolicy.ordinary_policy] using ordinary
          | true =>
              apply NativeTypePlanRelated.typesRead (.inl (.annotations (.expression (head :: values)))) trivial
              intro types typesSafe
              split
              · simpa only [TypeScopeMatcher.currentOps, NativeTypeAnnotationPolicy.ordinary_policy] using ordinary
              · exact annotated first second normalizeFirst normalizeSecond normalizeSafe normalizers
                  subtypesFirst subtypesSecond head values types typesSafe

theorem body (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (call : NativeTypeCallGraph.Call) :
    Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.body (TypeScopeMatcher.currentOps first normalizeFirst subtypesFirst) call)
      (NativeTypeCallGraph.body (TypeScopeMatcher.currentOps second normalizeSecond subtypesSecond) call) := by
  have old := NativeTypePlanRelated.body first second normalizeFirst normalizeSecond normalizeSafe normalizers
    subtypesFirst subtypesSecond
  cases call with
  | infer direct atom =>
      cases atom with
      | symbol name => exact old (.infer direct (.symbol name))
      | grounded value => exact old (.infer direct (.grounded value))
      | var _ => exact .pure rfl
      | expression children =>
          cases children with
          | nil => exact .pure rfl
          | cons head values =>
              exact node first second normalizeFirst normalizeSecond normalizeSafe normalizers
                subtypesFirst subtypesSecond direct head values
  | tuplePart atHead atom => exact old (.tuplePart atHead atom)
  | operatorRows atom => exact old (.operatorRows atom)

theorem returned_safe (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (world : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (depth : Nat) (call : NativeTypeCallGraph.Call) (supply : Supply)
    (reply : NativeTypeCallGraph.Reply)
    (returned : (NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps world normalize subtypes)
      source world depth call supply).1 = some reply) : ReplySafe reply :=
  NativeTypeScopedWorld.returned_safe_of_body source safe world _
    (NativeTypePolicySafety.body world normalize normalizeSafe subtypes _) depth call supply reply returned

theorem evaluate_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat)
    (call : NativeTypeCallGraph.Call) (supply : Supply) :
    NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps first normalizeFirst subtypesFirst)
        source first depth call supply =
      NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps second normalizeSecond subtypesSecond)
        source second depth call supply :=
  NativeTypeScopedWorld.evaluate_world_of_body source safe first second _ _
    (body first second normalizeFirst normalizeSecond normalizeSafe normalizers subtypesFirst subtypesSecond)
    depth call supply

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCurrentWorld
