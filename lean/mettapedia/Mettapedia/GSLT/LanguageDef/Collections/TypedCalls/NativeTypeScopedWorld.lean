import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSafety
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypePlanRelated

/-!
# World independence with occurrence-scoped recursive inference

The proof follows the original inference call graph while threading each
actual service state. Repeated keys may return differently freshened type
instances. Resource closure is derived by recursion; the pairwise plan
relation then transports the exact result and supply across external worlds.
Neither completion nor whole-inference world stability is a premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQueryRelation
open Mettapedia.Machines.ReadOnlyQuerySafety (OnSuccess)
open NativeTypeCallGraph NativeTypeCallGraphSafety TypeDependencyAdmission
open NativeTypeScopedReads (evaluate primitive)
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem returned_safe_of_body (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (world : ExternalView) (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (bodySafe : ∀ call, Mettapedia.Machines.ReadOnlyQuerySafety.Guarantees
      KeySafe ReplySafe (OnSuccess ReplySafe) (NativeTypeCallGraph.body ops call))
    (depth : Nat) : ∀ call supply reply,
    (evaluate ops source world depth call supply).1 = some reply →
      ReplySafe reply := by
  induction depth with
  | zero => intro call supply reply returned; cases returned
  | succ depth ih =>
      intro call supply reply returned
      let service : Supply → Question → Option Reply × Supply := fun current => fun
        | .inl key => primitive source world current key
        | .inr child => evaluate ops source world depth child current
      have valid : ∀ current key, KeySafe key → ∀ value,
          (service current key).1 = some value → ReplySafe value := by
        intro current key keySafe value found
        cases key with
        | inl key => exact NativeTypeScopedSafety.primitive_safe source safe world current key keySafe value found
        | inr child => exact ih child current value found
      exact completed_sound KeySafe ReplySafe (OnSuccess ReplySafe)
        (NativeTypeCallGraph.body _ call)
        (bodySafe call)
        service valid supply (.ok reply) (NativeTypeRecursiveDriver.completed_some returned)

theorem returned_safe (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (world : ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (depth : Nat) : ∀ call supply reply,
    (evaluate (TypeScopeMatcher.ops world normalize subtypes) source world depth call supply).1 = some reply →
      ReplySafe reply :=
  returned_safe_of_body source safe world _
    (NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes) depth

theorem evaluate_world_of_body (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (firstOps secondOps : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (bodies : ∀ call, Related KeySafe ReplySafe (OnSuccess ReplySafe)
      (NativeTypeCallGraph.body firstOps call) (NativeTypeCallGraph.body secondOps call))
    (depth : Nat) : ∀ call supply,
    evaluate firstOps source first depth call supply =
      evaluate secondOps source second depth call supply := by
  induction depth with
  | zero => intro call supply; rfl
  | succ depth ih =>
      intro call supply
      let before : Supply → Question → Option Reply × Supply := fun current => fun
        | .inl key => primitive source first current key
        | .inr child => evaluate firstOps source first depth child current
      let after : Supply → Question → Option Reply × Supply := fun current => fun
        | .inl key => primitive source second current key
        | .inr child => evaluate secondOps source second depth child current
      have agree : ∀ current key, KeySafe key → before current key = after current key := by
        intro current key keySafe
        cases key with
        | inl key => exact NativeTypeScopedSafety.primitive_world source safe first second current key keySafe
        | inr child => exact ih child current
      have valid : ∀ current key, KeySafe key → ∀ reply,
          (before current key).1 = some reply → ReplySafe reply := by
        intro current key keySafe reply returned
        cases key with
        | inl key => exact NativeTypeScopedSafety.primitive_safe source safe first current key keySafe reply returned
        | inr child =>
            exact returned_safe_of_body source safe first firstOps
              (fun call => left_guarantees _ _ _ (bodies call)) depth child current reply returned
      have same := demand_run_eq KeySafe ReplySafe (OnSuccess ReplySafe)
        (bodies call) before after agree valid supply
      exact congrArg (fun result =>
        let answer := NativeTypeRecursiveDriver.completed result.answer
        (answer, NativeTypeScopedReads.retain result.state answer)) same

theorem evaluate_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) : ∀ call supply,
    evaluate (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) source first depth call supply =
      evaluate (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) source second depth call supply :=
  evaluate_world_of_body source safe first second _ _
    (NativeTypePlanRelated.body first second normalizeFirst normalizeSecond normalizeSafe normalizers
      subtypesFirst subtypesSecond) depth

theorem source_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (active : String → Bool) (normalization : TypeNormalizationScope.Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active normalization)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) (call : Call) (supply : Supply) :
    evaluate (TypeDependencyClosure.sourceOps first active normalization subtypesFirst) source first depth call supply =
      evaluate (TypeDependencyClosure.sourceOps second active normalization subtypesSecond) source second depth call supply :=
  evaluate_world source safe first second _ _
    (TypeNormalizationScope.normalize_preserves active _
      (TypeNormalizationScope.observed_closed active first normalization closed))
    (TypeNormalizationScope.normalize_world active first second normalization closed)
    subtypesFirst subtypesSecond depth call supply

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedWorld
