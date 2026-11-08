import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.ScopedSubtypeReadSafety

/-!
# Resource-safe occurrence-scoped type ports

Each annotation read and subtype-row visit retains its actual fresh-name
supply. External-world equality includes that supply, including unsuccessful
matches and unfinished closure. Safety is derived from the captured source
rows and the actual returned value, not from an assumed completed oracle.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open TypeDependencyAdmission NativeTypeCallGraph NativeTypeCallGraphSafety
open NativeTypeSourcePorts (Source rawDeclarations)
open NativeTypeScopedReads (primitive)
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem rawDeclarations_world (source : Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (atom : Atom) :
    rawDeclarations source first atom = rawDeclarations source second atom := by
  simp only [rawDeclarations, observedSpace,
    observeList_resourceFree first _ safe.1, observeList_resourceFree second _ safe.1,
    observeList_resourceFree first _ safe.2, observeList_resourceFree second _ safe.2]

theorem primitive_safe (source : Source) (safe : NativeTypeSourcePorts.Safe source) (world : ExternalView)
    (supply : Supply) (key : Primitive) (keySafe : KeySafe (.inl key)) (reply : Reply)
    (returned : (primitive source world supply key).1 = some reply) : ReplySafe reply := by
  cases key with
  | annotations atom =>
      cases Option.some.inj returned
      exact TypeReadSupply.freshList_resourceFree _ _
        (NativeTypeSourcePorts.rawDeclarations_safe source safe world atom)
  | closure seeds =>
      simp only [primitive, Option.map_eq_some_iff] at returned
      obtain ⟨types, completed, rfl⟩ := returned
      exact ScopedSubtypeReadSafety.completeTypes_safe world source.rows
        (ScopedSubtypeReadSafety.rowsSafe_of_resourceFree source.rows safe.1)
        source.subtypeFresh source.alpha source.subtypeBudget seeds keySafe supply types completed
  | intrinsic atom =>
      exact NativeTypeSourcePorts.primitive_safe source safe world (.intrinsic atom) keySafe reply returned
  | kind atom =>
      exact NativeTypeSourcePorts.primitive_safe source safe world (.kind atom) keySafe reply returned
  | classify head values =>
      exact NativeTypeSourcePorts.primitive_safe source safe world (.classify head values) keySafe reply returned

theorem primitive_world (source : Source) (safe : NativeTypeSourcePorts.Safe source) (first second : ExternalView)
    (supply : Supply) (key : Primitive) (keySafe : KeySafe (.inl key)) :
    primitive source first supply key = primitive source second supply key := by
  cases key with
  | annotations atom =>
      simp only [primitive, rawDeclarations_world source safe first second atom]
  | closure seeds =>
      simp only [primitive]
      rw [ScopedSubtypeReadSafety.completeTypes_world first second source.rows
        (ScopedSubtypeReadSafety.rowsSafe_of_resourceFree source.rows safe.1)
        source.subtypeFresh source.alpha source.subtypeBudget seeds keySafe supply]
  | intrinsic atom =>
      simp only [primitive, NativeTypeSourcePorts.primitive_world source safe first second (.intrinsic atom) keySafe]
  | kind atom => rfl
  | classify head values => rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSafety
