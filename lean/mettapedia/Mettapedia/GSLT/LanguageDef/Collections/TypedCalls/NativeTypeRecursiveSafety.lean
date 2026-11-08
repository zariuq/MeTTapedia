import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeSourcePorts
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveDriver

/-!
# Recursive source results and reached primitive dependencies

Every completed child request is checked by induction through the actual
source call graph. This removes the former annotation-only child premise.
The plan's key invariant also proves that every reached subtype-closure
request has resource-free seeds, including when some later request is
unfinished. No extra blanket purity assertion or eager child traversal is
used to establish these invariants.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveSafety

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQuerySafety
open NativeTypeCallGraph NativeTypeCallGraphSafety NativeTypeRecursiveDriver TypeDependencyAdmission

def PrimitiveSafe (primitive : PrimitiveStore) : Prop :=
  ∀ key, KeySafe (.inl key) → ∀ reply, primitive key = some reply → ReplySafe reply

theorem returned_safe (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (primitive : PrimitiveStore) (ports : PrimitiveSafe primitive)
    (depth : Nat) : ∀ call reply,
      evaluate (TypeScopeMatcher.ops world normalize subtypes) primitive depth call = some reply → ReplySafe reply := by
  induction depth with
  | zero => intro call reply completed; cases completed
  | succ depth ih =>
      intro call reply completed
      have availableSafe : ∀ key, KeySafe key → ∀ value,
          available (TypeScopeMatcher.ops world normalize subtypes) primitive depth key = some value →
          ReplySafe value := by
        intro key keySafe value found
        cases key with
        | inl key => exact ports key keySafe value found
        | inr child => exact ih child value found
      exact completed_sound KeySafe ReplySafe (OnSuccess ReplySafe)
        (NativeTypeCallGraph.body _ call)
        (NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes call)
        (available _ primitive depth) availableSafe (.ok reply) (completed_some completed)

theorem available_safe (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (primitive : PrimitiveStore) (ports : PrimitiveSafe primitive)
    (depth : Nat) (key : Question) (keySafe : KeySafe key) (reply : Reply)
    (found : available (TypeScopeMatcher.ops world normalize subtypes) primitive depth key = some reply) :
    ReplySafe reply := by
  cases key with
  | inl key => exact ports key keySafe reply found
  | inr call => exact returned_safe world normalize normalizeSafe subtypes primitive ports depth call reply found

theorem reached_keys_safe (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (primitive : PrimitiveStore) (ports : PrimitiveSafe primitive)
    (depth : Nat) (call : Call) :
    ∀ read ∈ (run (available (TypeScopeMatcher.ops world normalize subtypes) primitive depth)
      (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeCallGraph.body (TypeScopeMatcher.ops world normalize subtypes) call))).reads,
      KeySafe read.1 :=
  reads_valid KeySafe ReplySafe (OnSuccess ReplySafe) _
    (NativeTypeCallGraphSafety.body world normalize normalizeSafe subtypes call) _
    (available_safe world normalize normalizeSafe subtypes primitive ports depth)

theorem expanded_keys_safe (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (primitive : PrimitiveStore) (ports : PrimitiveSafe primitive)
    (depth : Nat) : ∀ call read,
      read ∈ (run primitive (NativeTypeRecursiveDriver.expand
        (TypeScopeMatcher.ops world normalize subtypes) depth call)).reads → KeySafe (.inl read.1) := by
  induction depth with
  | zero => intro call read member; cases member
  | succ depth ih =>
      intro call read member
      rw [NativeTypeRecursiveDriver.expanded_reads] at member
      obtain ⟨query, visited, nested⟩ := List.mem_flatMap.mp member
      have keySafe := reached_keys_safe world normalize normalizeSafe subtypes primitive ports depth call query visited
      cases query with
      | mk key reply =>
          cases key with
          | inl primitiveKey =>
              simp only [expandedService, run, List.mem_singleton] at nested
              cases nested
              exact keySafe
          | inr child => exact ih child read nested

theorem source_returns_safe (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (world : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (depth : Nat) (call : Call) (reply : Reply)
    (completed : evaluate (TypeScopeMatcher.ops world normalize subtypes)
      (NativeTypeSourcePorts.primitive source world) depth call = some reply) : ReplySafe reply :=
  returned_safe world normalize normalizeSafe subtypes _ (NativeTypeSourcePorts.primitive_safe source safe world)
    depth call reply completed

/-- Primitive-world stability is derived from the source packet, actual
annotation lookup and completed subtype rounds. Reached closure seeds are
proved safe by the recursive graph, not assumed by this theorem. -/
theorem source_primitive_world_stable (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (operationWorld first second : RetainedTypePayloads.ExternalView) (normalize : Atom → Atom)
    (normalizeSafe : ∀ atom, resourceFree atom = true → resourceFree (normalize atom) = true)
    (subtypes : List Atom → List Atom) (depth : Nat) (call : Call) :
    evaluate (TypeScopeMatcher.ops operationWorld normalize subtypes)
        (NativeTypeSourcePorts.primitive source second) depth call =
      evaluate (TypeScopeMatcher.ops operationWorld normalize subtypes)
        (NativeTypeSourcePorts.primitive source first) depth call := by
  apply primitive_replay
  intro read member
  have keySafe := expanded_keys_safe operationWorld normalize normalizeSafe subtypes _
    (NativeTypeSourcePorts.primitive_safe source safe first) depth call read member
  exact (NativeTypeSourcePorts.primitive_world source safe second first read.1 keySafe).trans
    (run_agrees (NativeTypeSourcePorts.primitive source first)
      (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops operationWorld normalize subtypes) depth call) read member)

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveSafety
