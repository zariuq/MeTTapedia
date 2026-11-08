import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphWorld

/-!
# World independence of recursive source inference

The induction covers actual recursive child calls, not an annotation-only
approximation. Source annotation/freshening and completed subtype ports are
derived from the captured packet. The partial row-plan law supplies the
reached matching and normalization operations. Both unavailable and completed
results retain their distinctions, and nested primitive certificates keep
their execution order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveWorld

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open NativeTypeCallGraph NativeTypeRecursiveDriver NativeTypeRecursiveSafety TypeDependencyAdmission
open RetainedTypePayloads (ExternalView)

theorem step_world_of_children (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (firstSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (secondSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeSecond atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat)
    (children : ∀ call,
      evaluate (TypeScopeMatcher.ops first normalizeFirst subtypesFirst)
        (NativeTypeSourcePorts.primitive source first) depth call =
      evaluate (TypeScopeMatcher.ops second normalizeSecond subtypesSecond)
        (NativeTypeSourcePorts.primitive source second) depth call)
    (call : Call) :
    run (available (TypeScopeMatcher.ops first normalizeFirst subtypesFirst)
      (NativeTypeSourcePorts.primitive source first) depth)
      (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeCallGraph.body (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) call)) =
    run (available (TypeScopeMatcher.ops second normalizeSecond subtypesSecond)
      (NativeTypeSourcePorts.primitive source second) depth)
      (Mettapedia.Machines.ReadOnlyQueryDemand.demand
        (NativeTypeCallGraph.body (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) call)) := by
  let before := available (TypeScopeMatcher.ops first normalizeFirst subtypesFirst)
    (NativeTypeSourcePorts.primitive source first) depth
  let after := available (TypeScopeMatcher.ops second normalizeSecond subtypesSecond)
    (NativeTypeSourcePorts.primitive source second) depth
  have keys := reached_keys_safe first normalizeFirst firstSafe subtypesFirst _
    (NativeTypeSourcePorts.primitive_safe source safe first) depth call
  have replay := run_eq_of_agrees before after
    (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.body (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) call)) (by
        intro read member
        have old := run_agrees before
          (Mettapedia.Machines.ReadOnlyQueryDemand.demand
            (NativeTypeCallGraph.body (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) call)) read member
        have keySafe := keys read member
        cases read with
        | mk key reply =>
            cases key with
            | inl primitiveKey =>
                exact (NativeTypeSourcePorts.primitive_world source safe second first primitiveKey keySafe).trans old
            | inr child => exact (children child).symm.trans old)
  have operations := NativeTypeCallGraphWorld.body_world first second normalizeFirst normalizeSecond normalizers
    subtypesFirst subtypesSecond after
    (available_safe second normalizeSecond secondSafe subtypesSecond _
      (NativeTypeSourcePorts.primitive_safe source safe second) depth) call
  exact replay.symm.trans operations

/-- Every depth is compared, including genuine incompletion. A completed
typing is not assumed as a premise of world independence. -/
theorem evaluate_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (firstSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (secondSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeSecond atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) : ∀ call,
    evaluate (TypeScopeMatcher.ops first normalizeFirst subtypesFirst)
        (NativeTypeSourcePorts.primitive source first) depth call =
      evaluate (TypeScopeMatcher.ops second normalizeSecond subtypesSecond)
        (NativeTypeSourcePorts.primitive source second) depth call := by
  induction depth with
  | zero => intro call; rfl
  | succ depth ih =>
      intro call
      rw [evaluate_unfold, evaluate_unfold]
      exact congrArg (fun result => completed result.answer)
        (step_world_of_children source safe first second normalizeFirst normalizeSecond firstSafe secondSafe
          normalizers subtypesFirst subtypesSecond depth ih call)

theorem expanded_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (firstSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeFirst atom) = true)
    (secondSafe : ∀ atom, resourceFree atom = true → resourceFree (normalizeSecond atom) = true)
    (normalizers : ∀ atom, resourceFree atom = true → normalizeFirst atom = normalizeSecond atom)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) : ∀ call,
    run (NativeTypeSourcePorts.primitive source first)
        (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) depth call) =
      run (NativeTypeSourcePorts.primitive source second)
        (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) depth call) := by
  induction depth with
  | zero => intro call; rfl
  | succ depth ih =>
      intro call
      have answerEq :
          (run (NativeTypeSourcePorts.primitive source first)
            (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) (depth + 1) call)).answer =
          (run (NativeTypeSourcePorts.primitive source second)
            (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) (depth + 1) call)).answer := by
        rw [expanded_answer, expanded_answer]
        exact evaluate_world source safe first second normalizeFirst normalizeSecond firstSafe secondSafe
          normalizers subtypesFirst subtypesSecond (depth + 1) call
      have traceEq := step_world_of_children source safe first second normalizeFirst normalizeSecond firstSafe secondSafe
        normalizers subtypesFirst subtypesSecond depth
        (evaluate_world source safe first second normalizeFirst normalizeSecond firstSafe secondSafe
          normalizers subtypesFirst subtypesSecond depth) call
      have readsEq :
          (run (NativeTypeSourcePorts.primitive source first)
            (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) (depth + 1) call)).reads =
          (run (NativeTypeSourcePorts.primitive source second)
            (NativeTypeRecursiveDriver.expand (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) (depth + 1) call)).reads := by
        rw [expanded_reads, expanded_reads, ← traceEq]
        apply List.flatMap_congr
        intro query member
        have keySafe := reached_keys_safe first normalizeFirst firstSafe subtypesFirst _
          (NativeTypeSourcePorts.primitive_safe source safe first) depth call query member
        cases query with
        | mk key reply =>
            cases key with
            | inl primitiveKey =>
                simp only [expandedService, run,
                  NativeTypeSourcePorts.primitive_world source safe first second primitiveKey keySafe]
            | inr child => exact congrArg Observation.reads (ih child)
      exact congrArg₂ Observation.mk answerEq readsEq

/-- Concrete source normalization discharges the reached normalizer
assumptions. Only the individual primitive result-closure contract remains;
the whole recursive inference service is not assumed stable. -/
theorem source_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (active : String → Bool) (primitive : TypeNormalizationScope.Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) (call : Call) :
    evaluate (TypeDependencyClosure.sourceOps first active primitive subtypesFirst)
        (NativeTypeSourcePorts.primitive source first) depth call =
      evaluate (TypeDependencyClosure.sourceOps second active primitive subtypesSecond)
        (NativeTypeSourcePorts.primitive source second) depth call :=
  evaluate_world source safe first second _ _
    (TypeNormalizationScope.normalize_preserves active _
      (TypeNormalizationScope.observed_closed active first primitive closed))
    (TypeNormalizationScope.normalize_preserves active _
      (TypeNormalizationScope.observed_closed active second primitive closed))
    (TypeNormalizationScope.normalize_world active first second primitive closed)
    subtypesFirst subtypesSecond depth call

theorem expanded_source_world (source : NativeTypeSourcePorts.Source) (safe : NativeTypeSourcePorts.Safe source)
    (first second : ExternalView) (active : String → Bool) (primitive : TypeNormalizationScope.Primitive)
    (closed : TypeNormalizationScope.ResultsClosed active primitive)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (depth : Nat) (call : Call) :
    run (NativeTypeSourcePorts.primitive source first)
        (NativeTypeRecursiveDriver.expand (TypeDependencyClosure.sourceOps first active primitive subtypesFirst) depth call) =
      run (NativeTypeSourcePorts.primitive source second)
        (NativeTypeRecursiveDriver.expand (TypeDependencyClosure.sourceOps second active primitive subtypesSecond) depth call) :=
  expanded_world source safe first second _ _
    (TypeNormalizationScope.normalize_preserves active _
      (TypeNormalizationScope.observed_closed active first primitive closed))
    (TypeNormalizationScope.normalize_preserves active _
      (TypeNormalizationScope.observed_closed active second primitive closed))
    (TypeNormalizationScope.normalize_world active first second primitive closed)
    subtypesFirst subtypesSecond depth call

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveWorld
