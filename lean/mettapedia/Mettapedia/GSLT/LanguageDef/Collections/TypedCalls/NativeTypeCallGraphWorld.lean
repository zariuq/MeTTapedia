import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativePartialTypeWorld
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveSafety

/-! # Reached-operation world congruence of the complete call graph -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphWorld

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryPartialComposition
open NativeTypeCallGraph NativeTypeCallGraphSafety TypeDependencyAdmission
open RetainedTypePayloads (ExternalView)

abbrev Store := Question → Option Reply

def StoreSafe (available : Store) : Prop :=
  ∀ key, KeySafe key → ∀ reply, available key = some reply → ReplySafe reply

def liftObservation {Result : Type}
    (result : Observation (NativeTypeDemand.Question Atom) (Option Reply) Result) :
    Observation Question (Option Reply) Result :=
  ⟨result.answer, result.reads.map fun read => (viewQuestion read.1, read.2)⟩

theorem lifted_demand {Result : Type} (available : Store)
    (program : Program (NativeTypeDemand.Question Atom) Reply Result) :
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand (NativeTypeCallGraph.liftViews program)) =
      liftObservation (run (fun key => available (viewQuestion key))
        (Mettapedia.Machines.ReadOnlyQueryDemand.demand program)) := by
  induction program with
  | pure answer => rfl
  | read key next ih =>
      simp only [NativeTypeCallGraph.liftViews, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
      cases found : available (viewQuestion key) with
      | none => rfl
      | some reply =>
          rw [ih reply]
          rfl

theorem view_store_safe (available : Store) (safe : StoreSafe available) :
    NativePartialTypeWorld.StoreSafe (fun key => available (viewQuestion key)) :=
  fun key reply found => safe _ (viewQuestion_safe key) reply found

theorem ordinary_world (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizers : ∀ type_, resourceFree type_ = true → normalizeFirst type_ = normalizeSecond type_)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (available : Store) (safe : StoreSafe available)
    (head : Atom) (values : List Atom) :
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.ordinary (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) head values)) =
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.ordinary (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) head values)) := by
  simp only [NativeTypeCallGraph.ordinary, NativeTypeCallGraph.typesRead,
    Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
  cases found : available (.inr (.operatorRows head)) with
  | none => rfl
  | some reply =>
      cases reply with
      | kind _ | class_ _ => rfl
      | types rows =>
          have rowsSafe : resourceFreeList rows = true := safe (.inr (.operatorRows head)) trivial _ found
          have arrowEq : (rows.any fun row => ((TypeScopeMatcher.ops first normalizeFirst subtypesFirst).arrow row).isSome) =
              (rows.any fun row => ((TypeScopeMatcher.ops second normalizeSecond subtypesSecond).arrow row).isSome) := rfl
          simp only [← arrowEq]
          split
          · simp only [mapTypes, run_demand_map, lifted_demand]
            rw [NativePartialTypeWorld.rowsPlan_world first second normalizeFirst normalizeSecond normalizers
              subtypesFirst subtypesSecond (fun key => available (viewQuestion key))
              (view_store_safe available safe) values rows rowsSafe]
          · rfl

theorem node_world (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizers : ∀ type_, resourceFree type_ = true → normalizeFirst type_ = normalizeSecond type_)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (available : Store) (safe : StoreSafe available)
    (direct : Bool) (head : Atom) (values : List Atom) :
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.node (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) direct head values)) =
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.node (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) direct head values)) := by
  simp only [NativeTypeCallGraph.node, Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
  cases found : available (.inl (.classify head values)) with
  | none => rfl
  | some reply =>
      cases reply with
      | types _ | kind _ => rfl
      | class_ kind =>
          cases kind with
          | nativeMork | listValue => rfl
          | ordinary =>
              cases direct with
              | false =>
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [ordinary_world first second normalizeFirst normalizeSecond normalizers
                    subtypesFirst subtypesSecond available safe head values]
              | true =>
                  simp only [if_true, NativeTypeCallGraph.typesRead,
                    Mettapedia.Machines.ReadOnlyQueryDemand.demand, run]
                  cases annotations : available (.inl (.annotations (.expression (head :: values)))) with
                  | none => rfl
                  | some reply =>
                      cases reply with
                      | kind _ | class_ _ => rfl
                      | types types =>
                          simp only
                          split
                          · rw [ordinary_world first second normalizeFirst normalizeSecond normalizers
                              subtypesFirst subtypesSecond available safe head values]
                          · rfl

theorem body_world (first second : ExternalView) (normalizeFirst normalizeSecond : Atom → Atom)
    (normalizers : ∀ type_, resourceFree type_ = true → normalizeFirst type_ = normalizeSecond type_)
    (subtypesFirst subtypesSecond : List Atom → List Atom) (available : Store) (safe : StoreSafe available)
    (call : Call) :
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.body (TypeScopeMatcher.ops first normalizeFirst subtypesFirst) call)) =
    run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand
      (NativeTypeCallGraph.body (TypeScopeMatcher.ops second normalizeSecond subtypesSecond) call)) := by
  cases call with
  | infer direct atom =>
      cases atom with
      | var _ | symbol _ | grounded _ => rfl
      | expression children =>
          cases children with
          | nil => rfl
          | cons head values =>
              exact node_world first second normalizeFirst normalizeSecond normalizers
                subtypesFirst subtypesSecond available safe direct head values
  | tuplePart atHead atom => rfl
  | operatorRows atom => rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraphWorld
