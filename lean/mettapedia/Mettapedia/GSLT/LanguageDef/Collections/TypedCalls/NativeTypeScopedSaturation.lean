import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallRank
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedReads

/-!
# Structural saturation of occurrence-scoped inference

The existing evaluator is unchanged. Beyond the input call's structural
rank, both its reply and its complete fresh-name supply are independent of
recursion depth. This includes missing primitive observations: a separately
bounded subtype closure may remain incomplete at every saturated depth.
The bound is ghost evidence, not a new native cache key or admission gate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSaturation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines
open ReadOnlyQuery ReadOnlyQueryDemand ReadOnlyQueryRelation
open NativeTypeCallGraph NativeTypeCallRank
open NativeTypeSourcePorts (Source)
open NativeTypeScopedReads (evaluate primitive retain)
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

theorem evaluate_eq_of_rank (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) :
    ∀ (call : Call) (first second : Nat), rank call < first → rank call < second →
      ∀ supply, evaluate ops source world first call supply = evaluate ops source world second call supply := by
  intro call
  induction call using (measure rank).wf.induction with
  | h call ih =>
      intro first second firstEnough secondEnough supply
      cases first with
      | zero => omega
      | succ first =>
          cases second with
          | zero => omega
          | succ second =>
              let firstService : Supply → Question → Option Reply × Supply := fun current =>
                fun | .inl key => primitive source world current key
                    | .inr child => evaluate ops source world first child current
              let secondService : Supply → Question → Option Reply × Supply := fun current =>
                fun | .inl key => primitive source world current key
                    | .inr child => evaluate ops source world second child current
              have same : ∀ current key, KeyBelow (rank call) key →
                  firstService current key = secondService current key := by
                intro current key bounded
                cases key with
                | inl key => rfl
                | inr child =>
                    have smaller : rank child < rank call := bounded
                    exact ih child smaller first second (by omega) (by omega) current
              have observed := demand_run_eq (KeyBelow (rank call)) (fun _ => True) (fun _ => True)
                (refl_of_guarantees _ _ _ (body ops call) (body_keys_below ops call))
                firstService secondService same (fun _ _ _ _ _ => trivial) supply
              change
                (NativeTypeRecursiveDriver.completed
                    (QueryState.run firstService (ReadOnlyQueryDemand.demand (body ops call)) supply).answer,
                  retain (QueryState.run firstService (ReadOnlyQueryDemand.demand (body ops call)) supply).state
                    (NativeTypeRecursiveDriver.completed
                      (QueryState.run firstService (ReadOnlyQueryDemand.demand (body ops call)) supply).answer)) =
                (NativeTypeRecursiveDriver.completed
                    (QueryState.run secondService (ReadOnlyQueryDemand.demand (body ops call)) supply).answer,
                  retain (QueryState.run secondService (ReadOnlyQueryDemand.demand (body ops call)) supply).state
                    (NativeTypeRecursiveDriver.completed
                      (QueryState.run secondService (ReadOnlyQueryDemand.demand (body ops call)) supply).answer))
              rw [observed]

/-- The structural representative can be used for proof-only completion
evidence without adding recursion depth to an operational cache key. -/
theorem evaluate_canonical_depth (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) (call : Call) (depth : Nat)
    (enough : rank call < depth) (supply : Supply) :
    evaluate ops source world depth call supply = evaluate ops source world (rank call + 1) call supply :=
  evaluate_eq_of_rank ops source world call depth (rank call + 1) enough (by omega) supply

theorem saturated_missing_stays_missing (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (world : ExternalView) (call : Call) (first second : Nat)
    (firstEnough : rank call < first) (secondEnough : rank call < second) (supply : Supply)
    (missing : (evaluate ops source world first call supply).1 = none) :
    (evaluate ops source world second call supply).1 = none ∧
      (evaluate ops source world second call supply).2 = (evaluate ops source world first call supply).2 := by
  rw [← evaluate_eq_of_rank ops source world call first second firstEnough secondEnough supply]
  exact ⟨missing, rfl⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeScopedSaturation
