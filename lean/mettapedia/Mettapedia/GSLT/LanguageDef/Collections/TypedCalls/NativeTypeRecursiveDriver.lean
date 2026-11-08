import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeCallGraph

/-!
# Completed recursive native type requests

Recursive requests execute the source call graph through the existing partial
observation interpreter. Primitive annotation, kind, classification, intrinsic
typing and completed subtype closure remain distinct ports. A missing child
or unfinished closure returns `none`, which is refusal to publish a typing,
not the completed answer `some (.types [])`.

The expanded interpreter replaces every demanded recursive request with its
own computation, exposing a certificate containing only primitive source
observations. Its equality with the recursive driver is proved, including
the order of nested requests. A completed result is stable at every greater
recursion depth; no convergence claim is inferred from two equal incomplete
approximations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveDriver

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Machines.ReadOnlyQuery
open Mettapedia.Machines.ReadOnlyQueryDemand
open NativeTypeCallGraph NativeTypeViews

abbrev PrimitiveStore := Primitive → Option Reply

def completed : Option (Except Unit Reply) → Option Reply
  | some (.ok reply) => some reply
  | _ => none

theorem completed_some {response : Option (Except Unit Reply)} {reply : Reply}
    (returned : completed response = some reply) : response = some (.ok reply) := by
  cases response with
  | none => cases returned
  | some result => cases result with
      | error error => cases returned
      | ok value => exact congrArg (some ∘ Except.ok) (Option.some.inj returned)

def evaluate (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore) :
    Nat → Call → Option Reply
  | 0, _ => none
  | depth + 1, call =>
      let available : Question → Option Reply := fun
        | .inl key => primitive key
        | .inr child => evaluate ops primitive depth child
      completed (run available (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call))).answer

def available (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) : Question → Option Reply
  | .inl key => primitive key
  | .inr child => evaluate ops primitive depth child

theorem evaluate_unfold (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) (call : Call) :
    evaluate ops primitive (depth + 1) call =
      completed (run (available ops primitive depth) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call))).answer := rfl

def expand (ops : Ops Atom TypeScopeMatcher.State Atom) :
    Nat → Call → Program Primitive (Option Reply) (Option Reply)
  | 0, _ => .pure none
  | depth + 1, call =>
      let service : Question → Program Primitive (Option Reply) (Option Reply) := fun
        | .inl key => .read key (fun reply => .pure reply)
        | .inr child => expand ops depth child
      map completed (Mettapedia.Machines.ReadOnlyQueryExpansion.expand service (body ops call))

theorem expanded_answer (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) (call : Call) :
    (run primitive (expand ops depth call)).answer = evaluate ops primitive depth call := by
  induction depth generalizing call with
  | zero => rfl
  | succ depth ih =>
      simp only [expand, run_map, Mettapedia.Machines.ReadOnlyQueryExpansion.expansion_answer,
        evaluate_unfold]
      congr 2
      apply congrArg (fun oracle => run oracle (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call)))
      funext query
      cases query with
      | inl key => rfl
      | inr child => exact ih child

def expandedService (ops : Ops Atom TypeScopeMatcher.State Atom) (depth : Nat) :
    Question → Program Primitive (Option Reply) (Option Reply)
  | .inl key => .read key (fun reply => .pure reply)
  | .inr child => expand ops depth child

theorem expanded_service_replies (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) :
    Mettapedia.Machines.ReadOnlyQueryExpansion.replies primitive (expandedService ops depth) =
      available ops primitive depth := by
  funext query
  cases query with
  | inl key => rfl
  | inr child => exact expanded_answer ops primitive depth child

theorem expanded_reads (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) (call : Call) :
    (run primitive (expand ops (depth + 1) call)).reads =
      Mettapedia.Machines.ReadOnlyQueryExpansion.flatten primitive (expandedService ops depth)
        (run (available ops primitive depth) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call))).reads := by
  change (run primitive (map completed
    (Mettapedia.Machines.ReadOnlyQueryExpansion.expand (expandedService ops depth) (body ops call)))).reads = _
  rw [run_map, Mettapedia.Machines.ReadOnlyQueryExpansion.expansion_reads, expanded_service_replies]

/-- Exact primitive-certificate replay, after recursive children have been
expanded rather than retained as unexplained inference facts. -/
theorem primitive_replay (ops : Ops Atom TypeScopeMatcher.State Atom)
    (before after : PrimitiveStore) (depth : Nat) (call : Call)
    (agree : Agrees after (run before (expand ops depth call)).reads) :
    evaluate ops after depth call = evaluate ops before depth call := by
  rw [← expanded_answer, ← expanded_answer]
  exact congrArg Observation.answer (run_eq_of_agrees before after (expand ops depth call) agree)

theorem success_stable (ops : Ops Atom TypeScopeMatcher.State Atom) (primitive : PrimitiveStore)
    (depth : Nat) : ∀ extra call reply,
      evaluate ops primitive depth call = some reply →
      evaluate ops primitive (depth + extra) call = some reply := by
  induction depth with
  | zero => intro extra call reply success; cases success
  | succ depth ih =>
      intro extra call reply success
      have completedRun :
          (run (available ops primitive depth) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call))).answer =
            some (.ok reply) := completed_some success
      have successRun :
          (run (available ops primitive depth) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call))).answer ≠ none := by
        rw [completedRun]
        simp
      have replay := run_eq_of_agrees (available ops primitive depth)
        (available ops primitive (depth + extra)) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call)) (by
          intro read member
          have original := run_agrees (available ops primitive depth) (Mettapedia.Machines.ReadOnlyQueryDemand.demand (body ops call)) read member
          obtain ⟨value, isSome⟩ := Mettapedia.Machines.ReadOnlyQueryExpansion.successful_demand_reads_some
            (available ops primitive depth) (body ops call) successRun read member
          cases read with
          | mk key answer =>
              cases key with
              | inl key => exact original
              | inr child =>
                  have childDone : evaluate ops primitive depth child = some value := original.trans isSome
                  exact (ih extra child value childDone).trans isSome.symm)
      rw [Nat.succ_add, evaluate_unfold]
      rw [replay]
      exact success

theorem unavailable_is_not_empty (ops : Ops Atom TypeScopeMatcher.State Atom)
    (primitive : PrimitiveStore) (call : Call) :
    evaluate ops primitive 0 call = none ∧ evaluate ops primitive 0 call ≠ some (.types []) := by
  simp [evaluate]

/-- An actual source completion, including a completed empty answer, is
what licenses publication. A failed optimization may retain its residual
or use the canonical caller; it cannot publish an invented empty list. -/
def publishTypes (reply : Option Reply) : Option (List Atom) :=
  reply.bind fun | .types types => some types | _ => none

theorem publish_empty_only_if_complete {reply : Option Reply}
    (published : publishTypes reply = some []) : reply = some (.types []) := by
  cases reply with
  | none => cases published
  | some value => cases value <;> simp_all [publishTypes]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypeRecursiveDriver
