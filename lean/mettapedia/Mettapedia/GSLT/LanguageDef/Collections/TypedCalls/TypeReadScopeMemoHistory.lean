import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemo

/-!
# Mixed source-update and type-query histories retain cache validity

Queries execute the existing prepared request; declined requests keep the
session and are recorded distinctly from an unfinished inquiry. Source
histories run through the existing edit/import/layer publication algorithms.
The final cache invariant is derived from initialization and execution, not
assumed separately after every query or mutation.

Recursion-depth bounds are proof-only approximation evidence. The trace is
not a physical work-budget, a native memory-lifetime proof or a claim that
declining a prepared request exhausts the source language.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoHistory

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadScopeMemo
open RetainedTypePayloads (ExternalView)

inductive Event (size : Nat) where
  | refresh (actions : List (NativeTypingScopeOverlays.Action size))
  | query (depth : Nat) (call : Call)

inductive Bounded {size : Nat} : Event size → Prop where
  | refresh (actions : List (NativeTypingScopeOverlays.Action size)) : Bounded (.refresh actions)
  | query (depth : Nat) (call : Call) : NativeTypeCallRank.rank call < depth → Bounded (.query depth call)

inductive Observation where
  | declined (call : Call)
  | inquiry (call : Call) (reply : Option Reply)

def step {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (allow : Call → Bool)
    (session : Session size) : Event size → Option Observation × Session size
  | .refresh actions => (none, refresh session actions)
  | .query depth call =>
      match request? ops configuration external allow depth call session with
      | none => (some (.declined call), session)
      | some (reply, after) => (some (.inquiry call reply), after)

theorem step_valid {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (allow : Call → Bool) (session : Session size)
    (valid : Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external session)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant configuration.alpha)
    (event : Event size) (bounded : Bounded event) :
    Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external
      (step (TypeScopeMatcher.currentOps external normalize subtypes)
        configuration external allow session event).2 := by
  cases bounded with
  | refresh actions => exact refresh_valid _ configuration external session valid actions
  | query depth call enough =>
      simp only [step]
      split
      · exact valid
      · rename_i result returned
        exact request_valid configuration external normalize normalizer subtypes allow depth call session
          valid alpha enough (_, result) returned

def execute {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (allow : Call → Bool) :
    Session size → List (Event size) → List Observation × Session size
  | session, [] => ([], session)
  | session, event :: events =>
      let first := step ops configuration external allow session event
      let later := execute ops configuration external allow first.2 events
      (first.1.toList ++ later.1, later.2)

theorem execute_valid {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (allow : Call → Bool)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant configuration.alpha)
    (events : List (Event size)) : ∀ session,
    Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external session →
    (∀ event ∈ events, Bounded event) →
    Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external
      (execute (TypeScopeMatcher.currentOps external normalize subtypes)
        configuration external allow session events).2 := by
  induction events with
  | nil => intro _ valid _; exact valid
  | cons event events ih =>
      intro session valid bounded
      exact ih _ (step_valid configuration external normalize normalizer subtypes allow session valid alpha
          event (bounded event (by simp)))
        (fun next member => bounded next (List.mem_cons_of_mem _ member))

theorem initialized_history_valid {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (allow : Call → Bool)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant configuration.alpha)
    (scope : Scope size) (supply : TypeReadSupply.Supply) (events : List (Event size))
    (bounded : ∀ event ∈ events, Bounded event) :
    Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external
      (execute (TypeScopeMatcher.currentOps external normalize subtypes)
        configuration external allow (initial scope supply) events).2 :=
  execute_valid configuration external normalize normalizer subtypes allow alpha events _
    (initial_valid _ configuration external scope supply) bounded

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemoHistory
