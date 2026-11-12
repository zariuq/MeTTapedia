import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadSourceProjection
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemoRefinement
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.NativeTypingScopeOverlays

/-!
# Validated typing scopes own recursive retained replies

The existing overlay/import token decides whether an edit history permits
reuse. A successful check derives equality of actual typing packets. A failed
check clears retained entries, advances their local authority and keeps the
reached source state and private-name supply. Query execution then preserves
historical cache validity using the recursive source/memo theorem.

Raw source rows may contain unrelated mutable data: the source-projection gate
derives safety only for the rows that determine inference. Public input names
are reserved before query execution. A refused gate yields no prepared offer,
not a completed empty type family or a source-language error.

Configuration is fixed across each session history. Native compressed epoch
and address codecs, counter bounds, primitive implementation and finite work
accounting remain separate from this source-level authority adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemo

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts TypeReadQueryWorlds
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

abbrev Scope (size : Nat) := NativeTypingScopeOverlays.State size

def rawSource {size : Nat} (configuration : Source) (scope : Scope size) : Source :=
  { configuration with rows := NativeTypingScopeOverlays.layeredRows scope.source scope.reader scope.layers }

def snapshot {size : Nat} (configuration : Source) (scope : Scope size) : Source :=
  TypeReadSourceProjection.project (rawSource configuration scope)

/-- The packet equality comes from the actual edit/import/layer validator,
not a hypothesis that the old and new inference results already agree. -/
theorem snapshot_validated {size : Nat} (configuration : Source) (scope : Scope size)
    (actions : List (NativeTypingScopeOverlays.Action size))
    (bounded : NativeTypingScopeOverlays.CeilingValid scope.source scope.reader scope.layers)
    (accepted : NativeTypingScopeOverlays.check
      (NativeTypingScopeOverlays.execute scope actions) (NativeTypingScopeOverlays.token scope) = true) :
    snapshot configuration (NativeTypingScopeOverlays.execute scope actions) = snapshot configuration scope := by
  have same := NativeTypingScopeOverlays.validated_packet scope actions bounded accepted
  change Source.mk (NativeTypingScopeOverlays.packet (NativeTypingScopeOverlays.execute scope actions))
      (NativeTypingScopeCapture.capture configuration.intrinsicRows) configuration.rename
      configuration.subtypeBudget configuration.subtypeFresh configuration.alpha =
    Source.mk (NativeTypingScopeOverlays.packet scope)
      (NativeTypingScopeCapture.capture configuration.intrinsicRows) configuration.rename
      configuration.subtypeBudget configuration.subtypeFresh configuration.alpha
  rw [same]

structure Session (size : Nat) where
  scope : Scope size
  authority : Nat
  inference : TypeReadQueryMemo.State

def Valid {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (session : Session size) : Prop :=
  TypeReadQueryMemo.Valid ops (snapshot configuration session.scope) external
    TypeReadQueryMemoRefinement.completionDepth session.authority session.inference.cache

def initial {size : Nat} (scope : Scope size) (supply : Supply) : Session size :=
  ⟨scope, 0, ⟨supply, []⟩⟩

theorem initial_valid {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (scope : Scope size) (supply : Supply) :
    Valid ops configuration external (initial scope supply) :=
  TypeReadQueryMemoRefinement.empty_valid ops (snapshot configuration scope) external 0

def inheritedBound {size : Nat} (scope : Scope size) : Bool :=
  match scope.layers with
  | [] => true
  | first :: _ => decide (first.ceiling ≤ (scope.source.sources scope.reader).view.entries.length)

theorem inheritedBound_iff {size : Nat} (scope : Scope size) :
    inheritedBound scope = true ↔
      NativeTypingScopeOverlays.CeilingValid scope.source scope.reader scope.layers := by
  cases layers : scope.layers <;> simp [inheritedBound, layers, NativeTypingScopeOverlays.CeilingValid]

def refresh {size : Nat} (session : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) : Session size :=
  let after := NativeTypingScopeOverlays.execute session.scope actions
  if NativeTypingScopeOverlays.check after (NativeTypingScopeOverlays.token session.scope) &&
      inheritedBound session.scope then
    { session with scope := after }
  else
    ⟨after, session.authority + 1, ⟨session.inference.supply, []⟩⟩

theorem refresh_scope {size : Nat} (session : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) :
    (refresh session actions).scope = NativeTypingScopeOverlays.execute session.scope actions := by
  dsimp only [refresh]
  split <;> rfl

theorem refresh_supply {size : Nat} (session : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size)) :
    (refresh session actions).inference.supply = session.inference.supply := by
  dsimp only [refresh]
  split <;> rfl

theorem refresh_valid {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (session : Session size)
    (valid : Valid ops configuration external session)
    (actions : List (NativeTypingScopeOverlays.Action size)) :
    Valid ops configuration external (refresh session actions) := by
  dsimp only [refresh]
  split
  next accepted =>
    have flags := Bool.and_eq_true_iff.mp accepted
    have bounded := (inheritedBound_iff session.scope).mp flags.2
    change TypeReadQueryMemo.Valid ops
      (snapshot configuration (NativeTypingScopeOverlays.execute session.scope actions)) external
      TypeReadQueryMemoRefinement.completionDepth session.authority session.inference.cache
    rw [snapshot_validated configuration session.scope actions bounded flags.1]
    exact valid
  next _ =>
    exact TypeReadQueryMemoRefinement.empty_valid ops _ external _

/-- A host that derives valid inherited bounds may erase that admission
check. The remaining test is exactly its existing scope-token comparison. -/
theorem refresh_of_bounded {size : Nat} (session : Session size)
    (actions : List (NativeTypingScopeOverlays.Action size))
    (bounded : NativeTypingScopeOverlays.CeilingValid session.scope.source session.scope.reader session.scope.layers) :
    refresh session actions =
      if NativeTypingScopeOverlays.check (NativeTypingScopeOverlays.execute session.scope actions)
          (NativeTypingScopeOverlays.token session.scope) then
        { session with scope := NativeTypingScopeOverlays.execute session.scope actions }
      else
        ⟨NativeTypingScopeOverlays.execute session.scope actions, session.authority + 1,
          ⟨session.inference.supply, []⟩⟩ := by
  have boundedCheck := (inheritedBound_iff session.scope).mpr bounded
  simp only [refresh, boundedCheck, Bool.and_true]

/-- Reserve the actual source operand's names before any private read. This
is scope protection, not a restriction to ground input expressions. -/
def reserve (call : Call) (state : TypeReadQueryMemo.State) : TypeReadQueryMemo.State :=
  { state with supply := { state.supply with used := questionNames (.inr call) ++ state.supply.used } }

def inputWorld (call : Call) : Coordinates := ⟨Equiv.refl String, questionNames (.inr call)⟩

theorem input_fixed (call : Call) : Fixed (inputWorld call) (questionNames (.inr call)) :=
  ⟨fun _ member => member, fun _ _ => rfl⟩

theorem input_protected (call : Call) (state : TypeReadQueryMemo.State) :
    Protected (inputWorld call) (reserve call state).supply (reserve call state).supply := by
  constructor
  · exact fun _ member => List.mem_append_left _ member
  · intro name member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact List.mem_append_left _ present

def query {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (allow : Call → Bool)
    (depth : Nat) (call : Call) (session : Session size) : Option Reply × Session size :=
  let result := TypeReadQueryMemo.evaluate ops (snapshot configuration session.scope) external
    session.authority allow depth call (reserve call session.inference)
  (result.1, { session with inference := result.2 })

def request? {size : Nat} (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (configuration : Source) (external : ExternalView) (allow : Call → Bool)
    (depth : Nat) (call : Call) (session : Session size) : Option (Option Reply × Session size) :=
  if TypeReadSourceProjection.ready (rawSource configuration session.scope) then
    some (query ops configuration external allow depth call session)
  else none

/-- Successful source admission yields raw-source correspondence and earns
the next session's validity, including caches filled by recursive children. -/
theorem query_related {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (allow : Call → Bool)
    (depth : Nat) (call : Call) (session : Session size)
    (valid : Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external session)
    (accepted : TypeReadSourceProjection.ready (rawSource configuration session.scope) = true)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant configuration.alpha)
    (enough : NativeTypeCallRank.rank call < depth) :
    let result := query (TypeScopeMatcher.currentOps external normalize subtypes)
      configuration external allow depth call session
    let reference := NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      (rawSource configuration session.scope) external depth call (reserve call session.inference).supply
    ∃ after, Grows (inputWorld call) after ∧
      Protected after reference.2 result.2.inference.supply ∧
      Option.Rel (RepliesRelated after) reference.1 result.1 ∧
      Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external result.2 := by
  let ops := TypeScopeMatcher.currentOps external normalize subtypes
  let source := rawSource configuration session.scope
  have readySafe := TypeReadSourceProjection.project_safe source accepted
  have states : TypeReadQueryMemoRefinement.States ops (snapshot configuration session.scope) external
      TypeReadQueryMemoRefinement.completionDepth session.authority (inputWorld call)
      (reserve call session.inference).supply (reserve call session.inference) :=
    ⟨input_protected call session.inference, valid⟩
  obtain ⟨after, grown, kept, replies⟩ := TypeReadQueryMemoRefinement.evaluate_related
    (snapshot configuration session.scope) external readySafe alpha normalize normalizer subtypes
    TypeReadQueryMemoRefinement.completionDepth TypeReadQueryMemoRefinement.completion_saturated
    session.authority allow call depth depth enough enough (inputWorld call)
    (reserve call session.inference).supply (reserve call session.inference) (input_fixed call) states
  have projected := TypeReadSourceProjection.evaluate_project ops source external accepted depth
    call (reserve call session.inference).supply
  change NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      (snapshot configuration session.scope) external depth call (reserve call session.inference).supply =
    NativeTypeScopedReads.evaluate (TypeScopeMatcher.currentOps external normalize subtypes)
      (rawSource configuration session.scope) external depth call (reserve call session.inference).supply at projected
  have supplies := kept.1
  rw [projected] at supplies replies
  exact ⟨after, grown, supplies, replies, kept.2⟩

theorem request_valid {size : Nat} (configuration : Source) (external : ExternalView)
    (normalize : Atom → Atom) (normalizer : TypeReadQueryRows.Normalizers normalize normalize)
    (subtypes : List Atom → List Atom) (allow : Call → Bool)
    (depth : Nat) (call : Call) (session : Session size)
    (valid : Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external session)
    (alpha : SubtypeClosureCoordinates.AlphaEquivariant configuration.alpha)
    (enough : NativeTypeCallRank.rank call < depth)
    (result : Option Reply × Session size)
    (returned : request? (TypeScopeMatcher.currentOps external normalize subtypes)
      configuration external allow depth call session = some result) :
    Valid (TypeScopeMatcher.currentOps external normalize subtypes) configuration external result.2 := by
  unfold request? at returned
  split at returned
  next admitted =>
    cases Option.some.inj returned
    obtain ⟨_, _, _, _, later⟩ := query_related configuration external normalize normalizer subtypes allow
      depth call session valid admitted alpha enough
    exact later
  next _ => cases returned

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadScopeMemo
