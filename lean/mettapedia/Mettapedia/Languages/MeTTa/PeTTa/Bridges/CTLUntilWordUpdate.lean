import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilRoundPublication
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryWordRefinement

/-!
# Exact fresh-word effects at source boundaries

The update relation observes the actual known and next-frontier occurrence
lists and the local collector. Its append law updates membership between
chunks; a repeated node in a later chunk cannot be republished against a
stale initial known set. The single-letter law is derived from the source
leaf's exact live guard decision.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate

open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilScopedRound
open CTLUntilRoundPublication (known frontier)
open Mettapedia.Machines.CTLUntilCandidateBag (fresh)

variable {Context Label : Type} [DecidableEq Label]

def Update (codec : Codec Label) (label : Label) (round : Nat) (query : Query)
    (word : List Nat) (before after : State Context) : Prop :=
  ∃ oldKnown oldFrontier,
    known codec label query before.world.state = some oldKnown ∧
    frontier codec label round query before.world.state = some oldFrontier ∧
    known codec label query after.world.state = some (oldKnown ++ fresh word oldKnown.toFinset) ∧
    frontier codec label round query after.world.state = some (oldFrontier ++ fresh word oldKnown.toFinset) ∧
    after.scope.collected.length = before.scope.collected.length + (fresh word oldKnown.toFinset).length

theorem Update.nil (codec : Codec Label) (label : Label) (round : Nat) (query : Query)
    (state : State Context) (valid : Decoded codec query.handles state) : Update codec label round query [] state state := by
  obtain ⟨atoms, rows, snapshot, decoded⟩ := valid query.satisfactionHandle (by simp [Query.handles])
  obtain ⟨frontAtoms, frontRows, frontRead, frontDecode⟩ := valid query.nextFrontierHandle (by simp [Query.handles])
  have knownRead := CTLUntilRoundPublication.observe_decoded codec (CTLUntilMixedStore.satisfactionView label)
    query.satisfactionHandle state.world.state atoms rows snapshot decoded
  have nextRead := CTLUntilRoundPublication.observe_decoded codec
    (List.filterMap (CTLUntilMixedStore.frontSelect label (round + 1))) query.nextFrontierHandle
    state.world.state frontAtoms frontRows frontRead frontDecode
  exact ⟨_, _, knownRead, nextRead, by simpa [known] using knownRead,
    by simpa [CTLUntilRoundPublication.frontier] using nextRead, by simp⟩

theorem Update.append {codec : Codec Label} {label : Label} {round : Nat} {query : Query}
    {first later : List Nat} {before middle after : State Context}
    (early : Update codec label round query first before middle)
    (late : Update codec label round query later middle after) :
    Update codec label round query (first ++ later) before after := by
  obtain ⟨oldKnown, oldFrontier, oldKnownRead, oldFrontierRead, midKnownRead, midFrontierRead, earlyCount⟩ := early
  obtain ⟨midKnown, midFrontier, actualKnown, actualFrontier, finalKnown, finalFrontier, lateCount⟩ := late
  have sameKnown := Option.some.inj (actualKnown.symm.trans midKnownRead)
  have sameFrontier := Option.some.inj (actualFrontier.symm.trans midFrontierRead)
  subst midKnown
  subst midFrontier
  refine ⟨oldKnown, oldFrontier, oldKnownRead, oldFrontierRead, ?_, ?_, ?_⟩
  · rw [Mettapedia.Machines.CTLUntilCandidateBag.fresh_append_known, ← List.append_assoc]
    exact finalKnown
  · rw [Mettapedia.Machines.CTLUntilCandidateBag.fresh_append_known, ← List.append_assoc]
    exact finalFrontier
  · rw [Mettapedia.Machines.CTLUntilCandidateBag.fresh_append_known, List.length_append]
    omega

theorem leaf_update (codec : Codec Label) (label operand : Label) (round node : Nat) (query : Query)
    (program : SpaceSemantics.Program) (caller : Control) (before after : State Context)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (resolved : Resolved caller) (fixed : Fixed codec label operand round query caller)
    (bound : Bound caller query.names.prior node) (valid : Decoded codec query.handles before)
    (completed : ((GuardedNestedQuerySource.leaf program query.template Context).execute
      caller before context origins pending).stop = .complete after) :
    Update codec label round query [node] before after := by
  obtain ⟨principal, resolved⟩ := resolved
  have readings := fixed principal (resolve_sound resolved)
  have payload := CTLUntilCandidateAdmission.payload_readings codec label round node query.names principal
    readings.1 readings.2.2.2 (bound principal (resolve_sound resolved))
  obtain ⟨receipt⟩ := CTLUntilLeafPublication.completed_refinement codec label round node program query.template
    caller before after context origins pending principal resolved payload.1 payload.2 completed
  obtain ⟨oldKnown, oldFrontier, knownRead, nextRead, knownAfter, nextAfter, _absent⟩ :=
    CTLUntilRoundPublication.leaf_views codec label round node query before after receipt valid
  have decision := CTLUntilRoundPublication.leaf_decision codec label round node query before after receipt valid oldKnown knownRead
  have singleton : fresh [node] oldKnown.toFinset = if receipt.fresh then [node] else [] := by
    rw [decision]
    by_cases held : node ∈ oldKnown <;> simp [Mettapedia.Machines.CTLUntilCandidateBag.fresh_cons, held]
  refine ⟨oldKnown, oldFrontier, knownRead, nextRead, ?_, ?_, ?_⟩
  · rw [singleton]
    exact knownAfter
  · rw [singleton]
    exact nextAfter
  · rw [singleton]
    have count := receipt.count
    cases chosen : receipt.fresh <;> simpa [chosen] using count

theorem Update.observations {codec : Codec Label} {label : Label} {round : Nat} {query : Query}
    {word : List Nat} {before after : State Context}
    (updated : Update codec label round query word before after) (oldKnown oldFrontier : List Nat)
    (knownRead : known codec label query before.world.state = some oldKnown)
    (frontierRead : frontier codec label round query before.world.state = some oldFrontier) :
    known codec label query after.world.state = some (oldKnown ++ fresh word oldKnown.toFinset) ∧
    frontier codec label round query after.world.state = some (oldFrontier ++ fresh word oldKnown.toFinset) ∧
    after.scope.collected.length = before.scope.collected.length + (fresh word oldKnown.toFinset).length := by
  obtain ⟨actualKnown, actualFrontier, actualKnownRead, actualFrontierRead, result⟩ := updated
  cases Option.some.inj (knownRead.symm.trans actualKnownRead)
  cases Option.some.inj (frontierRead.symm.trans actualFrontierRead)
  exact result

/-- The empty next-frontier condition is explicit. Without it the true
source observation is prefix-append, not replacement by the new delta. -/
theorem Update.advance {codec : Codec Label} {label : Label} {round : Nat} {query : Query}
    {before after : State Context} (edges : List (Nat × Nat)) (holds : List Nat)
    (initial : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (updated : Update codec label round query
      (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges holds initial.delta) before after)
    (knownRead : known codec label query before.world.state = some initial.known)
    (frontierEmpty : frontier codec label round query before.world.state = some []) :
    let next := Mettapedia.Machines.CTLUntilCandidateBag.advance edges holds initial
    known codec label query after.world.state = some next.known ∧
    frontier codec label round query after.world.state = some next.delta ∧
    after.scope.collected.length = before.scope.collected.length + next.delta.length := by
  simpa only [Mettapedia.Machines.CTLUntilCandidateBag.advance, List.nil_append] using
    updated.observations initial.known [] knownRead frontierEmpty

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilWordUpdate
