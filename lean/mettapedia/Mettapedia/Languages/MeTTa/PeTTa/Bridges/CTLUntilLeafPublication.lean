import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedNestedQuerySource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilPublicationSource

/-!
# Typed refinement of actual completed guarded leaves

Closed readings of the reached caller determine both published rows. The
actual membership test selects held/fresh, and actual insertion receipts
derive the final store and its decoding. No final decoder or predicted
post-state is assumed. Target aliasing and old occurrences are preserved.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open CTLUntilMixedStore (Row render decodeRows)

variable {Context Label : Type}

structure Refinement (codec : Codec Label) (label : Label) (round node : Nat)
    (template : GuardedNestedQuerySource.Template) (before after : State Context) where
  fresh : Bool
  guardRows : List Atom
  snapshot : before.world.state.read template.satisfactionHandle = some guardRows
  decision : fresh = !decide (render codec (.satisfaction label node) ∈ guardRows)
  count : after.scope.collected.length = before.scope.collected.length + if fresh then 1 else 0
  reads : ∀ observed, after.world.state.read observed = (before.world.state.read observed).map
    (fun atoms => atoms ++ (if fresh then CTLUntilPublicationSource.additions label round node
      template.satisfactionHandle template.body.secondHandle observed else []).map (render codec))

/-- The two typed readings are preconditions on the original caller's
actual principal solution, not assumptions about the guard's future frame. -/
theorem completed_refinement (codec : Codec Label) (label : Label) (round node : Nat)
    (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (caller : Control) (before after : State Context) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (principal : Environment)
    (resolved : resolve caller.bindings = some principal)
    (firstRead : read principal template.body.firstCode = render codec (.satisfaction label node))
    (secondRead : read principal template.body.secondCode = render codec (.frontier label (round + 1) node))
    (completed : (GuardedNestedQuerySource.invoke program template caller before context origins pending).execution.stop = .complete after) :
    Nonempty (Refinement codec label round node template before after) := by
  obtain ⟨actualPrincipal, request, advance, actualResolved, requested, advanced, rfl⟩ :=
    GuardedNestedQuerySource.completed_origin program template caller before context origins pending after completed
  have same := Option.some.inj (actualResolved.symm.trans resolved)
  subst actualPrincipal
  have fields := CapturedQueryOperands.request_fields _ _ _ request requested
  have pattern := fields.2.1.trans firstRead
  have published := NamedGuardedCandidateExecution.execute_publication
    ((template.candidate caller context origins request).input program before pending) template.body advance advanced
  cases published with
  | held rows snapshot present copied unchanged noPacket =>
    change advance.state = before.world.state at unchanged
    change before.world.state.read request.handle = some rows at snapshot
    rw [fields.1] at snapshot
    change request.pattern ∈ rows at present
    rw [pattern] at present
    refine ⟨{
      fresh := false, guardRows := rows, snapshot,
      decision := by simp [present]
      count := by simp [State.advance, noPacket]
      reads := ?_ }⟩
    intro observed
    change advance.state.read observed = (before.world.state.read observed).map (fun atoms => atoms ++ [])
    rw [unchanged]
    simp
  | fresh guard evidence rows middle snapshot absent first second allocator packet =>
    have inherited : Solves evidence.principal caller.bindings :=
      NamedGuardedInsertionAdmission.after_guard_inherited guard evidence.principal (resolve_sound evidence.resolved)
    have secondValue : evidence.secondValue = render codec (.frontier label (round + 1) node) :=
      evidence.secondRead.symm.trans
        (CapturedQueryOperands.resolved_forces resolved template.body.secondCode _ secondRead
          (LiteralQuerySource.read_literal _ (CTLUntilPublicationSource.frontier_literal codec label (round + 1) node))
          evidence.principal inherited)
    change before.world.state.read request.handle = some rows at snapshot
    change request.pattern ∉ rows at absent
    change Effects.insert before.world.state request.handle request.pattern = some middle at first
    change Effects.insert middle template.body.secondHandle evidence.secondValue = some advance.state at second
    rw [fields.1] at snapshot first
    rw [pattern] at absent first
    rw [secondValue] at second
    refine ⟨{
      fresh := true, guardRows := rows, snapshot,
      decision := by simp [absent]
      count := by simp [State.advance, packet]
      reads := ?_ }⟩
    intro observed
    exact CTLUntilPublicationSource.raw_after_writes codec label round node before.world.state middle advance.state
      template.satisfactionHandle template.body.secondHandle observed first second

/-- Decoding preservation follows from the actual typed append, including
when satisfaction and frontier targets are the same handle. -/
theorem Refinement.decoded_after {codec : Codec Label} {label : Label} {round node : Nat}
    {template : GuardedNestedQuerySource.Template} {before after : State Context}
    (receipt : Refinement codec label round node template before after)
    (observed : NamedSpaces.Handle) (atoms : List Atom) (rows : List (Row Label))
    (snapshot : before.world.state.read observed = some atoms) (decoded : decodeRows codec atoms = some rows) :
    let additions := if receipt.fresh then CTLUntilPublicationSource.additions label round node
      template.satisfactionHandle template.body.secondHandle observed else []
    after.world.state.read observed = some ((rows ++ additions).map (render codec)) ∧
      decodeRows codec ((rows ++ additions).map (render codec)) = some (rows ++ additions) := by
  dsimp only
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  constructor
  · rw [receipt.reads, snapshot]
    simp only [Option.map_some, ← actual, List.map_append]
  · apply CTLUntilMixedStore.decode_rows_complete
    intro row member
    rcases List.mem_append.mp member with old | added
    · exact admitted row old
    · split at added
      · exact CTLUntilPublicationSource.additions_admitted label round node _ _ _ row added
      · cases added

/-- A live query view is unchanged when neither possible publication can
match it. This retains physical row positions and arbitrary captured callers,
and also preserves missing handles or a refused capture as such. -/
theorem Refinement.capture_preserved {codec : Codec Label} {label : Label} {round node : Nat}
    {template : GuardedNestedQuerySource.Template} {before after : State Context}
    (receipt : Refinement codec label round node template before after)
    (observed : NamedSpaces.Handle) (caller : Control) (pattern body destination : Atom)
    (older : List Goal) (offset : Nat)
    (unmatched : ∀ atom ∈ (CTLUntilMixedCapture.publication label round node).map (render codec),
      SpaceSemantics.matchValue [] pattern atom = none) :
    (after.world.state.read observed).bind (ScopedQuerySource.capture caller pattern body destination older offset) =
      (before.world.state.read observed).bind (ScopedQuerySource.capture caller pattern body destination older offset) := by
  rw [receipt.reads]
  cases before.world.state.read observed with
  | none => rfl
  | some atoms =>
    simp only [Option.map_some, Option.bind_some]
    apply ScopedQueryScanStability.capture_append_unmatched
    intro atom member
    split at member
    · exact unmatched atom (CTLUntilPublicationSource.additions_in_publication codec label round node
        template.satisfactionHandle template.body.secondHandle observed atom member)
    · simp at member

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLeafPublication
