import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedQueryGrowth
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilMixedStore

/-!
# Decoded satisfaction-pair projection of completed query growth

Raw `sat` support becomes the distinct set of `(formula, node)` pairs on a
successfully decoded mixed store. This counts all formula labels. Restricting
the result to one EU output label requires the separate label-stability law.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilQueryGrowth

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open CTLUntilMixedStore (Row render decodeRows)
open FlatQueryRowCodec (Codec)

variable {Label : Type}

def pairs (rows : List (Row Label)) : List (Label × Nat) :=
  rows.filterMap fun row => match row with
    | .satisfaction label node => some (label, node)
    | _ => none

def pairAtom (codec : Codec Label) (pair : Label × Nat) : Atom :=
  render codec (.satisfaction pair.1 pair.2)

theorem pairAtom_injective (codec : Codec Label) : Function.Injective (pairAtom codec) := by
  intro first second equal
  have decoded := congrArg (CTLUntilMixedStore.decode codec) equal
  change CTLUntilMixedStore.decode codec (render codec (.satisfaction first.1 first.2)) =
    CTLUntilMixedStore.decode codec (render codec (.satisfaction second.1 second.2)) at decoded
  rw [CTLUntilMixedStore.decode_render codec (.satisfaction first.1 first.2) trivial,
    CTLUntilMixedStore.decode_render codec (.satisfaction second.1 second.2) trivial] at decoded
  have fields := Row.satisfaction.inj (Option.some.inj decoded)
  exact Prod.ext fields.1 fields.2

theorem filtered_render (codec : Codec Label) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    (rows.map (render codec)).filter GuardedQueryGrowth.isSat = (pairs rows).map (pairAtom codec) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    have tail := ih (fun item member => admitted item (List.mem_cons_of_mem _ member))
    have head := admitted row List.mem_cons_self
    cases row with
    | frontier label round node => simpa [render, GuardedQueryGrowth.isSat, pairs] using tail
    | edge prior next => simpa [render, GuardedQueryGrowth.isSat, pairs] using tail
    | satisfaction label node =>
      simpa [render, GuardedQueryGrowth.isSat, pairs, pairAtom] using
        congrArg (List.cons (render codec (.satisfaction label node))) tail
    | other name children =>
      have notSat : name ≠ "sat" := head.2.2
      simpa [render, GuardedQueryGrowth.isSat, pairs, notSat] using tail

theorem support_card [DecidableEq Label] (codec : Codec Label) (rows : List (Row Label))
    (admitted : ∀ row ∈ rows, row.admitted) :
    (GuardedQueryGrowth.support (rows.map (render codec))).card = (pairs rows).toFinset.card := by
  unfold GuardedQueryGrowth.support
  rw [filtered_render codec rows admitted]
  have mapped : ((pairs rows).map (pairAtom codec)).toFinset = (pairs rows).toFinset.image (pairAtom codec) := by
    ext atom
    simp
  rw [mapped]
  exact Finset.card_image_of_injective _ (pairAtom_injective codec)

theorem decoded_measure [DecidableEq Label] (codec : Codec Label) (state : Effects.State)
    (handle : NamedSpaces.Handle) (atoms : List Atom) (rows : List (Row Label))
    (snapshot : state.read handle = some atoms) (decoded : decodeRows codec atoms = some rows) :
    GuardedQueryGrowth.measure handle state = (pairs rows).toFinset.card := by
  obtain ⟨actual, admitted⟩ := CTLUntilMixedStore.decode_rows_sound codec atoms rows decoded
  unfold GuardedQueryGrowth.measure
  rw [snapshot]
  simp only [Option.getD_some]
  rw [← actual]
  exact support_card codec rows admitted

/-- On decoded initial/final stores, the actual completed nested worker's
local packet count is the growth in distinct typed satisfaction pairs.
This does not infer successful completion from a zero packet count. -/
theorem completed_pair_count {Context : Type} [DecidableEq Label] (codec : Codec Label)
    (program : SpaceSemantics.Program) (template : GuardedNestedQuerySource.Template)
    (fields : List Atom) (frontierCode : template.body.secondCode = .expression (.symbol "fr" :: fields))
    (legs : List NestedQuerySource.Leg) (caller : EagerDFS.Destination.Control)
    (before after : NamedGuardedCandidateBatch.State Context) (context : Context) (origins : List Nat)
    (pending : List (EagerDFS.Destination.CollectionWork Context))
    (initialAtoms finalAtoms : List Atom) (initialRows finalRows : List (Row Label))
    (initialRead : before.world.state.read template.satisfactionHandle = some initialAtoms)
    (initialDecode : decodeRows codec initialAtoms = some initialRows)
    (finalRead : after.world.state.read template.satisfactionHandle = some finalAtoms)
    (finalDecode : decodeRows codec finalAtoms = some finalRows)
    (empty : before.scope.collected = [])
    (completed : (ScopedNestedQueryExecution.run program (GuardedNestedQuerySource.leaf program template Context)
      legs caller before context origins pending).stop = .complete after) :
    (pairs finalRows).toFinset.card = (pairs initialRows).toFinset.card + after.scope.collected.length := by
  have growth := GuardedQueryGrowth.nested_packet_count program template fields frontierCode legs caller before
    context origins pending after empty completed
  rw [decoded_measure codec before.world.state _ initialAtoms initialRows initialRead initialDecode,
    decoded_measure codec after.world.state _ finalAtoms finalRows finalRead finalDecode] at growth
  exact growth

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilQueryGrowth
