import Mettapedia.Machines.ReadOnlySpecialization
import Mettapedia.GSLT.Dynamics.CacheCoherence

/-!
# Validating specialization over a publication history

A specialization retains its ordered, adaptive read transcript. Each
publication must preserve readings whose supporting counters stay fixed.
The retained code can then run from the current state with the same
answer and reads as the original query.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Specialization

open ReadOnlyQuery (Program run Agrees)
open ReadOnlySpecialization (Residual drive drive_agrees observeSuffix)
open Mettapedia.GSLT.Dynamics.CacheCoherence (Notifies execute)

universe u v w x y
variable {State : Type u} {Action : Type v} {Key : Type w} {Value : Type x} {Answer : Type y}

section Versioned

variable {publish : State → Action → State} {invariant : State → Prop}
  {version : State → Key → Nat} {view : State → Key → Value}
  (history : Notifies publish invariant version view) {initial : State} (started : invariant initial)
  (edits : List Action) (static : Key → Bool) (fuel : Nat) (source : Program Key Value Answer)

include history started in
theorem valid_after_publications
    (retained : ∀ receipt ∈ (drive static (view initial) fuel source).reads,
      version (execute publish initial edits) receipt.1 = version initial receipt.1) :
    Agrees (view (execute publish initial edits)) (drive static (view initial) fuel source).reads := by
  intro receipt member
  exact (history.observe_execute_of_counter_eq started edits receipt.1 (retained receipt member)).trans
    (drive_agrees static (view initial) fuel source receipt member)

include history started in
theorem reuse_after_publications
    (retained : ∀ receipt ∈ (drive static (view initial) fuel source).reads,
      version (execute publish initial edits) receipt.1 = version initial receipt.1) :
    let residual := drive static (view initial) fuel source
    let current := view (execute publish initial edits)
    observeSuffix residual.reads residual.suffix current = run current source :=
  (drive static (view initial) fuel source).exactOn _
    (valid_after_publications history started edits static fuel source retained)

end Versioned

namespace Controls

private structure Reading where
  revision : Nat
  unrelated : Nat
  rows : List Nat

private def observed (space : Reading) (_ : Unit) : List Nat := space.rows
private def stamp (space : Reading) (_ : Unit) : Nat := space.revision
private def write (space : Reading) : Bool → Reading
  | false => {space with unrelated := space.unrelated + 1}
  | true => {space with revision := space.revision + 1, rows := space.rows.drop 1}

private def valid (space : Reading) : Prop := ∀ n ∈ space.rows, n = 7

private theorem notices : Notifies write valid stamp observed where
  preserves space edit admitted := by
    cases edit with
    | false => exact admitted
    | true => intro value present; exact admitted value (List.drop_subset _ _ present)
  monotone space edit key := by cases edit <;> simp [write, stamp]
  notifies space edit key _ same := by
    cases edit with
    | false => rfl
    | true => simp [write, stamp] at same

private def query : Program Unit (List Nat) (List Nat) := .read () .pure
private def old : Reading := ⟨0, 0, [7, 7]⟩
private theorem old_valid : valid old := by simp [valid, old]

theorem unrelated_update_reuses_both_occurrences :
    let residual := drive (fun _ => true) (observed old) 1 query
    observeSuffix residual.reads residual.suffix (observed (execute write old [false])) =
      run (observed (execute write old [false])) query ∧
    (run (observed (execute write old [false])) query).answer = [7, 7] := by
  refine ⟨reuse_after_publications notices old_valid [false] (fun _ => true) 1 query ?_, rfl⟩
  intro receipt member
  rfl

theorem deletion_of_equal_occurrence_expires_cached_read :
    stamp (execute write old [true]) () ≠ stamp old () ∧
    (run (observed (execute write old [true])) query).answer = [7] := by decide +kernel

end Controls

end Mettapedia.Machines.Specialization
