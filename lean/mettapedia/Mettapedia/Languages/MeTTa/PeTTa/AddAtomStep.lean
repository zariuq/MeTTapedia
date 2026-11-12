import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaStoreSelection
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingSpec
import Mettapedia.Languages.MeTTa.PeTTa.StdLibCalls

/-!
# `add-atom` of the PeTTa machine is an append of the ordered-store step

The store requests of the unifying PeTTa machine are `add-atom`, `remove-atom` and `match`.
Removal and a written `match` are already tied to the ordered-store step of the calculus
for an actual machine transition (`ContextualTransform.PeTTaSelectionCursor`,
`ContextualTransform.PeTTaQueryInterpretation`). The append was tied only to a list
function. This module ties it to the machine's transition.

* `add_atom_transition`: when the space of an `add-atom` resolves to a handle and the atom
  can be inserted there, the machine takes the step that stores the atom and answers
  `true`; `add_atom_transition_unique`: it takes no other step from that configuration.
* `add_atom_is_append`: with the space's rows represented by distinct occurrences and a
  fresh occurrence labelled with the atom, that machine step is an admitted firing of
  `OrderedStore.step` that makes the occurrence: the step's rows after it are the old rows
  followed by the new one, and they represent the rows the machine wrote.

Negative example: `add_atom_needs_a_space` (when the location is not a space the machine
takes no such step: the insertion has no result).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AddAtomStep

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open Unifying (resolve)

/-- **The machine's `add-atom` step.** -/
theorem add_atom_transition (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat)
    (location atom : Atom) (handle : NamedSpaces.Handle) (after : Effects.State)
    (control : source.control =
      .arguments bindings (.function "add-atom") [] [location, atom] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (inserted : Effects.insert source.state handle (resolve bindings atom) = some after) :
    Unifying.Transition registry source
      { source with
        state := after
        control := .returned [⟨Effects.boolean true, bindings⟩]
        uses := source.uses } := by
  have step := Unifying.Transition.primitive (registry := registry) (source := source)
    (bindings := bindings) (head := "add-atom") (index := index) (held := [location, atom])
    (answers := [Effects.boolean true]) (after := after) control (by decide) (by decide)
    (by decide) (by decide)
    (by simp [Unifying.primitiveInputs, resolved, inserted])
  simpa [Unifying.primitiveOutputs, Unifying.primitiveUses, Unifying.primitiveCopies] using step

/-- The machine is deterministic: from that configuration it takes no other step. -/
theorem add_atom_transition_unique (registry : SpaceSemantics.Program)
    (source target : Unifying.Configuration) (bindings : Subst) (index : Nat)
    (location atom : Atom) (handle : NamedSpaces.Handle) (after : Effects.State)
    (control : source.control =
      .arguments bindings (.function "add-atom") [] [location, atom] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (inserted : Effects.insert source.state handle (resolve bindings atom) = some after)
    (step : Unifying.Transition registry source target) :
    target =
      { source with
        state := after
        control := .returned [⟨Effects.boolean true, bindings⟩]
        uses := source.uses } := by
  have mine := (Unifying.step_iff_transition registry source _).mpr
    (add_atom_transition registry source bindings index location atom handle after control
      resolved inserted)
  have theirs := (Unifying.step_iff_transition registry source target).mpr step
  rw [mine] at theirs
  exact (Option.some.inj theirs).symm

variable {O : Type} [DecidableEq O] (label : O → Atom)

/-- The request that makes one occurrence and touches nothing else. -/
def addRequest (fresh : O) : OrderedStore.Publication Atom O := ⟨⟨[], [], [fresh]⟩, []⟩

/-- It is admitted exactly as an append is: distinct rows, a fresh occurrence, consistent
knowledge. -/
theorem addRequest_admitted (knowledge : EquationStore Atom) (ids : List O) (fresh : O)
    (unique : ids.Nodup) (isFresh : fresh ∉ ids)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, ids))
      (addRequest fresh) := by
  refine ⟨⟨unique, List.nodup_nil, List.nodup_singleton fresh⟩, ?_, consistent⟩
  refine ⟨by simp [addRequest, OrderedStore.Publication.commit, Selection.commit],
    by simp [addRequest, OrderedStore.Publication.commit, Selection.commit],
    by simp [addRequest, OrderedStore.Publication.commit, Selection.commit],
    by simpa [addRequest, OrderedStore.Publication.commit, Selection.commit] using isFresh, ?_⟩
  intro query member
  simp [addRequest, OrderedStore.Publication.commit] at member

/-- **An `add-atom` step of the machine is an admitted append of the ordered-store step.**
The space's rows are the labels of the distinct occurrences `ids`; `fresh` is an occurrence
outside them labelled with the atom to add. Then the machine takes its `add-atom` step,
the ordered-store step admits the request that makes `fresh`, the step's rows after it are
`ids ++ [fresh]`, and their labels are the rows the machine wrote to the space. -/
theorem add_atom_is_append (registry : SpaceSemantics.Program)
    (source : Unifying.Configuration) (bindings : Subst) (index : Nat)
    (location atom : Atom) (handle : NamedSpaces.Handle) (ids : List O) (fresh : O)
    (control : source.control =
      .arguments bindings (.function "add-atom") [] [location, atom] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (opened : source.state.read handle = some (ids.map label))
    (unique : ids.Nodup) (isFresh : fresh ∉ ids)
    (labelled : label fresh = resolve bindings atom)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∃ after : Effects.State,
      Unifying.Transition registry source
        { source with
          state := after
          control := .returned [⟨Effects.boolean true, bindings⟩]
          uses := source.uses } ∧
      after.read handle = some ((ids ++ [fresh]).map label) ∧
      ∃ admitted : (OrderedStore.step atomFrames PUnit.unit label).Admits
          (s := (knowledge, ids)) (addRequest fresh),
        (OrderedStore.step atomFrames PUnit.unit label).result (addRequest fresh) admitted =
          (knowledge, ids ++ [fresh]) := by
  obtain ⟨after, written⟩ :=
    NamedSpaces.Store.write_exists_of_read_some source.state handle (ids.map label)
      (ids.map label ++ [resolve bindings atom]) opened
  have inserted : Effects.insert source.state handle (resolve bindings atom) = some after := by
    simp [Effects.insert, opened, written]
  obtain ⟨before, wasOpen, nowOpen⟩ := Effects.insert_reads_back inserted
  have sameRows : before = ids.map label := by
    rw [opened] at wasOpen
    exact (Option.some.inj wasOpen).symm
  have admitted := addRequest_admitted label knowledge ids fresh unique isFresh consistent
  refine ⟨after,
    add_atom_transition registry source bindings index location atom handle after control
      resolved inserted, ?_, admitted, ?_⟩
  · rw [nowOpen, sameRows, List.map_append, List.map_singleton, labelled]
  · refine Prod.ext rfl ?_
    show ((OrderedStore.step atomFrames PUnit.unit label).result (addRequest fresh) admitted).2 =
      ids ++ [fresh]
    rw [OrderedStore.result_rows]
    exact OrderedStore.append_only ids [fresh]

/-- Where the location is not a space, the insertion has no result, so the hypotheses of
`add_atom_transition` cannot be met. -/
theorem add_atom_needs_a_space : Effects.readHandle (.symbol "nowhere") = none := rfl

end Mettapedia.Languages.MeTTa.PeTTa.AddAtomStep
