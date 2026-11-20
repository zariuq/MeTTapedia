import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellCorrespondence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin

/-!
# The received HOL admission/run theory on checked cell firings

The actual cell occurrence effect instantiates the existing interpretation of
received HOL definitions. Complete source words correspond to event paths,
including the chosen edge ordinal and its preparation. Finite reachable cell
observations therefore agree with the executable checked-admission relation.

The HOL input here is the checked general admission/run history. It is not
the separate `nat_step` record handler theory; connecting that concrete theory
requires its record decoding and recipe implementation correspondence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellHOL

open Mettapedia.Machines.TIsa Cells Control
open Mettapedia.Languages.HOLLight Mettapedia.Languages.OpenTheory
open CellOccurrences

universe u
variable {Key : Type u} [DecidableEq Key]

variable (edges : List (Edge Key)) (input : HOLRunAdmissionJoin.Input)
  (other : TypeFamilySemantics.OperatorFamilies.{u})
  (prior : TypeFamilySemantics.Assignment.{u})

noncomputable def Loaded (word : List (HOLPreparedRunEncoding.RawEvent (effect edges)))
    (before after : State Key) : Prop :=
  (input.operations.signature.pathValue (input.model (effect edges) other prior)
    (input.admittedValue (effect edges) other prior (step edges).eventAdmission)
    (HOLRunSpecialization.wordValue (effect edges) _ _ (input.runCoding (effect edges) other prior)
      (input.runAgreement (effect edges) other prior) word)
    ((input.runCoding (effect edges) other prior).states.symm (some before))
    ((input.runCoding (effect edges) other prior).states.symm (some after))).down

theorem loaded_word_iff (word : List (HOLPreparedRunEncoding.RawEvent (effect edges)))
    (before after : State Key) :
    Loaded edges input other prior word before after ↔
      ∃ path : @Quiver.Path (EffectCore.EventObject (effect edges) (step edges).eventAdmission) _ before after,
        HOLPreparedRunEncoding.word (effect edges) (step edges).eventAdmission path = word :=
  input.admitted_path_iff (effect edges) other prior (step edges).eventAdmission word before after

theorem loaded_reachable_iff_run (post : State Key → Prop) (before : State Key) :
    (∃ word after, Loaded edges input other prior word before after ∧ post after) ↔
      ∃ run : (step edges).Run before, post run.last := by
  constructor
  · rintro ⟨word, after, loaded, observed⟩
    obtain ⟨path, _⟩ := (loaded_word_iff edges input other prior word before after).mp loaded
    let run := (step edges).runOfEventPath path
    exact ⟨run.val, run.property.symm ▸ observed⟩
  · rintro ⟨run, observed⟩
    let path := run.eventPath (step edges)
    exact ⟨HOLPreparedRunEncoding.word (effect edges) (step edges).eventAdmission path,
      run.last, (loaded_word_iff edges input other prior _ before run.last).mpr ⟨path, rfl⟩, observed⟩

/-- This composes a received source-model interpretation with the concrete
checked cell implementation, at the exact finite region observation. -/
theorem loaded_reachable_iff_checked (keys : Finset (Location Key))
    (before : Location Key → Word) (generations : Location Key → Nat)
    (post : Multiset (Cell (Location Key)) → Prop) :
    (∃ word after, Loaded edges input other prior word ⟨keys, before, generations⟩ after ∧
      post (encode after.keys after.values)) ↔
      ∃ after, (CheckedCells.source edges keys).MultiStep before after ∧ post (encode keys after) := by
  exact (loaded_reachable_iff_run edges input other prior
    (fun state => post (encode state.keys state.values)) ⟨keys, before, generations⟩).trans
    (CellCorrespondence.reachable_iff_actual_run edges keys post before generations).symm

#print axioms loaded_word_iff
#print axioms loaded_reachable_iff_run
#print axioms loaded_reachable_iff_checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.CellHOL
