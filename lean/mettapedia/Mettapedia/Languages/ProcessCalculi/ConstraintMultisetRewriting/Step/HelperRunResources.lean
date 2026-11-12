import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HelperRebaseDomain

/-! # Exact resource accounts of complete helper runs -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs

variable {S : Signature} {O : Type} [DecidableEq O]

def outputs {source : State S O} (run : helperStep.Run source) : Finset O :=
  (run.word.map (fun entry => entry.2.made)).toFinset

theorem outputs_cons {source : State S O} (f : Firing source) (allowed : helperStep.Admits f)
    (rest : helperStep.Run f.after) : outputs (.cons f allowed rest) = insert f.made (outputs rest) := by
  simp only [outputs, Step.Run.word, List.map_cons, List.toFinset_cons]

theorem outputsAvoid_iff_disjoint {source : State S O} (run : helperStep.Run source) (context : Finset O) :
    OutputsAvoid run context ↔ Disjoint (outputs run) context := by
  constructor
  · intro avoids
    apply Finset.disjoint_left.mpr
    intro occurrence member inContext
    obtain ⟨entry, inWord, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    subst occurrence
    exact avoids entry inWord inContext
  · intro apart entry inWord
    exact Finset.disjoint_left.mp apart
      (List.mem_toFinset.mpr (List.mem_map.mpr ⟨entry, inWord, rfl⟩))

theorem present_last : ∀ {source : State S O} (run : helperStep.Run source),
    run.last.present = source.present ∪ outputs run
  | _, .nil _ => by simp [Step.Run.last, outputs, Step.Run.word]
  | source, .cons f allowed rest => by
      rw [Step.Run.last, present_last rest, outputs_cons]
      change MeTTaCalculus.OccurrenceCommits.fire source.present (f.selection.commit (T := Unit)) ∪ outputs rest = _
      simp [Helpers.Firing.selection, Selection.commit, MeTTaCalculus.OccurrenceCommits.fire]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Helpers
