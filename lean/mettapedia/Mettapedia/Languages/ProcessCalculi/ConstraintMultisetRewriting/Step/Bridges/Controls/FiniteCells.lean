import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.FiniteCells
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.CellFibres

/-!
# Checked finite packets: aliases, invalid indices and actual results

An encoded proposal drives the actual addition step. An invalid table ordinal,
a wrong output length, conflicting aliases and a wrong proposed sum have
different causes. Rejecting one proposal does not mean that the state has no
admitted transition. Infinitely many raw proposals can share one finite packet.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.FiniteCells

open Mettapedia.Machines.TIsa Cells CellEffects Control
open Kernel.CellOccurrences Kernel.CellProposals
open Kernel.CheckedCells.Controls (edge keys initial proposal badProposal)
open Kernel.CellCorrespondence.Controls (state firing admitted)
open Bridges.FiniteCells

theorem reads_finite_packet : packet? [edge] 0 [14#64] = some (outputCode firing) := by
  exact packet_outputCode firing

theorem packet_runs_actual_addition :
    fire? [edge] state (outputCode firing) = some (result state firing) :=
  fire_complete [edge] state firing admitted

theorem actual_delivered_words :
    (result state firing).values (.inl 0) = (8#64) ∧
      (result state firing).values (.inr 0) = (14#64) ∧
      (result state firing).values (.inr 1) = (7#64) := ⟨rfl, rfl, rfl⟩

theorem out_of_range_is_not_wrapped : packet? [edge] 1 [14#64] = none := rfl
theorem missing_word_is_not_padded : packet? [edge] 0 [] = none := rfl
theorem extra_word_is_not_ignored : packet? [edge] 0 [14#64, 99#64] = none := rfl

def aliasedEdge : Edge Nat := {edge with effect := {edge.effect with outputs := [0, 0]}}
def conflicting : OutputCode [aliasedEdge] := ⟨⟨0, by decide⟩, fun index => if index.val = 0 then 14 else 15⟩
def agreeing : OutputCode [aliasedEdge] := ⟨⟨0, by decide⟩, fun _ => 14⟩

theorem conflicting_aliases_refused : decode? conflicting = none := rfl

theorem agreeing_aliases_decoded :
    decode? agreeing = some (Kernel.CellProposals.normalize (unpack agreeing)) := by
  have coherent : outputCode (unpack agreeing) = agreeing := by
    apply congrArg (Sigma.mk agreeing.1)
    funext index
    fin_cases index <;> rfl
  exact if_pos coherent

def wrong : OutputCode [edge] := ⟨⟨0, by decide⟩, fun _ => 15⟩

theorem one_bad_proposal_does_not_mean_stuck :
    fire? [edge] state wrong = none ∧
      ∃ after, LogicOverTheStep.StepSpan.Succ (step [edge]) state after :=
  by
    constructor
    · have coherent : outputCode (unpack wrong) = wrong := by
        apply congrArg (Sigma.mk wrong.1)
        funext index
        fin_cases index
        rfl
      rw [fire?, decode?, if_pos coherent]
      have refused : ¬ CheckedAdmission.eligible (unpack wrong).edge state.keys state.values
          (Kernel.CellProposals.normalize (unpack wrong)).candidate := by decide
      exact if_neg refused
    · exact ⟨result state firing, firing, admitted, rfl⟩

theorem same_packet_for_raw_family (first second : Nat) :
    outputCode (Kernel.CellFibres.family first) = outputCode (Kernel.CellFibres.family second) :=
  (normalize_eq_iff_code_eq _ _).mp (Kernel.CellFibres.canonical_family_equal first second)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.FiniteCells

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.FiniteCells.packet_runs_actual_addition
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.FiniteCells.conflicting_aliases_refused
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Controls.FiniteCells.one_bad_proposal_does_not_mean_stuck
