import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.PacketResultReadouts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Concurrency.NativePacketRoundsControls

/-!
# Produced readings in an actual generative family

The two native firings independently open the same schema, retain its nonempty latent information,
and share symbolic captures. Both actual output ports return the false literal. A different literal
is refused at those ports. Empty residual-family data does not supply a model of global knowledge.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultReadouts.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidualExample (tiny bit)
open FamilyInformationControls (target valuation captured)
open NativePacketRoundsControls (state members reader open_models open_clear)
open NativeClosedReadings

def bitPattern (value : Bool) : ClosedTerm tiny [] () := bit (closedArity tiny) value

noncomputable def openData : FamilyInformation.SolutionData (state false) (members false) target where
  shared := captured
  member index := if index.val = 0 then valuation false else valuation true
  agrees index := by
    fin_cases index
    · exact FamilyInformationControls.valuation_agrees false
    · exact FamilyInformationControls.valuation_agrees true
  models index := by
    fin_cases index
    · exact open_models 0 false
    · exact open_models 1 true

theorem actual_native_present {last : NativeState tiny Nat ([] : Ctx tiny) ()}
    (witness : NativeRoundExecution.Witness (state false) (members false) last) :
    last.state.present = {0,1,7} := by
  rw [NativeConcurrent.sequential_present witness.sequential]
  ext occurrence
  simp [members,state,reader,MeTTaCalculus.OccurrenceCommits.fireList,
    MeTTaCalculus.OccurrenceCommits.fire,Selection.commit,or_comm,or_assoc]

theorem packet_outputs_false {last : NativeState tiny Nat ([] : Ctx tiny) ()}
    (witness : NativeRoundExecution.Witness (state false) (members false) last) :
    PacketReads (members false) 0 (bitPattern false) ∧
      PacketReads (members false) 1 (bitPattern false) := by
  have enabled (index : Fin (members false).length) :=
    ((native_admits_iff (members false)[index].toNative).mp
      (open_clear.admitted (members false)[index] (List.getElem_mem ..))).2.1
  have output (index : Fin (members false).length) (occurrence : Nat)
      (made : occurrence ∈ (members false)[index].selection.made)
      (present : occurrence ∈ last.state.present) :
      PacketReads (members false) occurrence (bitPattern false) := by
    refine ⟨(packetFinal_present_inl witness occurrence).mpr present,
      NativePacketRounds.fitData openData,?_,?_⟩
    · rw [packetFinal_equations]
      exact NativePacketRounds.fitData_joint openData (by simp [members]) enabled
    · rw [label_produced open_clear index occurrence made]
      apply (fitData_base_output_iff openData index (bitPattern false) occurrence).mpr
      fin_cases index <;> rfl
  have present := actual_native_present witness
  constructor
  · exact output ⟨0,by decide⟩ 0 (by simp [members,reader]) (by simp [present])
  · exact output ⟨1,by decide⟩ 1 (by simp [members,reader]) (by simp [present])

theorem different_produced_literal_refused :
    ¬ PacketReads (members false) 0 (bitPattern true) := by
  rintro ⟨_,substitution,model,seen⟩
  have fullModel : (NativePacketStep.packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ())).Models
      substitution (NativePacketRounds.jointProblem (members false)) := by
    rwa [packetFinal_equations] at model
  let index : Fin (members false).length := ⟨0,by decide⟩
  rw [label_produced open_clear index 0 (by simp [members,reader,index])] at seen
  have output := (base_output_iff (members false) index substitution fullModel (bitPattern true) 0).mp seen
  change bit _ true = bit _ false at output
  cases output

theorem tied_latent_information_refuses_every_result (occurrence : Nat) (pattern : ClosedTerm tiny [] ()) :
    ¬ PacketReads (members true) occurrence pattern := by
  rintro ⟨_,substitution,model,_⟩
  have fullModel : (NativePacketStep.packetAction (S := tiny) (O := Nat) (Γ := []) (sort := ())).Models
      substitution (NativePacketRounds.jointProblem (members true)) := by
    rwa [packetFinal_equations] at model
  have admitted (index : Fin (members true).length) : (members true)[index].toNative.Realized := by
    fin_cases index
    · exact NativePacketRoundsControls.tied_realized 0 false (by decide)
    · exact NativePacketRoundsControls.tied_realized 1 true (by decide)
  have enabled (index : Fin (members true).length) :=
    ((native_admits_iff (members true)[index].toNative).mp (admitted index)).2.1
  exact NativePacketRoundsControls.tied_not_jointly
    ((NativePacketRounds.consistent_iff_jointly (members true) (by simp [members]) enabled).mp
      ⟨substitution,fullModel⟩)

theorem actual_generative_result :
    ∃ last, ∃ witness : NativeRoundExecution.Witness (state false) (members false) last,
      witness.toRun.word.length = 2 ∧ Reads last 0 (bitPattern false) ∧ Reads last 1 (bitPattern false) ∧
        ¬ Reads last 0 (bitPattern true) := by
  obtain ⟨last,witness,_,count,_⟩ :=
    NativePacketRoundsControls.actual_native_every_order (List.Perm.refl (members false))
  have outputs := packet_outputs_false witness
  refine ⟨last,witness,count,?_,?_,?_⟩
  · exact (packet_result_reads_iff (members false) (by simp [members]) open_clear witness 0 (bitPattern false)).mp outputs.1
  · exact (packet_result_reads_iff (members false) (by simp [members]) open_clear witness 1 (bitPattern false)).mp outputs.2
  · exact fun seen => different_produced_literal_refused
      ((packet_result_reads_iff (members false) (by simp [members]) open_clear witness 0 (bitPattern true)).mpr seen)

noncomputable def emptyDeadData : FamilyInformation.SolutionData FamilyInformationControls.dead [] target :=
  PacketResultModels.emptyData FamilyInformationControls.dead target captured

theorem empty_tail_does_not_discharge_knowledge :
    ¬ ContextualResidual.Models emptyDeadData.shared FamilyInformationControls.dead.state.equations := by
  intro known
  exact FamilyInformationControls.dead_knowledge_unsolvable ⟨target,emptyDeadData.shared,known⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.PacketResultReadouts.Controls
