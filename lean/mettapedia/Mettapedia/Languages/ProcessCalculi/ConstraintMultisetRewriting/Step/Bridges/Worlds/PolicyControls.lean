import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Unique
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.Clashes

/-!
# Enlarging a visible rule set can remove unique and every commits

The existing one-token state admits the existing consume rule uniquely.
Adding the existing copy rule changes no row, frame or knowledge. Both the
reader and taker are individually admitted, with distinct match keys, so
the enlarged program admits no unique bag. Their common read/take occurrence
also prevents an every bag. The original one-match firing still works.
Thus widening a world's visible program needs its own policy licence;
adding a world while keeping the space fixed is a different operation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.PolicyControls

open RuleSyntax RuleSyntax.JointFirings
open RuleSyntax.Examples (Tm X E)

abbrev originalProgram : Program Tm := EveryControls.tokens
abbrev extendedProgram : Program Tm := ReadTake.program
abbrev tokenState : State Tm Nat := ReadTake.one

def uniqueMove (program : Program Tm) (before after : State Tm Nat) : Prop :=
  ∃ firing : JointFirings.Bag Nat E program before.frame,
    firing.AdmitsUnique X before program ∧ firing.result X before = after

def everyMove (program : Program Tm) (before after : State Tm Nat) : Prop :=
  ∃ firing : JointFirings.Bag Nat E program before.frame,
    firing.AdmitsEvery X before program ∧ firing.result X before = after

theorem program_extension : originalProgram ⊆ extendedProgram := by
  intro rule member
  have same : rule = RuleSyntax.Examples.consume := member
  subst rule
  exact Or.inr rfl

theorem original_unique :
    uniqueMove originalProgram tokenState (MaximalControls.lone.result X tokenState) :=
  ⟨MaximalControls.lone, Neighbour.lone_unique, rfl⟩

theorem original_result : (MaximalControls.lone.result X tokenState).present = {10} := by
  decide

theorem original_every :
    everyMove originalProgram tokenState (MaximalControls.lone.result X tokenState) :=
  ⟨MaximalControls.lone, Neighbour.lone_every, rfl⟩

theorem extended_matches_distinct :
    firingKey ReadTake.reader.firing ≠ firingKey ReadTake.taker.firing := by
  intro same
  have taken := congrArg (fun key : Rule Tm × List Nat × List Nat => key.2.1) same
  have different : ([] : List Nat) ≠ [0] := by decide
  exact different taken

theorem actual_competing_matches :
    ReadTake.reader.firing.Admits X tokenState ∧
      ReadTake.taker.firing.Admits X tokenState ∧
      firingKey ReadTake.reader.firing ≠ firingKey ReadTake.taker.firing :=
  ⟨ReadTake.reader_admitted, ReadTake.taker_admitted, extended_matches_distinct⟩

theorem extended_no_unique_bag :
    ¬ ∃ firing : JointFirings.Bag Nat E extendedProgram tokenState.frame,
      firing.AdmitsUnique X tokenState extendedProgram := by
  rintro ⟨firing, unique⟩
  obtain ⟨member, only⟩ := List.length_eq_one_iff.mp unique.2
  have readerKey := JointFirings.Bag.AdmitsUnique.key_eq unique only
    (g := ReadTake.reader.firing) ReadTake.reader.member ReadTake.reader_admitted
  have takerKey := JointFirings.Bag.AdmitsUnique.key_eq unique only
    (g := ReadTake.taker.firing) ReadTake.taker.member ReadTake.taker_admitted
  exact extended_matches_distinct (readerKey.trans takerKey.symm)

theorem extended_no_unique_move : ¬ ∃ after, uniqueMove extendedProgram tokenState after := by
  rintro ⟨after, firing, unique, _⟩
  exact extended_no_unique_bag ⟨firing, unique⟩

theorem extended_no_every_bag :
    ¬ ∃ firing : JointFirings.Bag Nat E extendedProgram tokenState.frame,
      firing.AdmitsEvery X tokenState extendedProgram := by
  rintro ⟨firing, every⟩
  have readerListed := every.2.2.2 ReadTake.reader.firing ReadTake.reader.member ReadTake.reader_admitted
  have takerListed := every.2.2.2 ReadTake.taker.firing ReadTake.taker.member ReadTake.taker_admitted
  have taken : 0 ∈ firing.selection.taken :=
    (JointFirings.Bag.mem_taken_iff_key firing 0).mpr ⟨_, takerListed, by decide⟩
  obtain ⟨reader, inside, sameKey⟩ := List.mem_map.mp readerListed
  have sameRead : reader.selection.read = [0] :=
    congrArg (fun key : Rule Tm × List Nat × List Nat => key.2.2) sameKey
  have kept : 0 ∈ firing.selection.read := by
    change 0 ∈ firing.members.flatMap (fun member => member.selection.read)
    exact List.mem_flatMap.mpr ⟨reader, inside, by rw [sameRead]; exact List.mem_cons_self⟩
  exact Finset.disjoint_left.mp every.1.2.1.apart
    (List.mem_toFinset.mpr taken) (List.mem_toFinset.mpr kept)

theorem extended_no_every_move : ¬ ∃ after, everyMove extendedProgram tokenState after := by
  rintro ⟨after, firing, every, _⟩
  exact extended_no_every_bag ⟨firing, every⟩

def widenedOriginal : Firing Nat E extendedProgram tokenState.frame :=
  let original := (EveryControls.takeAt 0 10).firing
  ⟨original.rule, program_extension original.member, original.ext, original.opening,
    original.selection, original.seen⟩

theorem one_match_survives : widenedOriginal.Admits X tokenState :=
  EveryControls.takeAt_admitted (by decide) (by decide)

theorem one_match_result_retained :
    widenedOriginal.result X tokenState = (EveryControls.takeAt 0 10).firing.result X tokenState := rfl

theorem unique_program_extension_fails :
    originalProgram ⊆ extendedProgram ∧
      (∃ after, uniqueMove originalProgram tokenState after) ∧
      ¬ ∃ after, uniqueMove extendedProgram tokenState after :=
  ⟨program_extension, ⟨_, original_unique⟩, extended_no_unique_move⟩

theorem unique_not_program_monotone :
    ¬ ∀ (first second : Program Tm), first ⊆ second →
      ∀ before after, uniqueMove first before after → uniqueMove second before after := by
  intro monotone
  exact extended_no_unique_move ⟨_, monotone originalProgram extendedProgram program_extension
    tokenState _ original_unique⟩

theorem every_program_extension_fails :
    originalProgram ⊆ extendedProgram ∧
      (∃ after, everyMove originalProgram tokenState after) ∧
      ¬ ∃ after, everyMove extendedProgram tokenState after :=
  ⟨program_extension, ⟨_, original_every⟩, extended_no_every_move⟩

theorem every_not_program_monotone :
    ¬ ∀ (first second : Program Tm), first ⊆ second →
      ∀ before after, everyMove first before after → everyMove second before after := by
  intro monotone
  exact extended_no_every_move ⟨_, monotone originalProgram extendedProgram program_extension
    tokenState _ original_every⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Worlds.PolicyControls
