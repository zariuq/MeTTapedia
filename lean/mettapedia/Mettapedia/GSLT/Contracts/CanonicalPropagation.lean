import Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses
import Mettapedia.Machines.SemiNaiveInsertSaturation

/-!
# Set propagation through a change of representatives

Ground rule instances over equation classes can propagate through
canonical keys at a fixed equality profile. The result is a commuting
square for both the known facts and the delta, including all iterations
and completed closures. The proof uses a bijection on fact classes;
it does not move set difference through a map that identifies facts.

Generating all correct ground instances is a separate matching
obligation. This contract does not license reusing these keys after a
tell has changed the quotient.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.CanonicalPropagation

open Mettapedia.Logic
open Mettapedia.Machines.RecursiveInsert.SemiNaive
open Mettapedia.GSLT.Contracts.CanonicalSuccessorClasses (NormalForms)

variable {Fact Key : Type} [DecidableEq Fact] [DecidableEq Key]

def keyRule (key : Fact ≃ Key) (rule : LP.PropRule Fact) : LP.PropRule Key :=
  ⟨rule.premises.map key.toEmbedding, key rule.head⟩

def keyProgram (key : Fact ≃ Key) (program : LP.PropProgram Fact) : LP.PropProgram Key :=
  program.image (keyRule key)

def keyState (key : Fact ≃ Key) (state : State Fact) : State Key :=
  ⟨state.known.map key.toEmbedding, state.delta.map key.toEmbedding⟩

omit [DecidableEq Fact] [DecidableEq Key] in
theorem keyRule_hot (key : Fact ≃ Key) (rule : LP.PropRule Fact) (delta : Finset Fact) :
    hot (keyRule key rule) (delta.map key.toEmbedding) ↔ hot rule delta := by
  simp only [hot, keyRule, Finset.map_eq_empty, Finset.mem_map_equiv]
  constructor
  · rintro (empty | ⟨fact, used, new⟩)
    · exact Or.inl empty
    · exact Or.inr ⟨key.symm fact, used, new⟩
  · rintro (empty | ⟨fact, used, new⟩)
    · exact Or.inl empty
    · exact Or.inr ⟨key fact, by simpa using used, by simpa using new⟩

omit [DecidableEq Fact] in
theorem keyState_invariant (key : Fact ≃ Key) (program : LP.PropProgram Fact) (state : State Fact) :
    Invariant (keyProgram key program) (keyState key state) ↔ Invariant program state := by
  constructor
  · intro valid
    refine ⟨Finset.map_subset_map.mp valid.delta_known, ?_⟩
    intro rule member enabled
    have atKey := valid.old_complete (keyRule key rule) (Finset.mem_image_of_mem _ member)
      (Finset.map_subset_map.mpr enabled)
    change hot (keyRule key rule) (state.delta.map key.toEmbedding) ∨
      key rule.head ∈ state.known.map key.toEmbedding at atKey
    rw [keyRule_hot, Finset.mem_map_equiv, Equiv.symm_apply_apply] at atKey
    exact atKey
  · intro valid
    refine ⟨Finset.map_subset_map.mpr valid.delta_known, ?_⟩
    intro encoded member enabled
    obtain ⟨rule, declared, rfl⟩ := Finset.mem_image.mp member
    have applies : rule.premises ⊆ state.known := Finset.map_subset_map.mp enabled
    change hot (keyRule key rule) (state.delta.map key.toEmbedding) ∨
      key rule.head ∈ state.known.map key.toEmbedding
    rw [keyRule_hot, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact valid.old_complete rule declared applies

theorem keyHeads (key : Fact ≃ Key) (program : LP.PropProgram Fact) (state : State Fact) :
    heads (keyProgram key program) (keyState key state) =
      (heads program state).map key.toEmbedding := by
  ext target
  obtain ⟨fact, rfl⟩ := key.surjective target
  simp only [mem_heads, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨encoded, member, enabled, ready, atKey⟩
    obtain ⟨rule, declared, rfl⟩ := Finset.mem_image.mp member
    exact ⟨rule, declared, Finset.map_subset_map.mp enabled, (keyRule_hot _ _ _).mp ready,
      key.injective atKey⟩
  · rintro ⟨rule, declared, enabled, ready, rfl⟩
    exact ⟨keyRule key rule, Finset.mem_image_of_mem _ declared, Finset.map_subset_map.mpr enabled,
      (keyRule_hot _ _ _).mpr ready, rfl⟩

theorem keyRound (key : Fact ≃ Key) (program : LP.PropProgram Fact) (state : State Fact) :
    round (keyProgram key program) (keyState key state) = keyState key (round program state) := by
  simp only [Mettapedia.Machines.RecursiveInsert.SemiNaive.round]
  rw [keyHeads]
  simp only [keyState, Finset.map_union, Finset.map_sdiff]

theorem keyRounds (key : Fact ≃ Key) (program : LP.PropProgram Fact) (seeds : Finset Fact) (n : Nat) :
    rounds (keyProgram key program) (seeds.map key.toEmbedding) n =
      keyState key (rounds program seeds n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [rounds, rounds, ih, keyRound]

theorem completed_closure [Fintype Fact] [Fintype Key] (key : Fact ≃ Key)
    (program : LP.PropProgram Fact) (seed : Finset Fact) :
    LP.saturate (keyProgram key program) (seed.map key.toEmbedding) =
      (LP.saturate program seed).map key.toEmbedding := by
  have sameFuel : LP.maxSteps (α := Key) = LP.maxSteps (α := Fact) := by
    unfold LP.maxSteps
    rw [Fintype.card_congr key]
  simp only [LP.saturate, sameFuel, ← rounds_eq_iterate]
  exact congrArg State.known (keyRounds key program seed _)

/-- Instantiate the transport by *the* equivalence of classes with
canonical keys, not a map from raw spellings which can merge facts. -/
theorem quotient_round {equations : Setoid Fact} (forms : NormalForms equations)
    [DecidableEq (Quotient equations)] (program : LP.PropProgram (Quotient equations))
    (state : State (Quotient equations)) :
    round (keyProgram forms.classEquiv program) (keyState forms.classEquiv state) =
      keyState forms.classEquiv (round program state) :=
  keyRound forms.classEquiv program state

namespace Controls

private def flip : Bool ≃ Bool :=
  ⟨Bool.not, Bool.not, by decide, by decide⟩

private def follow : LP.PropRule Bool := ⟨{false}, true⟩

theorem nontrivial_reencoding_keeps_delta :
    (round (keyProgram flip {follow}) (keyState flip ⟨{false}, {false}⟩)).delta = {false} := by
  rw [keyRound]
  decide

/-- Crossing an epoch that *merges* keys is not a change of
representatives within a fixed quotient. Old and fresh versions of a
row can become the same fact, so pushing subtraction through the merge
is wrong. -/
theorem merging_keys_does_not_commute_with_difference :
    (({false, true} : Finset Bool) \ {false}).image (fun _ => ()) ≠
      ({false, true} : Finset Bool).image (fun _ => ()) \
        ({false} : Finset Bool).image (fun _ => ()) := by
  decide

end Controls

#print axioms keyState_invariant
#print axioms keyRound
#print axioms completed_closure
#print axioms quotient_round
#print axioms Controls.nontrivial_reencoding_keeps_delta
#print axioms Controls.merging_keys_does_not_commute_with_difference

end Mettapedia.GSLT.Contracts.CanonicalPropagation
