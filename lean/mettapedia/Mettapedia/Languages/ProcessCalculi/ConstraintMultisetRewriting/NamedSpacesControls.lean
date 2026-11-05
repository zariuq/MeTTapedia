import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpacesComposition

/-!
# Named spaces: further controls and the axiom audit

* **The law is asked before selection.** Each selection's own problem resolves the free space
  variable, to a different name per selection, while the store before the step resolves it to
  none (`resolution_after_selection_is_vacuous`). Resolution checked after selection, as an
  ordinary check of the rule, would admit the ambient take; the law is an admission ask on the
  store before the step.
* **Per space** (`per_space_positive`, `per_space_negative`): a rule written at space 1 is valid
  at a world and at that world with space 2 emptied; removing the letter at space 1 refuses it.
* **Passing a name in a message extends reach** (`message_gives_reach`, `no_message_no_reach`):
  with a capability for space 7 posted at space 1 the board client reaches 7; without it, it does
  not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces.Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

/-- **Resolution after selection is vacuous**: each selection's problem resolves the variable
space, to a different name per selection, and the store before the step resolves it to none. -/
theorem resolution_after_selection_is_vacuous :
    ResolvesTo spaces (takeFirst.problem (located spaces twoSpaces letter)
        (grabAnywhere.toRule spaces) twoWorld) (.var 0) 1 ∧
      ResolvesTo spaces (takeSecond.problem (located spaces twoSpaces letter)
        (grabAnywhere.toRule spaces) twoWorld) (.var 0) 2 ∧
      ¬ Resolves spaces twoWorld.equations (.var 0) := by
  refine ⟨fun σ solved => ?_, fun σ solved => ?_, ?_⟩
  · simpa [spaces, Tm.subst] using unresolved_space_differs_by_selection.1 σ solved
  · simpa [spaces, Tm.subst] using unresolved_space_differs_by_selection.2 σ solved
  · rintro ⟨n, at_n⟩
    have := at_n (fun _ => .nm (n + 1)) (by simp [twoWorld])
    simp [spaces, Tm.subst] at this

/-! ### Per space -/

/-- The two-space world with the letter at space 2 removed. -/
def onlyFirst : Configuration Tm Nat := ⟨[], {0}⟩

/-- The two-space world with the letter at space 1 removed. -/
def onlySecond : Configuration Tm Nat := ⟨[], {1}⟩

theorem twoWorld_wellLocated : WellLocated spaces twoSpaces twoWorld := by
  intro o _
  by_cases h : o = 0
  · subst h
    exact ⟨1, resolvesTo_name (sts := spaces) _ 1⟩
  · have named : twoSpaces o = spaces.name 2 := by simp [twoSpaces, h, spaces]
    rw [named]
    exact ⟨2, resolvesTo_name _ 2⟩

theorem onlyFirst_wellLocated : WellLocated spaces twoSpaces onlyFirst := by
  intro o present
  simp only [onlyFirst, Finset.mem_singleton] at present
  subst present
  exact ⟨1, resolvesTo_name (sts := spaces) _ 1⟩

theorem at_one_is_zero {o : Nat}
    (at_one : ResolvesTo spaces ([] : EquationStore Tm) (twoSpaces o) 1) : o = 0 := by
  by_contra h
  have := at_one Tm.var (by simp)
  simp [twoSpaces, h, spaces, Tm.subst] at this

theorem grabAtOne_footprint {k : Nat} (footprint : Footprint spaces [] grabAtOne k) : k = 1 := by
  obtain ⟨s, member, at_k⟩ := footprint
  simp [LocatedRule.spaces, grabAtOne] at member
  subst member
  have := at_k Tm.var (by simp)
  simpa [spaces, Tm.subst] using this.symm

/-- **Positive control of per-space validity**: emptying space 2 does not change the validity of
a rule written at space 1. -/
theorem per_space_positive :
    takeFirst.Valid action (located spaces twoSpaces letter) (grabAtOne.toRule spaces) onlyFirst := by
  have valid := resolved_rule_takes_only_there.2
  obtain ⟨selection, validAt, after⟩ := valid
  have agree : AgreeOn spaces twoSpaces grabAtOne twoWorld onlyFirst := by
    refine ⟨rfl, fun o ⟨k, footprint, at_k⟩ => ?_⟩
    have one := grabAtOne_footprint footprint
    subst one
    have zero := at_one_is_zero at_k
    subst zero
    simp [twoWorld, onlyFirst]
  have direct : takeFirst.Valid action (located spaces twoSpaces letter)
      (grabAtOne.toRule spaces) twoWorld := by
    refine ⟨by simp [takeFirst], by simp [takeFirst], rfl, rfl, rfl, takeFirst_enabled _,
      ⟨Tm.var, ?_⟩, by simp [grabAtOne, LocatedRule.toRule]⟩
    simp [SubstitutionAction.Solves, Selection.problem, Selection.equations, grabAtOne,
      LocatedRule.toRule, takeFirst, twoWorld, place, located, spaces, twoSpaces, letter, Tm.subst]
  exact (valid_iff_of_agree_on_spaces (resolved_rule_resolved []) twoWorld_wellLocated
    onlyFirst_wellLocated agree (by simp [takeFirst]) (by simp [takeFirst])).mp direct

/-- **Negative control**: with the letter at space 1 removed, no selection is valid. -/
theorem per_space_negative (selection : Selection Nat) :
    ¬ selection.Valid action (located spaces twoSpaces letter) (grabAtOne.toRule spaces)
      onlySecond := by
  intro valid
  have lengths := valid.take_length
  simp only [grabAtOne, LocatedRule.toRule, List.map_cons, List.map_nil, List.length_cons,
    List.length_nil] at lengths
  obtain ⟨x, member⟩ : ∃ x, x ∈ selection.taken := by
    cases h : selection.taken with
    | nil => rw [h] at lengths; simp at lengths
    | cons x _ => exact ⟨x, by simp⟩
  have present := valid.occurrences.taken_subset (by simpa [Selection.commit] using member)
  simp only [onlySecond, Finset.mem_singleton] at present
  subst present
  obtain ⟨σ, solved⟩ := valid.consistent
  obtain ⟨_, takes, _, _⟩ := Selection.models_problem action valid solved
  have only : selection.taken = [1] := by
    cases h : selection.taken with
    | nil => simp [h] at member
    | cons y rest =>
        rw [h] at lengths
        simp only [List.length_cons] at lengths
        have : rest = [] := List.length_eq_zero_iff.mp (by omega)
        subst this
        rw [h] at member
        simp at member
        rw [member]
  rw [only] at takes
  simp [grabAtOne, LocatedRule.toRule, place, located, spaces, twoSpaces, letter, Tm.subst] at takes

/-! ### Passing a name in a message extends reach -/

/-- The board without the capability message: only the secret at 7. -/
def bareBoard : Configuration Tm Nat := ⟨[], {1}⟩

/-- **Positive control**: with the capability for 7 posted at space 1, the client reaches 7. -/
theorem message_gives_reach :
    Reach names board.equations boardSpace (located spaces boardSpace boardPayload) board.present
      clientTerms 7 := by
  apply Reach.closed
  have reachedOne : Reach names board.equations boardSpace
      (located spaces boardSpace boardPayload) board.present clientTerms 1 :=
    Reach.of_possesses (written_name_possessed ⟨Tm.var, by simp [board]⟩
      (by simp [clientTerms, spaces]))
  have message : located spaces boardSpace boardPayload 0 ∈ clientTerms ∪
      labelsAt spaces board.equations boardSpace (located spaces boardSpace boardPayload)
        board.present (Reach names board.equations boardSpace
          (located spaces boardSpace boardPayload) board.present clientTerms) :=
    Or.inr ⟨0, by simp [board], 1, reachedOne, resolvesTo_name (sts := spaces) _ 1, rfl⟩
  refine ground_term_possessed ⟨Tm.var, by simp [board]⟩ message ?_ ?_
  · intro σ
    simp [located, spaces, boardSpace, boardPayload, Tm.subst]
  · intro m different same
    change Tm.loc (.nm 1) (.app (.sym "cap") (.nm 7)) =
      Tm.swap 7 m (Tm.loc (.nm 1) (.app (.sym "cap") (.nm 7))) at same
    simp only [Tm.swap] at same
    have inner : (7 : Nat) = Equiv.swap 7 m 7 := Tm.nm.inj (Tm.app.inj (Tm.loc.inj same).2).2
    rw [Equiv.swap_apply_left] at inner
    exact different inner.symm

/-- **Negative control**: without the message the client does not reach 7. -/
theorem no_message_no_reach :
    ¬ Reach names bareBoard.equations boardSpace (located spaces boardSpace boardPayload)
      bareBoard.present clientTerms 7 := by
  intro reached
  have closed := reached (fun k => k ≠ 7) ?_
  · exact closed rfl
  intro m possessed
  rintro rfl
  apply possessed
  refine ⟨8, by decide, indistinguishable_of_invariant ?_ ?_⟩
  · rintro t (inK | ⟨o, present, k, notSeven, at_k, rfl⟩)
    · simp only [clientTerms, Set.mem_insert_iff, Set.mem_singleton_iff] at inK
      rcases inK with rfl | rfl | rfl | rfl <;> rfl
    · simp only [bareBoard, Finset.mem_singleton] at present
      subst present
      have := at_k Tm.var (by simp [bareBoard])
      simp [boardSpace, spaces, Tm.subst] at this
      exact absurd this.symm notSeven
  · simp [bareBoard]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces.Controls

/-! ## Axiom audit -/

section Audit

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamedSpaces

-- D1
#print axioms Embedding.valid_iff
#print axioms Embedding.step_iff
#print axioms flat_step_is_one_space
#print axioms flat_valid_is_one_space
#print axioms rigid_location_is_constant_space
#print axioms rigid_step_iff
#print axioms fromRigid_toRule
#print axioms fromRigid_resolved
#print axioms ResolvesTo.of_refines
#print axioms taken_at_port_space
#print axioms read_at_port_space
#print axioms made_at_port_space
#print axioms check_matches_at_space
#print axioms frame_survives
#print axioms frame_no_arrival
#print axioms LocatedStep.wellLocated
#print axioms valid_iff_of_agree_on_spaces
#print axioms Controls.unresolved_takes_from_either_space
#print axioms Controls.unresolved_space_differs_by_selection
#print axioms Controls.unresolved_rule_not_resolved
#print axioms Controls.resolved_rule_takes_only_there
#print axioms Controls.resolved_rule_refuses_other_space
#print axioms Controls.resolution_after_selection_is_vacuous
#print axioms Controls.per_space_positive
#print axioms Controls.per_space_negative
-- D2
#print axioms resolved_name_possessed
#print axioms ground_term_possessed
#print axioms footprint_possessed
#print axioms no_name_no_effect
#print axioms no_name_no_observation
#print axioms indistinguishable_after_step
#print axioms possession_after_step
#print axioms indistinguishable_of_invariant
#print axioms Reach.closed
#print axioms footprint_reached
#print axioms reach_after_step
#print axioms other_reach_after_step
#print axioms effects_in_reach
#print axioms reach_after_run
#print axioms Controls.board_client_has_no_name_for_seven
#print axioms Controls.board_client_cannot_affect_seven
#print axioms Controls.use_before_read_refused
#print axioms Controls.read_gives_name
#print axioms Controls.use_after_read_steps
#print axioms Controls.shared_variable_passes_name
#print axioms Controls.unrelated_binding_gives_no_name
#print axioms Controls.message_gives_reach
#print axioms Controls.no_message_no_reach
-- D3
#print axioms holds_insert_congr
#print axioms forwarder_faithful
#print axioms holds_congr
#print axioms forwarder_observations_agree
#print axioms Controls.forwarded_count_entailed
#print axioms send_is_rigid_send
#print axioms rigid_send_formed_iff
#print axioms ask_faithful_fragment
#print axioms Controls.mailbox_holder_cannot_take_at_owner_store
#print axioms Controls.peek_impossible_after_owner_take
#print axioms Controls.ask_acts_after_owner_take
#print axioms Controls.guarded_act_refused_when_present
#print axioms Controls.ask_absence_acts_when_present
#print axioms Controls.two_asks_two_copies
#print axioms Controls.forwarder_gap_observable
#print axioms Controls.primitive_send_no_gap
#print axioms Controls.shared_mailbox_intercepted
#print axioms Controls.separate_mailbox_not_intercepted
#print axioms Controls.peek_binds_owner_variable
-- D4
#print axioms disjoint_spaces_independent
#print axioms disjoint_spaces_ignore_writes
#print axioms disjoint_spaces_commute
#print axioms post_and_forward_commute
#print axioms Controls.shared_variable_blocks_commutation
#print axioms Controls.separate_variables_commute
#print axioms Controls.counting_owner_valid
#print axioms Controls.counting_owner_spoiled_by_post

end Audit
