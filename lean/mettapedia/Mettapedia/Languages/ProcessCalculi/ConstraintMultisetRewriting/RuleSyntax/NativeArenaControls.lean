import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Co-present resources are different from elementwise alternatives

This finite control uses the existing first-order transform instance. One
rule consumes distinct tokens 1 and 2 together and produces token 3. It is
admitted in their joint arena, and refused in each singleton arena. Thus a
compiler cannot distribute an arena-consuming operation over its elements.

The example does not equate arbitrary search with isolation of public spaces,
establish a linear-logic embedding, or choose a universal firing grain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.NativeArenaControls

open Examples (Tm X E c shift everywhere)
open MeTTaCalculus.OccurrenceCommits

def joinRule : Rule Tm := ⟨PUnit.unit, ⟨[c 1, c 2], [], [], [], [c 3]⟩, []⟩
def program : Program Tm := {joinRule}

def labels (occurrence : Nat) := if occurrence = 0 then c 1 else c 2
def arena : State Tm Nat := ⟨PUnit.unit, [], {0, 1}, labels⟩
def leftOnly : State Tm Nat := ⟨PUnit.unit, [], {0}, labels⟩
def rightOnly : State Tm Nat := ⟨PUnit.unit, [], {1}, labels⟩

def join : Firing Nat E program PUnit.unit :=
  ⟨joinRule, Set.mem_singleton _, PUnit.unit, shift, ⟨[0, 1], [], [2]⟩, []⟩

theorem join_information : join.information X arena = [(c 1, c 1), (c 2, c 2)] := rfl

theorem join_fresh (state : State Tm Nat) : join.Fresh X state := by
  apply Examples.fresh_of_ground
  intro term member assignment
  simp only [join, joinRule, Rule.terms, List.map_nil, List.flatMap_nil, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

theorem together_admitted : join.Admits X arena := by
  refine ⟨⟨join_fresh arena, by decide, by decide, rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_⟩
  · change Enabled (fun _ : Nat => ()) {0, 1}
      (⟨{0, 1}, ∅, {2}, []⟩ : Commit Nat Unit)
    decide
  · refine ⟨PUnit.unit, everywhere 0, ?_⟩
    rw [join_information]
    intro equation member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro future assignment _
    exact ⟨fun _ impossible => False.elim (List.not_mem_nil impossible),
      fun _ impossible => False.elim (List.not_mem_nil impossible)⟩

theorem left_refused : ¬ join.Admits X leftOnly := by
  intro admitted
  have missing := admitted.2.1.taken_subset (show 1 ∈ join.selection.commit.taken by decide)
  exact (by decide : 1 ∉ leftOnly.present) missing

theorem right_refused : ¬ join.Admits X rightOnly := by
  intro admitted
  have missing := admitted.2.1.taken_subset (show 0 ∈ join.selection.commit.taken by decide)
  exact (by decide : 0 ∉ rightOnly.present) missing

theorem joint_result : (join.result X arena).present = {2} ∧ (join.result X arena).label 2 = c 3 := by
  constructor
  · change (({0, 1} : Finset Nat) \ {0, 1}) ∪ {2} = {2}
    decide
  · rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.NativeArenaControls
