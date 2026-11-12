import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderChecks

/-!
# Controls for the first-order reading

Terms are numbers under syntactic equality, with one substitution. Occurrences are numbers
labelled by themselves.

* **A read position is not a copy.** The rule instance `twice` reads the label `5` at two
  positions. Its firing on the single occurrence `5` is admitted (`pick_is_admitted`) and is a
  proof from the resources `{5}` (`a_firing_with_two_reads_of_one_occurrence_is_a_proof`). Its use
  reads one copy (`the_use_reads_one_copy`); one copy for each read position would not fit
  (`one_copy_for_each_read_position_does_not_fit`).
* **Absence is not a guard on knowledge.** The rule instance `unlessNine` checks the absence of
  `9`. Its checks are not all equality checks (`absence_is_not_a_guard_on_knowledge`). Its firing
  is admitted at `{5}` (`unless_nine_is_admitted`) and refused at `{5, 9}`
  (`unless_nine_is_refused_beside_nine`). Read on labels, the check holds of `{5}` and fails of
  `{5} + {9}` (`absence_reads_the_frame`).
* **A predicate query that saw identities is outside the reading on labels.** It holds of one
  occurrence and fails of another with the same label
  (`a_predicate_query_observes_identities`), whereas the checks of a rule instance read labels
  only (`holds_iff_holdsOn`).
* **Completeness needs consistent final knowledge.** A use that tells `1 = 2` is a proof
  (`an_inconsistent_tell_is_a_proof`) whose final knowledge is inconsistent
  (`its_final_knowledge_is_inconsistent`), and no firing of it is admitted
  (`and_it_has_no_admitted_firing`).
* **Completeness needs a supply of fresh occurrences.** With no occurrences at all, a use that
  makes `7` is a proof from the reading of the empty configuration
  (`a_make_is_a_proof_without_occurrences`, `the_empty_configuration_reads_as_its_premises`),
  and no firing of it is admitted (`but_no_occurrence_can_be_made`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Logic.LinearLogic
open KnowledgeTensorFirstOrder

def plain : SubstitutionAction Nat Unit where
  E := Eq
  equivalence := eq_equivalence
  apply := fun _ term => term
  identity := ()
  compose := fun _ _ => ()
  apply_identity := fun _ => rfl
  apply_compose := fun _ _ _ => rfl
  preserves := fun _ _ _ same => same

def one : Configuration Nat Nat := ⟨[], {5}⟩

def withNine : Configuration Nat Nat := ⟨[], {5, 9}⟩

/-! ## A read position is not a copy -/

def twice : RuleInstance Nat := ⟨[], [5, 5], [], [], [7]⟩

def pick : Selection Nat := ⟨[], [5, 5], [7]⟩

theorem pick_is_admitted : pick.Valid plain id twice one := by
  refine ⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, by decide, ⟨(), ?_⟩, ?_⟩
  · intro equation member
    have shape : pick.problem id twice one = [(5, 5), (5, 5)] := rfl
    rw [shape] at member
    rcases List.mem_cons.mp member with rfl | later
    · exact rfl
    · rcases List.mem_cons.mp later with rfl | empty
      · exact rfl
      · cases empty
  · intro check member
    cases member

theorem a_firing_with_two_reads_of_one_occurrence_is_a_proof :
    (system plain {twice}).Derives (knowledge plain one) (resources id one)
      [useOf id (twice, pick)] (knowledge plain (pick.result id twice one))
      (resources id (pick.result id twice one)) := by
  have executable : ConditionalSchedule.Executable plain id one [(twice, pick)] :=
    ⟨pick_is_admitted, pick_is_admitted.consistent⟩
  have declared : ∀ firing ∈ [(twice, pick)],
      firing.1 ∈ ({twice} : Set (RuleInstance Nat)) ∧ GuardsOnly firing.1 := by
    intro firing member
    have which : firing = (twice, pick) := List.mem_singleton.mp member
    subst which
    refine ⟨rfl, ?_⟩
    intro check inside
    cases inside
  exact KnowledgeTensor.System.Run.derives
    (run_of_executable plain {twice} id [(twice, pick)] one executable declared)

theorem the_use_reads_one_copy :
    (system plain {twice}).read (useOf id (twice, pick)) = ({5} : Multiset Nat) := by
  decide

theorem one_copy_for_each_read_position_does_not_fit :
    ¬ ((([5, 5] : List Nat) : Multiset Nat) ≤ resources id one) := by
  intro fits
  exact absurd (Multiset.card_le_card fits) (by decide)

/-! ## Absence is not a guard on knowledge -/

def unlessNine : RuleInstance Nat := ⟨[], [], [], [Check.absent 9], [7]⟩

def makeSeven : Selection Nat := ⟨[], [], [7]⟩

theorem absence_is_not_a_guard_on_knowledge : ¬ GuardsOnly unlessNine := by
  intro guards
  obtain ⟨left, right, same⟩ := guards (Check.absent 9) (List.mem_singleton.mpr rfl)
  cases same

theorem unless_nine_is_admitted : makeSeven.Valid plain id unlessNine one := by
  refine ⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, by decide, ⟨(), ?_⟩, ?_⟩
  · intro equation member
    cases member
  · intro check member σ _
    have which : check = Check.absent 9 := List.mem_singleton.mp member
    subst which
    intro o present
    have same : o = 5 := Finset.mem_singleton.mp present
    rw [same]
    exact (by decide : (9 : Nat) ≠ 5)

theorem unless_nine_is_refused_beside_nine : ¬ makeSeven.Valid plain id unlessNine withNine := by
  intro valid
  have solved : plain.Models () (makeSeven.problem id unlessNine withNine) := by
    intro equation member
    cases member
  have holds := valid.checks (Check.absent 9) (List.mem_singleton.mpr rfl) () solved
  exact holds 9 (by decide) rfl

theorem absence_reads_the_frame :
    HoldsOn plain () (Check.absent 9) ({5} : Multiset Nat) ∧
      ¬ HoldsOn plain () (Check.absent 9) (({5} : Multiset Nat) + {9}) := by
  constructor
  · intro value member
    rw [Multiset.mem_singleton] at member
    rw [member]
    exact (by decide : (9 : Nat) ≠ 5)
  · intro clear
    exact clear 9 (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self 9))) rfl

/-! ## A predicate query that saw identities is not a function of the labels -/

def sawOne : PredicateQuery Nat Nat := ⟨fun _ => true, {1}⟩

theorem a_predicate_query_observes_identities :
    sawOne.Holds (fun _ : Nat => 0) {1} ∧ ¬ sawOne.Holds (fun _ : Nat => 0) {2} ∧
      labels (fun _ : Nat => 0) ({1} : Finset Nat) = labels (fun _ : Nat => 0) ({2} : Finset Nat) := by
  decide

/-! ## The two hypotheses of completeness are needed -/

def contradict : RuleInstance Nat := ⟨[], [], [(1, 2)], [], []⟩

theorem an_inconsistent_tell_is_a_proof :
    (system plain {contradict}).Derives (knowledge plain one)
      ((system plain {contradict}).premises ⟨contradict, [], []⟩) [⟨contradict, [], []⟩]
      (knowledge plain one ⊓ (system plain {contradict}).tell ⟨contradict, [], []⟩)
      ((system plain {contradict}).conclusions ⟨contradict, [], []⟩) :=
  KnowledgeTensor.System.Derives.rule _ _ ⟨rfl, rfl, rfl, fun check member => by cases member⟩

theorem its_final_knowledge_is_inconsistent :
    ¬ (knowledge plain one ⊓ (system plain {contradict}).tell ⟨contradict, [], []⟩).Nonempty := by
  rintro ⟨σ, _, told⟩
  have wrong : (1 : Nat) = 2 := told (1, 2) (List.mem_singleton.mpr rfl)
  exact absurd wrong (by decide)

theorem and_it_has_no_admitted_firing :
    ¬ ∃ selection : Selection Nat, selection.Valid plain id contradict one := by
  rintro ⟨selection, valid⟩
  obtain ⟨σ, solved⟩ := valid.consistent
  have wrong : (1 : Nat) = 2 := solved (1, 2) (List.mem_append_right _ (List.mem_singleton.mpr rfl))
  exact absurd wrong (by decide)

def nowhere : Empty → Nat := fun occurrence => nomatch occurrence

def blank : Configuration Nat Empty := ⟨[], ∅⟩

def produceSeven : RuleInstance Nat := ⟨[], [], [], [], [7]⟩

theorem a_make_is_a_proof_without_occurrences :
    (system plain {produceSeven}).Derives (knowledge plain blank)
      ((system plain {produceSeven}).premises ⟨produceSeven, [], []⟩) [⟨produceSeven, [], []⟩]
      (knowledge plain blank ⊓ (system plain {produceSeven}).tell ⟨produceSeven, [], []⟩)
      ((system plain {produceSeven}).conclusions ⟨produceSeven, [], []⟩) :=
  KnowledgeTensor.System.Derives.rule _ _ ⟨rfl, rfl, rfl, fun check member => by cases member⟩

theorem the_empty_configuration_reads_as_its_premises :
    resources nowhere blank = (system plain {produceSeven}).premises ⟨produceSeven, [], []⟩ := by
  decide

theorem but_no_occurrence_can_be_made :
    ¬ ∃ selection : Selection Empty, selection.Valid plain nowhere produceSeven blank := by
  rintro ⟨selection, valid⟩
  have lengths := congrArg List.length valid.outputs
  rw [List.length_map] at lengths
  cases made : selection.made with
  | nil =>
      rw [made] at lengths
      exact absurd lengths (by decide)
  | cons occurrence _ => exact occurrence.elim

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorFirstOrderControls
