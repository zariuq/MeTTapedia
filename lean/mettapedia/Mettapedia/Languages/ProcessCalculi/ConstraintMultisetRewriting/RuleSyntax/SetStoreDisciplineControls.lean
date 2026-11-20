import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOutcomes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreOpenControls

/-! # A determinate unique step and a ground ambiguity control -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplineControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings SetStoreSyntax
open SetStoreOpenControls (c choose choose_propagates)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

def singleProgram : Program (Terms (Term atoms)) := {choose 5}
def seed : Finset (Term atoms) := {c 5}

theorem single_pure : ∀ rule ∈ singleProgram, Propagates rule := by
  intro rule member
  obtain rfl := Set.mem_singleton_iff.mp member
  exact choose_propagates _

def singleMatch : GroundMatch singleProgram where
  rule := choose 5
  member := rfl
  propagates := choose_propagates _
  assignment := Subst.id atoms
  groundReads term inside := by
    obtain rfl := List.mem_singleton.mp inside
    trivial
  checked _ _ inside := by cases inside

theorem seed_ground : GroundRows seed := by
  intro term inside
  obtain rfl := Finset.mem_singleton.mp inside
  trivial

theorem one_determinate : Determinate (P := singleProgram) seed := by
  intro first second firstYes secondYes
  have covers : ∀ rule ∈ singleProgram, rule ∈ [choose 5] := by
    intro rule member
    simpa [singleProgram] using member
  have firstCandidate := SymmetricMatches.admitted_presentation_is_candidate (SetStore.represent seed)
    [choose 5] covers first firstYes
  have secondCandidate := SymmetricMatches.admitted_presentation_is_candidate (SetStore.represent seed)
    [choose 5] covers second secondYes
  simp only [SetStore.represent, seed, Finset.image_singleton, Finset.toList_singleton,
    SymmetricMatches.candidates, SymmetricMatches.selections, choose, List.length_nil,
    List.length_cons, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.append_nil, List.zip_nil_left, List.zip_cons_cons, List.zip_nil_right,
    List.mem_singleton] at firstCandidate secondCandidate
  exact congrArg SymmetricMatches.Presentation.key (firstCandidate.trans secondCandidate.symm)

theorem unique_makes_progress (timing : SetStore.AskTiming) :
    ∃ after, DisciplinedStep .unique timing singleProgram seed after := by
  apply discipline_progress (Equiv.refl ℕ) .unique timing seed seed_ground single_pure
    [choose 5] (fun rule member => by simpa [singleProgram] using member) (fun _ => one_determinate)
  intro closed
  have enabled : (consequence singleMatch).read ⊆ seed := by simp [consequence, singleMatch, choose, seed, c]
  have output := closed singleMatch enabled
  have made : c 15 ∈ (consequence singleMatch).made := by simp [consequence, singleMatch, choose, c]
  have impossible := output made
  simp [seed, c] at impossible

def ambiguousSeed : Finset (Term atoms) := {c 5, c 6}

def groundChoice (n : ℕ) (which : n = 5 ∨ n = 6) : GroundMatch SetStoreOpenControls.program where
  rule := choose n
  member := by rcases which with rfl | rfl <;> simp [SetStoreOpenControls.program]
  propagates := choose_propagates _
  assignment := Subst.id atoms
  groundReads term inside := by
    obtain rfl := List.mem_singleton.mp inside
    trivial
  checked _ _ inside := by cases inside

theorem ambiguous_ground : GroundRows ambiguousSeed := by
  intro term inside
  simp only [ambiguousSeed, Finset.mem_insert, Finset.mem_singleton] at inside
  rcases inside with rfl | rfl <;> trivial

theorem two_ground_choices_are_ambiguous :
    ¬ Determinate (P := SetStoreOpenControls.program) ambiguousSeed := by
  intro determinate
  let first := groundChoice 5 (Or.inl rfl)
  let second := groundChoice 6 (Or.inr rfl)
  have enabledFirst : (consequence first).read ⊆ ambiguousSeed := by
    simp [first, consequence, groundChoice, choose, ambiguousSeed, c]
  have enabledSecond : (consequence second).read ⊆ ambiguousSeed := by
    simp [second, consequence, groundChoice, choose, ambiguousSeed, c]
  have same := determinate first.firing second.firing
    (firing_admitted first ambiguousSeed ambiguous_ground enabledFirst)
    (firing_admitted second ambiguousSeed ambiguous_ground enabledSecond)
  have occurrences := SymmetricMatches.Same.read_occurrences
    ((SymmetricMatches.key_eq_iff _ _).mp same)
  have impossible : c 5 = c 6 := by
    simpa [first, second, SymmetricMatches.presentation, GroundMatch.firing, groundChoice, choose, Subst.applyTerm_id]
      using congrArg (fun rows => rows.toList.map (fun row => row.1)) occurrences
  simp [c] at impossible

theorem no_complete_unique_bag (bag : SetStore.Candidate SetStoreOpenControls.program) :
    ¬ bag.AdmitsUniqueBy X (SetStore.represent ambiguousSeed) SymmetricMatches.identity Set.univ := by
  intro unique
  obtain ⟨only, members⟩ := List.length_eq_one_iff.mp unique.2
  apply two_ground_choices_are_ambiguous
  intro first second firstYes secondYes
  exact (unique.key_eq members (Set.mem_univ (SymmetricMatches.identity.key first)) firstYes).trans
    (unique.key_eq members (Set.mem_univ (SymmetricMatches.identity.key second)) secondYes).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStoreDisciplineControls
