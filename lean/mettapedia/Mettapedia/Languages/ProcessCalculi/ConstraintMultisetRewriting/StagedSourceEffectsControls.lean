import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-! # Late refusal leaves the staged token intact; eager execution leaks it -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects.Controls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls (signature A)

def token : Term signature := .const 0
def receipt : Term signature := .const 1
def blocker : Term signature := .const 2
def label (occurrence : Nat) : Term signature := .const occurrence
def good : Configuration (Term signature) Nat := ⟨[], {0}⟩
def bad : Configuration (Term signature) Nat := ⟨[], {0, 2}⟩
def isToken : Term signature → Bool
  | .const value => value == 0
  | _ => false
def isBlocker : Term signature → Bool
  | .const value => value == 2
  | _ => false
def tokenCensus : PredicateQuery Nat (Term signature) := ⟨isToken, {0}⟩
def blockerCensus : PredicateQuery Nat (Term signature) := ⟨isBlocker, ∅⟩

def takeRule : RuleInstance (Term signature) := ⟨[token], [], [], [.count token 1], []⟩
def takeSelection : Selection Nat := ⟨[0], [], []⟩
def publishRule : RuleInstance (Term signature) := ⟨[], [], [], [.absent blocker], [receipt]⟩
def publishSelection : Selection Nat := ⟨[], [], [1]⟩
def takeInstruction : Instruction (Term signature) (Subst signature) Nat :=
  ⟨takeRule, takeSelection, [PredicateQueryAdmission.Query.fixed tokenCensus]⟩
def publishInstruction : Instruction (Term signature) (Subst signature) Nat :=
  ⟨publishRule, publishSelection, [PredicateQueryAdmission.Query.fixed blockerCensus]⟩
def code := [takeInstruction, publishInstruction]

theorem take_ready (world : Finset Nat) (present : 0 ∈ world) :
    takeSelection.Valid A label takeRule ⟨[], world⟩ := by
  classical
  refine ⟨by decide, by decide, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · exact ⟨by simpa [Selection.commit, takeSelection] using present,
      by simp [Selection.commit, takeSelection], by simp [Selection.commit, takeSelection],
      by simp [Selection.commit, takeSelection], by simp [Selection.commit]⟩
  · refine ⟨A.identity, ?_⟩
    intro equation member
    change equation ∈ [(token, token)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro check member candidate _
    obtain rfl := List.mem_singleton.mp member
    change (Check.matches A candidate label world token).card = 1
    have region : Check.matches A candidate label world token = {0} := by
      ext occurrence
      rw [Check.matches, Finset.mem_filter, Finset.mem_singleton]
      change (occurrence ∈ world ∧ (Term.const 0 : Term signature) = .const occurrence) ↔ occurrence = 0
      constructor
      · rintro ⟨_, same⟩
        exact (Term.const.inj same).symm
      · intro same
        subst occurrence
        exact ⟨present, rfl⟩
    rw [region]
    rfl

theorem take_good : PredicateQueryAdmission.Valid A label takeRule takeInstruction.observations good takeSelection := by
  apply (PredicateQueryAdmission.valid_fixed_iff _ _ _ [tokenCensus] _ _).mpr
  exact ⟨take_ready good.present (by decide), fun query member =>
    (List.mem_singleton.mp member) ▸ (by decide +kernel)⟩

theorem take_bad : PredicateQueryAdmission.Valid A label takeRule takeInstruction.observations bad takeSelection := by
  apply (PredicateQueryAdmission.valid_fixed_iff _ _ _ [tokenCensus] _ _).mpr
  exact ⟨take_ready bad.present (by decide), fun query member =>
    (List.mem_singleton.mp member) ▸ (by decide +kernel)⟩

def afterGood := takeSelection.result label takeRule good
def afterBad := takeSelection.result label takeRule bad

theorem publish_good : PredicateQueryAdmission.Valid A label publishRule publishInstruction.observations afterGood publishSelection := by
  apply (PredicateQueryAdmission.valid_fixed_iff _ _ _ [blockerCensus] _ _).mpr
  refine ⟨?_, fun query member => (List.mem_singleton.mp member) ▸ (by decide +kernel)⟩
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨A.identity, ?_⟩
    intro equation member
    change equation ∈ [(token, token)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro check member candidate _
    obtain rfl := List.mem_singleton.mp member
    intro occurrence present
    have impossible : occurrence ∈ (∅ : Finset Nat) := present
    simp at impossible

theorem publish_bad : ¬ publishSelection.Valid A label publishRule afterBad := by
  intro ready
  have solved : A.Models A.identity (publishSelection.problem label publishRule afterBad) := by
    intro equation member
    change equation ∈ [(token, token)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl
  have forbidden := ready.checks (.absent blocker) (List.mem_singleton_self _) A.identity solved 2 (by decide +kernel)
  exact forbidden rfl

theorem good_code_executes : Executable A label good code := by
  refine ⟨take_good, publish_good, ?_⟩
  refine ⟨A.identity, ?_⟩
  intro equation member
  change equation ∈ [(token, token)] at member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem bad_code_is_not_admitted : ¬ Executable A label bad code :=
  fun ready => publish_bad ready.2.1.firing

theorem staged_refusal_keeps_the_token :
    CompiledResult A label (compile label code) bad bad ∧ 0 ∈ bad.present := by
  exact ⟨.inr ⟨fun ready => bad_code_is_not_admitted ((compile_exact A label code bad).mp ready), rfl⟩, by decide⟩

theorem every_nonadmitted_result_has_no_residue (after : Configuration (Term signature) Nat)
    (result : CompiledResult A label (compile label code) bad after) : after = bad :=
  refused_has_no_residue bad_code_is_not_admitted result

/-- This is the eager let-source failure shape: its first public take is
legal, the later source refuses, and the token has already disappeared. -/
theorem eager_public_prefix_loses_the_token :
    takeSelection.Valid A label takeRule bad ∧ ¬ publishSelection.Valid A label publishRule afterBad ∧
      0 ∉ afterBad.present ∧ afterBad ≠ bad := by
  refine ⟨take_bad.firing, publish_bad, by decide +kernel, ?_⟩
  intro same
  have lost : 0 ∉ afterBad.present := by decide +kernel
  exact lost (same.symm ▸ (show 0 ∈ bad.present from by decide))

theorem successful_block_publishes_once :
    CompiledResult A label (compile label code) good
        (ConditionalSchedule.follow label good (code.map Instruction.raw)) ∧
      (ConditionalSchedule.follow label good (code.map Instruction.raw)).present = {1} := by
  exact ⟨(compiled_result_iff_source A label code _ _).mpr (.inl ⟨good_code_executes, rfl⟩), by decide +kernel⟩

/-- The first census is true before the take and false afterward. Keeping
its original cut is required even on this successful staged block. -/
theorem the_original_census_cut_is_required :
    (compile label code).Holds A label good ∧
      ¬ tokenCensus.Holds label (ConditionalSchedule.follow label good (code.map Instruction.raw)).present := by
  exact ⟨(compile_exact A label code good).mpr good_code_executes, by decide +kernel⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StagedSourceEffects.Controls
