import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderEq
import Mettapedia.Logic.LP.UnificationRenaming
import Mettapedia.Logic.LP.TermEquality

/-!
# A first-order set-store step

A normalized state retains one copy of each resolved row, with variable
sharing intact. A candidate uses the existing rule-syntax admission over a
duplicate-free occurrence presentation. Its result is the independently
defined finite-set update, not the occurrence allocator's result. The bridge
proves that these results agree after the checked principal substitution.
Unchanged states, including consistent renamings of unknowns, are not steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open JointFirings

variable {signature : LPSignature} [DecidableEq signature.vars]
  [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]

abbrev A := FirstOrder.action signature
abbrev X := frames (A (signature := signature))
abbrev Rows (signature : LPSignature) := Finset (Term signature)

/-- A row reading chooses one solution globally, preserving cross-row aliases. -/
def readings (problem : EquationStore (Term signature)) (rows : Rows signature) : Set (Rows signature) :=
  {values | ∃ assignment : Subst signature, A.Models assignment problem ∧
    values = rows.image assignment.applyTerm}

/-- Erasing solved knowledge retains exactly the possible row readings. -/
theorem readings_normalize (problem : EquationStore (Term signature)) (rows : Rows signature)
    (answer : Subst signature) (accepted : unifyTotal problem = some answer) :
    readings problem rows = readings [] (rows.image answer.applyTerm) := by
  ext values
  constructor
  · rintro ⟨assignment, solves, rfl⟩
    obtain ⟨residual, factors⟩ := (FirstOrder.accepted_principal problem answer accepted).factors assignment solves
    refine ⟨residual, SubstitutionAction.models_nil A residual, ?_⟩
    rw [Finset.image_image]
    apply Finset.image_congr
    intro value _
    have factor : assignment.applyTerm value = (residual.comp answer).applyTerm value := factors value
    exact factor.trans (Subst.applyTerm_comp residual answer value)
  · rintro ⟨residual, _, rfl⟩
    refine ⟨residual.comp answer,
      SubstitutionAction.models_compose A (FirstOrder.accepted_principal problem answer accepted).sound residual, ?_⟩
    rw [Finset.image_image]
    apply Finset.image_congr
    intro value _
    exact (Subst.applyTerm_comp residual answer value).symm

/-- Only names change; aliases inside and across rows are unchanged. -/
def SameRows (first second : Rows signature) : Prop :=
  ∃ names : Equiv.Perm signature.vars,
    second = first.image (UnificationRenaming.rename names)

theorem sameRows_refl (rows : Rows signature) : SameRows rows rows := by
  refine ⟨Equiv.refl _, ?_⟩
  have identity : UnificationRenaming.rename (id : signature.vars → signature.vars) = id :=
    funext UnificationRenaming.rename_id
  simp only [Equiv.coe_refl, identity, Finset.image_id]

theorem sameRows_symm {first second : Rows signature} (same : SameRows first second) :
    SameRows second first := by
  obtain ⟨names, rfl⟩ := same
  refine ⟨names.symm, ?_⟩
  rw [Finset.image_image]
  have undo : (UnificationRenaming.rename names.symm ∘ UnificationRenaming.rename names) = id := by
    funext value
    exact UnificationRenaming.rename_leftInverse names names.symm names.symm_apply_apply value
  rw [undo, Finset.image_id]

theorem sameRows_trans {first second third : Rows signature}
    (one : SameRows first second) (two : SameRows second third) : SameRows first third := by
  obtain ⟨names, rfl⟩ := one
  obtain ⟨later, rfl⟩ := two
  refine ⟨names.trans later, ?_⟩
  rw [Finset.image_image]
  apply Finset.image_congr
  intro value _
  exact UnificationRenaming.rename_comp names later value

def rowsSetoid (signature : LPSignature) [DecidableEq signature.vars]
    [DecidableEq signature.constants] [DecidableEq signature.functionSymbols] : Setoid (Rows signature) where
  r := SameRows
  iseqv := ⟨sameRows_refl, sameRows_symm, sameRows_trans⟩

/-- Distinct rows have distinct source memberships; generations are fresh output addresses. -/
def represent (rows : Rows signature) : State (Terms (Term signature)) (Term signature × ℕ) :=
  ⟨PUnit.unit, [], rows.image (fun value => (value, 0)), Prod.fst⟩

theorem represent_distinct (rows : Rows signature) :
    Set.InjOn (represent rows).label ((represent rows).present : Set (Term signature × ℕ)) := by
  rintro left insideLeft right insideRight equal
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp insideLeft
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp insideRight
  exact congrArg (fun value : Term signature => (value, 0)) equal

theorem represent_support (rows : Rows signature) :
    (represent rows).present.image (represent rows).label = rows := by
  simp only [represent, Finset.image_image, Function.comp_def, Finset.image_id']

inductive AskTiming where
  | afterTells
  | beforeTells

variable {P : Program (Terms (Term signature))}

abbrev Candidate (P : Program (Terms (Term signature))) :=
  Bag (Term signature × ℕ) (ext (A (signature := signature))) P PUnit.unit

def admitted (timing : AskTiming) (rows : Rows signature) (candidate : Candidate P) : Prop :=
  match timing with
  | .afterTells => candidate.Admits X (represent rows)
  | .beforeTells => candidate.AdmitsBeforeTells X (represent rows)

theorem admitted_after {timing : AskTiming} {rows : Rows signature} {candidate : Candidate P}
    (yes : admitted timing rows candidate) : candidate.Admits X (represent rows) := by
  cases timing with
  | afterTells => exact yes
  | beforeTells => exact Bag.admits_of_beforeTells X (represent rows) candidate yes

/-- Remove source memberships before solving; a tell may identify survivors with a taken value. -/
def setResult (rows : Rows signature) (candidate : Candidate P) (answer : Subst signature) : Rows signature :=
  update answer.applyTerm rows (candidate.selection.taken.toFinset.image Prod.fst)
    ((candidate.produce X).toFinset.image answer.applyTerm)

theorem setResult_eq_occurrence_support (rows : Rows signature) (candidate : Candidate P)
    (yes : candidate.Admits X (represent rows)) (answer : Subst signature) :
    setResult rows candidate answer = support X (a := PUnit.unit) (candidate.result X (represent rows)) answer := by
  have bridge := support_result_set_update X (a := PUnit.unit) (represent rows) candidate yes (represent_distinct rows) answer
  rw [represent_support] at bridge
  change support X (a := PUnit.unit) (candidate.result X (represent rows)) answer =
    update (fun value => answer.applyTerm ((Subst.id signature).applyTerm value)) rows
      (candidate.selection.taken.toFinset.image Prod.fst)
      ((candidate.produce X).toFinset.image answer.applyTerm) at bridge
  simpa only [setResult, Subst.applyTerm_id] using bridge.symm

def Step (timing : AskTiming) (P : Program (Terms (Term signature)))
    (rows after : Rows signature) : Prop :=
  ∃ candidate : Candidate P, candidate.members ≠ [] ∧ admitted timing rows candidate ∧
    ∃ answer : Subst signature,
      unifyTotal (candidate.information X (represent rows)) = some answer ∧
      after = setResult rows candidate answer ∧ ¬ SameRows rows after

/-- The correspondence is derived from relabelling and source injectivity, not a definition. -/
theorem step_iff_occurrence (timing : AskTiming) (P : Program (Terms (Term signature)))
    (rows after : Rows signature) :
    Step timing P rows after ↔
      ∃ candidate : Candidate P, candidate.members ≠ [] ∧ admitted timing rows candidate ∧
        ∃ answer : Subst signature,
          unifyTotal (candidate.information X (represent rows)) = some answer ∧
          after = support X (a := PUnit.unit) (candidate.result X (represent rows)) answer ∧ ¬ SameRows rows after := by
  constructor
  · rintro ⟨candidate, nonempty, yes, answer, accepted, rfl, changed⟩
    exact ⟨candidate, nonempty, yes, answer, accepted,
      setResult_eq_occurrence_support rows candidate (admitted_after yes) answer, changed⟩
  · rintro ⟨candidate, nonempty, yes, answer, accepted, result, changed⟩
    refine ⟨candidate, nonempty, yes, answer, accepted, ?_, changed⟩
    exact result.trans (setResult_eq_occurrence_support rows candidate (admitted_after yes) answer).symm

theorem before_step_is_after {rows after : Rows signature}
    (step : Step .beforeTells P rows after) : Step .afterTells P rows after := by
  obtain ⟨candidate, nonempty, yes, answer, accepted, result, changed⟩ := step
  exact ⟨candidate, nonempty, admitted_after yes, answer, accepted, result, changed⟩

theorem unchanged_is_not_step {timing : AskTiming} {rows after : Rows signature}
    (same : SameRows rows after) : ¬ Step timing P rows after := by
  rintro ⟨_, _, _, _, _, _, changed⟩
  exact changed same

theorem self_is_not_step (timing : AskTiming) (rows : Rows signature) : ¬ Step timing P rows rows :=
  unchanged_is_not_step (sameRows_refl rows)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SetStore
