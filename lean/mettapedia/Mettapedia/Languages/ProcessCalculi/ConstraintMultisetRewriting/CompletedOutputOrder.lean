import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InteractionFormation

/-!
# Completed publication preserves its result under output rotation

The ordinary CMR step publishes a bag of fresh physical occurrences. Moving
the first output to the end, with its actual made occurrence, preserves the
equations, physical commit, rights and complete result. This theorem says
nothing about an implementation's partially executed output prefixes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompletedOutputOrder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO uN
variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN} [DecidableEq O]

def firstLast {A : Type*} : List A → List A
  | [] => []
  | first :: rest => rest ++ [first]

theorem firstLast_perm {A : Type*} (items : List A) : items.Perm (firstLast items) := by
  cases items with
  | nil => exact List.Perm.refl []
  | cons first rest => exact @List.perm_append_comm A [first] rest

theorem map_firstLast {A B : Type*} (function : A → B) (items : List A) :
    (firstLast items).map function = firstLast (items.map function) := by
  cases items <;> simp [firstLast]

def rotateRule (rule : RuleInstance T) : RuleInstance T :=
  { rule with produce := firstLast rule.produce }

def rotateSelection (picked : Selection O) : Selection O :=
  { picked with made := firstLast picked.made }

theorem commit_unchanged (picked : Selection O) :
    (rotateSelection picked).commit (T := T) = picked.commit := by
  have same : (firstLast picked.made).toFinset = picked.made.toFinset := by
    apply Finset.ext
    intro occurrence
    simp only [List.mem_toFinset]
    exact (firstLast_perm picked.made).mem_iff.symm
  simp only [rotateSelection, Selection.commit, same]

omit [DecidableEq O] in
theorem problem_unchanged (picked : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) :
    (rotateSelection picked).problem label (rotateRule rule) before =
      picked.problem label rule before := rfl

theorem result_unchanged (picked : Selection O) (label : O → T)
    (rule : RuleInstance T) (before : Configuration T O) :
    (rotateSelection picked).result label (rotateRule rule) before =
      picked.result label rule before := by
  simp only [Selection.result, problem_unchanged, commit_unchanged]

/-- This acts on the actual selected output occurrences, not merely on labels
after forgetting duplicate or occurrence identity information. -/
theorem valid_rotates {action : SubstitutionAction T S} {picked : Selection O}
    {label : O → T} {rule : RuleInstance T} {before : Configuration T O}
    (valid : picked.Valid action label rule before) :
    (rotateSelection picked).Valid action label (rotateRule rule) before where
  take_distinct := valid.take_distinct
  output_distinct := (firstLast_perm picked.made).nodup_iff.mp valid.output_distinct
  take_length := valid.take_length
  read_length := valid.read_length
  outputs := by
    change (firstLast picked.made).map label = firstLast rule.produce
    rw [map_firstLast, valid.outputs]
  occurrences := by simpa only [commit_unchanged] using valid.occurrences
  consistent := valid.consistent
  checks := valid.checks

theorem step_rotates {action : SubstitutionAction T S} {label : O → T}
    {rule : RuleInstance T} {before after : Configuration T O}
    (stepped : Step action label rule before after) :
    Step action label (rotateRule rule) before after := by
  obtain ⟨picked, valid, rfl⟩ := stepped
  exact ⟨rotateSelection picked, valid_rotates valid, (result_unchanged picked label rule before).symm⟩

theorem formation_rotates
    {rights : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Rights N}
    {label : O → N × T} {picked : Selection O} {rule : RuleInstance (N × T)}
    (formed : InteractionFormation.Formed rights label picked rule) :
    InteractionFormation.Formed rights label (rotateSelection picked) (rotateRule rule) where
  physical := by simpa only [commit_unchanged] using formed.physical
  observations := formed.observations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CompletedOutputOrder
