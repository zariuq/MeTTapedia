import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalCheckRegions
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.CheckStability
import Mettapedia.Logic.LP.TermEquality

/-!
# Executable first-order licences for universal occurrence observations

The accepted total unifier is a principal answer of the existing equation
store. Certain rows are identical at that answer; potential rows unify after
it. The executable tests below characterize the existing universal checks,
not just one instantiation. Models include unresolved substitutions.

Profile: one finite occurrence store (bag multiplicity), first-order equations,
rules beside the store. The observations apply at the caller's chosen ask
problem; they choose neither guard timing nor a single/bag firing discipline.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence

open Mettapedia.Logic.LP
open PrincipalCheckRegions

variable {signature : LPSignature}
  [DecidableEq signature.vars] [DecidableEq signature.constants]
  [DecidableEq signature.functionSymbols]
  {O : Type} [DecidableEq O]

def certain (answer : Subst signature) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) : Finset O :=
  world.filter fun o => answer.applyTerm pattern = answer.applyTerm (label o)

def potential (answer : Subst signature) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) : Finset O :=
  world.filter fun o =>
    (unifyTotal [(answer.applyTerm pattern, answer.applyTerm (label o))]).isSome = true

theorem solver_isSome_iff (problem : EquationStore (Term signature)) :
    (unifyTotal problem).isSome = true ↔ (FirstOrder.action signature).Consistent problem := by
  cases solved : unifyTotal problem with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
    exact (FirstOrder.refused_iff_inconsistent problem).mp solved
  | some answer =>
    simp only [Option.isSome_some, true_iff]
    exact ⟨answer, unifyTotal_sound problem answer solved⟩

theorem residual_consistent_iff {problem : EquationStore (Term signature)}
    {answer : Subst signature} (accepted : unifyTotal problem = some answer)
    (left right : Term signature) :
    (FirstOrder.action signature).Consistent
        [(answer.applyTerm left, answer.applyTerm right)] ↔
      (FirstOrder.action signature).Consistent (problem ++ [(left, right)]) := by
  let principal := FirstOrder.accepted_principal problem answer accepted
  constructor
  · rintro ⟨residual, solves⟩
    refine ⟨residual.comp answer,
      ((FirstOrder.action signature).models_append _ _ _).mpr
        ⟨principal.extension_models _ residual, ?_⟩⟩
    intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    simpa only [SubstitutionAction.Solves, FirstOrder.action, Subst.applyTerm_comp] using
      solves _ (List.mem_singleton_self _)
  · rintro ⟨candidate, solves⟩
    obtain ⟨old, added⟩ := ((FirstOrder.action signature).models_append _ _ _).mp solves
    obtain ⟨residual, factors⟩ := principal.factors candidate old
    refine ⟨residual, ?_⟩
    intro equation member
    have same := List.mem_singleton.mp member
    subst equation
    have equality := added (left, right) (List.mem_singleton_self _)
    change candidate.applyTerm left = candidate.applyTerm right at equality
    have first : candidate.applyTerm left = residual.applyTerm (answer.applyTerm left) := by
      simpa only [FirstOrder.action, Subst.applyTerm_comp] using factors left
    have second : candidate.applyTerm right = residual.applyTerm (answer.applyTerm right) := by
      simpa only [FirstOrder.action, Subst.applyTerm_comp] using factors right
    exact first.symm.trans (equality.trans second)

omit [DecidableEq O] in
theorem certain_eq_matches (answer : Subst signature) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) :
    certain answer label world pattern =
      Check.matches (FirstOrder.action signature) answer label world pattern := by
  classical
  apply Finset.ext
  intro o
  unfold certain Check.matches
  rw [Finset.mem_filter, Finset.mem_filter]
  rfl

omit [DecidableEq O] in
theorem potential_eq_possible {problem : EquationStore (Term signature)}
    {answer : Subst signature} (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) :
    potential answer label world pattern =
      possibleRegion (FirstOrder.action signature) problem label world pattern := by
  ext o
  simp only [potential, possibleRegion, Finset.mem_filter]
  exact and_congr_right fun _ =>
    (solver_isSome_iff _).trans (residual_consistent_iff accepted pattern (label o))

omit [DecidableEq O] in
theorem certain_subset_potential {problem : EquationStore (Term signature)}
    {answer : Subst signature} (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) :
    certain answer label world pattern ⊆ potential answer label world pattern := by
  rw [certain_eq_matches, potential_eq_possible accepted]
  exact region_subset_possible _ label world pattern
    (FirstOrder.accepted_principal problem answer accepted).sound

theorem equal_iff {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer) (left right : Term signature) :
    (FirstOrder.action signature).Entails problem
        (fun assignment => (FirstOrder.action signature).Solves assignment (left, right)) ↔
      answer.applyTerm left = answer.applyTerm right := by
  exact equal_iff_principal_answer _
    ((FirstOrder.accepted_principal problem answer accepted).on _ [left, right]) left right
    (by simp) (by simp)

omit [DecidableEq O] in
theorem none_iff {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) :
    (FirstOrder.action signature).Entails problem
        (fun assignment => (Check.predicate .none pattern).Holds (FirstOrder.action signature) assignment label world) ↔
      potential answer label world pattern = ∅ := by
  rw [potential_eq_possible accepted]
  exact none_iff_possible_empty _ _ _ _ _

omit [DecidableEq O] in
theorem any_iff {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) :
    (FirstOrder.action signature).Entails problem
        (fun assignment => (Check.predicate .any pattern).Holds (FirstOrder.action signature) assignment label world) ↔
      (certain answer label world pattern).Nonempty := by
  rw [certain_eq_matches]
  exact any_iff_principal_nonempty _
    ((FirstOrder.accepted_principal problem answer accepted).on _ (pattern :: world.toList.map label))
    label world pattern List.mem_cons_self (fun o member =>
      List.mem_cons_of_mem _ (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr member, rfl⟩))

omit [DecidableEq O] in
theorem count_iff {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) (number : Nat) :
    (FirstOrder.action signature).Entails problem
        (fun assignment => (Check.count pattern number).Holds (FirstOrder.action signature) assignment label world) ↔
      (certain answer label world pattern).card = number ∧
        potential answer label world pattern ⊆ certain answer label world pattern := by
  let observed := pattern :: world.toList.map label
  have principal := (FirstOrder.accepted_principal problem answer accepted).on
    (FirstOrder.action signature) observed
  have comparison := count_iff_regions _ principal label world pattern number
    (show pattern ∈ observed by simp [observed])
    (fun o member => List.mem_cons_of_mem _
      (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr member, rfl⟩))
  rw [← certain_eq_matches, ← potential_eq_possible accepted] at comparison
  rw [comparison]
  exact and_congr_right fun _ =>
    ⟨fun same => same.le, fun sub =>
      Finset.Subset.antisymm sub (certain_subset_potential accepted label world pattern)⟩

omit [DecidableEq O] in
theorem collect_iff {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer)
    (label : O → Term signature) (world : Finset O) (pattern : Term signature) (seen : Finset O) :
    (FirstOrder.action signature).Entails problem
        (fun assignment => Check.matches (FirstOrder.action signature) assignment label world pattern = seen) ↔
      certain answer label world pattern = seen ∧
        potential answer label world pattern ⊆ certain answer label world pattern := by
  constructor
  · intro all
    have baseline := all answer (FirstOrder.accepted_principal problem answer accepted).sound
    have counted : (FirstOrder.action signature).Entails problem
        (fun assignment => (Check.count pattern seen.card).Holds
          (FirstOrder.action signature) assignment label world) := by
      intro assignment model
      change (Check.matches _ _ _ _ _).card = seen.card
      rw [all assignment model]
    exact ⟨(certain_eq_matches answer label world pattern).trans baseline,
      ((count_iff accepted label world pattern seen.card).mp counted).2⟩
  · rintro ⟨baseline, possible⟩ assignment model
    let observed := pattern :: world.toList.map label
    have principal := (FirstOrder.accepted_principal problem answer accepted).on
      (FirstOrder.action signature) observed
    have lower := principal_region_subset _ principal label world pattern
      (show pattern ∈ observed by simp [observed])
      (fun o member => List.mem_cons_of_mem _
        (List.mem_map.mpr ⟨o, Finset.mem_toList.mpr member, rfl⟩)) model
    have upper := region_subset_possible (FirstOrder.action signature) label world pattern model
    rw [← potential_eq_possible accepted] at upper
    rw [← certain_eq_matches] at lower
    exact (Finset.Subset.antisymm (upper.trans possible) lower).trans baseline

/-- False means that a check is not entailed, not that every solution refutes it. -/
def check (answer : Subst signature) (label : O → Term signature) (world : Finset O) :
    Check (Term signature) → Bool
  | .equal left right => decide (answer.applyTerm left = answer.applyTerm right)
  | .predicate .any pattern => decide (certain answer label world pattern).Nonempty
  | .predicate .none pattern => decide (potential answer label world pattern = ∅)
  | .count pattern number => decide ((certain answer label world pattern).card = number ∧
      potential answer label world pattern ⊆ certain answer label world pattern)

def collect (answer : Subst signature) (label : O → Term signature) (world : Finset O)
    (pattern : Term signature) (seen : Finset O) : Bool :=
  decide (certain answer label world pattern = seen ∧
    potential answer label world pattern ⊆ certain answer label world pattern)

theorem check_correct {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer) (label : O → Term signature)
    (world : Finset O) (condition : Check (Term signature)) :
    check answer label world condition = true ↔
      (FirstOrder.action signature).Entails problem
        (fun assignment => condition.Holds (FirstOrder.action signature) assignment label world) := by
  cases condition with
  | equal left right => simp only [check, decide_eq_true_eq]; exact (equal_iff accepted left right).symm
  | predicate quantifier pattern =>
      cases quantifier with
      | any => simp only [check, decide_eq_true_eq]; exact (any_iff accepted label world pattern).symm
      | none => simp only [check, decide_eq_true_eq]; exact (none_iff accepted label world pattern).symm
  | count pattern number => simp only [check, decide_eq_true_eq]; exact (count_iff accepted label world pattern number).symm

theorem collect_correct {problem : EquationStore (Term signature)} {answer : Subst signature}
    (accepted : unifyTotal problem = some answer) (label : O → Term signature)
    (world : Finset O) (pattern : Term signature) (seen : Finset O) :
    collect answer label world pattern seen = true ↔
      (FirstOrder.action signature).Entails problem
        (fun assignment => Check.matches (FirstOrder.action signature) assignment label world pattern = seen) := by
  simp only [collect, decide_eq_true_eq]
  exact (collect_iff accepted label world pattern seen).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence
