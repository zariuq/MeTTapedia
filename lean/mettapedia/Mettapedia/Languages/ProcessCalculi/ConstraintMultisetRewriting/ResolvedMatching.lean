import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipts

/-!
# Resolving a constraint firing into the existing matching semantics

At every solution of a constraint firing, the resolved patterns,
surviving frame and outputs form an actual firing of the existing occurrence
and matching engine. The ordered occurrence choices are preserved exactly.

This is an observation theorem for resolved instances. It does not identify
an unbound caller's raw frame with its resolved frame, nor turn a family of
ground instances into a universally justified derived rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedMatching

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-- Literal patterns at a resolved observation have no schematic holes. -/
def literalLayer (A : SubstitutionAction T S) : TermLayer Empty T T where
  E := A.E
  equivalence := A.equivalence
  vars := fun _ => ∅
  inst := fun _ term => some term
  inst_bound := by simp
  inst_local := by intros; rfl
  inst_congr := fun _ _ term _ => .some (A.equivalence.refl term)

def assignment : Subst Empty T := fun v => nomatch v

def resolvedCheck (A : SubstitutionAction T S) (σ : S) : Check T →
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Check Empty T T
  | .equal left right => ⟨A.apply σ left,
      fun _ _ => A.E (A.apply σ left) (A.apply σ right)⟩
  | .absent pattern =>
      Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Check.absent (A.apply σ pattern)
  | .count pattern n =>
      Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Check.count (A.apply σ pattern) n

def resolvedRule (A : SubstitutionAction T S) (σ : S) (rule : RuleInstance T) :
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Rule Empty T T :=
  ⟨rule.take.map (A.apply σ), rule.read.map (A.apply σ), rule.checks.map (resolvedCheck A σ),
    rule.produce.map (A.apply σ)⟩

noncomputable def receipt (A : SubstitutionAction T S) (σ : S) (label : O → T)
    (before : Configuration T O) (rule : RuleInstance T) (selection : Selection O) :
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipt O Empty T :=
  ⟨assignment, selection.taken, selection.read, selection.made,
    rule.checks.map fun check => Check.matches A σ label before.present check.pattern⟩

private theorem literal_covers (A : SubstitutionAction T S) (pattern value : T) :
    (literalLayer A).Covers assignment pattern value ↔ A.E pattern value := by
  constructor
  · rintro ⟨_, step⟩
    obtain ⟨resolved, equal, related⟩ := step.solves
    have same : pattern = resolved := Option.some.inj equal
    exact same ▸ related
  · intro related
    refine ⟨assignment, ?_, ?_, pattern, rfl, related⟩
    · intro v
      cases v
    · intro v
      cases v

omit [DecidableEq O] in
theorem resolved_region (A : SubstitutionAction T S) (σ : S) (label : O → T)
    (store : Finset O) (pattern : T) :
    regionOf (fun o => A.apply σ (label o)) store
      (semRegion (literalLayer A) assignment (A.apply σ pattern)) =
      Check.matches A σ label store pattern := by
  classical
  ext o
  simp only [mem_regionOf, semRegion_eq_true, literal_covers, Check.matches, Finset.mem_filter]

omit [DecidableEq O] in
private theorem check_observation (A : SubstitutionAction T S) (σ : S) (label : O → T)
    (store : Finset O) (check : Check T) (holds : check.Holds A σ label store) :
    (⟨semRegion (literalLayer A) assignment (resolvedCheck A σ check).pattern,
      Check.matches A σ label store check.pattern⟩ : PredicateQuery O T).Holds
        (fun o => A.apply σ (label o)) store ∧
      (resolvedCheck A σ check).holds assignment
        (labels (fun o => A.apply σ (label o)) (Check.matches A σ label store check.pattern)) := by
  classical
  constructor
  · change regionOf _ _ _ = _
    have patternEq : (resolvedCheck A σ check).pattern = A.apply σ check.pattern := by
      cases check <;> rfl
    rw [patternEq, resolved_region]
  · cases check with
    | equal _ _ => exact holds
    | absent pattern =>
      have empty : Check.matches A σ label store pattern = ∅ := by
        ext o
        simp only [Finset.notMem_empty, iff_false]
        intro member
        have split := Finset.mem_filter.mp member
        exact holds o split.1 split.2
      change labels _ (Check.matches A σ label store pattern) = 0
      rw [empty]
      rfl
    | count pattern n =>
      change Multiset.card (labels _ (Check.matches A σ label store pattern)) = n
      change (Check.matches A σ label store pattern).card = n at holds
      simpa only [labels, Multiset.card_map, Finset.card_def] using holds

omit [DecidableEq O] in
private theorem check_observations (A : SubstitutionAction T S) (σ : S) (label : O → T)
    (store : Finset O) (checks : List (Check T))
    (holds : ∀ check ∈ checks, check.Holds A σ label store) :
    List.Forall₂ (fun check seen =>
      (⟨semRegion (literalLayer A) assignment check.pattern, seen⟩ : PredicateQuery O T).Holds
        (fun o => A.apply σ (label o)) store ∧
        check.holds assignment (labels (fun o => A.apply σ (label o)) seen))
      (checks.map (resolvedCheck A σ))
      (checks.map fun check => Check.matches A σ label store check.pattern) := by
  induction checks with
  | nil => exact .nil
  | cons check rest ih =>
    exact .cons (check_observation A σ label store check (holds check (by simp)))
      (ih fun c member => holds c (by simp [member]))

omit [DecidableEq O] in
private theorem resolved_matches (A : SubstitutionAction T S) (σ : S) (label : O → T)
    {patterns : List T} {selected : List O}
    (solved : List.Forall₂ (fun p o => A.E (A.apply σ p) (A.apply σ (label o)))
      patterns selected) :
    List.Forall₂ ((literalLayer A).Solves assignment)
      (patterns.map (A.apply σ)) (selected.map (fun o => A.apply σ (label o))) := by
  induction solved with
  | nil => exact .nil
  | cons head _ ih => exact .cons ⟨_, rfl, head⟩ ih

private theorem literal_instTemplate (A : SubstitutionAction T S) (terms : List T) :
    instTemplate (literalLayer A) assignment terms = some terms := by
  change terms.mapM (pure (f := Option)) = some terms
  simpa using (List.mapM_pure (m := Option) (l := terms) (f := id))

/-- The same receipt witnesses the original matching engine's step, after
resolving every term in the shared configuration with the chosen solution. -/
theorem valid_receipt (A : SubstitutionAction T S) {σ : S}
    {selection : Selection O} {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} (valid : selection.Valid A label rule before)
    (solved : A.Models σ (selection.problem label rule before))
    :
    (receipt A σ label before rule selection).ValidAt (literalLayer A) (resolvedRule A σ rule)
      (fun o => A.apply σ (label o)) before.present := by
  obtain ⟨_, takes, reads, _⟩ := Selection.models_problem A valid solved
  refine ⟨valid.take_distinct, valid.output_distinct, valid.occurrences.taken_subset,
    valid.occurrences.kept_subset, valid.occurrences.apart, valid.occurrences.fresh,
    ?_, resolved_matches A σ label takes, resolved_matches A σ label reads, ?_, ?_⟩
  · intro v
    cases v
  · change instTemplate (literalLayer A) assignment (rule.produce.map (A.apply σ)) =
      some (selection.made.map (fun o => A.apply σ (label o)))
    rw [literal_instTemplate, ← valid.outputs]
    simp only [List.map_map, Function.comp_def]
  · exact check_observations A σ label before.present rule.checks
      (fun check member => valid.checks check member σ solved)

theorem resolved_step (A : SubstitutionAction T S) [DecidableEq T] {σ : S}
    {selection : Selection O} {label : O → T} {rule : RuleInstance T}
    {before : Configuration T O} (valid : selection.Valid A label rule before)
    (solved : A.Models σ (selection.problem label rule before))
    :
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Step
      (literalLayer A) (resolvedRule A σ rule)
      (labels (fun o => A.apply σ (label o)) before.present)
      (labels (fun o => A.apply σ (label o)) (selection.result label rule before).present) := by
  have core := (valid_receipt A valid solved).step
  simpa only [receipt, resolvedRule,
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipt.commit,
    Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.FiringReceipt.queries,
    Selection.result, Selection.commit, fire] using core

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ResolvedMatching
