import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.IssuedNames
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Names on the first-order step

For any substitution action and any assignment of generative names to terms, the first-order
instance of the step has a local naming (`firstOrderMentions`):

* a configuration mentions the names of its equations and of the labels of its present occurrences
  (`configurationNames`);
* a firing writes the names of its take and read patterns, its tells and its produced terms
  (`firingNames`). Take and read patterns are writes: their equations with the selected labels enter
  the knowledge. Checks and predicate queries are not: they add nothing to the result.

Locality holds without any hypothesis on the action: the result's knowledge is the firing's problem
and its store is the fired store, so every name in the result comes from the configuration, from the
firing's own terms, or from the label of an occurrence it selected, which was present
(`firstOrder_result_subset`). The issuing theory of `IssuedNames` therefore applies to the
first-order step with every action, ground or not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep

open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

universe uT uS uO uN

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {N : Type uN}

section Names

variable (label : O → T) (names : T → Set N)

/-- The names a configuration mentions: in its equations and in its present labels. -/
def configurationNames (C : Configuration T O) : Set N :=
  {n | (∃ e ∈ C.equations, n ∈ names e.1 ∨ n ∈ names e.2) ∨ ∃ o ∈ C.present, n ∈ names (label o)}

/-- The names a firing writes: its take and read patterns, its tells and its produced terms. -/
def firingNames (f : AnnotatedRuns.Firing T S O) : Set N :=
  {n | (∃ t ∈ f.rule.take, n ∈ names t) ∨ (∃ t ∈ f.rule.read, n ∈ names t) ∨
    (∃ e ∈ f.rule.tell, n ∈ names e.1 ∨ n ∈ names e.2) ∨ ∃ t ∈ f.rule.produce, n ∈ names t}

variable {label names}

omit [DecidableEq O] in
theorem mem_configurationNames {C : Configuration T O} {n : N} :
    n ∈ configurationNames label names C ↔
      (∃ e ∈ C.equations, n ∈ names e.1 ∨ n ∈ names e.2) ∨ ∃ o ∈ C.present, n ∈ names (label o) :=
  Iff.rfl

omit [DecidableEq O] in
theorem mem_firingNames {f : AnnotatedRuns.Firing T S O} {n : N} :
    n ∈ firingNames names f ↔
      (∃ t ∈ f.rule.take, n ∈ names t) ∨ (∃ t ∈ f.rule.read, n ∈ names t) ∨
        (∃ e ∈ f.rule.tell, n ∈ names e.1 ∨ n ∈ names e.2) ∨ ∃ t ∈ f.rule.produce, n ∈ names t :=
  Iff.rfl

end Names

omit [DecidableEq O] in
/-- An equation of a selection pairs a pattern with the label of a selected occurrence. -/
theorem mem_selection_equations {label : O → T} :
    ∀ {patterns : List T} {selected : List O} {e : Equation T},
      e ∈ Selection.equations label patterns selected → e.1 ∈ patterns ∧ ∃ o ∈ selected, e.2 = label o
  | [], _, _, member => by simp [Selection.equations] at member
  | _ :: _, [], _, member => by simp [Selection.equations] at member
  | p :: ps, o :: os, e, member => by
      simp only [Selection.equations, List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with here | later
      · subst here
        exact ⟨List.mem_cons.mpr (Or.inl rfl), o, List.mem_cons.mpr (Or.inl rfl), rfl⟩
      · obtain ⟨inPatterns, o', inSelected, same⟩ :=
          mem_selection_equations (label := label) (patterns := ps) (selected := os) later
        exact ⟨List.mem_cons.mpr (Or.inr inPatterns), o', List.mem_cons.mpr (Or.inr inSelected), same⟩

/-- **Locality of the first-order step**: an admitted firing's result mentions only names of its
configuration or of the firing's writes. No hypothesis on the action. -/
theorem firstOrder_result_subset (A : SubstitutionAction T S) (label : O → T) (names : T → Set N)
    {C : Configuration T O} (f : AnnotatedRuns.Firing T S O)
    (admitted : (AnnotatedRuns.firstOrder A label).Admits (s := C) f) :
    configurationNames label names (f.result label C) ⊆
      configurationNames label names C ∪ firingNames names f := by
  have valid : f.selection.Valid A label f.rule C := admitted.firing
  intro n mentioned
  have taken_present : ∀ o ∈ f.selection.taken, o ∈ C.present := fun o member =>
    valid.occurrences.taken_subset (show o ∈ f.selection.taken.toFinset from List.mem_toFinset.mpr member)
  have read_present : ∀ o ∈ f.selection.read, o ∈ C.present := fun o member =>
    valid.occurrences.kept_subset (show o ∈ f.selection.read.toFinset from List.mem_toFinset.mpr member)
  have fromStore : ∀ o ∈ C.present, n ∈ names (label o) →
      n ∈ configurationNames label names C ∪ firingNames names f := fun o present named =>
    Set.mem_union_left _ (mem_configurationNames.mpr (Or.inr ⟨o, present, named⟩))
  rcases (mem_configurationNames.mp mentioned) with ⟨e, member, named⟩ | ⟨o, present, named⟩
  · change e ∈ f.selection.problem label f.rule C at member
    simp only [Selection.problem, List.mem_append] at member
    rcases member with ((old | taken) | read) | told
    · exact Set.mem_union_left _ (mem_configurationNames.mpr (Or.inl ⟨e, old, named⟩))
    · obtain ⟨pattern, o, inTaken, same⟩ := mem_selection_equations taken
      rcases named with first | second
      · exact Set.mem_union_right _ (mem_firingNames.mpr (Or.inl ⟨e.1, pattern, first⟩))
      · rw [same] at second
        exact fromStore o (taken_present o inTaken) second
    · obtain ⟨pattern, o, inRead, same⟩ := mem_selection_equations read
      rcases named with first | second
      · exact Set.mem_union_right _ (mem_firingNames.mpr (Or.inr (Or.inl ⟨e.1, pattern, first⟩)))
      · rw [same] at second
        exact fromStore o (read_present o inRead) second
    · exact Set.mem_union_right _ (mem_firingNames.mpr (Or.inr (Or.inr (Or.inl ⟨e, told, named⟩))))
  · change o ∈ fire C.present (f.selection.commit (T := T)) at present
    rcases mem_fire.mp present with ⟨old, _⟩ | made
    · exact fromStore o old named
    · have produced : label o ∈ f.rule.produce := by
        rw [← valid.outputs]
        exact List.mem_map_of_mem (List.mem_toFinset.mp made)
      exact Set.mem_union_right _
        (mem_firingNames.mpr (Or.inr (Or.inr (Or.inr ⟨label o, produced, named⟩))))

/-- **The first-order step's naming**, for any action and any names of terms. -/
def firstOrderMentions (A : SubstitutionAction T S) (label : O → T) (names : T → Set N) :
    Mentions (AnnotatedRuns.firstOrder A label).toStep N where
  state := configurationNames label names
  firing := fun f => firingNames names f
  result_subset := fun f admitted => firstOrder_result_subset A label names f admitted

theorem firstOrder_result (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    (f : AnnotatedRuns.Firing T S O) (admitted : (AnnotatedRuns.firstOrder A label).toStep.Admits (s := C) f) :
    (AnnotatedRuns.firstOrder A label).toStep.result f admitted = f.result label C := rfl

#print axioms firstOrder_result_subset
#print axioms firstOrderMentions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep
