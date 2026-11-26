import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.CheckAccepts
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.JointFirings.EveryControls

/-!
# Scoped absence and census from ordinary matching

Rigid namespace coordinates yield exactly restriction to a slice of the
entry occurrence store. This gives scoped absence and counting in the
existing rule syntax. Authority to keep that slice stable is a separate
operational property.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ScopedCensus

open OneFrame (Terms frames ext)

section Slice

variable {T S N O : Type*} [DecidableEq N]
  (A : SubstitutionAction T S) (location : O → N) (label : O → T)
  (assignment : S) (present : Finset O) (namespaceId : N) (pattern : T)

theorem tagged_matches :
    matchesAt (frames (LocatedSubstitution.action A)) (a := PUnit.unit) (b := PUnit.unit)
      assignment (fun o => (location o, label o)) present (namespaceId, pattern) =
    matchesAt (frames A) (a := PUnit.unit) (b := PUnit.unit)
      assignment label (present.filter fun o => namespaceId = location o) pattern := by
  ext o
  rw [mem_matchesAt, mem_matchesAt, Finset.mem_filter]
  change (o ∈ present ∧ namespaceId = location o ∧ A.E (A.apply assignment pattern)
    (A.apply assignment (label o))) ↔
    (o ∈ present ∧ namespaceId = location o) ∧ A.E (A.apply assignment pattern)
      (A.apply assignment (label o))
  exact and_assoc.symm

theorem tagged_count (number : ℕ) :
    checkHolds (frames (LocatedSubstitution.action A)) (a := PUnit.unit) (b := PUnit.unit)
      assignment (fun o => (location o, label o)) present (.count (namespaceId, pattern) number) ↔
    checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit)
      assignment label (present.filter fun o => namespaceId = location o) (.count pattern number) := by
  simp only [checkHolds]
  rw [tagged_matches]

theorem tagged_predicate (quantifier : Quantifier) :
    checkHolds (frames (LocatedSubstitution.action A)) (a := PUnit.unit) (b := PUnit.unit)
      assignment (fun o => (location o, label o)) present (.predicate quantifier (namespaceId, pattern)) ↔
    checkHolds (frames A) (a := PUnit.unit) (b := PUnit.unit)
      assignment label (present.filter fun o => namespaceId = location o) (.predicate quantifier pattern) := by
  rw [checkHolds_predicate_iff, checkHolds_predicate_iff, tagged_matches]

end Slice

section Controls

open Mettapedia.Logic.LP
open Examples (c)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

private abbrev Value := Bool × Term atoms
private abbrev A : SubstitutionAction Value (Subst atoms) := LocatedSubstitution.action action
private abbrev X := frames A
private abbrev E := ext A

private def location (o : ℕ) : Bool := o != 0

private def world (present : Finset ℕ) : State (Terms Value) ℕ :=
  ⟨PUnit.unit, [], present, fun o => (location o, c 1)⟩

private def announce (checks : List (Check Value)) : Rule (Terms Value) :=
  ⟨PUnit.unit, ⟨[], [], [], checks, [(true, c 2)]⟩, []⟩

private def announcement (checks : List (Check Value)) :
    Firing ℕ E ({announce checks} : Program (Terms Value)) PUnit.unit :=
  ⟨announce checks, rfl, PUnit.unit, Subst.id atoms, ⟨[], [], [2]⟩, []⟩

private def absent : Check Value := .predicate .none (true, c 1)
private def census : Check Value := .count (true, c 1) 0

private theorem matches_one (σ : Subst atoms) (present : Finset ℕ) :
    matchesAt X (a := PUnit.unit) (b := PUnit.unit) σ ((world present).label) present (true, c 1) =
      present.filter (fun o => true = location o) := by
  ext o
  rw [mem_matchesAt, Finset.mem_filter]
  constructor
  · rintro ⟨live, matched, _⟩
    exact ⟨live, matched⟩
  · rintro ⟨live, matched⟩
    exact ⟨live, matched, action.equivalence.refl _⟩

private theorem opened_identity (check : Check Value) :
    Check.map (A.apply (Subst.id atoms)) check = check := by
  have fixed (t : Value) : A.apply (Subst.id atoms) t = t := A.apply_identity t
  cases check <;> simp only [Check.map, fixed]

private theorem rows_identity (checks : List (Check Value)) (present : Finset ℕ) :
    (announcement checks).row X (world present) = (world present).label := by
  funext o
  exact A.apply_identity _

private theorem permitted (check : Check Value) (ground : ∀ t ∈ checkTerms check, ∀ σ, A.apply σ t = t)
    (holds : ∀ σ : Subst atoms,
      checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ ((world {0}).label) {0} check) :
    (announcement [check]).Admits X (world {0}) := by
  have groundRule : ∀ t ∈ (announce [check]).terms, ∀ σ : Subst atoms, A.apply σ t = t := by
    intro t member σ
    have declared : t ∈ checkTerms check ++ [(true, c 2)] := by
      simpa [announce, Rule.terms] using member
    rcases List.mem_append.mp declared with inCheck | output
    · exact ground t inCheck σ
    · rw [List.mem_singleton.mp output]
      rfl
  refine ⟨⟨Examples.fresh_of_ground A _ _ groundRule, List.nodup_nil, List.nodup_singleton 2,
    rfl, rfl, rfl, rfl⟩, ⟨?_, ?_, ?_, ?_, ?_⟩,
    ⟨PUnit.unit, Subst.id atoms, fun _ member => absurd member List.not_mem_nil⟩, ?_⟩
  · exact Finset.empty_subset _
  · exact Finset.empty_subset _
  · exact Finset.disjoint_empty_left _
  · change Disjoint ({2} : Finset Nat) {0}
    decide
  · intro query member
    exact absurd member List.not_mem_nil
  · intro b σ _
    cases b
    refine ⟨fun opened inChecks => ?_, fun _ impossible => absurd impossible List.not_mem_nil⟩
    have listed : opened ∈ [Check.map (A.apply (Subst.id atoms)) check] := inChecks
    rw [List.mem_singleton.mp listed]
    rw [opened_identity, rows_identity]
    exact holds σ

private theorem refused (check : Check Value)
    (bad : ∀ σ : Subst atoms,
      ¬ checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ ((world {0, 1}).label) {0, 1} check) :
    ¬ (announcement [check]).Admits X (world {0, 1}) := by
  intro accepted
  obtain ⟨b, σ, model⟩ := accepted.2.2.1
  cases b
  apply bad σ
  have checked := (accepted.2.2.2 PUnit.unit σ model).1
  have inChecks : check ∈ ((announcement [check]).opened X).checks := by
    change check ∈ [Check.map (A.apply (Subst.id atoms)) check]
    simp [opened_identity]
  have had := checked check inChecks
  rw [rows_identity] at had
  exact had

/-- Both checks accept a row outside the queried namespace and refuse a
row with identical payload inside it. The successful firings publish. -/
theorem real_scoped_guards :
    ((announcement [absent]).Admits X (world {0}) ∧
      (announcement [census]).Admits X (world {0})) ∧
    ¬ (announcement [absent]).Admits X (world {0, 1}) ∧
    ¬ (announcement [census]).Admits X (world {0, 1}) := by
  have clear (σ : Subst atoms) :
      checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ (world {0}).label {0} census := by
    change (matchesAt X σ (world {0}).label {0} (true, c 1)).card = 0
    rw [matches_one]
    decide
  have blocked (σ : Subst atoms) :
      ¬ checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ (world {0, 1}).label {0, 1} census := by
    change (matchesAt X σ (world {0, 1}).label {0, 1} (true, c 1)).card ≠ 0
    rw [matches_one]
    decide
  have same (σ : Subst atoms) (present : Finset ℕ) :
      checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ (world present).label present absent ↔
      checkHolds X (a := PUnit.unit) (b := PUnit.unit) σ (world present).label present census :=
    none_iff_count_zero X σ _ _ _
  have ground (check : Check Value) (equal : checkTerms check = [(true, c 1)]) :
      ∀ term ∈ checkTerms check, ∀ σ : Subst atoms, A.apply σ term = term := by
    intro term member σ
    rw [equal, List.mem_singleton] at member
    subst term
    rfl
  exact ⟨⟨permitted absent (ground _ rfl) (fun σ => (same σ _).mpr (clear σ)),
      permitted census (ground _ rfl) clear⟩,
    refused absent (fun σ found => blocked σ ((same σ _).mp found)),
    refused census blocked⟩

end Controls

#print axioms tagged_matches
#print axioms tagged_count
#print axioms tagged_predicate
#print axioms real_scoped_guards

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ScopedCensus
