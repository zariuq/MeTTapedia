import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.PositiveProfile
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Equations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Removal

/-!
# Activation and footprint controls for the positive profile

A relay can hold received code without executing it. A received positive
rule fires unchanged; a received predicate-checking rule is refused at
activation even on a store where its check would pass. A check of row
syntax alone misses a query of the held rules.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.PositiveProfileControls

open Mettapedia.Logic.LP
open Examples (Tm X E c shift)
open RuleSyntax.Controls (atoms action)

/-- The existing relay still installs and fires a received positive rule.
No special evaluator stands between the two firings. -/
def relayRun :
    (positiveStep (E := E) X Relay.codes (∅ : Set ℕ)).Run (Relay.start 2) :=
  .cons (Relay.relayFiring 2) ⟨Relay.relay_admitted 2, rfl⟩
    (.cons Relay.bumpFiring ⟨Relay.bump_admitted, rfl⟩ (.nil _))

theorem relay_run_result : relayRun.last = Relay.bumpFiring.result X := rfl

/-- Code 2 now asks whether any row labelled 9 is present before making a
row. The relay knows only the received code value, not its body. -/
def predicateRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [], [], [.predicate .none (c 9)], [c 2]⟩, []⟩

def delayedCodes : Codes Tm ℕ Unit :=
  { Relay.codes with
    unfold := fun k => if k = 2 then Spec.ofRule predicateRule else Relay.codes.unfold k }

def install : RFiring ℕ ℕ E delayedCodes (Relay.start 2) :=
  ⟨.held 0, PUnit.unit, shift, ⟨[0], [], []⟩, [], [5], [2], [], []⟩

theorem install_admitted :
    (positiveStep X delayedCodes (∅ : Set ℕ)).Admits install := by
  obtain ⟨shapes, enabled, solvable, asks⟩ := Relay.relay_admitted 2
  change install.Admits X (∅ : Set ℕ) ∧ install.spec.positiveCheck = true
  refine ⟨⟨⟨?_, ?_, ?_⟩, enabled, ?_, ?_⟩, rfl⟩
  · exact shapes.1
  · exact shapes.2.1
  · let old := shapes.2.2
    exact ⟨old.available, old.arguments, old.installed, old.madeNodup, old.madeLength,
      old.madeNew, old.removed, old.removedNodup, old.removedHeld, old.published⟩
  · exact solvable
  · intro b σ solved
    have old := asks b σ solved
    exact ⟨old.1, fun _ member => absurd member List.not_mem_nil,
      old.2.2.1, old.2.2.2.1, old.2.2.2.2⟩

abbrev installed := install.result X

theorem installed_rule_available : 5 ∈ installed.rules :=
  Relay.relayed_mem_rules 2

def activate : RFiring ℕ ℕ E delayedCodes installed :=
  ⟨.held 5, PUnit.unit, Subst.id atoms, ⟨[], [], [7]⟩, [], [], [], [], []⟩

theorem activate_fresh : activate.Fresh X := by
  apply fresh_of_ground action
  intro t tagged σ
  have member : t ∈ predicateRule.terms := by
    have terms : activate.spec.terms = predicateRule.terms :=
      Spec.terms_of_plain (Spec.plain_ofRule predicateRule)
    rwa [terms] at tagged
  simp [predicateRule, Rule.terms, checkTerms] at member
  rcases member with rfl | rfl <;> rfl

/-- The unrestricted activation really is admitted and would produce its
row. Refusal below is due to the profile, not failure of the query. -/
theorem activate_admitted_unrestricted : activate.Admits X (∅ : Set ℕ) := by
  have enabled : MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : ℕ => ())
      installed.present (activate.selection.commit (T := Unit)) := by
    change MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : ℕ => ()) ({1} : Finset ℕ)
      ((⟨[], [], [7]⟩ : Selection ℕ).commit (T := Unit))
    apply enabled_of <;> simp
  refine ⟨⟨activate_fresh, ⟨List.nodup_nil, List.nodup_singleton 7, rfl, rfl, rfl, rfl⟩,
    ⟨installed_rule_available, rfl, rfl, List.nodup_nil, rfl, ?_, rfl, List.nodup_nil, ?_, rfl⟩⟩,
    enabled, ?_, ?_⟩
  · intro ρ made
    exact absurd made List.not_mem_nil
  · intro p removed
    exact absurd removed List.not_mem_nil
  · change X.Solvable [(.var 1, c 102)]
    refine ⟨PUnit.unit, fun _ => c 102, fun e member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro b σ _
    refine ⟨⟨?_, fun _ member => absurd member List.not_mem_nil⟩,
      fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil⟩
    intro guard member
    have shape : guard = .predicate .none (c 9) := List.mem_singleton.mp member
    subst guard
    intro o present
    have same : o = 1 := Finset.mem_singleton.mp present
    subst o
    change c 9 ≠ c 1
    intro impossible
    cases impossible

theorem activate_unrestricted_makes :
    7 ∈ (activate.result X).present ∧ (activate.result X).label 7 = c 2 :=
  ⟨by decide, rfl⟩

theorem activation_refused :
    ¬ (positiveStep X delayedCodes (∅ : Set ℕ)).Admits activate := by
  rintro ⟨_, accepted⟩
  change false = true at accepted
  cases accepted

/-- Even an ordinary positive row body can make a query of the rule store. -/
theorem rule_query_refused :
    Equations.unmatchedFiring.Admits X (∅ : Set Equations.Code) ∧
      Scope.Positive Equations.unmatchedFiring.spec.toRule ∧
        ¬ (positiveStep X Equations.codes (∅ : Set Equations.Code)).Admits
          Equations.unmatchedFiring := by
  refine ⟨Equations.unmatched_admitted, ⟨?_, rfl⟩, ?_⟩
  · intro c member
    exact absurd member List.not_mem_nil
  · rintro ⟨_, accepted⟩
    change false = true at accepted
    cases accepted

/-- A modifying rule may validate on the selected rule identities, but
publishes into the full store: it must leave the unused copy in place. -/
theorem remove_on_support :
    (positiveStep X Removal.codes (∅ : Set ℕ)).Admits (Removal.removeFiring 2 5).onSupport ∧
      6 ∉ (Removal.removeFiring 2 5).ruleSupport ∧
      6 ∈ ((Removal.removeFiring 2 5).result X).rules := by
  refine ⟨(positiveStep_admits_onSupport_iff X _ (Removal.remove_fresh 2 5)).mpr
    ⟨Removal.remove_admitted, rfl⟩, by decide, Removal.other_stays⟩

/-- Adding an unselected row and removing an unused held occurrence
leaves the firing admissible. The full opening is still fresh. -/
theorem remove_after_unrelated_changes :
    (positiveStep X Removal.codes (∅ : Set ℕ)).Admits
      (((Removal.removeFiring 2 5).atPresent {0, 9}).atRules {0, 5}) := by
  have original := Removal.remove_fresh 2 5
  have fresh : (((Removal.removeFiring 2 5).atPresent {0, 9}).atRules {0, 5}).Fresh X := by
    intro b g h
    obtain ⟨u, state, opened⟩ := original b g h
    refine ⟨u, ?_, opened⟩
    intro t member
    apply state t
    rcases member with (left | right | ⟨o, -, rfl⟩) | ⟨ρ, -, argument⟩
    · exact Or.inl (Or.inl left)
    · exact Or.inl (Or.inr (Or.inl right))
    · exact Or.inl (Or.inr (Or.inr ⟨0, Finset.mem_singleton_self 0, rfl⟩))
    · exact absurd argument List.not_mem_nil
  exact (positiveStep_admits_iff_of_sameSupport X _ (by decide) (by decide) original fresh).mpr
    ⟨Removal.remove_admitted, rfl⟩

/-- A proposed output is in the support too: clipping the view cannot
hide the collision with an already present output identity. -/
theorem occupied_output_still_refused :
    ¬ (positiveStep X Relay.codes (∅ : Set ℕ)).Admits
      (Relay.bumpFiring.atPresent {1, 7}).onSupport := by
  rintro ⟨admitted, _⟩
  exact Finset.disjoint_left.mp admitted.2.1.fresh (by decide : 7 ∈ ({7} : Finset ℕ)) (by decide)

#print axioms relay_run_result
#print axioms install_admitted
#print axioms activate_admitted_unrestricted
#print axioms activate_unrestricted_makes
#print axioms activation_refused
#print axioms rule_query_refused
#print axioms remove_on_support
#print axioms remove_after_unrelated_changes
#print axioms occupied_output_still_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.PositiveProfileControls
