import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.RowLocality

/-!
# What a firing reads of the rules a state holds

Change which identities a state holds, the labels staying as they are (`RState.withRules`). A firing
admitted at the state is admitted after the change (`RFiring.admits_of_outsideRules`) when the change
is outside what the firing reads of the rule occurrences (`RFiring.OutsideRules`):

* the occurrence it uses is still held (or its code is in the ambient program);
* the identities it makes are still new;
* the occurrences it removes are still held;
* no identity is newly held in a zone that one of its rule queries names;

and its opening is still fresh (the arguments of held rules are among what a state mentions). The
theorem is for every code system and every firing. Nothing else of the rule store is read: holding
other rules in other zones, or no longer holding rules the firing does not use, remove or ask about,
changes no admission.

Over first-order atoms, for the firing of `UsedUp.onceFiring`: holding the rule at one more identity
keeps it admitted (`RuleLocality.rule_outside_admitted`); no longer holding the occurrence it uses
refuses it (`RuleLocality.rule_used_refused`). For a rule query, the pair
`Equations.unmatched_admitted` and `Equations.unmatched_refused`: the same firing is admitted before
an equation is held in the zone it asks about and refused after.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)

section General

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z}

/-- The state that holds other identities, under the same labels. -/
def RState.withRules (s : RState Tm O R C Z) (W : Finset R) : RState Tm O R C Z :=
  ⟨s.toState, W, s.held⟩

/-- A firing, at the state that holds other identities. -/
def RFiring.atRules {s : RState Tm O R C Z} (f : RFiring O R E codes s) (W : Finset R) :
    RFiring O R E codes (s.withRules W) :=
  ⟨f.use, f.ext, f.opening, f.selection, f.seen, f.madeRules, f.installed, f.removedRules,
    f.published⟩

/-- **A change of the held identities outside what a firing reads of them**: its use is available,
the identities it makes are new, the occurrences it removes are held, and no identity is newly held
in a zone that one of its rule queries names. -/
structure RFiring.OutsideRules {s : RState Tm O R C Z} (f : RFiring O R E codes s)
    (ambient : Set C) (W : Finset R) : Prop where
  used : (s.withRules W).Available ambient f.use
  made : ∀ ρ ∈ f.madeRules, ρ ∉ W
  removed : ∀ x ∈ f.spec.removes.zip f.removedRules, x.2 ∈ W
  queried : ∀ q ∈ f.spec.unmatched, ∀ ρ, (s.held ρ).zone = q.1 → ρ ∈ W → ρ ∈ s.rules

variable (X : Frames Tm Hom) [DecidableEq O] {s : RState Tm O R C Z}

/-- **Locality in the rules held.** A firing admitted at a state is admitted after any change of the
held identities outside what it reads of them that keeps its opening fresh. -/
theorem RFiring.admits_of_outsideRules (f : RFiring O R E codes s) {ambient : Set C}
    {W : Finset R} (admitted : f.Admits X ambient) (outside : f.OutsideRules ambient W)
    (fresh : (f.atRules W).Fresh X) : (f.atRules W).Admits X ambient := by
  obtain ⟨⟨-, rows, shapes⟩, enabled, solvable, asks⟩ := admitted
  refine ⟨⟨fresh, rows, ?_⟩, enabled, solvable, ?_⟩
  · exact ⟨outside.used, shapes.arguments, shapes.installed, shapes.madeNodup, shapes.madeLength,
      outside.made, shapes.removed, shapes.removedNodup,
      fun x inside => ⟨outside.removed x inside, (shapes.removedHeld x inside).2⟩,
      shapes.published⟩
  · intro b σ solved
    have solved' : X.Models σ (f.information X) := solved
    have holds := asks b σ solved'
    exact ⟨holds.1,
      fun q inside ρ held zone =>
        holds.2.1 q inside ρ (outside.queried q inside ρ zone held) zone,
      holds.2.2.1, holds.2.2.2.1, holds.2.2.2.2⟩

end General

#print axioms RFiring.admits_of_outsideRules

namespace RuleLocality

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Holding the rule at the identity `7` as well is a change outside what the firing reads. -/
theorem outside_seven : UsedUp.onceFiring.OutsideRules (∅ : Set (Rule Tm)) {0, 7} where
  used := Finset.mem_insert_self 0 {7}
  made := fun _ inside => absurd inside List.not_mem_nil
  removed := fun _ inside => absurd inside List.not_mem_nil
  queried := fun _ inside => absurd inside List.not_mem_nil

/-- The opening is fresh at the state that holds the rule twice: the rule has no unknowns. -/
theorem fresh_seven : (UsedUp.onceFiring.atRules {0, 7}).Fresh X := by
  apply fresh_of_ground action
  intro t member σ
  have terms : (UsedUp.onceFiring.atRules {0, 7}).spec.terms = Exec.onceRule.terms :=
    Spec.terms_of_plain (Spec.plain_ofRule Exec.onceRule)
  rw [terms] at member
  have inside : t ∈ Exec.onceRule.terms := member
  simp [Exec.onceRule, Rule.terms] at inside
  rcases inside with rfl | rfl <;> rfl

/-- **A rule held besides, outside what the firing reads, keeps it admitted.** -/
theorem rule_outside_admitted :
    (UsedUp.onceFiring.atRules {0, 7}).Admits X (∅ : Set (Rule Tm)) :=
  UsedUp.onceFiring.admits_of_outsideRules X UsedUp.once_admitted outside_seven fresh_seven

/-- **Control: no longer holding the occurrence it uses refuses the firing.** -/
theorem rule_used_refused : ¬ (UsedUp.onceFiring.atRules ∅).Admits X (∅ : Set (Rule Tm)) :=
  stuck_of_no_rules X rfl _

#print axioms outside_seven
#print axioms rule_outside_admitted
#print axioms rule_used_refused

end RuleLocality

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
