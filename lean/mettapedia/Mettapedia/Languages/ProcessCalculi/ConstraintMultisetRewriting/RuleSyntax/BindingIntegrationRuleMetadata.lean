import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Program
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Ordinary row observations do not recover linear rule resources

The actual rule-occurrence step can consume a linear held rule while leaving
its frame, knowledge, rows and labels unchanged. Thus the ordinary state
projection cannot determine whether that held occurrence remains available.

An explicit row-materialization policy may intentionally select persistent
schemas. This counterexample instead rules out recovering arbitrary live-rule
availability from the ordinary projection alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.RuleMetadata

open Mettapedia.Logic.LP
open RuleOccurrences
open Examples (Tm X E c)
open RuleSyntax.Controls (atoms action)

/-- The rule changes no ordinary row, but its held occurrence is a resource. -/
def idle : Rule Tm := ⟨PUnit.unit, ⟨[], [], [], [], []⟩, []⟩

abbrev Native := RState Tm Nat Nat (Rule Tm) Unit

def initial (mode : Mode) : Native :=
  ⟨⟨PUnit.unit, [], {7}, fun _ => c 7⟩, {0}, fun _ => ⟨idle, [], mode, ()⟩⟩

def firing (mode : Mode) : RFiring Nat Nat E (ofRules Unit) (initial mode) :=
  ⟨.held 0, PUnit.unit, Subst.id atoms, ⟨[], [], []⟩, [], [], [], [], []⟩

theorem fresh (mode : Mode) : (firing mode).Fresh X := by
  intro target caller localAssignment
  refine ⟨caller, ?_, ?_⟩
  · intro term _
    change action.E (action.apply caller (action.apply action.identity term)) (action.apply caller term)
    rw [action.apply_identity]
    rfl
  · intro term member
    change term ∈ ([] : List (Term atoms)) at member
    cases member

theorem admitted (mode : Mode) :
    (rstep X Nat Nat E (ofRules Unit) (∅ : Set (Rule Tm))).Admits (firing mode) := by
  refine ⟨⟨fresh mode, ?_, ?_⟩, ?_, ?_, ?_⟩
  · exact ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, rfl⟩
  · exact ⟨by change (0 : Nat) ∈ ({0} : Finset Nat); simp,
      rfl, rfl, List.nodup_nil, rfl,
      fun _ member => False.elim (List.not_mem_nil member), rfl,
      List.nodup_nil, fun _ member => False.elim (List.not_mem_nil member), rfl⟩
  · change MeTTaCalculus.OccurrenceCommits.Enabled (fun _ : Nat => ()) {7}
      (⟨∅, ∅, ∅, []⟩ : MeTTaCalculus.OccurrenceCommits.Commit Nat Unit)
    decide
  · refine ⟨PUnit.unit, Subst.id atoms, ?_⟩
    intro equation member
    change equation ∈ ([] : EquationStore (Term atoms)) at member
    cases member
  · intro target point _
    simp [RFiring.Holds, RFiring.base, Firing.Holds, firing, initial, idle,
      ofRules, Spec.ofRule, Spec.toRule, RFiring.spec, RState.codeOf,
      Firing.opened, Firing.collectOpened, RuleInstance.map]

theorem ordinary_projection_unchanged (mode : Mode) :
    ((firing mode).result X).toState = (initial mode).toState := by
  change (⟨PUnit.unit, [],
      MeTTaCalculus.OccurrenceCommits.fire ({7} : Finset Nat)
        (⟨∅, ∅, ∅, []⟩ : MeTTaCalculus.OccurrenceCommits.Commit Nat Unit),
      fun _ => c 7⟩ : State Tm Nat) = ⟨PUnit.unit, [], {7}, fun _ => c 7⟩
  simp only [MeTTaCalculus.OccurrenceCommits.fire, Finset.sdiff_empty, Finset.union_empty]

theorem held_initially_available (mode : Mode) :
    (initial mode).Available (∅ : Set (Rule Tm)) (.held 0) := by
  change (0 : Nat) ∈ ({0} : Finset Nat)
  simp

theorem linear_consumed :
    ¬ ((firing .linear).result X).Available (∅ : Set (Rule Tm)) (.held 0) := by
  change (0 : Nat) ∉ ((firing .linear).result X).rules
  rw [(firing .linear).mem_result_rules (X := X)]
  rw [(firing .linear).kept_linear rfl rfl rfl]
  simp [initial, firing]

theorem persistent_retained :
    ((firing .persistent).result X).Available (∅ : Set (Rule Tm)) (.held 0) := by
  change (0 : Nat) ∈ ((firing .persistent).result X).rules
  rw [(firing .persistent).mem_result_rules (X := X)]
  rw [(firing .persistent).kept_persistent rfl rfl rfl]
  simp [initial, firing]

/-- The changed coordinate is the actual linear-rule resource, not a
change invented by a different ordinary-state observer. -/
theorem actual_linear_firing_changes_only_the_retained_rule_resource :
    (rstep X Nat Nat E (ofRules Unit) (∅ : Set (Rule Tm))).Admits (firing .linear) ∧
      ((firing .linear).result X).toState = (initial .linear).toState ∧
      (initial .linear).Available (∅ : Set (Rule Tm)) (.held 0) ∧
      ¬ ((firing .linear).result X).Available (∅ : Set (Rule Tm)) (.held 0) :=
  ⟨admitted .linear, ordinary_projection_unchanged .linear,
    held_initially_available .linear, linear_consumed⟩

/-- No predicate of the ordinary projection can recover availability at
every live-rule state. In particular, it cannot rehydrate consumed rules. -/
theorem availability_does_not_descend :
    ¬ ∃ available : State Tm Nat → Prop,
      ∀ state : Native, available state.toState ↔
        state.Available (∅ : Set (Rule Tm)) (.held 0) := by
  rintro ⟨available, exactAt⟩
  have before := (exactAt (initial .linear)).mpr (held_initially_available .linear)
  have after : available ((firing .linear).result X).toState := by
    rwa [ordinary_projection_unchanged .linear]
  exact linear_consumed ((exactAt ((firing .linear).result X)).mp after)

#print axioms admitted
#print axioms ordinary_projection_unchanged
#print axioms linear_consumed
#print axioms persistent_retained
#print axioms availability_does_not_descend

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.RuleMetadata
