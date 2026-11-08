import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameControls

/-!
# Repeated physical reads, private instances and shared aliases

Two ports may read one schematic row at different instances. A captured
shared variable instead stays linked across both ports. Repeated occurrences
of a schema variable within one whole row stay linked as well; freshening
separate holes would accept an invalid mixed instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)

abbrev base := ContextualFrame.Controls.signature
abbrev locals (_ : Nat) : MetaArity base := ([], ())
abbrev captures (_ : Nat) : MetaArity base := ([], ())
abbrev raw := ContextualFreshening.declarations locals captures
abbrev active := ContextualFreshening.scopedDeclarations locals captures
abbrev RawTerm := Term (signature base raw) [] ()
abbrev ActiveTerm := Term (signature base active) [] ()

def atom {V : Type} (declaration : V → MetaArity base) :
    Term (signature base declaration) [] () := .op (.inl .constant) .nil

def pair {V : Type} {declaration : V → MetaArity base}
    (first second : Term (signature base declaration) [] ()) :
    Term (signature base declaration) [] () :=
  .op (.inl .pair) (.cons first (.cons second .nil))

def p {V : Type} {declaration : V → MetaArity base}
    (term : Term (signature base declaration) [] ()) :
    Term (signature base declaration) [] () := pair term (atom declaration)

def a : ActiveTerm := atom active
def b : ActiveTerm := pair a a
def rawA : RawTerm := atom raw
def rawB : RawTerm := pair rawA rawA
def privateVariable : RawTerm := generator raw (.inl 0)
def universalRow : RawTerm := p privateVariable
def repeatedRow : RawTerm := pair privateVariable privateVariable

def sharedValue : Term (signature base captures) [] () := generator captures 0
def sharedRow : RawTerm :=
  instantiate (capturedSource locals captures) (p sharedValue)

def selection : Selection Nat := ⟨[], [7, 7], [99]⟩
def occupied : Finset Nat := {0, 2, 7}
def first : Fin selection.read.length := ⟨0, by decide⟩
def second : Fin selection.read.length := ⟨1, by decide⟩
def firstPort := ContextualActivationScopes.readPort selection first
def secondPort := ContextualActivationScopes.readPort selection second

def rule : RuleInstance RawTerm :=
  ⟨[], [p rawA, p rawB], [(privateVariable, rawA)], [.equal privateVariable rawA], [universalRow]⟩
def prepared := prepare locals captures occupied selection rule (fun _ => universalRow)
def repeated := prepare locals captures occupied selection rule (fun _ => repeatedRow)
def shared := prepare locals captures occupied selection rule (fun _ => sharedRow)

def split : Assignment active active
  | .inl name =>
      if name.scope = ContextualActivationScopes.scopeAt occupied secondPort then b else a
  | .inr _ => a

theorem both_read_ports_choose_the_same_physical_occurrence :
    selection.read.get first = 7 ∧ selection.read.get second = 7 := ⟨rfl, rfl⟩

theorem reads_reserve_scopes_nine_and_ten :
    ContextualActivationScopes.scopeAt occupied firstPort = 9 ∧
      ContextualActivationScopes.scopeAt occupied secondPort = 10 := by decide

theorem the_rule_has_its_own_scope_eight :
    ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort selection) = 8 := by decide

theorem one_scope_per_whole_row_allows_distinct_instances :
    instantiate split (prepared.read first) = p a ∧
      instantiate split (prepared.read second) = p b := by
  constructor <;> with_unfolding_all rfl

theorem the_distinct_instances_meet_both_ground_rule_patterns :
    instantiate split (prepared.read first) = prepared.rule.read.get first ∧
      instantiate split (prepared.read second) = prepared.rule.read.get second := by
  constructor <;> with_unfolding_all rfl

theorem the_rule_local_is_distinct_from_both_read_locals :
    Sum.inl (ScopedVar.at 8 (0 : Nat)) ∈ support (S := base) (source := active)
        (prepared.rule.produce.get ⟨0, by decide⟩) ∧
      Sum.inl (ScopedVar.at 9 (0 : Nat)) ∈ support (S := base) (source := active) (prepared.read first) ∧
        Sum.inl (ScopedVar.at 10 (0 : Nat)) ∈
          support (S := base) (source := active) (prepared.read second) := by
  refine ⟨?_, ?_, ?_⟩
  · exact List.mem_singleton_self _
  · exact List.mem_singleton_self _
  · exact List.mem_singleton_self _

theorem the_same_rule_scope_links_its_tell_and_output :
    instantiate split (prepared.rule.tell.get ⟨0, by decide⟩).1 = a ∧
      instantiate split (prepared.rule.produce.get ⟨0, by decide⟩) = p a := by
  constructor <;> with_unfolding_all rfl

theorem the_retained_check_uses_the_same_rule_local :
    prepared.rule.checks.get ⟨0, by decide⟩ =
      .equal (generator active (.inl (ScopedVar.at 8 0))) (atom active) := by
  with_unfolding_all rfl

theorem shared_variables_do_not_get_a_new_identity_per_read : shared.read first = shared.read second :=
  shared_value_does_not_change_between_ports locals captures occupied firstPort secondPort (p sharedValue)

theorem distinct_ground_instances_are_unequal : p a ≠ p b := by
  intro same
  have fields := eq_of_heq (Term.op.inj same).2
  have different := (Args.cons.inj fields).1
  have sizes := congrArg termSize different
  change 1 = 3 at sizes
  omega

theorem no_assignment_can_treat_a_shared_row_as_two_private_instances
    (candidate : Assignment active active) :
    ¬ (instantiate candidate (shared.read first) = p a ∧
      instantiate candidate (shared.read second) = p b) := by
  rintro ⟨one, two⟩
  rw [shared_variables_do_not_get_a_new_identity_per_read] at one
  exact distinct_ground_instances_are_unequal (one.symm.trans two)

theorem a_whole_row_keeps_both_occurrences_of_one_schema_variable_linked
    (candidate : Assignment active active) :
    instantiate candidate (repeated.read first) =
      pair (candidate (.inl (ScopedVar.at 9 0))) (candidate (.inl (ScopedVar.at 9 0))) := by
  change instantiate candidate
    (pair (generator active (.inl (ScopedVar.at 9 0)))
      (generator active (.inl (ScopedVar.at 9 0)))) = _
  change pair (instantiate candidate (generator active (.inl (ScopedVar.at 9 0))))
    (instantiate candidate (generator active (.inl (ScopedVar.at 9 0)))) = _
  exact congrArg₂ (pair (declaration := active))
    (instantiate_generator (S := base) candidate (.inl (ScopedVar.at 9 0)))
    (instantiate_generator (S := base) candidate (.inl (ScopedVar.at 9 0)))

theorem no_assignment_makes_one_repeated_variable_equal_two_distinct_values
    (candidate : Assignment active active) :
    instantiate candidate (repeated.read first) ≠ pair a b := by
  rw [a_whole_row_keeps_both_occurrences_of_one_schema_variable_linked]
  intro same
  have fields := eq_of_heq (Term.op.inj same).2
  have one := (Args.cons.inj fields).1
  have two := (Args.cons.inj (Args.cons.inj fields).2).1
  have different : a = b := one.symm.trans two
  have sizes := congrArg termSize different
  change 1 = 3 at sizes
  omega

def wrongPerHoleView : ActiveTerm :=
  pair (generator active (.inl (ScopedVar.at 9 0)))
    (generator active (.inl (ScopedVar.at 10 0)))

theorem freshening_per_hole_would_accept_the_invalid_mixed_instance :
    instantiate split wrongPerHoleView = pair a b := by with_unfolding_all rfl

theorem the_prepared_ledger_retains_old_scopes_and_all_three_new_scopes :
    prepared.occupied = {0, 2, 7, 8, 9, 10} := by decide

theorem the_next_rule_scope_starts_at_eleven :
    ContextualActivationScopes.scopeAt prepared.occupied
      (ContextualActivationScopes.rulePort selection) = 11 := by decide

def duplicateTake : Selection Nat := ⟨[7, 7], [], []⟩

theorem fresh_ports_do_not_justify_duplicate_consumption : ¬ duplicateTake.taken.Nodup := by decide

theorem empty_selection_still_reserves_one_rule_scope :
    (ContextualActivationScopes.reserved ∅ (⟨[], [], []⟩ : Selection Nat)).card = 1 := by decide

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSelectionViews.Controls
