import Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearchControls

/-! The producer controls are theorems checked by Lean's kernel. Candidate
production against external modules is additionally checked by the ordinary
article checker in the executable producer. -/

open Mettapedia.GSLT.LanguageDef.FirstOrderPremiseSearch.Controls

#print axioms premise_outputs_threaded
#print axioms ordered_children_retained
#print axioms repeated_holes_disagree
#print axioms occurs_check_refuses_cycle
#print axioms invocations_have_fresh_variables
#print axioms step_exhaustion_is_explicit
#print axioms depth_exhaustion_is_explicit
#print axioms unifier_exhaustion_is_explicit
#print axioms bad_seed_argument_arity
#print axioms bad_seed_premise_arity
#print axioms undeclared_variable_fault
#print axioms duplicate_rule_identity_fault
#print axioms unused_variable_not_invented
#print axioms repeated_calls_do_not_mutate_inputs
#print axioms deep_left_branch_does_not_hide_base

def main : IO UInt32 := do
  IO.println "15 kernel-checked first-order producer controls."
  return 0
