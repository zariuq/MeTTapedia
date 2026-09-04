import Mettapedia.Languages.ProcessCalculi.MORK.MM2RuleScopedExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ScheduledMinimum
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Rule-scoped scheduling after an inert probe

An unsuccessful rule-scoped directive consumes its own physical executable
occurrence.  Under exact and compact-key duplicate freedom, its successor
candidate inventory is ordinary occurrence erasure.  This is the algebraic
seam for composing finite administrative MORK segments without normalizing
their data spaces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open WQComputable

/-- An empty physical matcher discharges the complete guarded no-match
obligation, independently of the guard language. -/
theorem ruleScoped_guarded_no_matches_of_matcher_nil
    (space : List Atom) (directive : SourceExecFact)
    (matcherEmpty : cMatchInputSpecMork []
      (morkInsertSupport (morkEraseSupport space directive.atom)
        directive.atom) directive.rule.input = []) :
    (cMatchInputSpecMork []
      (morkInsertSupport (morkEraseSupport space directive.atom)
        directive.atom) directive.rule.input).filter
        (fun (substitution, _) =>
          matchSourceGuards substitution directive.rule.guards) = [] := by
  rw [matcherEmpty]
  rfl

/-- With physical uniqueness, an inert rule-scoped firing is exact ordinary
one-occurrence erasure. -/
theorem cFireRuleScopedSourceExecFact_eq_list_erase_of_no_matches
    (space : List Atom) (directive : SourceExecFact)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (present : directive.atom ∈ space)
    (noMatches :
      (cMatchInputSpecMork []
        (morkInsertSupport (morkEraseSupport space directive.atom)
          directive.atom)
        directive.rule.input).filter (fun (substitution, _) =>
          matchSourceGuards substitution directive.rule.guards) = []) :
    cFireRuleScopedSourceExecFact space directive =
      space.erase directive.atom := by
  rw [cFireRuleScopedSourceExecFact_eq_erase_of_no_matches
    space directive noMatches]
  exact morkEraseSupport_eq_erase_of_mem space directive.atom listNodup
    morkNodup present

/-- The supported candidate inventory after an inert rule-scoped firing is
exact directive occurrence erasure. -/
theorem cSupportedSourceExecFacts_after_ruleScoped_inert
    (space : List Atom) (directive : SourceExecFact)
    (listNodup : space.Nodup) (morkNodup : MorkSupportNodup space)
    (present : directive.atom ∈ space)
    (decoded : extractSupportedSourceExecFact directive.atom = some directive)
    (noMatches :
      (cMatchInputSpecMork []
        (morkInsertSupport (morkEraseSupport space directive.atom)
          directive.atom)
        directive.rule.input).filter (fun (substitution, _) =>
          matchSourceGuards substitution directive.rule.guards) = []) :
    cSupportedSourceExecFacts
        (cFireRuleScopedSourceExecFact space directive) =
      (cSupportedSourceExecFacts space).erase directive := by
  rw [cFireRuleScopedSourceExecFact_eq_list_erase_of_no_matches space directive
    listNodup morkNodup present noMatches]
  exact cSupportedSourceExecFacts_erase space directive decoded

/-- Once the least candidate is identified, the actual rule-scoped work queue
performs precisely its physical firing. -/
theorem cRuleScopedSourceWorkQueueStep_of_selected
    (space : List Atom) (directive : SourceExecFact)
    (selected : selectNextScheduled (cSupportedSourceExecFacts space) =
      some directive) :
    cRuleScopedSourceWorkQueueStep .leaveInert space =
      some (cFireRuleScopedSourceExecFact space directive) := by
  simp [cRuleScopedSourceWorkQueueStep, selected]

#print axioms cFireRuleScopedSourceExecFact_eq_list_erase_of_no_matches
#print axioms ruleScoped_guarded_no_matches_of_matcher_nil
#print axioms cSupportedSourceExecFacts_after_ruleScoped_inert
#print axioms cRuleScopedSourceWorkQueueStep_of_selected

end Mettapedia.Languages.ProcessCalculi.MORK
