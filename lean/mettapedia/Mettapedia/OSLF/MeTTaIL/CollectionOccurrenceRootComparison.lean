import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

/-!
# Canonical successors of the root and occurrence search strategies

Every certified root profile is a source-level specialization of the retained
occurrence search. The comparison uses the actual publication operations of
both searches and their common presented source relation. It compares
successor classes; chronological order and derivation observations have
separate conservation contracts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax CanonicalBags ScopedRuleMatching
open GeneralPremise CollectionOccurrenceHandoff CollectionOccurrenceBatch

private theorem root_rules {plan : GeneralExecutionAdmission.Plan}
    (certificate : CollectionRootSearch.CoverageProfile plan)
    (declaration : GeneralExecutionAdmission.RulePlan) (member : declaration ∈ plan.rules) :
    IncreasingSpines declaration.rule declaration.binding.spec ∧
      NullaryGuards declaration.rule.premises ∧
      BinderLawsFor [] (GeneralPlanEnvironment.environment plan).reflection declaration.rule := by
  obtain ⟨kind, schemas, rest, _, _, _, increasing, empty, binderOk⟩ := certificate.rules declaration member
  refine ⟨increasing, ?_, binderOk⟩
  rw [empty]
  intro premise impossible
  cases impossible

/-- The same canonical successors are published by the established root
strategy and the recursive occurrence strategy, at every fixed continuation
depth. The root certificate contributes only its existing local rule and
algebra conditions; no comparison result is supplied as a field. -/
theorem root_publication_target_iff {plan : GeneralExecutionAdmission.Plan}
    (certificate : CollectionRootSearch.CoverageProfile plan) (expected : TypeExpr)
    (source target : Pattern) (depth : Nat) :
    (∃ work receipt,
      receipt ∈ (CollectionRootSearch.search (profile := certificate.profile) expected).publication
        ((CollectionRootSearch.search (profile := certificate.profile) expected).run (canon source) work) ∧
      canon receipt.target = canon target) ↔
    ∃ work receipt, receipt ∈ (search plan [] expected depth).publication
      ((search plan [] expected depth).run source work) ∧ canon receipt.target = canon target := by
  rw [← CollectionRootSearch.presented_iff_published certificate.profile expected certificate.rules
    certificate.noLaws certificate.noExtrusions source target]
  constructor
  · rintro ⟨representative, original, before, valid, after⟩
    have sameSource := CollectionRootSearch.modelEquiv_canon expected
      certificate.profile.noEquations certificate.noLaws certificate.noExtrusions before
    have sameTarget : canon original.target = canon target := by
      simpa only [canon_idempotent] using
        CollectionRootSearch.modelEquiv_canon expected certificate.profile.noEquations
          certificate.noLaws certificate.noExtrusions after
    have fragment := root_rules certificate original.job.declaration
      (List.fst_mem_of_mem_zipIdx valid.1.1)
    have bounded : StructuralDescent.eventsDepth original.premiseHistory ≤ depth := by
      rw [valid.2.1.nullary_history_depth (GeneralRuleJobs.Job.selected_rule valid.1) fragment.2.1]
      exact Nat.zero_le _
    obtain ⟨work, packet, receipt, logged, finished, _, _, _, observed⟩ :=
      CollectionOccurrenceMachine.receipt_eventually_published valid fragment.2.2 fragment.1
        (.nullary fragment.2.1) depth bounded
    rw [← sameSource] at logged
    refine ⟨work, receipt, ?_, observed.symm.trans sameTarget⟩
    exact List.mem_filterMap.mpr ⟨packet, logged, finished⟩
  · rintro ⟨work, receipt, published, sameTarget⟩
    have stepped := (search_lawful plan [] expected depth).sound source work receipt published
    change (Complete.Presented.gslt plan [] expected).Step source (canon receipt.target) at stepped
    rwa [sameTarget] at stepped

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch
