import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplication
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceProjectionControls

/-! # One protected occurrence can supply two actual read ports -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplicationControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker hiding RuleInstance
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open InferenceSchemaActivation (action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload)
open InferenceSelectedFirings
open InferenceJudgmentBoards
open InferenceTraceClassifying

/-- Local admission of a rule with two equal premises is enough to execute
both premise ports against one physical row. The resulting open proof is
obtained from those selected native client/server firings. -/
theorem admitted_duplicate_reads_execute (definition : ValidatedCalculusLanguageDef)
    (instance_ : InferenceChecker.RuleInstance) (premise conclusion : Pattern)
    (applied : RuleApplication definition instance_ [premise, premise] conclusion) :
    let seed : Occurrence := (0, (.judgments, judgment premise))
    let before : Configuration Value Occurrence := ⟨[], {seed}⟩
    ∃ (middle after : Configuration Value Occurrence)
      (_client : SelectedFiring definition false before middle)
      (server : SelectedFiring definition true middle after),
      server.source = .inl instance_.ruleId ∧ server.inputs = .inl instance_.arguments ∧
      server.picked.read = [seed, seed] ∧
      Nonempty (OpenDerivation definition [premise] conclusion) := by
  intro seed before
  have background : locatedAction.Consistent before.equations :=
    ⟨action.identity, locatedAction.models_nil _⟩
  have scope : premise.isWellScoped = true :=
    (InferenceSchemaActivation.application_scopes applied).1 premise (by simp)
  let prior : Board before :=
    { entries := [(seed, premise)]
      distinct := by simp
      occupied := by
        intro occurrence
        simp only [List.map_cons, List.map_nil, List.mem_singleton, before, Finset.mem_singleton]
        constructor
        · rintro rfl
          exact ⟨rfl, rfl⟩
        · exact fun present => present.1
      readback := by intro entry member; obtain rfl := List.mem_singleton.mp member; rfl
      supported := by intro entry member; obtain rfl := List.mem_singleton.mp member; exact scope }
  obtain ⟨middle, after, client, server, source, inputs, reads, _, output, present, readback⟩ :=
    InferenceSelectedApplication.application_runs_with_reads definition applied before background
      [seed, seed] (by
        intro occurrence member
        have same : occurrence = seed := by
          simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self] using member
        subst occurrence
        exact Finset.mem_singleton_self _)
      rfl
  let trace : SelectedRun definition before [false, true] after :=
    .cons client (.cons server (.nil after))
  exact ⟨middle, after, client, server, source, inputs, reads,
    ⟨trace.derive prior output present (congrArg Prod.fst readback) conclusion readback⟩⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceSelectedApplicationControls
