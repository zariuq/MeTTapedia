import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability

/-! # Controls for physical premise location and publication authority -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceAuthorityControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open InferenceSchemaActivation (Tm action judgment)
open InferenceSchemaKernel (Space Value locatedAction)
open InferenceRequestExecution (Occurrence label location payload system)

/-- A selected public occurrence cannot satisfy a protected premise position,
even when its payload is byte-for-byte the expected judgment. -/
theorem wrong_space_premise_refused {O : Type*} [DecidableEq O]
    (where_ : O → Space) (contents : O → Tm) (raw : RuleInstance Tm)
    (before : Configuration Value O) (picked : Selection O) (occurrence : O)
    (selected : occurrence ∈ picked.read) (inRequests : where_ occurrence = .requests) :
    ¬picked.Valid locatedAction (fun item => (where_ item, contents item))
      (InferenceSchemaKernel.locate raw) before := by
  intro valid
  have protectedHere := LocatedRequest.read_space action where_ contents
    .requests .judgments .requests .judgments valid occurrence selected
  rw [inRequests] at protectedHere
  cases protectedHere

/-- The ordinary client role may create arbitrary data, but cannot create a
new protected occurrence under the actual authority-system step relation. -/
theorem client_cannot_publish (definition : ValidatedCalculusLanguageDef)
    {before after : Configuration Value Occurrence}
    (step : (system definition).Step payload false before after)
    (occurrence : Occurrence) (absent : occurrence ∉ before.present)
    (protectedHere : location occurrence = .judgments) : occurrence ∉ after.present := by
  obtain ⟨source, installed, inputs, raw, computed, picked, valid, formed, rfl⟩ := step
  intro present
  rcases mem_fire.mp present with retained | made
  · exact absent retained.1
  · have selected : occurrence ∈ picked.made := by simpa [Selection.commit] using made
    have permission := formed occurrence selected
    change (location occurrence == Space.requests) = true at permission
    rw [protectedHere] at permission
    cases permission

/-- Successful activation has exactly the locally computed source conclusion;
an arbitrary replacement output is not another result of that activation. -/
theorem fabricated_output_refused (definition : ValidatedCalculusLanguageDef)
    (id : RuleId) (arguments : List Pattern) (premises : List Pattern)
    (conclusion counterfeit : Pattern) (rule : RuleSchema)
    (computed : InferenceSchemaActivation.activate definition id arguments =
      some (InferenceSchemaActivation.fromResult id rule arguments premises conclusion))
    (different : counterfeit ≠ conclusion) :
    ∀ raw, InferenceSchemaActivation.activate definition id arguments = some raw →
      raw.produce ≠ [judgment counterfeit] := by
  intro raw activated output
  have same := Option.some.inj (computed.symm.trans activated)
  subst raw
  have equal := List.singleton_inj.mp output
  exact different ((InferenceSchemaActivation.judgment_injective equal).symm)

/-- Public proof-shaped data remains public after an ordinary client post. -/
theorem proof_shaped_post_stays_public (definition : ValidatedCalculusLanguageDef)
    (before : Configuration Value Occurrence) (background : locatedAction.Consistent before.equations)
    (goal : Pattern) :
    ∃ request, (system definition).Step payload false before (InferenceRequestExecution.posted before request) ∧
      request ∈ (InferenceRequestExecution.posted before request).present ∧
      location request = .requests ∧ payload request = judgment goal := by
  obtain ⟨request, fresh, readback⟩ := IndexedOccurrences.supply before.present (Space.requests, judgment goal)
  refine ⟨request, InferenceRequestExecution.client_posts definition before background _ _ fresh readback,
    Finset.mem_insert_self .., congrArg Prod.fst readback, congrArg Prod.snd readback⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceAuthorityControls
