import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TransformQualification
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SchemaPublicationAuthority
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PublicationAuthorityControls

/-!
# Joined qualification: checked inference is an authority restriction of the one-frame step

The inference hosts publish judgments through processes: an installed schema, its actual activation,
an ordinary occurrence firing, and the publication right of every made occurrence
(`SchemaPublicationAuthority.Process.Step`, `PublicationAuthority.Process.Step`). The derivation
adequacy results (`InferenceKernelReachability.reaches_iff_derivation`,
`InferenceSchemaKernel.System.published_judgment_has_source_derivation`) are stated over these
processes.

* `schema_step_iff_admitted`: a step of a schema process is exactly an admitted query-free firing
  of the one-frame instance `AnnotatedRuns.firstOrder` whose rule is the activation of an installed
  schema and whose made occurrences the process may send to; the result is the step's result.
* `rule_step_iff_admitted`: the same for processes with installed rule instances.

So the inference layer adds no admission of its own: it restricts which admitted firings a process
may fire. The restriction is proper, and it is what carries logical validity:

* `forged_admitted_but_not_published`: the forged producer, which makes the protected occurrence, is
  an admitted firing of the one-frame step, and no step of the client's process reaches its result.
  Operational admission alone does not confer the right to publish a judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification

open AnnotatedRuns (Firing firstOrder)

universe uT uS uO uN uR uX

section Placement

variable {T : Type uT} {S : Type uS} {O : Type uO} {N : Type uN} {R : Type uR} {X : Type uX}
  [DecidableEq O]

/-- **A schema process step is an authorized admitted firing of the one-frame step.** -/
theorem schema_step_iff_admitted (process : SchemaPublicationAuthority.Process R N)
    (activate : R → X → Option (RuleInstance T)) (A : SubstitutionAction T S) (label : O → T)
    (location : O → N) (before after : Configuration T O) :
    process.Step activate A label location before after ↔
      ∃ schema ∈ process.schemas, ∃ inputs rule, activate schema inputs = some rule ∧
        ∃ (picked : Selection O)
          (admitted : (firstOrder (S := S) A label).Admits (s := before)
            (⟨rule, [], picked⟩ : Firing T S O)),
          PublicationAuthority.Formed process.rights location picked ∧
            (firstOrder A label).result _ admitted = after := by
  constructor
  · rintro ⟨schema, installed, inputs, rule, computed, picked, valid, formed, rfl⟩
    exact ⟨schema, installed, inputs, rule, computed, picked,
      (PredicateQueryAdmission.valid_empty_iff A label rule before picked).mpr valid, formed, rfl⟩
  · rintro ⟨schema, installed, inputs, rule, computed, picked, admitted, formed, rfl⟩
    exact ⟨schema, installed, inputs, rule, computed, picked,
      (PredicateQueryAdmission.valid_empty_iff A label rule before picked).mp admitted, formed, rfl⟩

/-- **A rule process step is an authorized admitted firing of the one-frame step.** -/
theorem rule_step_iff_admitted (process : PublicationAuthority.Process T N)
    (A : SubstitutionAction T S) (label : O → T) (location : O → N)
    (before after : Configuration T O) :
    process.Step A label location before after ↔
      ∃ rule ∈ process.rules, ∃ (picked : Selection O)
        (admitted : (firstOrder (S := S) A label).Admits (s := before)
          (⟨rule, [], picked⟩ : Firing T S O)),
        PublicationAuthority.Formed process.rights location picked ∧
          (firstOrder A label).result _ admitted = after := by
  constructor
  · rintro ⟨rule, installed, picked, valid, formed, rfl⟩
    exact ⟨rule, installed, picked,
      (PredicateQueryAdmission.valid_empty_iff A label rule before picked).mpr valid, formed, rfl⟩
  · rintro ⟨rule, installed, picked, admitted, formed, rfl⟩
    exact ⟨rule, installed, picked,
      (PredicateQueryAdmission.valid_empty_iff A label rule before picked).mp admitted, formed, rfl⟩

end Placement

section Forgery

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A initial)
open PublicationAuthority.Controls (label producer forgedSelection forgedState system)

/-- **Operational admission does not confer publication.** The forged producer is an admitted
firing of the one-frame step, and the client's process reaches its result by no step. -/
theorem forged_admitted_but_not_published :
    ∃ admitted : (firstOrder (S := Subst signature) A label).Admits (s := initial)
        (⟨producer, [], forgedSelection⟩ : Firing (Term signature) (Subst signature) Nat),
      (firstOrder A label).result _ admitted = forgedState ∧
        ¬ system.Step A label true initial forgedState :=
  ⟨(PredicateQueryAdmission.valid_empty_iff A label producer initial forgedSelection).mpr
      PublicationAuthority.Controls.the_forged_producer_is_an_ordinary_valid_firing,
    rfl, PublicationAuthority.Controls.the_client_cannot_publish_the_protected_copy⟩

end Forgery

#print axioms schema_step_iff_admitted
#print axioms rule_step_iff_admitted
#print axioms forged_admitted_but_not_published

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.TransformQualification
