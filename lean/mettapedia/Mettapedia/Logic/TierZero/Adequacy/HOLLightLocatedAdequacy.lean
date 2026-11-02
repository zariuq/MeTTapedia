import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.InferenceKernelReachability
import Mettapedia.Languages.HOLLight.FirstOrder.Completeness
import Mettapedia.Languages.HOLLight.FirstOrder.PortableKernel

/-!
# The complete HOL Light inference catalog on the protected CMR authority path

All original first-order rule schemas, including their structural auxiliary
rules, are installed and activated through the same source-independent compiler.
The independent endpoint is HOL Light's ten inference operations and exactly
the explicitly admitted finite axiom policy. The result preserves whole
sequents, including hypotheses. Declaration contexts and definition admission
are a separate authority boundary; this theorem does not turn definitions
into arbitrary source axioms.

HOL object binders in this portable first-order representation are scoped
source data. Their independently proved freshness and substitution rules are
not a restriction on CMR's general contextual unification language.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedAdequacy

open Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Languages.HOLLight.FirstOrder
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

/-- Exactness for any package exposing the original full source rule catalog. -/
theorem reaches_iff_derives {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
    (catalog : definition.1 = holCalculus axioms) (policy : AxiomPolicy)
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (sequent : Sequent) :
    InferenceKernelReachability.Reaches definition (sequentJ sequent) ↔
      ∃ out : Theorem, Mettapedia.Logic.Derives (Mettapedia.Languages.HOLLight.Rule policy) out ∧ out.sequent = sequent := by
  rw [InferenceKernelReachability.reaches_iff_derivation]
  exact holCalculus_exact catalog policy admitted inList sequent

/-- The canonical validated full catalog is accepted by ordinary physical runs. -/
theorem validated_reaches_iff_derives (axioms : List Sequent) (policy : AxiomPolicy)
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (sequent : Sequent) :
    InferenceKernelReachability.Reaches (validatedHolCalculus axioms) (sequentJ sequent) ↔
      ∃ out : Theorem, Mettapedia.Logic.Derives (Mettapedia.Languages.HOLLight.Rule policy) out ∧ out.sequent = sequent :=
  reaches_iff_derives rfl policy admitted inList sequent

/-- Reading the actual portable module installs exactly the same full catalog. -/
theorem loaded_reaches_iff_derives (axioms : List Sequent) (policy : AxiomPolicy)
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    {loaded : ValidatedCalculusLanguageDef}
    (read : ModuleFormat.Portable.readValidatedCalculus? (kernelModule axioms) = some loaded)
    (sequent : Sequent) :
    InferenceKernelReachability.Reaches loaded (sequentJ sequent) ↔
      ∃ out : Theorem, Mettapedia.Logic.Derives (Mettapedia.Languages.HOLLight.Rule policy) out ∧ out.sequent = sequent := by
  rw [kernelModule_read] at read
  cases Option.some.inj read
  exact validated_reaches_iff_derives axioms policy admitted inList sequent

/-- In particular no primitive operation is excluded by the authority path. -/
theorem every_inference_reaches (axioms : List Sequent) (policy : AxiomPolicy)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms)
    {request : InferenceRequest} {out : Theorem} (step : request.Semantics out)
    (premises : ∀ premise ∈ request.premises, Mettapedia.Logic.Derives (Mettapedia.Languages.HOLLight.Rule policy) premise) :
    InferenceKernelReachability.Reaches (validatedHolCalculus axioms) (sequentJ out.sequent) := by
  have derived : Mettapedia.Logic.Derives (Mettapedia.Languages.HOLLight.Rule policy) out :=
    .node request.premises out (Or.inl ⟨request, rfl, step⟩) premises
  obtain ⟨source⟩ := holCalculus_complete
    (show (validatedHolCalculus axioms).1 = holCalculus axioms from rfl) policy inList derived
  exact InferenceKernelReachability.reaches_of_derivation source

end Mettapedia.Logic.TierZero.Adequacy.HOLLightLocatedAdequacy
