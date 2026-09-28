import Mettapedia.OSLF.Syntax.CanonicalConditionalOperationalClassification
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# A scoped operational event missing from the earlier raw classifier

The existing canonical rule polynomial retains only root step premises. The
authored LamCong premise has one local binder, and the contextual executor
fires it. The following comparison proves that the old polynomial does not
classify that firing; a scoped, context-indexed rule polynomial is required.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CanonicalScopedClassificationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.Binding.CanonicalConditionalOperationalClassification
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-- The declared LamCong event fires below its own binder in two layers. -/
theorem scoped_classifier_required_positive :
    wrappedTarget ∈
      ((Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution.rewriteAt
        RelationEnv.empty language 2 0
        wrappedRedex).map Prod.snd) :=
  lamCong_requires_two_layers.2

/-- The root-only evaluator has no corresponding result at the same fuel,
although it reads the same authored rule list. -/
theorem root_only_misses_scoped_step :
    wrappedTarget ∉
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        (engineBasePremises RelationEnv.empty) language 2 wrappedRedex := by
  decide +kernel

/-- Consequently the earlier free event construction is not a classifier
for the actual scoped LamCong execution. Its universal property remains
valid for the narrower root-only model it constructs. -/
theorem old_free_model_misses_scoped_step :
    ¬ Nonempty
      ((freeAuthoredRules (engineBasePremises RelationEnv.empty) language).model.carrier
        () (2, wrappedRedex, wrappedTarget)) := by
  intro evidence
  exact root_only_misses_scoped_step
    ((executable_iff_free_evidence
      (engineBasePremises RelationEnv.empty) language 2
      wrappedRedex wrappedTarget).mpr evidence)

end Mettapedia.OSLF.Binding.CanonicalScopedClassificationBoundary
