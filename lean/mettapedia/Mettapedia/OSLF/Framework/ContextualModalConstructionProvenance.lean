import Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted
import Mettapedia.OSLF.Framework.ContextualModalSignatureCompiler

/-!
# Construction provenance for contextual-modal generation

The contextual-modal signature compiler returns one ordinary flat calculus
language, but its lawful incremental implementation threads the already
compiled grounded-typing demand and emits a field-aware residual extension.
This module makes those two views one typed construction algebra.

Batch compilation of an appended demand and incremental application of the
residual are different construction routes.  `batch_incremental_evaluate`
proves that they evaluate to the same flat generated language, while
`batch_incremental_routes_distinct` proves that route erasure is genuine.
-/

namespace Mettapedia.OSLF.Framework.ContextualModalConstructionProvenance

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.ConstructionProvenance.ManySorted

variable (source : ValidatedLanguageDef)

/-- Artifact kinds needed by contextual-modal compilation. -/
inductive ArtifactKind where
  | groundedTypingDemand
  | calculusExtension
  | calculusLanguage
deriving DecidableEq

/-- Exact artifact type at each compiler stage. -/
def Artifact : ArtifactKind → Type
  | .groundedTypingDemand => SelectedNativeTypeFoundation.Demand source
  | .calculusExtension => CalculusLanguageExtension
  | .calculusLanguage => CalculusLanguageDef

/-- Authored roots are values at their exact compiler stage. -/
abbrev Source := Artifact source

/-- Typed operations of the contextual-modal construction pipeline. -/
inductive Operation : List ArtifactKind → ArtifactKind → Type where
  | appendDemand :
      Operation [.groundedTypingDemand, .groundedTypingDemand]
        .groundedTypingDemand
  | compile : Operation [.groundedTypingDemand] .calculusLanguage
  | continuation :
      Operation [.groundedTypingDemand, .groundedTypingDemand]
        .calculusExtension
  | applyExtension :
      Operation [.calculusExtension, .calculusLanguage] .calculusLanguage

/-- Interpret the construction operations by the existing compiler and its
field-aware extension algebra. -/
def interpretOperation : {inputs : List ArtifactKind} →
    {output : ArtifactKind} →
    Operation inputs output →
      FamilyList (Artifact source) inputs → Artifact source output
  | _, _, .appendDemand, .cons compiled (.cons residual .nil) =>
      compiled.append residual
  | _, _, .compile, .cons demand .nil =>
      ContextualModalSignatureCompiler.definition demand
  | _, _, .continuation, .cons compiled (.cons residual .nil) =>
      ContextualModalSignatureCompiler.continuationExtension
        compiled residual
  | _, _, .applyExtension, .cons extension (.cons language .nil) =>
      extension.apply language

/-- The contextual-modal compiler as a typed construction algebra. -/
def algebra : ManySortedConstructionAlgebra where
  Kind := ArtifactKind
  Object := Artifact source
  Source := Source source
  Operation := Operation
  interpretSource := fun value => value
  interpretOperation := interpretOperation source

/-- Batch route: append demands first, then compile the whole demand. -/
def batchRoute
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    ConstructionTree (algebra source) .calculusLanguage :=
  .apply .compile
    (.cons
      (.apply .appendDemand
        (.cons (.source compiled) (.cons (.source residual) .nil)))
      .nil)

/-- Incremental route: compile the prefix, calculate its state-aware residual,
then apply only that residual to the earlier flat result. -/
def incrementalRoute
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    ConstructionTree (algebra source) .calculusLanguage :=
  .apply .applyExtension
    (.cons
      (.apply .continuation
        (.cons (.source compiled) (.cons (.source residual) .nil)))
      (.cons (.apply .compile (.cons (.source compiled) .nil)) .nil))

/-- The two construction routes commute at the public flat-language boundary. -/
theorem batch_incremental_evaluate
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    (algebra source).evaluate (batchRoute source compiled residual) =
      (algebra source).evaluate (incrementalRoute source compiled residual) :=
  ContextualModalSignatureCompiler.definition_append compiled residual

/-- A route observation that sees whether a generated calculus language was
created by batch compilation or residual application. -/
def calculusRootTag :
    ConstructionTree (algebra source) .calculusLanguage → Nat
  | .source _ => 0
  | .apply .compile _ => 1
  | .apply .applyExtension _ => 2

/-- The commuting routes remain intensionally distinct. -/
theorem batch_incremental_routes_distinct
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    batchRoute source compiled residual ≠
      incrementalRoute source compiled residual := by
  intro equality
  have tagsEqual := congrArg (calculusRootTag source) equality
  change 1 = 2 at tagsEqual
  omega

/-- No function of the generated flat language alone can recover every
contextual-modal construction route. -/
theorem no_flat_history_recovery
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    ¬ ∃ recover : CalculusLanguageDef →
          ConstructionTree (algebra source) .calculusLanguage,
        Function.LeftInverse recover (algebra source).evaluate := by
  rintro ⟨recover, recovers⟩
  have routesEqual :
      batchRoute source compiled residual =
        incrementalRoute source compiled residual := by
    calc
      batchRoute source compiled residual =
          recover ((algebra source).evaluate
            (batchRoute source compiled residual)) :=
        (recovers (batchRoute source compiled residual)).symm
      _ = recover ((algebra source).evaluate
            (incrementalRoute source compiled residual)) := by
        rw [batch_incremental_evaluate]
      _ = incrementalRoute source compiled residual :=
        recovers (incrementalRoute source compiled residual)
  exact batch_incremental_routes_distinct source compiled residual routesEqual

/-- The batch route carries an exact receipt for the ordinary generated
language. -/
def batchReceipt
    (compiled residual : SelectedNativeTypeFoundation.Demand source) :
    ConstructionReceipt (algebra := algebra source)
      ((algebra source).evaluate (batchRoute source compiled residual)) where
  route := batchRoute source compiled residual
  evaluates := rfl

#print axioms batch_incremental_evaluate
#print axioms batch_incremental_routes_distinct
#print axioms no_flat_history_recovery

end Mettapedia.OSLF.Framework.ContextualModalConstructionProvenance
