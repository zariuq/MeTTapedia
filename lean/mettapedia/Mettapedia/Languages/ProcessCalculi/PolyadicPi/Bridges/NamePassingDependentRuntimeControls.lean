import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeEvidence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpineControls
import Mettapedia.TypeTheory.DisplayedPresheafRepresentableEvidence

/-!
# Native certificates on returning and looping compiled executions

An actual environment fetch and call reaches a public rho return with its
native origin specification and supplied execution receipt. A repeated
definition has two distinct source histories with the same endpoint and
initial witness. A predicate that only certifies the initial source state
cannot supply the operational evidence action needed to type the final one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational Mettapedia.GSLT.Ultrainfinite
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafRepresentableEvidence
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingObserverFunctor
open NamePassingDependentEvidence NamePassingDependentRuntimeEvidence
open NamePassingCompilerReadback.Controls NamePassingEnvironmentControls NamePassingSpineControls

def startPoint : sourcePrograms.Elements :=
  ⟨Opposite.op (Opposite.op (⟨names⟩ : SourceScope)), start⟩

theorem fetched_execution_keeps_native_origin :
    ∃ final, ∃ actual : ExecutionPath RhoUnaryReadback.Target (process start) final,
      ∃ receipt : Receipt (origins startPoint) (origins (compilerMap.mapElements.obj startPoint))
        (originMap compilerMap startPoint) startPoint (𝟙 startPoint)
        (world names) (code start) actual,
      receipt.specification = compilerMap.mapElements.map (𝟙 startPoint) ∧
        (NamePassingValueNative.sourcePredicate names).1 receipt.execution.after ∧
        (RhoUnaryInputObservation.targetPredicate (world names) .zero).1 final := by
  obtain ⟨final, ⟨actual⟩, observed⟩ := fetched_function_returns_in_rho
  obtain ⟨receipt⟩ := retain_prefix (origins startPoint)
    (origins (compilerMap.mapElements.obj startPoint)) (originMap compilerMap startPoint)
    startPoint (𝟙 startPoint) (world names) (code start) (supplied start) actual
  exact ⟨final, actual, receipt, receipt.computed, receipt.public_return_reflected observed, observed⟩

def loopPoint : sourcePrograms.Elements :=
  ⟨Opposite.op (Opposite.op (⟨[]⟩ : SourceScope)), loopingDefinition⟩

def loopPath : ExecutionPath (sourceTheory []) loopingDefinition loopingDefinition :=
  .cons ⟨⟨.environmentFetch, first_fetch.toModulo⟩⟩
    (.cons ⟨⟨.beta, retained_reference_called.toModulo⟩⟩ (.refl _))

theorem loopPath_two_events : loopPath.length = 2 := rfl

def noHistory :
    (OperationalReadbackEvidence.historyAndWitness (sourceTheory []) loopingDefinition
      ((origins loopPoint).obj loopPoint)).obj loopingDefinition :=
  ⟨.refl loopingDefinition, 𝟙 loopPoint⟩

def repeatedHistory :
    (OperationalReadbackEvidence.historyAndWitness (sourceTheory []) loopingDefinition
      ((origins loopPoint).obj loopPoint)).obj loopingDefinition :=
  (OperationalReadbackEvidence.historyAndWitness (sourceTheory []) loopingDefinition
    ((origins loopPoint).obj loopPoint)).map loopPath noHistory

theorem histories_distinct_same_witness :
    noHistory ≠ repeatedHistory ∧ noHistory.2 = repeatedHistory.2 := by
  constructor
  · intro same
    have lengths := congrArg (fun value => value.1.length) same
    change 0 = 2 at lengths
    cases lengths
  · rfl

/-- The source-state equality predicate cannot be an operational evidence
functor: the real two-event source path exits that predicate. -/
theorem stale_initial_predicate_is_not_operational :
    ¬ ∃ evidence : ExecutionObject (sourceTheory names) ⥤ Type,
      ∀ state, Nonempty (evidence.obj state) ↔ state = start := by
  rintro ⟨evidence, support⟩
  obtain ⟨initial⟩ := (support start).mpr rfl
  have atFinal : Nonempty (evidence.obj returned) := ⟨evidence.map successfulSourcePath initial⟩
  have same := (support returned).mp atFinal
  change Mettapedia.Languages.LambdaCalculus.NamePassing.Expr.defn stored (.lam (.var .zero)) =
    Mettapedia.Languages.LambdaCalculus.NamePassing.Expr.defn stored
      (.app (.var .zero) (.succ publicName))
    at same
  cases same

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingDependentRuntimeControls
