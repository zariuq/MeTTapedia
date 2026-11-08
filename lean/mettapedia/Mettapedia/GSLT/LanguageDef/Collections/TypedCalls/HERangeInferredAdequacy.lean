import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceAdequacy
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredProtocol

/-!
# Authored range with the actual inferred-reader argument protocol

This instantiates the existing recursive source induction with earned local
ports. It retains every result frame and the terminal Empty occurrence.
The theorem is for the named internal reader/source profile, not a global
public-HE type-service equivalence or native instruction-lowering theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredAdequacy

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed
open RetainedTypePayloads (ExternalView)
open HERangeSourceProgram (space)
open HERangeSourceAdequacy (values)
open HERangeSuperposeSource (NumericOrEmpty)

theorem source (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    let ports := HERangeInferredProtocol.ports minimal world active primitive unobservedClosure
    ∃ rows : List Result,
      Stateful.AtomRel ports.environment space () live scope (HERangeUntypedEntry.rangeCall lower upper)
        expected before rows () (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  HERangeSourceAdequacy.range_source_for (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure)
    policy before live scope lower upper expected demand

theorem retained_run (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps current.view current.services current.dispatch current.lookup policy
        ⟨(), space, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), stack, emitted⟩
        ⟨(), space, .returning rows, stack, emitted⟩ (admission := current.arguments) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (∀ row ∈ rows, isErrorAtom row.1.erase = false) ∧ rows.length = (upper - lower).toNat + 1 :=
  HERangeSourceAdequacy.retained_run_for (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure)
    policy before live scope lower upper expected demand stack emitted

/-- Root execution drains the real result occurrences into the prior
publication history. Pending work is not identified with no results. -/
theorem finished_run (minimal : Minimal.Services) (world : ExternalView) (active : String → Bool)
    (primitive : TypeNormalizationScope.Primitive) (unobservedClosure : List Atom → List Atom)
    (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom)
    (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) (emitted : List Result) :
    let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps current.view current.services current.dispatch current.lookup policy
        ⟨(), space, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), [], emitted⟩
        ⟨(), space, .returning [], [], emitted ++ rows⟩ (admission := current.arguments) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      rows.length = (upper - lower).toNat + 1 := by
  obtain ⟨rows, sourceRun, numeric, observed⟩ := source minimal world active primitive unobservedClosure
    policy before live scope lower upper expected demand
  let current := (HERangeInferredProtocol.ports minimal world active primitive unobservedClosure).environment
  have loaded : (RecursiveTasks.Contextual.WorldConfiguration.mk () space
      (.work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before)) [] emitted).SourceRel
      current policy (emitted ++ rows) () := ⟨rows, rows, (), .work sourceRun, .nil _, rfl⟩
  refine ⟨rows, RecursiveExecution.Contextual.Stateful.source_to_finished loaded, observed, ?_⟩
  have size := congrArg List.length observed
  simpa [values] using size

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeInferredAdequacy
