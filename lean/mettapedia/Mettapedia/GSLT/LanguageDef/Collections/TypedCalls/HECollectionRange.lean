import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSuperpose
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HERangeSourceAdequacy

/-! Authored recursive range in the collection source/snapshot world.
The existing induction is instantiated with actual extended-space frontiers,
the current inferred reader, and local primitive source derivations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRange

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HERangeSuperposeSource (NumericOrEmpty)
open HERangeSourceAdequacy (values)

def ports (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom) :
    HERangeWorldProtocol.Ports World where
  environment := environment minimal nativePolicy external active primitive subtypes
  label := HECollectionSpaceExtension.space
  ordinary name arguments member := HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes name arguments (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    tauto)
  rangeFrontier world policy live before lower upper := by
    obtain ⟨work, after, frontier, bindings, unified, read⟩ := HERangeEquationFrontiers.range_frontier policy live before lower upper
    refine ⟨work, after, ?_, bindings, unified, read⟩
    exact HECollectionSpaceExtension.old_frontier live before.bindings "range" _ [work] (by simp) frontier
  conditionalFrontier world policy live before condition yes no yesClosed noClosed := by
    obtain ⟨work, after, frontier, bindings, unified, read⟩ :=
      HEConditionalSourceFrontier.complete_singleton policy live before condition yes no yesClosed noClosed
    have extended := HERangeSourceProgram.lift_if_frontier _ _ _ _ _ _ frontier
    refine ⟨work, after, ?_, bindings, unified, read⟩
    simp only [HEConditionalEquationFrames.query, Entry.Value.erase, List.map_cons, List.map_nil] at extended ⊢
    exact HECollectionSpaceExtension.old_frontier live before.bindings "if" _ [work] (by simp) extended
  emptyFrontier world live before := by
    refine ⟨HERangeEquationFrontiers.emptyWork before, ?_, rfl, rfl, rfl⟩
    exact HECollectionSpaceExtension.old_frontier live before.bindings "empty" [] _ (by simp)
      (HERangeEquationFrontiers.empty_frontier live before)
  undefinedHead world names before name member := by
    have absent : getAnnotatedTypes HECollectionSpaceExtension.space (.symbol name) = [] := by
      rcases member with rfl | rfl <;> rfl
    exact HECollectionInferredQueries.undefined_head (HECollectionInferredQueries.currentOps external active primitive subtypes)
      external names before name _ absent
  number world policy before live scope value :=
    HECollectionArithmetic.number_undefined minimal nativePolicy external active primitive subtypes world policy live scope before value
  addition world := HECollectionArithmetic.addition_source minimal nativePolicy external active primitive subtypes world
  conditional world := HECollectionIfActivation.source_activation minimal nativePolicy external active primitive subtypes world
  superpose world := HECollectionSuperpose.source minimal nativePolicy external active primitive subtypes world

theorem source (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType) :
    ∃ rows : List Result,
      Stateful.AtomRel (environment minimal nativePolicy external active primitive subtypes) HECollectionSpaceExtension.space
        world live scope (HERangeUntypedEntry.rangeCall lower upper) expected before rows world (policy := policy) ∧
      (∀ row ∈ rows, NumericOrEmpty row.1) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] :=
  HERangeSourceAdequacy.range_source_world (ports minimal nativePolicy external active primitive subtypes)
    world policy before live scope lower upper expected demand

theorem retained_run (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
    (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)
    (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String)
    (lower upper : Int) (expected : Atom) (demand : expected = .symbol "Number" ∨ expected = Atom.undefinedType)
    (stack : List RecursiveTasks.Contextual.Continuation) (emitted : List Result) :
    let current := environment minimal nativePolicy external active primitive subtypes
    ∃ rows : List Result,
      RecursiveMachine.Contextual.WorldSteps current.view current.services current.dispatch current.lookup policy
        ⟨world, HECollectionSpaceExtension.space, .work (.atom live scope (HERangeUntypedEntry.rangeCall lower upper) expected before), stack, emitted⟩
        ⟨world, HECollectionSpaceExtension.space, .returning rows, stack, emitted⟩ (admission := current.arguments) ∧
      rows.map Prod.fst = values lower (upper - lower).toNat ++ [.symbol "Empty"] ∧
      (∀ row ∈ rows, isErrorAtom row.1.erase = false) ∧ rows.length = (upper - lower).toNat + 1 :=
  HERangeSourceAdequacy.retained_run_world (ports minimal nativePolicy external active primitive subtypes)
    world policy before live scope lower upper expected demand stack emitted

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRange
