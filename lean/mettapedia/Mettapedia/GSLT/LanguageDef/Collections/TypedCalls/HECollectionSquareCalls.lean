import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareFrame

/-! Reached numeric square calls and the separate terminal Empty route.
Empty is not fed to the numeric equation; its complete source query is absent
and the ordinary call boundary preserves the sentinel. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCalls

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation Spec.Type.RuntimeRefinement
open Spec.Bindings.ScopeObservation
open RetainedTypePayloads (ExternalView)
open HECollectionWorld (World environment)
open HECollectionSquareFrame (call)

theorem symbol_expression_miss (live : List Atom) (before : Bindings) (position : Nat)
    (name : String) (children : List Atom) (body : Atom) :
    EquationRowResultsRel live (.symbol name) before position (.expression [.symbol "=", .expression children, body]) [] := by
  let chosen := EquationFreshening.freshRule (EquationScope.visibleNames live (.symbol name) before) position (.expression children) body
  have alpha := EquationFreshening.freshRule_alphaVariant live (.symbol name) (.expression children) body before position
  change AlphaVariantRel live (.symbol name) before (.expression children) body chosen.1 chosen.2 at alpha
  apply EquationRowResultsRel.miss position (.expression children) body chosen.1 chosen.2 alpha
  intro otherPattern otherBody variant matched output candidate
  obtain ⟨_, _, renamed, _, _⟩ := variant
  obtain ⟨valuation, model⟩ := candidate.2.2
  have equal := ((UnifyCandidateRel.solutions ⟨matched, candidate.1, candidate.2⟩ valuation).mp model).1
  rw [EquationFreshening.alphaRename_eq renamed] at equal
  simp [applyTypeValuation, renameTypeVars] at equal

theorem symbol_frontier (live : List Atom) (before : Bindings) (name : String) :
    EquationFrontierRel HECollectionSpaceExtension.space live (.symbol name) before [] := by
  have scanned : EquationFrontierRel HECollectionSpaceExtension.space live (.symbol name) before
      ([[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []] :
        List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HECollectionSpaceExtension.space, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, CollectionStdlibSource.extensionRows, CollectionStdlibSource.authoredRows,
      CollectionStdlibSource.nativeTypeRows, CollectionStdlibSource.instructionTypeRows, Space.ofList,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))))))))))))))))))
    all_goals first
      | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
      | dsimp only [HEFreshEquationFrames.Range.pattern, HERangeSourceProgram.emptyRule, HERangeSourceProgram.emptyPattern,
          CollectionStdlibSource.equation, CollectionStdlibSource.squarePattern, CollectionStdlibSource.foldPattern,
          CollectionStdlibSource.collapsePattern, CollectionStdlibSource.letPattern, CollectionStdlibSource.app]
        exact symbol_expression_miss _ _ _ _ _ _
  simpa using scanned

variable (minimal : Minimal.Services) (nativePolicy : Policy) (external : ExternalView)
  (active : String → Bool) (primitive : TypeNormalizationScope.Primitive) (subtypes : List Atom → List Atom)

local notation "current" => environment minimal nativePolicy external active primitive subtypes
local notation "sourceSpace" => HECollectionSpaceExtension.space

theorem number_call (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (value : Int) :
    ∃ after, Stateful.CallRel current sourceSpace world live scope (call value) (.symbol "Number") before
      [(.grounded (.int (value * value)), after)] world (policy := policy) := by
  obtain ⟨work, after, frontier, bound, unified, read⟩ :=
    HECollectionSquareFrame.complete_frame policy (.symbol "Number" :: live) before value
  let body := HECollectionArithmetic.multiplication.call value value
  have bodyPlain : ¬FunctionPending policy body := by
    simp [body, HEBinaryNumericSource.Operation.call, HECollectionArithmetic.multiplication, FunctionPending,
      Minimal.IsFunction, Entry.Value.erase]
  have bodySource := HECollectionArithmetic.multiplication_source minimal nativePolicy external active primitive subtypes
    world policy after live scope value value
  refine ⟨after, Stateful.CallRel.equations (works := [work]) ?_ ?_ frontier (by simp) ?_⟩
  · simp [call, Entry.Value.erase, IsErrorRel]
  · simpa only [call, Entry.Value.erase, List.map_cons, List.map_nil] using
      HECollectionWorld.ordinary minimal nativePolicy external active primitive subtypes "sq" [.grounded (.int value)] (by simp)
  · apply Stateful.EquationBodiesRel.cons (world1 := world) (world2 := world)
      (produced := [(body, after)]) (children := [(.grounded (.int (value * value)), after)]) bound unified
    · rw [read]
      exact .producerRaw bodyPlain
    · apply Stateful.BoundaryBatchRel.single_iff.mpr
      exact .returned (.evaluate
        (by simp [body, HEBinaryNumericSource.Operation.call, HECollectionArithmetic.multiplication, Entry.Value.erase, Atom.notReducible])
        (by simp [body, HEBinaryNumericSource.Operation.call, HECollectionArithmetic.multiplication, Entry.Value.erase,
          IsEmptyOrErrorRel, IsErrorRel, Atom.empty]) bodySource)
    · exact .nil

theorem empty_call (world : World) (policy : Policy) (before : Frame) (live : List Atom) (scope : List String) (expected : Atom) :
    Stateful.CallRel current sourceSpace world live scope (.symbol "Empty") expected before
      [(.symbol "Empty", before)] world (policy := policy) := by
  apply Stateful.CallRel.absent
  · simp [Entry.Value.erase, IsErrorRel]
  · simp [NonGroundedCallRel, Minimal.HostCall, Entry.Value.erase, Minimal.embeddedInstruction]
  · simpa only [Entry.Value.erase, environment, id_eq] using symbol_frontier (expected :: live) before.bindings "Empty"

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareCalls
