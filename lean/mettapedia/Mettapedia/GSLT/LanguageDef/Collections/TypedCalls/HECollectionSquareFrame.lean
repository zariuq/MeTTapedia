import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionRange
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEOpenSyntaxBinding

/-! The square equation's actual fresh source capture. Its reached frame
retains the caller and supplies both multiplication operands; neither a body
result nor an empty caller is assumed. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareFrame

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.SolutionTheory Spec.Bindings.ScopeObservation.ModelTransport

def call (value : Int) : Entry.Value := .expression .active [.symbol "sq", .grounded (.int value)]

theorem complete_frame (policy : Policy) (live : List Atom) (before : Frame) (value : Int) :
    ∃ (work : EquationWork) (after : Frame),
      EquationFrontierRel HECollectionSpaceExtension.space live (call value).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (call value) (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = HECollectionArithmetic.multiplication.call value value := by
  let chosen := EquationFreshening.freshRule (EquationScope.visibleNames live (call value).erase before.bindings) 9
    CollectionStdlibSource.squarePattern CollectionStdlibSource.squareBody
  have alpha := EquationFreshening.freshRule_alphaVariant live (call value).erase
    CollectionStdlibSource.squarePattern CollectionStdlibSource.squareBody before.bindings 9
  change AlphaVariantRel live (call value).erase before.bindings CollectionStdlibSource.squarePattern CollectionStdlibSource.squareBody
    chosen.1 chosen.2 at alpha
  obtain ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ := alpha
  have nameFresh : rename "x" ∉ specBindingVars before.bindings := by
    intro present
    apply fresh "x" (Or.inl ?_) (EquationScope.binding_var_visible present)
    exact .expression (by simp) (.var "x")
  have closed : TypeSubst.typeVars (Entry.Value.grounded (.int value)).erase = [] := by simp [Entry.Value.erase, TypeSubst.typeVars]
  let captured := HEFreshSyntaxBinding.bindFrame policy before (rename "x") (.grounded (.int value)) nameFresh (by simp [closed])
  have bound := HEFreshSyntaxBinding.source_binding policy before (rename "x") (.grounded (.int value)) nameFresh closed
  have read := HEFreshSyntaxBinding.bound_read policy before (rename "x") (.grounded (.int value)) nameFresh closed policy
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment (call value) (Entry.Value.ofAtom chosen.1) captured.environment := by
    rw [EquationFreshening.alphaRename_eq renamedPattern]
    apply Entry.Value.UnifyRel.ordinary
    simp only [CollectionStdlibSource.squarePattern, CollectionStdlibSource.app, renameTypeVars, call,
      Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.substitute,
      HEFreshSyntaxBinding.resolve_fresh before (rename "x") nameFresh, HEFreshEquationFrames.Range.active_rebuild]
    exact .expression (.cons (.ordinary (.identical (by simp [Entry.Value.substitute]))) (.cons bound (.nil _)))
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment captured.environment)
  have model := Theory.normal_presentedValuation_satisfied captured.certified.normal
  have reached := (unified.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have equation : applyTypeValuation valuation (call value).erase = applyTypeValuation valuation chosen.1 := by
    simpa only [Entry.Value.erase_ofAtom] using reached.2
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (valuation name)) (call value).erase chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [←encodeModelAtom_applyTypeValuation, ←encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  let output : Bindings := ⟨matched.assignments ++ before.bindings.assignments, matched.equalities ++ before.bindings.equalities⟩
  have candidate : UnifyCandidateRel (call value).erase (Entry.Value.ofAtom chosen.1).erase before.bindings output := by
    simpa only [Entry.Value.erase_ofAtom] using
      (show UnifyCandidateRel (call value).erase chosen.1 before.bindings output from ⟨matched, matching, merged⟩)
  let after : Frame := ⟨output, captured.environment, unified.certifies before.certified candidate⟩
  let work : EquationWork := ⟨9, CollectionStdlibSource.squarePattern, CollectionStdlibSource.squareBody, chosen.1, chosen.2, output⟩
  have hit : EquationRowResultsRel live (call value).erase before.bindings 9
      (CollectionStdlibSource.equation CollectionStdlibSource.squarePattern CollectionStdlibSource.squareBody) [work] :=
    .hit 9 _ _ _ _ matched output ⟨rename, injective, renamedPattern, renamedBody, fresh⟩ matching merged
  have frontier : EquationFrontierRel HECollectionSpaceExtension.space live (call value).erase before.bindings
      ([[], [], [], [], [], [], [], [], [], [work], [], [], [], [], [], [], [], [], [], [], [], [], [], [], []] :
        List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HECollectionSpaceExtension.space, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, CollectionStdlibSource.extensionRows, CollectionStdlibSource.authoredRows,
      CollectionStdlibSource.nativeTypeRows, CollectionStdlibSource.instructionTypeRows, Space.ofList,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons hit
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil))))))))))))))))))))))))
    all_goals first
      | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
      | dsimp only [call, Entry.Value.erase, List.map, HEFreshEquationFrames.Range.pattern,
          HERangeSourceProgram.emptyRule, HERangeSourceProgram.emptyPattern, CollectionStdlibSource.equation,
          CollectionStdlibSource.foldPattern, CollectionStdlibSource.collapsePattern, CollectionStdlibSource.letPattern,
          CollectionStdlibSource.app]
        simp only [Entry.Value.erase, List.map_cons, List.map_nil]
        apply HERangeEquationFrontiers.different_head_miss
        decide
  refine ⟨work, after, by simpa using frontier, rfl, unified, ?_⟩
  change captured.read policy (Entry.Value.ofAtom chosen.2) = _
  rw [EquationFreshening.alphaRename_eq renamedBody]
  have resolved : Entry.Value.resolve captured.environment (rename "x") = .grounded (.int value) := by
    simpa only [Frame.read, Entry.Value.substitute] using read
  simp only [CollectionStdlibSource.squareBody, CollectionStdlibSource.app, renameTypeVars, Entry.Value.ofAtom,
    List.map_cons, List.map_nil, Frame.read, Entry.Value.substitute, resolved, HEFreshEquationFrames.Range.active_rebuild,
    HEBinaryNumericSource.Operation.call, HECollectionArithmetic.multiplication]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSquareFrame
