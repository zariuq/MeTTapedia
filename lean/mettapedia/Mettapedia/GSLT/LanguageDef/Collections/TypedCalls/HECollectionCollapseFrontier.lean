import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFunction

/-!
# Fresh source selection of the authored collapse equation

The complete physical frontier is derived from the extended source space.
Matching captures the held square/range syntax, not its evaluated answers.
The unused local binders remain fresh in the reached frame's full support.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFrontier

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.SolutionTheory Spec.Bindings.ScopeObservation.ModelTransport

def call (lower upper : Int) : Entry.Value :=
  .expression .active [.symbol "collapse", HECollectionSquareRange.call lower upper]

theorem call_closed (lower upper : Int) : TypeSubst.typeVars (call lower upper).erase = [] := by
  simp only [call, Entry.Value.erase, List.map_cons, List.map_nil, TypeSubst.typeVars,
    TypeSubst.typeVarsList, HECollectionSquareRange.call_closed, List.nil_append]

theorem complete_frame_scoped (policy : Policy) (live : List Atom) (before : Frame) (lower upper : Int) :
    ∃ (work : EquationWork) (after : Frame) (rename : String → String),
      Function.Injective rename ∧
      EquationFrontierRel HECollectionSpaceExtension.space live (call lower upper).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (call lower upper)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) =
        HECollectionCollapseFunction.function lower upper (rename "space") (rename "eval") (rename "result")
          (rename "res") (rename "item") ∧
      (∀ name, name ≠ "atom" → rename name ∉ specBindingVars after.bindings) ∧
      (∀ original name, QueryVisibleName live (call lower upper).erase before.bindings name → rename original ≠ name) := by
  let avoid := EquationScope.visibleNames live (call lower upper).erase before.bindings
  let ruleVariables := (atomVariables CollectionStdlibSource.collapsePattern ++ atomVariables CollectionStdlibSource.collapseBody).eraseDups
  let rename := instanceName avoid ruleVariables 11
  let chosen := EquationFreshening.freshRule avoid 11 CollectionStdlibSource.collapsePattern CollectionStdlibSource.collapseBody
  have injective : Function.Injective rename := instanceName_injective _ _ _
  have fresh (name : String) : rename name ∉ specBindingVars before.bindings := by
    intro present
    exact instanceName_not_mem avoid ruleVariables 11 name
      ((EquationScope.mem_visibleNames_iff live (call lower upper).erase before.bindings _).mpr
        (EquationScope.binding_var_visible present))
  have patternShape : chosen.1 = renameTypeVars rename CollectionStdlibSource.collapsePattern := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, CollectionStdlibSource.collapsePattern,
      CollectionStdlibSource.app, renameAtom, renameAtomList, renameTypeVars, rename, ruleVariables]
  have bodyShape : chosen.2 = renameTypeVars rename CollectionStdlibSource.collapseBody := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, CollectionStdlibSource.collapseBody,
      CollectionStdlibSource.app, Atom.undefinedType, renameAtom, renameAtomList, renameTypeVars, rename, ruleVariables]
  have closed := HECollectionSquareRange.call_closed lower upper
  let captured := HEFreshSyntaxBinding.bindFrame policy before (rename "atom") (HECollectionSquareRange.call lower upper)
    (fresh "atom") (by simp [closed])
  have bound := HEFreshSyntaxBinding.source_binding policy before (rename "atom") (HECollectionSquareRange.call lower upper)
    (fresh "atom") closed
  have read := HEFreshSyntaxBinding.bound_read policy before (rename "atom") (HECollectionSquareRange.call lower upper)
    (fresh "atom") closed policy
  have unified : Entry.Value.UnifyRel policy.rebuilding before.environment (call lower upper)
      (Entry.Value.ofAtom chosen.1) captured.environment := by
    rw [patternShape]
    apply Entry.Value.UnifyRel.ordinary
    have fixed := HEFreshSyntaxBinding.ground_substitution policy.rebuilding (Entry.Value.resolve before.environment)
      (HECollectionSquareRange.call lower upper) closed
    simp only [CollectionStdlibSource.collapsePattern, CollectionStdlibSource.app, renameTypeVars, call,
      Entry.Value.ofAtom, List.map_cons, List.map_nil, Entry.Value.substitute,
      HEFreshSyntaxBinding.resolve_fresh before (rename "atom") (fresh "atom"),
      HEFreshEquationFrames.Range.active_rebuild] at fixed ⊢
    rw [fixed]
    exact .expression (.cons (.ordinary (.identical (by simp [Entry.Value.substitute]))) (.cons bound (.nil _)))
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment captured.environment)
  have model := Theory.normal_presentedValuation_satisfied captured.certified.normal
  have reached := (unified.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have equation : applyTypeValuation valuation (call lower upper).erase = applyTypeValuation valuation chosen.1 := by
    simpa only [Entry.Value.erase_ofAtom] using reached.2
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (valuation name)) (call lower upper).erase chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [←encodeModelAtom_applyTypeValuation, ←encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  let output : Bindings := ⟨matched.assignments ++ before.bindings.assignments, matched.equalities ++ before.bindings.equalities⟩
  have candidate : UnifyCandidateRel (call lower upper).erase (Entry.Value.ofAtom chosen.1).erase before.bindings output := by
    simpa only [Entry.Value.erase_ofAtom] using
      (show UnifyCandidateRel (call lower upper).erase chosen.1 before.bindings output from ⟨matched, matching, merged⟩)
  let after : Frame := ⟨output, captured.environment, unified.certifies before.certified candidate⟩
  let work : EquationWork := ⟨11, CollectionStdlibSource.collapsePattern, CollectionStdlibSource.collapseBody, chosen.1, chosen.2, output⟩
  have alpha := EquationFreshening.freshRule_alphaVariant live (call lower upper).erase
    CollectionStdlibSource.collapsePattern CollectionStdlibSource.collapseBody before.bindings 11
  have hit : EquationRowResultsRel live (call lower upper).erase before.bindings 11
      (CollectionStdlibSource.equation CollectionStdlibSource.collapsePattern CollectionStdlibSource.collapseBody) [work] :=
    .hit 11 _ _ _ _ matched output alpha matching merged
  have frontier : EquationFrontierRel HECollectionSpaceExtension.space live (call lower upper).erase before.bindings
      ([[], [], [], [], [], [], [], [], [], [], [], [work], [], [], [], [], [], [], [], [], [], [], [], [], [], []] :
        List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HECollectionSpaceExtension.space, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, CollectionStdlibSource.extensionRows, CollectionStdlibSource.authoredRows,
      CollectionStdlibSource.nativeTypeRows, CollectionStdlibSource.instructionTypeRows, Space.ofList,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons hit (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))))))))))))))))))))))
    all_goals first
      | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
      | dsimp only [call, Entry.Value.erase, List.map, HEFreshEquationFrames.Range.pattern,
          HERangeSourceProgram.emptyRule, HERangeSourceProgram.emptyPattern, CollectionStdlibSource.equation,
          CollectionStdlibSource.squarePattern, CollectionStdlibSource.foldPattern, CollectionStdlibSource.letPattern,
          CollectionStdlibSource.app]
        simp only [Entry.Value.erase, List.map_cons, List.map_nil]
        apply HERangeEquationFrontiers.different_head_miss
        decide
  have support (name : String) : name ∈ specBindingVars output ↔ name = rename "atom" ∨ name ∈ specBindingVars before.bindings := by
    rw [mem_specBindingVars_append matched before.bindings name, QueryBindingProjection.SourceSupport.match_support matching name,
      call_closed, patternShape]
    simp [CollectionStdlibSource.collapsePattern, CollectionStdlibSource.app, renameTypeVars,
      TypeSubst.typeVars, TypeSubst.typeVarsList]
  refine ⟨work, after, rename, injective, by simpa using frontier, rfl, unified, ?_, ?_, ?_⟩
  · change captured.read policy (Entry.Value.ofAtom chosen.2) = _
    rw [bodyShape]
    have resolved (name : String) : Entry.Value.resolve captured.environment (rename name) =
        if name = "atom" then HECollectionSquareRange.call lower upper else .var (rename name) := by
      by_cases same : name = "atom"
      · subst name
        simpa only [Frame.read, Entry.Value.substitute, ↓reduceIte] using read
      · have apart : rename name ≠ rename "atom" := fun equal => same (injective equal)
        have stillFresh := HEFreshSyntaxBinding.other_stays_fresh policy before (rename "atom") (rename name)
          (HECollectionSquareRange.call lower upper) (fresh "atom") (fresh name) apart closed
        simpa only [if_neg same] using HEFreshSyntaxBinding.resolve_fresh captured (rename name) stillFresh
    simp only [CollectionStdlibSource.collapseBody, CollectionStdlibSource.app, renameTypeVars, Entry.Value.ofAtom,
      List.map_cons, List.map_nil, Frame.read, Entry.Value.substitute, resolved,
      HEFreshEquationFrames.Range.active_rebuild, HECollectionCollapseFunction.function, HECollectionCollapseFunction.body,
      HECollectionCollapseFunction.template, HECollectionCollapseControl.foldContinuation,
      HECollectionCollapseControl.foldCall, HECollectionFoldSourceLoop.operation]
    simp [Atom.undefinedType, renameTypeVars, Entry.Value.ofAtom, Entry.Value.substitute]
  · intro name different present
    rcases (support (rename name)).mp present with same | old
    · exact different (injective same)
    · exact fresh name old
  · intro original name visible same
    apply instanceName_not_mem avoid ruleVariables 11 original
    change rename original ∈ avoid
    rw [same]
    exact (EquationScope.mem_visibleNames_iff live (call lower upper).erase before.bindings name).mpr visible

theorem complete_frame (policy : Policy) (live : List Atom) (before : Frame) (lower upper : Int) :
    ∃ (work : EquationWork) (after : Frame) (rename : String → String),
      Function.Injective rename ∧
      EquationFrontierRel HECollectionSpaceExtension.space live (call lower upper).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (call lower upper)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) =
        HECollectionCollapseFunction.function lower upper (rename "space") (rename "eval") (rename "result")
          (rename "res") (rename "item") ∧
      (∀ name, name ≠ "atom" → rename name ∉ specBindingVars after.bindings) := by
  obtain ⟨work, after, rename, injective, frontier, bindings, unified, bodyRead, fresh, _avoids⟩ :=
    complete_frame_scoped policy live before lower upper
  exact ⟨work, after, rename, injective, frontier, bindings, unified, bodyRead, fresh⟩

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionCollapseFrontier
