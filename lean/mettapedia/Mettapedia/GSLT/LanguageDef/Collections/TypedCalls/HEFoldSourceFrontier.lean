import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldParameterCapture
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionSpaceExtension

/-! The standard fold equation is selected from the collection source space.
Its actual fresh rule instance earns the open-parameter capture and complete
physical equation frontier. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceFrontier

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation
open Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Match.SolutionTheory Spec.Bindings.ScopeObservation.ModelTransport
open HEFoldParameterCapture (query)

theorem complete_fixed_frame (policy : Policy) (live : List Atom) (before : Frame)
    (pairs : List Entry.Value) (init : Entry.Value) (left right : String)
    (different : left ≠ right)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right)
    (pairsClosed : TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) :
    ∃ (work : EquationWork) (after : Frame) (a b spaceName : String),
      EquationFrontierRel HECollectionSpaceExtension.space live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = HECollectionFoldFunction.function pairs init a b spaceName .active (operatorName := operatorName) (itemsMark := itemsMark) ∧
      a ≠ b ∧ a ≠ spaceName ∧ b ≠ spaceName ∧
      after.read policy (.var a) = .var a ∧ after.read policy (.var b) = .var b := by
  let avoid := EquationScope.visibleNames live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings ++ [left, right]
  let ruleVariables := (atomVariables CollectionStdlibSource.foldPattern ++ atomVariables CollectionStdlibSource.foldBody).eraseDups
  let rename := instanceName avoid ruleVariables 13
  let chosen := EquationFreshening.freshRule avoid 13 CollectionStdlibSource.foldPattern CollectionStdlibSource.foldBody
  have renameInjective : Function.Injective rename := instanceName_injective _ _ _
  have renameFresh (name : String) : rename name ∉ avoid := instanceName_not_mem _ _ _ _
  have renamedNotLeft (name : String) : rename name ≠ left := by
    intro same
    exact renameFresh name (by simp [avoid, same])
  have renamedNotRight (name : String) : rename name ≠ right := by
    intro same
    exact renameFresh name (by simp [avoid, same])
  have renamedOutside (name : String) : rename name ∉ specBindingVars before.bindings := by
    intro present
    exact renameFresh name (List.mem_append_left _
      ((EquationScope.mem_visibleNames_iff live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings _).mpr
        (EquationScope.binding_var_visible present)))
  let names : Fin 8 → String := ![left, right, rename "list", rename "init", rename "a", rename "b", rename "op", rename "space"]
  have nameInjective : Function.Injective names := by
    intro i j same
    fin_cases i <;> fin_cases j <;>
      simp_all [names, Function.Injective.eq_iff renameInjective, Ne.symm different,
        Ne.symm (renamedNotLeft _), Ne.symm (renamedNotRight _)]
  have nameFresh : ∀ i, 2 ≤ i.val → names i ∉ specBindingVars before.bindings := by
    intro i lower
    fin_cases i
    · norm_num at lower
    · norm_num at lower
    all_goals simpa [names] using renamedOutside _
  obtain ⟨captured, unified, bodyRead, aRead, bRead⟩ :=
    HEFoldParameterCapture.capture_fixed (operatorName := operatorName) (itemsMark := itemsMark) policy before names nameInjective nameFresh (by simpa [names] using leftFixed) (by simpa [names] using rightFixed)
      pairs init pairsClosed initClosed
  have patternShape : chosen.1 = HEFoldParameterCapture.pattern names := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, renameAtom, renameAtomList,
      CollectionStdlibSource.foldPattern, CollectionStdlibSource.app, names,
      HEFoldParameterCapture.pattern, rename, ruleVariables]
  have bodyShape : chosen.2 = HEFoldParameterCapture.body names := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, renameAtom, renameAtomList,
      CollectionStdlibSource.foldBody, CollectionStdlibSource.app, names,
      HEFoldParameterCapture.body, rename, ruleVariables]
  have sourceUnified : Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right)
      (Entry.Value.ofAtom chosen.1) captured.environment := by
    simpa only [patternShape, names, Matrix.cons_val_zero, Matrix.cons_val_one] using unified
  have alpha : AlphaVariantRel live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings
      CollectionStdlibSource.foldPattern CollectionStdlibSource.foldBody chosen.1 chosen.2 :=
    EquationFreshening.freshRule_alphaVariant_of_covers _ _ _ _ _ _ _
      (fun name visible => List.mem_append_left _
        ((EquationScope.mem_visibleNames_iff live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings name).mpr visible))
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment captured.environment)
  have model := Theory.normal_presentedValuation_satisfied captured.certified.normal
  have reached := (sourceUnified.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have equation : applyTypeValuation valuation (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase = applyTypeValuation valuation chosen.1 := by
    simpa only [Entry.Value.erase_ofAtom] using reached.2
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (valuation name))
      (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase chosen.1 := by
    unfold HEAtomEquationSatisfied
    rw [← encodeModelAtom_applyTypeValuation, ← encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom equation
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  let output : Bindings := ⟨matched.assignments ++ before.bindings.assignments, matched.equalities ++ before.bindings.equalities⟩
  have candidate : UnifyCandidateRel (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase (Entry.Value.ofAtom chosen.1).erase before.bindings output := by
    simpa only [Entry.Value.erase_ofAtom] using
      (show UnifyCandidateRel (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase chosen.1 before.bindings output from ⟨matched, matching, merged⟩)
  let after : Frame := ⟨output, captured.environment, sourceUnified.certifies before.certified candidate⟩
  let work : EquationWork := ⟨13, CollectionStdlibSource.foldPattern, CollectionStdlibSource.foldBody, chosen.1, chosen.2, output⟩
  have hit : EquationRowResultsRel live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings 13
      (CollectionStdlibSource.equation CollectionStdlibSource.foldPattern CollectionStdlibSource.foldBody) [work] :=
    .hit 13 _ _ _ _ matched output alpha matching merged
  have frontier : EquationFrontierRel HECollectionSpaceExtension.space live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings
      ([[], [], [], [], [], [], [], [], [], [], [], [], [], [work], [], [], [], [], [], [], [], [], [], [], [], []] :
        List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HECollectionSpaceExtension.space, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, CollectionStdlibSource.extensionRows, CollectionStdlibSource.authoredRows,
      CollectionStdlibSource.nativeTypeRows, CollectionStdlibSource.instructionTypeRows, Space.ofList,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons hit (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))))))))))))))))))))))
    all_goals first
      | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
      | dsimp only [query, Entry.Value.erase, List.map, HEFreshEquationFrames.Range.pattern,
          HERangeSourceProgram.emptyRule, HERangeSourceProgram.emptyPattern, CollectionStdlibSource.equation,
          CollectionStdlibSource.squarePattern, CollectionStdlibSource.collapsePattern, CollectionStdlibSource.letPattern,
          CollectionStdlibSource.app]
        simp only [Entry.Value.erase, List.map_cons, List.map_nil]
        apply HERangeEquationFrontiers.different_head_miss
        decide
  refine ⟨work, after, names 4, names 5, names 7, by simpa using frontier, rfl, sourceUnified, ?_,
    ?_, ?_, ?_, aRead, bRead⟩
  · change captured.read policy (Entry.Value.ofAtom chosen.2) = _
    rw [bodyShape]
    exact bodyRead
  all_goals intro same; have indices := nameInjective same; cases indices

theorem complete_frame (policy : Policy) (live : List Atom) (before : Frame)
    (pairs : List Entry.Value) (init : Entry.Value) (left right : String)
    (different : left ≠ right)
    (leftFresh : left ∉ specBindingVars before.bindings) (rightFresh : right ∉ specBindingVars before.bindings)
    (pairsClosed : TypeSubst.typeVarsList (pairs.map Entry.Value.erase) = [])
    (initClosed : TypeSubst.typeVars init.erase = [])
    (operatorName : String := CollectionStdlibSource.appendName) (itemsMark : Entry.Status := .active) :
    ∃ (work : EquationWork) (after : Frame) (a b spaceName : String),
      EquationFrontierRel HECollectionSpaceExtension.space live (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (query (operatorName := operatorName) (itemsMark := itemsMark) pairs init left right)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = HECollectionFoldFunction.function pairs init a b spaceName .active (operatorName := operatorName) (itemsMark := itemsMark) ∧
      a ≠ b ∧ a ≠ spaceName ∧ b ≠ spaceName ∧
      after.read policy (.var a) = .var a ∧ after.read policy (.var b) = .var b := by
  have leftFixed : before.read policy (.var left) = .var left := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before left leftFresh
  have rightFixed : before.read policy (.var right) = .var right := by
    simpa only [Frame.read, Entry.Value.substitute] using HEFreshSyntaxBinding.resolve_fresh before right rightFresh
  exact complete_fixed_frame policy live before pairs init left right different leftFixed rightFixed
    pairsClosed initClosed operatorName itemsMark

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEFoldSourceFrontier
