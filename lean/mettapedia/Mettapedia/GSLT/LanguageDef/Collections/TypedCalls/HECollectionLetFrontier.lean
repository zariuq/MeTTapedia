import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetCapture

/-!
# The complete authored-let frontier with open caller binders

Selection uses the actual physical let row. All other rows are checked as
annotations or different-headed equations. Freshening avoids both the live
caller and the three open variables of the consumer template.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetFrontier

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps Spec.Type.Presentation Spec.Bindings.ScopeObservation
open HECollectionLetCapture (call instruction)

theorem complete_frame (policy : Policy) (live : List Atom) (before : Frame)
    (values : List Int) (init : Int) (listName left right : String) (itemsMark : Entry.Status)
    (listLeft : listName ≠ left) (listRight : listName ≠ right) (different : left ≠ right)
    (listFixed : before.read policy (.var listName) = .var listName)
    (leftFixed : before.read policy (.var left) = .var left) (rightFixed : before.read policy (.var right) = .var right) :
    ∃ (work : EquationWork) (after : Frame) (patternName : String),
      EquationFrontierRel HECollectionSpaceExtension.space live (call values init listName left right itemsMark).erase before.bindings [work] ∧
      after.bindings = work.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment (call values init listName left right itemsMark)
        (Entry.Value.ofAtom work.pattern) after.environment ∧
      after.read policy (Entry.Value.ofAtom work.body) = instruction values init patternName left right itemsMark ∧
      patternName ≠ left ∧ patternName ≠ right ∧
      after.read policy (.var patternName) = .var patternName ∧
      after.read policy (.var left) = .var left ∧ after.read policy (.var right) = .var right := by
  let avoid := EquationScope.visibleNames live (call values init listName left right itemsMark).erase before.bindings ++ [listName, left, right]
  let ruleVariables := (atomVariables CollectionStdlibSource.letPattern ++ atomVariables CollectionStdlibSource.letBody).eraseDups
  let rename := instanceName avoid ruleVariables 15
  let chosen := EquationFreshening.freshRule avoid 15 CollectionStdlibSource.letPattern CollectionStdlibSource.letBody
  have renameInjective : Function.Injective rename := instanceName_injective _ _ _
  have renameFresh (name : String) : rename name ∉ avoid := instanceName_not_mem _ _ _ _
  have notList (name : String) : rename name ≠ listName := by
    intro same
    exact renameFresh name (by simp [avoid, same])
  have notLeft (name : String) : rename name ≠ left := by
    intro same
    exact renameFresh name (by simp [avoid, same])
  have notRight (name : String) : rename name ≠ right := by
    intro same
    exact renameFresh name (by simp [avoid, same])
  have outside (name : String) : rename name ∉ specBindingVars before.bindings := by
    intro present
    exact renameFresh name (List.mem_append_left _
      ((EquationScope.mem_visibleNames_iff live (call values init listName left right itemsMark).erase before.bindings _).mpr
        (EquationScope.binding_var_visible present)))
  let names : Fin 6 → String := ![listName, left, right, rename "pattern", rename "atom", rename "template"]
  have injective : Function.Injective names := by
    intro i j same
    fin_cases i <;> fin_cases j <;>
      simp_all [names, Function.Injective.eq_iff renameInjective, Ne.symm listLeft, Ne.symm listRight,
        Ne.symm different, Ne.symm (notList _), Ne.symm (notLeft _), Ne.symm (notRight _)]
  have fresh : ∀ i, 3 ≤ i.val → names i ∉ specBindingVars before.bindings := by
    intro i lower
    fin_cases i
    · norm_num at lower
    · norm_num at lower
    · norm_num at lower
    all_goals simpa [names] using outside _
  have fixed : ∀ i, i.val < 3 → before.read policy (.var (names i)) = .var (names i) := by
    intro i small
    fin_cases i
    · simpa [names] using listFixed
    · simpa [names] using leftFixed
    · simpa [names] using rightFixed
    all_goals norm_num at small
  obtain ⟨after, candidate, unified, bodyRead, patternFixed, keptLeft, keptRight⟩ :=
    HECollectionLetCapture.capture policy before names injective fresh fixed values init itemsMark
  have patternShape : chosen.1 = HECollectionLetCapture.pattern names := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, renameAtom, renameAtomList,
      CollectionStdlibSource.letPattern, CollectionStdlibSource.app, HECollectionLetCapture.pattern, names, rename, ruleVariables]
  have bodyShape : chosen.2 = HECollectionLetCapture.body names := by
    simp [chosen, EquationFreshening.freshRule, freshenEquationAvoiding, renameAtom, renameAtomList,
      CollectionStdlibSource.letBody, CollectionStdlibSource.app, HECollectionLetCapture.body, names, rename, ruleVariables, Atom.empty]
  have sourceCandidate : UnifyCandidateRel (call values init listName left right itemsMark).erase chosen.1 before.bindings after.bindings := by
    simpa [patternShape, names] using candidate
  obtain ⟨matched, matching, merged⟩ := sourceCandidate
  have alpha : AlphaVariantRel live (call values init listName left right itemsMark).erase before.bindings
      CollectionStdlibSource.letPattern CollectionStdlibSource.letBody chosen.1 chosen.2 :=
    EquationFreshening.freshRule_alphaVariant_of_covers _ _ _ _ _ _ _
      (fun name visible => List.mem_append_left _
        ((EquationScope.mem_visibleNames_iff live (call values init listName left right itemsMark).erase before.bindings name).mpr visible))
  let work : EquationWork := ⟨15, CollectionStdlibSource.letPattern, CollectionStdlibSource.letBody, chosen.1, chosen.2, after.bindings⟩
  have hit : EquationRowResultsRel live (call values init listName left right itemsMark).erase before.bindings 15
      (CollectionStdlibSource.equation CollectionStdlibSource.letPattern CollectionStdlibSource.letBody) [work] :=
    .hit 15 _ _ _ _ matched after.bindings alpha matching merged
  have frontier : EquationFrontierRel HECollectionSpaceExtension.space live (call values init listName left right itemsMark).erase before.bindings
      ([[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [work], [], [], [], [], [], [], [], [], [], []] :
        List (List EquationWork)).flatten := by
    apply EquationFrontierRel.completed
    simp only [HECollectionSpaceExtension.space, HERangeSourceProgram.space, HERangeSourceProgram.declaredSpace,
      HEIfSourceSelection.Range.space, CollectionStdlibSource.extensionRows, CollectionStdlibSource.authoredRows,
      CollectionStdlibSource.nativeTypeRows, CollectionStdlibSource.instructionTypeRows, Space.ofList,
      List.cons_append, List.nil_append, List.zipIdx_cons, List.zipIdx_nil]
    refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
      (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons hit (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_
        (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))))))))))))))))))))))))
    all_goals first
      | exact HERangeEquationFrontiers.annotation_irrelevant _ _ _ _ _ _
      | dsimp only [call, Entry.Value.erase, List.map, HEFreshEquationFrames.Range.pattern,
          HERangeSourceProgram.emptyRule, HERangeSourceProgram.emptyPattern, CollectionStdlibSource.equation,
          CollectionStdlibSource.squarePattern, CollectionStdlibSource.collapsePattern, CollectionStdlibSource.foldPattern,
          CollectionStdlibSource.app]
        simp only [Entry.Value.erase, List.map_cons, List.map_nil]
        apply HERangeEquationFrontiers.different_head_miss
        decide
  refine ⟨work, after, names 3, by simpa using frontier, rfl, ?_, ?_, ?_, ?_, patternFixed, keptLeft, keptRight⟩
  · simpa [work, patternShape, names] using unified
  · change after.read policy (Entry.Value.ofAtom chosen.2) = _
    rw [bodyShape]
    exact bodyRead
  · exact notLeft "pattern"
  · exact notRight "pattern"

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HECollectionLetFrontier
