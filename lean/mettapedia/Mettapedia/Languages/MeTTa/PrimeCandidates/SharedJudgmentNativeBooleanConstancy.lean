import Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanRegion

/-!
# Native weak constancy and the derived Boolean uniqueness theorem

The based Boolean selector is proved weakly constant by the datatype's
dependent eliminator. Equal-constructor branches compute to one reflexivity
proof; opposite-constructor branches use the native discrimination proof.
The closed native Hedberg construction then derives uniqueness. No UIP,
decision oracle or external path-elimination capability is assumed.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanConstancy

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Presentation Presentation.Declaration Presentation.FormationSensitive RussellTarski
open FormationSensitiveBasedIdentity (doubleWeaken)
open SharedJudgmentNativeBooleanRegion

variable {n m : Nat}

def comparisonType (side : Bool) (right first second : Tower.Tm n) : Tower.Tm n :=
  .id (pathType side right) (selected side right first) (selected side right second)

@[simp] theorem comparisonType_subst (sigma : Sub Tower.Head n m) (side : Bool)
    (right first second : Tower.Tm n) :
    subst sigma (comparisonType side right first second) =
      comparisonType side (subst sigma right) (subst sigma first) (subst sigma second) := by
  simp only [comparisonType, subst, pathType_subst, selected_subst]

theorem comparisonType_formed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right first second : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm)
    (firstTyped : Typing rules context first (pathType side right))
    (secondTyped : Typing rules context second (pathType side right)) :
    Typing rules context (comparisonType side right first second) (sortTm zero) :=
  .idForm (pathType_formed side rightTyped) (.sort zero)
    (selected_typed side formed rightTyped firstTyped) (selected_typed side formed rightTyped secondTyped)

def pathsContext (context : Tower.Ctx n) (side : Bool) (right : Tower.Tm n) : Tower.Ctx (n + 2) :=
  .snoc (.snoc context (pathType side right)) (rename wk (pathType side right))

theorem paths_context_formed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    ContextFormation rules (pathsContext context side right) :=
  .snoc (.snoc formed (pathType_formed side rightTyped) (.sort zero))
    (pathType_formed side rightTyped).weaken (.sort zero)

theorem right_twice_typed (side : Bool) {context : Tower.Ctx n} {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules (pathsContext context side right) (doubleWeaken right) boolTm := by
  simpa only [pathsContext, doubleWeaken, rename, boolTm] using
    (rightTyped.weaken (extension := pathType side right)).weaken
      (extension := rename wk (pathType side right))

theorem first_path_typed (side : Bool) (context : Tower.Ctx n) (right : Tower.Tm n) :
    Typing rules (pathsContext context side right) (.var 1) (pathType side (doubleWeaken right)) := by
  have indexEq : (0 : Fin (n + 1)).succ = (1 : Fin (n + 2)) := by ext; simp
  have first := Typing.var (R := rules) (Γ := pathsContext context side right) (0 : Fin (n + 1)).succ
  simp only [pathsContext, Ctx.lookup_snoc_succ, Ctx.lookup_snoc_zero, pathType_rename] at first
  rw [indexEq] at first
  simpa only [pathsContext, doubleWeaken, pathType_rename] using first

theorem second_path_typed (side : Bool) (context : Tower.Ctx n) (right : Tower.Tm n) :
    Typing rules (pathsContext context side right) (.var 0) (pathType side (doubleWeaken right)) := by
  simpa only [pathsContext, Ctx.lookup_snoc_zero, pathType_rename, doubleWeaken] using
    (Typing.var (R := rules) (Γ := pathsContext context side right) 0)

def weakType (side : Bool) (right : Tower.Tm n) : Tower.Tm n :=
  .pi (pathType side right) (.pi (rename wk (pathType side right))
    (comparisonType side (doubleWeaken right) (.var 1) (.var 0)))

theorem weakBody_formed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules (pathsContext context side right)
      (comparisonType side (doubleWeaken right) (.var 1) (.var 0)) (sortTm zero) :=
  comparisonType_formed side (paths_context_formed side formed rightTyped)
    (right_twice_typed side rightTyped) (first_path_typed side context right) (second_path_typed side context right)

theorem weakType_formed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules context (weakType side right) (sortTm zero) :=
  pi_formed (pathType_formed side rightTyped)
    (pi_formed (pathType_formed side rightTyped).weaken (weakBody_formed side formed rightTyped))

theorem weak_abstract (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) {body : Tower.Tm (n + 2)}
    (bodyTyped : Typing rules (pathsContext context side right) body
      (comparisonType side (doubleWeaken right) (.var 1) (.var 0))) :
    Typing rules context (.lam (.lam body)) (weakType side right) :=
  lambda_typed (pathType_formed side rightTyped)
    (pi_formed (pathType_formed side rightTyped).weaken (weakBody_formed side formed rightTyped))
    (lambda_typed (pathType_formed side rightTyped).weaken
      (weakBody_formed side formed rightTyped) bodyTyped)

def sameConstancy (side : Bool) : Tower.Tm n := .lam (.lam (.refl (.refl (point side))))

theorem sameConstancy_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) :
    Typing rules context (sameConstancy side) (weakType side (point side)) := by
  apply weak_abstract side formed (point_typed side context)
  have pathsFormed := paths_context_formed side formed (point_typed side context)
  have first := first_path_typed side context (point side)
  have second := second_path_typed side context (point side)
  have pointTwice : doubleWeaken (point side : Tower.Tm n) = point side := by
    simp only [doubleWeaken, point_rename]
  rw [pointTwice] at first second ⊢
  exact SharedJudgmentNativeHedberg.comparison_from_common_conversion (.sort zero)
    (pathType_formed side (point_typed side _))
    (selected_typed side pathsFormed (point_typed side _) first)
    (selected_typed side pathsFormed (point_typed side _) second)
    (.reflIntro (point_typed side _))
    (selected_same_conversion side (.var 1)) (selected_same_conversion side (.var 0))

def oppositeConstancy (side : Bool) : Tower.Tm n :=
  .lam (.lam (emptyEliminate (discriminate side (.var 1))
    (comparisonType side (point (!side)) (.var 1) (.var 0))))

theorem oppositeConstancy_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) :
    Typing rules context (oppositeConstancy side) (weakType side (point (!side))) := by
  apply weak_abstract side formed (point_typed (!side) context)
  have pathsFormed := paths_context_formed side formed (point_typed (!side) context)
  have first := first_path_typed side context (point (!side))
  have second := second_path_typed side context (point (!side))
  have pointTwice : doubleWeaken (point (!side) : Tower.Tm n) = point (!side) := by
    simp only [doubleWeaken, point_rename]
  rw [pointTwice] at first second ⊢
  exact empty_eliminate_typed (discriminate_typed side pathsFormed first)
    (comparisonType_formed side pathsFormed (point_typed (!side) _) first second)

@[simp] theorem weakType_subst (sigma : Sub Tower.Head n m) (side : Bool) (right : Tower.Tm n) :
    subst sigma (weakType side right) = weakType side (subst sigma right) := by
  simp only [weakType, subst, pathType_subst, subst_liftSub_wk, comparisonType_subst,
    doubleWeaken, liftSub, subst_liftSub_wk]
  rfl

@[simp] theorem weakType_inst (side : Bool) (right : Tower.Tm n) :
    inst0 right (weakType side (.var 0)) = weakType side right := by
  simp only [inst0, weakType_subst, subst, subst0, Fin.cases_zero]

def weakAt (side : Bool) (right : Tower.Tm n) : Tower.Tm n :=
  casesTerm (weakType side (.var 0)) (if side then oppositeConstancy side else sameConstancy side)
    (if side then sameConstancy side else oppositeConstancy side) right

theorem weakAt_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm) :
    Typing rules context (weakAt side right) (weakType side right) := by
  have cases : Typing rules context (weakAt side right) (inst0 right (weakType side (.var 0))) := by
    apply cases_typed (level := zero) (by intro valuation; simp [zero, two, one, LevelTower.zero, LevelExpr.eval])
      (weakType_formed side (.snoc formed (bool_typed context) (.sort zero)) (.var 0)) _ _ rightTyped
    · cases side
      · exact sameConstancy_typed false formed
      · exact oppositeConstancy_typed true formed
    · cases side
      · exact oppositeConstancy_typed false formed
      · exact sameConstancy_typed true formed
  simpa only [weakType_inst] using cases

def weakComparison (side : Bool) (right first second : Tower.Tm n) : Tower.Tm n :=
  .app (.app (weakAt side right) first) second

theorem weakComparison_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right first second : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm)
    (firstTyped : Typing rules context first (pathType side right))
    (secondTyped : Typing rules context second (pathType side right)) :
    Typing rules context (weakComparison side right first second) (comparisonType side right first second) := by
  have firstApplication := Typing.appElim (weakAt_typed side formed rightTyped) firstTyped
  have atOne : liftSub (subst0 first) (1 : Fin (n + 2)) = rename wk first := by
    rw [← Fin.succ_zero_eq_one]
    rfl
  have firstExact : Typing rules context (.app (weakAt side right) first)
      (.pi (pathType side right) (comparisonType side (rename wk right) (rename wk first) (.var 0))) := by
    simpa only [weakType, inst0, subst, subst_liftSub_wk, comparisonType_subst,
      doubleWeaken, atOne, liftSub_zero, SharedJudgmentNativeHedberg.subst0_weaken,
      subst0, Fin.cases_succ, Fin.cases_zero] using firstApplication
  simpa only [weakComparison, inst0, comparisonType_subst,
    SharedJudgmentNativeHedberg.subst0_weaken, subst, subst0, Fin.cases_zero] using
    Typing.appElim firstExact secondTyped

def uniqueness (side : Bool) (right first second : Tower.Tm n) : Tower.Tm n :=
  SharedJudgmentNativeHedberg.hedberg boolTm (point side) (selector side) right first second
    (weakComparison side right first second)

theorem uniqueness_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {right first second : Tower.Tm n}
    (rightTyped : Typing rules context right boolTm)
    (firstTyped : Typing rules context first (pathType side right))
    (secondTyped : Typing rules context second (pathType side right)) :
    Typing rules context (uniqueness side right first second) (.id (pathType side right) first second) :=
  (SharedJudgmentNativeHedberg.hedberg_in_extension signature formed (bool_typed_one context)
    (point_typed side context) (selector_typed side formed) rightTyped firstTyped secondTyped
    (weakComparison_typed side formed rightTyped firstTyped secondTyped)).typing

def tripleWeaken (term : Tower.Tm n) : Tower.Tm (n + 3) := rename wk (doubleWeaken term)

def basedUniquenessType (left : Tower.Tm n) : Tower.Tm n :=
  .pi boolTm (.pi (.id boolTm (rename wk left) (.var 0))
    (.pi (.id boolTm (doubleWeaken left) (.var 1))
      (.id (.id boolTm (tripleWeaken left) (.var 2)) (.var 1) (.var 0))))

def basedUniquenessContext (context : Tower.Ctx n) (left : Tower.Tm n) : Tower.Ctx (n + 3) :=
  .snoc (.snoc (.snoc context boolTm) (.id boolTm (rename wk left) (.var 0)))
    (.id boolTm (doubleWeaken left) (.var 1))

theorem weaken_boolean {context : Tower.Ctx n} {term extension : Tower.Tm n}
    (typed : Typing rules context term boolTm) :
    Typing rules (.snoc context extension) (rename wk term) boolTm := typed.weaken

theorem basedUniquenessContext_formed {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {left : Tower.Tm n}
    (leftTyped : Typing rules context left boolTm) :
    ContextFormation rules (basedUniquenessContext context left) :=
  .snoc (.snoc (.snoc formed (bool_typed context) (.sort zero))
    (.idForm (bool_typed _) (.sort zero) (weaken_boolean leftTyped) (.var 0)) (.sort zero))
    (.idForm (bool_typed _) (.sort zero) (weaken_boolean (weaken_boolean leftTyped)) (.var 1)) (.sort zero)

theorem basedUniquenessType_formed {context : Tower.Ctx n} {left : Tower.Tm n}
    (leftTyped : Typing rules context left boolTm) :
    Typing rules context (basedUniquenessType left) (sortTm zero) := by
  apply pi_formed (bool_typed context)
  apply pi_formed (.idForm (bool_typed _) (.sort zero) (weaken_boolean leftTyped) (.var 0))
  apply pi_formed (.idForm (bool_typed _) (.sort zero) (weaken_boolean (weaken_boolean leftTyped)) (.var 1))
  exact .idForm
    (.idForm (bool_typed _) (.sort zero) (weaken_boolean (weaken_boolean (weaken_boolean leftTyped))) (.var 2))
    (.sort zero) (.var 1) (.var 0)

def basedUniqueness (side : Bool) : Tower.Tm n :=
  .lam (.lam (.lam (uniqueness side (.var 2) (.var 1) (.var 0))))

theorem basedUniqueness_typed (side : Bool) {context : Tower.Ctx n}
    (formed : ContextFormation rules context) :
    Typing rules context (basedUniqueness side) (basedUniquenessType (point side)) := by
  have payload : Judgment rules (basedUniquenessContext context (point side))
      (uniqueness side (.var 2) (.var 1) (.var 0))
      (.id (pathType side (.var 2)) (.var 1) (.var 0)) := by
    refine ⟨basedUniquenessContext_formed formed (point_typed side context), ?_⟩
    apply uniqueness_typed side (basedUniquenessContext_formed formed (point_typed side context))
    · exact .var 2
    · cases side <;> exact .var 1
    · cases side <;> exact .var 0
  have result := SharedJudgmentNativeIdentityExtension.abstract_judgment
    (SharedJudgmentNativeIdentityExtension.abstract_judgment
      (SharedJudgmentNativeIdentityExtension.abstract_judgment payload))
  simpa only [basedUniqueness, basedUniquenessType, pathType, tripleWeaken, doubleWeaken, point_rename,
    SharedJudgmentNativeIdentityExtension.rules, SharedJudgmentNativeIdentityExtension.base,
    SharedJudgmentNativeBooleanRegion.rules, baseRules, SharedJudgmentNativeIdentityPaths.rules]
    using result.typing

@[simp] theorem basedUniquenessType_subst (sigma : Sub Tower.Head n m) (left : Tower.Tm n) :
    subst sigma (basedUniquenessType left) = basedUniquenessType (subst sigma left) := by
  simp only [basedUniquenessType, subst, boolTm, doubleWeaken, tripleWeaken,
    subst_liftSub_wk, liftSub]
  rfl

@[simp] theorem basedUniquenessType_inst (left : Tower.Tm n) :
    inst0 left (basedUniquenessType (.var 0)) = basedUniquenessType left := by
  simp only [inst0, basedUniquenessType_subst, subst, subst0, Fin.cases_zero]

/-- The left endpoint is eliminated inside the native language. Thus the
result is not restricted to externally selected constructor endpoints. -/
def regionAt (left : Tower.Tm n) : Tower.Tm n :=
  casesTerm (basedUniquenessType (.var 0)) (basedUniqueness false) (basedUniqueness true) left

theorem regionAt_typed {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {left : Tower.Tm n}
    (leftTyped : Typing rules context left boolTm) :
    Typing rules context (regionAt left) (basedUniquenessType left) := by
  have result := cases_typed (level := zero)
    (by intro valuation; simp [zero, two, one, LevelTower.zero, LevelExpr.eval])
    (basedUniquenessType_formed (context := .snoc context boolTm) (.var 0))
    (onFalse := basedUniqueness false) (onTrue := basedUniqueness true)
    (by simpa only [basedUniquenessType_inst, point, Bool.false_eq_true, ↓reduceIte] using basedUniqueness_typed false formed)
    (by simpa only [basedUniquenessType_inst, point, ↓reduceIte] using basedUniqueness_typed true formed) leftTyped
  simpa only [regionAt, basedUniquenessType_inst] using result

def region : Tower.Tm n := .lam (regionAt (.var 0))
def regionType : Tower.Tm n := .pi boolTm (basedUniquenessType (.var 0))

theorem region_typed {context : Tower.Ctx n} (formed : ContextFormation rules context) :
    Typing rules context region regionType :=
  lambda_typed (bool_typed context) (basedUniquenessType_formed (.var 0))
    (regionAt_typed (.snoc formed (bool_typed context) (.sort zero)) (.var 0))

/-- In particular this is a closed, fully native four-argument uniqueness
theorem: both endpoints and both paths are bound inside its own syntax. -/
theorem closed_region_judgment : Judgment rules (.nil : Tower.Ctx 0) region regionType :=
  ⟨.nil, region_typed .nil⟩

def pathPairType (path : Tower.Tm n) : Tower.Tm n :=
  .pi path (.pi (rename wk path) (.id (doubleWeaken path) (.var 1) (.var 0)))

theorem basedUniquenessType_after_right (left right : Tower.Tm n) :
    inst0 right (.pi (.id boolTm (rename wk left) (.var 0))
      (.pi (.id boolTm (doubleWeaken left) (.var 1))
        (.id (.id boolTm (tripleWeaken left) (.var 2)) (.var 1) (.var 0)))) =
      pathPairType (.id boolTm left right) := by
  simp only [inst0, subst, boolTm, doubleWeaken, tripleWeaken,
    subst_liftSub_wk, SharedJudgmentNativeHedberg.subst0_weaken, subst0,
    pathPairType, rename, liftSub]
  rfl

theorem pathPair_apply_typed {context : Tower.Ctx n} {function path first second : Tower.Tm n}
    (functionTyped : Typing rules context function (pathPairType path))
    (firstTyped : Typing rules context first path)
    (secondTyped : Typing rules context second path) :
    Typing rules context (.app (.app function first) second) (.id path first second) := by
  have firstApplication := Typing.appElim functionTyped firstTyped
  have atOne : liftSub (subst0 first) (1 : Fin (n + 2)) = rename wk first := by
    rw [← Fin.succ_zero_eq_one]
    rfl
  have firstExact : Typing rules context (.app function first)
      (.pi path (.id (rename wk path) (rename wk first) (.var 0))) := by
    simpa only [pathPairType, inst0, subst, subst_liftSub_wk, doubleWeaken,
      atOne, liftSub_zero, SharedJudgmentNativeHedberg.subst0_weaken,
      subst0, Fin.cases_succ, Fin.cases_zero] using firstApplication
  simpa only [inst0, subst, SharedJudgmentNativeHedberg.subst0_weaken, subst0, Fin.cases_zero] using
    Typing.appElim firstExact secondTyped

def regionPoint (left right first second : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (regionAt left) right) first) second

theorem regionPoint_typed {context : Tower.Ctx n}
    (formed : ContextFormation rules context) {left right first second : Tower.Tm n}
    (leftTyped : Typing rules context left boolTm)
    (rightTyped : Typing rules context right boolTm)
    (firstTyped : Typing rules context first (.id boolTm left right))
    (secondTyped : Typing rules context second (.id boolTm left right)) :
    Typing rules context (regionPoint left right first second) (.id (.id boolTm left right) first second) := by
  have firstApplication := Typing.appElim (regionAt_typed formed leftTyped) rightTyped
  have exactPair : Typing rules context (.app (regionAt left) right) (pathPairType (.id boolTm left right)) := by
    simpa only [basedUniquenessType, basedUniquenessType_after_right] using firstApplication
  exact pathPair_apply_typed exactPair firstTyped secondTyped

theorem regionAt_false_iota :
    rules.computation.step (regionAt (falseTm : Tower.Tm n)) (basedUniqueness false) :=
  iota_false _ _ _

theorem regionAt_true_iota :
    rules.computation.step (regionAt (trueTm : Tower.Tm n)) (basedUniqueness true) :=
  iota_true _ _ _

/-- The universal proof does not pick a constructor branch for a neutral
left endpoint. The statement concerns the Boolean signature's iota roots. -/
theorem regionAt_neutral_no_declared_iota (output : Tower.Tm (n + 1)) :
    ¬ iota.step (regionAt (.var 0)) output :=
  iota_neutral_absent _ _ _ _

#print axioms comparisonType_formed
#print axioms sameConstancy_typed
#print axioms oppositeConstancy_typed
#print axioms weakComparison_typed
#print axioms uniqueness_typed
#print axioms basedUniqueness_typed
#print axioms regionAt_typed
#print axioms closed_region_judgment
#print axioms regionPoint_typed
#print axioms regionAt_false_iota
#print axioms regionAt_true_iota
#print axioms regionAt_neutral_no_declared_iota

end Mettapedia.Languages.MeTTa.PrimeCandidates.SharedJudgmentNativeBooleanConstancy
