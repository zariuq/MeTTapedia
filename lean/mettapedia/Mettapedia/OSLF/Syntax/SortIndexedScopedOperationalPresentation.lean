import Mettapedia.OSLF.Syntax.ScopedOperationalPresentation

/-!
# Sort-indexed children of authored scoped rule constructors

An authored step premise retains its local binder sorts even though the
existing free-rule presentation indexes children only by context length.
This file retains those sorts in each child judgment and proves exact
erasure to the existing ordered child list. It does not itself assert that
the raw constructor endpoints pass the authored type checker.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.ScopedOperationalPresentation
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

/-- A recursive child's full binder context and endpoints. -/
abbrev SortedChild := List TypeExpr × Pattern × Pattern

/-- Forget only the sort labels, not the child position or endpoints. -/
def childDepth (child : SortedChild) : Nat × Pattern × Pattern :=
  (child.1.length, child.2.1, child.2.2)

/-- A scoped premise extends the exact ambient sort list; a root
congruence premise leaves it unchanged. Base premises have no child. -/
def PremiseSkeleton.sortedChild?
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premise : Premise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index premise initial final) : Option SortedChild :=
  match shape with
  | .scopedStep (step := step) _ _ stepShape =>
      some (step.binders ++ ambient, stepShape.childSource,
        stepShape.childTarget)
  | .congruence _ stepShape =>
      some (ambient, stepShape.childSource, stepShape.childTarget)
  | .freshness _ _ | .relationQuery _ _ | .forAll _ _ => none

/-- Every sorted child projects to precisely the previously published
depth-indexed child, including its source and target patterns. -/
theorem PremiseSkeleton.sortedChild?_depth
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premise : Premise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index premise initial final) :
    (PremiseSkeleton.sortedChild? ambient shape).map childDepth = shape.child? := by
  cases shape with
  | scopedStep _ _ stepShape =>
      simp [PremiseSkeleton.sortedChild?, PremiseSkeleton.child?,
        childDepth, List.length_append, Nat.add_comm,
        Mettapedia.OSLF.Binding.ScopedStepShapes.StepShape.childJudgment]
  | congruence _ stepShape =>
      simp [PremiseSkeleton.sortedChild?, PremiseSkeleton.child?,
        childDepth,
        Mettapedia.OSLF.Binding.ScopedStepShapes.StepShape.childJudgment]
  | freshness _ _ => rfl
  | relationQuery _ _ => rfl
  | forAll _ _ => rfl

/-- The whole ordered premise skeleton retains one full sort context for
each recursive child, without merging repeated children. -/
def RunSkeleton.sortedChildren
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final) : List SortedChild :=
  match run with
  | .nil => []
  | .cons head tail =>
      (PremiseSkeleton.sortedChild? ambient head).toList ++ RunSkeleton.sortedChildren ambient tail

/-- Erasing the sorted context commutes with the complete ordered list of
recursive premises, including repeated equal endpoint pairs. -/
theorem RunSkeleton.sortedChildren_depth
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final) :
    (RunSkeleton.sortedChildren ambient run).map childDepth = run.children := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      simp only [RunSkeleton.sortedChildren, RunSkeleton.children,
        List.map_append, ← Option.toList_map]
      rw [PremiseSkeleton.sortedChild?_depth ambient head, ih]

/-- One authored scoped premise has exactly one child, in the actual sort
extension named by that premise. -/
theorem RunSkeleton.single_scoped_sorted_child
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {step : ScopedStepPremise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index [.scopedStep step] initial final) :
    ∃ source target,
      RunSkeleton.sortedChildren ambient run =
        [(step.binders ++ ambient, source, target)] := by
  cases run with
  | cons head tail =>
      cases tail
      cases head with
      | scopedStep _ _ stepShape =>
          exact ⟨stepShape.childSource, stepShape.childTarget, rfl⟩

theorem RunSkeleton.single_scoped_sorted_child_of_eq
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.Assignment}
    (ambient : List TypeExpr)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final) {step : ScopedStepPremise}
    (single : premises = [.scopedStep step]) :
    ∃ source target,
      RunSkeleton.sortedChildren ambient run =
        [(step.binders ++ ambient, source, target)] := by
  subst premises
  exact RunSkeleton.single_scoped_sorted_child ambient run

/-- A whole-rule constructor's children retain the local binder sorts of
each recursive premise in the author's original order. -/
def RuleSkeleton.sortedChildren
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv lang ambient.length
      source target) : List SortedChild :=
  RunSkeleton.sortedChildren ambient shape.premises

theorem RuleSkeleton.sortedChildren_depth
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv lang ambient.length
      source target) :
    (RuleSkeleton.sortedChildren ambient shape).map childDepth =
      shape.children :=
  RunSkeleton.sortedChildren_depth ambient shape.premises

theorem RuleSkeleton.single_scoped_sorted_child
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) {source target : Pattern}
    (shape : RuleSkeleton RuleHistory relEnv lang ambient.length
      source target) {step : ScopedStepPremise}
    (single : shape.rule.premises = [.scopedStep step]) :
    ∃ childSource childTarget,
      RuleSkeleton.sortedChildren ambient shape =
        [(step.binders ++ ambient, childSource, childTarget)] := by
  unfold RuleSkeleton.sortedChildren
  exact RunSkeleton.single_scoped_sorted_child_of_eq ambient
    shape.premises single

/-- The conclusion and recursive child judgments retain the ordered sort
context, rather than only its cardinality. -/
structure Judgment where
  fuel : Nat
  ambient : List TypeExpr
  source : Pattern
  target : Pattern

def Judgment.depth (judgment : Judgment) :
    ScopedOperationalPresentation.Judgment :=
  ⟨judgment.fuel, judgment.ambient.length, judgment.source,
    judgment.target⟩

/-- The sort-indexed finite rule presentation reuses the authored
oracle-independent constructors, but addresses each recursive premise in
its actual binder extension. -/
def presentation (relEnv : RelationEnv) (lang : LanguageDef) :
    FinitePresentation Unit (fun _ => Judgment) where
  Shape := fun _ judgment =>
    match judgment.fuel with
    | 0 => Empty
    | _ + 1 => RuleSkeleton RuleHistory relEnv lang
        judgment.ambient.length judgment.source judgment.target
  premises := fun _ judgment shape =>
    match judgment with
    | ⟨0, _, _, _⟩ => nomatch shape
    | ⟨fuel + 1, ambient, _, _⟩ =>
        (RuleSkeleton.sortedChildren ambient shape).map fun child =>
          ⟨fuel, child.1, child.2.1, child.2.2⟩

/-- Forgetting sort labels recovers every recursive address of the existing
finite scoped presentation, including positions at repeated endpoints. -/
theorem presentation_premises_depth
    (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (shape : (presentation relEnv lang).Shape () judgment) :
    ((presentation relEnv lang).premises () judgment shape).map
        Judgment.depth =
      (ScopedOperationalPresentation.presentation relEnv lang).premises ()
        judgment.depth shape := by
  cases judgment with
  | mk fuel ambient source target =>
      cases fuel with
      | zero => cases shape
      | succ fuel =>
          change
            ((RuleSkeleton.sortedChildren ambient shape).map
              (fun child => (⟨fuel, child.1, child.2.1, child.2.2⟩ :
                Judgment))).map Judgment.depth =
            shape.children.map fun child =>
              (⟨fuel, child.1, child.2.1, child.2.2⟩ :
                ScopedOperationalPresentation.Judgment)
          simp only [List.map_map]
          rw [← RuleSkeleton.sortedChildren_depth ambient shape]
          simp only [List.map_map]
          rfl

private theorem castFinVal {n m : Nat} (equal : n = m)
    (position : Fin n) :
    (Equiv.cast (congrArg Fin equal) position).val = position.val := by
  simpa only [finCongr_eq_equivCast] using
    finCongr_apply_coe equal position

private theorem get_of_map_eq {Source Target : Type}
    (f : Source → Target) {source : List Source} {target : List Target}
    (corresponding : source.map f = target)
    (position : Fin target.length) :
    target.get position =
      f (source.get (Equiv.cast (congrArg Fin (by
        simpa only [List.length_map] using
          (congrArg List.length corresponding).symm)) position)) := by
  cases corresponding
  have lengthEq : (source.map f).length = source.length := by simp
  have sameIndex := castFinVal lengthEq position
  simp only [List.get_eq_getElem, List.getElem_map, sameIndex]

/-- Erasing sort lists is a cartesian map of rule polynomials: every
constructor and every individual recursive premise position is retained. -/
def depthPolynomialMap (relEnv : RelationEnv) (lang : LanguageDef) :
    Hom (presentation relEnv lang).polynomial
      (ScopedOperationalPresentation.presentation relEnv lang).polynomial
      (fun _ judgment => judgment.depth) where
  onShape := fun _ _ shape => shape
  onPosition := fun _ judgment shape => by
    have lengths :
        ((ScopedOperationalPresentation.presentation relEnv lang).premises
          () judgment.depth shape).length =
        ((presentation relEnv lang).premises () judgment shape).length := by
      simpa only [List.length_map] using
        (congrArg List.length
          (presentation_premises_depth relEnv lang judgment shape)).symm
    exact Equiv.cast (congrArg Fin lengths)
  onNext := by
    intro _ judgment shape position
    have corresponding := presentation_premises_depth relEnv lang
      judgment shape
    have lengths :
        ((ScopedOperationalPresentation.presentation relEnv lang).premises
          () judgment.depth shape).length =
        ((presentation relEnv lang).premises () judgment shape).length := by
      simpa only [List.length_map] using
        (congrArg List.length corresponding).symm
    change
      ((ScopedOperationalPresentation.presentation relEnv lang).premises
        () judgment.depth shape).get position =
      (((presentation relEnv lang).premises () judgment shape).get
        (Equiv.cast (congrArg Fin lengths) position)).depth
    exact get_of_map_eq Judgment.depth corresponding position

/-- Forget sort labels throughout a complete free derivation, recursively
transporting every premise by the cartesian rule-presentation map. -/
noncomputable def eraseTree (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment) :
    (presentation relEnv lang).Derivation () judgment →
      (ScopedOperationalPresentation.presentation relEnv lang).Derivation ()
        judgment.depth :=
  (depthPolynomialMap relEnv lang).mapFix () judgment

theorem sorted_derivation_has_depth_derivation
    (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (available : Nonempty ((presentation relEnv lang).Derivation ()
      judgment)) :
    Nonempty
      ((ScopedOperationalPresentation.presentation relEnv lang).Derivation
        () judgment.depth) :=
  available.map (eraseTree relEnv lang judgment)

#print axioms PremiseSkeleton.sortedChild?_depth
#print axioms RunSkeleton.sortedChildren_depth
#print axioms RunSkeleton.single_scoped_sorted_child
#print axioms presentation_premises_depth
#print axioms depthPolynomialMap
#print axioms sorted_derivation_has_depth_derivation

end Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
