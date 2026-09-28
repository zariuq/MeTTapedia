import Mettapedia.OSLF.Syntax.SortIndexedScopedOperationalPresentation
import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise

/-!
# Result sorts at authored recursive premise positions

A scoped step declaration specifies both its binder context and its result
sort. A bare congruence premise specifies neither sort; canonical elaboration
admits it only if the authored grammar checks exactly one root sort. This
module carries those result sorts through the *ordered* oracle-independent
premise skeleton. Failed or ambiguous sort inference rejects the annotation
rather than guessing a child's sort from its parent.

Erasing successful result-sort annotations recovers the previous list of
scoped child judgments, including repeated positions and endpoints. The
construction does not yet assert that instantiated child endpoints pass the
chosen result sort; that requires the typed matching and substitution laws.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedPremises

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise (check)
open Mettapedia.OSLF.Binding.ScopedPremiseSkeleton
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation

/-- A recursive premise judgment with its full local sort context and its
own result sort. -/
structure ResultSortedChild where
  ambient : List TypeExpr
  resultType : TypeExpr
  source : Pattern
  target : Pattern

/-- Forget only the premise's result sort. -/
def ResultSortedChild.eraseResult (child : ResultSortedChild) : SortedChild :=
  (child.ambient, child.source, child.target)

/-- The outer option records success of canonical sort admission; the
inner option distinguishes a nonrecursive base premise from a step. -/
def PremiseSkeleton.resultSortedChild?
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premise : Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index premise initial final) :
    Option (Option ResultSortedChild) :=
  match shape with
  | .scopedStep (step := step) _ _ stepShape =>
      if check lang free ambient step then
        some (some ⟨step.binders ++ ambient, step.resultType,
          stepShape.childSource, stepShape.childTarget⟩)
      else none
  | .congruence (source := source) (target := target) _ stepShape =>
      (inferRootSort? lang free ambient source target).map fun resultType =>
        some ⟨ambient, resultType, stepShape.childSource,
          stepShape.childTarget⟩
  | .freshness _ _ | .relationQuery _ _ | .forAll _ _ => some none

/-- Successful annotation of one premise retains its exact scoped child,
if any; only its result sort has been added. -/
theorem PremiseSkeleton.resultSortedChild?_erase
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premise : Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index premise initial final)
    (child : Option ResultSortedChild)
    (accepted : PremiseSkeleton.resultSortedChild? ambient free shape =
      some child) :
    child.map ResultSortedChild.eraseResult =
      SortIndexedScopedOperationalPresentation.PremiseSkeleton.sortedChild?
        ambient shape := by
  cases shape with
  | scopedStep _ _ stepShape =>
      simp only [PremiseSkeleton.resultSortedChild?] at accepted
      split at accepted
      · simp only [Option.some.injEq] at accepted
        subst child
        rfl
      · cases accepted
  | @congruence source target initial final ordinal stepShape =>
      simp only [PremiseSkeleton.resultSortedChild?] at accepted
      cases inferred : inferRootSort? lang free ambient source target with
      | none => simp [inferred] at accepted
      | some resultType =>
          simp only [inferred, Option.map_some, Option.some.injEq] at accepted
          subst child
          rfl
  | freshness _ _ =>
      simp [PremiseSkeleton.resultSortedChild?] at accepted
      subst child
      rfl
  | relationQuery _ _ =>
      simp [PremiseSkeleton.resultSortedChild?] at accepted
      subst child
      rfl
  | forAll _ _ =>
      simp [PremiseSkeleton.resultSortedChild?] at accepted
      subst child
      rfl

/-- An operationally available scoped step is still rejected as a sorted
recursive child when its authored endpoint check fails. -/
theorem PremiseSkeleton.scopedStep_rejected
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {step : ScopedStepPremise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index (.scopedStep step) initial final)
    (rejected : check lang free ambient step = false) :
    PremiseSkeleton.resultSortedChild? ambient free shape = none := by
  cases shape with
  | scopedStep _ _ _ =>
      simp [PremiseSkeleton.resultSortedChild?, rejected]

/-- A bare congruence with no unique authored root sort cannot enter the
result-sorted constructor, even if the raw operational skeleton exists. -/
theorem PremiseSkeleton.congruence_rejected
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {source target : Pattern}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index (.congruence source target) initial final)
    (rejected : inferRootSort? lang free ambient source target = none) :
    PremiseSkeleton.resultSortedChild? ambient free shape = none := by
  cases shape with
  | congruence _ _ =>
      simp [PremiseSkeleton.resultSortedChild?, rejected]

/-- Successful authored elaboration supplies a result-sort annotation for
every operational shape of the same premise. The selected firing ordinal
and its captured endpoints do not affect declaration-level sort admission. -/
theorem PremiseSkeleton.resultSortedChild?_of_compiled
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premise : Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (shape : PremiseSkeleton Evidence relEnv lang rule spec
      ambient.length index premise initial final)
    (compiled : CanonicalPremise)
    (hcompiled : compile? lang free ambient premise = some compiled) :
    ∃ child, PremiseSkeleton.resultSortedChild? ambient free shape =
      some child := by
  cases shape with
  | @scopedStep step initial final wellScoped ordinal stepShape =>
      cases checked : check lang free ambient step with
      | false => simp [compile?, checked] at hcompiled
      | true =>
          exact ⟨some ⟨step.binders ++ ambient, step.resultType,
            stepShape.childSource, stepShape.childTarget⟩, by
              simp [PremiseSkeleton.resultSortedChild?, checked]⟩
  | @congruence source target initial final ordinal stepShape =>
      cases inferred : inferRootSort? lang free ambient source target with
      | none => simp [compile?, inferred] at hcompiled
      | some resultType =>
          exact ⟨some ⟨ambient, resultType, stepShape.childSource,
            stepShape.childTarget⟩, by
              simp [PremiseSkeleton.resultSortedChild?, inferred]⟩
  | freshness _ _ => exact ⟨none, rfl⟩
  | relationQuery _ _ => exact ⟨none, rfl⟩
  | forAll _ _ => exact ⟨none, rfl⟩

/-- Annotate all recursive premises in author order. Any ambiguous bare
congruence premise causes the entire annotation to fail. -/
def RunSkeleton.resultSortedChildren?
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final) : Option (List ResultSortedChild) :=
  match run with
  | .nil => some []
  | .cons head tail => do
      let first ← PremiseSkeleton.resultSortedChild? ambient free head
      let rest ← RunSkeleton.resultSortedChildren? ambient free tail
      pure (first.toList ++ rest)

/-- Compiling the complete ordered authored premise list is sufficient to
annotate every recursive position in any matching operational run. This
holds with multiple premises and repeated equal child judgments. -/
theorem RunSkeleton.resultSortedChildren?_of_compiled
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final)
    (compiled : List CanonicalPremise)
    (hcompiled : compileList? lang free ambient premises = some compiled) :
    ∃ children,
      RunSkeleton.resultSortedChildren? ambient free run =
        some children := by
  induction run generalizing compiled with
  | nil => exact ⟨[], rfl⟩
  | @cons index premise rest initial intermediate final head tail ih =>
      cases firstEq : compile? lang free ambient premise with
      | none => simp [compileList?, firstEq] at hcompiled
      | some first =>
          cases restEq : compileList? lang free ambient rest with
          | none => simp [compileList?, firstEq, restEq] at hcompiled
          | some later =>
              obtain ⟨child, hchild⟩ :=
                PremiseSkeleton.resultSortedChild?_of_compiled
                  ambient free head first firstEq
              obtain ⟨children, hchildren⟩ := ih later restEq
              exact ⟨child.toList ++ children, by
                simp [RunSkeleton.resultSortedChildren?, hchild,
                  hchildren]⟩

/-- A successful ordered annotation has exactly the old ordered scoped
children after result-sort erasure. No recursive premise is added, merged,
or omitted. -/
theorem RunSkeleton.resultSortedChildren?_erase
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final)
    (children : List ResultSortedChild)
    (accepted : RunSkeleton.resultSortedChildren? ambient free run =
      some children) :
    children.map ResultSortedChild.eraseResult =
      SortIndexedScopedOperationalPresentation.RunSkeleton.sortedChildren
        ambient run := by
  induction run generalizing children with
  | nil =>
      simp [RunSkeleton.resultSortedChildren?] at accepted
      subst children
      rfl
  | @cons index premise rest initial intermediate final head tail ih =>
      simp only [RunSkeleton.resultSortedChildren?] at accepted
      cases firstEq : PremiseSkeleton.resultSortedChild? ambient free head with
      | none => simp [firstEq] at accepted
      | some first =>
          cases restEq : RunSkeleton.resultSortedChildren? ambient free tail with
          | none => simp [firstEq, restEq] at accepted
          | some later =>
              simp [firstEq, restEq] at accepted
              subst children
              simp only [List.map_append, ← Option.toList_map]
              rw [PremiseSkeleton.resultSortedChild?_erase ambient free
                head first firstEq]
              rw [ih later restEq]
              rfl

/-- A single explicitly scoped step is admitted without guessing its sort.
Its sole recursive child retains precisely the authored binder list and
result sort. -/
theorem RunSkeleton.single_scoped_result_child
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {step : ScopedStepPremise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index [.scopedStep step] initial final)
    (checked : check lang free ambient step = true) :
    ∃ source target,
      RunSkeleton.resultSortedChildren? ambient free run =
        some [⟨step.binders ++ ambient, step.resultType, source, target⟩] := by
  cases run with
  | cons head tail =>
      cases tail
      cases head with
      | scopedStep _ _ stepShape =>
          exact ⟨stepShape.childSource, stepShape.childTarget, by
            simp [RunSkeleton.resultSortedChildren?,
              PremiseSkeleton.resultSortedChild?, checked]⟩

theorem RunSkeleton.single_scoped_result_child_of_eq
    {Evidence : Type} {relEnv : RelationEnv} {lang : LanguageDef}
    {rule : RewriteRule} {spec : RuleBindingSpec}
    {index : Nat} {premises : List Premise}
    {initial final : Assignment}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    (run : RunSkeleton Evidence relEnv lang rule spec ambient.length
      index premises initial final)
    {step : ScopedStepPremise}
    (single : premises = [.scopedStep step])
    (checked : check lang free ambient step = true) :
    ∃ source target,
      RunSkeleton.resultSortedChildren? ambient free run =
        some [⟨step.binders ++ ambient, step.resultType, source, target⟩] := by
  subst premises
  exact RunSkeleton.single_scoped_result_child ambient free run checked

/-- The annotation of a whole authored rule constructor is the ordered
annotation of its actual premise skeleton. -/
def RuleSkeleton.resultSortedChildren?
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target) :
    Option (List ResultSortedChild) :=
  RunSkeleton.resultSortedChildren? ambient free shape.premises

theorem RuleSkeleton.resultSortedChildren?_erase
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    (children : List ResultSortedChild)
    (accepted : RuleSkeleton.resultSortedChildren? ambient free shape =
      some children) :
    children.map ResultSortedChild.eraseResult =
      SortIndexedScopedOperationalPresentation.RuleSkeleton.sortedChildren
        ambient shape := by
  exact RunSkeleton.resultSortedChildren?_erase ambient free
    shape.premises children accepted

theorem RuleSkeleton.single_scoped_result_child
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr) (free : FreeTypeContext)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    {step : ScopedStepPremise}
    (single : shape.rule.premises = [.scopedStep step])
    (checked : check lang free ambient step = true) :
    ∃ childSource childTarget,
      RuleSkeleton.resultSortedChildren? ambient free shape =
        some [⟨step.binders ++ ambient, step.resultType,
          childSource, childTarget⟩] := by
  unfold RuleSkeleton.resultSortedChildren?
  exact RunSkeleton.single_scoped_result_child_of_eq ambient free
    shape.premises single checked

/-- Admit the selected constructor through the same ordered premise
elaboration used for authored rules, at its actual ambient context. The
schema-variable context must have unique names. -/
def RuleSkeleton.canonicalResultChildren?
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target) :
    Option (List ResultSortedChild) := do
  if !(shape.rule.typeContext.map Prod.fst).Nodup then none else
    let free := freeFromRuleContext shape.rule.typeContext
    let _ ← compileList? lang free ambient shape.rule.premises
    RuleSkeleton.resultSortedChildren? ambient free shape

theorem RuleSkeleton.canonicalResultChildren?_of_compiled
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    (unique : (shape.rule.typeContext.map Prod.fst).Nodup)
    (compiled : List CanonicalPremise)
    (hcompiled : compileList? lang
      (freeFromRuleContext shape.rule.typeContext) ambient
      shape.rule.premises = some compiled) :
    RuleSkeleton.canonicalResultChildren? ambient shape =
      RuleSkeleton.resultSortedChildren? ambient
        (freeFromRuleContext shape.rule.typeContext) shape := by
  simp [RuleSkeleton.canonicalResultChildren?, unique, hcompiled]

/-- For a source rule whose ordered premises compiled, every chosen raw
operational shape has a canonical ordered result-sort annotation. This
establishes shape-level admission; typing of instantiated conclusion and
child endpoints remains a separate theorem. -/
theorem RuleSkeleton.canonicalResultChildren?_exists_of_compiled
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    (unique : (shape.rule.typeContext.map Prod.fst).Nodup)
    (compiled : List CanonicalPremise)
    (hcompiled : compileList? lang
      (freeFromRuleContext shape.rule.typeContext) ambient
      shape.rule.premises = some compiled) :
    ∃ children,
      RuleSkeleton.canonicalResultChildren? ambient shape =
        some children := by
  obtain ⟨children, assigned⟩ :=
    RunSkeleton.resultSortedChildren?_of_compiled ambient
      (freeFromRuleContext shape.rule.typeContext)
      shape.premises compiled hcompiled
  exact ⟨children, by
    rw [RuleSkeleton.canonicalResultChildren?_of_compiled
      ambient shape unique compiled hcompiled]
    exact assigned⟩

/-- An operational shape cannot acquire sorted recursive children when its
authored premise list fails canonical elaboration. -/
theorem RuleSkeleton.canonicalResultChildren?_rejected
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    (rejected : compileList? lang
      (freeFromRuleContext shape.rule.typeContext) ambient
      shape.rule.premises = none) :
    RuleSkeleton.canonicalResultChildren? ambient shape = none := by
  simp [RuleSkeleton.canonicalResultChildren?, rejected]

/-- Canonical declaration admission adds result-sort information without
changing any ordered recursive child of the chosen operational shape. -/
theorem RuleSkeleton.canonicalResultChildren?_erase
    {relEnv : RelationEnv} {lang : LanguageDef}
    (ambient : List TypeExpr)
    {source target : Pattern}
    (shape : ScopedOperationalPresentation.RuleSkeleton RuleHistory
      relEnv lang ambient.length source target)
    (children : List ResultSortedChild)
    (accepted : RuleSkeleton.canonicalResultChildren? ambient shape =
      some children) :
    children.map ResultSortedChild.eraseResult =
      SortIndexedScopedOperationalPresentation.RuleSkeleton.sortedChildren
        ambient shape := by
  unfold RuleSkeleton.canonicalResultChildren? at accepted
  split at accepted
  · simp at accepted
  · cases compiled : compileList? lang
      (freeFromRuleContext shape.rule.typeContext) ambient
      shape.rule.premises with
    | none => simp [compiled] at accepted
    | some premises =>
        simp [compiled] at accepted
        exact RuleSkeleton.resultSortedChildren?_erase ambient
          (freeFromRuleContext shape.rule.typeContext) shape children accepted

#print axioms PremiseSkeleton.resultSortedChild?_erase
#print axioms RunSkeleton.resultSortedChildren?_erase
#print axioms RuleSkeleton.resultSortedChildren?_erase
#print axioms RuleSkeleton.single_scoped_result_child
#print axioms RuleSkeleton.canonicalResultChildren?_erase
#print axioms RuleSkeleton.canonicalResultChildren?_rejected
#print axioms PremiseSkeleton.resultSortedChild?_of_compiled
#print axioms RunSkeleton.resultSortedChildren?_of_compiled
#print axioms RuleSkeleton.canonicalResultChildren?_exists_of_compiled

end Mettapedia.OSLF.Binding.ResultSortedScopedPremises
