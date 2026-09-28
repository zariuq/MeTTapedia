import Mettapedia.OSLF.Syntax.ResultSortedScopedPremises
import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms

/-!
# Result-sorted authored operational constructors

The conclusion of a rule and each recursive premise may have different
authored result sorts. This presentation indexes every judgment by its full
sort context and its own result sort. A constructor retains the complete raw
rule skeleton, canonical ordered premise elaboration, and checked conclusion
endpoints. The finite premise list keeps each recursive child at its declared
sort and position.

This is a typed subpresentation of the raw operational rules. Constructing a
shape from an arbitrary raw firing still needs the general typed matching and
conditional-premise theorem; the interface does not assume that theorem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution (RuleHistory)
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext HasType)
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.ResultSortedScopedPremises

/-- The result sort belongs to the judgment, rather than being fixed for
the entire derivation tree. -/
structure Judgment where
  fuel : Nat
  ambient : List TypeExpr
  resultType : TypeExpr
  source : Pattern
  target : Pattern

def Judgment.eraseResult (judgment : Judgment) :
    SortIndexedScopedOperationalPresentation.Judgment :=
  ⟨judgment.fuel, judgment.ambient, judgment.source, judgment.target⟩

/-- A source rule constructor together with exact canonical premise
annotation and the typing judgment for its conclusion. -/
structure RuleShape (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr) (source target : Pattern) where
  raw : ScopedOperationalPresentation.RuleSkeleton RuleHistory relEnv lang
    ambient.length source target
  children : List ResultSortedChild
  canonical : ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?
    ambient raw = some children
  sourceTyped : HasType lang free ambient source resultType
  targetTyped : HasType lang free ambient target resultType

/-- Build a result-sorted constructor from an actual operational shape,
source premise compilation, and separately established conclusion typing.
The raw constructor label is retained exactly. -/
noncomputable def RuleShape.ofCompiled
    {relEnv : RelationEnv} {lang : LanguageDef}
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr) {source target : Pattern}
    (raw : ScopedOperationalPresentation.RuleSkeleton RuleHistory relEnv
      lang ambient.length source target)
    (unique : (raw.rule.typeContext.map Prod.fst).Nodup)
    (compiled : List
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.CanonicalPremise)
    (hcompiled :
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
        lang
        (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
          raw.rule.typeContext)
        ambient raw.rule.premises = some compiled)
    (sourceTyped : HasType lang free ambient source resultType)
    (targetTyped : HasType lang free ambient target resultType) :
    RuleShape relEnv lang free ambient resultType source target :=
  let admitted :=
    ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_exists_of_compiled
      ambient raw unique compiled hcompiled;
  ⟨raw, Classical.choose admitted, Classical.choose_spec admitted,
    sourceTyped, targetTyped⟩

@[simp] theorem RuleShape.ofCompiled_raw
    {relEnv : RelationEnv} {lang : LanguageDef}
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (resultType : TypeExpr) {source target : Pattern}
    (raw : ScopedOperationalPresentation.RuleSkeleton RuleHistory relEnv
      lang ambient.length source target)
    (unique : (raw.rule.typeContext.map Prod.fst).Nodup)
    (compiled : List
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.CanonicalPremise)
    (hcompiled :
      Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.compileList?
        lang
        (Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise.freeFromRuleContext
          raw.rule.typeContext)
        ambient raw.rule.premises = some compiled)
    (sourceTyped : HasType lang free ambient source resultType)
    (targetTyped : HasType lang free ambient target resultType) :
    (RuleShape.ofCompiled free ambient resultType raw unique compiled
      hcompiled sourceTyped targetTyped).raw = raw := by
  rfl

/-- Children are listed in author order and keep their individual result
sorts. Fuel decreases at each recursive premise. -/
def presentation (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) :
    FinitePresentation Unit (fun _ => Judgment) where
  Shape := fun _ judgment =>
    match judgment.fuel with
    | 0 => Empty
    | _ + 1 => RuleShape relEnv lang free judgment.ambient
        judgment.resultType judgment.source judgment.target
  premises := fun _ judgment shape =>
    match judgment with
    | ⟨0, _, _, _, _⟩ => nomatch shape
    | ⟨fuel + 1, _, _, _, _⟩ =>
        shape.children.map fun child =>
          ⟨fuel, child.ambient, child.resultType, child.source,
            child.target⟩

/-- Forget the checked certificates and child result sorts of a rule
constructor while retaining its complete raw operational label. -/
def eraseShape (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) (judgment : Judgment)
    (shape : (presentation relEnv lang free).Shape () judgment) :
    (SortIndexedScopedOperationalPresentation.presentation relEnv lang).Shape
      () judgment.eraseResult :=
  match judgment with
  | ⟨0, _, _, _, _⟩ => nomatch shape
  | ⟨_ + 1, _, _, _, _⟩ => shape.raw

/-- Erasure to the existing sort-context rule presentation preserves the
exact ordered premise list, including multiple occurrences with equal
endpoints and different result sorts. -/
theorem presentation_premises_erase
    (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) (judgment : Judgment)
    (shape : (presentation relEnv lang free).Shape () judgment) :
    ((presentation relEnv lang free).premises () judgment shape).map
        Judgment.eraseResult =
      (SortIndexedScopedOperationalPresentation.presentation relEnv lang).premises
        () judgment.eraseResult (eraseShape relEnv lang free judgment shape) := by
  cases judgment with
  | mk fuel ambient resultType source target =>
      cases fuel with
      | zero => cases shape
      | succ fuel =>
          change
            (shape.children.map (fun child =>
              (⟨fuel, child.ambient, child.resultType, child.source,
                child.target⟩ : Judgment))).map Judgment.eraseResult =
              (SortIndexedScopedOperationalPresentation.RuleSkeleton.sortedChildren
                ambient shape.raw).map fun child =>
                  (⟨fuel, child.1, child.2.1, child.2.2⟩ :
                    SortIndexedScopedOperationalPresentation.Judgment)
          have corresponding :=
            ResultSortedScopedPremises.RuleSkeleton.canonicalResultChildren?_erase
              ambient shape.raw shape.children shape.canonical
          rw [← corresponding]
          simp [ResultSortedChild.eraseResult, Judgment.eraseResult,
            List.map_map]

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

/-- Forgetting result-sort certificates is cartesian: it preserves every
rule label and every ordered firing-evidence position. -/
def erasePolynomialMap (relEnv : RelationEnv) (lang : LanguageDef)
    (free : FreeTypeContext) :
    Hom (presentation relEnv lang free).polynomial
      (SortIndexedScopedOperationalPresentation.presentation relEnv lang).polynomial
      (fun _ judgment => judgment.eraseResult) where
  onShape := fun _ judgment shape => eraseShape relEnv lang free judgment shape
  onPosition := fun _ judgment shape => by
    have lengths :
        ((SortIndexedScopedOperationalPresentation.presentation relEnv lang).premises
          () judgment.eraseResult (eraseShape relEnv lang free judgment shape)).length =
        ((presentation relEnv lang free).premises () judgment shape).length := by
      simpa only [List.length_map] using
        (congrArg List.length
          (presentation_premises_erase relEnv lang free judgment shape)).symm
    exact Equiv.cast (congrArg Fin lengths)
  onNext := by
    intro _ judgment shape position
    have corresponding := presentation_premises_erase relEnv lang free
      judgment shape
    have lengths :
        ((SortIndexedScopedOperationalPresentation.presentation relEnv lang).premises
          () judgment.eraseResult (eraseShape relEnv lang free judgment shape)).length =
        ((presentation relEnv lang free).premises () judgment shape).length := by
      simpa only [List.length_map] using
        (congrArg List.length corresponding).symm
    change
      ((SortIndexedScopedOperationalPresentation.presentation relEnv lang).premises
        () judgment.eraseResult (eraseShape relEnv lang free judgment shape)).get
        position =
      (((presentation relEnv lang free).premises () judgment shape).get
        (Equiv.cast (congrArg Fin lengths) position)).eraseResult
    exact get_of_map_eq Judgment.eraseResult corresponding position

#print axioms presentation_premises_erase
#print axioms erasePolynomialMap
#print axioms RuleShape.ofCompiled

end Mettapedia.OSLF.Binding.ResultSortedScopedOperationalPresentation
