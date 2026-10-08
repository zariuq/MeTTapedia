import Mettapedia.SetTheory.Profiles.ProfileIndexedCalculusExtensions
import Mettapedia.SetTheory.Profiles.CommonCoreClassicalCollection

/-!
# Actual model interpretations of profile-indexed material deductions

The selected common profile includes the separately constructed Collection
extensions. Its varying graph interpretation computes proof-relevant
receipts with every future context retained. The ordinary HSet and ZFSet
interpretations use their actual operations; their host dependencies remain
separate from the constructive interpretation.

This is soundness of the first-order source calculus, including all logical,
quantifier and equality rules. It makes no soundness assertion about an
arbitrary higher-order native checker or an undeclared foreign profile.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation

open _root_.CategoryTheory
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute)
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open ProfileIndexedCalculus

universe u v

def commonCoreProfile : Profile where
  RuleName := CommonCore.LawName
  Rule := CommonCore.Axiom
  ruleName := CommonCore.Axiom.name

/-- Collection is adopted by the selected default, without claiming that
it follows from the weaker common primitive laws. -/
def commonProfile : Profile where
  RuleName := CommonCore.LawName
  Rule := CommonCore.Extension
  ruleName := CommonCore.Extension.name

def commonEmbedding : Translation commonCoreProfile commonProfile where
  rule := fun adopted => .primitive (.core adopted)

def fromCommonCore {count : Nat} {body : Formula count} (derivation : CommonCore.Derivation body) :
    Derivation commonCoreProfile [] body where
  declarations := (List.finRange derivation.assumptions.length).map
    (fun index : Fin derivation.assumptions.length =>
      ⟨derivation.assumptions[index.val],
        .primitive (body := derivation.assumptions[index.val]) (derivation.adopted index), index.val⟩)
  proof := by
    have same : declarationFormulas ((List.finRange derivation.assumptions.length).map
        (fun index : Fin derivation.assumptions.length =>
          (⟨derivation.assumptions[index.val],
            .primitive (body := derivation.assumptions[index.val]) (derivation.adopted index), index.val⟩ :
          Declaration commonCoreProfile count))) = derivation.assumptions := by
      simp only [declarationFormulas, List.map_map, Function.comp_def]
      exact List.map_getElem_finRange derivation.assumptions
    rw [same, List.append_nil]
    exact derivation.proof

variable {D : Type u} [Category.{u} D]

def contextualAdoption {count : Nat} {body : Formula count} (adoption : Adoption commonProfile body)
    (point : D) (environment : ContextualGraphFormulaRealization.Environment D count point) :
    ContextualGraphFormulaRealization.realize D body point environment :=
  match adoption with
  | .primitive rule => CommonCoreConstructive.validateExtension rule point environment
  | .substitution indices previous =>
      (ContextualGraphFormulaRealization.realize_substitution D indices _ point environment).symm ▸
        contextualAdoption previous point (environment ∘ indices)

def contextualDeclarationReceipts {count : Nat} (declarations : List (Declaration commonProfile count))
    (point : D) (environment : ContextualGraphFormulaRealization.Environment D count point) :
    ContextualGraphRealizedDeduction.Receipts (declarationFormulas declarations) environment := by
  intro index
  let original := CommonCoreSubstitution.originalPosition Declaration.formula declarations index
  have same : (declarationFormulas declarations)[index.val] = declarations[original.val].formula := by
    simp [declarationFormulas, original, CommonCoreSubstitution.originalPosition]
  rw [same]
  exact contextualAdoption declarations[original.val].adoption point environment

def appendContextualReceipts {count : Nat} {point : D}
    {first second : List (Formula count)}
    {environment : ContextualGraphFormulaRealization.Environment D count point}
    (left : ContextualGraphRealizedDeduction.Receipts first environment)
    (right : ContextualGraphRealizedDeduction.Receipts second environment) :
    ContextualGraphRealizedDeduction.Receipts (first ++ second) environment := by
  intro index
  by_cases earlier : index.val < first.length
  · simpa only [List.getElem_append_left earlier] using left ⟨index.val, earlier⟩
  · have bound : index.val - first.length < second.length := by
      have total := index.isLt
      simp only [List.length_append] at total
      omega
    simpa only [List.getElem_append_right (Nat.le_of_not_gt earlier)] using
      right ⟨index.val - first.length, bound⟩

/-- Full future-sensitive interpretation computes a realizer from the
actual source deduction and separate law/local receipt occurrences. -/
def contextual {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile assumptions body) (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions environment) :
    ContextualGraphFormulaRealization.realize D body point environment :=
  ContextualGraphRealizedDeduction.interpret derivation.proof point environment
    (appendContextualReceipts (contextualDeclarationReceipts derivation.declarations point environment) receipts)

def contextualClosed {count : Nat} {body : Formula count}
    (derivation : Derivation commonProfile [] body) (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D count point) :
    ContextualGraphFormulaRealization.realize D body point environment :=
  contextual derivation point environment (fun index => Fin.elim0 index)

/-- Variable substitution reindexes each retained local receipt at the
same hypothesis occurrence. No witness is extracted from a proposition. -/
def substitutedContextualReceipts {count other : Nat} (indices : Fin count → Fin other)
    (assumptions : List (Formula count)) (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D other point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions (environment ∘ indices)) :
    ContextualGraphRealizedDeduction.Receipts (assumptions.map (substitute indices)) environment := by
  intro index
  let original := CommonCoreSubstitution.originalPosition (substitute indices) assumptions index
  have same : (assumptions.map (substitute indices))[index.val] =
      substitute indices assumptions[original.val] := by
    simp [original, CommonCoreSubstitution.originalPosition]
  rw [same, ContextualGraphFormulaRealization.realize_substitution]
  exact receipts original

def contextualSubstitution {count other : Nat} (indices : Fin count → Fin other)
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile assumptions body) (point : D)
    (environment : ContextualGraphFormulaRealization.Environment D other point)
    (receipts : ContextualGraphRealizedDeduction.Receipts assumptions (environment ∘ indices)) :
    ContextualGraphFormulaRealization.realize D (substitute indices body) point environment :=
  contextual (derivation.substitute indices) point environment
    (substitutedContextualReceipts indices assumptions point environment receipts)

/-- A local cut interprets the replacement proofs at their actual law and
local receipts, including their quantified and equality-sensitive evidence. -/
def contextualCut {count : Nat} {source target : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile source body)
    (replacement : (index : Fin source.length) → GraphRealizedDeduction.Proof
      (declarationFormulas derivation.declarations ++ target) source[index.val])
    (point : D) (environment : ContextualGraphFormulaRealization.Environment D count point)
    (receipts : ContextualGraphRealizedDeduction.Receipts target environment) :
    ContextualGraphFormulaRealization.realize D body point environment :=
  contextual (derivation.cut replacement) point environment receipts

theorem contextual_closed_falsity_impossible {count : Nat} :
    ¬ Nonempty (Derivation commonProfile ([] : List (Formula count)) .bottom) := by
  rintro ⟨proof⟩
  let environment : ContextualGraphFormulaRealization.Environment Nat count 0 :=
    fun _ => ContextualGraphRealizedTheory.loopValue 0
  exact PEmpty.elim (contextualClosed proof 0 environment)

theorem contextual_foundation_not_derived :
    ¬ Nonempty (Derivation commonProfile [] CommonCore.foundationAxiom) := by
  rintro ⟨proof⟩
  exact CommonCoreConstructive.foundation_has_no_realizer
    ⟨contextualClosed proof 0 (CommonCoreConstructive.emptyEnvironment 0)⟩

theorem contextual_excluded_middle_not_derived :
    ¬ Nonempty (Derivation commonProfile [] ContextualGraphRealizedDeductionControls.excludedMiddle) := by
  rintro ⟨proof⟩
  exact ContextualGraphRealizedDeductionControls.excluded_middle_empty
    ⟨contextualClosed proof 0 (ContextualGraphRealizedDeductionControls.environment 1 0)⟩

variable {S : Type v} {member : S → S → Prop}

theorem ordinaryAdoption (operations : CommonCoreClassical.Operations S member)
    (powers : CommonCoreClassicalCollection.PowerOperation S member)
    (collection : CommonCoreClassicalCollection.StrongCollection member)
    {count : Nat} {body : Formula count} (adoption : Adoption commonProfile body)
    (environment : Fin count → S) : Tarski member body environment := by
  induction adoption with
  | primitive rule =>
      exact CommonCoreClassicalCollection.validateExtension operations powers collection rule environment
  | substitution indices _ ih =>
      exact (CommonCoreClassicalLogic.substitute_iff member indices _ environment).mpr (ih _)

theorem ordinary (operations : CommonCoreClassical.Operations S member)
    (powers : CommonCoreClassicalCollection.PowerOperation S member)
    (collection : CommonCoreClassicalCollection.StrongCollection member)
    {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile assumptions body) (environment : Fin count → S)
    (receipts : (index : Fin assumptions.length) → Tarski member assumptions[index.val] environment) :
    Tarski member body environment := by
  apply CommonCoreClassicalLogic.proof_sound member derivation.proof environment
  intro index
  by_cases law : index.val < (declarationFormulas derivation.declarations).length
  · rw [List.getElem_append_left law]
    let original := CommonCoreSubstitution.originalPosition Declaration.formula derivation.declarations
      ⟨index.val, law⟩
    have same : (declarationFormulas derivation.declarations)[index.val] =
        derivation.declarations[original.val].formula := by
      simp [declarationFormulas, original, CommonCoreSubstitution.originalPosition]
    rw [same]
    exact ordinaryAdoption operations powers collection derivation.declarations[original.val].adoption environment
  · have bound : index.val - (declarationFormulas derivation.declarations).length < assumptions.length := by
      have total := index.isLt
      simp only [List.length_append] at total
      omega
    simpa only [List.getElem_append_right (Nat.le_of_not_gt law)] using
      receipts ⟨index.val - (declarationFormulas derivation.declarations).length, bound⟩

theorem hyperset {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile assumptions body) (environment : Fin count → HSet.{v})
    (receipts : (index : Fin assumptions.length) → Tarski (· ∈ ·) assumptions[index.val] environment) :
    Tarski (· ∈ ·) body environment :=
  ordinary CommonCoreClassical.hypersetOperations CommonCoreClassicalCollection.hypersetPower
    CommonCoreClassicalCollection.hyperset_strongCollection derivation environment receipts

theorem wellFounded {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation commonProfile assumptions body) (environment : Fin count → ZFSet.{v})
    (receipts : (index : Fin assumptions.length) → Tarski (· ∈ ·) assumptions[index.val] environment) :
    Tarski (· ∈ ·) body environment :=
  ordinary CommonCoreClassical.wellFoundedOperations CommonCoreClassicalCollection.wellFoundedPower
    CommonCoreClassicalCollection.wellFounded_strongCollection derivation environment receipts

theorem hyperset_closed_falsity_impossible {count : Nat} :
    ¬ Nonempty (Derivation commonProfile ([] : List (Formula count)) .bottom) := by
  rintro ⟨proof⟩
  exact hyperset proof (fun _ => (∅ : HSet.{0})) (fun index => Fin.elim0 index)

theorem wellFounded_closed_falsity_impossible {count : Nat} :
    ¬ Nonempty (Derivation commonProfile ([] : List (Formula count)) .bottom) := by
  rintro ⟨proof⟩
  exact wellFounded proof (fun _ => (∅ : ZFSet.{0})) (fun index => Fin.elim0 index)

theorem quine_not_derived :
    ¬ Nonempty (Derivation commonProfile [] CommonCoreClassical.quineSentence) := by
  rintro ⟨proof⟩
  exact CommonCoreClassical.wellFounded_no_quine.{0} Fin.elim0
    (wellFounded proof Fin.elim0 (fun index => Fin.elim0 index))

end Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation
