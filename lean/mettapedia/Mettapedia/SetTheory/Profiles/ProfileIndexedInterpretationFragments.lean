import Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation

/-!
# Constructed common, Foundation and classical profile fragments

Foundation and excluded middle are independent syntax selections. Their
validation uses the actual well-founded carrier or the actual hyperset
carrier when Foundation is absent. These fragments do not stand for full
ZF, CZF, AFA or HOTG, and Foundation here is the declared regularity sentence,
not an automatically adopted membership-induction schema.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open ContextualMaterialLogic (Formula substitute)
open Mettapedia.SetTheory.CarveOuts.Sites (Tarski)
open ProfileIndexedCalculus

universe u

inductive Fragment where
  | common | foundation | classical | classicalFoundation
  deriving DecidableEq, Repr

def Fragment.hasFoundation : Fragment → Bool
  | .common | .classical => false
  | .foundation | .classicalFoundation => true

def Fragment.hasExcludedMiddle : Fragment → Bool
  | .common | .foundation => false
  | .classical | .classicalFoundation => true

def excludedMiddle {count : Nat} (body : Formula count) : Formula count :=
  .either body (.imply body .bottom)

inductive FragmentRuleName where
  | common (law : CommonCore.LawName)
  | foundation | excludedMiddle
  deriving DecidableEq, Repr

inductive FragmentRule (fragment : Fragment) : {count : Nat} → Formula count → Type where
  | common {count : Nat} {body : Formula count} (rule : CommonCore.Extension body) :
      FragmentRule fragment body
  | foundation (enabled : fragment.hasFoundation = true) :
      FragmentRule fragment CommonCore.foundationAxiom
  | excludedMiddle {count : Nat} (enabled : fragment.hasExcludedMiddle = true) (body : Formula count) :
      FragmentRule fragment (excludedMiddle body)

def fragmentProfile (fragment : Fragment) : Profile where
  RuleName := FragmentRuleName
  Rule := FragmentRule fragment
  ruleName := fun rule => match rule with
    | .common earlier => .common earlier.name
    | .foundation _ => .foundation
    | .excludedMiddle _ _ => .excludedMiddle

structure FragmentInclusion (source target : Fragment) : Prop where
  foundation : source.hasFoundation = true → target.hasFoundation = true
  excludedMiddle : source.hasExcludedMiddle = true → target.hasExcludedMiddle = true

def fragmentTranslation {source target : Fragment} (inclusion : FragmentInclusion source target) :
    Translation (fragmentProfile source) (fragmentProfile target) where
  rule := fun rule => match rule with
    | .common earlier => .primitive (.common earlier)
    | .foundation enabled => .primitive (.foundation (inclusion.foundation enabled))
    | .excludedMiddle enabled body => .primitive (.excludedMiddle (inclusion.excludedMiddle enabled) body)

def commonFragmentEmbedding (fragment : Fragment) : Translation commonProfile (fragmentProfile fragment) where
  rule := fun adopted => .primitive (.common adopted)

def commonFragmentRecovery : Translation (fragmentProfile .common) commonProfile where
  rule := fun rule => match rule with
    | .common earlier => .primitive earlier
    | .foundation enabled => Bool.noConfusion enabled
    | .excludedMiddle enabled _ => Bool.noConfusion enabled

theorem commonFragment_derivable_iff {count : Nat} (assumptions : List (Formula count))
    (body : Formula count) :
    Nonempty (Derivation (fragmentProfile .common) assumptions body) ↔
      Nonempty (Derivation commonProfile assumptions body) :=
  ⟨fun ⟨proof⟩ => ⟨commonFragmentRecovery.derivation proof⟩,
    fun ⟨proof⟩ => ⟨(commonFragmentEmbedding .common).derivation proof⟩⟩

theorem wellFoundedRule (fragment : Fragment) {count : Nat} {body : Formula count}
    (rule : FragmentRule fragment body) (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) body environment := by
  cases rule with
  | common earlier =>
      exact CommonCoreClassicalCollection.validateExtension
        CommonCoreClassical.wellFoundedOperations CommonCoreClassicalCollection.wellFoundedPower
        CommonCoreClassicalCollection.wellFounded_strongCollection earlier environment
  | foundation => exact CommonCoreClassical.wellFounded_foundation environment
  | excludedMiddle _ formula => exact Classical.em (Tarski (· ∈ ·) formula environment)

theorem hypersetRule (fragment : Fragment) (withoutFoundation : fragment.hasFoundation = false)
    {count : Nat} {body : Formula count} (rule : FragmentRule fragment body)
    (environment : Fin count → HSet.{u}) : Tarski (· ∈ ·) body environment := by
  cases rule with
  | common earlier =>
      exact CommonCoreClassicalCollection.validateExtension
        CommonCoreClassical.hypersetOperations CommonCoreClassicalCollection.hypersetPower
        CommonCoreClassicalCollection.hyperset_strongCollection earlier environment
  | foundation enabled => exact Bool.noConfusion (withoutFoundation.symm.trans enabled)
  | excludedMiddle _ formula => exact Classical.em (Tarski (· ∈ ·) formula environment)

theorem wellFoundedAdoption (fragment : Fragment) {count : Nat} {body : Formula count}
    (adoption : Adoption (fragmentProfile fragment) body) (environment : Fin count → ZFSet.{u}) :
    Tarski (· ∈ ·) body environment := by
  induction adoption with
  | primitive rule => exact wellFoundedRule fragment rule environment
  | substitution indices _ ih =>
      exact (CommonCoreClassicalLogic.substitute_iff (· ∈ ·) indices _ environment).mpr (ih _)

theorem hypersetAdoption (fragment : Fragment) (withoutFoundation : fragment.hasFoundation = false)
    {count : Nat} {body : Formula count} (adoption : Adoption (fragmentProfile fragment) body)
    (environment : Fin count → HSet.{u}) : Tarski (· ∈ ·) body environment := by
  induction adoption with
  | primitive rule => exact hypersetRule fragment withoutFoundation rule environment
  | substitution indices _ ih =>
      exact (CommonCoreClassicalLogic.substitute_iff (· ∈ ·) indices _ environment).mpr (ih _)

theorem fragmentOrdinary {S : Type u} (member : S → S → Prop) (fragment : Fragment)
    (validate : {count : Nat} → {body : Formula count} →
      Adoption (fragmentProfile fragment) body → (environment : Fin count → S) → Tarski member body environment)
    {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation (fragmentProfile fragment) assumptions body) (environment : Fin count → S)
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
    exact validate derivation.declarations[original.val].adoption environment
  · have bound : index.val - (declarationFormulas derivation.declarations).length < assumptions.length := by
      have total := index.isLt
      simp only [List.length_append] at total
      omega
    simpa only [List.getElem_append_right (Nat.le_of_not_gt law)] using
      receipts ⟨index.val - (declarationFormulas derivation.declarations).length, bound⟩

theorem fragmentWellFounded (fragment : Fragment) {count : Nat}
    {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation (fragmentProfile fragment) assumptions body)
    (environment : Fin count → ZFSet.{u})
    (receipts : (index : Fin assumptions.length) → Tarski (· ∈ ·) assumptions[index.val] environment) :
    Tarski (· ∈ ·) body environment :=
  fragmentOrdinary (· ∈ ·) fragment (wellFoundedAdoption fragment) derivation environment receipts

theorem fragmentHyperset (fragment : Fragment) (withoutFoundation : fragment.hasFoundation = false)
    {count : Nat} {assumptions : List (Formula count)} {body : Formula count}
    (derivation : Derivation (fragmentProfile fragment) assumptions body)
    (environment : Fin count → HSet.{u})
    (receipts : (index : Fin assumptions.length) → Tarski (· ∈ ·) assumptions[index.val] environment) :
    Tarski (· ∈ ·) body environment :=
  fragmentOrdinary (· ∈ ·) fragment (hypersetAdoption fragment withoutFoundation) derivation environment receipts

theorem every_fragment_closed_falsity_impossible (fragment : Fragment) {count : Nat} :
    ¬ Nonempty (Derivation (fragmentProfile fragment) ([] : List (Formula count)) .bottom) := by
  rintro ⟨proof⟩
  exact fragmentWellFounded fragment proof (fun _ => (∅ : ZFSet.{0})) (fun index => Fin.elim0 index)

def foundationDerivation : Derivation (fragmentProfile .foundation) [] CommonCore.foundationAxiom :=
  Derivation.adopt 0 (.primitive (.foundation rfl))

def excludedMiddleDerivation {count : Nat} (body : Formula count) :
    Derivation (fragmentProfile .classical) [] (excludedMiddle body) :=
  Derivation.adopt 0 (.primitive (.excludedMiddle rfl body))

/-- A source rule cannot be silently imported into the constructive common
profile merely because both profiles share equality/membership syntax. -/
theorem foundation_has_no_common_translation :
    ¬ Nonempty (Translation (fragmentProfile .foundation) commonProfile) := by
  rintro ⟨translation⟩
  exact contextual_foundation_not_derived ⟨translation.derivation foundationDerivation⟩

theorem classical_has_no_common_translation :
    ¬ Nonempty (Translation (fragmentProfile .classical) commonProfile) := by
  rintro ⟨translation⟩
  have proof := translation.derivation
    (excludedMiddleDerivation (Formula.member (n := 1) 0 0))
  exact contextual_excluded_middle_not_derived ⟨proof⟩

end Mettapedia.SetTheory.Profiles.ProfileIndexedInterpretation
