import Mettapedia.GSLT.LanguageDef.CostCanonicalReachablePairAlignment
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostFillDeterminism

/-!
# The reachable recursive type domain of the generated rho Cost language

The paired canonical recursion is total on a type domain that never exposes
a structural collection fibre.  For rho this domain is the collection-free
codomain spine: base types, and arrows whose result spine ends in a base
type.  Admissibility of every generated constructor parameter is derived
from the source table rather than re-proved per generated rule: both static
type images are structure-preserving with base sorts mapped to base sorts,
so parameter admissibility transports from the six authored rho rules, the
sole bare-collection rule is excluded by the recursion's own
non-bare-collection hypothesis, and the fixed apparatus constructors are
discharged by direct computation.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

/-- Collection-free codomain spine: the fragment of type expressions the
paired canonical recursion may reach as a result fibre. -/
def rhoReachableType : TypeExpr → Bool
  | .base _ => true
  | .arrow _ codomain => rhoReachableType codomain
  | .multiBinder _ => false
  | .collection _ _ => false

/-- Reachability of the result type demanded by one authored parameter.
Parameters without a demanded result type constrain nothing. -/
def rhoReachableParam (parameter : TermParam) : Bool :=
  match parameterType? parameter with
  | some expected => rhoReachableType expected
  | none => true

private theorem rhoReachableType_costBaseTypeExpr (type : TypeExpr) :
    rhoReachableType (costBaseTypeExpr type) = rhoReachableType type := by
  induction type with
  | base sort => rfl
  | arrow domain codomain _ ih =>
      simpa [costBaseTypeExpr, rhoReachableType] using ih
  | multiBinder body _ => simp [costBaseTypeExpr, rhoReachableType]
  | collection collectionType element _ =>
      simp [costBaseTypeExpr, rhoReachableType]

private theorem rhoReachableType_costWrappedTypeExpr (interactingSort : String)
    (type : TypeExpr) :
    rhoReachableType (costWrappedTypeExpr interactingSort type) =
      rhoReachableType type := by
  induction type with
  | base sort =>
      by_cases selected : sort = interactingSort <;>
        simp [costWrappedTypeExpr, rhoReachableType, selected]
  | arrow domain codomain _ ih =>
      simpa [costWrappedTypeExpr, rhoReachableType] using ih
  | multiBinder body _ => simp [costWrappedTypeExpr, rhoReachableType]
  | collection collectionType element _ =>
      simp [costWrappedTypeExpr, rhoReachableType]

private theorem rhoReachableParam_map_costBase (parameter : TermParam)
    (source : rhoReachableParam parameter = true) :
    rhoReachableParam (mapParameterType costBaseTypeExpr parameter) = true := by
  cases parameter with
  | simple name type =>
      simpa [rhoReachableParam, mapParameterType, parameterType?,
        rhoReachableType_costBaseTypeExpr] using source
  | abstractionNamed binder name type =>
      cases type with
      | base sort =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr, rhoReachableType]
      | arrow domain codomain =>
          simpa [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr, rhoReachableType,
            rhoReachableType_costBaseTypeExpr] using source
      | multiBinder body =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr]
      | collection collectionType element =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr]
  | multiAbstractionNamed binders name type =>
      cases type with
      | base sort =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr, rhoReachableType]
      | arrow domain codomain =>
          cases domain with
          | base sort =>
              simp [rhoReachableParam, mapParameterType, parameterType?,
                costBaseTypeExpr]
          | arrow innerDomain innerCodomain =>
              simp [rhoReachableParam, mapParameterType, parameterType?,
                costBaseTypeExpr]
          | multiBinder body =>
              simpa [rhoReachableParam, mapParameterType, parameterType?,
                costBaseTypeExpr, rhoReachableType,
                rhoReachableType_costBaseTypeExpr] using source
          | collection collectionType element =>
              simp [rhoReachableParam, mapParameterType, parameterType?,
                costBaseTypeExpr]
      | multiBinder body =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr]
      | collection collectionType element =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costBaseTypeExpr]

private theorem rhoReachableParam_map_costWrapped (interactingSort : String)
    (parameter : TermParam)
    (source : rhoReachableParam parameter = true) :
    rhoReachableParam
      (mapParameterType (costWrappedTypeExpr interactingSort) parameter) =
        true := by
  cases parameter with
  | simple name type =>
      simpa [rhoReachableParam, mapParameterType, parameterType?,
        rhoReachableType_costWrappedTypeExpr] using source
  | abstractionNamed binder name type =>
      cases type with
      | base sort =>
          by_cases selected : sort = interactingSort <;>
            simp [rhoReachableParam, mapParameterType, parameterType?,
              costWrappedTypeExpr, rhoReachableType, selected]
      | arrow domain codomain =>
          simpa [rhoReachableParam, mapParameterType, parameterType?,
            costWrappedTypeExpr, rhoReachableType,
            rhoReachableType_costWrappedTypeExpr] using source
      | multiBinder body =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costWrappedTypeExpr]
      | collection collectionType element =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costWrappedTypeExpr]
  | multiAbstractionNamed binders name type =>
      cases type with
      | base sort =>
          by_cases selected : sort = interactingSort <;>
            simp [rhoReachableParam, mapParameterType, parameterType?,
              costWrappedTypeExpr, rhoReachableType, selected]
      | arrow domain codomain =>
          cases domain with
          | base sort =>
              by_cases selected : sort = interactingSort <;>
                simp [rhoReachableParam, mapParameterType, parameterType?,
                  costWrappedTypeExpr, selected]
          | arrow innerDomain innerCodomain =>
              simp [rhoReachableParam, mapParameterType, parameterType?,
                costWrappedTypeExpr]
          | multiBinder body =>
              simpa [rhoReachableParam, mapParameterType, parameterType?,
                costWrappedTypeExpr, rhoReachableType,
                rhoReachableType_costWrappedTypeExpr] using source
          | collection collectionType element =>
              simp [rhoReachableParam, mapParameterType, parameterType?,
                costWrappedTypeExpr]
      | multiBinder body =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costWrappedTypeExpr]
      | collection collectionType element =>
          simp [rhoReachableParam, mapParameterType, parameterType?,
            costWrappedTypeExpr]

private theorem mem_of_mem_zipIdx {α : Type _} :
    ∀ {entries : List α} {start : Nat} {entry : α × Nat},
      entry ∈ entries.zipIdx start → entry.1 ∈ entries := by
  intro entries
  induction entries with
  | nil => intro start entry membership; cases membership
  | cons head tail ih =>
      intro start entry membership
      rw [List.zipIdx_cons] at membership
      rcases List.mem_cons.mp membership with rfl | inTail
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih inTail)

private theorem rhoSourceRule_paramsReachable_zero :
    (rhoCalc.terms[0].params.all rhoReachableParam) = true := by rfl
private theorem rhoSourceRule_paramsReachable_one :
    (rhoCalc.terms[1].params.all rhoReachableParam) = true := by rfl
private theorem rhoSourceRule_paramsReachable_two :
    (rhoCalc.terms[2].params.all rhoReachableParam) = true := by rfl
private theorem rhoSourceRule_paramsReachable_four :
    (rhoCalc.terms[4].params.all rhoReachableParam) = true := by rfl
private theorem rhoSourceRule_paramsReachable_five :
    (rhoCalc.terms[5].params.all rhoReachableParam) = true := by rfl

private theorem rhoSourceParallel_bare :
    ∃ parameterName collectionType elementType,
      rhoCalc.terms[3].params =
        [.simple parameterName (.collection collectionType elementType)] := by
  exact ⟨"ps", .hashBag, .base "Proc", by rfl⟩

/-- Every parameter of every generated non-bare rho Cost rule demands a
result type on the collection-free codomain spine. -/
theorem rho_generatedParameter_reachable {rule : GrammarRule}
    (membership : rule ∈ rhoCIGSLT.costWholeLanguage.terms)
    (notBare : ¬ UsesBareCollection rule)
    {parameter : TermParam} (parameterMembership : parameter ∈ rule.params)
    {expected : TypeExpr}
    (parameterTyped : parameterType? parameter = some expected) :
    rhoReachableType expected = true := by
  suffices reachable : rhoReachableParam parameter = true by
    simpa [rhoReachableParam, parameterTyped] using reachable
  have memberships := membership
  rw [CIGSLT.costWholeLanguage_terms] at memberships
  have split : rule ∈ rhoCIGSLT.continuationRetyping.generatedLanguage.terms ∨
      rule ∈ costCoreConstructors
        rhoCIGSLT.theory.presentation.interactingSort.1.name := by
    simpa [CIGSLT.costCoreLanguage, List.mem_append] using memberships
  rcases split with generated | apparatus
  · rw [show rhoCIGSLT.continuationRetyping.generatedLanguage.terms =
        rhoCalc.terms.map (costBaseConstructor rhoInteractionCut) ++
          rhoContinuationRetyping.wrappedConstructors.map
            (fun constructor =>
              costWrappedConstructor (theory := rhoIGSLT) constructor.1)
      from rfl] at generated
    rcases List.mem_append.mp generated with baseSide | wrappedSide
    · obtain ⟨sourceRule, sourceMembership, ruleEq⟩ :=
        List.mem_map.mp baseSide
      subst ruleEq
      have sourceReachable :
          (sourceRule.params.all rhoReachableParam) = true := by
        change sourceRule ∈ [rhoCalc.terms[0], rhoCalc.terms[1],
          rhoCalc.terms[2], rhoCalc.terms[3], rhoCalc.terms[4],
          rhoCalc.terms[5]] at sourceMembership
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at sourceMembership
        rcases sourceMembership with rfl | rfl | rfl | rfl | rfl | rfl
        · exact rhoSourceRule_paramsReachable_zero
        · exact rhoSourceRule_paramsReachable_one
        · exact rhoSourceRule_paramsReachable_two
        · obtain ⟨parameterName, collectionType, elementType, shape⟩ :=
            rhoSourceParallel_bare
          exact absurd ⟨parameterName, collectionType,
            costBaseTypeExpr elementType, by
              simp [costBaseConstructor, shape, costBaseParameter,
                isSelectedContinuation, mapParameterType,
                costBaseTypeExpr]⟩ notBare
        · exact rhoSourceRule_paramsReachable_four
        · exact rhoSourceRule_paramsReachable_five
      simp only [costBaseConstructor] at parameterMembership
      obtain ⟨entry, entryMembership, parameterEq⟩ :=
        List.mem_map.mp parameterMembership
      have sourceParameter : entry.1 ∈ sourceRule.params :=
        mem_of_mem_zipIdx entryMembership
      have entryReachable : rhoReachableParam entry.1 = true :=
        List.all_eq_true.mp sourceReachable entry.1 sourceParameter
      subst parameterEq
      unfold costBaseParameter
      split
      · exact rhoReachableParam_map_costWrapped _ entry.1 entryReachable
      · exact rhoReachableParam_map_costBase entry.1 entryReachable
    · obtain ⟨constructor, _, ruleEq⟩ := List.mem_map.mp wrappedSide
      subst ruleEq
      have sourceMembership := constructor.2
      have sourceReachable :
          (constructor.1.params.all rhoReachableParam) = true := by
        change constructor.1 ∈ [rhoCalc.terms[0], rhoCalc.terms[1],
          rhoCalc.terms[2], rhoCalc.terms[3], rhoCalc.terms[4],
          rhoCalc.terms[5]] at sourceMembership
        simp only [List.mem_cons, List.not_mem_nil, or_false]
          at sourceMembership
        rcases sourceMembership with sourceEq | sourceEq | sourceEq |
          sourceEq | sourceEq | sourceEq <;> rw [sourceEq]
        · exact rhoSourceRule_paramsReachable_zero
        · exact rhoSourceRule_paramsReachable_one
        · exact rhoSourceRule_paramsReachable_two
        · obtain ⟨parameterName, collectionType, elementType, shape⟩ :=
            rhoSourceParallel_bare
          exact absurd ⟨parameterName, collectionType,
            costWrappedTypeExpr
              rhoIGSLT.presentation.interactingSort.1.name elementType, by
                rw [sourceEq]
                simp [costWrappedConstructor, shape, mapParameterType,
                  costWrappedTypeExpr]⟩
            notBare
        · exact rhoSourceRule_paramsReachable_four
        · exact rhoSourceRule_paramsReachable_five
      simp only [costWrappedConstructor] at parameterMembership
      obtain ⟨sourceParameter, sourceParameterMembership, parameterEq⟩ :=
        List.mem_map.mp parameterMembership
      have entryReachable : rhoReachableParam sourceParameter = true :=
        List.all_eq_true.mp sourceReachable sourceParameter
          sourceParameterMembership
      subst parameterEq
      exact rhoReachableParam_map_costWrapped _ sourceParameter entryReachable
  · change rule ∈ [costSignatureUnitConstructor,
      costSignatureProductConstructor,
      costSignedConstructor
        rhoCIGSLT.theory.presentation.interactingSort.1.name,
      costTokenStackEmptyConstructor, costTokenStackConsConstructor,
      costFundingConstructor, costContactConstructor] at apparatus
    simp only [List.mem_cons, List.not_mem_nil, or_false] at apparatus
    rcases apparatus with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      revert parameterMembership
    · intro parameterMembership
      simp [costSignatureUnitConstructor] at parameterMembership
    · intro parameterMembership
      simp only [costSignatureProductConstructor, List.mem_cons,
        List.not_mem_nil, or_false] at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [rhoReachableParam, parameterType?, rhoReachableType]
    · intro parameterMembership
      simp only [costSignedConstructor, List.mem_cons,
        List.not_mem_nil, or_false] at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [rhoReachableParam, parameterType?, rhoReachableType]
    · intro parameterMembership
      simp [costTokenStackEmptyConstructor] at parameterMembership
    · intro parameterMembership
      simp only [costTokenStackConsConstructor, List.mem_cons,
        List.not_mem_nil, or_false] at parameterMembership
      rcases parameterMembership with rfl | rfl <;>
        simp [rhoReachableParam, parameterType?, rhoReachableType]
    · intro parameterMembership
      simp only [costFundingConstructor, List.mem_cons,
        List.not_mem_nil, or_false] at parameterMembership
      rcases parameterMembership with rfl
      simp [rhoReachableParam, parameterType?, rhoReachableType]
    · intro parameterMembership
      simp only [costContactConstructor, List.mem_cons,
        List.not_mem_nil, or_false] at parameterMembership
      rcases parameterMembership with rfl | rfl | rfl <;>
        simp [rhoReachableParam, parameterType?, rhoReachableType]

/-- The generated rho Cost language's recursive type domain: base fibres and
collection-free arrow spines, with every non-bare generated parameter
admissible by source-table transport. -/
def rhoCanonicalRecursiveTypeDomain :
    CostCanonicalRecursiveTypeDomain rhoCIGSLT where
  Admissible := fun type => rhoReachableType type = true
  base := fun _ => rfl
  codomain := fun admissible => admissible
  noCollection := fun admissible => by
    simp [rhoReachableType] at admissible
  parameter := by
    intro rule membership notBare parameter parameterMembership expected
      parameterTyped
    exact rho_generatedParameter_reachable membership notBare
      parameterMembership parameterTyped

/-- Positive boundary: the wrapped sort fibre is admissible. -/
example : rhoCanonicalRecursiveTypeDomain.Admissible
    (.base costWrappedSortName) := rfl

/-- Positive boundary: the input-continuation arrow fibre is admissible. -/
example : rhoCanonicalRecursiveTypeDomain.Admissible
    (.arrow (.base (costBaseSortName "Name")) (.base costWrappedSortName)) :=
  rfl

/-- Negative boundary: no structural collection fibre is admissible, so the
paired recursion can never reach the order-preserving collection normalizer
with a reflectively sorted bag. -/
example : ¬ rhoCanonicalRecursiveTypeDomain.Admissible
    (.collection .hashBag (.base (costBaseSortName "Proc"))) := by
  simp [rhoCanonicalRecursiveTypeDomain, rhoReachableType]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
