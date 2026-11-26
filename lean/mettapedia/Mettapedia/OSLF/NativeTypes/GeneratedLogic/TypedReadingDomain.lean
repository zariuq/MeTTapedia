import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Reference
import Mettapedia.GSLT.LanguageDef.WellSortedFillInversion

/-! # Transport through a typed reading's object domain -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (EquationDiscipline TypedStep)
open Mettapedia.OSLF.MeTTaIL.Reflection (ReflectionProfile)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted (ReflectiveScopeSafeAt)

/-- The object sort is determined by variable lookup, by a constructor label, or
by the language's typing of a bare collection. -/
theorem object_base_sort_unique {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {term : Pattern} {first second : String}
    (labelSort : ∀ ⦃left right : GrammarRule⦄,
      left ∈ language.terms → right ∈ language.terms → left.label = right.label →
      left.category = right.category)
    (collectionSort : ∀ ⦃kind elements rest first second⦄,
      HasType language free bound (.collection kind elements rest) (.base first) →
      HasType language free bound (.collection kind elements rest) (.base second) → first = second)
    (firstTyped : HasType language free bound term (.base first))
    (secondTyped : HasType language free bound term (.base second))
    (object : IsObject term) : first = second := by
  have firstCopy := firstTyped
  cases firstTyped with
  | bvar lookup =>
      cases secondTyped with
      | bvar other => exact TypeExpr.base.inj (Option.some.inj (lookup.symm.trans other))
  | fvar lookup =>
      cases secondTyped with
      | fvar other => exact TypeExpr.base.inj (Option.some.inj (lookup.symm.trans other))
  | constructor member =>
      obtain ⟨_, member', label, _, category, _⟩ := hasType_apply_inversion secondTyped
      rw [TypeExpr.base.inj category]
      exact labelSort member member' label
  | subst => simp [IsObject, isObjectPattern] at object
  | collectionConstructor => exact collectionSort firstCopy secondTyped

/-- A predicate preserved in both directions by the generating edges of an equivalence
is preserved by the full equivalence. -/
theorem eqvGen_predicate_iff {α : Type*} {R : α → α → Prop} {P : α → Prop}
    (preserves : ∀ ⦃first second⦄, R first second → (P first ↔ P second))
    {first second : α} (equivalent : Relation.EqvGen R first second) : P first ↔ P second := by
  induction equivalent with
  | rel _ _ edge => exact preserves edge
  | refl => exact Iff.rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

/-- Lift an equivalence through a domain on which its generators translate. The reverse
edge also needs the domain, so the preservation premise is two-sided. -/
theorem eqvGen_map_on_domain {α : Type*} {R S : α → α → Prop} {P : α → Prop}
    (preserves : ∀ ⦃first second⦄, R first second → (P first ↔ P second))
    (edgeMap : ∀ ⦃first second⦄, R first second → P first → S first second)
    {first second : α} (equivalent : Relation.EqvGen R first second) (admitted : P first) :
    Relation.EqvGen S first second := by
  induction equivalent with
  | rel first second edge => exact .rel first second (edgeMap edge admitted)
  | refl => exact .refl _
  | symm _ _ turn ih =>
      exact .symm _ _ (ih ((eqvGen_predicate_iff preserves turn).mpr admitted))
  | trans _ _ _ before _ left right =>
      exact .trans _ _ _ (left admitted) (right ((eqvGen_predicate_iff preserves before).mp admitted))

/-- A Boolean or propositional object domain characterized by one base sort in the
name context of the reading. Sort uniqueness constrains the connecting typed steps. -/
structure TypedReadingDomain (language : LanguageDef) (names : Option String) (sort : String)
    (admitted : Pattern → Prop) : Prop where
  typed : ∀ ⦃term⦄, admitted term →
    HasType language (EquationReading.nameContext names) [] term (.base sort)
  ofTyped : ∀ ⦃term⦄, HasType language (EquationReading.nameContext names) [] term (.base sort) →
    IsObject term → admitted term
  sortUnique : ∀ ⦃term first second⦄,
    HasType language (EquationReading.nameContext names) [] term (.base first) →
    HasType language (EquationReading.nameContext names) [] term (.base second) →
    IsObject term → first = second

namespace TypedReadingDomain

variable {language : LanguageDef} {names : Option String} {sort : String} {admitted : Pattern → Prop}
variable {relEnv : RelationEnv} {discipline : EquationDiscipline} {profile : ReflectionProfile}
variable {rules : RuleReading} {first second : Pattern}

theorem typedStep (domain : TypedReadingDomain language names sort admitted)
    (step : ObjectStep relEnv language ⟨.typed discipline profile .sorts names, rules⟩ first second)
    (source : admitted first) :
    TypedStep relEnv language discipline (EquationReading.nameContext names) [] (.base sort)
      (ReflectiveScopeSafeAt profile 0) first second := by
  obtain ⟨_, _, _, ⟨actual, rfl⟩, firstFormed, secondFormed, edge⟩ := step
  obtain rfl := domain.sortUnique firstFormed.typed (domain.typed source) firstFormed.object
  exact ⟨firstFormed, secondFormed, edge⟩

theorem step_iff (domain : TypedReadingDomain language names sort admitted)
    (step : ObjectStep relEnv language ⟨.typed discipline profile .sorts names, rules⟩ first second) :
    admitted first ↔ admitted second := by
  obtain ⟨_, _, _, ⟨actual, rfl⟩, firstFormed, secondFormed, _⟩ := step
  constructor
  · intro source
    obtain rfl := domain.sortUnique firstFormed.typed (domain.typed source) firstFormed.object
    exact domain.ofTyped secondFormed.typed secondFormed.object
  · intro target
    obtain rfl := domain.sortUnique secondFormed.typed (domain.typed target) secondFormed.object
    exact domain.ofTyped firstFormed.typed firstFormed.object

theorem equivalent_iff (domain : TypedReadingDomain language names sort admitted)
    (equivalent : ObjectEquivalent relEnv language ⟨.typed discipline profile .sorts names, rules⟩ first second) :
    admitted first ↔ admitted second := by
  refine eqvGen_predicate_iff ?_ equivalent
  intro _ _ edge
  exact domain.step_iff edge

theorem map_equivalent (domain : TypedReadingDomain language names sort admitted)
    {target : Pattern → Pattern → Prop}
    (edgeMap : ∀ ⦃source dest⦄,
      TypedStep relEnv language discipline (EquationReading.nameContext names) [] (.base sort)
        (ReflectiveScopeSafeAt profile 0) source dest → target source dest)
    (equivalent : ObjectEquivalent relEnv language ⟨.typed discipline profile .sorts names, rules⟩ first second)
    (source : admitted first) : Relation.EqvGen target first second := by
  refine eqvGen_map_on_domain ?_ ?_ equivalent source
  · intro _ _ edge
    exact domain.step_iff edge
  · intro _ _ edge good
    exact edgeMap (domain.typedStep edge good)

end TypedReadingDomain

/-- A formed generator at a base sort supplies one generator of the full typed reading. -/
theorem objectStep_of_typed_base
    {language : LanguageDef} {names : Option String} {sort : String} {relEnv : RelationEnv}
    {discipline : EquationDiscipline} {profile : ReflectionProfile} {rules : RuleReading}
    {first second : Pattern}
    (step : TypedStep relEnv language discipline (EquationReading.nameContext names) [] (.base sort)
      (ReflectiveScopeSafeAt profile 0) first second) :
    ObjectStep relEnv language ⟨.typed discipline profile .sorts names, rules⟩ first second :=
  ⟨step.1.object, step.2.1.object, .base sort, ⟨sort, rfl⟩, step⟩

section Controls

private def forward : Bool → Bool → Prop := fun source target => source = false ∧ target = true

example : Relation.EqvGen forward true false :=
  .symm _ _ (.rel _ _ ⟨rfl, rfl⟩)

example : ¬ (∀ ⦃first second⦄, forward first second → (first = false ↔ second = false)) := by
  intro preserved
  exact Bool.noConfusion ((preserved (first := false) (second := true) ⟨rfl, rfl⟩).mp rfl)

end Controls

#print axioms eqvGen_map_on_domain
#print axioms TypedReadingDomain.map_equivalent
#print axioms objectStep_of_typed_base

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
