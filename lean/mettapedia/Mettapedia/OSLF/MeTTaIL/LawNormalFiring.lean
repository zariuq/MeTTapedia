import Mettapedia.OSLF.MeTTaIL.LawNormalSites
import Mettapedia.OSLF.MeTTaIL.LawNormalReflective
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Firing at law-normal forms

A rule fires at the law-normal form of its focus when its left side is safe for the declared
laws (`FlatSafe`), it has no premises, its metavariable sorts are typed for the laws,
and its selected binder operation respects the laws (`LawFiringAdmissible`). The
captures are the normal forms of the original captures, and the reduct is law-equal to the
original (`rootFiring_normalize`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax CollectionLaws RuleBinding
open Mettapedia.GSLT.LanguageDef.WellSorted

variable {laws : List Laws}

/-- A rule fires at law-normal forms. -/
def LawFiringAdmissible (laws : List Laws) (environment : GeneralPremise.Environment) (index : Nat) : Prop :=
  ∀ rule spec, environment.language.rewrites[index]? = some rule →
    GeneralPremise.specification? environment index = some spec →
    FlatSafe laws rule.left ∧ rule.premises = [] ∧
      (∀ name expected, rule.typeContext.lookup name = some expected → LawTypeOk laws environment.language expected) ∧
      (∀ name dependencies, dependencies? spec name = some dependencies →
        ∀ entry ∈ dependencies, LawTypeOk laws environment.language entry)
      ∧ BinderLawsFor laws environment.reflection rule

theorem assignLawSame_normalize : ∀ assignment : ScopedRuleMatching.Assignment,
    AssignLawSame laws assignment (mapAssignment (normalize laws) assignment)
  | [] => .nil
  | (_, value) :: rest => .cons ⟨rfl, rfl, rfl, to_normalize laws value.body⟩ (assignLawSame_normalize rest)

/-- **Law-equal object terms have the same types**, for strictly typed laws. -/
theorem LawSame.hasType {language : LanguageDef} {free : FreeTypeContext}
    (admission : LawsTypedStrict laws language free) {left right : Pattern} (same : LawSame laws left right)
    {bound : List TypeExpr} {type : TypeExpr} (boundOk : ∀ entry ∈ bound, LawTypeOk laws language entry)
    (typeOk : LawTypeOk laws language type) (object : isObjectPattern left = true)
    (typed : HasType language free bound left type) : HasType language free bound right type := by
  have chain : Relation.ReflTransGen (Relation.SymmGen (LawStep laws)) left right := by
    rw [Relation.EqvGen.reflTransGen_symmGen]; exact same
  clear same
  suffices along : HasType language free bound right type ∧ isObjectPattern right = true from along.1
  induction chain with
  | refl => exact ⟨typed, object⟩
  | tail _ step ih =>
    obtain ⟨middleTyped, middleObject⟩ := ih
    rcases step with forward | backward
    · exact ⟨(forward.hasType_iff admission middleObject boundOk typeOk).mp middleTyped,
        forward.objectPattern_eq ▸ middleObject⟩
    · have object' := backward.objectPattern_eq.symm ▸ middleObject
      exact ⟨(backward.hasType_iff admission object' boundOk typeOk).mpr middleTyped, object'⟩

/-- **Normalized captures keep the declared sorts.** -/
theorem typedAssignment_normalize {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    (admission : LawsTypedStrict laws environment.language environment.free)
    (boundOk : ∀ entry ∈ context.bound, LawTypeOk laws environment.language entry)
    (sortsOk : ∀ name expected, context.rule.typeContext.lookup name = some expected →
      LawTypeOk laws environment.language expected)
    (dependenciesOk : ∀ name dependencies, dependencies? context.spec name = some dependencies →
      ∀ entry ∈ dependencies, LawTypeOk laws environment.language entry)
    {assignment : ScopedRuleMatching.Assignment} (typed : GeneralPremise.TypedAssignment environment context assignment) :
    GeneralPremise.TypedAssignment environment context (mapAssignment (normalize laws) assignment) := by
  obtain ⟨sorts, objects⟩ := typed
  refine ⟨fun name value member => ?_, fun name value member => ?_⟩
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    obtain ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, bodyTyped⟩ :=
      sorts name₀ value₀ inOriginal
    refine ⟨dependencies, expected, declared, sort, sameDependencies, sameAmbient, ?_⟩
    exact LawSame.hasType admission (to_normalize laws value₀.body)
      (fun entry inside => by
        rcases List.mem_append.mp inside with inDependencies | inBound
        · exact dependenciesOk name₀ dependencies declared entry inDependencies
        · exact boundOk entry inBound)
      (sortsOk name₀ expected sort) (objects name₀ value₀ inOriginal) bodyTyped
  · obtain ⟨⟨name₀, value₀⟩, inOriginal, same⟩ := List.mem_map.mp member
    simp only [Prod.mk.injEq] at same
    obtain ⟨rfl, rfl⟩ := same
    exact normalize_object _ (objects name₀ value₀ inOriginal)

/-- **A root firing has a counterpart at the law-normal form of its focus**, with normalized
captures and a law-equal result. -/
theorem rootFiring_normalize {environment : GeneralPremise.Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (admissible : LawFiringAdmissible laws environment index)
    (strict : LawsTypedStrict laws environment.language environment.free)
    (boundOk : ∀ entry ∈ bound, LawTypeOk laws environment.language entry)
    (typeOk : LawTypeOk laws environment.language type) :
    ∃ trace' target', GeneralPremise.RootFiring environment bound type (normalize laws source) index trace'
        (mapAssignment (normalize laws) captured) (mapAssignment (normalize laws) completed) history target' ∧
      LawSame laws target target' := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified admitted sourceSorted matched typed premises reduced
      targetSorted =>
    obtain ⟨safe, unconditional, sortsOk, dependenciesOk, binderOk⟩ :=
      admissible rule spec selected specified
    rw [unconditional] at premises
    cases premises
    obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.traced_iff_matches.mpr
      (matches_normalize laws safe (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩))
    obtain ⟨target', reduced', same⟩ := instantiateWith?_lawSame rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule)
      (binderOperation_lawSame _ rule binderOk)
      rule.right .right [] 0
      captured (mapAssignment (normalize laws) captured) target (assignLawSame_normalize captured) reduced
    refine ⟨trace', target', ?_, same⟩
    refine .fire selected specified admitted
      (LawSame.openPatternWellSorted strict (to_normalize laws source) boundOk typeOk sourceSorted) traced
      (typedAssignment_normalize strict boundOk sortsOk dependenciesOk typed) ?_ reduced'
      (LawSame.openPatternWellSorted strict same boundOk typeOk targetSorted)
    rw [unconditional]
    exact .nil

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
