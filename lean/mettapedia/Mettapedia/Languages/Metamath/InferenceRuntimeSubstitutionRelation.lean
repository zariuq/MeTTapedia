import Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge

/-!
# Extensional runtime substitutions for Metamath inference

`RuntimeSubstitutionMap` is a canonical materialization of a finite visible
substitution.  The live verifier instead constructs its `HashMap` incrementally
while checking floating hypotheses, so its internal insertion history need not
be definitionally equal to that canonical map.  This file states the exact
lookup-level relation needed at that boundary and proves that related maps give
the same formula-substitution behavior.

The relation excludes hidden runtime entries: every successful lookup must come
from a visible finite binding, and every visible binding must be the selected
runtime value.  Distinct source keys are therefore explicit whenever the
relation is used as a functional representation.
-/

namespace Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation

open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceSideConditionsSemantics
open Mettapedia.Languages.Metamath.InferenceSideConditionsRuntimeBridge

/-- Exact extensional correspondence between a visible finite substitution and
an arbitrary live verifier map.  Both lookup directions are included so that
neither missing visible bindings nor hidden runtime bindings are permitted. -/
def RuntimeSubstitutionCorrespondence
    (substitution : FiniteSubstitution)
    (runtimeSubstitution : Std.HashMap String RuntimeFormula) : Prop :=
  ∀ name runtimeFormula,
    runtimeSubstitution[name]? = some runtimeFormula ↔
      ∃ replacement : ConstantHeadedFormula,
        LookupSemantics substitution name replacement ∧
          runtimeFormula = replacement.toRuntime

/-- The canonical finite-list materialization has exact extensional
correspondence once duplicate source keys are excluded. -/
theorem runtimeSubstitutionMap_correspondence
    {substitution : FiniteSubstitution}
    (hunique : SubstitutionKeysUnique substitution) :
    RuntimeSubstitutionCorrespondence substitution
      (RuntimeSubstitutionMap substitution) := by
  intro name runtimeFormula
  constructor
  · intro hlookup
    exact runtimeSubstitutionMap_lookup_some_origin
      substitution name runtimeFormula hlookup
  · rintro ⟨replacement, hsemantics, rfl⟩
    exact runtimeSubstitutionMap_lookup_of_semantics hunique hsemantics

/-- Any exact runtime representative and the canonical map have identical
lookups.  This is the appropriate equality notion for `Std.HashMap`: the live
checker and the canonical materializer may use different insertion histories. -/
theorem runtimeLookup_eq_canonical
    {substitution : FiniteSubstitution}
    {runtimeSubstitution : Std.HashMap String RuntimeFormula}
    (hunique : SubstitutionKeysUnique substitution)
    (hcorrespondence :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution)
    (name : String) :
    runtimeSubstitution[name]? =
      (RuntimeSubstitutionMap substitution)[name]? := by
  cases hruntime : runtimeSubstitution[name]? with
  | none =>
      cases hcanonical : (RuntimeSubstitutionMap substitution)[name]? with
      | none => rfl
      | some runtimeFormula =>
          obtain ⟨replacement, hsemantics, hruntimeFormula⟩ :=
            runtimeSubstitutionMap_lookup_some_origin substitution name
              runtimeFormula hcanonical
          have hlive :
              runtimeSubstitution[name]? = some replacement.toRuntime :=
            (hcorrespondence name replacement.toRuntime).2
              ⟨replacement, hsemantics, rfl⟩
          rw [hruntime] at hlive
          contradiction
  | some runtimeFormula =>
      obtain ⟨replacement, hsemantics, hruntimeFormula⟩ :=
        (hcorrespondence name runtimeFormula).1 hruntime
      have hcanonical :
          (RuntimeSubstitutionMap substitution)[name]? =
            some replacement.toRuntime :=
        runtimeSubstitutionMap_lookup_of_semantics hunique hsemantics
      rw [hruntimeFormula, hcanonical]

/-- Formula substitution reads only map lookups, so any exact live
representative behaves identically to the canonical materialization. -/
theorem runtimeFormulaSubst_eq_canonical
    {substitution : FiniteSubstitution}
    {runtimeSubstitution : Std.HashMap String RuntimeFormula}
    (hunique : SubstitutionKeysUnique substitution)
    (hcorrespondence :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution)
    (source : ConstantHeadedFormula) :
    source.toRuntime.subst runtimeSubstitution =
      source.toRuntime.subst (RuntimeSubstitutionMap substitution) := by
  exact Metamath.HashMapLemmas.subst_preserved_by_keys
    (runtimeLookup_eq_canonical hunique hcorrespondence)

/-- Independent formula-substitution semantics is equivalent to exact live
success for every extensionally corresponding runtime map, not only for the
canonical materialization. -/
theorem formulaSubstitutionSemantics_iff_runtime_subst_of_correspondence
    {substitution : FiniteSubstitution}
    {runtimeSubstitution : Std.HashMap String RuntimeFormula}
    (hunique : SubstitutionKeysUnique substitution)
    (hcorrespondence :
      RuntimeSubstitutionCorrespondence substitution runtimeSubstitution)
    (source result : ConstantHeadedFormula) :
    FormulaSubstitutionSemantics substitution source result ↔
      source.toRuntime.subst runtimeSubstitution = .ok result.toRuntime := by
  rw [runtimeFormulaSubst_eq_canonical hunique hcorrespondence]
  exact formulaSubstitutionSemantics_iff_runtime_subst
    hunique source result

/-! ## Boundaries -/

private def correspondenceExample : ConstantHeadedFormula :=
  ⟨"wff", [.var "x"]⟩

/-- Positive boundary: the canonical one-binding map is an exact live
representative. -/
example :
    RuntimeSubstitutionCorrespondence
      [⟨"x", correspondenceExample⟩]
      (RuntimeSubstitutionMap [⟨"x", correspondenceExample⟩]) := by
  apply runtimeSubstitutionMap_correspondence
  simp [SubstitutionKeysUnique]

/-- Negative boundary: an otherwise empty visible substitution cannot conceal
an extra live binding. -/
example :
    ¬RuntimeSubstitutionCorrespondence []
      (({} : Std.HashMap String RuntimeFormula).insert "x"
        correspondenceExample.toRuntime) := by
  intro hcorrespondence
  have hlookup :=
    (hcorrespondence "x" correspondenceExample.toRuntime).1
      (by simp)
  simp [LookupSemantics] at hlookup

/-- Negative boundary: a visible binding cannot be omitted from an otherwise
empty live map. -/
example :
    ¬RuntimeSubstitutionCorrespondence
      [⟨"x", correspondenceExample⟩]
      ({} : Std.HashMap String RuntimeFormula) := by
  intro hcorrespondence
  have hlookup :=
    (hcorrespondence "x" correspondenceExample.toRuntime).2
      ⟨correspondenceExample, by simp [LookupSemantics], rfl⟩
  simp at hlookup

end Mettapedia.Languages.Metamath.InferenceRuntimeSubstitutionRelation
