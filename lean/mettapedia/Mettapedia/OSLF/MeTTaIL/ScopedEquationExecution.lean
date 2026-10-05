import Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

/-!
# Executing declared equations with contextual metavariables

An equation uses the existing rule-local dependency and occurrence declarations.
Each orientation is interpreted by the shared scoped rule matcher and
instantiator. Reversing an equation exchanges its left and right occurrence
sites as well as its patterns; premise sites retain their identity.

This module realizes premise-free declarations in an explicit ambient scope.
It checks the scope of the supplied source and every returned endpoint.
Structural binding admission alone does not validate every literal de Bruijn
index in a schema, so the endpoint checks are part of the execution contract.
Scope is distinct from sorting: this route does not infer a typed assignment or
assert preservation of a language sort.

Both orientations are matched independently. General output occurrence
substitutions need not be invertible by the variable-spine matcher. No general
reversibility or completeness claim is made for those substitutions.

The results enumerate instances of `LanguageDef.equations`, retaining equation,
orientation and match occurrences. They are not directed language rewrites.
The existing generated equation relation does not yet consume this interpreter.
-/

namespace Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching
open Mettapedia.OSLF.MeTTaIL.ScopedRuleExecution

set_option autoImplicit false

/-- The two authored orientations of a bidirectional declaration. -/
inductive Orientation where
  | forward
  | reverse
deriving Repr, DecidableEq

/-- Exchange endpoint sites while preserving all premise addresses. -/
def exchangeSite : RulePatternSite → RulePatternSite
  | .left => .right
  | .right => .left
  | .premise index depth argument => .premise index depth argument

@[simp] theorem exchangeSite_involution (site : RulePatternSite) :
    exchangeSite (exchangeSite site) = site := by
  cases site <;> rfl

/-- Reverse the side of one occurrence without changing its local path or
dependency substitution. -/
def exchangeOccurrence (occurrence : MetavariableOccurrence) :
    MetavariableOccurrence :=
  { occurrence with site := exchangeSite occurrence.site }

@[simp] theorem exchangeOccurrence_involution (occurrence : MetavariableOccurrence) :
    exchangeOccurrence (exchangeOccurrence occurrence) = occurrence := by
  cases occurrence
  simp [exchangeOccurrence]

/-- A reversed declaration has the same dependency telescope and readdresses
every occurrence on the exchanged endpoint. -/
def exchangeBindings (spec : RuleBindingSpec) : RuleBindingSpec :=
  { spec with occurrences := spec.occurrences.map exchangeOccurrence }

@[simp] theorem exchangeBindings_involution (spec : RuleBindingSpec) :
    exchangeBindings (exchangeBindings spec) = spec := by
  cases spec
  simp [exchangeBindings, List.map_map, Function.comp_def]

/-- Reuse the ordinary rule interpreter for one equation orientation. This
adapter does not insert the equation into the language's rewrite list. -/
def orientedRule (equation : Equation) : Orientation → RewriteRule
  | .forward =>
      { name := equation.name, typeContext := equation.typeContext,
        premises := equation.premises, left := equation.left,
        right := equation.right, bindings := equation.bindings }
  | .reverse =>
      { name := equation.name, typeContext := equation.typeContext,
        premises := equation.premises, left := equation.right,
        right := equation.left,
        bindings := equation.bindings.map exchangeBindings }

@[simp] theorem orientedRule_premises (equation : Equation) (orientation : Orientation) :
    (orientedRule equation orientation).premises = equation.premises := by
  cases orientation <;> rfl

@[simp] theorem orientedRule_typeContext (equation : Equation) (orientation : Orientation) :
    (orientedRule equation orientation).typeContext = equation.typeContext := by
  cases orientation <;> rfl

/-- Readdressing a reversed occurrence keeps the exact declared pattern site. -/
theorem occurrenceDeclared_exchanged (equation : Equation)
    (occurrence : MetavariableOccurrence) :
    occurrenceDeclared (orientedRule equation .reverse) (exchangeOccurrence occurrence) =
      occurrenceDeclared (orientedRule equation .forward) occurrence := by
  cases occurrence with
  | mk name site path arguments => cases site <;> rfl

/-- Reversing a side preserves its local binder depth, including a premise
address that does not change sides. -/
theorem occurrenceDepthAtSite?_exchanged (equation : Equation)
    (site : RulePatternSite) (path : List Nat) :
    occurrenceDepthAtSite? (orientedRule equation .reverse) (exchangeSite site) path =
      occurrenceDepthAtSite? (orientedRule equation .forward) site path := by
  cases site <;> rfl

/-- Run one premise-free equation orientation in the exact ambient context.
The shared matcher reads the oriented occurrence declaration, and the shared
instantiator emits the exact opposite side. -/
def applyEquationAt (language : LanguageDef) (ambient : Nat)
    (equation : Equation) (orientation : Orientation) (source : Pattern) : List Pattern :=
  if equation.premises.isEmpty then
    if source.isWellScopedAt ambient then
      (applyRuleAt RelationEnv.empty language ambient
        (orientedRule equation orientation) source).filter
          (fun target => target.isWellScopedAt ambient)
    else []
  else []

/-- The endpoint checks and the reused rule firing are all necessary and
sufficient for a returned equation instance. -/
theorem mem_applyEquationAt_rule_iff (language : LanguageDef) (ambient : Nat)
    (equation : Equation) (orientation : Orientation) (source target : Pattern) :
    target ∈ applyEquationAt language ambient equation orientation source ↔
      equation.premises = [] ∧ source.isWellScopedAt ambient = true ∧
        target ∈ applyRuleAt RelationEnv.empty language ambient
          (orientedRule equation orientation) source ∧
        target.isWellScopedAt ambient = true := by
  by_cases premisesEmpty : equation.premises.isEmpty = true
  · have premiseNil : equation.premises = [] := List.isEmpty_iff.mp premisesEmpty
    by_cases sourceScoped : source.isWellScopedAt ambient = true
    · simp [applyEquationAt, premiseNil, sourceScoped]
    · simp [applyEquationAt, premiseNil, sourceScoped]
  · have premiseNotNil : equation.premises ≠ [] := fun nil =>
      premisesEmpty (List.isEmpty_iff.mpr nil)
    simp [applyEquationAt, premisesEmpty, premiseNotNil]

/-- A premise-free equation execution retains the exact scoped assignment
recovered by matching; no root projection discards its dependencies. -/
theorem mem_applyEquationAt_iff (language : LanguageDef) (ambient : Nat)
    (equation : Equation) (orientation : Orientation) (source target : Pattern) :
    target ∈ applyEquationAt language ambient equation orientation source ↔
      equation.premises = [] ∧ source.isWellScopedAt ambient = true ∧
        target.isWellScopedAt ambient = true ∧
        ∃ spec captured,
          (orientedRule equation orientation).bindings = some spec ∧
          admittedFor (orientedRule equation orientation) spec = true ∧
          captured ∈ matchRuleAt (orientedRule equation orientation) spec ambient source ∧
          reduct? (orientedRule equation orientation) spec ambient captured = some target := by
  rw [mem_applyEquationAt_rule_iff, mem_applyRuleAt_iff]
  constructor
  · rintro ⟨premisesEmpty, sourceScoped,
      ⟨spec, captured, assignment, declared, admitted, matched, completed, applied⟩,
      targetScoped⟩
    have same : assignment = captured := by
      simpa [completeAssignments, premisesEmpty] using completed
    subst assignment
    exact ⟨premisesEmpty, sourceScoped, targetScoped,
      spec, captured, declared, admitted, matched, applied⟩
  · rintro ⟨premisesEmpty, sourceScoped, targetScoped,
      spec, captured, declared, admitted, matched, applied⟩
    refine ⟨premisesEmpty, sourceScoped, ?_, targetScoped⟩
    refine ⟨spec, captured, captured, declared, admitted, matched, ?_, applied⟩
    simp [completeAssignments, premisesEmpty]

/-- Every returned instance starts and ends in the supplied ambient scope. -/
theorem applyEquationAt_scoped {language : LanguageDef} {ambient : Nat}
    {equation : Equation} {orientation : Orientation} {source target : Pattern}
    (firing : target ∈ applyEquationAt language ambient equation orientation source) :
    source.isWellScopedAt ambient = true ∧ target.isWellScopedAt ambient = true := by
  obtain ⟨_, sourceScoped, _, targetScoped⟩ :=
    (mem_applyEquationAt_rule_iff language ambient equation orientation source target).mp firing
  exact ⟨sourceScoped, targetScoped⟩

/-- Premises remain a declared execution boundary of this interpreter. -/
theorem applyEquationAt_of_nonempty_premises (language : LanguageDef) (ambient : Nat)
    (equation : Equation) (orientation : Orientation) (source : Pattern)
    (nonempty : equation.premises ≠ []) :
    applyEquationAt language ambient equation orientation source = [] := by
  have notEmpty : equation.premises.isEmpty = false := by
    exact Bool.eq_false_iff.mpr (fun empty => nonempty (List.isEmpty_iff.mp empty))
  simp [applyEquationAt, notEmpty]

/-- A declaration without dependency metadata cannot enter the scoped route. -/
theorem applyEquationAt_of_no_bindings (language : LanguageDef) (ambient : Nat)
    (equation : Equation) (orientation : Orientation) (source : Pattern)
    (missing : equation.bindings = none) :
    applyEquationAt language ambient equation orientation source = [] := by
  cases orientation <;>
    simp [applyEquationAt, applyRuleAt, applyRuleWithAt, applyRuleComparedWithAt,
      orientedRule, missing]

/-- Enumerate the actual authored equation list in both orientations, retaining
the list multiplicity of declarations and all scoped matching choices. -/
def equationResultsAt (language : LanguageDef) (ambient : Nat) (source : Pattern) :
    List Pattern :=
  language.equations.flatMap fun equation =>
    applyEquationAt language ambient equation .forward source ++
      applyEquationAt language ambient equation .reverse source

theorem mem_equationResultsAt_iff (language : LanguageDef) (ambient : Nat)
    (source target : Pattern) :
    target ∈ equationResultsAt language ambient source ↔
      ∃ equation ∈ language.equations,
        target ∈ applyEquationAt language ambient equation .forward source ∨
        target ∈ applyEquationAt language ambient equation .reverse source := by
  simp only [equationResultsAt, List.mem_flatMap, List.mem_append]

/-- Language-level equation enumeration has the same scope contract. -/
theorem equationResultsAt_scoped {language : LanguageDef} {ambient : Nat}
    {source target : Pattern}
    (firing : target ∈ equationResultsAt language ambient source) :
    source.isWellScopedAt ambient = true ∧ target.isWellScopedAt ambient = true := by
  obtain ⟨equation, _, forward | reverse⟩ :=
    (mem_equationResultsAt_iff language ambient source target).mp firing
  · exact applyEquationAt_scoped forward
  · exact applyEquationAt_scoped reverse

end Mettapedia.OSLF.MeTTaIL.ScopedEquationExecution
