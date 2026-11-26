-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.CompilerGeneratedNames
Purpose: Classify every variable emitted by the executable compiler as either
  externally supplied or allocated in the compiler's consumed counter range.
Trusted boundary: none
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.CompilerCounter
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.CompilerTypeFreshening
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.Unification
import Mettapedia.Languages.MeTTa.PLeaTTa.Specialize
import Mettapedia.Languages.MeTTa.PLeaTTa.Source.Proofs.Basic

namespace Mettapedia.Languages.MeTTa.PLeaTTa

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom)

/-- A variable visible after compilation is either supplied by the caller or
allocated by the compiler between the original and current counter. -/
def CompilerNameAllowed (external : String → Prop) (origin limit : Nat)
    (name : String) : Prop :=
  external name ∨ ∃ index, origin ≤ index ∧ index < limit ∧
    name = compilerGeneratedName index

/-- Every name in a list satisfies the compiler-origin classification. -/
def CompilerNamesAllowed (external : String → Prop) (origin limit : Nat)
    (names : List String) : Prop :=
  ∀ name, name ∈ names → CompilerNameAllowed external origin limit name

abbrev CompilerAtomNamesAllowed (external : String → Prop)
    (origin limit : Nat) (atom : Atom) : Prop :=
  CompilerNamesAllowed external origin limit atom.vars

abbrev CompilerAtomsNamesAllowed (external : String → Prop)
    (origin limit : Nat) (atoms : List Atom) : Prop :=
  CompilerNamesAllowed external origin limit (atoms.flatMap Atom.vars)

abbrev CompilerGoalsNamesAllowed (external : String → Prop)
    (origin limit : Nat) (goals : List Goal) : Prop :=
  CompilerNamesAllowed external origin limit (specializationGoalsVars goals)

abbrev CompilerGoalNamesAllowed (external : String → Prop)
    (origin limit : Nat) (goal : Goal) : Prop :=
  CompilerNamesAllowed external origin limit (specializationGoalVars goal)

abbrev CompilerBranchesNamesAllowed (external : String → Prop)
    (origin limit : Nat) (branches : List (Atom × List Goal)) : Prop :=
  CompilerNamesAllowed external origin limit
    (specializationBranchVars branches)

/-- Type declarations are the only atom-valued compiler-environment input.
Their variables must already be visible when compilation begins. -/
def CompilerEnvNamesAllowed (external : String → Prop)
    (origin limit : Nat) (env : CEnv) : Prop :=
  ∀ head chain, chain ∈ env.typeChains head →
    CompilerAtomsNamesAllowed external origin limit chain

theorem CompilerNameAllowed.external {external : String → Prop}
    {origin limit : Nat} {name : String} (visible : external name) :
    CompilerNameAllowed external origin limit name :=
  Or.inl visible

theorem CompilerNameAllowed.generated {external : String → Prop}
    {origin limit index : Nat} (lower : origin ≤ index)
    (upper : index < limit) :
    CompilerNameAllowed external origin limit (compilerGeneratedName index) :=
  Or.inr ⟨index, lower, upper, rfl⟩

theorem CompilerNameAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {name : String} :
    CompilerNameAllowed external origin before name →
      CompilerNameAllowed external origin after name := by
  rintro (visible | ⟨index, lower, upper, rfl⟩)
  · exact .external visible
  · exact .generated lower (lt_of_lt_of_le upper le)

/-- Treat every name already visible at a recursive call boundary as an
external input to that call. This is only a proof view; no name is changed. -/
theorem CompilerNameAllowed.nest {external : String → Prop}
    {origin start limit : Nat} {name : String}
    (allowed : CompilerNameAllowed external origin start name) :
    CompilerNameAllowed (CompilerNameAllowed external origin start)
      start limit name :=
  .external allowed

/-- Flatten a recursive-call classification back into the enclosing compiler
interval. -/
theorem CompilerNameAllowed.flatten {external : String → Prop}
    {origin start limit : Nat} {name : String}
    (originStart : origin ≤ start) (startLimit : start ≤ limit)
    (allowed : CompilerNameAllowed
      (CompilerNameAllowed external origin start) start limit name) :
    CompilerNameAllowed external origin limit name := by
  rcases allowed with prior | ⟨index, startIndex, indexLimit, rfl⟩
  · exact prior.mono startLimit
  · exact .generated (Nat.le_trans originStart startIndex) indexLimit

theorem CompilerNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {names : List String}
    (allowed : CompilerNamesAllowed external origin before names) :
    CompilerNamesAllowed external origin after names := by
  intro name member
  exact (allowed name member).mono le

theorem CompilerNamesAllowed.nest {external : String → Prop}
    {origin start limit : Nat} {names : List String}
    (allowed : CompilerNamesAllowed external origin start names) :
    CompilerNamesAllowed (CompilerNameAllowed external origin start)
      start limit names := by
  intro name member
  exact (allowed name member).nest

theorem CompilerNamesAllowed.flatten {external : String → Prop}
    {origin start limit : Nat} {names : List String}
    (originStart : origin ≤ start) (startLimit : start ≤ limit)
    (allowed : CompilerNamesAllowed
      (CompilerNameAllowed external origin start) start limit names) :
    CompilerNamesAllowed external origin limit names := by
  intro name member
  exact (allowed name member).flatten originStart startLimit

@[simp] theorem compilerNamesAllowed_nil (external : String → Prop)
    (origin limit : Nat) :
    CompilerNamesAllowed external origin limit [] := by
  simp [CompilerNamesAllowed]

@[simp] theorem compilerNamesAllowed_append_iff (external : String → Prop)
    (origin limit : Nat) (left right : List String) :
    CompilerNamesAllowed external origin limit (left ++ right) ↔
      CompilerNamesAllowed external origin limit left ∧
      CompilerNamesAllowed external origin limit right := by
  simp [CompilerNamesAllowed, or_imp, forall_and]

theorem CompilerNamesAllowed.of_subset {external : String → Prop}
    {origin limit : Nat} {larger smaller : List String}
    (allowed : CompilerNamesAllowed external origin limit larger)
    (subset : ∀ name, name ∈ smaller → name ∈ larger) :
    CompilerNamesAllowed external origin limit smaller := by
  intro name member
  exact allowed name (subset name member)

theorem CompilerAtomNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {atom : Atom}
    (allowed : CompilerAtomNamesAllowed external origin before atom) :
    CompilerAtomNamesAllowed external origin after atom :=
  CompilerNamesAllowed.mono le allowed

theorem CompilerAtomsNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {atoms : List Atom}
    (allowed : CompilerAtomsNamesAllowed external origin before atoms) :
    CompilerAtomsNamesAllowed external origin after atoms :=
  CompilerNamesAllowed.mono le allowed

theorem CompilerAtomsNamesAllowed.of_sublist {external : String → Prop}
    {origin limit : Nat} {smaller larger : List Atom}
    (allowed : CompilerAtomsNamesAllowed external origin limit larger)
    (sublist : smaller.Sublist larger) :
    CompilerAtomsNamesAllowed external origin limit smaller := by
  intro name member
  simp only [List.mem_flatMap] at member
  rcases member with ⟨atom, atomMem, nameMem⟩
  apply allowed name
  simp only [List.mem_flatMap]
  exact ⟨atom, sublist.mem atomMem, nameMem⟩

theorem CompilerAtomsNamesAllowed.atom_mem {external : String → Prop}
    {origin limit : Nat} {atoms : List Atom} {atom : Atom}
    (allowed : CompilerAtomsNamesAllowed external origin limit atoms)
    (member : atom ∈ atoms) :
    CompilerAtomNamesAllowed external origin limit atom := by
  intro name nameMem
  apply allowed name
  simp only [List.mem_flatMap]
  exact ⟨atom, member, nameMem⟩

private theorem list_getLast_bang_mem_of_isEmpty_false {α : Type}
    [Inhabited α] {items : List α} (notEmpty : items.isEmpty = false) :
    items.getLast! ∈ items := by
  cases items with
  | nil => simp at notEmpty
  | cons head tail =>
      simpa only [List.getLast!] using
        (List.getLast_mem (l := head :: tail) (by simp))

private theorem list_head_bang_mem_of_isEmpty_false {α : Type}
    [Inhabited α] {items : List α} (notEmpty : items.isEmpty = false) :
    items.head! ∈ items := by
  cases items with
  | nil => simp at notEmpty
  | cons head tail => simp [List.head!]

private theorem compileListFuel_terms_isEmpty_false
    {fuel : Nat} {env : CEnv} {counter : Nat} {source : Atom}
    {sources terms : List Atom} {goals : List Goal} {next : Nat}
    (compiled : compileListFuel fuel env counter (source :: sources) =
      .ok (terms, goals, next)) : terms.isEmpty = false := by
  cases fuel with
  | zero => simp [compileListFuel] at compiled
  | succ childFuel =>
      rw [compileListFuel_cons_eq] at compiled
      simp only [Bind.bind, Except.bind] at compiled
      split at compiled
      · contradiction
      · split at compiled
        · contradiction
        · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          rfl

theorem CompilerGoalsNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {goals : List Goal}
    (allowed : CompilerGoalsNamesAllowed external origin before goals) :
    CompilerGoalsNamesAllowed external origin after goals :=
  CompilerNamesAllowed.mono le allowed

theorem CompilerGoalNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {goal : Goal}
    (allowed : CompilerGoalNamesAllowed external origin before goal) :
    CompilerGoalNamesAllowed external origin after goal :=
  CompilerNamesAllowed.mono le allowed

theorem CompilerBranchesNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after)
    {branches : List (Atom × List Goal)}
    (allowed : CompilerBranchesNamesAllowed external origin before branches) :
    CompilerBranchesNamesAllowed external origin after branches :=
  CompilerNamesAllowed.mono le allowed

theorem CompilerEnvNamesAllowed.mono {external : String → Prop}
    {origin before after : Nat} (le : before ≤ after) {env : CEnv}
    (allowed : CompilerEnvNamesAllowed external origin before env) :
    CompilerEnvNamesAllowed external origin after env := by
  intro head chain member
  exact (allowed head chain member).mono le

theorem CompilerEnvNamesAllowed.nest {external : String → Prop}
    {origin start limit : Nat} {env : CEnv}
    (allowed : CompilerEnvNamesAllowed external origin start env) :
    CompilerEnvNamesAllowed (CompilerNameAllowed external origin start)
      start limit env := by
  intro head chain member
  exact (allowed head chain member).nest

theorem compilerAtomNamesAllowed_of_external
    (external : String → Prop) (origin limit : Nat) (atom : Atom)
    (visible : ∀ name, name ∈ atom.vars → external name) :
    CompilerAtomNamesAllowed external origin limit atom := by
  intro name member
  exact .external (visible name member)

theorem compilerAtomsNamesAllowed_of_external
    (external : String → Prop) (origin limit : Nat) (atoms : List Atom)
    (visible : ∀ name, name ∈ atoms.flatMap Atom.vars → external name) :
    CompilerAtomsNamesAllowed external origin limit atoms := by
  intro name member
  exact .external (visible name member)

theorem compilerFreshAtom_namesAllowed (external : String → Prop)
    (origin counter : Nat) (lower : origin ≤ counter) :
    CompilerAtomNamesAllowed external origin (counter + 1)
      (fresh counter).1 := by
  intro name member
  simp only [fresh, Atom.vars, List.mem_singleton] at member
  subst name
  exact .generated lower (by omega)

theorem canonBool_namesAllowed {external : String → Prop}
    {origin limit : Nat} {atom : Atom}
    (allowed : CompilerAtomNamesAllowed external origin limit atom) :
    CompilerAtomNamesAllowed external origin limit (canonBool atom) := by
  intro name member
  apply allowed name
  cases atom with
  | sym symbol =>
      by_cases htrue : symbol = "true" <;>
        by_cases hfalse : symbol = "false" <;>
        simp_all [canonBool, Atom.vars]
  | var source => simpa [canonBool] using member
  | gnd ground =>
      cases ground with
      | bool value => cases value <;> simp [canonBool, Atom.vars] at member
      | int value | float value | str value | error value | external value _ =>
          simpa [canonBool] using member
      | unit => simpa [canonBool] using member
  | expr atoms => simpa [canonBool] using member

theorem compilerChainOf_vars_subset (atoms : List Atom) (name : String)
    (member : name ∈ (chainOf atoms).vars) :
    name ∈ atoms.flatMap Atom.vars := by
  induction atoms with
  | nil => simp [chainOf, nilA, Atom.vars] at member
  | cons atom rest ih =>
      simp only [chainOf, List.foldr_cons, consC, Atom.vars,
        List.mem_flatten, List.mem_map] at member
      rcases member with ⟨nameList, childWitness, nameMem⟩
      rcases childWitness with ⟨child, childMem, rfl⟩
      simp only [List.mem_cons] at childMem
      rcases childMem with hclosed | hatom | htail
      · subst child
        simp [Atom.vars] at nameMem
      · subst child
        simp only [List.flatMap_cons, List.mem_append]
        exact Or.inl nameMem
      · rcases htail with htail | hfalse
        · subst child
          simp only [List.flatMap_cons, List.mem_append]
          exact Or.inr (ih nameMem)
        · simp at hfalse

theorem chainOf_namesAllowed {external : String → Prop}
    {origin limit : Nat} {atoms : List Atom}
    (allowed : CompilerAtomsNamesAllowed external origin limit atoms) :
    CompilerAtomNamesAllowed external origin limit (chainOf atoms) := by
  intro name member
  exact allowed name (compilerChainOf_vars_subset atoms name member)

theorem chainify_namesAllowed {external : String → Prop}
    {origin limit : Nat} : ∀ {atom : Atom},
    CompilerAtomNamesAllowed external origin limit atom →
      CompilerAtomNamesAllowed external origin limit (chainify atom) := by
  intro atom allowed
  induction atom with
  | sym symbol => simpa [chainify] using canonBool_namesAllowed allowed
  | var name => simpa [chainify] using canonBool_namesAllowed allowed
  | gnd ground => simpa [chainify] using canonBool_namesAllowed allowed
  | expr atoms ih =>
      simp only [chainify]
      apply chainOf_namesAllowed
      intro name member
      simp only [List.mem_flatMap, List.mem_map] at member
      rcases member with ⟨compiled, ⟨source, sourceMem, rfl⟩, nameMem⟩
      apply ih source.val source.property
      · intro candidate candidateMem
        apply allowed candidate
        simp only [Atom.vars, List.mem_flatten, List.mem_map]
        exact ⟨source.val.vars,
          ⟨source.val, source.property, rfl⟩, candidateMem⟩
      · exact nameMem

@[simp] theorem compilerAtomNamesAllowed_sym (external : String → Prop)
    (origin limit : Nat) (name : String) :
    CompilerAtomNamesAllowed external origin limit (Atom.sym name) := by
  simp [CompilerNamesAllowed, Atom.vars]

@[simp] theorem compilerAtomNamesAllowed_gnd (external : String → Prop)
    (origin limit : Nat) (ground : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Ground) :
    CompilerAtomNamesAllowed external origin limit (Atom.gnd ground) := by
  simp [CompilerNamesAllowed, Atom.vars]

@[simp] theorem compilerAtomNamesAllowed_var_iff (external : String → Prop)
    (origin limit : Nat) (name : String) :
    CompilerAtomNamesAllowed external origin limit (Atom.var name) ↔
      CompilerNameAllowed external origin limit name := by
  simp [CompilerNamesAllowed, Atom.vars]

@[simp] theorem compilerAtomNamesAllowed_expr_iff (external : String → Prop)
    (origin limit : Nat) (atoms : List Atom) :
    CompilerAtomNamesAllowed external origin limit (Atom.expr atoms) ↔
      CompilerAtomsNamesAllowed external origin limit atoms := by
  simp [CompilerNamesAllowed, Atom.vars, List.mem_flatMap,
    List.mem_flatten, List.mem_map]

@[simp] theorem compilerAtomsNamesAllowed_nil (external : String → Prop)
    (origin limit : Nat) :
    CompilerAtomsNamesAllowed external origin limit [] := by
  simp [CompilerNamesAllowed]

@[simp] theorem compilerAtomsNamesAllowed_cons_iff
    (external : String → Prop) (origin limit : Nat) (atom : Atom)
    (atoms : List Atom) :
    CompilerAtomsNamesAllowed external origin limit (atom :: atoms) ↔
      CompilerAtomNamesAllowed external origin limit atom ∧
      CompilerAtomsNamesAllowed external origin limit atoms := by
  simp [CompilerNamesAllowed, or_imp, forall_and]

theorem compilerAtomExprCons_namesAllowed {external : String → Prop}
    {origin limit : Nat} {head : Atom} {tail : List Atom}
    (allowed : CompilerAtomNamesAllowed external origin limit
      (Atom.expr (head :: tail))) :
    CompilerAtomNamesAllowed external origin limit head ∧
      CompilerAtomsNamesAllowed external origin limit tail := by
  exact (compilerAtomsNamesAllowed_cons_iff external origin limit head tail).mp
    ((compilerAtomNamesAllowed_expr_iff external origin limit
      (head :: tail)).mp allowed)

theorem compilerAtomExprPair_namesAllowed {external : String → Prop}
    {origin limit : Nat} {first second : Atom}
    (allowed : CompilerAtomNamesAllowed external origin limit
      (Atom.expr [first, second])) :
    CompilerAtomNamesAllowed external origin limit first ∧
      CompilerAtomNamesAllowed external origin limit second := by
  have outer := compilerAtomExprCons_namesAllowed allowed
  have inner := (compilerAtomsNamesAllowed_cons_iff external origin limit
    second []).mp outer.2
  exact ⟨outer.1, inner.1⟩

theorem consC_namesAllowed {external : String → Prop}
    {origin limit : Nat} {head tail : Atom}
    (headAllowed : CompilerAtomNamesAllowed external origin limit head)
    (tailAllowed : CompilerAtomNamesAllowed external origin limit tail) :
    CompilerAtomNamesAllowed external origin limit (consC head tail) := by
  apply (compilerAtomNamesAllowed_expr_iff external origin limit
    [Atom.sym "#c", head, tail]).2
  simp only [compilerAtomsNamesAllowed_cons_iff,
    compilerAtomsNamesAllowed_nil, and_true]
  exact ⟨by simp, headAllowed, tailAllowed⟩

theorem bindingTemplate_namesAllowed {external : String → Prop}
    {origin limit : Nat} {base : Atom} {sources : List Atom}
    (baseAllowed : CompilerAtomNamesAllowed external origin limit base)
    (sourcesAllowed :
      CompilerAtomsNamesAllowed external origin limit sources) :
    CompilerAtomNamesAllowed external origin limit
      (bindingTemplate base sources) := by
  unfold bindingTemplate
  apply chainOf_namesAllowed
  apply (compilerAtomsNamesAllowed_cons_iff external origin limit base
    ((sources.flatMap Atom.vars).eraseDups.map Atom.var)).2
  constructor
  · exact baseAllowed
  · intro name member
    simp only [List.mem_flatMap, List.mem_map] at member
    rcases member with ⟨generatedAtom, ⟨sourceName, sourceMem, rfl⟩, nameMem⟩
    simp only [Atom.vars, List.mem_singleton] at nameMem
    subst name
    apply sourcesAllowed sourceName
    simpa using sourceMem

theorem partialValue_namesAllowed {external : String → Prop}
    {origin limit : Nat} {head : String} {arguments : List Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments) :
    CompilerAtomNamesAllowed external origin limit
      (partialValue head arguments) := by
  unfold partialValue partialC prologCompoundC
  apply (compilerAtomNamesAllowed_expr_iff external origin limit
    [prologCompoundTagA, Atom.sym "partial",
      chainOf [Atom.sym head, chainOf arguments]]).2
  simp only [compilerAtomsNamesAllowed_cons_iff,
    compilerAtomsNamesAllowed_nil, and_true]
  refine ⟨by simp [prologCompoundTagA], by simp, ?_⟩
  apply chainOf_namesAllowed
  simp only [compilerAtomsNamesAllowed_cons_iff,
    compilerAtomsNamesAllowed_nil, and_true]
  exact ⟨by simp, chainOf_namesAllowed argumentsAllowed⟩

theorem spacePat_namesAllowed {external : String → Prop}
    {origin limit : Nat} {space pattern : Atom}
    (spaceAllowed : CompilerAtomNamesAllowed external origin limit space)
    (patternAllowed : CompilerAtomNamesAllowed external origin limit pattern) :
    CompilerAtomNamesAllowed external origin limit
      (spacePat space pattern) := by
  unfold spacePat
  simp only [compilerAtomNamesAllowed_expr_iff,
    compilerAtomsNamesAllowed_cons_iff, compilerAtomsNamesAllowed_nil,
    and_true]
  exact ⟨by simp, spaceAllowed, patternAllowed⟩

theorem desugarLetStar_namesAllowed {external : String → Prop}
    {origin limit : Nat} : ∀ {bindings : List Atom} {body nested : Atom},
    CompilerAtomsNamesAllowed external origin limit bindings →
    CompilerAtomNamesAllowed external origin limit body →
    desugarLetStar? bindings body = some nested →
      CompilerAtomNamesAllowed external origin limit nested := by
  intro bindings
  induction bindings with
  | nil =>
      intro body nested _ _ desugared
      simp [desugarLetStar?] at desugared
  | cons binding rest ih =>
      intro body nested bindingsAllowed bodyAllowed desugared
      have bindingAndRest :=
        (compilerAtomsNamesAllowed_cons_iff external origin limit binding
          rest).mp bindingsAllowed
      cases binding with
      | sym symbol | var name | gnd ground =>
          simp [desugarLetStar?] at desugared
      | expr items =>
          cases items with
          | nil => simp [desugarLetStar?] at desugared
          | cons pattern tail =>
              cases tail with
              | nil => simp [desugarLetStar?] at desugared
              | cons value extra =>
                  cases extra with
                  | cons third more => simp [desugarLetStar?] at desugared
                  | nil =>
                      have pairAllowed := compilerAtomExprPair_namesAllowed
                        bindingAndRest.1
                      cases rest with
                      | nil =>
                          simp only [desugarLetStar?, Option.some.injEq] at desugared
                          subst nested
                          simpa [CompilerNamesAllowed, Atom.vars] using
                            And.intro pairAllowed.1
                              (And.intro pairAllowed.2 bodyAllowed)
                      | cons nextBinding more =>
                          simp only [desugarLetStar?] at desugared
                          cases recursiveEq : desugarLetStar?
                              (nextBinding :: more) body with
                          | none =>
                              simp only [recursiveEq, Option.map_none] at desugared
                              contradiction
                          | some recursive =>
                              simp only [recursiveEq, Option.map_some,
                                Option.some.injEq] at desugared
                              subst nested
                              have recursiveAllowed := ih bindingAndRest.2
                                bodyAllowed recursiveEq
                              simpa [CompilerNamesAllowed, Atom.vars] using
                                And.intro pairAllowed.1
                                  (And.intro pairAllowed.2 recursiveAllowed)

@[simp] theorem compilerAtomsNamesAllowed_append_iff
    (external : String → Prop) (origin limit : Nat) (left right : List Atom) :
    CompilerAtomsNamesAllowed external origin limit (left ++ right) ↔
      CompilerAtomsNamesAllowed external origin limit left ∧
      CompilerAtomsNamesAllowed external origin limit right := by
  simp [CompilerNamesAllowed, or_imp, forall_and]

theorem specializationGoalsVars_append_for_compiler
    (left right : List Goal) :
    specializationGoalsVars (left ++ right) =
      specializationGoalsVars left ++ specializationGoalsVars right := by
  induction left with
  | nil => rfl
  | cons goal rest ih =>
      simp only [List.cons_append, specializationGoalsVars, ih,
        List.append_assoc]

@[simp] theorem compilerGoalsNamesAllowed_nil (external : String → Prop)
    (origin limit : Nat) :
    CompilerGoalsNamesAllowed external origin limit [] := by
  simp [CompilerNamesAllowed, specializationGoalsVars]

@[simp] theorem compilerGoalsNamesAllowed_cons_iff
    (external : String → Prop) (origin limit : Nat) (goal : Goal)
    (goals : List Goal) :
    CompilerGoalsNamesAllowed external origin limit (goal :: goals) ↔
      CompilerGoalNamesAllowed external origin limit goal ∧
      CompilerGoalsNamesAllowed external origin limit goals := by
  simp [CompilerNamesAllowed, specializationGoalsVars, or_imp, forall_and]

@[simp] theorem compilerGoalsNamesAllowed_append_iff
    (external : String → Prop) (origin limit : Nat)
    (left right : List Goal) :
    CompilerGoalsNamesAllowed external origin limit (left ++ right) ↔
      CompilerGoalsNamesAllowed external origin limit left ∧
      CompilerGoalsNamesAllowed external origin limit right := by
  change CompilerNamesAllowed external origin limit
      (specializationGoalsVars (left ++ right)) ↔
    CompilerNamesAllowed external origin limit
        (specializationGoalsVars left) ∧
      CompilerNamesAllowed external origin limit
        (specializationGoalsVars right)
  rw [specializationGoalsVars_append_for_compiler]
  exact compilerNamesAllowed_append_iff external origin limit _ _

@[simp] theorem compilerBranchesNamesAllowed_nil (external : String → Prop)
    (origin limit : Nat) :
    CompilerBranchesNamesAllowed external origin limit [] := by
  simp [CompilerNamesAllowed, specializationBranchVars]

@[simp] theorem compilerBranchesNamesAllowed_cons_iff
    (external : String → Prop) (origin limit : Nat) (term : Atom)
    (goals : List Goal) (branches : List (Atom × List Goal)) :
    CompilerBranchesNamesAllowed external origin limit
        ((term, goals) :: branches) ↔
      CompilerAtomNamesAllowed external origin limit term ∧
      CompilerGoalsNamesAllowed external origin limit goals ∧
      CompilerBranchesNamesAllowed external origin limit branches := by
  simp [CompilerNamesAllowed, specializationBranchVars, or_imp, forall_and]

@[simp] theorem compilerBranchesNamesAllowed_append_iff
    (external : String → Prop) (origin limit : Nat)
    (left right : List (Atom × List Goal)) :
    CompilerBranchesNamesAllowed external origin limit (left ++ right) ↔
      CompilerBranchesNamesAllowed external origin limit left ∧
      CompilerBranchesNamesAllowed external origin limit right := by
  induction left with
  | nil => simp
  | cons branch rest ih =>
      rcases branch with ⟨term, goals⟩
      simp only [List.cons_append, compilerBranchesNamesAllowed_cons_iff, ih]
      tauto

/-- The mutually recursive compiler preserves the origin of every variable in
its returned term(s) and every nested goal term. Inputs may already contain
variables allocated earlier in the same compilation interval. -/
structure CompilerGeneratedNamesAt (fuel : Nat) : Prop where
  expr : ∀ external origin env start source term goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomNamesAllowed external origin start source →
    compileExprFuel fuel env start source = .ok (term, goals, next) →
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals
  pattern : ∀ external origin env start source term goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomNamesAllowed external origin start source →
    compilePatternFuel fuel env start source = .ok (term, goals, next) →
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals
  app : ∀ external origin env start head arguments term goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start arguments →
    compileAppFuel fuel env start head arguments = .ok (term, goals, next) →
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals
  appCore : ∀ external origin env start head arguments term goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start arguments →
    compileAppCoreFuel fuel env start head arguments =
        .ok (term, goals, next) →
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals
  typedArgs : ∀ external origin env start sources types terms goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start sources →
    CompilerAtomsNamesAllowed external origin start types →
    compileTypedArgsFuel fuel env start sources types =
        .ok (terms, goals, next) →
      CompilerAtomsNamesAllowed external origin next terms ∧
      CompilerGoalsNamesAllowed external origin next goals
  argsAt : ∀ external origin env start head index sources terms goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start sources →
    compileArgsAtFuel fuel env start head index sources =
        .ok (terms, goals, next) →
      CompilerAtomsNamesAllowed external origin next terms ∧
      CompilerGoalsNamesAllowed external origin next goals
  caseArms : ∀ external origin env scrutinee result start arms goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomNamesAllowed external origin start scrutinee →
    CompilerAtomNamesAllowed external origin start result →
    CompilerAtomsNamesAllowed external origin start arms →
    compileCaseArmsFuel fuel env scrutinee result start arms =
        .ok (goals, next) →
      CompilerGoalsNamesAllowed external origin next goals
  patternList : ∀ external origin env start sources terms goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start sources →
    compilePatternListFuel fuel env start sources =
        .ok (terms, goals, next) →
      CompilerAtomsNamesAllowed external origin next terms ∧
      CompilerGoalsNamesAllowed external origin next goals
  list : ∀ external origin env start sources terms goals next,
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start sources →
    compileListFuel fuel env start sources = .ok (terms, goals, next) →
      CompilerAtomsNamesAllowed external origin next terms ∧
      CompilerGoalsNamesAllowed external origin next goals

theorem CompilerGeneratedNamesAt.of_succ_eq {fuel recursiveFuel : Nat}
    (invariant : CompilerGeneratedNamesAt fuel)
    (same : fuel + 1 = recursiveFuel + 1) :
    CompilerGeneratedNamesAt recursiveFuel := by
  have : fuel = recursiveFuel := by omega
  simpa [this] using invariant

theorem compilerGeneratedNamesAt_zero : CompilerGeneratedNamesAt 0 := by
  constructor <;> intros <;>
    simp only [compileExprFuel.eq_1, compilePatternFuel_zero_eq,
      compileAppFuel.eq_1, compileAppCoreFuel.eq_1,
      compileTypedArgsFuel.eq_1, compileArgsAtFuel_zero_eq,
      compileCaseArmsFuel_zero_eq, compilePatternListFuel.eq_1,
      compileListFuel.eq_1] at * <;> contradiction

theorem compileListFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start sources terms goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start sources →
      compileListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start sources terms goals next originStart
    envAllowed sourcesAllowed compiled
  cases sources with
  | nil =>
      rw [compileListFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      simp
  | cons source sources =>
      have sourceAndRest :=
        (compilerAtomsNamesAllowed_cons_iff external origin start source
          sources).mp sourcesAllowed
      rw [compileListFuel_cons_eq] at compiled
      simp only [Bind.bind, Except.bind] at compiled
      split at compiled
      · contradiction
      · rename_i firstResult firstEq
        have firstCounter := (compilerCounterAt fuel).expr _ _ _ _ _ _ firstEq
        have firstNames := ih.expr external origin env start source
          firstResult.1 firstResult.2.1 firstResult.2.2 originStart envAllowed
          sourceAndRest.1 firstEq
        split at compiled
        · contradiction
        · rename_i restResult restEq
          have restCounter := (compilerCounterAt fuel).list _ _ _ _ _ _ restEq
          have restNames := ih.list external origin env firstResult.2.2 sources
            restResult.1 restResult.2.1 restResult.2.2
            (Nat.le_trans originStart firstCounter)
            (envAllowed.mono firstCounter)
            (sourceAndRest.2.mono firstCounter) restEq
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          constructor
          · apply (compilerAtomsNamesAllowed_cons_iff external origin
              restResult.2.2 firstResult.1 restResult.1).2
            exact ⟨firstNames.1.mono restCounter, restNames.1⟩
          · apply (compilerGoalsNamesAllowed_append_iff external origin
              restResult.2.2 firstResult.2.1 restResult.2.1).2
            exact ⟨firstNames.2.mono restCounter, restNames.2⟩

theorem compilePatternListFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start sources terms goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start sources →
      compilePatternListFuel (fuel + 1) env start sources =
          .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start sources terms goals next originStart
    envAllowed sourcesAllowed compiled
  cases sources with
  | nil =>
      rw [compilePatternListFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      simp
  | cons source sources =>
      have sourceAndRest :=
        (compilerAtomsNamesAllowed_cons_iff external origin start source
          sources).mp sourcesAllowed
      rw [compilePatternListFuel_cons_eq] at compiled
      simp only [Bind.bind, Except.bind] at compiled
      split at compiled
      · contradiction
      · rename_i firstResult firstEq
        have firstCounter :=
          (compilerCounterAt fuel).pattern _ _ _ _ _ _ firstEq
        have firstNames := ih.pattern external origin env start source
          firstResult.1 firstResult.2.1 firstResult.2.2 originStart envAllowed
          sourceAndRest.1 firstEq
        split at compiled
        · contradiction
        · rename_i restResult restEq
          have restCounter :=
            (compilerCounterAt fuel).patternList _ _ _ _ _ _ restEq
          have restNames := ih.patternList external origin env
            firstResult.2.2 sources restResult.1 restResult.2.1
            restResult.2.2 (Nat.le_trans originStart firstCounter)
            (envAllowed.mono firstCounter)
            (sourceAndRest.2.mono firstCounter) restEq
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          constructor
          · apply (compilerAtomsNamesAllowed_cons_iff external origin
              restResult.2.2 firstResult.1 restResult.1).2
            exact ⟨firstNames.1.mono restCounter, restNames.1⟩
          · apply (compilerGoalsNamesAllowed_append_iff external origin
              restResult.2.2 firstResult.2.1 restResult.2.1).2
            exact ⟨firstNames.2.mono restCounter, restNames.2⟩

theorem compileArgsAtFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start head index sources terms goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start sources →
      compileArgsAtFuel (fuel + 1) env start head index sources =
          .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start head index sources terms goals next
    originStart envAllowed sourcesAllowed compiled
  cases sources with
  | nil =>
      rw [compileArgsAtFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      simp
  | cons source sources =>
      have sourceAndRest :=
        (compilerAtomsNamesAllowed_cons_iff external origin start source
          sources).mp sourcesAllowed
      cases staged : env.atomTyped head index with
      | true =>
          rw [compileArgsAtFuel_staged_eq fuel env start head index source
            sources staged] at compiled
          simp only [Bind.bind, Except.bind] at compiled
          split at compiled
          · contradiction
          · rename_i restResult restEq
            have restCounter :=
              (compilerCounterAt fuel).argsAt _ _ _ _ _ _ _ _ restEq
            have restNames := ih.argsAt external origin env start head
              (index + 1) sources restResult.1 restResult.2.1
              restResult.2.2 originStart envAllowed sourceAndRest.2 restEq
            rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
            constructor
            · apply (compilerAtomsNamesAllowed_cons_iff external origin
                restResult.2.2 (chainify source) restResult.1).2
              exact ⟨(chainify_namesAllowed sourceAndRest.1).mono restCounter,
                restNames.1⟩
            · exact restNames.2
      | false =>
          rw [compileArgsAtFuel_evaluated_eq fuel env start head index source
            sources staged] at compiled
          simp only [Bind.bind, Except.bind] at compiled
          split at compiled
          · contradiction
          · rename_i firstResult firstEq
            have firstCounter :=
              (compilerCounterAt fuel).expr _ _ _ _ _ _ firstEq
            have firstNames := ih.expr external origin env start source
              firstResult.1 firstResult.2.1 firstResult.2.2 originStart
              envAllowed sourceAndRest.1 firstEq
            split at compiled
            · contradiction
            · rename_i restResult restEq
              have restCounter :=
                (compilerCounterAt fuel).argsAt _ _ _ _ _ _ _ _ restEq
              have restNames := ih.argsAt external origin env firstResult.2.2
                head (index + 1) sources restResult.1 restResult.2.1
                restResult.2.2 (Nat.le_trans originStart firstCounter)
                (envAllowed.mono firstCounter)
                (sourceAndRest.2.mono firstCounter) restEq
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              constructor
              · apply (compilerAtomsNamesAllowed_cons_iff external origin
                  restResult.2.2 firstResult.1 restResult.1).2
                exact ⟨firstNames.1.mono restCounter, restNames.1⟩
              · apply (compilerGoalsNamesAllowed_append_iff external origin
                  restResult.2.2 firstResult.2.1 restResult.2.1).2
                exact ⟨firstNames.2.mono restCounter, restNames.2⟩

theorem compilerGoalNamesAllowed_bin {external : String → Prop}
    {origin limit : Nat} {arguments : List Atom} {result : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result)
    (operation : String) :
    CompilerGoalNamesAllowed external origin limit
      (.bin operation arguments result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    (arguments.flatMap Atom.vars) result.vars).2
  exact ⟨argumentsAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_call {external : String → Prop}
    {origin limit : Nat} {arguments : List Atom} {result : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result)
    (operation : String) :
    CompilerGoalNamesAllowed external origin limit
      (.call operation arguments result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    (arguments.flatMap Atom.vars) result.vars).2
  exact ⟨argumentsAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_wact {external : String → Prop}
    {origin limit : Nat} {arguments : List Atom} {result : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result)
    (operation : String) :
    CompilerGoalNamesAllowed external origin limit
      (.wact operation arguments result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    (arguments.flatMap Atom.vars) result.vars).2
  exact ⟨argumentsAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_callDyn {external : String → Prop}
    {origin limit : Nat} {head : Atom} {arguments : List Atom} {result : Atom}
    (headAllowed : CompilerAtomNamesAllowed external origin limit head)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.callDyn head arguments result) := by
  change CompilerNamesAllowed external origin limit
    (head.vars ++ arguments.flatMap Atom.vars ++ result.vars)
  simp only [compilerNamesAllowed_append_iff]
  exact ⟨⟨headAllowed, argumentsAllowed⟩, resultAllowed⟩

theorem compilerGoalNamesAllowed_evalg {external : String → Prop}
    {origin limit : Nat} {value result : Atom}
    (valueAllowed : CompilerAtomNamesAllowed external origin limit value)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit (.evalg value result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    value.vars result.vars).2
  exact ⟨valueAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_spread {external : String → Prop}
    {origin limit : Nat} {value result : Atom}
    (valueAllowed : CompilerAtomNamesAllowed external origin limit value)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit (.spread value result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    value.vars result.vars).2
  exact ⟨valueAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_eq {external : String → Prop}
    {origin limit : Nat} {left right : Atom}
    (leftAllowed : CompilerAtomNamesAllowed external origin limit left)
    (rightAllowed : CompilerAtomNamesAllowed external origin limit right) :
    CompilerGoalNamesAllowed external origin limit (.eq left right) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    left.vars right.vars).2
  exact ⟨leftAllowed, rightAllowed⟩

theorem compilerGoalNamesAllowed_compileAlias {external : String → Prop}
    {origin limit : Nat} {left right : Atom}
    (leftAllowed : CompilerAtomNamesAllowed external origin limit left)
    (rightAllowed : CompilerAtomNamesAllowed external origin limit right) :
    CompilerGoalNamesAllowed external origin limit
      (.compileAlias left right) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    left.vars right.vars).2
  exact ⟨leftAllowed, rightAllowed⟩

/-- The typed streaming-catch delimiter carries the protected template and
caller result as ordinary liveness roots; both therefore obey the same
compiler-name discipline as an equality boundary. -/
theorem compilerGoalNamesAllowed_catchExit {external : String → Prop}
    {origin limit : Nat} {template result : Atom}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (resultAllowed :
      CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.catchExit template result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    template.vars result.vars).2
  exact ⟨templateAllowed, resultAllowed⟩

/-- The internal soft-cut transfer marker keeps its answer template live and
therefore inherits the same compiler-origin discipline as that atom. -/
theorem compilerGoalNamesAllowed_softcutExit {external : String → Prop}
    {origin limit : Nat} {template : Atom}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template) :
    CompilerGoalNamesAllowed external origin limit
      (.softcutExit template) :=
  templateAllowed

theorem compileBranch_namesAllowed {external : String → Prop}
    {origin limit : Nat} {out term : Atom} {goals aliases : List Goal}
    {branch : Atom × List Goal}
    (outAllowed : CompilerAtomNamesAllowed external origin limit out)
    (termAllowed : CompilerAtomNamesAllowed external origin limit term)
    (goalsAllowed : CompilerGoalsNamesAllowed external origin limit goals)
    (compiled : compileBranch out (term, goals) = (aliases, branch)) :
    CompilerGoalsNamesAllowed external origin limit aliases ∧
    CompilerAtomNamesAllowed external origin limit branch.1 ∧
    CompilerGoalsNamesAllowed external origin limit branch.2 := by
  cases term with
  | sym symbol | gnd ground | expr atoms =>
      simp only [compileBranch] at compiled
      rcases Prod.mk.inj compiled with ⟨rfl, rfl⟩
      exact ⟨by simp, termAllowed, goalsAllowed⟩
  | var name =>
      by_cases empty : goals.isEmpty = true
      · simp only [compileBranch, empty, if_true] at compiled
        rcases Prod.mk.inj compiled with ⟨rfl, rfl⟩
        exact ⟨by simp, termAllowed, goalsAllowed⟩
      · have nonempty : goals.isEmpty = false := Bool.eq_false_iff.mpr empty
        simp only [compileBranch, nonempty, Bool.false_eq_true, if_false] at compiled
        rcases Prod.mk.inj compiled with ⟨rfl, rfl⟩
        constructor
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_compileAlias termAllowed outAllowed
        · exact ⟨outAllowed, goalsAllowed⟩

theorem compilerGoalNamesAllowed_softcut {external : String → Prop}
    {origin limit : Nat} {template : Atom} {sub thenGoals elseGoals : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub)
    (thenAllowed : CompilerGoalsNamesAllowed external origin limit thenGoals)
    (elseAllowed : CompilerGoalsNamesAllowed external origin limit elseGoals) :
    CompilerGoalNamesAllowed external origin limit
      (.softcut template sub thenGoals elseGoals) := by
  change CompilerNamesAllowed external origin limit
    (template.vars ++ specializationGoalsVars sub ++
      specializationGoalsVars thenGoals ++ specializationGoalsVars elseGoals)
  simp only [compilerNamesAllowed_append_iff]
  exact ⟨⟨⟨templateAllowed, subAllowed⟩, thenAllowed⟩, elseAllowed⟩

theorem compilerGoalNamesAllowed_nested {external : String → Prop}
    {origin limit : Nat} {template result : Atom} {sub : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerNamesAllowed external origin limit
      (template.vars ++ specializationGoalsVars sub ++ result.vars) := by
  simp only [compilerNamesAllowed_append_iff]
  exact ⟨⟨templateAllowed, subAllowed⟩, resultAllowed⟩

theorem compilerGoalNamesAllowed_catchg {external : String → Prop}
    {origin limit : Nat} {template result : Atom} {sub : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.catchg template sub result) :=
  compilerGoalNamesAllowed_nested templateAllowed subAllowed resultAllowed

theorem compilerGoalNamesAllowed_findall {external : String → Prop}
    {origin limit : Nat} {template result : Atom} {sub : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.findall template sub result) :=
  compilerGoalNamesAllowed_nested templateAllowed subAllowed resultAllowed

theorem compilerGoalNamesAllowed_onceg {external : String → Prop}
    {origin limit : Nat} {template result : Atom} {sub : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.onceg template sub result) :=
  compilerGoalNamesAllowed_nested templateAllowed subAllowed resultAllowed

/-- Ordinary Prolog if-then-else is assembled from the name-safe streaming
soft-cut and once delimiters, so the composition introduces no new names. -/
theorem compilerGoalNamesAllowed_committedIfGoal {external : String → Prop}
    {origin limit : Nat} {template : Atom}
    {condition thenGoals elseGoals : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (conditionAllowed :
      CompilerGoalsNamesAllowed external origin limit condition)
    (thenAllowed :
      CompilerGoalsNamesAllowed external origin limit thenGoals)
    (elseAllowed :
      CompilerGoalsNamesAllowed external origin limit elseGoals) :
    CompilerGoalNamesAllowed external origin limit
      (committedIfGoal template condition thenGoals elseGoals) := by
  unfold committedIfGoal
  apply compilerGoalNamesAllowed_softcut templateAllowed
  · apply (compilerGoalsNamesAllowed_cons_iff external origin limit
      (Goal.onceg template condition template) []).2
    exact ⟨compilerGoalNamesAllowed_onceg templateAllowed conditionAllowed
      templateAllowed, by simp⟩
  · exact thenAllowed
  · exact elseAllowed

/-- The compiler's closed `True = False` goal contains no variable names. -/
theorem compilerGoalNamesAllowed_failureGoal {external : String → Prop}
    {origin limit : Nat} :
    CompilerGoalNamesAllowed external origin limit compilerFailureGoal := by
  unfold compilerFailureGoal
  exact compilerGoalNamesAllowed_eq (by simp [compilerTrueA])
    (by simp [compilerFalseA])

/-- Negation-as-failure adds only its closed marker and canonical failure
goal; every live variable therefore comes from the condition. -/
theorem compilerGoalsNamesAllowed_negatedGoals {external : String → Prop}
    {origin limit : Nat} {condition : List Goal}
    (conditionAllowed :
      CompilerGoalsNamesAllowed external origin limit condition) :
    CompilerGoalsNamesAllowed external origin limit
      (negatedGoals condition) := by
  unfold negatedGoals
  apply (compilerGoalsNamesAllowed_cons_iff external origin limit _ []).2
  constructor
  · apply compilerGoalNamesAllowed_committedIfGoal (by simp)
      conditionAllowed
    · apply (compilerGoalsNamesAllowed_cons_iff external origin limit
        compilerFailureGoal []).2
      exact ⟨compilerGoalNamesAllowed_failureGoal, by simp⟩
    · simp
  · simp

theorem compilerGoalNamesAllowed_transactiong {external : String → Prop}
    {origin limit : Nat} {template : Atom} {sub : List Goal}
    (templateAllowed :
      CompilerAtomNamesAllowed external origin limit template)
    (subAllowed : CompilerGoalsNamesAllowed external origin limit sub) :
    CompilerGoalNamesAllowed external origin limit
      (.transactiong template sub) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    template.vars (specializationGoalsVars sub)).2
  exact ⟨templateAllowed, subAllowed⟩

theorem compilerGoalNamesAllowed_amb {external : String → Prop}
    {origin limit : Nat} {branches : List (Atom × List Goal)} {result : Atom}
    (branchesAllowed :
      CompilerBranchesNamesAllowed external origin limit branches)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit (.amb branches result) := by
  apply (compilerNamesAllowed_append_iff external origin limit
    (specializationBranchVars branches) result.vars).2
  exact ⟨branchesAllowed, resultAllowed⟩

theorem compilerGoalNamesAllowed_ite {external : String → Prop}
    {origin limit : Nat} {condition result thenTerm elseTerm : Atom}
    {thenGoals elseGoals : List Goal}
    (conditionAllowed :
      CompilerAtomNamesAllowed external origin limit condition)
    (thenTermAllowed :
      CompilerAtomNamesAllowed external origin limit thenTerm)
    (thenGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit thenGoals)
    (elseTermAllowed :
      CompilerAtomNamesAllowed external origin limit elseTerm)
    (elseGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit elseGoals)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result) :
    CompilerGoalNamesAllowed external origin limit
      (.ite condition (thenTerm, thenGoals) (elseTerm, elseGoals) result) := by
  change CompilerNamesAllowed external origin limit
    (condition.vars ++ thenTerm.vars ++ specializationGoalsVars thenGoals ++
      elseTerm.vars ++ specializationGoalsVars elseGoals ++ result.vars)
  simp only [compilerNamesAllowed_append_iff]
  exact ⟨⟨⟨⟨⟨conditionAllowed, thenTermAllowed⟩, thenGoalsAllowed⟩,
    elseTermAllowed⟩, elseGoalsAllowed⟩, resultAllowed⟩

theorem compilerGoalNamesAllowed_smatch {external : String → Prop}
    {origin limit : Nat} {pattern : Atom}
    (patternAllowed :
      CompilerAtomNamesAllowed external origin limit pattern) :
    CompilerGoalNamesAllowed external origin limit (.smatch pattern) :=
  patternAllowed

/-- Every key or target variable carried by a compile-time substitution is
already visible to the enclosing compiler interval. -/
abbrev CompilerSubstNamesAllowed (external : String → Prop)
    (origin limit : Nat) (binding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst) : Prop :=
  CompilerNamesAllowed external origin limit (resolutionSubstVars binding)

private theorem substRange_mem_resolutionSubstVars (binding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst)
    (name : String)
    (member : name ∈ binding.flatMap (fun entry => entry.2.vars)) :
    name ∈ resolutionSubstVars binding := by
  rw [resolutionSubstVars]
  rcases List.mem_flatMap.mp member with ⟨entry, entryMember, nameMember⟩
  exact List.mem_flatMap.mpr
    ⟨entry, entryMember, List.mem_cons.mpr (.inr nameMember)⟩

/-- Deep atom substitution preserves the compiler-origin name
classification when the substitution itself satisfies that classification. -/
theorem CompilerAtomNamesAllowed.subst {external : String → Prop}
    {origin limit : Nat} {binding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst} {atom : Atom}
    (bindingAllowed :
      CompilerSubstNamesAllowed external origin limit binding)
    (atomAllowed : CompilerAtomNamesAllowed external origin limit atom) :
    CompilerAtomNamesAllowed external origin limit (subst binding atom) := by
  intro name member
  rcases subst_vars_origin binding atom name member with
    sourceMember | rangeMember
  · exact atomAllowed name sourceMember
  · exact bindingAllowed name
      (substRange_mem_resolutionSubstVars binding name rangeMember)

/-- Pointwise deep atom substitution preserves the compiler-origin name
classification for an ordered atom collection. -/
theorem CompilerAtomsNamesAllowed.substMap {external : String → Prop}
    {origin limit : Nat} {binding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst} {atoms : List Atom}
    (bindingAllowed :
      CompilerSubstNamesAllowed external origin limit binding)
    (atomsAllowed : CompilerAtomsNamesAllowed external origin limit atoms) :
    CompilerAtomsNamesAllowed external origin limit
      (atoms.map (subst binding)) := by
  intro name member
  rcases List.mem_flatMap.mp member with
    ⟨variableList, variableListMember, nameMember⟩
  rcases List.mem_map.mp variableListMember with
    ⟨atom, atomMember, rfl⟩
  apply CompilerAtomNamesAllowed.subst bindingAllowed
  · exact CompilerAtomsNamesAllowed.atom_mem atomsAllowed atomMember
  · exact nameMember

set_option maxHeartbeats 2000000 in
/-- Applying one compile-time binding throughout a nested emitted goal tree
does not invent variable names. The four motives follow `Goal`'s generated
mutual recursor over goals, goal lists, branch lists, and one branch. -/
theorem compilerGoalNamesAllowed_substCompiled
    {external : String → Prop} {origin limit : Nat}
    {binding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst}
    (bindingAllowed :
      CompilerSubstNamesAllowed external origin limit binding) :
    ∀ goal,
      CompilerGoalNamesAllowed external origin limit goal →
      CompilerGoalNamesAllowed external origin limit
        (substCompiledGoal binding goal) := by
  intro goal
  induction goal using Goal.rec
      (motive_2 := fun goals =>
        CompilerGoalsNamesAllowed external origin limit goals →
        CompilerGoalsNamesAllowed external origin limit
          (substCompiledGoals binding goals))
      (motive_3 := fun branches =>
        CompilerBranchesNamesAllowed external origin limit branches →
        CompilerBranchesNamesAllowed external origin limit
          (substCompiledBranches binding branches))
      (motive_4 := fun branch =>
        (CompilerAtomNamesAllowed external origin limit branch.1 ∧
          CompilerGoalsNamesAllowed external origin limit branch.2) →
        CompilerAtomNamesAllowed external origin limit
            (subst binding branch.1) ∧
          CompilerGoalsNamesAllowed external origin limit
            (substCompiledGoals binding branch.2))
  case call operation arguments result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (arguments.flatMap Atom.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        (arguments.flatMap Atom.vars) result.vars).mp allowed
      exact compilerGoalNamesAllowed_call
        (CompilerAtomsNamesAllowed.substMap bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2) operation
  case bin operation arguments result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (arguments.flatMap Atom.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        (arguments.flatMap Atom.vars) result.vars).mp allowed
      exact compilerGoalNamesAllowed_bin
        (CompilerAtomsNamesAllowed.substMap bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2) operation
  case callDyn head arguments result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (head.vars ++ arguments.flatMap Atom.vars ++ result.vars) at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      exact compilerGoalNamesAllowed_callDyn
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1)
        (CompilerAtomsNamesAllowed.substMap bindingAllowed allowed.1.2)
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.2)
  case evalg value result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (value.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        value.vars result.vars).mp allowed
      exact compilerGoalNamesAllowed_evalg
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case catchg template goals result goalsIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ specializationGoalsVars goals ++ result.vars)
        at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      exact compilerGoalNamesAllowed_catchg
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1)
        (goalsIH allowed.1.2)
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.2)
  case softcut template condition thenGoals elseGoals conditionIH thenIH
      elseIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ specializationGoalsVars condition ++
          specializationGoalsVars thenGoals ++
          specializationGoalsVars elseGoals) at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      exact compilerGoalNamesAllowed_softcut
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1.1)
        (conditionIH allowed.1.1.2) (thenIH allowed.1.2)
        (elseIH allowed.2)
  case eq left right =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (left.vars ++ right.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        left.vars right.vars).mp allowed
      exact compilerGoalNamesAllowed_eq
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case compileAlias left right =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (left.vars ++ right.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        left.vars right.vars).mp allowed
      exact compilerGoalNamesAllowed_compileAlias
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case cut => simp [substCompiledGoal, specializationGoalVars,
      CompilerNamesAllowed]
  case cutAt => simp [substCompiledGoal, specializationGoalVars,
      CompilerNamesAllowed]
  case catchExit template result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        template.vars result.vars).mp allowed
      exact compilerGoalNamesAllowed_catchExit
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case softcutExit template =>
      intro allowed
      exact compilerGoalNamesAllowed_softcutExit
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed)
  case findall template goals result goalsIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ specializationGoalsVars goals ++ result.vars)
        at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      exact compilerGoalNamesAllowed_findall
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1)
        (goalsIH allowed.1.2)
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.2)
  case onceg template goals result goalsIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ specializationGoalsVars goals ++ result.vars)
        at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      exact compilerGoalNamesAllowed_onceg
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1)
        (goalsIH allowed.1.2)
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.2)
  case transactiong template goals goalsIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (template.vars ++ specializationGoalsVars goals) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        template.vars (specializationGoalsVars goals)).mp allowed
      exact compilerGoalNamesAllowed_transactiong
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (goalsIH parts.2)
  case amb branches result branchesIH =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (specializationBranchVars branches ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        (specializationBranchVars branches) result.vars).mp allowed
      exact compilerGoalNamesAllowed_amb (branchesIH parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case spread value result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (value.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        value.vars result.vars).mp allowed
      exact compilerGoalNamesAllowed_spread
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2)
  case ite condition thenBranch elseBranch result thenIH elseIH =>
      intro allowed
      rcases thenBranch with ⟨thenTerm, thenGoals⟩
      rcases elseBranch with ⟨elseTerm, elseGoals⟩
      change CompilerNamesAllowed external origin limit
        (condition.vars ++ thenTerm.vars ++
          specializationGoalsVars thenGoals ++ elseTerm.vars ++
          specializationGoalsVars elseGoals ++ result.vars) at allowed
      simp only [compilerNamesAllowed_append_iff] at allowed
      have thenAllowed := thenIH ⟨allowed.1.1.1.1.2, allowed.1.1.1.2⟩
      have elseAllowed := elseIH ⟨allowed.1.1.2, allowed.1.2⟩
      exact compilerGoalNamesAllowed_ite
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.1.1.1.1.1)
        thenAllowed.1 thenAllowed.2 elseAllowed.1 elseAllowed.2
        (CompilerAtomNamesAllowed.subst bindingAllowed allowed.2)
  case smatch pattern =>
      intro allowed
      exact CompilerAtomNamesAllowed.subst bindingAllowed allowed
  case wact operation arguments result =>
      intro allowed
      change CompilerNamesAllowed external origin limit
        (arguments.flatMap Atom.vars ++ result.vars) at allowed
      have parts := (compilerNamesAllowed_append_iff external origin limit
        (arguments.flatMap Atom.vars) result.vars).mp allowed
      exact compilerGoalNamesAllowed_wact
        (CompilerAtomsNamesAllowed.substMap bindingAllowed parts.1)
        (CompilerAtomNamesAllowed.subst bindingAllowed parts.2) operation
  all_goals
    simp only [substCompiledGoals, substCompiledBranches,
      compilerGoalsNamesAllowed_nil, compilerGoalsNamesAllowed_cons_iff,
      compilerBranchesNamesAllowed_nil,
      compilerBranchesNamesAllowed_cons_iff] at *
  all_goals
    aesop (add safe forward [CompilerAtomNamesAllowed.subst])

@[simp] theorem compilerSubstNamesAllowed_nil (external : String → Prop)
    (origin limit : Nat) :
    CompilerSubstNamesAllowed external origin limit [] := by
  simp [CompilerSubstNamesAllowed, CompilerNamesAllowed,
    resolutionSubstVars]

/-- One successful shared-output constraint preserves the origin of every
variable stored in the accumulated compile-time binding. -/
theorem bindTypedSharedResult_namesAllowed
    {external : String → Prop} {origin limit : Nat}
    {sharedResult : Atom} {binding nextBinding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst}
    {branch : Atom × List Goal}
    (sharedAllowed :
      CompilerAtomNamesAllowed external origin limit sharedResult)
    (bindingAllowed :
      CompilerSubstNamesAllowed external origin limit binding)
    (branchResultAllowed :
      CompilerAtomNamesAllowed external origin limit branch.1)
    (bound : bindTypedSharedResult sharedResult binding branch =
      .ok nextBinding) :
    CompilerSubstNamesAllowed external origin limit nextBinding := by
  unfold bindTypedSharedResult at bound
  split at bound
  · rcases Except.ok.inj bound with rfl
    exact bindingAllowed
  · rename_i distinct
    cases exactEq : unifyTopExact (subst binding sharedResult)
        (subst binding branch.1) with
    | none => simp [exactEq] at bound
    | some generated =>
        simp only [exactEq] at bound
        rcases Except.ok.inj bound with rfl
        intro name member
        rcases substCompose_vars_origin generated binding name member with
          generatedMember | existingMember
        · have underlying := unifyTopExact_some_underlying
              (subst binding sharedResult) (subst binding branch.1)
              generated exactEq
          rcases unifyTopWith_substVars_origin prologGroundIdentical
              (subst binding sharedResult) (subst binding branch.1)
              generated underlying name generatedMember with
            sharedMember | branchMember
          · exact (CompilerAtomNamesAllowed.subst bindingAllowed
              sharedAllowed) name sharedMember
          · exact (CompilerAtomNamesAllowed.subst bindingAllowed
              branchResultAllowed) name branchMember
        · exact bindingAllowed name existingMember

/-- The left-to-right typed-result fold preserves the origin invariant for
its accumulated binding. -/
theorem bindTypedSharedResult_foldlM_namesAllowed
    {external : String → Prop} {origin limit : Nat}
    {sharedResult : Atom} {branches : List (Atom × List Goal)}
    {initial finalBinding : Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst}
    (sharedAllowed :
      CompilerAtomNamesAllowed external origin limit sharedResult)
    (branchesAllowed :
      CompilerBranchesNamesAllowed external origin limit branches)
    (initialAllowed :
      CompilerSubstNamesAllowed external origin limit initial)
    (folded : branches.foldlM (bindTypedSharedResult sharedResult) initial =
      .ok finalBinding) :
    CompilerSubstNamesAllowed external origin limit finalBinding := by
  induction branches generalizing initial with
  | nil =>
      rw [List.foldlM_nil] at folded
      rcases Except.ok.inj folded with rfl
      exact initialAllowed
  | cons branch branches ih =>
      rcases branch with ⟨branchResult, branchGoals⟩
      have branchParts :=
        (compilerBranchesNamesAllowed_cons_iff external origin limit
          branchResult branchGoals branches).1 branchesAllowed
      rw [List.foldlM_cons] at folded
      simp only [Bind.bind, Except.bind] at folded
      split at folded
      · contradiction
      · rename_i nextBinding nextBindingEq
        apply ih branchParts.2.2
          (bindTypedSharedResult_namesAllowed sharedAllowed initialAllowed
            branchParts.1 nextBindingEq)
          folded

/-- Successful global shared-output resolution preserves both the returned
result and every variable nested in every returned branch. -/
theorem resolveTypedSharedResult_namesAllowed
    {external : String → Prop} {origin limit : Nat}
    {sharedResult : Atom} {branches : List (Atom × List Goal)}
    {resolved : Atom × List (Atom × List Goal)}
    (sharedAllowed :
      CompilerAtomNamesAllowed external origin limit sharedResult)
    (branchesAllowed :
      CompilerBranchesNamesAllowed external origin limit branches)
    (resolution : resolveTypedSharedResult sharedResult branches =
      .ok resolved) :
    CompilerAtomNamesAllowed external origin limit resolved.1 ∧
      CompilerBranchesNamesAllowed external origin limit resolved.2 := by
  unfold resolveTypedSharedResult at resolution
  simp only [Bind.bind, Except.bind] at resolution
  split at resolution
  · contradiction
  · rename_i binding bindingEq
    rcases Except.ok.inj resolution with rfl
    have bindingAllowed := bindTypedSharedResult_foldlM_namesAllowed
      sharedAllowed branchesAllowed
      (compilerSubstNamesAllowed_nil external origin limit) bindingEq
    have resolvedAmb := compilerGoalNamesAllowed_substCompiled bindingAllowed
      (.amb branches sharedResult)
      (compilerGoalNamesAllowed_amb branchesAllowed sharedAllowed)
    change CompilerNamesAllowed external origin limit
      (specializationBranchVars (substCompiledBranches binding branches) ++
        (subst binding sharedResult).vars) at resolvedAmb
    have parts := (compilerNamesAllowed_append_iff external origin limit
      (specializationBranchVars (substCompiledBranches binding branches))
      (subst binding sharedResult).vars).1 resolvedAmb
    exact ⟨parts.2, parts.1⟩

theorem compilerCaseArmGoal_namesAllowed {external : String → Prop}
    {origin limit : Nat} {compiledPattern sourcePattern compiledBody
      scrutinee result : Atom} {patternGoals bodyGoals elseGoals : List Goal}
    (compiledPatternAllowed :
      CompilerAtomNamesAllowed external origin limit compiledPattern)
    (sourcePatternAllowed :
      CompilerAtomNamesAllowed external origin limit sourcePattern)
    (compiledBodyAllowed :
      CompilerAtomNamesAllowed external origin limit compiledBody)
    (scrutineeAllowed :
      CompilerAtomNamesAllowed external origin limit scrutinee)
    (resultAllowed : CompilerAtomNamesAllowed external origin limit result)
    (patternGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit patternGoals)
    (bodyGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit bodyGoals)
    (elseGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit elseGoals) :
    CompilerGoalNamesAllowed external origin limit
      (committedIfGoal (bindingTemplate compiledPattern [sourcePattern])
        (patternGoals ++ [Goal.eq compiledPattern scrutinee])
        (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals) := by
  apply compilerGoalNamesAllowed_committedIfGoal
  · apply bindingTemplate_namesAllowed compiledPatternAllowed
    apply (compilerAtomsNamesAllowed_cons_iff external origin limit
      sourcePattern []).2
    exact ⟨sourcePatternAllowed, by simp⟩
  · apply (compilerGoalsNamesAllowed_append_iff external origin limit
      patternGoals [Goal.eq compiledPattern scrutinee]).2
    constructor
    · exact patternGoalsAllowed
    · apply (compilerGoalsNamesAllowed_cons_iff external origin limit
        (Goal.eq compiledPattern scrutinee) []).2
      exact ⟨compilerGoalNamesAllowed_eq compiledPatternAllowed
        scrutineeAllowed, by simp⟩
  · apply (compilerGoalsNamesAllowed_append_iff external origin limit
      bodyGoals [Goal.eq result compiledBody]).2
    constructor
    · exact bodyGoalsAllowed
    · apply (compilerGoalsNamesAllowed_cons_iff external origin limit
        (Goal.eq result compiledBody) []).2
      exact ⟨compilerGoalNamesAllowed_eq resultAllowed compiledBodyAllowed,
        by simp⟩
  · exact elseGoalsAllowed

theorem compileTypeCheckWhen_generatedNames (external : String → Prop)
    (requiresCheck : Bool) (origin start : Nat) (value expected : Atom)
    (originStart : origin ≤ start)
    (valueAllowed : CompilerAtomNamesAllowed external origin start value)
    (expectedAllowed : CompilerAtomNamesAllowed external origin start expected) :
    CompilerGoalsNamesAllowed external origin
      (compileTypeCheckWhen requiresCheck value expected start).2
      (compileTypeCheckWhen requiresCheck value expected start).1 := by
  unfold compileTypeCheckWhen
  split
  · simp only [fresh]
    apply (compilerGoalsNamesAllowed_cons_iff external origin (start + 2)
      (.softcut (typeCheckBindingTemplate expected)
        [Goal.bin "get-type" [value] (Atom.var (compilerGeneratedName start)),
          Goal.eq (Atom.var (compilerGeneratedName start)) (chainify expected)]
        []
        [Goal.bin "get-metatype" [value]
            (Atom.var (compilerGeneratedName (start + 1))),
          Goal.eq (Atom.var (compilerGeneratedName (start + 1)))
            (chainify expected)])
      []).2
    constructor
    · apply compilerGoalNamesAllowed_softcut
      · unfold typeCheckBindingTemplate
        split
        · simp
        · apply bindingTemplate_namesAllowed
          · simp
          · simp only [compilerAtomsNamesAllowed_cons_iff,
              compilerAtomsNamesAllowed_nil, and_true]
            exact expectedAllowed.mono (by omega)
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        constructor
        · apply compilerGoalNamesAllowed_bin
          · simp
            exact valueAllowed.mono (by omega)
          · simp
            exact .generated originStart (by omega)
        · apply compilerGoalNamesAllowed_eq
          · simp
            exact .generated originStart (by omega)
          · exact (chainify_namesAllowed expectedAllowed).mono (by omega)
      · simp
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        constructor
        · apply compilerGoalNamesAllowed_bin
          · simp
            exact valueAllowed.mono (by omega)
          · simp
            exact .generated (Nat.le_trans originStart (by omega)) (by omega)
        · apply compilerGoalNamesAllowed_eq
          · simp
            exact .generated (Nat.le_trans originStart (by omega)) (by omega)
          · exact (chainify_namesAllowed expectedAllowed).mono (by omega)
    · simp
  · simp

theorem compileTypeCheck_generatedNames (external : String → Prop)
    (origin start : Nat) (value expected : Atom) (originStart : origin ≤ start)
    (valueAllowed : CompilerAtomNamesAllowed external origin start value)
    (expectedAllowed : CompilerAtomNamesAllowed external origin start expected) :
    CompilerGoalsNamesAllowed external origin
      (compileTypeCheck value expected start).2
      (compileTypeCheck value expected start).1 := by
  exact compileTypeCheckWhen_generatedNames external
    (typeRequiresCheck expected) origin start value expected originStart
    valueAllowed expectedAllowed

theorem compileResultTypeCheck_generatedNames (external : String → Prop)
    (origin start : Nat) (value expected : Atom) (originStart : origin ≤ start)
    (valueAllowed : CompilerAtomNamesAllowed external origin start value)
    (expectedAllowed : CompilerAtomNamesAllowed external origin start expected) :
    CompilerGoalsNamesAllowed external origin
      (compileResultTypeCheck value expected start).2
      (compileResultTypeCheck value expected start).1 := by
  exact compileTypeCheckWhen_generatedNames external
    (resultTypeRequiresCheck expected) origin start value expected originStart
    valueAllowed expectedAllowed

theorem compileTypedArgsFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start sources types terms goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start sources →
      CompilerAtomsNamesAllowed external origin start types →
      compileTypedArgsFuel (fuel + 1) env start sources types =
          .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start sources types terms goals next originStart
    envAllowed sourcesAllowed typesAllowed compiled
  cases sources with
  | nil =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_nil_eq] at compiled
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          simp
      | cons ty types =>
          rw [compileTypedArgsFuel_surplus_type_eq] at compiled
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          simp
  | cons source sources =>
      cases types with
      | nil =>
          rw [compileTypedArgsFuel_missing_type_eq] at compiled
          contradiction
      | cons ty types =>
          have sourceAndRest :=
            (compilerAtomsNamesAllowed_cons_iff external origin start source
              sources).mp sourcesAllowed
          have typeAndRest :=
            (compilerAtomsNamesAllowed_cons_iff external origin start ty
              types).mp typesAllowed
          cases expression : (ty == (Atom.sym "Expression")) with
          | true =>
              rw [compileTypedArgsFuel.eq_def] at compiled
              simp only [expression, if_true] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · rename_i restResult restEq
                have restCounter :=
                  (compilerCounterAt fuel).typedArgs _ _ _ _ _ _ _ restEq
                have restNames := ih.typedArgs external origin env start
                  sources types restResult.1 restResult.2.1 restResult.2.2
                  originStart envAllowed sourceAndRest.2 typeAndRest.2 restEq
                rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                constructor
                · apply (compilerAtomsNamesAllowed_cons_iff external origin
                    restResult.2.2 (chainify source) restResult.1).2
                  exact ⟨(chainify_namesAllowed sourceAndRest.1).mono
                    restCounter, restNames.1⟩
                · exact restNames.2
          | false =>
              rw [compileTypedArgsFuel_evaluated_eq fuel env start source ty
                sources types expression] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · rename_i firstResult firstEq
                have firstCounter :=
                  (compilerCounterAt fuel).expr _ _ _ _ _ _ firstEq
                have firstNames := ih.expr external origin env start source
                  firstResult.1 firstResult.2.1 firstResult.2.2 originStart
                  envAllowed sourceAndRest.1 firstEq
                let checked := compileTypeCheck firstResult.1 ty
                  firstResult.2.2
                have checkedCounter : firstResult.2.2 ≤ checked.2 := by
                  exact compileTypeCheck_counter_le firstResult.1 ty
                    firstResult.2.2
                have checkedNames : CompilerGoalsNamesAllowed external origin
                    checked.2 checked.1 := by
                  exact compileTypeCheck_generatedNames external origin
                    firstResult.2.2 firstResult.1 ty
                    (Nat.le_trans originStart firstCounter) firstNames.1
                    (typeAndRest.1.mono firstCounter)
                split at compiled
                · contradiction
                · rename_i restResult restEq
                  have restCounter :=
                    (compilerCounterAt fuel).typedArgs _ _ _ _ _ _ _ restEq
                  have restNames := ih.typedArgs external origin env checked.2
                    sources types restResult.1 restResult.2.1
                    restResult.2.2
                    (Nat.le_trans (Nat.le_trans originStart firstCounter)
                      checkedCounter)
                    ((envAllowed.mono firstCounter).mono checkedCounter)
                    ((sourceAndRest.2.mono firstCounter).mono checkedCounter)
                    ((typeAndRest.2.mono firstCounter).mono checkedCounter)
                    restEq
                  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                  constructor
                  · apply (compilerAtomsNamesAllowed_cons_iff external origin
                      restResult.2.2 firstResult.1 restResult.1).2
                    exact ⟨(firstNames.1.mono checkedCounter).mono restCounter,
                      restNames.1⟩
                  · have combined : CompilerGoalsNamesAllowed external origin
                        restResult.2.2
                        (firstResult.2.1 ++ (checked.1 ++ restResult.2.1)) := by
                      apply (compilerGoalsNamesAllowed_append_iff external
                        origin restResult.2.2 firstResult.2.1
                        (checked.1 ++ restResult.2.1)).2
                      constructor
                      · exact (firstNames.2.mono checkedCounter).mono restCounter
                      · apply (compilerGoalsNamesAllowed_append_iff external
                          origin restResult.2.2 checked.1 restResult.2.1).2
                        exact ⟨checkedNames.mono restCounter, restNames.2⟩
                    simpa [checked] using combined

theorem compileExprFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start source term goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomNamesAllowed external origin start source →
      compileExprFuel (fuel + 1) env start source =
          .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start source term goals next originStart
    envAllowed sourceAllowed compiled
  rw [compileExprFuel.eq_def] at compiled
  split at compiled
  · contradiction
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    exact ⟨sourceAllowed, by simp⟩
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    exact ⟨canonBool_namesAllowed sourceAllowed, by simp⟩
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    exact ⟨canonBool_namesAllowed sourceAllowed, by simp⟩
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    constructor <;> simp [nilA]
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    exact ⟨sourceAllowed, by simp⟩
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    exact ⟨sourceAllowed, by simp⟩
  · exact (ih.of_succ_eq (by omega)).app external origin _ _ _ _ term goals
      next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using sourceAllowed) compiled
  · simp only [Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i listResult listEq
      have listCounter := compileListFuel_counter_mono _ _ _ _ _ _ _ listEq
      have sourceParts := compilerAtomExprCons_namesAllowed sourceAllowed
      have listNames := (ih.of_succ_eq (by omega)).list external origin _ _ _ listResult.1
        listResult.2.1 listResult.2.2 originStart envAllowed
        sourceParts.2 listEq
      simp only [fresh] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have originList : origin ≤ listResult.2.2 :=
        Nat.le_trans originStart listCounter
      have resultAllowed : CompilerAtomNamesAllowed external origin
          (listResult.2.2 + 1)
          (Atom.var (compilerGeneratedName listResult.2.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated originList (by omega)
      constructor
      · exact resultAllowed
      · apply (compilerGoalsNamesAllowed_append_iff external origin
          (listResult.2.2 + 1) listResult.2.1
          [Goal.callDyn (Atom.var _) listResult.1 (Atom.var _)]).2
        constructor
        · exact listNames.2.mono (by omega)
        · apply (compilerGoalsNamesAllowed_cons_iff external origin
            (listResult.2.2 + 1) (Goal.callDyn (Atom.var _)
              listResult.1 (Atom.var _)) []).2
          constructor
          · apply compilerGoalNamesAllowed_callDyn
            · exact sourceParts.1.mono
                (Nat.le_trans listCounter (Nat.le_add_right _ _))
            · exact listNames.1.mono (by omega)
            · exact resultAllowed
          · simp
  · simp only [Bind.bind, Except.bind] at compiled
    split at compiled
    · contradiction
    · rename_i headResult headEq
      have headCounter := compileExprFuel_counter_mono _ _ _ _ _ _ _ headEq
      have sourceParts := compilerAtomExprCons_namesAllowed sourceAllowed
      have headNames := (ih.of_succ_eq (by omega)).expr external origin _ _ _ headResult.1
        headResult.2.1 headResult.2.2 originStart envAllowed sourceParts.1
        headEq
      split at compiled
      · contradiction
      · rename_i argsResult argsEq
        have argsCounter := compileListFuel_counter_mono _ _ _ _ _ _ _ argsEq
        have argsNames := (ih.of_succ_eq (by omega)).list external origin _ headResult.2.2 _
          argsResult.1 argsResult.2.1 argsResult.2.2
          (Nat.le_trans originStart headCounter)
          (envAllowed.mono headCounter)
          (sourceParts.2.mono headCounter) argsEq
        split at compiled
        · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          constructor
          · apply chainOf_namesAllowed
            apply (compilerAtomsNamesAllowed_cons_iff external origin
              argsResult.2.2 headResult.1 argsResult.1).2
            exact ⟨headNames.1.mono argsCounter, argsNames.1⟩
          · apply (compilerGoalsNamesAllowed_append_iff external origin
              argsResult.2.2 headResult.2.1 argsResult.2.1).2
            exact ⟨headNames.2.mono argsCounter, argsNames.2⟩
        · simp only [fresh] at compiled
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          have originArgs : origin ≤ argsResult.2.2 :=
            Nat.le_trans (Nat.le_trans originStart headCounter) argsCounter
          have resultAllowed : CompilerAtomNamesAllowed external origin
              (argsResult.2.2 + 1)
              (Atom.var (compilerGeneratedName argsResult.2.2)) := by
            simp only [compilerAtomNamesAllowed_var_iff]
            exact .generated originArgs (by omega)
          constructor
          · exact resultAllowed
          · have argsToFinal :
                argsResult.2.2 ≤ argsResult.2.2 + 1 := by omega
            have combined : CompilerGoalsNamesAllowed external origin
                (argsResult.2.2 + 1)
                (headResult.2.1 ++ (argsResult.2.1 ++
                  [Goal.callDyn headResult.1 argsResult.1
                    (Atom.var (compilerGeneratedName argsResult.2.2))])) := by
              apply (compilerGoalsNamesAllowed_append_iff external origin
                (argsResult.2.2 + 1) headResult.2.1
                (argsResult.2.1 ++ [Goal.callDyn headResult.1 argsResult.1
                  (Atom.var _)])).2
              constructor
              · exact CompilerGoalsNamesAllowed.mono argsToFinal
                  (CompilerGoalsNamesAllowed.mono argsCounter headNames.2)
              · apply (compilerGoalsNamesAllowed_append_iff external origin
                  (argsResult.2.2 + 1) argsResult.2.1
                  [Goal.callDyn headResult.1 argsResult.1 (Atom.var _)]).2
                constructor
                · exact CompilerGoalsNamesAllowed.mono argsToFinal argsNames.2
                · apply (compilerGoalsNamesAllowed_cons_iff external origin
                    (argsResult.2.2 + 1)
                    (Goal.callDyn headResult.1 argsResult.1 (Atom.var _)) []).2
                  exact ⟨compilerGoalNamesAllowed_callDyn
                    (CompilerAtomNamesAllowed.mono argsToFinal
                      (CompilerAtomNamesAllowed.mono argsCounter headNames.1))
                    (CompilerAtomsNamesAllowed.mono argsToFinal argsNames.1)
                    resultAllowed, by simp⟩
            simpa [List.append_assoc, compilerGeneratedName] using combined

theorem compilePatternFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start source term goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomNamesAllowed external origin start source →
      compilePatternFuel (fuel + 1) env start source =
          .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start source term goals next originStart
    envAllowed sourceAllowed compiled
  cases source with
  | var name =>
      rw [compilePatternFuel_var_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      exact ⟨sourceAllowed, by simp⟩
  | sym name =>
      rw [compilePatternFuel_sym_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      exact ⟨canonBool_namesAllowed sourceAllowed, by simp⟩
  | gnd ground =>
      rw [compilePatternFuel_gnd_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      exact ⟨canonBool_namesAllowed sourceAllowed, by simp⟩
  | expr items =>
      have itemsAllowed :=
        (compilerAtomNamesAllowed_expr_iff external origin start items).mp
          sourceAllowed
      cases items with
      | nil =>
          rw [compilePatternFuel_nil_eq] at compiled
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          constructor <;> simp [nilA]
      | cons head arguments =>
          have headAndArguments :=
            (compilerAtomsNamesAllowed_cons_iff external origin start head
              arguments).mp itemsAllowed
          cases head with
          | var name =>
              rw [compilePatternFuel_var_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · rename_i listResult listEq
                have listNames := ih.patternList external origin env start
                  (Atom.var name :: arguments) listResult.1 listResult.2.1
                  listResult.2.2 originStart envAllowed itemsAllowed listEq
                rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                exact ⟨chainOf_namesAllowed listNames.1, listNames.2⟩
          | gnd ground =>
              rw [compilePatternFuel_gnd_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · rename_i listResult listEq
                have listNames := ih.patternList external origin env start
                  (Atom.gnd ground :: arguments) listResult.1 listResult.2.1
                  listResult.2.2 originStart envAllowed itemsAllowed listEq
                rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                exact ⟨chainOf_namesAllowed listNames.1, listNames.2⟩
          | expr nested =>
              rw [compilePatternFuel_expr_head_eq] at compiled
              simp only [Bind.bind, Except.bind] at compiled
              split at compiled
              · contradiction
              · rename_i listResult listEq
                have listNames := ih.patternList external origin env start
                  (Atom.expr nested :: arguments) listResult.1 listResult.2.1
                  listResult.2.2 originStart envAllowed itemsAllowed listEq
                rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                exact ⟨chainOf_namesAllowed listNames.1, listNames.2⟩
          | sym name =>
              cases arguments with
              | nil =>
                  rw [compilePatternFuel_sym_nil_eq] at compiled
                  split at compiled
                  · exact ih.expr external origin env start (Atom.expr
                      [Atom.sym name]) term goals next originStart envAllowed
                      sourceAllowed compiled
                  · simp only [Bind.bind, Except.bind] at compiled
                    split at compiled
                    · contradiction
                    · rename_i listResult listEq
                      have listNames := ih.patternList external origin env start
                        [] listResult.1 listResult.2.1 listResult.2.2
                        originStart envAllowed (by simp) listEq
                      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                      constructor
                      · apply chainOf_namesAllowed
                        apply (compilerAtomsNamesAllowed_cons_iff external
                          origin listResult.2.2 (Atom.sym name)
                          listResult.1).2
                        exact ⟨by simp, listNames.1⟩
                      · exact listNames.2
              | cons first tail =>
                  cases tail with
                  | nil =>
                      rw [compilePatternFuel_sym_singleton_eq] at compiled
                      split at compiled
                      · exact ih.expr external origin env start
                          (Atom.expr [Atom.sym name, first]) term goals next
                          originStart envAllowed sourceAllowed compiled
                      · simp only [Bind.bind, Except.bind] at compiled
                        split at compiled
                        · contradiction
                        · rename_i listResult listEq
                          have listNames := ih.patternList external origin env
                            start [first] listResult.1 listResult.2.1
                            listResult.2.2 originStart envAllowed
                            headAndArguments.2 listEq
                          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                          constructor
                          · apply chainOf_namesAllowed
                            apply (compilerAtomsNamesAllowed_cons_iff external
                              origin listResult.2.2 (Atom.sym name)
                              listResult.1).2
                            exact ⟨by simp, listNames.1⟩
                          · exact listNames.2
                  | cons second rest =>
                      cases rest with
                      | nil =>
                          have pairAllowed :=
                            (compilerAtomsNamesAllowed_cons_iff external origin
                              start first [second]).mp headAndArguments.2
                          have secondAllowed :=
                            ((compilerAtomsNamesAllowed_cons_iff external origin
                              start second []).mp pairAllowed.2).1
                          by_cases chain : name = "#c"
                          · subst name
                            rw [compilePatternFuel_chain_eq] at compiled
                            rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                            exact ⟨sourceAllowed, by simp⟩
                          · by_cases consName : name = "cons"
                            · subst name
                              rw [compilePatternFuel_cons_eq] at compiled
                              simp only [Bind.bind, Except.bind] at compiled
                              split at compiled
                              · contradiction
                              · rename_i firstResult firstEq
                                have firstCounter :=
                                  compilePatternFuel_counter_mono _ _ _ _ _ _ _
                                    firstEq
                                have firstNames := ih.pattern external origin env
                                  start first firstResult.1 firstResult.2.1
                                  firstResult.2.2 originStart envAllowed
                                  pairAllowed.1 firstEq
                                split at compiled
                                · contradiction
                                · rename_i secondResult secondEq
                                  have secondCounter :=
                                    compilePatternFuel_counter_mono _ _ _ _ _ _ _
                                      secondEq
                                  have secondNames := ih.pattern external origin
                                    env firstResult.2.2 second secondResult.1
                                    secondResult.2.1 secondResult.2.2
                                    (Nat.le_trans originStart firstCounter)
                                    (envAllowed.mono firstCounter)
                                    (secondAllowed.mono firstCounter) secondEq
                                  rcases Except.ok.inj compiled with
                                    ⟨rfl, rfl, rfl⟩
                                  constructor
                                  · exact consC_namesAllowed
                                      (firstNames.1.mono secondCounter)
                                      secondNames.1
                                  · apply (compilerGoalsNamesAllowed_append_iff
                                      external origin secondResult.2.2
                                      firstResult.2.1 secondResult.2.1).2
                                    exact ⟨firstNames.2.mono secondCounter,
                                      secondNames.2⟩
                            · rw [compilePatternFuel_sym_pair_other_eq fuel env
                                start name first second chain consName] at compiled
                              split at compiled
                              · exact ih.expr external origin env start
                                  (Atom.expr [Atom.sym name, first, second]) term
                                  goals next originStart envAllowed sourceAllowed
                                  compiled
                              · simp only [Bind.bind, Except.bind] at compiled
                                split at compiled
                                · contradiction
                                · rename_i listResult listEq
                                  have listNames := ih.patternList external
                                    origin env start [first, second]
                                    listResult.1 listResult.2.1 listResult.2.2
                                    originStart envAllowed headAndArguments.2
                                    listEq
                                  rcases Except.ok.inj compiled with
                                    ⟨rfl, rfl, rfl⟩
                                  constructor
                                  · apply chainOf_namesAllowed
                                    apply (compilerAtomsNamesAllowed_cons_iff
                                      external origin listResult.2.2
                                      (Atom.sym name) listResult.1).2
                                    exact ⟨by simp, listNames.1⟩
                                  · exact listNames.2
                      | cons third rest =>
                          rw [compilePatternFuel_sym_many_eq] at compiled
                          split at compiled
                          · exact ih.expr external origin env start
                              (Atom.expr (Atom.sym name :: first :: second ::
                                third :: rest)) term goals next originStart
                              envAllowed sourceAllowed compiled
                          · simp only [Bind.bind, Except.bind] at compiled
                            split at compiled
                            · contradiction
                            · rename_i listResult listEq
                              have listNames := ih.patternList external origin
                                env start (first :: second :: third :: rest)
                                listResult.1 listResult.2.1 listResult.2.2
                                originStart envAllowed headAndArguments.2 listEq
                              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                              constructor
                              · apply chainOf_namesAllowed
                                apply (compilerAtomsNamesAllowed_cons_iff
                                  external origin listResult.2.2 (Atom.sym name)
                                  listResult.1).2
                                exact ⟨by simp, listNames.1⟩
                              · exact listNames.2

theorem compileCaseArmDo_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv)
    (scrutinee result : Atom) (start : Nat) (pattern body : Atom)
    (more : List Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (scrutineeAllowed :
      CompilerAtomNamesAllowed external origin start scrutinee)
    (resultAllowed : CompilerAtomNamesAllowed external origin start result)
    (patternAllowed : CompilerAtomNamesAllowed external origin start pattern)
    (bodyAllowed : CompilerAtomNamesAllowed external origin start body)
    (moreAllowed : CompilerAtomsNamesAllowed external origin start more)
    (compiled :
      (do
        let (compiledPattern, patternGoals, middlePattern) ←
          compilePatternFuel fuel env start pattern
        let (compiledBody, bodyGoals, middleBody) ←
          compileExprFuel fuel env middlePattern body
        let (elseGoals, finalCounter) ←
          compileCaseArmsFuel fuel env scrutinee result middleBody more
        let carry := bindingTemplate compiledPattern [pattern]
        .ok ([committedIfGoal carry
          (patternGoals ++ [Goal.eq compiledPattern scrutinee])
          (bodyGoals ++ [Goal.eq result compiledBody]) elseGoals],
          finalCounter)) = .ok (goals, next)) :
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i patternResult patternEq
    have patternCounter :=
      compilePatternFuel_counter_mono _ _ _ _ _ _ _ patternEq
    have patternNames := ih.pattern external origin env start pattern
      patternResult.1 patternResult.2.1 patternResult.2.2 originStart
      envAllowed patternAllowed patternEq
    split at compiled
    · contradiction
    · rename_i bodyResult bodyEq
      have bodyCounter := compileExprFuel_counter_mono _ _ _ _ _ _ _ bodyEq
      have bodyNames := ih.expr external origin env patternResult.2.2 body
        bodyResult.1 bodyResult.2.1 bodyResult.2.2
        (Nat.le_trans originStart patternCounter)
        (envAllowed.mono patternCounter) (bodyAllowed.mono patternCounter)
        bodyEq
      split at compiled
      · contradiction
      · rename_i elseResult elseEq
        have elseCounter :=
          compileCaseArmsFuel_counter_mono _ _ _ _ _ _ _ _ elseEq
        have elseNames := ih.caseArms external origin env scrutinee result
          bodyResult.2.2 more elseResult.1 elseResult.2
          (Nat.le_trans (Nat.le_trans originStart patternCounter) bodyCounter)
          ((envAllowed.mono patternCounter).mono bodyCounter)
          ((scrutineeAllowed.mono patternCounter).mono bodyCounter)
          ((resultAllowed.mono patternCounter).mono bodyCounter)
          ((moreAllowed.mono patternCounter).mono bodyCounter) elseEq
        rcases Except.ok.inj compiled with ⟨rfl, rfl⟩
        apply (compilerGoalsNamesAllowed_cons_iff external origin elseResult.2
          (committedIfGoal (bindingTemplate patternResult.1 [pattern])
            (patternResult.2.1 ++ [Goal.eq patternResult.1 scrutinee])
            (bodyResult.2.1 ++ [Goal.eq result bodyResult.1]) elseResult.1)
          []).2
        constructor
        · apply compilerCaseArmGoal_namesAllowed
          · exact (patternNames.1.mono bodyCounter).mono elseCounter
          · exact ((patternAllowed.mono patternCounter).mono bodyCounter).mono
              elseCounter
          · exact bodyNames.1.mono elseCounter
          · exact ((scrutineeAllowed.mono patternCounter).mono bodyCounter).mono
              elseCounter
          · exact ((resultAllowed.mono patternCounter).mono bodyCounter).mono
              elseCounter
          · exact (patternNames.2.mono bodyCounter).mono elseCounter
          · exact bodyNames.2.mono elseCounter
          · exact elseNames
        · simp

theorem compileCaseArmsFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env scrutinee result start arms goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomNamesAllowed external origin start scrutinee →
      CompilerAtomNamesAllowed external origin start result →
      CompilerAtomsNamesAllowed external origin start arms →
      compileCaseArmsFuel (fuel + 1) env scrutinee result start arms =
          .ok (goals, next) →
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env scrutinee result start arms goals next originStart
    envAllowed scrutineeAllowed resultAllowed armsAllowed compiled
  cases arms with
  | nil =>
      rw [compileCaseArmsFuel_nil_eq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl⟩
      apply (compilerGoalsNamesAllowed_cons_iff external origin start
        (Goal.eq (Atom.sym "True") (Atom.sym "False")) []).2
      exact ⟨compilerGoalNamesAllowed_eq (by simp) (by simp), by simp⟩
  | cons arm more =>
      have armAndMore :=
        (compilerAtomsNamesAllowed_cons_iff external origin start arm more).mp
          armsAllowed
      cases arm with
      | var name =>
          rw [compileCaseArmsFuel_var_malformed_eq] at compiled
          contradiction
      | sym name =>
          rw [compileCaseArmsFuel_sym_malformed_eq] at compiled
          contradiction
      | gnd ground =>
          rw [compileCaseArmsFuel_gnd_malformed_eq] at compiled
          contradiction
      | expr items =>
          cases items with
          | nil =>
              rw [compileCaseArmsFuel_expr_nil_malformed_eq] at compiled
              contradiction
          | cons pattern tail =>
              cases tail with
              | nil =>
                  rw [compileCaseArmsFuel_expr_singleton_malformed_eq] at compiled
                  contradiction
              | cons body rest =>
                  cases rest with
                  | cons third rest =>
                      rw [compileCaseArmsFuel_expr_many_malformed_eq] at compiled
                      contradiction
                  | nil =>
                      have pairAllowed :=
                        compilerAtomExprPair_namesAllowed armAndMore.1
                      cases pattern with
                      | var name =>
                          rw [compileCaseArmsFuel_var_pair_eq] at compiled
                          exact compileCaseArmDo_generatedNames fuel ih external
                            origin env scrutinee result start (Atom.var name)
                            body more goals next originStart envAllowed
                            scrutineeAllowed resultAllowed pairAllowed.1
                            pairAllowed.2 armAndMore.2 compiled
                      | gnd ground =>
                          rw [compileCaseArmsFuel_gnd_pair_eq] at compiled
                          exact compileCaseArmDo_generatedNames fuel ih external
                            origin env scrutinee result start (Atom.gnd ground)
                            body more goals next originStart envAllowed
                            scrutineeAllowed resultAllowed pairAllowed.1
                            pairAllowed.2 armAndMore.2 compiled
                      | expr nested =>
                          rw [compileCaseArmsFuel_expr_pair_eq] at compiled
                          exact compileCaseArmDo_generatedNames fuel ih external
                            origin env scrutinee result start (Atom.expr nested)
                            body more goals next originStart envAllowed
                            scrutineeAllowed resultAllowed pairAllowed.1
                            pairAllowed.2 armAndMore.2 compiled
                      | sym name =>
                          by_cases empty : name = "Empty"
                          · subst name
                            rw [compileCaseArmsFuel_empty_eq] at compiled
                            exact ih.caseArms external origin env scrutinee result
                              start more goals next originStart envAllowed
                              scrutineeAllowed resultAllowed armAndMore.2 compiled
                          · rw [compileCaseArmsFuel_sym_pair_eq fuel env
                              scrutinee result start name empty] at compiled
                            exact compileCaseArmDo_generatedNames fuel ih external
                              origin env scrutinee result start (Atom.sym name)
                              body more goals next originStart envAllowed
                              scrutineeAllowed resultAllowed pairAllowed.1
                              pairAllowed.2 armAndMore.2 compiled

theorem rewriteTrace_namesAllowed {external : String → Prop}
    {origin limit : Nat} {arguments : List Atom} {rewritten : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (rewrites : rewriteTrace? arguments = some rewritten) :
    CompilerAtomNamesAllowed external origin limit rewritten := by
  unfold rewriteTrace? at rewrites
  split at rewrites
  · rcases Option.some.inj rewrites with rfl
    simpa using argumentsAllowed
  · contradiction

theorem rewriteUnique_namesAllowed {external : String → Prop}
    {origin limit : Nat} {operation : String} {arguments : List Atom}
    {rewritten : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (rewrites : rewriteUnique? operation arguments = some rewritten) :
    CompilerAtomNamesAllowed external origin limit rewritten := by
  unfold rewriteUnique? at rewrites
  split at rewrites
  · rcases Option.some.inj rewrites with rfl
    simpa using argumentsAllowed
  · contradiction

theorem rewriteBinaryStreamOp_namesAllowed {external : String → Prop}
    {origin limit : Nat} {operation : String} {arguments : List Atom}
    {rewritten : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (rewrites : rewriteBinaryStreamOp? operation arguments = some rewritten) :
    CompilerAtomNamesAllowed external origin limit rewritten := by
  unfold rewriteBinaryStreamOp? at rewrites
  split at rewrites
  · rcases Option.some.inj rewrites with rfl
    simpa using argumentsAllowed
  · contradiction

theorem rewriteStreamOp_namesAllowed {external : String → Prop}
    {origin limit : Nat} {head : String} {arguments : List Atom}
    {rewritten : Atom}
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin limit arguments)
    (rewrites : rewriteStreamOp? head arguments = some rewritten) :
    CompilerAtomNamesAllowed external origin limit rewritten := by
  unfold rewriteStreamOp? at rewrites
  unfold rewriteStreamOpForHead at rewrites
  by_cases trace : (head == "trace!") = true
  · simp only [trace, if_true] at rewrites
    exact rewriteTrace_namesAllowed argumentsAllowed rewrites
  · simp only [trace] at rewrites
    by_cases unique : (head == "unique") = true
    · simp only [unique, if_true] at rewrites
      exact rewriteUnique_namesAllowed argumentsAllowed rewrites
    · simp only [unique] at rewrites
      by_cases alphaUnique : (head == "alpha-unique") = true
      · simp only [alphaUnique, if_true] at rewrites
        exact rewriteUnique_namesAllowed argumentsAllowed rewrites
      · simp only [alphaUnique] at rewrites
        by_cases union : (head == "union") = true
        · simp only [union, if_true] at rewrites
          exact rewriteBinaryStreamOp_namesAllowed argumentsAllowed rewrites
        · simp only [union] at rewrites
          by_cases intersection : (head == "intersection") = true
          · simp only [intersection, if_true] at rewrites
            exact rewriteBinaryStreamOp_namesAllowed argumentsAllowed rewrites
          · simp only [intersection] at rewrites
            by_cases subtraction : (head == "subtraction") = true
            · simp only [subtraction, if_true] at rewrites
              exact rewriteBinaryStreamOp_namesAllowed argumentsAllowed rewrites
            · simp only [subtraction] at rewrites
              contradiction

theorem compileAppFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ external origin env start head arguments term goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start arguments →
      compileAppFuel (fuel + 1) env start head arguments =
          .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed compiled
  rw [compileAppFuel.eq_def] at compiled
  split at compiled
  · contradiction
  · simp_all only [Nat.succ.injEq]
    split at compiled
    · rename_i rewritten rewriteEq
      exact ih.expr external origin _ _ rewritten
        term goals next originStart envAllowed
        (rewriteStreamOp_namesAllowed argumentsAllowed rewriteEq) compiled
    · split at compiled
      · simp only [Bind.bind, Except.bind] at compiled
        split at compiled
        · contradiction
        · rename_i argsResult argsEq
          have argsCounter :=
            compileArgsAtFuel_counter_mono (compiled := argsEq)
          have argsNames := ih.argsAt external origin
            _ _ _ 0 _ argsResult.1 argsResult.2.1
            argsResult.2.2 originStart envAllowed argumentsAllowed argsEq
          simp only [fresh] at compiled
          rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
          have originArgs : origin ≤ argsResult.2.2 :=
            Nat.le_trans originStart argsCounter
          have codeAllowed : CompilerAtomNamesAllowed external origin
              (argsResult.2.2 + 2)
              (Atom.var (compilerGeneratedName argsResult.2.2)) := by
            simp only [compilerAtomNamesAllowed_var_iff]
            exact .generated originArgs (by omega)
          have resultAllowed : CompilerAtomNamesAllowed external origin
              (argsResult.2.2 + 2)
              (Atom.var (compilerGeneratedName (argsResult.2.2 + 1))) := by
            simp only [compilerAtomNamesAllowed_var_iff]
            exact .generated (Nat.le_trans originArgs (by omega)) (by omega)
          constructor
          · exact resultAllowed
          · apply (compilerGoalsNamesAllowed_append_iff external origin
              (argsResult.2.2 + 2) argsResult.2.1
              [Goal.call _ argsResult.1 (Atom.var _),
                Goal.evalg (Atom.var _) (Atom.var _)]).2
            constructor
            · exact argsNames.2.mono (by omega)
            · simp only [compilerGoalsNamesAllowed_cons_iff,
                compilerGoalsNamesAllowed_nil, and_true]
              constructor
              · exact compilerGoalNamesAllowed_call
                  (argsNames.1.mono (by omega)) codeAllowed _
              · exact compilerGoalNamesAllowed_evalg codeAllowed resultAllowed
      · exact ih.appCore external origin _ _ _ _ term goals next originStart
          envAllowed argumentsAllowed compiled

theorem compileAmbBranchesWith_generatedNames
    (compileExpr : Nat → Atom → CompileM (Atom × List Goal × Nat))
    (external : String → Prop) (origin start : Nat)
    (expressions : List Atom)
    (outcome : List (Atom × List Goal) × Nat)
    (originStart : origin ≤ start)
    (expressionsAllowed :
      CompilerAtomsNamesAllowed external origin start expressions)
    (compileMono : ∀ counter expression term goals next,
      compileExpr counter expression = .ok (term, goals, next) →
        counter ≤ next)
    (compileNames : ∀ counter expression term goals next,
      origin ≤ counter →
      CompilerAtomNamesAllowed external origin counter expression →
      compileExpr counter expression = .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals)
    (compiled :
      compileAmbBranchesWith compileExpr start expressions = .ok outcome) :
    CompilerBranchesNamesAllowed external origin outcome.2 outcome.1 := by
  unfold compileAmbBranchesWith at compiled
  have go : ∀ (remaining : List Atom)
      (accumulator final : List (Atom × List Goal) × Nat),
      origin ≤ accumulator.2 →
      CompilerBranchesNamesAllowed external origin accumulator.2
        accumulator.1 →
      CompilerAtomsNamesAllowed external origin accumulator.2 remaining →
      List.foldlM
          (fun (acc : List (Atom × List Goal) × Nat) expression => do
            let (term, goals, nextCounter) ← compileExpr acc.2 expression
            .ok (acc.1 ++ [(term, goals)], nextCounter))
          accumulator remaining = .ok final →
        CompilerBranchesNamesAllowed external origin final.2 final.1 := by
    intro remaining
    induction remaining with
    | nil =>
        intro accumulator final _ accumulatorAllowed _ folded
        rw [List.foldlM_nil] at folded
        rcases Except.ok.inj folded with rfl
        exact accumulatorAllowed
    | cons expression rest ih =>
        intro accumulator final originAccumulator accumulatorAllowed
          remainingAllowed folded
        have expressionAndRest :=
          (compilerAtomsNamesAllowed_cons_iff external origin accumulator.2
            expression rest).mp remainingAllowed
        rw [List.foldlM_cons] at folded
        simp only [Bind.bind, Except.bind] at folded
        split at folded
        · contradiction
        · rename_i branchResult branchEq
          cases expressionEq : compileExpr accumulator.2 expression with
          | error message =>
              simp only [expressionEq] at branchEq
              contradiction
          | ok expressionResult =>
              simp only [expressionEq] at branchEq
              rcases Except.ok.inj branchEq with rfl
              have branchCounter := compileMono _ _ _ _ _ expressionEq
              have branchNames := compileNames _ _ _ _ _ originAccumulator
                expressionAndRest.1 expressionEq
              apply ih (accumulator.1 ++ [(expressionResult.1,
                expressionResult.2.1)], expressionResult.2.2) final
              · exact Nat.le_trans originAccumulator branchCounter
              · apply (compilerBranchesNamesAllowed_append_iff external
                    origin expressionResult.2.2 accumulator.1
                    [(expressionResult.1, expressionResult.2.1)]).2
                constructor
                · exact accumulatorAllowed.mono branchCounter
                · simp only [compilerBranchesNamesAllowed_cons_iff,
                    compilerBranchesNamesAllowed_nil, and_true]
                  exact branchNames
              · exact expressionAndRest.2.mono branchCounter
              · exact folded
  exact go expressions ([], start) outcome originStart (by simp)
    expressionsAllowed compiled

theorem freshFold_generatedNames (external : String → Prop) (origin : Nat) :
    ∀ (indices : List Nat) (accumulator : List Atom × Nat),
      origin ≤ accumulator.2 →
      CompilerAtomsNamesAllowed external origin accumulator.2 accumulator.1 →
      CompilerAtomsNamesAllowed external origin
        (indices.foldl
          (fun acc _ =>
            (acc.1 ++ [Atom.var (compilerGeneratedName acc.2)], acc.2 + 1))
          accumulator).2
        (indices.foldl
          (fun acc _ =>
            (acc.1 ++ [Atom.var (compilerGeneratedName acc.2)], acc.2 + 1))
          accumulator).1 := by
  intro indices
  induction indices with
  | nil =>
      intro accumulator _ accumulatorAllowed
      exact accumulatorAllowed
  | cons _ rest ih =>
      intro accumulator originAccumulator accumulatorAllowed
      rw [List.foldl_cons]
      apply ih
      · omega
      · apply (compilerAtomsNamesAllowed_append_iff external origin
            (accumulator.2 + 1) accumulator.1
            [Atom.var (compilerGeneratedName accumulator.2)]).2
        constructor
        · exact accumulatorAllowed.mono (by omega)
        · simp only [compilerAtomsNamesAllowed_cons_iff,
            compilerAtomsNamesAllowed_nil, and_true,
            compilerAtomNamesAllowed_var_iff]
          exact .generated originAccumulator (by omega)

theorem CompilerAtomsNamesAllowed.dropLast {external : String → Prop}
    {origin limit : Nat} {atoms : List Atom}
    (allowed : CompilerAtomsNamesAllowed external origin limit atoms) :
    CompilerAtomsNamesAllowed external origin limit atoms.dropLast :=
  allowed.of_sublist (List.dropLast_sublist atoms)

theorem CompilerAtomsNamesAllowed.getLast?_eq_some
    {external : String → Prop} {origin limit : Nat} {atoms : List Atom}
    {last : Atom}
    (allowed : CompilerAtomsNamesAllowed external origin limit atoms)
    (lastEq : atoms.getLast? = some last) :
    CompilerAtomNamesAllowed external origin limit last := by
  rcases List.getLast?_eq_some_iff.mp lastEq with ⟨initial, rfl⟩
  exact allowed.atom_mem (by simp)

/-- The executable fresh-variant algorithm replaces every chain variable by
one compiler-owned name in the exact counter interval it consumes. -/
theorem freshenTypeChain_generatedNames
    (external : String → Prop) (origin start : Nat) (chain : List Atom)
    (originStart : origin ≤ start) :
    CompilerAtomsNamesAllowed external origin
      (freshenTypeChain start chain).2 (freshenTypeChain start chain).1 := by
  intro name member
  rcases CompilerTypeFreshening.freshenTypeChain_names_generated member with
    ⟨index, bound, rfl⟩
  apply CompilerNameAllowed.generated
  · omega
  · rw [CompilerTypeFreshening.freshenTypeChain_counter_eq]
    omega

/-- The typed branch's arity decision preserves the name classification of
both its branch template and its optional call goal. -/
theorem compileTypedCallOrPartial_generatedNames
    {external : String → Prop} {origin limit : Nat}
    (arities : List Nat) (result : Atom) (head : String)
    (terms : List Atom)
    (resultAllowed :
      CompilerAtomNamesAllowed external origin limit result)
    (termsAllowed :
      CompilerAtomsNamesAllowed external origin limit terms) :
    CompilerAtomNamesAllowed external origin limit
        (compileTypedCallOrPartial arities result head terms).1 ∧
      CompilerGoalsNamesAllowed external origin limit
        (compileTypedCallOrPartial arities result head terms).2 := by
  unfold compileTypedCallOrPartial
  split
  · simp only
    constructor
    · exact resultAllowed
    · simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      exact compilerGoalNamesAllowed_call termsAllowed resultAllowed head
  · exact ⟨partialValue_namesAllowed termsAllowed, by simp⟩

theorem compileTypedDispatchStepWith_generatedNames
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List Goal × Nat))
    (external : String → Prop) (origin : Nat) (result : Atom)
    (head : String) (arities : List Nat)
    (accumulator outcome : List (Atom × List Goal) × Nat)
    (chain : List Atom)
    (originAccumulator : origin ≤ accumulator.2)
    (accumulatorAllowed :
      CompilerBranchesNamesAllowed external origin accumulator.2
        accumulator.1)
    (resultAllowed :
      CompilerAtomNamesAllowed external origin accumulator.2 result)
    (typedMono : ∀ start types terms goals next,
      compileTypedArgs start types = .ok (terms, goals, next) →
        start ≤ next)
    (typedNames : ∀ start types terms goals next,
      origin ≤ start →
      CompilerAtomsNamesAllowed external origin start types →
      compileTypedArgs start types = .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals)
    (compiled :
      compileTypedDispatchStepWith compileTypedArgs result head arities
        accumulator chain = .ok outcome) :
    CompilerBranchesNamesAllowed external origin outcome.2 outcome.1 := by
  unfold compileTypedDispatchStepWith at compiled
  rcases freshEq : freshenTypeChain accumulator.2 chain with
    ⟨freshChain, freshCounter⟩
  simp only [freshEq] at compiled
  cases resultTypeEq : freshChain.getLast? with
  | none => simp [resultTypeEq] at compiled
  | some resultType =>
      simp only [resultTypeEq, Bind.bind, Except.bind] at compiled
      cases callbackEq : compileTypedArgs freshCounter freshChain.dropLast with
      | error message => simp [callbackEq] at compiled
      | ok callbackResult =>
          simp only [callbackEq] at compiled
          rcases callEq : compileTypedCallOrPartial arities result head
              callbackResult.1 with ⟨branchResult, callGoals⟩
          simp only [callEq] at compiled
          rcases Except.ok.inj compiled with rfl
          have freshCounterMono : accumulator.2 ≤ freshCounter := by
            simpa only [freshEq] using
              CompilerTypeFreshening.freshenTypeChain_counter_le
                accumulator.2 chain
          have originFresh : origin ≤ freshCounter :=
            Nat.le_trans originAccumulator freshCounterMono
          have freshChainAllowed :
              CompilerAtomsNamesAllowed external origin freshCounter
                freshChain := by
            have allowed := freshenTypeChain_generatedNames external origin
              accumulator.2 chain originAccumulator
            simpa only [freshEq] using allowed
          have parameterTypesAllowed :
              CompilerAtomsNamesAllowed external origin freshCounter
                freshChain.dropLast := freshChainAllowed.dropLast
          have callbackCounter := typedMono _ _ _ _ _ callbackEq
          have callbackNames := typedNames _ _ _ _ _ originFresh
            parameterTypesAllowed callbackEq
          have resultTypeAllowed :
              CompilerAtomNamesAllowed external origin freshCounter
                resultType := by
            apply freshChainAllowed.getLast?_eq_some
            exact resultTypeEq
          have callNamesRaw := compileTypedCallOrPartial_generatedNames
            arities result head callbackResult.1
            (resultAllowed.mono (Nat.le_trans freshCounterMono callbackCounter))
            callbackNames.1
          have callNames :
              CompilerAtomNamesAllowed external origin callbackResult.2.2
                  branchResult ∧
                CompilerGoalsNamesAllowed external origin callbackResult.2.2
                  callGoals := by
            simpa only [callEq] using callNamesRaw
          have checksAllowed := compileResultTypeCheck_generatedNames external
            origin callbackResult.2.2 branchResult resultType
            (Nat.le_trans originFresh callbackCounter)
            callNames.1
            (resultTypeAllowed.mono callbackCounter)
          have checksCounter := compileResultTypeCheck_counter_le branchResult
            resultType callbackResult.2.2
          apply (compilerBranchesNamesAllowed_append_iff external origin
              (compileResultTypeCheck branchResult resultType
                callbackResult.2.2).2
              accumulator.1
              [(branchResult, callbackResult.2.1 ++ callGoals ++
                (compileResultTypeCheck branchResult resultType
                  callbackResult.2.2).1)]).2
          constructor
          · exact accumulatorAllowed.mono <|
              Nat.le_trans freshCounterMono <|
                Nat.le_trans callbackCounter checksCounter
          · simp only [compilerBranchesNamesAllowed_cons_iff,
              compilerBranchesNamesAllowed_nil, and_true]
            constructor
            · exact callNames.1.mono checksCounter
            · rw [List.append_assoc]
              apply (compilerGoalsNamesAllowed_append_iff external origin
                  (compileResultTypeCheck branchResult resultType
                    callbackResult.2.2).2
                  callbackResult.2.1
                  (callGoals ++
                    (compileResultTypeCheck branchResult resultType
                      callbackResult.2.2).1)).2
              constructor
              · exact callbackNames.2.mono checksCounter
              · apply (compilerGoalsNamesAllowed_append_iff external origin
                    (compileResultTypeCheck branchResult resultType
                      callbackResult.2.2).2
                    callGoals
                    (compileResultTypeCheck branchResult resultType
                      callbackResult.2.2).1).2
                exact ⟨callNames.2.mono checksCounter, checksAllowed⟩

theorem compileTypedDispatchFoldWith_generatedNames
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List Goal × Nat))
    (external : String → Prop) (origin start : Nat) (result : Atom)
    (head : String) (arities : List Nat) (chains : List (List Atom))
    (outcome : List (Atom × List Goal) × Nat)
    (originStart : origin ≤ start)
    (resultAllowed : CompilerAtomNamesAllowed external origin start result)
    (typedMono : ∀ counter types terms goals next,
      compileTypedArgs counter types = .ok (terms, goals, next) →
        counter ≤ next)
    (typedNames : ∀ counter types terms goals next,
      origin ≤ counter →
      CompilerAtomsNamesAllowed external origin counter types →
      compileTypedArgs counter types = .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals)
    (compiled :
      chains.foldlM
        (compileTypedDispatchStepWith compileTypedArgs result head arities)
        ([], start) = .ok outcome) :
    CompilerBranchesNamesAllowed external origin outcome.2 outcome.1 := by
  have go : ∀ (remaining : List (List Atom))
      (accumulator final : List (Atom × List Goal) × Nat),
      origin ≤ accumulator.2 →
      CompilerBranchesNamesAllowed external origin accumulator.2
        accumulator.1 →
      CompilerAtomNamesAllowed external origin accumulator.2 result →
      remaining.foldlM
          (compileTypedDispatchStepWith compileTypedArgs result head arities)
          accumulator = .ok final →
        CompilerBranchesNamesAllowed external origin final.2 final.1 := by
    intro remaining
    induction remaining with
    | nil =>
        intro accumulator final _ accumulatorAllowed _ folded
        rw [List.foldlM_nil] at folded
        rcases Except.ok.inj folded with rfl
        exact accumulatorAllowed
    | cons chain rest ih =>
        intro accumulator final originAccumulator accumulatorAllowed
          resultAtAccumulator folded
        rw [List.foldlM_cons] at folded
        cases stepEq : compileTypedDispatchStepWith compileTypedArgs result
            head arities accumulator chain with
        | error message =>
            simp only [stepEq, Bind.bind, Except.bind] at folded
            contradiction
        | ok stepOutcome =>
            simp only [stepEq, Bind.bind, Except.bind] at folded
            have stepCounter := typedDispatchStep_counter compileTypedArgs
              typedMono result head arities accumulator chain stepOutcome
              stepEq
            have stepNames := compileTypedDispatchStepWith_generatedNames
              compileTypedArgs external origin result head arities
              accumulator stepOutcome chain originAccumulator
              accumulatorAllowed resultAtAccumulator typedMono typedNames stepEq
            apply ih stepOutcome final
            · exact Nat.le_trans originAccumulator stepCounter
            · exact stepNames
            · exact resultAtAccumulator.mono stepCounter
            · exact folded
  apply go chains ([], start) outcome originStart (by simp) resultAllowed
  exact compiled

theorem compileAppDefaultWith_generatedNames
    (compileArgs : Nat → CompileM (List Atom × List Goal × Nat))
    (compileTypedArgs : Nat → List Atom →
      CompileM (List Atom × List Goal × Nat))
    (compileList : Nat → CompileM (List Atom × List Goal × Nat))
    (external : String → Prop) (origin : Nat)
    (argsMono : ∀ start terms goals next,
      compileArgs start = .ok (terms, goals, next) → start ≤ next)
    (typedMono : ∀ start types terms goals next,
      compileTypedArgs start types = .ok (terms, goals, next) →
        start ≤ next)
    (listMono : ∀ start terms goals next,
      compileList start = .ok (terms, goals, next) → start ≤ next)
    (argsNames : ∀ start terms goals next,
      origin ≤ start →
      compileArgs start = .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals)
    (typedNames : ∀ start types terms goals next,
      origin ≤ start →
      CompilerAtomsNamesAllowed external origin start types →
      compileTypedArgs start types = .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals)
    (listNames : ∀ start terms goals next,
      origin ≤ start →
      compileList start = .ok (terms, goals, next) →
        CompilerAtomsNamesAllowed external origin next terms ∧
        CompilerGoalsNamesAllowed external origin next goals) :
    ∀ env start head arguments term goals next,
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      compileAppDefaultWith compileArgs compileTypedArgs compileList
          env start head arguments = .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro env start head arguments term goals next originStart envAllowed compiled
  unfold compileAppDefaultWith at compiled
  by_cases prolog : env.prologFunctions.contains head = true
  · simp only [prolog, if_true, Bind.bind, Except.bind] at compiled
    cases argsEq : compileArgs start with
    | error message =>
        simp only [argsEq] at compiled
        contradiction
    | ok argsResult =>
        simp only [argsEq, fresh] at compiled
        rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
        have argsCounter := argsMono _ _ _ _ argsEq
        have compiledNames := argsNames _ _ _ _ originStart argsEq
        have resultAllowed : CompilerAtomNamesAllowed external origin
            (argsResult.2.2 + 2)
            (Atom.var (compilerGeneratedName argsResult.2.2)) := by
          simp only [compilerAtomNamesAllowed_var_iff]
          exact .generated (Nat.le_trans originStart argsCounter) (by omega)
        have okAllowed : CompilerAtomNamesAllowed external origin
            (argsResult.2.2 + 2)
            (Atom.var (compilerGeneratedName (argsResult.2.2 + 1))) := by
          simp only [compilerAtomNamesAllowed_var_iff]
          exact .generated
            (Nat.le_trans (Nat.le_trans originStart argsCounter)
              (Nat.le_succ argsResult.2.2))
            (by omega)
        constructor
        · exact resultAllowed
        · apply (compilerGoalsNamesAllowed_append_iff external origin
              (argsResult.2.2 + 2) argsResult.2.1
              [Goal.bin "translatePredicate"
                [chainify
                  (Atom.expr (Atom.sym head :: argsResult.1 ++
                    [Atom.var (compilerGeneratedName argsResult.2.2)]))]
                (Atom.var (compilerGeneratedName
                  (argsResult.2.2 + 1)))]).2
          constructor
          · exact compiledNames.2.mono
              (Nat.le_add_right argsResult.2.2 2)
          · simp only [compilerGoalsNamesAllowed_cons_iff,
                compilerGoalsNamesAllowed_nil, and_true]
            apply compilerGoalNamesAllowed_bin
            · simp only [compilerAtomsNamesAllowed_cons_iff,
                  compilerAtomsNamesAllowed_nil, and_true]
              apply chainify_namesAllowed
              apply (compilerAtomNamesAllowed_expr_iff external origin
                (argsResult.2.2 + 2)
                (Atom.sym head :: argsResult.1 ++
                  [Atom.var (compilerGeneratedName argsResult.2.2)])).2
              apply (compilerAtomsNamesAllowed_cons_iff external origin
                (argsResult.2.2 + 2) (Atom.sym head)
                (argsResult.1 ++
                  [Atom.var (compilerGeneratedName argsResult.2.2)])).2
              constructor
              · simp
              · apply (compilerAtomsNamesAllowed_append_iff external origin
                    (argsResult.2.2 + 2) argsResult.1
                    [Atom.var (compilerGeneratedName argsResult.2.2)]).2
                exact ⟨compiledNames.1.mono
                  (Nat.le_add_right argsResult.2.2 2), by simpa using
                    resultAllowed⟩
            · exact okAllowed
  · have prologFalse : env.prologFunctions.contains head = false :=
      Bool.eq_false_iff.mpr prolog
    simp only [prologFalse, Bool.false_eq_true, if_false] at compiled
    by_cases defined : env.defined.contains head = true
    · simp only [defined, if_true] at compiled
      have shortageFalse :
          typedDispatchInputShortage (env.typeChains head)
            arguments.length = false := by
        cases shortage : typedDispatchInputShortage (env.typeChains head)
            arguments.length with
        | false => rfl
        | true =>
            simp only [shortage, if_true] at compiled
            cases compiled
      simp only [shortageFalse, Bool.false_eq_true, if_false] at compiled
      by_cases typed : shouldUseTypedDispatch (env.typeChains head) = true
      · simp only [typed, if_true, fresh, Bind.bind, Except.bind] at compiled
        let resultAtom := Atom.var (compilerGeneratedName start)
        let firstCounter := start + 1
        cases foldEq : (env.typeChains head).foldlM
            (compileTypedDispatchStepWith compileTypedArgs resultAtom head
              (env.arities head)) ([], firstCounter) with
        | error message =>
            simp only [resultAtom, firstCounter, compilerGeneratedName] at foldEq
            rw [foldEq] at compiled
            contradiction
        | ok foldResult =>
            simp only [resultAtom, firstCounter, compilerGeneratedName] at foldEq
            rw [foldEq] at compiled
            have resultAtFirst : CompilerAtomNamesAllowed external origin
                firstCounter resultAtom := by
              simp only [resultAtom, firstCounter,
                compilerAtomNamesAllowed_var_iff]
              exact .generated originStart (by omega)
            have foldNames := compileTypedDispatchFoldWith_generatedNames
              compileTypedArgs external origin firstCounter resultAtom head
              (env.arities head) (env.typeChains head) foldResult
              (Nat.le_trans originStart (by simp [firstCounter])) resultAtFirst
              typedMono typedNames foldEq
            have stepMono : ∀ accumulator chain outcome,
                compileTypedDispatchStepWith compileTypedArgs resultAtom head
                    (env.arities head) accumulator chain = .ok outcome →
                  accumulator.2 ≤ outcome.2 := by
              intro accumulator chain outcome stepCompiled
              exact typedDispatchStep_counter compileTypedArgs typedMono
                resultAtom head (env.arities head) accumulator chain outcome
                stepCompiled
            have foldCounter := foldlM_counter_mono _ stepMono
              (env.typeChains head) ([], firstCounter) foldResult foldEq
            by_cases branchesEmpty : foldResult.1.isEmpty = true
            · simp only [branchesEmpty, if_true] at compiled
              cases argsEq : compileArgs start with
              | error message =>
                  simp only [argsEq] at compiled
                  contradiction
              | ok argsResult =>
                  simp only [argsEq] at compiled
                  have argsCounter := argsMono _ _ _ _ argsEq
                  have compiledNames := argsNames _ _ _ _ originStart argsEq
                  by_cases arity :
                      (env.arities head).contains argsResult.1.length = true
                  · simp only [arity, if_true] at compiled
                    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                    have finalResult : CompilerAtomNamesAllowed external origin
                        (argsResult.2.2 + 1)
                        (Atom.var (compilerGeneratedName argsResult.2.2)) := by
                      simp only [compilerAtomNamesAllowed_var_iff]
                      exact .generated (Nat.le_trans originStart argsCounter)
                        (by omega)
                    constructor
                    · exact finalResult
                    · apply (compilerGoalsNamesAllowed_append_iff external
                          origin (argsResult.2.2 + 1) argsResult.2.1
                          [Goal.call head argsResult.1
                            (Atom.var
                              (compilerGeneratedName argsResult.2.2))]).2
                      exact ⟨compiledNames.2.mono
                          (Nat.le_succ argsResult.2.2), by
                        simp only [compilerGoalsNamesAllowed_cons_iff,
                          compilerGoalsNamesAllowed_nil, and_true]
                        exact compilerGoalNamesAllowed_call
                          (compiledNames.1.mono
                            (Nat.le_succ argsResult.2.2)) finalResult head⟩
                  · have arityFalse :
                        (env.arities head).contains argsResult.1.length = false :=
                      Bool.eq_false_iff.mpr arity
                    simp only [arityFalse, Bool.false_eq_true, if_false] at compiled
                    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                    exact ⟨partialValue_namesAllowed compiledNames.1,
                      compiledNames.2⟩
            · have branchesNonempty : foldResult.1.isEmpty = false :=
                Bool.eq_false_iff.mpr branchesEmpty
              simp only [branchesNonempty, Bool.false_eq_true, if_false]
                at compiled
              cases resolutionEq : resolveTypedSharedResult resultAtom
                  foldResult.1 with
              | error message =>
                  simp only [resultAtom, compilerGeneratedName] at resolutionEq
                  simp only [resolutionEq] at compiled
                  contradiction
              | ok resolved =>
                  simp only [resultAtom, compilerGeneratedName] at resolutionEq
                  simp only [resolutionEq] at compiled
                  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                  have resolvedNames := resolveTypedSharedResult_namesAllowed
                    (resultAtFirst.mono foldCounter) foldNames resolutionEq
                  constructor
                  · exact resolvedNames.1
                  · simp only [compilerGoalsNamesAllowed_cons_iff,
                        compilerGoalsNamesAllowed_nil, and_true]
                    exact compilerGoalNamesAllowed_amb resolvedNames.2
                      resolvedNames.1
      · have typedFalse :
            shouldUseTypedDispatch (env.typeChains head) = false :=
          Bool.eq_false_iff.mpr typed
        simp only [typedFalse, Bool.false_eq_true, if_false, Bind.bind,
          Except.bind] at compiled
        cases argsEq : compileArgs start with
        | error message =>
            simp only [argsEq] at compiled
            contradiction
        | ok argsResult =>
            simp only [argsEq] at compiled
            have argsCounter := argsMono _ _ _ _ argsEq
            have compiledNames := argsNames _ _ _ _ originStart argsEq
            by_cases arity :
                (env.arities head).contains argsResult.1.length = true
            · simp only [arity, if_true, fresh] at compiled
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              have resultAllowed : CompilerAtomNamesAllowed external origin
                  (argsResult.2.2 + 1)
                  (Atom.var (compilerGeneratedName argsResult.2.2)) := by
                simp only [compilerAtomNamesAllowed_var_iff]
                exact .generated (Nat.le_trans originStart argsCounter) (by omega)
              constructor
              · exact resultAllowed
              · apply (compilerGoalsNamesAllowed_append_iff external origin
                    (argsResult.2.2 + 1) argsResult.2.1
                    [Goal.call head argsResult.1
                      (Atom.var (compilerGeneratedName argsResult.2.2))]).2
                exact ⟨compiledNames.2.mono
                    (Nat.le_succ argsResult.2.2), by
                  simp only [compilerGoalsNamesAllowed_cons_iff,
                    compilerGoalsNamesAllowed_nil, and_true]
                  exact compilerGoalNamesAllowed_call
                    (compiledNames.1.mono
                      (Nat.le_succ argsResult.2.2)) resultAllowed head⟩
            · have arityFalse :
                  (env.arities head).contains argsResult.1.length = false :=
                Bool.eq_false_iff.mpr arity
              simp only [arityFalse, Bool.false_eq_true, if_false] at compiled
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              exact ⟨partialValue_namesAllowed compiledNames.1,
                compiledNames.2⟩
    · have definedFalse : env.defined.contains head = false :=
        Bool.eq_false_iff.mpr defined
      simp only [definedFalse, Bool.false_eq_true, if_false] at compiled
      by_cases binary : env.isBin head = true
      · simp only [binary, if_true, Bind.bind, Except.bind] at compiled
        cases argsEq : compileArgs start with
        | error message =>
            simp only [argsEq] at compiled
            contradiction
        | ok argsResult =>
            simp only [argsEq] at compiled
            have argsCounter := argsMono _ _ _ _ argsEq
            have compiledNames := argsNames _ _ _ _ originStart argsEq
            cases arityEq : compileBinArity head with
            | none =>
                simp only [arityEq, fresh] at compiled
                rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                have resultAllowed : CompilerAtomNamesAllowed external origin
                    (argsResult.2.2 + 1)
                    (Atom.var (compilerGeneratedName argsResult.2.2)) := by
                  simp only [compilerAtomNamesAllowed_var_iff]
                  exact .generated (Nat.le_trans originStart argsCounter) (by omega)
                constructor
                · exact resultAllowed
                · apply (compilerGoalsNamesAllowed_append_iff external origin
                      (argsResult.2.2 + 1) argsResult.2.1
                      [Goal.bin head argsResult.1
                        (Atom.var (compilerGeneratedName argsResult.2.2))]).2
                  exact ⟨compiledNames.2.mono
                      (Nat.le_succ argsResult.2.2), by
                    simp only [compilerGoalsNamesAllowed_cons_iff,
                      compilerGoalsNamesAllowed_nil, and_true]
                    exact compilerGoalNamesAllowed_bin
                      (compiledNames.1.mono
                        (Nat.le_succ argsResult.2.2)) resultAllowed head⟩
            | some arity =>
                simp only [arityEq] at compiled
                by_cases arityMatch : (arity == argsResult.1.length) = true
                · simp only [arityMatch, if_true, fresh] at compiled
                  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                  have resultAllowed : CompilerAtomNamesAllowed external origin
                      (argsResult.2.2 + 1)
                      (Atom.var (compilerGeneratedName argsResult.2.2)) := by
                    simp only [compilerAtomNamesAllowed_var_iff]
                    exact .generated (Nat.le_trans originStart argsCounter)
                      (by omega)
                  constructor
                  · exact resultAllowed
                  · apply (compilerGoalsNamesAllowed_append_iff external origin
                        (argsResult.2.2 + 1) argsResult.2.1
                        [Goal.bin head argsResult.1
                          (Atom.var (compilerGeneratedName argsResult.2.2))]).2
                    exact ⟨compiledNames.2.mono
                        (Nat.le_succ argsResult.2.2), by
                      simp only [compilerGoalsNamesAllowed_cons_iff,
                        compilerGoalsNamesAllowed_nil, and_true]
                      exact compilerGoalNamesAllowed_bin
                        (compiledNames.1.mono
                          (Nat.le_succ argsResult.2.2)) resultAllowed head⟩
                · have arityMismatch :
                      (arity == argsResult.1.length) = false :=
                    Bool.eq_false_iff.mpr arityMatch
                  simp only [arityMismatch, Bool.false_eq_true, if_false] at compiled
                  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                  exact ⟨partialValue_namesAllowed compiledNames.1,
                    compiledNames.2⟩
      · have binaryFalse : env.isBin head = false :=
          Bool.eq_false_iff.mpr binary
        simp only [binaryFalse, Bool.false_eq_true, if_false, Bind.bind,
          Except.bind] at compiled
        cases listEq : compileList start with
        | error message =>
            simp only [listEq] at compiled
            contradiction
        | ok listResult =>
            simp only [listEq] at compiled
            have listCounter := listMono _ _ _ _ listEq
            have compiledNames := listNames _ _ _ _ originStart listEq
            by_cases dynamic :
                (env.dynamicUnknown && dynamicUnknownHead head) = true
            · simp only [dynamic, if_true, fresh] at compiled
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              have resultAllowed : CompilerAtomNamesAllowed external origin
                  (listResult.2.2 + 1)
                  (Atom.var (compilerGeneratedName listResult.2.2)) := by
                simp only [compilerAtomNamesAllowed_var_iff]
                exact .generated (Nat.le_trans originStart listCounter) (by omega)
              constructor
              · exact resultAllowed
              · apply (compilerGoalsNamesAllowed_append_iff external origin
                    (listResult.2.2 + 1) listResult.2.1
                    [Goal.callDyn (Atom.sym head) listResult.1
                      (Atom.var (compilerGeneratedName listResult.2.2))]).2
                exact ⟨compiledNames.2.mono
                    (Nat.le_succ listResult.2.2), by
                  simp only [compilerGoalsNamesAllowed_cons_iff,
                    compilerGoalsNamesAllowed_nil, and_true]
                  exact compilerGoalNamesAllowed_callDyn (by simp)
                    (compiledNames.1.mono
                      (Nat.le_succ listResult.2.2)) resultAllowed⟩
            · have dynamicFalse :
                  (env.dynamicUnknown && dynamicUnknownHead head) = false :=
                Bool.eq_false_iff.mpr dynamic
              simp only [dynamicFalse, Bool.false_eq_true, if_false] at compiled
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              constructor
              · apply chainOf_namesAllowed
                apply (compilerAtomsNamesAllowed_cons_iff external origin
                  listResult.2.2 (Atom.sym head) listResult.1).2
                exact ⟨by simp, compiledNames.1⟩
              · exact compiledNames.2

theorem compileAppDefaultWith_compiler_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (head : String) (arguments : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin start arguments)
    (compiled :
      compileAppDefaultWith
          (fun counter =>
            compileArgsAtFuel fuel env counter head 0 arguments)
          (fun counter parameterTypes =>
            compileTypedArgsFuel fuel env counter arguments parameterTypes)
          (fun counter => compileListFuel fuel env counter arguments)
          env start head arguments = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  let nestedExternal := CompilerNameAllowed external origin start
  have nestedEnv : CompilerEnvNamesAllowed nestedExternal start start env := by
    exact envAllowed.nest
  have nestedArguments :
      CompilerAtomsNamesAllowed nestedExternal start start arguments := by
    exact argumentsAllowed.nest
  have defaultNames := compileAppDefaultWith_generatedNames
    (fun counter => compileArgsAtFuel fuel env counter head 0 arguments)
    (fun counter parameterTypes =>
      compileTypedArgsFuel fuel env counter arguments parameterTypes)
    (fun counter => compileListFuel fuel env counter arguments)
    nestedExternal start
    (by
      intro counter terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).argsAt env counter head 0 arguments
        terms argumentGoals nextCounter argumentCompilation)
    (by
      intro counter types terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).typedArgs env counter arguments types
        terms argumentGoals nextCounter argumentCompilation)
    (by
      intro counter terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).list env counter arguments terms
        argumentGoals nextCounter argumentCompilation)
    (by
      intro counter terms argumentGoals nextCounter startCounter
        argumentCompilation
      exact ih.argsAt nestedExternal start env counter head 0 arguments
        terms argumentGoals nextCounter startCounter
        (nestedEnv.mono startCounter) (nestedArguments.mono startCounter)
        argumentCompilation)
    (by
      intro counter types terms argumentGoals nextCounter startCounter
        typesAllowed argumentCompilation
      exact ih.typedArgs nestedExternal start env counter arguments types
        terms argumentGoals nextCounter startCounter
        (nestedEnv.mono startCounter) (nestedArguments.mono startCounter)
        typesAllowed argumentCompilation)
    (by
      intro counter terms argumentGoals nextCounter startCounter
        argumentCompilation
      exact ih.list nestedExternal start env counter arguments terms
        argumentGoals nextCounter startCounter
        (nestedEnv.mono startCounter) (nestedArguments.mono startCounter)
        argumentCompilation)
    env start head arguments term goals next (Nat.le_refl start) nestedEnv
    compiled
  have defaultCounter := compileAppDefaultWith_counter
    (fun counter => compileArgsAtFuel fuel env counter head 0 arguments)
    (fun counter parameterTypes =>
      compileTypedArgsFuel fuel env counter arguments parameterTypes)
    (fun counter => compileListFuel fuel env counter arguments)
    (by
      intro counter terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).argsAt env counter head 0 arguments
        terms argumentGoals nextCounter argumentCompilation)
    (by
      intro counter types terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).typedArgs env counter arguments types
        terms argumentGoals nextCounter argumentCompilation)
    (by
      intro counter terms argumentGoals nextCounter argumentCompilation
      exact (compilerCounterAt fuel).list env counter arguments terms
        argumentGoals nextCounter argumentCompilation)
    env start head arguments term goals next compiled
  constructor
  · exact CompilerNamesAllowed.flatten originStart defaultCounter
      defaultNames.1
  · exact CompilerNamesAllowed.flatten originStart defaultCounter
      defaultNames.2

private theorem bindCheckedCompileResult {Value Answer : Type}
    {observed : Value → List Goal → Nat → Prop} {C : Prop}
    {operation : CompileM (Value × List Goal × Nat)}
    {resume : Value × List Goal × Nat → CompileM Answer} {answer : Answer}
    (compiled : (operation >>= resume) = .ok answer)
    (checked : ∀ value goals next, operation = .ok (value, goals, next) →
      observed value goals next)
    (finish : ∀ value goals next, observed value goals next →
      resume (value, goals, next) = .ok answer → C) : C := by
  cases result : operation with
  | error message => simp [result, Bind.bind, Except.bind] at compiled
  | ok output =>
      rcases output with ⟨value, goals, next⟩
      exact finish value goals next (checked value goals next result)
        (by simpa only [result, Bind.bind, Except.bind] using compiled)

private theorem CompilerGeneratedNamesAt.bindExpr {fuel : Nat}
    (ih : CompilerGeneratedNamesAt fuel)
    {external : String → Prop} {origin start : Nat} {env : CEnv} {source : Atom}
    {Answer : Type} {C : Prop}
    {resume : Atom × List Goal × Nat → CompileM Answer} {answer : Answer}
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled : (compileExprFuel fuel env start source >>= resume) = .ok answer)
    (finish : ∀ term goals next, start ≤ next →
      CompilerAtomNamesAllowed external origin next term →
      CompilerGoalsNamesAllowed external origin next goals →
      resume (term, goals, next) = .ok answer → C) : C :=
  bindCheckedCompileResult
    (observed := fun term goals next => start ≤ next ∧
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals)
    compiled
    (fun term goals next result =>
      ⟨compileExprFuel_counter_mono fuel env start source term goals next result,
       ih.expr external origin env start source term goals next originStart
         envAllowed sourceAllowed result⟩)
    (fun term goals next checked => finish term goals next checked.1 checked.2.1 checked.2.2)


theorem compileExprThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (source : Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (buildGoals : Atom → List Goal → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (buildAllowed : ∀ limit compiledTerm compiledGoals result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit compiledTerm →
      CompilerGoalsNamesAllowed external origin limit compiledGoals →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals compiledTerm compiledGoals result))
    (compiled :
      (do
        let (compiledTerm, compiledGoals, middle) ←
          compileExprFuel fuel env start source
        let (result, finalCounter) := fresh middle
        .ok (result, buildGoals compiledTerm compiledGoals result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed sourceAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  have allocatedNames2 := compilerFreshAtom_namesAllowed external origin
    counter1 (originStart.trans advance1)
  simp only [fresh] at remaining1
  have reached2 := advance1.trans (Nat.le_succ counter1)
  rcases Except.ok.inj remaining1 with ⟨rfl, rfl, rfl⟩
  exact ⟨allocatedNames2, buildAllowed _ _ _ _ reached2
    (valueNames1.mono (Nat.le_succ counter1)) (goalsNames1.mono (Nat.le_succ counter1))
    allocatedNames2⟩

theorem compileTwoExprThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (first second : Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (buildGoals : Atom → List Goal → Atom → List Goal → Atom →
      List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstAllowed : CompilerAtomNamesAllowed external origin start first)
    (secondAllowed : CompilerAtomNamesAllowed external origin start second)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals result))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start first
        let (secondTerm, secondGoals, middleSecond) ←
          compileExprFuel fuel env middleFirst second
        let (result, finalCounter) := fresh middleSecond
        .ok (result,
          buildGoals firstTerm firstGoals secondTerm secondGoals result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  have allocatedNames3 := compilerFreshAtom_namesAllowed external origin
    counter2 (originStart.trans reached2)
  simp only [fresh] at remaining2
  have reached3 := reached2.trans (Nat.le_succ counter2)
  rcases Except.ok.inj remaining2 with ⟨rfl, rfl, rfl⟩
  have later1 := advance2.trans (Nat.le_succ counter2)
  exact ⟨allocatedNames3, buildAllowed _ _ _ _ _ _ reached3
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (valueNames2.mono (Nat.le_succ counter2)) (goalsNames2.mono (Nat.le_succ counter2))
    allocatedNames3⟩

theorem compileTwoExpr_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (first second : Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (buildTerm : Atom → Atom → Atom)
    (buildGoals : Atom → List Goal → Atom → List Goal → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstAllowed : CompilerAtomNamesAllowed external origin start first)
    (secondAllowed : CompilerAtomNamesAllowed external origin start second)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
        CompilerAtomNamesAllowed external origin limit
            (buildTerm firstTerm secondTerm) ∧
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start first
        let (secondTerm, secondGoals, finalCounter) ←
          compileExprFuel fuel env middleFirst second
        .ok (buildTerm firstTerm secondTerm,
          buildGoals firstTerm firstGoals secondTerm secondGoals,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  rcases Except.ok.inj remaining2 with ⟨rfl, rfl, rfl⟩
  exact buildAllowed _ _ _ _ _ reached2
    (valueNames1.mono advance2) (goalsNames1.mono advance2)
    valueNames2 goalsNames2

theorem compileThreeExprThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (first second third : Atom) (term : Atom) (goals : List Goal)
    (next : Nat)
    (buildGoals : Atom → List Goal → Atom → List Goal → Atom →
      List Goal → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstAllowed : CompilerAtomNamesAllowed external origin start first)
    (secondAllowed : CompilerAtomNamesAllowed external origin start second)
    (thirdAllowed : CompilerAtomNamesAllowed external origin start third)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals
        thirdTerm thirdGoals result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit thirdTerm →
      CompilerGoalsNamesAllowed external origin limit thirdGoals →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals result))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start first
        let (secondTerm, secondGoals, middleSecond) ←
          compileExprFuel fuel env middleFirst second
        let (thirdTerm, thirdGoals, middleThird) ←
          compileExprFuel fuel env middleSecond third
        let (result, finalCounter) := fresh middleThird
        .ok (result,
          buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  refine ih.bindExpr (start := counter2) (originStart.trans reached2)
    (envAllowed.mono reached2) (thirdAllowed.mono reached2) remaining2 ?_
  intro value3 goals3 counter3 advance3 valueNames3 goalsNames3 remaining3
  have reached3 := reached2.trans advance3
  have allocatedNames4 := compilerFreshAtom_namesAllowed external origin
    counter3 (originStart.trans reached3)
  simp only [fresh] at remaining3
  have reached4 := reached3.trans (Nat.le_succ counter3)
  rcases Except.ok.inj remaining3 with ⟨rfl, rfl, rfl⟩
  have later2 := advance3.trans (Nat.le_succ counter3)
  have later1 := advance2.trans later2
  exact ⟨allocatedNames4, buildAllowed _ _ _ _ _ _ _ _ reached4
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (valueNames2.mono later2) (goalsNames2.mono later2)
    (valueNames3.mono (Nat.le_succ counter3)) (goalsNames3.mono (Nat.le_succ counter3))
    allocatedNames4⟩

private theorem compileFourExprThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (first second third fourth : Atom) (term : Atom) (goals : List Goal)
    (next : Nat)
    (buildGoals : Atom → List Goal → Atom → List Goal → Atom →
      List Goal → Atom → List Goal → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstAllowed : CompilerAtomNamesAllowed external origin start first)
    (secondAllowed : CompilerAtomNamesAllowed external origin start second)
    (thirdAllowed : CompilerAtomNamesAllowed external origin start third)
    (fourthAllowed : CompilerAtomNamesAllowed external origin start fourth)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals
        thirdTerm thirdGoals fourthTerm fourthGoals result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit thirdTerm →
      CompilerGoalsNamesAllowed external origin limit thirdGoals →
      CompilerAtomNamesAllowed external origin limit fourthTerm →
      CompilerGoalsNamesAllowed external origin limit fourthGoals →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals fourthTerm fourthGoals result))
    (compiled :
      (do
        let (firstTerm, firstGoals, afterFirst) ←
          compileExprFuel fuel env start first
        let (secondTerm, secondGoals, afterSecond) ←
          compileExprFuel fuel env afterFirst second
        let (thirdTerm, thirdGoals, afterThird) ←
          compileExprFuel fuel env afterSecond third
        let (fourthTerm, fourthGoals, afterFourth) ←
          compileExprFuel fuel env afterThird fourth
        let (result, finalCounter) := fresh afterFourth
        .ok (result,
          buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals fourthTerm fourthGoals result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  refine ih.bindExpr (start := counter2) (originStart.trans reached2)
    (envAllowed.mono reached2) (thirdAllowed.mono reached2) remaining2 ?_
  intro value3 goals3 counter3 advance3 valueNames3 goalsNames3 remaining3
  have reached3 := reached2.trans advance3
  refine ih.bindExpr (start := counter3) (originStart.trans reached3)
    (envAllowed.mono reached3) (fourthAllowed.mono reached3) remaining3 ?_
  intro value4 goals4 counter4 advance4 valueNames4 goalsNames4 remaining4
  have reached4 := reached3.trans advance4
  have allocatedNames5 := compilerFreshAtom_namesAllowed external origin
    counter4 (originStart.trans reached4)
  simp only [fresh] at remaining4
  have reached5 := reached4.trans (Nat.le_succ counter4)
  rcases Except.ok.inj remaining4 with ⟨rfl, rfl, rfl⟩
  have later3 := advance4.trans (Nat.le_succ counter4)
  have later2 := advance3.trans later3
  have later1 := advance2.trans later2
  exact ⟨allocatedNames5, buildAllowed _ _ _ _ _ _ _ _ _ _ reached5
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (valueNames2.mono later2) (goalsNames2.mono later2)
    (valueNames3.mono later3) (goalsNames3.mono later3)
    (valueNames4.mono (Nat.le_succ counter4)) (goalsNames4.mono (Nat.le_succ counter4))
    allocatedNames5⟩

theorem compileThreeExpr_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (first second third : Atom) (term : Atom) (goals : List Goal)
    (next : Nat)
    (buildTerm : Atom → Atom → Atom → Atom)
    (buildGoals : Atom → List Goal → Atom → List Goal → Atom →
      List Goal → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstAllowed : CompilerAtomNamesAllowed external origin start first)
    (secondAllowed : CompilerAtomNamesAllowed external origin start second)
    (thirdAllowed : CompilerAtomNamesAllowed external origin start third)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals
        thirdTerm thirdGoals,
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit thirdTerm →
      CompilerGoalsNamesAllowed external origin limit thirdGoals →
        CompilerAtomNamesAllowed external origin limit
            (buildTerm firstTerm secondTerm thirdTerm) ∧
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start first
        let (secondTerm, secondGoals, middleSecond) ←
          compileExprFuel fuel env middleFirst second
        let (thirdTerm, thirdGoals, finalCounter) ←
          compileExprFuel fuel env middleSecond third
        .ok (buildTerm firstTerm secondTerm thirdTerm,
          buildGoals firstTerm firstGoals secondTerm secondGoals thirdTerm
            thirdGoals,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  refine ih.bindExpr (start := counter2) (originStart.trans reached2)
    (envAllowed.mono reached2) (thirdAllowed.mono reached2) remaining2 ?_
  intro value3 goals3 counter3 advance3 valueNames3 goalsNames3 remaining3
  rcases Except.ok.inj remaining3 with ⟨rfl, rfl, rfl⟩
  have later1 := advance2.trans advance3
  exact buildAllowed _ _ _ _ _ _ _
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (valueNames2.mono advance3) (goalsNames2.mono advance3)
    valueNames3 goalsNames3

theorem compileExprThenThreeFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (source : Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (buildGoals : Atom → List Goal → Atom → Atom → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (buildAllowed : ∀ limit compiledTerm compiledGoals first second result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit compiledTerm →
      CompilerGoalsNamesAllowed external origin limit compiledGoals →
      CompilerAtomNamesAllowed external origin limit first →
      CompilerAtomNamesAllowed external origin limit second →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals compiledTerm compiledGoals first second result))
    (compiled :
      (do
        let (compiledTerm, compiledGoals, middle) ←
          compileExprFuel fuel env start source
        let (first, afterFirst) := fresh middle
        let (second, afterSecond) := fresh afterFirst
        let (result, finalCounter) := fresh afterSecond
        .ok (result,
          buildGoals compiledTerm compiledGoals first second result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed sourceAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  have allocatedNames2 := compilerFreshAtom_namesAllowed external origin
    counter1 (originStart.trans advance1)
  simp only [fresh] at remaining1
  have reached2 := advance1.trans (Nat.le_succ counter1)
  have allocatedNames3 := compilerFreshAtom_namesAllowed external origin
    (counter1 + 1) (originStart.trans reached2)
  have reached3 := reached2.trans (Nat.le_succ (counter1 + 1))
  have allocatedNames4 := compilerFreshAtom_namesAllowed external origin
    ((counter1 + 1) + 1) (originStart.trans reached3)
  have reached4 := reached3.trans (Nat.le_succ ((counter1 + 1) + 1))
  rcases Except.ok.inj remaining1 with ⟨rfl, rfl, rfl⟩
  have later2 := (Nat.le_succ (counter1 + 1)).trans (Nat.le_succ ((counter1 + 1) + 1))
  have later1 := (Nat.le_succ counter1).trans later2
  exact ⟨allocatedNames4, buildAllowed _ _ _ _ _ _ reached4
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (allocatedNames2.mono later2) (allocatedNames3.mono (Nat.le_succ ((counter1 + 1) + 1)))
    allocatedNames4⟩

theorem compileTwoExprThenFourFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (firstSource secondSource : Atom) (term : Atom) (goals : List Goal)
    (next : Nat)
    (buildGoals : Atom → List Goal → Atom → List Goal → Atom → Atom →
      Atom → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstSourceAllowed :
      CompilerAtomNamesAllowed external origin start firstSource)
    (secondSourceAllowed :
      CompilerAtomNamesAllowed external origin start secondSource)
    (buildAllowed : ∀ limit firstTerm firstGoals secondTerm secondGoals
        firstFresh secondFresh thirdFresh result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit firstFresh →
      CompilerAtomNamesAllowed external origin limit secondFresh →
      CompilerAtomNamesAllowed external origin limit thirdFresh →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals secondTerm secondGoals firstFresh
            secondFresh thirdFresh result))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start firstSource
        let (secondTerm, secondGoals, middleSecond) ←
          compileExprFuel fuel env middleFirst secondSource
        let (firstFresh, afterFirst) := fresh middleSecond
        let (secondFresh, afterSecond) := fresh afterFirst
        let (thirdFresh, afterThird) := fresh afterSecond
        let (result, finalCounter) := fresh afterThird
        .ok (result,
          buildGoals firstTerm firstGoals secondTerm secondGoals firstFresh
            secondFresh thirdFresh result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstSourceAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  refine ih.bindExpr (start := counter1) (originStart.trans advance1)
    (envAllowed.mono advance1) (secondSourceAllowed.mono advance1) remaining1 ?_
  intro value2 goals2 counter2 advance2 valueNames2 goalsNames2 remaining2
  have reached2 := advance1.trans advance2
  have allocatedNames3 := compilerFreshAtom_namesAllowed external origin
    counter2 (originStart.trans reached2)
  simp only [fresh] at remaining2
  have reached3 := reached2.trans (Nat.le_succ counter2)
  have allocatedNames4 := compilerFreshAtom_namesAllowed external origin
    (counter2 + 1) (originStart.trans reached3)
  have reached4 := reached3.trans (Nat.le_succ (counter2 + 1))
  have allocatedNames5 := compilerFreshAtom_namesAllowed external origin
    ((counter2 + 1) + 1) (originStart.trans reached4)
  have reached5 := reached4.trans (Nat.le_succ ((counter2 + 1) + 1))
  have allocatedNames6 := compilerFreshAtom_namesAllowed external origin
    (((counter2 + 1) + 1) + 1) (originStart.trans reached5)
  have reached6 := reached5.trans (Nat.le_succ (((counter2 + 1) + 1) + 1))
  rcases Except.ok.inj remaining2 with ⟨rfl, rfl, rfl⟩
  have later4 := (Nat.le_succ ((counter2 + 1) + 1)).trans (Nat.le_succ (((counter2 + 1) + 1) + 1))
  have later3 := (Nat.le_succ (counter2 + 1)).trans later4
  have later2 := (Nat.le_succ counter2).trans later3
  have later1 := advance2.trans later2
  exact ⟨allocatedNames6, buildAllowed _ _ _ _ _ _ _ _ _ reached6
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (valueNames2.mono later2) (goalsNames2.mono later2)
    (allocatedNames3.mono later3) (allocatedNames4.mono later4)
    (allocatedNames5.mono (Nat.le_succ (((counter2 + 1) + 1) + 1))) allocatedNames6⟩

theorem compileSpaceBoolean_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (spaceSource patternSource : Atom) (term : Atom) (goals : List Goal)
    (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (spaceAllowed :
      CompilerAtomNamesAllowed external origin start spaceSource)
    (patternAllowed :
      CompilerAtomNamesAllowed external origin start patternSource)
    (compiled :
      (do
        let (compiledSpace, compiledGoals, middle) ←
          compileExprFuel fuel env start spaceSource
        let (result, finalCounter) := fresh middle
        let pattern := chainify patternSource
        .ok (result, compiledGoals ++
          [Goal.softcut pattern
            [Goal.smatch (spacePat compiledSpace pattern)]
            [Goal.eq result compilerTrueA] [Goal.eq result compilerFalseA]], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    spaceSource term goals next
    (fun compiledSpace compiledGoals result =>
      let pattern := chainify patternSource
      compiledGoals ++ [Goal.softcut pattern
        [Goal.smatch (spacePat compiledSpace pattern)]
        [Goal.eq result compilerTrueA] [Goal.eq result compilerFalseA]])
    originStart envAllowed spaceAllowed
    (by
      intro limit compiledSpace compiledGoals result startLimit
        compiledSpaceAllowed compiledGoalsAllowed resultAllowed
      have patternAtLimit : CompilerAtomNamesAllowed external origin limit
          (chainify patternSource) :=
        (chainify_namesAllowed patternAllowed).mono startLimit
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        compiledGoals [Goal.softcut (chainify patternSource)
          [Goal.smatch (spacePat compiledSpace (chainify patternSource))]
          [Goal.eq result compilerTrueA] [Goal.eq result compilerFalseA]]).2
      constructor
      · exact compiledGoalsAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        apply compilerGoalNamesAllowed_softcut patternAtLimit
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_smatch
            (spacePat_namesAllowed compiledSpaceAllowed patternAtLimit)
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerTrueA])
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerFalseA]))
    compiled

theorem compileWorldDataAction_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (operation : String) (spaceSource dataSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start
      [spaceSource, dataSource])
    (compiled :
      (do
        let (compiledSpace, compiledGoals, middle) ←
          compileExprFuel fuel env start spaceSource
        let (result, finalCounter) := fresh middle
        .ok (result, compiledGoals ++
          [Goal.wact operation [compiledSpace, chainify dataSource] result],
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  have sourcePair :
      CompilerAtomNamesAllowed external origin start spaceSource ∧
      CompilerAtomNamesAllowed external origin start dataSource := by
    simpa using sourcesAllowed
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    spaceSource term goals next
    (fun compiledSpace compiledGoals result => compiledGoals ++
      [Goal.wact operation [compiledSpace, chainify dataSource] result])
    originStart envAllowed sourcePair.1
    (by
      intro limit compiledSpace compiledGoals result startLimit
        compiledSpaceAllowed compiledGoalsAllowed resultAllowed
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        compiledGoals
        [Goal.wact operation [compiledSpace, chainify dataSource] result]).2
      constructor
      · exact compiledGoalsAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_wact
          (by
            simpa using And.intro compiledSpaceAllowed
              ((chainify_namesAllowed sourcePair.2).mono startLimit))
          resultAllowed operation)
    compiled

/-- Compiling an ordered argument list followed by one fresh-result builtin
preserves the compiler-owned name interval.  This is the reusable bridge for
runtime conversions such as `Predicate/2`; their result must not be
precomputed merely to simplify the name proof. -/
theorem compileArgsThenFreshBin_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (argumentHead operation : String) (sources : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed :
      CompilerAtomsNamesAllowed external origin start sources)
    (compiled :
      (do
        let (compiledTerms, compiledGoals, middle) ←
          compileArgsAtFuel fuel env start argumentHead 0 sources
        let (result, finalCounter) := fresh middle
        .ok (result, compiledGoals ++
          [Goal.bin operation compiledTerms result], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases argumentsEq :
      compileArgsAtFuel fuel env start argumentHead 0 sources with
  | error message =>
      simp only [argumentsEq] at compiled
      contradiction
  | ok argumentsResult =>
      simp only [argumentsEq, fresh] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have argumentsCounter := (compilerCounterAt fuel).argsAt env start
        argumentHead 0 sources argumentsResult.1 argumentsResult.2.1
        argumentsResult.2.2 argumentsEq
      have argumentsNames := ih.argsAt external origin env start argumentHead 0
        sources argumentsResult.1 argumentsResult.2.1 argumentsResult.2.2
        originStart envAllowed sourcesAllowed argumentsEq
      have resultAllowed : CompilerAtomNamesAllowed external origin
          (argumentsResult.2.2 + 1)
          (Atom.var (compilerGeneratedName argumentsResult.2.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated (Nat.le_trans originStart argumentsCounter) (by omega)
      constructor
      · exact resultAllowed
      · apply (compilerGoalsNamesAllowed_append_iff external origin
            (argumentsResult.2.2 + 1) argumentsResult.2.1
            [Goal.bin operation argumentsResult.1
              (Atom.var (compilerGeneratedName argumentsResult.2.2))]).2
        constructor
        · exact argumentsNames.2.mono (by omega)
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_bin
            (argumentsNames.1.mono (by omega)) resultAllowed operation

theorem compileArgsThenFreshCall_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (operation : String) (sources : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed :
      CompilerAtomsNamesAllowed external origin start sources)
    (compiled :
      (do
        let (compiledTerms, compiledGoals, middle) ←
          compileArgsAtFuel fuel env start operation 0 sources
        let (result, finalCounter) := fresh middle
        .ok (result, compiledGoals ++
          [Goal.call operation compiledTerms result], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases argumentsEq : compileArgsAtFuel fuel env start operation 0 sources with
  | error message =>
      simp only [argumentsEq] at compiled
      contradiction
  | ok argumentsResult =>
      simp only [argumentsEq, fresh] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have argumentsCounter := (compilerCounterAt fuel).argsAt env start
        operation 0 sources argumentsResult.1 argumentsResult.2.1
        argumentsResult.2.2 argumentsEq
      have argumentsNames := ih.argsAt external origin env start operation 0
        sources argumentsResult.1 argumentsResult.2.1 argumentsResult.2.2
        originStart envAllowed sourcesAllowed argumentsEq
      have resultAllowed : CompilerAtomNamesAllowed external origin
          (argumentsResult.2.2 + 1)
          (Atom.var (compilerGeneratedName argumentsResult.2.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated (Nat.le_trans originStart argumentsCounter) (by omega)
      constructor
      · exact resultAllowed
      · apply (compilerGoalsNamesAllowed_append_iff external origin
            (argumentsResult.2.2 + 1) argumentsResult.2.1
            [Goal.call operation argumentsResult.1
              (Atom.var (compilerGeneratedName argumentsResult.2.2))]).2
        constructor
        · exact argumentsNames.2.mono (by omega)
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_call
            (argumentsNames.1.mono (by omega)) resultAllowed operation

theorem compileExprThenFreshFoldEquality_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (source : Atom) (indices : List Nat) (term : Atom) (goals : List Goal)
    (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled :
      (do
        let (compiledTerm, compiledGoals, middle) ←
          compileExprFuel fuel env start source
        let (slots, finalCounter) := indices.foldl
          (fun (acc : List Atom × Nat) _ =>
            let (freshTerm, following) := fresh acc.2
            (acc.1 ++ [freshTerm], following)) ([], middle)
        .ok (compilerTrueA, compiledGoals ++
          [Goal.eq compiledTerm (chainOf slots)], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases expressionEq : compileExprFuel fuel env start source with
  | error message =>
      simp only [expressionEq] at compiled
      contradiction
  | ok expressionResult =>
      simp only [expressionEq] at compiled
      rcases allocationEq : indices.foldl
          (fun (acc : List Atom × Nat) _ =>
            let (freshTerm, following) := fresh acc.2
            (acc.1 ++ [freshTerm], following))
          ([], expressionResult.2.2) with ⟨slots, finalCounter⟩
      simp only [allocationEq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have expressionCounter := compileExprFuel_counter_mono fuel env start
        source expressionResult.1 expressionResult.2.1 expressionResult.2.2
        expressionEq
      have expressionNames := ih.expr external origin env start source
        expressionResult.1 expressionResult.2.1 expressionResult.2.2
        originStart envAllowed sourceAllowed expressionEq
      have allocationEqForFold :
          indices.foldl
            (fun (acc : List Atom × Nat) _ =>
              (acc.1 ++ [Atom.var (compilerGeneratedName acc.2)],
                acc.2 + 1))
            ([], expressionResult.2.2) = (slots, next) := by
        simpa only [fresh, compilerGeneratedName] using allocationEq
      have allocationEqForCounter :
          indices.foldl
            (fun (acc : List Atom × Nat) _ =>
              (acc.1 ++ [Atom.var s!"_q{acc.2}"], acc.2 + 1))
            ([], expressionResult.2.2) = (slots, next) := by
        simpa only [fresh] using allocationEq
      have allocationCounter := freshFold_counter_mono indices
        ([], expressionResult.2.2)
      rw [allocationEqForCounter] at allocationCounter
      have slotsAllowed := freshFold_generatedNames external origin indices
        ([], expressionResult.2.2)
        (Nat.le_trans originStart expressionCounter) (by simp)
      rw [allocationEqForFold] at slotsAllowed
      constructor
      · simp [compilerTrueA]
      · apply (compilerGoalsNamesAllowed_append_iff external origin
            next expressionResult.2.1
            [Goal.eq expressionResult.1 (chainOf slots)]).2
        constructor
        · exact expressionNames.2.mono allocationCounter
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_eq
            (expressionNames.1.mono allocationCounter)
            (chainOf_namesAllowed slotsAllowed)

theorem compileExprThenTwoFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (source : Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (buildGoals : Atom → List Goal → Atom → Atom → List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (buildAllowed : ∀ limit compiledTerm compiledGoals intermediate result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit compiledTerm →
      CompilerGoalsNamesAllowed external origin limit compiledGoals →
      CompilerAtomNamesAllowed external origin limit intermediate →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals compiledTerm compiledGoals intermediate result))
    (compiled :
      (do
        let (compiledTerm, compiledGoals, middle) ←
          compileExprFuel fuel env start source
        let (intermediate, afterIntermediate) := fresh middle
        let (result, finalCounter) := fresh afterIntermediate
        .ok (result,
          buildGoals compiledTerm compiledGoals intermediate result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed sourceAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  have allocatedNames2 := compilerFreshAtom_namesAllowed external origin
    counter1 (originStart.trans advance1)
  simp only [fresh] at remaining1
  have reached2 := advance1.trans (Nat.le_succ counter1)
  have allocatedNames3 := compilerFreshAtom_namesAllowed external origin
    (counter1 + 1) (originStart.trans reached2)
  have reached3 := reached2.trans (Nat.le_succ (counter1 + 1))
  rcases Except.ok.inj remaining1 with ⟨rfl, rfl, rfl⟩
  have later1 := (Nat.le_succ counter1).trans (Nat.le_succ (counter1 + 1))
  exact ⟨allocatedNames3, buildAllowed _ _ _ _ _ reached3
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (allocatedNames2.mono (Nat.le_succ (counter1 + 1))) allocatedNames3⟩

/-- Syntactic-`superpose` branch normalization introduces only the enclosing
generated output and equalities between already-allowed atoms. -/
theorem compileSuperposeBranch_generatedNames
    (external : String → Prop) (origin limit outputIndex : Nat)
    (branch : Atom × List Goal)
    (branchTermAllowed :
      CompilerAtomNamesAllowed external origin limit branch.1)
    (branchGoalsAllowed :
      CompilerGoalsNamesAllowed external origin limit branch.2)
    (outputAllowed : CompilerAtomNamesAllowed external origin limit
      (.var (compilerGeneratedName outputIndex))) :
    CompilerGoalsNamesAllowed external origin limit
        (compileSuperposeBranch (.var (compilerGeneratedName outputIndex))
          branch).1 ∧
      CompilerAtomNamesAllowed external origin limit
        (compileSuperposeBranch (.var (compilerGeneratedName outputIndex))
          branch).2.1 ∧
      CompilerGoalsNamesAllowed external origin limit
        (compileSuperposeBranch (.var (compilerGeneratedName outputIndex))
          branch).2.2 := by
  rcases branch with ⟨term, goals⟩
  cases goals with
  | nil =>
      simpa [compileSuperposeBranch] using
        And.intro (compilerGoalsNamesAllowed_nil external origin limit)
          (And.intro branchTermAllowed branchGoalsAllowed)
  | cons goal goals =>
      have equalityAllowed : CompilerGoalNamesAllowed external origin limit
          (.eq term (.var (compilerGeneratedName outputIndex))) :=
        compilerGoalNamesAllowed_eq branchTermAllowed outputAllowed
      have aliasAllowed : CompilerGoalNamesAllowed external origin limit
          (.compileAlias term (.var (compilerGeneratedName outputIndex))) :=
        compilerGoalNamesAllowed_compileAlias branchTermAllowed outputAllowed
      cases term with
      | var name =>
          simpa [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
            using And.intro
              (show CompilerGoalsNamesAllowed external origin limit
                [.compileAlias (.var name)
                  (.var (compilerGeneratedName outputIndex))]
                from (compilerGoalsNamesAllowed_cons_iff external origin limit
                  _ _).2 ⟨aliasAllowed,
                    compilerGoalsNamesAllowed_nil external origin limit⟩)
              (And.intro outputAllowed branchGoalsAllowed)
      | sym name =>
          simpa [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
            using And.intro
              (compilerGoalsNamesAllowed_nil external origin limit)
              (And.intro outputAllowed
                ((compilerGoalsNamesAllowed_cons_iff external origin limit
                  _ _).2 ⟨equalityAllowed, branchGoalsAllowed⟩))
      | gnd value =>
          simpa [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
            using And.intro
              (compilerGoalsNamesAllowed_nil external origin limit)
              (And.intro outputAllowed
                ((compilerGoalsNamesAllowed_cons_iff external origin limit
                  _ _).2 ⟨equalityAllowed, branchGoalsAllowed⟩))
      | expr values =>
          simpa [compileSuperposeBranch, compileBranch, BEq.beq, Atom.beq]
            using And.intro
              (compilerGoalsNamesAllowed_nil external origin limit)
              (And.intro outputAllowed
                ((compilerGoalsNamesAllowed_cons_iff external origin limit
                  _ _).2 ⟨equalityAllowed, branchGoalsAllowed⟩))

/-- Ordered branch-list normalization preserves the generated-name
classification for both the lifted alias prefix and every normalized branch. -/
theorem compileSuperposeBranches_generatedNames
    (external : String → Prop) (origin limit outputIndex : Nat)
    (branches : List (Atom × List Goal))
    (branchesAllowed :
      CompilerBranchesNamesAllowed external origin limit branches)
    (outputAllowed : CompilerAtomNamesAllowed external origin limit
      (.var (compilerGeneratedName outputIndex))) :
    CompilerGoalsNamesAllowed external origin limit
        (compileSuperposeBranches (.var (compilerGeneratedName outputIndex))
          branches).1 ∧
      CompilerBranchesNamesAllowed external origin limit
        (compileSuperposeBranches (.var (compilerGeneratedName outputIndex))
          branches).2 := by
  induction branches with
  | nil => simp [compileSuperposeBranches]
  | cons branch rest inductionHypothesis =>
      rcases branch with ⟨term, goals⟩
      have allowed :=
        (compilerBranchesNamesAllowed_cons_iff external origin limit term
          goals rest).1 branchesAllowed
      have headAllowed := compileSuperposeBranch_generatedNames external origin
        limit outputIndex (term, goals) allowed.1 allowed.2.1 outputAllowed
      have tailAllowed := inductionHypothesis allowed.2.2
      simp only [compileSuperposeBranches]
      apply And.intro
      · exact (compilerGoalsNamesAllowed_append_iff external origin limit _ _).2
          ⟨headAllowed.1, tailAllowed.1⟩
      · exact (compilerBranchesNamesAllowed_cons_iff external origin limit
          _ _ _).2 ⟨headAllowed.2.1, headAllowed.2.2, tailAllowed.2⟩

theorem compileAmbThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (expressions : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (expressionsAllowed :
      CompilerAtomsNamesAllowed external origin start expressions)
    (compiled :
      (do
        let (branches, middle) ← compileAmbBranchesWith
          (fun counter expression =>
            compileExprFuel fuel env counter expression) start expressions
        let (result, finalCounter) := fresh middle
        .ok (result, [Goal.amb branches result], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases branchesEq : compileAmbBranchesWith
      (fun counter expression => compileExprFuel fuel env counter expression)
      start expressions with
  | error message =>
      simp only [branchesEq] at compiled
      contradiction
  | ok branchResult =>
      simp only [branchesEq, fresh] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have branchCounter := compileAmbBranchesWith_counter _ start expressions
        branchResult branchesEq (by
          intro counter expression branchTerm branchGoals branchNext
            branchCompiled
          exact (compilerCounterAt fuel).expr env counter expression
            branchTerm branchGoals branchNext branchCompiled)
      have nestedBranchNames := compileAmbBranchesWith_generatedNames
        (fun counter expression => compileExprFuel fuel env counter expression)
        (CompilerNameAllowed external origin start) start start expressions
        branchResult (Nat.le_refl start) expressionsAllowed.nest
        (by
          intro counter expression branchTerm branchGoals branchNext
            branchCompiled
          exact (compilerCounterAt fuel).expr env counter expression
            branchTerm branchGoals branchNext branchCompiled)
        (by
          intro counter expression branchTerm branchGoals branchNext
            startCounter expressionAllowed branchCompiled
          exact ih.expr (CompilerNameAllowed external origin start) start env
            counter expression branchTerm branchGoals branchNext startCounter
            (envAllowed.nest.mono startCounter)
            expressionAllowed branchCompiled)
        branchesEq
      have branchNames : CompilerBranchesNamesAllowed external origin
          branchResult.2 branchResult.1 :=
        CompilerNamesAllowed.flatten originStart branchCounter
          nestedBranchNames
      have resultAllowed : CompilerAtomNamesAllowed external origin
          (branchResult.2 + 1)
          (Atom.var (compilerGeneratedName branchResult.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated (Nat.le_trans originStart branchCounter) (by omega)
      constructor
      · exact resultAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_amb (branchNames.mono (by omega))
          resultAllowed

/-- A rejected empty branch collection cannot produce names; every successful
guarded collection is therefore the ordinary nonempty branch traversal. -/
theorem compileNonemptyAmbThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (expressions : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (expressionsAllowed :
      CompilerAtomsNamesAllowed external origin start expressions)
    (compiled :
      (if expressions.isEmpty then
        .error "superpose: empty"
      else do
        let (branches, middle) ← compileAmbBranchesWith
          (fun counter expression =>
            compileExprFuel fuel env counter expression) start expressions
        let (result, finalCounter) := fresh middle
        .ok (result, [Goal.amb branches result], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  by_cases empty : expressions.isEmpty = true
  · simp only [empty, if_true] at compiled
    contradiction
  · have nonempty : expressions.isEmpty = false :=
      Bool.eq_false_iff.mpr empty
    simp only [nonempty, Bool.false_eq_true, if_false] at compiled
    exact compileAmbThenFresh_generatedNames fuel ih external origin env start
      expressions term goals next originStart envAllowed expressionsAllowed
      compiled

/-- Generated-name preservation for the guarded syntactic-`superpose` path,
including its lifted alias prefix and normalized equality-before-body
branches. -/
theorem compileNonemptySuperposeThenFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (expressions : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (expressionsAllowed :
      CompilerAtomsNamesAllowed external origin start expressions)
    (compiled :
      (if expressions.isEmpty then
        .error "superpose: empty"
      else do
        let (branches, middle) ← compileAmbBranchesWith
          (fun counter expression =>
            compileExprFuel fuel env counter expression) start expressions
        let (result, finalCounter) := fresh middle
        let normalized := compileSuperposeBranches result branches
        .ok (result,
          normalized.1 ++ [Goal.amb normalized.2 result], finalCounter)) =
        .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  by_cases empty : expressions.isEmpty = true
  · simp only [empty, if_true] at compiled
    contradiction
  · have nonempty : expressions.isEmpty = false := Bool.eq_false_iff.mpr empty
    simp only [nonempty, Bool.false_eq_true, if_false, Bind.bind, Except.bind]
      at compiled
    cases branchesEq : compileAmbBranchesWith
        (fun counter expression => compileExprFuel fuel env counter expression)
        start expressions with
    | error message =>
        simp only [branchesEq] at compiled
        contradiction
    | ok branchResult =>
        simp only [branchesEq, fresh] at compiled
        rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
        have branchCounter := compileAmbBranchesWith_counter _ start
          expressions branchResult branchesEq (by
            intro counter expression branchTerm branchGoals branchNext
              branchCompiled
            exact (compilerCounterAt fuel).expr env counter expression
              branchTerm branchGoals branchNext branchCompiled)
        have nestedBranchNames := compileAmbBranchesWith_generatedNames
          (fun counter expression =>
            compileExprFuel fuel env counter expression)
          (CompilerNameAllowed external origin start) start start expressions
          branchResult (Nat.le_refl start) expressionsAllowed.nest
          (by
            intro counter expression branchTerm branchGoals branchNext
              branchCompiled
            exact (compilerCounterAt fuel).expr env counter expression
              branchTerm branchGoals branchNext branchCompiled)
          (by
            intro counter expression branchTerm branchGoals branchNext
              startCounter expressionAllowed branchCompiled
            exact ih.expr (CompilerNameAllowed external origin start) start env
              counter expression branchTerm branchGoals branchNext startCounter
              (envAllowed.nest.mono startCounter) expressionAllowed
              branchCompiled)
          branchesEq
        have branchNames : CompilerBranchesNamesAllowed external origin
            branchResult.2 branchResult.1 :=
          CompilerNamesAllowed.flatten originStart branchCounter
            nestedBranchNames
        have resultAllowed : CompilerAtomNamesAllowed external origin
            (branchResult.2 + 1)
            (Atom.var (compilerGeneratedName branchResult.2)) := by
          simp only [compilerAtomNamesAllowed_var_iff]
          exact .generated (Nat.le_trans originStart branchCounter) (by omega)
        have normalizedNames := compileSuperposeBranches_generatedNames
          external origin (branchResult.2 + 1) branchResult.2 branchResult.1
          (branchNames.mono (by omega)) resultAllowed
        constructor
        · exact resultAllowed
        · apply (compilerGoalsNamesAllowed_append_iff external origin
            (branchResult.2 + 1) _ _).2
          constructor
          · exact normalizedNames.1
          · exact (compilerGoalsNamesAllowed_cons_iff external origin
              (branchResult.2 + 1) _ _).2
                ⟨compilerGoalNamesAllowed_amb normalizedNames.2 resultAllowed,
                  compilerGoalsNamesAllowed_nil external origin
                    (branchResult.2 + 1)⟩

theorem compileExprFreshExprFresh_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (firstSource secondSource : Atom) (term : Atom) (goals : List Goal)
    (next : Nat)
    (buildGoals : Atom → List Goal → Atom → Atom → List Goal → Atom →
      List Goal)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (firstSourceAllowed :
      CompilerAtomNamesAllowed external origin start firstSource)
    (secondSourceAllowed :
      CompilerAtomNamesAllowed external origin start secondSource)
    (buildAllowed : ∀ limit firstTerm firstGoals intermediate secondTerm
        secondGoals result,
      start ≤ limit →
      CompilerAtomNamesAllowed external origin limit firstTerm →
      CompilerGoalsNamesAllowed external origin limit firstGoals →
      CompilerAtomNamesAllowed external origin limit intermediate →
      CompilerAtomNamesAllowed external origin limit secondTerm →
      CompilerGoalsNamesAllowed external origin limit secondGoals →
      CompilerAtomNamesAllowed external origin limit result →
        CompilerGoalsNamesAllowed external origin limit
          (buildGoals firstTerm firstGoals intermediate secondTerm secondGoals
            result))
    (compiled :
      (do
        let (firstTerm, firstGoals, middleFirst) ←
          compileExprFuel fuel env start firstSource
        let (intermediate, afterIntermediate) := fresh middleFirst
        let (secondTerm, secondGoals, middleSecond) ←
          compileExprFuel fuel env afterIntermediate secondSource
        let (result, finalCounter) := fresh middleSecond
        .ok (result,
          buildGoals firstTerm firstGoals intermediate secondTerm secondGoals
            result,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  refine ih.bindExpr originStart envAllowed firstSourceAllowed compiled ?_
  intro value1 goals1 counter1 advance1 valueNames1 goalsNames1 remaining1
  have allocatedNames2 := compilerFreshAtom_namesAllowed external origin
    counter1 (originStart.trans advance1)
  simp only [fresh] at remaining1
  have reached2 := advance1.trans (Nat.le_succ counter1)
  refine ih.bindExpr (start := (counter1 + 1)) (originStart.trans reached2)
    (envAllowed.mono reached2) (secondSourceAllowed.mono reached2) remaining1 ?_
  intro value3 goals3 counter3 advance3 valueNames3 goalsNames3 remaining3
  have reached3 := reached2.trans advance3
  have allocatedNames4 := compilerFreshAtom_namesAllowed external origin
    counter3 (originStart.trans reached3)
  have reached4 := reached3.trans (Nat.le_succ counter3)
  rcases Except.ok.inj remaining3 with ⟨rfl, rfl, rfl⟩
  have later2 := advance3.trans (Nat.le_succ counter3)
  have later1 := (Nat.le_succ counter1).trans later2
  exact ⟨allocatedNames4, buildAllowed _ _ _ _ _ _ _ reached4
    (valueNames1.mono later1) (goalsNames1.mono later1)
    (allocatedNames2.mono later2) (valueNames3.mono (Nat.le_succ counter3))
    (goalsNames3.mono (Nat.le_succ counter3)) allocatedNames4⟩

private def compilerMatchPatternSources : Atom → List Atom
  | Atom.expr (Atom.sym "," :: patterns) => patterns
  | pattern => [pattern]

private theorem compilerMatchPatternSources_eq (pattern : Atom) :
    compilerMatchPatternSources pattern =
      (match pattern with
      | Atom.expr (Atom.sym "," :: conjuncts) => conjuncts
      | _ => [pattern]) := by
  cases pattern with
  | sym symbol | var symbol | gnd symbol => rfl
  | expr items =>
      cases items with
      | nil => rfl
      | cons first rest =>
          cases first with
          | sym symbol =>
              by_cases comma : symbol = ","
              · subst symbol
                rfl
              · simp [compilerMatchPatternSources, comma]
          | var sourceName | gnd value | expr nested => rfl

private theorem compilerMatchPatternSources_vars_subset (pattern : Atom) :
    ∀ name, name ∈ (compilerMatchPatternSources pattern).flatMap Atom.vars →
      name ∈ pattern.vars := by
  intro name member
  cases pattern with
  | var sourceName =>
      simpa [compilerMatchPatternSources] using member
  | gnd value =>
      simpa [compilerMatchPatternSources] using member
  | sym symbol =>
      simpa [compilerMatchPatternSources] using member
  | expr items =>
      cases items with
      | nil => simp [compilerMatchPatternSources, Atom.vars] at member
      | cons first rest =>
          cases first with
          | sym symbol =>
              by_cases comma : symbol = ","
              · subst symbol
                simpa [compilerMatchPatternSources, Atom.vars,
                  List.flatMap_def] using member
              · simpa [compilerMatchPatternSources, Atom.vars, comma,
                  List.flatMap_def] using member
          | var sourceName =>
              simpa [compilerMatchPatternSources, Atom.vars,
                List.flatMap_def] using member
          | gnd value =>
              simpa [compilerMatchPatternSources, Atom.vars,
                List.flatMap_def] using member
          | expr nested =>
              simpa [compilerMatchPatternSources, Atom.vars,
                List.flatMap_def] using member

private theorem matchPatternSources_namesAllowed {external : String → Prop}
    {origin limit : Nat} {pattern : Atom}
    (patternAllowed :
      CompilerAtomNamesAllowed external origin limit pattern) :
    CompilerAtomsNamesAllowed external origin limit
      (compilerMatchPatternSources pattern) :=
  CompilerNamesAllowed.of_subset patternAllowed
    (compilerMatchPatternSources_vars_subset pattern)

theorem compilerMatchGoals_namesAllowed {external : String → Prop}
    {origin limit : Nat} {space : Atom} : ∀ {patterns : List Atom},
    CompilerAtomNamesAllowed external origin limit space →
    CompilerAtomsNamesAllowed external origin limit patterns →
    CompilerGoalsNamesAllowed external origin limit
      (patterns.map (fun pattern =>
        Goal.smatch (spacePat space (chainify pattern)))) := by
  intro patterns spaceAllowed patternsAllowed
  induction patterns with
  | nil => simp
  | cons pattern rest ih =>
      have splitAllowed :=
        (compilerAtomsNamesAllowed_cons_iff external origin limit pattern
          rest).mp patternsAllowed
      simp only [List.map_cons, compilerGoalsNamesAllowed_cons_iff]
      exact ⟨compilerGoalNamesAllowed_smatch
          (spacePat_namesAllowed spaceAllowed
            (chainify_namesAllowed splitAllowed.1)),
        ih splitAllowed.2⟩

private theorem compileMatch_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (spaceSource patternSource templateSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start
      [spaceSource, patternSource, templateSource])
    (compiled :
      (do
        let (compiledSpace, spaceGoals, middle) ←
          compileExprFuel fuel env start spaceSource
        let (compiledTemplate, templateGoals, finalCounter) ←
          compileExprFuel fuel env middle templateSource
        let patterns := match patternSource with
          | Atom.expr (Atom.sym "," :: conjuncts) => conjuncts
          | _ => [patternSource]
        .ok (compiledTemplate,
          spaceGoals ++ patterns.map (fun pattern =>
            Goal.smatch (spacePat compiledSpace (chainify pattern))) ++
            templateGoals,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  have inputNames :
      CompilerAtomNamesAllowed external origin start spaceSource ∧
      CompilerAtomNamesAllowed external origin start patternSource ∧
      CompilerAtomNamesAllowed external origin start templateSource := by
    simpa [and_assoc] using sourcesAllowed
  exact compileTwoExpr_generatedNames fuel ih external origin env start
    spaceSource templateSource term goals next (fun _ template => template)
    (fun compiledSpace spaceGoals _ templateGoals =>
      let patterns := match patternSource with
        | Atom.expr (Atom.sym "," :: conjuncts) => conjuncts
        | _ => [patternSource]
      spaceGoals ++ patterns.map (fun pattern =>
        Goal.smatch (spacePat compiledSpace (chainify pattern))) ++
        templateGoals)
    originStart envAllowed inputNames.1 inputNames.2.2
    (by
      intro limit compiledSpace spaceGoals compiledTemplate templateGoals
        startLimit compiledSpaceAllowed spaceGoalsAllowed
        compiledTemplateAllowed templateGoalsAllowed
      have helperPatternsAllowed : CompilerAtomsNamesAllowed external origin
          limit (compilerMatchPatternSources patternSource) :=
        matchPatternSources_namesAllowed (inputNames.2.1.mono startLimit)
      have matchGoalsAllowed : CompilerGoalsNamesAllowed external origin limit
          ((compilerMatchPatternSources patternSource).map (fun pattern =>
            Goal.smatch (spacePat compiledSpace (chainify pattern)))) :=
        compilerMatchGoals_namesAllowed compiledSpaceAllowed
          helperPatternsAllowed
      constructor
      · exact compiledTemplateAllowed
      · simp only [compilerGoalsNamesAllowed_append_iff]
        exact ⟨⟨spaceGoalsAllowed,
            by
              rw [← compilerMatchPatternSources_eq patternSource]
              exact matchGoalsAllowed⟩,
          templateGoalsAllowed⟩)
    compiled

private theorem compilerEmptyCaseBody_vars_subset {arm body : Atom}
    (selected :
      (match arm with
      | Atom.expr [Atom.sym "Empty", candidate] => some candidate
      | _ => none) = some body) :
    ∀ name, name ∈ body.vars → name ∈ arm.vars := by
  intro candidateName candidateMember
  cases arm with
  | var name => simp at selected
  | sym name => simp at selected
  | gnd value => simp at selected
  | expr items =>
      cases items with
      | nil => simp at selected
      | cons first rest =>
          cases rest with
          | nil => simp at selected
          | cons second tail =>
              cases tail with
              | cons third more =>
                  simp at selected
              | nil =>
                  cases first with
                  | var name => simp at selected
                  | gnd value => simp at selected
                  | expr nested => simp at selected
                  | sym name =>
                      by_cases empty : name = "Empty"
                      · subst name
                        have secondEq : second = body := by
                          exact Option.some.inj selected
                        subst body
                        simpa [Atom.vars, List.flatMap_def] using candidateMember
                      · simp [empty] at selected

private theorem compilerFindEmptyCaseBody_namesAllowed
    {external : String → Prop} {origin limit : Nat} {arms : List Atom}
    {body : Atom}
    (armsAllowed : CompilerAtomsNamesAllowed external origin limit arms)
    (selected :
      arms.findSome? (fun arm =>
        match arm with
        | Atom.expr [Atom.sym "Empty", candidate] => some candidate
        | _ => none) = some body) :
    CompilerAtomNamesAllowed external origin limit body := by
  rcases List.findSome?_eq_some_iff.mp selected with
    ⟨before, arm, after, rfl, armSelected, _⟩
  have armAllowed : CompilerAtomNamesAllowed external origin limit arm :=
    armsAllowed.atom_mem (by simp)
  exact CompilerNamesAllowed.of_subset armAllowed
    (compilerEmptyCaseBody_vars_subset armSelected)

private theorem compileCase_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (scrutinee : Atom) (arms : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (scrutineeAllowed :
      CompilerAtomNamesAllowed external origin start scrutinee)
    (armsAllowed : CompilerAtomsNamesAllowed external origin start arms)
    (compiled :
      (do
        let (compiledScrutinee, scrutineeGoals, afterScrutinee) ←
          compileExprFuel fuel env start scrutinee
        let (scrutineeValue, afterScrutineeValue) := fresh afterScrutinee
        let (result, afterResult) := fresh afterScrutineeValue
        let emptyArm := arms.findSome? (fun arm =>
          match arm with
          | Atom.expr [Atom.sym "Empty", body] => some body
          | _ => none)
        let (armGoals, afterArms) ← compileCaseArmsFuel fuel env
          scrutineeValue result afterResult arms
        match emptyArm with
        | some body => do
            let (compiledBody, bodyGoals, finalCounter) ←
              compileExprFuel fuel env afterArms body
            let failGoals := bodyGoals ++ [Goal.eq result compiledBody]
            let guard := scrutineeGoals ++
              [Goal.eq scrutineeValue compiledScrutinee]
            let positive := guard ++ armGoals
            let fallback := negatedGoals guard ++ failGoals
            .ok (result,
              [Goal.amb [(result, positive), (result, fallback)] result],
              finalCounter)
        | none =>
            .ok (result,
              scrutineeGoals ++
                [Goal.eq scrutineeValue compiledScrutinee] ++ armGoals,
              afterArms)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases scrutineeEq : compileExprFuel fuel env start scrutinee with
  | error message =>
      simp only [scrutineeEq] at compiled
      contradiction
  | ok scrutineeResult =>
      simp only [scrutineeEq, fresh] at compiled
      have scrutineeCounter := compileExprFuel_counter_mono fuel env start
        scrutinee scrutineeResult.1 scrutineeResult.2.1
        scrutineeResult.2.2 scrutineeEq
      have scrutineeNames := ih.expr external origin env start scrutinee
        scrutineeResult.1 scrutineeResult.2.1 scrutineeResult.2.2
        originStart envAllowed scrutineeAllowed scrutineeEq
      have afterFresh : start ≤ scrutineeResult.2.2 + 2 :=
        Nat.le_trans scrutineeCounter (by omega)
      have scrutineeValueAllowed : CompilerAtomNamesAllowed external origin
          (scrutineeResult.2.2 + 2)
          (Atom.var (compilerGeneratedName scrutineeResult.2.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated (Nat.le_trans originStart scrutineeCounter) (by omega)
      have resultAllowed : CompilerAtomNamesAllowed external origin
          (scrutineeResult.2.2 + 2)
          (Atom.var (compilerGeneratedName (scrutineeResult.2.2 + 1))) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated
          (Nat.le_trans (Nat.le_trans originStart scrutineeCounter) (by omega))
          (by omega)
      cases armsEq : compileCaseArmsFuel fuel env
          (Atom.var (toString "_q" ++ toString scrutineeResult.2.2))
          (Atom.var
            (toString "_q" ++ toString (scrutineeResult.2.2 + 1)))
          (scrutineeResult.2.2 + 1 + 1) arms with
      | error message =>
          simp only [armsEq] at compiled
          contradiction
      | ok armsResult =>
          simp only [armsEq] at compiled
          have armsCounter := compileCaseArmsFuel_counter_mono fuel env
            (Atom.var (compilerGeneratedName scrutineeResult.2.2))
            (Atom.var (compilerGeneratedName (scrutineeResult.2.2 + 1)))
            (scrutineeResult.2.2 + 2) arms armsResult.1 armsResult.2 armsEq
          have armsNames := ih.caseArms external origin env
            (Atom.var (compilerGeneratedName scrutineeResult.2.2))
            (Atom.var (compilerGeneratedName (scrutineeResult.2.2 + 1)))
            (scrutineeResult.2.2 + 2) arms armsResult.1 armsResult.2
            (Nat.le_trans originStart afterFresh)
            (envAllowed.mono afterFresh) scrutineeValueAllowed resultAllowed
            (armsAllowed.mono afterFresh) armsEq
          cases emptyEq : arms.findSome? (fun arm =>
              match arm with
              | Atom.expr [Atom.sym "Empty", body] => some body
              | _ => none) with
          | none =>
              simp only [emptyEq] at compiled
              rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
              have resultFinal := resultAllowed.mono armsCounter
              have scrutineeValueFinal :=
                scrutineeValueAllowed.mono armsCounter
              have compiledScrutineeFinal :=
                (scrutineeNames.1.mono (by omega)).mono armsCounter
              have scrutineeGoalsFinal :=
                (scrutineeNames.2.mono (by omega)).mono armsCounter
              constructor
              · exact resultFinal
              · simp only [compilerGoalsNamesAllowed_append_iff,
                  compilerGoalsNamesAllowed_cons_iff,
                  compilerGoalsNamesAllowed_nil, and_true]
                exact ⟨⟨scrutineeGoalsFinal,
                    compilerGoalNamesAllowed_eq scrutineeValueFinal
                      compiledScrutineeFinal⟩,
                  armsNames⟩
          | some body =>
              simp only [emptyEq] at compiled
              cases bodyEq : compileExprFuel fuel env armsResult.2 body with
              | error message =>
                  simp only [bodyEq] at compiled
                  contradiction
              | ok bodyResult =>
                  simp only [bodyEq] at compiled
                  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
                  have bodyCounter := compileExprFuel_counter_mono fuel env
                    armsResult.2 body bodyResult.1 bodyResult.2.1
                    bodyResult.2.2 bodyEq
                  have bodySourceAllowedAtStart :=
                    compilerFindEmptyCaseBody_namesAllowed armsAllowed emptyEq
                  have bodyNames := ih.expr external origin env armsResult.2
                    body bodyResult.1 bodyResult.2.1 bodyResult.2.2
                    (Nat.le_trans (Nat.le_trans originStart afterFresh)
                      armsCounter)
                    ((envAllowed.mono afterFresh).mono armsCounter)
                    ((bodySourceAllowedAtStart.mono afterFresh).mono
                      armsCounter)
                    bodyEq
                  have toFinal : armsResult.2 ≤ bodyResult.2.2 := bodyCounter
                  have resultFinal :=
                    (resultAllowed.mono armsCounter).mono toFinal
                  have scrutineeValueFinal :=
                    (scrutineeValueAllowed.mono armsCounter).mono toFinal
                  have sourceScrutineeFinal :=
                    ((scrutineeAllowed.mono afterFresh).mono armsCounter).mono
                      toFinal
                  have compiledScrutineeFinal :=
                    ((scrutineeNames.1.mono (by omega)).mono armsCounter).mono
                      toFinal
                  have scrutineeGoalsFinal :=
                    ((scrutineeNames.2.mono (by omega)).mono armsCounter).mono
                      toFinal
                  have armsGoalsFinal := armsNames.mono toFinal
                  have guardAllowed : CompilerGoalsNamesAllowed external origin
                      bodyResult.2.2
                      (scrutineeResult.2.1 ++
                        [Goal.eq
                          (Atom.var (compilerGeneratedName
                            scrutineeResult.2.2))
                          scrutineeResult.1]) := by
                    apply (compilerGoalsNamesAllowed_append_iff external origin
                      bodyResult.2.2 scrutineeResult.2.1 _).2
                    exact ⟨scrutineeGoalsFinal,
                      by
                        apply (compilerGoalsNamesAllowed_cons_iff external
                          origin bodyResult.2.2 _ []).2
                        exact ⟨compilerGoalNamesAllowed_eq
                          scrutineeValueFinal compiledScrutineeFinal,
                          by simp⟩⟩
                  have positiveAllowed : CompilerGoalsNamesAllowed
                      external origin bodyResult.2.2
                      ((scrutineeResult.2.1 ++
                        [Goal.eq
                          (Atom.var (compilerGeneratedName
                            scrutineeResult.2.2))
                          scrutineeResult.1]) ++ armsResult.1) := by
                    exact (compilerGoalsNamesAllowed_append_iff external origin
                      bodyResult.2.2 _ _).2 ⟨guardAllowed, armsGoalsFinal⟩
                  have failGoalsAllowed : CompilerGoalsNamesAllowed
                      external origin bodyResult.2.2
                      (bodyResult.2.1 ++
                        [Goal.eq
                          (Atom.var (compilerGeneratedName
                            (scrutineeResult.2.2 + 1)))
                          bodyResult.1]) := by
                    apply (compilerGoalsNamesAllowed_append_iff external origin
                      bodyResult.2.2 bodyResult.2.1 _).2
                    exact ⟨bodyNames.2,
                      by
                        apply (compilerGoalsNamesAllowed_cons_iff external
                          origin bodyResult.2.2 _ []).2
                        exact ⟨compilerGoalNamesAllowed_eq resultFinal
                          bodyNames.1, by simp⟩⟩
                  have negatedAllowed : CompilerGoalsNamesAllowed
                      external origin bodyResult.2.2
                      (negatedGoals
                        (scrutineeResult.2.1 ++
                          [Goal.eq
                            (Atom.var (compilerGeneratedName
                              scrutineeResult.2.2))
                            scrutineeResult.1])) :=
                    compilerGoalsNamesAllowed_negatedGoals guardAllowed
                  have fallbackAllowed : CompilerGoalsNamesAllowed
                      external origin bodyResult.2.2
                      (negatedGoals
                          (scrutineeResult.2.1 ++
                            [Goal.eq
                              (Atom.var (compilerGeneratedName
                                scrutineeResult.2.2))
                              scrutineeResult.1]) ++
                        (bodyResult.2.1 ++
                          [Goal.eq
                            (Atom.var (compilerGeneratedName
                              (scrutineeResult.2.2 + 1)))
                            bodyResult.1])) := by
                    exact (compilerGoalsNamesAllowed_append_iff external origin
                      bodyResult.2.2 _ _).2
                      ⟨negatedAllowed, failGoalsAllowed⟩
                  constructor
                  · exact resultFinal
                  · apply (compilerGoalsNamesAllowed_cons_iff external origin
                      bodyResult.2.2 _ []).2
                    constructor
                    · apply compilerGoalNamesAllowed_amb
                      · apply (compilerBranchesNamesAllowed_cons_iff external
                          origin bodyResult.2.2 _ _ _).2
                        refine ⟨resultFinal, positiveAllowed, ?_⟩
                        apply (compilerBranchesNamesAllowed_cons_iff external
                          origin bodyResult.2.2 _ _ []).2
                        exact ⟨resultFinal, fallbackAllowed, by simp⟩
                      · exact resultFinal
                    · simp

private theorem compileUnifyList_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (sources : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled :
      (do
        let (terms, compiledGoals, finalCounter) ←
          compileListFuel fuel env start sources
        .ok (chainOf (Atom.sym "unify" :: terms), compiledGoals,
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  simp only [Bind.bind, Except.bind] at compiled
  cases listEq : compileListFuel fuel env start sources with
  | error message =>
      simp only [listEq] at compiled
      contradiction
  | ok listResult =>
      simp only [listEq] at compiled
      rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
      have listNames := ih.list external origin env start sources listResult.1
        listResult.2.1 listResult.2.2 originStart envAllowed sourcesAllowed
        listEq
      constructor
      · apply chainOf_namesAllowed
        apply (compilerAtomsNamesAllowed_cons_iff external origin
          listResult.2.2 (Atom.sym "unify") listResult.1).2
        exact ⟨by simp, listNames.1⟩
      · exact listNames.2

private theorem compileSelfUnify_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (pattern thenSource elseSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (patternAllowed : CompilerAtomNamesAllowed external origin start pattern)
    (thenAllowed : CompilerAtomNamesAllowed external origin start thenSource)
    (elseAllowed : CompilerAtomNamesAllowed external origin start elseSource)
    (compiled :
      (do
        let (thenTerm, thenGoals, afterThen) ←
          compileExprFuel fuel env start thenSource
        let (elseTerm, elseGoals, afterElse) ←
          compileExprFuel fuel env afterThen elseSource
        let (result, finalCounter) := fresh afterElse
        let compiledPattern := chainify pattern
        .ok (result,
          [Goal.softcut compiledPattern [Goal.smatch compiledPattern]
            (thenGoals ++ [Goal.eq result thenTerm])
            (elseGoals ++ [Goal.eq result elseTerm])],
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  compileTwoExprThenFresh_generatedNames fuel ih external origin env start
    thenSource elseSource term goals next
    (fun thenTerm thenGoals elseTerm elseGoals result =>
      let compiledPattern := chainify pattern
      [Goal.softcut compiledPattern [Goal.smatch compiledPattern]
        (thenGoals ++ [Goal.eq result thenTerm])
        (elseGoals ++ [Goal.eq result elseTerm])])
    originStart envAllowed thenAllowed elseAllowed
    (by
      intro limit thenTerm thenGoals elseTerm elseGoals result startLimit
        thenTermAllowed thenGoalsAllowed elseTermAllowed elseGoalsAllowed
        resultAllowed
      have compiledPatternAllowed :=
        chainify_namesAllowed (patternAllowed.mono startLimit)
      apply (compilerGoalsNamesAllowed_cons_iff external origin limit _ []).2
      constructor
      · apply compilerGoalNamesAllowed_softcut compiledPatternAllowed
        · apply (compilerGoalsNamesAllowed_cons_iff external origin limit
            (Goal.smatch (chainify pattern)) []).2
          exact ⟨compilerGoalNamesAllowed_smatch compiledPatternAllowed,
            by simp⟩
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
            thenGoals [Goal.eq result thenTerm]).2
          exact ⟨thenGoalsAllowed,
            by
              apply (compilerGoalsNamesAllowed_cons_iff external origin limit
                _ []).2
              exact ⟨compilerGoalNamesAllowed_eq resultAllowed
                thenTermAllowed, by simp⟩⟩
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
            elseGoals [Goal.eq result elseTerm]).2
          exact ⟨elseGoalsAllowed,
            by
              apply (compilerGoalsNamesAllowed_cons_iff external origin limit
                _ []).2
              exact ⟨compilerGoalNamesAllowed_eq resultAllowed
                elseTermAllowed, by simp⟩⟩
      · simp)
    compiled

private theorem compileGeneralUnify_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (left right thenSource elseSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (leftAllowed : CompilerAtomNamesAllowed external origin start left)
    (rightAllowed : CompilerAtomNamesAllowed external origin start right)
    (thenAllowed : CompilerAtomNamesAllowed external origin start thenSource)
    (elseAllowed : CompilerAtomNamesAllowed external origin start elseSource)
    (compiled :
      (do
        let (leftTerm, leftGoals, afterLeft) ←
          compileExprFuel fuel env start left
        let (rightTerm, rightGoals, afterRight) ←
          compileExprFuel fuel env afterLeft right
        let (thenTerm, thenGoals, afterThen) ←
          compileExprFuel fuel env afterRight thenSource
        let (elseTerm, elseGoals, afterElse) ←
          compileExprFuel fuel env afterThen elseSource
        let (result, finalCounter) := fresh afterElse
        let carry := bindingTemplate (chainOf [leftTerm, rightTerm])
          [left, right]
        .ok (result,
          [Goal.softcut carry
            (leftGoals ++ rightGoals ++ [Goal.eq leftTerm rightTerm])
            (thenGoals ++ [Goal.eq result thenTerm])
            (elseGoals ++ [Goal.eq result elseTerm])],
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  compileFourExprThenFresh_generatedNames fuel ih external origin env start
    left right thenSource elseSource term goals next
    (fun leftTerm leftGoals rightTerm rightGoals thenTerm thenGoals elseTerm
        elseGoals result =>
      let carry := bindingTemplate (chainOf [leftTerm, rightTerm])
        [left, right]
      [Goal.softcut carry
        (leftGoals ++ rightGoals ++ [Goal.eq leftTerm rightTerm])
        (thenGoals ++ [Goal.eq result thenTerm])
        (elseGoals ++ [Goal.eq result elseTerm])])
    originStart envAllowed leftAllowed rightAllowed thenAllowed elseAllowed
    (by
      intro limit leftTerm leftGoals rightTerm rightGoals thenTerm thenGoals
        elseTerm elseGoals result startLimit leftTermAllowed leftGoalsAllowed
        rightTermAllowed rightGoalsAllowed thenTermAllowed thenGoalsAllowed
        elseTermAllowed elseGoalsAllowed resultAllowed
      have sourcePairAllowed : CompilerAtomsNamesAllowed external origin limit
          [left, right] := by
        apply (compilerAtomsNamesAllowed_cons_iff external origin limit
          left [right]).2
        exact ⟨leftAllowed.mono startLimit,
          (compilerAtomsNamesAllowed_cons_iff external origin limit right []).2
            ⟨rightAllowed.mono startLimit, by simp⟩⟩
      have compiledPairAllowed : CompilerAtomNamesAllowed external origin limit
          (chainOf [leftTerm, rightTerm]) := by
        apply chainOf_namesAllowed
        apply (compilerAtomsNamesAllowed_cons_iff external origin limit
          leftTerm [rightTerm]).2
        exact ⟨leftTermAllowed,
          (compilerAtomsNamesAllowed_cons_iff external origin limit
            rightTerm []).2 ⟨rightTermAllowed, by simp⟩⟩
      apply (compilerGoalsNamesAllowed_cons_iff external origin limit _ []).2
      constructor
      · apply compilerGoalNamesAllowed_softcut
          (bindingTemplate_namesAllowed compiledPairAllowed sourcePairAllowed)
        · simp only [compilerGoalsNamesAllowed_append_iff,
            compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact ⟨⟨leftGoalsAllowed, rightGoalsAllowed⟩,
            compilerGoalNamesAllowed_eq leftTermAllowed rightTermAllowed⟩
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
            thenGoals [Goal.eq result thenTerm]).2
          exact ⟨thenGoalsAllowed,
            by
              apply (compilerGoalsNamesAllowed_cons_iff external origin limit
                _ []).2
              exact ⟨compilerGoalNamesAllowed_eq resultAllowed
                thenTermAllowed, by simp⟩⟩
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
            elseGoals [Goal.eq result elseTerm]).2
          exact ⟨elseGoalsAllowed,
            by
              apply (compilerGoalsNamesAllowed_cons_iff external origin limit
                _ []).2
              exact ⟨compilerGoalNamesAllowed_eq resultAllowed
                elseTermAllowed, by simp⟩⟩
      · simp)
    compiled

private theorem compileSelfUnifyFromList_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (pattern thenSource elseSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start
      [Atom.sym "&self", pattern, thenSource, elseSource])
    (compiled :
      (do
        let (thenTerm, thenGoals, afterThen) ←
          compileExprFuel fuel env start thenSource
        let (elseTerm, elseGoals, afterElse) ←
          compileExprFuel fuel env afterThen elseSource
        let (result, finalCounter) := fresh afterElse
        let compiledPattern := chainify pattern
        .ok (result,
          [Goal.softcut compiledPattern [Goal.smatch compiledPattern]
            (thenGoals ++ [Goal.eq result thenTerm])
            (elseGoals ++ [Goal.eq result elseTerm])],
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  have sourceNames :
      CompilerAtomNamesAllowed external origin start pattern ∧
      CompilerAtomNamesAllowed external origin start thenSource ∧
      CompilerAtomNamesAllowed external origin start elseSource := by
    simpa [and_assoc] using sourcesAllowed
  exact compileSelfUnify_generatedNames fuel ih external origin env start
    pattern thenSource elseSource term goals next originStart envAllowed
    sourceNames.1 sourceNames.2.1 sourceNames.2.2 compiled

private theorem compileGeneralUnifyFromList_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (left right thenSource elseSource : Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start
      [left, right, thenSource, elseSource])
    (compiled :
      (do
        let (leftTerm, leftGoals, afterLeft) ←
          compileExprFuel fuel env start left
        let (rightTerm, rightGoals, afterRight) ←
          compileExprFuel fuel env afterLeft right
        let (thenTerm, thenGoals, afterThen) ←
          compileExprFuel fuel env afterRight thenSource
        let (elseTerm, elseGoals, afterElse) ←
          compileExprFuel fuel env afterThen elseSource
        let (result, finalCounter) := fresh afterElse
        let carry := bindingTemplate (chainOf [leftTerm, rightTerm])
          [left, right]
        .ok (result,
          [Goal.softcut carry
            (leftGoals ++ rightGoals ++ [Goal.eq leftTerm rightTerm])
            (thenGoals ++ [Goal.eq result thenTerm])
            (elseGoals ++ [Goal.eq result elseTerm])],
          finalCounter)) = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  have sourceNames :
      CompilerAtomNamesAllowed external origin start left ∧
      CompilerAtomNamesAllowed external origin start right ∧
      CompilerAtomNamesAllowed external origin start thenSource ∧
      CompilerAtomNamesAllowed external origin start elseSource := by
    simpa [and_assoc] using sourcesAllowed
  exact compileGeneralUnify_generatedNames fuel ih external origin env start
    left right thenSource elseSource term goals next originStart envAllowed
    sourceNames.1 sourceNames.2.1 sourceNames.2.2.1 sourceNames.2.2.2 compiled

private abbrev AppCoreGeneratedNamesFor (fuel : Nat)
    (kind : AppCoreHead) : Prop :=
  ∀ (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (head : String) (arguments : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat),
    origin ≤ start →
    CompilerEnvNamesAllowed external origin start env →
    CompilerAtomsNamesAllowed external origin start arguments →
    classifyAppCoreHead head = kind →
    compileAppCoreFuel (fuel + 1) env start head arguments =
        .ok (term, goals, next) →
      CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals

private theorem compileAppCoreFuel_hQuote_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hQuote := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
  constructor
  · apply chainify_namesAllowed
    simpa using argumentsAllowed
  · simp

private theorem compileAppCoreFuel_hPredicate_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hPredicate := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ goal _
  exact compileArgsThenFreshBin_generatedNames fuel ih external origin env
    start head "Predicate" [goal] term goals next originStart envAllowed
    (by simpa using argumentsAllowed) compiled

private theorem compileTranslatePredicateWith_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (goal term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (goalAllowed : CompilerAtomNamesAllowed external origin start goal)
    (compiled : compileTranslatePredicateWith
      (fun counter arguments =>
        compileListFuel fuel env counter arguments)
      start goal = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
      CompilerGoalsNamesAllowed external origin next goals := by
  cases goal with
  | var name => simp [compileTranslatePredicateWith] at compiled
  | sym name => simp [compileTranslatePredicateWith] at compiled
  | gnd ground => simp [compileTranslatePredicateWith] at compiled
  | expr items =>
      cases items with
      | nil => simp [compileTranslatePredicateWith] at compiled
      | cons outerHead innerArguments =>
          simp only [compileTranslatePredicateWith, Bind.bind, Except.bind]
            at compiled
          split at compiled
          · contradiction
          · rename_i listOutcome listValue listEq
            rcases listValue with ⟨terms, compiledGoals, nextCounter⟩
            simp only [fresh] at compiled
            rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
            have sourceParts :=
              (compilerAtomsNamesAllowed_cons_iff external origin start
                outerHead innerArguments).mp
                ((compilerAtomNamesAllowed_expr_iff external origin start
                  (outerHead :: innerArguments)).mp goalAllowed)
            have listCounter :=
              (compilerCounterAt fuel).list _ _ _ _ _ _ listEq
            have listNames := ih.list external origin env start innerArguments
              terms compiledGoals nextCounter originStart envAllowed
              sourceParts.2 listEq
            have stagedAllowed : CompilerAtomsNamesAllowed external origin
                nextCounter (outerHead :: terms) :=
              (compilerAtomsNamesAllowed_cons_iff external origin nextCounter
                outerHead terms).2
                ⟨sourceParts.1.mono listCounter, listNames.1⟩
            have predicateAllowed : CompilerAtomNamesAllowed external origin
                nextCounter (chainify (Atom.expr (outerHead :: terms))) :=
              chainify_namesAllowed
                ((compilerAtomNamesAllowed_expr_iff external origin nextCounter
                  (outerHead :: terms)).2 stagedAllowed)
            have resultAllowed : CompilerAtomNamesAllowed external origin
                (nextCounter + 1)
                (Atom.var (compilerGeneratedName nextCounter)) := by
              simp only [compilerAtomNamesAllowed_var_iff]
              exact .generated (Nat.le_trans originStart listCounter) (by omega)
            constructor
            · exact resultAllowed
            · apply (compilerGoalsNamesAllowed_append_iff external origin
                  (nextCounter + 1) compiledGoals
                  [Goal.bin "translatePredicate"
                    [chainify (Atom.expr (outerHead :: terms))]
                    (Atom.var (compilerGeneratedName nextCounter))]).2
              constructor
              · exact listNames.2.mono (Nat.le_succ nextCounter)
              · simp only [compilerGoalsNamesAllowed_cons_iff,
                    compilerGoalsNamesAllowed_nil, and_true]
                exact compilerGoalNamesAllowed_bin
                  (by simpa using
                    predicateAllowed.mono (Nat.le_succ nextCounter))
                  resultAllowed "translatePredicate"

private theorem compileAppCoreFuel_hTranslatePredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hTranslatePredicate := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ goal _
  exact compileTranslatePredicateWith_generatedNames fuel ih external origin
    env start goal term goals next originStart envAllowed
    (by simpa using argumentsAllowed) compiled

private theorem compileAppCoreFuel_hCallPredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCallPredicate := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ predicate _
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    predicate term goals next
    (fun compiledTerm compiledGoals result =>
      compiledGoals ++ [Goal.bin "translatePredicate" [compiledTerm] result])
    originStart envAllowed
    (by simpa using argumentsAllowed)
    (by
      intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
        resultAllowed
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        compiledGoals [Goal.bin "translatePredicate" [compiledTerm] result]).2
      constructor
      · exact goalsAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_bin (by simpa using termAllowed)
          resultAllowed "translatePredicate")
    compiled

local macro "solve_one_expr_wact_generated_names" fuel:ident ih:ident
    operation:str : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     rename_i _ _ source _
     exact compileExprThenFresh_generatedNames $fuel $ih external origin env
       start source term goals next
       (fun compiledTerm compiledGoals result =>
         compiledGoals ++ [Goal.wact $operation [compiledTerm] result])
       originStart envAllowed (by simpa using argumentsAllowed)
       (by
         intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
           resultAllowed
         apply (compilerGoalsNamesAllowed_append_iff external origin limit
           compiledGoals [Goal.wact $operation [compiledTerm] result]).2
         constructor
         · exact goalsAllowed
         · simp only [compilerGoalsNamesAllowed_cons_iff,
             compilerGoalsNamesAllowed_nil, and_true]
           exact compilerGoalNamesAllowed_wact (by simpa using termAllowed)
             resultAllowed $operation)
       compiled))

local macro "solve_one_expr_bin_generated_names" fuel:ident ih:ident
    operation:str : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     rename_i _ _ source _
     exact compileExprThenFresh_generatedNames $fuel $ih external origin env
       start source term goals next
       (fun compiledTerm compiledGoals result =>
         compiledGoals ++ [Goal.bin $operation [compiledTerm] result])
       originStart envAllowed (by simpa using argumentsAllowed)
       (by
         intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
           resultAllowed
         apply (compilerGoalsNamesAllowed_append_iff external origin limit
           compiledGoals [Goal.bin $operation [compiledTerm] result]).2
         constructor
         · exact goalsAllowed
         · simp only [compilerGoalsNamesAllowed_cons_iff,
             compilerGoalsNamesAllowed_nil, and_true]
           exact compilerGoalNamesAllowed_bin (by simpa using termAllowed)
             resultAllowed $operation)
       compiled))

private theorem compileAppCoreFuel_hAssertaPredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hAssertaPredicate := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_wact_generated_names fuel ih "assertaPredicate"

private theorem compileAppCoreFuel_hAssertzPredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hAssertzPredicate := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_wact_generated_names fuel ih "assertzPredicate"

private theorem compileAppCoreFuel_hRetractPredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hRetractPredicate := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_wact_generated_names fuel ih "retractPredicate"

private theorem compileAppCoreFuel_hProcessMettaString_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hProcessMettaString := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_wact_generated_names fuel ih "process_metta_string"

private theorem compileAppCoreFuel_hGetType_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hGetType := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_bin_generated_names fuel ih "get-type"

private theorem compileAppCoreFuel_hGetMetatype_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hGetMetatype := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_bin_generated_names fuel ih "get-metatype"

local macro "solve_direct_app_generated_names" fuel:ident ih:ident : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     all_goals
       exact CompilerGeneratedNamesAt.app $ih external origin env start _ _
         term goals next originStart envAllowed (by
           simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
         compiled))

private theorem compileAppCoreFuel_hTrace_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hTrace := by
  unfold AppCoreGeneratedNamesFor
  solve_direct_app_generated_names fuel ih

private theorem compileAppCoreFuel_hHashPlus_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hHashPlus := by
  unfold AppCoreGeneratedNamesFor
  solve_direct_app_generated_names fuel ih

private theorem compileAppCoreFuel_hHashMinus_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hHashMinus := by
  unfold AppCoreGeneratedNamesFor
  solve_direct_app_generated_names fuel ih

private theorem compileAppCoreFuel_hFor_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hFor := by
  unfold AppCoreGeneratedNamesFor
  solve_direct_app_generated_names fuel ih

private theorem compileAppCoreFuel_hReduce_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hReduce := by
  unfold AppCoreGeneratedNamesFor
  solve_direct_app_generated_names fuel ih

private theorem compileAppCoreFuel_hGetTypeSpace_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hGetTypeSpace := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ space source _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start space ∧
      CompilerAtomNamesAllowed external origin start source := by
    simpa using argumentsAllowed
  exact ih.app external origin env start "get-type" [source] term goals next
    originStart envAllowed (by simpa using pairAllowed.2) compiled

private theorem compileAppCoreFuel_hEmpty_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hEmpty := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
  constructor
  · simp [compilerTrueA]
  · simp only [compilerGoalsNamesAllowed_cons_iff,
      compilerGoalsNamesAllowed_nil, and_true]
    exact compilerGoalNamesAllowed_eq (by simp [compilerTrueA]) (by simp [compilerFalseA])

private theorem compileAppCoreFuel_hCut_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCut := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
  constructor <;> simp [CompilerNamesAllowed, specializationGoalVars, compilerTrueA]

private theorem compileAppCoreFuel_hUnquote_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hUnquote := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  · rename_i _ _ expression _
    exact ih.app external origin env start "eval" [expression] term goals next
      originStart envAllowed (by simpa using argumentsAllowed) compiled
  · rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    constructor
    · apply chainify_namesAllowed
      simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed
    · simp

private theorem compileAppCoreFuel_hWithMutex_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hWithMutex := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ mutex body _
  have bodyAllowed : CompilerAtomNamesAllowed external origin start body := by
    have pair : CompilerAtomNamesAllowed external origin start mutex ∧
        CompilerAtomNamesAllowed external origin start body := by
      simpa using argumentsAllowed
    exact pair.2
  exact ih.expr external origin env start body term goals next originStart
    envAllowed bodyAllowed compiled

private theorem compileAppCoreFuel_hGetState_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hGetState := by
  unfold AppCoreGeneratedNamesFor
  solve_one_expr_wact_generated_names fuel ih "get-state"

private theorem compileAppCoreFuel_hCollapse_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCollapse := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    source term goals next
    (fun compiledTerm compiledGoals result =>
      [Goal.findall compiledTerm compiledGoals result])
    originStart envAllowed (by simpa using argumentsAllowed)
    (by
      intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
        resultAllowed
      simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      exact compilerGoalNamesAllowed_findall termAllowed goalsAllowed
        resultAllowed)
    compiled

private theorem compileAppCoreFuel_hOnce_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hOnce := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    source term goals next
    (fun compiledTerm compiledGoals result =>
      [Goal.onceg compiledTerm compiledGoals result])
    originStart envAllowed (by simpa using argumentsAllowed)
    (by
      intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
        resultAllowed
      simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      exact compilerGoalNamesAllowed_onceg termAllowed goalsAllowed
        resultAllowed)
    compiled

private theorem compileAppCoreFuel_hEval_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hEval := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  simp only [fresh] at compiled
  rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
  have sourceAllowed : CompilerAtomNamesAllowed external origin start
      (chainify source) := by
    apply chainify_namesAllowed
    simpa using argumentsAllowed
  have resultAllowed : CompilerAtomNamesAllowed external origin (start + 1)
      (Atom.var (compilerGeneratedName start)) := by
    simp only [compilerAtomNamesAllowed_var_iff]
    exact .generated originStart (by omega)
  constructor
  · exact resultAllowed
  · simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
    exact compilerGoalNamesAllowed_evalg
      (sourceAllowed.mono (Nat.le_succ start)) resultAllowed

private theorem compileAppCoreFuel_hCatch_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCatch := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    source term goals next
    (fun compiledTerm compiledGoals result =>
      [Goal.catchg compiledTerm compiledGoals result])
    originStart envAllowed (by simpa using argumentsAllowed)
    (by
      intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
        resultAllowed
      simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      exact compilerGoalNamesAllowed_catchg termAllowed goalsAllowed
        resultAllowed)
    compiled

private theorem compileAppCoreFuel_hGetAtoms_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hGetAtoms := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  exact compileExprThenFresh_generatedNames fuel ih external origin env start
    source term goals next
    (fun compiledTerm compiledGoals result =>
      compiledGoals ++ [Goal.smatch (spacePat compiledTerm result)])
    originStart envAllowed (by simpa using argumentsAllowed)
    (by
      intro limit compiledTerm compiledGoals result _ termAllowed goalsAllowed
        resultAllowed
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        compiledGoals [Goal.smatch (spacePat compiledTerm result)]).2
      exact ⟨goalsAllowed, by
        simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_smatch
          (spacePat_namesAllowed termAllowed resultAllowed)⟩)
    compiled

private theorem compileAppCoreFuel_hAndThen_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hAndThen := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ first second _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start first ∧
      CompilerAtomNamesAllowed external origin start second := by
    simpa using argumentsAllowed
  exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
    start first second term goals next
    (fun firstTerm firstGoals secondTerm secondGoals result =>
      firstGoals ++ [Goal.ite firstTerm
        (result, secondGoals ++ [Goal.eq result secondTerm])
        (result, [Goal.eq result compilerFalseA]) result])
    originStart envAllowed pairAllowed.1 pairAllowed.2
    (by
      intro limit firstTerm firstGoals secondTerm secondGoals result _
        firstTermAllowed firstGoalsAllowed secondTermAllowed secondGoalsAllowed
        resultAllowed
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        firstGoals [Goal.ite firstTerm
          (result, secondGoals ++ [Goal.eq result secondTerm])
          (result, [Goal.eq result compilerFalseA]) result]).2
      constructor
      · exact firstGoalsAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        apply compilerGoalNamesAllowed_ite firstTermAllowed resultAllowed
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
              secondGoals [Goal.eq result secondTerm]).2
          exact ⟨secondGoalsAllowed, by
            simp only [compilerGoalsNamesAllowed_cons_iff,
              compilerGoalsNamesAllowed_nil, and_true]
            exact compilerGoalNamesAllowed_eq resultAllowed secondTermAllowed⟩
        · exact resultAllowed
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerFalseA])
        · exact resultAllowed)
    compiled

private theorem compileAppCoreFuel_hOrElse_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hOrElse := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ first second _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start first ∧
      CompilerAtomNamesAllowed external origin start second := by
    simpa using argumentsAllowed
  exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
    start first second term goals next
    (fun firstTerm firstGoals secondTerm secondGoals result =>
      firstGoals ++ [Goal.ite firstTerm
        (result, [Goal.eq result compilerTrueA])
        (result, secondGoals ++ [Goal.eq result secondTerm]) result])
    originStart envAllowed pairAllowed.1 pairAllowed.2
    (by
      intro limit firstTerm firstGoals secondTerm secondGoals result _
        firstTermAllowed firstGoalsAllowed secondTermAllowed secondGoalsAllowed
        resultAllowed
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        firstGoals [Goal.ite firstTerm
          (result, [Goal.eq result compilerTrueA])
          (result, secondGoals ++ [Goal.eq result secondTerm]) result]).2
      constructor
      · exact firstGoalsAllowed
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        apply compilerGoalNamesAllowed_ite firstTermAllowed resultAllowed
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerTrueA])
        · exact resultAllowed
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
              secondGoals [Goal.eq result secondTerm]).2
          exact ⟨secondGoalsAllowed, by
            simp only [compilerGoalsNamesAllowed_cons_iff,
              compilerGoalsNamesAllowed_nil, and_true]
            exact compilerGoalNamesAllowed_eq resultAllowed secondTermAllowed⟩
        · exact resultAllowed)
    compiled

private theorem compileAppCoreFuel_hCons_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCons := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ first second _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start first ∧
      CompilerAtomNamesAllowed external origin start second := by
    simpa using argumentsAllowed
  exact compileTwoExpr_generatedNames fuel ih external origin env start first
    second term goals next consC
    (fun _ firstGoals _ secondGoals => firstGoals ++ secondGoals)
    originStart envAllowed pairAllowed.1 pairAllowed.2
    (by
      intro limit firstTerm firstGoals secondTerm secondGoals _ firstTermAllowed
        firstGoalsAllowed secondTermAllowed secondGoalsAllowed
      exact ⟨consC_namesAllowed firstTermAllowed secondTermAllowed,
        (compilerGoalsNamesAllowed_append_iff external origin limit
          firstGoals secondGoals).2 ⟨firstGoalsAllowed, secondGoalsAllowed⟩⟩)
    compiled

private theorem compileAppCoreFuel_hChangeState_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hChangeState := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ first second _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start first ∧
      CompilerAtomNamesAllowed external origin start second := by
    simpa using argumentsAllowed
  exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
    start first second term goals next
    (fun firstTerm firstGoals secondTerm secondGoals result =>
      firstGoals ++ secondGoals ++
        [Goal.wact "change-state!" [firstTerm, secondTerm] result])
    originStart envAllowed pairAllowed.1 pairAllowed.2
    (by
      intro limit firstTerm firstGoals secondTerm secondGoals result _
        firstTermAllowed firstGoalsAllowed secondTermAllowed secondGoalsAllowed
        resultAllowed
      rw [List.append_assoc]
      apply (compilerGoalsNamesAllowed_append_iff external origin limit
        firstGoals (secondGoals ++
          [Goal.wact "change-state!" [firstTerm, secondTerm] result])).2
      exact ⟨firstGoalsAllowed, by
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          secondGoals [Goal.wact "change-state!" [firstTerm, secondTerm] result]).2
        exact ⟨secondGoalsAllowed, by
          simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_wact (by simpa using
            (And.intro firstTermAllowed secondTermAllowed)) resultAllowed
            "change-state!"⟩⟩)
    compiled

private theorem compileAppCoreFuel_hEqual_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hEqual := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ first second _
  have pairAllowed :
      CompilerAtomNamesAllowed external origin start first ∧
      CompilerAtomNamesAllowed external origin start second := by
    simpa using argumentsAllowed
  exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
    start first second term goals next
    (fun firstTerm firstGoals secondTerm secondGoals result =>
      [Goal.softcut (bindingTemplate (chainOf [firstTerm, secondTerm])
          [first, second])
        (firstGoals ++ secondGoals ++ [Goal.eq firstTerm secondTerm])
        [Goal.eq result compilerTrueA] [Goal.eq result compilerFalseA]])
    originStart envAllowed pairAllowed.1 pairAllowed.2
    (by
      intro limit firstTerm firstGoals secondTerm secondGoals result startLimit
        firstTermAllowed firstGoalsAllowed secondTermAllowed secondGoalsAllowed
        resultAllowed
      simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      apply compilerGoalNamesAllowed_softcut
      · apply bindingTemplate_namesAllowed
        · exact chainOf_namesAllowed (by simpa using
            (And.intro firstTermAllowed secondTermAllowed))
        · exact (by simpa using
            (And.intro (pairAllowed.1.mono startLimit)
              (pairAllowed.2.mono startLimit)))
      · rw [List.append_assoc]
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          firstGoals (secondGoals ++ [Goal.eq firstTerm secondTerm])).2
        exact ⟨firstGoalsAllowed, by
          apply (compilerGoalsNamesAllowed_append_iff external origin limit
            secondGoals [Goal.eq firstTerm secondTerm]).2
          exact ⟨secondGoalsAllowed, by
            simp only [compilerGoalsNamesAllowed_cons_iff,
              compilerGoalsNamesAllowed_nil, and_true]
            exact compilerGoalNamesAllowed_eq firstTermAllowed secondTermAllowed⟩⟩
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerTrueA])
      · simp only [compilerGoalsNamesAllowed_cons_iff,
          compilerGoalsNamesAllowed_nil, and_true]
        exact compilerGoalNamesAllowed_eq resultAllowed (by simp [compilerFalseA]))
    compiled

private theorem compileAppCoreFuel_hIf_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hIf := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  · rename_i _ _ condition thenSource _
    have pairAllowed :
        CompilerAtomNamesAllowed external origin start condition ∧
        CompilerAtomNamesAllowed external origin start thenSource := by
      simpa using argumentsAllowed
    exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
      start condition thenSource term goals next
      (fun conditionTerm conditionGoals thenTerm thenGoals result =>
        let thenCompiled := compileBranch result (thenTerm, thenGoals)
        thenCompiled.1 ++ conditionGoals ++
          [Goal.ite conditionTerm thenCompiled.2
            (result, [Goal.eq compilerTrueA compilerFalseA]) result])
      originStart envAllowed pairAllowed.1 pairAllowed.2
      (by
        intro limit conditionTerm conditionGoals thenTerm thenGoals result _
          conditionAllowed conditionGoalsAllowed thenTermAllowed
          thenGoalsAllowed resultAllowed
        have thenAllowed := compileBranch_namesAllowed resultAllowed
          thenTermAllowed thenGoalsAllowed rfl
        rw [List.append_assoc]
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          (compileBranch result (thenTerm, thenGoals)).1
          (conditionGoals ++
            [Goal.ite conditionTerm
              (compileBranch result (thenTerm, thenGoals)).2
              (result, [Goal.eq compilerTrueA compilerFalseA]) result])).2
        constructor
        · exact thenAllowed.1
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
              conditionGoals
              [Goal.ite conditionTerm
                (compileBranch result (thenTerm, thenGoals)).2
                (result, [Goal.eq compilerTrueA compilerFalseA]) result]).2
          constructor
          · exact conditionGoalsAllowed
          · simp only [compilerGoalsNamesAllowed_cons_iff,
              compilerGoalsNamesAllowed_nil, and_true]
            apply compilerGoalNamesAllowed_ite conditionAllowed thenAllowed.2.1
              thenAllowed.2.2 resultAllowed
            · simp only [compilerGoalsNamesAllowed_cons_iff,
                compilerGoalsNamesAllowed_nil, and_true]
              exact compilerGoalNamesAllowed_eq (by simp [compilerTrueA])
                (by simp [compilerFalseA])
            · exact resultAllowed)
      compiled
  · rename_i _ _ condition thenSource elseSource _
    have tripleAllowed :
        CompilerAtomNamesAllowed external origin start condition ∧
        CompilerAtomNamesAllowed external origin start thenSource ∧
        CompilerAtomNamesAllowed external origin start elseSource := by
      simpa [and_assoc] using argumentsAllowed
    exact compileThreeExprThenFresh_generatedNames fuel ih external origin env
      start condition thenSource elseSource term goals next
      (fun conditionTerm conditionGoals thenTerm thenGoals elseTerm elseGoals
          result =>
        let thenCompiled := compileBranch result (thenTerm, thenGoals)
        let elseCompiled := compileBranch result (elseTerm, elseGoals)
        thenCompiled.1 ++ elseCompiled.1 ++ conditionGoals ++
          [Goal.ite conditionTerm thenCompiled.2 elseCompiled.2 result])
      originStart envAllowed tripleAllowed.1 tripleAllowed.2.1
      tripleAllowed.2.2
      (by
        intro limit conditionTerm conditionGoals thenTerm thenGoals elseTerm
          elseGoals result _ conditionAllowed conditionGoalsAllowed
          thenTermAllowed thenGoalsAllowed elseTermAllowed elseGoalsAllowed
          resultAllowed
        have thenAllowed := compileBranch_namesAllowed resultAllowed
          thenTermAllowed thenGoalsAllowed rfl
        have elseAllowed := compileBranch_namesAllowed resultAllowed
          elseTermAllowed elseGoalsAllowed rfl
        rw [List.append_assoc, List.append_assoc]
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          (compileBranch result (thenTerm, thenGoals)).1
          ((compileBranch result (elseTerm, elseGoals)).1 ++
            (conditionGoals ++
              [Goal.ite conditionTerm
                (compileBranch result (thenTerm, thenGoals)).2
                (compileBranch result (elseTerm, elseGoals)).2 result]))).2
        constructor
        · exact thenAllowed.1
        · apply (compilerGoalsNamesAllowed_append_iff external origin limit
              (compileBranch result (elseTerm, elseGoals)).1
              (conditionGoals ++
                [Goal.ite conditionTerm
                  (compileBranch result (thenTerm, thenGoals)).2
                  (compileBranch result (elseTerm, elseGoals)).2 result])).2
          constructor
          · exact elseAllowed.1
          · apply (compilerGoalsNamesAllowed_append_iff external origin limit
                conditionGoals
                [Goal.ite conditionTerm
                  (compileBranch result (thenTerm, thenGoals)).2
                  (compileBranch result (elseTerm, elseGoals)).2 result]).2
            constructor
            · exact conditionGoalsAllowed
            · simp only [compilerGoalsNamesAllowed_cons_iff,
                compilerGoalsNamesAllowed_nil, and_true]
              exact compilerGoalNamesAllowed_ite conditionAllowed
                thenAllowed.2.1 thenAllowed.2.2 elseAllowed.2.1
                elseAllowed.2.2 resultAllowed)
      compiled

local macro "solve_three_expr_eq_generated_names" fuel:ident ih:ident : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     rename_i _ _ first second third _
     have tripleAllowed :
         CompilerAtomNamesAllowed external origin start first ∧
         CompilerAtomNamesAllowed external origin start second ∧
         CompilerAtomNamesAllowed external origin start third := by
       simpa [and_assoc] using argumentsAllowed
     exact compileThreeExpr_generatedNames $fuel $ih external origin env start
       first second third term goals next (fun _ _ thirdTerm => thirdTerm)
       (fun firstTerm firstGoals secondTerm secondGoals _ thirdGoals =>
         [Goal.eq firstTerm secondTerm] ++ firstGoals ++ secondGoals ++
           thirdGoals)
       originStart envAllowed tripleAllowed.1 tripleAllowed.2.1
       tripleAllowed.2.2
       (by
         intro limit firstTerm firstGoals secondTerm secondGoals thirdTerm
           thirdGoals firstTermAllowed firstGoalsAllowed secondTermAllowed
           secondGoalsAllowed thirdTermAllowed thirdGoalsAllowed
         constructor
         · exact thirdTermAllowed
         · simp only [List.singleton_append]
           apply (compilerGoalsNamesAllowed_cons_iff external origin limit
             (Goal.eq firstTerm secondTerm)
             (firstGoals ++ secondGoals ++ thirdGoals)).2
           constructor
           · exact compilerGoalNamesAllowed_eq firstTermAllowed
               secondTermAllowed
           · rw [List.append_assoc]
             apply (compilerGoalsNamesAllowed_append_iff external origin limit
               firstGoals (secondGoals ++ thirdGoals)).2
             exact ⟨firstGoalsAllowed,
               (compilerGoalsNamesAllowed_append_iff external origin limit
                 secondGoals thirdGoals).2
                 ⟨secondGoalsAllowed, thirdGoalsAllowed⟩⟩)
       compiled))

private theorem compileAppCoreFuel_hLet_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hLet := by
  unfold AppCoreGeneratedNamesFor
  solve_three_expr_eq_generated_names fuel ih

private theorem compileAppCoreFuel_hChain_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hChain := by
  unfold AppCoreGeneratedNamesFor
  solve_three_expr_eq_generated_names fuel ih

private theorem compileAppCoreFuel_hLetStar_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hLetStar := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ bindings body _
  have inputsAllowed :
      CompilerAtomsNamesAllowed external origin start bindings ∧
      CompilerAtomNamesAllowed external origin start body := by
    simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed
  cases desugaredEq : desugarLetStar? bindings body with
  | none =>
      simp only [desugaredEq] at compiled
      contradiction
  | some nested =>
      simp only [desugaredEq] at compiled
      exact ih.expr external origin env start nested term goals next originStart
        envAllowed
        (desugarLetStar_namesAllowed inputsAllowed.1 inputsAllowed.2
          desugaredEq)
        compiled

private theorem compileAppCoreFuel_hProgn_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hProgn := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  rename_i notEmptyTrue
  have notEmpty : arguments.isEmpty = false := by
    cases isEmptyEq : arguments.isEmpty <;> simp_all
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i result compiledList
    rcases result with ⟨terms, compiledGoals, nextCounter⟩
    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    have termsNotEmpty : terms.isEmpty = false := by
      cases arguments with
      | nil => simp at notEmpty
      | cons source sources =>
          exact compileListFuel_terms_isEmpty_false compiledList
    have classifiedNames := ih.list external origin env start arguments
      terms compiledGoals nextCounter originStart envAllowed
      argumentsAllowed compiledList
    exact ⟨classifiedNames.1.atom_mem
        (list_getLast_bang_mem_of_isEmpty_false termsNotEmpty),
      classifiedNames.2⟩

private theorem compileAppCoreFuel_hProg1_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hProg1 := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  rename_i notEmptyTrue
  have notEmpty : arguments.isEmpty = false := by
    cases isEmptyEq : arguments.isEmpty <;> simp_all
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i result compiledList
    rcases result with ⟨terms, compiledGoals, nextCounter⟩
    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    have termsNotEmpty : terms.isEmpty = false := by
      cases arguments with
      | nil => simp at notEmpty
      | cons source sources =>
          exact compileListFuel_terms_isEmpty_false compiledList
    have classifiedNames := ih.list external origin env start arguments
      terms compiledGoals nextCounter originStart envAllowed
      argumentsAllowed compiledList
    exact ⟨classifiedNames.1.atom_mem
        (list_head_bang_mem_of_isEmpty_false termsNotEmpty),
      classifiedNames.2⟩

private theorem compileAppCoreFuel_hTransaction_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hTransaction := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ body _
  have bodyAllowed :
      CompilerAtomNamesAllowed external origin start body := by
    simpa using argumentsAllowed
  simp only [Bind.bind, Except.bind] at compiled
  split at compiled
  · contradiction
  · rename_i bodyResult bodyEq
    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    have bodyNames := ih.expr external origin env start body bodyResult.1
      bodyResult.2.1 bodyResult.2.2 originStart envAllowed bodyAllowed bodyEq
    constructor
    · exact bodyNames.1
    · simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      apply compilerGoalNamesAllowed_transactiong
      · apply bindingTemplate_namesAllowed bodyNames.1
        simpa using bodyAllowed.mono
          (compileExprFuel_counter_mono fuel env start body bodyResult.1
            bodyResult.2.1 bodyResult.2.2 bodyEq)
      · exact bodyNames.2

private theorem compileAppCoreFuel_hUnique_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hUnique := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ source _
  have sourceAllowed :
      CompilerAtomNamesAllowed external origin start source := by
    simpa using argumentsAllowed
  exact compileExprThenThreeFresh_generatedNames fuel ih external origin env
    start source term goals next
    (fun compiledTerm compiledGoals collected deduplicated result =>
      [Goal.findall compiledTerm compiledGoals collected,
        Goal.bin "unique-atom" [collected] deduplicated,
        Goal.spread deduplicated result])
    originStart envAllowed sourceAllowed
    (by
      intro limit compiledTerm compiledGoals collected deduplicated result _
        compiledTermAllowed compiledGoalsAllowed collectedAllowed
        deduplicatedAllowed resultAllowed
      simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      constructor
      · exact compilerGoalNamesAllowed_findall compiledTermAllowed
          compiledGoalsAllowed collectedAllowed
      · constructor
        · exact compilerGoalNamesAllowed_bin (by simpa using collectedAllowed)
            deduplicatedAllowed _
        · exact compilerGoalNamesAllowed_spread deduplicatedAllowed
            resultAllowed)
    compiled

local macro "solve_binary_stream_set_generated_names" fuel:ident ih:ident
    operation:str : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     rename_i _ _ firstSource secondSource _
     have sourcesAllowed :
         CompilerAtomNamesAllowed external origin start firstSource ∧
         CompilerAtomNamesAllowed external origin start secondSource := by
       simpa using argumentsAllowed
     exact compileTwoExprThenFourFresh_generatedNames $fuel $ih external
       origin env start firstSource secondSource term goals next
       (fun firstTerm firstGoals secondTerm secondGoals firstCollected
           secondCollected combined result =>
         [Goal.findall firstTerm firstGoals firstCollected,
           Goal.findall secondTerm secondGoals secondCollected,
           Goal.bin $operation [firstCollected, secondCollected] combined,
           Goal.spread combined result])
       originStart envAllowed sourcesAllowed.1 sourcesAllowed.2
       (by
         intro limit firstTerm firstGoals secondTerm secondGoals firstCollected
           secondCollected combined result _ firstTermAllowed
           firstGoalsAllowed secondTermAllowed secondGoalsAllowed
           firstCollectedAllowed secondCollectedAllowed combinedAllowed
           resultAllowed
         simp only [compilerGoalsNamesAllowed_cons_iff,
           compilerGoalsNamesAllowed_nil, and_true]
         constructor
         · exact compilerGoalNamesAllowed_findall firstTermAllowed
             firstGoalsAllowed firstCollectedAllowed
         · constructor
           · exact compilerGoalNamesAllowed_findall secondTermAllowed
               secondGoalsAllowed secondCollectedAllowed
           · constructor
             · exact compilerGoalNamesAllowed_bin
                 (by
                   simpa using
                     (And.intro firstCollectedAllowed secondCollectedAllowed))
                 combinedAllowed _
             · exact compilerGoalNamesAllowed_spread combinedAllowed
                 resultAllowed)
       compiled))

private theorem compileAppCoreFuel_hUnion_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hUnion := by
  unfold AppCoreGeneratedNamesFor
  solve_binary_stream_set_generated_names fuel ih "union-atom"

private theorem compileAppCoreFuel_hIntersection_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hIntersection := by
  unfold AppCoreGeneratedNamesFor
  solve_binary_stream_set_generated_names fuel ih "intersection-atom"

private theorem compileAppCoreFuel_hSubtraction_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hSubtraction := by
  unfold AppCoreGeneratedNamesFor
  solve_binary_stream_set_generated_names fuel ih "subtraction-atom"

private theorem compileAppCoreFuel_hSucceedsPredicate_generatedNames
    (fuel : Nat) (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hSucceedsPredicate := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ space relation remaining _
  have expressionAllowed : CompilerAtomNamesAllowed external origin start
      (Atom.expr (space :: Atom.sym relation :: remaining)) := by
    simpa using argumentsAllowed
  have splitAllowed := compilerAtomExprCons_namesAllowed expressionAllowed
  have patternAllowed : CompilerAtomNamesAllowed external origin start
      (Atom.expr (Atom.sym relation :: remaining)) :=
    (compilerAtomNamesAllowed_expr_iff external origin start _).2
      splitAllowed.2
  exact compileSpaceBoolean_generatedNames fuel ih external origin env start
    space (Atom.expr (Atom.sym relation :: remaining)) term goals next
    originStart envAllowed splitAllowed.1 patternAllowed compiled

private theorem compileAppCoreFuel_hFind_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hFind := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ space pattern _
  have sourcesAllowed :
      CompilerAtomNamesAllowed external origin start space ∧
      CompilerAtomNamesAllowed external origin start pattern := by
    simpa using argumentsAllowed
  exact compileSpaceBoolean_generatedNames fuel ih external origin env start
    space pattern term goals next originStart envAllowed sourcesAllowed.1
    sourcesAllowed.2 compiled

local macro "solve_world_data_action_generated_names" fuel:ident ih:ident
    operation:str : tactic =>
  `(tactic|
    (intro external origin env start head arguments term goals next originStart
       envAllowed argumentsAllowed classified compiled
     change compileAppCoreFuel (Nat.succ $fuel) env start head arguments =
       .ok (term, goals, next) at compiled
     rw [compileAppCoreFuel.eq_def] at compiled
     simp only [classified] at compiled
     split at compiled <;> try contradiction
     all_goals try
       exact compileAppDefaultWith_compiler_generatedNames $fuel $ih external
         origin env start head _ term goals next originStart envAllowed
         argumentsAllowed compiled
     all_goals try (repeat' split at compiled)
     all_goals
       exact compileWorldDataAction_generatedNames $fuel $ih external origin
         env start $operation _ _ term goals next originStart envAllowed
         (by simpa using argumentsAllowed) compiled))

private theorem compileAppCoreFuel_hAddAtom_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hAddAtom := by
  unfold AppCoreGeneratedNamesFor
  solve_world_data_action_generated_names fuel ih "add-atom"

private theorem compileAppCoreFuel_hRemoveAtom_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hRemoveAtom := by
  unfold AppCoreGeneratedNamesFor
  solve_world_data_action_generated_names fuel ih "remove-atom"

private theorem compileAppCoreFuel_hCall_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCall := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try
    exact compileExprThenFresh_generatedNames fuel ih external origin env
      start _ term goals next
      (fun compiledTerm compiledGoals result => compiledGoals ++
        [Goal.spread compiledTerm result])
      originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      (by
        intro limit compiledTerm compiledGoals result _ compiledTermAllowed
          compiledGoalsAllowed resultAllowed
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          compiledGoals [Goal.spread compiledTerm result]).2
        constructor
        · exact compiledGoalsAllowed
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_spread compiledTermAllowed
            resultAllowed)
      compiled
  all_goals
    exact compileArgsThenFreshCall_generatedNames fuel ih external origin env
      start _ _ term goals next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      compiled

private theorem compileAppCoreFuel_hDoubleEqual_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hDoubleEqual := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try (repeat' split at compiled)
  all_goals try contradiction
  all_goals
    exact compileExprThenFreshFoldEquality_generatedNames fuel ih external
      origin env start _ _ term goals next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      compiled

private theorem compileAppCoreFuel_hBind_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hBind := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try
    exact ih.app external origin env start "change-state!" [_, _] term goals
      next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      compiled
  all_goals
    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    constructor
    · simp [compilerTrueA]
    · simp only [compilerGoalsNamesAllowed_cons_iff,
        compilerGoalsNamesAllowed_nil, and_true]
      exact compilerGoalNamesAllowed_eq (by simp [compilerTrueA]) (by simp [compilerFalseA])

private theorem compileAppCoreFuel_hSuperpose_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hSuperpose := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try
    exact compileNonemptySuperposeThenFresh_generatedNames fuel ih external
      origin env
      start
      _ term goals next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      compiled
  all_goals
    exact compileExprThenFresh_generatedNames fuel ih external origin env start
      _ term goals next
      (fun compiledTerm compiledGoals result => compiledGoals ++
        [Goal.spread compiledTerm result])
      originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      (by
        intro limit compiledTerm compiledGoals result _ compiledTermAllowed
          compiledGoalsAllowed resultAllowed
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          compiledGoals [Goal.spread compiledTerm result]).2
        constructor
        · exact compiledGoalsAllowed
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact compilerGoalNamesAllowed_spread compiledTermAllowed
            resultAllowed)
      compiled

private theorem compileAppCoreFuel_hHyperpose_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hHyperpose := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try
    exact compileAmbThenFresh_generatedNames fuel ih external origin env start
      _ term goals next originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      compiled
  all_goals
    exact compileExprThenTwoFresh_generatedNames fuel ih external origin env
      start _ term goals next
      (fun compiledTerm compiledGoals intermediate result =>
        compiledGoals ++ [Goal.spread compiledTerm intermediate,
          Goal.evalg intermediate result])
      originStart envAllowed
      (by simpa [CompilerNamesAllowed, Atom.vars] using argumentsAllowed)
      (by
        intro limit compiledTerm compiledGoals intermediate result _
          compiledTermAllowed compiledGoalsAllowed intermediateAllowed
          resultAllowed
        apply (compilerGoalsNamesAllowed_append_iff external origin limit
          compiledGoals [Goal.spread compiledTerm intermediate,
            Goal.evalg intermediate result]).2
        constructor
        · exact compiledGoalsAllowed
        · simp only [compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact ⟨compilerGoalNamesAllowed_spread compiledTermAllowed
            intermediateAllowed,
            compilerGoalNamesAllowed_evalg intermediateAllowed resultAllowed⟩)
      compiled

private theorem compileAppCoreFuel_hTest_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hTest := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ expression expected _
  have sourcesAllowed :
      CompilerAtomNamesAllowed external origin start expression ∧
      CompilerAtomNamesAllowed external origin start expected := by
    simpa using argumentsAllowed
  exact compileExprFreshExprFresh_generatedNames fuel ih external origin env
    start expression expected term goals next
    (fun expressionTerm expressionGoals answers expectedTerm expectedGoals
        result =>
      [Goal.findall expressionTerm expressionGoals answers] ++ expectedGoals ++
        [Goal.bin "#test-results" [answers, expectedTerm] result])
    originStart envAllowed sourcesAllowed.1 sourcesAllowed.2
    (by
      intro limit expressionTerm expressionGoals answers expectedTerm
        expectedGoals result _ expressionTermAllowed expressionGoalsAllowed
        answersAllowed expectedTermAllowed expectedGoalsAllowed resultAllowed
      simp only [compilerGoalsNamesAllowed_append_iff,
        compilerGoalsNamesAllowed_cons_iff, compilerGoalsNamesAllowed_nil,
        and_true]
      exact ⟨⟨compilerGoalNamesAllowed_findall expressionTermAllowed
          expressionGoalsAllowed answersAllowed,
        expectedGoalsAllowed⟩,
        compilerGoalNamesAllowed_bin
          (by simpa using And.intro answersAllowed expectedTermAllowed)
          resultAllowed _⟩)
    compiled

private theorem compileAppCoreFuel_hForall_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hForall := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ generator predicate _
  have sourcesAllowed :
      CompilerAtomNamesAllowed external origin start generator ∧
      CompilerAtomNamesAllowed external origin start predicate := by
    simpa using argumentsAllowed
  exact compileExprFreshExprFresh_generatedNames fuel ih external origin env
    start generator predicate term goals next
    (fun generatorTerm generatorGoals collected predicateTerm predicateGoals
        result =>
      [Goal.findall generatorTerm generatorGoals collected] ++ predicateGoals ++
        [Goal.call "#allacc" [predicateTerm, collected] result])
    originStart envAllowed sourcesAllowed.1 sourcesAllowed.2
    (by
      intro limit generatorTerm generatorGoals collected predicateTerm
        predicateGoals result _ generatorTermAllowed generatorGoalsAllowed
        collectedAllowed predicateTermAllowed predicateGoalsAllowed
        resultAllowed
      simp only [compilerGoalsNamesAllowed_append_iff,
        compilerGoalsNamesAllowed_cons_iff, compilerGoalsNamesAllowed_nil,
        and_true]
      exact ⟨⟨compilerGoalNamesAllowed_findall generatorTermAllowed
          generatorGoalsAllowed collectedAllowed,
        predicateGoalsAllowed⟩,
        compilerGoalNamesAllowed_call
          (by simpa using And.intro predicateTermAllowed collectedAllowed)
          resultAllowed _⟩)
      compiled

private theorem compileAppCoreFuel_hFoldall_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hFoldall := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ folder generator initial _
  have sourcesAllowed :
      CompilerAtomNamesAllowed external origin start folder ∧
      CompilerAtomNamesAllowed external origin start generator ∧
      CompilerAtomNamesAllowed external origin start initial := by
    simpa [and_assoc] using argumentsAllowed
  simp only [Bind.bind, Except.bind] at compiled
  cases generatorEq : compileExprFuel fuel env start generator with
  | error message =>
      simp only [generatorEq] at compiled
      contradiction
  | ok generatorResult =>
      simp only [generatorEq, fresh] at compiled
      have generatorCounter := compileExprFuel_counter_mono fuel env start
        generator generatorResult.1 generatorResult.2.1 generatorResult.2.2
        generatorEq
      have generatorNames := ih.expr external origin env start generator
        generatorResult.1 generatorResult.2.1 generatorResult.2.2
        originStart envAllowed sourcesAllowed.2.1 generatorEq
      have innerStart : start ≤ generatorResult.2.2 + 1 :=
        Nat.le_trans generatorCounter (by omega)
      have collectedAllowed : CompilerAtomNamesAllowed external origin
          (generatorResult.2.2 + 1)
          (Atom.var (compilerGeneratedName generatorResult.2.2)) := by
        simp only [compilerAtomNamesAllowed_var_iff]
        exact .generated (Nat.le_trans originStart generatorCounter) (by omega)
      exact compileTwoExprThenFresh_generatedNames fuel ih external origin env
        (generatorResult.2.2 + 1) folder initial term goals next
        (fun folderTerm folderGoals initialTerm initialGoals result =>
          [Goal.findall generatorResult.1 generatorResult.2.1
              (Atom.var (compilerGeneratedName generatorResult.2.2))] ++
            folderGoals ++ initialGoals ++
            [Goal.call "#foldacc"
              [folderTerm,
                Atom.var (compilerGeneratedName generatorResult.2.2),
                initialTerm] result])
        (Nat.le_trans originStart innerStart) (envAllowed.mono innerStart)
        (sourcesAllowed.1.mono innerStart)
        (sourcesAllowed.2.2.mono innerStart)
        (by
          intro limit folderTerm folderGoals initialTerm initialGoals result
            innerLimit folderTermAllowed folderGoalsAllowed initialTermAllowed
            initialGoalsAllowed resultAllowed
          have generatorTermAllowed := generatorNames.1.mono
            (Nat.le_trans (by omega : generatorResult.2.2 ≤
              generatorResult.2.2 + 1) innerLimit)
          have generatorGoalsAllowed := generatorNames.2.mono
            (Nat.le_trans (by omega : generatorResult.2.2 ≤
              generatorResult.2.2 + 1) innerLimit)
          have collectedAtLimit := collectedAllowed.mono innerLimit
          simp only [compilerGoalsNamesAllowed_append_iff,
            compilerGoalsNamesAllowed_cons_iff,
            compilerGoalsNamesAllowed_nil, and_true]
          exact ⟨⟨⟨compilerGoalNamesAllowed_findall generatorTermAllowed
                generatorGoalsAllowed collectedAtLimit,
              folderGoalsAllowed⟩,
            initialGoalsAllowed⟩,
            compilerGoalNamesAllowed_call
              (by
                simpa using And.intro folderTermAllowed
                  (And.intro collectedAtLimit initialTermAllowed))
              resultAllowed _⟩)
        compiled

private theorem compileAppCoreFuel_hMatch_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hMatch := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  case h_55 =>
    rename_i _ _ spaceSource patternSource templateSource _
    exact compileMatch_generatedNames fuel ih external origin env start
      spaceSource patternSource templateSource term goals next originStart
      envAllowed (by simpa [and_assoc] using argumentsAllowed)
      compiled
  case h_57 =>
    rename_i _ _ space pattern _
    rcases Except.ok.inj compiled with ⟨rfl, rfl, rfl⟩
    have inputsAllowed :
        CompilerAtomNamesAllowed external origin start space ∧
        CompilerAtomNamesAllowed external origin start pattern := by
      simpa using argumentsAllowed
    constructor
    · apply partialValue_namesAllowed
      simpa using And.intro (chainify_namesAllowed inputsAllowed.1)
        (chainify_namesAllowed inputsAllowed.2)
    · simp

private theorem compileAppCoreFuel_hCase_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hCase := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  rename_i _ _ scrutinee arms _
  have sourcesAllowed :
      CompilerAtomNamesAllowed external origin start scrutinee ∧
      CompilerAtomsNamesAllowed external origin start arms := by
    simpa using argumentsAllowed
  exact compileCase_generatedNames fuel ih external origin env start
    scrutinee arms term goals next originStart envAllowed sourcesAllowed.1
    sourcesAllowed.2 compiled

private theorem compileAppCoreFuel_hUnify_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .hUnify := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  split at compiled <;> try contradiction
  all_goals try
    exact compileAppDefaultWith_compiler_generatedNames fuel ih external
      origin env start head _ term goals next originStart envAllowed
      argumentsAllowed compiled
  all_goals try (repeat' split at compiled)
  all_goals try
    exact compileUnifyList_generatedNames fuel ih external origin env start
      _ term goals next originStart envAllowed
      (by simpa using argumentsAllowed) compiled
  all_goals try
    exact compileSelfUnifyFromList_generatedNames fuel ih external origin env
      start _ _ _ term goals next originStart envAllowed
      (by simpa using argumentsAllowed) compiled
  all_goals try
    exact compileGeneralUnifyFromList_generatedNames fuel ih external origin env
      start _ _ _ _ term goals next originStart envAllowed
      (by simpa using argumentsAllowed) compiled

private theorem compileAppCoreFuel_other_generatedNames (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    AppCoreGeneratedNamesFor fuel .other := by
  unfold AppCoreGeneratedNamesFor
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed classified compiled
  change compileAppCoreFuel (Nat.succ fuel) env start head arguments =
    .ok (term, goals, next) at compiled
  rw [compileAppCoreFuel.eq_def] at compiled
  simp only [classified] at compiled
  exact compileAppDefaultWith_compiler_generatedNames fuel ih external
    origin env start head arguments term goals next originStart envAllowed
    argumentsAllowed compiled


theorem compileAppCoreFuel_generatedNames_step (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    ∀ (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
      (head : String) (arguments : List Atom) (term : Atom)
      (goals : List Goal) (next : Nat),
      origin ≤ start →
      CompilerEnvNamesAllowed external origin start env →
      CompilerAtomsNamesAllowed external origin start arguments →
      compileAppCoreFuel (fuel + 1) env start head arguments =
          .ok (term, goals, next) →
        CompilerAtomNamesAllowed external origin next term ∧
        CompilerGoalsNamesAllowed external origin next goals := by
  intro external origin env start head arguments term goals next originStart
    envAllowed argumentsAllowed compiled
  cases classified : classifyAppCoreHead head with
  | hQuote =>
      exact compileAppCoreFuel_hQuote_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hPredicate =>
      exact compileAppCoreFuel_hPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hTranslatePredicate =>
      exact compileAppCoreFuel_hTranslatePredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCallPredicate =>
      exact compileAppCoreFuel_hCallPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hAssertaPredicate =>
      exact compileAppCoreFuel_hAssertaPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hAssertzPredicate =>
      exact compileAppCoreFuel_hAssertzPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hRetractPredicate =>
      exact compileAppCoreFuel_hRetractPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hProcessMettaString =>
      exact compileAppCoreFuel_hProcessMettaString_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hUnquote =>
      exact compileAppCoreFuel_hUnquote_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hEmpty =>
      exact compileAppCoreFuel_hEmpty_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCut =>
      exact compileAppCoreFuel_hCut_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hTest =>
      exact compileAppCoreFuel_hTest_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hTrace =>
      exact compileAppCoreFuel_hTrace_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hAndThen =>
      exact compileAppCoreFuel_hAndThen_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hOrElse =>
      exact compileAppCoreFuel_hOrElse_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hHashPlus =>
      exact compileAppCoreFuel_hHashPlus_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hHashMinus =>
      exact compileAppCoreFuel_hHashMinus_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCons =>
      exact compileAppCoreFuel_hCons_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hIf =>
      exact compileAppCoreFuel_hIf_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hLet =>
      exact compileAppCoreFuel_hLet_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hLetStar =>
      exact compileAppCoreFuel_hLetStar_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCase =>
      exact compileAppCoreFuel_hCase_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCollapse =>
      exact compileAppCoreFuel_hCollapse_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hOnce =>
      exact compileAppCoreFuel_hOnce_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hSuperpose =>
      exact compileAppCoreFuel_hSuperpose_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hUnify =>
      exact compileAppCoreFuel_hUnify_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hSucceedsPredicate =>
      exact compileAppCoreFuel_hSucceedsPredicate_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hFor =>
      exact compileAppCoreFuel_hFor_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hChain =>
      exact compileAppCoreFuel_hChain_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hFoldall =>
      exact compileAppCoreFuel_hFoldall_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hForall =>
      exact compileAppCoreFuel_hForall_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hProgn =>
      exact compileAppCoreFuel_hProgn_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hProg1 =>
      exact compileAppCoreFuel_hProg1_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hWithMutex =>
      exact compileAppCoreFuel_hWithMutex_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hTransaction =>
      exact compileAppCoreFuel_hTransaction_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hHyperpose =>
      exact compileAppCoreFuel_hHyperpose_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hUnique =>
      exact compileAppCoreFuel_hUnique_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hUnion =>
      exact compileAppCoreFuel_hUnion_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hIntersection =>
      exact compileAppCoreFuel_hIntersection_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hSubtraction =>
      exact compileAppCoreFuel_hSubtraction_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hEval =>
      exact compileAppCoreFuel_hEval_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCatch =>
      exact compileAppCoreFuel_hCatch_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hCall =>
      exact compileAppCoreFuel_hCall_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hReduce =>
      exact compileAppCoreFuel_hReduce_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hGetTypeSpace =>
      exact compileAppCoreFuel_hGetTypeSpace_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hGetAtoms =>
      exact compileAppCoreFuel_hGetAtoms_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hGetType =>
      exact compileAppCoreFuel_hGetType_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hGetMetatype =>
      exact compileAppCoreFuel_hGetMetatype_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hMatch =>
      exact compileAppCoreFuel_hMatch_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hFind =>
      exact compileAppCoreFuel_hFind_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hDoubleEqual =>
      exact compileAppCoreFuel_hDoubleEqual_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hEqual =>
      exact compileAppCoreFuel_hEqual_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hAddAtom =>
      exact compileAppCoreFuel_hAddAtom_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hRemoveAtom =>
      exact compileAppCoreFuel_hRemoveAtom_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hBind =>
      exact compileAppCoreFuel_hBind_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hGetState =>
      exact compileAppCoreFuel_hGetState_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | hChangeState =>
      exact compileAppCoreFuel_hChangeState_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled
  | other =>
      exact compileAppCoreFuel_other_generatedNames fuel ih external origin env
        start head arguments term goals next originStart envAllowed
        argumentsAllowed classified compiled

theorem compilerGeneratedNamesAt_succ (fuel : Nat)
    (ih : CompilerGeneratedNamesAt fuel) :
    CompilerGeneratedNamesAt (fuel + 1) where
  expr := compileExprFuel_generatedNames_step fuel ih
  pattern := compilePatternFuel_generatedNames_step fuel ih
  app := compileAppFuel_generatedNames_step fuel ih
  appCore := compileAppCoreFuel_generatedNames_step fuel ih
  typedArgs := compileTypedArgsFuel_generatedNames_step fuel ih
  argsAt := compileArgsAtFuel_generatedNames_step fuel ih
  caseArms := compileCaseArmsFuel_generatedNames_step fuel ih
  patternList := compilePatternListFuel_generatedNames_step fuel ih
  list := compileListFuel_generatedNames_step fuel ih

/-- At every fuel index, all names emitted by every mutually recursive
compiler traversal are either caller-visible or exact `_q<index>` allocations
inside the counter interval consumed by that traversal. -/
theorem compilerGeneratedNamesAt (fuel : Nat) :
    CompilerGeneratedNamesAt fuel := by
  induction fuel with
  | zero => exact compilerGeneratedNamesAt_zero
  | succ fuel ih =>
      simpa [Nat.succ_eq_add_one] using compilerGeneratedNamesAt_succ fuel ih

theorem compileExprFuel_generated_names (fuel : Nat) (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (source term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled :
      compileExprFuel fuel env start source = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).expr external origin env start source term
    goals next originStart envAllowed sourceAllowed compiled

theorem compilePatternFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (source term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled :
      compilePatternFuel fuel env start source = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).pattern external origin env start source term
    goals next originStart envAllowed sourceAllowed compiled

theorem compileAppFuel_generated_names (fuel : Nat) (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (head : String)
    (arguments : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin start arguments)
    (compiled :
      compileAppFuel fuel env start head arguments = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).app external origin env start head arguments
    term goals next originStart envAllowed argumentsAllowed compiled

theorem compileAppCoreFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (head : String) (arguments : List Atom) (term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin start arguments)
    (compiled : compileAppCoreFuel fuel env start head arguments =
      .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).appCore external origin env start head
    arguments term goals next originStart envAllowed argumentsAllowed compiled

theorem compileTypedArgsFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (sources types terms : List Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (typesAllowed : CompilerAtomsNamesAllowed external origin start types)
    (compiled : compileTypedArgsFuel fuel env start sources types =
      .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).typedArgs external origin env start sources
    types terms goals next originStart envAllowed sourcesAllowed typesAllowed
    compiled

theorem compileArgsAtFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (head : String) (index : Nat) (sources terms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled : compileArgsAtFuel fuel env start head index sources =
      .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).argsAt external origin env start head index
    sources terms goals next originStart envAllowed sourcesAllowed compiled

theorem compileCaseArmsFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv)
    (scrutinee result : Atom) (start : Nat) (arms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (scrutineeAllowed :
      CompilerAtomNamesAllowed external origin start scrutinee)
    (resultAllowed : CompilerAtomNamesAllowed external origin start result)
    (armsAllowed : CompilerAtomsNamesAllowed external origin start arms)
    (compiled : compileCaseArmsFuel fuel env scrutinee result start arms =
      .ok (goals, next)) :
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).caseArms external origin env scrutinee result
    start arms goals next originStart envAllowed scrutineeAllowed resultAllowed
    armsAllowed compiled

theorem compilePatternListFuel_generated_names (fuel : Nat)
    (external : String → Prop) (origin : Nat) (env : CEnv) (start : Nat)
    (sources terms : List Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled : compilePatternListFuel fuel env start sources =
      .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).patternList external origin env start sources
    terms goals next originStart envAllowed sourcesAllowed compiled

theorem compileListFuel_generated_names (fuel : Nat) (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (sources terms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled :
      compileListFuel fuel env start sources = .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals :=
  (compilerGeneratedNamesAt fuel).list external origin env start sources terms
    goals next originStart envAllowed sourcesAllowed compiled

theorem compileExpr_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (source term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled : compileExpr env start source = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compileExpr at compiled
  exact compileExprFuel_generated_names _ external origin env start source term
    goals next originStart envAllowed sourceAllowed compiled

theorem compilePattern_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (source term : Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourceAllowed : CompilerAtomNamesAllowed external origin start source)
    (compiled : compilePattern env start source = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compilePattern at compiled
  exact compilePatternFuel_generated_names _ external origin env start source
    term goals next originStart envAllowed sourceAllowed compiled

theorem compileApp_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (head : String)
    (arguments : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin start arguments)
    (compiled : compileApp env start head arguments = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compileApp at compiled
  exact compileAppFuel_generated_names _ external origin env start head
    arguments term goals next originStart envAllowed argumentsAllowed compiled

theorem compileAppCore_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (head : String)
    (arguments : List Atom) (term : Atom) (goals : List Goal) (next : Nat)
    (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (argumentsAllowed :
      CompilerAtomsNamesAllowed external origin start arguments)
    (compiled :
      compileAppCore env start head arguments = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed external origin next term ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compileAppCore at compiled
  exact compileAppCoreFuel_generated_names _ external origin env start head
    arguments term goals next originStart envAllowed argumentsAllowed compiled

theorem compileTypedArgs_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (sources types terms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (typesAllowed : CompilerAtomsNamesAllowed external origin start types)
    (compiled :
      compileTypedArgs env start sources types = .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compileTypedArgs at compiled
  exact compileTypedArgsFuel_generated_names _ external origin env start
    sources types terms goals next originStart envAllowed sourcesAllowed
    typesAllowed compiled

theorem compileList_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (sources terms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled : compileList env start sources = .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compileList at compiled
  exact compileListFuel_generated_names _ external origin env start sources
    terms goals next originStart envAllowed sourcesAllowed compiled

theorem compilePatternList_generated_names (external : String → Prop)
    (origin : Nat) (env : CEnv) (start : Nat) (sources terms : List Atom)
    (goals : List Goal) (next : Nat) (originStart : origin ≤ start)
    (envAllowed : CompilerEnvNamesAllowed external origin start env)
    (sourcesAllowed : CompilerAtomsNamesAllowed external origin start sources)
    (compiled :
      compilePatternList env start sources = .ok (terms, goals, next)) :
    CompilerAtomsNamesAllowed external origin next terms ∧
    CompilerGoalsNamesAllowed external origin next goals := by
  unfold compilePatternList at compiled
  exact compilePatternListFuel_generated_names _ external origin env start
    sources terms goals next originStart envAllowed sourcesAllowed compiled

/-- Source-facing classification.  Under an explicit certificate that every
variable imported through the compiler environment already occurs in the
source, every output variable is either a source occurrence or an exact
compiler allocation `_q<index>` with `start ≤ index < next`.  A source name
that merely resembles `_q<index>` remains on the source side of the
disjunction; it is never misclassified as fresh. -/
theorem compileExpr_generated_name_classification (env : CEnv) (start : Nat)
    (source term : Atom) (goals : List Goal) (next : Nat)
    (envAllowed : CompilerEnvNamesAllowed
      (fun name => name ∈ source.vars) start start env)
    (compiled : compileExpr env start source = .ok (term, goals, next)) :
    CompilerAtomNamesAllowed (fun name => name ∈ source.vars) start next term ∧
    CompilerGoalsNamesAllowed (fun name => name ∈ source.vars) start next
      goals := by
  apply compileExpr_generated_names (fun name => name ∈ source.vars) start
    env start source term goals next (by rfl) envAllowed
  · exact compilerAtomNamesAllowed_of_external
      (fun name => name ∈ source.vars) start start source
      (fun _ member => member)
  · exact compiled


end Mettapedia.Languages.MeTTa.PLeaTTa
