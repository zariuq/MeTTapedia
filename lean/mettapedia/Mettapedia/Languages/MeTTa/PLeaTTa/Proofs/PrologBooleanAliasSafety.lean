-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologBooleanAliasSafety
Purpose: Prove that the independent ordered finite-tree MGU cannot introduce
  the runtime-private Boolean spellings into alias-safe source terms.
Trusted boundary: none
Main exports: TreeSubstitution.BooleanAliasSafe,
  OrderedTreeMgu.binding_booleanAliasSafe,
  UnifyResolution.preserves_booleanAliasSafe
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologCanonicalRuntimeReading
import Mettapedia.Languages.MeTTa.PLeaTTa.PeTTaSpec.PrologGoalSemantics

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety

open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.GoalSemantics
open PrologCanonicalRuntimeReading

/-- Every replacement stored in a canonical substitution is free of the
runtime-private rigid spellings `True` and `False`. -/
def TreeSubstitution.BooleanAliasSafe
    (bindings : TreeSubstitution) : Prop :=
  ∀ entry ∈ bindings, NoRuntimeBooleanAliases entry.2

/-- Both sides of one canonical equation are Boolean-alias-safe. -/
def TreeEquationBooleanAliasSafe (equation : TreeEquation) : Prop :=
  NoRuntimeBooleanAliases equation.1 ∧
    NoRuntimeBooleanAliases equation.2

/-- Every equation in an ordered worklist is Boolean-alias-safe. -/
def TreeEquationsBooleanAliasSafe
    (equations : List TreeEquation) : Prop :=
  ∀ equation ∈ equations, TreeEquationBooleanAliasSafe equation

/-- Source-term presentation of Boolean-alias safety. -/
def TermBooleanAliasSafe (term : Term) : Prop :=
  NoRuntimeBooleanAliases (Term.denote term)

/-- Source-substitution presentation of Boolean-alias safety. -/
def Substitution.BooleanAliasSafe (bindings : Substitution) : Prop :=
  TreeSubstitution.BooleanAliasSafe (Substitution.denote bindings)

mutual

/-- Replacing a variable by an alias-safe tree preserves alias safety. -/
theorem noRuntimeBooleanAliases_instantiateOne
    (source : LogicVar) {replacement : Tree}
    (replacementSafe : NoRuntimeBooleanAliases replacement) :
    (tree : Tree) →
      NoRuntimeBooleanAliases tree →
      NoRuntimeBooleanAliases
        (Tree.instantiateOne source replacement tree)
  | .variable identity, _ => by
      by_cases same : identity = source
      · subst identity
        simpa [Tree.instantiateOne] using replacementSafe
      · simp [Tree.instantiateOne, same, NoRuntimeBooleanAliases]
  | .node symbol children, safe => by
      simp only [NoRuntimeBooleanAliases] at safe ⊢
      simp only [Tree.instantiateOne]
      exact
        ⟨safe.1, safe.2.1,
          noRuntimeBooleanAliasesList_instantiateOne source replacementSafe
            children safe.2.2⟩

/-- Ordered-child counterpart to
`noRuntimeBooleanAliases_instantiateOne`. -/
theorem noRuntimeBooleanAliasesList_instantiateOne
    (source : LogicVar) {replacement : Tree}
    (replacementSafe : NoRuntimeBooleanAliases replacement) :
    (trees : List Tree) →
      NoRuntimeBooleanAliasesList trees →
      NoRuntimeBooleanAliasesList
        (Trees.instantiateOne source replacement trees)
  | [], _ => trivial
  | tree :: trees, safe => by
      simp only [NoRuntimeBooleanAliasesList] at safe ⊢
      simp only [Trees.instantiateOne]
      exact
        ⟨noRuntimeBooleanAliases_instantiateOne source replacementSafe tree
            safe.1,
          noRuntimeBooleanAliasesList_instantiateOne source replacementSafe
            trees safe.2⟩

end

namespace TreeSubstitution.BooleanAliasSafe

/-- The empty substitution is alias-safe. -/
theorem nil : TreeSubstitution.BooleanAliasSafe [] := by
  intro entry member
  simp at member

/-- A safe head replacement and safe tail form a safe substitution. -/
theorem cons {source : LogicVar} {replacement : Tree}
    {bindings : TreeSubstitution}
    (replacementSafe : NoRuntimeBooleanAliases replacement)
    (bindingsSafe : TreeSubstitution.BooleanAliasSafe bindings) :
    TreeSubstitution.BooleanAliasSafe
      ((source, replacement) :: bindings) := by
  intro entry member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact replacementSafe
  · exact bindingsSafe entry member

/-- Concatenation preserves safe replacements in both components. -/
theorem append {extension bindings : TreeSubstitution}
    (extensionSafe : TreeSubstitution.BooleanAliasSafe extension)
    (bindingsSafe : TreeSubstitution.BooleanAliasSafe bindings) :
    TreeSubstitution.BooleanAliasSafe (extension ++ bindings) := by
  intro entry member
  simp only [List.mem_append] at member
  rcases member with member | member
  · exact extensionSafe entry member
  · exact bindingsSafe entry member

/-- Applying an alias-safe canonical substitution to an alias-safe tree
cannot introduce a reserved Boolean spelling. -/
theorem apply {bindings : TreeSubstitution}
    (bindingsSafe : TreeSubstitution.BooleanAliasSafe bindings) :
    (tree : Tree) →
      NoRuntimeBooleanAliases tree →
      NoRuntimeBooleanAliases (TreeSubstitution.apply bindings tree) := by
  induction bindings with
  | nil =>
      intro tree treeSafe
      exact treeSafe
  | cons entry bindings inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      intro tree treeSafe
      have replacementSafe :
          NoRuntimeBooleanAliases replacement :=
        bindingsSafe (source, replacement) (by simp)
      have tailSafe : TreeSubstitution.BooleanAliasSafe bindings := by
        intro tailEntry tailMember
        exact bindingsSafe tailEntry (by simp [tailMember])
      simp only [TreeSubstitution.apply]
      exact
        noRuntimeBooleanAliases_instantiateOne source replacementSafe _
          (inductionHypothesis tailSafe tree treeSafe)

/-- Ordered-child application preserves alias safety pointwise. -/
theorem applyTrees {bindings : TreeSubstitution}
    (bindingsSafe : TreeSubstitution.BooleanAliasSafe bindings) :
    (trees : List Tree) →
      NoRuntimeBooleanAliasesList trees →
      NoRuntimeBooleanAliasesList
        (TreeSubstitution.applyTrees bindings trees)
  | [], _ => by simp [NoRuntimeBooleanAliasesList]
  | tree :: trees, safe => by
      simp only [NoRuntimeBooleanAliasesList] at safe ⊢
      simp only [TreeSubstitution.applyTrees_cons]
      exact
        ⟨bindingsSafe.apply tree safe.1,
          bindingsSafe.applyTrees trees safe.2⟩

/-- Applying a safe substitution to a safe ordered equation worklist
preserves safety of every normalized equation. -/
theorem applyEquations {bindings : TreeSubstitution}
    (bindingsSafe : TreeSubstitution.BooleanAliasSafe bindings)
    {equations : List TreeEquation}
    (equationsSafe : TreeEquationsBooleanAliasSafe equations) :
    TreeEquationsBooleanAliasSafe
      (TreeSubstitution.applyEquations bindings equations) := by
  intro normalized normalizedMember
  simp only [TreeSubstitution.applyEquations, List.mem_map]
    at normalizedMember
  obtain ⟨equation, member, rfl⟩ := normalizedMember
  exact
    ⟨bindingsSafe.apply equation.1 (equationsSafe equation member).1,
      bindingsSafe.apply equation.2 (equationsSafe equation member).2⟩

end TreeSubstitution.BooleanAliasSafe

private theorem treeAndForest_binding_booleanAliasSafe :
    (∀ {left right binding}, TreeMgu left right binding →
      NoRuntimeBooleanAliases left →
        NoRuntimeBooleanAliases right →
        TreeSubstitution.BooleanAliasSafe binding) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      NoRuntimeBooleanAliasesList left →
        NoRuntimeBooleanAliasesList right →
        TreeSubstitution.BooleanAliasSafe binding) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      NoRuntimeBooleanAliases left →
        NoRuntimeBooleanAliases right →
        TreeSubstitution.BooleanAliasSafe binding)
    (forest := fun left right binding =>
      NoRuntimeBooleanAliasesList left →
        NoRuntimeBooleanAliasesList right →
        TreeSubstitution.BooleanAliasSafe binding)
    (fun _ _ _ => TreeSubstitution.BooleanAliasSafe.nil)
    (fun _ _ _ _ _ valueSafe =>
      TreeSubstitution.BooleanAliasSafe.cons valueSafe
        TreeSubstitution.BooleanAliasSafe.nil)
    (fun _ _ _ _ valueSafe _ =>
      TreeSubstitution.BooleanAliasSafe.cons valueSafe
        TreeSubstitution.BooleanAliasSafe.nil)
    (fun _ _ _ _ _ childrenInduction leftNode rightNode => by
      simp only [NoRuntimeBooleanAliases] at leftNode rightNode
      exact childrenInduction leftNode.2.2 rightNode.2.2)
    (fun _ _ => TreeSubstitution.BooleanAliasSafe.nil)
    (fun _ _ _ _ base extension _ _ headInduction tailInduction
        leftChildren rightChildren => by
      simp only [NoRuntimeBooleanAliasesList]
        at leftChildren rightChildren
      have baseSafe :=
        headInduction leftChildren.1 rightChildren.1
      have extensionSafe :=
        tailInduction
          (baseSafe.applyTrees _ leftChildren.2)
          (baseSafe.applyTrees _ rightChildren.2)
      exact extensionSafe.append baseSafe)

/-- A deterministic tree MGU stores only alias-safe replacements when both
input trees are alias-safe. -/
theorem TreeMgu.binding_booleanAliasSafe
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : TreeMgu left right binding)
    (leftSafe : NoRuntimeBooleanAliases left)
    (rightSafe : NoRuntimeBooleanAliases right) :
    TreeSubstitution.BooleanAliasSafe binding :=
  treeAndForest_binding_booleanAliasSafe.1 derivation leftSafe rightSafe

/-- Ordered child unification preserves alias safety while threading each
head MGU through the remaining children. -/
theorem TreesMgu.binding_booleanAliasSafe
    {left right : List Tree} {binding : TreeSubstitution}
    (derivation : TreesMgu left right binding)
    (leftSafe : NoRuntimeBooleanAliasesList left)
    (rightSafe : NoRuntimeBooleanAliasesList right) :
    TreeSubstitution.BooleanAliasSafe binding :=
  treeAndForest_binding_booleanAliasSafe.2 derivation leftSafe rightSafe

/-- The deterministic ordered equation MGU cannot introduce a reserved
Boolean spelling into an alias-safe worklist. -/
theorem OrderedTreeMgu.binding_booleanAliasSafe
    {equations : List TreeEquation} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding)
    (equationsSafe : TreeEquationsBooleanAliasSafe equations) :
    TreeSubstitution.BooleanAliasSafe binding := by
  induction derivation with
  | nil =>
      exact TreeSubstitution.BooleanAliasSafe.nil
  | cons left right equations base extension head tail
      inductionHypothesis =>
      have headSafe :
          TreeEquationBooleanAliasSafe (left, right) :=
        equationsSafe (left, right) (by simp)
      have baseSafe :
          TreeSubstitution.BooleanAliasSafe base :=
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety.TreeMgu.binding_booleanAliasSafe
          head headSafe.1 headSafe.2
      have remainingSafe :
          TreeEquationsBooleanAliasSafe equations := by
        intro equation member
        exact equationsSafe equation (by simp [member])
      have normalizedSafe :
          TreeEquationsBooleanAliasSafe
            (TreeSubstitution.applyEquations base equations) :=
        baseSafe.applyEquations remainingSafe
      have extensionSafe :
          TreeSubstitution.BooleanAliasSafe extension :=
        inductionHypothesis normalizedSafe
      exact extensionSafe.append baseSafe

namespace Substitution.BooleanAliasSafe

/-- The empty source substitution is alias-safe. -/
theorem nil : Substitution.BooleanAliasSafe [] := by
  exact TreeSubstitution.BooleanAliasSafe.nil

/-- Concatenation preserves source-substitution alias safety. -/
theorem append {extension bindings : Substitution}
    (extensionSafe : Substitution.BooleanAliasSafe extension)
    (bindingsSafe : Substitution.BooleanAliasSafe bindings) :
    Substitution.BooleanAliasSafe (extension ++ bindings) := by
  unfold Substitution.BooleanAliasSafe at extensionSafe bindingsSafe ⊢
  rw [Substitution.denote_append]
  exact extensionSafe.append bindingsSafe

/-- An alias-safe source substitution preserves an alias-safe source term. -/
theorem applyTerm {bindings : Substitution}
    (bindingsSafe : Substitution.BooleanAliasSafe bindings)
    (term : Term) (termSafe : TermBooleanAliasSafe term) :
    TermBooleanAliasSafe (bindings.applyTerm term) := by
  unfold Substitution.BooleanAliasSafe at bindingsSafe
  unfold TermBooleanAliasSafe at termSafe ⊢
  rw [Substitution.denote_applyTerm]
  exact bindingsSafe.apply _ termSafe

end Substitution.BooleanAliasSafe

/-- Source-level presentation of an alias-safe ordered equation worklist. -/
def TermEquationsBooleanAliasSafe
    (equations : List (Term × Term)) : Prop :=
  ∀ equation ∈ equations,
    TermBooleanAliasSafe equation.1 ∧
      TermBooleanAliasSafe equation.2

/-- Denoting a safe source worklist produces a safe canonical worklist. -/
theorem denoteEquations_booleanAliasSafe
    {equations : List (Term × Term)}
    (safe : TermEquationsBooleanAliasSafe equations) :
    TreeEquationsBooleanAliasSafe (denoteEquations equations) := by
  intro denoted denotedMember
  simp only [denoteEquations, List.mem_map] at denotedMember
  obtain ⟨equation, member, rfl⟩ := denotedMember
  exact safe equation member

/-- Exact reification of a computed ordered MGU retains Boolean-alias
safety from its complete source equation worklist. -/
theorem ComputesDenotationalMgu.binding_booleanAliasSafe
    {equations : List (Term × Term)} {binding : Substitution}
    (computed : ComputesDenotationalMgu equations binding)
    (equationsSafe : TermEquationsBooleanAliasSafe equations) :
    Substitution.BooleanAliasSafe binding := by
  rcases computed with ⟨canonicalBinding, derivation, rfl⟩
  unfold Substitution.BooleanAliasSafe
  rw [TreeSubstitution.denote_reify
    (derivation.binding_wellFormed
      (denoteEquations_wellFormed equations))]
  exact
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety.OrderedTreeMgu.binding_booleanAliasSafe
      derivation (denoteEquations_booleanAliasSafe equationsSafe)

/-- Primitive equality resolution preserves source-substitution alias
safety.  The ordered MGU sees only the two operands after the carried safe
substitution, and its exact reification is then prepended to that state. -/
theorem UnifyResolution.preserves_booleanAliasSafe
    {bindings result : Substitution} {left right : Term}
    (resolution : UnifyResolution bindings left right result)
    (bindingsSafe : Substitution.BooleanAliasSafe bindings)
    (leftSafe : TermBooleanAliasSafe left)
    (rightSafe : TermBooleanAliasSafe right) :
    Substitution.BooleanAliasSafe result := by
  rcases resolution with ⟨extension, computed, rfl⟩
  apply Substitution.BooleanAliasSafe.append
  · apply
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety.ComputesDenotationalMgu.binding_booleanAliasSafe
        computed
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    exact
      ⟨bindingsSafe.applyTerm left leftSafe,
        bindingsSafe.applyTerm right rightSafe⟩
  · exact bindingsSafe

/-- Clause-head resolution preserves alias safety when the carried binding
and every raw head equation are safe. -/
theorem HeadResolution.preserves_booleanAliasSafe
    {branch : Resolver.ClauseBranch} {result : Substitution}
    (resolution : Resolver.HeadResolution branch result)
    (bindingsSafe : Substitution.BooleanAliasSafe branch.bindings)
    (equationsSafe :
      TermEquationsBooleanAliasSafe branch.headEquations) :
    Substitution.BooleanAliasSafe result := by
  rcases resolution with ⟨extension, computed, rfl⟩
  apply Substitution.BooleanAliasSafe.append
  · apply
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety.ComputesDenotationalMgu.binding_booleanAliasSafe
        computed
    intro equation member
    simp only [Resolver.ClauseBranch.normalizedHeadEquations, List.mem_map]
      at member
    obtain ⟨raw, rawMember, rfl⟩ := member
    exact
      ⟨bindingsSafe.applyTerm raw.1 (equationsSafe raw rawMember).1,
        bindingsSafe.applyTerm raw.2 (equationsSafe raw rawMember).2⟩
  · exact bindingsSafe

/-! ## Anti-vacuity -/

/-- Source substitutions distinguish the normalized source Boolean atom from
the private runtime spelling.  The safety invariant therefore excludes a
real forged state rather than accepting every well-formed term. -/
theorem source_substitution_boolean_alias_safety_is_discriminating :
    Substitution.BooleanAliasSafe
        [(.source "x", .atom "true")] ∧
      ¬ Substitution.BooleanAliasSafe
        [(.source "x", .atom "True")] := by
  simp [Substitution.BooleanAliasSafe,
    TreeSubstitution.BooleanAliasSafe, Substitution.denote, Term.denote,
    NoRuntimeBooleanAliases, NoRuntimeBooleanAliasesList]

/-- A genuine ordered source MGU may bind a variable to normalized `true`,
and the preservation theorem certifies the resulting substitution. -/
theorem normalized_true_unifyResolution_is_safe :
    ∃ result,
      UnifyResolution [] (.variable (.source "x")) (.atom "true") result ∧
        Substitution.BooleanAliasSafe result := by
  let result :=
    TreeSubstitution.reify
      [(.source "x", Term.denote (.atom "true"))]
  have computed :
      ComputesDenotationalMgu
        [(.variable (.source "x"), .atom "true")] result := by
    exact computes_singleton_left_variable (.source "x") (.atom "true")
      (by simp [Term.denote])
      (by simp [Term.denote, Tree.occurs, Trees.occurs])
  have resolution :
      UnifyResolution [] (.variable (.source "x")) (.atom "true")
        result := by
    refine ⟨result, ?_, by simp [result]⟩
    simpa [Substitution.applyTerm] using computed
  exact
    ⟨result, resolution,
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety.UnifyResolution.preserves_booleanAliasSafe
        resolution
        Substitution.BooleanAliasSafe.nil
        (by simp [TermBooleanAliasSafe, Term.denote,
          NoRuntimeBooleanAliases])
        (by simp [TermBooleanAliasSafe, Term.denote,
          NoRuntimeBooleanAliases, NoRuntimeBooleanAliasesList])⟩

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologBooleanAliasSafety
