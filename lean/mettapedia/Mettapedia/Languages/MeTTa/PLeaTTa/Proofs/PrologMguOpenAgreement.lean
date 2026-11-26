-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguOpenAgreement
Purpose: Show that an ordered canonical MGU has an order-preserving open
  runtime spelling under the shared alpha graph, without grounding residual
  variables or inventing output names.
Trusted boundary: none
Main exports:
  orderedTreeMgu_binding_variablesSatisfy,
  AlphaTreeSubstitutionAgrees,
  SharedAlphaEquationsAgree.orderedMgu_open_spelling_exists
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguValuation

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguOpenAgreement

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PrologPrefilterBridge
open PrologMguBridge
open PrologMguValuation

/-! ## Finite variable support

The support predicate is deliberately representation-independent.  In the
application below `predicate identity` means that the shared alpha graph
contains some executable name for `identity`; the generic form makes the
origin theorem useful independently of this one bridge.
-/

mutual

/-- Every variable in one canonical tree satisfies `predicate`. -/
def TreeVariablesSatisfy (predicate : LogicVar → Prop) : Tree → Prop
  | .variable identity => predicate identity
  | .node _ children => TreesVariablesSatisfy predicate children

/-- Ordered child-list counterpart of `TreeVariablesSatisfy`. -/
def TreesVariablesSatisfy (predicate : LogicVar → Prop) :
    List Tree → Prop
  | [] => True
  | tree :: trees =>
      TreeVariablesSatisfy predicate tree ∧
        TreesVariablesSatisfy predicate trees

end

/-- Every source and every replacement variable in a canonical substitution
satisfies one support predicate.  Including replacement variables is
load-bearing for open residual-variable preservation. -/
def TreeSubstitutionVariablesSatisfy
    (predicate : LogicVar → Prop)
    (binding : TreeSubstitution) : Prop :=
  ∀ entry, entry ∈ binding →
    predicate entry.1 ∧ TreeVariablesSatisfy predicate entry.2

/-- Both sides of every ordered canonical equation stay inside one finite
variable support. -/
def TreeEquationsVariablesSatisfy
    (predicate : LogicVar → Prop)
    (equations : List TreeEquation) : Prop :=
  ∀ equation, equation ∈ equations →
    TreeVariablesSatisfy predicate equation.1 ∧
      TreeVariablesSatisfy predicate equation.2

mutual

/-- Capture-free replacement cannot invent an unsupported variable. -/
theorem treeVariablesSatisfy_instantiateOne
    {predicate : LogicVar → Prop}
    (source : LogicVar) {replacement : Tree}
    (replacementSupported : TreeVariablesSatisfy predicate replacement) :
    ∀ {tree : Tree}, TreeVariablesSatisfy predicate tree →
      TreeVariablesSatisfy predicate
        (Tree.instantiateOne source replacement tree)
  | .variable identity, supported => by
      by_cases same : identity = source
      · subst identity
        simpa [Tree.instantiateOne] using replacementSupported
      · simpa [Tree.instantiateOne, same] using supported
  | .node symbol children, supported => by
      simpa [Tree.instantiateOne, TreeVariablesSatisfy] using
        treesVariablesSatisfy_instantiateOne source replacementSupported
          supported

/-- Ordered companion to support preservation by one replacement. -/
theorem treesVariablesSatisfy_instantiateOne
    {predicate : LogicVar → Prop}
    (source : LogicVar) {replacement : Tree}
    (replacementSupported : TreeVariablesSatisfy predicate replacement) :
    ∀ {trees : List Tree}, TreesVariablesSatisfy predicate trees →
      TreesVariablesSatisfy predicate
        (Trees.instantiateOne source replacement trees)
  | [], _ => trivial
  | tree :: trees, supported => by
      exact
        ⟨treeVariablesSatisfy_instantiateOne source replacementSupported
            supported.1,
          treesVariablesSatisfy_instantiateOne source
            replacementSupported supported.2⟩

end

/-- Applying a support-preserving canonical substitution cannot invent a
variable outside that support. -/
theorem treeSubstitutionVariablesSatisfy_apply
    {predicate : LogicVar → Prop}
    {binding : TreeSubstitution}
    (bindingSupported :
      TreeSubstitutionVariablesSatisfy predicate binding) :
    ∀ {tree : Tree}, TreeVariablesSatisfy predicate tree →
      TreeVariablesSatisfy predicate
        (TreeSubstitution.apply binding tree) := by
  induction binding with
  | nil =>
      intro tree supported
      exact supported
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      intro tree supported
      have tailSupported :
          TreeSubstitutionVariablesSatisfy predicate binding := by
        intro candidate member
        exact bindingSupported candidate (by simp [member])
      have replacementSupported :
          TreeVariablesSatisfy predicate replacement :=
        (bindingSupported (source, replacement) (by simp)).2
      exact treeVariablesSatisfy_instantiateOne source replacementSupported
        (inductionHypothesis tailSupported supported)

/-- Ordered application counterpart. -/
theorem treeSubstitutionVariablesSatisfy_applyTrees
    {predicate : LogicVar → Prop}
    {binding : TreeSubstitution}
    (bindingSupported :
      TreeSubstitutionVariablesSatisfy predicate binding) :
    ∀ {trees : List Tree}, TreesVariablesSatisfy predicate trees →
      TreesVariablesSatisfy predicate
        (TreeSubstitution.applyTrees binding trees) := by
  induction binding with
  | nil =>
      intro trees supported
      exact supported
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      intro trees supported
      have tailSupported :
          TreeSubstitutionVariablesSatisfy predicate binding := by
        intro candidate member
        exact bindingSupported candidate (by simp [member])
      have replacementSupported :
          TreeVariablesSatisfy predicate replacement :=
        (bindingSupported (source, replacement) (by simp)).2
      exact treesVariablesSatisfy_instantiateOne source
        replacementSupported
        (inductionHypothesis tailSupported supported)

/-- Support certificates compose in the same order as substitutions. -/
theorem treeSubstitutionVariablesSatisfy_append
    {predicate : LogicVar → Prop}
    {extension binding : TreeSubstitution}
    (extensionSupported :
      TreeSubstitutionVariablesSatisfy predicate extension)
    (bindingSupported :
      TreeSubstitutionVariablesSatisfy predicate binding) :
    TreeSubstitutionVariablesSatisfy predicate (extension ++ binding) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact extensionSupported entry member
  · exact bindingSupported entry member

/-- Applying a supported substitution to a supported equation family
preserves the support. -/
theorem TreeEquationsVariablesSatisfy.apply
    {predicate : LogicVar → Prop}
    {equations : List TreeEquation}
    (equationsSupported :
      TreeEquationsVariablesSatisfy predicate equations)
    {binding : TreeSubstitution}
    (bindingSupported :
      TreeSubstitutionVariablesSatisfy predicate binding) :
    TreeEquationsVariablesSatisfy predicate
      (TreeSubstitution.applyEquations binding equations) := by
  intro normalized member
  simp only [TreeSubstitution.applyEquations, List.mem_map] at member
  obtain ⟨equation, equationMember, rfl⟩ := member
  have original := equationsSupported equation equationMember
  exact
    ⟨treeSubstitutionVariablesSatisfy_apply bindingSupported original.1,
      treeSubstitutionVariablesSatisfy_apply bindingSupported original.2⟩

/-! ## Ordered MGU variable-origin theorem -/

mutual

private theorem treeAndForest_binding_variablesSatisfy {predicate : LogicVar → Prop} :
    (∀ {left right binding}, TreeMgu left right binding →
      TreeVariablesSatisfy predicate left →
        TreeVariablesSatisfy predicate right →
        TreeSubstitutionVariablesSatisfy predicate binding) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      TreesVariablesSatisfy predicate left →
        TreesVariablesSatisfy predicate right →
        TreeSubstitutionVariablesSatisfy predicate binding) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      TreeVariablesSatisfy predicate left →
        TreeVariablesSatisfy predicate right →
        TreeSubstitutionVariablesSatisfy predicate binding)
    (forest := fun left right binding =>
      TreesVariablesSatisfy predicate left →
        TreesVariablesSatisfy predicate right →
        TreeSubstitutionVariablesSatisfy predicate binding)
    (fun _ _ _ entry member => by simp at member)
    (fun source value _ _ sourceSupported valueSupported entry member => by
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨sourceSupported, valueSupported⟩)
    (fun value target _ _ valueSupported targetSupported entry member => by
      simp only [List.mem_singleton] at member
      subst entry
      exact ⟨targetSupported, valueSupported⟩)
    (fun _ _ _ _ _ childrenInduction leftNode rightNode =>
      childrenInduction leftNode rightNode)
    (fun _ _ entry member => by simp at member)
    (fun _ _ _ _ base extension _ _ headInduction tailInduction
        leftSupported rightSupported => by
      have baseSupported :=
        headInduction leftSupported.1 rightSupported.1
      have extensionSupported :=
        tailInduction
          (treeSubstitutionVariablesSatisfy_applyTrees
            baseSupported leftSupported.2)
          (treeSubstitutionVariablesSatisfy_applyTrees
            baseSupported rightSupported.2)
      exact treeSubstitutionVariablesSatisfy_append
        extensionSupported baseSupported)

/-- A canonical tree MGU contains no variable outside the two input trees.
The theorem covers both binding keys and variables nested in replacement
values. -/
theorem treeMgu_binding_variablesSatisfy
    {predicate : LogicVar → Prop}
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : TreeMgu left right binding)
    (leftSupported : TreeVariablesSatisfy predicate left)
    (rightSupported : TreeVariablesSatisfy predicate right) :
    TreeSubstitutionVariablesSatisfy predicate binding :=
  (@treeAndForest_binding_variablesSatisfy predicate).1 derivation leftSupported rightSupported

/-- Ordered child-list companion to the MGU variable-origin theorem. -/
theorem treesMgu_binding_variablesSatisfy
    {predicate : LogicVar → Prop}
    {left right : List Tree} {binding : TreeSubstitution}
    (derivation : TreesMgu left right binding)
    (leftSupported : TreesVariablesSatisfy predicate left)
    (rightSupported : TreesVariablesSatisfy predicate right) :
    TreeSubstitutionVariablesSatisfy predicate binding :=
  (@treeAndForest_binding_variablesSatisfy predicate).2 derivation leftSupported rightSupported

end

/-- The ordered equation MGU cannot invent a key or replacement variable:
its entire substitution remains in the variable support of the original
equation family, despite repeated normalization of the tail worklist. -/
theorem orderedTreeMgu_binding_variablesSatisfy
    {predicate : LogicVar → Prop}
    {equations : List TreeEquation} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding)
    (equationsSupported :
      TreeEquationsVariablesSatisfy predicate equations) :
    TreeSubstitutionVariablesSatisfy predicate binding := by
  induction derivation with
  | nil =>
      intro entry member
      simp at member
  | cons left right equations base extension head tail
      inductionHypothesis =>
      have headSupported :=
        equationsSupported (left, right) (by simp)
      have baseSupported :=
        treeMgu_binding_variablesSatisfy
          head headSupported.1 headSupported.2
      have remainingSupported :
          TreeEquationsVariablesSatisfy predicate equations := by
        intro equation member
        exact equationsSupported equation (by simp [member])
      have extensionSupported :=
        inductionHypothesis
          (TreeEquationsVariablesSatisfy.apply
            remainingSupported baseSupported)
      exact treeSubstitutionVariablesSatisfy_append
        extensionSupported baseSupported

/-! ## Shared-alpha coverage and open substitution spelling -/

/-- One canonical variable is covered when the shared alpha graph gives it
an executable name. -/
def AlphaCovers
    (alpha : List (LogicVar × String)) (identity : LogicVar) : Prop :=
  ∃ name, (identity, name) ∈ alpha

mutual

/-- Structural agreement proves alpha coverage for every canonical variable
in the represented tree. -/
theorem canonicalRuntimeAgrees_variablesSatisfy
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    TreeVariablesSatisfy (AlphaCovers alpha) tree := by
  induction agreement with
  | «variable» linked =>
      exact ⟨_, linked⟩
  | atom | trueAtom | falseAtom | integer | float | string | nil =>
      trivial
  | partialValue arguments inductionHypothesis =>
      exact ⟨trivial, ⟨inductionHypothesis, trivial⟩⟩
  | cons head tail headInduction tailInduction =>
      exact ⟨headInduction, ⟨tailInduction, trivial⟩⟩

/-- Ordered list counterpart of alpha coverage. -/
theorem canonicalRuntimeAgreesList_variablesSatisfy
    {alpha : List (LogicVar × String)}
    {trees : List Tree} {atoms : List Atom}
    (agreement :
      List.Forall₂ (CanonicalRuntimeAgrees alpha) trees atoms) :
    TreesVariablesSatisfy (AlphaCovers alpha) trees := by
  induction agreement with
  | nil =>
      trivial
  | cons head _tail tailInduction =>
      exact
        ⟨canonicalRuntimeAgrees_variablesSatisfy head, tailInduction⟩

end

/-- A shared-alpha equation family covers every variable in its canonical
denotation. -/
theorem sharedAlphaEquationsAgree_variablesSatisfy
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    TreeEquationsVariablesSatisfy (AlphaCovers alpha)
      (denoteEquations equations) := by
  intro denoted member
  simp only [denoteEquations, List.mem_map] at member
  obtain ⟨equation, equationMember, rfl⟩ := member
  induction agreement with
  | nil =>
      simp at equationMember
  | cons left right tail inductionHypothesis =>
      simp only [List.mem_cons] at equationMember
      rcases equationMember with rfl | equationMember
      · exact
          ⟨canonicalRuntimeAgrees_variablesSatisfy
              (AlphaTermAgrees.canonicalRuntimeAgrees left),
            canonicalRuntimeAgrees_variablesSatisfy
              (AlphaTermAgrees.canonicalRuntimeAgrees right)⟩
      · exact inductionHypothesis equationMember

/-- Pointwise, order-preserving spelling of one canonical substitution in
runtime atoms.  No valuation or MGU property is built into the relation:
each key must be linked by the given graph, and each raw replacement must be
represented structurally under that same graph. -/
inductive AlphaTreeSubstitutionAgrees
    (alpha : List (LogicVar × String)) :
    TreeSubstitution → Subst → Prop where
  | nil : AlphaTreeSubstitutionAgrees alpha [] []
  | cons {identity : LogicVar} {name : String}
      {tree : Tree} {atom : Atom}
      {canonical : TreeSubstitution} {runtime : Subst}
      (linked : (identity, name) ∈ alpha)
      (replacement : CanonicalRuntimeAgrees alpha tree atom)
      (tail : AlphaTreeSubstitutionAgrees alpha canonical runtime) :
      AlphaTreeSubstitutionAgrees alpha
        ((identity, tree) :: canonical) ((name, atom) :: runtime)

/-- Structural substitution spelling preserves exact association-list
length. -/
theorem AlphaTreeSubstitutionAgrees.length_eq
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime) :
    canonical.length = runtime.length := by
  induction agreement with
  | nil => rfl
  | cons _ _ _ inductionHypothesis =>
      simp [inductionHypothesis]

/-- Exact alpha spelling covers every key and every replacement variable in
the canonical substitution.  Retaining this fact is load-bearing when a
residual representative is later composed with a freshly reserved clause:
the representative cannot mention a variable outside its original alpha
support. -/
theorem AlphaTreeSubstitutionAgrees.variablesSatisfy
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution} {runtime : Subst}
    (agreement :
      AlphaTreeSubstitutionAgrees alpha canonical runtime) :
    TreeSubstitutionVariablesSatisfy
      (AlphaCovers alpha) canonical := by
  induction agreement with
  | nil =>
      intro entry member
      simp at member
  | @cons identity name tree atom canonical runtime
      linked replacement tail inductionHypothesis =>
      intro entry member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact
          ⟨⟨name, linked⟩,
            canonicalRuntimeAgrees_variablesSatisfy replacement⟩
      · exact inductionHypothesis entry member

/-- Alpha coverage of every source plus representability of every
replacement constructively yields an order-preserving runtime spelling.
Residual variables remain variables; no grounding function appears. -/
theorem alphaTreeSubstitutionAgrees_exists
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution}
    (covered :
      TreeSubstitutionVariablesSatisfy (AlphaCovers alpha) canonical)
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical) :
    ∃ runtime, AlphaTreeSubstitutionAgrees alpha canonical runtime := by
  induction canonical with
  | nil =>
      exact ⟨[], .nil⟩
  | cons entry canonical inductionHypothesis =>
      rcases entry with ⟨identity, tree⟩
      have headCovered :=
        covered (identity, tree) (by simp)
      obtain ⟨name, linked⟩ := headCovered.1
      obtain ⟨atom, replacement⟩ :=
        representable (identity, tree) (by simp)
      have tailCovered :
          TreeSubstitutionVariablesSatisfy
            (AlphaCovers alpha) canonical := by
        intro candidate member
        exact covered candidate (by simp [member])
      have tailRepresentable :
          TreeSubstitutionRuntimeRepresentable alpha canonical := by
        intro candidate member
        exact representable candidate (by simp [member])
      obtain ⟨runtime, tail⟩ :=
        inductionHypothesis tailCovered tailRepresentable
      exact ⟨(name, atom) :: runtime, .cons linked replacement tail⟩

/-- Every independently ordered MGU over a shared-alpha equation family has
an open, order-preserving runtime spelling.  This theorem does not claim
that the executable unifier returns that exact association list; it provides
the non-ground cross-representation object needed to prove that next. -/
theorem SharedAlphaEquationsAgree.orderedMgu_open_spelling_exists
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ runtime, AlphaTreeSubstitutionAgrees alpha canonical runtime := by
  have covered :=
    orderedTreeMgu_binding_variablesSatisfy derivation
      (sharedAlphaEquationsAgree_variablesSatisfy agreement)
  have representable :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.OrderedTreeMgu.binding_runtimeRepresentable
      derivation
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.runtimeRepresentable
        agreement)
  exact alphaTreeSubstitutionAgrees_exists covered representable

/-! ### Anti-vacuity -/

private def unsupportedIdentity : LogicVar := .source "unsupported"

private def supportedIdentity : LogicVar := .source "supported"

private def sourceOnlyAlpha : List (LogicVar × String) :=
  [(supportedIdentity, "supported")]

/-- The spelling theorem cannot manufacture a runtime name for a canonical
binding source absent from the alpha graph.  This is the exact failure mode
the variable-origin theorem excludes for real ordered MGUs. -/
theorem unmapped_source_has_no_open_spelling :
    ¬ ∃ runtime,
      AlphaTreeSubstitutionAgrees []
        [(unsupportedIdentity, .variable unsupportedIdentity)] runtime := by
  rintro ⟨runtime, agreement⟩
  cases agreement with
  | cons linked _ _ =>
      simp at linked

/-- Covering only substitution keys is insufficient: an open replacement
variable also needs a graph partner.  This discriminator is why
`TreeSubstitutionVariablesSatisfy` includes variables inside replacement
values rather than merely the association-list domain. -/
theorem unmapped_residual_has_no_open_spelling :
    ¬ ∃ runtime,
      AlphaTreeSubstitutionAgrees sourceOnlyAlpha
        [(supportedIdentity, .variable unsupportedIdentity)] runtime := by
  rintro ⟨runtime, agreement⟩
  cases agreement with
  | cons _ replacement _ =>
      cases replacement with
      | «variable» linked =>
          simp [sourceOnlyAlpha, supportedIdentity, unsupportedIdentity]
            at linked

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguOpenAgreement
