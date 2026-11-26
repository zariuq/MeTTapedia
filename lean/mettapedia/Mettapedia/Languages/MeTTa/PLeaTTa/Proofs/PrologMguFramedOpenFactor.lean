-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguFramedOpenFactor
Purpose: Prove open-MGU output representability for equations whose ordinary
  values are nested below aligned private rigid frames.
Trusted boundary: none
Main exports:
  MguRuntimePair,
  TreeMgu.binding_alphaOpenable_of_pair,
  OrderedTreeMgu.singleton_binding_alphaOpenable
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguExecutableOpenFactor

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguFramedOpenFactor

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PrologMguOpenAgreement
open PrologMguValuation
open PrologPrefilterBridge

/-!
`CanonicalRuntimeAgrees` deliberately describes values, not private syntax.
The relation below lets those values occur below a common rigid frame without
pretending that the frame itself is a value.  Exact subtrees are inert, and a
rigid-symbol clash is retained explicitly because a real `TreeMgu` derivation
cannot cross it.
-/

mutual

/-- Two MGU inputs can produce only alpha-spellable replacement values.

`values` is the only constructor that grants a variable permission to bind to
the opposite tree.  `equal` carries an inert subtree without requiring a value
spelling, `node` recurses below one aligned rigid frame, and `rigidClash`
records an independently visible failure. -/
inductive MguRuntimePair (alpha : List (LogicVar × String)) :
    Tree → Tree → Prop where
  | values {left right : Tree}
      (leftRepresentable : TreeRuntimeRepresentable alpha left)
      (rightRepresentable : TreeRuntimeRepresentable alpha right) :
      MguRuntimePair alpha left right
  | equal (tree : Tree) : MguRuntimePair alpha tree tree
  | node (symbol : RigidSymbol) {left right : List Tree}
      (children : MguRuntimePairs alpha left right) :
      MguRuntimePair alpha (.node symbol left) (.node symbol right)
  | rigidClash (leftSymbol rightSymbol : RigidSymbol)
      (left right : List Tree) (different : leftSymbol ≠ rightSymbol) :
      MguRuntimePair alpha (.node leftSymbol left) (.node rightSymbol right)

/-- Ordered child counterpart of `MguRuntimePair`. -/
inductive MguRuntimePairs (alpha : List (LogicVar × String)) :
    List Tree → List Tree → Prop where
  | nil : MguRuntimePairs alpha [] []
  | cons {left right : Tree} {lefts rights : List Tree}
      (head : MguRuntimePair alpha left right)
      (tail : MguRuntimePairs alpha lefts rights) :
      MguRuntimePairs alpha (left :: lefts) (right :: rights)

end

/-- The two facts needed to spell one canonical binding without grounding its
residual variables. -/
def TreeSubstitutionAlphaOpenable
    (alpha : List (LogicVar × String))
    (binding : TreeSubstitution) : Prop :=
  TreeSubstitutionVariablesSatisfy (AlphaCovers alpha) binding ∧
    TreeSubstitutionRuntimeRepresentable alpha binding

theorem TreeSubstitutionAlphaOpenable.append
    {alpha : List (LogicVar × String)}
    {extension base : TreeSubstitution}
    (extensionOpenable :
      TreeSubstitutionAlphaOpenable alpha extension)
    (baseOpenable : TreeSubstitutionAlphaOpenable alpha base) :
    TreeSubstitutionAlphaOpenable alpha (extension ++ base) := by
  exact
    ⟨treeSubstitutionVariablesSatisfy_append
        extensionOpenable.1 baseOpenable.1,
      TreeSubstitutionRuntimeRepresentable.append
        extensionOpenable.2 baseOpenable.2⟩

mutual

/-- Applying an alpha-openable substitution preserves the frame/value split.
In particular, substitution never turns an inert metadata frame into a value
slot. -/
theorem MguRuntimePair.apply
    {alpha : List (LogicVar × String)} {left right : Tree}
    (pair : MguRuntimePair alpha left right)
    {binding : TreeSubstitution}
    (openable : TreeSubstitutionAlphaOpenable alpha binding) :
    MguRuntimePair alpha
      (TreeSubstitution.apply binding left)
      (TreeSubstitution.apply binding right) :=
  match pair with
  | .values leftRepresentable rightRepresentable =>
      .values (openable.2.apply leftRepresentable)
        (openable.2.apply rightRepresentable)
  | .equal tree => .equal (TreeSubstitution.apply binding tree)
  | .node symbol children => by
      simpa [TreeSubstitution.apply_node] using
        MguRuntimePair.node symbol (children.apply openable)
  | .rigidClash leftSymbol rightSymbol left right different => by
      simpa [TreeSubstitution.apply_node] using
        MguRuntimePair.rigidClash leftSymbol rightSymbol
          (TreeSubstitution.applyTrees binding left)
          (TreeSubstitution.applyTrees binding right) different

/-- Ordered application counterpart. -/
theorem MguRuntimePairs.apply
    {alpha : List (LogicVar × String)} {left right : List Tree}
    (pairs : MguRuntimePairs alpha left right)
    {binding : TreeSubstitution}
    (openable : TreeSubstitutionAlphaOpenable alpha binding) :
    MguRuntimePairs alpha
      (TreeSubstitution.applyTrees binding left)
      (TreeSubstitution.applyTrees binding right) :=
  match pairs with
  | .nil => by
      simpa [TreeSubstitution.applyTrees] using
        (MguRuntimePairs.nil (alpha := alpha))
  | .cons head tail => by
      simpa [TreeSubstitution.applyTrees_cons] using
        MguRuntimePairs.cons (head.apply openable) (tail.apply openable)

end

mutual

private theorem treeAndForest_binding_alphaOpenable {alpha : List (LogicVar × String)} :
    (∀ {left right binding}, TreeMgu left right binding →
      MguRuntimePair alpha left right →
        TreeSubstitutionAlphaOpenable alpha binding) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      MguRuntimePairs alpha left right →
        TreeSubstitutionAlphaOpenable alpha binding) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      MguRuntimePair alpha left right →
        TreeSubstitutionAlphaOpenable alpha binding)
    (forest := fun left right binding =>
      MguRuntimePairs alpha left right →
        TreeSubstitutionAlphaOpenable alpha binding)
    (fun tree framed => by
      exact ⟨by intro entry member; simp at member,
        by intro entry member; simp at member⟩)
    (fun source value different absent framed => by
      cases framed with
      | values leftRepresentable rightRepresentable =>
          exact
            ⟨treeMgu_binding_variablesSatisfy
                (.bindLeft source value different absent)
                (canonicalRuntimeAgrees_variablesSatisfy
                  leftRepresentable.choose_spec)
                (canonicalRuntimeAgrees_variablesSatisfy
                  rightRepresentable.choose_spec),
              TreeMgu.binding_runtimeRepresentable
                (.bindLeft source value different absent)
                leftRepresentable rightRepresentable⟩
      | equal tree => exact False.elim (different rfl))
    (fun value target notVariable absent framed => by
      cases framed with
      | values leftRepresentable rightRepresentable =>
          exact
            ⟨treeMgu_binding_variablesSatisfy
                (.bindRight value target notVariable absent)
                (canonicalRuntimeAgrees_variablesSatisfy
                  leftRepresentable.choose_spec)
                (canonicalRuntimeAgrees_variablesSatisfy
                  rightRepresentable.choose_spec),
              TreeMgu.binding_runtimeRepresentable
                (.bindRight value target notVariable absent)
                leftRepresentable rightRepresentable⟩
      | equal tree => exact False.elim (notVariable target rfl))
    (fun symbol left right different children childrenInduction framed => by
      cases framed with
      | values leftRepresentable rightRepresentable =>
          exact
            ⟨treeMgu_binding_variablesSatisfy
                (.node symbol left right different children)
                (canonicalRuntimeAgrees_variablesSatisfy
                  leftRepresentable.choose_spec)
                (canonicalRuntimeAgrees_variablesSatisfy
                  rightRepresentable.choose_spec),
              TreeMgu.binding_runtimeRepresentable
                (.node symbol left right different children)
                leftRepresentable rightRepresentable⟩
      | equal tree => exact False.elim (different rfl)
      | node _ childPairs => exact childrenInduction childPairs
      | rigidClash leftSymbol rightSymbol leftChildren rightChildren clash =>
          exact False.elim (clash rfl))
    (fun framed => by
      cases framed
      exact ⟨by intro entry member; simp at member,
        by intro entry member; simp at member⟩)
    (fun left right lefts rights base extension head tail headInduction
        tailInduction framed => by
      cases framed with
      | cons headPair tailPairs =>
          have baseOpenable := headInduction headPair
          have extensionOpenable :=
            tailInduction (tailPairs.apply baseOpenable)
          exact extensionOpenable.append baseOpenable)

/-- A real canonical root MGU over framed inputs can emit only ordinary
alpha-covered, runtime-representable replacement values. -/
theorem TreeMgu.binding_alphaOpenable_of_pair
    {alpha : List (LogicVar × String)}
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : TreeMgu left right binding)
    (pair : MguRuntimePair alpha left right) :
    TreeSubstitutionAlphaOpenable alpha binding :=
  (@treeAndForest_binding_alphaOpenable alpha).1 derivation pair

/-- Ordered child-list specialization of the same output guarantee. -/
theorem TreesMgu.binding_alphaOpenable_of_pairs
    {alpha : List (LogicVar × String)}
    {left right : List Tree} {binding : TreeSubstitution}
    (derivation : TreesMgu left right binding)
    (pairs : MguRuntimePairs alpha left right) :
    TreeSubstitutionAlphaOpenable alpha binding :=
  (@treeAndForest_binding_alphaOpenable alpha).2 derivation pairs

end


/-- A one-equation ordered MGU inherits the framed root guarantee exactly;
the empty tail cannot add bindings. -/
theorem OrderedTreeMgu.singleton_binding_alphaOpenable
    {alpha : List (LogicVar × String)}
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu [(left, right)] binding)
    (pair : MguRuntimePair alpha left right) :
    TreeSubstitutionAlphaOpenable alpha binding := by
  cases derivation with
  | cons _ _ equations base extension head tail =>
      cases tail
      simpa using
        (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguFramedOpenFactor.TreeMgu.binding_alphaOpenable_of_pair
          head pair)

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguFramedOpenFactor
