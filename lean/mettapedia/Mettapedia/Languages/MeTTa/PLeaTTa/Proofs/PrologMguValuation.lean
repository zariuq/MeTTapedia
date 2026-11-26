-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguValuation
Purpose: Construct an executable ground unifier witness from the independent
  ordered canonical MGU over one shared runtime alpha graph.
Trusted boundary: none
Main exports:
  OrderedTreeMgu.binding_runtimeRepresentable,
  unifyB_complete_of_ordered_shared_alpha
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguBridge

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PrologStateBridge
open PrologPrefilterBridge
open PrologMguBridge

/-! ## Representation closure under canonical substitution -/

/-- One canonical tree has some executable spelling under the shared alpha
graph.  The spelling is existential because one canonical Prolog NaN
identity may be represented by several IEEE payloads. -/
def TreeRuntimeRepresentable
    (alpha : List (LogicVar × String)) (tree : Tree) : Prop :=
  ∃ atom, CanonicalRuntimeAgrees alpha tree atom

/-- Every tree in one ordered child list is runtime-representable. -/
def TreesRuntimeRepresentable
    (alpha : List (LogicVar × String)) (trees : List Tree) : Prop :=
  ∀ tree, tree ∈ trees → TreeRuntimeRepresentable alpha tree

/-- Every replacement in one canonical substitution is
runtime-representable. -/
def TreeSubstitutionRuntimeRepresentable
    (alpha : List (LogicVar × String))
    (binding : TreeSubstitution) : Prop :=
  ∀ entry, entry ∈ binding → TreeRuntimeRepresentable alpha entry.2

/-- Both sides of every canonical equation are runtime-representable. -/
def TreeEquationsRuntimeRepresentable
    (alpha : List (LogicVar × String))
    (equations : List TreeEquation) : Prop :=
  ∀ equation, equation ∈ equations →
    TreeRuntimeRepresentable alpha equation.1 ∧
      TreeRuntimeRepresentable alpha equation.2

/-- Replacing one variable by a representable tree preserves
representability.  This is a structural existence theorem, not an
executable substitution claim. -/
theorem CanonicalRuntimeAgrees.instantiateOne_exists
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    (source : LogicVar) {replacement : Tree}
    (replacementRepresentable :
      TreeRuntimeRepresentable alpha replacement) :
    TreeRuntimeRepresentable alpha
      (Tree.instantiateOne source replacement tree) := by
  induction agreement with
  | @«variable» identity name linked =>
      by_cases same : identity = source
      · subst source
        simpa [Tree.instantiateOne] using replacementRepresentable
      · exact ⟨.var _, by
          simpa [Tree.instantiateOne, same] using
            (CanonicalRuntimeAgrees.variable linked)⟩
  | atom notTrue notFalse =>
      exact ⟨.sym _, by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.atom
            (alpha := alpha) notTrue notFalse)⟩
  | trueAtom =>
      exact ⟨.sym "True", by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))⟩
  | falseAtom =>
      exact ⟨.sym "False", by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))⟩
  | integer value =>
      exact ⟨.gnd (.int value), by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.integer (alpha := alpha) value)⟩
  | float value =>
      exact ⟨.gnd (.float value), by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.float (alpha := alpha) value)⟩
  | string value =>
      exact ⟨.gnd (.str value), by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.string (alpha := alpha) value)⟩
  | partialValue arguments inductionHypothesis =>
      obtain ⟨encoded, encodedAgreement⟩ := inductionHypothesis
      exact ⟨partialC _ encoded, by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.partialValue encodedAgreement)⟩
  | nil =>
      exact ⟨nilA, by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.nil (alpha := alpha))⟩
  | cons head tail headInduction tailInduction =>
      obtain ⟨encodedHead, encodedHeadAgreement⟩ := headInduction
      obtain ⟨encodedTail, encodedTailAgreement⟩ := tailInduction
      exact ⟨consC encodedHead encodedTail, by
        simpa [Tree.instantiateOne, Trees.instantiateOne] using
          (CanonicalRuntimeAgrees.cons
            encodedHeadAgreement encodedTailAgreement)⟩

/-- Applying a representable canonical substitution to a representable tree
preserves representability. -/
theorem TreeSubstitutionRuntimeRepresentable.apply
    {alpha : List (LogicVar × String)}
    {binding : TreeSubstitution}
    (bindingRepresentable :
      TreeSubstitutionRuntimeRepresentable alpha binding)
    {tree : Tree} (treeRepresentable :
      TreeRuntimeRepresentable alpha tree) :
    TreeRuntimeRepresentable alpha
      (TreeSubstitution.apply binding tree) := by
  induction binding with
  | nil =>
      exact treeRepresentable
  | cons entry binding inductionHypothesis =>
      rcases entry with ⟨source, replacement⟩
      have tailRepresentable :
          TreeSubstitutionRuntimeRepresentable alpha binding := by
        intro candidate member
        exact bindingRepresentable candidate (by simp [member])
      have replacementRepresentable :
          TreeRuntimeRepresentable alpha replacement :=
        bindingRepresentable (source, replacement) (by simp)
      obtain ⟨atom, agreement⟩ :=
        inductionHypothesis tailRepresentable
      exact
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.CanonicalRuntimeAgrees.instantiateOne_exists
          agreement source replacementRepresentable

/-- Ordered application counterpart. -/
theorem TreeSubstitutionRuntimeRepresentable.applyTrees
    {alpha : List (LogicVar × String)}
    {binding : TreeSubstitution}
    (bindingRepresentable :
      TreeSubstitutionRuntimeRepresentable alpha binding)
    {trees : List Tree}
    (treesRepresentable : TreesRuntimeRepresentable alpha trees) :
    TreesRuntimeRepresentable alpha
      (TreeSubstitution.applyTrees binding trees) := by
  induction trees with
  | nil =>
      intro tree member
      simp at member
  | cons head tail inductionHypothesis =>
      intro tree member
      rw [TreeSubstitution.applyTrees_cons] at member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact bindingRepresentable.apply
          (treesRepresentable head (by simp))
      · apply inductionHypothesis
          (fun candidate candidateMember =>
            treesRepresentable candidate (by simp [candidateMember]))
        exact member

/-- Runtime-representability is closed under ordered substitution
composition. -/
theorem TreeSubstitutionRuntimeRepresentable.append
    {alpha : List (LogicVar × String)}
    {extension binding : TreeSubstitution}
    (extensionRepresentable :
      TreeSubstitutionRuntimeRepresentable alpha extension)
    (bindingRepresentable :
      TreeSubstitutionRuntimeRepresentable alpha binding) :
    TreeSubstitutionRuntimeRepresentable alpha (extension ++ binding) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact extensionRepresentable entry member
  · exact bindingRepresentable entry member

/-- A representable canonical node exposes representability of all of its
children. -/
theorem TreeRuntimeRepresentable.children
    {alpha : List (LogicVar × String)}
    {symbol : RigidSymbol} {children : List Tree}
    (representable :
      TreeRuntimeRepresentable alpha (.node symbol children)) :
    TreesRuntimeRepresentable alpha children := by
  rcases representable with ⟨atom, agreement⟩
  cases agreement with
  | atom | trueAtom | falseAtom | integer | float | string | nil =>
      intro tree member
      simp at member
  | @partialValue head argumentsTree encodedArguments arguments =>
      intro tree member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · by_cases isTrue : head = "true"
        · subst head
          exact ⟨.sym "True", CanonicalRuntimeAgrees.trueAtom⟩
        · by_cases isFalse : head = "false"
          · subst head
            exact ⟨.sym "False", CanonicalRuntimeAgrees.falseAtom⟩
          · exact ⟨.sym head,
              CanonicalRuntimeAgrees.atom isTrue isFalse⟩
      · exact ⟨encodedArguments, arguments⟩
  | @cons headTree tailTree headAtom tailAtom head tail =>
      intro tree member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨headAtom, head⟩
      · exact ⟨tailAtom, tail⟩

private theorem treeAndForest_binding_runtimeRepresentable {alpha : List (LogicVar × String)} :
    (∀ {left right binding}, TreeMgu left right binding →
      TreeRuntimeRepresentable alpha left →
        TreeRuntimeRepresentable alpha right →
        TreeSubstitutionRuntimeRepresentable alpha binding) ∧
    (∀ {left right binding}, TreesMgu left right binding →
      TreesRuntimeRepresentable alpha left →
        TreesRuntimeRepresentable alpha right →
        TreeSubstitutionRuntimeRepresentable alpha binding) :=
  TreeMgu.inductBoth
    (tree := fun left right binding =>
      TreeRuntimeRepresentable alpha left →
        TreeRuntimeRepresentable alpha right →
        TreeSubstitutionRuntimeRepresentable alpha binding)
    (forest := fun left right binding =>
      TreesRuntimeRepresentable alpha left →
        TreesRuntimeRepresentable alpha right →
        TreeSubstitutionRuntimeRepresentable alpha binding)
    (fun _ _ _ => by
      intro entry member
      simp at member)
    (fun source value _ _ _ valueRepresentable =>
      fun entry member => by
        simp only [List.mem_singleton] at member
        subst entry
        exact valueRepresentable)
    (fun value target _ _ valueRepresentable _ =>
      fun entry member => by
        simp only [List.mem_singleton] at member
        subst entry
        exact valueRepresentable)
    (fun _ _ _ _ _ childrenInduction leftNode rightNode =>
      childrenInduction leftNode.children rightNode.children)
    (fun _ _ => by
      intro entry member
      simp at member)
    (fun left right lefts rights base extension _ _ headInduction
        tailInduction leftTrees rightTrees => by
      have leftHead := leftTrees left (by simp)
      have rightHead := rightTrees right (by simp)
      have baseRepresentable := headInduction leftHead rightHead
      have leftTail :
          TreesRuntimeRepresentable alpha lefts := by
        intro tree member
        exact leftTrees tree (by simp [member])
      have rightTail :
          TreesRuntimeRepresentable alpha rights := by
        intro tree member
        exact rightTrees tree (by simp [member])
      have extensionRepresentable := tailInduction
        (baseRepresentable.applyTrees leftTail)
        (baseRepresentable.applyTrees rightTail)
      exact extensionRepresentable.append baseRepresentable)

/-- Canonical child-list unification preserves runtime-representability of
the generated binding. -/
theorem TreesMgu.binding_runtimeRepresentable
    {alpha : List (LogicVar × String)}
    {left right : List Tree} {binding : TreeSubstitution}
    (derivation : TreesMgu left right binding)
    (leftRepresentable : TreesRuntimeRepresentable alpha left)
    (rightRepresentable : TreesRuntimeRepresentable alpha right) :
    TreeSubstitutionRuntimeRepresentable alpha binding :=
  (@treeAndForest_binding_runtimeRepresentable alpha).2 derivation leftRepresentable rightRepresentable

/-- Root canonical unification preserves runtime-representability of the
generated binding. -/
theorem TreeMgu.binding_runtimeRepresentable
    {alpha : List (LogicVar × String)}
    {left right : Tree} {binding : TreeSubstitution}
    (derivation : TreeMgu left right binding)
    (leftRepresentable : TreeRuntimeRepresentable alpha left)
    (rightRepresentable : TreeRuntimeRepresentable alpha right) :
    TreeSubstitutionRuntimeRepresentable alpha binding :=
  (@treeAndForest_binding_runtimeRepresentable alpha).1 derivation leftRepresentable rightRepresentable

/-- Applying a representable substitution preserves representability on both
sides of every equation. -/
theorem TreeEquationsRuntimeRepresentable.apply
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation}
    (equationsRepresentable :
      TreeEquationsRuntimeRepresentable alpha equations)
    {binding : TreeSubstitution}
    (bindingRepresentable :
      TreeSubstitutionRuntimeRepresentable alpha binding) :
    TreeEquationsRuntimeRepresentable alpha
      (TreeSubstitution.applyEquations binding equations) := by
  intro normalized member
  simp only [TreeSubstitution.applyEquations, List.mem_map] at member
  obtain ⟨equation, equationMember, rfl⟩ := member
  have original := equationsRepresentable equation equationMember
  exact ⟨bindingRepresentable.apply original.1,
    bindingRepresentable.apply original.2⟩

/-- The ordered canonical MGU cannot invent an unrepresentable replacement:
every binding value is assembled from representable equation subtrees. -/
theorem OrderedTreeMgu.binding_runtimeRepresentable
    {alpha : List (LogicVar × String)}
    {equations : List TreeEquation} {binding : TreeSubstitution}
    (derivation : OrderedTreeMgu equations binding)
    (equationsRepresentable :
      TreeEquationsRuntimeRepresentable alpha equations) :
    TreeSubstitutionRuntimeRepresentable alpha binding := by
  induction derivation with
  | nil =>
      intro entry member
      simp at member
  | cons left right equations base extension head tail
      inductionHypothesis =>
      have headRepresentable :=
        equationsRepresentable (left, right) (by simp)
      have baseRepresentable :=
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.TreeMgu.binding_runtimeRepresentable
          head headRepresentable.1 headRepresentable.2
      have remainingRepresentable :
          TreeEquationsRuntimeRepresentable alpha equations := by
        intro equation member
        exact equationsRepresentable equation (by simp [member])
      have extensionRepresentable :=
        inductionHypothesis
          (remainingRepresentable.apply baseRepresentable)
      exact extensionRepresentable.append baseRepresentable

/-- A shared-alpha equation family supplies representability of every
denoted canonical equation, independently of any unifier. -/
theorem SharedAlphaEquationsAgree.runtimeRepresentable
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    TreeEquationsRuntimeRepresentable alpha
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
          ⟨⟨_, AlphaTermAgrees.canonicalRuntimeAgrees left⟩,
            ⟨_, AlphaTermAgrees.canonicalRuntimeAgrees right⟩⟩
      · exact inductionHypothesis equationMember

/-! ## A finite ground instance of the canonical MGU -/

mutual

/-- Replace every residual canonical variable by one fixed ordinary atom.
The operation is a homomorphism over rigid nodes; it is used only to obtain
one closed completeness witness, never as the reported MGU. -/
def groundTree : Tree → Tree
  | .variable _ => .node (.atom "$pleatta-ground") []
  | .node symbol children => .node symbol (groundTrees children)

/-- Ordered child counterpart of `groundTree`. -/
def groundTrees : List Tree → List Tree
  | [] => []
  | tree :: trees => groundTree tree :: groundTrees trees

end

@[simp] theorem groundTrees_eq_map (trees : List Tree) :
    groundTrees trees = trees.map groundTree := by
  induction trees with
  | nil => rfl
  | cons tree trees inductionHypothesis =>
      simp [groundTrees, inductionHypothesis]

/-- Grounding a representable tree produces a representable executable atom
with no runtime variables.  Runtime float payloads are retained from the
representation witness, so canonical Prolog NaN identity does not require
choosing a distinguished IEEE payload. -/
theorem CanonicalRuntimeAgrees.ground_exists
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    ∃ groundedAtom,
      CanonicalRuntimeAgrees alpha (groundTree tree) groundedAtom ∧
        groundedAtom.vars = [] := by
  induction agreement with
  | «variable» =>
      exact ⟨.sym "$pleatta-ground", by
        simpa [groundTree] using
          (CanonicalRuntimeAgrees.atom
            (alpha := alpha)
            (name := "$pleatta-ground") (by decide) (by decide)),
        by simp [Atom.vars]⟩
  | atom notTrue notFalse =>
      exact ⟨.sym _, by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.atom
            (alpha := alpha) notTrue notFalse),
        by simp [Atom.vars]⟩
  | trueAtom =>
      exact ⟨.sym "True", by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.trueAtom (alpha := alpha)),
        by simp [Atom.vars]⟩
  | falseAtom =>
      exact ⟨.sym "False", by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.falseAtom (alpha := alpha)),
        by simp [Atom.vars]⟩
  | integer value =>
      exact ⟨.gnd (.int value), by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.integer (alpha := alpha) value),
        by simp [Atom.vars]⟩
  | float value =>
      exact ⟨.gnd (.float value), by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.float (alpha := alpha) value),
        by simp [Atom.vars]⟩
  | string value =>
      exact ⟨.gnd (.str value), by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.string (alpha := alpha) value),
        by simp [Atom.vars]⟩
  | partialValue arguments inductionHypothesis =>
      obtain ⟨groundedArguments, groundedAgreement, closed⟩ :=
        inductionHypothesis
      exact
        ⟨partialC _ groundedArguments,
          by
            simpa [groundTree, groundTrees] using
              (CanonicalRuntimeAgrees.partialValue groundedAgreement),
          by
            simp [partialC, prologCompoundC, prologCompoundTagA,
              chainOf, consC, nilA, Atom.vars, closed]⟩
  | nil =>
      exact ⟨nilA, by
        simpa [groundTree, groundTrees] using
          (CanonicalRuntimeAgrees.nil (alpha := alpha)),
        by simp [nilA, Atom.vars]⟩
  | cons head tail headInduction tailInduction =>
      obtain ⟨groundedHead, groundedHeadAgreement, headClosed⟩ :=
        headInduction
      obtain ⟨groundedTail, groundedTailAgreement, tailClosed⟩ :=
        tailInduction
      exact
        ⟨consC groundedHead groundedTail,
          by
            simpa [groundTree, groundTrees] using
              (CanonicalRuntimeAgrees.cons
                groundedHeadAgreement groundedTailAgreement),
          by simp [consC, Atom.vars, headClosed, tailClosed]⟩

/-- The closed semantic valuation used for executable completeness.  It
first applies the independent ordered MGU, then grounds only the residual
variables. -/
def GroundAlphaValuationAgrees
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (runtime : Subst) : Prop :=
  ∀ {identity name}, (identity, name) ∈ alpha →
    CanonicalRuntimeAgrees alpha
      (groundTree
        (TreeSubstitution.apply canonical (.variable identity)))
      (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (.var name))

/-- An open executable result admits the independently specified canonical
solution as a closed instance.  Keeping the completing valuation explicit
separates ground-instance completeness from the stronger, still-open claim
that the two open MGU spellings agree up to residual alpha-renaming. -/
def GroundAlphaResultFactors
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (result : Subst) : Prop :=
  ∃ valuation,
    GroundAlphaValuationAgrees alpha canonical valuation ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.SubstFactorsThroughWith
        Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical valuation result

/-- Deep executable substitution commutes with the proper-list chain
encoder. -/
private theorem subst_chainOf
    (runtime : Subst) (atoms : List Atom) :
    Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (chainOf atoms) =
      chainOf (atoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)) := by
  induction atoms with
  | nil =>
      simp [chainOf, nilA]
  | cons head tail inductionHypothesis =>
      change
        Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime head)
            (chainOf (tail.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)))
      rw [show
        Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (consC head (chainOf tail)) =
          consC (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime head)
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime (chainOf tail)) by
              simp [consC, Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr]]
      rw [inductionHypothesis]

/-- Grounded valuation agreement lifts structurally through every supported
canonical/runtime term. -/
theorem canonicalRuntimeAgrees_ground_apply
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      GroundAlphaValuationAgrees alpha canonical runtime) :
    CanonicalRuntimeAgrees alpha
      (groundTree (TreeSubstitution.apply canonical tree))
      (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime atom) := by
  induction agreement with
  | «variable» linked =>
      exact valuation linked
  | atom notTrue notFalse =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.atom (alpha := alpha) notTrue notFalse)
  | trueAtom =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.trueAtom (alpha := alpha))
  | falseAtom =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.falseAtom (alpha := alpha))
  | integer value =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.integer (alpha := alpha) value)
  | float value =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.float (alpha := alpha) value)
  | string value =>
      simpa [groundTree, groundTrees] using
        (CanonicalRuntimeAgrees.string (alpha := alpha) value)
  | @partialValue head argumentsTree encodedArguments arguments
      inductionHypothesis =>
      simpa [TreeSubstitution.apply_node, groundTree, groundTrees,
        groundTrees_eq_map, partialC, prologCompoundC,
        prologCompoundTagA, subst_chainOf] using
          (CanonicalRuntimeAgrees.partialValue inductionHypothesis)
  | nil =>
      simpa [TreeSubstitution.apply_node, groundTree, groundTrees, nilA] using
        (CanonicalRuntimeAgrees.nil (alpha := alpha))
  | cons head tail headInduction tailInduction =>
      simpa [TreeSubstitution.apply_node, groundTree, groundTrees,
        consC, Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using
          (CanonicalRuntimeAgrees.cons headInduction tailInduction)

/-- A canonical ordered unifier plus a grounded runtime valuation makes both
complete executable head payloads comparator-equivalent. -/
theorem SharedAlphaEquationsAgree.atomsEquivalent_of_ground_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      GroundAlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeUnifiesEquations canonical (denoteEquations equations)) :
    AtomsEquivalentWith Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical
      (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime))
      (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)) := by
  induction agreement with
  | nil =>
      exact .nil
  | @cons leftTerm rightTerm leftAtom rightAtom equations leftAtoms
      rightAtoms left right tail inductionHypothesis =>
      have leftApplied :=
        canonicalRuntimeAgrees_ground_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees left) valuation
      have rightApplied :=
        canonicalRuntimeAgrees_ground_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees right) valuation
      have headEquality :
          TreeSubstitution.apply canonical (Term.denote leftTerm) =
            TreeSubstitution.apply canonical (Term.denote rightTerm) := by
        apply unifies (Term.denote leftTerm, Term.denote rightTerm)
        simp [denoteEquations]
      have groundedEquality := congrArg groundTree headEquality
      rw [groundedEquality] at leftApplied
      exact .cons
        (CanonicalRuntimeAgrees.equivalent_of_same
          functional leftApplied rightApplied)
        (inductionHypothesis (by
          intro denoted member
          exact unifies denoted (by
            simp only [denoteEquations, List.mem_map] at member ⊢
            obtain ⟨equation, equationMember, rfl⟩ := member
            exact ⟨equation, List.mem_cons_of_mem _ equationMember, rfl⟩)))

/-! ## Constructing the closed executable valuation -/

/-- An alpha-linked variable has a closed runtime spelling after applying
and grounding any representable canonical substitution. -/
theorem TreeSubstitutionRuntimeRepresentable.groundedImage_exists
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution}
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha) :
    ∃ atom,
      CanonicalRuntimeAgrees alpha
          (groundTree
            (TreeSubstitution.apply canonical (.variable identity)))
          atom ∧
        atom.vars = [] := by
  have variableRepresentable :
      TreeRuntimeRepresentable alpha (.variable identity) :=
    ⟨.var name, .variable linked⟩
  obtain ⟨appliedAtom, appliedAgreement⟩ :=
    representable.apply variableRepresentable
  exact
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.CanonicalRuntimeAgrees.ground_exists
      appliedAgreement

/-- Choose one closed spelling of a grounded canonical image.  The fallback
is unreachable for pairs retained from `alpha`; keeping the function total
makes the association-list construction ordinary data. -/
noncomputable def groundedValue
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution)
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical)
    (identity : LogicVar) (name : String) : Atom :=
  if linked : (identity, name) ∈ alpha then
    Classical.choose (representable.groundedImage_exists linked)
  else
    .sym "$pleatta-ground"

/-- The chosen value has exactly the grounded semantic image and is closed
whenever its alpha pair is live. -/
theorem groundedValue_spec
    {alpha : List (LogicVar × String)}
    {canonical : TreeSubstitution}
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha) :
    CanonicalRuntimeAgrees alpha
        (groundTree
          (TreeSubstitution.apply canonical (.variable identity)))
        (groundedValue alpha canonical representable identity name) ∧
      (groundedValue alpha canonical representable identity name).vars =
        [] := by
  simp only [groundedValue, dif_pos linked]
  exact Classical.choose_spec
    (representable.groundedImage_exists linked)

private theorem eraseDups_nodup_alpha :
    ∀ alpha : List (LogicVar × String), alpha.eraseDups.Nodup
  | [] => by simp
  | head :: tail => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_eraseDups] at member
        simp at member
      · exact eraseDups_nodup_alpha
          (tail.filter (fun pair => !pair == head))
termination_by alpha => alpha.length
decreasing_by
  have lengthBound :=
    List.length_filter_le
      (fun pair : LogicVar × String => !pair == head) tail
  simp only [List.length_cons]
  omega

/-- Inverse functionality plus duplicate-free pairs implies duplicate-free
runtime names. -/
theorem AlphaBackwardFunctional.snd_nodup_of_nodup
    {alpha : List (LogicVar × String)}
    (backward : AlphaBackwardFunctional alpha)
    (nodup : alpha.Nodup) :
    (alpha.map Prod.snd).Nodup := by
  induction alpha with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      rcases head with ⟨headIdentity, headName⟩
      rw [List.nodup_cons] at nodup
      simp only [List.map_cons, List.nodup_cons]
      constructor
      · intro nameMember
        rw [List.mem_map] at nameMember
        obtain ⟨⟨identity, name⟩, pairMember, nameEq⟩ := nameMember
        simp only at nameEq
        subst name
        have identityEq : headIdentity = identity :=
          backward
            (left := headIdentity) (right := identity) (name := headName)
            (by exact List.mem_cons_self)
            (by exact List.mem_cons_of_mem _ pairMember)
        subst identity
        exact nodup.1 pairMember
      · apply inductionHypothesis
        · intro left right name leftMember rightMember
          exact backward
            (left := left) (right := right) (name := name)
            (List.mem_cons_of_mem _ leftMember)
            (List.mem_cons_of_mem _ rightMember)
        · exact nodup.2

/-- Removing exact duplicate alpha pairs preserves inverse functionality. -/
theorem AlphaBackwardFunctional.eraseDups
    {alpha : List (LogicVar × String)}
    (backward : AlphaBackwardFunctional alpha) :
    AlphaBackwardFunctional alpha.eraseDups := by
  intro left right name leftMember rightMember
  exact backward
    (List.mem_eraseDups.mp leftMember)
    (List.mem_eraseDups.mp rightMember)

/-- Duplicate-free alpha pairs have duplicate-free executable projections. -/
theorem AlphaBackwardFunctional.eraseDups_snd_nodup
    {alpha : List (LogicVar × String)}
    (backward : AlphaBackwardFunctional alpha) :
    (alpha.eraseDups.map Prod.snd).Nodup :=
  AlphaBackwardFunctional.snd_nodup_of_nodup
    (AlphaBackwardFunctional.eraseDups backward)
    (eraseDups_nodup_alpha alpha)

/-- Finite closed executable valuation induced by the shared alpha graph and
one representable canonical MGU.  Exact duplicate alpha pairs are erased;
inverse functionality then makes the executable association-list keys
unique. -/
noncomputable def groundedRuntime
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution)
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical) : Subst :=
  alpha.eraseDups.map fun pair =>
    (pair.2,
      groundedValue alpha canonical representable pair.1 pair.2)

@[simp] theorem groundedRuntime_keys
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution)
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical) :
    (groundedRuntime alpha canonical representable).map Prod.fst =
      alpha.eraseDups.map Prod.snd := by
  simp [groundedRuntime, List.map_map]

/-- Every live alpha spelling has an exact lookup in the constructed runtime
valuation, and that lookup is closed and semantically correct. -/
theorem groundedRuntime_lookup
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonical : TreeSubstitution}
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical)
    {identity : LogicVar} {name : String}
    (linked : (identity, name) ∈ alpha) :
    let runtime := groundedRuntime alpha canonical representable
    ∃ value,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup runtime name = some value ∧
        CanonicalRuntimeAgrees alpha
          (groundTree
            (TreeSubstitution.apply canonical (.variable identity)))
          value ∧
        value.vars = [] := by
  let value :=
    groundedValue alpha canonical representable identity name
  have alphaMember :
      (identity, name) ∈ alpha.eraseDups :=
    List.mem_eraseDups.mpr linked
  have runtimeMember :
      (name, value) ∈
        groundedRuntime alpha canonical representable := by
    apply List.mem_map.mpr
    exact ⟨(identity, name), alphaMember, rfl⟩
  have keysNodup :
      ((groundedRuntime alpha canonical representable).map Prod.fst).Nodup := by
    rw [groundedRuntime_keys]
    exact AlphaBackwardFunctional.eraseDups_snd_nodup shared.backward
  have lookup :
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup
          (groundedRuntime alpha canonical representable) name =
        some value :=
    Mettapedia.Languages.MeTTa.PLeaTTa.subst_lookup_of_mem_of_keys_nodup
      _ name value keysNodup runtimeMember
  have specification :=
    groundedValue_spec representable linked
  exact ⟨value, lookup, specification.1, specification.2⟩

/-- The constructed finite association list realizes the grounded canonical
valuation on every live alpha pair. -/
theorem groundedRuntime_valuation
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {canonical : TreeSubstitution}
    (representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical) :
    GroundAlphaValuationAgrees alpha canonical
      (groundedRuntime alpha canonical representable) := by
  intro identity name linked
  obtain ⟨value, lookup, agreement, closed⟩ :=
    groundedRuntime_lookup shared representable linked
  rw [Mettapedia.Languages.MeTTa.PLeaTTa.subst_var_of_lookup_closed _ _ _ lookup closed]
  exact agreement

/-! ## Unconditional executable success from the ordered canonical MGU -/

/-- The constructed closed runtime valuation is a comparator-respecting
unifier of the two complete executable payloads. -/
theorem SharedAlphaEquationsAgree.deepEquivalentUnifies_of_ordered_mgu
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ runtime,
      Mettapedia.Languages.MeTTa.PLeaTTa.DeepEquivalentUnifies Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical runtime
        [(.expr leftAtoms, .expr rightAtoms)] := by
  have representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.OrderedTreeMgu.binding_runtimeRepresentable
      derivation
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.runtimeRepresentable
        agreement)
  let runtime := groundedRuntime alpha canonical representable
  have valuation :
      GroundAlphaValuationAgrees alpha canonical runtime :=
    groundedRuntime_valuation shared representable
  refine ⟨runtime, ?_⟩
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  simp only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr]
  exact .expression
    (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.atomsEquivalent_of_ground_unifier
      shared.forward agreement valuation derivation.isMostGeneral.1)

/-- The actual exact-ground executable unifier succeeds for every
shared-alpha equation family carrying the independent ordered canonical MGU.
No runtime valuation is assumed: it is constructed above as a closed finite
instance of that MGU. -/
theorem unifyTopExact_complete_of_ordered_shared_alpha
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ result,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  obtain ⟨runtime, runtimeUnifies⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.deepEquivalentUnifies_of_ordered_mgu
      shared agreement derivation
  have equivalent :=
    runtimeUnifies (.expr leftAtoms, .expr rightAtoms) (by simp)
  exact Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_complete_of_prolog_equivalent_unifier
    (.expr leftAtoms) (.expr rightAtoms) runtime equivalent

/-- Every actual executable MGU returned for a shared-alpha head is general
enough to accept the independently ordered canonical MGU's closed runtime
instance.  The witness is constructed from the canonical derivation rather
than assumed, and factorization holds on every runtime atom.  This is the
ground-instance half of cross-representation output adequacy; it deliberately
does not identify the two open substitution spellings. -/
theorem unifyTopExact_ground_factor_of_ordered_shared_alpha
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    GroundAlphaResultFactors alpha canonical result := by
  have representable :
      TreeSubstitutionRuntimeRepresentable alpha canonical :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.OrderedTreeMgu.binding_runtimeRepresentable
      derivation
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.runtimeRepresentable
        agreement)
  let valuation := groundedRuntime alpha canonical representable
  have valuationAgrees :
      GroundAlphaValuationAgrees alpha canonical valuation :=
    groundedRuntime_valuation shared representable
  have valuationUnifies :
      Mettapedia.Languages.MeTTa.PLeaTTa.DeepEquivalentUnifies Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical valuation
        [(.expr leftAtoms, .expr rightAtoms)] := by
    intro equation member
    simp only [List.mem_singleton] at member
    subst equation
    simp only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr]
    exact .expression
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.atomsEquivalent_of_ground_unifier
        shared.forward agreement valuationAgrees
        derivation.isMostGeneral.1)
  have runtimeMgu :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_isMgu
      (.expr leftAtoms) (.expr rightAtoms) result returned
  exact ⟨valuation, valuationAgrees,
    runtimeMgu.2 valuation valuationUnifies⟩

/-- Current-binding specialization of unconditional ordered-MGU
completeness.  Agreement is stated after deep normalization by `base`,
exactly matching the operands passed to `unifyTopExact` inside `unifyB`. -/
theorem unifyB_complete_of_ordered_shared_alpha
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))
        (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ result,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result := by
  obtain ⟨runtime, runtimeUnifies⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.SharedAlphaEquationsAgree.deepEquivalentUnifies_of_ordered_mgu
      shared agreement derivation
  have equivalent :=
    runtimeUnifies
      (.expr (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)),
        .expr (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))) (by simp)
  apply Mettapedia.Languages.MeTTa.PLeaTTa.unifyB_complete_of_prolog_equivalent_unifier
    base (.expr leftAtoms) (.expr rightAtoms) runtime
  simpa only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using equivalent

/-- A successful `unifyB` call exposes a generated open MGU through which
the independently ordered canonical solution has a closed instance.  The
last conjunct pins the exact installation over `base`; no property of the
composed association-list spelling is smuggled into the factorization
claim. -/
theorem unifyB_result_has_ground_factor_of_ordered_shared_alpha
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))
        (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    ∃ generated,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
          (.expr (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))) =
          some generated ∧
        GroundAlphaResultFactors alpha canonical generated ∧
        result =
          match generated with
          | [] => base
          | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated base := by
  obtain ⟨generated, generatedEq, _, installed⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyB_result_has_generated_mgu
      base (.expr leftAtoms) (.expr rightAtoms) result returned
  have normalizedEq :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
          (.expr (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))) =
          some generated := by
    simpa only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using generatedEq
  have factors :=
    unifyTopExact_ground_factor_of_ordered_shared_alpha
      shared agreement derivation normalizedEq
  exact ⟨generated, normalizedEq, factors, installed⟩

/-- The live retained-clause alpha graph and payload theorem, normalized by
the incoming executable binding exactly once.  Both unconditional success
and returned-MGU adequacy consume this same interface, preventing the two
lanes from drifting on suffix freshness or head normalization. -/
theorem FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding) ++
          [Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length) :
    SharedRuntimeAlpha
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables)) ∧
      SharedAlphaEquationsAgree
        (queryAlpha ++
          RuntimeAlpha.graph
            (referenceFreshTargets
              (reference.freshCopy freshSeed).firstFresh
              reference.variables)
            (executableFreshTargets
              (resolutionFreshSuffix argsv result rest binding query seed)
              reference.variables))
        (argumentEquations queryTerms
          (reference.freshCopy freshSeed).clause.arguments)
        ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (((freshenResolutionClause argsv args result rest binding query
              seed barrier executable).params ++
            [(freshenResolutionClause argsv args result rest binding query
              seed barrier executable).result]).map
          (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) := by
  have shared :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguBridge.FreshenedClauseAlphaAgrees.sharedHeadEquations
      freshened queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  have stable :=
    subst_freshenResolutionClause_head_eq_self
      argsv args result rest binding query seed barrier highWater executable
  subst argsv
  refine ⟨shared.1, ?_⟩
  simpa only [List.map_append, List.map_singleton, stable.1, stable.2]
    using shared.2

/-- The real executable `unifyB` call at one retained nonempty-suffix clause
head succeeds from the independent ordered MGU alone.  Query/clause
allocator disjointness, suffix capture-freedom, and construction of a closed
runtime valuation are all internal conclusions. -/
theorem FreshenedClauseAlphaAgrees.unifyB_complete_of_ordered_mgu
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding) ++
          [Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu
        (denoteEquations
          (argumentEquations queryTerms
            (reference.freshCopy freshSeed).clause.arguments))
        canonical) :
    ∃ executableResult,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result])) =
        some executableResult := by
  have normalized :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
      freshened argsvEq queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  exact unifyB_complete_of_ordered_shared_alpha
    binding normalized.1 normalized.2 derivation

/-- Returned-substitution counterpart of
`unifyB_complete_of_ordered_mgu` at the actual retained-clause activation.
The live suffix-aware alpha graph constructs a canonical closed instance of
the generated executable MGU, and the exact `unifyB` installation remains
visible. -/
theorem FreshenedClauseAlphaAgrees.unifyB_result_has_ground_factor
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding) ++
          [Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu
        (denoteEquations
          (argumentEquations queryTerms
            (reference.freshCopy freshSeed).clause.arguments))
        canonical)
    {executableResult : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result])) =
        some executableResult) :
    ∃ generated,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
          some generated ∧
        GroundAlphaResultFactors
          (queryAlpha ++
            RuntimeAlpha.graph
              (referenceFreshTargets
                (reference.freshCopy freshSeed).firstFresh
                reference.variables)
              (executableFreshTargets
                (resolutionFreshSuffix argsv result rest binding query seed)
                reference.variables))
          canonical generated ∧
        executableResult =
          match generated with
          | [] => binding
          | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated binding := by
  have normalized :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
      freshened argsvEq queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  exact unifyB_result_has_ground_factor_of_ordered_shared_alpha
    binding normalized.1 normalized.2 derivation returned

/-! ## Anti-vacuity: success does not claim executable MGU agreement -/

private def residualWitnessX : LogicVar := .source "X"
private def residualWitnessY : LogicVar := .source "Y"

private def residualWitnessAlpha : List (LogicVar × String) :=
  [(residualWitnessX, "X"), (residualWitnessY, "Y")]

private def residualWitnessEquations : List (Term × Term) :=
  [(.variable residualWitnessX, .variable residualWitnessY)]

private def residualWitnessCanonical : TreeSubstitution :=
  [(residualWitnessX, .variable residualWitnessY)]

/-- The actual ordered executable MGU for the residual-alias discriminator
is open and has the same left-variable orientation as the canonical
derivation.  This concrete guard prevents the ground-factorization theorem
from being mistaken for a claim that the runtime reports its closed
completeness witness. -/
theorem residual_alias_executable_mgu_is_open :
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
        (.expr [.var "X"]) (.expr [.var "Y"]) =
      some [("X", .var "Y")] ∧
    Mettapedia.Languages.MeTTa.PLeaTTa.subst [("X", .var "Y")] (.var "Y") = .var "Y" := by
  constructor
  · unfold Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyTopWith, Atom.size,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyRoundsWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeAllWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeEqWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeListWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.occurs, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.extend, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.erase]
  · simp [Mettapedia.Languages.MeTTa.PLeaTTa.subst, Mettapedia.Languages.MeTTa.PLeaTTa.substN, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup]

/-- The completeness witness is intentionally stricter than the canonical
MGU.  For `X = Y`, the ordered MGU retains residual variable `Y`, while the
constructed executable witness grounds that residual variable and still
forces exact executable unification to succeed.  Thus the completeness
theorem cannot be cited as executable-output/MGU adequacy. -/
theorem residual_alias_grounding_is_strict :
    OrderedTreeMgu
        (denoteEquations residualWitnessEquations)
        residualWitnessCanonical ∧
      TreeSubstitution.apply residualWitnessCanonical
          (.variable residualWitnessY) =
        .variable residualWitnessY ∧
      groundTree
          (TreeSubstitution.apply residualWitnessCanonical
            (.variable residualWitnessY)) ≠
        TreeSubstitution.apply residualWitnessCanonical
          (.variable residualWitnessY) ∧
      ∃ result,
        Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
            (.expr [.var "X"]) (.expr [.var "Y"]) =
          some result := by
  have derivation :
      OrderedTreeMgu
        (denoteEquations residualWitnessEquations)
        residualWitnessCanonical := by
    apply OrderedTreeMgu.cons
      (.variable residualWitnessX) (.variable residualWitnessY) []
      residualWitnessCanonical []
    · exact .bindLeft residualWitnessX (.variable residualWitnessY)
        (by simp [residualWitnessX, residualWitnessY])
        (by simp [Tree.occurs, residualWitnessX, residualWitnessY])
    · exact .nil
  have shared : SharedRuntimeAlpha residualWitnessAlpha := by
    constructor
    · intro identity left right leftMember rightMember
      simp [residualWitnessAlpha, residualWitnessX, residualWitnessY]
        at leftMember rightMember
      rcases leftMember with leftMember | leftMember <;>
        rcases rightMember with rightMember | rightMember <;>
        simp_all
    · intro left right name leftMember rightMember
      simp [residualWitnessAlpha, residualWitnessX, residualWitnessY]
        at leftMember rightMember
      rcases leftMember with leftMember | leftMember <;>
        rcases rightMember with rightMember | rightMember <;>
        simp_all
  have agreement :
      SharedAlphaEquationsAgree residualWitnessAlpha
        residualWitnessEquations [.var "X"] [.var "Y"] :=
    .cons
      (.variable (by simp [residualWitnessAlpha]))
      (.variable (by simp [residualWitnessAlpha]))
      .nil
  refine ⟨derivation, ?_, ?_, ?_⟩
  · simp [residualWitnessCanonical, residualWitnessX, residualWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne]
  · simp [residualWitnessCanonical, residualWitnessX, residualWitnessY,
      TreeSubstitution.apply, Tree.instantiateOne, groundTree]
  · exact unifyTopExact_complete_of_ordered_shared_alpha
      shared agreement derivation

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation
