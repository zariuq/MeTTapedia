import Mettapedia.OSLF.Syntax.IndexedOperationalPresentationCategory

/-!
# Restricting a rule presentation to admitted judgments

An indexed rule presentation may have more raw constructors than an authored
typing judgment accepts. Restricting its judgment indices is not enough:
every recursive premise of a retained constructor must also have an admitted
index. The restricted shape therefore carries a proof for each child. The
inclusion is cartesian and retains individual premise positions and firing
histories.

This construction is independent of the choice of admission predicate. In
particular, instantiating it with endpoint typing does not itself prove that
every authored rewrite preserves typing; that is a separate source-to-model
obligation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePresentationCategory
open Mettapedia.OSLF.Binding.IndexedOperationalPresentationCategory

universe uBase uIndex uShape uPosition

variable {Base : Type uBase}

/-- The rule presentation whose judgments satisfy `Admit`. A constructor
survives exactly when each of its recursive child judgments is also
admitted; proof fields add no premise positions. -/
def restrict
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    Presentation.{uBase, uIndex, uShape, uPosition} Base where
  Judgment := fun b => {i : P.Judgment b // Admit b i}
  rules :=
    { Shape := fun b i =>
        {shape : P.rules.Shape b i.1 //
          ∀ position : P.rules.Position shape,
            Admit b (P.rules.next shape position)}
      Position := fun shape => P.rules.Position shape.1
      next := fun shape position =>
        ⟨P.rules.next shape.1 position, shape.2 position⟩ }

/-- Forget admission certificates without changing the underlying
judgment, rule constructor, or any recursive premise address. -/
def inclusion
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    restrict P Admit ⟶ P where
  judgment := fun _ index => index.1
  rules :=
    { onShape := fun _ _ shape => shape.1
      onPosition := fun _ _ shape => Equiv.refl (P.rules.Position shape.1)
      onNext := by intros; rfl }

/-- A source constructor with no recursive positions remains available at
each admitted conclusion. This gives the genuine base case for constructing
admitted firing trees. -/
def nullaryTree
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (b : Base) (i : P.Judgment b) (accepted : Admit b i)
    (shape : P.rules.Shape b i)
    (nullary : IsEmpty (P.rules.Position shape)) :
    (restrict P Admit).rules.Fix b ⟨i, accepted⟩ :=
  .roll ⟨shape, fun position => False.elim (nullary.false position)⟩
    (fun position => False.elim (nullary.false position))

/-- A raw constructor tree is admitted at every node, including every
recursive premise occurrence. This property is defined by structural
recursion over the actual proof-relevant tree. -/
noncomputable def AllNodesAdmitted
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    ∀ b i, P.rules.Fix b i → Prop :=
  IndexedPolynomial.Fix.eliminate P.rules
    (fun _ _ _ => Prop)
    (fun b i _shape _children ih =>
      Admit b i ∧ ∀ position, ih position)

/-- Node-wise admission at a constructor is precisely admission of its
conclusion together with admission of every individually addressed child. -/
@[simp] theorem allNodesAdmitted_roll
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (b : Base) (i : P.Judgment b)
    (shape : P.rules.Shape b i)
    (children : (position : P.rules.Position shape) →
      P.rules.Fix b (P.rules.next shape position)) :
    AllNodesAdmitted P Admit b i (.roll shape children) ↔
      Admit b i ∧ ∀ position,
        AllNodesAdmitted P Admit b (P.rules.next shape position)
          (children position) := by
  rfl

/-- The root of an admitted raw tree satisfies the same judgment
predicate used to index the restricted rule presentation. -/
theorem allNodesAdmitted_root
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (b : Base) (i : P.Judgment b) (tree : P.rules.Fix b i)
    (admitted : AllNodesAdmitted P Admit b i tree) : Admit b i := by
  match tree with
  | .roll shape children =>
      exact (allNodesAdmitted_roll P Admit b i shape children).mp
        admitted |>.1

/-- The cartesian inclusion maps complete admitted proof trees into raw
ones, preserving every constructor and child occurrence. -/
noncomputable def includeFree
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    free (restrict P Admit) ⟶ free P :=
  freeMap (inclusion P Admit)

/-- Erasing an admitted constructor tree produces a raw tree whose root
and every recursive child satisfy the selected judgment predicate. The
proof follows each original premise address, so repeated equal endpoints
remain separate occurrences. -/
theorem includeFree_allNodes
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (b : Base) (index : (restrict P Admit).Judgment b)
    (tree : (restrict P Admit).rules.Fix b index) :
    AllNodesAdmitted P Admit b index.1
      ((includeFree P Admit).toFun b index tree) := by
  refine IndexedPolynomial.Fix.eliminate (restrict P Admit).rules
    (fun b index tree => AllNodesAdmitted P Admit b index.1
      ((includeFree P Admit).toFun b index tree)) ?_ b index tree
  intro b index shape children ih
  apply (allNodesAdmitted_roll P Admit b index.1 shape.1
    (fun position =>
      (includeFree P Admit).toFun b _ (children position))).mpr
  exact ⟨index.2, ih⟩

/-- Recursively lift a raw constructor tree once every node has an
admission proof. The constructor and each original premise position are
retained; only proof fields are added. -/
noncomputable def liftAllNodes
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    ∀ b i (tree : P.rules.Fix b i)
      (admitted : AllNodesAdmitted P Admit b i tree),
      (restrict P Admit).rules.Fix b
        ⟨i, allNodesAdmitted_root P Admit b i tree admitted⟩ :=
  IndexedPolynomial.Fix.eliminate P.rules
    (fun b i tree => ∀ admitted : AllNodesAdmitted P Admit b i tree,
      (restrict P Admit).rules.Fix b
        ⟨i, allNodesAdmitted_root P Admit b i tree admitted⟩)
    (fun b i shape children ih admitted =>
      let details := (allNodesAdmitted_roll P Admit b i shape children).mp
        admitted
      .roll
        ⟨shape, fun position =>
          allNodesAdmitted_root P Admit b _ (children position)
            (details.2 position)⟩
        (fun position => ih position (details.2 position)))

/-- Admitting all nodes and then forgetting their certificates returns the
same complete raw firing tree, including repeated premise positions. -/
theorem includeFree_liftAllNodes
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    ∀ b i (tree : P.rules.Fix b i)
      (admitted : AllNodesAdmitted P Admit b i tree),
      (includeFree P Admit).toFun b
        ⟨i, allNodesAdmitted_root P Admit b i tree admitted⟩
        (liftAllNodes P Admit b i tree admitted) = tree := by
  refine IndexedPolynomial.Fix.eliminate P.rules
    (fun b i tree => ∀ admitted : AllNodesAdmitted P Admit b i tree,
      (includeFree P Admit).toFun b
        ⟨i, allNodesAdmitted_root P Admit b i tree admitted⟩
        (liftAllNodes P Admit b i tree admitted) = tree) ?_
  intro b i shape children ih admitted
  change IndexedPolynomial.Fix.roll shape _ =
    IndexedPolynomial.Fix.roll shape children
  congr 1
  funext position
  exact ih position
    (((allNodesAdmitted_roll P Admit b i shape children).mp
      admitted).2 position)

/-- Conversely, a tree already constructed in the restricted presentation
is recovered after erasure and node-wise re-admission. -/
theorem liftAllNodes_includeFree
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop) :
    ∀ b (index : (restrict P Admit).Judgment b)
      (tree : (restrict P Admit).rules.Fix b index),
      liftAllNodes P Admit b index.1
        ((includeFree P Admit).toFun b index tree)
        (includeFree_allNodes P Admit b index tree) = tree := by
  refine IndexedPolynomial.Fix.eliminate (restrict P Admit).rules
    (fun b index tree =>
      liftAllNodes P Admit b index.1
        ((includeFree P Admit).toFun b index tree)
        (includeFree_allNodes P Admit b index tree) = tree) ?_
  intro b index shape children ih
  change IndexedPolynomial.Fix.roll shape _ =
    IndexedPolynomial.Fix.roll shape children
  congr 1
  funext position
  exact ih position

/-- Complete trees in the restricted rule presentation are equivalent to
raw trees for which *every* constructor occurrence passes admission. This
equivalence retains the original shape and premise-position tree; it is
stronger than agreement of endpoint predicates. -/
noncomputable def admittedTreeEquiv
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (b : Base) (i : P.Judgment b) (accepted : Admit b i) :
    (restrict P Admit).rules.Fix b ⟨i, accepted⟩ ≃
      {tree : P.rules.Fix b i // AllNodesAdmitted P Admit b i tree} where
  toFun tree := ⟨(includeFree P Admit).toFun b ⟨i, accepted⟩ tree,
    includeFree_allNodes P Admit b ⟨i, accepted⟩ tree⟩
  invFun raw := liftAllNodes P Admit b i raw.1 raw.2
  left_inv := by
    intro tree
    exact liftAllNodes_includeFree P Admit b ⟨i, accepted⟩ tree
  right_inv := by
    intro raw
    apply Subtype.ext
    exact includeFree_liftAllNodes P Admit b i raw.1 raw.2

/-- Interpretations of the restricted free rule algebra are exactly
cartesian interpretations of the restricted presentation. -/
noncomputable def freeHomEquiv
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (target : Equipped.{uBase, uIndex, uShape, uPosition} Base) :
    (free (restrict P Admit) ⟶ target) ≃
      (restrict P Admit ⟶ target.presentation) :=
  IndexedOperationalPresentationCategory.freeHomEquiv
    (restrict P Admit) target

/-- Restricting an interpretation along the inclusion agrees with
interpreting the actual admitted free tree and then forgetting its
admission certificates. -/
theorem interpretation_restricts
    (P : Presentation.{uBase, uIndex, uShape, uPosition} Base)
    (Admit : ∀ b, P.Judgment b → Prop)
    (target : Equipped.{uBase, uIndex, uShape, uPosition} Base)
    (interpretation : free P ⟶ target) :
    freeHomEquiv P Admit target
      (includeFree P Admit ≫ interpretation) =
    inclusion P Admit ≫
      (IndexedOperationalPresentationCategory.freeHomEquiv P target)
        interpretation := by
  rfl

#print axioms inclusion
#print axioms includeFree
#print axioms includeFree_allNodes
#print axioms liftAllNodes
#print axioms includeFree_liftAllNodes
#print axioms liftAllNodes_includeFree
#print axioms admittedTreeEquiv
#print axioms freeHomEquiv
#print axioms interpretation_restricts

end Mettapedia.OSLF.Binding.AdmittedJudgmentRulePresentation
