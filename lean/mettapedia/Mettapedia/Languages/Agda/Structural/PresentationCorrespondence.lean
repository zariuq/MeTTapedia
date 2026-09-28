import Mettapedia.Languages.Agda.Structural.PresentationCompleteness
import Mettapedia.Languages.Agda.Structural.PresentationSoundness

/-!
# Proof-relevant correspondence of the computation presentation

The translations retain argument positions, generated premise outputs, and
root declaration addresses. Their inverse laws compare complete derivations,
including cases where distinct occurrences have the same endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

/-- Selecting a generated congruence recovers its actual argument occurrence. -/
theorem selectArgument_compatibleAt {Γ : Ctx sig} :
    ∀ {arity : List (MetaArity sig)} (args : Args sig arity Γ)
      (position : Fin arity.length)
      (result : Term sig ((arity.get position).1 ++ Γ) (arity.get position).2)
      (child : Step (IntrinsicScopedLocalCongruence.getArg args position) result),
      selectArgument (IntrinsicScopedLocalCongruence.compatibleAt args position result child) =
        ⟨position, result, rfl, stepToTree child⟩
  | _ :: _, .cons _ _, ⟨0, _⟩, _, _ => rfl
  | _ :: _, .cons head tail, ⟨n + 1, bound⟩, result, child => by
      let lift (selected : SelectedArgument tail
          (IntrinsicScopedLocalCongruence.replaceArg tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ result)) :
          SelectedArgument (.cons head tail)
            (.cons head (IntrinsicScopedLocalCongruence.replaceArg tail
              ⟨n, Nat.lt_of_succ_lt_succ bound⟩ result)) :=
        ⟨selected.position.succ, selected.result,
          congrArg (Args.cons head) selected.replaced, selected.child⟩
      exact congrArg lift
        (selectArgument_compatibleAt tail ⟨n, Nat.lt_of_succ_lt_succ bound⟩ result child)

/-- Encoding a selected argument uses exactly its generated rule constructor. -/
theorem stepToTree_compatibleAt {Γ : Ctx sig} {s : Srt} (op : Op s)
    (args : Args sig (sig.arity op) Γ) (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (child : Step (IntrinsicScopedLocalCongruence.getArg args position) result) :
    stepToTree (.congr op (IntrinsicScopedLocalCongruence.compatibleAt args position result child)) =
      Authored.congruenceTree op args position result (stepToTree child) := by
  exact congrArg (fun selected : SelectedArgument args
      (IntrinsicScopedLocalCongruence.replaceArg args position result) =>
    selected.replaced ▸ Authored.congruenceTree op args selected.position selected.result selected.child)
    (selectArgument_compatibleAt args position result child)

private theorem argsTail_transport {Γ : Ctx sig} {binders : Ctx sig} {s : Srt}
    {arity : List (MetaArity sig)} (head : Term sig (binders ++ Γ) s)
    {source first second : Args sig arity Γ} (same : first = second)
    (proof : ArgsStep source first) :
    (congrArg (Args.cons head) same) ▸ CompatibleDerivations.ArgsStep.tail head proof =
      CompatibleDerivations.ArgsStep.tail head (same ▸ proof) := by
  cases same
  rfl

private theorem argsCongr_transport {Γ : Ctx sig} {s : Srt} (op : Op s)
    {source first second : Args sig (sig.arity op) Γ} (same : first = second)
    (proof : ArgsStep source first) :
    same ▸ CompatibleDerivations.Step.congr (S := sig) (R := Root) op proof =
      CompatibleDerivations.Step.congr (S := sig) (R := Root) op (same ▸ proof) := by
  cases same
  rfl

private theorem treeToStep_transport {Γ : Ctx sig} {s : Srt} (op : Op s)
    {source first second : Args sig (sig.arity op) Γ} (same : first = second)
    (tree : Tree Authored.computationRules Authored.algebra
      ⟨Γ, s, .op op source, .op op first⟩) :
    treeToStep (same ▸ tree) = same ▸ treeToStep tree := by
  cases same
  rfl


/-- The completeness map on an arbitrary polynomial judgment. -/
def encodeStepAt : {j : Judgment Authored.algebra} → StepAt j →
    Tree Authored.computationRules Authored.algebra j
  | ⟨_, _, _, _⟩, derivation => stepToTree derivation

private def rootTreeAt : {j : Judgment Authored.algebra} → Authored.RootAt j →
    Tree Authored.computationRules Authored.algebra j
  | ⟨_, _, _, _⟩, root => Authored.rootTree root

private def treeOfRootShape {j : Judgment Authored.algebra}
    (shape : Shape Authored.roots Authored.algebra j) :
    Tree Authored.computationRules Authored.algebra j :=
  shape.2 ▸ Authored.fireAddress (Authored.rootAddress shape.1.index) shape.1.ambient
    shape.1.valuation shape.1.close (fun position =>
      Fin.elim0 (Fin.cast (congrArg List.length
        (Authored.root_premises_empty shape.1.index)) position))

private theorem treeOfRootShape_shapeOfRootAt {j : Judgment Authored.algebra}
    (root : Authored.RootAt j) :
    treeOfRootShape (Authored.shapeOfRootAt root) = rootTreeAt root := by
  rcases j with ⟨Γ, s, source, target⟩
  rfl

private theorem rootTreeAt_rootOfShape {j : Judgment Authored.algebra}
    (shape : Shape Authored.roots Authored.algebra j) :
    rootTreeAt (Authored.rootOfShape shape) = treeOfRootShape shape :=
  (treeOfRootShape_shapeOfRootAt (Authored.rootOfShape shape)).symm.trans
    (congrArg treeOfRootShape (Authored.shapeOfRootAt_rootOfShape shape))

private theorem rootFire_eq (index : Fin Authored.roots.length) (Γ : Ctx sig)
    (values : Valuation (M := (Authored.roots.get index).1) Authored.algebra Γ)
    (close : Sub sig (Authored.roots.get index).2.conclusion.ctx Γ)
    (children : (position : Fin (Authored.roots.get index).2.premises.length) →
      Tree Authored.computationRules Authored.algebra
        (childJudgment [Authored.roots.get index] Authored.algebra
          (Authored.localOccurrence (Authored.roots.get index) Γ values close) position)) :
    Authored.fireAddress (Authored.rootAddress index) Γ values close children =
      treeOfRootShape ⟨⟨index, Γ, values, close⟩, rfl⟩ := by
  apply congrArg (Authored.fireAddress (Authored.rootAddress index) Γ values close)
  funext position
  exact Fin.elim0 (Fin.cast (congrArg List.length (Authored.root_premises_empty index)) position)

private def RoundTrip {j : Judgment Authored.algebra}
    (tree : Tree Authored.computationRules Authored.algebra j) : Prop :=
  encodeStepAt (interpretTree tree) = tree

private theorem roundTrip_mp {first second : Judgment Authored.algebra}
    (same : first = second) (tree : Tree Authored.computationRules Authored.algebra first)
    (proof : RoundTrip tree) :
    RoundTrip ((congrArg (Tree Authored.computationRules Authored.algebra) same).mp tree) := by
  cases same
  exact proof

private theorem roundTrip_of_mp {first second : Judgment Authored.algebra}
    (same : first = second) (tree : Tree Authored.computationRules Authored.algebra first)
    (proof : RoundTrip ((congrArg (Tree Authored.computationRules Authored.algebra) same).mp tree)) :
    RoundTrip tree := by
  cases same
  exact proof

private def GoodValues {r : LocalRule sig} (address : Authored.Address r) (Γ : Ctx sig)
    (values : Valuation (M := r.1) Authored.algebra Γ)
    (close : Sub sig r.2.conclusion.ctx Γ) : Prop :=
  ∀ (children : (position : Fin r.2.premises.length) →
      Tree Authored.computationRules Authored.algebra
        (childJudgment [r] Authored.algebra (Authored.localOccurrence r Γ values close) position)),
    (∀ position, RoundTrip (children position)) →
    RoundTrip (Authored.fireAddress address Γ values close children)

private theorem mpr_mp {α β : Type} (same : α = β) (value : α) :
    same.mpr (same.mp value) = value := by
  cases same
  rfl

private theorem congruenceFire_eq {Γ : Ctx sig} {s : Srt} (op : Op s)
    (args : Args sig (sig.arity op) Γ) (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (children : (p : Fin (IntrinsicScopedLocalCongruence.rule (S := sig) op position).2.premises.length) →
      Tree Authored.computationRules Authored.algebra
        (childJudgment [IntrinsicScopedLocalCongruence.rule (S := sig) op position] Authored.algebra
          (IntrinsicScopedLocalCongruence.occurrence (S := sig) op position args result) p)) :
    Authored.congruenceTree op args position result
        ((congrArg (Tree Authored.computationRules Authored.algebra)
          (IntrinsicScopedLocalCongruence.child_occurrence (S := sig) op position args result)).mp
          (children ⟨0, Nat.zero_lt_succ 0⟩)) =
      (congrArg (Tree Authored.computationRules Authored.algebra)
        (IntrinsicScopedLocalCongruence.conclusion_occurrence (S := sig) op position args result)).mp
        (Authored.fireAddress (Authored.congruenceAddress op position) Γ
          (IntrinsicScopedLocalCongruence.valuation (S := sig) op position args result)
          (IntrinsicScopedLocalCongruence.emptyClose Γ) children) := by
  apply congrArg ((congrArg (Tree Authored.computationRules Authored.algebra)
    (IntrinsicScopedLocalCongruence.conclusion_occurrence (S := sig) op position args result)).mp)
  apply congrArg (Authored.fireAddress (Authored.congruenceAddress op position) Γ
    (IntrinsicScopedLocalCongruence.valuation (S := sig) op position args result)
    (IntrinsicScopedLocalCongruence.emptyClose Γ))
  funext childPosition
  have zero : childPosition = (⟨0, Nat.zero_lt_succ 0⟩ : Fin 1) := Fin.eq_zero childPosition
  subst childPosition
  exact mpr_mp _ _


mutual
/-- Interpreting the encoding returns the entire original compatible derivation. -/
theorem treeToStep_stepToTree : ∀ {Γ : Ctx sig} {s : Srt}
    {source target : Term sig Γ s} (derivation : Step source target),
    treeToStep (stepToTree derivation) = derivation
  | _, _, _, _, .root root => interpretTree_rootTree root
  | _, _, _, _, @CompatibleDerivations.Step.congr _ _ _ _ op source _ arguments => by
      let selected := selectArgument arguments
      have fired := interpretTree_congruenceTree op source selected.position
        selected.result selected.child
      exact (treeToStep_transport op selected.replaced
        (Authored.congruenceTree op source selected.position selected.result selected.child)).trans
        ((congrArg (fun proof : Step (.op op source)
            (.op op (IntrinsicScopedLocalCongruence.replaceArg source selected.position selected.result)) =>
            selected.replaced ▸ proof) fired).trans
          ((argsCongr_transport op selected.replaced
            (IntrinsicScopedLocalCongruence.compatibleAt source selected.position selected.result
              (treeToStep selected.child))).trans
            (congrArg (CompatibleDerivations.Step.congr (S := sig) (R := Root) op)
              (selectArgument_sound arguments))))

private theorem selectArgument_sound : ∀ {Γ : Ctx sig} {arity : List (MetaArity sig)}
    {source target : Args sig arity Γ} (derivation : ArgsStep source target),
    (selectArgument derivation).replaced ▸
        IntrinsicScopedLocalCongruence.compatibleAt source (selectArgument derivation).position
          (selectArgument derivation).result (treeToStep (selectArgument derivation).child) = derivation
  | _, _, _, _, .head tail child =>
      congrArg (CompatibleDerivations.ArgsStep.head tail) (treeToStep_stepToTree child)
  | _, _, _, _, .tail head child =>
      (argsTail_transport head (selectArgument child).replaced
        (IntrinsicScopedLocalCongruence.compatibleAt _ (selectArgument child).position
          (selectArgument child).result (treeToStep (selectArgument child).child))).trans
        (congrArg (CompatibleDerivations.ArgsStep.tail head) (selectArgument_sound child))
end

private theorem roundTrip_root {j : Judgment Authored.algebra} (root : Authored.RootAt j) :
    RoundTrip (rootTreeAt root) := by
  rcases j with ⟨Γ, s, source, target⟩
  change stepToTree (treeToStep (Authored.rootTree root)) = Authored.rootTree root
  exact congrArg (fun proof : Step source target => stepToTree proof) (interpretTree_rootTree root)

private theorem goodValues_root (index : Fin Authored.roots.length) (Γ : Ctx sig)
    (values : Valuation (M := (Authored.roots.get index).1) Authored.algebra Γ)
    (close : Sub sig (Authored.roots.get index).2.conclusion.ctx Γ) :
    GoodValues (Authored.rootAddress index) Γ values close := by
  intro children _childrenRoundTrip
  have same := (rootFire_eq index Γ values close children).trans
    (rootTreeAt_rootOfShape ⟨⟨index, Γ, values, close⟩, rfl⟩).symm
  exact (congrArg RoundTrip same).mpr
    (roundTrip_root (Authored.rootOfShape ⟨⟨index, Γ, values, close⟩, rfl⟩))

private theorem roundTrip_congruence {Γ : Ctx sig} {s : Srt} (op : Op s)
    (args : Args sig (sig.arity op) Γ) (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2)
    (child : Tree Authored.computationRules Authored.algebra
      ⟨((sig.arity op).get position).1 ++ Γ, ((sig.arity op).get position).2,
        IntrinsicScopedLocalCongruence.getArg args position, result⟩)
    (childRoundTrip : RoundTrip child) :
    RoundTrip (Authored.congruenceTree op args position result child) := by
  exact (congrArg (fun proof => stepToTree proof)
    (interpretTree_congruenceTree op args position result child)).trans
    ((stepToTree_compatibleAt op args position result (treeToStep child)).trans
      (congrArg (Authored.congruenceTree op args position result) childRoundTrip))

private theorem goodValues_congruence_canonical {Γ : Ctx sig} {s : Srt} (op : Op s)
    (args : Args sig (sig.arity op) Γ) (position : Fin (sig.arity op).length)
    (result : Term sig (((sig.arity op).get position).1 ++ Γ) ((sig.arity op).get position).2) :
    GoodValues (Authored.congruenceAddress op position) Γ
      (IntrinsicScopedLocalCongruence.valuation (S := sig) op position args result)
      (IntrinsicScopedLocalCongruence.emptyClose Γ) := by
  intro children childrenRoundTrip
  let sameChild := IntrinsicScopedLocalCongruence.child_occurrence (S := sig) op position args result
  let sameConclusion := IntrinsicScopedLocalCongruence.conclusion_occurrence (S := sig) op position args result
  have childRoundTrip := roundTrip_mp sameChild (children ⟨0, Nat.zero_lt_succ 0⟩)
    (childrenRoundTrip ⟨0, Nat.zero_lt_succ 0⟩)
  have congruenceRoundTrip := roundTrip_congruence op args position result _ childRoundTrip
  have transported := (congrArg RoundTrip (congruenceFire_eq op args position result children)).mp
    congruenceRoundTrip
  exact roundTrip_of_mp sameConclusion _ transported

private theorem goodValues_congruence {Γ : Ctx sig} {s : Srt} (op : Op s)
    (position : Fin (sig.arity op).length)
    (values : Valuation (M := (IntrinsicScopedLocalCongruence.rule (S := sig) op position).1)
      Authored.algebra Γ)
    (close : Sub sig (IntrinsicScopedLocalCongruence.rule (S := sig) op position).2.conclusion.ctx Γ) :
    GoodValues (Authored.congruenceAddress op position) Γ values close := by
  have close_same : close = IntrinsicScopedLocalCongruence.emptyClose Γ := by
    funext resultSort var
    nomatch var
  cases close_same
  exact (congrArg (fun vals => GoodValues (Authored.congruenceAddress op position) Γ vals
      (IntrinsicScopedLocalCongruence.emptyClose Γ))
    (IntrinsicScopedLocalCongruence.valuation_recovery (S := sig) op position values)).mp
      (goodValues_congruence_canonical op (IntrinsicScopedLocalCongruence.inputs (S := sig) op position values)
        position (values ⟨0, Nat.zero_lt_succ _⟩))


private def GoodIndex (index : Fin Authored.computationRules.length) : Prop :=
  ∀ (Γ : Ctx sig)
    (values : Valuation (M := (Authored.computationRules.get index).1) Authored.algebra Γ)
    (close : Sub sig (Authored.computationRules.get index).2.conclusion.ctx Γ),
    GoodValues (⟨index, rfl⟩ : Authored.Address (Authored.computationRules.get index)) Γ values close

private theorem goodIndex_of_address {r : LocalRule sig} (address : Authored.Address r)
    (good : ∀ (Γ : Ctx sig) (values : Valuation (M := r.1) Authored.algebra Γ)
      (close : Sub sig r.2.conclusion.ctx Γ), GoodValues address Γ values close) :
    GoodIndex address.index := by
  rcases address with ⟨index, same⟩
  subst r
  exact good

/-- Every table address is a retained root declaration or generated argument slot. -/
theorem computation_index_cases (index : Fin Authored.computationRules.length) :
    (∃ rootIndex : Fin Authored.roots.length, index = (Authored.rootAddress rootIndex).index) ∨
    (∃ (s : Srt) (op : Op s) (position : Fin (sig.arity op).length),
      index = Authored.congruenceIndex op position) := by
  rcases index with ⟨i, bound⟩
  match i with
  | 0 => exact Or.inl ⟨⟨0, by decide⟩, rfl⟩
  | 1 => exact Or.inl ⟨⟨1, by decide⟩, rfl⟩
  | 2 => exact Or.inl ⟨⟨2, by decide⟩, rfl⟩
  | 3 => exact Or.inl ⟨⟨3, by decide⟩, rfl⟩
  | 4 => exact Or.inl ⟨⟨4, by decide⟩, rfl⟩
  | 5 => exact Or.inl ⟨⟨5, by decide⟩, rfl⟩
  | 6 => exact Or.inr ⟨.term, .lam, ⟨0, by decide⟩, rfl⟩
  | 7 => exact Or.inr ⟨.term, .lamNoAbs, ⟨0, by decide⟩, rfl⟩
  | 8 => exact Or.inr ⟨.term, .pi, ⟨0, by decide⟩, rfl⟩
  | 9 => exact Or.inr ⟨.term, .pi, ⟨1, by decide⟩, rfl⟩
  | 10 => exact Or.inr ⟨.term, .piNoAbs, ⟨0, by decide⟩, rfl⟩
  | 11 => exact Or.inr ⟨.term, .piNoAbs, ⟨1, by decide⟩, rfl⟩
  | 12 => exact Or.inr ⟨.term, .eliminate, ⟨0, by decide⟩, rfl⟩
  | 13 => exact Or.inr ⟨.term, .eliminate, ⟨1, by decide⟩, rfl⟩
  | 14 => exact Or.inr ⟨.term, .sortTerm, ⟨0, by decide⟩, rfl⟩
  | 15 => exact Or.inr ⟨.term, .levelTerm, ⟨0, by decide⟩, rfl⟩
  | 16 => exact Or.inr ⟨.type, .el, ⟨0, by decide⟩, rfl⟩
  | 17 => exact Or.inr ⟨.type, .el, ⟨1, by decide⟩, rfl⟩
  | 18 => exact Or.inr ⟨.sort, .set, ⟨0, by decide⟩, rfl⟩
  | 19 => exact Or.inr ⟨.sort, .prop, ⟨0, by decide⟩, rfl⟩
  | 20 => exact Or.inr ⟨.level, .levelSuc, ⟨0, by decide⟩, rfl⟩
  | 21 => exact Or.inr ⟨.level, .levelMax, ⟨0, by decide⟩, rfl⟩
  | 22 => exact Or.inr ⟨.level, .levelMax, ⟨1, by decide⟩, rfl⟩
  | 23 => exact Or.inr ⟨.level, .levelNeutral, ⟨0, by decide⟩, rfl⟩
  | 24 => exact Or.inr ⟨.elim, .apply, ⟨0, by decide⟩, rfl⟩
  | 25 => exact Or.inr ⟨.spine, .cons, ⟨0, by decide⟩, rfl⟩
  | 26 => exact Or.inr ⟨.spine, .cons, ⟨1, by decide⟩, rfl⟩
  | 27 => exact Or.inr ⟨.spine, .append, ⟨0, by decide⟩, rfl⟩
  | 28 => exact Or.inr ⟨.spine, .append, ⟨1, by decide⟩, rfl⟩
  | i + 29 =>
      exfalso
      change i + 29 < 29 at bound
      omega

private theorem goodIndex (index : Fin Authored.computationRules.length) : GoodIndex index := by
  rcases computation_index_cases index with ⟨rootIndex, rfl⟩ | ⟨s, op, position, rfl⟩
  · exact goodIndex_of_address (Authored.rootAddress rootIndex) (goodValues_root rootIndex)
  · exact goodIndex_of_address (Authored.congruenceAddress op position)
      (fun _ values close => goodValues_congruence op position values close)

/-- Encoding the interpretation recovers every constructor and every ordered child. -/
theorem encodeStepAt_interpretTree {j : Judgment Authored.algebra}
    (tree : Tree Authored.computationRules Authored.algebra j) :
    encodeStepAt (interpretTree tree) = tree :=
  Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate
    (rules Authored.computationRules Authored.algebra) (fun _ _ tree => RoundTrip tree)
    (fun _ _ shape children childrenRoundTrip => by
      rcases shape with ⟨event, same⟩
      cases same
      exact goodIndex event.index event.ambient event.valuation event.close children childrenRoundTrip)
    () j tree

/-- Both translations preserve the complete proof objects at exact endpoints. -/
theorem stepToTree_treeToStep {Γ : Ctx sig} {s : Srt} {source target : Term sig Γ s}
    (tree : Tree Authored.computationRules Authored.algebra ⟨Γ, s, source, target⟩) :
    stepToTree (treeToStep tree) = tree := encodeStepAt_interpretTree tree

/-- The full 29-rule firing histories and compatible structural derivations coincide. -/
def treeStepEquiv {Γ : Ctx sig} {s : Srt} (source target : Term sig Γ s) :
    Tree Authored.computationRules Authored.algebra ⟨Γ, s, source, target⟩ ≃ Step source target where
  toFun := treeToStep
  invFun := stepToTree
  left_inv := stepToTree_treeToStep
  right_inv := treeToStep_stepToTree

/-- Equal endpoints do not collapse the two overlapping computational occurrences. -/
theorem encoded_overlapping_occurrences_distinct :
    stepToTree Controls.outerOccurrence ≠ stepToTree Controls.innerOccurrence := by
  intro same
  exact Controls.overlapping_occurrences_distinct
    ((treeStepEquiv Controls.overlapSource Controls.overlapTarget).symm.injective same)

/-- Positive control: decoding the actual identity-beta tree recovers its root evidence. -/
theorem identity_beta_tree_roundTrip :
    treeToStep (stepToTree Controls.identityBeta) = Controls.identityBeta :=
  treeToStep_stepToTree Controls.identityBeta

#print axioms selectArgument_compatibleAt
#print axioms stepToTree_compatibleAt
#print axioms treeToStep_stepToTree
#print axioms encodeStepAt_interpretTree
#print axioms treeStepEquiv
#print axioms encoded_overlapping_occurrences_distinct

end Mettapedia.Languages.Agda.Structural
