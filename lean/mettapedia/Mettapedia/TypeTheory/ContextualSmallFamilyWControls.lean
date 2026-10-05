import Mettapedia.TypeTheory.ContextualSmallFamilyWSubstitutionCoherence
import Mettapedia.TypeTheory.ContextualSmallFamilyTypeFormerControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualWComparison

/-!
# Infinite growing contextual W controls

The parameters include arbitrary bare hypersets. Cyclic parameters have
branching nodes whose dependent positions grow at every later stage;
ordinary leaf tags have no positions. Actual trees and substitutions
retain those full future branches and the wider parameter coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSmallFamilyWControls

open CategoryTheory MaterialSets.Hypersets
open ContextualSmallFamilyTypeFormers ContextualSmallFamilyTypeFormerCoherence
open ContextualSmallFamilyUniverseControls ContextualSmallFamilyTypeFormerControls
open ContextualSmallFamilyWTypes ContextualSmallFamilyWAlgebra
open PowerClassPresheafBaseChange

def growingPositions : cyclicSmall.Elements ⥤ Type where
  obj argument := {position : Fin (argument.1.1 + 1) // argument.2.2.val = true}
  map {first second} step := TypeCat.ofHom fun position =>
    ⟨Fin.castLE (Nat.succ_le_succ (leOfHom step.1.1)) position.val, by
      have tags : first.2.2.val = second.2.2.val :=
        congrArg (fun label : cyclicSmall.obj second.1 => label.2.val) step.2
      exact tags.symm.trans position.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro position
    exact Subtype.ext (Fin.ext rfl)
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro position
    exact Subtype.ext (Fin.ext rfl)

def zeroLeaf (point : parameters.Elements) : WAt cyclicSmall growingPositions point :=
  ContextualWTypes.sup (futureDomain cyclicSmall point) (futureBody cyclicSmall growingPositions point)
    (falseMember point.1 point.2)
    (fun _ _ position => Bool.noConfusion position.property)
    (fun _ _ _ _ position => Bool.noConfusion position.property)

theorem zeroLeaf_natural {first second : parameters.Elements} (step : first ⟶ second) :
    wMap cyclicSmall growingPositions step (zeroLeaf first) = zeroLeaf second := by
  rcases first with ⟨first, material⟩
  rcases second with ⟨second, otherMaterial⟩
  rcases step with ⟨arrow, same⟩
  change material = otherMaterial at same
  subst otherMaterial
  let step : parameter first material ⟶ parameter second material := ⟨arrow, rfl⟩
  apply Subtype.ext
  apply eq_of_heq
  refine (wMap_raw cyclicSmall growingPositions step (zeroLeaf (parameter first material))).trans ?_
  have labels : HEq ((futureDomain cyclicSmall (parameter first material)).map
      (ContextualSmallFamilyUniverse.rootArrow arrow) (falseMember first material)) (falseMember second material) :=
    heq_of_eq (Prod.ext (Fin.ext rfl) (Subtype.ext rfl))
  apply ContextualWReindexing.sup_heq (signature_prefix cyclicSmall growingPositions step) rfl _ _ labels
  intro future firstArrow secondArrow arrows firstPosition secondPosition positions
  exact Bool.noConfusion firstPosition.property

noncomputable def starNode (point : parameters.Elements) (label : cyclicSmall.obj point) :
    ContextualSmallFamilyWPolynomial.At cyclicSmall growingPositions (w cyclicSmall growingPositions) point :=
  ⟨label, {
    app future _arrow _position := zeroLeaf (ContextualSmallFamilyWCone.futurePoint point future)
    naturality _ _ _ later _position :=
      zeroLeaf_natural ((ContextualSmallFamilyUniverse.futureElement point.1 point.2).map later) }⟩

noncomputable def starValue (point : parameters.Elements) (label : cyclicSmall.obj point) :
    WAt cyclicSmall growingPositions point := constructorValue cyclicSmall growingPositions point (starNode point label)

theorem zeroLeaf_heq {first second : parameters.Elements} (points : first = second) : HEq (zeroLeaf first) (zeroLeaf second) := by
  cases points
  rfl

theorem starNode_natural {first second : parameters.Elements} (step : first ⟶ second) (label : cyclicSmall.obj first) :
    ContextualSmallFamilyWPolynomial.pMap cyclicSmall growingPositions (w cyclicSmall growingPositions) step
      (starNode first label) = starNode second (cyclicSmall.map step label) := by
  rcases first with ⟨first, material⟩
  rcases second with ⟨second, otherMaterial⟩
  rcases step with ⟨arrow, same⟩
  change material = otherMaterial at same
  subst otherMaterial
  let firstPoint := parameter first material
  let secondPoint := parameter second material
  let step : firstPoint ⟶ secondPoint := ⟨arrow, rfl⟩
  let coneChange := ContextualSmallFamilyUniverse.futurePrefix arrow
  let root := ContextualSmallFamilyUniverse.root second
  let sourceNode := ContextualWPolynomialReindexing.pull coneChange
    (ContextualSmallFamilyWPolynomial.signature cyclicSmall growingPositions (w cyclicSmall growingPositions) firstPoint) root
    ((ContextualWPolynomialReindexing.family
      (ContextualSmallFamilyWPolynomial.signature cyclicSmall growingPositions (w cyclicSmall growingPositions) firstPoint)).map
      (ContextualSmallFamilyUniverse.rootArrow arrow) (starNode firstPoint label))
  let targetNode := starNode secondPoint (cyclicSmall.map step label)
  have labels : HEq sourceNode.1 targetNode.1 := heq_of_eq (Prod.ext (Fin.ext rfl) (Subtype.ext rfl))
  have nodes := ContextualWPolynomialReindexing.node_ext_heq
    (ContextualSmallFamilyWPolynomial.signature_prefix cyclicSmall growingPositions (w cyclicSmall growingPositions) step)
    root sourceNode targetNode labels (by
      intro future firstArrow secondArrow arrows firstPosition secondPosition positions
      exact zeroLeaf_heq (prefixPoint_eq step future))
  exact eq_of_heq ((ContextualSmallFamilyWPolynomial.pMap_value cyclicSmall growingPositions
    (w cyclicSmall growingPositions) step (starNode firstPoint label)).trans nodes)

theorem starValue_natural {first second : parameters.Elements} (step : first ⟶ second) (label : cyclicSmall.obj first) :
    wMap cyclicSmall growingPositions step (starValue first label) = starValue second (cyclicSmall.map step label) :=
  (ContextualSmallFamilyWConstructor.constructor_natural cyclicSmall growingPositions step (starNode first label)).trans
    (congrArg (constructorValue cyclicSmall growingPositions second) (starNode_natural step label))

noncomputable def oneStar (stage : Nat) : WAt cyclicSmall growingPositions (parameter stage HSet.quineAtom) :=
  starValue (parameter stage HSet.quineAtom) (cyclicMember stage)

theorem oneStar_natural {first second : Nat} (arrow : first ⟶ second) :
    wMap cyclicSmall growingPositions (CategoryOfElements.homMk (F := parameters)
      (parameter first HSet.quineAtom) (parameter second HSet.quineAtom) arrow rfl) (oneStar first) = oneStar second :=
  (starValue_natural (CategoryOfElements.homMk (F := parameters)
    (parameter first HSet.quineAtom) (parameter second HSet.quineAtom) arrow rfl) (cyclicMember first)).trans
    (congrArg (starValue (parameter second HSet.quineAtom)) (Prod.ext (Fin.ext rfl) (Subtype.ext rfl)))

theorem branching_tree_differs_from_leaf (stage : Nat) : oneStar stage ≠ zeroLeaf (parameter stage HSet.quineAtom) := by
  intro same
  have labels := congrArg
    (fun tree : WAt cyclicSmall growingPositions (parameter stage HSet.quineAtom) =>
      (destructorValue cyclicSmall growingPositions (parameter stage HSet.quineAtom) tree).1.2.val) same
  dsimp only [oneStar, starValue] at labels
  rw [ContextualSmallFamilyWAlgebra.destructor_constructor] at labels
  change true = false at labels
  cases labels

def newFuture (stage : Nat) : Future.Objects 0 := ⟨stage + 1, homOfLE (Nat.zero_le _)⟩

def newlyAvailablePosition (stage : Nat) :
    ContextualWTypes.Position (futureDomain cyclicSmall (parameter 0 HSet.quineAtom))
      (futureBody cyclicSmall growingPositions (parameter 0 HSet.quineAtom))
      (X := ContextualSmallFamilyUniverse.root 0) (cyclicMember 0)
      (ContextualSmallFamilyUniverse.rootArrow (homOfLE (Nat.zero_le (stage + 1)))) :=
  ⟨⟨stage + 1, Nat.lt_succ_self (stage + 1)⟩, rfl⟩

theorem arbitrarily_new_future_positions (stage : Nat) : (newlyAvailablePosition stage).val.val = stage + 1 := rfl

theorem new_positions_cannot_be_present (stage : Nat) :
    ¬ ∃ position : ContextualWTypes.Position (futureDomain cyclicSmall (parameter 0 HSet.quineAtom))
      (futureBody cyclicSmall growingPositions (parameter 0 HSet.quineAtom))
      (X := ContextualSmallFamilyUniverse.root 0) (cyclicMember 0)
      (𝟙 (ContextualSmallFamilyUniverse.root 0)), position.val.val = (newlyAvailablePosition stage).val.val := by
  rintro ⟨position, same⟩
  have zero := congrArg Fin.val (Fin.eq_zero position.val)
  exact Nat.ne_of_lt (Nat.zero_lt_succ stage) (zero.symm.trans same)

noncomputable def futureBranchNode (bound : Nat) :
    ContextualSmallFamilyWPolynomial.At cyclicSmall growingPositions (w cyclicSmall growingPositions)
      (parameter 0 HSet.quineAtom) :=
  ⟨cyclicMember 0, {
    app future _arrow position :=
      if position.val.val ≤ bound then zeroLeaf (parameter future.1 HSet.quineAtom) else oneStar future.1
    naturality first second _earlier later position := by
      change wMap cyclicSmall growingPositions
        (CategoryOfElements.homMk (F := parameters) (parameter first.1 HSet.quineAtom)
          (parameter second.1 HSet.quineAtom) later.1 rfl)
        (if position.val.val ≤ bound then zeroLeaf (parameter first.1 HSet.quineAtom) else oneStar first.1) =
          (if position.val.val ≤ bound then zeroLeaf (parameter second.1 HSet.quineAtom) else oneStar second.1)
      by_cases small : position.val.val ≤ bound
      · rw [if_pos small, if_pos small]
        exact zeroLeaf_natural _
      · rw [if_neg small, if_neg small]
        exact oneStar_natural later.1 }⟩

noncomputable def futureBranchTree (bound : Nat) : WAt cyclicSmall growingPositions (parameter 0 HSet.quineAtom) :=
  constructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchNode bound)

def probePosition (value : Nat) :
    ContextualWTypes.Position (futureDomain cyclicSmall (parameter 0 HSet.quineAtom))
      (futureBody cyclicSmall growingPositions (parameter 0 HSet.quineAtom))
      (X := ContextualSmallFamilyUniverse.root 0) (cyclicMember 0)
      (ContextualSmallFamilyUniverse.rootArrow (homOfLE (Nat.zero_le (value + 1)))) :=
  ⟨⟨value, Nat.lt_trans (Nat.lt_succ_self value) (Nat.lt_succ_self (value + 1))⟩, rfl⟩

theorem smaller_bound_distinguishes_actual_future {first second : Nat} (less : first < second) :
    futureBranchTree first ≠ futureBranchTree second := by
  intro same
  have nodes : futureBranchNode first = futureBranchNode second :=
    (constructorEquiv cyclicSmall growingPositions (parameter 0 HSet.quineAtom)).injective same
  have branches := ContextualWPolynomialReindexing.node_branches_heq rfl (ContextualSmallFamilyUniverse.root 0)
    (futureBranchNode first) (futureBranchNode second) (heq_of_eq nodes)
  have values := eq_of_heq (ContextualWPolynomialReindexing.branch_app_heq
    (first := ContextualSmallFamilyWPolynomial.signature cyclicSmall growingPositions (w cyclicSmall growingPositions)
      (parameter 0 HSet.quineAtom)) (point := ContextualSmallFamilyUniverse.root 0) rfl (cyclicMember 0) (cyclicMember 0) HEq.rfl
    (futureBranchNode first).2 (futureBranchNode second).2 branches (newFuture second)
    (ContextualSmallFamilyUniverse.rootArrow (homOfLE (Nat.zero_le (second + 1))))
    (ContextualSmallFamilyUniverse.rootArrow (homOfLE (Nat.zero_le (second + 1)))) HEq.rfl
    (probePosition second) (probePosition second) HEq.rfl)
  change (if second ≤ first then zeroLeaf (parameter (second + 1) HSet.quineAtom) else oneStar (second + 1)) =
    (if second ≤ second then zeroLeaf (parameter (second + 1) HSet.quineAtom) else oneStar (second + 1)) at values
  rw [if_neg (Nat.not_le.mpr less), if_pos (Nat.le_refl second)] at values
  exact branching_tree_differs_from_leaf (second + 1) values

theorem infinitely_many_whole_future_trees : Function.Injective futureBranchTree := by
  intro first second same
  rcases Nat.lt_trichotomy first second with less | equal | more
  · exact (smaller_bound_distinguishes_actual_future less same).elim
  · exact equal
  · exact (smaller_bound_distinguishes_actual_future more same.symm).elim

theorem destructor_futureBranch_app (bound : Nat) (future : Future.Objects 0)
    (arrow : ContextualSmallFamilyUniverse.root 0 ⟶ future)
    (position : ContextualWTypes.Position (futureDomain cyclicSmall (parameter 0 HSet.quineAtom))
      (futureBody cyclicSmall growingPositions (parameter 0 HSet.quineAtom))
      (X := ContextualSmallFamilyUniverse.root 0) (cyclicMember 0) arrow) :
    (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree bound)).2.app future arrow position =
      (futureBranchNode bound).2.app future arrow position := by
  have nodeEq := destructor_constructor cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchNode bound)
  have branches := ContextualWPolynomialReindexing.node_branches_heq rfl (ContextualSmallFamilyUniverse.root 0)
    (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree bound))
    (futureBranchNode bound) (heq_of_eq nodeEq)
  exact eq_of_heq (ContextualWPolynomialReindexing.branch_app_heq
    (first := ContextualSmallFamilyWPolynomial.signature cyclicSmall growingPositions (w cyclicSmall growingPositions)
      (parameter 0 HSet.quineAtom)) (point := ContextualSmallFamilyUniverse.root 0) rfl (cyclicMember 0) (cyclicMember 0) HEq.rfl
    (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree bound)).2
    (futureBranchNode bound).2 branches future arrow arrow HEq.rfl position position HEq.rfl)

theorem all_present_branches_agree (first second : Nat)
    (position : ContextualWTypes.Position (futureDomain cyclicSmall (parameter 0 HSet.quineAtom))
      (futureBody cyclicSmall growingPositions (parameter 0 HSet.quineAtom))
      (X := ContextualSmallFamilyUniverse.root 0) (cyclicMember 0) (𝟙 (ContextualSmallFamilyUniverse.root 0))) :
    (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree first)).2.app
      (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position =
    (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree second)).2.app
      (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position := by
  have source := destructor_futureBranch_app first (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position
  have target := destructor_futureBranch_app second (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position
  have zero := congrArg Fin.val (Fin.eq_zero position.val)
  change position.val.val = 0 at zero
  have values : (futureBranchNode first).2.app (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position =
      (futureBranchNode second).2.app (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position := by
    change (if position.val.val ≤ first then zeroLeaf (parameter 0 HSet.quineAtom) else oneStar 0) =
      (if position.val.val ≤ second then zeroLeaf (parameter 0 HSet.quineAtom) else oneStar 0)
    exact (if_pos (zero.symm ▸ Nat.zero_le first)).trans (if_pos (zero.symm ▸ Nat.zero_le second)).symm
  exact source.trans (values.trans target.symm)

theorem present_branches_do_not_determine_W :
    (∀ position, (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree 0)).2.app
      (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position =
      (destructorValue cyclicSmall growingPositions (parameter 0 HSet.quineAtom) (futureBranchTree 1)).2.app
        (ContextualSmallFamilyUniverse.root 0) (𝟙 _) position) ∧ futureBranchTree 0 ≠ futureBranchTree 1 :=
  ⟨all_present_branches_agree 0 1, smaller_bound_distinguishes_actual_future (Nat.zero_lt_succ 0)⟩

def tagFamily : parameters.Elements ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def tagAlgebra : Algebra cyclicSmall growingPositions (target := tagFamily) where
  app _ := TypeCat.ofHom fun node => node.1.2.val
  naturality first second step := by
    rcases first with ⟨first, material⟩
    rcases second with ⟨second, otherMaterial⟩
    rcases step with ⟨arrow, same⟩
    change material = otherMaterial at same
    subst otherMaterial
    let firstPoint := parameter first material
    let secondPoint := parameter second material
    let step : firstPoint ⟶ secondPoint := ⟨arrow, rfl⟩
    apply ConcreteCategory.hom_ext
    intro node
    have labels := ContextualWPolynomialReindexing.node_label_heq
      (ContextualSmallFamilyWPolynomial.signature_prefix cyclicSmall growingPositions tagFamily step).symm
      (ContextualSmallFamilyUniverse.root second)
      (ContextualSmallFamilyWPolynomial.pMap cyclicSmall growingPositions tagFamily step node) _
      (ContextualSmallFamilyWPolynomial.pMap_value cyclicSmall growingPositions tagFamily step node)
    exact congrArg (fun label : cyclicSmall.obj secondPoint => label.2.val) (eq_of_heq labels)

theorem fold_oneStar_tag (stage : Nat) : foldValue cyclicSmall growingPositions tagAlgebra
    (parameter stage HSet.quineAtom) (oneStar stage) = true :=
  ContextualSmallFamilyWInitiality.fold_beta cyclicSmall growingPositions tagAlgebra
    (parameter stage HSet.quineAtom) (starNode (parameter stage HSet.quineAtom) (cyclicMember stage))

noncomputable def changedTree (saved : HSet.{0}) :
    WAt (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions) (pairedPoint saved) :=
  ContextualSmallFamilyWSubstitution.wComparison selectFirst cyclicSmall growingPositions (pairedPoint saved) (oneStar 0)

theorem noninjective_substitution_preserves_fold (saved : HSet.{0}) :
    foldValue (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions)
      (ContextualSmallFamilyWSubstitutionCoherence.substitutedAlgebra selectFirst cyclicSmall growingPositions tagAlgebra)
      (pairedPoint saved) (changedTree saved) = true :=
  (ContextualSmallFamilyWSubstitutionCoherence.fold_substitution selectFirst cyclicSmall growingPositions tagAlgebra
    (pairedPoint saved) (oneStar 0)).symm.trans (fold_oneStar_tag 0)

noncomputable def changedTotal (saved : HSet.{0}) : ContextualSmallFamilyUniverse.TotalAt
    (w (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions)) 0 :=
  ⟨(HSet.quineAtom, saved), changedTree saved⟩

theorem literal_W_classification_retains_forgotten_parameter :
    (ContextualSmallFamilyUniverse.classificationForward
      (w (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions))).app 0
        (changedTotal ∅) ≠
      (ContextualSmallFamilyUniverse.classificationForward
        (w (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions))).app 0
          (changedTotal HSet.quineAtom) := by
  intro same
  have parameters := congrArg (fun receipt : ContextualSmallFamilyUniverse.ClassificationPullback
      (w (domainUnder selectFirst cyclicSmall) (bodyUnder selectFirst cyclicSmall growingPositions)) |>.obj 0 => receipt.val.2.2) same
  exact HSet.empty_ne_quineAtom parameters

theorem everywhere_unary_has_no_tree (point : parameters.Elements) :
    ¬ Nonempty (WAt cyclicSmall (smallUnit (E := cyclicSmall.Elements)) point) := by
  rintro ⟨tree⟩
  have impossible : ∀ (future : Future.Objects point.1)
      (raw : ContextualWReindexing.Raw (signature cyclicSmall (smallUnit (E := cyclicSmall.Elements)) point) future), False := by
    intro future raw
    induction raw with
    | @sup future _label _children ih => exact ih future (𝟙 future) PUnit.unit
  exact impossible _ tree.val

theorem wide_parameter_stays_uncovered {I : Type} (reading : I → parameters.obj 0) :
    ¬ Function.Surjective reading := parameter_object_has_no_small_cover reading

theorem actual_whole_W_decoder :
    ContextualSmallFamilyUniverse.decodedFamily
      (ContextualSmallFamilyUniverse.classifier (w cyclicSmall growingPositions)) = w cyclicSmall growingPositions :=
  ContextualSmallFamilyWSubstitutionCoherence.w_decoder cyclicSmall growingPositions

end Mettapedia.TypeTheory.ContextualSmallFamilyWControls
