import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialCoalgebraControls

/-!
# Cyclic and infinite-context controls for internal membership

A one-node loop has its unique contextual decoration. Empty and cyclic
sets are distinct, and pairing and union retain the cyclic child. On the
infinite advancing stage site, a set has no present members at stage zero
but acquires the empty set as a member later. This rules out reflection of
identity from present child subsets alone. These controls use the optional
external host-Choice final coalgebra, rather than constant hyperset membership.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafDescent.Controls

universe u
variable {D : Type u} [Category.{u} D]

abbrev loopNodes := terminal (E := D)

def loopRelation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation
    (loopNodes (D := D)) loopNodes :=
  Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifiedRelation loopNodes loopNodes
    (unitHom loopNodes)

noncomputable def loopSet : (sets (D := D)).sections :=
  (decorate loopNodes loopRelation).mapSection terminalSection

theorem loop_future {point target : D} (arrow : point ⟶ target) (child : sets.obj target) :
    FutureMember arrow child (loopSet.val point) ↔ loopSet.val target = child := by
  have result := graph_future loopNodes loopRelation point target arrow PUnit.unit child
  constructor
  · intro available
    obtain ⟨other, same, _⟩ := result.mp available
    cases other
    exact same
  · intro same
    exact result.mpr ⟨PUnit.unit, same, rfl⟩

theorem loop_member (point : D) (child : sets.obj point) :
    Member point child (loopSet.val point) ↔ loopSet.val point = child :=
  loop_future (𝟙 point) child

theorem loop_self_member (point : D) : Member point (loopSet.val point) (loopSet.val point) :=
  (loop_member point _).mpr rfl

theorem loop_ne_empty (point : D) : loopSet.val point ≠ emptySet.val point := by
  intro same
  have available := loop_self_member point
  rw [same] at available
  exact member_empty point _ available

theorem loop_is_singleton : (singletonSet (D := D)).mapSection loopSet = loopSet := by
  apply Subtype.ext
  funext point
  apply (internal_extensionality point _ _).mp
  intro target arrow child
  have term := loopSet.property arrow
  change Member target child (sets.map arrow (singletonSet.app point (loopSet.val point))) ↔ _
  rw [singletonSet.naturality arrow (loopSet.val point), term]
  exact (member_singleton target child _).trans (loop_member target child).symm

theorem pair_cyclic_member (point : D) :
    Member point (loopSet.val point) (pairSet.app point (emptySet.val point, loopSet.val point)) :=
  (member_pair point _ _ _).mpr (Or.inr rfl)

theorem union_cyclic_member (point : D) :
    Member point (loopSet.val point)
      (unionSet.app point (pairSet.app point (emptySet.val point, loopSet.val point))) :=
  (member_union point _ _).mpr ⟨loopSet.val point, pair_cyclic_member point, loop_self_member point⟩

def cyclicTest : CoveredFuturePowerClassifier.StablePredicate
    (CoveredFuturePowerClassifier.product (loopNodes (D := D)) sets) where
  holds value := value.2.2 = loopSet.val value.1
  closed {first second} move available := by
    have valueEq : sets.map move.1 first.2.2 = second.2.2 := congrArg Prod.snd move.2
    exact valueEq.symm.trans ((congrArg (sets.map move.1) available).trans (loopSet.property move.1))

theorem separation_preserves_cyclic (point : D) :
    Member point (loopSet.val point)
      ((separationSet loopNodes cyclicTest).app point
        (PUnit.unit, pairSet.app point (emptySet.val point, loopSet.val point))) :=
  (member_separation loopNodes cyclicTest point _ _ _).mpr ⟨pair_cyclic_member point, rfl⟩

theorem separation_excludes_empty (point : D) :
    ¬ Member point (emptySet.val point)
      ((separationSet loopNodes cyclicTest).app point
        (PUnit.unit, pairSet.app point (emptySet.val point, loopSet.val point))) := by
  intro belongs
  exact loop_ne_empty point ((member_separation loopNodes cyclicTest point _ _ _).mp belongs).2.symm

theorem cyclic_not_natural (point : D) :
    ¬ Member point (loopSet.val point) (HostChoiceContextualSetInfinity.naturals.val point) := by
  intro belongs
  obtain ⟨number, same⟩ := (HostChoiceContextualSetInfinity.member_naturals point _).mp belongs
  have notSelf := HostChoiceContextualSetInfinity.ordinal_not_self_member point number
  rw [same] at notSelf
  exact notSelf (loop_self_member point)

namespace Infinite

abbrev values := sets (D := Stagesᵒᵖ)

def latePredicate (point : Stagesᵒᵖ) : Predicate values point where
  holds argument := 1 ≤ stageIndex argument.1.1 ∧ argument.2 = emptySet.val argument.1.1
  closed {first second} move available := by
    have same : values.map move.1.1 first.2 = second.2 := move.2
    have emptyNatural := emptySet.property move.1.1
    refine ⟨available.1.trans (growthLe move.1.1), ?_⟩
    exact same.symm.trans ((congrArg (values.map move.1.1) available.2).trans emptyNatural)

noncomputable def lateEnumeration (point : Stagesᵒᵖ) : Enumeration (latePredicate point) where
  Carrier future := {_receipt : PUnit.{1} // 1 ≤ stageIndex future.1}
  value future _ := emptySet.val future.1
  covered _ _ := ⟨fun ⟨later, same⟩ => ⟨⟨PUnit.unit, later⟩, same.symm⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.property, same.symm⟩⟩

noncomputable def latePower (point : Stagesᵒᵖ) : Power values point :=
  ⟨latePredicate point, ⟨lateEnumeration point⟩⟩

theorem latePower_restrict {first second : Stagesᵒᵖ} (arrow : first ⟶ second) :
    restrictPower values arrow (latePower first) = latePower second := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def lateSet : values.sections :=
  assemble.mapSection ⟨latePower, fun arrow => latePower_restrict arrow⟩

theorem late_future (point target : Stagesᵒᵖ) (arrow : point ⟶ target) (child : values.obj target) :
    FutureMember arrow child (lateSet.val point) ↔
      1 ≤ stageIndex target ∧ child = emptySet.val target := by
  change (unfold.app point (assemble.app point (latePower point))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem late_has_no_present_member (child : values.obj (world 0)) :
    ¬ Member (world 0) child (lateSet.val (world 0)) := by
  intro available
  have later := ((late_future (world 0) (world 0) (𝟙 _) child).mp available).1
  exact Nat.not_succ_le_zero 0 later

theorem late_has_later_member :
    FutureMember ContextualMaterialCoalgebraControls.firstAdvance
      (emptySet.val (world 1)) (lateSet.val (world 0)) :=
  (late_future _ _ _ _).mpr ⟨Nat.le_refl 1, rfl⟩

theorem present_members_equal :
    ∀ child : values.obj (world 0),
      Member (world 0) child (lateSet.val (world 0)) ↔
        Member (world 0) child (emptySet.val (world 0)) :=
  fun child => ⟨fun available => (late_has_no_present_member child available).elim,
    fun available => (member_empty (world 0) child available).elim⟩

theorem late_ne_empty : lateSet.val (world 0) ≠ emptySet.val (world 0) := by
  intro same
  have available := late_has_later_member
  rw [same] at available
  have emptyNatural := emptySet.property ContextualMaterialCoalgebraControls.firstAdvance
  exact member_empty (world 1) _
    (emptyNatural ▸ (futureMember_iff _ _ _).mp available)

theorem present_extensionality_fails :
    ¬ (∀ first second : values.obj (world 0),
      (∀ child, Member (world 0) child first ↔ Member (world 0) child second) → first = second) :=
  fun reflection => late_ne_empty (reflection _ _ present_members_equal)

theorem arbitrarily_late_empty_member (stage : ℕ) :
    Member (world (stage+1)) (emptySet.val (world (stage+1))) (lateSet.val (world (stage+1))) :=
  (late_future _ _ (𝟙 _) _).mpr ⟨Nat.succ_le_succ (Nat.zero_le stage), rfl⟩

theorem late_self_membership_fails (stage : ℕ) :
    ¬ Member (world (stage+1)) (lateSet.val (world (stage+1))) (lateSet.val (world (stage+1))) := by
  intro available
  have empty : lateSet.val (world (stage+1)) = emptySet.val (world (stage+1)) :=
    ((late_future _ _ (𝟙 _) _).mp available).2
  have child := arbitrarily_late_empty_member stage
  rw [empty] at child
  exact member_empty _ _ child

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls
