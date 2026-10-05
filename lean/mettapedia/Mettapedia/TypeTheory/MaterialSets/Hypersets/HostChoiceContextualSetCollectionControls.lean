import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretationControls

/-!
# Functional images and future-totality controls for internal Collection

An actual natural operation supplies an argument-dependent total relation.
Internal Collection produces its complete future image. The singleton
operation has distinct empty and cyclic outputs. On the infinite stage
site, its image of the late-member set is again late, with a nonempty
material child. A second stable relation is total at the initial present
stage but not at the next future; it has no all-future collecting set.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollectionControls

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality
open HostChoiceContextualSetCollection HostChoiceContextualSetInterpretationControls
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafDescent.Controls

universe u
variable {D : Type u} [Category.{u} D]

def functionalTest (operation : NaturalHom (sets (D := D)) sets) :
    CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product (terminal (E := D))
        (CoveredFuturePowerClassifier.product sets sets)) where
  holds value := operation.app value.1 value.2.2.1 = value.2.2.2
  closed {first second} move available := by
    have childEq : sets.map move.1 first.2.2.1 = second.2.2.1 :=
      congrArg (fun value => value.2.1) move.2
    have witnessEq : sets.map move.1 first.2.2.2 = second.2.2.2 :=
      congrArg (fun value => value.2.2) move.2
    exact (congrArg (operation.app second.1) childEq).symm.trans
      ((operation.naturality move.1 first.2.2.1).symm.trans
        ((congrArg (sets.map move.1) available).trans witnessEq))

theorem functional_total (operation : NaturalHom (sets (D := D)) sets)
    (point : D) (parent : sets.obj point) :
    Total terminal (functionalTest operation) point PUnit.unit parent := by
  intro target _ child _
  exact ⟨operation.app target child, rfl⟩

theorem functional_collection (operation : NaturalHom (sets (D := D)) sets)
    (point : D) (parent : sets.obj point) :
    ∃ collection : sets.obj point,
      ∀ (target : D) (arrow : point ⟶ target) (witness : sets.obj target),
        Member target witness (sets.map arrow collection) ↔
          ∃ child : sets.obj target, Member target child (sets.map arrow parent) ∧
            operation.app target child = witness := by
  obtain ⟨collection, clauses⟩ := internal_strongCollection terminal (functionalTest operation)
    point PUnit.unit parent (functional_total operation point parent)
  refine ⟨collection, ?_⟩
  intro target arrow witness
  constructor
  · intro belongs
    exact (clauses target arrow).2 witness belongs
  · rintro ⟨child, belongs, valueEq⟩
    obtain ⟨other, collected, law⟩ := (clauses target arrow).1 child belongs
    change operation.app target child = other at law
    exact (law.symm.trans valueEq) ▸ collected

theorem identity_collection (point : D) (parent : sets.obj point) :
    ∃ collection : sets.obj point,
      collection = parent ∧
        ∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
          Member target child (sets.map arrow collection) ↔
            Member target child (sets.map arrow parent) := by
  let identity : NaturalHom (sets (D := D)) sets := ⟨fun _ value => value, fun _ _ => rfl⟩
  obtain ⟨collection, image⟩ := functional_collection identity point parent
  have members : ∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
      Member target child (sets.map arrow collection) ↔ Member target child (sets.map arrow parent) := by
    intro target arrow child
    exact (image target arrow child).trans
      ⟨fun ⟨other, belongs, same⟩ => same ▸ belongs, fun belongs => ⟨child, belongs, rfl⟩⟩
  exact ⟨collection, (internal_extensionality point collection parent).mp members, members⟩

theorem singleton_empty_ne_loop (point : D) :
    singletonSet.app point (emptySet.val point) ≠ loopSet.val point := by
  intro same
  have belongs := (member_singleton point (emptySet.val point) (emptySet.val point)).mpr rfl
  rw [same] at belongs
  exact loop_ne_empty point ((loop_member point _).mp belongs)

theorem singleton_empty_ne_empty (point : D) :
    singletonSet.app point (emptySet.val point) ≠ emptySet.val point := by
  intro same
  have belongs := (member_singleton point (emptySet.val point) (emptySet.val point)).mpr rfl
  rw [same] at belongs
  exact member_empty point _ belongs

theorem singleton_cyclic_collection (point : D) :
    ∃ collection : sets.obj point,
      collection = pairSet.app point (singletonSet.app point (emptySet.val point), loopSet.val point) ∧
        ∀ (target : D) (arrow : point ⟶ target) (witness : sets.obj target),
          Member target witness (sets.map arrow collection) ↔
            ∃ child : sets.obj target,
              Member target child (sets.map arrow
                (pairSet.app point (emptySet.val point, loopSet.val point))) ∧
                singletonSet.app target child = witness := by
  obtain ⟨collection, image⟩ := functional_collection singletonSet point
    (pairSet.app point (emptySet.val point, loopSet.val point))
  refine ⟨collection, ?_, image⟩
  apply (internal_extensionality point _ _).mp
  intro target arrow witness
  rw [image target arrow witness]
  have emptyNatural := emptySet.property arrow
  have cyclicNatural := loopSet.property arrow
  have cyclicSingleton : singletonSet.app target (loopSet.val target) = loopSet.val target :=
    congrArg (fun term : (sets (D := D)).sections => term.val target) loop_is_singleton
  have targetMembers := future_pair arrow witness
    (singletonSet.app point (emptySet.val point)) (loopSet.val point)
  rw [singletonSet.naturality arrow (emptySet.val point), emptyNatural, cyclicNatural] at targetMembers
  constructor
  · rintro ⟨child, belongs, valueEq⟩
    have sourceEq := (futureMember_iff arrow child _).mpr belongs
    have pairLaw := future_pair arrow child (emptySet.val point) (loopSet.val point)
    rw [emptyNatural, cyclicNatural] at pairLaw
    rcases pairLaw.mp sourceEq with emptyEq | cyclicEq
    · exact (futureMember_iff arrow witness _).mp
        (targetMembers.mpr (Or.inl ((congrArg (singletonSet.app target) emptyEq).trans valueEq)))
    · exact (futureMember_iff arrow witness _).mp
        (targetMembers.mpr (Or.inr (cyclicSingleton.symm.trans
          ((congrArg (singletonSet.app target) cyclicEq).trans valueEq))))
  · intro belongs
    rcases targetMembers.mp ((futureMember_iff arrow witness _).mpr belongs) with emptyEq | cyclicEq
    · refine ⟨emptySet.val target, ?_, emptyEq⟩
      exact (futureMember_iff arrow _ _).mp
        ((future_pair arrow _ (emptySet.val point) (loopSet.val point)).mpr (Or.inl emptyNatural))
    · refine ⟨loopSet.val target, ?_, cyclicSingleton.trans cyclicEq⟩
      exact (futureMember_iff arrow _ _).mp
        ((future_pair arrow _ (emptySet.val point) (loopSet.val point)).mpr (Or.inr cyclicNatural))

namespace Infinite

abbrev values := sets (D := Stagesᵒᵖ)

def lateSingletonPredicate (point : Stagesᵒᵖ) : Predicate values point where
  holds argument := 1 ≤ stageIndex argument.1.1 ∧
    argument.2 = singletonSet.app argument.1.1 (emptySet.val argument.1.1)
  closed {first second} move available := by
    have same : values.map move.1.1 first.2 = second.2 := move.2
    exact ⟨available.1.trans (growthLe move.1.1), same.symm.trans
      ((congrArg (values.map move.1.1) available.2).trans
        ((singletonSet.naturality move.1.1 (emptySet.val first.1.1)).trans
          (congrArg (singletonSet.app second.1.1) (emptySet.property move.1.1))))⟩

noncomputable def lateSingletonEnumeration (point : Stagesᵒᵖ) : Enumeration (lateSingletonPredicate point) where
  Carrier future := {_receipt : PUnit.{1} // 1 ≤ stageIndex future.1}
  value future _ := singletonSet.app future.1 (emptySet.val future.1)
  covered _ _ := ⟨fun ⟨later, same⟩ => ⟨⟨PUnit.unit, later⟩, same.symm⟩,
    fun ⟨receipt, same⟩ => ⟨receipt.property, same.symm⟩⟩

noncomputable def lateSingletonPower (point : Stagesᵒᵖ) : Power values point :=
  ⟨lateSingletonPredicate point, ⟨lateSingletonEnumeration point⟩⟩

theorem lateSingletonPower_restrict {first second : Stagesᵒᵖ} (arrow : first ⟶ second) :
    restrictPower values arrow (lateSingletonPower first) = lateSingletonPower second := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def lateSingletonSet : values.sections :=
  assemble.mapSection ⟨lateSingletonPower, fun arrow => lateSingletonPower_restrict arrow⟩

theorem lateSingleton_future (point target : Stagesᵒᵖ) (arrow : point ⟶ target)
    (child : values.obj target) :
    FutureMember arrow child (lateSingletonSet.val point) ↔
      1 ≤ stageIndex target ∧ child = singletonSet.app target (emptySet.val target) := by
  change (unfold.app point (assemble.app point (lateSingletonPower point))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem lateSingleton_has_no_present_member (child : values.obj (world 0)) :
    ¬ Member (world 0) child (lateSingletonSet.val (world 0)) := by
  intro available
  exact Nat.not_succ_le_zero 0
    ((lateSingleton_future (world 0) (world 0) (𝟙 _) child).mp available).1

theorem lateSingleton_has_later_nonempty_member :
    FutureMember ContextualMaterialCoalgebraControls.firstAdvance
      (singletonSet.app (world 1) (emptySet.val (world 1))) (lateSingletonSet.val (world 0)) ∧
        singletonSet.app (world 1) (emptySet.val (world 1)) ≠ emptySet.val (world 1) :=
  ⟨(lateSingleton_future _ _ _ _).mpr ⟨Nat.le_refl 1, rfl⟩, singleton_empty_ne_empty (world 1)⟩

theorem lateSingleton_ne_empty : lateSingletonSet.val (world 0) ≠ emptySet.val (world 0) := by
  intro same
  have belongs := lateSingleton_has_later_nonempty_member.1
  rw [same] at belongs
  exact member_empty (world 1) _
    ((emptySet.property ContextualMaterialCoalgebraControls.firstAdvance) ▸
      (futureMember_iff _ _ _).mp belongs)

theorem lateSingleton_ne_late : lateSingletonSet.val (world 0) ≠
    HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val (world 0) := by
  intro same
  have belongs := lateSingleton_has_later_nonempty_member.1
  rw [same] at belongs
  exact singleton_empty_ne_empty (world 1)
    ((HostChoiceContextualSetInterpretationControls.Infinite.late_future _ _ _ _).mp belongs).2

theorem singleton_late_collection (point : Stagesᵒᵖ) :
    ∃ collection : values.obj point,
      collection = lateSingletonSet.val point ∧
        ∀ (target : Stagesᵒᵖ) (arrow : point ⟶ target) (witness : values.obj target),
          Member target witness (values.map arrow collection) ↔
            ∃ child : values.obj target,
              Member target child (values.map arrow
                (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val point)) ∧
                singletonSet.app target child = witness := by
  obtain ⟨collection, image⟩ := functional_collection singletonSet point
    (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val point)
  refine ⟨collection, ?_, image⟩
  apply (internal_extensionality point _ _).mp
  intro target arrow witness
  rw [image target arrow witness]
  have targetLaw := (futureMember_iff arrow witness _).symm.trans (lateSingleton_future point target arrow witness)
  constructor
  · rintro ⟨child, belongs, valueEq⟩
    have childLaw := (HostChoiceContextualSetInterpretationControls.Infinite.late_future point target arrow child).mp
      ((futureMember_iff arrow child _).mpr belongs)
    exact targetLaw.mpr ⟨childLaw.1, valueEq.symm.trans
      (congrArg (singletonSet.app target) childLaw.2)⟩
  · intro belongs
    obtain ⟨later, valueEq⟩ := targetLaw.mp belongs
    refine ⟨emptySet.val target, ?_, valueEq.symm⟩
    exact (futureMember_iff arrow _ _).mp
      ((HostChoiceContextualSetInterpretationControls.Infinite.late_future point target arrow _).mpr ⟨later, rfl⟩)

def tooLateTest : CoveredFuturePowerClassifier.StablePredicate
    (CoveredFuturePowerClassifier.product (terminal (E := Stagesᵒᵖ))
      (CoveredFuturePowerClassifier.product values values)) where
  holds value := 2 ≤ stageIndex value.1
  closed move available := available.trans (growthLe move.1)

theorem present_total :
    ∀ child : values.obj (world 0),
      Member (world 0) child (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val (world 0)) →
        ∃ witness : values.obj (world 0), tooLateTest.holds ⟨world 0, (PUnit.unit, (child, witness))⟩ :=
  fun child belongs => (HostChoiceContextualSetInterpretationControls.Infinite.late_has_no_present_member child belongs).elim

theorem future_total_fails :
    ¬ Total terminal tooLateTest (world 0) PUnit.unit
      (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val (world 0)) := by
  intro total
  obtain ⟨_, law⟩ := total (world 1) ContextualMaterialCoalgebraControls.firstAdvance (emptySet.val (world 1))
    ((futureMember_iff _ _ _).mp HostChoiceContextualSetInterpretationControls.Infinite.late_has_later_member)
  exact Nat.not_succ_le_self 1 law

theorem no_all_future_collector :
    ¬ ∃ collection : values.obj (world 0),
      ∀ (target : Stagesᵒᵖ) (arrow : world 0 ⟶ target) (child : values.obj target),
        Member target child (values.map arrow
          (HostChoiceContextualSetInterpretationControls.Infinite.lateSet.val (world 0))) →
          ∃ witness : values.obj target, Member target witness (values.map arrow collection) ∧
            tooLateTest.holds ⟨target, (PUnit.unit, (child, witness))⟩ := by
  rintro ⟨_, covers⟩
  obtain ⟨_, _, law⟩ := covers (world 1) ContextualMaterialCoalgebraControls.firstAdvance (emptySet.val (world 1))
    ((futureMember_iff _ _ _).mp HostChoiceContextualSetInterpretationControls.Infinite.late_has_later_member)
  exact Nat.not_succ_le_self 1 law

end Infinite

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetCollectionControls
