import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCoalgebraFinality
import Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier
import Mettapedia.TypeTheory.MaterialSets.Hypersets.CoveredFuturePowerLogic

/-!
# Internal membership in the final covered-power coalgebra

The context and child-receipt bound is `u`; set fibres inhabit `Type (u+1)`.
Membership is read at the identity future from the actual final structure.
Its transport and extensionality retain every future context and actual arrow.
The inverse structure constructs sets from small-covered future predicates.

Graph decoration applies to stable relations with original-bound small
projection fibres, including graphs with wider node carriers. External host
Choice is inherited from full covered-coalgebra finality and small-relation
classification. No unrestricted powerset or internal Choice is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation

open _root_.CategoryTheory CoveredFuturePowerFamilies CoveredFuturePowerFunctor
open Mettapedia.TypeTheory.ContextualWitnessCover
open PowerClassPresheafBaseChange

universe u v
variable {D : Type u} [Category.{u} D]

namespace Finality

abbrev sets : D ⥤ Type (u+1) :=
  (HostChoiceContextualCoalgebraFinality.finalCoalgebra.{u,0} (D := D)).V.interpretation

abbrev unfold : NaturalHom (sets (D := D)) (family (sets (D := D))) :=
  (HostChoiceContextualCoalgebraFinality.finalCoalgebra.{u,0} (D := D)).str

noncomputable def assemble : NaturalHom (family (sets (D := D))) (sets (D := D)) :=
  HostChoiceContextualCoalgebraFinality.structureInverse.{u,0}

theorem unfold_assemble (point : D) (predicate : Power (sets (D := D)) point) :
    unfold.app point (assemble.app point predicate) = predicate := by
  exact congrArg (fun operation : NaturalHom (family (sets (D := D)))
    (family (sets (D := D))) => operation.app point predicate)
      (HostChoiceContextualCoalgebraFinality.structureInverse_structure.{u,0} (D := D))

theorem assemble_unfold (point : D) (value : (sets (D := D)).obj point) :
    assemble.app point (unfold.app point value) = value := by
  exact congrArg (fun operation : NaturalHom (sets (D := D))
    (sets (D := D)) => operation.app point value)
      (HostChoiceContextualCoalgebraFinality.structure_structureInverse.{u,0} (D := D))

theorem assemble_injective (point : D) : Function.Injective (assemble.app point) := by
  intro first second same
  exact (unfold_assemble point first).symm.trans
    ((congrArg (unfold.app point) same).trans (unfold_assemble point second))

end Finality

open Finality

def Member (point : D) (child parent : (sets (D := D)).obj point) : Prop :=
  (unfold.app point parent).val.holds (current sets point child)

def FutureMember {point target : D} (arrow : point ⟶ target)
    (child : (sets (D := D)).obj target) (parent : (sets (D := D)).obj point) : Prop :=
  (unfold.app point parent).val.holds ⟨⟨target, arrow⟩, child⟩

theorem futureMember_iff {point target : D} (arrow : point ⟶ target)
    (child : (sets (D := D)).obj target) (parent : (sets (D := D)).obj point) :
    FutureMember arrow child parent ↔ Member target child (sets.map arrow parent) :=
  CoveredFuturePowerClassifier.classified_future sets sets unfold point parent
    ⟨⟨target, arrow⟩, child⟩

theorem member_transport {point target : D} (arrow : point ⟶ target)
    {child parent : (sets (D := D)).obj point} (available : Member point child parent) :
    Member target (sets.map arrow child) (sets.map arrow parent) := by
  apply (futureMember_iff arrow _ parent).mp
  exact (unfold.app point parent).val.closed
    (show current sets point child ⟶
      (⟨⟨target, arrow⟩, sets.map arrow child⟩ : Arguments sets point) from
        ⟨⟨arrow, Category.id_comp arrow⟩, rfl⟩) available

def membershipRelation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation
    (sets (D := D)) (sets (D := D)) :=
  Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifiedRelation sets sets unfold

theorem membershipRelation_truth (point : D) (parent child : (sets (D := D)).obj point) :
    membershipRelation.predicate.holds ⟨point, (parent, child)⟩ ↔ Member point child parent :=
  Iff.rfl

/-- All future membership, rather than only present membership, reflects identity. -/
theorem internal_extensionality (point : D) (first second : (sets (D := D)).obj point) :
    (∀ (target : D) (arrow : point ⟶ target) (child : sets.obj target),
      Member target child (sets.map arrow first) ↔
        Member target child (sets.map arrow second)) ↔ first = second := by
  constructor
  · intro same
    have power : unfold.app point first = unfold.app point second := by
      apply Subtype.ext
      apply Predicate.ext
      rintro ⟨⟨target, arrow⟩, child⟩
      exact (futureMember_iff arrow child first).trans
        ((same target arrow child).trans (futureMember_iff arrow child second).symm)
    exact (assemble_unfold point first).symm.trans
      ((congrArg (assemble.app point) power).trans (assemble_unfold point second))
  · rintro rfl _ _ _
    exact Iff.rfl

/-- Graph nodes may be wider; only the relation's projection is receipt-small. -/
noncomputable def decorate (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes) :
    NaturalHom nodes (sets (D := D)) :=
  (HostChoiceContextualCoalgebraFinality.readout
    (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier nodes nodes relation)).comp
      (HostChoiceContextualCoalgebraFinality.raise.{u,0,u+1}
        (ContextualSmallCoalgebraGenerators.quotient (D := D)))

theorem decorate_square (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes) :
    (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier nodes nodes relation).comp
      (imageHom (decorate nodes relation)) = (decorate nodes relation).comp unfold :=
  ContextualSmallCoalgebraComparisons.compose_square _ _ _ _ _
    (HostChoiceContextualCoalgebraFinality.readout_square _)
    (HostChoiceContextualCoalgebraFinality.raise_square.{u,0,u+1} _)

theorem graph_future (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes)
    (point target : D) (arrow : point ⟶ target) (node : nodes.obj point)
    (child : sets.obj target) :
    FutureMember arrow child ((decorate nodes relation).app point node) ↔
      ∃ other : nodes.obj target, (decorate nodes relation).app target other = child ∧
        relation.predicate.holds ⟨target, (nodes.map arrow node, other)⟩ := by
  exact (ContextualCoalgebraBisimulation.coalgebra_map_truth _ (decorate nodes relation)
    unfold (decorate_square nodes relation) point node ⟨target, arrow⟩ child).trans
      ⟨fun ⟨other, same, available⟩ => ⟨other, same,
        (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier_future
          nodes nodes relation point node ⟨⟨target, arrow⟩, other⟩).mp available⟩,
        fun ⟨other, same, available⟩ => ⟨other, same,
        (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier_future
          nodes nodes relation point node ⟨⟨target, arrow⟩, other⟩).mpr available⟩⟩

theorem graph_current (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes)
    (point : D) (node : nodes.obj point) (child : sets.obj point) :
    Member point child ((decorate nodes relation).app point node) ↔
      ∃ other : nodes.obj point, (decorate nodes relation).app point other = child ∧
        relation.predicate.holds ⟨point, (node, other)⟩ := by
  have result := graph_future nodes relation point point (𝟙 point) node child
  rw [nodes.map_id] at result
  exact result

theorem graph_decoration_unique (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes) :
    ∃! operation : NaturalHom nodes (sets (D := D)),
      (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier nodes nodes relation).comp
        (imageHom operation) = operation.comp unfold := by
  refine ⟨decorate nodes relation, decorate_square nodes relation, ?_⟩
  intro candidate square
  exact HostChoiceContextualCoalgebraFinality.maps_equal_into_lift _ _
    ContextualSmallCoalgebraGenerators.quotient_separated candidate (decorate nodes relation)
      square (decorate_square nodes relation)

theorem graph_equations_iff_square (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes)
    (operation : NaturalHom nodes (sets (D := D))) :
    (∀ (point target : D) (arrow : point ⟶ target) (node : nodes.obj point) (child : sets.obj target),
      FutureMember arrow child (operation.app point node) ↔
        ∃ other : nodes.obj target, operation.app target other = child ∧
          relation.predicate.holds ⟨target, (nodes.map arrow node, other)⟩) ↔
      (Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier nodes nodes relation).comp
        (imageHom operation) = operation.comp unfold := by
  constructor
  · intro equations
    apply NaturalHom.ext
    intro point node
    apply Subtype.ext
    apply Predicate.ext
    rintro ⟨⟨target, arrow⟩, child⟩
    change (∃ other, operation.app target other = child ∧
      ((Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.classifier nodes nodes relation).app
        point node).val.holds ⟨⟨target, arrow⟩, other⟩) ↔ _
    exact (show _ ↔ ∃ other : nodes.obj target, operation.app target other = child ∧
        relation.predicate.holds ⟨target, (nodes.map arrow node, other)⟩ from Iff.rfl).trans
      (equations point target arrow node child).symm
  · intro square point target arrow node child
    exact ContextualCoalgebraBisimulation.coalgebra_map_truth _ operation unfold square
      point node ⟨target, arrow⟩ child

/-- Every stable small graph has a unique contextual decoration into sets. -/
theorem graph_antiFoundation (nodes : D ⥤ Type v)
    (relation : Mettapedia.TypeTheory.HostChoiceContextualSmallMapClassifier.SmallRelation nodes nodes) :
    ∃! operation : NaturalHom nodes (sets (D := D)),
      ∀ (point target : D) (arrow : point ⟶ target) (node : nodes.obj point) (child : sets.obj target),
        FutureMember arrow child (operation.app point node) ↔
          ∃ other : nodes.obj target, operation.app target other = child ∧
            relation.predicate.holds ⟨target, (nodes.map arrow node, other)⟩ := by
  obtain ⟨operation, square, unique⟩ := graph_decoration_unique nodes relation
  refine ⟨operation, (graph_equations_iff_square nodes relation operation).mpr square, ?_⟩
  intro candidate equations
  exact unique candidate ((graph_equations_iff_square nodes relation candidate).mp equations)

def emptyPredicate (point : D) : Predicate (sets (D := D)) point where
  holds _ := False
  closed _ available := available

def emptyEnumeration (point : D) : Enumeration (emptyPredicate point) where
  Carrier _ := PEmpty.{u+1}
  value _ := PEmpty.elim
  covered _ _ := ⟨False.elim, fun ⟨code, _⟩ => PEmpty.elim code⟩

def emptyPower (point : D) : Power (sets (D := D)) point :=
  ⟨emptyPredicate point, ⟨emptyEnumeration point⟩⟩

theorem emptyPower_restrict {point target : D} (arrow : point ⟶ target) :
    restrictPower sets arrow (emptyPower point) = emptyPower target := by
  apply Subtype.ext
  apply Predicate.ext
  intro _
  exact Iff.rfl

noncomputable def emptySet : (sets (D := D)).sections :=
  assemble.mapSection ⟨emptyPower, fun arrow => emptyPower_restrict arrow⟩

theorem member_empty (point : D) (child : sets.obj point) :
    ¬ Member point child (emptySet.val point) := by
  intro available
  change (unfold.app point (assemble.app point (emptyPower point))).val.holds _ at available
  rw [unfold_assemble] at available
  exact available

noncomputable def singletonSet : NaturalHom (sets (D := D)) (sets (D := D)) :=
  (unitHom sets).comp assemble

theorem future_singleton {point target : D} (arrow : point ⟶ target)
    (child : sets.obj target) (value : sets.obj point) :
    FutureMember arrow child (singletonSet.app point value) ↔ sets.map arrow value = child := by
  change (unfold.app point (assemble.app point (singletonPower sets point value))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem member_singleton (point : D) (child value : sets.obj point) :
    Member point child (singletonSet.app point value) ↔ value = child := by
  have result := future_singleton (𝟙 point) child value
  rw [sets.map_id] at result
  exact result

def pairPredicate (point : D) (first second : sets.obj point) : Predicate sets point where
  holds argument := (singleton sets point first).holds argument ∨
    (singleton sets point second).holds argument
  closed move available := available.elim
    (fun left => Or.inl ((singleton sets point first).closed move left))
    (fun right => Or.inr ((singleton sets point second).closed move right))

def pairEnumeration (point : D) (first second : sets.obj point) :
    Enumeration (pairPredicate point first second) where
  Carrier _ := ULift.{u} Bool
  value future code := if code.down then sets.map future.2 first else sets.map future.2 second
  covered future child := by
    constructor
    · rintro (left | right)
      · exact ⟨ULift.up true, left⟩
      · exact ⟨ULift.up false, right⟩
    · rintro ⟨⟨code⟩, same⟩
      cases code with
      | false => exact Or.inr same
      | true => exact Or.inl same

def pairPower (point : D) (first second : sets.obj point) : Power sets point :=
  ⟨pairPredicate point first second, ⟨pairEnumeration point first second⟩⟩

theorem pairPower_restrict {point target : D} (arrow : point ⟶ target)
    (first second : sets.obj point) : restrictPower sets arrow (pairPower point first second) =
      pairPower target (sets.map arrow first) (sets.map arrow second) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  change (sets.map (arrow ≫ argument.1.2) first = argument.2 ∨
    sets.map (arrow ≫ argument.1.2) second = argument.2) ↔ _
  rw [sets.map_comp]
  exact Iff.rfl

def pairPowerHom : NaturalHom (CoveredFuturePowerClassifier.product (sets (D := D)) sets)
    (family sets) where
  app point value := pairPower point value.1 value.2
  naturality arrow value := pairPower_restrict arrow value.1 value.2

noncomputable def pairSet : NaturalHom
    (CoveredFuturePowerClassifier.product (sets (D := D)) sets) sets :=
  pairPowerHom.comp assemble

theorem future_pair {point target : D} (arrow : point ⟶ target)
    (child : sets.obj target) (first second : sets.obj point) :
    FutureMember arrow child (pairSet.app point (first, second)) ↔
      sets.map arrow first = child ∨ sets.map arrow second = child := by
  change (unfold.app point (assemble.app point (pairPower point first second))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem member_pair (point : D) (child first second : sets.obj point) :
    Member point child (pairSet.app point (first, second)) ↔ first = child ∨ second = child := by
  have result := future_pair (𝟙 point) child first second
  rw [sets.map_id] at result
  exact result

/-- Both the outer and inner child receipts retain the original bound. -/
def unionPredicate (point : D) (parent : sets.obj point) : Predicate sets point where
  holds argument := ∃ middle : sets.obj argument.1.1,
    (unfold.app point parent).val.holds ⟨argument.1, middle⟩ ∧
      Member argument.1.1 argument.2 middle
  closed {first second} move available := by
    obtain ⟨middle, outer, inner⟩ := available
    refine ⟨sets.map move.1.1 middle, ?_, ?_⟩
    · exact (unfold.app point parent).val.closed
        (first := ⟨first.1, middle⟩)
        (second := ⟨second.1, sets.map move.1.1 middle⟩)
        ⟨move.1, rfl⟩ outer
    · have transported := member_transport move.1.1 inner
      change Member second.1.1 (sets.map move.1.1 first.2) (sets.map move.1.1 middle) at transported
      have valueEq : sets.map move.1.1 first.2 = second.2 := move.2
      exact (congrArg (fun value => Member second.1.1 value (sets.map move.1.1 middle)) valueEq) ▸ transported

noncomputable def unionEnumeration (point : D) (parent : sets.obj point) :
    Enumeration (unionPredicate point parent) where
  Carrier future := Σ outer :
      (HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).Carrier future,
    (HostChoiceContextualCoalgebraFinality.enumerations unfold future.1
      ((HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).value future outer)).Carrier
        ⟨future.1, 𝟙 future.1⟩
  value future code := (HostChoiceContextualCoalgebraFinality.enumerations unfold future.1
    ((HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).value future code.1)).value
      ⟨future.1, 𝟙 future.1⟩ code.2
  covered future child := by
    constructor
    · rintro ⟨middle, outer, inner⟩
      obtain ⟨outerCode, same⟩ :=
        (HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).covered future middle |>.mp outer
      subst middle
      obtain ⟨innerCode, innerSame⟩ :=
        (HostChoiceContextualCoalgebraFinality.enumerations unfold future.1
          ((HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).value future outerCode)).covered
          ⟨future.1, 𝟙 future.1⟩ child |>.mp inner
      exact ⟨⟨outerCode, innerCode⟩, innerSame⟩
    · rintro ⟨⟨outerCode, innerCode⟩, same⟩
      refine ⟨(HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).value future outerCode,
        ?_, ?_⟩
      · exact (HostChoiceContextualCoalgebraFinality.enumerations unfold point parent).covered future _ |>.mpr
          ⟨outerCode, rfl⟩
      · exact (HostChoiceContextualCoalgebraFinality.enumerations unfold future.1 _).covered
          ⟨future.1, 𝟙 future.1⟩ child |>.mpr ⟨innerCode, same⟩

noncomputable def unionPower (point : D) (parent : sets.obj point) : Power sets point :=
  ⟨unionPredicate point parent, ⟨unionEnumeration point parent⟩⟩

theorem unionPower_restrict {point target : D} (arrow : point ⟶ target)
    (parent : sets.obj point) : restrictPower sets arrow (unionPower point parent) =
      unionPower target (sets.map arrow parent) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  change (∃ middle, (unfold.app point parent).val.holds
    ⟨⟨argument.1.1, arrow ≫ argument.1.2⟩, middle⟩ ∧ Member _ argument.2 middle) ↔
      ∃ middle, (unfold.app target (sets.map arrow parent)).val.holds
        ⟨argument.1, middle⟩ ∧ Member _ argument.2 middle
  have same := unfold.naturality arrow parent
  constructor
  · rintro ⟨middle, outer, inner⟩
    refine ⟨middle, ?_, inner⟩
    exact (congrArg (fun power : Power sets target =>
      power.val.holds ⟨argument.1, middle⟩) same) ▸ outer
  · rintro ⟨middle, outer, inner⟩
    refine ⟨middle, ?_, inner⟩
    exact (congrArg (fun power : Power sets target =>
      power.val.holds ⟨argument.1, middle⟩) same).symm ▸ outer

noncomputable def unionPowerHom : NaturalHom (sets (D := D)) (family sets) where
  app := unionPower
  naturality := unionPower_restrict

noncomputable def unionSet : NaturalHom (sets (D := D)) sets := unionPowerHom.comp assemble

theorem future_union {point target : D} (arrow : point ⟶ target)
    (child : sets.obj target) (parent : sets.obj point) :
    FutureMember arrow child (unionSet.app point parent) ↔
      ∃ middle : sets.obj target, FutureMember arrow middle parent ∧ Member target child middle := by
  change (unfold.app point (assemble.app point (unionPower point parent))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem member_union (point : D) (child parent : sets.obj point) :
    Member point child (unionSet.app point parent) ↔
      ∃ middle : sets.obj point, Member point middle parent ∧ Member point child middle :=
  future_union (𝟙 point) child parent

noncomputable def separationPower (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D))))
    (point : D) (parameter : parameters.obj point) (parent : sets.obj point) : Power sets point :=
  CoveredFuturePowerLogic.separatePower (unfold.app point parent)
    (CoveredFuturePowerClassifier.relationPredicate parameters sets test point parameter)

theorem separationPower_restrict (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D))))
    {point target : D} (arrow : point ⟶ target)
    (parameter : parameters.obj point) (parent : sets.obj point) :
    restrictPower sets arrow (separationPower parameters test point parameter parent) =
      separationPower parameters test target (parameters.map arrow parameter) (sets.map arrow parent) := by
  apply Subtype.ext
  apply Predicate.ext
  intro argument
  have parentEq := congrArg (fun power : Power sets target => power.val.holds argument)
    (unfold.naturality arrow parent)
  change ((unfold.app point parent).val.holds
    ⟨⟨argument.1.1, arrow ≫ argument.1.2⟩, argument.2⟩ ∧
    test.holds ⟨argument.1.1, (parameters.map (arrow ≫ argument.1.2) parameter, argument.2)⟩) ↔ _
  rw [parameters.map_comp]
  exact and_congr (iff_of_eq parentEq) Iff.rfl

noncomputable def separationPowerHom (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D)))) :
    NaturalHom (CoveredFuturePowerClassifier.product parameters sets) (family sets) where
  app point value := separationPower parameters test point value.1 value.2
  naturality arrow value := separationPower_restrict parameters test arrow value.1 value.2

/-- Full stable proposition-valued separation filters the actual small receipts. -/
noncomputable def separationSet (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D)))) :
    NaturalHom (CoveredFuturePowerClassifier.product parameters sets) sets :=
  (separationPowerHom parameters test).comp assemble

theorem future_separation (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D))))
    {point target : D} (arrow : point ⟶ target)
    (parameter : parameters.obj point) (parent : sets.obj point) (child : sets.obj target) :
    FutureMember arrow child ((separationSet parameters test).app point (parameter, parent)) ↔
      FutureMember arrow child parent ∧ test.holds ⟨target, (parameters.map arrow parameter, child)⟩ := by
  change (unfold.app point (assemble.app point
    (separationPower parameters test point parameter parent))).val.holds _ ↔ _
  rw [unfold_assemble]
  exact Iff.rfl

theorem member_separation (parameters : D ⥤ Type v)
    (test : CoveredFuturePowerClassifier.StablePredicate
      (CoveredFuturePowerClassifier.product parameters (sets (D := D))))
    (point : D) (parameter : parameters.obj point) (parent child : sets.obj point) :
    Member point child ((separationSet parameters test).app point (parameter, parent)) ↔
      Member point child parent ∧ test.holds ⟨point, (parameter, child)⟩ := by
  have result := future_separation parameters test (𝟙 point) parameter parent child
  rw [parameters.map_id] at result
  exact result

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInterpretation
