import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraComparisons
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UniverseLift

/-!
# A constructed material carrier for all small contextual coalgebras

Every small coded state has an explicitly constructed graph at its original
bound. The collection of all codes is one universe larger. Lifting these
graphs constructs a collecting graph at that raised bound, with no selected
presentation or inverse to the raw behavioral quotient.

Context transport ranges over every coded representative of the input
material member. Their target readings agree by contextual bisimulation.
The row is proved to be a singleton before its union computes the target
value. This supplies actual member maps and their functor laws.

The material carrier lies in `HSet.{u + 1}` and its actual member subtype in
`Type (u + 2)`. Full occurrence-fibre predicates construct a class face in
`Type (u + 1)`, with an explicit member decoder and inverse. The original
small context and its actual arrows are retained.
The full proposition-valued filters, range and union at the raised graph
bound are part of this construction. Same-level Collection is not asserted.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCarrier

open _root_.CategoryTheory PowerClassPresheafBaseChange
open ContextualSmallCoalgebraGenerators
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization (pullbackFirst pullbackSecond)

universe u
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))

def readValue (point : D) (argument : (coproduct (D := D)).obj point) : HSet.{u} :=
  ContextualCoalgebraMaterialReadout.value argument.1.coalgebra worlds arrows ⟨point, argument.2⟩

def readGraph (point : D) (argument : (coproduct (D := D)).obj point) : AccessiblePointedGraph.{u} :=
  ContextualCoalgebraMaterialReadout.valueGraph argument.1.coalgebra worlds arrows ⟨point, argument.2⟩

theorem mk_readGraph (point : D) (argument : (coproduct (D := D)).obj point) :
    HSet.mk (readGraph worlds arrows point argument) = readValue worlds arrows point argument := rfl

theorem readValue_contexts_eq {first second : D}
    (left : (coproduct (D := D)).obj first) (right : (coproduct (D := D)).obj second)
    (same : readValue worlds arrows first left = readValue worlds arrows second right) : first = second := by
  obtain ⟨relation, bisimulation, related⟩ :=
    (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows).labelledBisimilar_of_decorate_eq
      (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows) same
  obtain ⟨label, matching, matched, readings, _⟩ :=
    (bisimulation related).1 (.context first first (𝟙 first))
      ⟨first, left.1.carrier.map (𝟙 first) left.2⟩
      (ContextualCoalgebraLabelledGraph.context_step left.1.coalgebra (𝟙 first) left.2)
  have labels := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective readings
  cases labels
  exact (ContextualCoalgebraLabelledGraph.step_source right.1.coalgebra matched).symm

theorem readValue_matching (left right : Code D) {point : D}
    {first : left.carrier.obj point} {second : right.carrier.obj point}
    (same : readValue worlds arrows point ⟨left, first⟩ = readValue worlds arrows point ⟨right, second⟩)
    (label : ContextualCoalgebraLabelledGraph.Label D)
    (next : ContextualCoalgebraLabelledGraph.State left.carrier)
    (step : ContextualCoalgebraLabelledGraph.Step left.coalgebra ⟨point, first⟩ label next) :
    ∃ matching, ContextualCoalgebraLabelledGraph.Step right.coalgebra ⟨point, second⟩ label matching ∧
      ContextualCoalgebraMaterialReadout.value left.coalgebra worlds arrows next =
        ContextualCoalgebraMaterialReadout.value right.coalgebra worlds arrows matching := by
  obtain ⟨relation, bisimulation, related⟩ :=
    (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows).labelledBisimilar_of_decorate_eq
      (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows) same
  obtain ⟨other, matching, matched, readings, children⟩ := (bisimulation related).1 label next step
  have labels := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective readings
  cases labels
  exact ⟨matching, matched,
    (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows).decorate_eq_of_labelledBisimilar
      (ContextualCoalgebraMaterialReadout.labelPresentation worlds arrows)
      ⟨relation, bisimulation, children⟩⟩

theorem readValue_stable {first second : D} (step : first ⟶ second)
    {left right : (coproduct (D := D)).obj first}
    (same : readValue worlds arrows first left = readValue worlds arrows first right) :
    readValue worlds arrows second ((coproduct (D := D)).map step left) =
      readValue worlds arrows second ((coproduct (D := D)).map step right) := by
  obtain ⟨matching, matched, readings⟩ := readValue_matching worlds arrows left.1 right.1 same
    (.context first second step) ⟨second, left.1.carrier.map step left.2⟩
    (ContextualCoalgebraLabelledGraph.context_step left.1.coalgebra step left.2)
  have target := (ContextualCoalgebraLabelledGraph.context_step_iff right.1.coalgebra
    step right.2 matching).mp matched
  cases target
  exact readings

theorem readValue_forth (left right : Code D) {point : D}
    {first : left.carrier.obj point} {second : right.carrier.obj point}
    (same : readValue worlds arrows point ⟨left, first⟩ = readValue worlds arrows point ⟨right, second⟩)
    (future : Future.Objects point) (child : left.carrier.obj future.1)
    (available : (left.coalgebra.app point first).val.holds ⟨future, child⟩) :
    ∃ matching, (right.coalgebra.app point second).val.holds ⟨future, matching⟩ ∧
      readValue worlds arrows future.1 ⟨left, child⟩ = readValue worlds arrows future.1 ⟨right, matching⟩ := by
  obtain ⟨matching, matched, readings⟩ := readValue_matching worlds arrows left right same
    (.child point future.1 future.2) ⟨future.1, child⟩
    (ContextualCoalgebraLabelledGraph.child_step left.coalgebra future.2 first child available)
  obtain ⟨next, target, available⟩ :=
    (ContextualCoalgebraLabelledGraph.child_step_iff right.coalgebra future.2 second matching).mp matched
  cases target
  exact ⟨next, available, readings⟩

theorem coproduct_truth (point : D) (argument : (coproduct (D := D)).obj point)
    (future : Future.Objects point) (child : (coproduct (D := D)).obj future.1) :
    (coproductCoalgebra.app point argument).val.holds ⟨future, child⟩ ↔
      ∃ next : argument.1.carrier.obj future.1, child = ⟨argument.1, next⟩ ∧
        (argument.1.coalgebra.app point argument.2).val.holds ⟨future, next⟩ := by
  constructor
  · rintro ⟨next, same, available⟩
    exact ⟨next, same.symm, available⟩
  · rintro ⟨next, same, available⟩
    exact ⟨next, same.symm, available⟩

theorem readValue_isBisimulation :
    ContextualCoalgebraBisimulation.IsBisimulation (coproductCoalgebra (D := D))
      (fun point left right => readValue worlds arrows point left = readValue worlds arrows point right) where
  stable {_ _} step {_ _} same := readValue_stable worlds arrows step same
  forth {point left right} same future {child} available := by
    obtain ⟨next, rfl, admitted⟩ := (coproduct_truth point left future child).mp available
    obtain ⟨matching, matched, readings⟩ := readValue_forth worlds arrows left.1 right.1 same future next admitted
    exact ⟨⟨right.1, matching⟩, (coproduct_truth point right future _).mpr ⟨matching, rfl, matched⟩, readings⟩
  back {point left right} same future {child} available := by
    obtain ⟨next, rfl, admitted⟩ := (coproduct_truth point right future child).mp available
    obtain ⟨matching, matched, readings⟩ := readValue_forth worlds arrows right.1 left.1 same.symm future next admitted
    exact ⟨⟨left.1, matching⟩, (coproduct_truth point left future _).mpr ⟨matching, rfl, matched⟩, readings.symm⟩

theorem readValue_eq_of_canonical_eq (left right : Code D) (point : D)
    (first : left.carrier.obj point) (second : right.carrier.obj point)
    (same : (canonical left).app point first = (canonical right).app point second) :
    readValue worlds arrows point ⟨left, first⟩ = readValue worlds arrows point ⟨right, second⟩ := by
  let joined := ContextualSmallCoalgebraComparisons.pullbackCode left right quotientCoalgebra
    (canonical left) (canonical right) (canonical_square left) (canonical_square right)
  let pair : joined.carrier.obj point := ⟨(first, second), same⟩
  have earlier := ContextualCoalgebraMaterialReadout.coalgebra_map_value joined.coalgebra worlds arrows
    (pullbackFirst (canonical left) (canonical right)) left.coalgebra
    (ContextualCoalgebraPullback.first_square left.coalgebra right.coalgebra quotientCoalgebra
      (canonical left) (canonical right) (canonical_square left) (canonical_square right)) point pair
  have later := ContextualCoalgebraMaterialReadout.coalgebra_map_value joined.coalgebra worlds arrows
    (pullbackSecond (canonical left) (canonical right)) right.coalgebra
    (ContextualCoalgebraPullback.second_square left.coalgebra right.coalgebra quotientCoalgebra
      (canonical left) (canonical right) (canonical_square left) (canonical_square right)) point pair
  exact earlier.symm.trans later

theorem readValue_eq_iff_bisimilar (point : D) (left right : (coproduct (D := D)).obj point) :
    readValue worlds arrows point left = readValue worlds arrows point right ↔
      ContextualCoalgebraBisimulation.Bisimilar coproductCoalgebra point left right := by
  constructor
  · intro same
    exact ContextualCoalgebraBisimulation.greatest coproductCoalgebra
      (readValue_isBisimulation worlds arrows) same
  · intro related
    exact readValue_eq_of_canonical_eq worlds arrows left.1 right.1 point left.2 right.2
      ((ContextualCoalgebraQuotient.projection_eq_iff coproductCoalgebra point left right).mpr related)

def carrierGraph (point : D) : AccessiblePointedGraph.{u + 1} :=
  AccessiblePointedGraph.sup fun argument : (coproduct (D := D)).obj point =>
    (readGraph worlds arrows point argument).lift

def carrier (point : D) : HSet.{u + 1} := HSet.mk (carrierGraph worlds arrows point)

theorem mem_carrier_iff (point : D) (member : HSet.{u + 1}) :
    member ∈ carrier worlds arrows point ↔
      ∃ argument : (coproduct (D := D)).obj point, HSet.lift (readValue worlds arrows point argument) = member := by
  change member ∈ HSet.range (fun argument : (coproduct (D := D)).obj point =>
    (readGraph worlds arrows point argument).lift) ↔ _
  rw [HSet.mem_range]
  exact exists_congr fun argument => Iff.rfl

abbrev Members (point : D) := {member : HSet.{u + 1} // member ∈ carrier worlds arrows point}

def observe (point : D) (argument : (coproduct (D := D)).obj point) : Members worlds arrows point :=
  ⟨HSet.lift (readValue worlds arrows point argument), (mem_carrier_iff worlds arrows point _).mpr ⟨argument, rfl⟩⟩

theorem observe_surjective (point : D) : Function.Surjective (observe worlds arrows point) := by
  intro member
  obtain ⟨argument, same⟩ := (mem_carrier_iff worlds arrows point member.val).mp member.property
  exact ⟨argument, Subtype.ext same⟩

theorem observe_eq_iff (point : D) (left right : (coproduct (D := D)).obj point) :
    observe worlds arrows point left = observe worlds arrows point right ↔
      ContextualCoalgebraBisimulation.Bisimilar coproductCoalgebra point left right := by
  constructor
  · intro same
    exact (readValue_eq_iff_bisimilar worlds arrows point left right).mp
      (HSet.lift_injective (congrArg Subtype.val same))
  · intro related
    exact Subtype.ext (congrArg HSet.lift ((readValue_eq_iff_bisimilar worlds arrows point left right).mpr related))

abbrev Representatives (point : D) (member : HSet.{u + 1}) :=
  {argument : (coproduct (D := D)).obj point // HSet.lift (readValue worlds arrows point argument) = member}

def transportRange {first second : D} (step : first ⟶ second) (member : HSet.{u + 1}) : HSet.{u + 1} :=
  HSet.range fun representative : Representatives worlds arrows first member =>
    (readGraph worlds arrows second ((coproduct (D := D)).map step representative.val)).lift

theorem transportRange_singleton {first second : D} (step : first ⟶ second)
    (argument : (coproduct (D := D)).obj first) :
    transportRange worlds arrows step (HSet.lift (readValue worlds arrows first argument)) =
      {HSet.lift (readValue worlds arrows second ((coproduct (D := D)).map step argument))} := by
  apply HSet.ext
  intro member
  rw [transportRange, HSet.mem_range, HSet.mem_singleton]
  constructor
  · rintro ⟨representative, same⟩
    have moved := readValue_stable worlds arrows step (HSet.lift_injective representative.property)
    exact same.symm.trans (congrArg HSet.lift moved)
  · intro same
    exact ⟨⟨argument, rfl⟩, same.symm⟩

def transportValue {first second : D} (step : first ⟶ second) (member : HSet.{u + 1}) : HSet.{u + 1} :=
  HSet.sUnion (transportRange worlds arrows step member)

theorem transportValue_beta {first second : D} (step : first ⟶ second)
    (argument : (coproduct (D := D)).obj first) :
    transportValue worlds arrows step (HSet.lift (readValue worlds arrows first argument)) =
      HSet.lift (readValue worlds arrows second ((coproduct (D := D)).map step argument)) := by
  rw [transportValue, transportRange_singleton, HSet.sUnion_singleton]

theorem transportValue_mem {first second : D} (step : first ⟶ second)
    (member : HSet.{u + 1}) (present : member ∈ carrier worlds arrows first) :
    transportValue worlds arrows step member ∈ carrier worlds arrows second := by
  obtain ⟨argument, rfl⟩ := (mem_carrier_iff worlds arrows first member).mp present
  rw [transportValue_beta]
  exact (observe worlds arrows second ((coproduct (D := D)).map step argument)).property

def transport {first second : D} (step : first ⟶ second)
    (member : Members worlds arrows first) : Members worlds arrows second :=
  ⟨transportValue worlds arrows step member.val, transportValue_mem worlds arrows step member.val member.property⟩

theorem transport_observe {first second : D} (step : first ⟶ second)
    (argument : (coproduct (D := D)).obj first) :
    transport worlds arrows step (observe worlds arrows first argument) =
      observe worlds arrows second ((coproduct (D := D)).map step argument) :=
  Subtype.ext (transportValue_beta worlds arrows step argument)

theorem transport_identity (point : D) (member : Members worlds arrows point) :
    transport worlds arrows (𝟙 point) member = member := by
  obtain ⟨argument, rfl⟩ := observe_surjective worlds arrows point member
  rw [transport_observe]
  exact congrArg (observe worlds arrows point)
    (congrArg (fun operation => operation argument) ((coproduct (D := D)).map_id point))

theorem transport_comp {first middle last : D} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (member : Members worlds arrows first) :
    transport worlds arrows (earlier ≫ later) member =
      transport worlds arrows later (transport worlds arrows earlier member) := by
  obtain ⟨argument, rfl⟩ := observe_surjective worlds arrows first member
  rw [transport_observe, transport_observe, transport_observe]
  exact congrArg (observe worlds arrows last)
    (congrArg (fun operation => operation argument) ((coproduct (D := D)).map_comp earlier later))

def family : D ⥤ Type (u + 2) where
  obj := Members worlds arrows
  map step := TypeCat.ofHom (transport worlds arrows step)
  map_id point := by
    apply ConcreteCategory.hom_ext
    exact transport_identity worlds arrows point
  map_comp earlier later := by
    apply ConcreteCategory.hom_ext
    exact transport_comp worlds arrows earlier later

def observation : NaturalHom (coproduct (D := D)) (family worlds arrows) where
  app := observe worlds arrows
  naturality := transport_observe worlds arrows

/-- The full fibre predicate on occurrences supplies a class carrier at
the raised graph bound, with an actual member decoder and inverse. -/
abbrev Classes (point : D) : Type (u + 1) :=
  AccessiblePointedGraph.PowerMemberClass (carrierGraph worlds arrows point)

def memberEquiv (point : D) : Classes worlds arrows point ≃ Members worlds arrows point where
  toFun memberClass :=
    let member := AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point) memberClass
    ⟨member.val, by
      change member.val ∈ HSet.mk (carrierGraph worlds arrows point)
      rw [← AccessiblePointedGraph.picture_eq_mk]
      exact member.property⟩
  invFun member :=
    (AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point)).symm
      ⟨member.val, by
        rw [AccessiblePointedGraph.picture_eq_mk]
        exact member.property⟩
  left_inv memberClass := by
    apply (AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point)).injective
    exact (AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point)).apply_symm_apply _
  right_inv member := by
    apply Subtype.ext
    let pictured : AccessiblePointedGraph.PicturedMembers (carrierGraph worlds arrows point) :=
      ⟨member.val, by rw [AccessiblePointedGraph.picture_eq_mk]; exact member.property⟩
    change ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point))
      ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point)).symm pictured)).val = member.val
    exact congrArg (fun value : AccessiblePointedGraph.PicturedMembers (carrierGraph worlds arrows point) => value.val)
      ((AccessiblePointedGraph.powerMemberEquiv (carrierGraph worlds arrows point)).apply_symm_apply pictured)

def classFamily : D ⥤ Type (u + 1) where
  obj := Classes worlds arrows
  map {first second} step := TypeCat.ofHom fun memberClass =>
    (memberEquiv worlds arrows second).symm
      (transport worlds arrows step ((memberEquiv worlds arrows first) memberClass))
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro memberClass
    change (memberEquiv worlds arrows point).symm
      (transport worlds arrows (𝟙 point) ((memberEquiv worlds arrows point) memberClass)) = memberClass
    rw [transport_identity]
    exact (memberEquiv worlds arrows point).symm_apply_apply memberClass
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    intro memberClass
    change (memberEquiv worlds arrows last).symm
      (transport worlds arrows (earlier ≫ later) ((memberEquiv worlds arrows first) memberClass)) =
      (memberEquiv worlds arrows last).symm
        (transport worlds arrows later ((memberEquiv worlds arrows middle)
          ((memberEquiv worlds arrows middle).symm
            (transport worlds arrows earlier ((memberEquiv worlds arrows first) memberClass)))))
    rw [(memberEquiv worlds arrows middle).apply_symm_apply]
    exact congrArg (memberEquiv worlds arrows last).symm (transport_comp worlds arrows earlier later _)

def classToMembers : NaturalHom (classFamily worlds arrows) (family worlds arrows) where
  app := fun point => memberEquiv worlds arrows point
  naturality {first second} step memberClass :=
    ((memberEquiv worlds arrows second).apply_symm_apply
      (transport worlds arrows step ((memberEquiv worlds arrows first) memberClass))).symm

def membersToClass : NaturalHom (family worlds arrows) (classFamily worlds arrows) where
  app := fun point => (memberEquiv worlds arrows point).symm
  naturality {first second} step member := by
    change Members worlds arrows first at member
    change (memberEquiv worlds arrows second).symm
      (transport worlds arrows step ((memberEquiv worlds arrows first)
        ((memberEquiv worlds arrows first).symm member))) =
      (memberEquiv worlds arrows second).symm (transport worlds arrows step member)
    exact congrArg (memberEquiv worlds arrows second).symm
      (congrArg (transport worlds arrows step) ((memberEquiv worlds arrows first).apply_symm_apply member))

theorem classToMembers_membersToClass (point : D) (member : Members worlds arrows point) :
    (classToMembers worlds arrows).app point ((membersToClass worlds arrows).app point member) = member :=
  (memberEquiv worlds arrows point).apply_symm_apply member

theorem membersToClass_classToMembers (point : D) (memberClass : Classes worlds arrows point) :
    (membersToClass worlds arrows).app point ((classToMembers worlds arrows).app point memberClass) = memberClass :=
  (memberEquiv worlds arrows point).symm_apply_apply memberClass

def classObservation : NaturalHom (coproduct (D := D)) (classFamily worlds arrows) :=
  (observation worlds arrows).comp (membersToClass worlds arrows)

theorem classObservation_value (point : D) (argument : (coproduct (D := D)).obj point) :
    ((classToMembers worlds arrows).app point ((classObservation worlds arrows).app point argument)).val =
      HSet.lift (readValue worlds arrows point argument) :=
  congrArg Subtype.val (classToMembers_membersToClass worlds arrows point (observe worlds arrows point argument))

theorem classObservation_surjective (point : D) :
    Function.Surjective ((classObservation worlds arrows).app point) := by
  intro memberClass
  obtain ⟨argument, same⟩ := observe_surjective worlds arrows point ((memberEquiv worlds arrows point) memberClass)
  exact ⟨argument, (congrArg (memberEquiv worlds arrows point).symm same).trans
    ((memberEquiv worlds arrows point).symm_apply_apply memberClass)⟩

theorem classObservation_eq_iff (point : D) (left right : (coproduct (D := D)).obj point) :
    (classObservation worlds arrows).app point left = (classObservation worlds arrows).app point right ↔
      ContextualCoalgebraBisimulation.Bisimilar coproductCoalgebra point left right := by
  constructor
  · intro same
    exact (observe_eq_iff worlds arrows point left right).mp ((memberEquiv worlds arrows point).symm.injective same)
  · intro related
    exact congrArg (memberEquiv worlds arrows point).symm ((observe_eq_iff worlds arrows point left right).mpr related)

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSmallCoalgebraMaterialCarrier
