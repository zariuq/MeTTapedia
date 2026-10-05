import Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualSetInfinity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.HypersetLogicalStrength
import Mettapedia.TypeTheory.ContextualKernelQuotients
import Mettapedia.TypeTheory.IdentityObservationComparison

/-!
# Consumers and presentation identities in the contextual set model

The actual final covered-power coalgebra supplies the behavioural observation
of any covered contextual coalgebra. Its kernel is greatest bisimilarity at
the same complete future arrows. The constructed kernel quotient classifies
all natural consumers that respect that observation, without selecting an
inverse from the literal image in the final carrier.

At every world the material embedding sends graph presentations and their
actual occurrence readings into the internal membership family. A nontrivial
presentation symmetry obstructs descent of occurrence transport through this
discrete value reading, even up to natural fibre equivalence. Coherent J for
observed motives still commutes with the reading.

The context and graph bound is `u`; final sets and literal members live in
`Type (u+1)`. External host Choice is inherited from finality. This comparison
does not assert native equality reflection, UIP, univalence or internal Choice.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualObserverComparison

open _root_.CategoryTheory AccessiblePointedGraph
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.GroupoidIdentityElimination
open HostChoiceContextualSetInterpretation HostChoiceContextualSetInterpretation.Finality

universe u v w
variable {D : Type u} [Category.{u} D]

noncomputable def observe {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) : NaturalHom A sets :=
  (HostChoiceContextualCoalgebraFinality.readout coalgebra).comp
    (HostChoiceContextualCoalgebraFinality.raise.{u,0,u+1}
      (ContextualSmallCoalgebraGenerators.quotient (D := D)))

theorem observe_kernel {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (point : D) (first second : A.obj point) :
    (observe coalgebra).app point first = (observe coalgebra).app point second ↔
      ContextualCoalgebraBisimulation.Bisimilar coalgebra point first second := by
  constructor
  · intro same
    exact (HostChoiceContextualCoalgebraFinality.readout_kernel coalgebra point first second).mp
      (congrArg ULift.down same)
  · intro related
    exact congrArg ULift.up
      ((HostChoiceContextualCoalgebraFinality.readout_kernel coalgebra point first second).mpr related)

def Behavioral {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    {C : D ⥤ Type w} (consumer : NaturalHom A C) : Prop :=
  ∀ point {first second}, ContextualCoalgebraBisimulation.Bisimilar coalgebra point first second →
    consumer.app point first = consumer.app point second

theorem respects_iff_behavioral {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    {C : D ⥤ Type w} (consumer : NaturalHom A C) :
    Mettapedia.TypeTheory.ContextualKernelQuotients.Respects (observe coalgebra) consumer ↔
      Behavioral coalgebra consumer := by
  constructor
  · intro compatible point first second related
    exact compatible point ((observe_kernel coalgebra point first second).mpr related)
  · intro compatible point first second same
    exact compatible point ((observe_kernel coalgebra point first second).mp same)

noncomputable def classes {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) : D ⥤ Type v :=
  Mettapedia.TypeTheory.ContextualKernelQuotients.quotient (observe coalgebra)

noncomputable def classProjection {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) :
    NaturalHom A (classes coalgebra) :=
  Mettapedia.TypeTheory.ContextualKernelQuotients.projection (observe coalgebra)

noncomputable def consumerEquiv {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) (C : D ⥤ Type w) :
    NaturalHom (classes coalgebra) C ≃ {consumer : NaturalHom A C // Behavioral coalgebra consumer} where
  toFun consumer := ⟨(classProjection coalgebra).comp consumer,
    (respects_iff_behavioral coalgebra _).mp
      (Mettapedia.TypeTheory.ContextualKernelQuotients.projection_respects (observe coalgebra) consumer)⟩
  invFun consumer := Mettapedia.TypeTheory.ContextualKernelQuotients.descend
    (observe coalgebra) consumer.val ((respects_iff_behavioral coalgebra _).mpr consumer.property)
  left_inv consumer := by
    apply NaturalHom.ext
    intro point value
    exact Quotient.inductionOn value fun _ => rfl
  right_inv consumer := Subtype.ext
    (Mettapedia.TypeTheory.ContextualKernelQuotients.descend_factorization
      (observe coalgebra) consumer.val _)

theorem consumer_beta {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) (C : D ⥤ Type w)
    (consumer : {consumer : NaturalHom A C // Behavioral coalgebra consumer})
    (point : D) (argument : A.obj point) :
    ((consumerEquiv coalgebra C).symm consumer).app point
      ((classProjection coalgebra).app point argument) = consumer.val.app point argument := rfl

theorem unique_consumer {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) {C : D ⥤ Type w}
    (consumer : NaturalHom A C) (compatible : Behavioral coalgebra consumer) :
    ∃! factor : NaturalHom (classes coalgebra) C,
      (classProjection coalgebra).comp factor = consumer := by
  have respects := (respects_iff_behavioral coalgebra consumer).mpr compatible
  refine ⟨Mettapedia.TypeTheory.ContextualKernelQuotients.descend
    (observe coalgebra) consumer respects,
    Mettapedia.TypeTheory.ContextualKernelQuotients.descend_factorization
      (observe coalgebra) consumer respects, ?_⟩
  intro factor same
  exact Mettapedia.TypeTheory.ContextualKernelQuotients.descend_unique
    (observe coalgebra) consumer respects factor same

/-- Agreement of all natural behavioural consumers is exactly the actual
observation kernel. The separating consumer is the constructed class map. -/
theorem all_consumers_iff {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A))
    (point : D) (first second : A.obj point) :
    (∀ (C : D ⥤ Type v) (consumer : NaturalHom A C), Behavioral coalgebra consumer →
      consumer.app point first = consumer.app point second) ↔
      ContextualCoalgebraBisimulation.Bisimilar coalgebra point first second := by
  constructor
  · intro agreement
    have compatible : Behavioral coalgebra (classProjection coalgebra) :=
      (respects_iff_behavioral coalgebra _).mp
        (fun _ _ _ same => Quotient.sound same)
    exact (observe_kernel coalgebra point first second).mp
      ((Mettapedia.TypeTheory.ContextualKernelQuotients.projection_eq_iff
        (observe coalgebra) point first second).mp
          (agreement (classes coalgebra) (classProjection coalgebra) compatible))
  · intro related _ consumer compatible
    exact compatible point related

noncomputable def classEmbedding {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) :
    NaturalHom (classes coalgebra) sets :=
  Mettapedia.TypeTheory.ContextualKernelQuotients.embedding (observe coalgebra)

theorem classEmbedding_injective {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) (point : D) :
    Function.Injective ((classEmbedding coalgebra).app point) :=
  Mettapedia.TypeTheory.ContextualKernelQuotients.embedding_injective (observe coalgebra) point

theorem section_kernel_iff {A : D ⥤ Type v}
    (coalgebra : NaturalHom A (CoveredFuturePowerFamilies.family A)) (first second : A.sections) :
    (observe coalgebra).mapSection first = (observe coalgebra).mapSection second ↔
      ∀ point, ContextualCoalgebraBisimulation.Bisimilar coalgebra point (first.val point) (second.val point) := by
  constructor
  · intro same point
    exact (observe_kernel coalgebra point _ _).mp
      (congrArg (fun value : (sets (D := D)).sections => value.val point) same)
  · intro related
    apply Subtype.ext
    funext point
    exact (observe_kernel coalgebra point _ _).mpr (related point)

noncomputable def graphValue (point : D) (graph : AccessiblePointedGraph.{u}) : sets.obj point :=
  HostChoiceContextualSetInfinity.reading.app point (HSet.mk graph)

theorem graphValue_eq_iff (point : D) (first second : AccessiblePointedGraph.{u}) :
    graphValue point first = graphValue point second ↔ HSet.mk first = HSet.mk second :=
  ⟨fun same => HostChoiceContextualSetInfinity.reading_injective point same, congrArg _⟩

theorem graphValue_context {point target : D} (arrow : point ⟶ target)
    (graph : AccessiblePointedGraph.{u}) :
    sets.map arrow (graphValue point graph) = graphValue target graph :=
  HostChoiceContextualSetInfinity.reading.naturality arrow (HSet.mk graph)

noncomputable def graphReadout (point : D) : AccessiblePointedGraph.{u} ⥤ Discrete (sets.obj point) where
  obj graph := Discrete.mk (graphValue point graph)
  map path := Discrete.eqToHom (congrArg (HostChoiceContextualSetInfinity.reading.app point) path.material_eq)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def internalMembers (point : D) : Discrete (sets.obj point) ⥤ Type (u+1) where
  obj parent := {child : sets.obj point // Member point child parent.as}
  map arrow := TypeCat.ofHom fun child =>
    ⟨child.val, (Discrete.eq_of_hom arrow) ▸ child.property⟩
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext rfl
  map_comp _ _ := by
    apply ConcreteCategory.hom_ext
    intro child
    exact Subtype.ext rfl

noncomputable def graphMembers (point : D) : AccessiblePointedGraph.{u} ⥤ Type (u+1) :=
  compose (graphReadout point) (internalMembers point)

noncomputable def occurrenceMember (point : D) (graph : AccessiblePointedGraph.{u})
    (occurrence : Occurrence graph) : (graphMembers point).obj graph :=
  ⟨HostChoiceContextualSetInfinity.reading.app point occurrence.picture,
    (HostChoiceContextualSetInfinity.reading_material_member point _ _).mpr
      (MaterialIdentityObservation.occurrenceMember graph occurrence).property⟩

noncomputable def occurrenceReading (point : D) :
    NatTrans MaterialIdentityObservation.liftedOccurrences (graphMembers point) where
  app graph := TypeCat.ofHom fun occurrence => occurrenceMember point graph occurrence.down
  naturality {_ _} path := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    apply Subtype.ext
    exact congrArg (HostChoiceContextualSetInfinity.reading.app point)
      (path.occurrence_picture occurrence.down)

theorem occurrenceReading_surjective (point : D) (graph : AccessiblePointedGraph.{u}) :
    Function.Surjective ((occurrenceReading point).app graph) := by
  intro member
  obtain ⟨material, same, belongs⟩ :=
    (HostChoiceContextualSetInfinity.reading_member point (HSet.mk graph) member.val).mp member.property
  obtain ⟨occurrence, valueEq⟩ := MaterialIdentityObservation.occurrenceReading_surjective graph
    ⟨material, belongs⟩
  refine ⟨occurrence, Subtype.ext ?_⟩
  exact (congrArg (HostChoiceContextualSetInfinity.reading.app point)
    (congrArg Subtype.val valueEq)).trans same

theorem occurrenceReading_context {point target : D} (arrow : point ⟶ target)
    (graph : AccessiblePointedGraph.{u}) (occurrence : Occurrence graph) :
    sets.map arrow (occurrenceMember point graph occurrence).val =
      (occurrenceMember target graph occurrence).val :=
  HostChoiceContextualSetInfinity.reading.naturality arrow occurrence.picture

/-- Any nontrivial occurrence action forbids natural descent into ordinary
identity of the actual set values, even when all fibres may be replaced by
naturally equivalent ones. -/
theorem no_occurrence_descent_of_moved (point : D)
    {graph : AccessiblePointedGraph.{u}} (loop : PresentationIso graph graph)
    (occurrence : Occurrence graph) (moved : loop.occurrenceTransport occurrence ≠ occurrence) :
    ¬ ∃ family : Discrete (sets.obj point) ⥤ Type (u+1),
      Nonempty (MaterialIdentityObservation.NaturalEquivalence MaterialIdentityObservation.liftedOccurrences
        (compose (graphReadout point) family)) := by
  rintro ⟨family, ⟨comparison⟩⟩
  have trivial := MaterialIdentityObservation.loop_action_trivial_of_discrete_descent
    (graphReadout point) MaterialIdentityObservation.liftedOccurrences family comparison loop
      (ULift.up occurrence)
  exact moved (congrArg ULift.down trivial)

theorem J_graphReadout (point : D) (motive : Arrow (Discrete (sets.obj point)) ⥤ Type w)
    (atReflexivity : NaturalSection (compose diagonal motive)) :
    J (compose (graphReadout point).mapArrow motive)
        (reindexReflexivity (graphReadout point) motive atReflexivity) =
      (J motive atReflexivity).reindex (graphReadout point).mapArrow :=
  J_sub_section (graphReadout point) motive atReflexivity

def presentationLayer : Mettapedia.TypeTheory.ScopedIdentity.Layer AccessiblePointedGraph.{u} where
  Route := PresentationIso
  refl := PresentationIso.refl
  Support first second := Nonempty (PresentationIso first second)
  forget path := ⟨path⟩

theorem identityComparison (point : D) :
    Mettapedia.TypeTheory.IdentityObservationComparison.Comparison presentationLayer.{u} (graphValue point) where
  toObservedEquality path := congrArg (HostChoiceContextualSetInfinity.reading.app point) path.material_eq

theorem identityComparison_faithful_iff (point : D) :
    (identityComparison point).Faithful ↔
      Mettapedia.TypeTheory.ScopedIdentity.RouteUIP presentationLayer.{u} :=
  (identityComparison point).faithful_iff_routeUIP

noncomputable def propositionValue (point : D) (proposition : Prop) : sets.obj point :=
  HostChoiceContextualSetInfinity.reading.app point (HypersetLogicalStrength.truthSet proposition)

theorem propositionValue_eq_iff (point : D) (first second : Prop) :
    propositionValue point first = propositionValue point second ↔ (first ↔ second) :=
  (show propositionValue point first = propositionValue point second ↔
      HypersetLogicalStrength.truthSet first = (HypersetLogicalStrength.truthSet second : HSet.{u}) from
    ⟨fun same => HostChoiceContextualSetInfinity.reading_injective point same, congrArg _⟩).trans
      (HypersetLogicalStrength.truthSet_eq_iff first second)

theorem propositionValue_member (point : D) (proposition : Prop) :
    Member point (emptySet.val point) (propositionValue point proposition) ↔ proposition := by
  rw [← HostChoiceContextualSetInfinity.reading_empty point]
  exact (HostChoiceContextualSetInfinity.reading_material_member point _ _).trans
    (HypersetLogicalStrength.empty_member_truthSet proposition)

theorem propositionValue_empty (point : D) (proposition : Prop) :
    propositionValue point proposition = emptySet.val point ↔ ¬ proposition := by
  rw [← HostChoiceContextualSetInfinity.reading_empty point]
  exact (show propositionValue point proposition =
      HostChoiceContextualSetInfinity.reading.app point (∅ : HSet.{u}) ↔
      HypersetLogicalStrength.truthSet proposition = (∅ : HSet.{u}) from
    ⟨fun same => HostChoiceContextualSetInfinity.reading_injective point same, congrArg _⟩).trans
      (HypersetLogicalStrength.truthSet_eq_empty proposition)

/-- Positive member recovery from mere inequality has exactly the inherited
double-negation price on the actual embedded proposition values. -/
theorem positive_recovery_iff_doubleNegation (point : D) :
    (∀ proposition : Prop, propositionValue point proposition ≠ emptySet.val point →
      Member point (emptySet.val point) (propositionValue point proposition)) ↔
      (∀ proposition : Prop, ¬ ¬ proposition → proposition) := by
  constructor
  · intro recover proposition doubleNegation
    exact (propositionValue_member point proposition).mp
      (recover proposition ((not_congr (propositionValue_empty point proposition)).mpr doubleNegation))
  · intro eliminate proposition nonempty
    exact (propositionValue_member point proposition).mpr
      (eliminate proposition ((not_congr (propositionValue_empty point proposition)).mp nonempty))

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualObserverComparison
