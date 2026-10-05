import Mettapedia.GSLT.Distinction.DependentComposition
import Mettapedia.GSLT.Distinction.DependentCompositionIdentity
import Mettapedia.TypeTheory.MaterialSets.Hypersets.FamilyDescent
import Mettapedia.GSLT.Distinction.Constructive.Controls
import Mettapedia.GSLT.Distinction.MaterializationObserver
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls

/-!
# Controls for coherent dependent composition

Each control pins one hypothesis of `DependentComposition` or
`DependentCompositionIdentity`. Controls proved elsewhere are reused by name
rather than reproved.

* **A first stage is not enough** (`Functional`): the identity readout of a
  Boolean and the coarse readout both factor the constant Boolean family, the
  identity section descends through the first, and the composite does not
  descend, because the descended section fails the second stage.
* **Path dependence** (`Paths`): two span relations between self-loop spans,
  satisfying all four occurrence lifting laws with actual events, each with an
  exact transport of the constant Boolean family; the two paths through the middle compose to the identity and to
  negation, so no transport of the composite relation agrees with its paths.
* **Records** (`Records`): an evidenced record of the edge-tag term keys its
  term on the occurrence, which the material readout does not retain, while its
  family key is retained. A declared record keyed on the material member alone
  is retained by the readout and licenses a false transport. The same family
  has a second factorization through the same readout along which the edge tag
  does descend: a record must carry its factorization, not only the fact that
  the family descends.
* **Occurrence-sensitive families** (`Occurrences`): Co Prime2's controls
  (`edgeTag_not_compatible`, `edgeSelectedFamily_not_factors`,
  `occurrences_no_material_descent`), and the identity-context occurrence motive
  observed through its right endpoint and the readout, which descends through
  no composite ending in the readout.
* **Bounds are not transport** (`Bounds`): in the constructive coarse system the
  two terms are at depth bound `0` at every depth, yet the varying family has
  no transport and the identity section of the constant family disagrees. A
  map with error `1` moves a reading, so no reading-indexed family transports
  universally. Equal material members carry no transport of the edge-selected
  family. For the real metric with a positive discount (classical), the two
  phases of a cycle are at logical distance `0` and a phase-sensitive family
  has no transport.
* **Collection is not coherent choice** (`Collection`): Co Prime2's natural-loop
  control: the all-witness projection covers every point, and no natural
  section exists.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.DependentCompositionControls

open Mettapedia.TypeTheory.ExtensionalReadout
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization
open Mettapedia.TypeTheory.DependentFamilySectionDescent
open Mettapedia.GSLT.Distinction.DependentComposition

universe u v w

/-- Negation of a Boolean as an equivalence. -/
def negation : Bool ≃ Bool where
  toFun := not
  invFun := not
  left_inv := Bool.not_not
  right_inv := Bool.not_not

/-- The identity on `true` and negation on `false`. -/
def twist : Bool → (Bool ≃ Bool)
  | true => Equiv.refl Bool
  | false => negation

theorem twist_self : ∀ b, twist b b = true
  | true => rfl
  | false => rfl

/-! ## A first stage is not enough -/

namespace Functional

/-- The identity split readout of a Boolean. -/
def identityReadout : SplitReadout Bool Bool where
  observe := id
  representative := id
  observe_representative _ := rfl

def firstStage : FamilyFactorization identityReadout.observe (fun _ : Bool => Bool) :=
  FamilyFactorization.constant _ Bool

def secondStage : FamilyFactorization Canary.coarseBool firstStage.targetFamily :=
  FamilyFactorization.constant _ Bool

/-- The identity section descends through the identity readout. -/
theorem identity_descends_first : Compatible firstStage (fun b : Bool => b) := by
  intro left right same
  have equal : left = right := same
  subst equal
  rfl

/-- **The composite does not descend.** -/
theorem identity_not_composite :
    ¬ Compatible (composeFactorization firstStage secondStage) (fun b : Bool => b) :=
  blocked _ _ (left := true) (right := false) rfl (fun same => Bool.noConfusion (eq_of_heq same))

/-- **The second stage fails for the descended section**, while both stages
factor the family and the first stage descends the section. -/
theorem second_stage_fails :
    Compatible firstStage (fun b : Bool => b) ∧
      ¬ Compatible secondStage (descendSection identityReadout firstStage (fun b : Bool => b)) :=
  ⟨identity_descends_first, fun second => identity_not_composite
    ((compatible_compose_iff identityReadout firstStage secondStage _).mpr
      ⟨identity_descends_first, second⟩)⟩

end Functional

/-! ## Path dependence -/

namespace Paths

open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.GSLT.Distinction.SpanTransport

/-- Every state with one self-loop event. -/
def loops (X : Type) : ReductionSpan.{0, 0} X where
  Edge := X
  source := id
  target := id

/-- The total relation on states and on events. -/
def everything (X Y : Type) : SpanRelation (loops X) (loops Y) where
  states _ _ := True
  events _ _ := True
  source_rel := fun _ _ _ => trivial
  target_rel := fun _ _ _ => trivial

/-- **All four occurrence lifting laws hold**, each matching an actual event. -/
theorem everything_laws (X Y : Type) :
    (everything X Y).SourceForthOcc ∧ (everything X Y).SourceBackOcc ∧
      (everything X Y).TargetForthOcc ∧ (everything X Y).TargetBackOcc :=
  ⟨fun _ y _ _ _ => ⟨y, rfl, trivial⟩, fun x _ _ _ _ => ⟨x, rfl, trivial⟩,
    fun _ y _ _ _ => ⟨y, rfl, trivial⟩, fun x _ _ _ _ => ⟨x, rfl, trivial⟩⟩

def first := everything PUnit Bool
def second := everything Bool PUnit

/-- The first transport is the identity. -/
def firstTransport : RelTransport first.states (fun _ => Bool) (fun _ => Bool) :=
  fun _ _ _ => Equiv.refl Bool

/-- The second transport twists at the middle point `false`. -/
def secondTransport : RelTransport second.states (fun _ => Bool) (fun _ => Bool) :=
  fun middle _ _ => twist middle

def through (middle : Bool) : Path first.states second.states PUnit.unit PUnit.unit :=
  ⟨middle, trivial, trivial⟩

/-- **The two paths disagree.** -/
theorem paths_disagree :
    pathTransport firstTransport secondTransport (through true) true = true ∧
      pathTransport firstTransport secondTransport (through false) true = false :=
  ⟨rfl, rfl⟩

theorem not_pathIndependent : ¬ PathIndependent firstTransport secondTransport := by
  intro independent
  have same := congrArg (fun equivalence : Bool ≃ Bool => equivalence true)
    (independent (through true) (through false))
  exact Bool.noConfusion (paths_disagree.1.symm.trans (same.trans paths_disagree.2))

/-- **Two descending stages whose composite does not descend**: both relations
satisfy all four lifting laws and carry exact transports, and no transport of
the composite relation agrees with its paths. -/
theorem composite_does_not_descend :
    ¬ ∃ T : RelTransport (first.comp second).states (fun _ => Bool) (fun _ => Bool),
      Descends firstTransport secondTransport T :=
  fun ⟨T, descends⟩ =>
    not_pathIndependent (pathIndependent_of_descends firstTransport secondTransport T descends)

/-- The composite relation does carry a transport (the identity); it is the
agreement with the stages that fails. -/
theorem composite_identity_incoherent :
    ¬ Descends firstTransport secondTransport
      (fun _ _ _ => Equiv.refl Bool : RelTransport (first.comp second).states (fun _ => Bool)
        (fun _ => Bool)) :=
  fun descends => composite_does_not_descend ⟨_, descends⟩

end Paths

/-! ## Records -/

namespace Records

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

/-- **An evidenced record of the edge tag**: its family is keyed on the material
member, its term on the occurrence itself. -/
def edgeRecord : DependenceRecord (fun _ : Occurrence twoChildren.{u} => Bool) edgeTag where
  FamilyKey := PicturedMembers twoChildren
  TermKey := Occurrence twoChildren
  familyKey := memberObservation twoChildren
  termKey := id
  coarsen := memberObservation twoChildren
  coarsen_termKey _ := rfl
  family := boolMemberFamily
  term := by
    rw [compatible_familyAlong_iff]
    intro left right same
    have equal : left = right := same
    subst equal
    exact HEq.rfl

/-- The material readout retains the family key. -/
def memberRetainsFamily :
    Retains (memberObservation twoChildren.{u}) edgeRecord.{u}.familyKey :=
  ⟨id, fun _ => rfl⟩

/-- **The material readout does not retain the term key**: the record predicts
that the term is blocked while its family is transported. -/
theorem member_erases_termKey :
    IsEmpty (Retains (memberObservation twoChildren.{u}) edgeRecord.{u}.termKey) :=
  ⟨fun retains => twoChildrenOccurrence_ne
    ((retains.decode_observe (twoChildrenOccurrence true)).symm.trans
      ((congrArg retains.decode twoChildren_same_member).trans
        (retains.decode_observe (twoChildrenOccurrence false))))⟩

/-- The prediction holds: the family is transported, the term is blocked
(Co Prime2's `edgeTag_not_compatible`). -/
theorem record_prediction :
    Nonempty (FamilyFactorization (memberObservation twoChildren.{u}) (fun _ => Bool)) ∧
      ¬ Compatible boolMemberFamily.{u} edgeTag :=
  ⟨⟨edgeRecord.familyAlong memberRetainsFamily⟩, edgeTag_not_compatible⟩

/-- A declared key that drops the edge: the material member itself. -/
def memberRetention :
    Retains (memberObservation twoChildren.{u}) (memberObservation twoChildren) :=
  ⟨id, fun _ => rfl⟩

/-- **A record that drops an observation licenses a false transport**: keyed on
the material member alone, it is retained by the material readout, and the
transport it would license is false. Its evidence field cannot be filled. -/
theorem dropped_record_licence_false :
    Nonempty (Retains (memberObservation twoChildren.{u}) (memberObservation twoChildren)) ∧
      ¬ Compatible (familyAlong boolMemberFamily.{u} memberRetention) edgeTag :=
  ⟨⟨memberRetention⟩, fun compatible => edgeTag_not_compatible
    ((compatible_iff_heq _ _).mpr ((compatible_familyAlong_iff _ _ _).mp compatible))⟩

/-- A second factorization of the same constant family through the same
readout, identifying each fibre through the edge. -/
def twistedMemberFamily :
    FamilyFactorization (memberObservation twoChildren.{u}) (fun _ => Bool) where
  targetFamily _ := Bool
  identify occurrence := twist (edgeTag occurrence)

/-- **Descent of a term is relative to the factorization**: the edge tag
descends along the twisted factorization and not along the constant one. -/
theorem same_family_opposite_verdicts :
    Compatible twistedMemberFamily.{u} edgeTag ∧ ¬ Compatible boolMemberFamily.{u} edgeTag := by
  refine ⟨?_, edgeTag_not_compatible⟩
  rw [compatible_iff_heq]
  intro left right _
  exact heq_of_eq ((twist_self (edgeTag left)).trans (twist_self (edgeTag right)).symm)

end Records

/-! ## Occurrence-sensitive families -/

namespace Occurrences

open _root_.CategoryTheory
open Mettapedia.TypeTheory.GroupoidIdentityElimination
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph
open Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PresentationIdentityControls
open Mettapedia.GSLT.Distinction.DependentCompositionIdentity

local infixr:80 " ⋙₀ " => compose

/-- **Reused**: the occurrence-sensitive family has no descent through the
material readout, even up to a natural fibre equivalence. -/
theorem occurrences_control :
    ¬ ∃ family : Discrete HSet.{u} ⥤ Type u,
      Nonempty (NaturalEquivalence presentationOccurrences (compose readout family)) :=
  MaterialIdentityObservation.Controls.occurrences_no_material_descent

/-- **Reused**: pointwise, the edge-selected family does not factor through
material members, even up to fibre equivalence. -/
theorem edgeSelected_control :
    ¬ Nonempty (FamilyFactorization (memberObservation twoChildren.{u}) edgeSelectedFamily) :=
  edgeSelectedFamily_not_factors

/-- The right endpoint of an identity witness, an exact observation of the
identity context. -/
def rightEndpoint (C : Type v) [Category.{w} C] : Arrow C ⥤ C where
  obj witness := witness.right
  map square := square.right
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The swap acting on both ends of the reflexive witness of `twoChildren`. -/
def swapSquare : Arrow.mk (𝟙 twoChildren.{u}) ⟶ Arrow.mk (𝟙 twoChildren.{u}) :=
  Arrow.homMk swapOccurrences swapOccurrences (by
    change swapOccurrences ≫ 𝟙 twoChildren = 𝟙 twoChildren ≫ swapOccurrences
    rw [Category.comp_id, Category.id_comp])

theorem swapSquare_moves :
    occurrenceMotive.map swapSquare.{u} (twoChildrenOccurrence true) ≠ twoChildrenOccurrence true := by
  change swapOccurrences.occurrenceTransport (twoChildrenOccurrence true) ≠ _
  rw [swap_true_occurrence]
  exact twoChildrenOccurrence_ne.symm

/-- **The occurrence motive descends through no composite of the right
endpoint and the material readout**, even up to natural fibre equivalence. -/
theorem occurrenceMotive_no_descent :
    ¬ ∃ observed : Discrete HSet.{u} ⥤ Type u,
      Nonempty (NaturalEquivalence occurrenceMotive
        ((rightEndpoint AccessiblePointedGraph.{u} ⋙₀ readout) ⋙₀ observed)) :=
  no_descent_through_readout (rightEndpoint _) occurrenceMotive swapSquare
    (twoChildrenOccurrence true) swapSquare_moves

end Occurrences

/-! ## Bounds are not transport -/

namespace Bounds

open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.Distinction.Constructive.Controls

/-- The two terms of the coarse system are at depth bound `0` at every depth. -/
theorem coarse_distance_zero (depth : ℕ) : coarse.depthBound coarseVocabulary depth false true = 0 :=
  coarse.depthBound_eq_zero_of_gradedBisimilar coarseVocabulary coarse_gradedBisimilar depth

/-- Closeness at depth bound `0`. -/
def atZero (depth : ℕ) (left right : Bool) : Prop :=
  coarse.depthBound coarseVocabulary depth left right = 0

/-- **Distance `0` under a non-reflecting observer gives no family transport.** -/
theorem distance_zero_no_transport (depth : ℕ) :
    ¬ Nonempty (RelTransport (atZero depth) Canary.varying Canary.varying) :=
  fun ⟨T⟩ => Canary.unit_not_equiv_bool ⟨T (coarse_distance_zero depth)⟩

/-- Nor universally. -/
theorem distance_zero_not_universal (depth : ℕ) :
    ¬ ∀ F : Bool → Type, Nonempty (RelTransport (atZero depth) F F) :=
  fun all => Bool.noConfusion ((universal_transport_iff (atZero depth)).mp all
    (coarse_distance_zero depth))

/-- **The constant family factors through every observation, yet its identity
section is not carried across distance `0`.** -/
theorem distance_zero_no_term_transport (depth : ℕ) :
    ¬ SectionsRelated (fun _ _ _ => Equiv.refl Bool : RelTransport (atZero depth)
      (fun _ => Bool) (fun _ => Bool)) (fun b => b) (fun b => b) :=
  fun related => Bool.noConfusion (related (coarse_distance_zero depth))

/-- A map with error `1` raising the reading of `true` from `0` to `1`. -/
def raise : ObservationMap (graded 0 (by decide) (by decide)) (graded 1 (by decide) (by decide)) 1 :=
  rise 0 1 (by decide) (by decide) (by decide) (by decide) (by decide)

theorem raise_moves_reading :
    (graded 1 (by decide) (by decide)).value (raise.atom ()) (raise.mapTerm true) ≠
      (graded 0 (by decide) (by decide)).value () true := by
  decide

/-- **A bound at a positive error gives no transport**: the reading of `true`
moves within the error `1`, and no reading-indexed family transports
universally. -/
theorem positive_error_no_transport :
    ¬ ∀ Φ : ℤ → Type,
      Nonempty (Φ ((graded 0 (by decide) (by decide)).value () true) ≃
        Φ ((graded 1 (by decide) (by decide)).value (raise.atom ()) (raise.mapTerm true))) :=
  fun all => raise_moves_reading ((readingTransport_iff raise () true).mp all)

end Bounds

namespace MaterialBounds

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.AccessiblePointedGraph

/-- **Equal material members carry no transport of the edge-selected family**,
along any relation containing the two occurrences. -/
theorem material_equal_no_transport (close : Occurrence twoChildren.{u} → Occurrence twoChildren → Prop)
    (related : close (twoChildrenOccurrence true) (twoChildrenOccurrence false)) :
    ¬ Nonempty (RelTransport close edgeSelectedFamily edgeSelectedFamily) := by
  rintro ⟨T⟩
  have equiv := T related
  have simpler : PUnit ≃ PEmpty := by
    simpa [edgeSelectedFamily] using equiv
  exact (simpler PUnit.unit).elim

theorem material_kernel_no_transport :
    ¬ Nonempty (RelTransport
      (fun left right : Occurrence twoChildren.{u} =>
        memberObservation twoChildren left = memberObservation twoChildren right)
      edgeSelectedFamily edgeSelectedFamily) :=
  material_equal_no_transport _ twoChildren_same_member

end MaterialBounds

namespace RealMetric

open Mettapedia.GSLT.ObservedMaterialization.Controls
open Mettapedia.TypeTheory.MaterialSets.Hypersets.OutcomeLabels

/-- A family that distinguishes the two phases of a cycle. -/
def phaseFamily : State.{0} → Type
  | .terminal _ => PUnit
  | .cycle _ true => PUnit
  | .cycle _ false => PEmpty

/-- **Classical** (real metric): for every positive discount the two phases of
a cycle are at logical distance `0`, and the phase family has no transport
along distance `0`. -/
theorem phases_distance_zero_no_transport {discount : ℝ} (nonneg : 0 ≤ discount)
    (le_one : discount ≤ 1) (positive : 0 < discount) :
    (GradedSystem.ofSystem system.{0} discount nonneg le_one).logicalDistance
        (State.cycle (Outcome.result 0) true) (State.cycle (Outcome.result 0) false) = 0 ∧
      ¬ Nonempty (RelTransport
        (fun left right => (GradedSystem.ofSystem system.{0} discount nonneg le_one).logicalDistance
          left right = 0) phaseFamily phaseFamily) := by
  have zero := (MaterializationObserver.DiscountControl.positive_discount_kernel (Outcome.result 0)
    true nonneg le_one positive).1
  refine ⟨zero, ?_⟩
  rintro ⟨T⟩
  exact (T zero PUnit.unit).elim

end RealMetric

/-! ## Collection is not coherent choice -/

namespace Collection

open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollection
open Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls.Advancing

/-- **Reused**: covering is not a coherent dependent section. -/
theorem collection_not_coherent_choice :
    (∀ atPoint, Function.Surjective
      ((projection domain.{u} body (StablePredicate.full body)).app atPoint)) ∧
      ¬ Nonempty collected.{u}.family.sections :=
  ⟨collection_projection_covers, collected_no_natural_section⟩

end Collection

end Mettapedia.GSLT.Distinction.DependentCompositionControls
