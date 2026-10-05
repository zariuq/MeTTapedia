import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.IndexedCoveredPowerBaseChange

/-!
# Base change of the material parameter-slice recipient

The recipient over C is compared with the literal dependent pullback of
the recipient over B along an arbitrary natural map C → B. The pulled
coalgebra is independently formed through indexed-power base change.
Constructed forward and inverse maps preserve the complete future-child
predicate, retained parameter and actual decoded material member.

The inverse laws hold for natural maps and compatible sections, including
noninjective substitutions. Originally small sources have a unique map
over the pulled parameter. Cover existence remains propositional; no
uniform original-bound enumeration or raw quotient inverse is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientBaseChange

open _root_.CategoryTheory CoveredFuturePowerFunctor
open CoveredFuturePowerFamilies (Predicate)
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.ContextualImageFactorization (pullback pullbackFirst pullbackSecond)
open ContextualMaterialSliceRecipient

universe u v w z
variable {D : Type u} [Category.{u} D]
variable (worlds : ArgumentCoding D)
variable (arrows : (source target : D) → ArgumentCoding (source ⟶ target))
variable (B : D ⥤ Type v) (C : D ⥤ Type w) (change : NaturalHom C B)

abbrev pulledFamily := pullback (parameter worlds arrows B) change
abbrev pulledParameter := pullbackSecond (parameter worlds arrows B) change
abbrev originalProjection := pullbackFirst (parameter worlds arrows B) change

def forward : NaturalHom (family worlds arrows C) (pulledFamily worlds arrows B C change) where
  app point value := ⟨((change.app point value.1, value.2), value.1), rfl⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext (Prod.ext (change.naturality step value.1) rfl) rfl

def backward : NaturalHom (pulledFamily worlds arrows B C change) (family worlds arrows C) where
  app _ value := (value.val.2, value.val.1.2)
  naturality _ _ := rfl

theorem backward_forward (point : D) (value : (family worlds arrows C).obj point) :
    (backward worlds arrows B C change).app point ((forward worlds arrows B C change).app point value) = value :=
  Prod.ext rfl rfl

theorem forward_backward (point : D) (value : (pulledFamily worlds arrows B C change).obj point) :
    (forward worlds arrows B C change).app point ((backward worlds arrows B C change).app point value) = value := by
  apply Subtype.ext
  exact Prod.ext (Prod.ext value.property.symm rfl) rfl

theorem backward_forward_hom : (forward worlds arrows B C change).comp (backward worlds arrows B C change) = identityHom (family worlds arrows C) := by
  apply NaturalHom.ext
  exact backward_forward worlds arrows B C change

theorem forward_backward_hom :
    (backward worlds arrows B C change).comp (forward worlds arrows B C change) = identityHom (pulledFamily worlds arrows B C change) := by
  apply NaturalHom.ext
  exact forward_backward worlds arrows B C change

theorem forward_parameter : (forward worlds arrows B C change).comp (pulledParameter worlds arrows B C change) = parameter worlds arrows C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_parameter : (backward worlds arrows B C change).comp (parameter worlds arrows C) = pulledParameter worlds arrows B C change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem forward_behavior :
    (forward worlds arrows B C change).comp ((originalProjection worlds arrows B C change).comp (behavior worlds arrows B)) = behavior worlds arrows C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_behavior :
    (backward worlds arrows B C change).comp (behavior worlds arrows C) = (originalProjection worlds arrows B C change).comp (behavior worlds arrows B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

def fibreEquiv (point : D) : (family worlds arrows C).obj point ≃ (pulledFamily worlds arrows B C change).obj point where
  toFun := (forward worlds arrows B C change).app point
  invFun := (backward worlds arrows B C change).app point
  left_inv := backward_forward worlds arrows B C change point
  right_inv := forward_backward worlds arrows B C change point

def sectionEquiv : (family worlds arrows C).sections ≃ (pulledFamily worlds arrows B C change).sections where
  toFun := (forward worlds arrows B C change).mapSection
  invFun := (backward worlds arrows B C change).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact backward_forward worlds arrows B C change point (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact forward_backward worlds arrows B C change point (term.val point)

def pulledMemberDecode : NaturalHom (pulledFamily worlds arrows B C change)
    (ContextualSmallCoalgebraMaterialCarrier.family worlds arrows) :=
  (originalProjection worlds arrows B C change).comp (memberDecode worlds arrows B)

theorem forward_memberDecode :
    (forward worlds arrows B C change).comp (pulledMemberDecode worlds arrows B C change) =
      memberDecode worlds arrows C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem backward_memberDecode :
    (backward worlds arrows B C change).comp (memberDecode worlds arrows C) =
      pulledMemberDecode worlds arrows B C change := by
  apply NaturalHom.ext
  intro _ _
  rfl

def coalgebraEntry : NaturalHom (pulledFamily worlds arrows B C change)
    (IndexedCoveredPowerBaseChange.baseFamily (parameter worlds arrows B) change) where
  app point value := ⟨((indexedCoalgebra worlds arrows B).app point value.val.1, value.val.2), value.property⟩
  naturality step value := by
    apply Subtype.ext
    exact Prod.ext ((indexedCoalgebra worlds arrows B).naturality step value.val.1) rfl

def pulledIndexedCoalgebra : NaturalHom (pulledFamily worlds arrows B C change)
    (IndexedCoveredPower.family (pulledParameter worlds arrows B C change)) :=
  (coalgebraEntry worlds arrows B C change).comp (IndexedCoveredPowerBaseChange.backward (parameter worlds arrows B) change)

def pulledCoalgebra : NaturalHom (pulledFamily worlds arrows B C change)
    (CoveredFuturePowerFamilies.family (pulledFamily worlds arrows B C change)) :=
  (pulledIndexedCoalgebra worlds arrows B C change).comp (IndexedCoveredPower.predicateProjection (pulledParameter worlds arrows B C change))

theorem pulled_parameter_square :
    (pulledIndexedCoalgebra worlds arrows B C change).comp
      (IndexedCoveredPower.projection (pulledParameter worlds arrows B C change)) = pulledParameter worlds arrows B C change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem original_square :
    (pulledCoalgebra worlds arrows B C change).comp (imageHom (originalProjection worlds arrows B C change)) =
      (originalProjection worlds arrows B C change).comp (coalgebra worlds arrows B) := by
  apply NaturalHom.ext
  intro point value
  exact IndexedCoveredPowerBaseChange.image_lift (parameter worlds arrows B) change point value.val.2
    ((coalgebra worlds arrows B).app point value.val.1)
    (IndexedCoveredPowerBaseChange.input_support (parameter worlds arrows B) change point
      ((coalgebraEntry worlds arrows B C change).app point value))

theorem forward_square : (coalgebra worlds arrows C).comp (imageHom (forward worlds arrows B C change)) =
    (forward worlds arrows B C change).comp (pulledCoalgebra worlds arrows B C change) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  change (∃ child : (family worlds arrows C).obj future.1.1,
    (forward worlds arrows B C change).app future.1.1 child = future.2 ∧
      (children worlds arrows C point value).holds ⟨future.1, child⟩) ↔
    (((behaviorCoalgebra worlds arrows).app point value.2).val.holds ⟨future.1, future.2.val.1.2⟩ ∧
      future.2.val.1.1 = B.map future.1.2 (change.app point value.1)) ∧
        future.2.val.2 = C.map future.1.2 value.1
  constructor
  · rintro ⟨child, same, admitted, supported⟩
    have behavioral := congrArg (fun pair : (pulledFamily worlds arrows B C change).obj future.1.1 => pair.val.1.2) same
    have parameterEq := congrArg (fun pair : (pulledFamily worlds arrows B C change).obj future.1.1 => pair.val.2) same
    have originalParameter := congrArg (fun pair : (pulledFamily worlds arrows B C change).obj future.1.1 => pair.val.1.1) same
    refine ⟨⟨?_, ?_⟩, parameterEq.symm.trans supported⟩
    · rw [← behavioral]
      exact admitted
    · exact originalParameter.symm.trans ((congrArg (change.app future.1.1) supported).trans
        (change.naturality future.1.2 value.1).symm)
  · rintro ⟨⟨admitted, _originalParameter⟩, supported⟩
    refine ⟨(future.2.val.2, future.2.val.1.2), ?_, admitted, supported⟩
    apply Subtype.ext
    exact Prod.ext (Prod.ext future.2.property.symm rfl) rfl

theorem backward_square : (pulledCoalgebra worlds arrows B C change).comp (imageHom (backward worlds arrows B C change)) =
    (backward worlds arrows B C change).comp (coalgebra worlds arrows C) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  apply Predicate.ext
  intro future
  change (∃ child : (pulledFamily worlds arrows B C change).obj future.1.1,
    (backward worlds arrows B C change).app future.1.1 child = future.2 ∧
      ((coalgebra worlds arrows B).app point value.val.1).val.holds ⟨future.1, child.val.1⟩ ∧
        child.val.2 = C.map future.1.2 value.val.2) ↔
    ((behaviorCoalgebra worlds arrows).app point value.val.1.2).val.holds ⟨future.1, future.2.2⟩ ∧
      future.2.1 = C.map future.1.2 value.val.2
  constructor
  · rintro ⟨child, same, ⟨admitted, _originalParameter⟩, supported⟩
    exact ⟨by rw [← congrArg Prod.snd same]; exact admitted,
      (congrArg Prod.fst same).symm.trans supported⟩
  · rintro ⟨admitted, supported⟩
    let child : (pulledFamily worlds arrows B C change).obj future.1.1 :=
      ⟨((change.app future.1.1 future.2.1, future.2.2), future.2.1), rfl⟩
    refine ⟨child, rfl, ⟨admitted, ?_⟩, supported⟩
    exact (congrArg (change.app future.1.1) supported).trans
      ((change.naturality future.1.2 value.val.2).symm.trans
        (congrArg (B.map future.1.2) value.property).symm)

theorem forward_indexed_square :
    (indexedCoalgebra worlds arrows C).comp (IndexedCoveredPower.image (parameter worlds arrows C) (pulledParameter worlds arrows B C change)
      (forward worlds arrows B C change) (forward_parameter worlds arrows B C change)) =
        (forward worlds arrows B C change).comp (pulledIndexedCoalgebra worlds arrows B C change) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext rfl (congrArg
    (fun operation : NaturalHom (family worlds arrows C) (CoveredFuturePowerFamilies.family (pulledFamily worlds arrows B C change)) =>
      operation.app point value) (forward_square worlds arrows B C change))

theorem backward_indexed_square :
    (pulledIndexedCoalgebra worlds arrows B C change).comp (IndexedCoveredPower.image (pulledParameter worlds arrows B C change) (parameter worlds arrows C)
      (backward worlds arrows B C change) (backward_parameter worlds arrows B C change)) =
        (backward worlds arrows B C change).comp (indexedCoalgebra worlds arrows C) := by
  apply NaturalHom.ext
  intro point value
  apply Subtype.ext
  exact Prod.ext rfl (congrArg
    (fun operation : NaturalHom (pulledFamily worlds arrows B C change) (CoveredFuturePowerFamilies.family (family worlds arrows C)) =>
      operation.app point value) (backward_square worlds arrows B C change))

def reindex : NaturalHom (family worlds arrows C) (family worlds arrows B) :=
  (forward worlds arrows B C change).comp (originalProjection worlds arrows B C change)

theorem reindex_value (point : D) (value : (family worlds arrows C).obj point) :
    (reindex worlds arrows B C change).app point value = (change.app point value.1, value.2) := rfl

theorem reindex_square : (coalgebra worlds arrows C).comp (imageHom (reindex worlds arrows B C change)) =
    (reindex worlds arrows B C change).comp (coalgebra worlds arrows B) :=
  ContextualSmallCoalgebraComparisons.compose_square (coalgebra worlds arrows C) (pulledCoalgebra worlds arrows B C change)
    (coalgebra worlds arrows B) (forward worlds arrows B C change) (originalProjection worlds arrows B C change)
    (forward_square worlds arrows B C change) (original_square worlds arrows B C change)

theorem reindex_parameter : (reindex worlds arrows B C change).comp (parameter worlds arrows B) = (parameter worlds arrows C).comp change := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_behavior : (reindex worlds arrows B C change).comp (behavior worlds arrows B) = behavior worlds arrows C := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_kernel (point : D) (left right : (family worlds arrows C).obj point) :
    (reindex worlds arrows B C change).app point left = (reindex worlds arrows B C change).app point right ↔
      change.app point left.1 = change.app point right.1 ∧ left.2 = right.2 :=
  ⟨fun same => ⟨congrArg (fun pair : (family worlds arrows B).obj point => pair.1) same,
      congrArg (fun pair : (family worlds arrows B).obj point => pair.2) same⟩,
    fun same => Prod.ext same.1 same.2⟩

theorem reindex_memberDecode :
    (reindex worlds arrows B C change).comp (memberDecode worlds arrows B) =
      memberDecode worlds arrows C := by
  apply NaturalHom.ext
  intro _ _
  rfl

def decodedReindex : NaturalHom (decodedFamily worlds arrows C) (decodedFamily worlds arrows B) where
  app point value := (change.app point value.1, value.2)
  naturality step value := Prod.ext (change.naturality step value.1) rfl

theorem decode_reindex :
    (decode worlds arrows C).comp (decodedReindex worlds arrows B C change) =
      (reindex worlds arrows B C change).comp (decode worlds arrows B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem encode_reindex :
    (encode worlds arrows C).comp (reindex worlds arrows B C change) =
      (decodedReindex worlds arrows B C change).comp (encode worlds arrows B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_identity : reindex worlds arrows B B (identityHom B) = identityHom (family worlds arrows B) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem reindex_composition {E : D ⥤ Type z} (next : NaturalHom E C) :
    (reindex worlds arrows C E next).comp (reindex worlds arrows B C change) = reindex worlds arrows B E (next.comp change) := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem whole_reindexed_section (term : (family worlds arrows C).sections) :
    (reindex worlds arrows B C change).mapSection term =
      (originalProjection worlds arrows B C change).mapSection ((forward worlds arrows B C change).mapSection term) := by
  apply Subtype.ext
  funext point
  rfl

theorem pulled_relative_separated (point : D) {left right : (pulledFamily worlds arrows B C change).obj point}
    (related : ContextualCoalgebraBisimulation.Bisimilar (pulledCoalgebra worlds arrows B C change) point left right)
    (sameBase : left.val.2 = right.val.2) : left = right := by
  have readingEq := relative_separated worlds arrows C point
    (ContextualCoalgebraBisimulation.bisimilar_preserved (pulledCoalgebra worlds arrows B C change)
      (backward worlds arrows B C change) (coalgebra worlds arrows C) (backward_square worlds arrows B C change) related) sameBase
  exact (forward_backward worlds arrows B C change point left).symm.trans
    ((congrArg ((forward worlds arrows B C change).app point) readingEq).trans
      (forward_backward worlds arrows B C change point right))

section EnumeratedSource

variable {A : D ⥤ Type z} (sourceParameter : NaturalHom A C)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def pulledEnumeratedReadout (receipts : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    NaturalHom A (pulledFamily worlds arrows B C change) :=
  (fromEnumerated worlds arrows C sourceParameter transition receipts).comp (forward worlds arrows B C change)

include sourceSquare in
theorem pulled_enumerated_square (receipts : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts)) =
        (pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts).comp
          (pulledCoalgebra worlds arrows B C change) :=
  ContextualSmallCoalgebraComparisons.compose_square
    (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra worlds arrows C)
    (pulledCoalgebra worlds arrows B C change)
    (fromEnumerated worlds arrows C sourceParameter transition receipts) (forward worlds arrows B C change)
    (pairReadout_square worlds arrows C sourceParameter transition sourceSquare
      (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
        (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts)
      (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_square worlds arrows A
        (IndexedCoalgebraBisimulation.original sourceParameter transition) receipts))
    (forward_square worlds arrows B C change)

theorem pulled_enumerated_parameter (receipts : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    (pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts).comp
      (pulledParameter worlds arrows B C change) = sourceParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

theorem pulled_enumerated_kernel (receipts : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val)
    (point : D) (first second : A.obj point) :
    (pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts).app point first =
      (pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts).app point second ↔
        IndexedCoalgebraBisimulation.Related sourceParameter transition point first second := by
  constructor
  · intro same
    exact (enumerated_kernel worlds arrows C sourceParameter transition receipts point first second).mp
      ((fibreEquiv worlds arrows B C change point).injective same)
  · intro related
    exact congrArg ((forward worlds arrows B C change).app point)
      ((enumerated_kernel worlds arrows C sourceParameter transition receipts point first second).mpr related)

include sourceSquare in
theorem unique_enumerated_pulled_map (receipts : ∀ point value,
    CoveredFuturePowerFamilies.Enumeration
      ((IndexedCoalgebraBisimulation.original sourceParameter transition).app point value).val) :
    ∃! operation : NaturalHom A (pulledFamily worlds arrows B C change),
      (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
        operation.comp (pulledCoalgebra worlds arrows B C change) ∧
          operation.comp (pulledParameter worlds arrows B C change) = sourceParameter := by
  let actual := pulledEnumeratedReadout worlds arrows B C change sourceParameter transition receipts
  have square := pulled_enumerated_square worlds arrows B C change sourceParameter transition sourceSquare receipts
  have base := pulled_enumerated_parameter worlds arrows B C change sourceParameter transition receipts
  refine ⟨actual, ⟨square, base⟩, ?_⟩
  intro candidate laws
  apply NaturalHom.ext
  intro point value
  apply pulled_relative_separated worlds arrows B C change point
  · exact ContextualCoalgebraBisimulation.greatest (pulledCoalgebra worlds arrows B C change)
      (ContextualSmallCoalgebraGenerators.mixed_image_isBisimulation
        (IndexedCoalgebraBisimulation.original sourceParameter transition) (pulledCoalgebra worlds arrows B C change)
        candidate actual laws.1 square) ⟨value, rfl, rfl⟩
  · exact (congrArg (fun operation : NaturalHom A C => operation.app point value) laws.2).trans
      (congrArg (fun operation : NaturalHom A C => operation.app point value) base).symm

end EnumeratedSource

section SmallSource

variable {A : D ⥤ Type u} (sourceParameter : NaturalHom A C)
variable (transition : NaturalHom A (IndexedCoveredPower.family sourceParameter))
variable (sourceSquare : transition.comp (IndexedCoveredPower.projection sourceParameter) = sourceParameter)

def pulledSmallReadout : NaturalHom A (pulledFamily worlds arrows B C change) :=
  (fromSmall worlds arrows C sourceParameter transition).comp (forward worlds arrows B C change)

include sourceSquare in
theorem pulled_small_square :
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp
      (imageHom (pulledSmallReadout worlds arrows B C change sourceParameter transition)) =
        (pulledSmallReadout worlds arrows B C change sourceParameter transition).comp (pulledCoalgebra worlds arrows B C change) :=
  ContextualSmallCoalgebraComparisons.compose_square
    (IndexedCoalgebraBisimulation.original sourceParameter transition) (coalgebra worlds arrows C)
    (pulledCoalgebra worlds arrows B C change) (fromSmall worlds arrows C sourceParameter transition) (forward worlds arrows B C change)
    (pairReadout_square worlds arrows C sourceParameter transition sourceSquare
      (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout worlds arrows A
        (IndexedCoalgebraBisimulation.original sourceParameter transition)
          (smallReceipts C sourceParameter transition))
      (ContextualSmallCoalgebraMaterialCoalgebra.enumeratedReadout_square worlds arrows A
        (IndexedCoalgebraBisimulation.original sourceParameter transition)
          (smallReceipts C sourceParameter transition)))
    (forward_square worlds arrows B C change)

theorem pulled_small_parameter :
    (pulledSmallReadout worlds arrows B C change sourceParameter transition).comp (pulledParameter worlds arrows B C change) =
      sourceParameter := by
  apply NaturalHom.ext
  intro _ _
  rfl

include sourceSquare in
theorem unique_small_pulled_map : ∃! operation : NaturalHom A (pulledFamily worlds arrows B C change),
    (IndexedCoalgebraBisimulation.original sourceParameter transition).comp (imageHom operation) =
      operation.comp (pulledCoalgebra worlds arrows B C change) ∧
        operation.comp (pulledParameter worlds arrows B C change) = sourceParameter := by
  let actual := pulledSmallReadout worlds arrows B C change sourceParameter transition
  have square := pulled_small_square worlds arrows B C change sourceParameter transition sourceSquare
  have base := pulled_small_parameter worlds arrows B C change sourceParameter transition
  refine ⟨actual, ⟨square, base⟩, ?_⟩
  intro candidate laws
  apply NaturalHom.ext
  intro point value
  apply pulled_relative_separated worlds arrows B C change point
  · exact ContextualCoalgebraBisimulation.greatest (pulledCoalgebra worlds arrows B C change)
      (ContextualSmallCoalgebraGenerators.mixed_image_isBisimulation
        (IndexedCoalgebraBisimulation.original sourceParameter transition) (pulledCoalgebra worlds arrows B C change)
        candidate actual laws.1 square) ⟨value, rfl, rfl⟩
  · exact (congrArg (fun operation : NaturalHom A C => operation.app point value) laws.2).trans
      (congrArg (fun operation : NaturalHom A C => operation.app point value) base).symm

end SmallSource

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualMaterialSliceRecipientBaseChange
