import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Witness-retaining dependent sequencing

An effectful computation may select a value on which the type of its next
result depends.  There is a representation-independent safe target for this
sequencing: retain the selected value together with the dependent result in a
sigma type.

For any lawful answer effect, `bindSigma` sequences an effectful source with
a family of effectful continuations and returns `Carrier (Sigma Family)`.
It needs no assumption that the family is constant.  The construction
commutes with every answer-effect morphism, so order- or multiplicity-forgetting
readouts remain explicit downstream maps rather than hidden typing rules.

Erasing the selected index is a separate operation.  A bidirectional
identification of every fibre with one common carrier is required even to
erase fibre values uniformly without loss inside each fibre.  Such a
uniformization does not exist for the genuinely varying Boolean family, and
even when it does exist, erasing the index is non-injective as soon as two
different indices are inhabited.

This is the conservative value/computation boundary: general dependent
sequencing retains a sigma witness.  Any stronger dependent Kleisli operation
which hides that witness owes an effect-specific preservation and
reconstruction theorem.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u v

/-! ## The generic sigma-retaining operation -/

/-- Sequence an effectful index with an index-dependent continuation while
retaining the selected index in the result. -/
def bindSigma (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index → Type u}
    (indices : effect.Carrier Index)
    (next : (index : Index) → effect.Carrier (Family index)) :
    effect.Carrier (Sigma Family) :=
  effect.bind indices fun index =>
    effect.map (Sigma.mk index) (next index)

/-- A pure selected index reduces to the corresponding mapped continuation. -/
theorem bindSigma_pure
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index → Type u}
    (index : Index)
    (next : (index : Index) → effect.Carrier (Family index)) :
    bindSigma effect (effect.pure index) next =
      effect.map (Sigma.mk index) (next index) := by
  exact effect.pure_bind index _

/-- No selected index yields no dependent result. -/
theorem bindSigma_empty
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index → Type u}
    (next : (index : Index) → effect.Carrier (Family index)) :
    bindSigma effect (effect.empty : effect.Carrier Index) next =
      (effect.empty : effect.Carrier (Sigma Family)) := by
  exact effect.empty_bind _

/-- Sigma-retaining sequencing distributes over outer alternative choice.
This law preserves the effect's own order and multiplicity discipline. -/
theorem bindSigma_choice
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index → Type u}
    (left right : effect.Carrier Index)
    (next : (index : Index) → effect.Carrier (Family index)) :
    bindSigma effect (effect.choice left right) next =
      effect.choice (bindSigma effect left next)
        (bindSigma effect right next) := by
  exact effect.choice_bind left right _

/-- Every operation-preserving map of answer effects commutes with the
sigma-retaining dependent sequencing operation. -/
theorem morphism_map_bindSigma
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    {Index : Type u} {Family : Index → Type u}
    (indices : source.Carrier Index)
    (next : (index : Index) → source.Carrier (Family index)) :
    morphism.map (bindSigma source indices next) =
      bindSigma target (morphism.map indices)
        (fun index => morphism.map (next index)) := by
  unfold bindSigma AnswerEffect.map
  rw [morphism.map_bind]
  congr 1
  funext index
  rw [morphism.map_bind]
  congr 1
  funext value
  exact morphism.map_pure (⟨index, value⟩ : Sigma Family)

/-! ## Uniform fibre representations and the cost of hiding the index -/

/-- A common carrier which represents every fibre bidirectionally.  This is
stronger than a one-way readout because exact dependent values must be
recoverable at each known index. -/
structure UniformFibreRepresentation
    {Index : Type u} (Family : Index → Type v) where
  Carrier : Type v
  identify : (index : Index) → Family index ≃ Carrier

namespace UniformFibreRepresentation

variable {Index : Type u} {Family : Index → Type v}

/-- Forget the selected index after identifying its fibre with the common
carrier. -/
def eraseIndex (representation : UniformFibreRepresentation Family) :
    Sigma Family → representation.Carrier
  | ⟨index, value⟩ => representation.identify index value

/-- At a known index, a common-carrier value can be restored to the sigma
type. -/
def restoreAt (representation : UniformFibreRepresentation Family)
    (index : Index) : representation.Carrier → Sigma Family :=
  fun value => ⟨index, (representation.identify index).symm value⟩

/-- Erasing after restoration at a selected index is exact. -/
@[simp] theorem eraseIndex_restoreAt
    (representation : UniformFibreRepresentation Family)
    (index : Index) (value : representation.Carrier) :
    representation.eraseIndex (representation.restoreAt index value) = value := by
  exact (representation.identify index).apply_symm_apply value

/-- Even a bidirectional uniform fibre representation cannot reconstruct the
selected index.  Two different indices carrying the same common value collide
under index erasure. -/
theorem eraseIndex_not_injective
    (representation : UniformFibreRepresentation Family)
    {leftIndex rightIndex : Index} (different : leftIndex ≠ rightIndex)
    (value : representation.Carrier) :
    ¬ Function.Injective representation.eraseIndex := by
  intro injective
  let left : Sigma Family := representation.restoreAt leftIndex value
  let right : Sigma Family := representation.restoreAt rightIndex value
  have sameErasure : representation.eraseIndex left =
      representation.eraseIndex right := by
    simp [left, right]
  have sameSigma : left = right := injective sameErasure
  exact different (congrArg Sigma.fst sameSigma)

/-- Consequently no global reconstruction can be a left inverse to index
erasure when two indices are available. -/
theorem no_global_reconstruction
    (representation : UniformFibreRepresentation Family)
    {leftIndex rightIndex : Index} (different : leftIndex ≠ rightIndex)
    (value : representation.Carrier) :
    ¬ ∃ restore : representation.Carrier → Sigma Family,
      ∀ dependentValue,
        restore (representation.eraseIndex dependentValue) = dependentValue := by
  rintro ⟨restore, restores⟩
  apply representation.eraseIndex_not_injective different value
  intro left right sameErasure
  exact (restores left).symm.trans ((congrArg restore sameErasure).trans
    (restores right))

end UniformFibreRepresentation

/-! ## Constant and varying controls -/

/-- Constant families admit the expected uniform representation. -/
def constantRepresentation (Index : Type u) (Value : Type v) :
    UniformFibreRepresentation (fun _ : Index => Value) where
  Carrier := Value
  identify _ := Equiv.refl Value

/-- Nevertheless, erasing the Boolean index of a constant family is lossy. -/
theorem constant_family_index_erasure_lossy :
    ¬ Function.Injective
      (constantRepresentation Bool PUnit).eraseIndex := by
  exact
    (constantRepresentation Bool PUnit).eraseIndex_not_injective
      Bool.false_ne_true PUnit.unit

/-- The genuinely varying Boolean family has no common exact fibre
representation at all. -/
theorem varying_family_has_no_uniform_representation :
    ¬ Nonempty (UniformFibreRepresentation varyingBoolFamily) := by
  rintro ⟨representation⟩
  apply varyingBoolFamily_not_constant
  exact ⟨representation.Carrier,
    fun index => ⟨representation.identify index⟩⟩

/-! ## Executable choice controls -/

/-- A dependent continuation whose false fibre contributes one value and
whose true fibre contributes two. -/
def varyingListAnswers :
    (index : Bool) → List (varyingBoolFamily index)
  | false => [PUnit.unit]
  | true => [false, true]

/-- Ordered choice followed by dependent sequencing retains the selected
index beside every result. -/
def varyingListResult : List (Sigma varyingBoolFamily) :=
  bindSigma listEffect [false, true] varyingListAnswers

/-- Positive control: the exact selected-index chronology remains visible. -/
theorem varyingListResult_indices :
    varyingListResult.map Sigma.fst = [false, true, true] := by
  rfl

/-- The same dependent sequence commutes with the canonical order-forgetting
map from lists to occurrence bags. -/
theorem varyingList_to_bag_natural :
    listToBag.map varyingListResult =
      bindSigma bagEffect (listToBag.map ([false, true] : List Bool))
        (fun index => listToBag.map (varyingListAnswers index)) := by
  exact morphism_map_bindSigma
    listToBag ([false, true] : List Bool) varyingListAnswers

/-- Naturality does not make the order-forgetting morphism faithful.  The
dependent sequencing law and the retained-information law are separate. -/
theorem dependent_sequencing_does_not_make_listToBag_faithful :
    (listToBag.map varyingListResult =
      bindSigma bagEffect (listToBag.map ([false, true] : List Bool))
        (fun index => listToBag.map (varyingListAnswers index))) ∧
      ¬ listToBag.{0}.Faithful :=
  ⟨varyingList_to_bag_natural, listToBag_not_faithful⟩

/-! ## Axiom audit -/

#print axioms bindSigma_pure
#print axioms bindSigma_choice
#print axioms morphism_map_bindSigma
#print axioms UniformFibreRepresentation.eraseIndex_not_injective
#print axioms UniformFibreRepresentation.no_global_reconstruction
#print axioms constant_family_index_erasure_lossy
#print axioms varying_family_has_no_uniform_representation
#print axioms varyingListResult_indices
#print axioms varyingList_to_bag_natural
#print axioms dependent_sequencing_does_not_make_listToBag_faithful

end Mettapedia.TypeTheory.WitnessRetainingDependentSequencing
