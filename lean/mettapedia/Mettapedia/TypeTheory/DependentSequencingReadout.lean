import Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization
import Mettapedia.TypeTheory.WitnessRetainingDependentSequencing

/-!
# Readouts of effectful dependent sequencing

Effectful dependent sequencing has an unconditional result type: retain the
selected index together with its dependent result in a sigma type.  A common
result carrier can be used only after every fibre is identified with that
carrier.  This module studies the resulting readout through an arbitrary
answer effect.

At any fixed known index, mapping restoration followed by erasure is exact.
Globally, however, an answer effect whose singleton constructor is faithful
cannot repair the information lost by erasing two distinct indices.  The
effectful readout is split-surjective but non-injective, and therefore has no
global left-inverse reconstruction.

The result separates three obligations:

* sigma-retaining dependent sequencing is available for every answer effect;
* uniform result typing requires a fibrewise equivalence; and
* hiding the selected index is a lossy observation unless an independent
  restriction proves that the relevant index fibre is thin.

No evaluation strategy, concrete effect, or language calculus is selected.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DependentSequencingReadout

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect
open Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization
open Mettapedia.TypeTheory.WitnessRetainingDependentSequencing
open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

universe u

/-! ## Faithful singleton answers -/

/-- An answer effect faithfully embeds a single returned value.  This is
strictly weaker than requiring every effectful answer map to be faithful. -/
def SingletonFaithful (effect : AnswerEffect.{u}) : Prop :=
  forall (Value : Type u), Function.Injective (@effect.pure Value)

/-! ## Uniform effectful readout -/

/-- Forget the selected index from every effectful dependent answer after
identifying each fibre with one common carrier. -/
def eraseAnswers
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family) :
    effect.Carrier (Sigma Family) -> effect.Carrier representation.Carrier :=
  effect.map representation.eraseIndex

/-- Restore every common-carrier answer at one explicitly selected index. -/
def restoreAnswersAt
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (index : Index) :
    effect.Carrier representation.Carrier -> effect.Carrier (Sigma Family) :=
  effect.map (representation.restoreAt index)

/-- At a known index, restoration followed by erasure is exact through every
answer effect. -/
theorem eraseAnswers_restoreAnswersAt
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (index : Index) (answers : effect.Carrier representation.Carrier) :
    eraseAnswers effect representation
        (restoreAnswersAt effect representation index answers) = answers := by
  unfold eraseAnswers restoreAnswersAt
  rw [AnswerEffect.map_comp]
  have pointwise :
      (fun value =>
        representation.eraseIndex (representation.restoreAt index value)) =
        (fun value => value) := by
    funext value
    exact representation.eraseIndex_restoreAt index value
  rw [pointwise, AnswerEffect.map_id]

/-- Choosing any index gives a section, so effectful index erasure is always
surjective when the index type is inhabited. -/
theorem eraseAnswers_surjective
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (index : Index) :
    Function.Surjective (eraseAnswers effect representation) := by
  intro answers
  exact
    ⟨restoreAnswersAt effect representation index answers,
      eraseAnswers_restoreAnswersAt effect representation index answers⟩

/-- A faithful singleton constructor exposes the collision caused by erasing
two distinct selected indices.  No amount of lawful answer-effect structure
repairs that lost coordinate. -/
theorem eraseAnswers_not_injective
    (effect : AnswerEffect.{u})
    (singletonFaithful : SingletonFaithful effect)
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    {leftIndex rightIndex : Index} (different : leftIndex ≠ rightIndex)
    (value : representation.Carrier) :
    Not (Function.Injective (eraseAnswers effect representation)) := by
  intro injective
  let leftValue : Sigma Family := representation.restoreAt leftIndex value
  let rightValue : Sigma Family := representation.restoreAt rightIndex value
  have sameErasure : representation.eraseIndex leftValue =
      representation.eraseIndex rightValue := by
    simp [leftValue, rightValue]
  have sameMapped :
      eraseAnswers effect representation (effect.pure leftValue) =
        eraseAnswers effect representation (effect.pure rightValue) := by
    simp [eraseAnswers, sameErasure]
  have sameSingletons := injective sameMapped
  have sameValues : leftValue = rightValue :=
    singletonFaithful (Sigma Family) sameSingletons
  exact different (congrArg Sigma.fst sameValues)

/-- Consequently there is no reconstruction which is a left inverse to the
effectful index erasure on all answers. -/
theorem no_global_answer_reconstruction
    (effect : AnswerEffect.{u})
    (singletonFaithful : SingletonFaithful effect)
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    {leftIndex rightIndex : Index} (different : leftIndex ≠ rightIndex)
    (value : representation.Carrier) :
    Not (Exists fun restore :
        effect.Carrier representation.Carrier ->
          effect.Carrier (Sigma Family) =>
      Function.LeftInverse restore (eraseAnswers effect representation)) := by
  rintro ⟨restore, reconstructs⟩
  exact
    (eraseAnswers_not_injective effect singletonFaithful representation
      different value) reconstructs.injective

/-! ## Sequencing directly into the uniform readout -/

/-- Sequence a dependent continuation and then expose only its common fibre
carrier.  The definition makes the loss explicit by factoring through the
sigma-retaining operation. -/
def bindUniform
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (indices : effect.Carrier Index)
    (next : (index : Index) -> effect.Carrier (Family index)) :
    effect.Carrier representation.Carrier :=
  eraseAnswers effect representation (bindSigma effect indices next)

/-- Factoring through the retained sigma is extensionally the same as mapping
the selected fibre equivalence in each continuation.  The former expression
keeps the information boundary visible. -/
theorem bindUniform_eq_bind
    (effect : AnswerEffect.{u})
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (indices : effect.Carrier Index)
    (next : (index : Index) -> effect.Carrier (Family index)) :
    bindUniform effect representation indices next =
      effect.bind indices fun index =>
        effect.map (representation.identify index) (next index) := by
  unfold bindUniform eraseAnswers bindSigma AnswerEffect.map
  rw [effect.bind_assoc]
  congr 1
  funext index
  rw [effect.bind_assoc]
  congr 1
  funext value
  exact effect.pure_bind (Sigma.mk index value) _

/-- Every operation-preserving map of answer effects commutes with the
uniform dependent-result readout. -/
theorem morphism_map_eraseAnswers
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (answers : source.Carrier (Sigma Family)) :
    morphism.map (eraseAnswers source representation answers) =
      eraseAnswers target representation (morphism.map answers) := by
  exact
    AnswerEffect.Morphism.map_natural morphism
      representation.eraseIndex answers

/-- Operation-preserving maps of answer effects also commute with the complete
dependent-sequencing/readout composite.  An order- or multiplicity-forgetting
map remains explicit after the dependent witness boundary. -/
theorem morphism_map_bindUniform
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    {Index : Type u} {Family : Index -> Type u}
    (representation : UniformFibreRepresentation Family)
    (indices : source.Carrier Index)
    (next : (index : Index) -> source.Carrier (Family index)) :
    morphism.map (bindUniform source representation indices next) =
      bindUniform target representation (morphism.map indices)
        (fun index => morphism.map (next index)) := by
  unfold bindUniform
  rw [morphism_map_eraseAnswers, morphism_map_bindSigma]

/-! ## Positive and negative controls -/

namespace Canary

/-- Ordered answer lists faithfully embed singleton results. -/
theorem list_singletonFaithful : SingletonFaithful listEffect := by
  intro Value left right equalSingletons
  change [left] = [right] at equalSingletons
  injection equalSingletons

/-- A fixed Boolean index can be restored and erased exactly for arbitrary
ordered answer lists. -/
theorem constant_list_fixed_index_roundtrip (answers : List PUnit) :
    eraseAnswers listEffect (constantRepresentation Bool PUnit)
        (restoreAnswersAt listEffect (constantRepresentation Bool PUnit)
          false answers) = answers :=
  eraseAnswers_restoreAnswersAt listEffect
    (constantRepresentation Bool PUnit) false answers

/-- The same readout is globally split-surjective but not faithful because it
identifies answers selected at `false` and `true`. -/
theorem constant_list_readout_split_but_not_faithful :
    Function.Surjective
        (eraseAnswers listEffect (constantRepresentation Bool PUnit)) /\
      Not (Function.Injective
        (eraseAnswers listEffect (constantRepresentation Bool PUnit))) :=
  ⟨eraseAnswers_surjective listEffect
      (constantRepresentation Bool PUnit) false,
    eraseAnswers_not_injective listEffect list_singletonFaithful
      (constantRepresentation Bool PUnit) Bool.false_ne_true PUnit.unit⟩

/-- A genuinely varying family fails before index erasure: there is no exact
common fibre carrier from which to define `bindUniform`. -/
theorem varying_family_rejects_uniform_result :
    Not (Nonempty (UniformFibreRepresentation varyingBoolFamily)) :=
  varying_family_has_no_uniform_representation

/-- Paired value/computation boundary: uniform constant fibres permit a split
readout but not faithful witness hiding, while a genuinely varying family has
no uniform readout at all. -/
theorem dependent_result_readout_boundary :
    (Function.Surjective
        (eraseAnswers listEffect (constantRepresentation Bool PUnit)) /\
      Not (Function.Injective
        (eraseAnswers listEffect (constantRepresentation Bool PUnit)))) /\
      Not (Nonempty (UniformFibreRepresentation varyingBoolFamily)) :=
  ⟨constant_list_readout_split_but_not_faithful,
    varying_family_rejects_uniform_result⟩

end Canary

#print axioms eraseAnswers_restoreAnswersAt
#print axioms eraseAnswers_surjective
#print axioms eraseAnswers_not_injective
#print axioms no_global_answer_reconstruction
#print axioms bindUniform_eq_bind
#print axioms morphism_map_eraseAnswers
#print axioms morphism_map_bindUniform
#print axioms Canary.constant_list_readout_split_but_not_faithful
#print axioms Canary.dependent_result_readout_boundary

end Mettapedia.TypeTheory.DependentSequencingReadout
