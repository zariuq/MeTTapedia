import Mettapedia.GSLT.Dynamics.AnswerEffect
import Mettapedia.TypeTheory.DependentFamilyObserverFactorization

/-!
# Effectful dependent families over observations

Every answer effect acts functorially on equivalences of result types.
Consequently, a dependent family which factors through an observation still
factors after applying the answer-effect carrier pointwise.  The same holds
for dependent products and sums assembled by the displayed factorization
laws.

This is a preservation theorem, not a reflection theorem.  Applying an effect
may change which type distinctions remain observable, and an
operation-preserving morphism of answer effects need not be faithful.  The
negative controls retain both facts explicitly.

No evaluation order, multiplicity policy, state semantics, or concrete
language calculus is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization

open Mettapedia.GSLT.Dynamics.AnswerEffects
open Mettapedia.TypeTheory.DependentFamilyObserverFactorization

universe u uSource uTarget

namespace AnswerEffect

/-- Mapping the identity function changes no answers. -/
@[simp] theorem map_id (effect : AnswerEffect.{u})
    {Alpha : Type u} (answers : effect.Carrier Alpha) :
    effect.map (fun value => value) answers = answers := by
  exact effect.bind_pure answers

/-- Answer-effect mapping preserves composition. -/
theorem map_comp (effect : AnswerEffect.{u})
    {Alpha Beta Gamma : Type u}
    (first : Alpha → Beta) (second : Beta → Gamma)
    (answers : effect.Carrier Alpha) :
    effect.map second (effect.map first answers) =
      effect.map (fun value => second (first value)) answers := by
  unfold Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect.map
  rw [effect.bind_assoc]
  congr 1
  funext value
  exact effect.pure_bind (first value) _

/-- Every equivalence of answer types induces an equivalence of effectful
answer carriers. -/
def mapEquiv (effect : AnswerEffect.{u})
    {Alpha Beta : Type u} (equivalence : Alpha ≃ Beta) :
    effect.Carrier Alpha ≃ effect.Carrier Beta where
  toFun := effect.map equivalence
  invFun := effect.map equivalence.symm
  left_inv := by
    intro answers
    rw [map_comp effect]
    have functionEqual :
        (fun value => equivalence.symm (equivalence value)) =
          (fun value => value) := by
      funext value
      exact equivalence.symm_apply_apply value
    rw [functionEqual, map_id effect]
  right_inv := by
    intro answers
    rw [map_comp effect]
    have functionEqual :
        (fun value => equivalence (equivalence.symm value)) =
          (fun value => value) := by
      funext value
      exact equivalence.apply_symm_apply value
    rw [functionEqual, map_id effect]

end AnswerEffect

namespace AnswerEffect.Morphism

/-- Every operation-preserving answer-effect morphism is natural with respect
to ordinary answer mapping. -/
theorem map_natural
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    {Alpha Beta : Type u} (function : Alpha → Beta)
    (answers : source.Carrier Alpha) :
    morphism.map (source.map function answers) =
      target.map function (morphism.map answers) := by
  unfold Mettapedia.GSLT.Dynamics.AnswerEffects.AnswerEffect.map
  rw [morphism.map_bind]
  congr 1
  funext value
  exact morphism.map_pure (function value)

/-- Naturality applies in particular to transport along type
equivalences. -/
theorem mapEquiv_natural
    {source target : AnswerEffect.{u}}
    (morphism : AnswerEffect.Morphism source target)
    {Alpha Beta : Type u} (equivalence : Alpha ≃ Beta)
    (answers : source.Carrier Alpha) :
    morphism.map ((AnswerEffect.mapEquiv source equivalence) answers) =
      (AnswerEffect.mapEquiv target equivalence) (morphism.map answers) :=
  map_natural morphism equivalence answers

end AnswerEffect.Morphism

namespace FamilyFactorization

variable {Source : Type uSource} {Target : Type uTarget}
variable {observe : Source → Target} {family : Source → Type u}

/-- Apply an answer effect pointwise to a factorizing dependent family. -/
def throughAnswerEffect
    (factorization : FamilyFactorization observe family)
    (effect : AnswerEffect.{u}) :
    FamilyFactorization observe
      (fun source => effect.Carrier (family source)) where
  targetFamily := fun target =>
    effect.Carrier (factorization.targetFamily target)
  identify := fun source =>
    AnswerEffect.mapEquiv effect (factorization.identify source)

/-- Dependent sums assembled from compatible displayed families continue to
factor after applying any answer effect. -/
def dependentSigmaThroughAnswerEffect
    {dependentFamily : Sigma family → Type u}
    (base : FamilyFactorization observe family)
    (dependent : FamilyFactorization base.totalObservation dependentFamily)
    (effect : AnswerEffect.{u}) :
    FamilyFactorization observe
      (fun source => effect.Carrier
        (Sigma fun value : family source =>
          dependentFamily ⟨source, value⟩)) :=
  throughAnswerEffect (base.dependentSigma dependent) effect

/-- The parallel closure statement for dependent products. -/
def dependentPiThroughAnswerEffect
    {dependentFamily : Sigma family → Type u}
    (base : FamilyFactorization observe family)
    (dependent : FamilyFactorization base.totalObservation dependentFamily)
    (effect : AnswerEffect.{u}) :
    FamilyFactorization observe
      (fun source => effect.Carrier
        (forall value : family source,
          dependentFamily ⟨source, value⟩)) :=
  throughAnswerEffect (base.dependentPi dependent) effect

end FamilyFactorization

/-! ## Positive and negative controls -/

namespace Canary

/-- A coarse observation under which a constant Boolean family factors. -/
def coarseBool : Bool → PUnit.{1} := fun _ => PUnit.unit

def constantBool :
    FamilyFactorization coarseBool (fun _ => Bool) :=
  FamilyFactorization.constant coarseBool Bool

/-- Positive control: ordered-list computations of the constant family still
factor through the coarse observation. -/
def listConstantFactors :
    FamilyFactorization coarseBool (fun _ => List Bool) :=
  FamilyFactorization.throughAnswerEffect constantBool listEffect

/-- A family whose finite-support carriers have different cardinalities. -/
def varyingFinite : Bool → Type
  | false => Empty
  | true => PUnit

theorem finset_empty_not_equiv_finset_unit :
    ¬ Nonempty (Finset Empty ≃ Finset PUnit) := by
  rintro ⟨equivalence⟩
  have equalCardinality := Fintype.card_congr equivalence
  simp at equalCardinality

/-- Applying an answer effect does not automatically make every varying
family factor: finite support still distinguishes the empty and singleton
answer types. -/
theorem supportVarying_does_not_factor :
    ¬ Nonempty
      (FamilyFactorization coarseBool
        (fun index => supportEffect.Carrier (varyingFinite index))) := by
  apply FamilyFactorization.not_nonempty_of_nonEquivalent_fibres
    (left := false) (right := true) rfl
  simpa [varyingFinite, supportEffect] using
    finset_empty_not_equiv_finset_unit

/-- Operation preservation and naturality do not imply faithfulness: the
canonical list-to-bag morphism commutes with all answer maps while forgetting
enumeration order. -/
theorem listToBag_natural_but_not_faithful :
    (∀ {Alpha Beta : Type} (function : Alpha → Beta)
        (answers : List Alpha),
      listToBag.map (listEffect.map function answers) =
        bagEffect.map function (listToBag.map answers)) ∧
      ¬ listToBag.{0}.Faithful := by
  constructor
  · intro Alpha Beta function answers
    exact AnswerEffect.Morphism.map_natural listToBag function answers
  · exact listToBag_not_faithful

/-- Paired effectful boundary: compatible fibres lift through an effect, but
an incompatible finite-support family remains obstructed. -/
theorem effectful_family_factorization_boundary :
    Nonempty
        (FamilyFactorization coarseBool
          (fun _index : Bool => List Bool)) ∧
      ¬ Nonempty
        (FamilyFactorization coarseBool
          (fun index => supportEffect.Carrier (varyingFinite index))) :=
  ⟨⟨listConstantFactors⟩, supportVarying_does_not_factor⟩

end Canary

#print axioms AnswerEffect.map_id
#print axioms AnswerEffect.map_comp
#print axioms AnswerEffect.mapEquiv
#print axioms AnswerEffect.Morphism.map_natural
#print axioms FamilyFactorization.throughAnswerEffect
#print axioms FamilyFactorization.dependentSigmaThroughAnswerEffect
#print axioms FamilyFactorization.dependentPiThroughAnswerEffect
#print axioms Canary.supportVarying_does_not_factor
#print axioms Canary.listToBag_natural_but_not_faithful
#print axioms Canary.effectful_family_factorization_boundary

end Mettapedia.TypeTheory.EffectfulFamilyObserverFactorization
