import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementStructuralSoundness
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractAssumptionSubstitutionSoundness

/-!
# Substitution through actual predicate assumptions

Maps into assumptions factor through their satisfying subobjects. Lifting an
assumption uses its independently computed inverse image; each data component
retains its actual section. Predicate and entailment substitution are derived
from the mutual evaluator theorem, including future-sensitive quantifiers.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory NativeLocalTypeFormers
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C] {n k : Nat}

namespace ModelSubstitution

set_option backward.isDefEq.respectTransparency false in
def weakenAssumption (model : ModelData S C) (Γ : Scope C n) (φ : Subfunctor Γ.1) :
    ModelSubstitution model (Γ.assume φ) Γ TermExpr.var where
  arrow := φ.ι
  readout _ := rfl

set_option backward.isDefEq.respectTransparency false in
def intoAssumption {model : ModelData S C} {Γ : Scope C k} {Δ : Scope C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (φ : Subfunctor Δ.1)
    (satisfies : ∀ world value, modelMap.arrow.app world value ∈ φ.obj world) :
    ModelSubstitution model Γ (Δ.assume φ) substitution where
  arrow := assumptionMap φ modelMap.arrow satisfies
  readout index := by
    rw [ScopeData.lookup_assume, ← Value.substitute_composition]
    change model.evaluateTerm Γ (substitution index) =
      some (Value.substitute (K := (NativeModel C).toCwf) (Δ.2.lookup index)
        (assumptionMap φ modelMap.arrow satisfies ≫ φ.ι))
    rw [assumptionMap_inclusion]
    exact modelMap.readout index

set_option backward.isDefEq.respectTransparency false in
def liftAssumption {model : ModelData S C} {Γ : Scope C k} {Δ : Scope C n}
    {substitution : Substitution S n k} (modelMap : ModelSubstitution model Γ Δ substitution)
    (stable : StrictPiSubstitution model.products) (φ : Subfunctor Δ.1) :
    ModelSubstitution model (Γ.assume (φ.preimage modelMap.arrow)) (Δ.assume φ) substitution where
  arrow := assumptionMap φ ((φ.preimage modelMap.arrow).ι ≫ modelMap.arrow)
    (fun _world value => value.property)
  readout index := by
    rw [ScopeData.lookup_assume, ← Value.substitute_composition]
    change model.evaluateTerm (Γ.assume (φ.preimage modelMap.arrow)) (substitution index) =
      some (Value.substitute (K := (NativeModel C).toCwf) (Δ.2.lookup index)
        (assumptionMap φ ((φ.preimage modelMap.arrow).ι ≫ modelMap.arrow)
          (fun _world value => value.property) ≫ φ.ι))
    rw [assumptionMap_inclusion]
    change model.evaluateTerm (Γ.assume (φ.preimage modelMap.arrow)) (substitution index) =
      some (Value.substitute (K := (NativeModel C).toCwf) (Δ.2.lookup index)
        ((NativeModel C).toCwf.compS modelMap.arrow (φ.preimage modelMap.arrow).ι))
    rw [Value.substitute_composition]
    exact model.evaluateTerm_restrict stable Γ (φ.preimage modelMap.arrow)
      (substitution index) _ (modelMap.readout index)

end ModelSubstitution

namespace ModelData

variable (model : ModelData S C)

theorem substitutionWeakenAssumption_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (predicateInterpreted : Interprets model (.predicate context predicate)) :
    Interprets model (.substitution (.assume context predicate) context TermExpr.var) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionWeakenAssumption_sound model.toAbstract context predicate
      predicateInterpreted.toAbstract)

theorem substitutionIntoAssumption_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate))
    (guardInterpreted : Interprets model (.entails source (predicate.substitute substitution))) :
    Interprets model (.substitution source (.assume target predicate) substitution) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionIntoAssumption_sound model.toAbstract (model.stable_toAbstract stable)
      source target predicate substitution substitutionInterpreted.toAbstract
      predicateInterpreted.toAbstract guardInterpreted.toAbstract)

theorem substitutionLift_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (type : TypeExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.substitution (.snoc source (type.substitute substitution))
      (.snoc target type) (liftSubstitution substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionLift_sound model.toAbstract (model.stable_toAbstract stable) source
      target type substitution substitutionInterpreted.toAbstract typeInterpreted.toAbstract)

theorem substitutionAssumptionLift_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.substitution (.assume source (predicate.substitute substitution))
      (.assume target predicate) substitution) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionAssumptionLift_sound model.toAbstract (model.stable_toAbstract stable)
      source target predicate substitution substitutionInterpreted.toAbstract
      predicateInterpreted.toAbstract)

theorem substitutePredicate_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (predicate : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.predicate source (predicate.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutePredicate_sound model.toAbstract (model.stable_toAbstract stable) source
      target substitution predicate substitutionInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem substituteEntailment_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (predicate : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (entailmentInterpreted : Interprets model (.entails target predicate)) :
    Interprets model (.entails source (predicate.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substituteEntailment_sound model.toAbstract (model.stable_toAbstract stable)
      source target substitution predicate substitutionInterpreted.toAbstract
      entailmentInterpreted.toAbstract)

theorem substitutePredicateEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (first second : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicatesInterpreted : Interprets model (.predicateEq target first second)) :
    Interprets model (.predicateEq source (first.substitute substitution) (second.substitute substitution)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutePredicateEquality_sound model.toAbstract
      (model.stable_toAbstract stable) source target substitution first second
      substitutionInterpreted.toAbstract predicatesInterpreted.toAbstract)

theorem predicateSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n)
    (first second : Substitution S n k) (predicate : PropExpr S n)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.predicateEq source (predicate.substitute first) (predicate.substitute second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicateSubstitutionCongruence_sound model.toAbstract
      (model.stable_toAbstract stable) source target first second predicate
      substitutionsInterpreted.toAbstract predicateInterpreted.toAbstract)

theorem substitutionIntoAssumptionEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (first second : Substitution S n k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (predicateInterpreted : Interprets model (.predicate target predicate))
    (firstGuard : Interprets model (.entails source (predicate.substitute first)))
    (secondGuard : Interprets model (.entails source (predicate.substitute second))) :
    Interprets model (.substitutionEq source (.assume target predicate) first second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.substitutionIntoAssumptionEquality_sound model.toAbstract
      (model.stable_toAbstract stable) source target predicate first second
      substitutionsInterpreted.toAbstract predicateInterpreted.toAbstract firstGuard.toAbstract
      secondGuard.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
