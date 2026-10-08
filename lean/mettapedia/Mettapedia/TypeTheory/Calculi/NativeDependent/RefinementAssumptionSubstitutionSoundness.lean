import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementStructuralSoundness

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
    Interprets model (.substitution (.assume context predicate) context TermExpr.var) := by
  rcases predicateInterpreted with ⟨Γ, φ, contextRead, predicateRead⟩
  exact ⟨Γ.assume φ, Γ, φ.ι,
    model.evaluateContext_assume context predicate Γ φ contextRead predicateRead,
    contextRead, (ModelSubstitution.weakenAssumption model Γ φ).evaluate⟩

theorem substitutionIntoAssumption_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate))
    (guardInterpreted : Interprets model (.entails source (predicate.substitute substitution))) :
    Interprets model (.substitution source (.assume target predicate) substitution) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases predicateInterpreted.predicateAt Δ targetRead with ⟨φ, predicateRead⟩
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  have pulled := model.evaluatePredicate_substitute stable predicate Γ Δ substitution modelMap φ predicateRead
  have guardRead := guardInterpreted.entailsAt Γ sourceRead
  have top : φ.preimage σ = ⊤ := Option.some.inj (pulled.symm.trans guardRead)
  have satisfies : ∀ world value, σ.app world value ∈ φ.obj world := by
    intro world value
    change value ∈ (φ.preimage σ).obj world
    rw [top]
    trivial
  let restricted := modelMap.intoAssumption φ satisfies
  exact ⟨Γ, Δ.assume φ, restricted.arrow, sourceRead,
    model.evaluateContext_assume target predicate Δ φ targetRead predicateRead, restricted.evaluate⟩

theorem substitutionLift_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (type : TypeExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (typeInterpreted : Interprets model (.type target type)) :
    Interprets model (.substitution (.snoc source (type.substitute substitution))
      (.snoc target type) (liftSubstitution substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases typeInterpreted.typeAt Δ targetRead with ⟨A, typeRead⟩
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  have pulled := model.evaluateType_substitute stable type Γ Δ substitution modelMap A typeRead
  let lifted := modelMap.lift stable A
  exact ⟨_, _, lifted.arrow,
    model.evaluateContext_snoc source (type.substitute substitution) Γ _ sourceRead pulled,
    model.evaluateContext_snoc target type Δ A targetRead typeRead, lifted.evaluate⟩

theorem substitutionAssumptionLift_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (substitution : Substitution S n k)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.substitution (.assume source (predicate.substitute substitution))
      (.assume target predicate) substitution) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases predicateInterpreted.predicateAt Δ targetRead with ⟨φ, predicateRead⟩
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  have pulled := model.evaluatePredicate_substitute stable predicate Γ Δ substitution modelMap φ predicateRead
  let lifted := modelMap.liftAssumption stable φ
  exact ⟨_, _, lifted.arrow,
    model.evaluateContext_assume source (predicate.substitute substitution) Γ _ sourceRead pulled,
    model.evaluateContext_assume target predicate Δ φ targetRead predicateRead, lifted.evaluate⟩

theorem substitutePredicate_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (predicate : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.predicate source (predicate.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases predicateInterpreted.predicateAt Δ targetRead with ⟨φ, predicateRead⟩
  exact ⟨Γ, φ.preimage σ, sourceRead,
    model.evaluatePredicate_substitute stable predicate Γ Δ substitution
      (ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead) φ predicateRead⟩

theorem substituteEntailment_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (predicate : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (entailmentInterpreted : Interprets model (.entails target predicate)) :
    Interprets model (.entails source (predicate.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  have evaluated := model.evaluatePredicate_substitute stable predicate Γ Δ substitution
    (ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead) ⊤
    (entailmentInterpreted.entailsAt Δ targetRead)
  exact ⟨Γ, sourceRead, evaluated⟩

theorem substitutePredicateEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (substitution : Substitution S n k)
    (first second : PropExpr S n)
    (substitutionInterpreted : Interprets model (.substitution source target substitution))
    (predicatesInterpreted : Interprets model (.predicateEq target first second)) :
    Interprets model (.predicateEq source (first.substitute substitution) (second.substitute substitution)) := by
  rcases substitutionInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, substitutionRead⟩
  rcases predicatesInterpreted with ⟨actual, φ, actualRead, firstRead, secondRead⟩
  cases Option.some.inj (actualRead.symm.trans targetRead)
  let modelMap := ModelSubstitution.ofEvaluated model Γ Δ substitution σ substitutionRead
  exact ⟨Γ, φ.preimage σ, sourceRead,
    model.evaluatePredicate_substitute stable first Γ Δ substitution modelMap φ firstRead,
    model.evaluatePredicate_substitute stable second Γ Δ substitution modelMap φ secondRead⟩

theorem predicateSubstitutionCongruence_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n)
    (first second : Substitution S n k) (predicate : PropExpr S n)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (predicateInterpreted : Interprets model (.predicate target predicate)) :
    Interprets model (.predicateEq source (predicate.substitute first) (predicate.substitute second)) := by
  rcases substitutionsInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  rcases predicateInterpreted.predicateAt Δ targetRead with ⟨φ, predicateRead⟩
  exact ⟨Γ, φ.preimage σ, sourceRead,
    model.evaluatePredicate_substitute stable predicate Γ Δ first
      (ModelSubstitution.ofEvaluated model Γ Δ first σ firstRead) φ predicateRead,
    model.evaluatePredicate_substitute stable predicate Γ Δ second
      (ModelSubstitution.ofEvaluated model Γ Δ second σ secondRead) φ predicateRead⟩

theorem substitutionIntoAssumptionEquality_sound (stable : StrictPiSubstitution model.products)
    (source : ContextExpr S k) (target : ContextExpr S n) (predicate : PropExpr S n)
    (first second : Substitution S n k)
    (substitutionsInterpreted : Interprets model (.substitutionEq source target first second))
    (predicateInterpreted : Interprets model (.predicate target predicate))
    (firstGuard : Interprets model (.entails source (predicate.substitute first)))
    (secondGuard : Interprets model (.entails source (predicate.substitute second))) :
    Interprets model (.substitutionEq source (.assume target predicate) first second) := by
  rcases substitutionsInterpreted with ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead, secondRead⟩
  have left := model.substitutionIntoAssumption_sound stable source target predicate first
    ⟨Γ, Δ, σ, sourceRead, targetRead, firstRead⟩ predicateInterpreted firstGuard
  have right := model.substitutionIntoAssumption_sound stable source target predicate second
    ⟨Γ, Δ, σ, sourceRead, targetRead, secondRead⟩ predicateInterpreted secondGuard
  rcases predicateInterpreted.predicateAt Δ targetRead with ⟨φ, predicateRead⟩
  have assumedRead := model.evaluateContext_assume target predicate Δ φ targetRead predicateRead
  rcases left.substitutionAt Γ (Δ.assume φ) sourceRead assumedRead with ⟨leftArrow, leftRead⟩
  rcases right.substitutionAt Γ (Δ.assume φ) sourceRead assumedRead with ⟨rightArrow, rightRead⟩
  have equal : leftArrow = rightArrow := by
    apply (Δ.assume φ).2.components_injective
    funext index
    have before := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp firstRead index
    have after := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp secondRead index
    have leftComponent := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp leftRead index
    have rightComponent := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp rightRead index
    have oldLeft := Option.some.inj (before.symm.trans leftComponent)
    have oldRight := Option.some.inj (after.symm.trans rightComponent)
    exact oldLeft.symm.trans oldRight
  cases equal
  exact ⟨Γ, Δ.assume φ, leftArrow, sourceRead, assumedRead, leftRead, rightRead⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
