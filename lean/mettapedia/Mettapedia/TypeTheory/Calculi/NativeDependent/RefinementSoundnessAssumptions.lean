import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundnessLogic
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingEvaluation
import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic

/-!
# Generated entailment in actual satisfying contexts

Weakening and assumption restriction follow from the full authored renaming
calculation. Hypothesis positions traverse the actual mixed context. Logical
elimination retains its restricted branch contexts and image-coverage premise.
No conditional proof is read as a section over an unrestricted context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory NativeLocalTypeFormers PresheafNativePropositionReadout
open Mettapedia.GSLT.Topos
open Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open External (bindResult_eq_some_iff)

universe u v
variable {S : Symbols.{v}} {C : Type u} [Category.{u} C]

namespace ModelData

variable (model : ModelData S C) (stable : StrictPiSubstitution model.products) {n : Nat}

include stable

theorem predicateAssumptionRead (Γ : Scope C n) (assumption : Subfunctor Γ.1)
    (predicate : PropExpr S n) (φ : Subfunctor Γ.1)
    (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluatePredicate (Γ.assume assumption) predicate = some (φ.preimage assumption.ι) := by
  simpa only [PropExpr.rename_identity, ModelRenaming.restrict] using model.evaluatePredicate_rename stable predicate
    (Γ.assume assumption) Γ id (ModelRenaming.restrict Γ assumption) φ predicateRead

theorem predicateVariableRead (Γ : Scope C n) (A : NativeType Γ.1)
    (predicate : PropExpr S n) (φ : Subfunctor Γ.1)
    (predicateRead : model.evaluatePredicate Γ predicate = some φ) :
    model.evaluatePredicate (Γ.snoc A) (predicate.rename Fin.succ) =
      some (φ.preimage ((NativeModel C).toCwf.wk A)) :=
  model.evaluatePredicate_rename stable predicate (Γ.snoc A) Γ Fin.succ
    (ModelRenaming.weaken Γ A) φ predicateRead

theorem hypothesis_read : {n : Nat} → {context : ContextExpr S n} → {predicate : PropExpr S n} →
    Hypothesis context predicate → (Γ : Scope C n) → model.evaluateContext context = some Γ →
      model.evaluatePredicate Γ predicate = some ⊤
  | _, _, _, .here context predicate, Γ, contextRead => by
      rw [evaluateContext] at contextRead
      rcases (bindResult_eq_some_iff _ _ _).mp contextRead with ⟨base, baseRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, predicateRead, last⟩
      cases Option.some.inj last
      exact (model.predicateAssumptionRead stable base φ predicate φ predicateRead).trans
        (congrArg some (assumption_holds φ))
  | _, _, _, .assumptionThere member newer, Γ, contextRead => by
      rw [evaluateContext] at contextRead
      rcases (bindResult_eq_some_iff _ _ _).mp contextRead with ⟨base, baseRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨φ, _newerRead, last⟩
      cases Option.some.inj last
      exact (model.predicateAssumptionRead stable base φ _ ⊤
        (hypothesis_read member base baseRead)).trans
          (congrArg some (preimage_top' φ.ι))
  | _, _, _, .variableThere member type, Γ, contextRead => by
      rw [evaluateContext] at contextRead
      rcases (bindResult_eq_some_iff _ _ _).mp contextRead with ⟨base, baseRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, _typeRead, last⟩
      cases Option.some.inj last
      exact (model.predicateVariableRead stable base A _ ⊤
        (hypothesis_read member base baseRead)).trans
          (congrArg some (preimage_top' ((NativeModel C).toCwf.wk A)))

theorem hypothesis_sound (context : ContextExpr S n) (predicate : PropExpr S n)
    (member : Hypothesis context predicate)
    (contextInterpreted : Interprets model (.context context)) :
    Interprets model (.entails context predicate) := by
  rcases contextInterpreted with ⟨Γ, contextRead⟩
  exact ⟨Γ, contextRead, model.hypothesis_read stable member Γ contextRead⟩

theorem implicationIntroduction_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (branchInterpreted : Interprets model (.entails (.assume context first) second)) :
    Interprets model (.entails context (.implies first second)) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have assumedRead := model.evaluateContext_assume context first Γ φ contextRead firstRead
  have branch : ψ.preimage φ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable Γ φ second ψ secondRead).symm.trans
      (branchInterpreted.entailsAt (Γ.assume φ) assumedRead))
  exact ⟨Γ, contextRead, (model.evaluate_implies Γ first second φ ψ firstRead secondRead).trans
    (congrArg some (implication_top φ ψ branch))⟩

theorem disjunctionElimination_sound (context : ContextExpr S n)
    (first second consequent : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (consequentInterpreted : Interprets model (.predicate context consequent))
    (coveredInterpreted : Interprets model (.entails context (.or first second)))
    (firstBranch : Interprets model (.entails (.assume context first) consequent))
    (secondBranch : Interprets model (.entails (.assume context second) consequent)) :
    Interprets model (.entails context consequent) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  rcases consequentInterpreted.predicateAt Γ contextRead with ⟨χ, consequentRead⟩
  have covered : φ ⊔ ψ = ⊤ := Option.some.inj
    ((model.evaluate_or Γ first second φ ψ firstRead secondRead).symm.trans
      (coveredInterpreted.entailsAt Γ contextRead))
  have firstHeld : χ.preimage φ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable Γ φ consequent χ consequentRead).symm.trans
      (firstBranch.entailsAt (Γ.assume φ)
        (model.evaluateContext_assume context first Γ φ contextRead firstRead)))
  have secondHeld : χ.preimage ψ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable Γ ψ consequent χ consequentRead).symm.trans
      (secondBranch.entailsAt (Γ.assume ψ)
        (model.evaluateContext_assume context second Γ ψ contextRead secondRead)))
  exact ⟨Γ, contextRead, consequentRead.trans
    (congrArg some (disjunction_elimination φ ψ χ covered firstHeld secondHeld))⟩

theorem predicateExtensionality_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (firstBranch : Interprets model (.entails (.assume context first) second))
    (secondBranch : Interprets model (.entails (.assume context second) first)) :
    Interprets model (.predicateEq context first second) := by
  rcases firstInterpreted with ⟨Γ, φ, contextRead, firstRead⟩
  rcases secondInterpreted.predicateAt Γ contextRead with ⟨ψ, secondRead⟩
  have firstHeld : ψ.preimage φ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable Γ φ second ψ secondRead).symm.trans
      (firstBranch.entailsAt (Γ.assume φ)
        (model.evaluateContext_assume context first Γ φ contextRead firstRead)))
  have secondHeld : φ.preimage ψ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable Γ ψ first φ firstRead).symm.trans
      (secondBranch.entailsAt (Γ.assume ψ)
        (model.evaluateContext_assume context second Γ ψ contextRead secondRead)))
  exact ⟨Γ, φ, contextRead, firstRead,
    secondRead.trans (congrArg some (predicate_equal φ ψ firstHeld secondHeld).symm)⟩

theorem existentialElimination_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (consequent : PropExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (consequentInterpreted : Interprets model (.predicate context consequent))
    (coveredInterpreted : Interprets model (.entails context (.exists domain predicate)))
    (branchInterpreted : Interprets model
      (.entails (.assume (.snoc context domain) predicate) (consequent.rename Fin.succ))) :
    Interprets model (.entails context consequent) := by
  rcases domainInterpreted with ⟨Γ, A, contextRead, domainRead⟩
  have extendedRead := model.evaluateContext_snoc context domain Γ A contextRead domainRead
  rcases predicateInterpreted.predicateAt (Γ.snoc A) extendedRead with ⟨φ, predicateRead⟩
  rcases consequentInterpreted.predicateAt Γ contextRead with ⟨ψ, consequentRead⟩
  have covered : φ.image ((NativeModel C).toCwf.wk A) = ⊤ := Option.some.inj
    ((model.evaluate_exists Γ domain predicate A φ domainRead predicateRead).symm.trans
      (coveredInterpreted.entailsAt Γ contextRead))
  have variableRead := model.predicateVariableRead stable Γ A consequent ψ consequentRead
  have assumedRead := model.evaluateContext_assume (.snoc context domain) predicate
    (Γ.snoc A) φ extendedRead predicateRead
  have restricted : (ψ.preimage ((NativeModel C).toCwf.wk A)).preimage φ.ι = ⊤ := Option.some.inj
    ((model.predicateAssumptionRead stable (Γ.snoc A) φ (consequent.rename Fin.succ) _
      variableRead).symm.trans (branchInterpreted.entailsAt ((Γ.snoc A).assume φ) assumedRead))
  exact ⟨Γ, contextRead, consequentRead.trans
    (congrArg some (existential_elimination _ φ ψ covered restricted))⟩

theorem imageElimination_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (predicate : PropExpr S n) (typeInterpreted : Interprets model (.type context type))
    (predicateInterpreted : Interprets model (.predicate context predicate))
    (coveredInterpreted : Interprets model (.entails context (.image type)))
    (branchInterpreted : Interprets model (.entails (.snoc context type) (predicate.rename Fin.succ))) :
    Interprets model (.entails context predicate) := by
  rcases typeInterpreted with ⟨Γ, A, contextRead, typeRead⟩
  rcases predicateInterpreted.predicateAt Γ contextRead with ⟨φ, predicateRead⟩
  have covered : Subfunctor.range ((NativeModel C).toCwf.wk A) = ⊤ := Option.some.inj
    ((model.evaluate_image Γ type A typeRead).symm.trans
      (coveredInterpreted.entailsAt Γ contextRead))
  have restricted : φ.preimage ((NativeModel C).toCwf.wk A) =
      (⊤ : Subfunctor (Γ.snoc A).1) := Option.some.inj
    ((model.predicateVariableRead stable Γ A predicate φ predicateRead).symm.trans
      (branchInterpreted.entailsAt (Γ.snoc A)
        (model.evaluateContext_snoc context type Γ A contextRead typeRead)))
  exact ⟨Γ, contextRead, predicateRead.trans
    (congrArg some (image_cover_cancel _ φ covered restricted))⟩

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
