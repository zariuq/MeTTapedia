import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSoundnessLogic
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementRenamingEvaluation
import Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementNativeAbstractComparison
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractSoundnessAssumptions

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
    Interprets model (.entails context predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.hypothesis_sound model.toAbstract (model.stable_toAbstract stable) context
      predicate member contextInterpreted.toAbstract)

theorem implicationIntroduction_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (branchInterpreted : Interprets model (.entails (.assume context first) second)) :
    Interprets model (.entails context (.implies first second)) :=
  model.interprets_of_abstract
    (Abstract.ModelData.implicationIntroduction_sound model.toAbstract (model.stable_toAbstract stable)
      context first second firstInterpreted.toAbstract secondInterpreted.toAbstract
      branchInterpreted.toAbstract)

theorem disjunctionElimination_sound (context : ContextExpr S n)
    (first second consequent : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (consequentInterpreted : Interprets model (.predicate context consequent))
    (coveredInterpreted : Interprets model (.entails context (.or first second)))
    (firstBranch : Interprets model (.entails (.assume context first) consequent))
    (secondBranch : Interprets model (.entails (.assume context second) consequent)) :
    Interprets model (.entails context consequent) :=
  model.interprets_of_abstract
    (Abstract.ModelData.disjunctionElimination_sound model.toAbstract (model.stable_toAbstract stable)
      context first second consequent firstInterpreted.toAbstract secondInterpreted.toAbstract
      consequentInterpreted.toAbstract coveredInterpreted.toAbstract firstBranch.toAbstract
      secondBranch.toAbstract)

theorem predicateExtensionality_sound (context : ContextExpr S n) (first second : PropExpr S n)
    (firstInterpreted : Interprets model (.predicate context first))
    (secondInterpreted : Interprets model (.predicate context second))
    (firstBranch : Interprets model (.entails (.assume context first) second))
    (secondBranch : Interprets model (.entails (.assume context second) first)) :
    Interprets model (.predicateEq context first second) :=
  model.interprets_of_abstract
    (Abstract.ModelData.predicateExtensionality_sound model.toAbstract (model.stable_toAbstract stable)
      context first second firstInterpreted.toAbstract secondInterpreted.toAbstract firstBranch.toAbstract
      secondBranch.toAbstract)

theorem existentialElimination_sound (context : ContextExpr S n) (domain : TypeExpr S n)
    (predicate : PropExpr S (n + 1)) (consequent : PropExpr S n)
    (domainInterpreted : Interprets model (.type context domain))
    (predicateInterpreted : Interprets model (.predicate (.snoc context domain) predicate))
    (consequentInterpreted : Interprets model (.predicate context consequent))
    (coveredInterpreted : Interprets model (.entails context (.exists domain predicate)))
    (branchInterpreted : Interprets model
      (.entails (.assume (.snoc context domain) predicate) (consequent.rename Fin.succ))) :
    Interprets model (.entails context consequent) :=
  model.interprets_of_abstract
    (Abstract.ModelData.existentialElimination_sound model.toAbstract (model.stable_toAbstract stable)
      context domain predicate consequent domainInterpreted.toAbstract predicateInterpreted.toAbstract
      consequentInterpreted.toAbstract coveredInterpreted.toAbstract branchInterpreted.toAbstract)

theorem imageElimination_sound (context : ContextExpr S n) (type : TypeExpr S n)
    (predicate : PropExpr S n) (typeInterpreted : Interprets model (.type context type))
    (predicateInterpreted : Interprets model (.predicate context predicate))
    (coveredInterpreted : Interprets model (.entails context (.image type)))
    (branchInterpreted : Interprets model (.entails (.snoc context type) (predicate.rename Fin.succ))) :
    Interprets model (.entails context predicate) :=
  model.interprets_of_abstract
    (Abstract.ModelData.imageElimination_sound model.toAbstract (model.stable_toAbstract stable) context
      type predicate typeInterpreted.toAbstract predicateInterpreted.toAbstract
      coveredInterpreted.toAbstract branchInterpreted.toAbstract)

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
