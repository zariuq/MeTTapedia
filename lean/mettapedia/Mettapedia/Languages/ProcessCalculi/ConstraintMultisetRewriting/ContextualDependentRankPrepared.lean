import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentRankParts

/-!
# Preparation keeps the normal weight

The normal weight of a judged term depends on the term only up to typed equality
(`sideWeight_of_equivalent`), and is kept along the identity substitution into a context of equal
types (`sideWeight_normalized`). Preparation normalizes the context's declarations along such a
substitution, then each annotation and side up to typed equality, so it keeps the normal weight of
every store (`prepare_weight`). A decomposition of the prepared store therefore lowers the weight rank
of the original store.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRank

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra complete in
/-- **Equivalent judged terms have the same normal weight.** -/
theorem sideWeight_of_equivalent {Θ : Context S.R} {s t : TotalTerm Θ} (same : (frames S.levels).E s t) :
    sideWeight facts roots heads algebra rigid complete s = sideWeight facts roots heads algebra rigid complete t := by
  have chosen := Classical.choose_spec (long_exists facts roots heads algebra rigid complete Θ.formed s.2.typed)
  have normal : NormalForm S.R S.roles Θ.raw t.2.code
      (Classical.choose (long_exists facts roots heads algebra rigid complete Θ.formed s.2.typed)) t.1.code :=
    ⟨chosen.1.convType S.levels same.1, Equal.convType (.trans (.symm same.2) chosen.2) same.1⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete t normal]
  rfl

include facts roots heads algebra complete in
/-- **The normal weight is kept into a context of equal types**, along the identity substitution. -/
theorem sideWeight_normalized {Θ : Context S.R}
    (result : ContextualDependentContextNormalization.Normalized (S := S) Θ.raw) (t : TotalTerm Θ) :
    sideWeight facts roots heads algebra rigid complete (t.reindex result.iso.hom) =
      sideWeight facts roots heads algebra rigid complete t := by
  have chosen := Classical.choose_spec (long_exists facts roots heads algebra rigid complete Θ.formed t.2.typed)
  have normal : NormalForm S.R S.roles result.context.raw (t.reindex result.iso.hom).2.code
      (Classical.choose (long_exists facts roots heads algebra rigid complete Θ.formed t.2.typed))
      (t.reindex result.iso.hom).1.code := by
    change NormalForm S.R S.roles result.raw (subst ids t.2.code) _ (subst ids t.1.code)
    rw [subst_ids, subst_ids]
    exact ⟨chosen.1.stable S.levels result.forward result.backward, Equal.stable chosen.2 result.forward⟩
  rw [sideWeight_eq facts roots heads algebra rigid complete _ normal]
  rfl

/-- The normal weight of a store mapped sidewise by a weight-preserving map. -/
theorem storeWeight_map {Θ Θ' : Context S.R} (f : TotalTerm Θ → TotalTerm Θ')
    (keeps : ∀ t, sideWeight facts roots heads algebra rigid complete (f t) =
      sideWeight facts roots heads algebra rigid complete t) :
    ∀ problem : EquationStore (TotalTerm Θ),
      storeWeight facts roots heads algebra rigid complete (problem.map fun equation => (f equation.1, f equation.2)) =
        storeWeight facts roots heads algebra rigid complete problem
  | [] => rfl
  | equation :: rest => by
      simp only [List.map_cons, storeWeight, equationWeight, keeps]
      rw [storeWeight_map f keeps rest]

variable (root : ExecutableReduction.RootEvaluator S.R)
  (rootComplete : ∀ {n : Nat} (term : Tm Head n), root term = none → ∀ target, ¬ S.R.computation.step term target)

include facts roots heads algebra complete in
/-- Normalizing the context's declarations keeps the normal weight. -/
theorem contextStep_weight (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    storeWeight facts roots heads algebra rigid complete
        (ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem).remaining =
      storeWeight facts roots heads algebra rigid complete problem := by
  cases computed : ContextualDependentContextNormalization.normalize root rootComplete facts roots heads fuel Θ.raw
      Θ.formed with
  | none =>
      have step : ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem =
          Update.pending S.levels problem := by
        unfold ContextualDependentNormalizing.contextStep
        rw [computed]
      rw [step]
      rfl
  | some result =>
      have step : ContextualDependentNormalizing.contextStep root rootComplete facts roots heads fuel problem =
          result.update problem := by
        unfold ContextualDependentNormalizing.contextStep
        rw [computed]
      rw [step]
      exact storeWeight_map facts roots heads algebra rigid complete (fun t => t.reindex result.iso.hom)
        (sideWeight_normalized facts roots heads algebra rigid complete result) problem

include facts roots heads algebra complete in
/-- **Preparation keeps the normal weight.** -/
theorem prepare_weight (fuel : Nat) {Θ : Context S.R} (problem : EquationStore (TotalTerm Θ)) :
    storeWeight facts roots heads algebra rigid complete
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining =
      storeWeight facts roots heads algebra rigid complete problem := by
  rw [ContextualDependentNormalizing.prepare_remaining]
  have terms : ∀ {Γ : Context S.R} (original : TotalTerm Γ),
      sideWeight facts roots heads algebra rigid complete
          (ContextualDependentNormalization.termAt root facts roots heads fuel original) =
        sideWeight facts roots heads algebra rigid complete original := fun original =>
    (sideWeight_of_equivalent facts roots heads algebra rigid complete
      (ContextualDependentNormalization.termAt_equivalent root facts roots heads fuel original)).symm
  unfold ContextualDependentNormalization.storeAt
  refine (storeWeight_map facts roots heads algebra rigid complete _ terms _).trans ?_
  exact contextStep_weight facts roots heads algebra rigid complete root rootComplete fuel problem

include facts roots heads algebra complete in
/-- **A lighter store after preparation lowers the weight rank of the original store.** -/
theorem below_of_prepared (fuel : Nat) {Θ : Context S.R} {problem : EquationStore (TotalTerm Θ)}
    {store : EquationStore
      (TotalTerm (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).target)}
    (lower : storeWeight facts roots heads algebra rigid complete store <
      storeWeight facts roots heads algebra rigid complete
        (ContextualDependentNormalizing.prepare root rootComplete facts roots heads fuel problem).remaining) :
    ContextualDependentWorklist.Below (weightRank facts roots heads algebra rigid complete store)
      (weightRank facts roots heads algebra rigid complete problem) := by
  rw [prepare_weight facts roots heads algebra rigid complete root rootComplete fuel problem] at lower
  have same := ContextualDependentFragment.prepare_arity facts roots heads root rootComplete fuel problem
  unfold weightRank ContextualDependentWorklist.Below
  rw [same]
  exact Prod.Lex.right _ lower

end ContextualDependentRank
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
