import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentCheckingBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEtaBudget
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentProjectionInversion

/-!
# Successful dependent recovery persists at larger budgets

The executable checker preserves the reconstructed annotation and body.
Projection recovery additionally uses stable normalization and final typed
conversion. These are the actual solver routines, including their returned
data; no monotonicity of a caller-supplied success predicate is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentRecoveryBudget

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentConversionBudget ContextualDependentCheckingBudget

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
theorem formType_mono {fuel larger : Nat} {Γ : Context S.R} {code : Tm Head Γ.arity}
    {result : {type : TypeOver Γ // type.code = code}}
    (accepted : ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code = some result)
    (enough : fuel ≤ larger) :
    ContextualDependentPruning.formType facts roots heads algebra declared choices reducer larger Γ code = some result := by
  unfold ContextualDependentPruning.formType at accepted ⊢
  obtain ⟨inferred, synthesized, rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨level, recognized, returned⟩ := Option.bind_eq_some_iff.mp rest
  exact Option.bind_eq_some_iff.mpr ⟨inferred,
    synth_success_mono S.R choices reducer stable synthesized enough,
    Option.bind_eq_some_iff.mpr ⟨level, asUniverse_success_mono S.R reducer stable recognized enough, returned⟩⟩

include stable in
theorem recover_mono {fuel larger : Nat} {Γ Δ : Context S.R}
    {selection : ContextualDependentTypedInversion.Inclusion Γ Δ} {type : TypeOver Γ}
    {target : Tm Head Δ.arity} {result : ContextualDependentTypedInversion.Recovery selection type target}
    (accepted : ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer
      fuel selection type target = some result) (enough : fuel ≤ larger) :
    ContextualDependentTypedInversion.recover facts roots heads algebra declared choices reducer
      larger selection type target = some result := by
  unfold ContextualDependentTypedInversion.recover at accepted ⊢
  split at accepted
  · cases accepted
  · rename_i body found
    obtain ⟨checked, computed, returned⟩ := Option.bind_eq_some_iff.mp accepted
    exact Option.bind_eq_some_iff.mpr ⟨checked,
      check_success_mono S.R choices reducer stable computed enough, returned⟩

include stable in
theorem projection_recover_mono {fuel larger : Nat} {source expanded target : Context S.R}
    {selection : ContextualDependentTypedInversion.Inclusion source expanded}
    {expand : expanded ⟶ target} {restore : target ⟶ expanded} {type : TypeOver source}
    {original : TotalTerm target}
    {result : ContextualDependentProjectionInversion.Recovery S.levels (restore ≫ selection.hom) type original}
    (accepted : ContextualDependentProjectionInversion.recover facts roots heads algebra declared choices reducer
      fuel selection expand restore type original = some result) (enough : fuel ≤ larger) :
    ContextualDependentProjectionInversion.recover facts roots heads algebra declared choices reducer
      larger selection expand restore type original = some result := by
  unfold ContextualDependentProjectionInversion.recover at accepted ⊢
  obtain ⟨normal, reduced, afterReduction⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨proposed, recovered, afterRecovery⟩ := Option.bind_eq_some_iff.mp afterReduction
  obtain ⟨checked, compared, returned⟩ := Option.bind_eq_some_iff.mp afterRecovery
  have reducedLater : reducer larger (original.reindex expand).2.code = some normal := by
    induction enough with
    | refl => exact reduced
    | @step larger _ ih => exact stable larger _ normal ih
  exact Option.bind_eq_some_iff.mpr ⟨normal, reducedLater,
    Option.bind_eq_some_iff.mpr ⟨proposed,
      recover_mono facts roots heads algebra declared choices reducer stable recovered enough,
      Option.bind_eq_some_iff.mpr ⟨checked,
        ContextualDependentEtaBudget.compare_mono facts roots heads algebra reducer stable compared enough, returned⟩⟩⟩

end ContextualDependentRecoveryBudget
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
