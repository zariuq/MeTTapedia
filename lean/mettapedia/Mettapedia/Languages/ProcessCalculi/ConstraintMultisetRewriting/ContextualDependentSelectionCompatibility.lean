import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentPruning

/-!
# The computed context selection has exact declaration compatibility

The existing selection algorithm retains raw declaration types by inversion.
Its returned variable map therefore has the stronger CtxRen property used by
comparison and checking reflection, rather than only a typed-substitution
certificate. This property is proved from the actual computation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSelectionCompatibility

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentTypedInversion ContextualDependentPruning

variable {Head : Type} {rules : Rules Head}

theorem drop_compatible {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ)
    (compatible : CtxRen Γ.raw Δ.raw inclusion.forward)
    (type : Tm Head Δ.arity) (formed : IsType rules Δ.raw type) :
    CtxRen Γ.raw (extendKnown Δ type formed).raw (drop inclusion type formed).forward := by
  intro index
  change Presentation.rename wk (Ctx.lookup Δ.raw (inclusion.forward index)) =
    Presentation.rename (fun index => (inclusion.forward index).succ) (Ctx.lookup Γ.raw index)
  rw [compatible, rename_comp]
  rfl

theorem keep_compatible {Γ Δ : Context rules} (inclusion : Inclusion Γ Δ)
    (compatible : CtxRen Γ.raw Δ.raw inclusion.forward) (source : TypeOver Γ)
    (target : Tm Head Δ.arity) (formed : IsType rules Δ.raw target)
    (recovers : Presentation.rename inclusion.forward source.code = target) :
    CtxRen (extend Γ source).raw (extendKnown Δ target formed).raw
      (keep inclusion source target formed recovers).forward := by
  have extended := compatible.snoc source.code
  rw [recovers] at extended
  exact extended

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable [DecidableEq Head] [DecidableRel S.R.headEq]
  [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R)
  (heads : HeadPreserving S.R) (algebra : CumulativeAlgebra S.R) (declared : DeclaredTypesFormed S.R)
variable (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)

set_option backward.isDefEq.respectTransparency false in
theorem select_compatible (fuel : Nat) {n : Nat} (raw : Ctx Head n) :
    ∀ (formed : CtxFormed S.R raw) (requested : Fin n → Bool)
      (result : ContextualDependentPruning.Selection (⟨n, raw, formed⟩ : Context S.R) requested),
      select facts roots heads algebra declared choices reducer fuel raw formed requested = some result →
        CtxRen result.source.raw raw result.inclusion.forward := by
  induction raw with
  | nil =>
      intro formed requested result computed
      cases Option.some.inj computed
      intro index
      exact Fin.elim0 index
  | snoc raw type ih =>
      intro formed requested result computed
      simp only [select] at computed
      obtain ⟨prior, priorComputed, computed⟩ := Option.bind_eq_some_iff.mp computed
      have priorCompatible := ih _ _ prior priorComputed
      split at computed
      · split at computed
        · cases computed
        · rename_i code found
          obtain ⟨checked, _, computed⟩ := Option.bind_eq_some_iff.mp computed
          have recovered : Presentation.rename prior.inclusion.forward checked.val.code = type := by
            rw [checked.property]
            exact ContextualDependentInversion.invert_sound type prior.inclusion.forward _
              (ContextualDependentInversion.lookup_exact prior.inclusion.forward prior.inclusion.injective) code found
          cases Option.some.inj computed
          exact keep_compatible prior.inclusion priorCompatible _ _ _ recovered
      · cases Option.some.inj computed
        exact drop_compatible prior.inclusion priorCompatible _ _

end ContextualDependentSelectionCompatibility
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
