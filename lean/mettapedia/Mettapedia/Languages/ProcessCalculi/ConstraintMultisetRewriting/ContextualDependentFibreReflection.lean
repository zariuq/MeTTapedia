import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentFibre
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TranslationEta

/-!
# Second-order fibre conservativity on the image

The map `fibre` of the second-order step into the unifier's typed βη frame **reflects the typed
βη equality** (`fibre_reflects`): two observations whose translations are equal in the typed βη
equality are the same observation. Translations are η-long and mention no head, so η-long
reflection makes their equality syntactic, and the raising encoding is injective.

On translated stores this gives, for second-order assignments and their translations:

* **solutions correspond**: `Ψ.hom f` solves the translated store exactly when `f` solves the
  store (`fibre_models_iff`);
* **asks of equation guards** over every dependent solution reflect to second-order asks
  (`fibre_entails_reflect`);
* **certified refutations transfer back**: a translated store with no dependent solution has no
  second-order solution (`fibre_refutation`); the unifier's certified refutations are of this
  kind;
* **principal answers**: a principal answer of the unifier's frame that is a translated assignment
  solves the second-order store (`fibre_principal_solves`), and the second-order principal answer of
  the pattern equation `m(x) ≐ n(x)` translates to a principal answer of the unifier's frame
  (`fibre_pattern_principal`). Without η that answer has no principal counterpart
  (`Translation.pattern_no_principal`).

The correspondence is stated on the image of the translation. Dependent solutions into arbitrary
later frames are not all translations (`ContextualDependentFibreControls.offImage_solution`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentFibre

open CategoryTheory Interface Interface.Translation
open Mettapedia.OSLF
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ContextualDependentEtaLong

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (complete : AlgorithmicComplete S.R S.roles)
  (rigid : ∀ name, S.roles name = .rigid) (church : ConversionCoherence.ChurchRosser S.R)
variable {sig : Binding.Signature} (names : BindingSignatureEmbedding.Names sig)
  (realization : BindingSignatureEmbedding.Realization names S.R)

section Reflection

variable (sortInjective : Function.Injective names.sort)
  (operatorInjective : ∀ {s : sig.Srt}, Function.Injective (names.operator (sort := s)))
include facts roots heads algebra complete rigid sortInjective operatorInjective

/-- **The second-order step reflects the typed βη equality.** -/
theorem fibre_reflects : (fibre facts roots heads church names realization).Reflects := by
  intro M o o' same
  obtain ⟨Γ, s, t⟩ := o
  obtain ⟨Γ', s', t'⟩ := o'
  have formed : CtxFormed S.R (metaCtx (Head := Head) names M) :=
    metaCtx_formed names realization M
  have typeSame := long_type_unique facts roots heads algebra complete formed
    (type_long rigid names realization _ Γ s) (type_long rigid names realization _ Γ' s') same.1
  obtain ⟨rfl, rfl⟩ := bindingType_injective names sortInjective
    (typeSame.eq_of_headFree (type_headFree names Γ s))
  have termSame := long_unique facts roots heads algebra complete formed
    (entry_long facts rigid names realization ⟨Γ, s, t⟩)
    (entry_long facts rigid names realization ⟨Γ, s, t'⟩) same.2
  have terms := eq_of_heq (encode_injective names M @operatorInjective t t' rfl
    (abstractN_injective _ (termSame.eq_of_headFree (entry_headFree names ⟨Γ, s, t⟩))))
  subst terms
  rfl

/-- **Solutions correspond on translated stores.** -/
theorem fibre_models_iff {M N : List (Binding.MetaArity sig)}
    (f : Binding.ContextualFamily.Assignment (S := sig) M.get N.get)
    (K : EquationStore (Binding.ContextualFamily.Observation sig M.get)) :
    (ContextualDependentEta.frames S.levels).Models
        ((fibre facts roots heads church names realization).hom f)
        ((fibre facts roots heads church names realization).store K) ↔
      (listFrames sig).Models (a := M) (b := N) f K :=
  (fibre facts roots heads church names realization).models_iff
    (fibre_reflects facts roots heads algebra complete rigid church names realization sortInjective
      @operatorInjective) f K

/-- **Asks of equation guards reflect.** -/
theorem fibre_entails_reflect {M : List (Binding.MetaArity sig)}
    {K G : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    (asked : (ContextualDependentEta.frames S.levels).Entails
      ((fibre facts roots heads church names realization).store K)
      (fun _ g => (ContextualDependentEta.frames S.levels).Models g
        ((fibre facts roots heads church names realization).store G))) :
    (listFrames sig).Entails (a := M) K (fun _ f => (listFrames sig).Models f G) :=
  (fibre facts roots heads church names realization).entails_reflect
    (fibre_reflects facts roots heads algebra complete rigid church names realization sortInjective
      @operatorInjective) asked

/-- **A principal answer that is a translated assignment solves the second-order store.** -/
theorem fibre_principal_solves {M N : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    {f : Binding.ContextualFamily.Assignment (S := sig) M.get N.get}
    (principal : (ContextualDependentEta.frames S.levels).Principal
      ((fibre facts roots heads church names realization).store K)
      ((fibre facts roots heads church names realization).hom f)) :
    (listFrames sig).Models (a := M) (b := N) f K :=
  (fibre_models_iff facts roots heads algebra complete rigid church names realization sortInjective
    @operatorInjective f K).mp principal.sound

end Reflection

/-- **Certified refutations transfer back**: a translated store without dependent solutions has
no second-order solution. No hypothesis beyond the map is needed. -/
theorem fibre_refutation {M : List (Binding.MetaArity sig)}
    {K : EquationStore (Binding.ContextualFamily.Observation sig M.get)}
    (refuted : ¬ (ContextualDependentEta.frames S.levels).Solvable
      ((fibre facts roots heads church names realization).store K)) :
    ¬ (listFrames sig).Solvable (a := M) K :=
  fun solvable => refuted ((fibre facts roots heads church names realization).solvable solvable)

/-! ## The pattern equation `m(x) ≐ n(x)` with η -/

section Pattern

variable (s : sig.Srt)

omit [UniverseLevel.LevelOrder L] in
theorem pair_lookup_subst {k : Nat} (σ : Sub Head (pairFrame s).length k) (i : Fin (pairFrame s).length) :
    subst σ (Ctx.lookup (metaCtx (Head := Head) names (pairFrame s)) i) = liftClosed (unaryType names s) := by
  rw [metaCtx_lookup, subst_liftClosed, EtaFrames.pairFrame_get]

omit [UniverseLevel.LevelOrder L] in
theorem unary_lookup_subst {k : Nat} (σ : Sub Head (unaryFrame s).length k) (i : Fin (unaryFrame s).length) :
    subst σ (Ctx.lookup (metaCtx (Head := Head) names (unaryFrame s)) i) = liftClosed (unaryType names s) := by
  rw [metaCtx_lookup, subst_liftClosed, EtaFrames.unaryFrame_get]

/-- **With η, the translated pattern equation has a principal answer in the unifier's frame**:
the translation of the second-order principal answer `m, n ↦ g(x)`. -/
theorem fibre_pattern_principal :
    (ContextualDependentEta.frames S.levels).Principal
      (a := (fibre facts roots heads church names realization).obj (pairFrame s))
      (m := (fibre facts roots heads church names realization).obj (unaryFrame s))
      ((fibre facts roots heads church names realization).store (patternStore s))
      ((fibre facts roots heads church names realization).hom (collapse s)) where
  sound := (fibre facts roots heads church names realization).models (pattern_principal s).sound
  factors := by
    intro b τ solved
    have equation := (solved _ (List.mem_singleton_self _)).2
    change Equal S.R b.raw (etaOf (τ.substitution (mIdx s))) (etaOf (τ.substitution (nIdx s)))
      (subst τ.substitution (liftClosed (unaryType names s))) at equation
    rw [subst_liftClosed] at equation
    have typedAt : ∀ i : Fin (pairFrame s).length,
        Typed S.R b.raw (τ.substitution i) (liftClosed (unaryType names s)) := by
      intro i
      have typed := τ.typed i
      change Typed S.R b.raw (τ.substitution i)
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) i)) at typed
      exact pair_lookup_subst names s τ.substitution i ▸ typed
    let residual : b ⟶ (fibre facts roots heads church names realization).obj (unaryFrame s) :=
      ⟨consSub (τ.substitution (mIdx s)) (fun k => k.elim0), by
        intro (i : Fin (unaryFrame s).length)
        show Typed S.R b.raw _ (subst _ (Ctx.lookup (metaCtx names (unaryFrame s)) i))
        rw [unary_lookup_subst names s]
        refine Fin.cases ?_ (fun k => k.elim0) i
        exact typedAt (mIdx s)⟩
    refine ⟨residual, fun t => act_equal_of_substEq ⟨τ.typed, fun i => ?_⟩ t⟩
    rcases i with ⟨_ | _ | k, bound⟩
    · change Equal S.R b.raw (τ.substitution (mIdx s)) (etaOf (τ.substitution (mIdx s)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) (mIdx s)))
      exact (pair_lookup_subst names s τ.substitution (mIdx s)).symm ▸
        EtaFrames.eta_equal names realization s (typedAt (mIdx s))
    · change Equal S.R b.raw (τ.substitution (nIdx s)) (etaOf (τ.substitution (mIdx s)))
        (subst τ.substitution (Ctx.lookup (metaCtx names (pairFrame s)) (nIdx s)))
      exact (pair_lookup_subst names s τ.substitution (nIdx s)).symm ▸
        Derivable.trans (EtaFrames.eta_equal names realization s (typedAt (nIdx s))) (.symm equation)
    · exact absurd bound (show ¬ (k + 1 + 1 < 2) by omega)

end Pattern

end ContextualDependentFibre
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
