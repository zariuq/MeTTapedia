import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentParameterExchange
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUpdate

/-!
# Pruning a metavariable to a fresh one over fewer arguments

The newest metavariable `G` has a dependent Pi spine over the outer context. A **restriction**
selects some of its binders: a second spine over the same outer context, for a fresh
metavariable `H`, with an injective map of its binders into `G`'s binders, exact declaration
compatibility, and the same final result type. The pruning answer replaces `G` by `H` and
sets `G := λ z̄. H (z̄ restricted)`.

The answer is natural: reading it after any outer substitution `s` and then reindexing by `r`
is reading it at `r ≫ s`. This uses the composition laws of spine reindexing up to transport
(`ContextualDependentSpineTransport`), including those of the pattern argument maps.

An outer solution factors through the answer exactly when its value for `G`, opened at fresh
arguments, is typed-equal to a renaming of a body over `H`'s binders. Every update built
from such a factorization keeps the whole store, instantiated, and loses no solution. Whether
every solution of a given store factors is a property of the store; the flex-flex and
equalizer forcing theorems prove it from actual equations.

Exchanging two independent metavariables is an isomorphism of contexts, hence an update that
loses nothing and makes the older one the newest.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentPrune

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open TypedContextual.QuotientComprehensionSyntax
open ContextualDependentPiSpine ContextualDependentGeneralPattern ContextualDependentEta
open ContextualDependentUpdate ContextualDependentTypedInversion
open ContextualDependentPiSpine.Transport

variable {Head : Type} {rules : Rules Head}

/-! ## Restrictions of a spine -/

/-- **A restriction** of `G`'s spine to the binders of `H`'s spine. -/
structure Restriction {Γ : Context rules} {type keptType : TypeOver Γ} (spine : Spine type)
    (kept : Spine keptType) where
  keep : kept.Local → spine.Local
  injective : Function.Injective keep
  compatible : CtxRen kept.target.raw spine.target.raw (argRen kept spine idRen keep)
  resultCode : spine.result.code = Presentation.rename (argRen kept spine idRen keep) kept.result.code
  resultLevel : spine.result.level = kept.result.level

namespace Restriction

variable {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
  (restriction : Restriction spine kept)

/-- The binder map after an outer substitution. -/
def ren {Δ : Context rules} (base : Δ ⟶ Γ) : Ren (kept.reindex base).target.arity (spine.reindex base).target.arity :=
  argRen (kept.reindex base) (spine.reindex base) idRen (reindexArgs kept spine restriction.keep base)

theorem ren_injective {Δ : Context rules} (base : Δ ⟶ Γ) : Function.Injective (restriction.ren base) :=
  argRen_injective Function.injective_id (reindexArgs_injective kept spine restriction.keep base restriction.injective)

theorem ren_compatible {Δ : Context rules} (base : Δ ⟶ Γ) :
    CtxRen (kept.reindex base).target.raw (spine.reindex base).target.raw (restriction.ren base) :=
  reindex_compatible kept spine restriction.keep base restriction.compatible

/-- The binder map after an outer substitution, as a typed inclusion. -/
def inclusionAt {Δ : Context rules} (base : Δ ⟶ Γ) : Inclusion (kept.reindex base).target (spine.reindex base).target :=
  reindexInclusion kept spine restriction.keep base restriction.injective restriction.compatible

theorem inclusionAt_forward {Δ : Context rules} (base : Δ ⟶ Γ) :
    (restriction.inclusionAt base).forward = restriction.ren base := rfl

theorem resultAt {Δ : Context rules} (base : Δ ⟶ Γ) :
    (kept.reindex base).result.reindex (restriction.inclusionAt base).hom = (spine.reindex base).result := by
  apply TypeOver.ext
  · change subst (renSub (restriction.ren base)) (kept.reindex base).result.code = (spine.reindex base).result.code
    rw [subst_renSub, ← kept.result_reindex base, ← spine.result_reindex base]
    change Presentation.rename (restriction.ren base) (subst (kept.map base).substitution kept.result.code) =
      subst (spine.map base).substitution spine.result.code
    rw [restriction.resultCode, subst_map_rename]
    rfl
  · change (kept.reindex base).result.level = (spine.reindex base).result.level
    rw [← kept.result_reindex base, ← spine.result_reindex base]
    exact restriction.resultLevel.symm

/-- `H` applied to the kept binders, inside `G`'s telescope at the outer substitution. -/
def body {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base)) :
    Term (spine.reindex base).target (spine.reindex base).result :=
  ((((kept.reindex base).openFunction value).reindex (restriction.inclusionAt base).hom)).cast
    (restriction.resultAt base)

theorem body_code {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base)) :
    (restriction.body base value).code =
      Presentation.rename (restriction.ren base) ((kept.reindex base).openFunction value).code := by
  rw [body, Term.cast_code]
  exact subst_renSub _ _

/-- **The restricted function** `λ z̄. h (z̄ restricted)` at an outer substitution. -/
def restrict {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base)) :
    Term Δ (type.reindex base) :=
  (spine.reindex base).abstractBody (restriction.body base value)

/-- Opening the restricted function gives the restricted application, by beta. -/
theorem open_restrict {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base)) :
    Equal rules (spine.reindex base).target.raw ((spine.reindex base).openFunction (restriction.restrict base value)).code
      (restriction.body base value).code (spine.reindex base).result.code :=
  (spine.reindex base).beta _

/-- **Restriction from a renamed body.** A function whose opening is a renaming of a body over
the kept binders is the restriction of that body's abstraction. -/
theorem equal_restrict {Δ : Context rules} (base : Δ ⟶ Γ) (function : Term Δ (type.reindex base))
    (inner : Term (kept.reindex base).target (kept.reindex base).result)
    (same : Equal rules (spine.reindex base).target.raw ((spine.reindex base).openFunction function).code
      (Presentation.rename (restriction.ren base) inner.code) (spine.reindex base).result.code) :
    Equal rules Δ.raw function.code
      (restriction.restrict base ((kept.reindex base).abstractBody inner)).code (type.reindex base).code := by
  apply ((spine.reindex base).openFunction_equal_iff _ _).mpr
  refine same.trans ?_
  have renamed := ((kept.reindex base).beta inner).rename (restriction.ren_compatible base)
  have annotation : Presentation.rename (restriction.ren base) (kept.reindex base).result.code =
      (spine.reindex base).result.code := by
    have := congrArg TypeOver.code (restriction.resultAt base)
    change subst (renSub (restriction.ren base)) (kept.reindex base).result.code = _ at this
    rwa [subst_renSub] at this
  rw [annotation, ← restriction.body_code] at renamed
  exact renamed.symm.trans (restriction.open_restrict base _).symm

/-! ### Naturality of the restricted function -/

theorem body_reindex_heq {Δ Θ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base))
    (refinement : Θ ⟶ Δ) :
    HEq (((restriction.body base value).reindex ((spine.reindex base).map refinement)).cast
        ((spine.reindex base).result_reindex refinement))
      (restriction.body (refinement ≫ base) ((value.reindex refinement).cast
        (keptType.reindex_comp refinement base).symm)) := by
  apply term_heq (spine.target_comp base refinement) (spine.result_comp_heq base refinement)
  rw [Term.cast_code]
  change HEq (subst ((spine.reindex base).map refinement).substitution (restriction.body base value).code) _
  rw [restriction.body_code base value]
  change HEq (subst ((spine.reindex base).map refinement).substitution
      (Presentation.rename (argRen (kept.reindex base) (spine.reindex base) idRen
        (reindexArgs kept spine restriction.keep base)) ((kept.reindex base).openFunction value).code)) _
  rw [subst_map_rename, show subst ((kept.reindex base).map refinement).substitution
      ((kept.reindex base).openFunction value).code = _ from
      (kept.reindex base).openFunction_reindex_code refinement value]
  rw [restriction.body_code (refinement ≫ base)]
  refine rename_heq (congrArg Context.arity (kept.target_comp base refinement))
    (congrArg Context.arity (spine.target_comp base refinement))
    (Spine.argRen_comp_heq kept spine restriction.keep base refinement) ?_
  refine code_heq (kept.target_comp base refinement) (kept.result_comp_heq base refinement) ?_
  exact openFunction_congr (keptType.reindex_comp refinement base).symm (kept.reindex_comp_heq base refinement)
    (Transport.cast_heq _ _).symm

/-- **Naturality**: the restricted function at `base`, reindexed by `refinement`, is the
restricted function at `refinement ≫ base`. -/
theorem restrict_reindex_code {Δ Θ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base))
    (refinement : Θ ⟶ Δ) :
    ((restriction.restrict base value).reindex refinement).code =
      (restriction.restrict (refinement ≫ base)
        ((value.reindex refinement).cast (keptType.reindex_comp refinement base).symm)).code := by
  rw [restrict, (spine.reindex base).abstractBody_reindex refinement]
  exact spine.abstractBody_comp_code base refinement _ _ (restriction.body_reindex_heq base value refinement)

theorem restrict_congr_code {Δ : Context rules} {first second : Δ ⟶ Γ} (same : first = second)
    {one : Term Δ (keptType.reindex first)} {two : Term Δ (keptType.reindex second)} (sameValue : one.code = two.code) :
    (restriction.restrict first one).code = (restriction.restrict second two).code := by
  subst same
  obtain rfl := Term.ext sameValue
  rfl

/-! ### The pruning answer and its factorization -/

/-- The context of `H` in place of `G`. -/
abbrev prunedContext := extend Γ keptType

/-- **The pruning answer** `G := λ z̄. H (z̄ restricted)`. -/
def answer : extend Γ keptType ⟶ extend Γ type :=
  pair (projectionHom Γ keptType)
    (restriction.restrict (projectionHom Γ keptType) (newest Γ keptType))

theorem answer_projection :
    restriction.answer ≫ projectionHom Γ type = projectionHom Γ keptType := pair_projection _ _

/-- The answer reindexed by a residual `pair base value` is the restricted function at `base`. -/
theorem answer_value_code {Δ : Context rules} (base : Δ ⟶ Γ) (value : Term Δ (keptType.reindex base)) :
    subst (pair base value).substitution (restriction.answer.substitution 0) =
      (restriction.restrict base value).code := by
  change ((restriction.restrict (projectionHom Γ keptType) (newest Γ keptType)).reindex (pair base value)).code = _
  rw [restriction.restrict_reindex_code]
  exact restriction.restrict_congr_code (pair_projection base value) (by
    rw [Term.cast_code]
    rfl)

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- **Factorization through the pruning answer.** If the value of `G` under an outer solution is
typed-equal to the restricted function of some `h`, the solution factors through the answer,
on every annotated term. -/
theorem factors_of_restrict {Δ : Context rules} (solution : Δ ⟶ extend Γ type)
    (value : Term Δ (keptType.reindex (solution ≫ projectionHom Γ type)))
    (same : Equal rules Δ.raw (pulledNewest solution).code
      (restriction.restrict (solution ≫ projectionHom Γ type) value).code
      (type.reindex (solution ≫ projectionHom Γ type)).code) :
    ∀ term : TotalTerm (extend Γ type), (frames levels).E (term.reindex solution)
      (term.reindex (pair (solution ≫ projectionHom Γ type) value ≫ restriction.answer)) := by
  apply ContextualDependentEta.act_equal_of_substEq levels
  refine ⟨solution.typed, fun index => ?_⟩
  refine Fin.cases ?_ (fun index => ?_) index
  · rw [pulledNewest_code] at same
    change Equal rules Δ.raw (solution.substitution 0)
      (subst (pair (solution ≫ projectionHom Γ type) value).substitution (restriction.answer.substitution 0))
      (subst solution.substitution (Presentation.rename wk type.code))
    rw [restriction.answer_value_code, ← subst_projection type.code, subst_subComp]
    exact same
  · exact .refl (solution.typed index.succ)

/-- **Factorization from a renamed body**, the form the forcing theorems produce. -/
theorem factors_of_renamed {Δ : Context rules} (solution : Δ ⟶ extend Γ type)
    (inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
      (kept.reindex (solution ≫ projectionHom Γ type)).result)
    (same : Equal rules (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
      ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
      (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
      (spine.reindex (solution ≫ projectionHom Γ type)).result.code) :
    ∃ residual : Δ ⟶ extend Γ keptType, ∀ term : TotalTerm (extend Γ type),
      (frames levels).E (term.reindex solution) (term.reindex (residual ≫ restriction.answer)) :=
  ⟨_, restriction.factors_of_restrict levels solution _
    (restriction.equal_restrict _ (pulledNewest solution) inner same)⟩

end Restriction

/-! ## Updates from factorizations -/

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- **An update from a factorization**: the whole store is instantiated by the answer, and
every solution that factors through the answer is kept. -/
def ofFactorization {Γ target : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (answer : target ⟶ Γ)
    (factors : ∀ (Δ : Context rules) (solution : Δ ⟶ Γ), (frames levels).Models solution problem →
      ∃ residual : Δ ⟶ target, ∀ term : TotalTerm Γ,
        (frames levels).E (term.reindex solution) (term.reindex (residual ≫ answer))) :
    Update levels problem where
  target := target
  answer := answer
  remaining := (frames levels).applyStore answer problem
  sound := fun _ residual solved =>
    (Frames.models_applyStore (X := frames levels) answer residual problem).mp solved
  complete := by
    intro Δ solution solved
    obtain ⟨residual, factor⟩ := factors Δ solution solved
    exact ⟨residual, (Frames.models_applyStore (X := frames levels) answer residual problem).mpr
      ((Elimination.models_pointwise levels factor problem).mp solved), factor⟩

theorem ofFactorization_remaining {Γ target : Context rules} {problem : EquationStore (TotalTerm Γ)}
    (answer : target ⟶ Γ)
    (factors : ∀ (Δ : Context rules) (solution : Δ ⟶ Γ), (frames levels).Models solution problem →
      ∃ residual : Δ ⟶ target, ∀ term : TotalTerm Γ,
        (frames levels).E (term.reindex solution) (term.reindex (residual ≫ answer))) :
    (ofFactorization levels answer factors).remaining = (frames levels).applyStore answer problem := rfl

/-- **The pruning update.** When every solution of the store has a `G` that is a restriction,
the store is instantiated with `G := λ z̄. H (z̄ restricted)` and no solution is lost. -/
def prune {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
    (restriction : Restriction spine kept) (problem : EquationStore (TotalTerm (extend Γ type)))
    (forced : ∀ (Δ : Context rules) (solution : Δ ⟶ extend Γ type), (frames levels).Models solution problem →
      ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
          (kept.reindex (solution ≫ projectionHom Γ type)).result,
        Equal rules (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
          ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
          (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
          (spine.reindex (solution ≫ projectionHom Γ type)).result.code) :
    Update levels problem :=
  ofFactorization levels restriction.answer fun Δ solution solved => by
    obtain ⟨inner, same⟩ := forced Δ solution solved
    exact restriction.factors_of_renamed levels solution inner same

theorem prune_target {Γ : Context rules} {type keptType : TypeOver Γ} {spine : Spine type} {kept : Spine keptType}
    (restriction : Restriction spine kept) (problem : EquationStore (TotalTerm (extend Γ type)))
    (forced : ∀ (Δ : Context rules) (solution : Δ ⟶ extend Γ type), (frames levels).Models solution problem →
      ∃ inner : Term (kept.reindex (solution ≫ projectionHom Γ type)).target
          (kept.reindex (solution ≫ projectionHom Γ type)).result,
        Equal rules (spine.reindex (solution ≫ projectionHom Γ type)).target.raw
          ((spine.reindex (solution ≫ projectionHom Γ type)).openFunction (pulledNewest solution)).code
          (Presentation.rename (restriction.ren (solution ≫ projectionHom Γ type)) inner.code)
          (spine.reindex (solution ≫ projectionHom Γ type)).result.code) :
    (prune levels restriction problem forced).target = extend Γ keptType := rfl

/-! ## Exchanging independent metavariables -/

/-- An answer with a retraction loses no solution. -/
def ofRetraction {Γ target : Context rules} (problem : EquationStore (TotalTerm Γ))
    (answer : target ⟶ Γ) (inverse : Γ ⟶ target) (retraction : inverse ≫ answer = 𝟙 Γ) :
    Update levels problem :=
  ofFactorization levels answer fun Δ solution _ => ⟨solution ≫ inverse, fun term => by
    rw [Category.assoc, retraction, Category.comp_id]
    exact ((frames levels).equivalence Δ).refl _⟩

/-- **Metavariable exchange**: in `Γ, F, G` with `G` independent of `F`, the store moves to
`Γ, G, F`, where `F` is the newest. Nothing is lost and nothing is chosen. -/
def exchange {Γ : Context rules} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    Update levels problem :=
  ofRetraction levels problem (ContextualDependentParameterExchange.swap next first)
    (ContextualDependentParameterExchange.swap first next) (ContextualDependentParameterExchange.swap_twice first next)

theorem exchange_target {Γ : Context rules} (first next : TypeOver Γ)
    (problem : EquationStore (TotalTerm (ContextualDependentParameterExchange.context first next))) :
    (exchange levels first next problem).target = ContextualDependentParameterExchange.context next first := rfl

end ContextualDependentPrune
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
