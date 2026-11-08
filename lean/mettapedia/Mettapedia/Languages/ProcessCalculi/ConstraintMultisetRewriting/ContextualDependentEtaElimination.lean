import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentEta

/-!
# Principal definition elimination at typed beta-eta frames

Substituting a value for the newest variable is principal in the actual typed
eta frame. Every solution factors through the substitution on all annotated
terms, including types depending on that variable. The factorization uses
typed substitution equality and functionality, not raw equality of solutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head}
variable (levels : LevelModel rules L)

theorem act_equal_of_substEq {Γ Δ : Context rules} {first second : Δ ⟶ Γ}
    (same : homTypedEquality rules first second) (term : TotalTerm Γ) :
    (frames levels).E (term.reindex first) (term.reindex second) := by
  apply (equivalent_iff_classes levels _ _).mpr
  exact QTerm.reindex_congruent (QTerm.mk levels term.2) same

namespace Elimination

def last (Γ : Context rules) (type : TypeOver Γ) : TotalTerm (extend Γ type) :=
  ⟨type.reindex (projectionHom Γ type), newest Γ type⟩

def definition (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    Equation (TotalTerm (extend Γ type)) :=
  (last Γ type, TotalTerm.reindex ⟨type, value⟩ (projectionHom Γ type))

def instantiate (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) : Γ ⟶ extend Γ type :=
  pair (𝟙 Γ) (value.cast type.reindex_id.symm)

theorem instantiate_projection (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    instantiate Γ value ≫ projectionHom Γ type = 𝟙 Γ := pair_projection _ _

theorem instantiate_last (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    (last Γ type).reindex (instantiate Γ value) = (⟨type, value⟩ : TotalTerm Γ) := by
  apply totalTerm_ext
  · change (type.reindex (projectionHom Γ type)).reindex (instantiate Γ value) = type
    rw [← TypeOver.reindex_comp, instantiate_projection, TypeOver.reindex_id]
  · change (value.cast type.reindex_id.symm).code = value.code
    exact Term.cast_code _ _

theorem instantiate_value (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    (TotalTerm.reindex (⟨type, value⟩ : TotalTerm Γ) (projectionHom Γ type)).reindex
      (instantiate Γ value) = (⟨type, value⟩ : TotalTerm Γ) := by
  let original : TotalTerm Γ := ⟨type, value⟩
  change (original.reindex (projectionHom Γ type)).reindex (instantiate Γ value) = original
  rw [← reindex_comp, instantiate_projection, reindex_id]

theorem definition_principal (Γ : Context rules) {type : TypeOver Γ} (value : Term Γ type) :
    (frames levels).Principal [definition Γ value] (instantiate Γ value) where
  sound := by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    change (frames levels).E ((last Γ type).reindex (instantiate Γ value))
      ((TotalTerm.reindex (⟨type, value⟩ : TotalTerm Γ) (projectionHom Γ type)).reindex (instantiate Γ value))
    rw [instantiate_last, instantiate_value]
    exact ((frames levels).equivalence Γ).refl _
  factors := by
    intro Δ solution solved
    let restricted := solution ≫ projectionHom Γ type
    have equation := solved _ (List.mem_singleton_self _)
    have newestEqual : Equal rules Δ.raw (solution.substitution 0)
        (subst restricted.substitution value.code)
        (subst solution.substitution (Ctx.lookup (extend Γ type).raw 0)) := by
      have compared := equation.2
      change Equal rules Δ.raw (solution.substitution 0)
        (subst solution.substitution (subst projection value.code))
        (subst solution.substitution (subst projection type.code)) at compared
      rw [subst_subComp] at compared
      rw [subst_projection] at compared
      exact compared
    have same : homTypedEquality rules solution (restricted ≫ instantiate Γ value) := by
      refine ⟨solution.typed, fun index => ?_⟩
      refine Fin.cases ?_ (fun index => ?_) index
      · change Equal rules Δ.raw (solution.substitution 0)
          (subst restricted.substitution (value.cast type.reindex_id.symm).code)
          (subst solution.substitution (Ctx.lookup (extend Γ type).raw 0))
        rw [Term.cast_code]
        exact newestEqual
      · exact .refl (solution.typed index.succ)
    exact ⟨restricted, act_equal_of_substEq levels same⟩

theorem models_pointwise {Γ Δ : Context rules} {first second : Δ ⟶ Γ}
    (same : ∀ term : TotalTerm Γ, (frames levels).E (term.reindex first) (term.reindex second))
    (problem : EquationStore (TotalTerm Γ)) :
    (frames levels).Models first problem ↔ (frames levels).Models second problem := by
  constructor
  · intro solved equation member
    exact ((frames levels).equivalence Δ).trans (((frames levels).equivalence Δ).symm (same equation.1))
      (((frames levels).equivalence Δ).trans (solved equation member) (same equation.2))
  · intro solved equation member
    exact ((frames levels).equivalence Δ).trans (same equation.1)
      (((frames levels).equivalence Δ).trans (solved equation member) (((frames levels).equivalence Δ).symm (same equation.2)))

/-- The remaining equations may depend on the eliminated variable. Every
solution of the whole problem, not just the definition, factors through the
computed substitution and solves the transported residual. -/
theorem definition_models_iff {Γ Δ : Context rules} {type : TypeOver Γ}
    (value : Term Γ type) (problem : EquationStore (TotalTerm (extend Γ type)))
    (solution : Δ ⟶ extend Γ type) :
    (frames levels).Models solution (definition Γ value :: problem) ↔
      ∃ residual : Δ ⟶ Γ,
        (frames levels).Models residual ((frames levels).applyStore (instantiate Γ value) problem) ∧
        ∀ term : TotalTerm (extend Γ type),
          (frames levels).E (term.reindex solution) (term.reindex (residual ≫ instantiate Γ value)) := by
  constructor
  · intro solved
    have defined : (frames levels).Models solution [definition Γ value] :=
      Frames.models_of_subset
        (fun _ member => List.mem_cons.mpr (.inl (List.mem_singleton.mp member))) solved
    obtain ⟨residual, factor⟩ := (definition_principal levels Γ value).factors Δ solution defined
    refine ⟨residual, ?_, factor⟩
    apply (Frames.models_applyStore (X := frames levels) (instantiate Γ value) residual problem).mpr
    exact (models_pointwise levels factor problem).mp
      (Frames.models_of_subset (fun _ member => List.mem_cons_of_mem _ member) solved)
  · rintro ⟨residual, rest, factor⟩
    apply (models_pointwise levels factor _).mpr
    have defined := Frames.models_comp (X := frames levels) (definition_principal levels Γ value).sound residual
    have remaining := (Frames.models_applyStore (X := frames levels) (instantiate Γ value) residual problem).mp rest
    intro equation member
    rcases List.mem_cons.mp member with rfl | member
    · exact defined _ (List.mem_singleton_self _)
    · exact remaining equation member

end Elimination
end ContextualDependentEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
