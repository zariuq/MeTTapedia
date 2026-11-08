import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Interface
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedContextualSums

/-!
# The transform frame with typed function and pair eta

The existing typed contextual category supplies the telescopes, substitutions
and formed annotated terms. Its total-term relation retains both type equality
and term equality at the first annotation. The universe model supplies the
joins needed to compare type equalities at different displayed universes.

This instance uses typed beta-eta judgments throughout. The raw syntax is the
same dependent telescope grammar as the raw-conversion frame; its formation
and substitution certificates are the stronger typed judgments. No untyped
conversion path is silently promoted to a typed equality certificate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEta

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual

variable {Head : Type} {rules : Rules Head}

theorem totalTerm_ext {Γ : Context rules} {first second : TotalTerm Γ}
    (sameType : first.1 = second.1) (sameTerm : first.2.code = second.2.code) :
    first = second := by
  rcases first with ⟨firstType, firstTerm⟩
  rcases second with ⟨secondType, secondTerm⟩
  dsimp only at sameType sameTerm
  subst secondType
  obtain rfl := Term.ext sameTerm
  rfl

theorem reindex_id {Γ : Context rules} (term : TotalTerm Γ) :
    term.reindex (𝟙 Γ) = term :=
  totalTerm_ext term.1.reindex_id (subst_ids term.2.code)

theorem reindex_comp {Γ Δ Θ : Context rules} (term : TotalTerm Θ)
    (σ : Γ ⟶ Δ) (τ : Δ ⟶ Θ) :
    term.reindex (σ ≫ τ) = (term.reindex τ).reindex σ :=
  totalTerm_ext (term.1.reindex_comp σ τ)
    (subst_subComp σ.substitution τ.substitution term.2.code).symm

variable {L : Type} [UniverseLevel.LevelOrder L] (levels : LevelModel rules L)

/-- The typed contextual frame, retaining the actual syntax before any
quotient. Function and pair eta belong to its typed equality relation. -/
def frames : Frames (fun Γ : Context rules => TotalTerm Γ) (fun Γ Δ : Context rules => Δ ⟶ Γ) where
  E := (totalTermSetoid levels _).r
  equivalence _ := (totalTermSetoid levels _).iseqv
  act σ term := term.reindex σ
  id Γ := 𝟙 Γ
  comp τ σ := τ ≫ σ
  act_id := reindex_id
  act_comp τ σ term := reindex_comp term τ σ
  preserves := @fun _ _ σ _ _ same =>
    ⟨reindex_typeEquality same.1 σ, same.2.substitute σ.typed⟩

theorem equivalent_iff {Γ : Context rules} (first second : TotalTerm Γ) :
    (frames levels).E first second ↔
      TypeEq rules Γ.raw first.1.code second.1.code ∧
        Equal rules Γ.raw first.2.code second.2.code first.1.code := Iff.rfl

theorem equivalent_iff_classes {Γ : Context rules} (first second : TotalTerm Γ) :
    (frames levels).E first second ↔
      QTerm.mk levels first.2 = QTerm.mk levels second.2 :=
  (QTerm.mk_eq_iff levels first.2 second.2).symm

theorem models_iff {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    (problem : EquationStore (TotalTerm Γ)) :
    (frames levels).Models σ problem ↔
      ∀ equation ∈ problem,
        TypeEq rules Δ.raw (subst σ.substitution equation.1.1.code)
          (subst σ.substitution equation.2.1.code) ∧
        Equal rules Δ.raw (subst σ.substitution equation.1.2.code)
          (subst σ.substitution equation.2.2.code)
          (subst σ.substitution equation.1.1.code) := Iff.rfl

/-- The frame sees the existing dependent function eta theorem. -/
theorem function_eta {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (function : Term Γ (DependentTypes.rawPi levels domain codomain)) :
    (frames levels).E
      (⟨_, Products.rawLam levels (Products.rawFreshApp levels function)⟩ : TotalTerm Γ)
      ⟨_, function⟩ :=
  (equivalent_iff_classes levels _ _).mpr (Products.rawEta levels function)

/-- Pair eta retains the dependency of the second projection's type. -/
theorem pair_eta {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (value : Term Γ (DependentTypes.rawSigma levels domain codomain)) :
    (frames levels).E
      (⟨_, Sums.rawPair levels (Sums.rawFst levels value) (Sums.rawSnd levels value)⟩ : TotalTerm Γ)
      ⟨_, value⟩ :=
  (equivalent_iff_classes levels _ _).mpr (Sums.rawEta levels value)

theorem solvable_of_equivalent {Γ : Context rules} (first second : TotalTerm Γ)
    (same : (frames levels).E first second) : (frames levels).Solvable [(first, second)] := by
  refine ⟨Γ, (frames levels).id Γ, ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  change (frames levels).E ((frames levels).act ((frames levels).id Γ) first)
    ((frames levels).act ((frames levels).id Γ) second)
  rw [(frames levels).act_id, (frames levels).act_id]
  exact same

theorem function_eta_solvable {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (function : Term Γ (DependentTypes.rawPi levels domain codomain)) :
    (frames levels).Solvable
      [((⟨_, Products.rawLam levels (Products.rawFreshApp levels function)⟩ : TotalTerm Γ),
        ⟨_, function⟩)] :=
  solvable_of_equivalent levels _ _ (function_eta levels function)

theorem pair_eta_solvable {Γ : Context rules} {domain : TypeOver Γ}
    {codomain : TypeOver (extend Γ domain)}
    (value : Term Γ (DependentTypes.rawSigma levels domain codomain)) :
    (frames levels).Solvable
      [((⟨_, Sums.rawPair levels (Sums.rawFst levels value) (Sums.rawSnd levels value)⟩ : TotalTerm Γ),
        ⟨_, value⟩)] :=
  solvable_of_equivalent levels _ _ (pair_eta levels value)

end ContextualDependentEta
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
