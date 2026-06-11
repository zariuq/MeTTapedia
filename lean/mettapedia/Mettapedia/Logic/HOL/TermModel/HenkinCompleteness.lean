import Mettapedia.Logic.HOL.TermModel.Fundamental
import Mettapedia.Logic.HOL.ClassicalWorld

/-!
# Classical Henkin completeness for HOL

The canonical term `PreModel` is closed under denotation (`term_closed`), hence a genuine
`HenkinModel`; and a closed formula is satisfied exactly when it belongs to the world
(`models_iff_mem`).  Combining with the classical canonical world `exists_classical_world`
gives **Henkin completeness in model-existence form**:

> a consistent classical HOL theory (witnessed + excluded middle) has a Henkin general model.

This is Henkin's 1950 theorem for the theory of types, here machine-verified.
-/

namespace Mettapedia.Logic.HOL
namespace ClosedTheorySet

open Mettapedia.Logic.HOL.WithParams
open scoped Classical

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- The canonical term `PreModel` is closed under denotation: a term's value under an
admissible valuation is admissible (representable). -/
theorem termPreModel_term_closed (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier)
    {Γ : Ctx Base} {τ : Ty Base} (t : Term (WithParams Const) Γ τ)
    (ρ : PreModel.Valuation (termPreModel M hC) Γ)
    (hρ : PreModel.ValuationAdmissible (termPreModel M hC) ρ) :
    (termPreModel M hC).adm τ (PreModel.denote (termPreModel M hC) t ρ) :=
  ⟨subst (fun {σ} v => treify M σ (ρ v)) t,
   fundamental M hC t ρ (fun {σ} v => treify M σ (ρ v)) (fun {_} v => rep_treify M (hρ v))⟩

/-- The canonical term model as a `HenkinModel`. -/
noncomputable def termHenkinModel (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier) :
    HenkinModel Base (WithParams Const) where
  toPreModel := termPreModel M hC
  term_closed := fun t ρ hρ => termPreModel_term_closed M hC t ρ hρ

theorem termHenkinModel_models_iff (M : World (WithParams Const))
    (hC : ∀ χ : ClosedFormula (WithParams Const),
      χ ∈ M.carrier ∨ (.not χ : ClosedFormula (WithParams Const)) ∈ M.carrier)
    (φ : ClosedFormula (WithParams Const)) :
    (termHenkinModel M hC).models φ ↔ φ ∈ M.carrier :=
  models_iff_mem M hC φ

/-- **Classical Henkin completeness (model existence).**  A consistent classical theory
`witnessLimit T enum ∪ EMSchema` has a Henkin general model satisfying `T` and the
excluded-middle schema. -/
theorem henkin_model_exists {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const)
      (witnessLimit T enum ∪ EMSchema Const)) :
    ∃ N : HenkinModel.{u, v, v} Base (WithParams Const),
      (∀ ψ ∈ T, N.models ψ) ∧ (∀ ψ ∈ EMSchema Const, N.models ψ) := by
  obtain ⟨W, hT, hEM, hComplete⟩ := exists_classical_world enum henum hCons
  refine ⟨termHenkinModel W hComplete, ?_, ?_⟩
  · intro ψ hψ
    rw [termHenkinModel_models_iff]
    exact hT ψ hψ
  · intro ψ hψ
    rw [termHenkinModel_models_iff]
    exact hEM ψ hψ

end ClosedTheorySet
end Mettapedia.Logic.HOL
