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

/-- **Henkin satisfiability (the precise headline).**  Exactly Henkin's 1950 theorem in
model-existence form: if the witnessed, excluded-middle-extended theory
`witnessLimit T enum ∪ EMSchema` is consistent, then it has a Henkin **general** model
satisfying *every* one of its members.

This is the honest statement of what is proved — it is **not** "every consistent HOL
theory is satisfiable in a standard model": the hypothesis is consistency of the
*witnessed + EM* theory (i.e. classical consistency over a Henkin-expanded signature),
and the model is a *general* (Henkin) model. -/
theorem henkin_satisfiable {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const)
      (witnessLimit T enum ∪ EMSchema Const)) :
    ∃ N : HenkinModel.{u, v, v} Base (WithParams Const),
      ∀ ψ ∈ witnessLimit T enum ∪ EMSchema Const, N.models ψ := by
  obtain ⟨W, hHW, hComplete⟩ := exists_classical_world enum henum hCons
  refine ⟨termHenkinModel W hComplete, fun ψ hψ => ?_⟩
  rw [termHenkinModel_models_iff]
  exact hHW ψ hψ

/-- Convenience corollary: the Henkin model satisfies the original theory `T` and the
excluded-middle schema (a weakening of `henkin_satisfiable`, since both are subtheories
of `witnessLimit T enum ∪ EMSchema`). -/
theorem henkin_model_exists {T : ClosedTheorySet (WithParams Const)}
    (enum : Nat → Body Const) (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const)
      (witnessLimit T enum ∪ EMSchema Const)) :
    ∃ N : HenkinModel.{u, v, v} Base (WithParams Const),
      (∀ ψ ∈ T, N.models ψ) ∧ (∀ ψ ∈ EMSchema Const, N.models ψ) := by
  obtain ⟨N, hN⟩ := henkin_satisfiable enum henum hCons
  exact ⟨N, fun ψ hψ => hN ψ (Set.mem_union_left _ (subset_witnessLimit T enum hψ)),
    fun ψ hψ => hN ψ (Set.mem_union_right _ hψ)⟩

end ClosedTheorySet
end Mettapedia.Logic.HOL
