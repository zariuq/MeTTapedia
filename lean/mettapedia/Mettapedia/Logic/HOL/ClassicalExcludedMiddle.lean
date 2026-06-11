import Mettapedia.Logic.HOL.MaximalConsistent
import Mettapedia.Logic.HOL.WitnessedExtension
import Mettapedia.Logic.HOL.Syntax.FreshConst

/-!
# The excluded-middle schema and its classical `∀`-lifts

For the classical 2-valued term model the world must contain the **excluded-middle
schema** `EMSchema`: closed instances `χ∨¬χ` and the *universal* instances
`∀x.(φ∨¬φ)`.  The universal instances are exactly what `emdne_all` consumes to drive
the `∀`-counterexample.  This file defines the schema, its membership lemmas, and the
two `Provable`-level classical lifts used in the world's `all_counterexample`:

* `provable_allNotNot_of_notEx` : `¬∃x.¬φ ⊢ ∀x.¬¬φ`;
* `provable_all_of_emAll_dne`    : `∀x.(φ∨¬φ), ∀x.¬¬φ ⊢ ∀x.φ` (over `WithParams`, via a
  fresh parameter for `emdne_all`).
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

/-- The excluded-middle schema over `WithParams Const`: closed `χ∨¬χ` and universal
`∀x.(φ∨¬φ)` instances. -/
def EMSchema (Const : Ty Base → Type v) : ClosedTheorySet (WithParams Const) :=
  {χ | (∃ ψ : ClosedFormula (WithParams Const), χ = Term.or ψ (.not ψ)) ∨
       (∃ (σ : Ty Base) (φ : Formula (WithParams Const) [σ]),
          χ = .all (Term.or φ (.not φ)))}

theorem emClosed_mem (ψ : ClosedFormula (WithParams Const)) :
    (Term.or ψ (.not ψ) : ClosedFormula (WithParams Const)) ∈ EMSchema Const :=
  Or.inl ⟨ψ, rfl⟩

theorem emAll_mem {σ : Ty Base} (φ : Formula (WithParams Const) [σ]) :
    (.all (Term.or φ (.not φ)) : ClosedFormula (WithParams Const)) ∈ EMSchema Const :=
  Or.inr ⟨σ, φ, rfl⟩

/-- `¬∃x.¬φ ⊢ ∀x.¬¬φ`, lifted to theories. -/
theorem provable_allNotNot_of_notEx {T : ClosedTheorySet (WithParams Const)}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (h : Provable (Const := WithParams Const) T (.not (.ex (.not φ)))) :
    Provable (Const := WithParams Const) T (.all (.not (.not φ))) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, allNot_of_notEx (φ := .not φ) d⟩

/-- `∀x.(φ∨¬φ), ∀x.¬¬φ ⊢ ∀x.φ`, lifted to theories (over `WithParams`, instantiating
`emdne_all` at a parameter fresh for `φ`). -/
theorem provable_all_of_emAll_dne {T : ClosedTheorySet (WithParams Const)}
    {σ : Ty Base} {φ : Formula (WithParams Const) [σ]}
    (hEM : Provable (Const := WithParams Const) T (.all (Term.or φ (.not φ))))
    (hDNE : Provable (Const := WithParams Const) T (.all (.not (.not φ)))) :
    Provable (Const := WithParams Const) T (.all φ) := by
  have key : ExtDerivation (WithParams Const) []
      (.imp (.all (.not (.not φ))) (.imp (.all (Term.or φ (.not φ))) (.all φ))) :=
    ExtDerivation.impI (ExtDerivation.impI
      (emdne_all (Const := WithParams Const) φ (param σ (maxParam φ))
        (noConstOccurrence_param_of_ge (maxParam φ) φ (le_refl _))))
  have keyP : Provable (Const := WithParams Const) T
      (.imp (.all (.not (.not φ))) (.imp (.all (Term.or φ (.not φ))) (.all φ))) :=
    provable_of_closedTheory (fun {ψ} hψ => by cases hψ) key
  exact provable_mp (provable_mp keyP hDNE) hEM

end Mettapedia.Logic.HOL
