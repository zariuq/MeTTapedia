import Mettapedia.Logic.HOL.WitnessedSaturation
import Mettapedia.Logic.HOL.PrimeHenkinExtension

/-!
# Witnessed prime extension (Henkin existence)

Combining the Henkin saturation (`witnessLimit`) with the proven prime-extension
engine yields the **existence property** in a deductively-closed prime consistent
theory: every consistent, parameter-free theory over `WithParams Const` extends to

* deductively closed,
* consistent,
* prime (`φ ∨ ψ ∈ U → φ ∈ U ∨ ψ ∈ U`),
* **∃-witnessed** (`∃x. φ ∈ U → ∃ closed t, φ[t] ∈ U`),

provided one-variable bodies are enumerated.  This is four of the five
`ClosedTheorySet.World` fields — the Henkin core of completeness — assembled from
verified parts.  (The remaining `all_counterexample` field is the deeper ∀-case,
handled separately in the canonical model.)
-/

namespace Mettapedia.Logic.HOL

open Mettapedia.Logic.HOL.WithParams ClosedTheorySet

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **Henkin existence.**  A consistent, parameter-free theory over `WithParams Const`
extends to a deductively-closed, consistent, prime, ∃-witnessed theory. -/
theorem exists_witnessed_prime_extension
    {T : ClosedTheorySet (WithParams Const)} (enum : Nat → Body Const)
    (henum : ∀ b : Body Const, ∃ n, enum n = b)
    (hCons : Consistent (Const := WithParams Const) T)
    (hT0 : ∀ ψ ∈ T, ∀ (σ : Ty Base) (k : Nat), NoConstOccurrence (param σ k) ψ) :
    ∃ U : ClosedTheorySet (WithParams Const),
      (∀ {ψ : ClosedFormula (WithParams Const)}, ψ ∈ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := WithParams Const) U ∧
      Consistent (Const := WithParams Const) U ∧
      (∀ {φ ψ : ClosedFormula (WithParams Const)},
        (.or φ ψ : ClosedFormula (WithParams Const)) ∈ U → φ ∈ U ∨ ψ ∈ U) ∧
      (∀ {σ : Ty Base} {φ : Formula (WithParams Const) [σ]},
        (.ex φ : ClosedFormula (WithParams Const)) ∈ U →
          ∃ t : ClosedTerm (WithParams Const) σ, instantiate (Base := Base) t φ ∈ U) := by
  have hHcons : Consistent (Const := WithParams Const) (witnessLimit T enum) :=
    witnessLimit_consistent T enum hCons hT0
  obtain ⟨U, hExt, hClosed, hUcons, hPrime⟩ :=
    exists_prime_extension_of_consistent (Const := WithParams Const) hHcons
  refine ⟨U, fun hψ => hExt (subset_witnessLimit T enum hψ), hClosed, hUcons, hPrime, ?_⟩
  intro σ φ hex
  obtain ⟨k, hax⟩ := exists_witnessAxiom T enum ⟨σ, φ⟩ (henum ⟨σ, φ⟩)
  refine ⟨.const (param σ k), ?_⟩
  apply hClosed
  exact provable_mp (provable_of_mem (hExt hax)) (provable_of_mem hex)

end Mettapedia.Logic.HOL
