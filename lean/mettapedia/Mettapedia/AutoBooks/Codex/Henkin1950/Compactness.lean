import Mettapedia.AutoBooks.Codex.Henkin1950.ExtensionalSoundness

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Narrow theorem-facing compactness consequences for Henkin (1950).

The full reverse direction of Theorem 3 still depends on the remaining bridge
from the currently surfaced model theory to the exact proof system and
consistency notion used in the paper. This file currently packages the trusted
HOL-side finite-theory derivability and consistency notions that a future
reverse-side compactness theorem will need.
-/

/-- Finite closed-theory derivability in the trusted HOL derivation system over
Henkin's paper signature. -/
def TheoremFromTheory (T : ClosedTheorySet) (φ : Sentence) : Prop :=
  ∃ Δ : ClosedTheory,
    (∀ ψ : Sentence, ψ ∈ Δ → ψ ∈ T) ∧
      Derivation Primitive Δ φ

/-- Consistency for the trusted HOL derivation system over Henkin's paper
signature. -/
def DerivationConsistent (T : ClosedTheorySet) : Prop :=
  ¬ TheoremFromTheory T (.bot : Sentence)

/-- Any finite-theory derivation in the raw trusted HOL proof system also gives
set-based provability in the extensional closed-theory system. This is the
proof-theoretic bridge from the weaker `Derivation` packaging used for
soundness to the stronger closed-theory notion underlying `Consistent`. -/
theorem setProvable_of_theoremFromTheory
    {T : ClosedTheorySet} {φ : Sentence} :
    TheoremFromTheory T φ → SetProvable T φ := by
  rintro ⟨Δ, hΔ, hφ⟩
  exact
    ClosedTheorySet.provable_of_closedTheory
      (T := T)
      (Δ := Δ)
      (hΔ := by
        intro ψ hψ
        exact hΔ ψ hψ)
      (hφ := ExtDerivation.ofBase hφ)

/-- The paper-facing consistency notion already implies consistency for the
smaller trusted HOL derivation system. This isolates one honest reverse-side
compactness prerequisite without overclaiming the full semantic converse of
Theorem 3. -/
theorem derivationConsistent_of_consistent
    {T : ClosedTheorySet} :
    Consistent T → DerivationConsistent T := by
  intro hCons hBot
  exact hCons (setProvable_of_theoremFromTheory hBot)

/-- Reverse-Theorem-3 precursor at the currently trusted proof-system layer:
if every finite closed subtheory is satisfiable in a paper-general model, then
no finite closed subtheory derives falsity in the raw HOL derivation system. -/
theorem derivationConsistent_of_finiteSubsetSatisfiable
    {T : ClosedTheorySet} :
    FiniteSubsetSatisfiable T → DerivationConsistent T := by
  intro hFin hBot
  rcases hBot with ⟨Δ, hΔ, hDeriv⟩
  rcases hFin Δ hΔ with ⟨M, hM⟩
  let ρ : HenkinModel.Valuation M.toHenkinModel [] := emptyValuation
  have hρ : HenkinModel.ValuationAdmissible M.toHenkinModel ρ := by
    intro τ v
    nomatch v
  have hSat : Mettapedia.Logic.HOL.Soundness.SatisfiesHyps M.toHenkinModel ρ Δ := by
    intro ψ hψ
    simp only [ρ]
    exact hM ψ hψ
  have hFalse :=
    Mettapedia.Logic.HOL.Soundness.derivation_sound hDeriv hρ hSat
  exact (HenkinModel.models_bot M.toHenkinModel) hFalse

/-- Theorem 3 forward corollary at the currently trusted proof-system layer:
any closed theory satisfiable in a paper-general model is already consistent
against finite derivations of falsity in the raw HOL derivation system. -/
theorem theorem3_forward_derivationConsistent
    {T : ClosedTheorySet} :
    Satisfiable T → DerivationConsistent T := by
  intro hSat
  exact
    derivationConsistent_of_finiteSubsetSatisfiable
      (theorem3_forward_finiteSubsets hSat)

/-- Contrapositive canary for the currently trusted compactness direction:
if a closed theory finitely derives falsity in the raw HOL proof system, it
cannot be satisfiable in a paper-general model. -/
theorem not_satisfiable_of_not_derivationConsistent
    {T : ClosedTheorySet} :
    ¬ DerivationConsistent T → ¬ Satisfiable T := by
  intro hT hSat
  exact hT (theorem3_forward_derivationConsistent hSat)

/-- The same obstruction already appears one step earlier: if the trusted HOL
finite-derivation notion finds a contradiction, then the theory cannot even
have all of its finite closed subtheories satisfiable in paper-general models.
-/
theorem not_finiteSubsetSatisfiable_of_not_derivationConsistent
    {T : ClosedTheorySet} :
    ¬ DerivationConsistent T → ¬ FiniteSubsetSatisfiable T := by
  intro hT hFin
  exact hT (derivationConsistent_of_finiteSubsetSatisfiable hFin)

/-- The paper-facing consistency notion is also obstructed by any finite
derivation of falsity in the raw trusted HOL proof system. This is the direct
contrapositive companion to `derivationConsistent_of_consistent`. -/
theorem not_consistent_of_not_derivationConsistent
    {T : ClosedTheorySet} :
    ¬ DerivationConsistent T → ¬ Consistent T := by
  intro hT hCons
  exact hT (derivationConsistent_of_consistent hCons)

/-- Theorem 3 forward reaches the paper-facing extensional consistency notion
once the current paper-general model class is strengthened by a uniform
`EqAppArgSound` hypothesis. This is the honest compactness-level corollary of
the new extensional soundness layer. -/
theorem theorem3_forward_consistent_of_eqAppArgSound
    (hSound : ∀ M : GeneralModel, EqAppArgSound M)
    {T : ClosedTheorySet} :
    Satisfiable T → Consistent T :=
  consistent_of_satisfiable_of_eqAppArgSound hSound

/-- Contrapositive compactness canary for the extensional consistency notion
under the same explicit soundness seam. -/
theorem not_satisfiable_of_inconsistent_of_eqAppArgSound
    (hSound : ∀ M : GeneralModel, EqAppArgSound M)
    {T : ClosedTheorySet} :
    ¬ Consistent T → ¬ Satisfiable T := by
  intro hT hSat
  exact hT (theorem3_forward_consistent_of_eqAppArgSound hSound hSat)

end Mettapedia.AutoBooks.Codex.Henkin1950
