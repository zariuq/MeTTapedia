import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianDirectSum
import Mathlib.Analysis.Normed.Algebra.Spectrum

/-!
# Routed CAROM: global Hermitian stability of commuting complex families

A commuting finite-dimensional complex transition family decomposes into
finitely many nonzero simultaneous generalized-eigenspace blocks.  When every
active block character lies in one strict disk, the local word energies can be
chosen with one common contraction rate, assembled on the dependent product,
and transported through the internal-direct-sum equivalence.  No orthogonality
of the embedded blocks is assumed.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set
open scoped ENNReal NNReal

namespace RoutedCarom

universe uCommand uState

section CommutingComplexFamily

variable {Command : Type uCommand} [Fintype Command] [DecidableEq Command]
variable {V : Type uState} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable [FiniteDimensional ℂ V]

/-- The nonzero simultaneous generalized characters of a transition family. -/
def ActiveSimultaneousCharacter
    (transition : Command → Module.End ℂ V) :=
  { character : Command → ℂ //
    simultaneousGenBlock transition character ≠ ⊥ }

omit [Fintype Command] [DecidableEq Command] in
/-- A nonzero simultaneous generalized block makes each coordinate of its
character an ordinary eigenvalue of the corresponding command. -/
theorem activeCharacter_hasEigenvalue
    (transition : Command → Module.End ℂ V)
    (character : Command → ℂ)
    (active : simultaneousGenBlock transition character ≠ ⊥)
    (command : Command) :
    (transition command).HasEigenvalue (character command) := by
  have block_le :
      simultaneousGenBlock transition character ≤
        (transition command).maxGenEigenspace (character command) :=
    iInf_le (fun indexedCommand =>
      (transition indexedCommand).maxGenEigenspace (character indexedCommand))
      command
  have maximal_ne_bot :
      (transition command).maxGenEigenspace (character command) ≠ ⊥ := by
    intro maximal_eq_bot
    apply active
    exact le_antisymm (by simpa [maximal_eq_bot] using block_le) bot_le
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank] at maximal_ne_bot
  exact Module.End.hasEigenvalue_of_hasGenEigenvalue maximal_ne_bot

omit [Fintype Command] [DecidableEq Command] in
/-- A spectral-radius disk bound controls every coordinate of every active
simultaneous character. -/
theorem activeCharacter_norm_le_of_spectralRadius_le
    (transition : Command → Module.End ℂ V)
    (radius : ℝ) (radius_nonneg : 0 ≤ radius)
    (spectral_bound : ∀ command,
      spectralRadius ℂ (transition command) ≤ ENNReal.ofReal radius)
    (character : Command → ℂ)
    (active : simultaneousGenBlock transition character ≠ ⊥)
    (command : Command) :
    ‖character command‖ ≤ radius := by
  have spectrum_mem :
      character command ∈ spectrum ℂ (transition command) :=
    (activeCharacter_hasEigenvalue transition character active command).mem_spectrum
  have norm_le_radius :
      (‖character command‖₊ : ENNReal) ≤ ENNReal.ofReal radius :=
    (le_iSup₂ (α := ENNReal) (character command) spectrum_mem).trans
      (spectral_bound command)
  have toReal_bound := ENNReal.toReal_mono ENNReal.ofReal_ne_top norm_le_radius
  simpa [ENNReal.toReal_ofReal radius_nonneg] using toReal_bound

/-- A strict common disk bound on every active simultaneous character yields
a common positive Hermitian contraction energy for the whole commuting
transition family.  The proof assembles the generalized blocks algebraically;
it does not assume that they are orthogonal in the ambient norm. -/
theorem exists_commonHermitianEnergy_of_commuting_activeCharacter_bound
    (transition : Command → Module.End ℂ V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second))
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1)
    (character_bound :
      ∀ character : Command → ℂ,
        simultaneousGenBlock transition character ≠ ⊥ →
          ∀ command, ‖character command‖ ≤ radius) :
    Nonempty (CommonHermitianEnergyLyapunov transition) := by
  classical
  let Active := ActiveSimultaneousCharacter transition
  let summand : Active → Submodule ℂ V := fun character =>
    simultaneousGenBlock transition character.1
  have allIndependent := iSupIndep_simultaneousGenBlock transition
  have activeFinite : Set.Finite
      {character : Command → ℂ |
        simultaneousGenBlock transition character ≠ ⊥} :=
    Submodule.finite_ne_bot_of_iSupIndep allIndependent
  letI : Finite Active := Finite.to_subtype activeFinite
  letI : Fintype Active := Fintype.ofFinite Active
  letI : DecidableEq Active := Classical.decEq Active
  have commutesAll : ∀ first second,
      Commute (transition first) (transition second) :=
    commuteAll_of_pairwise transition commutes
  have activeInternal := activeSimultaneousBlocks_internal transition commutes
  have independent : iSupIndep summand := by
    simpa only [Active, summand, ActiveSimultaneousCharacter] using
      activeInternal.1
  have spans : ⨆ character : Active, summand character = ⊤ := by
    simpa only [Active, summand, ActiveSimultaneousCharacter] using
      activeInternal.2

  obtain ⟨balance, scale, balance_pos, scale_pos, strict_rate_scale⟩ :=
    exists_balance_scale_strict_rate radius radius_nonneg radius_lt_one
  let weight : ℝ := 2 * scale ^ 2
  have weight_pos : 0 < weight := by
    dsimp [weight]
    positivity
  let rate : ℝ :=
    (1 + balance) * radius ^ 2 +
      (1 + 1 / balance) * (1 / weight)
  have rate_nonneg : 0 ≤ rate := by
    dsimp [rate]
    positivity
  have rate_lt_one : rate < 1 := by
    dsimp [rate, weight]
    simpa [div_eq_mul_inv] using strict_rate_scale

  let residual (character : Active) :
      Command → Module.End ℂ (summand character) :=
    simultaneousBlockResidual transition commutesAll character.1
  let blockTransition : ∀ character : Active,
      Command → Module.End ℂ (summand character) := fun character =>
    endScalarShiftedTransition character.1 (residual character)
  let nilpotent (character : Active) :
      ∀ command, IsNilpotent (residual character command) :=
    simultaneousBlockResidual_isNilpotent transition commutesAll character.1
  let depth (character : Active) : ℕ :=
    jointNilpotenceBudget
      (positiveNilpotenceDepth (residual character) (nilpotent character))
  have jointlyNilpotent (character : Active) :
      EndJointlyNilpotentAt (residual character) (depth character) := by
    exact simultaneousBlockResidual_endJointlyNilpotentAt
      transition commutesAll character.1
  let certificate (character : Active) :
      CommonHermitianEnergyLyapunov (blockTransition character) := by
    exact balancedEndScalarShiftedJointNilpotentCommonLyapunov
      character.1 (residual character) (depth character)
      (jointlyNilpotent character).succ.succ
      weight radius balance weight_pos radius_nonneg balance_pos
      (character_bound character.1 character.2) rate_lt_one
  have certificate_rate (character : Active) :
      (certificate character).rate = rate := by
    rfl
  let productCertificate :
      CommonHermitianEnergyLyapunov (piEndTransition blockTransition) :=
    piCommonHermitianEnergyLyapunov blockTransition certificate rate
      rate_nonneg rate_lt_one certificate_rate

  let productEquiv :
    (∀ character : Active, summand character) ≃ₗ[ℂ]
        (Π₀ character : Active, summand character) :=
    (DFinsupp.linearEquivFunOnFintype
      (R := ℂ) (ι := Active)
      (M := fun character : Active => summand character)).symm
  let directEquiv : (Π₀ character : Active, summand character) ≃ₗ[ℂ] V :=
    independent.linearEquiv spans
  let coordinateEquiv : (∀ character : Active, summand character) ≃ₗ[ℂ] V :=
    productEquiv.trans directEquiv
  have productEquiv_apply
      (state : ∀ character : Active, summand character)
      (character : Active) :
      productEquiv state character = state character := by
    have recovered :=
      (DFinsupp.linearEquivFunOnFintype
        (R := ℂ) (ι := Active)
        (M := fun index : Active => summand index)).apply_symm_apply state
    exact congrFun recovered character
  have intertwines (command : Command) (state : ∀ character, summand character) :
      coordinateEquiv (piEndTransition blockTransition command state) =
        transition command (coordinateEquiv state) := by
    have componentwise :
        productEquiv (piEndTransition blockTransition command state) =
          DirectSum.lmap (fun character => blockTransition character command)
            (productEquiv state) := by
      ext character
      rw [DirectSum.lmap_apply, productEquiv_apply, productEquiv_apply]
      rfl
    change directEquiv
        (productEquiv (piEndTransition blockTransition command state)) =
      transition command (directEquiv (productEquiv state))
    rw [componentwise]
    simpa only [directEquiv, blockTransition, summand, residual,
      ← simultaneousBlockTransition_eq_endScalarShiftedTransition,
      simultaneousBlockTransition] using
      internalDirectSumEquiv_intertwines summand independent spans
        (transition command)
        (fun character =>
          mapsTo_simultaneousGenBlock transition commutesAll character.1 command)
        (productEquiv state)
  exact ⟨productCertificate.conjugate
    (piEndTransition blockTransition) transition coordinateEquiv
    intertwines⟩

/-- Pairwise commutation plus one strict spectral-radius disk bound yields a
global common Hermitian contraction energy. -/
theorem exists_commonHermitianEnergy_of_commuting_spectralRadius_le
    (transition : Command → Module.End ℂ V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second))
    (radius : ℝ) (radius_nonneg : 0 ≤ radius) (radius_lt_one : radius < 1)
    (spectral_bound : ∀ command,
      spectralRadius ℂ (transition command) ≤ ENNReal.ofReal radius) :
    Nonempty (CommonHermitianEnergyLyapunov transition) := by
  exact exists_commonHermitianEnergy_of_commuting_activeCharacter_bound
    transition commutes radius radius_nonneg radius_lt_one
    (fun character active command =>
      activeCharacter_norm_le_of_spectralRadius_le
        transition radius radius_nonneg spectral_bound character active command)

/-- For a finite command family, separate strict spectral-radius hypotheses
yield one uniform strict radius and hence one global common Hermitian energy. -/
theorem exists_commonHermitianEnergy_of_commuting_spectralRadius_lt_one
    (transition : Command → Module.End ℂ V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second))
    (spectral_stable : ∀ command,
      spectralRadius ℂ (transition command) < 1) :
    Nonempty (CommonHermitianEnergyLyapunov transition) := by
  let radiusNN : ℝ≥0 :=
    Finset.univ.sup fun command =>
      (spectralRadius ℂ (transition command)).toNNReal
  let radius : ℝ := radiusNN
  have spectral_ne_top (command : Command) :
      spectralRadius ℂ (transition command) ≠ ∞ := by
    exact ne_of_lt ((spectral_stable command).trans (by simp))
  have each_lt_one (command : Command) :
      (spectralRadius ℂ (transition command)).toNNReal < (1 : ℝ≥0) := by
    apply ENNReal.toNNReal_lt_of_lt_coe
    simpa using spectral_stable command
  have radius_lt_one : radius < 1 := by
    change radiusNN < (1 : ℝ≥0)
    apply (Finset.sup_lt_iff (by norm_num)).2
    intro command _
    exact each_lt_one command
  have spectral_bound (command : Command) :
      spectralRadius ℂ (transition command) ≤ ENNReal.ofReal radius := by
    rw [← ENNReal.coe_toNNReal (spectral_ne_top command)]
    change
      ((spectralRadius ℂ (transition command)).toNNReal : ENNReal) ≤
        ENNReal.ofReal (radiusNN : ℝ)
    rw [ENNReal.ofReal_coe_nnreal]
    exact_mod_cast Finset.le_sup (f := fun indexedCommand =>
      (spectralRadius ℂ (transition indexedCommand)).toNNReal)
      (Finset.mem_univ command)
  exact exists_commonHermitianEnergy_of_commuting_spectralRadius_le
    transition commutes radius (by positivity) radius_lt_one spectral_bound

#print axioms ActiveSimultaneousCharacter
#print axioms activeCharacter_hasEigenvalue
#print axioms activeCharacter_norm_le_of_spectralRadius_le
#print axioms exists_commonHermitianEnergy_of_commuting_activeCharacter_bound
#print axioms exists_commonHermitianEnergy_of_commuting_spectralRadius_le
#print axioms exists_commonHermitianEnergy_of_commuting_spectralRadius_lt_one

end CommutingComplexFamily

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
