import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromHermitianWordStability

/-!
# Routed CAROM: finite Hermitian direct-sum assembly

Local simultaneous-block certificates are useful globally only after their
energies have been assembled without assuming that the embedded blocks are
orthogonal in the ambient norm.  This file performs the algebraic assembly
on a finite dependent product.  Each component may have its own state type
and energy, but every component must use the same strict rate.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Finset Function Set

namespace RoutedCarom

universe uCommand uBlock uState

section FiniteHermitianProduct

variable {Command : Type uCommand}
variable {Block : Type uBlock} [Fintype Block]
variable {State : Block → Type uState}
variable [∀ block, NormedAddCommGroup (State block)]
variable [∀ block, InnerProductSpace ℂ (State block)]

/-- Apply one command independently on every component of a dependent
product. -/
noncomputable def piEndTransition
    (transition : ∀ block, Command → Module.End ℂ (State block))
    (command : Command) :
    Module.End ℂ (∀ block, State block) :=
  LinearMap.piMap fun block => transition block command

omit [Fintype Block] in
@[simp] theorem piEndTransition_apply
    (transition : ∀ block, Command → Module.End ℂ (State block))
    (command : Command) (state : ∀ block, State block) (block : Block) :
    piEndTransition transition command state block =
      transition block command (state block) := rfl

/-- Sum a family of local Hermitian energies over a finite dependent
product. -/
noncomputable def piHermitianEnergy
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (state : ∀ block, State block) : ℝ :=
  ∑ block, (certificate block).energy (state block)

theorem piHermitianEnergy_nonneg
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (state : ∀ block, State block) :
    0 ≤ piHermitianEnergy certificate state := by
  exact Finset.sum_nonneg fun block _ => (certificate block).energy_nonneg _

theorem piHermitianEnergy_pos
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    {state : ∀ block, State block} (state_ne_zero : state ≠ 0) :
    0 < piHermitianEnergy certificate state := by
  obtain ⟨block, block_ne_zero⟩ := Function.ne_iff.mp state_ne_zero
  apply Finset.sum_pos'
  · exact fun other _ => (certificate other).energy_nonneg _
  · exact ⟨block, Finset.mem_univ _, (certificate block).energy_pos block_ne_zero⟩

theorem piHermitianEnergy_zero
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block)) :
    piHermitianEnergy certificate 0 = 0 := by
  apply Finset.sum_eq_zero
  intro block _
  have zero_smul := (certificate block).energy_smul (0 : ℂ) (0 : State block)
  simpa using zero_smul

/-- The assembled energy vanishes exactly at the zero product state. -/
theorem piHermitianEnergy_eq_zero_iff
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (state : ∀ block, State block) :
    piHermitianEnergy certificate state = 0 ↔ state = 0 := by
  constructor
  · intro energy_zero
    by_contra state_ne_zero
    have := piHermitianEnergy_pos certificate state_ne_zero
    linarith
  · rintro rfl
    exact piHermitianEnergy_zero certificate

theorem piHermitianEnergy_smul
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (scalar : ℂ) (state : ∀ block, State block) :
    piHermitianEnergy certificate (scalar • state) =
      ‖scalar‖ ^ 2 * piHermitianEnergy certificate state := by
  simp only [piHermitianEnergy, Pi.smul_apply, (certificate _).energy_smul]
  exact (Finset.mul_sum _ _ _).symm

theorem piHermitianEnergy_parallelogram
    {transition : ∀ block, Command → Module.End ℂ (State block)}
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (first second : ∀ block, State block) :
    piHermitianEnergy certificate (first + second) +
        piHermitianEnergy certificate (first - second) =
      2 * (piHermitianEnergy certificate first +
        piHermitianEnergy certificate second) := by
  simp only [piHermitianEnergy, Pi.add_apply, Pi.sub_apply]
  rw [← Finset.sum_add_distrib]
  calc
    ∑ block, ((certificate block).energy (first block + second block) +
        (certificate block).energy (first block - second block)) =
        ∑ block, 2 * ((certificate block).energy (first block) +
          (certificate block).energy (second block)) := by
      apply Finset.sum_congr rfl
      intro block _
      exact (certificate block).parallelogram (first block) (second block)
    _ = 2 * ∑ block, ((certificate block).energy (first block) +
          (certificate block).energy (second block)) := by
      rw [Finset.mul_sum]
    _ = 2 * (∑ block, (certificate block).energy (first block) +
          ∑ block, (certificate block).energy (second block)) := by
      rw [Finset.sum_add_distrib]

/-- Local certificates with one shared strict rate assemble into a common
Hermitian certificate for the componentwise command family. -/
noncomputable def piCommonHermitianEnergyLyapunov
    (transition : ∀ block, Command → Module.End ℂ (State block))
    (certificate : ∀ block,
      CommonHermitianEnergyLyapunov (transition block))
    (rate : ℝ)
    (rate_nonneg : 0 ≤ rate)
    (rate_lt_one : rate < 1)
    (rate_eq : ∀ block, (certificate block).rate = rate) :
    CommonHermitianEnergyLyapunov (piEndTransition transition) where
  energy := piHermitianEnergy certificate
  rate := rate
  rate_nonneg := rate_nonneg
  rate_lt_one := rate_lt_one
  energy_nonneg := piHermitianEnergy_nonneg certificate
  energy_pos := piHermitianEnergy_pos certificate
  energy_smul := piHermitianEnergy_smul certificate
  parallelogram := piHermitianEnergy_parallelogram certificate
  contracts := by
    intro command state
    have component_bound (block : Block) :
        (certificate block).energy
            (transition block command (state block)) ≤
          rate * (certificate block).energy (state block) := by
      rw [← rate_eq block]
      exact (certificate block).contracts command (state block)
    simp only [piHermitianEnergy, piEndTransition_apply]
    calc
      ∑ block, (certificate block).energy
          (transition block command (state block)) ≤
          ∑ block, rate * (certificate block).energy (state block) :=
        Finset.sum_le_sum fun block _ => component_bound block
      _ = rate * ∑ block, (certificate block).energy (state block) := by
        rw [Finset.mul_sum]

/-! ## Finite-product fixture -/

/-- Two independent copies of the strict `9/10` complex contraction share
the same assembled Hermitian certificate. -/
noncomputable def duplicatedNineTenthsTransition
    (_ : Bool) : Unit → Module.End ℂ ℂ :=
  endScalarShiftedTransition nineTenthsComplexCoefficient zeroComplexResidual

noncomputable def duplicatedNineTenthsCertificate
    (_ : Bool) :
    CommonHermitianEnergyLyapunov
      (endScalarShiftedTransition nineTenthsComplexCoefficient
        zeroComplexResidual) :=
  nineTenthsComplexCommonHermitianEnergy

noncomputable def duplicatedNineTenthsCommonHermitianEnergy :
    CommonHermitianEnergyLyapunov
      (piEndTransition duplicatedNineTenthsTransition) :=
  piCommonHermitianEnergyLyapunov duplicatedNineTenthsTransition
    duplicatedNineTenthsCertificate
    nineTenthsComplexCommonHermitianEnergy.rate
    nineTenthsComplexCommonHermitianEnergy.rate_nonneg
    nineTenthsComplexCommonHermitianEnergy.rate_lt_one
    (fun block => by cases block <;> rfl)

/-- The assembled two-block energy does not assign positive energy to the
zero state. -/
theorem duplicatedNineTenths_zeroEnergy :
    duplicatedNineTenthsCommonHermitianEnergy.energy 0 = 0 := by
  exact piHermitianEnergy_zero duplicatedNineTenthsCertificate

#print axioms piEndTransition_apply
#print axioms piHermitianEnergy_nonneg
#print axioms piHermitianEnergy_pos
#print axioms piHermitianEnergy_zero
#print axioms piHermitianEnergy_eq_zero_iff
#print axioms piHermitianEnergy_smul
#print axioms piHermitianEnergy_parallelogram
#print axioms piCommonHermitianEnergyLyapunov
#print axioms duplicatedNineTenthsCommonHermitianEnergy
#print axioms duplicatedNineTenths_zeroEnergy

end FiniteHermitianProduct

section InternalDirectSumIntertwining

universe uRing uIndex uAmbient

variable {R : Type uRing} [Ring R]
variable {Index : Type uIndex} [DecidableEq Index]
variable {Ambient : Type uAmbient} [AddCommGroup Ambient] [Module R Ambient]

/-- The internal-direct-sum equivalence intertwines a globally linear
transition with the componentwise restrictions to invariant summands. -/
theorem internalDirectSumEquiv_intertwines
    (summand : Index → Submodule R Ambient)
    (independent : iSupIndep summand)
    (spans : ⨆ index, summand index = ⊤)
    (transition : Module.End R Ambient)
    (invariant : ∀ index, MapsTo transition (summand index) (summand index))
    (state : Π₀ index, summand index) :
    independent.linearEquiv spans
        (DirectSum.lmap
          (fun index => transition.restrict (invariant index)) state) =
      transition (independent.linearEquiv spans state) := by
  have naturality :
      (DFinsupp.lsum ℕ fun index => (summand index).subtype).comp
          (DirectSum.lmap
            (fun index => transition.restrict (invariant index))) =
        transition.comp
          (DFinsupp.lsum ℕ fun index => (summand index).subtype) := by
    have component_eq (index : Index) :
        (summand index).subtype.comp
            (transition.restrict (invariant index)) =
          transition.comp (summand index).subtype := by
      ext value
      rfl
    have map_after_sum :
        transition.comp
            (DFinsupp.lsum ℕ fun index => (summand index).subtype) =
          DFinsupp.lsum ℕ
            (fun index => transition.comp (summand index).subtype) := by
      apply DFinsupp.lhom_ext
      intro index value
      simp
    calc
      _ = DFinsupp.lsum ℕ
          (fun index => (summand index).subtype.comp
            (transition.restrict (invariant index))) := by
        apply LinearMap.ext
        intro value
        exact DFinsupp.sum_mapRange_index.linearMap
      _ = DFinsupp.lsum ℕ
          (fun index => transition.comp (summand index).subtype) := by
        congr 1
      _ = _ := map_after_sum.symm
  change
    ((DFinsupp.lsum ℕ fun index => (summand index).subtype).comp
        (DirectSum.lmap
          (fun index => transition.restrict (invariant index)))) state =
      (transition.comp
        (DFinsupp.lsum ℕ fun index => (summand index).subtype)) state
  rw [naturality]
  rfl

#print axioms internalDirectSumEquiv_intertwines

end InternalDirectSumIntertwining

section HermitianConjugacy

universe uSource uTarget

variable {Source : Type uSource} {Target : Type uTarget}
variable [AddCommGroup Source] [Module ℂ Source]
variable [AddCommGroup Target] [Module ℂ Target]

/-- Transport a common Hermitian energy through an exact linear conjugacy. -/
noncomputable def CommonHermitianEnergyLyapunov.conjugate
    (sourceTransition : Command → Module.End ℂ Source)
    (targetTransition : Command → Module.End ℂ Target)
    (equivalence : Source ≃ₗ[ℂ] Target)
    (intertwines : ∀ command state,
      equivalence (sourceTransition command state) =
        targetTransition command (equivalence state))
    (certificate : CommonHermitianEnergyLyapunov sourceTransition) :
    CommonHermitianEnergyLyapunov targetTransition where
  energy := fun state => certificate.energy (equivalence.symm state)
  rate := certificate.rate
  rate_nonneg := certificate.rate_nonneg
  rate_lt_one := certificate.rate_lt_one
  energy_nonneg := fun state => certificate.energy_nonneg _
  energy_pos := by
    intro state state_ne_zero
    apply certificate.energy_pos
    exact (equivalence.symm.map_ne_zero_iff).mpr state_ne_zero
  energy_smul := by
    intro scalar state
    rw [equivalence.symm.map_smul]
    exact certificate.energy_smul scalar (equivalence.symm state)
  parallelogram := by
    intro first second
    simpa only [map_add, map_sub] using
      certificate.parallelogram
        (equivalence.symm first) (equivalence.symm second)
  contracts := by
    intro command state
    have conjugated :
        equivalence.symm (targetTransition command state) =
          sourceTransition command (equivalence.symm state) := by
      apply equivalence.injective
      simpa only [LinearEquiv.apply_symm_apply] using
        (intertwines command (equivalence.symm state)).symm
    rw [conjugated]
    exact certificate.contracts command (equivalence.symm state)

#print axioms CommonHermitianEnergyLyapunov.conjugate

end HermitianConjugacy

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
