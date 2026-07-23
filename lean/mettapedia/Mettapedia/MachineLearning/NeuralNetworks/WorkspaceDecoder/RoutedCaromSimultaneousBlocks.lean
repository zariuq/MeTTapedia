import Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder.RoutedCaromBlockStability
import Mathlib.LinearAlgebra.Eigenspace.Pi

/-!
# Routed CAROM: simultaneous generalized-eigenspace blocks

A commuting finite-dimensional family over an algebraically closed field
decomposes into simultaneous generalized-eigenspace blocks.  On each such
block, every command is its block eigenvalue times the identity plus a
nilpotent residual.  The residuals continue to commute after restriction.

This is the algebraic decomposition needed before constructing and assembling
local Lyapunov metrics.  It does not yet transport a complex block metric back
to a real coordinate basis.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder

open Function Set

namespace RoutedCarom

universe uCommand uField uState

section SimultaneousBlocks

variable {Command : Type uCommand}
variable {K : Type uField} [Field K]
variable {V : Type uState} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Algebraic joint nilpotence for a finite schedule of endomorphisms. -/
def EndJointlyNilpotentAt
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State) (depth : ℕ) : Prop :=
  ∀ schedule : List Command, schedule.length = depth →
    (schedule.map residual).prod = 0

/-- The simultaneous maximal generalized eigenspace selected by one family
of candidate eigenvalues. -/
def simultaneousGenBlock
    (transition : Command → Module.End K V) (character : Command → K) :
    Submodule K V :=
  ⨅ command, (transition command).maxGenEigenspace (character command)

omit [FiniteDimensional K V] in
/-- Pairwise commutation, including the diagonal case, written in the form
used by restriction lemmas. -/
theorem commuteAll_of_pairwise
    (transition : Command → Module.End K V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second)) :
    ∀ first second, Commute (transition first) (transition second) := by
  intro first second
  rcases eq_or_ne first second with rfl | distinct
  · exact Commute.refl _
  · exact commutes distinct

omit [FiniteDimensional K V] in
/-- Every command preserves every simultaneous generalized-eigenspace block. -/
theorem mapsTo_simultaneousGenBlock
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    MapsTo (transition command)
      (simultaneousGenBlock transition character)
      (simultaneousGenBlock transition character) := by
  intro state state_mem
  apply (Submodule.span_singleton_le_iff_mem _ _).1
  rw [simultaneousGenBlock]
  refine le_iInf fun blockCommand => ?_
  apply (Submodule.span_singleton_le_iff_mem _ _).2
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (commutes blockCommand command) (character blockCommand)
    ((iInf_le (fun indexedCommand =>
      (transition indexedCommand).maxGenEigenspace (character indexedCommand))
      blockCommand) state_mem)

omit [FiniteDimensional K V] in
/-- The scalar-shifted residual also preserves a simultaneous block. -/
theorem mapsTo_simultaneousGenBlock_residual
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    MapsTo
      (transition command - algebraMap K (Module.End K V) (character command))
      (simultaneousGenBlock transition character)
      (simultaneousGenBlock transition character) := by
  intro state state_mem
  exact (simultaneousGenBlock transition character).sub_mem
    (mapsTo_simultaneousGenBlock transition commutes character command state_mem)
    ((simultaneousGenBlock transition character).smul_mem _ state_mem)

/-- A command restricted to one simultaneous block. -/
noncomputable def simultaneousBlockTransition
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    Module.End K (simultaneousGenBlock transition character) :=
  (transition command).restrict
    (mapsTo_simultaneousGenBlock transition commutes character command)

/-- The nilpotent part of a command on one simultaneous block. -/
noncomputable def simultaneousBlockResidual
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    Module.End K (simultaneousGenBlock transition character) :=
  (transition command - algebraMap K (Module.End K V) (character command)).restrict
    (mapsTo_simultaneousGenBlock_residual transition commutes character command)

/-- On a simultaneous generalized-eigenspace block, each scalar-shifted
command residual is nilpotent. -/
theorem simultaneousBlockResidual_isNilpotent
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    IsNilpotent
      (simultaneousBlockResidual transition commutes character command) := by
  apply Module.End.isNilpotent_restrict_of_le
    (q := (transition command).maxGenEigenspace (character command))
    (iInf_le (fun blockCommand =>
      (transition blockCommand).maxGenEigenspace (character blockCommand)) command)
  exact (transition command).isNilpotent_restrict_maxGenEigenspace_sub_algebraMap
    (character command)

omit [FiniteDimensional K V] in
/-- Removing scalar identity parts preserves pairwise command commutation. -/
theorem commute_residuals
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (first second : Command) :
    Commute
      (transition first - algebraMap K (Module.End K V) (character first))
      (transition second - algebraMap K (Module.End K V) (character second)) := by
  exact
    ((commutes first second).sub_right
      (Algebra.commute_algebraMap_right (character second) (transition first))).sub_left
      (Algebra.commute_algebraMap_left (character first)
        (transition second - algebraMap K (Module.End K V) (character second)))

omit [FiniteDimensional K V] in
/-- The nilpotent residuals continue to commute after restriction to a
simultaneous block. -/
theorem simultaneousBlockResidual_commute
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (first second : Command) :
    Commute
      (simultaneousBlockResidual transition commutes character first)
      (simultaneousBlockResidual transition commutes character second) := by
  exact LinearMap.restrict_commute
    (commute_residuals transition commutes character first second)
    (mapsTo_simultaneousGenBlock_residual transition commutes character first)
    (mapsTo_simultaneousGenBlock_residual transition commutes character second)

omit [FiniteDimensional K V] in
/-- Exact scalar-plus-residual decomposition on each simultaneous block. -/
theorem simultaneousBlockTransition_eq_scalar_add_residual
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) (command : Command) :
    simultaneousBlockTransition transition commutes character command =
      algebraMap K
          (Module.End K (simultaneousGenBlock transition character))
          (character command) +
        simultaneousBlockResidual transition commutes character command := by
  ext state
  simp [simultaneousBlockTransition, simultaneousBlockResidual]

/-- Over an algebraically closed field, the simultaneous generalized blocks
of a commuting family span the whole finite-dimensional state space. -/
theorem iSup_simultaneousGenBlock_eq_top
    [IsAlgClosed K]
    (transition : Command → Module.End K V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second)) :
    ⨆ character : Command → K,
      simultaneousGenBlock transition character = ⊤ := by
  exact Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    transition commutes (fun command => Module.End.iSup_maxGenEigenspace_eq_top _)

omit [FiniteDimensional K V] in
/-- Distinct simultaneous generalized characters give independent blocks.
This is stronger than pairwise disjointness and is the algebraic input needed
for an internal direct-sum decomposition. -/
theorem iSupIndep_simultaneousGenBlock
    (transition : Command → Module.End K V) :
    iSupIndep (simultaneousGenBlock transition) := by
  unfold simultaneousGenBlock
  exact iSupIndep.iInf
    (fun command eigenvalue =>
      (transition command).maxGenEigenspace eigenvalue)
    (fun command => (transition command).independent_genEigenspace ⊤)

/-- Removing the zero simultaneous blocks preserves both independence and
their supremum. -/
theorem activeSimultaneousBlocks_internal
    [IsAlgClosed K]
    (transition : Command → Module.End K V)
    (commutes : Pairwise fun first second =>
      Commute (transition first) (transition second)) :
    let active := { character : Command → K //
      simultaneousGenBlock transition character ≠ ⊥ }
    iSupIndep (fun character : active =>
        simultaneousGenBlock transition character) ∧
      (⨆ character : active,
        simultaneousGenBlock transition character) = ⊤ := by
  dsimp only
  constructor
  · simpa only [iSupIndep_ne_bot] using
      iSupIndep_simultaneousGenBlock transition
  · rw [iSup_ne_bot_subtype]
    exact iSup_simultaneousGenBlock_eq_top transition commutes

section FiniteCommands

variable [Fintype Command] [DecidableEq Command]

omit [Fintype Command] [DecidableEq Command] in
/-- A mapped list from a globally commuting endomorphism family is pairwise
commuting. -/
theorem mappedEnd_pairwiseCommute
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State)
    (commutes : ∀ first second,
      Commute (residual first) (residual second))
    (schedule : List Command) :
    (schedule.map residual).Pairwise Commute := by
  induction schedule with
  | nil => simp
  | cons command schedule ih =>
      simp only [List.map_cons, List.pairwise_cons]
      constructor
      · intro mapped mapped_mem
        obtain ⟨other, _, rfl⟩ := List.mem_map.mp mapped_mem
        exact commutes command other
      · exact ih

/-- Pairwise commuting, individually nilpotent endomorphisms have a finite
joint nilpotence budget. -/
theorem pairwiseCommuting_individuallyNilpotent_endJointlyNilpotentAt
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State)
    (nilpotenceDepth : Command → ℕ)
    (depth_pos : ∀ command, 0 < nilpotenceDepth command)
    (individuallyNilpotent : ∀ command,
      residual command ^ nilpotenceDepth command = 0)
    (commutes : ∀ first second,
      Commute (residual first) (residual second)) :
    EndJointlyNilpotentAt residual
      (jointNilpotenceBudget nilpotenceDepth) := by
  classical
  intro schedule schedule_length
  obtain ⟨command, depth_le_count⟩ :=
    exists_nilpotenceDepth_le_count nilpotenceDepth depth_pos schedule schedule_length
  let repeated := List.replicate (nilpotenceDepth command) command
  have repeated_subperm : List.Subperm repeated schedule := by
    apply List.subperm_iff_count.mpr
    intro other
    by_cases other_eq : other = command
    · subst other
      simpa [repeated] using depth_le_count
    · have other_not_mem : other ∉ repeated := by
        simp [repeated, other_eq]
      rw [List.count_eq_zero.mpr other_not_mem]
      exact Nat.zero_le _
  have grouped_perm :
      List.Perm (repeated ++ schedule.diff repeated) schedule :=
    List.subperm_append_diff_self_of_count_le
      (List.subperm_ext_iff.mp repeated_subperm)
  have mapped_prod_eq :
      ((repeated ++ schedule.diff repeated).map residual).prod =
        (schedule.map residual).prod :=
    (grouped_perm.map residual).prod_eq'
      (mappedEnd_pairwiseCommute residual commutes _)
  rw [← mapped_prod_eq, List.map_append, List.prod_append]
  have repeated_prod_zero : (repeated.map residual).prod = 0 := by
    simp [repeated, individuallyNilpotent command]
  rw [repeated_prod_zero, zero_mul]

/-- Choose a positive nilpotence exponent uniformly command-by-command from
individual `IsNilpotent` witnesses. -/
noncomputable def positiveNilpotenceDepth
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State)
    (nilpotent : ∀ command, IsNilpotent (residual command))
    (command : Command) : ℕ :=
  Classical.choose (nilpotent command) + 1

omit [Fintype Command] [DecidableEq Command] in
theorem positiveNilpotenceDepth_pos
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State)
    (nilpotent : ∀ command, IsNilpotent (residual command))
    (command : Command) :
    0 < positiveNilpotenceDepth residual nilpotent command := by
  simp [positiveNilpotenceDepth]

omit [Fintype Command] [DecidableEq Command] in
theorem pow_positiveNilpotenceDepth_eq_zero
    {State : Type*} [AddCommMonoid State] [Module K State]
    (residual : Command → Module.End K State)
    (nilpotent : ∀ command, IsNilpotent (residual command))
    (command : Command) :
    residual command ^ positiveNilpotenceDepth residual nilpotent command = 0 := by
  rw [positiveNilpotenceDepth, pow_succ,
    Classical.choose_spec (nilpotent command), zero_mul]

/-- The residual family on every simultaneous block is jointly nilpotent at
an explicit finite counting budget. -/
theorem simultaneousBlockResidual_endJointlyNilpotentAt
    (transition : Command → Module.End K V)
    (commutes : ∀ first second,
      Commute (transition first) (transition second))
    (character : Command → K) :
    let residual := simultaneousBlockResidual transition commutes character
    let nilpotent : ∀ command, IsNilpotent (residual command) :=
      simultaneousBlockResidual_isNilpotent transition commutes character
    EndJointlyNilpotentAt residual
      (jointNilpotenceBudget
        (positiveNilpotenceDepth residual nilpotent)) := by
  dsimp only
  apply pairwiseCommuting_individuallyNilpotent_endJointlyNilpotentAt
  · exact positiveNilpotenceDepth_pos _ _
  · exact pow_positiveNilpotenceDepth_eq_zero _ _
  · exact simultaneousBlockResidual_commute transition commutes character

end FiniteCommands

#print axioms commuteAll_of_pairwise
#print axioms mapsTo_simultaneousGenBlock
#print axioms simultaneousBlockResidual_isNilpotent
#print axioms simultaneousBlockResidual_commute
#print axioms simultaneousBlockTransition_eq_scalar_add_residual
#print axioms iSup_simultaneousGenBlock_eq_top
#print axioms iSupIndep_simultaneousGenBlock
#print axioms activeSimultaneousBlocks_internal
#print axioms pairwiseCommuting_individuallyNilpotent_endJointlyNilpotentAt
#print axioms simultaneousBlockResidual_endJointlyNilpotentAt

end SimultaneousBlocks

end RoutedCarom

end Mettapedia.MachineLearning.NeuralNetworks.WorkspaceDecoder
