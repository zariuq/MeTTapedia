import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationWeight
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualInterfacePotential
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternProblems

/-!
# Constraint truth and finite solver measures under queue permutation

Moving a selected equation past its retained prefix preserves every model,
active declaration, structural weight and pattern property. Mapping an
assignment preserves that permutation. These laws concern constraint truth
and the stated finite measures; the driver retains its actual queue order.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual
open ContextualActiveSupport
open ContextualEquationWeight
open ContextualPatternFragment

variable {S : Signature} {V Next : Type} {source : V → MetaArity S} {next : Next → MetaArity S}

theorem models_permutation (candidate : Assignment source next) {first second : Problem source}
    (permuted : first.Perm second) : Models candidate first ↔ Models candidate second := by
  constructor
  · exact fun solved equation member => solved equation (permuted.mem_iff.mpr member)
  · exact fun solved equation member => solved equation (permuted.mem_iff.mp member)

theorem active_permutation [DecidableEq V] {first second : Problem source} (permuted : first.Perm second) :
    active first = active second := by
  ext identity
  simp only [mem_active, permuted.mem_iff]

theorem weight_permutation {first second : Problem source} (permuted : first.Perm second) :
    weight first = weight second :=
  (permuted.map equationSize).sum_eq

theorem patterns_permutation {first second : Problem source} (permuted : first.Perm second) :
    ProblemPattern first ↔ ProblemPattern second := by
  constructor
  · exact fun patterned equation member => patterned equation (permuted.mem_iff.mpr member)
  · exact fun patterned equation member => patterned equation (permuted.mem_iff.mp member)

theorem map_permutation (assignment : Assignment source next) {first second : Problem source}
    (permuted : first.Perm second) : (mapProblem assignment first).Perm (mapProblem assignment second) :=
  permuted.map _

theorem potential_permutation [DecidableEq V] (candidate : Assignment source next)
    {first second : Problem source} (permuted : first.Perm second) :
    potential candidate (active first) = potential candidate (active second) := by
  rw [active_permutation permuted]

theorem interface_permutation [DecidableEq V] {first second : Problem source} (permuted : first.Perm second) :
    ContextualInterfacePotential.cost source (active first) = ContextualInterfacePotential.cost source (active second) := by
  rw [active_permutation permuted]

theorem selected_to_head (equation : Equation (Observation S source)) (before after : Problem source) :
    (before ++ equation :: after).Perm (equation :: (before ++ after)) := by
  induction before with
  | nil => exact .refl _
  | cons first rest smaller => exact (smaller.cons first).trans (.swap _ _ _)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualProblemPermutation
