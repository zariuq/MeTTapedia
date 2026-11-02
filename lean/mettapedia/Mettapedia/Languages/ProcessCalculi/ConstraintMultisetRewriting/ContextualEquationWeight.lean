import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveProgress

/-!
# Structural weight of an actual contextual equation queue

Both sides contribute their existing binding-tree sizes. This measure
accounts for constructor decomposition, where equation count may increase.
Dropping a reflexive equation strictly decreases it while preserving the
whole original tail.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationWeight

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V : Type} {source : V → MetaArity S}

def equationSize (equation : Equation (Observation S source)) : Nat :=
  termSize equation.1.2.2 + termSize equation.2.2.2

def weight (problem : Problem source) : Nat := (problem.map equationSize).sum

theorem weight_nil : weight ([] : Problem source) = 0 := rfl

theorem weight_cons (equation : Equation (Observation S source)) (rest : Problem source) :
    weight (equation :: rest) = equationSize equation + weight rest := rfl

theorem weight_append (first second : Problem source) : weight (first ++ second) = weight first + weight second := by
  simp only [weight, List.map_append, List.sum_append]

theorem reflexive_decreases [DecidableEq V] {Γ : Ctx S} {sort : S.Srt}
    (term : Term (signature S source) Γ sort) (rest : Problem source) :
    weight ((ContextualReflexive.discharge term).keep_right rest).remaining <
      weight ((observe term, observe term) :: rest) := by
  rw [ContextualReflexiveProgress.remaining_is_the_original_tail (S := S) (source := source) term rest,
    weight_cons]
  change weight rest < termSize term + termSize term + weight rest
  have positive := termSize_pos term
  omega

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualEquationWeight
