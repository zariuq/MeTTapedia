import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameWorklist

/-!
# Reflexive normalization exposes actual identical meta-root leaves

Rigid heads are decomposed by the existing normalizer. An arbitrary
contextual-hole application is retained as one leaf, including repeated
or compound arguments. No pattern-spine restriction is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualResidual

variable {S : Signature} {V W : Type} {source : V → MetaArity S}

structure Leaf (source : V → MetaArity S) where
  context : Ctx S
  identity : V
  arguments : Args (signature S source) ((source identity).1.map (fun sort => ([], sort))) context

def Leaf.term (leaf : Leaf source) : Term (signature S source) leaf.context (source leaf.identity).2 :=
  .op (.inr (.mk leaf.identity)) leaf.arguments
def Leaf.observation (leaf : Leaf source) : Observation S source := observe leaf.term

def diagonals (observations : List (Observation S source)) : Problem source := observations.map fun value => (value, value)
def leafProblem (leaves : List (Leaf source)) : Problem source := diagonals (leaves.map Leaf.observation)

mutual
def leaves : {Γ : Ctx S} → {sort : S.Srt} → Term (signature S source) Γ sort → List (Leaf source)
  | _, _, .var _ => []
  | _, _, .op (.inl _) arguments => argumentLeaves arguments
  | context, _, .op (.inr (.mk identity)) arguments => [⟨context, identity, arguments⟩]

def argumentLeaves : {arities : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    Args (signature S source) arities Γ → List (Leaf source)
  | _, _, .nil => []
  | _, _, .cons head tail => leaves head ++ argumentLeaves tail
end

def observedLeaves (observation : Observation S source) : List (Leaf source) := leaves observation.2.2
def queueLeaves (observations : List (Observation S source)) : List (Leaf source) := observations.flatMap observedLeaves

theorem diagonals_models {next : W → MetaArity S} (candidate : Assignment source next)
    (observations : List (Observation S source)) : Models candidate (diagonals observations) := by
  intro equation member
  obtain ⟨value, _present, rfl⟩ := List.mem_map.mp member
  rfl

theorem leaf_models {next : W → MetaArity S} (candidate : Assignment source next) (values : List (Leaf source)) :
    Models candidate (leafProblem values) := diagonals_models candidate _

theorem leafProblem_append (first second : List (Leaf source)) :
    leafProblem (first ++ second) = leafProblem first ++ leafProblem second := by
  simp only [leafProblem, diagonals, List.map_append]

variable [∀ result, DecidableEq (S.Op result)]

mutual
theorem terms_self : ∀ {Γ : Ctx S} {sort : S.Srt} (term : Term (signature S source) Γ sort),
    ContextualRigidSolver.terms term term = some (leafProblem (leaves term))
  | _, _, .var _ => by simp [ContextualRigidSolver.terms, leaves, leafProblem, diagonals]
  | _, _, .op (.inl _) arguments => by
      simp only [ContextualRigidSolver.terms, dite_true, leaves]
      exact arguments_self arguments
  | _, _, .op (.inr (.mk _)) _ => by simp only [ContextualRigidSolver.terms]; rfl

theorem arguments_self : ∀ {arities : List (List S.Srt × S.Srt)} {Γ : Ctx S}
    (arguments : Args (signature S source) arities Γ),
    ContextualRigidSolver.arguments arguments arguments = some (leafProblem (argumentLeaves arguments))
  | _, _, .nil => by simp only [ContextualRigidSolver.arguments]; rfl
  | _, _, .cons head tail => by
      simp only [ContextualRigidSolver.arguments, terms_self head, arguments_self tail, argumentLeaves,
        leafProblem_append]
      rfl
end

variable [DecidableEq S.Srt]

theorem equation_self (observation : Observation S source) :
    ContextualRigidSolver.equation (observation, observation) = some (leafProblem (observedLeaves observation)) := by
  rcases observation with ⟨context, sort, term⟩
  simpa only [ContextualRigidSolver.equation, observedLeaves, dif_pos] using terms_self term

theorem normalize_diagonals (observations : List (Observation S source)) :
    ContextualRigidSolver.normalize (diagonals observations) = some (leafProblem (queueLeaves observations)) := by
  induction observations with
  | nil => rfl
  | cons head tail earlier =>
      change ContextualRigidSolver.merge (ContextualRigidSolver.equation (head, head))
        (ContextualRigidSolver.normalize (diagonals tail)) = _
      rw [equation_self, earlier]
      change some (leafProblem (observedLeaves head) ++ leafProblem (queueLeaves tail)) = _
      rw [← leafProblem_append]
      rfl

theorem normalize_leaves (values : List (Leaf source)) :
    ContextualRigidSolver.normalize (leafProblem values) = some (leafProblem values) := by
  induction values with
  | nil => rfl
  | cons head tail earlier =>
      change ContextualRigidSolver.merge (ContextualRigidSolver.equation (head.observation, head.observation))
        (ContextualRigidSolver.normalize (leafProblem tail)) = _
      rw [equation_self, earlier]
      rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReflexiveRun
