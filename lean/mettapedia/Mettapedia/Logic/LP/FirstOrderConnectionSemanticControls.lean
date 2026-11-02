import Mettapedia.Logic.LP.FirstOrderConnectionTrace

/-!
# First-order connection semantics: accepted refutations and actual models

The negative matrix has an explicit nonempty first-order model. Every
accepted proof is excluded by the semantic theorem, for every unification
fuel. The positive variable/constant connection is checked by the actual
unifier and replay rather than an assumed operational derivation.
-/

namespace Mettapedia.Logic.LP.FirstOrderConnectionSemanticControls

noncomputable section

open FirstOrderBridge

abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Bool
  relationArity _ := 1
  functionSymbols := Unit
  functionArity _ := 1

def predicate (symbol : Bool) (term : Term signature) : Atom signature :=
  ⟨symbol, fun _ => term⟩

instance unitStructure : (language signature).Structure Unit where
  funMap _ _ := ()
  RelMap symbol _ := match symbol with
    | .relation truth => truth = true

def satisfiableMatrix : ConnFOCNF signature :=
  [[.pos (predicate false (.var 0)), .pos (predicate true (.var 0))],
   [.neg (predicate false (.var 0)), .neg (predicate true (.var 0))],
   [.pos (predicate true (.var 0))]]

theorem the_satisfiable_matrix_has_a_nonempty_first_order_model :
    @ConnFOModels signature satisfiableMatrix Unit unitStructure := by
  intro clause member assignment
  simp only [satisfiableMatrix, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact ⟨.pos (predicate true (.var 0)), by simp,
      by change true = true; rfl⟩
  · exact ⟨.neg (predicate false (.var 0)), by simp,
      by change ¬ false = true; decide⟩
  · exact ⟨.pos (predicate true (.var 0)), by simp,
      by change true = true; rfl⟩

theorem every_proof_and_fuel_reject_this_satisfiable_matrix (proof : FOProofObj signature) (fuel : Nat) :
    checkProofFO satisfiableMatrix fuel proof = false :=
  checkProofFO_rejects_model satisfiableMatrix fuel proof the_satisfiable_matrix_has_a_nonempty_first_order_model

def positiveRoot : ConnFOClause signature := [.pos (predicate true (.var 0))]
def negativeUnit : ConnFOClause signature := [.neg (predicate true (.const 7))]
def inconsistentMatrix : ConnFOCNF signature := [positiveRoot, negativeUnit]
def variableConnectionProof : FOProofObj signature :=
  ⟨1, positiveRoot, [.step_extend negativeUnit (.neg (predicate true (.const 7)))]⟩

theorem the_actual_variable_constant_connection_is_accepted :
    checkProofFO inconsistentMatrix 3 variableConnectionProof = true := by
  have unified : unifyComplementLit? 3 (.pos (predicate true (.var 0)))
      (.neg (predicate true (.const 7))) = some (Subst.single (σ := signature) 0 (.const 7)) := by
    change some ((Subst.id signature).comp (Subst.single (σ := signature) 0 (.const 7))) =
      some (Subst.single (σ := signature) 0 (.const 7))
    congr 1
    funext name
    exact Subst.applyTerm_id _
  simp [checkProofFO, variableConnectionProof, inconsistentMatrix, replayFO, positiveRoot,
    replayFOAgenda, unified, negativeUnit]

theorem acceptance_excludes_every_nonempty_structure (Model : Type*) [Nonempty Model]
    [(language signature).Structure Model] : ¬ ConnFOModels inconsistentMatrix Model :=
  checkProofFO_unsatisfiable inconsistentMatrix 3 variableConnectionProof the_actual_variable_constant_connection_is_accepted

end

end Mettapedia.Logic.LP.FirstOrderConnectionSemanticControls
