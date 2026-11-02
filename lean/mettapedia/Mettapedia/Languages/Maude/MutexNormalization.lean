import Mettapedia.Languages.Maude.ACUFlattenSubstitution
import Mettapedia.Languages.Maude.Examples

/-! The mutex initialization equation and its normalized transition domain.
No transition introduces init, so normalization of reachable markings never
needs to invent a new initialization token. Full E/R coherence is a separate
adequacy obligation; the full source theory is retained here.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.MutexNormalization

def mergeOperator : Operator := ⟨"mutex.merge", "__", ["Marking", "Marking"], "Marking",
  {constructor := true, associative := true, commutative := true, identity := some (.app "mutex.empty" [])}⟩

def operation : ACUOperation Examples.mutex [] where
  declaration := mergeOperator
  declared := by simp [Examples.mutex, Examples.markingOperators, mergeOperator, Examples.constant]
  arguments := rfl
  associative := rfl
  commutative := rfl
  unit := .app "mutex.empty" []
  identity := rfl
  unit_sorted := .app
    (declaration := ⟨"mutex.empty", "empty", [], "Marking", {constructor := true}⟩)
    (by simp [Examples.mutex, Examples.markingOperators]) .nil

def token (name : String) : Term := .app ("mutex." ++ name) []
def initial : Term := token "init"
def expanded : Term := operation.merge (token "idle1") (operation.merge (token "idle2") (token "permit"))
def initRow : Row := ⟨"init", [], [], initial, expanded⟩

theorem token_sorted (name : String)
    (allowed : name ∈ ["empty", "idle1", "idle2", "crit1", "crit2", "permit", "init"]) :
    HasSort Examples.mutex.signature [] (token name) "Marking" := by
  apply HasSort.app (declaration := ⟨"mutex." ++ name, name, [], "Marking", {constructor := true}⟩)
  · simp only [Examples.mutex, Examples.markingOperators, List.mem_append, List.mem_map]
    exact .inl ⟨name, allowed, rfl⟩
  · exact .nil

theorem initial_sorted : HasSort Examples.mutex.signature [] initial "Marking" := token_sorted "init" (by simp)
theorem expanded_sorted : HasSort Examples.mutex.signature [] expanded "Marking" :=
  operation.merge_sorted (token_sorted "idle1" (by simp))
    (operation.merge_sorted (token_sorted "idle2" (by simp)) (token_sorted "permit" (by simp)))

theorem init_member : initRow ∈ Examples.mutex.equations := by
  simp [initRow, Examples.mutex, initial, expanded, token, operation, ACUOperation.merge,
    mergeOperator, Examples.constant, Examples.binary]

theorem initialization_equivalent : Equivalent Examples.mutex [] "Marking" initial expanded := by
  let assignment : Valuation := Term.var
  have used : initRow.usedContext = [] := by simp [initRow, Row.usedContext]
  have valuation : TypedValuation Examples.mutex.signature [] initRow.usedContext assignment := by
    intro name sort found
    rw [used] at found
    cases found
  have equation := Equivalent.equation assignment init_member (by decide_cbv)
    (used.symm ▸ initial_sorted) (used.symm ▸ expanded_sorted) valuation (.nil assignment)
  simpa only [initRow, initial, expanded, token, ACUOperation.merge, Term.substitute,
    List.map_cons, List.map_nil] using equation

def InitFree (parts : List Term) : Prop := ∀ term ∈ parts, term ≠ initial

theorem rhs_init_free {row : Row} (member : row ∈ Examples.mutex.rules) :
    InitFree (operation.flatten row.right) := by
  simp only [Examples.mutex, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals
    simp [InitFree, operation, mergeOperator, ACUOperation.flatten, Examples.constant, Examples.binary, initial, token]

theorem partition_residual_init_free {sources selected residual : List Term}
    (free : InitFree sources) (partition : sources.Perm (selected ++ residual)) : InitFree residual :=
  fun term member => free term (partition.mem_iff.mpr (List.mem_append_right selected member))

theorem ground_commit_init_free {sources selected residual : List Term} {row : Row}
    (free : InitFree sources) (partition : sources.Perm (selected ++ residual))
    (member : row ∈ Examples.mutex.rules) : InitFree (operation.flatten row.right ++ residual) := by
  intro term inside
  rcases List.mem_append.mp inside with produced | retained
  · exact rhs_init_free member term produced
  · exact partition_residual_init_free free partition term retained

#print axioms initialization_equivalent
#print axioms ground_commit_init_free

end Mettapedia.Languages.Maude.MutexNormalization
