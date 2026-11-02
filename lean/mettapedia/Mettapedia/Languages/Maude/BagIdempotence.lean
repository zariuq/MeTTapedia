import Mettapedia.Languages.Maude.ACUFlattenSubstitution
import Mettapedia.Languages.Maude.Examples
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.InsertIdx

/-! Duplicate removal follows from the authored equation B B = B and the
selected ACU laws. The physical bag need not silently become a set. Every
removed duplicate is justified by an equation instance in its residual
context, and folding the deduplicated presentation is source-equivalent.
-/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.Languages.Maude.BagIdempotence

def mergeOperator : Operator := ⟨"set.merge", "__", ["Bag", "Bag"], "Bag",
  {constructor := true, associative := true, commutative := true, identity := some (.app "set.empty" [])}⟩

def operation : ACUOperation Examples.idempotent [] where
  declaration := mergeOperator
  declared := by simp [Examples.idempotent, Examples.bagOperators, mergeOperator, Examples.constant]
  arguments := rfl
  associative := rfl
  commutative := rfl
  unit := .app "set.empty" []
  identity := rfl
  unit_sorted := .app
    (declaration := ⟨"set.empty", "empty", [], "Bag", {constructor := true}⟩)
    (by simp [Examples.idempotent, Examples.bagOperators]) .nil

def row : Row := ⟨"idempotence", [("B", "Bag")], [],
  operation.merge (.var "B") (.var "B"), .var "B"⟩

theorem row_member : row ∈ Examples.idempotent.equations := by
  simp [Examples.idempotent, row, operation, ACUOperation.merge, mergeOperator, Examples.binary, Examples.bag]

theorem idempotent (term : Term) (typed : HasSort Examples.idempotent.signature [] term "Bag") :
    Equivalent Examples.idempotent [] "Bag" (operation.merge term term) term := by
  let assignment : Valuation := fun _ => term
  have contextSame : row.usedContext = [("B", "Bag")] := by
    simp [row, Row.usedContext, ACUOperation.merge, Term.variables]
  have variableTyped : HasSort Examples.idempotent.signature [("B", "Bag")] (.var "B") "Bag" :=
    .var (by simp [List.lookup])
  have valuation : TypedValuation Examples.idempotent.signature [] row.usedContext assignment := by
    intro name sort found
    rw [contextSame] at found
    have sortSame : sort = "Bag" := by
      simp only [List.lookup] at found
      split at found
      · exact (Option.some.inj found).symm
      · cases found
    subst sort
    exact typed
  have left : HasSort Examples.idempotent.signature row.usedContext row.left "Bag" := by
    rw [contextSame]
    apply HasSort.app operation.declared
    rw [operation.arguments]
    exact .cons variableTyped (.cons variableTyped .nil)
  have right : HasSort Examples.idempotent.signature row.usedContext row.right "Bag" := by
    rw [contextSame]
    exact variableTyped
  have equation := Equivalent.equation assignment row_member (by decide_cbv) left right valuation (.nil assignment)
  simpa only [row, ACUOperation.merge, Term.substitute, List.map_cons, List.map_nil, assignment] using equation

theorem remove_duplicate (term : Term) (rest : List Term)
    (typed : HasSort Examples.idempotent.signature [] term "Bag") (sorted : operation.Sorted rest) :
    Equivalent Examples.idempotent [] "Bag" (operation.fold (term :: term :: rest))
      (operation.fold (term :: rest)) :=
  .trans (.symm (operation.assoc typed typed (operation.fold_sorted rest sorted)))
    (operation.merge_left (idempotent term typed) (operation.fold_sorted rest sorted))

theorem absorb_member (term : Term) (rest : List Term)
    (sorted : operation.Sorted rest) (member : term ∈ rest) :
    Equivalent Examples.idempotent [] "Bag" (operation.fold (term :: rest)) (operation.fold rest) := by
  obtain ⟨selected, within, same⟩ := List.mem_iff_getElem.mp member
  have partition : rest.Perm (term :: rest.eraseIdx selected) := by
    simpa only [same] using (List.getElem_cons_eraseIdx_perm within).symm
  have remainingSorted : operation.Sorted (rest.eraseIdx selected) := fun part inside =>
    sorted part (List.mem_of_mem_eraseIdx inside)
  have allSorted : operation.Sorted (term :: rest) := fun part inside => by
    rcases List.mem_cons.mp inside with rfl | inside
    · exact sorted _ member
    · exact sorted part inside
  exact .trans (operation.fold_perm (partition.cons term) allSorted)
    (.trans (remove_duplicate term _ (sorted term member) remainingSorted)
      (.symm (operation.fold_perm partition sorted)))

theorem dedup_fold_equivalent (parts : List Term) (sorted : operation.Sorted parts) :
    Equivalent Examples.idempotent [] "Bag" (operation.fold parts) (operation.fold parts.dedup) := by
  induction parts with
  | nil => exact .refl operation.unit_sorted
  | cons first rest ih =>
    have restSorted : operation.Sorted rest := fun part member => sorted part (List.mem_cons_of_mem first member)
    by_cases member : first ∈ rest
    · rw [List.dedup_cons_of_mem member]
      exact .trans (absorb_member first rest restSorted member) (ih restSorted)
    · rw [List.dedup_cons_of_notMem member]
      exact operation.merge_right (sorted first List.mem_cons_self) (ih restSorted)

theorem normalize_equivalent (source : Term) (typed : HasSort Examples.idempotent.signature [] source "Bag") :
    Equivalent Examples.idempotent [] "Bag" source (operation.fold (operation.flatten source).dedup) :=
  .trans (operation.equivalent_fold_flatten (by decide_cbv) typed)
    (dedup_fold_equivalent _ (operation.flatten_sorted (by decide_cbv) typed))

#print axioms remove_duplicate
#print axioms normalize_equivalent

end Mettapedia.Languages.Maude.BagIdempotence
