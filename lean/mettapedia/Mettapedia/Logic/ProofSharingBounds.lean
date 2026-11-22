import Mettapedia.OSLF.NativeTypes.Certificates.FiniteTreeExecution
import Mettapedia.OSLF.NativeTypes.Certificates.Shared.Cache
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses

/-!
# A forced exponential tree expansion with linear DAG sharing

The fixed calculus has a base judgment `0` and one rule deriving `n+1` from
two occurrences of `n`. Every accepted proof tree of `n` therefore contains
exactly `2^(n+1)-1` nodes. A chronological DAG keeps one checked node per level
and cites the same previous node twice. This is a concrete separation of
representations for one calculus, not a separation of Frege and extended
Frege, and not merely a poor compiler's output.

The size accounts below count nodes, references and unary-encoded rule and
reference indices. No constant-time unbounded-integer assumption is needed
for the certificate-size comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSharingBounds

open Mettapedia.OSLF.NativeTypes.Certificates

inductive Rule where
  | base
  | duplicate (level : Nat)
  deriving DecidableEq, Repr

def conclusion : Rule → Nat
  | .base => 0
  | .duplicate level => level + 1

def premises : Rule → List Nat
  | .base => []
  | .duplicate level => [level, level]

abbrev presentation : Presentation where
  Judgment := Nat
  Rule := Rule
  conclusion := conclusion
  premises := premises

/-- A bound for every accepted tree, rather than for a selected unfolding. -/
theorem accepted_tree_nodes (tree : Tree presentation) (level : Nat)
    (accepted : tree.check level = true) :
    TreeExecution.nodes tree + 1 = 2 ^ (level + 1) := by
  induction tree generalizing level with
  | node rule children ih =>
      have checked : decide (conclusion rule = level) = true ∧
          decide (∀ position, (children position).check ((premises rule).get position) = true) = true := by
        simpa only [Tree.check, Bool.and_eq_true] using accepted
      have root := of_decide_eq_true checked.1
      have sub := of_decide_eq_true checked.2
      cases rule with
      | base =>
          have zero : level = 0 := root.symm
          subst level
          simp [TreeExecution.nodes, presentation, premises, conclusion]
      | duplicate smaller =>
          change Fin 2 → Tree presentation at children
          have next : level = smaller + 1 := root.symm
          subst level
          have left := ih (0 : Fin 2) smaller (sub (0 : Fin 2))
          have right := ih (1 : Fin 2) smaller (sub (1 : Fin 2))
          change (1 + (TreeExecution.nodes (children (0 : Fin 2)) +
            (TreeExecution.nodes (children (1 : Fin 2)) + 0))) + 1 = 2 ^ (smaller + 1 + 1)
          rw [pow_succ]
          omega

/-- A DAG row keeps both ordered uses of the previous proof. -/
def baseRow : Shared.Row presentation := ⟨.base, Fin.elim0⟩

def duplicateRow (level : Nat) : Shared.Row presentation := ⟨.duplicate level, fun _ => level⟩

def rows (level : Nat) : List (Shared.Row presentation) :=
  baseRow :: (List.range level).map duplicateRow

def certificate (level : Nat) : Shared.Certificate presentation := ⟨rows level, level⟩

theorem rows_length (level : Nat) : (rows level).length = level + 1 := by
  simp [rows]

theorem premiseSlots (level : Nat) : Shared.premiseSlots (rows level) = 2 * level := by
  simp [Shared.premiseSlots, rows, baseRow, duplicateRow, presentation, premises,
    List.map_map, Function.comp_def, Nat.mul_comm]

theorem inspect_duplicate (table : List Nat) (level : Nat)
    (present : table[level]? = some level) :
    Shared.inspectRow table (duplicateRow level) = (true, 2) := by
  simp [Shared.inspectRow, Shared.inspectPremises, duplicateRow, presentation, premises,
    List.finRange_succ, List.finRange_zero, List.map_cons, List.map_nil, present]

theorem inspect_tail (count level : Nat) (table : List Nat)
    (previous : table[level]? = some level) (prefixLength : table.length = level + 1) :
    (Shared.inspectRows table
      ((List.range' level count).map duplicateRow)).table =
      some (table ++ List.range' (level + 1) count) := by
  induction count generalizing level table with
  | zero => simp [Shared.inspectRows]
  | succ count ih =>
      have nextPresent : (table ++ [level + 1])[level + 1]? = some (level + 1) := by
        rw [← prefixLength]
        simp
      simp only [List.range'_succ, List.map_cons, Shared.inspectRows,
        inspect_duplicate table level previous, ↓reduceIte]
      change (Shared.inspectRows (table ++ [level + 1])
        ((List.range' (level + 1) count).map duplicateRow)).table = _
      rw [ih (level + 1) (table ++ [level + 1]) nextPresent (by simp [prefixLength])]
      simp [presentation, List.append_assoc]

theorem dag_checked (level : Nat) : Shared.checkJudgments (certificate level) level = true := by
  have tail := inspect_tail level 0 [0] rfl rfl
  have table : (Shared.inspectRows [] (rows level)).table = some (List.range (level + 1)) := by
    simpa [rows, baseRow, Shared.inspectRows, Shared.inspectRow, Shared.inspectPremises,
      presentation, premises, conclusion, List.range_eq_range', List.range'_succ] using tail
  simp only [Shared.checkJudgments, Shared.checkJudgmentsWithWork_eq_inspectRows, certificate, table]
  simp

/-- The accepted DAG performs exactly two premise checks per nonbase row and
one final root comparison. Neither repeated occurrence is erased. -/
theorem dag_work (level : Nat) :
    Shared.checkJudgmentsWithWork (certificate level) level =
      (true, level + 1, 2 * level + 1) := by
  have checked := dag_checked level
  have exactWork := Shared.checkJudgments_work_eq (certificate level) level checked
  simp only [certificate] at exactWork
  rw [rows_length, premiseSlots] at exactWork
  exact Prod.ext checked (Prod.ext exactWork.1 exactWork.2)

def ruleSize : Rule → Nat
  | .base => 1
  | .duplicate level => level + 2

/-- Unary indices overestimate binary references. Both uses of a shared
premise are charged, as are the rule constructor and its level. -/
def rowSize (row : Shared.Row presentation) : Nat :=
  ruleSize row.rule + 1 +
    (List.ofFn fun position => row.references position + 1).sum

def certificateSize (proof : Shared.Certificate presentation) : Nat :=
  proof.root + 1 + (proof.rows.map rowSize).sum

theorem rowSize_duplicate (level : Nat) : rowSize (duplicateRow level) = 3 * level + 5 := by
  simp [rowSize, ruleSize, duplicateRow, presentation, premises, List.ofFn_succ]
  omega

theorem certificateSize_zero : certificateSize (certificate 0) = 3 := rfl

theorem certificateSize_succ (level : Nat) :
    certificateSize (certificate (level + 1)) = certificateSize (certificate level) + 3 * level + 6 := by
  simp only [certificateSize, certificate, rows, List.range_succ, List.map_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_append, List.sum_nil,
    rowSize_duplicate]
  omega

open Mettapedia.GSLT.LanguageDef.ProofSystems

def treeSystem : SizedChecker Nat (Tree presentation) where
  check level tree := tree.check level
  claimSize level := level + 1
  certificateSize := TreeExecution.nodes

def dagSystem : SizedChecker Nat (Shared.Certificate presentation) where
  check level proof := Shared.checkJudgments proof level
  claimSize level := level + 1
  certificateSize := certificateSize

/-- Canonical input size is quadratic even with unary rule and reference
indices. The exponential tree lower bound is not a binary-index artifact. -/
theorem dag_input_bound (level : Nat) :
    dagSystem.inputSize (level, certificate level) ≤ 4 * (level + 1) ^ 2 := by
  change level + 1 + certificateSize (certificate level) ≤ _
  induction level with
  | zero => rw [certificateSize_zero]; decide
  | succ level ih =>
      rw [certificateSize_succ]
      nlinarith

theorem tree_lower_bound (level : Nat) (tree : Tree presentation)
    (accepted : treeSystem.check level tree = true) : 2 ^ level ≤ treeSystem.certificateSize tree := by
  have forced := accepted_tree_nodes tree level accepted
  have positive : 0 < 2 ^ level := Nat.pow_pos (by decide)
  rw [pow_succ] at forced
  change 2 ^ level ≤ TreeExecution.nodes tree
  omega

/-- A computable size translation in the other direction. No executed
polynomial-time compiler claim is attached to this size-only structure. -/
def dag_sizeSimulates_tree : SizeSimulation dagSystem treeSystem where
  translate level _ := certificate level
  preserves := fun level _ _ => dag_checked level
  sizeBound := by
    refine ⟨4 * Polynomial.X ^ 2, ?_⟩
    rintro ⟨level, tree⟩
    have small := dag_input_bound level
    have base : level + 1 ≤ treeSystem.inputSize (level, tree) := Nat.le_add_right _ _
    have squares := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left base 2)
    have output : certificateSize (certificate level) ≤ dagSystem.inputSize (level, certificate level) :=
      Nat.le_add_left _ _
    simpa [dagSystem, Polynomial.eval_mul, Polynomial.eval_pow] using (output.trans small).trans squares

/-- No polynomial-size translator can replace all shared proofs of this
fixed calculus by trees. This quantifies over every accepted target tree. -/
theorem no_tree_sizeSimulation_dag : ¬ Nonempty (SizeSimulation treeSystem dagSystem) := by
  rintro ⟨simulation⟩
  obtain ⟨polynomial, bounded⟩ := simulation.sizeBound
  let envelope : Polynomial Nat := polynomial.comp (4 * (Polynomial.X + 1) ^ 2)
  obtain ⟨level, gap⟩ := exists_eval_lt_two_pow envelope 1 0
  have lower := tree_lower_bound level _ (simulation.preserves level (certificate level) (dag_checked level))
  have upper := (bounded (level, certificate level)).trans
    (eval_mono polynomial (dag_input_bound level))
  have strict : polynomial.eval (4 * (level + 1) ^ 2) < 2 ^ level := by
    simpa [envelope, Polynomial.eval_comp] using gap
  exact Nat.not_le_of_gt strict (lower.trans upper)

namespace Controls

theorem seven_nodes_for_level_two (tree : Tree presentation)
    (accepted : tree.check 2 = true) : TreeExecution.nodes tree = 7 := by
  have exactSize := accepted_tree_nodes tree 2 accepted
  norm_num at exactSize
  omega

theorem level_three_dag_work :
    Shared.checkJudgmentsWithWork (certificate 3) 3 = (true, 4, 7) := dag_work 3

theorem missing_second_premise_refused :
    Shared.checkJudgments (P := presentation)
      ⟨[baseRow, ⟨.duplicate 0, fun position => if position.val = 0 then 0 else 1⟩], 1⟩ 1 = false := by decide

end Controls

end Mettapedia.Logic.ProofSharingBounds
