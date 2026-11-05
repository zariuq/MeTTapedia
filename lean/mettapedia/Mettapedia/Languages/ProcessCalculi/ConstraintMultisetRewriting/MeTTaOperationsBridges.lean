import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm

/-!
# Where the MeTTa operation encodings meet MeTTa-IL, OSLF and MM2

Agreements proved elsewhere in this family:

* MeTTa-IL binding application is the transform candidate's substitution on
  first-order patterns (`MeTTaOperationsComm.applyBindings_eq_psubst`), and
  COMM and REFL agree with `ReflectionClosure.Step` over MeTTa-IL patterns
  (`comm_adequacy`, `reflect_adequacy`).
* The occurrence-commit layer under the candidate step can certify the
  completeness of the occurrences a predicate selects
  (`MeTTaOperationsCollapse.predicate_query_detects_twin`);
  the candidate step's ports cannot.

This file adds two boundaries with separating examples.

* `rest_merge_separates`, `subst_node_separates`: outside the first-order
  fragment MeTTa-IL's `applyBindings` merges a bound collection rest and
  eliminates an explicit `subst` node. The candidate step's syntactic action
  does neither. Bag decomposition belongs to a term layer with bag equality,
  as in `CanonicalMatching`, not to syntactic equality.
* `conjunction_rows_alias`, `two_reads_alias`, `two_takes_need_two`: an MM2
  conjunction may witness two sources with one stored atom, and two reads of
  the candidate step may select one occurrence. Two takes may not, which is
  the distinct-element reading of a MeTTa-IL bag pattern. Conjunctive queries
  are reads; bag left-hand sides are takes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsBridges

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MetaMeTTaComparison (atomAction)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsComm
  (psubst firstOrder)

/-! ## MeTTa-IL binding application outside the first-order fragment -/

def a : Pattern := .apply "a" []
def b : Pattern := .apply "b" []

/-- A bound rest is merged into the collection by MeTTa-IL and kept as a
name by the syntactic action. -/
theorem rest_merge_separates :
    firstOrder (.collection .hashBag [a] (some "r")) = false ∧
      applyBindings [("r", .collection .hashBag [b] none)] (.collection .hashBag [a] (some "r")) =
        .collection .hashBag [a, b] none ∧
      psubst (Bindings.lookup [("r", .collection .hashBag [b] none)]) (.collection .hashBag [a] (some "r")) =
        .collection .hashBag [a] (some "r") := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- An explicit `subst` node is eliminated by MeTTa-IL and kept by the
syntactic action. -/
theorem subst_node_separates :
    firstOrder (.subst (.bvar 0) a) = false ∧
      applyBindings [] (.subst (.bvar 0) a) = a ∧
      psubst (Bindings.lookup []) (.subst (.bvar 0) a) = .subst (.bvar 0) a := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## Conjunctions are reads; bag patterns are takes -/

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsExec

def pa : Atom := Insertion.wrap "p" (.symbol "a")
def selfAtom : Atom := .symbol "exec-alias"

/-- `(exec … (, (p $X) (p $Y)) …)` over the single stored atom `(p a)`. -/
def aliasExec : Exec :=
  ⟨selfAtom, [Insertion.wrap "p" (.var "X"), Insertion.wrap "p" (.var "Y")], [], []⟩

/-- MM2 rows form a relational product: one stored atom witnesses both sources. -/
theorem conjunction_rows_alias :
    Row {pa, selfAtom} aliasExec (fun v => if v = "X" ∨ v = "Y" then some (.symbol "a") else none) := by
  intro p member
  simp only [aliasExec, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

def aliasLabel (n : Nat) : Atom := if n = 0 then pa else .symbol "ok"

def readsBoth : RuleInstance Atom :=
  ⟨[], [Insertion.wrap "p" (.var "X"), Insertion.wrap "p" (.var "Y")], [], [], [.symbol "ok"]⟩

def takesBoth : RuleInstance Atom :=
  ⟨[Insertion.wrap "p" (.var "X"), Insertion.wrap "p" (.var "Y")], [], [], [], [.symbol "ok"]⟩

def aliasBefore : Configuration Atom Nat := ⟨[], {0}⟩

/-- Two reads of the candidate step select one occurrence. -/
theorem two_reads_alias :
    (⟨[], [0, 0], [1]⟩ : Selection Nat).Valid atomAction aliasLabel readsBoth aliasBefore := by
  refine ⟨by decide, by decide, rfl, rfl, rfl, by decide, ?_, ?_⟩
  · refine ⟨fun v => if v = "X" ∨ v = "Y" then some (.symbol "a") else none, ?_⟩
    intro e member
    simp [Selection.problem, Selection.equations, readsBoth, aliasBefore] at member
    rcases member with rfl | rfl <;> (change subst _ _ = subst _ _; decide)
  · intro check member
    simp [readsBoth] at member

/-- Two takes cannot select one occurrence: a bag pattern consumes distinct elements. -/
theorem two_takes_need_two (selection : Selection Nat) :
    ¬ selection.Valid atomAction aliasLabel takesBoth aliasBefore := by
  intro valid
  obtain ⟨first, second, taken⟩ : ∃ first second, selection.taken = [first, second] := by
    have length := valid.take_length
    simp only [takesBoth, List.length_cons, List.length_nil] at length
    match h : selection.taken, length with
    | [first, second], _ => exact ⟨first, second, rfl⟩
  have distinct := valid.take_distinct
  have present := valid.occurrences.taken_subset
  rw [taken] at distinct
  simp only [Selection.commit, taken, List.toFinset_cons, List.toFinset_nil, insert_empty_eq] at present
  have one : first ∈ aliasBefore.present := present (by simp)
  have two : second ∈ aliasBefore.present := present (by simp)
  simp only [aliasBefore, Finset.mem_singleton] at one two
  subst one two
  simp at distinct

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.MeTTaOperationsBridges
