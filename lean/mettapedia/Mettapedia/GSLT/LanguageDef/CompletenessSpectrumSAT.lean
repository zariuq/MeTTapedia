import Mettapedia.GSLT.LanguageDef.CompletenessSpectrum
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi

/-!
# SAT as an exact two-polarity certificate authority

SAT separates certificate completeness from search and decision cleanly.

* A satisfying assignment is a small positive certificate.
* A complete truth table is a deliberately simple negative certificate.
* The two checkers form one fail-closed tagged authority.

The truth-table format is not proposed as an efficient UNSAT format.  It is a
fully executable completeness canary against which resolution, LRAT, or other
compressed refutation authorities can later be refined.
-/

namespace Mettapedia.GSLT.LanguageDef.CompletenessSpectrum.SAT

open Mettapedia.GSLT.LanguageDef.KernelAuthority

universe uVar

/-- A propositional literal. -/
inductive Literal (Var : Type uVar) where
  | positive (atom : Var)
  | negative (atom : Var)
deriving DecidableEq

abbrev Clause (Var : Type uVar) := List (Literal Var)

abbrev CNF (Var : Type uVar) := List (Clause Var)

abbrev Assignment (Var : Type uVar) := Var -> Bool

def Literal.eval {Var : Type uVar}
    (assignment : Assignment Var) : Literal Var -> Bool
  | .positive atom => assignment atom
  | .negative atom => !(assignment atom)

def Clause.eval {Var : Type uVar}
    (clause : Clause Var) (assignment : Assignment Var) : Bool :=
  clause.any (Literal.eval assignment)

def CNF.eval {Var : Type uVar}
    (formula : CNF Var) (assignment : Assignment Var) : Bool :=
  formula.all (fun clause => clause.eval assignment)

/-- The ordinary existential model semantics of SAT. -/
def Satisfiable {Var : Type uVar} (formula : CNF Var) : Prop :=
  exists assignment : Assignment Var, formula.eval assignment = true

/-- The ordinary universal countermodel semantics of UNSAT. -/
def Unsatisfiable {Var : Type uVar} (formula : CNF Var) : Prop :=
  forall assignment : Assignment Var, formula.eval assignment = false

theorem unsatisfiable_iff_not_satisfiable
    {Var : Type uVar} (formula : CNF Var) :
    Unsatisfiable formula <-> Not (Satisfiable formula) := by
  constructor
  · intro unsatisfiable satisfiable
    obtain ⟨assignment, accepted⟩ := satisfiable
    rw [unsatisfiable assignment] at accepted
    contradiction
  · intro notSatisfiable assignment
    cases evaluated : formula.eval assignment with
    | false => rfl
    | true => exact (notSatisfiable ⟨assignment, evaluated⟩).elim

/-! ## Positive assignment authority -/

/-- Replay a proposed satisfying assignment. -/
def assignmentChecker {Var : Type uVar} :
    Checker (CNF Var) (Assignment Var) where
  check formula assignment := formula.eval assignment

/-- Satisfying assignments are exact certificates for SAT. -/
theorem assignmentChecker_authority {Var : Type uVar} :
    (assignmentChecker (Var := Var)).Authority Satisfiable where
  sound := by
    intro formula assignment accepted
    exact ⟨assignment, accepted⟩
  complete := by
    intro formula satisfiable
    exact satisfiable

/-! ## Complete truth-table authority for UNSAT -/

/-- A truth-table certificate explicitly lists assignments. -/
abbrev TruthTableCertificate (Var : Type uVar) := List (Assignment Var)

/-- The rows cover every assignment and every covered row falsifies the CNF. -/
def TruthTableValid {Var : Type uVar}
    (formula : CNF Var) (rows : TruthTableCertificate Var) : Prop :=
  (forall assignment : Assignment Var, assignment ∈ rows) /\
    forall assignment : Assignment Var, assignment ∈ rows ->
      formula.eval assignment = false

private instance truthTableValidDecidable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var]
    (formula : CNF Var) (rows : TruthTableCertificate Var) :
    Decidable (TruthTableValid formula rows) := by
  unfold TruthTableValid
  infer_instance

/-- Executable replay of a complete truth-table refutation. -/
def truthTableChecker
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    Checker (CNF Var) (TruthTableCertificate Var) where
  check formula rows :=
    @decide (TruthTableValid formula rows)
      (truthTableValidDecidable formula rows)

/-- Canonical exhaustive certificate used only to prove format completeness. -/
noncomputable def fullTruthTable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    TruthTableCertificate Var :=
  Finset.univ.toList

/-- Complete truth-table refutations are exact certificates for UNSAT. -/
theorem truthTableChecker_authority
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    (truthTableChecker (Var := Var)).Authority Unsatisfiable where
  sound := by
    intro formula rows accepted assignment
    have valid : TruthTableValid formula rows := by
      exact of_decide_eq_true accepted
    exact valid.2 assignment (valid.1 assignment)
  complete := by
    intro formula unsatisfiable
    refine ⟨fullTruthTable, ?_⟩
    apply decide_eq_true
    constructor
    · intro assignment
      simp [fullTruthTable]
    · intro assignment _
      exact unsatisfiable assignment

/-! ## A fail-closed two-polarity authority -/

abbrev PolarityClaim (Var : Type uVar) := Sum (CNF Var) (CNF Var)

abbrev PolarityCertificate (Var : Type uVar) :=
  Sum (Assignment Var) (TruthTableCertificate Var)

/-- The left tag asks for SAT evidence; the right tag asks for UNSAT evidence. -/
def polarityChecker
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    Checker (PolarityClaim Var) (PolarityCertificate Var) :=
  Checker.sum assignmentChecker truthTableChecker

def PolarityMeaning {Var : Type uVar} : PolarityClaim Var -> Prop :=
  Sum.elim Satisfiable Unsatisfiable

/-- SAT and UNSAT authorities compose without allowing a certificate to cross
its polarity tag. -/
theorem polarityChecker_authority
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    (polarityChecker (Var := Var)).Authority PolarityMeaning :=
  Checker.sum_authority assignmentChecker_authority
    truthTableChecker_authority

/-! ## Finite decision exists but is not part of replay authority -/

/-- Exhaustive SAT decision for a finite variable type.  Fast solvers may
replace this producer while retaining the independent assignment checker. -/
private instance satisfiableDecidable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var]
    (formula : CNF Var) : Decidable (Satisfiable formula) := by
  unfold Satisfiable
  infer_instance

def satisfiabilityDecisionKernel
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    Checker.DecisionKernel (CNF Var) Satisfiable where
  decide formula := decide (Satisfiable formula)
  correct := by
    intro formula
    simp

/-! ## Separating fixtures -/

namespace Canary

abbrev OneVar := Fin 1

def x : OneVar := 0

def positive : Literal OneVar := .positive x

def negative : Literal OneVar := .negative x

def trueAssignment : Assignment OneVar := fun _ => true

def falseAssignment : Assignment OneVar := fun _ => false

def positiveFormula : CNF OneVar := [[positive]]

def contradictionFormula : CNF OneVar := [[positive], [negative]]

theorem positive_assignment_accepted :
    (assignmentChecker (Var := OneVar)).check
      positiveFormula trueAssignment = true := by
  rfl

theorem wrong_assignment_rejected :
    (assignmentChecker (Var := OneVar)).check
      positiveFormula falseAssignment = false := by
  rfl

theorem contradiction_unsatisfiable :
    Unsatisfiable contradictionFormula := by
  intro assignment
  cases value : assignment x <;>
    simp [contradictionFormula, positive, negative, x,
      CNF.eval, Clause.eval, Literal.eval]

theorem complete_truth_table_accepted :
    (truthTableChecker (Var := OneVar)).check contradictionFormula
      (fullTruthTable (Var := OneVar)) = true := by
  apply decide_eq_true
  constructor
  · intro assignment
    simp [fullTruthTable]
  · intro assignment _
    exact contradiction_unsatisfiable assignment

/-- One row is not a valid UNSAT certificate even though that row falsifies
the formula: universal coverage is load-bearing evidence. -/
theorem incomplete_truth_table_rejected :
    (truthTableChecker (Var := OneVar)).check contradictionFormula
      [trueAssignment] = false := by
  change decide (TruthTableValid contradictionFormula [trueAssignment]) = false
  rw [decide_eq_false_iff_not]
  intro valid
  have included := valid.1 falseAssignment
  have different : falseAssignment ≠ trueAssignment := by
    intro same
    have pointwise := congrFun same x
    simp [falseAssignment, trueAssignment] at pointwise
  simp [different] at included

theorem contradiction_not_satisfiable :
    Not (Satisfiable contradictionFormula) :=
  (unsatisfiable_iff_not_satisfiable contradictionFormula).mp
    contradiction_unsatisfiable

/-- SAT evidence cannot be replayed against an UNSAT-tagged claim. -/
theorem cross_polarity_certificate_rejected :
    (polarityChecker (Var := OneVar)).check
      (.inr contradictionFormula) (.inl trueAssignment) = false :=
  rfl

end Canary

end Mettapedia.GSLT.LanguageDef.CompletenessSpectrum.SAT
