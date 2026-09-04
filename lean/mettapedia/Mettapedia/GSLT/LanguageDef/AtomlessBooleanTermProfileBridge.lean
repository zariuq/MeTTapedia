import Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision

/-!
# Boolean terms as exact atomless-profile observations

The atomless profile decision procedure observes which Venn cells of a finite
valuation are nonzero.  This module proves that those observations determine
the value of every ordinary Boolean-algebra term, then compiles equations into
profile formulas.

The bridge is semantic rather than representational: Boolean terms retain
their ordinary algebraic interpretation, profile formulas retain their cold
carrier semantics, and the compilation theorem relates the two independently
defined meanings.  Atomlessness is needed only when the finite profile
evaluator eliminates quantifiers; the term and equation bridge itself holds in
every Boolean algebra.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge

open Mettapedia.Foundations.Gunk
open Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
open Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileDecision

universe u

/-! ## A Boolean term is constant on each Venn cell -/

/-- Intersecting a term value with a Venn cell either returns the whole cell
or zero, according to the ordinary two-valued evaluation of the same term on
that cell's polarity assignment. -/
theorem cellValue_inf_term_eval
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (cell : Cell arity)
    (term : Term (Fin arity)) :
    cellValue valuation cell ⊓ term.eval valuation =
      if term.eval cell then cellValue valuation cell else ⊥ := by
  induction term with
  | atom name =>
      cases cellValueAt : cell name
      · simp only [Term.eval, cellValueAt, Bool.false_eq_true,
          ↓reduceIte]
        have belowComplement :
            cellValue valuation cell ≤ (valuation name)ᶜ := by
          simpa only [cellValueAt, Bool.false_eq_true, ↓reduceIte] using
            cellValue_le_literal valuation cell name
        exact disjoint_iff.mp
          (le_compl_iff_disjoint_right.mp belowComplement)
      · simp only [Term.eval, cellValueAt, ↓reduceIte]
        exact inf_eq_left.mpr (by
          simpa only [cellValueAt, ↓reduceIte] using
            cellValue_le_literal valuation cell name)
  | bottom => simp [Term.eval]
  | top => simp [Term.eval]
  | meet left right leftIH rightIH =>
      rw [Term.eval]
      have distribute :
          cellValue valuation cell ⊓
              (left.eval valuation ⊓ right.eval valuation) =
            (cellValue valuation cell ⊓ left.eval valuation) ⊓
              (cellValue valuation cell ⊓ right.eval valuation) := by
        calc
          cellValue valuation cell ⊓
                (left.eval valuation ⊓ right.eval valuation) =
              (cellValue valuation cell ⊓ cellValue valuation cell) ⊓
                (left.eval valuation ⊓ right.eval valuation) := by
            rw [inf_idem]
          _ = (cellValue valuation cell ⊓ left.eval valuation) ⊓
                (cellValue valuation cell ⊓ right.eval valuation) := by
            ac_rfl
      rw [distribute, leftIH, rightIH]
      cases leftValue : left.eval cell <;>
        cases rightValue : right.eval cell <;>
        simp [Term.eval, leftValue, rightValue]
  | join left right leftIH rightIH =>
      rw [Term.eval, inf_sup_left, leftIH, rightIH]
      cases leftValue : left.eval cell <;>
        cases rightValue : right.eval cell <;>
        simp [Term.eval, leftValue, rightValue]
  | complement body bodyIH =>
      cases bodyValue : body.eval cell
      · have bodyDisjoint :
            Disjoint (cellValue valuation cell) (body.eval valuation) := by
          apply disjoint_iff.mpr
          simpa only [bodyValue, Bool.false_eq_true, ↓reduceIte] using bodyIH
        have belowComplement :
            cellValue valuation cell ≤ (body.eval valuation)ᶜ :=
          le_compl_iff_disjoint_right.mpr bodyDisjoint
        simpa [Term.eval, bodyValue] using
          (inf_eq_left.mpr belowComplement)
      · have belowBody :
            cellValue valuation cell ≤ body.eval valuation := by
          apply inf_eq_left.mp
          simpa only [bodyValue, ↓reduceIte] using bodyIH
        have complementDisjoint :
            Disjoint (cellValue valuation cell) (body.eval valuation)ᶜ :=
          disjoint_compl_right_iff.mpr belowBody
        simpa [Term.eval, bodyValue] using
          disjoint_iff.mp complementDisjoint

/-! ## Venn-cell intersections separate algebra elements -/

/-- A valuation is recovered from its head and tail components. -/
theorem extendValuation_head_tail
    {B : Type u} {arity : Nat} (valuation : Fin (arity + 1) -> B) :
    extendValuation (valuation 0) (fun index => valuation index.succ) =
      valuation := by
  funext index
  refine Fin.cases ?_ (fun _tailIndex => ?_) index
  · rfl
  · rfl

/-- If two algebra elements have the same intersection with every Venn cell,
then they are equal.  The proof is structural: the newest variable and its
complement split both elements, while the induction hypothesis separates the
two resulting tails. -/
theorem cellIntersections_separate
    {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> (valuation : Fin arity -> B) -> (left right : B) ->
      (forall cell : Cell arity,
        cellValue valuation cell ⊓ left =
          cellValue valuation cell ⊓ right) ->
      left = right := by
  intro arity
  induction arity with
  | zero =>
      intro valuation left right equalOnCells
      let emptyCell : Cell 0 := Fin.elim0
      simpa only [cellValue_zero, top_inf_eq] using
        equalOnCells emptyCell
  | succ arity inductionHypothesis =>
      intro valuation left right equalOnCells
      let head : B := valuation 0
      let tail : Fin arity -> B := fun index => valuation index.succ
      have positive : head ⊓ left = head ⊓ right := by
        apply inductionHypothesis tail
        intro cell
        have atCell := equalOnCells (extendCell true cell)
        rw [← extendValuation_head_tail valuation] at atCell
        simpa only [cellValue_extend_true, head, tail, inf_assoc,
          inf_left_comm, inf_comm] using atCell
      have negative : headᶜ ⊓ left = headᶜ ⊓ right := by
        apply inductionHypothesis tail
        intro cell
        have atCell := equalOnCells (extendCell false cell)
        rw [← extendValuation_head_tail valuation] at atCell
        simpa only [cellValue_extend_false, head, tail, inf_assoc,
          inf_left_comm, inf_comm] using atCell
      calc
        left = head ⊓ left ⊔ headᶜ ⊓ left := by
          simpa only [inf_comm] using
            (sup_inf_inf_compl (x := left) (y := head)).symm
        _ = head ⊓ right ⊔ headᶜ ⊓ right := by
          rw [positive, negative]
        _ = right := by
          simpa only [inf_comm] using
            (sup_inf_inf_compl (x := right) (y := head))

/-- Equality of ordinary term values is exactly agreement of their Boolean
truth values on every nonzero Venn cell of the current valuation. -/
theorem equation_eval_eq_iff_nonzero_cells_agree
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (equation : Equation (Fin arity)) (valuation : Fin arity -> B) :
    equation.left.eval valuation = equation.right.eval valuation <->
      forall cell : Cell arity, cellValue valuation cell ≠ ⊥ ->
        equation.left.eval cell = equation.right.eval cell := by
  constructor
  · intro valuesEqual cell cellNonzero
    have intersectionsEqual :
        cellValue valuation cell ⊓ equation.left.eval valuation =
          cellValue valuation cell ⊓ equation.right.eval valuation := by
      rw [valuesEqual]
    rw [cellValue_inf_term_eval valuation cell equation.left,
      cellValue_inf_term_eval valuation cell equation.right] at intersectionsEqual
    cases leftValue : equation.left.eval cell <;>
      cases rightValue : equation.right.eval cell <;>
      simp_all
  · intro cellsAgree
    apply cellIntersections_separate valuation
    intro cell
    rw [cellValue_inf_term_eval valuation cell equation.left,
      cellValue_inf_term_eval valuation cell equation.right]
    by_cases cellNonzero : cellValue valuation cell ≠ ⊥
    · rw [cellsAgree cell cellNonzero]
    · have cellZero : cellValue valuation cell = ⊥ := not_ne_iff.mp cellNonzero
      simp [cellZero]

/-! ## Executable equation-to-profile compilation -/

/-- Canonical structural enumeration of all Venn cells.  This enumeration is
used only by the compiler; the semantic separation theorem above does not
depend on an ordering of cells. -/
def allCells : (arity : Nat) -> List (Cell arity)
  | 0 => [Fin.elim0]
  | arity + 1 =>
      (allCells arity).flatMap fun cell =>
        [extendCell false cell, extendCell true cell]

theorem mem_allCells : {arity : Nat} -> (cell : Cell arity) ->
    cell ∈ allCells arity
  | 0, cell => by
      have cellEq : cell = Fin.elim0 := Subsingleton.elim _ _
      simp [allCells, cellEq]
  | arity + 1, cell => by
      rw [allCells, List.mem_flatMap]
      refine ⟨tailCell cell, mem_allCells (tailCell cell), ?_⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      cases headValue : cell 0
      · exact Or.inl ((extendCell_head_tail cell).symm.trans
          (congrArg (fun polarity => extendCell polarity (tailCell cell))
            headValue))
      · exact Or.inr ((extendCell_head_tail cell).symm.trans
          (congrArg (fun polarity => extendCell polarity (tailCell cell))
            headValue))

/-- Truth in the profile language. -/
def truthFormula {arity : Nat} : Formula arity := .negation .falsum

/-- Finite conjunction in the profile language. -/
def conjoin {arity : Nat} : List (Formula arity) -> Formula arity
  | [] => truthFormula
  | formula :: formulas => .conjunction formula (conjoin formulas)

theorem satisfies_conjoin_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (formulas : List (Formula arity)) (valuation : Fin arity -> B) :
    Satisfies (conjoin formulas) valuation <->
      forall formula, formula ∈ formulas -> Satisfies formula valuation := by
  induction formulas with
  | nil => simp [conjoin, truthFormula, Satisfies]
  | cons formula formulas inductionHypothesis =>
      simp only [conjoin, Satisfies, List.mem_cons]
      rw [inductionHypothesis]
      constructor
      · rintro ⟨headSatisfied, tailSatisfied⟩ candidate
        rintro (rfl | member)
        · exact headSatisfied
        · exact tailSatisfied candidate member
      · intro allSatisfied
        exact ⟨allSatisfied formula (Or.inl rfl),
          fun candidate member => allSatisfied candidate (Or.inr member)⟩

/-- One cell contributes no constraint when both sides agree there; otherwise
it requires that the cell be zero. -/
def cellAgreementFormula {arity : Nat}
    (equation : Equation (Fin arity)) (cell : Cell arity) :
    Formula arity :=
  if equation.left.eval cell = equation.right.eval cell then
    truthFormula
  else
    .negation (.cellNonzero cell)

theorem satisfies_cellAgreementFormula_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (equation : Equation (Fin arity)) (cell : Cell arity)
    (valuation : Fin arity -> B) :
    Satisfies (cellAgreementFormula equation cell) valuation <->
      cellValue valuation cell ≠ ⊥ ->
        equation.left.eval cell = equation.right.eval cell := by
  by_cases agrees : equation.left.eval cell = equation.right.eval cell
  · simp [cellAgreementFormula, agrees, truthFormula, Satisfies]
  · simp [cellAgreementFormula, agrees, Satisfies]

/-- Compile one ordinary Boolean equation into the finite profile language. -/
def equationFormula {arity : Nat}
    (equation : Equation (Fin arity)) : Formula arity :=
  conjoin ((allCells arity).map (cellAgreementFormula equation))

/-- The compiled profile formula has exactly the ordinary algebraic meaning
of its source equation in every Boolean algebra. -/
theorem satisfies_equationFormula_iff_eval_eq
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (equation : Equation (Fin arity)) (valuation : Fin arity -> B) :
    Satisfies (equationFormula equation) valuation <->
      equation.left.eval valuation = equation.right.eval valuation := by
  rw [equation_eval_eq_iff_nonzero_cells_agree]
  simp only [equationFormula, satisfies_conjoin_iff, List.mem_map]
  constructor
  · intro allCompiled cell cellNonzero
    apply (satisfies_cellAgreementFormula_iff equation cell valuation).mp
    exact allCompiled (cellAgreementFormula equation cell)
      ⟨cell, mem_allCells cell, rfl⟩
    exact cellNonzero
  · intro cellsAgree formula formulaMember
    obtain ⟨cell, _cellMember, rfl⟩ := formulaMember
    exact (satisfies_cellAgreementFormula_iff equation cell valuation).mpr
      (cellsAgree cell)

/-- In an atomless Boolean algebra, finite profile evaluation of a compiled
equation is exact for its ordinary carrier interpretation. -/
theorem decideAt_equationFormula_eq_true_iff_eval_eq
    {B : Type u} [BooleanAlgebra B] (gunky : IsGunky B)
    {arity : Nat} (equation : Equation (Fin arity))
    (valuation : Fin arity -> B) :
    decideAt (equationFormula equation) (profileOf valuation) = true <->
      equation.left.eval valuation = equation.right.eval valuation :=
  (decideAt_eq_true_iff_satisfies gunky (equationFormula equation)
    valuation).trans
      (satisfies_equationFormula_iff_eval_eq equation valuation)

/-! ## Discriminating examples -/

namespace Canary

open BooleanAlgebraIdentityDecision.Canary

theorem distributive_compilation_exact
    {B : Type u} [BooleanAlgebra B]
    (valuation : TwoVar -> B) :
    Satisfies (equationFormula distributiveIdentity) valuation :=
  (satisfies_equationFormula_iff_eval_eq distributiveIdentity valuation).mpr
    (distributive_bool_valid.validIn valuation)

theorem falseIdentity_compilation_rejected_at_separatingAssignment :
    ¬ Satisfies (equationFormula falseIdentity) separatingAssignment := by
  rw [satisfies_equationFormula_iff_eval_eq]
  exact separatingAssignment_refutes_falseIdentity

end Canary

#print axioms cellValue_inf_term_eval
#print axioms cellIntersections_separate
#print axioms equation_eval_eq_iff_nonzero_cells_agree
#print axioms mem_allCells
#print axioms satisfies_equationFormula_iff_eval_eq
#print axioms decideAt_equationFormula_eq_true_iff_eval_eq
#print axioms Canary.distributive_compilation_exact
#print axioms Canary.falseIdentity_compilation_rejected_at_separatingAssignment

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanTermProfileBridge
