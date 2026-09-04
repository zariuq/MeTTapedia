import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Logic.StoneGunkDuality
import Mathlib.Data.Fintype.Pi

/-!
# Finite decision of identities in infinite Boolean semantic bases

Boolean-algebra identities have finite syntax and can be decided by their
two-valued truth tables even when they are interpreted in an infinite,
atomless algebra.  This module proves that statement rather than assuming it:

* terms are interpreted in an arbitrary Boolean algebra;
* validity under every Boolean assignment implies validity in every Boolean
  algebra, using Stone separation;
* validity in any one nontrivial Boolean algebra reflects two-valued validity;
* finite variable sets yield both a direct decision kernel and an explicit
  complete truth-table certificate authority.

The result is an equational decision procedure.  It is not quantifier
elimination for the full first-order theory of atomless Boolean algebras.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.Foundations.Gunk
open TopologicalSpace

universe uVar uAlgebra

/-! ## Boolean terms and independent semantics -/

/-- Finitary terms in the algebraic signature of Boolean algebras. -/
inductive Term (Var : Type uVar) where
  | atom (name : Var)
  | bottom
  | top
  | meet (left right : Term Var)
  | join (left right : Term Var)
  | complement (body : Term Var)
deriving Repr, DecidableEq

namespace Term

/-- Interpretation of one term in an arbitrary Boolean algebra. -/
def eval {Var : Type uVar} {B : Type uAlgebra} [BooleanAlgebra B]
    (assignment : Var -> B) : Term Var -> B
  | .atom name => assignment name
  | .bottom => ⊥
  | .top => ⊤
  | .meet left right => eval assignment left ⊓ eval assignment right
  | .join left right => eval assignment left ⊔ eval assignment right
  | .complement body => (eval assignment body)ᶜ

end Term

/-- An equational claim retains both Boolean terms. -/
structure Equation (Var : Type uVar) where
  left : Term Var
  right : Term Var
deriving Repr, DecidableEq

abbrev BoolAssignment (Var : Type uVar) := Var -> Bool

/-- Validity in a selected Boolean algebra is independent of any checker. -/
def ValidIn {Var : Type uVar} (B : Type uAlgebra) [BooleanAlgebra B]
    (equation : Equation Var) : Prop :=
  forall assignment : Var -> B,
    equation.left.eval assignment = equation.right.eval assignment

/-- Ordinary two-valued validity. -/
def BoolValid {Var : Type uVar} (equation : Equation Var) : Prop :=
  ValidIn Bool equation

/-- Validity in every Boolean algebra of one ambient universe. -/
def ValidInEvery {Var : Type uVar} (equation : Equation Var) : Prop :=
  forall (B : Type uAlgebra), forall [BooleanAlgebra B], ValidIn B equation

/-! ## Stone separation gives universal soundness -/

private noncomputable def characteristic (proposition : Prop) : Bool := by
  classical
  exact if proposition then true else false

@[simp] private theorem characteristic_eq_true_iff (proposition : Prop) :
    characteristic proposition = true <-> proposition := by
  classical
  simp [characteristic]

private noncomputable def stoneAssignment
    {Var : Type uVar} {B : Type uAlgebra}
    [BooleanAlgebra B] (assignment : Var -> B) (point : StoneSpace B) :
    BoolAssignment Var :=
  fun name =>
    characteristic (point ∈ stoneRepr B (assignment name))

private theorem bool_inf_eq_true_iff (left right : Bool) :
    left ⊓ right = true <-> left = true /\ right = true := by
  cases left <;> cases right <;> decide

private theorem bool_sup_eq_true_iff (left right : Bool) :
    left ⊔ right = true <-> left = true \/ right = true := by
  cases left <;> cases right <;> decide

private theorem bool_compl_eq_true_iff (value : Bool) :
    valueᶜ = true <-> ¬ value = true := by
  cases value <;> decide

private theorem bool_bot_eq_true_iff :
    (⊥ : Bool) = true <-> False := by
  decide

private theorem bool_top_eq_true_iff :
    (⊤ : Bool) = true <-> True := by
  decide

private theorem mem_stoneRepr_bot {B : Type uAlgebra} [BooleanAlgebra B]
    (point : StoneSpace B) :
    point ∈ stoneRepr B (⊥ : B) <-> False := by
  rw [(stoneRepr B).map_bot]
  rfl

private theorem mem_stoneRepr_top {B : Type uAlgebra} [BooleanAlgebra B]
    (point : StoneSpace B) :
    point ∈ stoneRepr B (⊤ : B) <-> True := by
  rw [(stoneRepr B).map_top]
  rfl

private theorem mem_stoneRepr_inf {B : Type uAlgebra} [BooleanAlgebra B]
    (point : StoneSpace B) (left right : B) :
    point ∈ stoneRepr B (left ⊓ right) <->
      point ∈ stoneRepr B left /\ point ∈ stoneRepr B right := by
  rw [(stoneRepr B).map_inf]
  rfl

private theorem mem_stoneRepr_sup {B : Type uAlgebra} [BooleanAlgebra B]
    (point : StoneSpace B) (left right : B) :
    point ∈ stoneRepr B (left ⊔ right) <->
      point ∈ stoneRepr B left \/ point ∈ stoneRepr B right := by
  rw [(stoneRepr B).map_sup]
  rfl

private theorem mem_stoneRepr_compl {B : Type uAlgebra} [BooleanAlgebra B]
    (point : StoneSpace B) (value : B) :
    point ∈ stoneRepr B valueᶜ <-> ¬ point ∈ stoneRepr B value := by
  rw [map_compl' (stoneRepr B)]
  rfl

private theorem eval_stoneAssignment_eq_true_iff
    {Var : Type uVar} {B : Type uAlgebra} [BooleanAlgebra B]
    (assignment : Var -> B) (point : StoneSpace B) (term : Term Var) :
    term.eval (stoneAssignment assignment point) = true <->
      point ∈ stoneRepr B (term.eval assignment) := by
  classical
  induction term with
  | atom name =>
      simp [Term.eval, stoneAssignment]
  | bottom =>
      simpa only [Term.eval, mem_stoneRepr_bot] using bool_bot_eq_true_iff
  | top =>
      simpa only [Term.eval, mem_stoneRepr_top] using bool_top_eq_true_iff
  | meet left right leftIH rightIH =>
      simpa only [Term.eval, bool_inf_eq_true_iff, mem_stoneRepr_inf]
        using and_congr leftIH rightIH
  | join left right leftIH rightIH =>
      simpa only [Term.eval, bool_sup_eq_true_iff, mem_stoneRepr_sup]
        using or_congr leftIH rightIH
  | complement body bodyIH =>
      simpa only [Term.eval, bool_compl_eq_true_iff, mem_stoneRepr_compl]
        using not_congr bodyIH

/-- A two-valued identity holds in every Boolean algebra.  Stone
representation supplies enough Boolean-valued point observations to reflect
equality of arbitrary algebra elements. -/
theorem BoolValid.validIn {Var : Type uVar} {B : Type uAlgebra}
    [BooleanAlgebra B] {equation : Equation Var}
    (valid : BoolValid equation) : ValidIn B equation := by
  intro assignment
  apply (stoneRepr B).injective
  apply SetLike.ext
  intro point
  rw [← eval_stoneAssignment_eq_true_iff assignment point equation.left]
  rw [← eval_stoneAssignment_eq_true_iff assignment point equation.right]
  rw [valid (stoneAssignment assignment point)]

theorem BoolValid.validInEvery {Var : Type uVar}
    {equation : Equation Var} (valid : BoolValid equation) :
    ValidInEvery.{uVar, uAlgebra} equation := by
  intro B _
  exact valid.validIn

/-! ## Any nontrivial Boolean algebra also reflects two-valued validity -/

private def twoPointAssignment {Var : Type uVar} {B : Type uAlgebra}
    [BooleanAlgebra B] (assignment : BoolAssignment Var) : Var -> B :=
  fun name => if assignment name then ⊤ else ⊥

private theorem eval_twoPointAssignment {Var : Type uVar}
    {B : Type uAlgebra} [BooleanAlgebra B]
    (assignment : BoolAssignment Var) (term : Term Var) :
    term.eval (twoPointAssignment (B := B) assignment) =
      if term.eval assignment then ⊤ else ⊥ := by
  induction term with
  | atom name => simp [Term.eval, twoPointAssignment]
  | bottom => simp [Term.eval]
  | top => simp [Term.eval]
  | meet left right leftIH rightIH =>
      cases leftValue : left.eval assignment <;>
        cases rightValue : right.eval assignment <;>
        simp_all [Term.eval]
  | join left right leftIH rightIH =>
      cases leftValue : left.eval assignment <;>
        cases rightValue : right.eval assignment <;>
        simp_all [Term.eval]
  | complement body bodyIH =>
      cases bodyValue : body.eval assignment <;>
        simp_all [Term.eval]

/-- Validity in any one nontrivial Boolean algebra reflects ordinary Boolean
validity. -/
theorem boolValid_of_validIn {Var : Type uVar} {B : Type uAlgebra}
    [BooleanAlgebra B] [Nontrivial B] {equation : Equation Var}
    (valid : ValidIn B equation) : BoolValid equation := by
  intro assignment
  have equality := valid (twoPointAssignment (B := B) assignment)
  rw [eval_twoPointAssignment, eval_twoPointAssignment] at equality
  cases leftValue : equation.left.eval assignment <;>
    cases rightValue : equation.right.eval assignment <;>
    simp_all

/-- Every nontrivial Boolean algebra has exactly the same equational theory as
`Bool`. -/
theorem boolValid_iff_validIn {Var : Type uVar} {B : Type uAlgebra}
    [BooleanAlgebra B] [Nontrivial B] (equation : Equation Var) :
    BoolValid equation <-> ValidIn B equation :=
  ⟨fun valid => valid.validIn, boolValid_of_validIn⟩

/-! ## Finite replay and decision -/

/-- A validity certificate explicitly lists Boolean assignments. -/
abbrev TruthTableCertificate (Var : Type uVar) := List (BoolAssignment Var)

/-- Every assignment occurs and every listed row validates the identity. -/
def TruthTableValid {Var : Type uVar} (equation : Equation Var)
    (rows : TruthTableCertificate Var) : Prop :=
  (forall assignment : BoolAssignment Var, assignment ∈ rows) /\
    forall assignment : BoolAssignment Var, assignment ∈ rows ->
      equation.left.eval assignment = equation.right.eval assignment

private instance truthTableValidDecidable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var]
    (equation : Equation Var) (rows : TruthTableCertificate Var) :
    Decidable (TruthTableValid equation rows) := by
  unfold TruthTableValid
  infer_instance

/-- Replay a complete finite truth table. -/
def truthTableChecker
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    Checker (Equation Var) (TruthTableCertificate Var) where
  check equation rows := decide (TruthTableValid equation rows)

/-- Canonical exhaustive certificate used to prove format completeness. -/
noncomputable def fullTruthTable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    TruthTableCertificate Var :=
  Finset.univ.toList

/-- Complete truth tables are exact certificates for Boolean-algebra
identities. -/
theorem truthTableChecker_authority
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    (truthTableChecker (Var := Var)).Authority BoolValid where
  sound := by
    intro equation rows accepted assignment
    have valid : TruthTableValid equation rows := of_decide_eq_true accepted
    exact valid.2 assignment (valid.1 assignment)
  complete := by
    intro equation valid
    refine ⟨fullTruthTable, ?_⟩
    apply decide_eq_true
    constructor
    · intro assignment
      simp [fullTruthTable]
    · intro assignment _
      exact valid assignment

private instance boolValidDecidable
    {Var : Type uVar} [Fintype Var] [DecidableEq Var]
    (equation : Equation Var) : Decidable (BoolValid equation) := by
  unfold BoolValid ValidIn
  infer_instance

/-- Direct exhaustive decision is kept separate from certificate replay. -/
def decisionKernel
    {Var : Type uVar} [Fintype Var] [DecidableEq Var] :
    Checker.DecisionKernel (Equation Var) BoolValid where
  decide equation := decide (BoolValid equation)
  correct := by
    intro equation
    simp

/-! ## Atomless Cantor calibration -/

/-- The infinite-primary model used by the Stone-gunk authority. -/
abbrev CantorAlgebra := Clopens (Nat -> Bool)

private instance cantorAlgebraNontrivial : Nontrivial CantorAlgebra := by
  constructor
  refine ⟨⊥, ⊤, ?_⟩
  intro equal
  let point : Nat -> Bool := fun _ => false
  have member : point ∈ ((⊤ : CantorAlgebra) : Set (Nat -> Bool)) := by
    simp
  rw [← equal] at member
  simp at member

/-- Finite truth-table validity is equivalent to validity in the atomless
Cantor clopen algebra. -/
theorem boolValid_iff_cantorValid {Var : Type uVar}
    (equation : Equation Var) :
    BoolValid equation <-> ValidIn CantorAlgebra equation :=
  boolValid_iff_validIn equation

/-- The semantic carrier is genuinely gunky and therefore infinite even
though each finite-variable identity has a finite decision procedure. -/
theorem cantor_is_gunky_and_infinite :
    IsGunky CantorAlgebra /\ Infinite CantorAlgebra :=
  ⟨isGunky_clopens_cantor, infinite_of_isGunky isGunky_clopens_cantor⟩

/-! ## Discriminating examples -/

namespace Canary

abbrev TwoVar := Fin 2

def x : Term TwoVar := .atom 0
def y : Term TwoVar := .atom 1

def distributiveIdentity : Equation TwoVar where
  left := .meet x (.join y (.complement y))
  right := x

def falseIdentity : Equation TwoVar where
  left := .meet x y
  right := .join x y

def separatingAssignment : BoolAssignment TwoVar
  | 0 => true
  | _ => false

theorem distributive_bool_valid : BoolValid distributiveIdentity := by
  intro assignment
  cases assignment 0 <;> cases assignment 1 <;>
    simp [distributiveIdentity, x, y, Term.eval]

theorem distributive_cantor_valid :
    ValidIn CantorAlgebra distributiveIdentity :=
  (boolValid_iff_cantorValid distributiveIdentity).mp distributive_bool_valid

theorem distributive_truth_table_accepted :
    (truthTableChecker (Var := TwoVar)).check distributiveIdentity
      (fullTruthTable (Var := TwoVar)) = true := by
  apply decide_eq_true
  constructor
  · intro assignment
    simp [fullTruthTable]
  · intro assignment _
    exact distributive_bool_valid assignment

theorem separatingAssignment_refutes_falseIdentity :
    falseIdentity.left.eval separatingAssignment ≠
      falseIdentity.right.eval separatingAssignment := by
  decide

theorem falseIdentity_not_boolValid : ¬ BoolValid falseIdentity := by
  intro valid
  exact separatingAssignment_refutes_falseIdentity
    (valid separatingAssignment)

theorem falseIdentity_not_cantorValid :
    ¬ ValidIn CantorAlgebra falseIdentity :=
  fun valid => falseIdentity_not_boolValid
    ((boolValid_iff_cantorValid falseIdentity).mpr valid)

theorem falseIdentity_decision_rejects :
    (decisionKernel (Var := TwoVar)).decide falseIdentity = false := by
  simp [decisionKernel, falseIdentity_not_boolValid]

/-- Omitting one row invalidates an otherwise correct truth-table
certificate. -/
theorem incomplete_truth_table_rejected :
    (truthTableChecker (Var := TwoVar)).check distributiveIdentity
      [separatingAssignment] = false := by
  change decide
    (TruthTableValid distributiveIdentity [separatingAssignment]) = false
  rw [decide_eq_false_iff_not]
  intro valid
  let missing : BoolAssignment TwoVar := fun _ => false
  have included := valid.1 missing
  have different : missing ≠ separatingAssignment := by
    intro equality
    have atZero := congrFun equality 0
    simp [missing, separatingAssignment] at atZero
  simp [different] at included

end Canary

#print axioms BoolValid.validIn
#print axioms BoolValid.validInEvery
#print axioms boolValid_of_validIn
#print axioms boolValid_iff_validIn
#print axioms truthTableChecker_authority
#print axioms decisionKernel
#print axioms boolValid_iff_cantorValid
#print axioms cantor_is_gunky_and_infinite
#print axioms Canary.distributive_cantor_valid
#print axioms Canary.distributive_truth_table_accepted
#print axioms Canary.falseIdentity_not_cantorValid
#print axioms Canary.falseIdentity_decision_rejects
#print axioms Canary.incomplete_truth_table_rejected

end Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentityDecision
