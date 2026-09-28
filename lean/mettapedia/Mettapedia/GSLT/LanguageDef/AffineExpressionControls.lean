import Mettapedia.GSLT.LanguageDef.AffineExpressionOSLF
import Mettapedia.GSLT.LanguageDef.AffineExpressionRealization

/-!
# Positive and negative controls for affine admission

These controls check source syntax, compiler decisions, evaluated artifacts,
order, duplicate occurrences, interrupted folds, and numeric near misses.
They use kernel reduction and the general correctness theorems.
-/

namespace Mettapedia.GSLT.AffineExpression.Controls

open Mettapedia.Algebra

def horner : Expr 2 := .bin .add (.bin .mul (.input 0) .acc) (.input 1)

def hornerForm : Form 2 :=
  .affine (.bin .add (.bin .mul (.input 0) (.lit 1)) (.lit 0))
    (.bin .add (.bin .mul (.input 0) (.lit 0)) (.input 1))

theorem horner_admitted : compile horner = some hornerForm := rfl

theorem horner_uniform (a b x : Int) :
    hornerForm.apply ![a, b] x = a * x + b := by
  rw [compile_sound horner hornerForm horner_admitted]
  rfl

theorem varying_coefficients :
    compiledFold hornerForm [![2, 3], ![4, 5]] 1 = 25 := by decide

theorem reversing_changes_answer :
    compiledFold hornerForm [![4, 5], ![2, 3]] 1 = 21 := by decide

theorem duplicate_occurrences_count :
    compiledFold hornerForm [![1, 3], ![1, 3]] 0 = 6 ∧
    compiledFold hornerForm [![1, 3]] 0 = 3 := by decide

theorem no_replay :
    compiledFold hornerForm [![4, 5]] (sourceFold horner [![2, 3]] 1) = 25 := by
  decide

def itemMinusAccumulator : Expr 1 := .bin .sub (.input 0) .acc

theorem petta_operand_order :
    sourceFold itemMinusAccumulator [![2]] 20 = -18 ∧
    sourceFold itemMinusAccumulator [![2], ![2]] 20 = 20 := by decide

/-- Inputs may be nonlinear in themselves; only accumulator dependence is
restricted. This is useful for weighted aggregation over arbitrary rows. -/
def nonlinearInputs : Expr 2 :=
  .bin .add (.bin .mul (.bin .mul (.input 0) (.input 1)) .acc)
    (.bin .mul (.input 0) (.input 0))

theorem nonlinear_inputs_admitted : (compile nonlinearInputs).isSome = true := by decide

def square : Expr 0 := .bin .mul .acc .acc

theorem square_declined : compile square = none := rfl

def cancellation : Expr 0 := .bin .sub square square

/-- An honest false negative: the recognized grammar is not the largest
semantic affine fragment. Rejection must continue with source execution. -/
theorem cancellation_boundary : compile cancellation = none ∧
    ∀ x : Int, cancellation.eval Fin.elim0 x = 0 := by
  constructor
  · rfl
  · intro x
    simp [cancellation, square, Expr.eval, Op.eval]

theorem rejected_source_still_computes :
    (theory (n := 0) Fin.elim0 9).MultiStep square (.lit 81) := by
  apply (reaches_literal_iff _ _ _ _).mpr
  rfl

def intermediateOverflow : Expr 0 :=
  .bin .sub (.bin .add (.lit 127) (.lit 1)) (.lit 1)

/-- The final integer fits signed eight-bit bounds, but a source intermediate
does not. A native guard checking only the final answer is insufficient. -/
theorem final_fit_is_insufficient :
    intermediateOverflow.eval Fin.elim0 0 = 127 ∧
    checked (-128) 127 (intermediateOverflow.eval Fin.elim0 0) = some 127 ∧
    intermediateOverflow.evalChecked (-128) 127 Fin.elim0 0 = none := by
  decide

theorem source_charge_survives_fusion :
    (compileAccepted horner (by decide)).sourceCharge = 5 ∧
    (normalize ![2, 3] 1 horner).length = 5 := by
  constructor
  · rfl
  · rw [normalization_charge]; rfl

/-- An observable OSLF predicate is transported using the actual generated
modality on source reachability. -/
theorem positive_terminal_predicate :
    Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltDiamond
      (theory ![2, 3] 1).closure (terminalPredicate (fun x => x = 5)) horner := by
  apply (oslf_terminal_exact _ _ _ _ horner_admitted _).mpr
  decide

theorem wrong_terminal_rejected :
    ¬ (theory ![2, 3] 1).MultiStep horner (.lit 6) := by
  rw [compiled_reaches_iff _ _ _ _ horner_admitted]
  decide

end Mettapedia.GSLT.AffineExpression.Controls
