import Foundation.Propositional.ClassicalSemantics.NNFormula
import Mettapedia.GSLT.Logic.PropositionalFormula
import Mettapedia.GSLT.Logic.PropositionalResolution
import Mettapedia.GSLT.Logic.PropositionalResolutionComplete
import Mettapedia.Logic.Bridges.PropositionalCutTait

/-!
# Our propositional/resolution GSLT vs Foundation classical semantics

Bool valuations embed as Foundation valuations. Satisfaction of a formula
agrees with Foundation models of its Tait embedding. Unsat of `toCNF A`
is unsat of `A`. Combined with `complete`, that yields a resolution
refutation.

No GSLT/OSLF import of Foundation: this file is the Logic/Bridges hook.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Bridges.PropositionalResolutionTait

open Mettapedia.GSLT.Logic.PropositionalFormula
open Mettapedia.GSLT.Logic.PropositionalResolution
open Mettapedia.Logic.Bridges.PropositionalCutTait
open LO.Propositional
open LO.Propositional.ClassicalSemantics
open LO.Propositional.NNFormula

def boolVal (v : Nat → Bool) : Valuation Nat :=
  fun n => v n = true

theorem sat_eq_val (v : Nat → Bool) :
    (A : Formula) →
      (Formula.sat v A = true ↔ val (boolVal v) (formulaEmbed A))
  | .atom n => by
      simp [Formula.sat, formulaEmbed, boolVal, val_atom]
  | .not A => by
      have ih := sat_eq_val v A
      constructor
      · intro h
        have hf : Formula.sat v A = false := by
          cases hA : Formula.sat v A with
          | false => rfl
          | true => simp [Formula.sat, hA] at h
        have : ¬ val (boolVal v) (formulaEmbed A) := by
          intro hv
          have := ih.mpr hv
          simp [hf] at this
        simpa [formulaEmbed, valAux_neg] using this
      · intro h
        have : ¬ val (boolVal v) (formulaEmbed A) := by
          simpa [formulaEmbed, valAux_neg] using h
        cases hA : Formula.sat v A with
        | false => simp [Formula.sat, hA]
        | true => exact (this (ih.mp hA)).elim
  | .and A B => by
      have ihA := sat_eq_val v A
      have ihB := sat_eq_val v B
      simp [Formula.sat, formulaEmbed, Bool.and_eq_true, ihA, ihB]
  | .or A B => by
      have ihA := sat_eq_val v A
      have ihB := sat_eq_val v B
      simp [Formula.sat, formulaEmbed, Bool.or_eq_true, ihA, ihB]

theorem sat_iff_models (v : Nat → Bool) (A : Formula) :
    Formula.sat v A = true ↔ boolVal v ⊧ formulaEmbed A :=
  (sat_eq_val v A).trans models_iff_val.symm

theorem unsat_cnf_iff_unsat_formula (A : Formula) :
    Unsat (toCNF A) ↔ ∀ v : Nat → Bool, Formula.sat v A = false := by
  constructor
  · intro h v
    have := h v
    simpa [sat_toCNF] using this
  · intro h v
    have := h v
    simpa [sat_toCNF] using this

/-- An unsatisfiable formula has a resolution refutation of its CNF. -/
theorem unsat_formula_refutes (A : Formula)
    (h : ∀ v : Nat → Bool, Formula.sat v A = false) :
    ClauseDerives (toCNF A) [] :=
  complete (toCNF A) ((unsat_cnf_iff_unsat_formula A).mpr h)

#print axioms sat_iff_models
#print axioms unsat_formula_refutes

end Mettapedia.Logic.Bridges.PropositionalResolutionTait
