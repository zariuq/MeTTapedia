import Mettapedia.Languages.ProcessCalculi.CCS.Blocks

/-!
# The static theory of CCS, decided

Two typed processes of CCS are related by its laws (the laws of its parallel bag and of its sums, restriction of
inaction, exchange of restrictions, scope extrusion and the empty sum) exactly when their canonical forms are equal
(`static_iff_canon_eq`, the restriction-block theory's `equationEquiv_iff_canon_eq` at CCS's blocks).

The controls decide:

- the summands of a sum stand in no order, also under a guard;
- the empty sum is inaction, and inaction is the unit of composition;
- a restriction extrudes over a component, and a restriction no component uses is garbage;
- **negative**: a sum is a multiset of summands, so a summand counts twice;
- **negative**: a sum is not a parallel composition;
- **negative**: a restriction under a guard does not leave it;
- **negative**: a restriction whose name a summand uses is no garbage.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS.StaticTheory

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv)
open Mettapedia.GSLT.LanguageDef.WellSorted (checkHasType checkHasType_sound isObjectPattern)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (canon equationEquiv_iff_canon_eq)
open Mettapedia.Languages.ProcessCalculi.CCS.Blocks (ccsBlock ccsNameContext ccsNameContext_base)

/-- **The static theory of CCS is decided by canonical forms**, for processes whose free variables are names. -/
theorem static_iff_canon_eq {first second : Pattern}
    (firstTyped : checkHasType ccsCalc ccsNameContext [] first (.base "Proc") = true)
    (secondTyped : checkHasType ccsCalc ccsNameContext [] second (.base "Proc") = true)
    (object : isObjectPattern first = true) :
    EquationEquiv base ccsCalc first second ↔ canon ccsBlock first = canon ccsBlock second :=
  equationEquiv_iff_canon_eq ccsNameContext_base (checkHasType_sound firstTyped) (checkHasType_sound secondTyped)
    object

/-- The free name `c`. -/
def nameC : Pattern := .fvar "c"

/-! ## Positive -/

/-- The summands of a sum stand in no order. -/
example : EquationEquiv base ccsCalc (sum [act nameA nil, act nameB nil]) (sum [act nameB nil, act nameA nil]) :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- Under a guard too. -/
example : EquationEquiv base ccsCalc (sum [act nameA (sum [act nameB nil, coact nameC nil])])
    (sum [act nameA (sum [coact nameC nil, act nameB nil])]) :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- The empty sum is inaction. -/
example : EquationEquiv base ccsCalc (sum []) nil :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- The empty sum, as a component, is the unit of composition. -/
example : EquationEquiv base ccsCalc (par [sum [], sum [act nameA nil]]) (sum [act nameA nil]) :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- A restriction extrudes over a component: `(νx)(x.0 | b.0)` and `(νx) x.0 | b.0`. -/
example : EquationEquiv base ccsCalc (nu (par [sum [act (.bvar 0) nil], sum [act nameB nil]]))
    (par [nu (sum [act (.bvar 0) nil]), sum [act nameB nil]]) :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-- A restriction no component uses is garbage: `(νx) a.0` is `a.0`. -/
example : EquationEquiv base ccsCalc (nu (sum [act nameA nil])) (sum [act nameA nil]) :=
  (static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)).mpr (by decide +kernel)

/-! ## Negative -/

/-- **A summand counts twice**: `a.0 + a.0` is not `a.0`. -/
example : ¬ EquationEquiv base ccsCalc (sum [act nameA nil, act nameA nil]) (sum [act nameA nil]) := by
  rw [static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **A sum is not a parallel composition**: `a.0 + b.0` is not `a.0 | b.0`. -/
example : ¬ EquationEquiv base ccsCalc (sum [act nameA nil, act nameB nil])
    (par [sum [act nameA nil], sum [act nameB nil]]) := by
  rw [static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **A restriction under a guard does not leave it**: `a.(νx) x.0` is not `(νx) a.x.0`. -/
example : ¬ EquationEquiv base ccsCalc (sum [act nameA (nu (sum [act (.bvar 0) nil]))])
    (nu (sum [act nameA (sum [act (.bvar 0) nil])])) := by
  rw [static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

/-- **A used restriction is no garbage**: `(νx)(x.0 + a.0)` is not `a.0`. -/
example : ¬ EquationEquiv base ccsCalc (nu (sum [act (.bvar 0) nil, act nameA nil])) (sum [act nameA nil]) := by
  rw [static_iff_canon_eq (by decide +kernel) (by decide +kernel) (by decide +kernel)]
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.CCS.StaticTheory
