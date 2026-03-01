import Mettapedia.Languages.MeTTa.HE.Interpreter

/-!
# HE MeTTa Structural Properties

Proven structural properties of the HE interpreter formalization.
These capture invariants that hold across all inputs, not just specific test cases.

## Main Theorems
* `metta_fuel_zero` - At fuel 0, atom returned unchanged
* `mettaCall_fuel_zero` - At fuel 0, mettaCall returns atom unchanged
* `interpretArgs_fuel_zero` - At fuel 0, interpretArgs wraps args in expression
* `metta_empty_pass` - Empty always passes through metta
* `metta_error_pass` - Error expressions always pass through metta
* `interpretArgs_nil` - Empty argument list base case
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.OSLF.MeTTaCore (Atom GroundedValue)

/-! ## Fuel Zero Properties

These are definitional (rfl), since fuel = 0 is the base case of all functions. -/

/-- At fuel 0, metta returns the atom unchanged. -/
theorem metta_fuel_zero (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    metta atom type_ space b dispatch ev 0 = [(atom, b)] := rfl

/-- At fuel 0, interpretExpression returns the atom unchanged. -/
theorem interpretExpression_fuel_zero (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    interpretExpression atom type_ space b dispatch ev 0 = [(atom, b)] := rfl

/-- At fuel 0, mettaCall returns the atom unchanged. -/
theorem mettaCall_fuel_zero (atom type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    mettaCall atom type_ space b dispatch ev 0 = [(atom, b)] := rfl

/-- At fuel 0, interpretArgs returns the args wrapped in an expression. -/
theorem interpretArgs_fuel_zero (args types : List Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    interpretArgs args types space b dispatch ev 0 = [(.expression args, b)] := rfl

/-- At fuel 0, interpretFunction returns the atom unchanged. -/
theorem interpretFunction_fuel_zero (atom opType retType : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    interpretFunction atom opType retType space b dispatch ev 0 = [(atom, b)] := rfl

/-- At fuel 0, interpretTuple returns the atom unchanged. -/
theorem interpretTuple_fuel_zero (atom : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) :
    interpretTuple atom space b dispatch ev 0 = [(atom, b)] := rfl

/-! ## Empty/Error Passthrough -/

/-- Empty always passes through metta unchanged. -/
theorem metta_empty_pass (type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) (n : Nat) :
    metta Atom.empty type_ space b dispatch ev (n + 1) = [(Atom.empty, b)] := by
  simp [metta, isEmptyAtom, Atom.empty, BEq.beq, Atom.beq]

/-- Error expressions always pass through metta unchanged. -/
theorem metta_error_pass (src msg type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) (n : Nat) :
    metta (Atom.error src msg) type_ space b dispatch ev (n + 1) =
    [(Atom.error src msg, b)] := by
  simp [metta, isEmptyAtom, Atom.empty, isErrorAtom, Atom.error,
        BEq.beq, Atom.beq]

/-! ## interpretArgs Base Case -/

/-- Empty argument list produces empty expression. -/
theorem interpretArgs_nil (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) (n : Nat) :
    interpretArgs [] [] space b dispatch ev (n + 1) =
    [(.expression [], b)] := rfl

/-! ## Non-expression mettaCall -/

/-- mettaCall on a variable returns it unchanged. -/
theorem mettaCall_variable (v : String) (type_ : Atom) (space : Space) (b : Bindings)
    (dispatch : GroundedDispatch) (ev : List Atom) (n : Nat) :
    mettaCall (.var v) type_ space b dispatch ev (n + 1) = [(.var v, b)] := by
  simp [mettaCall, isErrorAtom]

/-! ## Bindings Properties -/

/-- Empty bindings have no loop. -/
theorem empty_bindings_no_loop : Bindings.empty.hasLoop = false := rfl

/-- Assigning "x" to symbol "a" in empty bindings has no loop. -/
example : (Bindings.empty.assign "x" (.symbol "a")).hasLoop = false := rfl

/-! ## matchTypes Properties -/

/-- matchTypes with %Undefined% on either side always succeeds. -/
theorem matchTypes_undefined_succeeds (t : Atom) (b : Bindings) :
    matchTypes Atom.undefinedType t b ≠ [] := by
  simp [matchTypes, Atom.undefinedType, BEq.beq, Atom.beq]

/-- matchTypes with Atom on either side always succeeds. -/
theorem matchTypes_atom_succeeds (t : Atom) (b : Bindings) :
    matchTypes t Atom.atomType b ≠ [] := by
  simp [matchTypes, Atom.atomType, BEq.beq, Atom.beq]

end Mettapedia.Languages.MeTTa.HE
