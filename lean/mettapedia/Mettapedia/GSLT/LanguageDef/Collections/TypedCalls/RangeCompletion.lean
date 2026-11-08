import Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence

/-!
# HE: completing a typed call at its range

HE returns the raw result of a call whose declared range is `Atom` as written,
and evaluates it once at the declared range otherwise
(`HECorrespondence.he_atom_demand`, `Languages.MeTTa.HE.ordinaryCallReturn_evaluate`);
the model's rule for HE is the same single evaluation of the substituted body
(`HECorrespondence.return_once_iff_inst`). This module checks, in HE's
interpreter, what a fast path must keep for a typed head whose range is not
`Atom`: the evaluation it already performs, and a check of the value at the
range.

* **The range check of a value is a class test.** A number evaluated at
  `Number` is itself, at every budget from two on (`he_number_at_number`); at
  `String` it is the error `(Error n (BadType String Number))`, at every budget
  from two on (`he_number_at_string`).
* **A typed head answers as the untyped one does, through the range check.**
  With `(: f (-> Number Number))` and `(= (f $x) 5)`, `(f 1)` answers `5`, as the
  untyped `(= (u $x) 5)` does (`he_typed_head`, `he_untyped_head`); with
  `(: f2 (-> Number String))` the same body answers the range check's error
  on the value `5` (`he_range_mismatch`).

Each statement holds at every budget from a stated one, the budget a variable
of the proof, as in `HECorrespondence.Interpreter`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeCompletion

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter
  (symbol apply equation typed arrow)

/-- A number. -/
def num (n : ℤ) : Atom := .grounded (.int n)

set_option maxHeartbeats 4000000 in
/-- **A number at `Number` is itself.** -/
theorem he_number_at_number (fuel : ℕ) (enough : 2 ≤ fuel) :
    evalAtom (Space.ofList []) GroundedDispatch.none (num 5) (symbol "Number") Bindings.empty fuel =
      [(num 5, Bindings.empty)] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
/-- **A number at `String` is the range check's error.** -/
theorem he_number_at_string (fuel : ℕ) (enough : 2 ≤ fuel) :
    evalAtom (Space.ofList []) GroundedDispatch.none (num 5) (symbol "String") Bindings.empty fuel =
      [(.expression [symbol "Error", num 5,
        .expression [symbol "BadType", symbol "String", symbol "Number"]], Bindings.empty)] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  cbv

/-- `(: f (-> Number Number))`, `(= (f $x) 5)`, `(: f2 (-> Number String))`,
`(= (f2 $x) 5)` and the untyped `(= (u $x) 5)`. -/
def space : Space := Space.ofList [
  typed "f" (arrow [symbol "Number", symbol "Number"]),
  equation (apply "f" [.var "x"]) (num 5),
  typed "f2" (arrow [symbol "Number", symbol "String"]),
  equation (apply "f2" [.var "x"]) (num 5),
  equation (apply "u" [.var "x"]) (num 5)]

/-- HE's answers for an atom at budget `fuel`. -/
def answers (atom : Atom) (fuel : ℕ) : List Atom :=
  (evalAtom space GroundedDispatch.none atom Atom.undefinedType Bindings.empty fuel).map Prod.fst

set_option maxHeartbeats 8000000 in
/-- **The typed head answers `5`**, its body evaluated and checked at `Number`. -/
theorem he_typed_head (fuel : ℕ) (enough : 10 ≤ fuel) : answers (apply "f" [num 1]) fuel = [num 5] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 10 := ⟨fuel - 10, by omega⟩
  cbv

set_option maxHeartbeats 8000000 in
/-- The untyped head answers `5` as well. -/
theorem he_untyped_head (fuel : ℕ) (enough : 8 ≤ fuel) : answers (apply "u" [num 1]) fuel = [num 5] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 8 := ⟨fuel - 8, by omega⟩
  cbv

set_option maxHeartbeats 8000000 in
/-- **At a range the value does not meet, the answer is the range check's
error on the value**, where the untyped head answers `5`. -/
theorem he_range_mismatch (fuel : ℕ) (enough : 10 ≤ fuel) :
    answers (apply "f2" [num 1]) fuel =
      [.expression [symbol "Error", num 5,
        .expression [symbol "BadType", symbol "String", symbol "Number"]]] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 10 := ⟨fuel - 10, by omega⟩
  cbv

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.RangeCompletion
