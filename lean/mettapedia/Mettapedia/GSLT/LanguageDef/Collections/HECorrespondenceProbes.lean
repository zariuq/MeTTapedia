import Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence

/-!
# The probe table against HE's interpreter, at every budget

The five probe rows of `EvaluationControls` as an HE space (`probes`), and HE's
interpreter on each row at every budget from the least one that completes it,
with the budget a variable of the proof: nine for the first three rows,
seventeen for the fourth and ten for the fifth (`he_probe_p1`, …,
`he_probe_p5`). Together they give the HE column of the table, `(+ 1 2)`,
`(+ 1 2)`, `(h (f a))`, `(wrapped 5)` and `5`, at every budget of at least
seventeen (`he_probe_table`).

The fourth row needs the largest budget: the result `(h (f a))` of `p4` is
evaluated at `%Undefined%`, the call of `h` returns `(wrapped (f a))`, and that
result is evaluated again, its argument giving `5`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The probe program of `EvaluationControls` as an HE space. -/
def probes : Space := Space.ofList [
  equation (apply "f" [symbol "a"]) (symbol "5"),
  typed "h" (arrow [Atom.atomType, Atom.undefinedType]),
  equation (apply "h" [.var "x"]) (apply "wrapped" [.var "x"]),
  typed "p1" (arrow [Atom.atomType, Atom.atomType]),
  equation (apply "p1" [.var "x"]) (.var "x"),
  typed "p2" (arrow [Atom.atomType, Atom.atomType]),
  equation (apply "p2" [.var "x"]) (apply "+" [symbol "1", symbol "2"]),
  typed "p3" (arrow [Atom.atomType, Atom.atomType]),
  equation (apply "p3" [.var "x"]) (apply "h" [.var "x"]),
  typed "p4" (arrow [Atom.atomType, Atom.undefinedType]),
  equation (apply "p4" [.var "x"]) (apply "h" [.var "x"]),
  typed "p5" (arrow [Atom.atomType, Atom.undefinedType]),
  equation (apply "p5" [.var "x"]) (.var "x")]

set_option maxHeartbeats 4000000 in
/-- `(p1 (+ 1 2))`, declared `Atom` to `Atom`, returns its argument as written. -/
theorem he_probe_p1 (fuel : ℕ) (enough : 9 ≤ fuel) :
    (eval probes (apply "p1" [apply "+" [symbol "1", symbol "2"]]) fuel).map Prod.fst =
      [apply "+" [symbol "1", symbol "2"]] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 9 := ⟨fuel - 9, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
/-- `(p2 (f a))` returns its body `(+ 1 2)` as written. -/
theorem he_probe_p2 (fuel : ℕ) (enough : 9 ≤ fuel) :
    (eval probes (apply "p2" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
      [apply "+" [symbol "1", symbol "2"]] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 9 := ⟨fuel - 9, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
/-- `(p3 (f a))` returns the substituted body `(h (f a))` as written. -/
theorem he_probe_p3 (fuel : ℕ) (enough : 9 ≤ fuel) :
    (eval probes (apply "p3" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
      [apply "h" [apply "f" [symbol "a"]]] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 9 := ⟨fuel - 9, by omega⟩
  cbv

set_option maxHeartbeats 60000000 in
/-- `(p4 (f a))`, declared `Atom` to `%Undefined%`, evaluates its substituted
body: `(wrapped 5)`. -/
theorem he_probe_p4 (fuel : ℕ) (enough : 17 ≤ fuel) :
    (eval probes (apply "p4" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
      [apply "wrapped" [symbol "5"]] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 17 := ⟨fuel - 17, by omega⟩
  cbv

set_option maxHeartbeats 4000000 in
/-- `(p5 (f a))` evaluates its substituted body `(f a)`: `5`. -/
theorem he_probe_p5 (fuel : ℕ) (enough : 10 ≤ fuel) :
    (eval probes (apply "p5" [apply "f" [symbol "a"]]) fuel).map Prod.fst = [symbol "5"] := by
  obtain ⟨n, rfl⟩ : ∃ n, fuel = n + 10 := ⟨fuel - 10, by omega⟩
  cbv

/-- **HE's interpreter computes the HE column of the probe table** at every
budget of at least seventeen: `(+ 1 2)`, `(+ 1 2)`, `(h (f a))`, `(wrapped 5)`,
`5`. -/
theorem he_probe_table (fuel : ℕ) (enough : 17 ≤ fuel) :
    (eval probes (apply "p1" [apply "+" [symbol "1", symbol "2"]]) fuel).map Prod.fst =
        [apply "+" [symbol "1", symbol "2"]] ∧
      (eval probes (apply "p2" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
        [apply "+" [symbol "1", symbol "2"]] ∧
      (eval probes (apply "p3" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
        [apply "h" [apply "f" [symbol "a"]]] ∧
      (eval probes (apply "p4" [apply "f" [symbol "a"]]) fuel).map Prod.fst =
        [apply "wrapped" [symbol "5"]] ∧
      (eval probes (apply "p5" [apply "f" [symbol "a"]]) fuel).map Prod.fst = [symbol "5"] :=
  ⟨he_probe_p1 fuel (by omega), he_probe_p2 fuel (by omega), he_probe_p3 fuel (by omega),
    he_probe_p4 fuel enough, he_probe_p5 fuel (by omega)⟩

end Mettapedia.GSLT.LanguageDef.Collections.HECorrespondence.Interpreter
