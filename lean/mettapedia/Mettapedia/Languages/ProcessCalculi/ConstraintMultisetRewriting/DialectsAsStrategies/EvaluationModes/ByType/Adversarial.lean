import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Determines

/-!
# Parameter disciplines, inspection of text, and odd programs

**Three disciplines for a parameter.** In this core a parameter of a value type is passed by value
(its argument runs once, before the call, and every answer of the argument is one call), and a held
parameter in `byType` is passed by name (its text runs at each value position where it occurs). By
need (run at the first use, the answer shared, never run if unused) needs a store of memo cells
local to each alternative, which this core does not have and which was not added here; the tree's
call-time-choice calculus (`Machines.BranchLocalNeed.CallTimeChoice`) has it, with the same three
disciplines as profiles and the separating programs proved there (`Witnesses.samePick_need`,
`konstFail_need`, `konstPick_need`, `konstLoop_value_diverges`, ...).

* `konst_rows`: `(= (konst $a $b) $a)` with `$b` unused. By value, an argument with two answers gives
  two answers, a refused argument gives the refusal, and a diverging argument gives no run at all
  (`konst_loop_value`, every fuel); by name each gives the one answer `A`.
* `uses_rows`: a parameter used zero, one and two times on the choice `(two)`.

**Text can be inspected; a run cannot** (`inspect_rows`, `intension_lost_after_run`). A consumer
whose parameter holds receives the text and can take it apart with its equations' patterns (the
text `(+ 1 2)` matches `(+ $a $b)`, the text `3` does not); a consumer whose parameter is a value
type receives the run's value, and two texts with the same answers are no longer told apart.

**Odd programs inside the model** (`odd_rows`): an `if` whose untaken branch diverges or is refused,
an effect counted on the trace, a one-level interpreter over held text, `quote` and `eval`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-! ## By value and by name -/

/-- `(: konst (-> %Undefined% X %Undefined%)) (= (konst $a $b) $a)`. -/
def konstT (X : CTy) : TFn :=
  ⟨"konst", some ([.undef, X], .undef), [([V "a", V "b"], V "a")]⟩

/-- `(: bad (-> Number)) (= (bad) a)`: its only answer is refused. -/
def badT : TFn := ⟨"bad", some ([], .number), [([], S "a")]⟩

/-- `(= (loop) (loop))`. -/
def loopT : TFn := ⟨"loop", none, [([], E [S "loop"])]⟩

/-- The program of the laziness rows. -/
def konstProg (X : CTy) : TProg := [konstT X, twoT, badT, loopT]

/-- `(konst A M)`. -/
def konstQ (M : Atom) : Atom := E [S "konst", S "A", M]

theorem konst_rows :
    answersB byType (konstProg .undef) F (konstQ (E [S "two"])) = some [S "A", S "A"] ∧
    answersB byType (konstProg .atom) F (konstQ (E [S "two"])) = some [S "A"] ∧
    answersB byType (konstProg .undef) F (konstQ (E [S "bad"])) =
      some [E [S "Error", S "a", E [S "BadType", S "Number"]]] ∧
    answersB byType (konstProg .atom) F (konstQ (E [S "bad"])) = some [S "A"] ∧
    runB byType (konstProg .undef) F (konstQ (E [S "loop"])) = none ∧
    answersB byType (konstProg .atom) F (konstQ (E [S "loop"])) = some [S "A"] := by
  decide +kernel

theorem loop_clauses (X : CTy) :
    (elabFnB byType (tmodesOf (konstProg X)) loopT).clauses = [([], .call "loop" [])] := by
  cases X <;> rfl

theorem find_loop (X : CTy) :
    (elabProgB byType (konstProg X)).find "loop" 0 =
      some (elabFnB byType (tmodesOf (konstProg X)) loopT) := by
  cases X <;> rfl

/-- **`(loop)` has no run at any fuel.** -/
theorem loop_none (X : CTy) : ∀ n : Nat,
    exec (elabProgB byType (konstProg X)) n (.enter "loop" []) = none
  | 0 => rfl
  | 1 => by
      rw [Laws.exec_enter_first _ "loop" [] _ [] (.call "loop" []) [] [] 0 (find_loop X) rfl rfl
        (loop_clauses X) rfl fun _ => rfl]
      rfl
  | n + 2 => by
      rw [Laws.exec_enter_first _ "loop" [] _ [] (.call "loop" []) [] [] (n + 1) (find_loop X)
        rfl rfl (loop_clauses X) rfl fun _ => rfl, exec_call]
      simp only [List.map_nil, loop_none X n, Option.map_none]

/-- **By value, an unused diverging argument takes the whole run with it**, at every fuel. -/
theorem konst_loop_value (n : Nat) : runB byType (konstProg .undef) n (konstQ (E [S "loop"])) = none := by
  have hq : queryB byType (konstProg .undef) (konstQ (E [S "loop"])) =
      .bind (.ret (S "A")) (slot 0) (.bind (.call "loop" []) (slot 1)
        (.call "konst" [.var (slot 0), .var (slot 1)])) := by
    rfl
  unfold runB
  rw [hq]
  match n with
  | 0 => rfl
  | 1 => rfl
  | m + 2 =>
      rw [Laws.exec_bind_ret_val, exec_bind]
      match m with
      | 0 => rfl
      | k + 1 =>
          rw [exec_call]
          simp only [List.map_nil, loop_none .undef k, Option.bind_none]

/-- A parameter used zero, one and two times on `(two)`: by value `done` twice, `1 2`, two
pairs; by name `done` once, `1 2`, four pairs. -/
def usesProg (X : CTy) : TProg :=
  [twoT, heldBodyT "zero-use" X .undef (S "done"), heldBodyT "one-use" X .undef (V "x"),
    heldBodyT "two-use" X .undef (E [S "pair", V "x", V "x"])]

theorem uses_rows :
    answersB byType (usesProg .undef) F (E [S "zero-use", E [S "two"]]) =
      some [S "done", S "done"] ∧
    answersB byType (usesProg .atom) F (E [S "zero-use", E [S "two"]]) = some [S "done"] ∧
    answersB byType (usesProg .undef) F (E [S "one-use", E [S "two"]]) = some [N 1, N 2] ∧
    answersB byType (usesProg .atom) F (E [S "one-use", E [S "two"]]) = some [N 1, N 2] ∧
    answersB byType (usesProg .undef) F (E [S "two-use", E [S "two"]]) =
      some [pairOf (N 1) (N 1), pairOf (N 2) (N 2)] ∧
    answersB byType (usesProg .atom) F (E [S "two-use", E [S "two"]]) =
      some [pairOf (N 1) (N 1), pairOf (N 1) (N 2), pairOf (N 2) (N 1), pairOf (N 2) (N 2)] ∧
    answersB codeOnly (usesProg .atom) F (E [S "two-use", E [S "two"]]) =
      some [pairOf (E [S "two"]) (E [S "two"])] := by
  decide +kernel

/-! ## Inspecting text, and what a run loses -/

/-- `(: shape (-> X %Undefined%)) (= (shape (+ $a $b)) (plus-of $a $b))`. -/
def shapeT (X : CTy) : TFn :=
  ⟨"shape", some ([X], .undef), [([E [S "+", V "a", V "b"]], E [S "plus-of", V "a", V "b"])]⟩

/-- `(: swap (-> Atom Atom)) (= (swap (+ $a $b)) (+ $b $a))`: text rebuilt. -/
def swapT : TFn :=
  ⟨"swap", some ([.atom], .atom), [([E [S "+", V "a", V "b"]], E [S "+", V "b", V "a"])]⟩

/-- `(: g (-> Atom %Undefined%)) (= (g $x) (shape $x))`: held text handed to a consumer. -/
def inspectProg (X : CTy) : TProg :=
  [shapeT X, swapT, heldBodyT "g" .atom .undef (E [S "shape", V "x"])]

/-- A held consumer takes the text `(+ 1 2)` apart and tells it from `3`; a value consumer sees
`3` both times. Rebuilt text is still code: `(swap (+ 1 2))` is `(+ 2 1)`, and running it gives
`3`. -/
theorem inspect_rows :
    answersB byType (inspectProg .atom) F (E [S "g", E [S "+", N 1, N 2]]) =
      some [E [S "plus-of", N 1, N 2]] ∧
    answersB byType (inspectProg .atom) F (E [S "g", N 3]) = some [E [S "shape", N 3]] ∧
    answersB byType (inspectProg .undef) F (E [S "g", E [S "+", N 1, N 2]]) =
      some [E [S "shape", N 3]] ∧
    answersB byType (inspectProg .undef) F (E [S "g", N 3]) = some [E [S "shape", N 3]] ∧
    answersB byType (inspectProg .atom) F (E [S "swap", E [S "+", N 1, N 2]]) =
      some [E [S "+", N 2, N 1]] ∧
    answersB byType (inspectProg .atom) F (E [S "eval", E [S "swap", E [S "+", N 1, N 2]]]) =
      some [N 3] := by
  decide +kernel

/-- **After a run, only the answers remain**: through a held parameter returned under a value
result, two texts that print the same lists print the same lists again, in every program. -/
theorem intension_lost_after_run {H : CTy} (hH : H.holds = true) {R : CTy} (hR : R.holds = false)
    (hRc : R.check = none) (P0 : TProg) (M M' : Atom)
    (same : ∀ L, PrintsB byType (heldBodyT "g" H R (V "x") :: P0) M L ↔
      PrintsB byType (heldBodyT "g" H R (V "x") :: P0) M' L) (L : List Atom) :
    PrintsB byType (heldBodyT "g" H R (V "x") :: P0) (Laws.gQ M) L ↔
      PrintsB byType (heldBodyT "g" H R (V "x") :: P0) (Laws.gQ M') L := by
  rw [byType_plain_root hH hR hRc, byType_plain_root hH hR hRc]
  exact same L

/-! ## Odd programs inside the model -/

/-- `(: vif (-> Bool %Undefined% %Undefined% %Undefined%))`: an `if` whose branches are values. -/
def vifT : TFn :=
  ⟨"vif", some ([.bool, .undef, .undef], .undef),
    [([S "True", V "t", V "e"], V "t"), ([S "False", V "t", V "e"], V "e")]⟩

/-- `(: interp (-> Atom %Undefined%))` over `(plus a b)` and `(num n)`: a one-level interpreter. -/
def interpT : TFn :=
  ⟨"interp", some ([.atom], .undef),
    [([E [S "plus", V "a", V "b"]], E [S "+", E [S "interp", V "a"], E [S "interp", V "b"]]),
     ([E [S "num", V "n"]], V "n")]⟩

/-- `(: quote (-> Atom Atom))` with no equation: the call stays as written. -/
def quoteT : TFn := ⟨"quote", some ([.atom], .atom), []⟩

/-- The odd programs. `if`: the untaken held branch never runs, so a diverging or refused branch is
harmless; with value branches both run (refusal printed, divergence: no run at fuel `F`). An effect
(a call of `f`) counted on each answer's trace: two runs by name, one by value. The interpreter takes
held text apart in every design. `quote` keeps text; `eval` of a quotation gives the quotation back
(nothing unquotes it). -/
theorem odd_rows :
    answersB byType [tfA, myIfT .atom .undef, loopT] F
        (E [S "my-if", S "True", N 1, E [S "loop"]]) = some [N 1] ∧
    answersB byType [tfA, myIfT .atom .undef, badT] F
        (E [S "my-if", S "True", N 1, E [S "bad"]]) = some [N 1] ∧
    runB byType [vifT, loopT] F (E [S "vif", S "True", N 1, E [S "loop"]]) = none ∧
    answersB byType [vifT, badT] F (E [S "vif", S "True", N 1, E [S "bad"]]) =
      some [E [S "Error", S "a", E [S "BadType", S "Number"]]] ∧
    (runB byType [tfA, dupT .atom .undef] F (dupQ callFA)).map (Nested.runsOf "f") = some [2] ∧
    (runB byType [tfA, dupT .undef .undef] F (dupQ callFA)).map (Nested.runsOf "f") = some [1] ∧
    (runB codeOnly [tfA, dupT .atom .undef] F (dupQ callFA)).map (Nested.runsOf "f") =
      some [0] ∧
    answersB byType [interpT] F
        (E [S "interp", E [S "plus", E [S "num", N 1], E [S "num", N 2]]]) = some [N 3] ∧
    answersB codeOnly [interpT] F
        (E [S "interp", E [S "plus", E [S "num", N 1], E [S "num", N 2]]]) = some [N 3] ∧
    answersB byType [tfA, quoteT] F (E [S "quote", callFA]) = some [E [S "quote", callFA]] ∧
    answersB byType [tfA, quoteT] F (E [S "eval", E [S "quote", callFA]]) =
      some [E [S "quote", callFA]] := by
  decide +kernel

/-! ## Data handed to a held parameter -/

/-- A value that is text (here `(f a)`, returned by `held-atom`), bound by `let` and handed to a held
parameter, is text again there: `byType` runs it under a value result (`5`, as Hyperon Experimental
and the Prime draft measured), `codeOnly` keeps it (`(f a)`, as the PeTTa lane measured); a held
result keeps it in every design. So `byType` keeps data inert only where the position's type holds:
the parameter's `Atom` alone does not protect a value. -/
theorem data_through_held_rows :
    answersB byType [tfA, heldIdT "held-atom" .atom .atom, heldIdT "g" .atom .undef] F
        (E [S "let", V "v", E [S "held-atom", callFA], E [S "g", V "v"]]) = some [N 5] ∧
    answersB codeOnly [tfA, heldIdT "held-atom" .atom .atom, heldIdT "g" .atom .undef] F
        (E [S "let", V "v", E [S "held-atom", callFA], E [S "g", V "v"]]) = some [callFA] ∧
    answersB byType [tfA, heldIdT "held-atom" .atom .atom, heldIdT "g" .atom .atom] F
        (E [S "let", V "v", E [S "held-atom", callFA], E [S "g", V "v"]]) = some [callFA] ∧
    answersB byType [tfA, heldIdT "held-atom" .atom .atom, heldIdT "g" .undef .undef] F
        (E [S "let", V "v", E [S "held-atom", callFA], E [S "g", V "v"]]) = some [callFA] := by
  decide +kernel

/-! ## With bags, dropping a check may lose every answer -/

/-- `(: g (-> R)) (= (g) 1) (= (g) a)`: two alternatives, the second not a number. -/
def gAltT (R : CTy) : TFn := ⟨"g", some ([], R), [([], N 1), ([], S "a")]⟩

/-- `(= (h 1) done) (= (h a) (loop))`. -/
def hAltT : TFn := ⟨"h", none, [([N 1], S "done"), ([S "a"], E [S "loop"])]⟩

/-- The program: the laziness program's `(loop)`, then `g` and `h`. -/
def bagProg (R : CTy) : TProg := konstProg .undef ++ [gAltT R, hAltT]

/-- `(let $y (g) (h $y))`. -/
def bagQ : Atom := E [S "let", V "y", E [S "g"], E [S "h", V "y"]]

/-- Under `Number` the alternative `a` is refused, the other gives `done`. -/
theorem bag_strong :
    answersB byType (bagProg .number) F bagQ =
      some [S "done", E [S "Error", S "a", E [S "BadType", S "Number"]]] := by
  decide +kernel

theorem bag_loop_none : ∀ n : Nat,
    exec (elabProgB byType (bagProg .undef)) n (.enter "loop" []) = none
  | 0 => rfl
  | 1 => by
      rw [Laws.exec_enter_first _ "loop" [] _ [] (.call "loop" []) [] [] 0 rfl rfl rfl rfl rfl
        fun _ => rfl]
      rfl
  | n + 2 => by
      rw [Laws.exec_enter_first _ "loop" [] _ [] (.call "loop" []) [] [] (n + 1) rfl rfl rfl rfl rfl
        fun _ => rfl, exec_call]
      simp only [List.map_nil, bag_loop_none n, Option.map_none]

theorem bag_loop_call_none (k : Nat) :
    exec (elabProgB byType (bagProg .undef)) k (.comp [] (.call "loop" [])) = none := by
  match k with
  | 0 => rfl
  | j + 1 =>
      rw [exec_call]
      simp only [List.map_nil]
      exact bag_loop_none j

theorem bag_h_none : ∀ n : Nat,
    exec (elabProgB byType (bagProg .undef)) n (.enter "h" [S "a"]) = none
  | 0 => rfl
  | k + 1 => by
      rw [Laws.exec_enter]
      have hfind : (elabProgB byType (bagProg .undef)).find "h" [S "a"].length =
          some (elabFnB byType (tmodesOf (bagProg .undef)) hAltT) := rfl
      have hcl : (elabFnB byType (tmodesOf (bagProg .undef)) hAltT).clauses =
          [([N 1], .ret (S "done")), ([S "a"], .call "loop" [])] := rfl
      rw [hfind]
      simp only
      rw [show firstRefusal (elabFnB byType (tmodesOf (bagProg .undef)) hAltT).argChecks [S "a"] =
        none from rfl]
      simp only
      rw [if_pos (by rw [hcl]; rfl), hcl]
      have hm1 : matchAtom.matchList [N 1] [S "a"] [] = none := rfl
      have hm2 : matchAtom.matchList [S "a"] [S "a"] [] = some [] := rfl
      simp only [runClauses, hm1, hm2, bag_loop_call_none, Option.map_none]

theorem bag_cont_none (m : Nat) :
    exec (elabProgB byType (bagProg .undef)) m
      (.comp [("y", S "a")] (.bind (.ret (.var "y")) (slot 0) (.call "h" [.var (slot 0)]))) =
      none := by
  match m with
  | 0 => rfl
  | 1 => rfl
  | j + 2 =>
      rw [Laws.exec_bind_ret_val, exec_call]
      simp only [List.map, inst_var_head]
      exact bag_h_none j

theorem bag_g_rows :
    runB byType (bagProg .undef) F (E [S "g"]) =
      some [(.val (N 1), ["g"]), (.val (S "a"), ["g"])] := by
  decide +kernel

/-- **Dropping the check loses every answer**: under `%Undefined%` the alternative `a` is no longer
refused, `(h a)` runs `(loop)`, and the whole bag has no run at any fuel, while under `Number` it was
`done` and a refusal. The weakening law holds (its premise, a run that refused nothing, fails under
`Number`); its strengthening "every answer that was not refused survives" is false once answers are
bags. -/
theorem bag_weak_none (n : Nat) : runB byType (bagProg .undef) n bagQ = none := by
  have hq : queryB byType (bagProg .undef) bagQ =
      .bind (.call "g" []) "y" (.bind (.ret (.var "y")) (slot 0) (.call "h" [.var (slot 0)])) :=
    rfl
  unfold runB
  rw [hq]
  match n with
  | 0 => rfl
  | m + 1 =>
      rw [exec_bind]
      cases hg : exec (elabProgB byType (bagProg .undef)) m (.comp [] (.call "g" [])) with
      | none => rfl
      | some L =>
          have hL : L = [(.val (N 1), ["g"]), (.val (S "a"), ["g"])] := by
            have hF : exec (elabProgB byType (bagProg .undef)) F (.comp [] (.call "g" [])) =
                some [(.val (N 1), ["g"]), (.val (S "a"), ["g"])] := bag_g_rows
            exact exec_det _ _ hg hF
          subst hL
          simp only [Option.bind_some, continueEach, bag_cont_none m]
          cases exec (elabProgB byType (bagProg .undef)) m
            (.comp [("y", N 1)] (.bind (.ret (.var "y")) (slot 0) (.call "h" [.var (slot 0)]))) <;>
            rfl

/-! ## A second declared row: a check or an alternative -/

/-- `(= (g $x) (+ $x 1))` under one declared row. -/
def incRow (g : String) (row : List CTy × CTy) : TFn :=
  ⟨g, some row, [([V "x"], E [S "+", V "x", N 1])]⟩

/-- Rows read as alternatives: one copy of the function per row, and a head that answers with
every copy (`(= (g $x) (g#1 $x))`, `(= (g $x) (g#2 $x))`), its parameter typed `H`. -/
def rowsAsAlternatives (H : CTy) (row1 row2 : List CTy × CTy) (body : Atom) : TProg :=
  [⟨"g", some ([H], .undef), [([V "x"], E [S "g#1", V "x"]), ([V "x"], E [S "g#2", V "x"])]⟩,
    ⟨"g#1", some row1, [([V "x"], body)]⟩, ⟨"g#2", some row2, [([V "x"], body)]⟩]

/-- The declared-row rows (measured: `(: g2 (-> Number Number))` and `(: g2 (-> $t $t))` give `2` once
on HE and the Prime draft and twice on the PeTTa lane; `(: q2 (-> Atom Atom))` and
`(: q2 (-> Number Number))` give `(+ 1 2)` on HE, `3` on the Prime draft, both on the PeTTa lane).
Read as checks, the two rows of `g2` are one elaboration whose checks are both rows' checks (here
`Number`), and the answer is `2`; read as alternatives the answer is `2` twice, and removing the row
`(-> $t $t)`, which refuses nothing, takes one `2` away. Rows that disagree on a parameter's mode have no
single elaboration as checks; as alternatives they give the text and the value. -/
theorem declared_rows :
    answersB byType [incRow "g" ([.number], .number)] F (E [S "g", N 1]) = some [N 2] ∧
    answersB byType (rowsAsAlternatives .undef ([.number], .number) ([.var "t"], .var "t")
        (E [S "+", V "x", N 1])) F (E [S "g", N 1]) = some [N 2, N 2] ∧
    answersB byType (rowsAsAlternatives .atom ([.atom], .atom) ([.number], .number) (V "x")) F
        (E [S "g", E [S "+", N 1, N 2]]) = some [E [S "+", N 1, N 2], N 3] := by
  decide +kernel

/-- **A declared row must be a check for the weakening law to hold of rows**: read as
alternatives, adding a row that refuses nothing changes the answers. -/
theorem rows_as_alternatives_break_weakening :
    runB byType [incRow "g" ([.number], .number)] F (E [S "g", N 1]) =
        some [(.val (N 2), ["g"])] ∧
      allVal [(.val (N 2), ["g"])] = true ∧
      (runB byType (rowsAsAlternatives .undef ([.number], .number) ([.var "t"], .var "t")
        (E [S "+", V "x", N 1])) F (E [S "g", N 1])).map (observe true) ≠ some [N 2] := by
  decide +kernel

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
