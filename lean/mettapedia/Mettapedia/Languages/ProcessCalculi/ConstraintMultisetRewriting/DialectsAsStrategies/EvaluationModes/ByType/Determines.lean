import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes.ByType.Choice

/-!
# What the typed family determines

* `weakening_determines` (`TDesign`, all four designs): the two weakening laws hold together exactly
  in `byType`. With `resultWeakening_iff` and `heldWeakening_iff` this says which law forces which
  choice: weakening a value result forces the default "run"; weakening a held annotation to `Atom`
  forces `Atom` text to run at value positions.
* `determines_rows`: the rows the brief asks about, run in `byType` and, for comparison, in
  `codeOnly` (the code-value reading, which `Embed.codeValue_eq_codeOnly` identifies with the
  study's code value): the three conflicting Prime test lines, Hyperon Experimental's `let` row
  (`M-1`), HE's `if`, and the PeTTa lane's held arguments; and for each, the program a programmer
  writes in `byType` to get the other behaviour.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Core CoreLaws Typed Acceptance

namespace ByType

/-- **The two weakening laws hold together exactly in `byType`.** -/
theorem weakening_determines (td : TDesign) :
    (KeepsResultWeakening td ∧ KeepsHeldWeakening td) ↔ td = byType := by
  constructor
  · rintro ⟨_, h⟩
    exact (heldWeakening_iff td).mp h
  · rintro rfl
    exact ⟨keepsResultWeakening_of byType rfl, byType_keepsHeldWeakening⟩

/-! ## The bit that remains: what plain `Atom` text does at a value position -/

/-- **In `codeOnly`, `(Code T)` text has the plain reading and `Atom` text is inert**, at the root of
every program under every unchecked value result. -/
theorem codeOnly_root (T : CTy) {R : CTy} (hR : R.holds = false) (hRc : R.check = none)
    (P0 : TProg) (M : Atom) :
    (∀ L, PrintsB codeOnly (heldBodyT "g" (.code T) R (V "x") :: P0) (Laws.gQ M) L ↔
      PrintsB codeOnly (heldBodyT "g" (.code T) R (V "x") :: P0) M L) ∧
    PrintsB codeOnly (heldBodyT "g" .atom R (V "x") :: P0) (Laws.gQ M) [M] := by
  have hcode : rdOf codeOnly (heldTyped [.code T] [V "x"]) R "x" = true := by
    simp [rdOf, runsAt, codeOnly, kindOf, heldTyped, patVars, V, hR]
  have hatom : rdOf codeOnly (heldTyped [.atom] [V "x"]) R "x" = false := by
    simp [rdOf, runsAt, codeOnly, kindOf, heldTyped, patVars, V]
  refine ⟨fun L => ?_, ⟨0 + 4, ?_⟩⟩
  · apply printsB_iff_of_shift 4 1
    intro n
    rw [runB_heldId codeOnly rfl hR hRc P0 M n, if_pos hcode]
    cases runB codeOnly (heldBodyT "g" (.code T) R (V "x") :: P0) (n + 1) M with
    | none => rfl
    | some A => simp only [Option.map_some]; congr 1; exact Laws.observe_prefix _ "g" A
  · rw [answersB_eq, runB_heldId codeOnly rfl hR hRc P0 M 0, if_neg (by simp [hatom])]
    rfl

/-- **The bit that remains.** `byType` keeps both weakening laws; `codeOnly` keeps the weakening of
value results and gives up the weakening of held annotations, and in exchange keeps a value handed to
an `Atom` parameter inert under a value result (`Adversarial.data_through_held_rows`). -/
theorem remaining_bit :
    (KeepsResultWeakening byType ∧ KeepsHeldWeakening byType) ∧
      (KeepsResultWeakening codeOnly ∧ ¬ KeepsHeldWeakening codeOnly) :=
  ⟨(weakening_determines byType).mpr rfl,
    keepsResultWeakening_of codeOnly rfl, fun h => absurd ((heldWeakening_iff codeOnly).mp h)
      (by decide)⟩

/-! ## The rows -/

/-- `(: roles:compute (-> Proc Proc)) (= (roles:compute $x) $x)`. -/
def rolesCompute : TFn := ⟨"roles:compute", some ([.proc], .proc), [([V "x"], V "x")]⟩

/-- `(: via-id (-> Atom %Undefined%)) (= (via-id $x) (myid $x))` with `myid : (-> %Undefined%
%Undefined%)`. -/
def viaIdProgT : TProg :=
  [tfA, valueIdX .undef, ⟨"via-id", some ([.atom], .undef), [([V "x"], E [S "myid", V "x"])]⟩]

/-- **The rows.** In order: the `%Undefined%` Prime line and its other behaviour; the two `Proc` Prime
lines and the result type they would need; the values-final line; HE's `let` row and the explicit run;
HE's `if` and the held result; the PeTTa lane's held arguments at a field and through an evaluated
identity, with the explicit hold. -/
theorem determines_rows :
    -- `held_arguments`: `(: held-undefined (-> Atom %Undefined%))`, `(held-undefined (f a))`
    answersB byType [tfA, heldIdT "held-undefined" .atom .undef] F
        (E [S "held-undefined", callFA]) = some [N 5] ∧
    answersB byType [tfA, holdFn, heldBodyT "held-undefined" .atom .undef (E [S "hold", V "x"])]
        F (E [S "held-undefined", callFA]) = some [callFA] ∧
    -- `atom_result_type`: `(: held (-> Atom Proc))`, `(held (+ 1 2))`
    answersB byType [heldIdT "held" .atom .proc] F (E [S "held", E [S "+", N 1, N 2]]) =
        some [N 3] ∧
    answersB byType [heldIdT "held" .atom .atom] F (E [S "held", E [S "+", N 1, N 2]]) =
        some [E [S "+", N 1, N 2]] ∧
    answersB byType [heldIdT "held" .atom (.code .number)] F
        (E [S "held", E [S "+", N 1, N 2]]) = some [E [S "+", N 1, N 2]] ∧
    -- `atom_proc_roles`: `(: roles:changing (-> Atom Proc))`, `(roles:changing (+ 4 5))`
    answersB byType [heldIdT "roles:changing" .atom .proc] F
        (E [S "roles:changing", E [S "+", N 4, N 5]]) = some [N 9] ∧
    answersB byType [heldIdT "roles:changing" .atom .atom] F
        (E [S "roles:changing", E [S "+", N 4, N 5]]) = some [E [S "+", N 4, N 5]] ∧
    -- `(roles:compute (roles:hold (+ 7 8)))`: values are final
    answersB byType [heldIdT "roles:hold" .atom .atom, rolesCompute] F
        (E [S "roles:compute", E [S "roles:hold", E [S "+", N 7, N 8]]]) =
      some [E [S "+", N 7, N 8]] ∧
    -- HE's `M-1`: `(let $y (held-atom (f a)) $y)`, and the explicit run
    answersB byType [tfA, heldIdT "held-atom" .atom .atom] F qLet = some [callFA] ∧
    answersB byType [tfA, heldIdT "held-atom" .atom .atom] F
        (E [S "let", V "y", E [S "held-atom", callFA], E [S "eval", V "y"]]) = some [N 5] ∧
    -- HE's `if`: `(my-if True (f a) (boom))`, and a held result
    answersB byType [tfA, myIfT .atom .undef] F qIf = some [N 5] ∧
    answersB byType [tfA, myIfT .atom .atom] F qIf = some [callFA] ∧
    -- the PeTTa lane's held arguments: a field, and an evaluated identity; then the explicit hold
    answersB byType [tfA, heldBodyT "hu-wrap" .atom .undef (E [S "wrap", V "x"])] F qWrap =
        some [E [S "wrap", N 5]] ∧
    answersB byType
        [tfA, holdFn, heldBodyT "hu-wrap" .atom .undef (E [S "wrap", E [S "hold", V "x"]])] F
        qWrap = some [E [S "wrap", callFA]] ∧
    answersB byType viaIdProgT F (E [S "via-id", callFA]) = some [N 5] := by
  decide +kernel

/-- The same rows in `codeOnly` (code value's reading): the `Proc` lines and the PeTTa rows come
out as written text, the `%Undefined%` line does not. -/
theorem codeOnly_rows :
    answersB codeOnly [tfA, heldIdT "held-undefined" .atom .undef] F
        (E [S "held-undefined", callFA]) = some [callFA] ∧
    answersB codeOnly [heldIdT "held" .atom .proc] F (E [S "held", E [S "+", N 1, N 2]]) =
        some [E [S "+", N 1, N 2]] ∧
    answersB codeOnly [heldIdT "roles:changing" .atom .proc] F
        (E [S "roles:changing", E [S "+", N 4, N 5]]) = some [E [S "+", N 4, N 5]] ∧
    answersB codeOnly [tfA, heldIdT "held-atom" .atom .atom] F qLet = some [callFA] ∧
    answersB codeOnly [tfA, myIfT .atom .undef] F qIf = some [callFA] ∧
    answersB codeOnly [tfA, heldBodyT "hu-wrap" .atom .undef (E [S "wrap", V "x"])] F qWrap =
        some [E [S "wrap", callFA]] ∧
    answersB codeOnly viaIdProgT F (E [S "via-id", callFA]) = some [callFA] ∧
    answersB codeOnly [tfA, heldIdT "held-undefined" (.code .number) .undef] F
        (E [S "held-undefined", callFA]) = some [N 5] := by
  decide +kernel

end ByType

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.EvaluationModes
