import Mettapedia.Languages.MeTTa.PeTTa.RunsTells
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPatternDecides

/-!
# Every read and take is decided

`RunsTells` shows that a `match` reads, and a `remove-atom` takes, exactly the occurrences
whose firing the step admits, for every scan the machine completed. A scan fails to complete
only when the fuelled unifier runs out of fuel on a row. `UnifyingDecides` proves that it
never does on an idempotent substitution. So the two theorems hold with no hypothesis that
the scan completed, for rows with variables as for rows without.

* `scan_completes`: a `match` scan completes, for any rows, when the reader's bindings are
  idempotent.
* `selectedRows_completes`: a `remove-atom` selection completes, for any rows.
* `every_match_reads_exactly_the_admissible`, `every_removal_takes_exactly_the_admissible`:
  the theorems of `RunsTells` with the completed scan as a conclusion.
* `reached_match_reads_exactly_the_admissible`: the same for the bindings of any evaluation
  the streaming machine reaches from an entry, with no hypothesis on the bindings.
* `scanCall_completes`: a call's selection among the equation rows completes, for any rows
  and any argument patterns, the list view included (`UnifyingPatternDecides`);
  `reached_call_selection_completes`: the same for any evaluation the machine reaches.

Positive example: `Controls.open_rows_scan_completes` (rows that hold variables, one of them
twice, read by a pattern that binds it to a deep term).
Negative example: `Controls.cyclic_reader_scan_fails` (a reader whose bindings are not
idempotent: the scan of one row does not complete, so the hypothesis is used).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames)
open PeTTaQueryInterpretation (scan)
open Unifying (unify)

/-- **A `match` scan completes**, whatever the rows hold, when the reader's bindings are
idempotent. -/
theorem scan_completes {O : Type} (label : O → Atom) (bindings : Subst) (pattern : Atom)
    (idempotent : Unifying.Idempotent bindings) :
    ∀ (use : Nat) (rows : List O), ∃ packets, scan label bindings pattern use rows = some packets
  | _, [] => ⟨[], rfl⟩
  | use, row :: rest => by
      obtain ⟨later, scanned⟩ := scan_completes label bindings pattern idempotent (use + 1) rest
      have decides := Unifying.unify_decides bindings pattern
        (Unifying.rename use (label row)) idempotent
      simp only [scan, scanned, Option.bind_eq_bind, Option.bind_some]
      cases outcome : unify bindings pattern (Unifying.rename use (label row)) with
      | ok bound => exact ⟨_, rfl⟩
      | clash => exact ⟨_, rfl⟩
      | exhausted => exact absurd outcome decides

/-- **A `remove-atom` selection completes**, whatever the rows hold. -/
theorem selectedRows_completes {O : Type} (label : O → Atom) (pattern : Atom) :
    ∀ (use : Nat) (rows : List O),
      ∃ taken, PeTTaStoreSelection.selectedRows label pattern use rows = some taken
  | _, [] => ⟨[], rfl⟩
  | use, row :: rest => by
      obtain ⟨later, selected⟩ := selectedRows_completes label pattern (use + 1) rest
      have decides := Unifying.unify_decides [] pattern (Unifying.rename use (label row))
        (fun _ _ found => by cases found)
      simp only [PeTTaStoreSelection.selectedRows, selected, Option.bind_eq_bind,
        Option.bind_some]
      cases outcome : unify [] pattern (Unifying.rename use (label row)) with
      | ok bound => exact ⟨_, rfl⟩
      | clash => exact ⟨_, rfl⟩
      | exhausted => exact absurd outcome decides

/-- **A call's selection among the equation rows completes**, whatever the rows hold, when
the caller's bindings are idempotent: no equation's argument patterns run the unifier out
of fuel, with or without the list view. -/
theorem scanCall_completes {O : Type} (label : O → Atom) (bindings : Subst) (head : String)
    (values : List Atom) (idempotent : Unifying.Idempotent bindings) :
    ∀ (use : Nat) (rows : List O),
      ∃ packets, scanCall label bindings head values use rows = some packets
  | _, [] => ⟨[], rfl⟩
  | use, row :: rest => by
      simp only [scanCall]
      cases found : LiveEquations.equationOfRow (label row) with
      | none => exact scanCall_completes label bindings head values idempotent use rest
      | some equation =>
          by_cases selected :
              (equation.head == head && equation.arguments.length == values.length) = true
          · obtain ⟨later, scanned⟩ :=
              scanCall_completes label bindings head values idempotent (use + 1) rest
            have decides := Unifying.unifyArguments_decides bindings
              (equation.arguments.map (Unifying.rename use)) values idempotent
            simp only [selected, if_true, scanned, Option.bind_eq_bind, Option.bind_some]
            cases outcome : Unifying.unifyArguments bindings
                (equation.arguments.map (Unifying.rename use)) values with
            | ok bound => exact ⟨_, rfl⟩
            | clash => exact ⟨_, rfl⟩
            | exhausted => exact absurd outcome decides
          · simp only [selected, Bool.false_eq_true, if_false]
            exact scanCall_completes label bindings head values idempotent use rest

/-- **A `match` reads exactly the admissible occurrences.** Its scan completes, and the
occurrence at a position is among those read exactly when the reader's knowledge together
with the equation between the pattern and a fresh copy of that occurrence's atom is solvable
in the step's frames. Rows may hold variables. -/
theorem every_match_reads_exactly_the_admissible {O : Type} (label : O → Atom)
    (bindings : Subst) (pattern : Atom) (idempotent : Unifying.Idempotent bindings) (use : Nat)
    (rows : List O) (unique : rows.Nodup) :
    ∃ packets, scan label bindings pattern use rows = some packets ∧
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (occurrence ∈ packets.map Prod.fst ↔
          atomFrames.Solvable (a := PUnit.unit)
            (knowledgeOf bindings ++
              [(pattern, Unifying.rename (use + index) (label occurrence))])) := by
  obtain ⟨packets, scanned⟩ := scan_completes label bindings pattern idempotent use rows
  exact ⟨packets, scanned, fun index occurrence at_ =>
    match_reads_exactly_the_admissible label bindings pattern idempotent use rows packets unique
      scanned index occurrence at_⟩

/-- **A `remove-atom` takes exactly the admissible occurrences.** Its selection completes,
and the occurrence at a position is taken exactly when the equation between the pattern and
a fresh copy of that occurrence's atom is solvable in the step's frames. Rows may hold
variables. -/
theorem every_removal_takes_exactly_the_admissible {O : Type} (label : O → Atom)
    (pattern : Atom) (use : Nat) (rows : List O) (unique : rows.Nodup) :
    ∃ taken, PeTTaStoreSelection.selectedRows label pattern use rows = some taken ∧
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (occurrence ∈ taken ↔
          atomFrames.Solvable (a := PUnit.unit)
            [(pattern, Unifying.rename (use + index) (label occurrence))]) := by
  obtain ⟨taken, selected⟩ := selectedRows_completes label pattern use rows
  exact ⟨taken, selected, fun index occurrence at_ =>
    removal_takes_exactly_the_admissible label pattern use rows taken unique selected index
      occurrence at_⟩

/-- **In every evaluation the machine reaches, a `match` reads exactly the admissible
occurrences.** The bindings of a pending evaluation reached from an entry are idempotent
(`reached_evaluation_idempotent`), so nothing is assumed of them: for any pattern and any
rows, the scan made with those bindings completes and reads the occurrences whose firing
the step admits. -/
theorem reached_match_reads_exactly_the_admissible {O : Type} (label : O → Atom)
    (registry : SpaceSemantics.Program) (fuel : Nat) (world : Streaming.World)
    (expression : Atom) (bindings : Subst) (body : Atom) (caller : List Streaming.Frame)
    (pending : Streaming.Job.execute ⟨.evaluate bindings body, caller⟩ ∈
      (Streaming.advance registry fuel (Streaming.enter world expression)).agenda)
    (pattern : Atom) (use : Nat) (rows : List O) (unique : rows.Nodup) :
    ∃ packets, scan label bindings pattern use rows = some packets ∧
      ∀ (index : Nat) (occurrence : O), rows[index]? = some occurrence →
        (occurrence ∈ packets.map Prod.fst ↔
          atomFrames.Solvable (a := PUnit.unit)
            (knowledgeOf bindings ++
              [(pattern, Unifying.rename (use + index) (label occurrence))])) :=
  every_match_reads_exactly_the_admissible label bindings pattern
    (Streaming.BindingInvariant.reached_evaluation_idempotent registry fuel world expression
      bindings body caller pending)
    use rows unique

/-- **In every evaluation the machine reaches, a call's selection completes**: with the
bindings of a pending evaluation reached from an entry, the selection of the equations of
any head for any values, among any rows, is decided for every row. -/
theorem reached_call_selection_completes {O : Type} (label : O → Atom)
    (registry : SpaceSemantics.Program) (fuel : Nat) (world : Streaming.World)
    (expression : Atom) (bindings : Subst) (body : Atom) (caller : List Streaming.Frame)
    (pending : Streaming.Job.execute ⟨.evaluate bindings body, caller⟩ ∈
      (Streaming.advance registry fuel (Streaming.enter world expression)).agenda)
    (head : String) (values : List Atom) (use : Nat) (rows : List O) :
    ∃ packets, scanCall label bindings head values use rows = some packets :=
  scanCall_completes label bindings head values
    (Streaming.BindingInvariant.reached_evaluation_idempotent registry fuel world expression
      bindings body caller pending)
    use rows

namespace Controls

/-- Rows that hold variables: `(p $y (h $y))` and `(p $z b)`. -/
def openRows : Nat → Atom
  | 0 => .expression [.symbol "p", .var "y", .expression [.symbol "h", .var "y"]]
  | _ => .expression [.symbol "p", .var "z", .symbol "b"]

/-- Positive: the scan of the two open rows by `(p (g (g a)) $w)` completes and reads both;
in the first the variable met twice is bound to a deep term on the way. -/
theorem open_rows_scan_completes :
    ((scan openRows []
        (.expression [.symbol "p", .expression [.symbol "g", .expression [.symbol "g", .symbol "a"]],
          .var "w"]) 0 [0, 1]).map fun packets => packets.map Prod.fst) = some [0, 1] := by
  decide +kernel

/-- Negative: a reader whose bindings are not idempotent (`$x` is bound to `(g $x)`). The
scan of the one row `(pair $u $u)` by `(pair $x $x)` does not complete. -/
theorem cyclic_reader_scan_fails :
    scan (fun _ : Nat => Atom.expression [.symbol "pair", .var "u", .var "u"])
      Unifying.Controls.cyclic (.expression [.symbol "pair", .var "x", .var "x"]) 0 [0] = none := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
