import Mettapedia.Languages.CHR.Machine

/-! Controls for the refined CHR machine, checked by kernel evaluation. The
expected stores are SWI-CHR's for the same programs. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine.Controls

open Mettapedia.Languages.CHR

private def h (name : String) (arguments : List Term) : Head := ⟨name, arguments⟩
private def int (n : Int) : Term := .value (.integer n)

/-- `candidate(1) <=> true.  candidate(N) <=> prime(N), M is N-1, candidate(M).
prime(Y) \ prime(X) <=> 0 =:= X mod Y | true.` -/
private def sieve : Program := ⟨[⟨"candidate", 1⟩, ⟨"prime", 1⟩], [
  ⟨"sieve_end", [], [h "candidate" [int 1]], [], []⟩,
  ⟨"sieve_next", [], [h "candidate" [.var 0]], [],
    [.tell (h "prime" [.var 0]), .assign 1 (.operation .subtract (.index 0) (.literal 1)),
     .tell (h "candidate" [.var 1])]⟩,
  ⟨"sieve_remove", [h "prime" [.var 0]], [h "prime" [.var 1]],
    [.compare .equal (.literal 0) (.operation .modulo (.index 1) (.index 0))], []⟩]⟩

private def final (program : Program) (seeds : List Head) : State :=
  advance (table program) 400 (start seeds)

/-- The primes up to 6 remain, newest first, and the run completed. -/
example : slot ("prime", 1) (final sieve [h "candidate" [int 6]]).store =
    [⟨9, [.integer 2]⟩, ⟨7, [.integer 3]⟩, ⟨3, [.integer 5]⟩] := by decide +kernel

example : (final sieve [h "candidate" [int 6]]).tasks = [] ∧
    (final sieve [h "candidate" [int 6]]).status = .running := by decide +kernel

/-- `start <=> q, r.  q, r <=> s.  q <=> true.`: the body posts `q` and lets it
finish before `r` is told, so only `r` remains. Telling `r` first leaves `s`. -/
private def bodyOrder (first second : String) : Program := ⟨[⟨"start", 0⟩, ⟨"q", 0⟩, ⟨"r", 0⟩, ⟨"s", 0⟩], [
  ⟨"begin", [], [h "start" []], [], [.tell (h first []), .tell (h second [])]⟩,
  ⟨"pair", [], [h "q" [], h "r" []], [], [.tell (h "s" [])]⟩,
  ⟨"drop", [], [h "q" []], [], []⟩]⟩

example : ((final (bodyOrder "q" "r") [h "start" []]).store.flatMap (·.2)).map (·.id) = [2] := by decide +kernel
example : slot ("r", 0) (final (bodyOrder "q" "r") [h "start" []]).store = [⟨2, []⟩] := by decide +kernel
example : slot ("s", 0) (final (bodyOrder "r" "q") [h "start" []]).store = [⟨3, []⟩] := by decide +kernel

/-- A division by zero in a body faults the run. -/
private def divide : Program := ⟨[⟨"d", 1⟩, ⟨"e", 1⟩], [
  ⟨"divide", [], [h "d" [.var 0]], [], [.assign 1 (.operation .quotient (.index 0) (.literal 0)), .tell (h "e" [.var 1])]⟩]⟩

example : (final divide [h "d" [int 1]]).status = .faulted .divisionByZero := by decide +kernel

end Mettapedia.Languages.CHR.Machine.Controls
