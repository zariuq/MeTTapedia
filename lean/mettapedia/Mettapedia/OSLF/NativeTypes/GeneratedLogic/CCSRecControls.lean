import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: CCS with recursion through the front door

`ccsRecCalc` asked through the front door in the environment of five definitions (`definitions`), with its canonical
forms (`CCSRecForms.forms`), which read the language modulo its bag, its sums and its restriction laws, calls as
atoms. Free names are free variables of the name sort (`a`, `b`), restricted names bound variables.

- **A call reacts through its body**: the server `A(x) ≝ x.A(x)` beside `~a.0` answers and is a server again,
  `A(a) | ~a.0` ending at `A(a)` (`server_answers`); alone (`server_waits`) or beside a co-action on another name
  (`server_other_name`) it has no step.
- **Unfolding is a step, not a law**: `A(a)` is not its body `a.A(a)` (`call_not_body`).
- **Two calls react**: `A(a) | B(a)`, with `B(x) ≝ ~x.0`, ends at `A(a)` (`calls_react`); a sum and a call react too,
  `a.0 | B(a)` ending at `0` (`sum_call_reacts`).
- **A silent summand of a body**: `T ≝ τ.0` ends at `0` (`silent_call`), and `D ≝ τ.D` steps only to itself
  (`silent_loop`).
- **Parameters**: `S(x, y) ≝ x.S(y, x)` alternates its channels, so `S(a, b) | ~a.0 | ~b.0` always ends at `S(a, b)`
  (`swap_alternates`) and never at `S(b, a)` (`swap_not_reversed`).
- **A private name as an argument**: `(νz)(A(z) | ~z.0)` reacts inside the restriction and ends at `(νz) A(z)`
  (`private_argument`), and `(νz) A(z) | ~a.0` has no step (`private_stays_private`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.CCS (nil par sum nu act coact tau)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive (ccsRecCalc Definition admits definitionsEnv call)

/-! ## The definitions -/

/-- `A(x) ≝ x.A(x)`: a server, answering on its channel forever. -/
def server : Definition := ⟨1, [act (.bvar 0) (call 0 [.bvar 0])]⟩

/-- `B(x) ≝ ~x.0`: a client, asking once. -/
def client : Definition := ⟨1, [coact (.bvar 0) nil]⟩

/-- `D ≝ τ.D`: a silent loop. -/
def loop : Definition := ⟨0, [tau (call 2 [])]⟩

/-- `S(x, y) ≝ x.S(y, x)`: alternating between two channels. -/
def swap : Definition := ⟨2, [act (.bvar 0) (call 3 [.bvar 1, .bvar 0])]⟩

/-- `T ≝ τ.0`. -/
def once : Definition := ⟨0, [tau nil]⟩

def definitions : List Definition := [server, client, loop, swap, once]

theorem admitted : admits definitions = true := by decide +kernel

abbrev Recursive := referenceStructure (definitionsEnv definitions) ccsRecCalc CCSRecForms.reading

/-- The front door, in the environment of the definitions, with the canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask (definitionsEnv definitions) [] ccsRecCalc 4 formula term none rounds (some (CCSRecForms.forms admitted 4))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Recursive.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Recursive.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- Every run ends, at `result`. -/
def finallyAt (result : Pattern) : Formula 0 :=
  .mu (.or (.and (.is result) (.necessarily .any .bot)) (.and (.possibly .any .top) (.necessarily .any (.var 0))))

/-- The free names `a` and `b`. -/
def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"

/-! ## A call reacts through its body -/

theorem server_answers_answer :
    answer (endsAt (call 0 [a])) (par [call 0 [a], sum [coact a nil]]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **The server answers and is a server again**: `A(a) | ~a.0` ends at `A(a)`. -/
theorem server_answers : Recursive.sat Env.closed (endsAt (call 0 [a])) (par [call 0 [a], sum [coact a nil]]) :=
  answer_proved server_answers_answer

theorem server_waits_answer : answer steps (call 0 [a]) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **Alone, the server waits.** -/
theorem server_waits : ¬ Recursive.sat Env.closed steps (call 0 [a]) :=
  answer_refuted server_waits_answer

theorem server_other_name_answer :
    answer steps (par [call 0 [a], sum [coact b nil]]) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **A co-action on another name is no partner.** -/
theorem server_other_name : ¬ Recursive.sat Env.closed steps (par [call 0 [a], sum [coact b nil]]) :=
  answer_refuted server_other_name_answer

theorem call_not_body_answer :
    answer (.is (sum [act a (call 0 [a])])) (call 0 [a]) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **Unfolding is a step, not a law**: `A(a)` is not `a.A(a)`. -/
theorem call_not_body : ¬ Recursive.sat Env.closed (.is (sum [act a (call 0 [a])])) (call 0 [a]) :=
  answer_refuted call_not_body_answer

/-! ## Calls and sums react -/

theorem calls_react_answer :
    answer (endsAt (call 0 [a])) (par [call 0 [a], call 1 [a]]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **Two calls react through their bodies**: `A(a) | B(a)` ends at `A(a)`. -/
theorem calls_react : Recursive.sat Env.closed (endsAt (call 0 [a])) (par [call 0 [a], call 1 [a]]) :=
  answer_proved calls_react_answer

theorem sum_call_reacts_answer :
    answer (endsAt nil) (par [sum [act a nil], call 1 [a]]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A sum and a call react**: `a.0 | B(a)` ends at `0`. -/
theorem sum_call_reacts : Recursive.sat Env.closed (endsAt nil) (par [sum [act a nil], call 1 [a]]) :=
  answer_proved sum_call_reacts_answer

/-! ## Silent summands of a body -/

theorem silent_call_answer : answer (endsAt nil) (call 4 []) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A call takes a silent summand of its body**: `T` ends at `0`. -/
theorem silent_call : Recursive.sat Env.closed (endsAt nil) (call 4 []) :=
  answer_proved silent_call_answer

theorem silent_loop_answer :
    answer (.and steps (.necessarily .any (.is (call 2 [])))) (call 2 []) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A silent loop steps, and only to itself**: `D ≝ τ.D`. -/
theorem silent_loop : Recursive.sat Env.closed (.and steps (.necessarily .any (.is (call 2 [])))) (call 2 []) :=
  answer_proved silent_loop_answer

/-! ## Parameters -/

/-- `S(a, b) | ~a.0 | ~b.0`. -/
def swapped : Pattern := par [call 3 [a, b], sum [coact a nil], sum [coact b nil]]

theorem swap_alternates_answer : answer (finallyAt (call 3 [a, b])) swapped 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Parameters change places**: `S(x, y) ≝ x.S(y, x)`, so `S(a, b) | ~a.0 | ~b.0` always ends at `S(a, b)`. -/
theorem swap_alternates : Recursive.sat Env.closed (finallyAt (call 3 [a, b])) swapped :=
  answer_proved swap_alternates_answer

theorem swap_not_reversed_answer : answer (finallyAt (call 3 [b, a])) swapped 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **It does not end at `S(b, a)`.** -/
theorem swap_not_reversed : ¬ Recursive.sat Env.closed (finallyAt (call 3 [b, a])) swapped :=
  answer_refuted swap_not_reversed_answer

/-! ## A private name as an argument -/

theorem private_argument_answer :
    answer (endsAt (nu (call 0 [.bvar 0]))) (nu (par [call 0 [.bvar 0], sum [coact (.bvar 0) nil]])) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A private name as an argument**: `(νz)(A(z) | ~z.0)` ends at `(νz) A(z)`. -/
theorem private_argument :
    Recursive.sat Env.closed (endsAt (nu (call 0 [.bvar 0]))) (nu (par [call 0 [.bvar 0], sum [coact (.bvar 0) nil]])) :=
  answer_proved private_argument_answer

theorem private_stays_private_answer :
    answer steps (par [nu (call 0 [.bvar 0]), sum [coact a nil]]) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **A private channel is no other**: `(νz) A(z) | ~a.0` has no step. -/
theorem private_stays_private : ¬ Recursive.sat Env.closed steps (par [nu (call 0 [.bvar 0]), sum [coact a nil]]) :=
  answer_refuted private_stays_private_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecControls
