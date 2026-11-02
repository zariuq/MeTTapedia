import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: the parallel fragment of π through the front door, modulo its laws

The parallel fragment of the tree's π-calculus (`piParallelFragment`: `piCalc`'s rules without its laws of
restriction and replication), asked through the front door with its canonical forms (`PiForms.forms`), in π's typed
reading. Parallel
composition is a bag with the flattening algebra and inaction as its unit, and the language steps modulo these laws.
The canonical forms keep plain steps, so the questions use plain modalities. Channels and data are names: the free
names `a` and `b`, and a bound variable for a restricted name.

- `a(y).0 | a⟨b⟩` communicates and ends at `0` (`comm_ends`).
- The input inside a nested bag, beside an inaction: the same (`nested_comm_ends`). As written, no rule fires
  at the top bag; its canonical form is the flattened bag, where the communication fires.
- `!a(y).0 | a⟨b⟩` has no step (`server_waits`): a replicated process acts through its unfolding, a law of `piCalc`
  the fragment does not have. With the laws it serves (`PiPrenexControls.server_serves_once`).
- `νx (x(y).0 | x⟨b⟩)` communicates on the restricted channel and ends at `νx. 0` (`restricted_comm_ends`).
- One receiver and two messages: either message is received, and both runs end at the remaining message
  (`two_messages_one_result`).
- An input and an output on different channels do not communicate (`different_channels_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piParallelFragment)

abbrev Pi := referenceStructure RelationEnv.empty piParallelFragment PiForms.reading

/-- The front door, with the canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] piParallelFragment 3 formula term none rounds (some (PiForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Pi.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Pi.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- Every run goes on forever. -/
def forever : Formula 0 := .nu (.and (.possibly .any .top) (.necessarily .any (.var 0)))

def zero : Pattern := .apply "PiNil" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def input (channel body : Pattern) : Pattern := .apply "PiInp" [channel, .lambda none body]
def output (channel datum : Pattern) : Pattern := .apply "PiOut" [channel, datum]
def replicate (process : Pattern) : Pattern := .apply "PiRep" [process]
def server (channel body : Pattern) : Pattern := replicate (input channel body)
def restrict (body : Pattern) : Pattern := .apply "PiNu" [.lambda none body]
def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"

/-! ## Communication -/

theorem comm_ends_answer :
    answer (endsAt zero) (par [input a zero, output a b]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`a(y).0 | a⟨b⟩` communicates and ends at `0`.** -/
theorem comm_ends : Pi.sat Env.closed (endsAt zero) (par [input a zero, output a b]) :=
  answer_proved comm_ends_answer

theorem nested_comm_ends_answer :
    answer (endsAt zero) (par [par [input a zero, zero], output a b]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The input inside a nested bag, beside an inaction, still communicates.** -/
theorem nested_comm_ends : Pi.sat Env.closed (endsAt zero) (par [par [input a zero, zero], output a b]) :=
  answer_proved nested_comm_ends_answer

theorem server_waits_answer : answer steps (par [server a zero, output a b]) 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the laws of replication a server waits**: `!a(y).0 | a⟨b⟩` has no step. -/
theorem server_waits : ¬ Pi.sat Env.closed steps (par [server a zero, output a b]) :=
  answer_refuted server_waits_answer

theorem restricted_comm_ends_answer :
    answer (endsAt (restrict zero)) (restrict (par [input (.bvar 0) zero, output (.bvar 0) b])) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`νx (x(y).0 | x⟨b⟩)` communicates on the restricted channel and ends at `νx. 0`.** -/
theorem restricted_comm_ends :
    Pi.sat Env.closed (endsAt (restrict zero)) (restrict (par [input (.bvar 0) zero, output (.bvar 0) b])) :=
  answer_proved restricted_comm_ends_answer

/-! ## Choice and its absence -/

theorem two_messages_one_result_answer :
    answer (endsAt (output a b)) (par [input a zero, output a b, output a b]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **One receiver and two messages: both runs end at the remaining message.** -/
theorem two_messages_one_result :
    Pi.sat Env.closed (endsAt (output a b)) (par [input a zero, output a b, output a b]) :=
  answer_proved two_messages_one_result_answer

theorem different_channels_stuck_answer :
    answer steps (par [input a zero, output b b]) 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **An input and an output on different channels do not communicate.** -/
theorem different_channels_stuck : ¬ Pi.sat Env.closed steps (par [input a zero, output b b]) :=
  answer_refuted different_channels_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
