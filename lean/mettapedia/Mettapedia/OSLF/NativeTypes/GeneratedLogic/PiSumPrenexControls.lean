import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

/-!
# Controls: the π-calculus with sums through the front door

`piSumCalc` asked through the front door with its canonical forms (`PiSumPrenexForms.forms`), which read the language
modulo its bag, the multisets of its sums, its restriction laws, the empty sum and its laws of replication, in the
typed reading. Free names are free variables of the name sort (`x`, `w`, `z`), restricted names bound variables. A
sum of guards is written `[g + …]`.

- **A silent prefix is taken**: `[τ.0]` ends at `0` (`silent_step`).
- **A choice is resolved**: in `[x(y).0 + z(y).0] | [x⟨w⟩.0]` the input on `x` communicates and the input on `z` is
  discarded, ending at `0` (`choice_resolved`); with a silent alternative, `[x(y).0 + τ.[z⟨w⟩.0]] | [x⟨w⟩.0]` can
  also take the silent prefix, leaving the output on `x` waiting (`silent_alternative`).
- **Different channels do not communicate** (negative): `[x(y).0] | [z⟨w⟩.0]` has no step (`channels_apart`).
- **A server serves once and stays**: `![x(y).0] | [x⟨w⟩.0]` ends at the server alone (`server_serves_once`); the
  forwarder `![x(y).[x⟨y⟩.0]] | [x⟨w⟩.0]` runs forever (`forwarder_diverges`).
- **A private name is sent out of its scope**: `(νa)[x⟨a⟩.0] | [x(y).[y⟨w⟩.0]]` ends at `(νa)[a⟨w⟩.0]`
  (`sent_name_escapes`).
- **The empty sum is inaction** (`empty_sum_is_inaction`).
- **A private channel stays private** (negative): `(νa)[a(y).0] | [x⟨w⟩.0]` has no step (`private_channel_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums (piSumCalc)
open PiControls (steps endsAt forever zero par restrict replicate)

abbrev PiSum := referenceStructure RelationEnv.empty piSumCalc PiSumPrenexForms.reading

/-- The front door, with the canonical forms of the π-calculus with sums at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] piSumCalc 3 formula term none rounds (some (PiSumPrenexForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : PiSum.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ PiSum.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

/-- A sum of guards. -/
def choice (guards : List Pattern) : Pattern := .apply "PiSum" [.collection .hashBag guards none]

/-- An input guard. -/
def receive (channel body : Pattern) : Pattern := .apply "PiRecv" [channel, .lambda none body]

/-- An output guard followed by a process. -/
def send (channel datum continuation : Pattern) : Pattern := .apply "PiSend" [channel, datum, continuation]

/-- A silent guard followed by a process. -/
def silent (continuation : Pattern) : Pattern := .apply "PiTau" [continuation]

/-- The free names `x`, `w` and `z`. -/
def x : Pattern := .fvar "x"
def w : Pattern := .fvar "w"
def z : Pattern := .fvar "z"

/-! ## Choice -/

theorem silent_step_answer : answer (endsAt zero) (choice [silent zero]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A silent prefix is taken**: `[τ.0]` ends at `0`. -/
theorem silent_step : PiSum.sat Env.closed (endsAt zero) (choice [silent zero]) := answer_proved silent_step_answer

/-- `[x(y).0 + z(y).0] | [x⟨w⟩.0]`. -/
def twoInputs : Pattern := par [choice [receive x zero, receive z zero], choice [send x w zero]]

theorem choice_resolved_answer : answer (endsAt zero) twoInputs 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A choice is resolved**: the input on `x` communicates, the input on `z` is discarded, and the run ends at `0`. -/
theorem choice_resolved : PiSum.sat Env.closed (endsAt zero) twoInputs := answer_proved choice_resolved_answer

/-- `[x(y).0 + τ.[z⟨w⟩.0]] | [x⟨w⟩.0]`. -/
def silentAlternative : Pattern :=
  par [choice [receive x zero, silent (choice [send z w zero])], choice [send x w zero]]

theorem silent_alternative_answer :
    answer (.possibly .any (.is (par [choice [send z w zero], choice [send x w zero]]))) silentAlternative 4 =
      .proved (.exploration 4) := by
  decide +kernel

/-- **A silent alternative can be taken instead**, leaving the output on `x` waiting. -/
theorem silent_alternative :
    PiSum.sat Env.closed (.possibly .any (.is (par [choice [send z w zero], choice [send x w zero]])))
      silentAlternative :=
  answer_proved silent_alternative_answer

/-- `[x(y).0] | [z⟨w⟩.0]`. -/
def apart : Pattern := par [choice [receive x zero], choice [send z w zero]]

theorem channels_apart_answer : answer steps apart 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Different channels do not communicate.** -/
theorem channels_apart : ¬ PiSum.sat Env.closed steps apart := answer_refuted channels_apart_answer

/-! ## Replication -/

/-- `![x(y).0] | [x⟨w⟩.0]`. -/
def serving : Pattern := par [replicate (choice [receive x zero]), choice [send x w zero]]

theorem server_serves_once_answer :
    answer (endsAt (replicate (choice [receive x zero]))) serving 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A server serves once and stays.** -/
theorem server_serves_once : PiSum.sat Env.closed (endsAt (replicate (choice [receive x zero]))) serving :=
  answer_proved server_serves_once_answer

/-- `![x(y).[x⟨y⟩.0]] | [x⟨w⟩.0]`. -/
def forwarder : Pattern :=
  par [replicate (choice [receive x (choice [send x (.bvar 0) zero])]), choice [send x w zero]]

theorem forwarder_diverges_answer : answer forever forwarder 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The forwarder runs forever**: its step returns to the same canonical process. -/
theorem forwarder_diverges : PiSum.sat Env.closed forever forwarder := answer_proved forwarder_diverges_answer

/-! ## Restriction -/

/-- `(νa)[x⟨a⟩.0] | [x(y).[y⟨w⟩.0]]`. -/
def sending : Pattern :=
  par [restrict (choice [send x (.bvar 0) zero]), choice [receive x (choice [send (.bvar 0) w zero])]]

theorem sent_name_escapes_answer :
    answer (endsAt (restrict (choice [send (.bvar 0) w zero]))) sending 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A private name is sent out of its scope**, and the receiver uses it under the restriction. -/
theorem sent_name_escapes : PiSum.sat Env.closed (endsAt (restrict (choice [send (.bvar 0) w zero]))) sending :=
  answer_proved sent_name_escapes_answer

theorem empty_sum_is_inaction_answer : answer (.is zero) (choice []) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The empty sum is inaction.** -/
theorem empty_sum_is_inaction : PiSum.sat Env.closed (.is zero) (choice []) := answer_proved empty_sum_is_inaction_answer

/-- `(νa)[a(y).0] | [x⟨w⟩.0]`. -/
def private_ : Pattern := par [restrict (choice [receive (.bvar 0) zero]), choice [send x w zero]]

theorem private_channel_stuck_answer : answer steps private_ 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private channel stays private.** -/
theorem private_channel_stuck : ¬ PiSum.sat Env.closed steps private_ := answer_refuted private_channel_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexControls
