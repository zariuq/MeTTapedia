import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

/-!
# Controls: the π-calculus through the front door, modulo its restriction laws

`piCalc` asked through the front door with its canonical forms (`PiPrenexForms.forms`), which read the language
modulo its bag, its restriction laws (ν of inaction, exchange and scope extrusion) and its laws of replication
(unfolding, `!0 = 0`, `!!P = !P`, `!(P | Q) = !P | !Q`, `!P | !P = !P`), in π's typed reading. Free
names are free variables of the name sort (`x`, `w`), restricted names bound variables. The parallel fragment reads the
same processes in the same reading.

- **Extrusion lets a guarded input meet an output**: in `(νa)(x(y).a⟨y⟩) | x⟨w⟩` no rule fires as written, since the
  input stands under the restriction; modulo extrusion the two communicate and end at `(νa) a⟨w⟩`
  (`extrusion_enables_comm`). The parallel fragment, without the restriction laws, refutes any step for that process
  (`fragment_stuck`).
- **A private name is sent out of its scope**: `(νa) x⟨a⟩ | x(z).z⟨w⟩` ends at `(νa) a⟨w⟩` (`sent_name_escapes`).
- **Garbage**: `(νa)(x(y).0 | x⟨w⟩)` ends at `0` itself (`garbage_ends_at_inaction`). The fragment's run does not
  end at `0` (`fragment_keeps_garbage`).
- **A private channel stays private** (negative): `(νa) a(y).0 | a'⟨w⟩`, here `(νa) a(y).0 | x⟨w⟩`, has no step
  (`private_channel_stuck`).
- **A server serves once and stays**: `!x(y).0 | x⟨w⟩` ends at the server alone (`server_serves_once`), through
  the server's unfolding, which the parallel fragment lacks (`PiControls.server_waits`). A replicated output serves
  an input the same way (`replicated_output_serves`).
- **The laws of replication**: two copies of a server are one (`two_servers_are_one`), but a server is not one copy
  of its body (`server_not_one_copy`); `!0` is `0` (`replicated_inaction`), and `!(x⟨w⟩ | x(y).0)` is
  `!x⟨w⟩ | !x(y).0` (`replication_distributes`).
- **Divergence**: the forwarder `!x(y).x⟨y⟩ | x⟨w⟩` runs forever (`forwarder_diverges`), its step returning to the
  same canonical process, so a closed region of one process decides it. Without the canonical forms the front door
  leaves it open (`forwarder_open_without_forms`). `!(x⟨w⟩ | x(y).0)` runs forever too (`replicated_pair_diverges`),
  while a server with one client does not (`serving_ends`).
- **A private server stays private** (negative): `(νa) !a(y).0 | x⟨w⟩` has no step (`private_server_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance (piCalc piParallelFragment)
open PiControls (steps endsAt forever zero par input output replicate server restrict)

abbrev Pi := referenceStructure RelationEnv.empty piCalc PiPrenexForms.reading

/-- The front door, with π's canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] piCalc 3 formula term none rounds (some (PiPrenexForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Pi.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Pi.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

/-- The free names `x` and `w`. -/
def x : Pattern := .fvar "x"
def w : Pattern := .fvar "w"

/-! ## Extrusion -/

/-- `(νa)(x(y).a⟨y⟩) | x⟨w⟩`. -/
def guarded : Pattern := par [restrict (input x (output (.bvar 1) (.bvar 0))), output x w]

theorem extrusion_enables_comm_answer :
    answer (endsAt (restrict (output (.bvar 0) w))) guarded 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Extrusion lets a guarded input meet an output**, and the run ends at `(νa) a⟨w⟩`. -/
theorem extrusion_enables_comm : Pi.sat Env.closed (endsAt (restrict (output (.bvar 0) w))) guarded :=
  answer_proved extrusion_enables_comm_answer

theorem fragment_stuck_answer : PiControls.answer steps guarded 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the restriction laws the same process has no step.** -/
theorem fragment_stuck : ¬ PiControls.Pi.sat Env.closed steps guarded :=
  PiControls.answer_refuted fragment_stuck_answer

/-- `(νa) x⟨a⟩ | x(z).z⟨w⟩`. -/
def sending : Pattern := par [restrict (output x (.bvar 0)), input x (output (.bvar 0) w)]

theorem sent_name_escapes_answer :
    answer (endsAt (restrict (output (.bvar 0) w))) sending 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A private name is sent out of its scope**, and the receiver uses it under the restriction. -/
theorem sent_name_escapes : Pi.sat Env.closed (endsAt (restrict (output (.bvar 0) w))) sending :=
  answer_proved sent_name_escapes_answer

/-! ## Garbage -/

/-- `(νa)(x(y).0 | x⟨w⟩)`. -/
def unused : Pattern := restrict (par [input x zero, output x w])

theorem garbage_ends_at_inaction_answer : answer (endsAt zero) unused 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A restriction no component uses is garbage**: the run ends at `0` itself. -/
theorem garbage_ends_at_inaction : Pi.sat Env.closed (endsAt zero) unused := answer_proved garbage_ends_at_inaction_answer

theorem fragment_keeps_garbage_answer :
    PiControls.answer (endsAt zero) unused 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Without the restriction laws the run ends at `(νa) 0`, which is not `0`.** -/
theorem fragment_keeps_garbage : ¬ PiControls.Pi.sat Env.closed (endsAt zero) unused :=
  PiControls.answer_refuted fragment_keeps_garbage_answer

/-! ## Privacy -/

/-- `(νa) a(y).0 | x⟨w⟩`. -/
def private_ : Pattern := par [restrict (input (.bvar 0) zero), output x w]

theorem private_channel_stuck_answer : answer steps private_ 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private channel stays private**: the output outside the restriction does not reach it. -/
theorem private_channel_stuck : ¬ Pi.sat Env.closed steps private_ := answer_refuted private_channel_stuck_answer

/-! ## Replication -/

/-- `!x(y).0 | x⟨w⟩`. -/
def serving : Pattern := par [server x zero, output x w]

theorem server_serves_once_answer : answer (endsAt (server x zero)) serving 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A server serves once and stays**: `!x(y).0 | x⟨w⟩` ends at the server alone. -/
theorem server_serves_once : Pi.sat Env.closed (endsAt (server x zero)) serving :=
  answer_proved server_serves_once_answer

theorem replicated_output_serves_answer :
    answer (endsAt (replicate (output x w))) (par [replicate (output x w), input x zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A replicated output serves an input**: `!x⟨w⟩ | x(y).0` ends at `!x⟨w⟩`. -/
theorem replicated_output_serves :
    Pi.sat Env.closed (endsAt (replicate (output x w))) (par [replicate (output x w), input x zero]) :=
  answer_proved replicated_output_serves_answer

theorem two_servers_are_one_answer :
    answer (.is (server x zero)) (par [server x zero, server x zero]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Two copies of a server are one.** -/
theorem two_servers_are_one : Pi.sat Env.closed (.is (server x zero)) (par [server x zero, server x zero]) :=
  answer_proved two_servers_are_one_answer

theorem server_not_one_copy_answer : answer (.is (input x zero)) (server x zero) 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A server is not one copy of its body.** -/
theorem server_not_one_copy : ¬ Pi.sat Env.closed (.is (input x zero)) (server x zero) :=
  answer_refuted server_not_one_copy_answer

theorem replicated_inaction_answer : answer (.is zero) (replicate zero) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`!0` is `0`.** -/
theorem replicated_inaction : Pi.sat Env.closed (.is zero) (replicate zero) := answer_proved replicated_inaction_answer

/-- `x⟨w⟩ | x(y).0`. -/
def pair : Pattern := par [output x w, input x zero]

theorem replication_distributes_answer :
    answer (.is (par [replicate (output x w), replicate (input x zero)])) (replicate pair) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Replication distributes**: `!(x⟨w⟩ | x(y).0)` is `!x⟨w⟩ | !x(y).0`. -/
theorem replication_distributes :
    Pi.sat Env.closed (.is (par [replicate (output x w), replicate (input x zero)])) (replicate pair) :=
  answer_proved replication_distributes_answer

/-- `!x(y).x⟨y⟩ | x⟨w⟩`. -/
def forwarder : Pattern := par [server x (output x (.bvar 0)), output x w]

theorem forwarder_diverges_answer : answer forever forwarder 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The forwarder runs forever**: its step returns to the same canonical process. -/
theorem forwarder_diverges : Pi.sat Env.closed forever forwarder := answer_proved forwarder_diverges_answer

/-- **Without the canonical forms the front door leaves the forwarder open.** -/
theorem forwarder_open_without_forms : ask RelationEnv.empty [] piCalc 3 forever forwarder none 4 = .unknown 4 := by
  decide +kernel

theorem replicated_pair_diverges_answer : answer forever (replicate pair) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`!(x⟨w⟩ | x(y).0)` runs forever**: each step leaves the same canonical process. -/
theorem replicated_pair_diverges : Pi.sat Env.closed forever (replicate pair) :=
  answer_proved replicated_pair_diverges_answer

theorem serving_ends_answer : answer forever serving 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A server with one client does not run forever**: it serves once, and the server alone has no step. -/
theorem serving_ends : ¬ Pi.sat Env.closed forever serving := answer_refuted serving_ends_answer

/-- `(νa) !a(y).0 | x⟨w⟩`. -/
def privateServer : Pattern := par [restrict (server (.bvar 0) zero), output x w]

theorem private_server_stuck_answer : answer steps privateServer 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private server stays private**: the output outside the restriction does not reach it. -/
theorem private_server_stuck : ¬ Pi.sat Env.closed steps privateServer := answer_refuted private_server_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
