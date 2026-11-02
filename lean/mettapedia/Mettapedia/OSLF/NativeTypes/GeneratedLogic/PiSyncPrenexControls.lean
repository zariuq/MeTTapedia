import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

/-!
# Controls: the synchronous π-calculus through the front door, modulo its laws

`piSyncCalc` asked through the front door with its canonical forms (`PiSyncPrenexForms.forms`), which read the
language modulo its bag, its restriction laws and its laws of replication, in the typed reading. Free names are free
variables of the name sort (`x`, `w`, `z`), restricted names bound variables.

- **Extrusion lets a guarded input meet an output, and the output's continuation is released**: in
  `(νa)(x(y).a⟨y⟩.0) | x⟨w⟩.z(u).0` no rule fires as written, since the input stands under the restriction; modulo
  extrusion the two communicate and end at `(νa) a⟨w⟩.0 | z(u).0` (`extrusion_releases_continuation`).
- **A private name is sent out of its scope**: `(νa) x⟨a⟩.0 | x(y).y⟨w⟩.0` ends at `(νa) a⟨w⟩.0`
  (`sent_name_escapes`).
- **Garbage**: `(νa)(x(y).0 | x⟨w⟩.0)` ends at `0` itself (`garbage_ends_at_inaction`).
- **An output guards its continuation** (negative): in `x⟨w⟩.z⟨w⟩.0 | z(u).0` the second output waits for the
  first, which has no partner, so there is no step (`continuation_waits`). Asynchronous π has no such guard.
- **A private channel stays private** (negative): `(νa) a(y).0 | x⟨w⟩.0` has no step (`private_channel_stuck`).
- **Replication**: a server serves a client once and stays, and the client's continuation is released
  (`server_releases_continuation`); a replicated output serves an input (`replicated_sender_serves`); two copies of a
  server are one (`two_servers_are_one`); the forwarder `!x(y).x⟨y⟩.0 | x⟨w⟩.0` runs forever (`forwarder_diverges`),
  while a server with one client does not (`serving_ends`, negative); and a private server stays private
  (`private_server_stuck`, negative).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPrenexControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous (piSyncCalc)
open PiControls (steps endsAt forever zero par input restrict replicate server)

abbrev PiSync := referenceStructure RelationEnv.empty piSyncCalc PiSyncPrenexForms.reading

/-- The front door, with synchronous π's canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] piSyncCalc 3 formula term none rounds (some (PiSyncPrenexForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : PiSync.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ PiSync.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

/-- An output of `datum` on `channel`, followed by `continuation`. -/
def send (channel datum continuation : Pattern) : Pattern := .apply "PiOutK" [channel, datum, continuation]

/-- The free names `x`, `w` and `z`. -/
def x : Pattern := .fvar "x"
def w : Pattern := .fvar "w"
def z : Pattern := .fvar "z"

/-! ## Extrusion -/

/-- `(νa)(x(y).a⟨y⟩.0) | x⟨w⟩.z(u).0`. -/
def guarded : Pattern := par [restrict (input x (send (.bvar 1) (.bvar 0) zero)), send x w (input z zero)]

theorem extrusion_releases_continuation_answer :
    answer (endsAt (par [restrict (send (.bvar 0) w zero), input z zero])) guarded 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Extrusion lets a guarded input meet an output, and the output's continuation is released**: the run ends at
`(νa) a⟨w⟩.0 | z(u).0`. -/
theorem extrusion_releases_continuation :
    PiSync.sat Env.closed (endsAt (par [restrict (send (.bvar 0) w zero), input z zero])) guarded :=
  answer_proved extrusion_releases_continuation_answer

/-- `(νa) x⟨a⟩.0 | x(y).y⟨w⟩.0`. -/
def sending : Pattern := par [restrict (send x (.bvar 0) zero), input x (send (.bvar 0) w zero)]

theorem sent_name_escapes_answer :
    answer (endsAt (restrict (send (.bvar 0) w zero))) sending 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A private name is sent out of its scope**, and the receiver uses it under the restriction. -/
theorem sent_name_escapes : PiSync.sat Env.closed (endsAt (restrict (send (.bvar 0) w zero))) sending :=
  answer_proved sent_name_escapes_answer

/-! ## Garbage -/

/-- `(νa)(x(y).0 | x⟨w⟩.0)`. -/
def unused : Pattern := restrict (par [input x zero, send x w zero])

theorem garbage_ends_at_inaction_answer : answer (endsAt zero) unused 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A restriction no component uses is garbage**: the run ends at `0` itself. -/
theorem garbage_ends_at_inaction : PiSync.sat Env.closed (endsAt zero) unused :=
  answer_proved garbage_ends_at_inaction_answer

/-! ## Guards -/

/-- `x⟨w⟩.z⟨w⟩.0 | z(u).0`. -/
def waiting : Pattern := par [send x w (send z w zero), input z zero]

theorem continuation_waits_answer : answer steps waiting 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **An output guards its continuation**: the second output waits for the first, which has no partner. -/
theorem continuation_waits : ¬ PiSync.sat Env.closed steps waiting := answer_refuted continuation_waits_answer

/-- `(νa) a(y).0 | x⟨w⟩.0`. -/
def private_ : Pattern := par [restrict (input (.bvar 0) zero), send x w zero]

theorem private_channel_stuck_answer : answer steps private_ 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private channel stays private**: the output outside the restriction does not reach it. -/
theorem private_channel_stuck : ¬ PiSync.sat Env.closed steps private_ := answer_refuted private_channel_stuck_answer

/-! ## Replication -/

/-- `!x(y).0 | x⟨w⟩.z(u).0`. -/
def serving : Pattern := par [server x zero, send x w (input z zero)]

theorem server_releases_continuation_answer :
    answer (endsAt (par [server x zero, input z zero])) serving 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A server serves a client once and stays, and the client's continuation is released**: the run ends at
`!x(y).0 | z(u).0`. -/
theorem server_releases_continuation :
    PiSync.sat Env.closed (endsAt (par [server x zero, input z zero])) serving :=
  answer_proved server_releases_continuation_answer

/-- `!x⟨w⟩.0 | x(y).0`. -/
def replicatedSender : Pattern := par [replicate (send x w zero), input x zero]

theorem replicated_sender_serves_answer :
    answer (endsAt (replicate (send x w zero))) replicatedSender 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A replicated output serves an input**: `!x⟨w⟩.0 | x(y).0` ends at `!x⟨w⟩.0`. -/
theorem replicated_sender_serves : PiSync.sat Env.closed (endsAt (replicate (send x w zero))) replicatedSender :=
  answer_proved replicated_sender_serves_answer

theorem two_servers_are_one_answer :
    answer (.is (server x zero)) (par [server x zero, server x zero]) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Two copies of a server are one.** -/
theorem two_servers_are_one : PiSync.sat Env.closed (.is (server x zero)) (par [server x zero, server x zero]) :=
  answer_proved two_servers_are_one_answer

/-- `!x(y).x⟨y⟩.0 | x⟨w⟩.0`. -/
def forwarder : Pattern := par [server x (send x (.bvar 0) zero), send x w zero]

theorem forwarder_diverges_answer : answer forever forwarder 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **The forwarder runs forever**: its step returns to the same canonical process. -/
theorem forwarder_diverges : PiSync.sat Env.closed forever forwarder := answer_proved forwarder_diverges_answer

theorem serving_ends_answer : answer forever serving 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A server with one client does not run forever.** -/
theorem serving_ends : ¬ PiSync.sat Env.closed forever serving := answer_refuted serving_ends_answer

/-- `(νa) !a(y).0 | x⟨w⟩.0`. -/
def privateServer : Pattern := par [restrict (server (.bvar 0) zero), send x w zero]

theorem private_server_stuck_answer : answer steps privateServer 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private server stays private**: the output outside the restriction does not reach it. -/
theorem private_server_stuck : ¬ PiSync.sat Env.closed steps privateServer := answer_refuted private_server_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSyncPrenexControls
