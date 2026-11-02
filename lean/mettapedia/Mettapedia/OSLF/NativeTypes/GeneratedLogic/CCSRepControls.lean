import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls

/-!
# Controls: CCS with replication through the front door

`ccsRepCalc` asked through the front door with its canonical forms (`CCSRepForms.forms`), which read the language
modulo its bag, the multisets of its sums, its restriction laws, the empty sum and its laws of replication, in the
typed reading. Free names are free variables of the name sort (`a`, `b`), restricted names bound variables. A sum of
guards is written `[g + …]`, and `!P` replicates `P`.

- **A replicated action serves once and stays**: `![a.0] | [~a.0]` ends at `![a.0]` (`server_serves_once`), and so
  does a replicated choice, its other summand discarded in the copy (`replicated_choice_serves_once`).
- **Replicated partners run forever**: `![a.0] | ![~a.0]` returns to itself after every step (`partners_diverge`), and
  so does `!{[a.0] | [~a.0]}`, a replicated pair (`replicated_pair_diverges`); a replicated silent prefix runs forever
  (`replicated_silent_diverges`).
- **Different names do not react** (negative): `![a.0] | [~b.0]` has no step (`names_apart`).
- **A private replicated action stays private** (negative): `(νx) ![x.0] | [~a.0]` has no step (`private_stuck`).
- Without the canonical forms the front door leaves the server open: the unfolding is a law, not a rule
  (`server_open_without_forms`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.CCS (nil par sum nu act coact tau)
open Mettapedia.Languages.ProcessCalculi.CCS.Replicated (ccsRepCalc)
open CCSControls (steps endsAt a b)
open PiControls (forever)

abbrev CCSRep := referenceStructure RelationEnv.empty ccsRepCalc CCSRepForms.reading

/-- The front door, with the canonical forms of CCS with replication at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] ccsRepCalc 3 formula term none rounds (some (CCSRepForms.forms 3))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : CCSRep.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ CCSRep.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

/-- Replication of a process. -/
def replicate (process : Pattern) : Pattern := .apply "CRep" [process]

/-! ## A replicated action serves once and stays -/

/-- `![a.0] | [~a.0]`. -/
def server : Pattern := par [replicate (sum [act a nil]), sum [coact a nil]]

theorem server_serves_once_answer :
    answer (endsAt (replicate (sum [act a nil]))) server 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`![a.0] | [~a.0]` ends at `![a.0]`.** -/
theorem server_serves_once : CCSRep.sat Env.closed (endsAt (replicate (sum [act a nil]))) server :=
  answer_proved server_serves_once_answer

/-- `![a.0 + b.0] | [~a.0]`. -/
def choiceServer : Pattern := par [replicate (sum [act a nil, act b nil]), sum [coact a nil]]

theorem replicated_choice_serves_once_answer :
    answer (endsAt (replicate (sum [act a nil, act b nil]))) choiceServer 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`![a.0 + b.0] | [~a.0]` ends at `![a.0 + b.0]`**: the copy's other summand is discarded. -/
theorem replicated_choice_serves_once :
    CCSRep.sat Env.closed (endsAt (replicate (sum [act a nil, act b nil]))) choiceServer :=
  answer_proved replicated_choice_serves_once_answer

/-! ## Replicated partners run forever -/

/-- `![a.0] | ![~a.0]`. -/
def partners : Pattern := par [replicate (sum [act a nil]), replicate (sum [coact a nil])]

theorem partners_diverge_answer : answer forever partners 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`![a.0] | ![~a.0]` runs forever**, every step returning to the same canonical process. -/
theorem partners_diverge : CCSRep.sat Env.closed forever partners := answer_proved partners_diverge_answer

/-- `!{[a.0] | [~a.0]}`. -/
def replicatedPair : Pattern := replicate (par [sum [act a nil], sum [coact a nil]])

theorem replicated_pair_diverges_answer : answer forever replicatedPair 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A replicated pair runs forever**: `!{[a.0] | [~a.0]}` is `![a.0] | ![~a.0]`. -/
theorem replicated_pair_diverges : CCSRep.sat Env.closed forever replicatedPair :=
  answer_proved replicated_pair_diverges_answer

theorem replicated_silent_diverges_answer :
    answer forever (replicate (sum [tau nil])) 4 = .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A replicated silent prefix runs forever**: `![τ.0]`. -/
theorem replicated_silent_diverges : CCSRep.sat Env.closed forever (replicate (sum [tau nil])) :=
  answer_proved replicated_silent_diverges_answer

/-! ## No step -/

theorem names_apart_answer :
    answer steps (par [replicate (sum [act a nil]), sum [coact b nil]]) 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **Different names do not react**: `![a.0] | [~b.0]` has no step. -/
theorem names_apart : ¬ CCSRep.sat Env.closed steps (par [replicate (sum [act a nil]), sum [coact b nil]]) :=
  answer_refuted names_apart_answer

/-- `(νx) ![x.0] | [~a.0]`. -/
def privateServer : Pattern := par [nu (replicate (sum [act (.bvar 0) nil])), sum [coact a nil]]

theorem private_stuck_answer : answer steps privateServer 4 = .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **A private replicated action stays private**: `(νx) ![x.0] | [~a.0]` has no step. -/
theorem private_stuck : ¬ CCSRep.sat Env.closed steps privateServer := answer_refuted private_stuck_answer

/-! ## Without the canonical forms -/

/-- **Without the canonical forms the front door leaves the server open**: the unfolding is a law, not a rule. -/
theorem server_open_without_forms :
    ask RelationEnv.empty [] ccsRepCalc 3 (endsAt (replicate (sum [act a nil]))) server none 4 = .unknown 4 := by
  decide +kernel

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepControls
