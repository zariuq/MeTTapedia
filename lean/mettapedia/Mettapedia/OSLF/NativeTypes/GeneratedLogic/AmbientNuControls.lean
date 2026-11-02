import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: mobile ambients with restriction and replication through the front door

`ambientNuCalc` asked through the front door with its canonical forms (`AmbientNuForms.forms`), which read the
language modulo its bag, its restriction laws, its replication laws and the boundary law (a restriction crosses an
ambient it does not name), in the typed reading. Free names are free variables of the name sort (`a`, `b`, `c`, `n`),
restricted names bound variables (`x`).

- **The three moves**: `a[in b.0] | b[0]` ends at `b[a[0]]` (`enter_ends`), not at `a[b[0]]` (`enter_not_reversed`);
  `b[a[out b.0]]` ends at `a[0] | b[0]` (`exit_ends`); `open a.0 | a[0]` ends at `0` (`open_ends`).
- **Moves in sequence**, every run ending at one process: opening an ambient releases one that then enters a sibling
  (`open_then_enter`) or leaves its parent (`open_then_exit`); nested opens, in either order, release the innermost
  ambient (`nested_opens`). The first step does not already end there (`open_then_enter_not_at_once`).
- **A capability guards what follows it**: an ambient under `open b.` moves only after `b` is opened
  (`guarded_waits`), and without `b` it never moves (`guarded_stuck`).
- **Ambients of one name are distinct ambients**: `open a.0` opens one of two `a[0]` and leaves the other
  (`same_name_one_opened`); `a[in a.0] | a[0]` enters the other `a` (`same_name_enters`).
- **Restriction**: a private ambient cannot be entered from outside its scope (`private_stuck`), and can be inside it
  (`private_entered`); a restricted ambient leaves its parent, its restriction crossing the parent's boundary
  (`boundary_exit`); opening releases a restricted ambient (`open_releases_restricted`). A restriction its process does
  not use is garbage (`garbage_restriction`), while a used one keeps its name private (`private_name_kept`).
- Without the canonical forms the front door leaves a run under a restriction open (`restricted_open_without_forms`).
- **Replication**: `!a[0] | open a.0` ends at `!a[0]`, the replicated ambient opened once and staying
  (`replicated_opened_once`); so does `!!a[0] | open a.0`, a replication replicated being the replication
  (`replication_replicated`); and with two replicated ambients, opening one leaves both (`two_servers_one_opened`).
  A replicated ambient copies a molecule, its own restricted location, so the presentations unfold at most three
  copies.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientNuCalc)

abbrev Ambients := referenceStructure RelationEnv.empty ambientNuCalc AmbientNuForms.reading

/-- The front door, with the canonical forms at the fuel. The fuel bounds the depth at which steps are listed. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] ambientNuCalc 8 formula term none rounds (some (AmbientNuForms.forms 8))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : Ambients.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ Ambients.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- Every run ends, at `result`. -/
def finallyAt (result : Pattern) : Formula 0 :=
  .mu (.or (.and (.is result) (.necessarily .any .bot)) (.and (.possibly .any .top) (.necessarily .any (.var 0))))

/-- Some run goes on forever. -/
def forever : Formula 0 := .nu (.and (.possibly .any .top) (.necessarily .any (.var 0)))

def zero : Pattern := .apply "AZero" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def amb (name content : Pattern) : Pattern := .apply "AAmb" [name, content]
def enter (name process : Pattern) : Pattern := .apply "AIn" [name, process]
def leave (name process : Pattern) : Pattern := .apply "AOut" [name, process]
def dissolve (name process : Pattern) : Pattern := .apply "AOpen" [name, process]
def restrict (body : Pattern) : Pattern := .apply "ANu" [.lambda none body]
def replicate (process : Pattern) : Pattern := .apply "ARep" [process]

def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"
def c : Pattern := .fvar "c"
def n : Pattern := .fvar "n"
/-- The name a restriction binds, inside it. -/
def x : Pattern := .bvar 0

/-! ## The three moves -/

theorem enter_ends_answer :
    answer (endsAt (amb b (amb a zero))) (par [amb a (enter b zero), amb b zero]) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`a[in b.0] | b[0]` enters and ends at `b[a[0]]`.** -/
theorem enter_ends : Ambients.sat Env.closed (endsAt (amb b (amb a zero))) (par [amb a (enter b zero), amb b zero]) :=
  answer_proved enter_ends_answer

theorem enter_not_reversed_answer :
    answer (endsAt (amb a (amb b zero))) (par [amb a (enter b zero), amb b zero]) 3 =
      .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **It does not end at `a[b[0]]`.** -/
theorem enter_not_reversed :
    ¬ Ambients.sat Env.closed (endsAt (amb a (amb b zero))) (par [amb a (enter b zero), amb b zero]) :=
  answer_refuted enter_not_reversed_answer

theorem exit_ends_answer :
    answer (endsAt (par [amb a zero, amb b zero])) (amb b (amb a (leave b zero))) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`b[a[out b.0]]` leaves and ends at `a[0] | b[0]`.** -/
theorem exit_ends : Ambients.sat Env.closed (endsAt (par [amb a zero, amb b zero])) (amb b (amb a (leave b zero))) :=
  answer_proved exit_ends_answer

theorem open_ends_answer : answer (endsAt zero) (par [dissolve a zero, amb a zero]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`open a.0 | a[0]` dissolves the ambient and ends at `0`.** -/
theorem open_ends : Ambients.sat Env.closed (endsAt zero) (par [dissolve a zero, amb a zero]) :=
  answer_proved open_ends_answer

/-! ## Moves in sequence -/

theorem open_then_enter_answer :
    answer (finallyAt (amb b (amb c zero))) (par [dissolve a zero, amb a (amb c (enter b zero)), amb b zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Opening releases an ambient that then enters a sibling**: `open a.0 | a[c[in b.0]] | b[0]` ends at `b[c[0]]`;
inside `a`, `c` has no sibling `b`. -/
theorem open_then_enter :
    Ambients.sat Env.closed (finallyAt (amb b (amb c zero)))
      (par [dissolve a zero, amb a (amb c (enter b zero)), amb b zero]) :=
  answer_proved open_then_enter_answer

theorem open_then_enter_not_at_once_answer :
    answer (endsAt (amb b (amb c zero))) (par [dissolve a zero, amb a (amb c (enter b zero)), amb b zero]) 4 =
      .refuted (.canonicalRegion 4) := by
  decide +kernel

/-- **The first step does not already end there.** -/
theorem open_then_enter_not_at_once :
    ¬ Ambients.sat Env.closed (endsAt (amb b (amb c zero)))
      (par [dissolve a zero, amb a (amb c (enter b zero)), amb b zero]) :=
  answer_refuted open_then_enter_not_at_once_answer

theorem open_then_exit_answer :
    answer (finallyAt (par [amb c zero, amb b zero])) (amb b (par [dissolve a zero, amb a (amb c (leave b zero))])) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Opening releases an ambient that then leaves its parent**: `b[open a.0 | a[c[out b.0]]]` ends at
`c[0] | b[0]`; inside `a`, the parent of `c` is not `b`. -/
theorem open_then_exit :
    Ambients.sat Env.closed (finallyAt (par [amb c zero, amb b zero]))
      (amb b (par [dissolve a zero, amb a (amb c (leave b zero))])) :=
  answer_proved open_then_exit_answer

theorem nested_opens_answer :
    answer (finallyAt (amb c zero)) (par [dissolve a zero, amb a (par [dissolve b zero, amb b (amb c zero)])]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **Nested opens, in either order, release the innermost ambient**: `open a.0 | a[open b.0 | b[c[0]]]` ends at
`c[0]`. -/
theorem nested_opens :
    Ambients.sat Env.closed (finallyAt (amb c zero))
      (par [dissolve a zero, amb a (par [dissolve b zero, amb b (amb c zero)])]) :=
  answer_proved nested_opens_answer

/-! ## A capability guards what follows it -/

theorem guarded_waits_answer :
    answer (finallyAt (amb c (amb a zero))) (par [dissolve b (amb a (enter c zero)), amb b zero, amb c zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **`open b.a[in c.0] | b[0] | c[0]` ends at `c[a[0]]`**: `a` moves once `b` is opened. -/
theorem guarded_waits :
    Ambients.sat Env.closed (finallyAt (amb c (amb a zero)))
      (par [dissolve b (amb a (enter c zero)), amb b zero, amb c zero]) :=
  answer_proved guarded_waits_answer

theorem guarded_stuck_answer :
    answer steps (par [dissolve b (amb a (enter c zero)), amb c zero]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **`open b.a[in c.0] | c[0]` has no step**: the ambient under the capability never moves. -/
theorem guarded_stuck : ¬ Ambients.sat Env.closed steps (par [dissolve b (amb a (enter c zero)), amb c zero]) :=
  answer_refuted guarded_stuck_answer

/-! ## Ambients of one name -/

theorem same_name_one_opened_answer :
    answer (endsAt (amb a zero)) (par [amb a zero, amb a zero, dissolve a zero]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`a[0] | a[0] | open a.0` opens one `a` and ends at the other.** -/
theorem same_name_one_opened :
    Ambients.sat Env.closed (endsAt (amb a zero)) (par [amb a zero, amb a zero, dissolve a zero]) :=
  answer_proved same_name_one_opened_answer

theorem same_name_enters_answer :
    answer (endsAt (amb a (amb a zero))) (par [amb a (enter a zero), amb a zero]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`a[in a.0] | a[0]` enters the other `a`** and ends at `a[a[0]]`. -/
theorem same_name_enters :
    Ambients.sat Env.closed (endsAt (amb a (amb a zero))) (par [amb a (enter a zero), amb a zero]) :=
  answer_proved same_name_enters_answer

/-! ## Restriction -/

theorem private_stuck_answer :
    answer steps (par [restrict (amb x zero), amb a (enter n zero)]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **A private ambient cannot be entered from outside its scope**: `(νx) x[0] | a[in n.0]` has no step. -/
theorem private_stuck : ¬ Ambients.sat Env.closed steps (par [restrict (amb x zero), amb a (enter n zero)]) :=
  answer_refuted private_stuck_answer

theorem private_entered_answer :
    answer (endsAt (restrict (amb x (amb a zero)))) (restrict (par [amb x zero, amb a (enter x zero)])) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **Inside its scope it can**: `(νx)(x[0] | a[in x.0])` ends at `(νx) x[a[0]]`. -/
theorem private_entered :
    Ambients.sat Env.closed (endsAt (restrict (amb x (amb a zero)))) (restrict (par [amb x zero, amb a (enter x zero)])) :=
  answer_proved private_entered_answer

theorem boundary_exit_answer :
    answer (endsAt (par [restrict (amb x zero), amb b zero])) (amb b (restrict (amb x (leave b zero)))) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A restricted ambient leaves its parent**: `b[(νx) x[out b.0]]` ends at `(νx) x[0] | b[0]`, the restriction
crossing `b`'s boundary. -/
theorem boundary_exit :
    Ambients.sat Env.closed (endsAt (par [restrict (amb x zero), amb b zero])) (amb b (restrict (amb x (leave b zero)))) :=
  answer_proved boundary_exit_answer

theorem open_releases_restricted_answer :
    answer (endsAt (restrict (amb x zero))) (par [dissolve a zero, amb a (restrict (amb x zero))]) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **Opening releases a restricted ambient**: `open a.0 | a[(νx) x[0]]` ends at `(νx) x[0]`. -/
theorem open_releases_restricted :
    Ambients.sat Env.closed (endsAt (restrict (amb x zero))) (par [dissolve a zero, amb a (restrict (amb x zero))]) :=
  answer_proved open_releases_restricted_answer

theorem garbage_restriction_answer : answer (.is (amb a zero)) (restrict (amb a zero)) 1 = .proved (.canonicalRegion 1) := by
  decide +kernel

/-- **A restriction its process does not use is garbage**: `(νx) a[0]` is `a[0]`. -/
theorem garbage_restriction : Ambients.sat Env.closed (.is (amb a zero)) (restrict (amb a zero)) :=
  answer_proved garbage_restriction_answer

theorem private_name_kept_answer :
    answer (.is (amb a zero)) (restrict (amb x zero)) 1 = .refuted (.canonicalRegion 1) := by
  decide +kernel

/-- **A used restriction keeps its name private**: `(νx) x[0]` is not `a[0]`. -/
theorem private_name_kept : ¬ Ambients.sat Env.closed (.is (amb a zero)) (restrict (amb x zero)) :=
  answer_refuted private_name_kept_answer

/-! ## Without the canonical forms -/

/-- **Without the canonical forms the front door leaves a run under a restriction open.** -/
theorem restricted_open_without_forms :
    ask RelationEnv.empty [] ambientNuCalc 8 (endsAt (restrict (amb x (amb a zero))))
      (restrict (par [amb x zero, amb a (enter x zero)])) none 3 = .unknown 3 := by
  decide +kernel

/-! ## Replication -/

theorem replicated_opened_once_answer :
    answer (endsAt (replicate (amb a zero))) (par [replicate (amb a zero), dissolve a zero]) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`!a[0] | open a.0` ends at `!a[0]`**: the replicated ambient is opened once and stays. -/
theorem replicated_opened_once :
    Ambients.sat Env.closed (endsAt (replicate (amb a zero))) (par [replicate (amb a zero), dissolve a zero]) :=
  answer_proved replicated_opened_once_answer

theorem replication_replicated_answer :
    answer (endsAt (replicate (amb a zero))) (par [replicate (replicate (amb a zero)), dissolve a zero]) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`!!a[0] | open a.0` ends at `!a[0]`**: a replication replicated is the replication. -/
theorem replication_replicated :
    Ambients.sat Env.closed (endsAt (replicate (amb a zero)))
      (par [replicate (replicate (amb a zero)), dissolve a zero]) :=
  answer_proved replication_replicated_answer

theorem two_servers_one_opened_answer :
    answer (endsAt (par [replicate (amb a zero), replicate (amb b zero)]))
      (par [replicate (amb a zero), replicate (amb b zero), dissolve b zero]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`!a[0] | !b[0] | open b.0` ends at `!a[0] | !b[0]`**: with two replicated ambients, opening one leaves both. -/
theorem two_servers_one_opened :
    Ambients.sat Env.closed (endsAt (par [replicate (amb a zero), replicate (amb b zero)]))
      (par [replicate (amb a zero), replicate (amb b zero), dissolve b zero]) :=
  answer_proved two_servers_one_opened_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
