import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: mobile ambients with communication and paths through the front door

`ambientCommCalc` asked through the front door with its canonical forms (`AmbientCommForms.forms`), which read the
language modulo its bag, its restriction and replication laws, the boundary law and the laws of paths, in the typed
reading. Free names are free variables of the name sort (`a`, `b`), and a received name or capability term is the
input's bound variable (`x`).

- **Communication of a name**: `(x).x[0] | ⟨a⟩` ends at `a[0]` (`name_received`), not at `b[0]`
  (`name_received_not_other`). A private name is sent inside its scope: `ν x.(⟨x⟩ | (y).y[0])` ends at `ν x.x[0]`
  (`private_name_sent`). A received name drives a capability: `(x).open x.0 | ⟨a⟩ | a[b[0]]` ends at `b[0]`
  (`received_name_opens`).
- **Communication of a capability term**: `(y).a[y.0] | ⟨in b⟩ | b[0]` ends at `b[a[0]]`, the received capability
  moving the ambient (`capability_received`).
- **Paths**: `a[(in b.out b).0] | b[0]` enters `b` and leaves it again, ending at `a[0] | b[0]` (`path_moves`); the
  empty path is no prefix, `a[ε.0]` is `a[0]` (`empty_path`), and a capability term prefix is the capability,
  `a[(in b).0]` is `a[in b.0]` (`capability_prefix`).
- **No communication without both ends of one channel**: an input alone does not step (`input_alone_stuck`), nor does
  an input of a name beside an output of a capability term (`channels_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCommCalc)

abbrev Ambients := referenceStructure RelationEnv.empty ambientCommCalc AmbientCommForms.reading

/-- The front door, with the canonical forms at the fuel. The fuel bounds the depth at which steps are listed. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] ambientCommCalc 8 formula term none rounds (some (AmbientCommForms.forms 8))

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

def zero : Pattern := .apply "AZero" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def amb (name content : Pattern) : Pattern := .apply "AAmb" [name, content]
def enter (name process : Pattern) : Pattern := .apply "AIn" [name, process]
def dissolve (name process : Pattern) : Pattern := .apply "AOpen" [name, process]
def restrict (body : Pattern) : Pattern := .apply "ANu" [.lambda none body]
def capIn (name : Pattern) : Pattern := .apply "CapIn" [name]
def capOut (name : Pattern) : Pattern := .apply "CapOut" [name]
def eps : Pattern := .apply "CapEps" []
def path (first second : Pattern) : Pattern := .apply "CapPath" [first, second]
def prefixed (capability process : Pattern) : Pattern := .apply "ACap" [capability, process]
def receiveName (body : Pattern) : Pattern := .apply "AInName" [.lambda none body]
def sendName (name : Pattern) : Pattern := .apply "AOutName" [name]
def receiveCap (body : Pattern) : Pattern := .apply "AInCap" [.lambda none body]
def sendCap (capability : Pattern) : Pattern := .apply "AOutCap" [capability]

def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"
/-- The variable an input binds, or a restriction, inside it. -/
def x : Pattern := .bvar 0

/-! ## Communication of a name -/

theorem name_received_answer :
    answer (endsAt (amb a zero)) (par [receiveName (amb x zero), sendName a]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`(x).x[0] | ⟨a⟩` receives `a` and ends at `a[0]`.** -/
theorem name_received : Ambients.sat Env.closed (endsAt (amb a zero)) (par [receiveName (amb x zero), sendName a]) :=
  answer_proved name_received_answer

theorem name_received_not_other_answer :
    answer (endsAt (amb b zero)) (par [receiveName (amb x zero), sendName a]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **It does not end at `b[0]`.** -/
theorem name_received_not_other :
    ¬ Ambients.sat Env.closed (endsAt (amb b zero)) (par [receiveName (amb x zero), sendName a]) :=
  answer_refuted name_received_not_other_answer

theorem private_name_sent_answer :
    answer (finallyAt (restrict (amb x zero))) (restrict (par [sendName x, receiveName (amb x zero)])) 3 =
      .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A private name is sent inside its scope**: `ν x.(⟨x⟩ | (y).y[0])` ends at `ν x.x[0]`. -/
theorem private_name_sent :
    Ambients.sat Env.closed (finallyAt (restrict (amb x zero)))
      (restrict (par [sendName x, receiveName (amb x zero)])) :=
  answer_proved private_name_sent_answer

theorem received_name_opens_answer :
    answer (finallyAt (amb b zero)) (par [receiveName (dissolve x zero), sendName a, amb a (amb b zero)]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A received name drives a capability**: `(x).open x.0 | ⟨a⟩ | a[b[0]]` ends at `b[0]`. -/
theorem received_name_opens :
    Ambients.sat Env.closed (finallyAt (amb b zero))
      (par [receiveName (dissolve x zero), sendName a, amb a (amb b zero)]) :=
  answer_proved received_name_opens_answer

/-! ## Communication of a capability term -/

theorem capability_received_answer :
    answer (finallyAt (amb b (amb a zero)))
        (par [receiveCap (amb a (prefixed x zero)), sendCap (capIn b), amb b zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A received capability moves an ambient**: `(y).a[y.0] | ⟨in b⟩ | b[0]` ends at `b[a[0]]`. -/
theorem capability_received :
    Ambients.sat Env.closed (finallyAt (amb b (amb a zero)))
      (par [receiveCap (amb a (prefixed x zero)), sendCap (capIn b), amb b zero]) :=
  answer_proved capability_received_answer

/-! ## Paths -/

theorem path_moves_answer :
    answer (finallyAt (par [amb a zero, amb b zero]))
        (par [amb a (prefixed (path (capIn b) (capOut b)) zero), amb b zero]) 4 =
      .proved (.canonicalRegion 4) := by
  decide +kernel

/-- **A path moves an ambient step by step**: `a[(in b.out b).0] | b[0]` ends at `a[0] | b[0]`. -/
theorem path_moves :
    Ambients.sat Env.closed (finallyAt (par [amb a zero, amb b zero]))
      (par [amb a (prefixed (path (capIn b) (capOut b)) zero), amb b zero]) :=
  answer_proved path_moves_answer

theorem empty_path_answer : answer (.is (amb a zero)) (amb a (prefixed eps zero)) 2 = .proved (.canonicalRegion 2) := by
  decide +kernel

/-- **The empty path is no prefix**: `a[ε.0]` is `a[0]`. -/
theorem empty_path : Ambients.sat Env.closed (.is (amb a zero)) (amb a (prefixed eps zero)) :=
  answer_proved empty_path_answer

theorem capability_prefix_answer :
    answer (.is (amb a (enter b zero))) (amb a (prefixed (capIn b) zero)) 2 = .proved (.canonicalRegion 2) := by
  decide +kernel

/-- **A capability term prefix is the capability**: `a[(in b).0]` is `a[in b.0]`. -/
theorem capability_prefix : Ambients.sat Env.closed (.is (amb a (enter b zero))) (amb a (prefixed (capIn b) zero)) :=
  answer_proved capability_prefix_answer

/-! ## No communication without both ends of one channel -/

theorem input_alone_stuck_answer : answer steps (receiveName (amb x zero)) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **An input alone does not step.** -/
theorem input_alone_stuck : ¬ Ambients.sat Env.closed steps (receiveName (amb x zero)) :=
  answer_refuted input_alone_stuck_answer

theorem channels_apart_answer :
    answer steps (par [receiveName (amb x zero), sendCap (capIn b)]) 2 = .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **An input of a name and an output of a capability term do not communicate.** -/
theorem channels_apart : ¬ Ambients.sat Env.closed steps (par [receiveName (amb x zero), sendCap (capIn b)]) :=
  answer_refuted channels_apart_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientCommControls
