import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSCanonicalForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: CCS through the front door, modulo its laws

`ccsCalc` asked through the front door with its canonical forms (`CCSForms.forms`), which read the language modulo
its bag, its sums and its restriction laws, in the typed reading. Free names are free variables of the name sort (`a`,
`b`), restricted names bound variables.

- **A reaction**: `a.0 | ~a.0` ends at `0` (`reaction_ends`), not at `a.0` (`reaction_not_kept`).
- **A choice resolved**: `(a.0 + b.0) | ~a.0` ends at `0` (`choice_resolved`): the summand `b.0` is discarded, so the
  run does not end at `b.0` (`choice_discards`).
- **A silent step**: `τ.0 + a.0` ends at `0` (`silent_taken`).
- **A private name**: `(νx)(x.0 | ~x.0)` reacts and ends at `0`, the restriction then garbage (`private_reacts`);
  `(νx) x.0 | ~a.0` has no step, the private name being no other (`private_stays_private`).
- **Modulo the laws**: `(a.0 | 0) | ~a.0` ends at `0` (`nested_ends`); without the canonical forms the front door
  leaves it open (`nested_open_without_forms`).
- **Guards**: in `a.(~a.0)` the co-action waits under the action, so there is no step (`guard_holds`).
- **Names**: `a.0 | ~b.0` has no step (`other_name_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.Languages.ProcessCalculi.CCS (ccsCalc nil par sum nu act coact tau)

abbrev CCS := referenceStructure RelationEnv.empty ccsCalc CCSForms.reading

/-- The front door, with CCS's canonical forms at the fuel. -/
def answer (formula : Formula 0) (term : Pattern) (rounds : ℕ) : Answer :=
  ask RelationEnv.empty [] ccsCalc 4 formula term none rounds (some (CCSForms.forms 4))

theorem answer_proved {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .proved evidence) : CCS.sat Env.closed formula term :=
  ask_proved_in (formsFor_formsReading _) answered

theorem answer_refuted {formula : Formula 0} {term : Pattern} {rounds : ℕ} {evidence : Evidence}
    (answered : answer formula term rounds = .refuted evidence) : ¬ CCS.sat Env.closed formula term :=
  ask_refuted_in (formsFor_formsReading _) answered

def steps : Formula 0 := .possibly .any .top

/-- Steps, and every step ends at `result`, which has no step. -/
def endsAt (result : Pattern) : Formula 0 :=
  .and (.possibly .any .top) (.necessarily .any (.and (.is result) (.necessarily .any .bot)))

/-- The free names `a` and `b`. -/
def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"

/-! ## Reactions -/

theorem reaction_ends_answer :
    answer (endsAt nil) (par [sum [act a nil], sum [coact a nil]]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`a.0 | ~a.0` reacts and ends at `0`.** -/
theorem reaction_ends : CCS.sat Env.closed (endsAt nil) (par [sum [act a nil], sum [coact a nil]]) :=
  answer_proved reaction_ends_answer

theorem reaction_not_kept_answer :
    answer (endsAt (sum [act a nil])) (par [sum [act a nil], sum [coact a nil]]) 3 =
      .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **It does not end at `a.0`.** -/
theorem reaction_not_kept :
    ¬ CCS.sat Env.closed (endsAt (sum [act a nil])) (par [sum [act a nil], sum [coact a nil]]) :=
  answer_refuted reaction_not_kept_answer

/-! ## Choice -/

/-- `(a.0 + b.0) | ~a.0`. -/
def choice : Pattern := par [sum [act a nil, act b nil], sum [coact a nil]]

theorem choice_resolved_answer : answer (endsAt nil) choice 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A reaction resolves a choice**: the run ends at `0`. -/
theorem choice_resolved : CCS.sat Env.closed (endsAt nil) choice := answer_proved choice_resolved_answer

theorem choice_discards_answer : answer (endsAt (sum [act b nil])) choice 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **The other summand is discarded**: the run does not end at `b.0`. -/
theorem choice_discards : ¬ CCS.sat Env.closed (endsAt (sum [act b nil])) choice :=
  answer_refuted choice_discards_answer

/-! ## Silent steps -/

theorem silent_taken_answer : answer (endsAt nil) (sum [tau nil, act a nil]) 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A silent summand is taken**: `τ.0 + a.0` ends at `0`. -/
theorem silent_taken : CCS.sat Env.closed (endsAt nil) (sum [tau nil, act a nil]) := answer_proved silent_taken_answer

/-! ## Restriction -/

/-- `(νx)(x.0 | ~x.0)`. -/
def privatePair : Pattern := nu (par [sum [act (.bvar 0) nil], sum [coact (.bvar 0) nil]])

theorem private_reacts_answer : answer (endsAt nil) privatePair 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **A reaction on a private name**, after which the restriction is garbage: the run ends at `0`. -/
theorem private_reacts : CCS.sat Env.closed (endsAt nil) privatePair := answer_proved private_reacts_answer

/-- `(νx) x.0 | ~a.0`. -/
def privateApart : Pattern := par [nu (sum [act (.bvar 0) nil]), sum [coact a nil]]

theorem private_stays_private_answer : answer steps privateApart 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **A private name is no other name**: `(νx) x.0 | ~a.0` has no step. -/
theorem private_stays_private : ¬ CCS.sat Env.closed steps privateApart :=
  answer_refuted private_stays_private_answer

/-! ## Modulo the laws -/

/-- `(a.0 | 0) | ~a.0`. -/
def nested : Pattern := par [par [sum [act a nil], nil], sum [coact a nil]]

theorem nested_ends_answer : answer (endsAt nil) nested 3 = .proved (.canonicalRegion 3) := by
  decide +kernel

/-- **`(a.0 | 0) | ~a.0` ends at `0`**: the nested compositions are one, modulo the laws. -/
theorem nested_ends : CCS.sat Env.closed (endsAt nil) nested := answer_proved nested_ends_answer

/-- **Without the canonical forms the front door leaves it open.** -/
theorem nested_open_without_forms :
    ask RelationEnv.empty [] ccsCalc 4 (endsAt nil) nested none 3 = .unknown 3 := by
  decide +kernel

/-! ## No step -/

theorem guard_holds_answer : answer steps (sum [act a (sum [coact a nil])]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **A guard holds its continuation back**: in `a.(~a.0)` the co-action does not react with the action above it. -/
theorem guard_holds : ¬ CCS.sat Env.closed steps (sum [act a (sum [coact a nil])]) :=
  answer_refuted guard_holds_answer

theorem other_name_stuck_answer :
    answer steps (par [sum [act a nil], sum [coact b nil]]) 3 = .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **A reaction needs one name**: `a.0 | ~b.0` has no step. -/
theorem other_name_stuck : ¬ CCS.sat Env.closed steps (par [sum [act a nil], sum [coact b nil]]) :=
  answer_refuted other_name_stuck_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSControls
