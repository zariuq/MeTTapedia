import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels

/-!
# Controls: two-level context labels of mobile ambients at the front door

The modal decider of mobile ambients (`AmbientContextLabels.decider`) answers context-labelled modalities, each
context one of the four two-level families. Each family enables a step that the inert process lacks:

- **parallel**: `open a.0` beside `a[0]` steps (`open_beside`), `0` does not (`zero_beside`);
- **parent**: the private ambient `(νx) x[out b.0]` inside `b[□ | 0]` leaves it (`private_exits`), while `(νx) x[0]`
  does not step (`private_stays`); beside `b[0]` neither steps (`private_beside_stuck`);
- **sibling**: `in b.0` inside `a[□ | 0]`, beside `b[0]`, moves `a` into `b` (`enter_beside`), `0` does not
  (`zero_sibling`); beside `b[0]` alone `in b.0` has no step (`enter_alone_stuck`);
- **grandparent**: `out b.0` inside `a[□ | 0]` inside `b[… | 0]` moves `a` out (`exit_inside`), `0` does not
  (`zero_grandparent`).

**Two steps see further** (`exit_in_two_steps`, `zero_in_two_steps`): in the sibling context `a[□ | in b.0] | b[0]`,
`out b.0` first enters `b` with `a` and then leaves it, while `0` only enters. So the four families are a complete
finite family of contexts in which redexes are immediate, but a context enabling a step only after another step
separates processes too: the grandparent family is not needed to tell `out b.0` from `0` by saturated bisimilarity.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextLabels

def zero : Pattern := .apply "AZero" []
def par (items : List Pattern) : Pattern := .collection .hashBag items none
def amb (name content : Pattern) : Pattern := .apply "AAmb" [name, content]
def enter (name process : Pattern) : Pattern := .apply "AIn" [name, process]
def leave (name process : Pattern) : Pattern := .apply "AOut" [name, process]
def dissolve (name process : Pattern) : Pattern := .apply "AOpen" [name, process]
def restrict (body : Pattern) : Pattern := .apply "ANu" [.lambda none body]
def a : Pattern := .fvar "a"
def b : Pattern := .fvar "b"
/-- The restricted name, inside its restriction. -/
def x : Pattern := .bvar 0

/-- Some step in the context. -/
def stepsIn (context : AmbientContext) : Formula 0 := .possibly (contextLabel "h" context) .top

/-- Some step in the context, then another. -/
def twoStepsIn (context : AmbientContext) : Formula 0 :=
  .possibly (contextLabel "h" context) (.possibly .any .top)

/-! ## Parallel -/

theorem open_beside : frontDoor.sat Env.closed (stepsIn (.par (amb a zero))) (dissolve a zero) :=
  decided_holds (by decide +kernel)

theorem zero_beside : ¬ frontDoor.sat Env.closed (stepsIn (.par (amb a zero))) zero :=
  decided_fails (by decide +kernel)

/-! ## Parent -/

theorem private_exits :
    frontDoor.sat Env.closed (stepsIn (.parent "b" zero)) (restrict (amb x (par [leave b zero]))) :=
  decided_holds (by decide +kernel)

theorem private_stays : ¬ frontDoor.sat Env.closed (stepsIn (.parent "b" zero)) (restrict (amb x (par [zero]))) :=
  decided_fails (by decide +kernel)

theorem private_beside_stuck :
    ¬ frontDoor.sat Env.closed (stepsIn (.par (amb b zero))) (restrict (amb x (par [leave b zero]))) :=
  decided_fails (by decide +kernel)

/-! ## Sibling -/

theorem enter_beside : frontDoor.sat Env.closed (stepsIn (.sibling "a" zero "b" zero)) (enter b zero) :=
  decided_holds (by decide +kernel)

theorem zero_sibling : ¬ frontDoor.sat Env.closed (stepsIn (.sibling "a" zero "b" zero)) zero :=
  decided_fails (by decide +kernel)

theorem enter_alone_stuck : ¬ frontDoor.sat Env.closed (stepsIn (.par (amb b zero))) (enter b zero) :=
  decided_fails (by decide +kernel)

/-! ## Grandparent -/

theorem exit_inside : frontDoor.sat Env.closed (stepsIn (.grandparent "b" zero "a" zero)) (leave b zero) :=
  decided_holds (by decide +kernel)

theorem zero_grandparent : ¬ frontDoor.sat Env.closed (stepsIn (.grandparent "b" zero "a" zero)) zero :=
  decided_fails (by decide +kernel)

/-! ## Two steps see further -/

theorem exit_in_two_steps :
    frontDoor.sat Env.closed (twoStepsIn (.sibling "a" (enter b zero) "b" zero)) (leave b zero) :=
  decided_holds (by decide +kernel)

theorem zero_in_two_steps :
    ¬ frontDoor.sat Env.closed (twoStepsIn (.sibling "a" (enter b zero) "b" zero)) zero :=
  decided_fails (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls
