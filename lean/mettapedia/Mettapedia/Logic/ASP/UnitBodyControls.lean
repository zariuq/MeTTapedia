import Mettapedia.Logic.ASP.Driver
import Mettapedia.Logic.ASP.WeightCertificate

/-!
# Controls for unit bodies

Values are computed by the kernel (`decide +kernel`).

## The literal of a body

A body with exactly one literal is a unit body, and its literal stands for it: `a` is `T a` and
`not b` is `F b`, with complements `F a` and `T b` (`unit_lits`). The empty body, `a, a` (two
literals, one atom) and `a, not b` are not unit bodies and keep their variables (`nonunit_lits`); the
rule `c :- a, a` has the body variable `(a, a)` (`twice_varList`).

## Choice, a rule with one positive atom, a constraint

`a :- not b. b :- not a. c :- a. :- c.` (`unitP`; the constraint reads as `f :- c, not f` with the
falsum atom `f`) has only unit bodies besides the constraint's, so its variables are its four atoms
(`unitP_varList`). Its completion (`unitP_inputs`) is one clause per rule, `b ∨ a` for `a :- not b`,
`not a ∨ c` for `c :- a` and the unit `not c` of the constraint, then the support clauses in atom
order, `not c ∨ a` for `c` among them. Its stable model is `{b}` (`unitP_stable`).

* With the constraint `:- b.` added (`unitNo`) there is no stable model: `not a` from `not c` and
  `not a ∨ c`, then the empty clause from `not a`, `not b` and `b ∨ a` (`unitNo_certificate`,
  `unitNo_no_stable`), also for the checker with definitions (`unitNo_certificate_noDefs`). The
  driver refutes it with an accepted certificate of its own (`unitNo_driver`).
* Without its last step the certificate is refused (`unitNo_truncated_refused`), and so is the
  certificate for `unitP`, which has a stable model (`unitP_refused`).

## A loop through a unit body

`a :- b. b :- a. a :- not c.` (`loopU`) is not tight: `a` and `b` support each other. The loop nogood
of `{a, b}` for `a` is `{T a, T c}`: the external rule `a :- not c` contributes the complement `T c`
of the literal `F c` of its unit body (`loopU_loopNogood`). Its loop step is accepted
(`loopU_loop_step`); the step stating `not a` alone, leaving the external body out, is refused
(`loopU_short_loop_refused`), and that clause is false in the stable model `{a, b}`
(`loopU_short_loop_unsound`).

With the fact `c.` and the constraint `:- not a.` added (`loopUc`), the completion has the model
`{a, b, c}` (`loopUc_supported`), but the program has no stable model: the loop step of `{a, b}` and
one RUP step refute it (`loopUc_certificate`, `loopUc_no_stable`). The fact's empty body is no unit
body and keeps its variable, whose body nogood is the unit clause of that variable
(`loopUc_varList`). Without the loop step the certificate is refused (`loopUc_needs_loop`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.UnitBodyControls

open Program Mettapedia.GSLT.Logic PropositionalFormula

/-- The atoms of the small programs. -/
inductive Atom
  | a
  | b
  | c
  | f
  deriving DecidableEq, Repr

open Atom

/-! ## The literal of a body -/

theorem unit_lits :
    (⟨[a], []⟩ : Body Atom).IsUnit ∧ (⟨[a], []⟩ : Body Atom).lit = tAtom a ∧
      (⟨[a], []⟩ : Body Atom).lit.compl = fAtom a ∧
      (⟨[], [b]⟩ : Body Atom).IsUnit ∧ (⟨[], [b]⟩ : Body Atom).lit = fAtom b ∧
      (⟨[], [b]⟩ : Body Atom).lit.compl = tAtom b := by
  decide +kernel

theorem nonunit_lits :
    ¬ (⟨[], []⟩ : Body Atom).IsUnit ∧ (⟨[], []⟩ : Body Atom).lit = tBody ⟨[], []⟩ ∧
      ¬ (⟨[a, a], []⟩ : Body Atom).IsUnit ∧ (⟨[a, a], []⟩ : Body Atom).lit = tBody ⟨[a, a], []⟩ ∧
      ¬ (⟨[a], [b]⟩ : Body Atom).IsUnit ∧ (⟨[a], [b]⟩ : Body Atom).lit = tBody ⟨[a], [b]⟩ := by
  decide +kernel

/-- `c :- a, a.` -/
theorem twice_varList : Program.varList [(⟨c, [a, a], []⟩ : Rule Atom)] = [.atom c, .atom a, .body ⟨[a, a], []⟩] := by
  decide +kernel

/-! ## Choice, a rule with one positive atom, a constraint -/

/-- `a :- not b. b :- not a. c :- a. :- c.` -/
def unitP : Program Atom := [⟨a, [], [b]⟩, ⟨b, [], [a]⟩, ⟨c, [a], []⟩, ⟨f, [c], [f]⟩]

theorem unitP_falsum : unitP.falsum f = true ∧ unitP.falsum c = false := by decide +kernel

theorem unitP_varList : unitP.varList = [.atom b, .atom a, .atom c, .atom f] := by decide +kernel

/-- The nogoods of the rules: `{F b, F a}`, `{F a, F b}`, `{T a, F c}`, and the constraint's `{T c}`. -/
theorem unitP_ruleNogoods :
    (unitP.flatMap unitP.ruleNogoods).map Nogood.lits =
      [[fAtom b, fAtom a], [fAtom a, fAtom b], [tAtom a, fAtom c], [tAtom c]] := by
  decide +kernel

/-- The support nogoods in atom order: `{T b, T a}`, `{T a, T b}`, `{T c, F a}`, `{T f}`. -/
theorem unitP_supportNogoods :
    (unitP.allAtoms.map unitP.supportNogood).map Nogood.lits =
      [[tAtom b, tAtom a], [tAtom a, tAtom b], [tAtom c, fAtom a], [tAtom f]] := by
  decide +kernel

theorem unitP_inputs : unitP.inputs =
    [(1, [.pos 0, .pos 1]), (2, [.pos 1, .pos 0]), (3, [.neg 1, .pos 2]), (4, [.neg 2]),
     (5, [.neg 0, .neg 1]), (6, [.neg 1, .neg 0]), (7, [.neg 2, .pos 1]), (8, [.neg 3])] := by
  decide +kernel

theorem unitP_stable : unitP.Stable ↑({b} : Finset Atom) := (unitP.isStable_iff _).mp (by decide +kernel)

/-- With `:- b.` -/
def unitNo : Program Atom := unitP ++ [⟨f, [b], [f]⟩]

theorem unitNo_inputs : unitNo.inputs =
    [(1, [.pos 2, .pos 0]), (2, [.pos 0, .pos 2]), (3, [.neg 0, .pos 1]), (4, [.neg 1]), (5, [.neg 2]),
     (6, [.neg 0, .neg 2]), (7, [.neg 1, .pos 0]), (8, [.neg 2, .neg 0]), (9, [.neg 3])] := by
  decide +kernel

/-- `not a` from `not c` and `not a ∨ c`; then the empty clause from `not a`, `not b` and `b ∨ a`. -/
def unitNoCertificate : List CertStep := [.lrat (.rup 10 [.neg 0] [4, 3]), .lrat (.rup 11 [] [10, 5, 1])]

theorem unitNo_certificate : unitNo.checkCert unitNoCertificate = true := by decide +kernel

theorem unitNo_no_stable (S : Set Atom) : ¬ unitNo.Stable S := unitNo.checkCert_sound unitNo_certificate S

theorem unitNo_certificate_noDefs :
    (⟨unitNo, []⟩ : DefProgram Atom).checkCert (unitNoCertificate.map CertStep.toW) = true := by
  rw [DefProgram.checkCert_noDefs]
  exact unitNo_certificate

theorem unitNo_truncated_refused : unitNo.checkCert (unitNoCertificate.take 1) = false := by decide +kernel

theorem unitNo_driver : unitNo.solve.model? = none ∧ unitNo.solve.certificate?.map unitNo.checkCert = some true := by
  decide +kernel

/-- No certificate is accepted for `unitP`, which has a stable model. -/
theorem unitP_refused (steps : List CertStep) : unitP.checkCert steps = false := by
  cases accepted : unitP.checkCert steps with
  | false => rfl
  | true => exact absurd unitP_stable (unitP.checkCert_sound accepted _)

/-! ## A loop through a unit body -/

/-- `a :- b. b :- a. a :- not c.` -/
def loopU : Program Atom := [⟨a, [b], []⟩, ⟨b, [a], []⟩, ⟨a, [], [c]⟩]

theorem loopU_not_tight : loopU.PosDep b a ∧ loopU.PosDep a b :=
  ⟨⟨⟨a, [b], []⟩, List.mem_cons_self, rfl, List.mem_cons_self⟩,
    ⟨⟨b, [a], []⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl, List.mem_cons_self⟩⟩

theorem loopU_varList : loopU.varList = [.atom b, .atom a, .atom c] := by decide +kernel

theorem loopU_stable : loopU.Stable ↑({a, b} : Finset Atom) := (loopU.isStable_iff _).mp (by decide +kernel)

theorem loopU_loopNogood : (loopU.loopNogood {a, b} a).lits = [tAtom a, tAtom c] := by decide +kernel

/-- The loop step of `{a, b}` for `a`, with the clause `not a ∨ not c`. -/
theorem loopU_loop_step : (loopU.certStep loopU.inputs (.loop 7 [.neg 1, .neg 2] [1, 0] 1)).isSome = true := by
  decide +kernel

/-- Stating `not a` alone is refused. -/
theorem loopU_short_loop_refused : loopU.certStep loopU.inputs (.loop 7 [.neg 1] [1, 0] 1) = none := by
  decide +kernel

/-- `not a` is false in the stable model `{a, b}`. -/
theorem loopU_short_loop_unsound :
    Clause.sat (loopU.encode (canonical ↑({a, b} : Finset Atom))) [.neg 1] = false := by
  rw [← finValuation_eq_canonical]
  decide +kernel

/-- With `c.` and `:- not a.` -/
def loopUc : Program Atom := loopU ++ [⟨c, [], []⟩, ⟨f, [], [a, f]⟩]

theorem loopUc_varList : loopUc.varList = [.atom b, .atom c, .atom a, .atom f, .body ⟨[], []⟩] ∧
    loopUc.inputs[4]? = some (5, [.pos 4]) := by
  decide +kernel

theorem loopUc_supported : ({b, a, c} : Finset Atom) ∈ loopUc.supportedModels := by decide +kernel

/-- The loop clause `not a ∨ not c` of `{a, b}` for `a`, then the empty clause from the fact's
empty body (clause 5), the fact (clause 4), the constraint's unit `a` (clause 6) and the loop
clause. -/
def loopUcCertificate : List CertStep := [.loop 11 [.neg 2, .neg 1] [2, 0] 2, .lrat (.rup 12 [] [5, 4, 6, 11])]

theorem loopUc_certificate : loopUc.checkCert loopUcCertificate = true := by decide +kernel

theorem loopUc_no_stable (S : Set Atom) : ¬ loopUc.Stable S := loopUc.checkCert_sound loopUc_certificate S

theorem loopUc_needs_loop : loopUc.checkCert loopUcCertificate.tail = false := by decide +kernel

theorem loopUc_driver : loopUc.solve.model? = none ∧ loopUc.solve.certificate?.map loopUc.checkCert = some true := by
  decide +kernel

end Mettapedia.Logic.ASP.UnitBodyControls
