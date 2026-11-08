import Mettapedia.Logic.ASP.WeightCertificate

/-!
# Controls for the falsum-reduced completion

Values are computed by the kernel (`decide +kernel`).

## Two integrity constraints with one head

`a :- not b. b :- not a. :- a, not c. :- b.` reads as the rules `f :- a, not c, not f` and
`f :- b, not f` for the constraints, both of the falsum atom `f` (`twoF`, `twoF_falsum`); `c` heads no
rule and is no falsum atom. The numbering has the four atoms and no body: the bodies of the choice
rules are unit bodies (`twoF_varList`). The completion (`twoF_inputs`) has one clause per choice
rule, `b ∨ a` for `a :- not b`, the clause `not a ∨ c` of the first constraint (its positive atom,
then its negated atom other than `f`), the unit `not b` of the second, and the support clauses in
atom order, `not a ∨ not b` for `a`, then `not c` and `not f` among them.

* Two RUP steps refute it (`twoF_certificate`, `twoF_no_stable`): `not a` from `not c` and the first
  constraint, then the empty clause from `not a`, `not b` and the choice of `a`. Without its last
  step the certificate is refused (`twoF_truncated_refused`).
* Without the second constraint the program has the stable model `{b}` (`oneF_stable`), so no
  certificate is accepted for it (`oneF_certificates_refused`).
* A loop step over a set holding `f` is refused (`twoF_loop_falsum_refused`), even with the clause
  `not f`, which holds in every stable model; the loop step over `{a}` is accepted with the clause
  `not a ∨ not b` (`twoF_loop_step`), and refused with a clause over a body variable
  (`twoF_loop_body_refused`).

## A Hall step over one shared head

Three pigeons in two holes with every at-least-one and exclusion rule of one falsum atom
(`pigF`): one Hall step from the three pigeons against the two holes refutes it
(`pigF_certificate`, `pigF_no_stable`). With the fact `f.` added, `f` is no falsum atom
(`pigFact_falsum`), the program has a stable model (`pigFact_stable`), and the same Hall step is
refused (`pigFact_hall_refused`).

## Constraint rules

Constraint rules may share a head (`twoF_constraintRules`); a rule for the head without its
negation makes none of the head's rules a constraint rule. `f :- not f` beside `f :- a` and `a.`
is no constraint rule (`unnegated_not_constraint`), and indeed `{a, f}` is a stable model
(`unnegated_stable`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.FalsumControls

open DefProgram Mettapedia.GSLT.Logic PropositionalFormula

/-- The atoms of the small program. -/
inductive Atom
  | a
  | b
  | c
  | f
  deriving DecidableEq, Repr

open Atom

/-! ## Two integrity constraints with one head -/

/-- `a :- not b. b :- not a. :- a, not c. :- b.` -/
def twoF : DefProgram Atom :=
  ⟨[⟨a, [], [b]⟩, ⟨b, [], [a]⟩, ⟨f, [a], [c, f]⟩, ⟨f, [b], [f]⟩], []⟩

theorem twoF_falsum :
    twoF.rules.falsum f = true ∧ twoF.rules.falsum a = false ∧ twoF.rules.falsum c = false := by
  decide +kernel

theorem twoF_varList : twoF.varList = [.atom a, .atom c, .atom b, .atom f] := by
  decide +kernel

theorem twoF_inputs : twoF.inputs =
    [(1, [.pos 2, .pos 0]), (2, [.pos 0, .pos 2]),
     (3, [.neg 0, .pos 1]), (4, [.neg 2]),
     (5, [.neg 0, .neg 2]), (6, [.neg 1]), (7, [.neg 2, .neg 0]), (8, [.neg 3])] := by
  decide +kernel

/-- `not a` from `not c` and `not a ∨ c`; then the empty clause from `not a`, `not b` and `b ∨ a`. -/
def twoFCertificate : List WCertStep :=
  [.lrat (.rup 9 [.neg 0] [6, 3]), .lrat (.rup 10 [] [9, 4, 1])]

theorem twoF_certificate : twoF.checkCert twoFCertificate = true := by decide +kernel

theorem twoF_no_stable (S : Set Atom) : ¬ twoF.Stable S := twoF.checkCert_sound twoF_certificate S

theorem twoF_truncated_refused : twoF.checkCert (twoFCertificate.take 1) = false := by decide +kernel

/-- Without the second constraint. -/
def oneF : DefProgram Atom := ⟨[⟨a, [], [b]⟩, ⟨b, [], [a]⟩, ⟨f, [a], [c, f]⟩], []⟩

theorem oneF_stable : oneF.Stable ↑({b} : Finset Atom) := (oneF.isStable_iff _).mp (by decide +kernel)

theorem oneF_certificates_refused (steps : List WCertStep) : oneF.checkCert steps = false := by
  cases accepted : oneF.checkCert steps with
  | false => rfl
  | true => exact absurd oneF_stable (oneF.checkCert_sound accepted _)

/-- The loop step `not f` over `{f}`, for `f`. -/
theorem twoF_loop_falsum_refused : twoF.certStep twoF.inputs (.loop 9 [.neg 3] [3] 3) = none := by
  decide +kernel

/-- The loop step `not a ∨ not b` over `{a}`, for `a`: the unit body `not b` of its external rule stands
as its literal `F b`, whose complement `T b` is the loop nogood's. -/
theorem twoF_loop_step : (twoF.certStep twoF.inputs (.loop 9 [.neg 0, .neg 2] [0] 0)).isSome = true := by
  decide +kernel

/-- The loop step with the clause `not a ∨ B` over a fifth variable `B`, as if the body `not b` had a
variable, is refused. -/
theorem twoF_loop_body_refused : twoF.certStep twoF.inputs (.loop 9 [.neg 0, .pos 4] [0] 0) = none := by
  decide +kernel

/-! ## A Hall step over one shared head -/

/-- Three pigeons in two holes over the placements `0, …, 5` (pigeon `p` in hole `h` is `2p + h`),
each chosen against `6 + x`, with the at-least-one and exclusion rules all of the atom `12`. -/
def pigFRules : Program ℕ :=
  [⟨12, [], [0, 1, 12]⟩, ⟨12, [], [2, 3, 12]⟩, ⟨12, [], [4, 5, 12]⟩,
   ⟨12, [0, 2], [12]⟩, ⟨12, [0, 4], [12]⟩, ⟨12, [2, 4], [12]⟩,
   ⟨12, [1, 3], [12]⟩, ⟨12, [1, 5], [12]⟩, ⟨12, [3, 5], [12]⟩] ++
  (List.range 6).flatMap fun x => [⟨x, [], [6 + x]⟩, ⟨6 + x, [], [x]⟩]

def pigF : DefProgram ℕ := ⟨pigFRules, []⟩

/-- The holes as cliques, in the variable numbers of `Q`. -/
def holes (Q : DefProgram ℕ) : List (List ℕ) :=
  [[0, 2, 4].map fun x => Q.index (.atom x), [1, 3, 5].map fun x => Q.index (.atom x)]

theorem pigF_certificate : pigF.checkCert [.hall 1000 [] [0, 1, 2] (holes pigF)] = true := by
  decide +kernel

theorem pigF_no_stable (S : Set ℕ) : ¬ pigF.Stable S := pigF.checkCert_sound pigF_certificate S

/-- With the fact `f.` -/
def pigFact : DefProgram ℕ := ⟨pigFRules ++ [⟨12, [], []⟩], []⟩

theorem pigFact_falsum : pigF.rules.falsum 12 = true ∧ pigFact.rules.falsum 12 = false := by
  decide +kernel

/-- `f`, pigeon `0` in hole `0` and pigeon `1` in hole `1`, pigeon `2` nowhere. -/
theorem pigFact_stable : pigFact.Stable ↑({0, 3, 7, 8, 10, 11, 12} : Finset ℕ) :=
  (pigFact.isStable_iff _).mp (by decide +kernel)

theorem pigFact_hall_refused : pigFact.checkCert [.hall 1000 [] [0, 1, 2] (holes pigFact)] = false := by
  decide +kernel

/-! ## Constraint rules -/

theorem twoF_constraintRules :
    twoF.rules.ConstraintRule ⟨f, [a], [c, f]⟩ ∧ twoF.rules.ConstraintRule ⟨f, [b], [f]⟩ := by
  constructor <;> refine (twoF.rules.isConstraintRule_iff (by decide)).mp (by decide +kernel)

/-- `f :- not f. f :- a. a.` -/
def unnegated : Program Atom := [⟨f, [], [f]⟩, ⟨f, [a], []⟩, ⟨a, [], []⟩]

theorem unnegated_not_constraint : ¬ unnegated.ConstraintRule ⟨f, [], [f]⟩ := by
  simp [Program.ConstraintRule, unnegated]

theorem unnegated_stable : unnegated.Stable ↑({a, f} : Finset Atom) :=
  (unnegated.isStable_iff _).mp (by decide +kernel)

end Mettapedia.Logic.ASP.FalsumControls
