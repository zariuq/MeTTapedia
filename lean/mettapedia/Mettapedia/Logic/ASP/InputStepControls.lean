import Mettapedia.Logic.ASP.WeightCertificate

/-!
# Controls for input steps over added constraints

Values are computed by the kernel (`decide +kernel`).

## The program and its constraints

Two choices and the integrity constraint `:- a, b.` read as the rules `a :- not (asp:out a)`,
`(asp:out a) :- not a`, the same for `b`, and `asp:falsum :- a, b, not asp:falsum` (`choiceAB`). Its
stable models are `{(asp:out a), (asp:out b)}`, `{a, (asp:out b)}` and `{b, (asp:out a)}`
(`choiceAB_stable`), and not `{a, b}` (`choiceAB_not_both`). The numbering has the five atoms and no
body (`choiceAB_varList`): `(asp:out a)`, `(asp:out b)`, `a`, `b`, `asp:falsum` are the variables
`0, …, 4`. The completion has ten clauses (`choiceAB_inputs`).

The constraints added (`added`) are `(a) ∅`, then `∅ (a, b)`, forbidding `not a` with `not b`, then
`(b) ∅`. Their clauses are `not a`, `a ∨ b` and `not b` (`added_clauses`). Each of the three stable
models violates one of them, and the first two leave `{b, (asp:out a)}` (`bOutA_meets`).

## Accepted

The three input steps, then the empty clause by RUP: `not a` and `not b` make `a ∨ b` false
(`certificate`, `certificate_accepted`). So no stable model meets the three constraints
(`no_stable_meets`). The input clause may repeat or reorder the literals of the constraint's
clause: they are compared as sets (`reordered_accepted`). The empty constraint has the empty clause,
which refutes alone (`empty_constraint_accepted`).

## Refused

* The certificate with the input step `a ∨ not b`, the clause of no added constraint
  (`wrongInput_refused`).
* The certificate over the first two constraints only (`shortened_refused`): the input step
  `not b` matches none of them. Indeed `{b, (asp:out a)}` meets both, so every certificate is refused
  over them (`shortened_certificates_refused`).
* The certificate without its RUP step (`truncated_refused`).
* The certificate for the checker without added constraints, which refuses every input step
  (`unconstrained_refused`; `checkCert` is `checkCertWith []`, `DefProgram.checkCertWith_nil`).
* An input step for a constraint over `c`, an atom outside the program, which has no variable
  (`unknownAtom_refused`); that constraint matches no step, while the others still do
  (`unknownAtom_others_match`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.InputStepControls

open DefProgram Mettapedia.GSLT.Logic PropositionalFormula

/-- The atoms of the library's translation, and one atom `c` outside the program. -/
inductive Atom
  | a
  | b
  /-- `(asp:out a)` -/
  | outA
  /-- `(asp:out b)` -/
  | outB
  /-- `asp:falsum` -/
  | falsum
  | c
  deriving DecidableEq, Repr

open Atom

/-! ## The program and its constraints -/

/-- The choices of `a` and `b` and the integrity constraint `:- a, b.` -/
def choiceAB : DefProgram Atom :=
  ⟨[⟨a, [], [outA]⟩, ⟨outA, [], [a]⟩, ⟨b, [], [outB]⟩, ⟨outB, [], [b]⟩, ⟨falsum, [a, b], [falsum]⟩], []⟩

theorem choiceAB_stable :
    choiceAB.Stable ↑({outA, outB} : Finset Atom) ∧ choiceAB.Stable ↑({a, outB} : Finset Atom) ∧
      choiceAB.Stable ↑({b, outA} : Finset Atom) :=
  ⟨(choiceAB.isStable_iff _).mp (by decide +kernel), (choiceAB.isStable_iff _).mp (by decide +kernel),
    (choiceAB.isStable_iff _).mp (by decide +kernel)⟩

theorem choiceAB_not_both : ¬ choiceAB.Stable ↑({a, b} : Finset Atom) := fun h =>
  absurd ((choiceAB.isStable_iff _).mpr h) (by decide +kernel)

theorem choiceAB_varList :
    choiceAB.varList = [.atom outA, .atom outB, .atom a, .atom b, .atom falsum] := by
  decide +kernel

/-- `(asp:out a) ∨ a` for `a :- not (asp:out a)` and the like, the clause `not a ∨ not b` of the
constraint, then the support clauses in atom order. -/
theorem choiceAB_inputs : choiceAB.inputs =
    [(1, [.pos 0, .pos 2]), (2, [.pos 2, .pos 0]), (3, [.pos 1, .pos 3]), (4, [.pos 3, .pos 1]),
     (5, [.neg 2, .neg 3]),
     (6, [.neg 0, .neg 2]), (7, [.neg 1, .neg 3]), (8, [.neg 2, .neg 0]), (9, [.neg 3, .neg 1]),
     (10, [.neg 4])] := by
  decide +kernel

/-- `(a) ∅`, `∅ (a, b)`, `(b) ∅`. -/
def added : List (List Atom × List Atom) := [([a], []), ([], [a, b]), ([b], [])]

/-- `not a`, `a ∨ b`, `not b`: the C solver's `-3`, `3 4`, `-4`. -/
theorem added_clauses : added.map choiceAB.inputClause = [[.neg 2], [.pos 2, .pos 3], [.neg 3]] := by
  decide +kernel

/-- `{b, (asp:out a)}` meets the first two constraints. -/
theorem bOutA_meets : ∀ k ∈ added.take 2,
    ¬ ((∀ p ∈ k.1, p ∈ (↑({b, outA} : Finset Atom) : Set Atom)) ∧
      ∀ n ∈ k.2, n ∉ (↑({b, outA} : Finset Atom) : Set Atom)) := by
  simp only [Finset.mem_coe]
  decide +kernel

/-! ## Accepted -/

/-- The certificate around its second step. -/
def certWith (second : WCertStep) : List WCertStep :=
  [.input 11 [.neg 2], second, .input 13 [.neg 3], .lrat (.rup 14 [] [11, 13, 12])]

/-- `(certificate (input 11 (-3)) (input 12 (3 4)) (input 13 (-4)) (rup 14 () (11 13 12)))`. -/
def certificate : List WCertStep := certWith (.input 12 [.pos 2, .pos 3])

theorem certificate_accepted : choiceAB.checkCertWith added certificate = true := by decide +kernel

theorem no_stable_meets (S : Set Atom) :
    ¬ (choiceAB.Stable S ∧ ∀ k ∈ added, ¬ ((∀ p ∈ k.1, p ∈ S) ∧ ∀ n ∈ k.2, n ∉ S)) :=
  choiceAB.checkCertWith_sound certificate_accepted S

/-- `b ∨ a ∨ b` for `a ∨ b`. -/
theorem reordered_accepted : choiceAB.checkCertWith added (certWith (.input 12 [.pos 3, .pos 2, .pos 3])) = true := by
  decide +kernel

theorem empty_constraint_accepted : choiceAB.checkCertWith [([], [])] [.input 11 []] = true := by
  decide +kernel

/-! ## Refused -/

/-- `a ∨ not b`. -/
theorem wrongInput_refused : choiceAB.checkCertWith added (certWith (.input 12 [.pos 2, .neg 3])) = false := by
  decide +kernel

theorem shortened_refused : choiceAB.checkCertWith (added.take 2) certificate = false := by decide +kernel

theorem shortened_certificates_refused (steps : List WCertStep) :
    choiceAB.checkCertWith (added.take 2) steps = false := by
  cases accepted : choiceAB.checkCertWith (added.take 2) steps with
  | false => rfl
  | true => exact absurd ⟨choiceAB_stable.2.2, bOutA_meets⟩ (choiceAB.checkCertWith_sound accepted _)

theorem truncated_refused : choiceAB.checkCertWith added (certificate.take 3) = false := by decide +kernel

theorem unconstrained_refused : choiceAB.checkCert certificate = false := by decide +kernel

/-- `c` has no variable: `choiceAB.index (.atom c)` is `5`, past the numbering, and the clause
`not 5` of the constraint `(c) ∅` is refused. -/
theorem unknownAtom_refused :
    choiceAB.index (.atom c) = 5 ∧ choiceAB.inputClause ([c], []) = [.neg 5] ∧
      choiceAB.inputStepOk [([c], [])] [.neg 5] = false := by
  decide +kernel

/-- Beside a constraint over `c`, the clause of another constraint is accepted. -/
theorem unknownAtom_others_match : choiceAB.inputStepOk [([c], []), ([a], [])] [.neg 2] = true := by
  decide +kernel

end Mettapedia.Logic.ASP.InputStepControls
