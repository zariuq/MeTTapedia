import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.OwnUnknowns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.Atoms

/-!
# The same firings without being renamings of each other

A rule and a copy with its own unknowns renamed have the same firings (`renamed_succ`). The converse
fails. Over first-order atoms at one frame, `silent n` takes the row `n` and tells `1 ≐ 2`, which no
instantiation solves.

* `silent_refused`: no firing of a silent rule is admitted, in any program and at any state.
* **`silent_same`**: the programs `{silent 1}` and `{silent 2}` have the same transitions, namely
  none.
* **`silent_not_renamed`**: no morphism out of the unknowns of `silent 1` carries it to `silent 2`.

So equality of two rules up to the names of their own unknowns is a sufficient test for having the
same firings, and not a necessary one: whether a rule ever fires depends on whether its tells and
guards can be met, which the test does not look at. A rule that does fire, for contrast, is the
link of `Derived.Atoms.token_admitted`.

The sufficient test has an instance here: `echo` takes a row `x` and makes `9`; its copy with the
unknown shifted is another rule (`echo_renamed_ne`) with the same transitions beside every program
(`echo_renamed_succ`, by `undo_shift`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.SameFirings

open Interface (Frames)
open LogicOverTheStep.StepSpan (Succ)
open Mettapedia.Logic.LP
open Examples (Tm X E c x shift)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- **A silent rule**: take the row `n` and tell `1 ≐ 2`. -/
def silent (n : ℕ) : Rule Tm := ⟨PUnit.unit, ⟨[c n], [], [(c 1, c 2)], [], []⟩, []⟩

/-- **No firing of a silent rule is admitted**: its information has no solution. -/
theorem silent_refused {n : ℕ} {P : Program Tm} {s : State Tm ℕ} (g : Firing ℕ E P s.frame)
    (rule : g.rule = silent n) : ¬ g.Admits X s := by
  obtain ⟨r, inP, ext, opening, selection, seen⟩ := g
  have isRule : r = silent n := rule
  subst isRule
  intro admitted
  obtain ⟨b, σ, solved⟩ := admitted.2.2.1
  have equal : c 1 = c 2 :=
    solved (c 1, c 2) (List.mem_append_right _ (List.mem_singleton_self _))
  exact absurd (Term.const.inj equal) (by decide)

/-- **Two silent rules have the same transitions**: none. -/
theorem silent_same (s t : State Tm ℕ) :
    Succ (step X ℕ E {silent 1}).toStep s t ↔ Succ (step X ℕ E {silent 2}).toStep s t := by
  constructor
  · rintro ⟨g, admitted, -⟩
    exact absurd admitted (silent_refused g g.member)
  · rintro ⟨g, admitted, -⟩
    exact absurd admitted (silent_refused g g.member)

/-- **They are not renamings of each other**: no morphism out of the unknowns of the first carries
it to the second. -/
theorem silent_not_renamed (j : Subst atoms) :
    renamed X (silent 1) (b := PUnit.unit) j ≠ silent 2 := by
  intro same
  let takeOf : Rule Tm → List (Tm PUnit.unit) := fun r => r.body.take
  have takes : takeOf (renamed X (silent 1) (b := PUnit.unit) j) = takeOf (silent 2) :=
    congrArg takeOf same
  have heads : c 1 = c 2 := (List.cons.inj takes).1
  exact absurd (Term.const.inj heads) (by decide)

/-! ## A renamed copy: the sufficient test has an instance -/

/-- A rule with one unknown of its own: take a row `x`, make the row `9`. -/
def echo : Rule Tm := ⟨PUnit.unit, ⟨[x], [], [], [], [c 9]⟩, []⟩

/-- Back along the shift of the unknowns. -/
def unshift : Subst atoms := fun v => Term.var (v - 1)

/-- The shift is undone on the terms of the rule. -/
theorem undo_shift : ∀ t ∈ echo.terms,
    X.act (a := PUnit.unit) (b := echo.locals) unshift
      (X.act (a := echo.locals) (b := PUnit.unit) shift t) = t := by
  intro t member
  have inside : t ∈ echo.terms := member
  simp [echo, Rule.terms] at inside
  rcases inside with rfl | rfl <;> rfl

/-- **The rule and its copy with the unknown renamed have the same transitions**, beside every
program: `renamed_succ` at this rule. -/
theorem echo_renamed_succ (Q : Program Tm) (s t : State Tm ℕ) :
    Succ (step X ℕ E (Q ∪ {echo})).toStep s t ↔
      Succ (step X ℕ E (Q ∪ {renamed X echo (b := PUnit.unit) shift})).toStep s t :=
  renamed_succ X Q echo (b := PUnit.unit) shift unshift undo_shift s t

/-- **The copy is another rule**: its take pattern is another unknown. -/
theorem echo_renamed_ne : renamed X echo (b := PUnit.unit) shift ≠ echo := by
  intro same
  let takeOf : Rule Tm → List (Tm PUnit.unit) := fun r => r.body.take
  have takes : takeOf (renamed X echo (b := PUnit.unit) shift) = takeOf echo :=
    congrArg takeOf same
  have heads : (Term.var 1 : Term atoms) = (Term.var 0 : Term atoms) := (List.cons.inj takes).1
  exact absurd (Term.var.inj heads) (by decide)

#print axioms silent_refused
#print axioms silent_same
#print axioms silent_not_renamed
#print axioms undo_shift
#print axioms echo_renamed_succ
#print axioms echo_renamed_ne

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.SameFirings
