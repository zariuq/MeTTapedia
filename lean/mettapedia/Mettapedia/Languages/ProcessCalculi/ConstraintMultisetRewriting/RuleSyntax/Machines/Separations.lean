import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Branching
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Representation.Equivariance

/-!
# A system hosted in the weak sense and not one firing for one step

**One firing for one step, through the constants** (`OneStepHosts`): a finite list of rules hosts a system on
the naturals one firing for one step when the system steps from `n` to `m` exactly when the rules rewrite the
one-row bag of the constant `n` to the one-row bag of the constant `m`. This is the sense of
`Representation`, read on the encoding `n ↦ {.sym n}`.

* **`evenToZero`**: every even number steps to `0`, and nothing else steps.
* **Not one firing for one step** (`evenToZero_not_oneStep`): a finite list of rules mentions finitely many
  constants, so its rewriting is unchanged by exchanging an even constant and the next odd one beyond them
  (`Representation.rewrites_equivariant`); the system tells them apart.
* **Hosted in the weak sense** (`evenToZero_weak`): a code lists `[0]` from an even number and `[]` from an odd
  one (`exists_parityCode`), and the program of `Branching` hosts it, with silent firings that end.

The encoding matters: an encoding that writes the parity of `n` into its row lets one rule fire exactly at the
even numbers. The separation is for the encoding by constants.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Separations

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open Mettapedia.Languages.PartrecMachine
open Turing.ToPartrec
open NamesOnTheStep (Expr)
open Presentation.Schematic
open PartialRecursive
open Branching (Choose stepWeak)

/-- **One firing for one step, through the constants.** -/
def OneStepHosts (rules : List SRule) (R : ℕ → ℕ → Prop) : Prop :=
  ∀ n m, R n m ↔ Rewrites rules {Expr.sym n} {Expr.sym m}

/-- **A positive instance**: the rule that takes a row and makes it again hosts, one firing for one step, the
system in which every number steps to itself. -/
theorem identity_oneStep : OneStepHosts [rowRule (unk 0) (unk 0)] fun n m => m = n := by
  intro n m
  constructor
  · rintro rfl
    exact (rewrites_rootRules_iff [(unk 0, unk 0)] (.sym m) {Expr.sym m}).mpr
      ⟨.sym m, ⟨(unk 0, unk 0), List.mem_singleton_self _, fun _ => .sym m, rfl, rfl⟩, rfl⟩
  · intro rewrites
    obtain ⟨e', ⟨pair, member, θ, matched, made⟩, same⟩ :=
      (rewrites_rootRules_iff [(unk 0, unk 0)] (.sym n) {Expr.sym m}).mp rewrites
    obtain rfl := List.mem_singleton.mp member
    have first : θ 0 = Expr.sym n := matched
    have second : θ 0 = e' := made
    have third : Expr.sym m = e' := Multiset.singleton_inj.mp same
    exact Expr.sym.inj (third.trans (second.symm.trans first))

/-- **Every even number steps to `0`**, and nothing else steps. -/
def evenToZero (n m : ℕ) : Prop := (∃ j, n = 2 * j) ∧ m = 0

/-- **`evenToZero` is hosted one firing for one step by no finite list of rules**, of any kind. -/
theorem evenToZero_not_oneStep (rules : List SRule) : ¬ OneStepHosts rules evenToZero := by
  intro hosts
  have related : evenToZero (2 * (Representation.programBound rules + 1)) 0 :=
    ⟨⟨Representation.programBound rules + 1, rfl⟩, rfl⟩
  have swapped := Representation.rewrites_equivariant rules
    (c := 2 * (Representation.programBound rules + 1)) (d := 2 * (Representation.programBound rules + 1) + 1)
    (by omega) (by omega) ((hosts _ _).mp related)
  rw [Multiset.map_singleton, Multiset.map_singleton] at swapped
  have moved : Representation.swapRow (2 * (Representation.programBound rules + 1))
      (2 * (Representation.programBound rules + 1) + 1) (.sym (2 * (Representation.programBound rules + 1))) =
      .sym (2 * (Representation.programBound rules + 1) + 1) := if_pos rfl
  have zeroStays : Representation.swapRow (2 * (Representation.programBound rules + 1))
      (2 * (Representation.programBound rules + 1) + 1) (.sym 0) = .sym 0 := by
    show (if 0 = 2 * (Representation.programBound rules + 1) then _ else
      if 0 = 2 * (Representation.programBound rules + 1) + 1 then _ else _) = _
    rw [if_neg (by omega), if_neg (by omega)]
  rw [moved, zeroStays] at swapped
  obtain ⟨⟨j, even⟩, -⟩ := (hosts _ _).mpr swapped
  omega

/-- **A code that lists the successors of `evenToZero`**: `[0]` from an even number, `[]` from an odd one. -/
theorem exists_parityCode : ∃ c : Code, ∀ n, c.eval [n] = pure (if n % 2 = 0 then [0] else []) := by
  have partrec : Partrec fun n : ℕ => Part.some (n % 2) :=
    (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)).to_comp.partrec
  obtain ⟨c₂, evaluates⟩ := Code.exists_code ((Nat.Partrec'.part_iff₁ (f := fun n => Part.some (n % 2))).mpr partrec)
  refine ⟨Code.comp (Code.case Code.zero' Code.tail) c₂, fun n => ?_⟩
  have evaluated : c₂.eval [n] = pure <$> Part.some (n % 2) := evaluates ⟨[n], rfl⟩
  rcases Nat.mod_two_eq_zero_or_one n with parity | parity <;> simp [evaluated, parity]

/-- The parity code computes the successors of `evenToZero`. -/
theorem choose_parity {c : Code} (evaluates : ∀ n, c.eval [n] = pure (if n % 2 = 0 then [0] else []))
    (n m : ℕ) : Choose c n m ↔ evenToZero n m := by
  constructor
  · rintro ⟨l, member, inside⟩
    rw [evaluates n] at member
    have same : l = if n % 2 = 0 then [0] else [] := Part.mem_some_iff.mp member
    subst same
    by_cases parity : n % 2 = 0
    · rw [if_pos parity] at inside
      exact ⟨⟨n / 2, by omega⟩, List.mem_singleton.mp inside⟩
    · rw [if_neg parity] at inside
      exact absurd inside List.not_mem_nil
  · rintro ⟨⟨j, rfl⟩, rfl⟩
    refine ⟨[0], ?_, List.mem_singleton_self 0⟩
    rw [evaluates, if_pos (by omega)]
    exact Part.mem_some _

/-- **`evenToZero` is hosted in the weak sense**: the program of `Branching` for the parity code relates every
number to the state of its pending evaluation, with silent firings that end. -/
theorem evenToZero_weak :
    ∃ (c : Code) (total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x]), (∀ n m, Choose c n m ↔ evenToZero n m) ∧
      ∀ n, (stepWeak c total).related n (start c [n]) := by
  obtain ⟨c, evaluates⟩ := exists_parityCode
  have total : ∀ x : ℕ, ∃ l, l ∈ c.eval [x] := fun x => ⟨_, by rw [evaluates]; exact Part.mem_some _⟩
  exact ⟨c, total, choose_parity evaluates, Branching.stepWeak_start c total⟩

#print axioms identity_oneStep
#print axioms evenToZero_not_oneStep
#print axioms exists_parityCode
#print axioms choose_parity
#print axioms evenToZero_weak

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines.Separations
