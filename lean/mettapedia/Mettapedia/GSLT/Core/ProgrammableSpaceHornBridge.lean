import Mettapedia.GSLT.Core.ProgrammableSpaceInference
import Mettapedia.GSLT.Parsing.FiniteHornSaturation

/-!
# Authored rule positions and finite executable saturation

An authored list retains each rule position as its own inference instance.
The propositional chainer forgets duplicate positions and duplicate premises
when it compiles that list to finite support. The two presentations have the
same finite-proof closure, and a fair persistent run therefore agrees exactly
with the executable finite-support saturation. This does not identify their
derivation receipts, firing costs or intermediate results.

Only the authored rules and initial facts must be finite. The atom type need
not be finite, and fairness provides no policy-independent time bound.

This comparison uses the existing finite-set chainer and its standard host
dependencies, including classical choice in finite-set extensionality and
deduplication proof metadata. These are comparison dependencies; no additional
principle is added to the generic inference theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Core.ProgrammableSpaceHornBridge

open AnnotatedHorn ProgrammableSpaceInference

universe u
variable {Atom : Type u} [DecidableEq Atom]

def authoredTheory (rules : List (DefiniteRule Atom)) (facts : Finset Atom) :
    Theory Atom (Fin rules.length) where
  seeds := {atom | atom ∈ facts}
  rule position := rules.get position

def compileRule (rule : DefiniteRule Atom) : Mettapedia.Logic.LP.PropRule Atom :=
  ⟨rule.body.toFinset, rule.head⟩

def compiledProgram (rules : List (DefiniteRule Atom)) : Mettapedia.Logic.LP.PropProgram Atom :=
  (rules.map compileRule).toFinset

theorem compiled_rule_iff (rules : List (DefiniteRule Atom))
    (rule : Mettapedia.Logic.LP.PropRule Atom) :
    rule ∈ compiledProgram rules ↔
      ∃ position : Fin rules.length, compileRule (rules.get position) = rule := by
  constructor
  · intro member
    obtain ⟨authored, present, same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    obtain ⟨position, rfl⟩ := List.mem_iff_get.mp present
    exact ⟨position, same⟩
  · rintro ⟨position, rfl⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨rules.get position, List.get_mem _ _, rfl⟩)

theorem authored_derivation_to_compiled (rules : List (DefiniteRule Atom)) (facts : Finset Atom)
    {atom : Atom} (derivation : (authoredTheory rules facts).Derivable atom) :
    Mettapedia.Logic.LP.Derivable (compiledProgram rules) facts atom := by
  induction derivation with
  | seed present => exact .fact present
  | rule position _ induction =>
    apply Mettapedia.Logic.LP.Derivable.rule
      ((compiled_rule_iff rules _).mpr ⟨position, rfl⟩)
    intro premise present
    exact induction premise (List.mem_toFinset.mp present)

theorem compiled_derivation_to_authored (rules : List (DefiniteRule Atom)) (facts : Finset Atom)
    {atom : Atom} (derivation : Mettapedia.Logic.LP.Derivable (compiledProgram rules) facts atom) :
    (authoredTheory rules facts).Derivable atom := by
  induction derivation with
  | fact present => exact .seed present
  | @rule rule present _ induction =>
    obtain ⟨position, rfl⟩ := (compiled_rule_iff rules rule).mp present
    apply Theory.Derivable.rule position
    intro premise member
    exact induction premise (List.mem_toFinset.mpr member)

theorem authored_derivation_iff_compiled (rules : List (DefiniteRule Atom)) (facts : Finset Atom)
    (atom : Atom) :
    (authoredTheory rules facts).Derivable atom ↔
      Mettapedia.Logic.LP.Derivable (compiledProgram rules) facts atom :=
  ⟨authored_derivation_to_compiled rules facts, compiled_derivation_to_authored rules facts⟩

theorem authored_closure_eq_saturation (rules : List (DefiniteRule Atom)) (facts : Finset Atom) :
    (authoredTheory rules facts).closure =
      {atom | atom ∈ Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast
        (compiledProgram rules) facts} := by
  ext atom
  exact (authored_derivation_iff_compiled rules facts atom).trans
    (Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast_iff_derivable _ _ atom).symm

theorem fair_support_eq_saturation (rules : List (DefiniteRule Atom)) (facts : Finset Atom)
    (run : Run (authoredTheory rules facts)) (fair : run.RuleInstanceFair) :
    run.support = {atom | atom ∈ Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast
      (compiledProgram rules) facts} :=
  (run.support_eq_closure fair).trans (authored_closure_eq_saturation rules facts)

theorem finite_facts_available {Instances : Type*} {theory : Theory Atom Instances}
    (run : Run theory) (facts : Finset Atom) (available : ∀ atom ∈ facts, atom ∈ run.support) :
    ∃ tick, ∀ atom ∈ facts, atom ∈ run.facts tick := by
  induction facts using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert first rest _ induction =>
    obtain ⟨firstTick, firstPresent⟩ := available first (Finset.mem_insert_self _ _)
    obtain ⟨restTick, restPresent⟩ := induction
      (fun atom member => available atom (Finset.mem_insert_of_mem member))
    refine ⟨max firstTick restTick, ?_⟩
    intro atom member
    rcases Finset.mem_insert.mp member with same | inRest
    · subst atom
      exact run.monotone (Nat.le_max_left _ _) firstPresent
    · exact run.monotone (Nat.le_max_right _ _) (restPresent atom inRest)

theorem finite_fair_run_eventually_exact (rules : List (DefiniteRule Atom)) (facts : Finset Atom)
    (run : Run (authoredTheory rules facts)) (fair : run.RuleInstanceFair) :
    ∃ tick, run.facts tick = (authoredTheory rules facts).closure := by
  obtain ⟨tick, ready⟩ := finite_facts_available run
    (Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast (compiledProgram rules) facts)
    (by intro atom present; rw [fair_support_eq_saturation rules facts run fair]; exact present)
  refine ⟨tick, Set.Subset.antisymm (run.sound tick) ?_⟩
  intro atom derivation
  exact ready atom (by
    change atom ∈ {atom | atom ∈ Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast
      (compiledProgram rules) facts}
    rw [← authored_closure_eq_saturation rules facts]
    exact derivation)

namespace Controls

def rules : List (DefiniteRule Nat) := [⟨[0], 1⟩, ⟨[1], 2⟩, ⟨[0, 0], 1⟩]
def initial : Finset Nat := {0}
def saturated : Finset Nat :=
  Mettapedia.GSLT.Parsing.FiniteHornSaturation.saturateFast (compiledProgram rules) initial

def firstPosition : Fin rules.length := ⟨0, by decide⟩
def duplicatePosition : Fin rules.length := ⟨2, by decide⟩

theorem finite_execution_reaches_two : 2 ∈ saturated := by decide +kernel

theorem finite_execution_refuses_unreachable : 3 ∉ saturated := by decide +kernel

theorem exact_saturated_support : saturated = {0, 1, 2} := by decide +kernel

theorem ordered_positions_are_retained :
    firstPosition ≠ duplicatePosition ∧
      (authoredTheory rules initial).rule firstPosition ≠
        (authoredTheory rules initial).rule duplicatePosition := by
  constructor
  · decide +kernel
  · intro same
    have body := congrArg DefiniteRule.body same
    change [0] = [0, 0] at body
    exact (by decide : [0] ≠ [0, 0]) body

theorem compiled_support_forgets_duplicate_premise :
    compileRule ((authoredTheory rules initial).rule firstPosition) =
      compileRule ((authoredTheory rules initial).rule duplicatePosition) := by
  simp [compileRule, authoredTheory, rules, firstPosition, duplicatePosition]

end Controls

end Mettapedia.GSLT.Core.ProgrammableSpaceHornBridge
