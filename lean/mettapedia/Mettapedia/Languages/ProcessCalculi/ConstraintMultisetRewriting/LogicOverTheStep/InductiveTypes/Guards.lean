import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Numbers

/-!
# A second mechanism: a guard on every made row

Instead of restricting who may write, the step may admit a firing only when every row it makes passes
a check (`guardedProgram`, an admission policy of the tree's step, `Interface.Step.ofEffect`, as the
step under a program is). For a free type membership is decided from the row
(`Numbers.generated_iff_isNumeral`), so the check is a structural test of the made row
(`numGuard`).

* **Under the guard, membership holds for every rule set** (`guarded_membership`): whatever rules are
  installed, junk included, every number row of every state reached from the empty store is generated.
  No right and no writer discipline is involved.
* **Control: without the guard it fails** (`unguarded_breaks_membership`): the same rule set reaches
  `natRow junkE` on the plain step under a program.
* **The guard checks membership, not derivation** (`guard_admits_shortcut`): it admits the firing that
  makes the row of two from nothing.

The price is the check: a structural test of each made row, which exists because a free type's row
determines its derivation. For a type whose rows do not determine their premises, a guard must search
for a derivation; restricting writers to the constructors needs no such search, because each firing
of a constructor carries its own premises.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open NamesOnTheStep NamesOnTheStep.IssuingControls
open MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)
open Interface
open StepSpan (Succ)
open ProgramAdequacy (program program_succ_iff)

namespace Guards

/-- **The guard of the numbers**: a made number row is the row of a numeral, by the structural check. -/
def numGuard (t : Expr) : Prop := ∀ x, t = natRow x → Numbers.isNumeral x = true

/-- **The first-order step under a rule set, with a guard on every made row**: an admission policy of
the tree's step, as the step under a program is, with the guard added. -/
def guardedProgram (R : Set (RuleInstance Expr)) (guard : Expr → Prop) :
    Interface.Step (Frames.ofSubstitution ground) Occ Conf (fun _ => AnnotatedRuns.Firing Expr Unit Occ) :=
  Interface.Step.ofEffect (AnnotatedRuns.firstOrder ground Prod.fst).toStep.effectCore
    fun {C} f _ => f.Valid ground Prod.fst C ∧ f.rule ∈ R ∧ ∀ t ∈ f.rule.produce, guard t

theorem guarded_succ_iff (R : Set (RuleInstance Expr)) (guard : Expr → Prop) (C C' : Conf) :
    Succ (guardedProgram R guard) C C' ↔
      ∃ (rule : RuleInstance Expr) (sel : Selection Occ), rule ∈ R ∧ (∀ t ∈ rule.produce, guard t) ∧
        sel.Valid ground Prod.fst rule C ∧ sel.result Prod.fst rule C = C' := by
  constructor
  · rintro ⟨f, ⟨_, valid, member, guarded⟩, reached⟩
    exact ⟨f.rule, f.selection, member, guarded, valid.firing, reached⟩
  · rintro ⟨rule, sel, member, guarded, valid, reached⟩
    let f : AnnotatedRuns.Firing Expr Unit Occ := ⟨rule, [], sel⟩
    have fValid : f.Valid ground Prod.fst C := PredicateQueryAdmission.regionValid_nil_iff.mpr valid
    exact ⟨f, ⟨(AnnotatedRuns.firstOrder ground Prod.fst).toStep.prepares fValid, fValid, member,
      guarded⟩, reached⟩

/-- A guarded move keeps every number row generated. -/
theorem guarded_keeps {R : Set (RuleInstance Expr)} {C C' : Conf}
    (moved : Succ (guardedProgram R numGuard) C C')
    (holds : ClosedBy contents (fun e => place e = .num) {r | Generated natRules ∅ r} C) :
    ClosedBy contents (fun e => place e = .num) {r | Generated natRules ∅ r} C' := by
  obtain ⟨rule, sel, _, guarded, valid, rfl⟩ := (guarded_succ_iff R numGuard C C').mp moved
  rintro r ⟨o, present, rfl⟩ atNum
  rcases mem_fire.mp present with ⟨old, -⟩ | made
  · exact holds o.1 ⟨o, old, rfl⟩ atNum
  · have madeList : o ∈ sel.made := by simpa [Selection.commit] using made
    have produced := made_label valid madeList
    obtain ⟨x, isRow⟩ := place_num atNum
    have checked := guarded o.1 produced x isRow
    rw [isRow]
    exact Numbers.generated_iff_isNumeral.mpr checked

/-- **Under the guard, membership holds for every rule set.** -/
theorem guarded_membership (R : Set (RuleInstance Expr)) {C : Conf}
    (run : Relation.ReflTransGen (Succ (guardedProgram R numGuard)) ProgramAdequacy.emptyStore C)
    {r : Expr} (present : r ∈ contents C) (atNum : place r = .num) :
    ∃ k, r = natRow (numeral k) := by
  have invariant : ClosedBy contents (fun e => place e = .num) {r | Generated natRules ∅ r} C := by
    clear present atNum
    induction run with
    | refl => exact closedBy_empty _ _
    | tail _ moved ih => exact guarded_keeps moved ih
  exact Numbers.natRules_generated_iff.mp (invariant r present atNum)

/-- The rules of the owner and the junk writer together. -/
def mixedRules : Set (RuleInstance Expr) :=
  {ρ | ∃ schema ∈ [Schema.zero, .succ, .junk], ∃ x, activate schema x = some ρ}

/-- **Control: without the guard, the same rule set reaches junk** on the step under a program. -/
theorem unguarded_breaks_membership :
    ∃ C, Succ (program ground Prod.fst mixedRules) ProgramAdequacy.emptyStore C ∧
      natRow junkE ∈ contents C ∧ ¬ Generated natRules ∅ (natRow junkE) := by
  obtain ⟨C, moved, -, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := Numbers.junkWriter)
      (d := ([], natRow junkE)) rfl (List.mem_singleton_self _) (x := []) rfl plain_empty
      fun _ member => absurd member List.not_mem_nil
  obtain ⟨schema, installed, x, ρ, computed, sel, valid, -, rfl⟩ := moved
  refine ⟨_, (program_succ_iff ground Prod.fst mixedRules _ _).mpr
    ⟨ρ, sel, ⟨schema, by simp [Numbers.junkWriter] at installed; simp [installed], x, computed⟩,
      valid, rfl⟩, ?_, Numbers.junk_not_generated⟩
  rw [exact]
  exact Set.mem_insert _ _

/-- **The guard checks membership, not derivation**: it admits making the row of two from nothing. -/
theorem guard_admits_shortcut :
    ∃ C, Succ (guardedProgram {rule [] [] [natRow (succE (succE zeroE))]} numGuard)
      ProgramAdequacy.emptyStore C ∧ natRow (numeral 2) ∈ contents C ∧
        natRow (numeral 1) ∉ contents C := by
  obtain ⟨C, moved, -, exact⟩ :=
    ctor_fires (activate := activate) (place := place) (process := Numbers.shortcutWriter)
      (d := ([], natRow (succE (succE zeroE)))) rfl (List.mem_singleton_self _) (x := []) rfl
      plain_empty fun _ member => absurd member List.not_mem_nil
  obtain ⟨schema, installed, x, ρ, computed, sel, valid, -, rfl⟩ := moved
  have isShortcut : schema = .shortcut := List.mem_singleton.mp installed
  subst isShortcut
  rcases x with _ | ⟨a, rest⟩
  · simp only [activate, Option.some.injEq] at computed
    subst computed
    refine ⟨_, (guarded_succ_iff _ numGuard _ _).mpr ⟨_, sel, rfl, fun t produced y isRow => ?_, valid,
      rfl⟩, ?_, ?_⟩
    · have := List.mem_singleton.mp produced
      rw [this] at isRow
      rw [← natRow_injective isRow]
      rfl
    · rw [exact]
      exact Set.mem_insert _ _
    · rw [exact, contents_empty]
      simp [numeral, natRow, succE, zeroE]
  · simp [activate] at computed

end Guards

#print axioms Guards.guarded_succ_iff
#print axioms Guards.guarded_membership
#print axioms Guards.unguarded_breaks_membership
#print axioms Guards.guard_admits_shortcut

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
