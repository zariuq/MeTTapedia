import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Separation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder
import Mettapedia.Logic.LP.TermEquality

/-!
# A program with no check that a neighbour switches off: a tell on a shared unknown

The separation `no_uniformTranslation` needs one property of its source: a composable neighbour
switches reachable success off (`ParallelCalculus.Switchable`). Over first-order terms the step under
a program with no check at all has it, with the same parallel composition as the absence-guarded
source (`stepCalculus`: the union of configurations, on disjoint stores with jointly solvable
knowledge) and success "a row `9` is present". Occurrences are pairs of a row and a copy number,
labelled by their row.

* the program has one rule, `tellRule`: read a row `y`, tell `y = 5`, make the row `9`; it has no
  checks (`tellRule_checks`): no absence, no count, no equality guard;
* alone, the store holding the row `x` succeeds (`request_succeeds`);
* the store with no rows whose knowledge says `x = 6` is composable with it
  (`request_neighbour_composable`); beside it no firing of the program is admitted, since its
  information would equate `5` and `6` (`nothing_admitted_beside`), so success is unreachable
  (`beside_neighbour_blocked`);
* hence the step under this program is switchable (`tellSource_switchable`), and no uniform
  translation carries it into a presentation with a parallel context rule
  (`no_uniformTranslation_presentation`), into rho's presentation (`no_uniformTranslation_rhoCalc`),
  into the reduction of a rho rule set (`no_uniformTranslation_rho`), or into positive bag rules
  (`no_uniformTranslation_bag`).

Composability supplies a solution of the two knowledges together. Admission beside the neighbour
needs a solution of the firing's own information together with the neighbour's knowledge
(`Composition.positive_admission_iff`), and here there is none (`composable_not_monotone`): a tell
must be consistent with the whole knowledge, the neighbour's included. So a parallel component can
switch success off through a shared unknown, with no absence guard. Without absence and count checks
it can do so only when every run to success has a firing whose information mentions an unknown the
neighbour's knowledge mentions (`SharedUnknown.switched_off_has_guard_or_shared`); over ground terms,
where there are no unknowns, such a program is never switchable (`Monotone.not_switchable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.Composition
  (unionOf)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

/-- Terms: numerals as constants and as variables, no function symbols. -/
abbrev atoms : LPSignature where
  constants := ℕ
  vars := ℕ
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Empty
  functionArity := Empty.elim

/-- The first-order action on these terms. -/
abbrev A : SubstitutionAction (Term atoms) (Subst atoms) := FirstOrder.action atoms

/-- An occurrence: its row and a copy number. -/
abbrev Occ := Term atoms × ℕ

/-- The caller's unknown. -/
def x : Term atoms := .var 0

/-- The rule's unknown. -/
def y : Term atoms := .var 1

/-- A constant. -/
def c (n : ℕ) : Term atoms := .const n

/-- **The rule**: read a row `y`, tell `y = 5`, make the row `9`. -/
def tellRule : RuleInstance (Term atoms) := ⟨[], [y], [(y, c 5)], [], [c 9]⟩

/-- It has no checks: no absence, no count, no equality guard. -/
theorem tellRule_checks : tellRule.checks = [] := rfl

/-- The program of that one rule. -/
def program (r : RuleInstance (Term atoms)) : Prop := r = tellRule

/-- **The step under the program**, with the parallel composition of `stepCalculus` and success
"a row `9` is present". -/
abbrev tellSource : ParallelCalculus := stepCalculus A (Prod.fst : Occ → Term atoms) program (· = c 9)

/-- The store holding the row `x`, with no knowledge. -/
def request : Configuration (Term atoms) Occ := ⟨[], {(x, 0)}⟩

/-- The store with no rows whose knowledge says `x = 6`. -/
def neighbour : Configuration (Term atoms) Occ := ⟨[(x, c 6)], ∅⟩

/-- The firing of `tellRule` at the request: read the row `x`, make the row `9`. -/
def fireAt : AnnotatedRuns.Firing (Term atoms) (Subst atoms) Occ :=
  ⟨tellRule, [], ⟨[], [(x, 0)], [(c 9, 0)]⟩⟩

/-- Its information at the request: the read equation and the tell. -/
theorem fireAt_problem :
    fireAt.selection.problem Prod.fst fireAt.rule request = [(y, x), (y, c 5)] := rfl

/-- **Alone, the firing is admitted.** -/
theorem fireAt_admitted : fireAt.Valid A Prod.fst request := by
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [fireAt, request, Selection.commit, x, c]
  · refine ⟨fun _ => c 5, fun e inside => ?_⟩
    rw [fireAt_problem] at inside
    simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
    rcases inside with rfl | rfl <;> rfl
  · intro check inside
    simp [fireAt, tellRule] at inside
  · intro query inside
    simp [fireAt] at inside

/-- **Alone, the request succeeds.** -/
theorem request_succeeds : tellSource.Succeeds request := by
  refine ⟨_, .single ⟨fireAt, rfl, fireAt_admitted, rfl⟩, (c 9, 0), ?_, rfl⟩
  change (c 9, 0) ∈ fire request.present (fireAt.selection.commit (T := Term atoms))
  rw [mem_fire]
  exact Or.inr (by simp [fireAt, Selection.commit])

/-- The request and the neighbour are composable: disjoint, and jointly solvable. -/
theorem request_neighbour_composable : tellSource.composable request neighbour := by
  refine ⟨Finset.disjoint_empty_right _, fun _ => c 6, fun e inside => ?_⟩
  simp only [request, neighbour, List.nil_append, List.mem_singleton] at inside
  subst inside
  rfl

/-- **Beside the neighbour no firing of the program is admitted**: its information would equate the
constants `5` and `6`. -/
theorem nothing_admitted_beside (f : AnnotatedRuns.Firing (Term atoms) (Subst atoms) Occ)
    (inProgram : program f.rule) : ¬ f.Valid A Prod.fst (unionOf request neighbour) := by
  intro valid
  have rule : f.rule = tellRule := inProgram
  obtain ⟨firing, -⟩ := valid
  obtain ⟨σ, solved⟩ := firing.consistent
  have readLength : f.selection.read.length = 1 := by
    rw [← firing.read_length, rule]
    rfl
  obtain ⟨o, single⟩ := List.length_eq_one_iff.mp readLength
  have present : o ∈ (unionOf request neighbour).present := by
    apply firing.occurrences.kept_subset
    simp [Selection.commit, single]
  have isX : o = (x, 0) := by
    simpa [unionOf, request, neighbour] using present
  have known : (x, c 6) ∈ f.selection.problem Prod.fst f.rule (unionOf request neighbour) := by
    simp [Selection.problem, unionOf, request, neighbour]
  have read : (y, o.1) ∈ f.selection.problem Prod.fst f.rule (unionOf request neighbour) := by
    simp [Selection.problem, Selection.equations, rule, tellRule, single]
  have told : (y, c 5) ∈ f.selection.problem Prod.fst f.rule (unionOf request neighbour) := by
    simp [Selection.problem, rule, tellRule]
  have six : σ 0 = c 6 := solved _ known
  have readEq : σ 1 = Subst.applyTerm σ o.1 := solved _ read
  have five : σ 1 = c 5 := solved _ told
  rw [isX] at readEq
  have same : (c 5 : Term atoms) = c 6 := five.symm.trans (readEq.trans six)
  exact absurd (Term.const.inj same) (by decide)

/-- **Beside the neighbour, success is unreachable**: nothing fires, and no row `9` is present. -/
theorem beside_neighbour_blocked : ¬ tellSource.Succeeds (unionOf request neighbour) := by
  rintro ⟨C', run, shows⟩
  rcases Relation.ReflTransGen.cases_head run with rfl | ⟨_, ⟨f, inProgram, admitted, -⟩, -⟩
  · obtain ⟨o, present, isNine⟩ := shows
    have isX : o = (x, 0) := by
      simpa [unionOf, request, neighbour] using present
    subst isX
    have wrong : (x : Term atoms) = c 9 := isNine
    exact absurd wrong (by simp [x, c])
  · exact nothing_admitted_beside f inProgram admitted

/-- **Composability does not make admission of a firing without checks monotone.** The pair is
composable (disjoint, jointly solvable knowledge), the firing is admitted alone, and it is refused
beside: admission beside the neighbour needs a solution of the firing's own information together
with the neighbour's knowledge (`Composition.positive_admission_iff`), which composability does not
provide. -/
theorem composable_not_monotone :
    Composable A request neighbour ∧ fireAt.Valid A Prod.fst request ∧
      ¬ fireAt.Valid A Prod.fst (unionOf request neighbour) :=
  ⟨request_neighbour_composable, fireAt_admitted, nothing_admitted_beside fireAt rfl⟩

/-- **The step under the program is switchable.** -/
theorem tellSource_switchable : tellSource.Switchable :=
  ⟨request, neighbour, request_neighbour_composable, request_succeeds, beside_neighbour_blocked⟩

/-- **No uniform translation of the step under the program into any presentation with a parallel
context rule**, read modulo its equations, for every success term `ω`. -/
theorem no_uniformTranslation_presentation
    {base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator}
    {language : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    {kind : Mettapedia.OSLF.MeTTaIL.Syntax.CollType} (has : HasParallelContextRule kind language)
    (ω : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    IsEmpty (UniformTranslation tellSource (presentationCalculus base language kind ω)) :=
  isEmpty_uniformTranslation tellSource_switchable (presentationCalculus_persistent has ω)

/-- **Instance: rho's presentation.** -/
theorem no_uniformTranslation_rhoCalc
    (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (ω : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    IsEmpty (UniformTranslation tellSource (presentationCalculus base
      Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc .hashBag ω)) :=
  no_uniformTranslation_presentation rhoCalc_hasParallelContextRule ω

section Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres

/-- **No uniform translation of the step under the program into the reduction of any rho rule
set**, for every success component `c`. -/
theorem no_uniformTranslation_rho {Index : Type*} (rules : Index → RhoScopedParallelEvents.ProcessRule)
    (admitted : Index → Prop) (context : Ctx sig) (c : Process context) :
    IsEmpty (UniformTranslation tellSource (rhoCalculus rules admitted context c)) :=
  isEmpty_uniformTranslation tellSource_switchable (rhoCalculus_persistent rules admitted context c)

end Rho

/-- **No uniform translation of the step under the program into positive bag rules.** -/
theorem no_uniformTranslation_bag
    {Γ : Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Equivalence.Rule
      Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NamesOnTheStep.Expr → Prop}
    (positiveRules : ∀ ρ, Γ ρ → ρ.Positive) :
    IsEmpty (UniformTranslation tellSource (bagCalculus Γ)) :=
  isEmpty_uniformTranslation tellSource_switchable (bagCalculus_persistent positiveRules)

#print axioms fireAt_admitted
#print axioms request_succeeds
#print axioms request_neighbour_composable
#print axioms nothing_admitted_beside
#print axioms beside_neighbour_blocked
#print axioms composable_not_monotone
#print axioms tellSource_switchable
#print axioms no_uniformTranslation_presentation
#print axioms no_uniformTranslation_rhoCalc
#print axioms no_uniformTranslation_rho
#print axioms no_uniformTranslation_bag

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.PositiveTell
