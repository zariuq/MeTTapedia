import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.Runs

/-!
# The program at the graph along runs

`Runs` states what the evaluated program does along runs. This module states the same of the program at the
ground graph of the interpretation (`specialized rows (groundGraph I) P`), whose rules hold the points and tell
each call row equal to its point.

* `at_fragment`: the rule at ground points is in the wider fragment of `Determined` when the rule has no collect query
  pattern, only equation checks, and every written unknown bound by matching or by a condition's value. The
  unknowns of a condition's arguments are determined by the tell of the call row, so nothing is asked of the
  arguments (the evaluated rule needs them anchored).
* `graphStep_iff`, `rewritesBy_graph_iff`: rewriting of a bag by the program at the graph is the atomic
  evaluation of a rule of the program.
* `graphCorrespondence`: the program at the graph and the atomic evaluation on bags, one firing for one
  evaluation each way, related by reading a state as a bag.
* `graph_run_to_evaluated`, `evaluated_run_to_graph`: the program at the graph and the evaluated program have
  runs between states that read as the same bags.
* `graph_to_evaluated_along_run`: at every state a run of the evaluated program reaches from a state that
  reads as a bag, the admitted firings of the program at the graph are the point firings of the admitted
  evaluated firings, with the same choices.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation.Schematic (Tm SRule SState X E rowSig toTerm inst inst_toTerm equationsOf written isGuard
  vars_toTerm exists_zip_of_mem mem_written_of_produce)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (Reads ReadsBag Rewrites)

/-- A row of the ground graph holds no unknown. -/
theorem ground_of_graph {I : Interpretation ℕ Expr} {g : Tm} (onGraph : g ∈ groundGraph I) (y : ℕ) :
    y ∉ g.freeVars := by
  obtain ⟨f, args, value, -, rfl⟩ := onGraph
  exact vars_toTerm _ _

section Fragment

variable (ρ : RuleWithCondition ℕ Tm) {points : List Tm}

/-- **What the rule at ground points determines**: what the rule binds by matching, and every unknown of the
value and of the arguments of a condition. -/
theorem at_determines (lengths : points.length = ρ.conditions.length)
    (ground : ∀ g ∈ points, ∀ y : ℕ, y ∉ g.freeVars) {x : ℕ}
    (known : Presentation.Schematic.Bound ρ.rule x ∨ ∃ c ∈ ρ.conditions, x ∈ (callRow rows c).freeVars) :
    Determines (ρ.at rows points) x := by
  rcases known with bound | ⟨c, inConditions, inCall⟩
  · exact .bound bound
  · obtain ⟨g, paired⟩ := exists_zip_of_mem
      (show (ρ.calls rows).length = points.length by rw [RuleWithCondition.calls_length, lengths])
      (show callRow rows c ∈ ρ.calls rows from List.mem_map_of_mem inConditions)
    have told : (callRow rows c, g) ∈ (ρ.at rows points).body.tell := List.mem_append_left _ paired
    exact .toldLeft told (fun y vars => absurd vars (ground g (List.of_mem_zip paired).2 y)) inCall

/-- **The rule at ground points is in the wider fragment**, with nothing asked of the arguments. -/
theorem at_fragment (lengths : points.length = ρ.conditions.length)
    (ground : ∀ g ∈ points, ∀ y : ℕ, y ∉ g.freeVars) (noCollect : ρ.rule.collect = [])
    (guards : ρ.rule.body.checks.all isGuard = true) (restricted : ρ.RangeRestrictedWith) :
    DeterminedPositive (ρ.at rows points) := by
  refine ⟨noCollect, guards, fun t inside x vars => ?_⟩
  have cases : t ∈ written ρ.rule ∨ t ∈ ((ρ.calls rows).zip points).map Prod.fst ∨
      t ∈ ((ρ.calls rows).zip points).map Prod.snd := by
    simp only [written, RuleWithCondition.at_tell, RuleWithCondition.at_checks, RuleWithCondition.at_produce,
      List.map_append, List.mem_append] at inside ⊢
    tauto
  rcases cases with own | call | point
  · rcases restricted t own x vars with bound | ⟨c, inConditions, inValue⟩
    · exact at_determines ρ lengths ground (.inl bound)
    · exact at_determines ρ lengths ground (.inr ⟨c, inConditions, (mem_vars_callRow c).mpr (.inr inValue)⟩)
  · obtain ⟨pair, inZip, rfl⟩ := List.mem_map.mp call
    obtain ⟨c, inConditions, isCall⟩ := List.mem_map.mp (List.of_mem_zip inZip).1
    rw [← isCall] at vars
    exact at_determines ρ lengths ground (.inr ⟨c, inConditions, vars⟩)
  · obtain ⟨pair, inZip, rfl⟩ := List.mem_map.mp point
    exact absurd vars (ground _ (List.of_mem_zip inZip).2 x)

/-- **The equations of the rule at points hold at an instantiation** exactly when the rule's own do and each
call row's instance is its point's. -/
theorem equations_at_iff (points : List Tm) (θ : ℕ → Expr) :
    (∀ e ∈ equationsOf (ρ.at rows points), inst θ e.1 = inst θ e.2) ↔
      (∀ e ∈ equationsOf ρ.rule, inst θ e.1 = inst θ e.2) ∧
      ∀ e ∈ (ρ.calls rows).zip points, inst θ e.1 = inst θ e.2 := by
  simp only [equationsOf, RuleWithCondition.at_tell, RuleWithCondition.at_checks, List.forall_mem_append]
  tauto

end Fragment

/-- **The atomic evaluation of a rule is one rewrite of the bag by the rule at points of the ground graph.** -/
theorem graphStep_iff (I : Interpretation ℕ Expr) (ρ : RuleWithCondition ℕ Tm) (B B' : Multiset Expr) :
    EvalStep I ρ B B' ↔ ∃ points : List Tm, points.length = ρ.conditions.length ∧
      (∀ g ∈ points, g ∈ groundGraph I) ∧ Rewrites [ρ.at rows points] B B' := by
  constructor
  · rintro ⟨θ, rest, split, reads, equations, conditions, out⟩
    refine ⟨ρ.conditions.map fun c => toTerm (groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value)),
      List.length_map _, fun g inside => ?_, ρ.at rows _, List.mem_singleton_self _, θ, rest, split, reads, ?_,
      out⟩
    · obtain ⟨c, inConditions, rfl⟩ := List.mem_map.mp inside
      exact ⟨c.name, _, _, conditions c inConditions, rfl⟩
    · refine (equations_at_iff ρ _ θ).mpr ⟨equations, fun e inside => ?_⟩
      have zipped : (ρ.calls rows).zip
          (ρ.conditions.map fun c => toTerm (groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value))) =
          ρ.conditions.map fun c =>
            (callRow rows c, toTerm (groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value))) := by
        simp only [RuleWithCondition.calls, List.zip_map']
      rw [zipped] at inside
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp inside
      exact (inst_row θ c.name c.arguments c.value).trans (inst_toTerm θ _).symm
  · rintro ⟨points, lengths, onGraph, r, member, θ, rest, split, reads, equations, out⟩
    obtain rfl := List.mem_singleton.mp member
    obtain ⟨own, calls⟩ := (equations_at_iff ρ points θ).mp equations
    refine ⟨θ, rest, split, reads, own, fun c inConditions => ?_, out⟩
    obtain ⟨g, paired⟩ := exists_zip_of_mem
      (show (ρ.calls rows).length = points.length by rw [RuleWithCondition.calls_length, lengths])
      (show callRow rows c ∈ ρ.calls rows from List.mem_map_of_mem inConditions)
    obtain ⟨f, args, value, answers, rfl⟩ := onGraph g (List.of_mem_zip paired).2
    have same := calls _ paired
    rw [inst_toTerm] at same
    have row : groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) = groundRow f args value :=
      (inst_row θ c.name c.arguments c.value).symm.trans same
    obtain ⟨rfl, rfl, rfl⟩ := groundRow_inj row
    exact answers

section Runs

variable {O : Type} [DecidableEq O] {I : Interpretation ℕ Expr} {P : Set (RuleWithCondition ℕ Tm)}

/-- **Rewriting of a bag by the program at the graph is the atomic evaluation of a rule of the program.** -/
theorem rewritesBy_graph_iff {B B' : Multiset Expr} :
    RewritesBy (specialized rows (groundGraph I) P) B B' ↔ ∃ ρ ∈ P, EvalStep I ρ B B' := by
  constructor
  · rintro ⟨r, ⟨ρ, inP, points, lengths, onGraph, rfl⟩, single⟩
    exact ⟨ρ, inP, (graphStep_iff I ρ B B').mpr ⟨points, lengths, onGraph, single⟩⟩
  · rintro ⟨ρ, inP, evaluates⟩
    obtain ⟨points, lengths, onGraph, single⟩ := (graphStep_iff I ρ B B').mp evaluates
    exact ⟨ρ.at rows points, ⟨ρ, inP, points, lengths, onGraph, rfl⟩, single⟩

/-- **The rules of the program at the ground graph are in the wider fragment.** -/
theorem specialized_fragment (noCollect : ∀ ρ ∈ P, ρ.rule.collect = [])
    (guards : ∀ ρ ∈ P, ρ.rule.body.checks.all isGuard = true) (restricted : ∀ ρ ∈ P, ρ.RangeRestrictedWith) :
    ∀ r ∈ specialized rows (groundGraph I) P, DeterminedPositive r := by
  rintro r ⟨ρ, inP, points, lengths, onGraph, rfl⟩
  exact at_fragment ρ lengths (fun g inside y => ground_of_graph (onGraph g inside) y) (noCollect ρ inP)
    (guards ρ inP) (restricted ρ inP)

/-- **The program at the graph and the atomic evaluation on bags, along runs**: one firing for one evaluation
each way, related by reading a state as a bag. -/
def graphCorrespondence [Infinite O] (noCollect : ∀ ρ ∈ P, ρ.rule.collect = [])
    (guards : ∀ ρ ∈ P, ρ.rule.body.checks.all isGuard = true) (restricted : ∀ ρ ∈ P, ρ.RangeRestrictedWith) :
    OperationalCorrespondence (evaluation I P) (programSystem O (specialized rows (groundGraph I) P)) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads stepped
    obtain ⟨f, admitted, rfl⟩ := stepped
    obtain ⟨bag', rewrites, reads'⟩ := readsBag_backward_determined reads f admitted
      (makesDetermined_of_writes (specialized_fragment noCollect guards restricted f.rule f.member).2.2)
    exact Or.inr ⟨bag', rewritesBy_graph_iff.mp ⟨f.rule, f.member, rewrites⟩, reads'⟩
  forward := by
    intro bag bag' s reads evaluates
    obtain ⟨r, member, single⟩ := rewritesBy_graph_iff.mpr evaluates
    obtain ⟨f, admitted, -, reads'⟩ := readsBag_forward_determined member
      (specialized_fragment noCollect guards restricted r member) reads single
    exact ⟨_, (executionPath_nonempty_iff_multiStep (programSystem O (specialized rows (groundGraph I) P)) _ _).mpr
      (.step ⟨f, admitted, rfl⟩ (.refl _)), reads'⟩

/-- **Every run of the program at the graph is matched by the evaluated program**, between states that read as
the same bags. -/
theorem graph_run_to_evaluated [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s s' : SState O}
    {B : Multiset Expr} (reads : ReadsBag s B)
    (run : (programSystem O (specialized rows (groundGraph I) P)).MultiStep s s') :
    ∃ B' : Multiset Expr, ReadsBag s' B' ∧ (evaluation I P).MultiStep B B' ∧
      ∀ t : SState O, ReadsBag t B →
        ∃ t', (programSystem O (evaluated I P)).MultiStep t t' ∧ ReadsBag t' B' := by
  obtain ⟨(B' : Multiset Expr), bagRun, reads'⟩ :=
    (graphCorrespondence (O := O) (I := I) (fun ρ inP => (evaluable ρ inP).noCollect)
      (fun ρ inP => (evaluable ρ inP).guards)
      (fun ρ inP => (evaluable ρ inP).restricted)).toOperationalReadback.reflectMultiStep reads run
  exact ⟨B', reads', bagRun, fun t readsT => (evaluatedCorrespondence (O := O) evaluable).liftMultiStep readsT bagRun⟩

/-- **Every run of the evaluated program is matched by the program at the graph**, between states that read as
the same bags. -/
theorem evaluated_run_to_graph [Infinite O] (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s s' : SState O}
    {B : Multiset Expr} (reads : ReadsBag s B) (run : (programSystem O (evaluated I P)).MultiStep s s') :
    ∃ B' : Multiset Expr, ReadsBag s' B' ∧ (evaluation I P).MultiStep B B' ∧
      ∀ t : SState O, ReadsBag t B →
        ∃ t', (programSystem O (specialized rows (groundGraph I) P)).MultiStep t t' ∧ ReadsBag t' B' := by
  obtain ⟨(B' : Multiset Expr), bagRun, reads'⟩ :=
    (evaluatedCorrespondence (O := O) (I := I) evaluable).toOperationalReadback.reflectMultiStep reads run
  exact ⟨B', reads', bagRun, fun t readsT =>
    (graphCorrespondence (O := O) (I := I) (fun ρ inP => (evaluable ρ inP).noCollect)
      (fun ρ inP => (evaluable ρ inP).guards)
      (fun ρ inP => (evaluable ρ inP).restricted)).liftMultiStep readsT bagRun⟩

/-- **Along every run of the evaluated program from a state that reads as a bag, the two programs admit the
same firings with the same choices**: at every state the run reaches, every admitted firing of the program at
the graph is the point firing of an admitted evaluated firing. The converse holds at every state
(`evaluated_to_graph`). -/
theorem graph_to_evaluated_along_run (evaluable : ∀ ρ ∈ P, ρ.Evaluable) {s t : SState O}
    (run : Relation.ReflTransGen (Succ (step X O E (evaluated I P)).toStep) s t)
    (reads : ∃ bag, ReadsBag s bag) (h : Firing O E (specialized rows (groundGraph I) P) PUnit.unit)
    (admitted : (step X O E (specialized rows (groundGraph I) P)).Admits (s := t) h) :
    ∃ (ρ : RuleWithCondition ℕ Tm) (pts : List EvalPoint) (c : Choice O (Subst rowSig))
      (mE : ρ.evalAt pts ∈ evaluated I P)
      (mP : ρ.at rows (ρ.pointRows pts) ∈ specialized rows (groundGraph I) P),
      ρ ∈ P ∧ h = pointFiring (A := Presentation.Schematic.A) ρ (ρ.pointRows pts) mP c ∧
      (step X O E (evaluated I P)).Admits (s := t) (evalFiring ρ pts mE c) := by
  obtain ⟨bag, rowsOf, readsT, -⟩ := evaluated_run_reads (fun ρ inP t inProduce x vars =>
    (evaluable ρ inP).restricted t (mem_written_of_produce inProduce) x vars) run reads
  exact graph_to_evaluated (fun ρ inP => (evaluable ρ inP).anchored) readsT h admitted

end Runs

#print axioms graph_to_evaluated_along_run
#print axioms at_fragment
#print axioms graphStep_iff
#print axioms rewritesBy_graph_iff
#print axioms specialized_fragment
#print axioms graphCorrespondence
#print axioms graph_run_to_evaluated
#print axioms evaluated_run_to_graph

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
