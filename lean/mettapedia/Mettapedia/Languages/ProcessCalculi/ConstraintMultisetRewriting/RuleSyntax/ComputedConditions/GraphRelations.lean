import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions.GraphRuns

/-!
# Conditions over relations, at their graph

A condition `value := f(arguments)` is read here where `f` relates one list of arguments
to any number of values, as an authored relation premise does. The program is the one of
`Syntax`: the rules at points of a ground graph (`specialized`).

* `RelationStep`: a firing by matching whose conditions each hold in their relation.
* `rewritesBy_relations_iff`: rewriting by the program at the graph is that firing.
* `relationCorrespondence`: on the step, one firing for one such firing each way, along
  runs of every length.
* `evalStep_iff_relationStep`, `groundGraph_eq`: evaluation by a function is the instance
  whose relation is the function's graph.

Controls: one call with two values gives two successors and no third
(`Controls.chooser_iff`), and no function gives the same steps (`Controls.not_a_function`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions

open Mettapedia.Logic.LP
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (equalityGSLT)
open NamesOnTheStep (Expr)
open LogicOverTheStep.StepSpan (Succ)
open Presentation.Schematic (Tm SState toTerm inst inst_toTerm equationsOf isGuard vars_toTerm exists_zip_of_mem)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Machines (ReadsBag Rewrites)

/-- For each name, which values stand at which arguments. -/
abbrev Relations := ℕ → List Expr → Expr → Prop

/-- The ground rows of the relations. -/
def relationGraph (R : Relations) : Set Tm :=
  {row | ∃ f arguments value, R f arguments value ∧ row = toTerm (groundRow f arguments value)}

/-- **A firing by matching whose conditions hold in their relations.** -/
def RelationStep (R : Relations) (ρ : RuleWithCondition ℕ Tm) (A A' : Multiset Expr) : Prop :=
  ∃ (θ : ℕ → Expr) (rest : Multiset Expr),
    (ρ.rule.body.take.map (inst θ) : Multiset Expr) + rest = A ∧ (∀ q ∈ ρ.rule.body.read, inst θ q ∈ rest) ∧
    (∀ e ∈ equationsOf ρ.rule, inst θ e.1 = inst θ e.2) ∧
    (∀ c ∈ ρ.conditions, R c.name (c.arguments.map (inst θ)) (inst θ c.value)) ∧
    A' = (ρ.rule.body.produce.map (inst θ) : Multiset Expr) + rest

/-- Evaluation by a function is the instance at the function's graph. -/
theorem evalStep_iff_relationStep (I : Interpretation ℕ Expr) (ρ : RuleWithCondition ℕ Tm)
    (A A' : Multiset Expr) :
    EvalStep I ρ A A' ↔ RelationStep (fun f arguments value => I f arguments = some value) ρ A A' :=
  Iff.rfl

theorem groundGraph_eq (I : Interpretation ℕ Expr) :
    groundGraph I = relationGraph (fun f arguments value => I f arguments = some value) :=
  rfl

theorem ground_of_relationGraph {R : Relations} {g : Tm} (onGraph : g ∈ relationGraph R) (y : ℕ) :
    y ∉ g.freeVars := by
  obtain ⟨_, _, _, -, rfl⟩ := onGraph
  exact vars_toTerm _ _

/-- **A firing with related conditions is one rewrite by the rule at points of the graph.** -/
theorem relationStep_iff (R : Relations) (ρ : RuleWithCondition ℕ Tm) (A A' : Multiset Expr) :
    RelationStep R ρ A A' ↔ ∃ points : List Tm, points.length = ρ.conditions.length ∧
      (∀ g ∈ points, g ∈ relationGraph R) ∧ Rewrites [ρ.at rows points] A A' := by
  constructor
  · rintro ⟨θ, rest, split, reads, equations, conditions, out⟩
    refine ⟨ρ.conditions.map fun c => toTerm (groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value)),
      List.length_map _, fun g inside => ?_, ρ.at rows _, List.mem_singleton_self _, θ, rest, split, reads, ?_,
      out⟩
    · obtain ⟨c, inConditions, rfl⟩ := List.mem_map.mp inside
      exact ⟨c.name, _, _, conditions c inConditions, rfl⟩
    · refine (equations_at_iff ρ _ θ).mpr ⟨equations, fun e inside => ?_⟩
      simp only [RuleWithCondition.calls, List.zip_map'] at inside
      obtain ⟨c, -, rfl⟩ := List.mem_map.mp inside
      exact (inst_row θ c.name c.arguments c.value).trans (inst_toTerm θ _).symm
  · rintro ⟨points, lengths, onGraph, r, member, θ, rest, split, reads, equations, out⟩
    obtain rfl := List.mem_singleton.mp member
    obtain ⟨own, calls⟩ := (equations_at_iff ρ points θ).mp equations
    refine ⟨θ, rest, split, reads, own, fun c inConditions => ?_, out⟩
    obtain ⟨g, paired⟩ := exists_zip_of_mem
      (show (ρ.calls rows).length = points.length by rw [RuleWithCondition.calls_length, lengths])
      (show callRow rows c ∈ ρ.calls rows from List.mem_map_of_mem inConditions)
    obtain ⟨f, arguments, value, related, rfl⟩ := onGraph g (List.of_mem_zip paired).2
    have same := calls _ paired
    rw [inst_toTerm] at same
    have row : groundRow c.name (c.arguments.map (inst θ)) (inst θ c.value) = groundRow f arguments value :=
      (inst_row θ c.name c.arguments c.value).symm.trans same
    obtain ⟨rfl, rfl, rfl⟩ := groundRow_inj row
    exact related

/-- The systems of bags under firings with related conditions. -/
def relationEvaluation (R : Relations) (P : Set (RuleWithCondition ℕ Tm)) : GSLT :=
  equalityGSLT (Multiset Expr) (fun A A' => ∃ ρ ∈ P, RelationStep R ρ A A')

section Runs

variable {R : Relations} {P : Set (RuleWithCondition ℕ Tm)}

/-- **Rewriting by the program at the graph.** -/
theorem rewritesBy_relations_iff {A A' : Multiset Expr} :
    RewritesBy (specialized rows (relationGraph R) P) A A' ↔ ∃ ρ ∈ P, RelationStep R ρ A A' := by
  constructor
  · rintro ⟨r, ⟨ρ, inP, points, lengths, onGraph, rfl⟩, single⟩
    exact ⟨ρ, inP, (relationStep_iff R ρ A A').mpr ⟨points, lengths, onGraph, single⟩⟩
  · rintro ⟨ρ, inP, steps⟩
    obtain ⟨points, lengths, onGraph, single⟩ := (relationStep_iff R ρ A A').mp steps
    exact ⟨ρ.at rows points, ⟨ρ, inP, points, lengths, onGraph, rfl⟩, single⟩

theorem relations_fragment (noCollect : ∀ ρ ∈ P, ρ.rule.collect = [])
    (guards : ∀ ρ ∈ P, ρ.rule.body.checks.all isGuard = true) (restricted : ∀ ρ ∈ P, ρ.RangeRestrictedWith) :
    ∀ r ∈ specialized rows (relationGraph R) P, DeterminedPositive r := by
  rintro r ⟨ρ, inP, points, lengths, onGraph, rfl⟩
  exact at_fragment ρ lengths (fun g inside y => ground_of_relationGraph (onGraph g inside) y)
    (noCollect ρ inP) (guards ρ inP) (restricted ρ inP)

/-- **Relation conditions on the step, along runs.** -/
def relationCorrespondence {O : Type} [DecidableEq O] [Infinite O]
    (noCollect : ∀ ρ ∈ P, ρ.rule.collect = []) (guards : ∀ ρ ∈ P, ρ.rule.body.checks.all isGuard = true)
    (restricted : ∀ ρ ∈ P, ρ.RangeRestrictedWith) :
    OperationalCorrespondence (relationEvaluation R P)
      (programSystem O (specialized rows (relationGraph R) P)) where
  related bag s := ReadsBag s bag
  readStep := by
    intro bag s s' reads fired
    rcases (stepCorrespondence (O := O) (relations_fragment noCollect guards restricted)).readStep reads fired with
      same | ⟨bag', rewritten, reads'⟩
    · exact Or.inl same
    · exact Or.inr ⟨bag', rewritesBy_relations_iff.mp rewritten, reads'⟩
  forward := by
    intro bag bag' s reads steps
    exact (stepCorrespondence (O := O) (relations_fragment noCollect guards restricted)).forward reads
      (rewritesBy_relations_iff.mpr steps)

end Runs

/-! ## Controls -/

namespace Controls

private theorem inst_sym (θ : ℕ → Expr) (n : ℕ) : inst θ (.const (.sym n) : Tm) = .sym n := rfl

private theorem inst_var (θ : ℕ → Expr) (x : ℕ) : inst θ (.var x : Tm) = θ x := rfl

/-- One name with the two values `2` and `3`. -/
def twoValues : Relations := fun f arguments value =>
  f = 0 ∧ arguments = [] ∧ (value = .sym 2 ∨ value = .sym 3)

/-- Take `1`, let `x` be a value of the relation, make `x`. -/
def chooser : RuleWithCondition ℕ Tm where
  rule := ⟨PUnit.unit, ⟨[.const (.sym 1)], [], [], [], [.var 0]⟩, []⟩
  conditions := [{ name := 0, arguments := [], value := .var 0 }]

/-- The chooser takes the whole bag `{1}`. -/
private theorem chooser_rest {θ : ℕ → Expr} {rest : Multiset Expr}
    (split : (chooser.rule.body.take.map (inst θ) : Multiset Expr) + rest = {.sym 1}) : rest = 0 :=
  (Multiset.cons_inj_right (Expr.sym 1)).mp (by simpa [inst_sym, chooser] using split)

/-- **Positive and negative**: exactly the two related values are successors. -/
theorem chooser_iff (after : Multiset Expr) :
    RelationStep twoValues chooser {.sym 1} after ↔ after = {.sym 2} ∨ after = {.sym 3} := by
  constructor
  · rintro ⟨θ, rest, split, -, -, conditions, rfl⟩
    obtain rfl := chooser_rest split
    have related := conditions _ (List.mem_singleton_self _)
    rcases related.2.2 with two | three
    · exact Or.inl (by simpa [inst_var, chooser] using two)
    · exact Or.inr (by simpa [inst_var, chooser] using three)
  · have fires : ∀ n, (n = 2 ∨ n = 3) → RelationStep twoValues chooser {.sym 1} {.sym n} := fun n valued =>
      ⟨fun _ => .sym n, 0, by simp [inst_sym, chooser], by simp [chooser], by simp [chooser, equationsOf],
        by simpa [inst_var, chooser, twoValues] using valued, by simp [inst_var, chooser]⟩
    rintro (rfl | rfl)
    · exact fires 2 (Or.inl rfl)
    · exact fires 3 (Or.inr rfl)

/-- **The generalization is needed**: no function has these steps. -/
theorem not_a_function (I : Interpretation ℕ Expr) :
    ¬ ∀ after, EvalStep I chooser {.sym 1} after ↔ RelationStep twoValues chooser {.sym 1} after := by
  intro same
  have value : ∀ n : ℕ, EvalStep I chooser {.sym 1} {.sym n} → I 0 [] = some (.sym n) := by
    rintro n ⟨θ, rest, split, -, -, conditions, out⟩
    obtain rfl := chooser_rest split
    have made : θ 0 = .sym n := by simpa [inst_var, chooser, eq_comm] using out
    simpa [inst_var, made] using conditions _ (List.mem_singleton_self _)
  have two := value 2 ((same _).mpr ((chooser_iff _).mpr (Or.inl rfl)))
  have three := value 3 ((same _).mpr ((chooser_iff _).mpr (Or.inr rfl)))
  simp [two] at three

end Controls

#print axioms relationStep_iff
#print axioms relationCorrespondence
#print axioms Controls.chooser_iff
#print axioms Controls.not_a_function

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ComputedConditions
