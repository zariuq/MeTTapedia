import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormationCorrect
import Mettapedia.Data.List.OptionMapMReflection

/-!
# Equation and program formation for result-passing compilation

Ordered source equations and directives receive their own derivations.
Literal Atom return declarations hold the body; other admitted bodies use
the recursive expression rules. Compilation preserves and reflects these
rules without silently dropping an equation or directive. This remains
formation correctness, not a whole-source execution theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive ExpressionRel (context : Context) (expression : Atom) : Plan → Prop where
  | formed (result : Result)
      (body : FormationAt context (LambdaStaging.depthOf expression * 2 + 2)
        (Supply.start [expression]) expression result) :
      ExpressionRel context expression (normalized result)

theorem expression_iff (context : Context) (expression : Atom) (plan : Plan) :
    compileExpression context expression = some plan ↔ ExpressionRel context expression plan := by
  constructor
  · intro computed
    simp only [compileExpression,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
    obtain ⟨result,formed,rfl⟩ := computed
    exact .formed result ((compile_iff _ _ _ _ _).mp formed)
  · intro rule
    cases rule with
    | formed result body =>
        simp only [compileExpression,(compile_iff _ _ _ _ _).mpr body,bind,pure,Option.bind_some]

inductive EquationBodyRel (context : Context) (equation : SpaceSemantics.Equation) : Result → Prop where
  | held (raw : rawOutput context.source equation.head equation.arguments.length = true) :
      EquationBodyRel context equation
        ⟨Supply.start (equation.body :: equation.arguments),Plan.value equation.body⟩
  | evaluated (result : Result)
      (notRaw : rawOutput context.source equation.head equation.arguments.length = false)
      (body : FormationAt context (LambdaStaging.depthOf equation.body * 2 + 2)
        (Supply.start (equation.body :: equation.arguments)) equation.body result) :
      EquationBodyRel context equation result

inductive EquationRel (context : Context) (equation : SpaceSemantics.Equation) : SpaceSemantics.Equation → Prop where
  | formed (signature : Signature) (result : Result)
      (passive : equation.arguments.all (passivePattern context) = true)
      (lookup : context.lookup equation.head equation.arguments.length = some signature)
      (body : EquationBodyRel context equation result) :
      EquationRel context equation
        (procedure signature.target (equation.arguments.map result.supply.normalize)
          (Mettapedia.FreshString.fresh result.supply.used) (normalized result))

theorem equation_has_rule (context : Context) (equation target : SpaceSemantics.Equation)
    (computed : compileEquation context equation = some target) : EquationRel context equation target := by
  cases passive : equation.arguments.all (passivePattern context)
  · simp [compileEquation,passive] at computed
  · simp only [compileEquation,passive,Bool.not_true,Bool.false_eq_true,↓reduceIte,
      bind,Option.bind_eq_some_iff] at computed
    obtain ⟨signature,lookup,computed⟩ := computed
    cases raw : rawOutput context.source equation.head equation.arguments.length
    · simp only [raw,Bool.false_eq_true,↓reduceIte,Option.bind_eq_some_iff] at computed
      obtain ⟨result,body,computed⟩ := computed
      simp only [Supply.fresh,Option.some.injEq] at computed
      subst target
      exact .formed signature result passive lookup (.evaluated result raw ((compile_iff _ _ _ _ _).mp body))
    · simp only [raw,↓reduceIte,Option.bind_some,Supply.fresh,Option.some.injEq] at computed
      subst target
      exact .formed signature _ passive lookup (.held raw)

theorem equation_of_rule {context : Context} {equation target : SpaceSemantics.Equation}
    (rule : EquationRel context equation target) : compileEquation context equation = some target := by
  cases rule with
  | formed signature result passive lookup body =>
      cases body with
      | held raw =>
          simp only [compileEquation,passive,Bool.not_true,Bool.false_eq_true,↓reduceIte,
            lookup,raw,bind,Option.bind_some,Supply.fresh]
      | evaluated result notRaw body =>
          simp only [compileEquation,passive,Bool.not_true,Bool.false_eq_true,↓reduceIte,
            lookup,notRaw,(compile_iff _ _ _ _ _).mpr body,bind,Option.bind_some,Supply.fresh]

theorem equation_iff (context : Context) (equation target : SpaceSemantics.Equation) :
    compileEquation context equation = some target ↔ EquationRel context equation target :=
  ⟨equation_has_rule context equation target,equation_of_rule⟩

theorem equation_head_lookup {context : Context} {equation target : SpaceSemantics.Equation}
    (rule : EquationRel context equation target) :
    (context.lookup equation.head equation.arguments.length).map Signature.target = some target.head := by
  cases rule with
  | formed signature result passive lookup body => simp only [lookup,Option.map_some,procedure]

inductive ProgramRel (source : SpaceSemantics.Program) (policy : BranchPolicy) : Program → Prop where
  | formed (code : List SpaceSemantics.Equation) (plans : List Plan)
      (equations : List.Forall₂ (EquationRel (Context.ofProgram source policy)) source.equations code)
      (directives : List.Forall₂ (ExpressionRel (Context.ofProgram source policy)) source.initializers plans) :
      ProgramRel source policy ⟨source,Context.ofProgram source policy,code,plans.map Plan.execute⟩

theorem program_iff (source : SpaceSemantics.Program) (policy : BranchPolicy) (target : Program) :
    compileProgram source policy = some target ↔ ProgramRel source policy target := by
  constructor
  · intro computed
    simp only [compileProgram,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
    obtain ⟨code,equations,plans,directives,rfl⟩ := computed
    exact .formed code plans
      ((Mettapedia.Data.List.option_mapM_relation _ _ (equation_iff _) _ _).mp equations)
      ((Mettapedia.Data.List.option_mapM_relation _ _ (expression_iff _) _ _).mp directives)
  · intro rule
    cases rule with
    | formed code plans equations directives =>
        have codeComputed := (Mettapedia.Data.List.option_mapM_relation _ _ (equation_iff _) _ _).mpr equations
        have plansComputed := (Mettapedia.Data.List.option_mapM_relation _ _ (expression_iff _) _ _).mpr directives
        simp only [compileProgram,codeComputed,plansComputed,bind,pure,Option.bind_some]

theorem program_retains_source {source : SpaceSemantics.Program} {policy : BranchPolicy} {target : Program}
    (rule : ProgramRel source policy target) : target.source = source := by
  cases rule
  rfl

theorem program_equation_count {source : SpaceSemantics.Program} {policy : BranchPolicy} {target : Program}
    (rule : ProgramRel source policy target) : target.code.length = source.equations.length := by
  cases rule with
  | formed code plans equations directives => exact equations.length_eq.symm

theorem program_directive_count {source : SpaceSemantics.Program} {policy : BranchPolicy} {target : Program}
    (rule : ProgramRel source policy target) : target.queries.length = source.initializers.length := by
  cases rule with
  | formed code plans equations directives => simpa only [List.length_map] using directives.length_eq.symm

theorem program_interface_order {source : SpaceSemantics.Program} {policy : BranchPolicy} {target : Program}
    (rule : ProgramRel source policy target) :
    source.equations.map (fun equation =>
        ((Context.ofProgram source policy).lookup equation.head equation.arguments.length).map Signature.target) =
      target.code.map (fun equation => some equation.head) := by
  cases rule with
  | formed code plans equations directives =>
      generalize source.equations = inputs at equations ⊢
      induction equations with
      | nil => rfl
      | cons head tail ih => simp only [List.map_cons,equation_head_lookup head,ih]

/-- Carry the actual formation derivation with a successfully compiled
program. The proof is erased by execution; it certifies formation only. -/
def compileWithFormation (source : SpaceSemantics.Program) (policy : BranchPolicy := .swiAliases) :
    Option {target : Program // ProgramRel source policy target} :=
  match computed : compileProgram source policy with
  | none => none
  | some target => some ⟨target,(program_iff source policy target).mp computed⟩

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
