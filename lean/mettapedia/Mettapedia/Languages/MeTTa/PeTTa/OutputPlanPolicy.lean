import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanCompiler

/-!
# Runtime branch constraints do not add compiler-time aliases

The alternative policy emits literal equations before the selected branch's
goals. Its compiler leaves the incoming alias relation unchanged, rather than
merging source inputs while assembling different alternatives. Runtime
unification remains meaningful; this is not an erasure of branch constraints.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem branch_runtime (supply : Supply) (plan : Plan) (output : Atom) :
    branch supply plan output .runtimeConstraints = some (supply,equate plan.output output plan.goals) := rfl

theorem visitMany_aliases (visit : Supply → Atom → Option Result)
    (preserves : ∀ supply expression result, visit supply expression = some result →
      result.supply.aliases = supply.aliases)
    (held : Nat → Bool) (input : List Atom) :
    ∀ supply index result, visitMany visit held supply index input = some result →
      result.supply.aliases = supply.aliases := by
  induction input with
  | nil =>
      intro supply index result computed
      simp only [visitMany,Option.some.injEq] at computed
      subst result
      rfl
  | cons first rest ih =>
      intro supply index result computed
      cases demand : held index
      · simp only [visitMany,demand,Bool.false_eq_true,↓reduceIte,bind,pure,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨entry,entered,later,tail,rfl⟩ := computed
        exact (ih entry.supply (index + 1) later tail).trans (preserves supply first entry entered)
      · simp only [visitMany,demand,↓reduceIte,bind,pure,Option.bind_some,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨later,tail,rfl⟩ := computed
        exact ih supply (index + 1) later tail

theorem branches_runtime_aliases (input : List Plan) :
    ∀ supply output result, branches .runtimeConstraints supply input output = some result →
      result.1.aliases = supply.aliases := by
  induction input with
  | nil =>
      intro supply output result computed
      simp only [branches,Option.some.injEq] at computed
      subst result
      rfl
  | cons first rest ih =>
      intro supply output result computed
      simp only [branches,branch_runtime,bind,pure,Option.bind_some,
        Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨later,tail,rfl⟩ := computed
      exact ih supply output later tail

theorem letBindings_aliases (visit : Supply → Atom → Option Result)
    (preserves : ∀ supply expression result, visit supply expression = some result →
      result.supply.aliases = supply.aliases) (rows : List Atom) :
    ∀ supply body result, letBindings visit supply rows body = some result →
      result.supply.aliases = supply.aliases := by
  induction rows with
  | nil => intro supply body result computed; cases computed
  | cons first rest ih =>
      intro supply body result computed
      rw [letBindings] at computed
      cases rest with
      | nil =>
          simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨parts,parsed,p,pattern,v,value,b,bodyComputed,rfl⟩ := computed
          exact (preserves v.supply body b bodyComputed).trans
            ((preserves p.supply parts.2 v value).trans (preserves supply parts.1 p pattern))
      | cons second more =>
          simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨parts,parsed,p,pattern,v,value,b,bodyComputed,rfl⟩ := computed
          exact (ih v.supply body b bodyComputed).trans
            ((preserves p.supply parts.2 v value).trans (preserves supply parts.1 p pattern))

theorem caseBranches_runtime_aliases (visit : Supply → Atom → Option Result)
    (preserves : ∀ supply expression result, visit supply expression = some result →
      result.supply.aliases = supply.aliases)
    (context : Context) (policy : context.branchPolicy = .runtimeConstraints)
    (rows : SpaceSemantics.Cases) :
    ∀ supply output result, caseBranches visit context supply rows output = some result →
      result.1.aliases = supply.aliases := by
  induction rows with
  | nil =>
      intro supply output result computed
      simp only [caseBranches,Option.some.injEq] at computed
      subst result
      rfl
  | cons row rest ih =>
      rcases row with ⟨pattern,body⟩
      intro supply output result computed
      simp only [caseBranches] at computed
      split at computed
      · cases computed
      · simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨compiled,bodyComputed,selected,branchComputed,later,tail,rfl⟩ := computed
        rw [policy,branch_runtime] at branchComputed
        cases branchComputed
        exact (ih compiled.supply output later tail).trans (preserves _ _ _ bodyComputed)

theorem perform_runtime_aliases (context : Context) (policy : context.branchPolicy = .runtimeConstraints)
    (visit : Supply → Atom → Option Result)
    (preserves : ∀ supply expression result, visit supply expression = some result →
      result.supply.aliases = supply.aliases)
    (supply : Supply) (shape : Shape) (result : Result)
    (computed : perform context visit supply shape = some result) :
    result.supply.aliases = supply.aliases := by
  cases shape with
  | value | quoted | empty =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      rfl
  | unsupported => cases computed
  | bindings rows body => exact letBindings_aliases visit preserves rows supply body result computed
  | binding pattern value body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨p,patternComputed,v,valueComputed,b,bodyComputed,rfl⟩ := computed
      exact (preserves v.supply body b bodyComputed).trans
        ((preserves p.supply value v valueComputed).trans (preserves supply pattern p patternComputed))
  | alternatives values =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,children,selected,selectedComputed,rfl⟩ := computed
      rw [policy] at selectedComputed
      exact (branches_runtime_aliases compiled.plans compiled.supply supply.fresh.2 selected selectedComputed).trans
        (visitMany_aliases visit preserves (fun _ => false) values supply.fresh.1 0 compiled children)
  | collection body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨child,childComputed,rfl⟩ := computed
      exact preserves supply body child childComputed
  | first body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨child,childComputed,rfl⟩ := computed
      exact preserves supply body child childComputed
  | condition condition yes no =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨tested,testedComputed,yesPlan,yesComputed,noPlan,noComputed,
        yesGoal,yesGoalComputed,noGoal,noGoalComputed,rfl⟩ := computed
      rw [policy,branch_runtime] at yesGoalComputed
      cases yesGoalComputed
      rw [policy,branch_runtime] at noGoalComputed
      cases noGoalComputed
      exact (preserves yesPlan.supply no noPlan noComputed).trans
        ((preserves tested.supply.fresh.1 yes yesPlan yesComputed).trans
          (preserves supply condition tested testedComputed))
  | selection key rows =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨parsed,parsedComputed,selected,keyComputed,compiled,rowsComputed,rfl⟩ := computed
      exact (caseBranches_runtime_aliases visit preserves context policy parsed
        selected.supply.fresh.1 selected.supply.fresh.2 compiled rowsComputed).trans
          (preserves supply key selected keyComputed)
  | query location pattern body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨space,spaceComputed,bodyPlan,bodyComputed,rfl⟩ := computed
      exact (preserves space.supply body bodyPlan bodyComputed).trans
        (preserves supply location space spaceComputed)
  | groundedApplication head arguments =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,children,rfl⟩ := computed
      exact visitMany_aliases visit preserves (fun _ => false) arguments supply 0 compiled children
  | listApplication head arguments =>
      simp only [perform,bind,Option.bind_eq_some_iff] at computed
      obtain ⟨first,headComputed,compiled,children,remaining⟩ := computed
      cases output : first.plan.output with
      | var name | symbol name | grounded value => simp only [output] at remaining; cases remaining
      | expression values =>
          simp only [output] at remaining
          split at remaining
          · simp only [Option.some.injEq] at remaining
            subst result
            exact (visitMany_aliases visit preserves (fun _ => false) arguments first.supply 0 compiled children).trans
              (preserves supply (.expression head) first headComputed)
          · cases remaining
  | application head arguments =>
      simp only [perform,bind,Option.bind_eq_some_iff] at computed
      obtain ⟨compiled,children,remaining⟩ := computed
      have unchanged := visitMany_aliases visit preserves
        (if context.callable head then Eval.argumentIsRaw context.source head else fun _ => false)
        arguments supply 0 compiled children
      split at remaining
      · simp only [pure,Option.bind_eq_some_iff,Option.some.injEq] at remaining
        obtain ⟨mode,modeComputed,rfl⟩ := remaining
        exact unchanged
      · split at remaining
        · simp only [Option.some.injEq] at remaining
          subst result
          exact unchanged
        · split at remaining
          · cases remaining
          · simp only [Option.some.injEq] at remaining
            subst result
            exact unchanged

theorem compile_runtime_aliases (context : Context) (policy : context.branchPolicy = .runtimeConstraints) :
    ∀ depth supply expression result, compile context depth supply expression = some result →
      result.supply.aliases = supply.aliases := by
  intro depth
  induction depth with
  | zero => intro supply expression result computed; cases computed
  | succ depth ih =>
      intro supply expression result computed
      exact perform_runtime_aliases context policy (compile context depth) ih supply
        (classify expression) result computed

/-- The alternative compiler retains the authored argument patterns. It adds
its output formal without merging distinct source inputs at compile time. -/
theorem compiled_runtime_formals (context : Context) (policy : context.branchPolicy = .runtimeConstraints)
    (equation target : SpaceSemantics.Equation)
    (compiled : compileEquation context equation = some target) :
    ∃ outputName, target.arguments = equation.arguments ++ [.var outputName] := by
  simp only [compileEquation] at compiled
  split at compiled
  · cases compiled
  · simp only [bind,Option.bind_eq_some_iff] at compiled
    obtain ⟨signature,found,body⟩ := compiled
    cases raw : rawOutput context.source equation.head equation.arguments.length with
    | true =>
        simp only [raw,↓reduceIte,Supply.fresh,Option.bind_some,Option.some.injEq] at body
        subst target
        refine ⟨Mettapedia.FreshString.fresh (Supply.start (equation.body :: equation.arguments)).used,?_⟩
        change equation.arguments.map (Supply.start (equation.body :: equation.arguments)).normalize ++ _ = _
        have normal : (Supply.start (equation.body :: equation.arguments)).normalize = id := by
          funext term
          exact Unifying.resolve_of_unbound term (by intro name present; rfl)
        rw [normal,List.map_id]
    | false =>
        simp only [raw,Bool.false_eq_true,↓reduceIte,Option.bind_eq_some_iff] at body
        obtain ⟨result,bodyComputed,finished⟩ := body
        have unchanged : result.supply.aliases = [] :=
          compile_runtime_aliases context policy _ _ _ _ bodyComputed
        simp only [Supply.fresh,Option.some.injEq] at finished
        subst target
        refine ⟨Mettapedia.FreshString.fresh result.supply.used,?_⟩
        have normal : result.supply.normalize = id := by
          funext term
          change Unifying.resolve result.supply.aliases term = term
          rw [unchanged]
          exact Unifying.resolve_of_unbound term (by intro name present; rfl)
        change equation.arguments.map result.supply.normalize ++ _ = equation.arguments ++ _
        rw [normal,List.map_id]

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
