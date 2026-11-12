import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanFormation

/-!
# Structural compiler preservation and reflection

Every successful compilation has a derivation of the explicit formation
rules, and every such bounded derivation is computed. This establishes the
compiler/rule connection without a whole-source evaluator oracle. It is not
yet the operational simulation of these plans against source execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem arguments_has_rule (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result → child supply expression result) :
    ∀ held input supply index result,
      visitMany visit held supply index input = some result → ArgumentsRel child held supply index input result := by
  intro held input
  induction input with
  | nil =>
      intro supply index result computed
      simp only [visitMany,Option.some.injEq] at computed
      subst result
      exact .nil supply index
  | cons first rest ih =>
      intro supply index result computed
      cases demand : held index
      · simp only [visitMany,demand,Bool.false_eq_true,↓reduceIte,bind,pure,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨entered,head,later,tail,rfl⟩ := computed
        exact .evaluatedArgument supply index first rest entered later demand
          (children _ _ _ head) (ih entered.supply (index + 1) later tail)
      · simp only [visitMany,demand,↓reduceIte,bind,pure,Option.bind_some,
          Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨later,tail,rfl⟩ := computed
        exact .heldArgument supply index first rest later demand (ih supply (index + 1) later tail)

theorem arguments_of_rule (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, child supply expression result → visit supply expression = some result) :
    ∀ held supply index input result,
      ArgumentsRel child held supply index input result → visitMany visit held supply index input = some result := by
  intro held supply index input result derivation
  induction derivation with
  | nil supply index => rfl
  | heldArgument supply index first rest later demand tail ih =>
      simp only [visitMany,demand,↓reduceIte,bind,pure,Option.bind_some,ih]
  | evaluatedArgument supply index first rest entered later demand head tail ih =>
      simp only [visitMany,demand,Bool.false_eq_true,↓reduceIte,bind,pure,
        children _ _ _ head,Option.bind_some,ih]

theorem arguments_iff (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result ↔ child supply expression result)
    (held : Nat → Bool) (input : List Atom) (supply : Supply) (index : Nat) (result : Results) :
    visitMany visit held supply index input = some result ↔ ArgumentsRel child held supply index input result :=
  ⟨arguments_has_rule visit child (fun s e r h => (children s e r).mp h) held input supply index result,
   arguments_of_rule visit child (fun s e r h => (children s e r).mpr h) held supply index input result⟩

theorem bindings_of_rule (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, child supply expression result → visit supply expression = some result)
    {supply : Supply} {rows : List Atom} {body : Atom} {result : Result}
    (rule : BindingsRel child supply rows body result) : letBindings visit supply rows body = some result := by
  induction rule with
  | last supply row pattern value body p v b parsed patternRule valueRule bodyRule =>
      simp only [letBindings,parsed,bind,pure,Option.bind_some,
        children _ _ _ patternRule,children _ _ _ valueRule,children _ _ _ bodyRule]
  | next supply row nextRow pattern value body rest p v b parsed patternRule valueRule tail ih =>
      rw [letBindings]
      simp only [parsed,bind,pure,Option.bind_some,children _ _ _ patternRule,
        children _ _ _ valueRule,ih]

theorem bindings_has_rule (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result → child supply expression result)
    (rows : List Atom) : ∀ supply body result,
      letBindings visit supply rows body = some result → BindingsRel child supply rows body result := by
  induction rows with
  | nil => intro supply body result computed; cases computed
  | cons row rest ih =>
      intro supply body result computed
      rw [letBindings] at computed
      cases rest with
      | nil =>
          simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨parts,parsed,p,patternRule,v,valueRule,b,bodyRule,rfl⟩ := computed
          exact .last supply row parts.1 parts.2 body p v b parsed
            (children _ _ _ patternRule) (children _ _ _ valueRule) (children _ _ _ bodyRule)
      | cons nextRow rest =>
          simp only [bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
          obtain ⟨parts,parsed,p,patternRule,v,valueRule,b,tail,rfl⟩ := computed
          exact .next supply row nextRow parts.1 parts.2 body rest p v b parsed
            (children _ _ _ patternRule) (children _ _ _ valueRule) (ih v.supply body b tail)

theorem bindings_iff (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result ↔ child supply expression result)
    (supply : Supply) (rows : List Atom) (body : Atom) (result : Result) :
    letBindings visit supply rows body = some result ↔ BindingsRel child supply rows body result :=
  ⟨bindings_has_rule visit child (fun s e r h => (children s e r).mp h) rows supply body result,
   bindings_of_rule visit child (fun s e r h => (children s e r).mpr h)⟩

theorem cases_of_rule (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, child supply expression result → visit supply expression = some result)
    {supply : Supply} {rows : SpaceSemantics.Cases} {output : Atom} {result : Supply × List Atom}
    (rule : CasesRel context child supply rows output result) :
    caseBranches visit context supply rows output = some result := by
  induction rule with
  | nil supply output => rfl
  | cons supply pattern body output rest compiled selected later passive bodyRule branchRule tail ih =>
      simp only [caseBranches,passive,Bool.not_true,Bool.false_eq_true,↓reduceIte,
        bind,pure,children _ _ _ bodyRule,branch_of_rule branchRule,ih,Option.bind_some]

theorem cases_has_rule (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result → child supply expression result)
    (rows : SpaceSemantics.Cases) : ∀ supply output result,
      caseBranches visit context supply rows output = some result → CasesRel context child supply rows output result := by
  induction rows with
  | nil =>
      intro supply output result computed
      simp only [caseBranches,Option.some.injEq] at computed
      subst result
      exact .nil supply output
  | cons first rest ih =>
      rcases first with ⟨pattern,body⟩
      intro supply output result computed
      cases passive : passivePattern context pattern
      · simp [caseBranches,passive] at computed
      · simp only [caseBranches,passive,Bool.not_true,Bool.false_eq_true,↓reduceIte,
          bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨compiled,bodyRule,selected,branchRule,later,tail,rfl⟩ := computed
        exact .cons supply pattern body output rest compiled selected later passive
          (children _ _ _ bodyRule) (branch_has_rule branchRule) (ih selected.1 output later tail)

theorem cases_iff (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result ↔ child supply expression result)
    (supply : Supply) (rows : SpaceSemantics.Cases) (output : Atom) (result : Supply × List Atom) :
    caseBranches visit context supply rows output = some result ↔ CasesRel context child supply rows output result :=
  ⟨cases_has_rule context visit child (fun s e r h => (children s e r).mp h) rows supply output result,
   cases_of_rule context visit child (fun s e r h => (children s e r).mpr h)⟩

theorem layer_has_rule (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result → child supply expression result)
    (supply : Supply) (shape : Shape) (result : Result)
    (computed : perform context visit supply shape = some result) :
    Layer context child supply shape result := by
  have arguments := arguments_has_rule visit child children
  cases shape with
  | value expression =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      exact .value supply expression
  | quoted payload =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      exact .quoted supply payload
  | binding pattern value body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨p,patternRule,v,valueRule,b,bodyRule,rfl⟩ := computed
      exact .binding supply pattern value body p v b
        (children _ _ _ patternRule) (children _ _ _ valueRule) (children _ _ _ bodyRule)
  | bindings rows body =>
      exact .bindings supply rows body result (bindings_has_rule visit child children rows supply body result computed)
  | alternatives values =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,argumentRules,selected,branchRules,rfl⟩ := computed
      exact .alternatives supply values compiled selected (arguments _ _ _ _ _ argumentRules)
        ((branches_iff _ _ _ _ _).mp branchRules)
  | collection body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,bodyRule,rfl⟩ := computed
      exact .collection supply body compiled (children _ _ _ bodyRule)
  | first body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,bodyRule,rfl⟩ := computed
      exact .first supply body compiled (children _ _ _ bodyRule)
  | empty =>
      simp only [perform,Option.some.injEq] at computed
      subst result
      exact .empty supply
  | condition condition yes no =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨tested,testRule,yesPlan,yesRule,noPlan,noRule,yesGoal,yesBranch,noGoal,noBranch,rfl⟩ := computed
      exact .condition supply condition yes no tested yesPlan noPlan yesGoal noGoal
        (children _ _ _ testRule) (children _ _ _ yesRule) (children _ _ _ noRule)
        (branch_has_rule yesBranch) (branch_has_rule noBranch)
  | selection key rows =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨parsed,rowReader,selected,keyRule,compiled,caseRules,rfl⟩ := computed
      exact .selection supply key rows parsed selected compiled rowReader (children _ _ _ keyRule)
        (cases_has_rule context visit child children _ _ _ _ caseRules)
  | query location pattern body =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨space,locationRule,compiled,bodyRule,rfl⟩ := computed
      exact .query supply location pattern body space compiled
        (children _ _ _ locationRule) (children _ _ _ bodyRule)
  | application head values =>
      rw [perform] at computed
      simp only [bind,Option.bind_eq_some_iff] at computed
      obtain ⟨compiled,argumentRules,computed⟩ := computed
      cases nativeHead : Eval.ioHead head || StdLib.known head
      · simp only [nativeHead,Bool.false_eq_true,↓reduceIte] at computed
        cases lookup : context.lookup head values.length with
        | none =>
            cases callable : context.callable head
            · simp only [lookup,callable,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at computed
              subst result
              exact .constructor supply head values compiled nativeHead
                (arguments _ _ _ _ _ argumentRules) lookup callable
            · simp [lookup,callable] at computed
        | some signature =>
            simp only [lookup,Option.some.injEq] at computed
            subst result
            exact .authoredCall supply head values compiled signature nativeHead
              (arguments _ _ _ _ _ argumentRules) lookup
      · simp only [nativeHead,↓reduceIte,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
        obtain ⟨mode,modeRule,rfl⟩ := computed
        exact .nativeCall supply head values compiled mode nativeHead
          (arguments _ _ _ _ _ argumentRules) modeRule
  | groundedApplication head values =>
      simp only [perform,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] at computed
      obtain ⟨compiled,argumentRules,rfl⟩ := computed
      exact .grounded supply head values compiled (arguments _ _ _ _ _ argumentRules)
  | listApplication head values =>
      simp only [perform,bind,Option.bind_eq_some_iff] at computed
      obtain ⟨first,headRule,compiled,argumentRules,remaining⟩ := computed
      cases output : first.plan.output with
      | var name | symbol name | grounded value => simp only [output] at remaining; cases remaining
      | expression emitted =>
          simp only [output] at remaining
          split at remaining
          next normal =>
            simp only [Option.some.injEq] at remaining
            subst result
            exact .listHead supply head values first compiled emitted
              (children _ _ _ headRule) (arguments _ _ _ _ _ argumentRules) output
              (staticData_source context _ normal)
          next notNormal => cases remaining
  | unsupported => cases computed

theorem layer_of_rule (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, child supply expression result → visit supply expression = some result)
    {supply : Supply} {shape : Shape} {result : Result}
    (rule : Layer context child supply shape result) :
    perform context visit supply shape = some result := by
  have arguments := arguments_of_rule visit child children
  cases rule with
  | value | quoted | empty => rfl
  | binding pattern value body p v b patternRule valueRule bodyRule =>
      simp only [perform,bind,pure,children _ _ _ patternRule,children _ _ _ valueRule,
        children _ _ _ bodyRule,Option.bind_some]
  | bindings rows body result rowRules =>
      exact bindings_of_rule visit child children rowRules
  | alternatives values compiled selected argumentRules branchRules =>
      simp only [perform,bind,pure,arguments _ _ _ _ _ argumentRules,
        (branches_iff _ _ _ _ _).mpr branchRules,Option.bind_some]
  | collection body compiled bodyRule =>
      simp only [perform,bind,pure,children _ _ _ bodyRule,Option.bind_some]
  | first body compiled bodyRule =>
      simp only [perform,bind,pure,children _ _ _ bodyRule,Option.bind_some]
  | condition condition yes no tested yesPlan noPlan yesGoal noGoal testRule yesRule noRule yesBranch noBranch =>
      simp only [perform,bind,pure,children _ _ _ testRule,children _ _ _ yesRule,
        children _ _ _ noRule,branch_of_rule yesBranch,branch_of_rule noBranch,Option.bind_some]
  | selection key rows parsed selected compiled rowReader keyRule caseRules =>
      simp only [perform,rowReader,bind,pure,children _ _ _ keyRule,
        cases_of_rule context visit child children caseRules,Option.bind_some]
  | query location pattern body space compiled locationRule bodyRule =>
      simp only [perform,bind,pure,children _ _ _ locationRule,children _ _ _ bodyRule,Option.bind_some]
  | nativeCall head values compiled mode nativeHead argumentRules modeRule =>
      simp only [perform,bind,pure,arguments _ _ _ _ _ argumentRules,nativeHead,
        modeRule,↓reduceIte,Option.bind_some]
  | authoredCall head values compiled signature notNative argumentRules lookup =>
      simp only [perform,bind,arguments _ _ _ _ _ argumentRules,notNative,
        Bool.false_eq_true,↓reduceIte,lookup,Option.bind_some]
  | constructor head values compiled notNative argumentRules notRegistered notCallable =>
      have argumentComputed := arguments _ _ _ _ _ argumentRules
      simp only [notCallable,Bool.false_eq_true,↓reduceIte] at argumentComputed
      simp only [perform,bind,notNative,Bool.false_eq_true,↓reduceIte,
        notRegistered,notCallable,argumentComputed,Option.bind_some]
  | grounded head values compiled argumentRules =>
      simp only [perform,bind,pure,arguments _ _ _ _ _ argumentRules,Option.bind_some]
  | listHead head values first compiled emitted headRule argumentRules output normal =>
      simp only [perform,bind,children _ _ _ headRule,arguments _ _ _ _ _ argumentRules,
        Option.bind_some,output,normal.computed,↓reduceIte]

theorem perform_iff (context : Context) (visit : Supply → Atom → Option Result)
    (child : Supply → Atom → Result → Prop)
    (children : ∀ supply expression result, visit supply expression = some result ↔ child supply expression result)
    (supply : Supply) (shape : Shape) (result : Result) :
    perform context visit supply shape = some result ↔ Layer context child supply shape result :=
  ⟨layer_has_rule context visit child (fun s e r h => (children s e r).mp h) supply shape result,
   layer_of_rule context visit child (fun s e r h => (children s e r).mpr h)⟩

theorem compile_iff (context : Context) : ∀ depth supply expression result,
    compile context depth supply expression = some result ↔ FormationAt context depth supply expression result := by
  intro depth
  induction depth with
  | zero => intro supply expression result; simp [compile,FormationAt]
  | succ depth ih =>
      intro supply expression result
      exact perform_iff context (compile context depth) (FormationAt context depth) ih supply (classify expression) result

theorem formation_functional {context : Context} {depth : Nat} {supply : Supply} {expression : Atom}
    {first second : Result}
    (left : FormationAt context depth supply expression first)
    (right : FormationAt context depth supply expression second) : first = second := by
  exact Option.some.inj (((compile_iff context depth supply expression first).mpr left).symm.trans
    ((compile_iff context depth supply expression second).mpr right))

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
