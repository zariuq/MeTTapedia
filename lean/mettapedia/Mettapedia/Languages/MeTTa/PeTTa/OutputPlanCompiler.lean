import Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
import Mettapedia.Languages.MeTTa.PeTTa.LambdaStaging

/-!
# Structural output-plan compilation

Private procedures accept an explicit result argument. Their first goal
unifies that argument with the compiled result term before running the body.
Original equations remain visible as source data. The compiler uses the
existing streaming evaluator for its emitted quote/let/control forms.

This is a static-program compilation component. Unsupported dynamic heads,
partial calls, native relational modes and lambda authoring return none at
this admission boundary; they are not assigned empty source meanings. Full
source/compiler adequacy, typed alternatives, dynamic program updates and
compiler-local readout remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (atomFreeVars)

structure Signature where
  source : String
  arity : Nat
  target : String

def reserveNames : Finset String → List (String × Nat) → Finset String × List Signature
  | used, [] => (used,[])
  | used, (source,arity) :: rest =>
      let target := Mettapedia.FreshString.fresh used
      let later := reserveNames (insert target used) rest
      (later.1,⟨source,arity,target⟩ :: later.2)

structure Context where
  source : SpaceSemantics.Program
  signatures : List Signature
  branchPolicy : BranchPolicy := .swiAliases

def Context.ofProgram (program : SpaceSemantics.Program)
    (policy : BranchPolicy := .swiAliases) : Context :=
  let interfaces := (program.equations.map fun equation => (equation.head,equation.arguments.length)).eraseDups
  let declared := program.declarations.filterMap fun declaration =>
    match declaration with
    | .expression [.symbol ":",.symbol name,_] => some name
    | _ => none
  ⟨program,(reserveNames ((program.equations.map (·.head) ++ declared).toFinset) interfaces).2,policy⟩

def Context.lookup (context : Context) (head : String) (arity : Nat) : Option Signature :=
  context.signatures.find? fun signature => signature.source == head && signature.arity == arity

def Context.callable (context : Context) (head : String) : Bool :=
  Eval.ioHead head || StdLib.known head || context.source.equations.any (·.head == head)

def nativeMode? (head : String) : Option NativeMode :=
  if head ∈ ["add-atom","change-state!","println!"] then some .trueBeforeEffect
  else if head ∈ ["+","-","*","%","<","<=",">",">=","==",
      "get-atoms","get-state","get-metatype","get-type","remove-atom"] then some .forward
  else none

structure Result where
  supply : Supply
  plan : Plan

structure Results where
  supply : Supply
  plans : List Plan

def visitMany (visit : Supply → Atom → Option Result) (held : Nat → Bool) :
    Supply → Nat → List Atom → Option Results
  | supply, _, [] => some ⟨supply,[]⟩
  | supply, index, expression :: rest => do
      let first ← if held index then some ⟨supply,Plan.value expression⟩ else visit supply expression
      let later ← visitMany visit held first.supply (index + 1) rest
      pure ⟨later.supply,first.plan :: later.plans⟩

def branches (policy : BranchPolicy) : Supply → List Plan → Atom → Option (Supply × List Atom)
  | supply, [], _ => some (supply,[])
  | supply, first :: rest, output => do
      let firstBranch ← branch supply first output policy
      let later ← branches policy firstBranch.1 rest output
      pure (later.1,firstBranch.2 :: later.2)

/-- A known source-control head must not silently become a constructor when
this compilation component lacks its required form or operational region. -/
def controlHead (head : String) : Bool :=
  head ∈ ["quote","let","chain","let*","superpose","collapse","once","empty","if","case","match","|->",
    "cut","catch","progn","prog1","and-then","or-else","forall","foldall","sealed",
    "hyperpose","with_mutex","transaction","test","unique","alpha-unique","union","intersection","subtraction"]

mutual
  def passivePattern (context : Context) : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | .expression (.symbol head :: rest) =>
        (head == "cons" || (!context.callable head && !controlHead head)) && passivePatterns context rest
    | .expression items => passivePatterns context items

  def passivePatterns (context : Context) : List Atom → Bool
    | [] => true
    | first :: rest => passivePattern context first && passivePatterns context rest
end

mutual
  /-- A translated list head which needs no further data-term evaluation.
Variable leaves remain data; a variable in head position still needs dispatch.
Known calls and control forms inside the list cannot use this case. -/
  def staticData (context : Context) : Atom → Bool
    | .var _ | .symbol _ | .grounded _ => true
    | .expression [] => true
    | .expression (.symbol head :: rest) =>
        !context.callable head && !controlHead head && staticDataList context rest
    | .expression (.expression head :: rest) =>
        staticData context (.expression head) && staticDataList context rest
    | .expression (.grounded _ :: rest) => staticDataList context rest
    | .expression (.var _ :: _) => false

  def staticDataList (context : Context) : List Atom → Bool
    | [] => true
    | first :: rest => staticData context first && staticDataList context rest
end

/-- Visit each authored binding at the same child allowance. Expanding a
flat let* into a deep synthetic tree would add an unrelated depth limit. -/
def letBindings (visit : Supply → Atom → Option Result) :
    Supply → List Atom → Atom → Option Result
  | _, [], _ => none
  | supply, first :: rest, body => do
      let (pattern,value) ← LambdaStaging.rowParts first
      let p ← visit supply pattern
      let v ← visit p.supply value
      let b ← match rest with
        | [] => visit v.supply body
        | _ :: _ => letBindings visit v.supply rest body
      pure ⟨b.supply,Plan.bind p.plan v.plan b.plan⟩

def caseBranches (visit : Supply → Atom → Option Result) (context : Context) :
    Supply → SpaceSemantics.Cases → Atom → Option (Supply × List Atom)
  | supply, [], _ => some (supply,[])
  | supply, (pattern,body) :: rest, output => do
      if !passivePattern context pattern then none else do
        let compiled ← visit supply body
        let selected ← branch compiled.supply compiled.plan output context.branchPolicy
        let later ← caseBranches visit context selected.1 rest output
        pure (later.1,.expression [pattern,selected.2] :: later.2)

inductive Shape where
  | value (expression : Atom)
  | quoted (payload : Atom)
  | binding (pattern value body : Atom)
  | bindings (rows : List Atom) (body : Atom)
  | alternatives (values : List Atom)
  | collection (body : Atom)
  | first (body : Atom)
  | empty
  | condition (test yes no : Atom)
  | selection (key : Atom) (rows : List Atom)
  | query (location pattern body : Atom)
  | application (head : String) (arguments : List Atom)
  | groundedApplication (head : OSLFCore.GroundedValue) (arguments : List Atom)
  | listApplication (head arguments : List Atom)
  | unsupported

/-- A structural view of the existing source Atom, not a second parser. -/
def classify : Atom → Shape
  | .expression [.symbol "quote",payload] => .quoted payload
  | .expression [.symbol "let",pattern,value,body]
  | .expression [.symbol "chain",pattern,value,body] => .binding pattern value body
  | .expression [.symbol "let*",.expression rows,body] => .bindings rows body
  | .expression [.symbol "superpose",.expression values] => .alternatives values
  | .expression [.symbol "collapse",body] => .collection body
  | .expression [.symbol "once",body] => .first body
  | .expression [.symbol "empty"] => .empty
  | .expression [.symbol "if",test,yes,no] => .condition test yes no
  | .expression [.symbol "if",test,yes] => .condition test yes (call "empty" [])
  | .expression [.symbol "case",key,.expression rows] => .selection key rows
  | .expression [.symbol "match",location,pattern,body] => .query location pattern body
  | .expression [.symbol "|->",_,_] => .unsupported
  | .expression (.symbol head :: arguments) =>
      if controlHead head then .unsupported else .application head arguments
  | .expression [] => .value (.expression [])
  | .expression (.grounded head :: arguments) => .groundedApplication head arguments
  | .expression (.expression head :: arguments) => .listApplication head arguments
  | .expression _ => .unsupported
  | expression => .value expression

def perform (context : Context) (visit : Supply → Atom → Option Result)
    (supply : Supply) : Shape → Option Result
  | .value expression => some ⟨supply,Plan.value expression⟩
  | .quoted payload => some ⟨supply,Plan.value payload⟩
  | .binding pattern value body => do
      let p ← visit supply pattern
      let v ← visit p.supply value
      let b ← visit v.supply body
      pure ⟨b.supply,Plan.bind p.plan v.plan b.plan⟩
  | .bindings rows body => letBindings visit supply rows body
  | .alternatives alternatives => do
      let allocated := supply.fresh
      let compiled ← visitMany visit (fun _ => false) allocated.1 0 alternatives
      let selected ← branches context.branchPolicy compiled.supply compiled.plans allocated.2
      pure ⟨selected.1,⟨call "superpose" [.expression selected.2],allocated.2⟩⟩
  | .collection body => do
      let child ← visit supply body
      let allocated := child.supply.fresh
      pure ⟨allocated.1,
        ⟨call "let" [hold allocated.2,call "collapse" [child.plan.execute],unit],allocated.2⟩⟩
  | .first body => do
      let child ← visit supply body
      pure ⟨child.supply,⟨call "once" [child.plan.goals],child.plan.output⟩⟩
  | .empty => some ⟨supply,⟨call "empty" [],.expression []⟩⟩
  | .condition condition yes no => do
      let tested ← visit supply condition
      let allocated := tested.supply.fresh
      let yesPlan ← visit allocated.1 yes
      let noPlan ← visit yesPlan.supply no
      let yesGoal ← branch noPlan.supply yesPlan.plan allocated.2 context.branchPolicy
      let noGoal ← branch yesGoal.1 noPlan.plan allocated.2 context.branchPolicy
      pure ⟨noGoal.1,
        ⟨sequence tested.plan.goals
          (call "if" [hold tested.plan.output,yesGoal.2,noGoal.2]),allocated.2⟩⟩
  | .selection key rows => do
      let parsed ← Eval.readCases rows
      let selected ← visit supply key
      let allocated := selected.supply.fresh
      let compiled ← caseBranches visit context allocated.1 parsed allocated.2
      pure ⟨compiled.1,
        ⟨sequence selected.plan.goals
          (call "case" [hold selected.plan.output,.expression compiled.2]),allocated.2⟩⟩
  | .query location pattern body => do
      let space ← visit supply location
      let compiled ← visit space.supply body
      pure ⟨compiled.supply,
        ⟨sequence space.plan.goals
          (sequence (call "match" [hold space.plan.output,pattern,unit]) compiled.plan.goals),compiled.plan.output⟩⟩
  | .application head arguments => do
      let held := if context.callable head then Eval.argumentIsRaw context.source head else fun _ => false
      let compiled ← visitMany visit held supply 0 arguments
      let goals := ordered (compiled.plans.map Plan.goals)
      let values := compiled.plans.map Plan.output
      if Eval.ioHead head || StdLib.known head then do
        let mode ← nativeMode? head
        let allocated := compiled.supply.fresh
        pure ⟨allocated.1,⟨sequence goals (native context.source mode head values allocated.2),allocated.2⟩⟩
      else
        match context.lookup head arguments.length with
        | some signature =>
            let allocated := compiled.supply.fresh
            some ⟨allocated.1,⟨sequence goals (invoke signature.target values allocated.2),allocated.2⟩⟩
        | none =>
            if context.callable head then none
            else some ⟨compiled.supply,⟨goals,.expression (.symbol head :: values)⟩⟩
  | .groundedApplication value arguments => do
      let compiled ← visitMany visit (fun _ => false) supply 0 arguments
      pure ⟨compiled.supply,Plan.data (.grounded value) compiled.plans⟩
  | .listApplication head arguments => do
      let first ← visit supply (.expression head)
      let compiled ← visitMany visit (fun _ => false) first.supply 0 arguments
      match first.plan.output with
      | .expression values =>
          if staticData context (.expression values) then
            some ⟨compiled.supply,⟨sequence first.plan.goals (ordered (compiled.plans.map Plan.goals)),
              .expression (.expression values :: compiled.plans.map Plan.output)⟩⟩
          else none
      | _ => none
  | .unsupported => none

def compile (context : Context) : Nat → Supply → Atom → Option Result
  | 0, _, _ => none
  | depth + 1, supply, expression =>
      perform context (compile context depth) supply (classify expression)

def normalized (result : Result) : Plan := result.supply.plan result.plan

def compileExpression (context : Context) (expression : Atom) : Option Plan := do
  let result ← compile context (LambdaStaging.depthOf expression * 2 + 2) (Supply.start [expression]) expression
  pure (normalized result)

/-- A literal Atom output declaration holds the authored body. Overloaded
typed-call correspondence is not established by this one declaration test. -/
def rawOutput (program : SpaceSemantics.Program) (head : String) (arity : Nat) : Bool :=
  program.declarations.any fun declaration =>
    match declaration with
    | .expression [.symbol ":",.symbol name,.expression (.symbol "->" :: types)] =>
        name == head && types.length == arity + 1 && types[arity]? == some (.symbol "Atom")
    | _ => false

def compileEquation (context : Context) (equation : SpaceSemantics.Equation) :
    Option SpaceSemantics.Equation := do
  if !(equation.arguments.all (passivePattern context)) then none else do
    let signature ← context.lookup equation.head equation.arguments.length
    let supply := Supply.start (equation.body :: equation.arguments)
    let result ← if rawOutput context.source equation.head equation.arguments.length then
        some ⟨supply,Plan.value equation.body⟩
      else compile context (LambdaStaging.depthOf equation.body * 2 + 2) supply equation.body
    let body := normalized result
    let allocated := result.supply.fresh
    match allocated.2 with
    | .var outputName => some (procedure signature.target
        (equation.arguments.map result.supply.normalize) outputName body)
    | _ => none

structure Program where
  source : SpaceSemantics.Program
  context : Context
  code : List SpaceSemantics.Equation
  queries : List Atom

def compileProgram (source : SpaceSemantics.Program)
    (policy : BranchPolicy := .swiAliases) : Option Program := do
  let context := Context.ofProgram source policy
  let code ← source.equations.mapM (compileEquation context)
  let plans ← source.initializers.mapM (compileExpression context)
  pure ⟨source,context,code,plans.map Plan.execute⟩

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
