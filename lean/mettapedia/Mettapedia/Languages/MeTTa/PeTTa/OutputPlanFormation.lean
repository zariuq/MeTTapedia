import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanBranchRules
import Mettapedia.Languages.MeTTa.PeTTa.OutputPlanDataHeads

/-!
# Formation judgments for exposed-result compilation

The rules inspect the existing source Atom view and explicitly relate child
plans, held argument roles, branch construction and private/native calls.
They do not call the compiler or assume its successful output. This layer is
compilation-rule correspondence; the emitted goals' operational adequacy is
a further obligation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.OutputPlan

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

inductive ArgumentsRel (child : Supply → Atom → Result → Prop) (held : Nat → Bool) :
    Supply → Nat → List Atom → Results → Prop where
  | nil (supply : Supply) (index : Nat) : ArgumentsRel child held supply index [] ⟨supply,[]⟩
  | heldArgument (supply : Supply) (index : Nat) (first : Atom) (rest : List Atom)
      (later : Results) (heldHere : held index = true)
      (tail : ArgumentsRel child held supply (index + 1) rest later) :
      ArgumentsRel child held supply index (first :: rest)
        ⟨later.supply,Plan.value first :: later.plans⟩
  | evaluatedArgument (supply : Supply) (index : Nat) (first : Atom) (rest : List Atom)
      (entered : Result) (later : Results) (evaluatedHere : held index = false)
      (head : child supply first entered)
      (tail : ArgumentsRel child held entered.supply (index + 1) rest later) :
      ArgumentsRel child held supply index (first :: rest) ⟨later.supply,entered.plan :: later.plans⟩

inductive BindingsRel (child : Supply → Atom → Result → Prop) :
    Supply → List Atom → Atom → Result → Prop where
  | last (supply : Supply) (row pattern value body : Atom) (p v b : Result)
      (parsed : LambdaStaging.rowParts row = some (pattern,value))
      (patternRule : child supply pattern p)
      (valueRule : child p.supply value v) (bodyRule : child v.supply body b) :
      BindingsRel child supply [row] body ⟨b.supply,Plan.bind p.plan v.plan b.plan⟩
  | next (supply : Supply) (row nextRow pattern value body : Atom) (rest : List Atom)
      (p v b : Result) (parsed : LambdaStaging.rowParts row = some (pattern,value))
      (patternRule : child supply pattern p) (valueRule : child p.supply value v)
      (tail : BindingsRel child v.supply (nextRow :: rest) body b) :
      BindingsRel child supply (row :: nextRow :: rest) body ⟨b.supply,Plan.bind p.plan v.plan b.plan⟩

inductive CasesRel (context : Context) (child : Supply → Atom → Result → Prop) :
    Supply → SpaceSemantics.Cases → Atom → Supply × List Atom → Prop where
  | nil (supply : Supply) (output : Atom) : CasesRel context child supply [] output (supply,[])
  | cons (supply : Supply) (pattern body output : Atom) (rest : SpaceSemantics.Cases)
      (compiled : Result) (selected : Supply × Atom) (later : Supply × List Atom)
      (passive : passivePattern context pattern = true)
      (bodyRule : child supply body compiled)
      (branchRule : BranchRel context.branchPolicy compiled.supply compiled.plan output selected)
      (tail : CasesRel context child selected.1 rest output later) :
      CasesRel context child supply ((pattern,body) :: rest) output
        (later.1,.expression [pattern,selected.2] :: later.2)

inductive Layer (context : Context) (child : Supply → Atom → Result → Prop) :
    Supply → Shape → Result → Prop where
  | value (supply : Supply) (expression : Atom) :
      Layer context child supply (.value expression) ⟨supply,Plan.value expression⟩
  | quoted (supply : Supply) (payload : Atom) :
      Layer context child supply (.quoted payload) ⟨supply,Plan.value payload⟩
  | binding (supply : Supply) (pattern value body : Atom) (p v b : Result)
      (patternRule : child supply pattern p) (valueRule : child p.supply value v)
      (bodyRule : child v.supply body b) :
      Layer context child supply (.binding pattern value body) ⟨b.supply,Plan.bind p.plan v.plan b.plan⟩
  | bindings (supply : Supply) (rows : List Atom) (body : Atom) (result : Result)
      (rowRules : BindingsRel child supply rows body result) :
      Layer context child supply (.bindings rows body) result
  | alternatives (supply : Supply) (values : List Atom) (compiled : Results)
      (selected : Supply × List Atom)
      (arguments : ArgumentsRel child (fun _ => false) supply.fresh.1 0 values compiled)
      (branches : BranchesRel context.branchPolicy compiled.supply compiled.plans supply.fresh.2 selected) :
      Layer context child supply (.alternatives values)
        ⟨selected.1,⟨call "superpose" [.expression selected.2],supply.fresh.2⟩⟩
  | collection (supply : Supply) (body : Atom) (compiled : Result)
      (bodyRule : child supply body compiled) :
      Layer context child supply (.collection body)
        ⟨compiled.supply.fresh.1,
          ⟨call "let" [hold compiled.supply.fresh.2,call "collapse" [compiled.plan.execute],unit],
            compiled.supply.fresh.2⟩⟩
  | first (supply : Supply) (body : Atom) (compiled : Result)
      (bodyRule : child supply body compiled) :
      Layer context child supply (.first body)
        ⟨compiled.supply,⟨call "once" [compiled.plan.goals],compiled.plan.output⟩⟩
  | empty (supply : Supply) :
      Layer context child supply .empty ⟨supply,⟨call "empty" [],.expression []⟩⟩
  | condition (supply : Supply) (condition yes no : Atom) (tested yesPlan noPlan : Result)
      (yesGoal noGoal : Supply × Atom)
      (testRule : child supply condition tested)
      (yesRule : child tested.supply.fresh.1 yes yesPlan)
      (noRule : child yesPlan.supply no noPlan)
      (yesBranch : BranchRel context.branchPolicy noPlan.supply yesPlan.plan tested.supply.fresh.2 yesGoal)
      (noBranch : BranchRel context.branchPolicy yesGoal.1 noPlan.plan tested.supply.fresh.2 noGoal) :
      Layer context child supply (.condition condition yes no)
        ⟨noGoal.1,
          ⟨sequence tested.plan.goals (call "if" [hold tested.plan.output,yesGoal.2,noGoal.2]),
            tested.supply.fresh.2⟩⟩
  | selection (supply : Supply) (key : Atom) (rows : List Atom) (parsed : SpaceSemantics.Cases)
      (selected : Result) (compiled : Supply × List Atom)
      (rowReader : Eval.readCases rows = some parsed)
      (keyRule : child supply key selected)
      (cases : CasesRel context child selected.supply.fresh.1 parsed selected.supply.fresh.2 compiled) :
      Layer context child supply (.selection key rows)
        ⟨compiled.1,
          ⟨sequence selected.plan.goals (call "case" [hold selected.plan.output,.expression compiled.2]),
            selected.supply.fresh.2⟩⟩
  | query (supply : Supply) (location pattern body : Atom) (space compiled : Result)
      (locationRule : child supply location space) (bodyRule : child space.supply body compiled) :
      Layer context child supply (.query location pattern body)
        ⟨compiled.supply,
          ⟨sequence space.plan.goals
            (sequence (call "match" [hold space.plan.output,pattern,unit]) compiled.plan.goals),
              compiled.plan.output⟩⟩
  | nativeCall (supply : Supply) (head : String) (arguments : List Atom) (compiled : Results)
      (mode : NativeMode) (nativeHead : (Eval.ioHead head || StdLib.known head) = true)
      (argumentRules : ArgumentsRel child
        (if context.callable head then Eval.argumentIsRaw context.source head else fun _ => false)
          supply 0 arguments compiled)
      (modeRule : nativeMode? head = some mode) :
      Layer context child supply (.application head arguments)
        ⟨compiled.supply.fresh.1,
          ⟨sequence (ordered (compiled.plans.map Plan.goals))
            (native context.source mode head (compiled.plans.map Plan.output) compiled.supply.fresh.2),
              compiled.supply.fresh.2⟩⟩
  | authoredCall (supply : Supply) (head : String) (arguments : List Atom) (compiled : Results)
      (signature : Signature) (notNative : (Eval.ioHead head || StdLib.known head) = false)
      (argumentRules : ArgumentsRel child
        (if context.callable head then Eval.argumentIsRaw context.source head else fun _ => false)
          supply 0 arguments compiled)
      (lookup : context.lookup head arguments.length = some signature) :
      Layer context child supply (.application head arguments)
        ⟨compiled.supply.fresh.1,
          ⟨sequence (ordered (compiled.plans.map Plan.goals))
            (invoke signature.target (compiled.plans.map Plan.output) compiled.supply.fresh.2),
              compiled.supply.fresh.2⟩⟩
  | constructor (supply : Supply) (head : String) (arguments : List Atom) (compiled : Results)
      (notNative : (Eval.ioHead head || StdLib.known head) = false)
      (argumentRules : ArgumentsRel child
        (if context.callable head then Eval.argumentIsRaw context.source head else fun _ => false)
          supply 0 arguments compiled)
      (notRegistered : context.lookup head arguments.length = none)
      (notCallable : context.callable head = false) :
      Layer context child supply (.application head arguments)
        ⟨compiled.supply,⟨ordered (compiled.plans.map Plan.goals),
          .expression (.symbol head :: compiled.plans.map Plan.output)⟩⟩
  | grounded (supply : Supply) (head : OSLFCore.GroundedValue) (arguments : List Atom) (compiled : Results)
      (argumentRules : ArgumentsRel child (fun _ => false) supply 0 arguments compiled) :
      Layer context child supply (.groundedApplication head arguments)
        ⟨compiled.supply,Plan.data (.grounded head) compiled.plans⟩
  | listHead (supply : Supply) (head arguments : List Atom) (first : Result) (compiled : Results)
      (values : List Atom) (headRule : child supply (.expression head) first)
      (argumentRules : ArgumentsRel child (fun _ => false) first.supply 0 arguments compiled)
      (knownList : first.plan.output = .expression values)
      (normal : DataTree context (.expression values)) :
      Layer context child supply (.listApplication head arguments)
        ⟨compiled.supply,⟨sequence first.plan.goals (ordered (compiled.plans.map Plan.goals)),
          .expression (.expression values :: compiled.plans.map Plan.output)⟩⟩

/-- The bound is compilation recursion depth. It is unrelated to evaluation
fuel or producer exhaustion. Unsupported forms have no formation rule. -/
def FormationAt (context : Context) : Nat → Supply → Atom → Result → Prop
  | 0, _, _, _ => False
  | depth + 1, supply, expression, result =>
      Layer context (FormationAt context depth) supply (classify expression) result

end Mettapedia.Languages.MeTTa.PeTTa.OutputPlan
