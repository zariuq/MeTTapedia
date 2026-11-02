import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRScopedInstances
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-! A typed compiled fact instance constructs the actual retained unary
provider-query witness, including its row index and matcher trace. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.QueryInstances

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match RuleBinding
open GeneralFirstOrderProjection
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem output_query (pools : Join.Pools) (clause : Clause) (sourceEnvironment : BindingTyping.SourceEnvironment)
    (chosen : List GroundFact) (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context pools clause ++ extra)
    (bound : context.bound = []) (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes pools))
    (admitted : admittedFor context.rule context.spec = true) (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (code target : Pattern) (shape : VectorFirstOrder code) (noBinders : binderFree code = true)
    (coherent : NameCoherent context.rule (context.site 0) [] code)
    (defined : Defined (BindingTyping.ofClause pools clause sourceEnvironment chosen) code.freeFvarNames)
    (instantiated : applyBindings (BindingTyping.ofClause pools clause sourceEnvironment chosen) code = target)
    (typedTarget : OpenPatternWellSorted environment.language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] (.base "DlStatement") target)
    (index : Nat) (present : environment.provider.rows[index]? = some ⟨Query.factRelation,[target]⟩)
    (signature : GeneralPremise.signature? environment.provider Query.factRelation 1 =
      some ⟨Query.factRelation,[.base "DlStatement"],[.output]⟩)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause pools clause sourceEnvironment chosen) initial) :
    ∃ final trace,
      GeneralPremise.TracedQuery environment context Query.factRelation [code] initial index final [(0,trace)] ∧
      ScopedCompatible 0 (BindingTyping.ofClause pools clause sourceEnvironment chosen) final := by
  obtain ⟨final,matching,compatible,typed,objects⟩ := ScopedInstances.typed_match environment.language pools clause
    sourceEnvironment chosen context.rule context.spec extra ctx admitted zero (context.site 0) [] code target shape noBinders
    coherent defined instantiated (.base "DlStatement") typedTarget initial before
  obtain ⟨trace,traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  have arguments : GeneralPremise.TracedArgumentsHold context 0 initial [code] [target] [.output] final [(0,trace)] := by
    apply GeneralPremise.Interpreted.TracedArgumentsHold.output
    · simpa only [bound,List.length_nil] using traced
    · exact .nil
  have sorted : GeneralPremise.TypedAssignment environment context final := by
    simpa only [GeneralPremise.TypedAssignment,bound,free] using And.intro typed objects
  have rowTyped : GeneralPremise.RowTyped environment.language environment.free context.bound
      ⟨Query.factRelation,[.base "DlStatement"],[.output]⟩ ⟨Query.factRelation,[target]⟩ := by
    constructor
    · rfl
    · rw [free,bound]
      exact .cons typedTarget .nil
  exact ⟨final,trace,.row present signature rowTyped arguments sorted,compatible⟩

theorem input_query (pools : Join.Pools) (clause : Clause) (sourceEnvironment : BindingTyping.SourceEnvironment)
    (chosen : List GroundFact) (environment : GeneralPremise.Environment) (context : GeneralPremise.Context)
    (extra : List (String × TypeExpr))
    (ctx : context.rule.typeContext = BindingContext.context pools clause ++ extra)
    (bound : context.bound = []) (free : environment.free = FreeTypeContext.ofList (Executable.freeTypes pools))
    (admitted : admittedFor context.rule context.spec = true) (zero : GeneralPremise.checkZeroDependencies context.spec = true)
    (relation : String) (leftCode rightCode left right : Pattern)
    (leftShape : ∃ name, leftCode = .fvar name) (rightShape : ∃ name, rightCode = .fvar name)
    (leftCoherent : NameCoherent context.rule (context.site 0) [] leftCode)
    (rightCoherent : NameCoherent context.rule (context.site 1) [] rightCode)
    (initial : ScopedRuleMatching.Assignment)
    (before : ScopedCompatible 0 (BindingTyping.ofClause pools clause sourceEnvironment chosen) initial)
    (leftDefined : GeneralPremise.BoundNames initial leftCode.freeFvarNames)
    (rightDefined : GeneralPremise.BoundNames initial rightCode.freeFvarNames)
    (leftRead : applyBindings (BindingTyping.ofClause pools clause sourceEnvironment chosen) leftCode = left)
    (rightRead : applyBindings (BindingTyping.ofClause pools clause sourceEnvironment chosen) rightCode = right)
    (index : Nat) (present : environment.provider.rows[index]? = some ⟨relation,[left,right]⟩)
    (signature : GeneralPremise.signature? environment.provider relation 2 =
      some ⟨relation,[.base "DlValue",.base "DlValue"],[.input,.input]⟩)
    (rowTyped : GeneralPremise.RowTyped environment.language environment.free context.bound
      ⟨relation,[.base "DlValue",.base "DlValue"],[.input,.input]⟩ ⟨relation,[left,right]⟩) :
    GeneralPremise.TracedQuery environment context relation [leftCode,rightCode] initial index initial [(0,[]),(1,[])] := by
  have leftValue := ScopedInstances.input_value pools clause sourceEnvironment chosen environment context extra ctx bound admitted zero
    0 leftCode left leftShape leftCoherent initial before leftDefined leftRead
  have rightValue := ScopedInstances.input_value pools clause sourceEnvironment chosen environment context extra ctx bound admitted zero
    1 rightCode right rightShape rightCoherent initial before rightDefined rightRead
  have rawTyped : CapturesTyped environment.language (FreeTypeContext.ofList (Executable.freeTypes pools)) [] context.rule.typeContext
      (BindingTyping.ofClause pools clause sourceEnvironment chosen) := by
    rw [ctx]
    exact BindingTyping.clause_typed_extended environment.language pools clause sourceEnvironment chosen extra
  have sorted : GeneralPremise.TypedAssignment environment context initial := by
    have assigned := ScopedCompatible.typed_admitted (bound := []) before rawTyped admitted zero
    simpa only [GeneralPremise.TypedAssignment,bound,free] using assigned
  apply GeneralPremise.Interpreted.TracedQuery.row present signature rowTyped
  · exact .input leftValue (.input rightValue .nil)
  · exact sorted

#print axioms output_query
#print axioms input_query

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.QueryInstances
