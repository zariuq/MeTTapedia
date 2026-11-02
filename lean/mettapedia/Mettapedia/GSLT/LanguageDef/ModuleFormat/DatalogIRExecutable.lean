import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQuery
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRProgram
import Mettapedia.Languages.Datalog.DerivationIdentity
import Mettapedia.Languages.Datalog.Comparisons
import Mettapedia.Languages.Datalog.SymbolOrder
import Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission

/-! Executable positive Datalog preparation. Compilation emits ordinary GSLT
rules; primitive comparison rows contain no joins or derived facts. Native
carrier references expand through an explicit dictionary into semantic IR.
The basic scalar profile admits symbols, signed numbers and unsigned numbers.
Symbol ordering uses the independent decoded UTF-8 byte-order policy.
Floating values have an explicit diagnostic. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax Match
open Join (Pools)

def relationRef (index : Nat) : Pattern := .fvar ("dl:relation:" ++ toString index)
def valueRef (index : Nat) : Pattern := .fvar ("dl:value:" ++ toString index)

def fact? (pools : Pools) (source : GroundFact) : Option Pattern := do
  let relation ← pools.relations.idxOf? source.relation
  let values ← source.values.mapM fun value => valueRef <$> pools.literals.idxOf? value
  pure (.apply "GroundFact" [relationRef relation,.apply "GroundTuple" [Join.vector values]])

def freeTypes (pools : Pools) : List (String × TypeExpr) :=
  (List.range pools.relations.length).map (fun index => ("dl:relation:" ++ toString index,.base "DlRelation")) ++
  (List.range pools.literals.length).map (fun index => ("dl:value:" ++ toString index,.base "DlValue"))

def dictionary (pools : Pools) : Bindings :=
  pools.relations.zipIdx.map (fun (name,index) => ("dl:relation:" ++ toString index,IRCodec.relation name)) ++
  pools.literals.zipIdx.map (fun (value,index) => ("dl:value:" ++ toString index,IRCodec.value value))

def request (pools : Pools) : Pattern := Query.call
  ((List.range pools.relations.length).map relationRef) ((List.range pools.literals.length).map valueRef)

def compare (operator : ComparisonOperator) (left right : Value) : Bool :=
  match operator with
  | .equal => left == right
  | .different => left != right
  | _ => match left,right with
    | .symbol a,.symbol b => match operator with
      | .less => SymbolOrder.less a b | .lessEqual => SymbolOrder.less a b || a == b
      | .greater => SymbolOrder.less b a | .greaterEqual => SymbolOrder.less b a || a == b | _ => false
    | .number a,.number b => match operator with
      | .less => decide (a < b) | .lessEqual => decide (a ≤ b)
      | .greater => decide (a > b) | .greaterEqual => decide (a ≥ b) | _ => false
    | .unsigned a,.unsigned b => match operator with
      | .less => decide (a < b) | .lessEqual => decide (a ≤ b)
      | .greater => decide (a > b) | .greaterEqual => decide (a ≥ b) | _ => false
    | _,_ => false

def policy : Comparisons.Policy where
  Holds := fun operator left right => match operator with
    | .equal => left = right
    | .different => left ≠ right
    | _ => match left,right with
      | .symbol a,.symbol b => match operator with
        | .less => SymbolOrder.Less a b | .lessEqual => SymbolOrder.Less a b ∨ a = b
        | .greater => SymbolOrder.Less b a | .greaterEqual => SymbolOrder.Less b a ∨ a = b | _ => False
      | .number a,.number b => match operator with
        | .less => a < b | .lessEqual => a ≤ b | .greater => a > b | .greaterEqual => a ≥ b | _ => False
      | .unsigned a,.unsigned b => match operator with
        | .less => a < b | .lessEqual => a ≤ b | .greater => a > b | .greaterEqual => a ≥ b | _ => False
      | _,_ => False
  check := compare
  exact := by
    intro operator left right
    cases operator <;> cases left <;> cases right <;> simp [compare, SymbolOrder.less_exact]

def operators (program : Program) : List ComparisonOperator :=
  (program.statements.flatMap fun statement => match statement with
    | .rule clause => (Comparisons.guards clause).map (·.operator)
    | _ => []).eraseDups

def comparisonRows (program : Program) (pools : Pools) : List GeneralPremise.ProviderRow :=
  (operators program).flatMap fun operator => pools.literals.zipIdx.flatMap fun (left,i) =>
    pools.literals.zipIdx.filterMap fun (right,j) =>
      if compare operator left right then some ⟨Join.comparisonName operator,[valueRef i,valueRef j]⟩ else none

def comparisonSignatures (program : Program) : List GeneralPremise.Signature :=
  (operators program).map fun operator =>
    ⟨Join.comparisonName operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩

def operandType (program : Program) (clause : Clause) : Argument → Option AttributeType
  | .literal value => some value.type
  | .var name => StaticTyping.inferredContext (ProgramStatic.signature program) clause name
  | .anonymous => none

def scalarDiagnostic? (program : Program) (pools : Pools) : Option String :=
  if pools.literals.any (fun value => match value with | .floating _ => true | _ => false) ||
      (ProgramStatic.declarations program).any (fun declaration => declaration.attributes.any (·.type == .floating)) then
    some "floating scalars require a declared floating comparison profile"
  else none

structure Prepared where
  source : Program
  vocabulary : Pools
  compiled : LanguageDef
  seedFacts : List Pattern
  staticRows : List GeneralPremise.ProviderRow
  deriving Repr

def prepare (program : Program) (seeds : List GroundFact) : Except String Prepared := do
  let some prepared := Join.Program.prepare? program seeds
    | .error s!"program or input fact is outside the typed positive core: {reprStr (ProgramStatic.diagnose program)}"
  if let some diagnostic := scalarDiagnostic? program prepared.vocabulary then .error diagnostic else do
    let some encoded := seeds.mapM (fact? prepared.vocabulary)
      | .error "input contains a value outside the prepared vocabulary"
    pure ⟨program,prepared.vocabulary,Query.language (prepared.rules.map (Query.lowerRule prepared.vocabulary)),
      encoded.eraseDups,comparisonRows program prepared.vocabulary⟩

def snapshot (prepared : Prepared) (known : List Pattern) : GeneralExecutionAdmission.Snapshot :=
  ⟨prepared.compiled,freeTypes prepared.vocabulary,
    {signatures := ⟨Query.factRelation,[.base "DlStatement"],[.output]⟩ :: comparisonSignatures prepared.source,
     rows := (Query.provider known).rows ++ prepared.staticRows}⟩

def permissions : GeneralExecutionAdmission.Permissions := {sites := .rootOnly,includeDerivedEquations := false}
def plan (prepared : Prepared) (known : List Pattern) := GeneralExecutionAdmission.compile (snapshot prepared known) permissions

def decodeFact? (prepared : Prepared) (value : Pattern) : Option GroundFact :=
  IRCodec.groundFact? (applyBindings (dictionary prepared.vocabulary) value)

theorem primitive_comparison_exact (operator : ComparisonOperator) (left right : Value) :
    compare operator left right = true ↔ policy.Holds operator left right := policy.exact _ _ _

#print axioms primitive_comparison_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
