import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleCompilation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteEmission

/-! Prepared CHR programs use the existing plan and physical Pattern wire.
The controller metadata contains compact core instructions, not source CSTs.
This is serialization/emission code; its source correspondence is a separate
proof obligation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ExecutionData

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL

def bool (value : Bool) : CettaWire.Term := .symbol (if value then "True" else "False")
def variableName (index : Nat) : CettaWire.Term := .string (toString index)
def encoded (pattern : Pattern) : CettaWire.Term := InferenceCettaWire.encodePattern pattern

def term? (vocabulary : Vocabulary) : Mettapedia.Languages.CHR.Term → Option CettaWire.Term
  | .value value => do pure (.application "ChrLiteral" [encoded (← value? vocabulary value)])
  | .var index => some (.application "ChrVariable" [variableName index])
  | .tuple fields => do pure (.application "ChrTuple" [encodeList id (← fields.mapM (term? vocabulary))])

def head? (vocabulary : Vocabulary) (head : Head) : Option CettaWire.Term := do
  let predicate ← vocabulary.predicates.idxOf? head.name
  pure (.application "ChrHead" [encoded (predicateRef predicate), encodeList id (← head.arguments.mapM (term? vocabulary))])

def intOperator : IntOperator → CettaWire.Term
  | .add => .symbol "ChrAdd" | .subtract => .symbol "ChrSubtract" | .multiply => .symbol "ChrMultiply"
  | .quotient => .symbol "ChrQuotient" | .remainder => .symbol "ChrRemainder" | .modulo => .symbol "ChrModulo"

def intExpr : IntExpr → CettaWire.Term
  | .literal value => .application "ChrNumber" [bool (decide (value < 0)), .natural value.natAbs]
  | .index idx => .application "ChrIntVariable" [variableName idx]
  | .operation operator left right => .application "ChrIntOperation" [intOperator operator, intExpr left, intExpr right]

def comparison : Comparison → CettaWire.Term
  | .equal => .symbol "ChrEqual" | .different => .symbol "ChrDifferent" | .less => .symbol "ChrLess"
  | .lessEqual => .symbol "ChrLessEqual" | .greater => .symbol "ChrGreater" | .greaterEqual => .symbol "ChrGreaterEqual"

def guard? (vocabulary : Vocabulary) : Mettapedia.Languages.CHR.Guard → Option CettaWire.Term
  | .identical left right => do pure (.application "ChrIdentity" [← term? vocabulary left, ← term? vocabulary right])
  | .distinct left right => do pure (.application "ChrDifference" [← term? vocabulary left, ← term? vocabulary right])
  | .compare operator left right => some (.application "ChrCompare" [comparison operator, intExpr left, intExpr right])

def goal? (vocabulary : Vocabulary) : Goal → Option CettaWire.Term
  | .tell head => do pure (.application "ChrTell" [← head? vocabulary head])
  | .assign index expression => some (.application "ChrAssign" [variableName index, intExpr expression])
  | .fail => some (.symbol "ChrFail")

def entry? (prepared : Prepared) (index : Nat) (entry : Entry) : Option CettaWire.Term := do
  let rule ← prepared.program.rules[entry.occurrence.rule]?
  pure (.application "ChrEntry" [.string (toString entry.occurrence.rule), .string (queryLabel index),
    encodeList variableName entry.boundVariables,
    encodeList id (← rule.guards.mapM (guard? prepared.vocabulary)),
    encodeList id (← rule.body.mapM (goal? prepared.vocabulary)), bool rule.removed.isEmpty])

def spec (prepared : Prepared) : CompleteEmission.Spec := ⟨plan prepared, [], .base "ChrMatchState", .canonical⟩

def arguments? (prepared : Prepared) (seeds : List Constraint) : Option (List CettaWire.Term) := do
  let entries ← prepared.entries.zipIdx.mapM fun (entry,index) => entry? prepared index entry
  let goals ← seeds.mapM fun constraint => goal? prepared.vocabulary (.tell constraint.asHead)
  pure [CompletePlanWire.planTerm (plan prepared) (freeTypes prepared) [] (.base "ChrMatchState"),
    StandardWire.commitTerm (plan prepared) .canonical (CompleteEmission.table (spec prepared)),
    encoded (vector ((List.range prepared.vocabulary.predicates.length).map predicateRef)),
    encoded (vector (prepared.vocabulary.scalars.zipIdx.map (fun (value,index) =>
      match value with | .integer number => integer number | _ => scalarRef index))),
    encodeList id entries, encodeList id goals]

def emitText? (prepared : Prepared) (seeds : List Constraint) (name : String) : Except String String := do
  let .ok matcher := CompleteEmission.emitText? (spec prepared) (name ++ ":match") .classes
    | throw s!"CHR matching plan is not admitted: {reprStr (plan prepared).obligations}"
  let some arguments := arguments? prepared seeds | throw "CHR controller metadata encoding failed"
  let begin := (CettaWire.Term.application "gslt:chr:begin" arguments).render
  pure (matcher ++ "\n(: " ++ name ++ ":begin (-> %Undefined%))\n(= (" ++ name ++ ":begin) " ++ begin ++ ")\n" ++
    "(: " ++ name ++ ":run (-> Number Number %Undefined%))\n" ++
    "(= (" ++ name ++ ":run $ticks $quantum) (let $machine (" ++ name ++ ":begin) " ++
    "(let $finished (gslt:chr:advance $ticks $quantum $machine) (gslt:chr:result $finished))))\n")

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.ExecutionData
