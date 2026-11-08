import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler

/-! The reference reading of D0 source packets, printed as the MeTTa IR of
CeTTa's D0 frontend (`langdef/lang/datalog/reader.metta`) so the two readers
can be compared. Each input line is `SOURCE<TAB>PACKET<TAB>OUTPUT`; OUTPUT
receives `(= (lean:result) RESULT)` where RESULT is
`(Read PROGRAM ISSUES)` or `ReadRefused`. -/

open Mettapedia.Languages.Datalog

def hexDigits (n : Nat) : String :=
  String.ofList (Nat.toDigits 16 n)

def text (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\"
    else if c.toNat < 32 || c.toNat = 127 then "\\u{" ++ hexDigits c.toNat ++ "}"
    else c.toString) ++ "\""

def list (items : List String) : String := "(" ++ " ".intercalate items ++ ")"

def name (parts : QualifiedName) : String := list (parts.map text)

def attributeType : AttributeType → String
  | .symbol => "D0Symbol" | .number => "D0Number" | .unsigned => "D0Unsigned" | .floating => "D0Float"

def value : Value → String
  | .symbol s => "(D0SymbolValue " ++ text s ++ ")"
  | .number n => "(D0NumberValue " ++ toString n ++ ")"
  | .unsigned n => "(D0UnsignedValue " ++ toString n ++ ")"
  | .floating w => "(D0FloatValue " ++ toString w.toNat ++ ")"

def argument : Argument → String
  | .var x => "(D0Var " ++ text x ++ ")"
  | .anonymous => "D0Anonymous"
  | .literal v => "(D0Literal " ++ value v ++ ")"

def atom (a : Atom) : String := "(D0Atom " ++ name a.relation ++ " " ++ list (a.arguments.map argument) ++ ")"

def operator : ComparisonOperator → String
  | .equal => "D0Equal" | .different => "D0Different" | .less => "D0Less"
  | .lessEqual => "D0LessEqual" | .greater => "D0Greater" | .greaterEqual => "D0GreaterEqual"

def premise : Premise → String
  | .atom a => "(D0Positive " ++ atom a ++ ")"
  | .comparison c => "(D0Compare " ++ operator c.operator ++ " " ++ argument c.left ++ " " ++ argument c.right ++ ")"

def statement : Statement → String
  | .declaration d => "(D0Declaration " ++ name d.name ++ " " ++
      list (d.attributes.map fun a => "(D0Attribute " ++ text a.name ++ " " ++ attributeType a.type ++ ")") ++ ")"
  | .fact f => "(D0Fact " ++ name f.relation ++ " " ++ list (f.values.map value) ++ ")"
  | .rule c => "(D0Rule " ++ atom c.head ++ " " ++ list (c.body.map premise) ++ ")"
  | .input n => "(D0Input " ++ name n ++ ")"
  | .output n => "(D0Output " ++ name n ++ ")"

def issue : ProgramStatic.Issue → String
  | .duplicateRelations => "DuplicateRelations"
  | .invalidDeclaration i => "(InvalidDeclaration " ++ toString i ++ ")"
  | .illTypedFact i => "(IllTypedFact " ++ toString i ++ ")"
  | .illTypedClause i => "(IllTypedClause " ++ toString i ++ ")"
  | .undeclaredInterface i => "(UndeclaredInterface " ++ toString i ++ ")"

def result (source packet : String) : String :=
  match Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogRuntimeCompiler.readProgram source packet with
  | .error _ => "ReadRefused"
  | .ok program => "(Read (D0Program " ++ list (program.statements.map statement) ++ ") " ++
      list ((ProgramStatic.diagnose program).map issue) ++ ")"

def main (arguments : List String) : IO Unit := do
  let [jobs] := arguments | throw (IO.userError "expected a job list")
  let mut count := 0
  for line in (← IO.FS.readFile jobs).splitOn "\n" do
    match line.splitOn "\t" with
    | [sourcePath, packetPath, outputPath] =>
      let source ← IO.FS.readFile sourcePath
      let packet ← IO.FS.readFile packetPath
      IO.FS.writeFile outputPath ("(= (lean:result) " ++ result source packet ++ ")\n")
      count := count + 1
    | _ => pure ()
  IO.println s!"read {count} D0 packets"
