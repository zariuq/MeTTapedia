import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRPrologSyntax

/-! Write the ground CHR source reader's operator table as MeTTa data. The
packet labels `pl:apply:N` and `pl:operator:N` index this table, so a reader
written in MeTTa uses the same operators as the source grammar. -/

open Mettapedia.GSLT.LanguageDef.ModuleFormat
open Mettapedia.Logic.Prolog

def specifier : ReaderOperator.Specifier → String
  | .fx => "fx" | .fy => "fy" | .xf => "xf" | .yf => "yf"
  | .xfx => "xfx" | .xfy => "xfy" | .yfx => "yfx"

/-- A MeTTa string literal for an operator name: only `"` and `\` need escapes. -/
def quote (name : String) : String :=
  "\"" ++ String.join (name.toList.map fun c =>
    if c = '"' then "\\\"" else if c = '\\' then "\\\\" else c.toString) ++ "\""

def main (arguments : List String) : IO Unit := do
  let [path] := arguments | throw (IO.userError "expected the output path")
  let rows := CHRPrologSyntax.profile.operators.zipIdx.map fun (op, index) =>
    s!"(= (c0:operator {index}) ({quote op.name} {specifier op.specifier} {op.priority.value}))"
  IO.FS.writeFile path (String.intercalate "\n"
    ("; Generated from the ground CHR source profile; do not edit." :: rows) ++ "\n")
  IO.println s!"wrote {rows.length} operators"
