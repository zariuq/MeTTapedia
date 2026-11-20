import Mettapedia.Languages.MeTTa.Experimental.DerivedTransformForms.Lowering
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxCommand

/-! File driver for the candidate grammars and retained-packet expansion. -/

open Mettapedia.Languages.MeTTa
open Experimental.DerivedTransformForms
open Mettapedia.GSLT.LanguageDef.ModuleFormat
open OSLFCore (Atom)

def render : Atom → String
  | .symbol word => word
  | .var word => "$" ++ word
  | .grounded (.string value) => reprStr value
  | .grounded value => value.toString
  | .expression fields => "(" ++ String.intercalate " " (fields.map render) ++ ")"
termination_by value => sizeOf value

def surface (name : String) : IO Presentations.Surface :=
  match name with
  | "expression" => pure .expression
  | "interaction" => pure .interaction
  | _ => throw (IO.userError "expected expression or interaction")

def lowerPacket (style : Presentations.Surface) (sourcePath packetPath outputPath : String) : IO Unit := do
  let .ok [.expression [.symbol "result", packet, .symbol "nil"]] :=
      PeTTa.SpaceSemantics.readSource (← IO.FS.readFile packetPath)
    | throw (IO.userError "expected one explicitly selected whole-input packet")
  let input ← IO.FS.readFile sourcePath
  let .ok result := Lowering.accepted style input packet
    | throw (IO.userError s!"source lowering refused: {reprStr (Lowering.accepted style input packet)}")
  let target := result.toPeTTa
  let serialized := render target
  unless PeTTa.SpaceSemantics.readSource serialized == .ok [target] do
    throw (IO.userError "expanded source does not retain its atom representation")
  if ← (System.FilePath.mk outputPath).pathExists then throw (IO.userError "output already exists")
  IO.FS.writeFile outputPath ("!" ++ serialized ++ "\n")
  IO.println serialized

def main (arguments : List String) : IO Unit := do
  match arguments with
  | "ambiguity" :: operations =>
      SourceSyntaxCommand.run Presentations.AmbiguityControl.Ambiguity.library
        Presentations.AmbiguityControl.Ambiguity.module operations
  | "export" :: name :: directory :: [] =>
      let style ← surface name
      let some description := Presentations.description? style
        | throw (IO.userError "grammar did not elaborate")
      if ← (System.FilePath.mk directory).pathExists then throw (IO.userError "output already exists")
      SourceSyntaxNativePlan.exportDescription description [] directory
  | "lower" :: name :: sourcePath :: packetPath :: outputPath :: [] =>
      lowerPacket (← surface name) sourcePath packetPath outputPath
  | "normalize" :: inputPath :: outputPath :: [] =>
      let .ok atoms := PeTTa.SpaceSemantics.readSource (← IO.FS.readFile inputPath)
        | throw (IO.userError "output is not a finite source answer sequence")
      if ← (System.FilePath.mk outputPath).pathExists then throw (IO.userError "output already exists")
      IO.FS.writeFile outputPath (String.intercalate "\n" (atoms.map render) ++ "\n")
  | "forest" :: name :: sourcePath :: forestPath :: identityPath :: [] =>
      let style ← surface name
      match style with
      | .expression =>
          SourceSyntaxCommand.run Presentations.ExpressionSurface.Expressions.library
            Presentations.ExpressionSurface.Expressions.module ["forest", sourcePath, forestPath, identityPath]
      | .interaction =>
          SourceSyntaxCommand.run Presentations.InteractionSurface.Interactions.library
            Presentations.InteractionSurface.Interactions.module ["forest", sourcePath, forestPath, identityPath]
  | "coverage" :: name :: sourcePath :: forestPath :: identityPath :: rounds :: [] =>
      let style ← surface name
      match style with
      | .expression =>
          SourceSyntaxCommand.run Presentations.ExpressionSurface.Expressions.library
            Presentations.ExpressionSurface.Expressions.module ["coverage", sourcePath, forestPath, identityPath, rounds]
      | .interaction =>
          SourceSyntaxCommand.run Presentations.InteractionSurface.Interactions.library
            Presentations.InteractionSurface.Interactions.module ["coverage", sourcePath, forestPath, identityPath, rounds]
  | "catalogue" :: name :: sourcePath :: forestPath :: identityPath :: packetsPath :: rounds :: [] =>
      let style ← surface name
      match style with
      | .expression =>
          SourceSyntaxCommand.run Presentations.ExpressionSurface.Expressions.library
            Presentations.ExpressionSurface.Expressions.module
              ["catalogue", sourcePath, forestPath, identityPath, packetsPath, rounds]
      | .interaction =>
          SourceSyntaxCommand.run Presentations.InteractionSurface.Interactions.library
            Presentations.InteractionSurface.Interactions.module
              ["catalogue", sourcePath, forestPath, identityPath, packetsPath, rounds]
  | _ => throw (IO.userError "expected export, lower, normalize, forest, coverage or catalogue with surface and paths")
