import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Generated wire for MM2 typed native refinement

This wire exports the source-derived schemas that the runtime must consume.
Unlike the earlier four-kind projection, it retains each known head, total
arity, and ordered argument roles.  Runtime code is expected to be a generic
executor of these bytes; it must not reconstruct MM2 declarations privately.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeWire

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement

def renderRole : Role → String
  | .atom => "atom"
  | .key => "key"
  | .pattern => "pattern"
  | .template => "template"
  | .inputSpec => "input-spec"
  | .inputFactor => "input-factor"
  | .outputSpec => "output-spec"
  | .outputSink => "output-sink"

def renderRoles (roles : List Role) : String :=
  String.join (roles.map fun role => " " ++ renderRole role)

def renderSchema (schema : FormSchema) : String :=
  "  (form \"" ++ schema.head ++ "\" " ++
    toString schema.totalArity ++ renderRoles schema.argumentRoles ++ ")\n"

def renderSchemas (source : List FormSchema) : String :=
  String.join (source.map renderSchema)

/-- Canonical typed-native artifact generated from the maintained sources. -/
def wire : String :=
  "(GSLTTypedNativeV1\n" ++
  "  (syntax-name \"" ++
    Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT.mm2Syntax.name ++
    "\")\n" ++
  "  (execution-name \"" ++ Execution.source.name ++ "\")\n" ++
  "  (execution-profile \"" ++ Execution.source.profile ++ "\")\n" ++
  "  (cursor-name \"" ++ Cursor.source.name ++ "\")\n" ++
  "  (cursor-version \"" ++ Cursor.source.version ++ "\")\n" ++
  "  (action-encoding \"" ++ Cursor.source.actionEncoding ++ "\")\n" ++
  "  (quoted-worker \"" ++ Cursor.source.quotedRuleHead ++ "\" " ++
    toString Cursor.source.quotedRuleArity ++ " " ++
    toString Cursor.source.quotedTagArity ++ ")\n" ++
  renderSchemas schemas ++
  "  (input-compat \"" ++ Execution.source.input.compatibility.interface ++
    "\" variadic pattern)\n" ++
  "  (input-explicit \"" ++ Execution.source.input.explicitHead ++
    "\" variadic input-factor)\n" ++
  renderSchemas inputProviderSchemas ++
  "  (output-compat \"" ++ Execution.source.output.compatibility.interface ++
    "\" variadic template)\n" ++
  "  (output-explicit \"" ++ Execution.source.output.explicitHead ++
    "\" variadic output-sink)\n" ++
  renderSchemas outputProviderSchemas ++
  ")\n"

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

theorem wire_source_links_exact :
    Cursor.source.syntaxName =
        Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT.mm2Syntax.name ∧
      Cursor.source.executionName = Execution.source.name ∧
      Cursor.source.executionProfile = Execution.source.profile := by
  decide +kernel

theorem wire_contains_source_compiled_schemas :
    renderSchemas schemas =
      renderSchemas
        (schemasFrom Execution.source Cursor.source
          (by decide) (by decide) (by decide) (by decide) (by decide)) := by
  rfl

theorem wire_contains_exact_provider_schemas :
    inputProviderSchemas =
        Execution.source.input.explicitSources.map (providerSchema .pattern) ∧
      outputProviderSchemas =
        (Execution.source.output.coreSinks ++
          Execution.source.output.extensionSinks).map
            (providerSchema .template) := by
  exact ⟨rfl, rfl⟩

theorem wire_contains_exact_quoted_worker_shape :
    Cursor.source.quotedRuleHead = "step" ∧
      Cursor.source.quotedRuleArity = 3 ∧
      Cursor.source.quotedTagArity = 2 := by
  decide +kernel

private def changedExecution : Execution.Presentation := {
  Execution.source with
    workShell := { Execution.source.workShell with head := "changed-exec" } }

/-- Mutating the execution source changes the compiled schema bytes. -/
theorem changed_execution_source_changes_schema_wire :
    renderSchema (workSchemaFrom changedExecution) ≠
      renderSchema workSchema := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_nonempty
#print axioms wire_source_links_exact
#print axioms wire_contains_source_compiled_schemas
#print axioms wire_contains_exact_provider_schemas
#print axioms wire_contains_exact_quoted_worker_shape
#print axioms changed_execution_source_changes_schema_wire

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TypedNativeWire
