import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.ExperimentControls
import Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire
import Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-!
# Authored MM2 typed-graph decoder cursor wire

This file is the authority for the compact cursor presentation consumed by
the native typed-graph decoder.  The presentation links three existing
sources instead of copying their decisions into the neural implementation:

* the authored MM2 syntax `LanguageDef`;
* the authored support-transform execution presentation;
* the proved reflective-worker boundary of the OEIS fragment.

Unrestricted MM2 is open-world.  Therefore this cursor does not reject an
otherwise well-formed atom merely because it is not an executable directive
or an OEIS worker.  It exports semantic observations for recognized forms;
the syntax-derived atom/program frontier remains the admissibility authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TGADCursorWire

open Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxNTT

/-- A named head whose first non-head child addresses an MM2 relation key. -/
structure AddressedRelation where
  head : String
  arity : Nat
  addressPosition : Nat
  deriving Repr, DecidableEq

/-- Finite authored projection from MM2 semantic forms to decoder events. -/
structure CursorPresentation where
  name : String
  version : String
  syntaxName : String
  executionName : String
  executionProfile : String
  actionEncoding : String
  syntaxProjection : String
  quotedRuleHead : String
  quotedRuleArity : Nat
  quotedTagArity : Nat
  patternHead : String
  demand : AddressedRelation
  producer : AddressedRelation
  query : AddressedRelation
  result : AddressedRelation
  deriving Repr, DecidableEq

/-- The maintained MM2/OEIS cursor.  Execution name and profile are projected
from the same `ExecutionPresentation` used to generate the CeTTa profile. -/
def presentation : CursorPresentation :=
  { name := "MM2OEISReflectiveCursor"
    version := "1"
    syntaxName := mm2Syntax.name
    executionName :=
      Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.presentation.name
    executionProfile :=
      Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.presentation.profile
    actionEncoding := "native-sexpr-preorder-v1"
    syntaxProjection := "derive-native-ast-from-language-def"
    quotedRuleHead := "step"
    quotedRuleArity := 3
    quotedTagArity := 2
    patternHead := ","
    demand := ⟨"w", 4, 1⟩
    producer := ⟨"g", 5, 1⟩
    query := ⟨"query", 2, 1⟩
    result := ⟨"result", 3, 1⟩ }

private def renderRelation (role : String)
    (relation : AddressedRelation) : String :=
  "  (" ++ role ++ " " ++ relation.head ++ " " ++
    toString relation.arity ++ " " ++ toString relation.addressPosition ++ ")\n"

/-- Canonical, line-oriented input to the generic cursor compiler. -/
def render (source : CursorPresentation) : String :=
  "(GSLTTGADCursorV1\n" ++
  "  (name " ++ source.name ++ ")\n" ++
  "  (version " ++ source.version ++ ")\n" ++
  "  (syntax-name " ++ source.syntaxName ++ ")\n" ++
  "  (execution-name " ++ source.executionName ++ ")\n" ++
  "  (execution-profile " ++ source.executionProfile ++ ")\n" ++
  "  (action-encoding " ++ source.actionEncoding ++ ")\n" ++
  "  (syntax-projection " ++ source.syntaxProjection ++ ")\n" ++
  "  (quoted-rule " ++ source.quotedRuleHead ++ " " ++
    toString source.quotedRuleArity ++ " " ++
    toString source.quotedTagArity ++ " " ++ source.patternHead ++ ")\n" ++
  renderRelation "demand" source.demand ++
  renderRelation "producer" source.producer ++
  renderRelation "query" source.query ++
  renderRelation "result" source.result ++
  ")\n"

def wire : String := render presentation

theorem wire_nonempty : wire ≠ "" := by
  decide +kernel

theorem presentation_source_links_exact :
    presentation.syntaxName = mm2Syntax.name ∧
      presentation.executionName =
        Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.presentation.name ∧
      presentation.executionProfile =
        Mettapedia.Languages.ProcessCalculi.MORK.MM2ExecutionProfileWire.presentation.profile := by
  decide +kernel

theorem relation_inventory_exact :
    presentation.demand = ⟨"w", 4, 1⟩ ∧
      presentation.producer = ⟨"g", 5, 1⟩ ∧
      presentation.query = ⟨"query", 2, 1⟩ ∧
      presentation.result = ⟨"result", 3, 1⟩ := by
  decide +kernel

private def cursorWithoutProducer := {
  presentation with producer := ⟨"absent-producer", 5, 1⟩
}

/-- A semantic mutation changes generated cursor bytes. -/
theorem removing_producer_identity_changes_wire :
    render cursorWithoutProducer ≠ wire := by
  decide +kernel

def writeWire (path : System.FilePath) : IO Unit :=
  IO.FS.writeFile path wire

#print axioms wire_nonempty
#print axioms presentation_source_links_exact
#print axioms relation_inventory_exact
#print axioms removing_producer_identity_changes_wire

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2TGADCursorWire
