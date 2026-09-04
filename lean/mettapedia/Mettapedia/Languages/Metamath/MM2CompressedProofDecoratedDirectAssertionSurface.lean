import Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
import Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
import Mettapedia.Languages.ProcessCalculi.MORK.SupportedExecErasure

/-!
# Decorated speculative direct-assertion surface

The ordered verifier decorates the compact assertion launcher with a finite
normal-machine handoff before applying speculative lookup.  Consequently its
direct assertion probe has one additional owned bridge premise and one
additional opaque rule output.  This module exposes that actual compiler
result as a structured directive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeHeapLookupCanary
open Mettapedia.Languages.Metamath.MM2CompressedProofSpeculativeOrderedPresentation
open Mettapedia.Languages.ProcessCalculi.MORK

def decoratedDirectAssertionBridgeCaptureTemplate : Atom :=
  .expression
    [.symbol "mm-internal-compressed-normal-dispatch-bridge",
      .var "normal-bridge-rule"]

def decoratedDirectAssertionPatterns : List Atom :=
  directAssertionPatterns ++ [decoratedDirectAssertionBridgeCaptureTemplate]

def decoratedDirectAssertionSinks : List Sink :=
  directAssertionSinks ++ [.add (.var "normal-bridge-rule")]

def decoratedDirectAssertionRule : Atom :=
  decoratedSpeculativeBody.selected.artifact.directOpaqueRule

/-- Cursor fallback selected from the same decorated source presentation.
It differs from the calibration assertion handler because it also captures
the normal-machine bridge. -/
def decoratedCursorAssertionRule : Atom :=
  decoratedSpeculativeBody.selected.artifact.sourceOpaqueRule

private theorem decoratedDirectAssertionRule_supported :
    (extractSupportedSourceExecFact decoratedDirectAssertionRule).isSome =
      true := by
  decide +kernel

def decoratedDirectAssertionDirective : SourceExecFact :=
  (extractSupportedSourceExecFact decoratedDirectAssertionRule).get
    (by simpa using decoratedDirectAssertionRule_supported)

private theorem decoratedCursorAssertionRule_supported :
    (extractSupportedSourceExecFact decoratedCursorAssertionRule).isSome =
      true := by
  decide +kernel

def decoratedCursorAssertionDirective : SourceExecFact :=
  (extractSupportedSourceExecFact decoratedCursorAssertionRule).get
    (by simpa using decoratedCursorAssertionRule_supported)

theorem extract_decoratedDirectAssertionRule_exact :
    extractSupportedSourceExecFact decoratedDirectAssertionRule =
      some decoratedDirectAssertionDirective := by
  unfold decoratedDirectAssertionDirective
  exact (Option.some_get
    (by simpa using decoratedDirectAssertionRule_supported)).symm

theorem extract_decoratedCursorAssertionRule_exact :
    extractSupportedSourceExecFact decoratedCursorAssertionRule =
      some decoratedCursorAssertionDirective := by
  unfold decoratedCursorAssertionDirective
  exact (Option.some_get
    (by simpa using decoratedCursorAssertionRule_supported)).symm

theorem decoratedDirectAssertionDirective_atom_exact :
    decoratedDirectAssertionDirective.atom = decoratedDirectAssertionRule := by
  exact extractSupportedSourceExecFact_atom
    extract_decoratedDirectAssertionRule_exact

theorem decoratedDirectAssertionDirective_decodes :
    extractSupportedSourceExecFact decoratedDirectAssertionDirective.atom =
      some decoratedDirectAssertionDirective := by
  rw [decoratedDirectAssertionDirective_atom_exact]
  exact extract_decoratedDirectAssertionRule_exact

theorem decoratedDirectAssertionDirective_not_predecessor_shape
    (tail : List Atom) :
    decoratedDirectAssertionDirective.atom ≠
        .expression (.symbol "mm-compressed-step-pending" :: tail) ∧
      decoratedDirectAssertionDirective.atom ≠
        .expression (.symbol "mm-compressed-heap-lookup" :: tail) := by
  constructor
  · exact supportedExecAtom_ne_expression_head
      decoratedDirectAssertionDirective_decodes
      "mm-compressed-step-pending" tail (by decide)
  · exact supportedExecAtom_ne_expression_head
      decoratedDirectAssertionDirective_decodes
      "mm-compressed-heap-lookup" tail (by decide)

theorem decoratedCursorAssertionDirective_atom_exact :
    decoratedCursorAssertionDirective.atom = decoratedCursorAssertionRule := by
  exact extractSupportedSourceExecFact_atom
    extract_decoratedCursorAssertionRule_exact

theorem decoratedDirectAssertionDirective_input_exact :
    decoratedDirectAssertionDirective.rule.input =
      .compat (mkPattern decoratedDirectAssertionPatterns) := by
  decide +kernel

theorem decoratedDirectAssertionDirective_sinks_exact :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      decoratedDirectAssertionSinks := by
  decide +kernel

theorem decoratedDirectAssertionDirective_guards_exact :
    decoratedDirectAssertionDirective.rule.guards = [] := by
  decide +kernel

def decoratedDirectAssertionBridgeCaptureRow : Atom :=
  .expression
    [.symbol "mm-internal-compressed-normal-dispatch-bridge",
      compressedNormalDispatchBridgeRule]

#print axioms extract_decoratedDirectAssertionRule_exact
#print axioms decoratedDirectAssertionDirective_decodes
#print axioms decoratedDirectAssertionDirective_not_predecessor_shape
#print axioms extract_decoratedCursorAssertionRule_exact
#print axioms decoratedDirectAssertionDirective_atom_exact
#print axioms decoratedCursorAssertionDirective_atom_exact
#print axioms decoratedDirectAssertionDirective_input_exact
#print axioms decoratedDirectAssertionDirective_sinks_exact
#print axioms decoratedDirectAssertionDirective_guards_exact

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
