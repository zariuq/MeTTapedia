import Mettapedia.GSLT.Parsing.TptpOfficialRecordProjectionSource
import Mathlib.Tactic

/-!
# Structural round trips for canonical TPTP records

The public TPTP reader uses source spans as metadata.  Canonical printing may
change those spans while preserving the ordered record structure.  This file
defines that normalization and proves that the physical public-value codec is
left-invertible after normalization.  Duplicate occurrences and their order
remain visible.

The final contract inspects selected equations of the authored canonical text
printer: file/list traversal, every top-level record family, includes, binary
connectives, and binding forms.  Concrete text parse/print behavior is tested
by the executable reader gates; this theorem does not assume native C.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.TptpCanonicalPrintSource

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.GSLT.Parsing.TptpOfficialCompositionSource (app equation?)
open Mettapedia.GSLT.Parsing.TptpOfficialRecordProjectionSource

def zeroSpan : SExpr := app "tptp-rec:span" [.atom "0", .atom "0"]

def normalizeInput : Input → Input
  | .annotated family name role formula annotation _ =>
      .annotated family name role formula annotation zeroSpan
  | .includeRecord path selection qualifier _ =>
      .includeRecord path selection qualifier zeroSpan

def normalizeFile (file : File) : File :=
  { inputs := file.inputs.map normalizeInput, span := zeroSpan }

def structuralRender (file : File) : SExpr := encodeFile (normalizeFile file)

def structuralRead (value : SExpr) : Option File := decodeFile value

@[simp] theorem structuralRead_render (file : File) :
    structuralRead (structuralRender file) = some (normalizeFile file) := by
  simp [structuralRead, structuralRender]

theorem structural_roundtrip_preserves_duplicates
    (input : Input) (span : SExpr) :
    structuralRead
        (structuralRender { inputs := [input, input], span := span }) =
      some (normalizeFile { inputs := [input, input], span := span }) := by
  exact structuralRead_render _

structure SourceDocument where
  identity : SExpr
  digest : String
  text : String
  records : File
  deriving DecidableEq, Repr

def recoverOriginalText (document : SourceDocument) : String := document.text

@[simp] theorem original_spelling_recovery
    (identity : SExpr) (digest text : String) (records : File) :
    recoverOriginalText { identity, digest, text, records } = text := rfl

/-! ## Exact authored-source qualification contract -/

def sourceString (value : String) : SExpr := .atom ("\"" ++ value ++ "\"")

def printerInputLeft (constructor : String) : SExpr :=
  app "tptp-print-v1:input"
    [app constructor
      [.atom "?name", .atom "?role", .atom "?formula", .atom "?ann",
       .atom "?span"]]

def printerAnnotatedRight (family : String) : SExpr :=
  app "tptp-print-v1:annotated"
    [sourceString family, .atom "?name", .atom "?role", .atom "?formula",
     .atom "?ann"]

def printerClauseRight (constructor : String) : SExpr :=
  app constructor
    [.atom "?name", .atom "?role", .atom "?formula", .atom "?ann"]

def printerBinaryLeft (constructor : String) : SExpr :=
  app "tptp-print-v1:expr"
    [app constructor [.atom "?left", .atom "?right"]]

def printerBinaryRight (token : String) : SExpr :=
  app "tptp-print-v1:binary"
    [sourceString token, .atom "?left", .atom "?right"]

def printerQuantifierLeft (constructor : String) : SExpr :=
  app "tptp-print-v1:expr"
    [app constructor [.atom "?vars", .atom "?body"]]

def printerQuantifierRight (token : String) : SExpr :=
  app "tptp-print-v1:quant"
    [sourceString token, .atom "?vars", .atom "?body"]

def AuthoredCanonicalPrintSourceExact (printerSyntax : SExpr) : Prop :=
    equation? printerSyntax 4 =
      some
        (app "tptp-print-v1:document" [.atom "?file"],
         app "bnf-v1:text->string"
           [app "tptp-print-v1:file" [.atom "?file"]]) ∧
    equation? printerSyntax 5 =
      some
        (app "tptp-print-v1:file"
           [app "tptp-rec:file" [.atom "?inputs", .atom "?span"]],
         app "tptp-print-v1:inputs" [.atom "?inputs"]) ∧
    equation? printerSyntax 6 =
      some
        (app "tptp-print-v1:inputs" [app "tptp-rec:inputs-nil" []],
         app "bnf-v1:text-nil" []) ∧
    equation? printerSyntax 7 =
      some
        (app "tptp-print-v1:inputs"
           [app "tptp-rec:inputs-cons" [.atom "?head", .atom "?tail"]],
         app "tptp-print-v1:cat3"
           [app "tptp-print-v1:input" [.atom "?head"],
            app "bnf-v1:string->text" [sourceString "\\n"],
            app "tptp-print-v1:inputs" [.atom "?tail"]]) ∧
    equation? printerSyntax 8 =
      some (printerInputLeft "tptp-rec:fof", printerAnnotatedRight "fof") ∧
    equation? printerSyntax 9 =
      some
        (printerInputLeft "tptp-rec:cnf",
         printerClauseRight "tptp-print-v1:annotated-cnf") ∧
    equation? printerSyntax 10 =
      some (printerInputLeft "tptp-rec:tff", printerAnnotatedRight "tff") ∧
    equation? printerSyntax 11 =
      some (printerInputLeft "tptp-rec:thf", printerAnnotatedRight "thf") ∧
    equation? printerSyntax 12 =
      some
        (printerInputLeft "tptp-rec:tcf",
         printerClauseRight "tptp-print-v1:annotated-tcf") ∧
    equation? printerSyntax 13 =
      some (printerInputLeft "tptp-rec:tpi", printerAnnotatedRight "tpi") ∧
    equation? printerSyntax 28 =
      some
        (app "tptp-print-v1:input"
           [app "tptp-rec:include"
             [.atom "?file", .atom "?selection", .atom "?qualification",
              .atom "?span"]],
         app "tptp-print-v1:cat4"
           [app "bnf-v1:string->text" [sourceString "include("],
            app "tptp-print-v1:word" [.atom "?file"],
            app "tptp-print-v1:include-tail"
              [.atom "?selection", .atom "?qualification"],
            app "bnf-v1:string->text" [sourceString ")."]]) ∧
    equation? printerSyntax 105 =
      some (printerBinaryLeft "tptp-rec:equals", printerBinaryRight "=") ∧
    equation? printerSyntax 106 =
      some
        (printerBinaryLeft "tptp-rec:not-equals", printerBinaryRight "!=") ∧
    equation? printerSyntax 107 =
      some (printerBinaryLeft "tptp-rec:and", printerBinaryRight "&") ∧
    equation? printerSyntax 108 =
      some (printerBinaryLeft "tptp-rec:or", printerBinaryRight "|") ∧
    equation? printerSyntax 120 =
      some
        (printerQuantifierLeft "tptp-rec:forall",
         printerQuantifierRight "!") ∧
    equation? printerSyntax 121 =
      some
        (printerQuantifierLeft "tptp-rec:exists",
         printerQuantifierRight "?") ∧
    equation? printerSyntax 122 =
      some
        (printerQuantifierLeft "tptp-rec:lambda",
         printerQuantifierRight "^")

#print axioms structuralRead_render
#print axioms structural_roundtrip_preserves_duplicates
#print axioms original_spelling_recovery

end Mettapedia.GSLT.Parsing.TptpCanonicalPrintSource
