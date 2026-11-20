import Mettapedia.GSLT.LanguageDef.MacroExportComplete
import Mettapedia.GSLT.LanguageDef.MacroCheckedNarrowing

/-!
# The shipped macro libraries, as exported

Each library rule appears here exactly as `cesta check-macros` reports it; the
decoding and the admission of each are decided by the kernel, and Cesta's
admission test checks that these atoms are the ones the modules currently
produce. The laws below are stated about the source use (`invoke`) of each
decoded rule and hold for the readable export of every use by
`export_correct`: the `_export` corollaries state them for the block `lower`
produces. Each rule is in the declared forms of `MacroExportComplete`
(`_forms`), so every use of it has such an export and every header definition
of it is admitted.

The caller's code is abstract: a hypothesis says what each evaluated argument
yields and how it changes the caller-visible state. Implementation facts are
hypotheses on the `Profile`: the types the written type names denote and that
`int` represents `1`.
-/

namespace Mettapedia.GSLT.LanguageDef.MacroExportLibraries

open Mettapedia.GSLT.LanguageDef.MacroExportPlan
open Mettapedia.GSLT.LanguageDef.MacroExportStateful
open Mettapedia.GSLT.LanguageDef.MacroExportCorrect
open Mettapedia.GSLT.LanguageDef.MacroExportTheorem
open Mettapedia.GSLT.LanguageDef.MacroExportHeader
open Mettapedia.GSLT.LanguageDef.MacroExportComplete
open Mettapedia.Languages.C11

set_option autoImplicit false
set_option maxRecDepth 20000

/-! ## The rules -/

/-- The `tryNarrow` rule as `cesta check-macros` reports it for `macros/Narrowing.module`, theory `Checked`. -/
def tryNarrowAtom : Atom :=
  .list [(.symbol "rule"),
    (.text "TryNarrow"),
    (.text "try-narrow"),
    (.text "Expr"),
    (.list [(.symbol "Macro"),
       (.text "cesta-macro/3"),
       (.list [(.symbol "Profile"), (.text "gnu11")]),
       (.list [(.symbol "Ports"),
          (.list [(.symbol "CompilerBuiltin"),
             (.symbol "conversion"),
             (.text "__builtin_add_overflow")])]),
       (.list [(.symbol "Arguments"),
          (.list [(.symbol "Arg"),
             (.symbol "source"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "target"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "value"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "source")])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "out"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "target")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])])]),
       (.list [(.symbol "Result"), (.list [(.symbol "CType"), (.symbol "int")]), (.text "value")]),
       (.list [(.symbol "Locals"),
          (.list [(.symbol "Local"), (.symbol "converted"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "accepted"), (.text "ordinary")])]),
       (.list [(.symbol "Template"),
          (.list [(.symbol "block"),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "target")]),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "converted")])]),
             (.list [(.symbol "var"),
                (.symbol "int"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.symbol "0")]),
             (.list [(.symbol "if"),
                (.list [(.symbol "!"),
                   (.list [(.symbol "call"),
                      (.list [(.symbol "CompilerRef"), (.symbol "conversion")]),
                      (.list [(.symbol "Argument"), (.symbol "value")]),
                      (.symbol "0"),
                      (.list [(.symbol "&"),
                         (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "converted")])])])]),
                (.list [(.symbol "block"),
                   (.list [(.symbol "="),
                      (.list [(.symbol "Argument"), (.symbol "out")]),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "converted")])]),
                   (.list [(.symbol "="),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                      (.symbol "1")])])]),
             (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")])])])])]

def tryNarrow : Rule where
  label := "TryNarrow"
  head := "try-narrow"
  expression := true
  gnu := true
  arguments := [⟨"source", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"target", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"value", .value, true, .list [.symbol "CType", .typeArg 0]⟩,
    ⟨"out", .modifiable, true, .list [.symbol "CType", .typeArg 1]⟩]
  result := .list [.symbol "CType", .symbol "int"]
  locals := [("converted", "ordinary"), ("accepted", "ordinary")]
  body := .list [.symbol "block",
              .list [.symbol "var", .typeArg 1, .localRef 0],
              .list [.symbol "var", .symbol "int", .localRef 1, .symbol "0"],
              .list [.symbol "if",
                .list [.symbol "!",
                  .list [.symbol "call",
                    .symbol "__builtin_add_overflow",
                    .arg 2,
                    .symbol "0",
                    .list [.symbol "&", .localRef 0]]],
                .list [.symbol "block",
                  .list [.symbol "=", .arg 3, .localRef 0],
                  .list [.symbol "=", .localRef 1, .symbol "1"]]],
              .localRef 1]

theorem tryNarrow_decodes : decodeRule tryNarrowAtom = some tryNarrow := rfl

theorem tryNarrow_admitted : admittedRule tryNarrow = true := by decide

/-- The `arrayBytes` rule as `cesta check-macros` reports it for `macros/Sizes.module`, theory `Checked`. -/
def arrayBytesAtom : Atom :=
  .list [(.symbol "rule"),
    (.text "ArrayBytes"),
    (.text "array-bytes"),
    (.text "Expr"),
    (.list [(.symbol "Macro"),
       (.text "cesta-macro/3"),
       (.list [(.symbol "Profile"), (.text "gnu11")]),
       (.list [(.symbol "Ports"),
          (.list [(.symbol "CompilerBuiltin"),
             (.symbol "multiply"),
             (.text "__builtin_mul_overflow")])]),
       (.list [(.symbol "Arguments"),
          (.list [(.symbol "Arg"),
             (.symbol "element"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "count"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "size"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "length"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "out"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "size")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])])]),
       (.list [(.symbol "Result"), (.list [(.symbol "CType"), (.symbol "int")]), (.text "value")]),
       (.list [(.symbol "Locals"),
          (.list [(.symbol "Local"), (.symbol "bytes"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "accepted"), (.text "ordinary")])]),
       (.list [(.symbol "Template"),
          (.list [(.symbol "block"),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "size")]),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")])]),
             (.list [(.symbol "var"),
                (.symbol "int"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.symbol "0")]),
             (.list [(.symbol "if"),
                (.list [(.symbol "!"),
                   (.list [(.symbol "call"),
                      (.list [(.symbol "CompilerRef"), (.symbol "multiply")]),
                      (.list [(.symbol "Argument"), (.symbol "length")]),
                      (.list [(.symbol "sizeof"),
                         (.symbol "type"),
                         (.list [(.symbol "TypeArgument"), (.symbol "element")])]),
                      (.list [(.symbol "&"),
                         (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")])])])]),
                (.list [(.symbol "block"),
                   (.list [(.symbol "="),
                      (.list [(.symbol "Argument"), (.symbol "out")]),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")])]),
                   (.list [(.symbol "="),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                      (.symbol "1")])])]),
             (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")])])])])]

def arrayBytes : Rule where
  label := "ArrayBytes"
  head := "array-bytes"
  expression := true
  gnu := true
  arguments := [⟨"element", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"count", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"size", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"length", .value, true, .list [.symbol "CType", .typeArg 1]⟩,
    ⟨"out", .modifiable, true, .list [.symbol "CType", .typeArg 2]⟩]
  result := .list [.symbol "CType", .symbol "int"]
  locals := [("bytes", "ordinary"), ("accepted", "ordinary")]
  body := .list [.symbol "block",
              .list [.symbol "var", .typeArg 2, .localRef 0],
              .list [.symbol "var", .symbol "int", .localRef 1, .symbol "0"],
              .list [.symbol "if",
                .list [.symbol "!",
                  .list [.symbol "call",
                    .symbol "__builtin_mul_overflow",
                    .arg 3,
                    .list [.symbol "sizeof", .symbol "type", .typeArg 0],
                    .list [.symbol "&", .localRef 0]]],
                .list [.symbol "block",
                  .list [.symbol "=", .arg 4, .localRef 0],
                  .list [.symbol "=", .localRef 1, .symbol "1"]]],
              .localRef 1]

theorem arrayBytes_decodes : decodeRule arrayBytesAtom = some arrayBytes := rfl

theorem arrayBytes_admitted : admittedRule arrayBytes = true := by decide

/-- The `doubledCapacity` rule as `cesta check-macros` reports it for `macros/Sizes.module`, theory `Checked`. -/
def doubledCapacityAtom : Atom :=
  .list [(.symbol "rule"),
    (.text "DoubledCapacity"),
    (.text "doubled-capacity"),
    (.text "Expr"),
    (.list [(.symbol "Macro"),
       (.text "cesta-macro/3"),
       (.list [(.symbol "Profile"), (.text "gnu11")]),
       (.list [(.symbol "Ports"),
          (.list [(.symbol "CompilerBuiltin"), (.symbol "add"), (.text "__builtin_add_overflow")])]),
       (.list [(.symbol "Arguments"),
          (.list [(.symbol "Arg"),
             (.symbol "count"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "initial"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "capacity"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "out"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])])]),
       (.list [(.symbol "Result"), (.list [(.symbol "CType"), (.symbol "int")]), (.text "value")]),
       (.list [(.symbol "Locals"),
          (.list [(.symbol "Local"), (.symbol "next"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "accepted"), (.text "ordinary")])]),
       (.list [(.symbol "Template"),
          (.list [(.symbol "block"),
             (.list [(.symbol "_Static_assert"),
                (.list [(.symbol ">"),
                   (.list [(.symbol "cast"),
                      (.list [(.symbol "TypeArgument"), (.symbol "count")]),
                      (.list [(.symbol "-"), (.symbol "1")])]),
                   (.symbol "0")]),
                (.text "\"doubled-capacity count must be unsigned\"")]),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "count")]),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "next")]),
                (.list [(.symbol "Argument"), (.symbol "initial")])]),
             (.list [(.symbol "var"),
                (.symbol "int"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.symbol "1")]),
             (.list [(.symbol "if"),
                (.list [(.symbol "Argument"), (.symbol "capacity")]),
                (.list [(.symbol "if"),
                   (.list [(.symbol "call"),
                      (.list [(.symbol "CompilerRef"), (.symbol "add")]),
                      (.list [(.symbol "Argument"), (.symbol "capacity")]),
                      (.list [(.symbol "Argument"), (.symbol "capacity")]),
                      (.list [(.symbol "&"),
                         (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "next")])])]),
                   (.list [(.symbol "="),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                      (.symbol "0")])])]),
             (.list [(.symbol "if"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.list [(.symbol "="),
                   (.list [(.symbol "Argument"), (.symbol "out")]),
                   (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "next")])])]),
             (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")])])])])]

def doubledCapacity : Rule where
  label := "DoubledCapacity"
  head := "doubled-capacity"
  expression := true
  gnu := true
  arguments := [⟨"count", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"initial", .value, true, .list [.symbol "CType", .typeArg 0]⟩,
    ⟨"capacity", .value, true, .list [.symbol "CType", .typeArg 0]⟩,
    ⟨"out", .modifiable, true, .list [.symbol "CType", .typeArg 0]⟩]
  result := .list [.symbol "CType", .symbol "int"]
  locals := [("next", "ordinary"), ("accepted", "ordinary")]
  body := .list [.symbol "block",
              .list [.symbol "_Static_assert",
                .list [.symbol ">",
                  .list [.symbol "cast", .typeArg 0, .list [.symbol "-", .symbol "1"]],
                  .symbol "0"],
                .text "\"doubled-capacity count must be unsigned\""],
              .list [.symbol "var", .typeArg 0, .localRef 0, .arg 1],
              .list [.symbol "var", .symbol "int", .localRef 1, .symbol "1"],
              .list [.symbol "if",
                .arg 2,
                .list [.symbol "if",
                  .list [.symbol "call",
                    .symbol "__builtin_add_overflow",
                    .arg 2,
                    .arg 2,
                    .list [.symbol "&", .localRef 0]],
                  .list [.symbol "=", .localRef 1, .symbol "0"]]],
              .list [.symbol "if", .localRef 1, .list [.symbol "=", .arg 3, .localRef 0]],
              .localRef 1]

theorem doubledCapacity_decodes : decodeRule doubledCapacityAtom = some doubledCapacity := rfl

theorem doubledCapacity_admitted : admittedRule doubledCapacity = true := by decide

/-- The `push` rule as `cesta check-macros` reports it for `macros/Worklists.module`, theory `Growable`. -/
def pushAtom : Atom :=
  .list [(.symbol "rule"),
    (.text "Push"),
    (.text "worklist-push"),
    (.text "Expr"),
    (.list [(.symbol "Macro"),
       (.text "cesta-macro/3"),
       (.list [(.symbol "Profile"), (.text "gnu11")]),
       (.list [(.symbol "Ports"),
          (.list [(.symbol "CompilerBuiltin"), (.symbol "add"), (.text "__builtin_add_overflow")]),
          (.list [(.symbol "CompilerBuiltin"),
             (.symbol "multiply"),
             (.text "__builtin_mul_overflow")])]),
       (.list [(.symbol "Arguments"),
          (.list [(.symbol "Arg"),
             (.symbol "element"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "count"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "resize"),
             (.list [(.symbol "CType"),
                (.symbol "void"),
                (.list [(.symbol "*"),
                   (.list [(.symbol "function"),
                      (.list [(.symbol "c:ParenthesizedDeclarator"),
                         (.list [(.symbol "*"), (.symbol "TypeSlot")])]),
                      (.list [(.symbol "void"), (.list [(.symbol "*"), (.symbol "old")])]),
                      (.list [(.symbol "TypeArgument"), (.symbol "count")])])])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "buffer"),
             (.list [(.symbol "CType"),
                (.list [(.symbol "TypeArgument"), (.symbol "element")]),
                (.list [(.symbol "*"), (.symbol "TypeSlot")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "length"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "capacity"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "count")])]),
             (.text "addressable-modifiable"),
             (.list [(.symbol "Evaluation"), (.text "once")])]),
          (.list [(.symbol "Arg"),
             (.symbol "value"),
             (.list [(.symbol "CType"), (.list [(.symbol "TypeArgument"), (.symbol "element")])]),
             (.text "value"),
             (.list [(.symbol "Evaluation"), (.text "once")])])]),
       (.list [(.symbol "Result"), (.list [(.symbol "CType"), (.symbol "int")]), (.text "value")]),
       (.list [(.symbol "Locals"),
          (.list [(.symbol "Local"), (.symbol "next_capacity"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "bytes"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "replacement"), (.text "ordinary")]),
          (.list [(.symbol "Local"), (.symbol "accepted"), (.text "ordinary")])]),
       (.list [(.symbol "Template"),
          (.list [(.symbol "block"),
             (.list [(.symbol "_Static_assert"),
                (.list [(.symbol ">"),
                   (.list [(.symbol "cast"),
                      (.list [(.symbol "TypeArgument"), (.symbol "count")]),
                      (.list [(.symbol "-"), (.symbol "1")])]),
                   (.symbol "0")]),
                (.text "\"worklist count must be unsigned\"")]),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "count")]),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "next_capacity")])]),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "count")]),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")]),
                (.symbol "0")]),
             (.list [(.symbol "var"),
                (.list [(.symbol "TypeArgument"), (.symbol "element")]),
                (.list [(.symbol "*"),
                   (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "replacement")])])]),
             (.list [(.symbol "var"),
                (.symbol "int"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.symbol "1")]),
             (.list [(.symbol "if"),
                (.list [(.symbol "||"),
                   (.list [(.symbol "=="),
                      (.list [(.symbol "&"), (.list [(.symbol "Argument"), (.symbol "length")])]),
                      (.list [(.symbol "&"), (.list [(.symbol "Argument"), (.symbol "capacity")])])]),
                   (.list [(.symbol "||"),
                      (.list [(.symbol ">"),
                         (.list [(.symbol "Argument"), (.symbol "length")]),
                         (.list [(.symbol "Argument"), (.symbol "capacity")])]),
                      (.list [(.symbol "&&"),
                         (.list [(.symbol "Argument"), (.symbol "capacity")]),
                         (.list [(.symbol "!"), (.list [(.symbol "Argument"), (.symbol "buffer")])])])])]),
                (.list [(.symbol "="),
                   (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                   (.symbol "0")])]),
             (.list [(.symbol "if"),
                (.list [(.symbol "&&"),
                   (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                   (.list [(.symbol "=="),
                      (.list [(.symbol "Argument"), (.symbol "length")]),
                      (.list [(.symbol "Argument"), (.symbol "capacity")])])]),
                (.list [(.symbol "block"),
                   (.list [(.symbol "if"),
                      (.list [(.symbol "=="),
                         (.list [(.symbol "Argument"), (.symbol "capacity")]),
                         (.symbol "0")]),
                      (.list [(.symbol "="),
                         (.list [(.symbol "LocalRef"),
                            (.text "ordinary"),
                            (.symbol "next_capacity")]),
                         (.symbol "8")]),
                      (.list [(.symbol "if"),
                         (.list [(.symbol "call"),
                            (.list [(.symbol "CompilerRef"), (.symbol "add")]),
                            (.list [(.symbol "Argument"), (.symbol "capacity")]),
                            (.list [(.symbol "Argument"), (.symbol "capacity")]),
                            (.list [(.symbol "&"),
                               (.list [(.symbol "LocalRef"),
                                  (.text "ordinary"),
                                  (.symbol "next_capacity")])])]),
                         (.list [(.symbol "="),
                            (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                            (.symbol "0")])])]),
                   (.list [(.symbol "if"),
                      (.list [(.symbol "&&"),
                         (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                         (.list [(.symbol "call"),
                            (.list [(.symbol "CompilerRef"), (.symbol "multiply")]),
                            (.list [(.symbol "LocalRef"),
                               (.text "ordinary"),
                               (.symbol "next_capacity")]),
                            (.list [(.symbol "sizeof"),
                               (.symbol "type"),
                               (.list [(.symbol "TypeArgument"), (.symbol "element")])]),
                            (.list [(.symbol "&"),
                               (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")])])])]),
                      (.list [(.symbol "="),
                         (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                         (.symbol "0")])]),
                   (.list [(.symbol "if"),
                      (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                      (.list [(.symbol "block"),
                         (.list [(.symbol "="),
                            (.list [(.symbol "LocalRef"),
                               (.text "ordinary"),
                               (.symbol "replacement")]),
                            (.list [(.symbol "call"),
                               (.list [(.symbol "Argument"), (.symbol "resize")]),
                               (.list [(.symbol "Argument"), (.symbol "buffer")]),
                               (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "bytes")])])]),
                         (.list [(.symbol "if"),
                            (.list [(.symbol "!"),
                               (.list [(.symbol "LocalRef"),
                                  (.text "ordinary"),
                                  (.symbol "replacement")])]),
                            (.list [(.symbol "="),
                               (.list [(.symbol "LocalRef"),
                                  (.text "ordinary"),
                                  (.symbol "accepted")]),
                               (.symbol "0")]),
                            (.list [(.symbol "block"),
                               (.list [(.symbol "="),
                                  (.list [(.symbol "Argument"), (.symbol "buffer")]),
                                  (.list [(.symbol "LocalRef"),
                                     (.text "ordinary"),
                                     (.symbol "replacement")])]),
                               (.list [(.symbol "="),
                                  (.list [(.symbol "Argument"), (.symbol "capacity")]),
                                  (.list [(.symbol "LocalRef"),
                                     (.text "ordinary"),
                                     (.symbol "next_capacity")])])])])])])])]),
             (.list [(.symbol "if"),
                (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")]),
                (.list [(.symbol "block"),
                   (.list [(.symbol "="),
                      (.list [(.symbol "[]"),
                         (.list [(.symbol "Argument"), (.symbol "buffer")]),
                         (.list [(.symbol "Argument"), (.symbol "length")])]),
                      (.list [(.symbol "Argument"), (.symbol "value")])]),
                   (.list [(.symbol "++"), (.list [(.symbol "Argument"), (.symbol "length")])])])]),
             (.list [(.symbol "LocalRef"), (.text "ordinary"), (.symbol "accepted")])])])])]

def push : Rule where
  label := "Push"
  head := "worklist-push"
  expression := true
  gnu := true
  arguments := [⟨"element", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"count", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"resize", .value, true, .list [.symbol "CType",
        .symbol "void",
        .list [.symbol "*",
          .list [.symbol "function",
            .list [.symbol "c:ParenthesizedDeclarator", .list [.symbol "*", .symbol "TypeSlot"]],
            .list [.symbol "void", .list [.symbol "*", .symbol "old"]],
            .typeArg 1]]]⟩,
    ⟨"buffer", .modifiable, true, .list [.symbol "CType", .typeArg 0, .list [.symbol "*", .symbol "TypeSlot"]]⟩,
    ⟨"length", .modifiable, true, .list [.symbol "CType", .typeArg 1]⟩,
    ⟨"capacity", .modifiable, true, .list [.symbol "CType", .typeArg 1]⟩,
    ⟨"value", .value, true, .list [.symbol "CType", .typeArg 0]⟩]
  result := .list [.symbol "CType", .symbol "int"]
  locals := [("next_capacity", "ordinary"), ("bytes", "ordinary"), ("replacement", "ordinary"), ("accepted", "ordinary")]
  body := .list [.symbol "block",
              .list [.symbol "_Static_assert",
                .list [.symbol ">",
                  .list [.symbol "cast", .typeArg 1, .list [.symbol "-", .symbol "1"]],
                  .symbol "0"],
                .text "\"worklist count must be unsigned\""],
              .list [.symbol "var", .typeArg 1, .localRef 0],
              .list [.symbol "var", .typeArg 1, .localRef 1, .symbol "0"],
              .list [.symbol "var", .typeArg 0, .list [.symbol "*", .localRef 2]],
              .list [.symbol "var", .symbol "int", .localRef 3, .symbol "1"],
              .list [.symbol "if",
                .list [.symbol "||",
                  .list [.symbol "==", .list [.symbol "&", .arg 4], .list [.symbol "&", .arg 5]],
                  .list [.symbol "||",
                    .list [.symbol ">", .arg 4, .arg 5],
                    .list [.symbol "&&", .arg 5, .list [.symbol "!", .arg 3]]]],
                .list [.symbol "=", .localRef 3, .symbol "0"]],
              .list [.symbol "if",
                .list [.symbol "&&", .localRef 3, .list [.symbol "==", .arg 4, .arg 5]],
                .list [.symbol "block",
                  .list [.symbol "if",
                    .list [.symbol "==", .arg 5, .symbol "0"],
                    .list [.symbol "=", .localRef 0, .symbol "8"],
                    .list [.symbol "if",
                      .list [.symbol "call",
                        .symbol "__builtin_add_overflow",
                        .arg 5,
                        .arg 5,
                        .list [.symbol "&", .localRef 0]],
                      .list [.symbol "=", .localRef 3, .symbol "0"]]],
                  .list [.symbol "if",
                    .list [.symbol "&&",
                      .localRef 3,
                      .list [.symbol "call",
                        .symbol "__builtin_mul_overflow",
                        .localRef 0,
                        .list [.symbol "sizeof", .symbol "type", .typeArg 0],
                        .list [.symbol "&", .localRef 1]]],
                    .list [.symbol "=", .localRef 3, .symbol "0"]],
                  .list [.symbol "if",
                    .localRef 3,
                    .list [.symbol "block",
                      .list [.symbol "=",
                        .localRef 2,
                        .list [.symbol "call", .arg 2, .arg 3, .localRef 1]],
                      .list [.symbol "if",
                        .list [.symbol "!", .localRef 2],
                        .list [.symbol "=", .localRef 3, .symbol "0"],
                        .list [.symbol "block",
                          .list [.symbol "=", .arg 3, .localRef 2],
                          .list [.symbol "=", .arg 5, .localRef 0]]]]]]],
              .list [.symbol "if",
                .localRef 3,
                .list [.symbol "block",
                  .list [.symbol "=", .list [.symbol "[]", .arg 3, .arg 4], .arg 6],
                  .list [.symbol "++", .arg 4]]],
              .localRef 3]

theorem push_decodes : decodeRule pushAtom = some push := rfl

theorem push_admitted : admittedRule push = true := by decide

/-- The `probe` rule as `cesta check-macros` reports it for `macros/Probes.module`, theory `Switched`. -/
def probeAtom : Atom :=
  .list [(.symbol "rule"),
    (.text "Probe"),
    (.text "probe"),
    (.text "Statement"),
    (.list [(.symbol "Macro"),
       (.text "cesta-macro/3"),
       (.list [(.symbol "Profile"), (.text "gnu11")]),
       (.list [(.symbol "Ports"),
          (.list [(.symbol "CompilerBuiltin"), (.symbol "constant"), (.text "__builtin_constant_p")])]),
       (.list [(.symbol "Arguments"),
          (.list [(.symbol "Arg"),
             (.symbol "enabled"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])]),
          (.list [(.symbol "Arg"),
             (.symbol "effect"),
             (.list [(.symbol "CType"), (.symbol "void")]),
             (.text "syntax"),
             (.list [(.symbol "Evaluation"), (.text "syntax")])])]),
       (.list [(.symbol "Result"),
          (.list [(.symbol "CType"), (.symbol "void")]),
          (.text "statement")]),
       (.list [(.symbol "Locals")]),
       (.list [(.symbol "Template"),
          (.list [(.symbol "block"),
             (.list [(.symbol "_Static_assert"),
                (.list [(.symbol "call"),
                   (.list [(.symbol "CompilerRef"), (.symbol "constant")]),
                   (.list [(.symbol "Argument"), (.symbol "enabled")])]),
                (.text "\"probe switch must be a constant expression\"")]),
             (.list [(.symbol "?:"),
                (.list [(.symbol "Argument"), (.symbol "enabled")]),
                (.list [(.symbol "cast"),
                   (.symbol "void"),
                   (.list [(.symbol "Argument"), (.symbol "effect")])]),
                (.list [(.symbol "cast"), (.symbol "void"), (.symbol "0")])])])])])]

def probe : Rule where
  label := "Probe"
  head := "probe"
  expression := false
  gnu := true
  arguments := [⟨"enabled", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩,
    ⟨"effect", .syntax, false, .list [.symbol "CType", .symbol "void"]⟩]
  result := .list [.symbol "CType", .symbol "void"]
  locals := []
  body := .list [.symbol "block",
              .list [.symbol "_Static_assert",
                .list [.symbol "call", .symbol "__builtin_constant_p", .arg 0],
                .text "\"probe switch must be a constant expression\""],
              .list [.symbol "?:",
                .arg 0,
                .list [.symbol "cast", .symbol "void", .arg 1],
                .list [.symbol "cast", .symbol "void", .symbol "0"]]]

theorem probe_decodes : decodeRule probeAtom = some probe := rfl

theorem probe_admitted : admittedRule probe = true := by decide

/-! ## Facts the laws use -/

theorem interval_value (n : Int) (f : IntegerFormat) :
    ∃ m, convertInteger intervalReductionPolicy n (.integer f) = .value m := by
  cases f with
  | unsigned p h => exact ⟨_, rfl⟩
  | signed p h r =>
      unfold convertInteger
      dsimp only
      split
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩

theorem update_same (m : Memory) (l : Loc) (c : Cell) (h : m l = some c) : update m l c = m := by
  funext k
  by_cases hk : k = l
  · subst hk; simp [update, h]
  · simp [update, hk]

/-- What acquisition leaves of the exporter's names is a suffix of them. -/
theorem acquire_suffix {rule : Rule} {written : List Atom} : ∀ (slotsL : List (Nat × Argument))
    (supply : List String) (items : List Marked) (slotList : List (Nat × Marked)) (supply' : List String),
    acquire rule written slotsL supply = some (items, slotList, supply') → ∃ pre, supply = pre ++ supply'
  | [], supply, items, slotList, supply', h => by
      simp only [acquire, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨[], by simp [h.2.2]⟩
  | (i, a) :: rest, supply, items, slotList, supply', h => by
      by_cases hc : a.category = .syntax
      · obtain ⟨slots, hrest, -⟩ := acquire_syntax h hc
        exact acquire_suffix rest supply items slots supply' hrest
      · obtain ⟨n, s, ty, item, s2, initial, message, itemsRest, slots, rfl, hty, hrest, -⟩ :=
          acquire_evaluated h hc
        obtain ⟨-, preT, hs⟩ := admittedType_shape hty
        obtain ⟨preR, hs2⟩ := acquire_suffix rest s2 itemsRest slots supply' hrest
        exact ⟨n :: (preT ++ preR), by rw [hs, hs2]; simp⟩

/-- The names a lowering picks for a rule's locals are distinct, one per local. -/
theorem chosenLocals_nodup {rule : Rule} {written : List Atom} {supply : List String} {block : Marked}
    (lowered : lower rule written supply = some block) (distinct : supply.Nodup) :
    (chosenLocals rule written supply).Nodup ∧
      (chosenLocals rule written supply).length = rule.locals.length := by
  obtain ⟨acquired, slotList, s1, template, hacq, hk, -, -⟩ := lower_some lowered
  obtain ⟨pre, hsup⟩ := acquire_suffix _ supply acquired slotList s1 hacq
  have hs1 : s1.Nodup := by rw [hsup] at distinct; exact (List.nodup_append.mp distinct).2.1
  simp only [chosenLocals, hacq]
  exact ⟨hs1.sublist (List.take_sublist _ _), by simp [hk]⟩

theorem pair_of_nodup {l : List String} (hl : l.Nodup) (h2 : l.length = 2) :
    ∃ a b, l = [a, b] ∧ a ≠ b := by
  match l, hl, h2 with
  | [a, b], hl, _ => exact ⟨a, b, rfl, by simpa using hl⟩

/-! ## `try-narrow`: commit on success, keep the destination on failure -/

section TryNarrow

variable (profile : Profile) (S T v o : Atom) (operands : Nat → Operand) (st : State)
  (n : Int) (fS fT : IntegerFormat) (pub1 pub2 : Public) (l : Loc) (before : Int)

/-- The destination cell after narrowing `n` into a cell holding `before`. -/
def narrowed (fT : IntegerFormat) (n before : Int) : Cell :=
  { type := .integer fT, value := some (.int fT (MacroCheckedNarrowing.execute fT n before).2) }

/-- What the library's caller supplies: a value, then a destination of the
target format; the profile's meaning of the written target type and of `int`. -/
structure NarrowCall : Prop where
  value : (operands 2).value st.pub = .ok (.int fS n, pub1)
  place : (operands 3).place pub1 = .ok (l, pub2)
  heap : l.region = .heap
  cell : pub2.heap l = some { type := .integer fT, value := some (.int fT before) }
  target : profile.types T = some (.integer fT)
  int : profile.types (.symbol "int") = some (.integer profile.int)
  one : profile.int.Represents 1

theorem tryNarrow_runs (call : NarrowCall profile T operands st n fS fT pub1 pub2 l before)
    (a b : String) (hab : a ≠ b) :
    invoke profile [S, T, v, o] operands tryNarrow [a, b] st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fT n before).1, release st.next
        { pub := { pub2 with heap := update pub2.heap l (narrowed fT n before) },
          frame := st.frame, next := st.next + 2 }) := by
  obtain ⟨hv, hp, hheap, hcell, htype, hint, hone⟩ := call
  have hslots : slotsOf tryNarrow = [(0, tryNarrow.arguments[0]), (1, tryNarrow.arguments[1]),
      (2, tryNarrow.arguments[2]), (3, tryNarrow.arguments[3])] := rfl
  unfold invoke
  rw [hslots]
  simp only [acquireArguments, tryNarrow, callerValue, callerPlace, hv, hp, State.withPub,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [instantiate, instantiateMany, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hab' : (a == b) = false := by simpa using hab
  have frame : ∀ (F : Memory), (∀ x, x.object < st.next → F x = st.frame x) →
      (fun x => if st.next ≤ x.object then none else F x) =
        fun x => if st.next ≤ x.object then none else st.frame x := by
    intro F hF; funext x
    by_cases hx : st.next ≤ x.object
    · simp [hx]
    · simp [hx, hF x (by omega)]
  by_cases hrep : fT.Represents n
  · have hn : convertInteger intervalReductionPolicy n (.integer fT) = .value n :=
      convertInteger_preserves_representable _ _ _ hrep
    have hn' : convertInteger profile.signedPolicy n (.integer fT) = .value n :=
      convertInteger_preserves_representable _ _ _ hrep
    have hx := MacroCheckedNarrowing.success_stores_input fT n before
      ((MacroCheckedNarrowing.execute_accepted_iff fT n before).mpr hrep)
    have ha := (MacroCheckedNarrowing.execute_accepted_iff fT n before).mpr hrep
    simp only [narrowed]
    rw [hx, ha]
    simp [hab', value, statements, statement, typeOf, typeAtom, htype, hint, bind, Except.bind, pure,
      Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, hn, hn', values, overflowBuiltin, State.read,
      State.write, update, load, store, truth, boolean, place, hheap, hcell, hrep, release, Except.map]
    refine frame _ fun x hx => ?_
    have e0 : x ≠ { region := .frame, object := st.next, index := 0 } := by rintro rfl; simp at hx
    have e1 : x ≠ { region := .frame, object := st.next + 1, index := 0 } := by rintro rfl; simp at hx
    have h1' : ¬ st.next ≤ x.object := by omega
    have h2' : ¬ st.next + 1 + 1 ≤ x.object := by omega
    simp [e0, e1, h1', h2']
  · obtain ⟨m, hm⟩ := interval_value n fT
    have hf : (MacroCheckedNarrowing.execute fT n before).1 = false := by
      cases h : (MacroCheckedNarrowing.execute fT n before).1
      · rfl
      · exact absurd ((MacroCheckedNarrowing.execute_accepted_iff fT n before).mp h) hrep
    simp only [narrowed]
    rw [MacroCheckedNarrowing.failure_preserves_destination fT n before hf, hf,
      update_same _ _ _ hcell]
    simp [hab', value, statements, statement, typeOf, typeAtom, htype, hint, bind, Except.bind, pure,
      Except.pure, lookup, List.lookup, h0, convert, hz, hm, values, overflowBuiltin, State.read,
      State.write, update, load, truth, boolean, place, hrep, release, Except.map]
    refine frame _ fun x hx => ?_
    have e0 : x ≠ { region := .frame, object := st.next, index := 0 } := by rintro rfl; simp at hx
    have e1 : x ≠ { region := .frame, object := st.next + 1, index := 0 } := by rintro rfl; simp at hx
    have h1' : ¬ st.next ≤ x.object := by omega
    simp [e0, e1, h1']

/-- The readable export of any `try-narrow` use implements the narrowing
contract: on success the destination holds the value and the result is 1; on
failure the destination keeps its value and the result is 0. -/
theorem tryNarrow_export (call : NarrowCall profile T operands st n fS fT pub1 pub2 l before)
    (supply : List String) (block : Marked)
    (lowered : lower tryNarrow [S, T, v, o] supply = some block) (distinct : supply.Nodup) :
    runBlock profile [S, T, v, o] operands true block st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fT n before).1, release st.next
        { pub := { pub2 with heap := update pub2.heap l (narrowed fT n before) },
          frame := st.frame, next := st.next + 2 }) := by
  rw [show true = tryNarrow.expression from rfl,
    export_correct profile _ operands tryNarrow supply block st lowered distinct tryNarrow_admitted]
  obtain ⟨hnd, hlen⟩ := chosenLocals_nodup lowered distinct
  obtain ⟨a, b, hab, hne⟩ := pair_of_nodup hnd hlen
  rw [hab]
  exact tryNarrow_runs profile S T v o operands st n fS fT pub1 pub2 l before call a b hne

end TryNarrow

/-! ## `array-bytes`: the product of a count and an element size, checked -/

section ArrayBytes

variable (profile : Profile) (E C Z len o : Atom) (operands : Nat → Operand) (st : State)
  (n : Int) (fL fZ : IntegerFormat) (tE : Ty) (k : Nat) (pub1 pub2 : Public) (l : Loc) (before : Int)

/-- The caller's count and destination, the element type's size and the
destination's format. -/
structure BytesCall : Prop where
  value : (operands 3).value st.pub = .ok (.int fL n, pub1)
  place : (operands 4).place pub1 = .ok (l, pub2)
  heap : l.region = .heap
  cell : pub2.heap l = some { type := .integer fZ, value := some (.int fZ before) }
  size : profile.types Z = some (.integer fZ)
  element : profile.types E = some tE
  bytes : profile.sizeOf tE = some k
  int : profile.types (.symbol "int") = some (.integer profile.int)
  one : profile.int.Represents 1

theorem arrayBytes_runs (call : BytesCall profile E Z operands st n fL fZ tE k pub1 pub2 l before)
    (a b : String) (hab : a ≠ b) :
    invoke profile [E, C, Z, len, o] operands arrayBytes [a, b] st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fZ (n * k) before).1, release st.next
        { pub := { pub2 with heap := update pub2.heap l (narrowed fZ (n * k) before) },
          frame := st.frame, next := st.next + 2 }) := by
  obtain ⟨hv, hp, hheap, hcell, hsize, helem, hbytes, hint, hone⟩ := call
  have hslots : slotsOf arrayBytes = [(0, arrayBytes.arguments[0]), (1, arrayBytes.arguments[1]),
      (2, arrayBytes.arguments[2]), (3, arrayBytes.arguments[3]), (4, arrayBytes.arguments[4])] := rfl
  unfold invoke
  rw [hslots]
  simp only [acquireArguments, arrayBytes, callerValue, callerPlace, hv, hp, State.withPub,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [instantiate, instantiateMany, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hab' : (a == b) = false := by simpa using hab
  have frame : ∀ (F : Memory), (∀ x, x.object < st.next → F x = st.frame x) →
      (fun x => if st.next ≤ x.object then none else F x) =
        fun x => if st.next ≤ x.object then none else st.frame x := by
    intro F hF; funext x
    by_cases hx : st.next ≤ x.object
    · simp [hx]
    · simp [hx, hF x (by omega)]
  by_cases hrep : fZ.Represents (n * k)
  · have hn : convertInteger intervalReductionPolicy (n * k) (.integer fZ) = .value (n * k) :=
      convertInteger_preserves_representable _ _ _ hrep
    have hn' : convertInteger profile.signedPolicy (n * k) (.integer fZ) = .value (n * k) :=
      convertInteger_preserves_representable _ _ _ hrep
    have ha := (MacroCheckedNarrowing.execute_accepted_iff fZ (n * k) before).mpr hrep
    simp only [narrowed]
    rw [MacroCheckedNarrowing.success_stores_input fZ (n * k) before ha, ha]
    simp [hab', value, statements, statement, typeOf, typeAtom, hsize, helem, hbytes, hint, bind, Except.bind,
      pure, Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, hn, hn', values, overflowBuiltin,
      State.read, State.write, update, load, store, truth, boolean, place, hheap, hcell, hrep, release,
      Except.map]
    refine frame _ fun x hx => ?_
    have e0 : x ≠ { region := .frame, object := st.next, index := 0 } := by rintro rfl; simp at hx
    have e1 : x ≠ { region := .frame, object := st.next + 1, index := 0 } := by rintro rfl; simp at hx
    have h1' : ¬ st.next ≤ x.object := by omega
    have h2' : ¬ st.next + 1 + 1 ≤ x.object := by omega
    simp [e0, e1, h1', h2']
  · obtain ⟨m, hm⟩ := interval_value (n * k) fZ
    have hf : (MacroCheckedNarrowing.execute fZ (n * k) before).1 = false := by
      cases h : (MacroCheckedNarrowing.execute fZ (n * k) before).1
      · rfl
      · exact absurd ((MacroCheckedNarrowing.execute_accepted_iff fZ (n * k) before).mp h) hrep
    simp only [narrowed]
    rw [MacroCheckedNarrowing.failure_preserves_destination fZ (n * k) before hf, hf,
      update_same _ _ _ hcell]
    simp [hab', value, statements, statement, typeOf, typeAtom, hsize, helem, hbytes, hint, bind, Except.bind,
      pure, Except.pure, lookup, List.lookup, h0, convert, hz, hm, values, overflowBuiltin, State.read,
      State.write, update, load, truth, boolean, place, hrep, release, Except.map]
    refine frame _ fun x hx => ?_
    have e0 : x ≠ { region := .frame, object := st.next, index := 0 } := by rintro rfl; simp at hx
    have e1 : x ≠ { region := .frame, object := st.next + 1, index := 0 } := by rintro rfl; simp at hx
    have h1' : ¬ st.next ≤ x.object := by omega
    simp [e0, e1, h1']

/-- The readable export of any `array-bytes` use stores the byte count of the
array exactly when the destination's format represents it, and otherwise
keeps the destination. -/
theorem arrayBytes_export (call : BytesCall profile E Z operands st n fL fZ tE k pub1 pub2 l before)
    (supply : List String) (block : Marked)
    (lowered : lower arrayBytes [E, C, Z, len, o] supply = some block) (distinct : supply.Nodup) :
    runBlock profile [E, C, Z, len, o] operands true block st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fZ (n * k) before).1, release st.next
        { pub := { pub2 with heap := update pub2.heap l (narrowed fZ (n * k) before) },
          frame := st.frame, next := st.next + 2 }) := by
  rw [show true = arrayBytes.expression from rfl,
    export_correct profile _ operands arrayBytes supply block st lowered distinct arrayBytes_admitted]
  obtain ⟨hnd, hlen⟩ := chosenLocals_nodup lowered distinct
  obtain ⟨a, b, hab, hne⟩ := pair_of_nodup hnd hlen
  rw [hab]
  exact arrayBytes_runs profile E C Z len o operands st n fL fZ tE k pub1 pub2 l before call a b hne

end ArrayBytes

/-! ## `doubled-capacity`: an empty capacity starts at the initial value, a
nonempty one doubles, and an overflow keeps the destination -/

section DoubledCapacity

variable (profile : Profile) (C init cap o : Atom) (operands : Nat → Operand) (st : State)
  (i c : Int) (fI fK fC : IntegerFormat) (pub1 pub2 pub3 : Public) (l : Loc) (before : Int)

/-- An integer cell holding `v`. -/
def stored (f : IntegerFormat) (v : Int) : Cell := { type := .integer f, value := some (.int f v) }

/-- Whether the capacity is accepted, and what the destination then holds. -/
def doubled (fC : IntegerFormat) (i c before : Int) : Bool × Int :=
  if c = 0 then (true, i) else if fC.Represents (c + c) then (true, c + c) else (false, before)

structure DoublingCall : Prop where
  initial : (operands 1).value st.pub = .ok (.int fI i, pub1)
  capacity : (operands 2).value pub1 = .ok (.int fK c, pub2)
  place : (operands 3).place pub2 = .ok (l, pub3)
  heap : l.region = .heap
  cell : pub3.heap l = some { type := .integer fC, value := some (.int fC before) }
  count : profile.types C = some (.integer fC)
  fits : fC.Represents i
  int : profile.types (.symbol "int") = some (.integer profile.int)
  one : profile.int.Represents 1

theorem doubledCapacity_runs (call : DoublingCall profile C operands st i c fI fK fC pub1 pub2 pub3 l before)
    (a b : String) (hab : a ≠ b) :
    invoke profile [C, init, cap, o] operands doubledCapacity [a, b] st =
      .ok (boolean profile (doubled fC i c before).1, release st.next
        { pub := { pub3 with heap := update pub3.heap l (stored fC (doubled fC i c before).2) },
          frame := st.frame, next := st.next + 2 }) := by
  obtain ⟨hi, hc, hp, hheap, hcell, hcount, hfits, hint, hone⟩ := call
  have hslots : slotsOf doubledCapacity = [(0, doubledCapacity.arguments[0]), (1, doubledCapacity.arguments[1]),
      (2, doubledCapacity.arguments[2]), (3, doubledCapacity.arguments[3])] := rfl
  unfold invoke
  rw [hslots]
  simp only [acquireArguments, doubledCapacity, callerValue, callerPlace, hi, hc, hp, State.withPub,
    List.getElem_cons_zero, List.getElem_cons_succ]
  simp only [instantiate, instantiateMany, List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.getD_some]
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hinit : convertInteger profile.signedPolicy i (.integer fC) = .value i :=
    convertInteger_preserves_representable _ _ _ hfits
  have hab' : (a == b) = false := by simpa using hab
  have frame : ∀ (F : Memory), (∀ x, x.object < st.next → F x = st.frame x) →
      (fun x => if st.next ≤ x.object then none else F x) =
        fun x => if st.next ≤ x.object then none else st.frame x := by
    intro F hF; funext x
    by_cases hx : st.next ≤ x.object
    · simp [hx]
    · simp [hx, hF x (by omega)]
  have finish : ∀ x : Loc, x.object < st.next → x ≠ { region := .frame, object := st.next, index := 0 } ∧
      x ≠ { region := .frame, object := st.next + 1, index := 0 } ∧ ¬ st.next ≤ x.object ∧
        ¬ st.next + 1 + 1 ≤ x.object := fun x hx =>
    ⟨by rintro rfl; simp at hx, by rintro rfl; simp at hx, by omega, by omega⟩
  by_cases hc0 : c = 0
  · subst hc0
    simp only [doubled, stored, if_true]
    simp [hab', value, statements, statement, typeOf, typeAtom, hcount, hint, bind, Except.bind, pure,
      Except.pure, lookup, List.lookup, h1, convert, ho, hinit, State.read,
      State.write, update, load, store, truth, boolean, place, hheap, hcell, release, Except.map]
    refine frame _ fun x hx => ?_
    obtain ⟨e0, e1, h1', h2'⟩ := finish x hx
    simp [e0, e1, h1']
  · by_cases hrep : fC.Represents (c + c)
    · have hd : convertInteger intervalReductionPolicy (c + c) (.integer fC) = .value (c + c) :=
        convertInteger_preserves_representable _ _ _ hrep
      have hd' : convertInteger profile.signedPolicy (c + c) (.integer fC) = .value (c + c) :=
        convertInteger_preserves_representable _ _ _ hrep
      simp only [doubled, stored, hc0, hrep, if_true, if_false]
      simp [hab', hc0, value, statements, statement, typeOf, typeAtom, hcount, hint, bind, Except.bind, pure,
        Except.pure, lookup, List.lookup, h1, convert, ho, hinit, hd, hd', values, overflowBuiltin,
        State.read, State.write, update, load, store, truth, boolean, place, hheap, hcell, hrep, release,
        Except.map]
      refine frame _ fun x hx => ?_
      obtain ⟨e0, e1, h1', h2'⟩ := finish x hx
      simp [e0, e1, h1']
    · obtain ⟨m, hm⟩ := interval_value (c + c) fC
      simp only [doubled, stored, hc0, hrep, if_false]
      rw [update_same _ _ _ hcell]
      simp [hab', hc0, value, statements, statement, typeOf, typeAtom, hcount, hint, bind, Except.bind, pure,
        Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, hinit, hm, values, overflowBuiltin,
        State.read, State.write, update, load, store, truth, boolean, place, hrep, release,
        Except.map]
      refine frame _ fun x hx => ?_
      obtain ⟨e0, e1, h1', h2'⟩ := finish x hx
      simp [e0, e1, h1']

theorem doubledCapacity_export (call : DoublingCall profile C operands st i c fI fK fC pub1 pub2 pub3 l before)
    (supply : List String) (block : Marked)
    (lowered : lower doubledCapacity [C, init, cap, o] supply = some block) (distinct : supply.Nodup) :
    runBlock profile [C, init, cap, o] operands true block st =
      .ok (boolean profile (doubled fC i c before).1, release st.next
        { pub := { pub3 with heap := update pub3.heap l (stored fC (doubled fC i c before).2) },
          frame := st.frame, next := st.next + 2 }) := by
  rw [show true = doubledCapacity.expression from rfl,
    export_correct profile _ operands doubledCapacity supply block st lowered distinct doubledCapacity_admitted]
  obtain ⟨hnd, hlen⟩ := chosenLocals_nodup lowered distinct
  obtain ⟨a, b, hab, hne⟩ := pair_of_nodup hnd hlen
  rw [hab]
  exact doubledCapacity_runs profile C init cap o operands st i c fI fK fC pub1 pub2 pub3 l before call a b hne

end DoubledCapacity

/-! ## `probe`: a disabled probe runs nothing, an enabled one runs its effect once -/

section Probe

variable (profile : Profile) (E X : Atom) (operands : Nat → Operand) (st : State) (pub1 : Public)

theorem probe_runs (f : IntegerFormat) (e : Int) (hswitch : (operands 0).value st.pub = .ok (.int f e, pub1)) :
    invoke profile [E, X] operands probe [] st =
      if e = 0 then .ok (.void, release st.next (st.withPub pub1))
      else (callerValue { profile, written := [E, X], operands, params := fun _ => none } 1
          (st.withPub pub1)).map fun r => (.void, release st.next r.2) := by
  have hslots : slotsOf probe = [(0, probe.arguments[0]), (1, probe.arguments[1])] := rfl
  unfold invoke
  rw [hslots]
  simp only [acquireArguments, probe]
  simp only [instantiate, instantiateMany]
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  by_cases he : e = 0
  · subst he
    simp [value, statements, statement, callerValue, hswitch, State.withPub, truth, bind, Except.bind,
      pure, Except.pure, h0, Except.map, release_release]
  · rcases hx : (operands 1).value pub1 with err | ⟨w, p⟩
    · simp [he, value, statements, statement, callerValue, hswitch, hx, State.withPub, truth, bind, Except.bind,
        Except.map]
    · simp [he, value, statements, statement, callerValue, hswitch, hx, State.withPub, truth, bind, Except.bind,
        pure, Except.pure, Except.map, release_release]

/-- The readable export of a disabled probe runs nothing but its switch; an
enabled one runs its effect exactly once. -/
theorem probe_export (f : IntegerFormat) (e : Int) (hswitch : (operands 0).value st.pub = .ok (.int f e, pub1))
    (supply : List String) (block : Marked)
    (lowered : lower probe [E, X] supply = some block) (distinct : supply.Nodup) :
    runBlock profile [E, X] operands false block st =
      if e = 0 then .ok (.void, release st.next (st.withPub pub1))
      else (callerValue { profile, written := [E, X], operands, params := fun _ => none } 1
          (st.withPub pub1)).map fun r => (.void, release st.next r.2) := by
  rw [show false = probe.expression from rfl,
    export_correct profile _ operands probe supply block st lowered distinct probe_admitted]
  obtain ⟨hnd, hlen⟩ := chosenLocals_nodup lowered distinct
  rw [List.length_eq_zero_iff.mp hlen]
  exact probe_runs profile E X operands st pub1 f e hswitch

end Probe

/-! ## `worklist-push`: guards, growth through one resize call, and the store -/

section Push

variable (profile : Profile) (E C R B N K V : Atom) (operands : Nat → Operand) (st : State)
  (g : String) (lB lL lC : Loc) (bufp w : Val) (len cap : Int) (fC : IntegerFormat) (tE : Ty) (k : Nat)
  (pub1 pub2 pub3 pub4 pub5 : Public)

/-- What a `worklist-push` caller supplies: the resize function, the buffer,
length and capacity objects, and the value; the profile's meaning of the
element and count types. -/
structure PushCall : Prop where
  resize : (operands 2).value st.pub = .ok (.fn g, pub1)
  buffer : (operands 3).place pub1 = .ok (lB, pub2)
  length : (operands 4).place pub2 = .ok (lL, pub3)
  capacity : (operands 5).place pub3 = .ok (lC, pub4)
  value : (operands 6).value pub4 = .ok (w, pub5)
  bufferHeap : lB.region = .heap
  lengthHeap : lL.region = .heap
  capacityHeap : lC.region = .heap
  bufferCell : pub5.heap lB = some { type := .pointer tE, value := some bufp }
  lengthCell : pub5.heap lL = some (stored fC len)
  capacityCell : pub5.heap lC = some (stored fC cap)
  count : profile.types C = some (.integer fC)
  element : profile.types E = some tE
  size : profile.sizeOf tE = some k
  int : profile.types (.symbol "int") = some (.integer profile.int)
  one : profile.int.Represents 1

/-- Zero converts to every integer format under every policy: a push declares
its byte count initialized to zero. -/
@[simp] theorem convert_zero_integer (policy : SignedConversionPolicy) (f : IntegerFormat) :
    convertInteger policy 0 (.integer f) = .value 0 :=
  convertInteger_preserves_representable policy f 0 f.zero_representable

@[simp] theorem convert_zero (profile : Profile) (f : IntegerFormat) :
    convert profile (.integer f) (.int profile.int 0) = .ok (.int f 0) := by
  simp [convert]

@[simp] theorem constant_zero (profile : Profile) : constant profile "0" = some (.int profile.int 0) := rfl

/-- The captured arguments of a `worklist-push` use, in acquisition order. -/
def pushParams (g : String) (lB lL lC : Loc) (w : Val) : Nat → Option Param := fun k =>
  if k = 6 then some (.value w) else if k = 5 then some (.place lC) else if k = 4 then some (.place lL)
  else if k = 3 then some (.place lB) else if k = 2 then some (.value (.fn g))
  else if k = 1 then some .syntax else if k = 0 then some .syntax else none

/-- The template with its locals named. -/
def pushTemplate (n0 n1 n2 n3 : String) : Marked :=
  instantiate (fun i => .arg i) (fun j => [n0, n1, n2, n3].getD j "") push.body

/-- The use acquires its arguments in declared order, then runs the template. -/
theorem push_acquired (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5) (n0 n1 n2 n3 : String) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      Except.map (fun x => (x.1, release st.next x.2))
        (value { profile, written := [E, C, R, B, N, K, V], operands, params := pushParams g lB lL lC w } []
          (pushTemplate n0 n1 n2 n3) (st.withPub pub5)) := by
  obtain ⟨hres, hbuf, hlen, hcap, hval, -⟩ := call
  have hslots : slotsOf push = [(0, push.arguments[0]), (1, push.arguments[1]), (2, push.arguments[2]),
      (3, push.arguments[3]), (4, push.arguments[4]), (5, push.arguments[5]), (6, push.arguments[6])] := rfl
  unfold invoke
  rw [hslots]
  simp only [acquireArguments, push, callerValue, callerPlace, hres, hbuf, hlen, hcap, hval, State.withPub,
    List.getElem_cons_zero, List.getElem_cons_succ]
  rfl

/-- The private frame after a use: whatever the template declared is gone. -/
theorem release_frame (st : State) (F : Memory) (hF : ∀ x : Loc, x.object < st.next → F x = st.frame x) :
    (fun x : Loc => if st.next ≤ x.object then none else F x) =
      fun x => if st.next ≤ x.object then none else st.frame x := by
  funext x
  by_cases hx : st.next ≤ x.object
  · simp [hx]
  · simp [hx, hF x (by omega)]

theorem below_frame {st : State} {x : Loc} (hx : x.object < st.next) (m : Nat) (hm : st.next ≤ m)
    (r : Region) (i : Int) : (x = { region := r, object := m, index := i }) = False := by
  apply propext; constructor
  · rintro rfl; simp at hx; omega
  · intro h; cases h

theorem distinct4 {n0 n1 n2 n3 : String} (h : [n0, n1, n2, n3].Nodup) :
    (n0 == n1) = false ∧ (n0 == n2) = false ∧ (n0 == n3) = false ∧ (n1 == n2) = false ∧
      (n1 == n3) = false ∧ (n2 == n3) = false ∧ (n1 == n0) = false ∧ (n2 == n0) = false ∧
        (n3 == n0) = false ∧ (n2 == n1) = false ∧ (n3 == n1) = false ∧ (n3 == n2) = false := by
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at h
  obtain ⟨⟨h01, h02, h03⟩, ⟨h12, h13⟩, h23⟩ := h
  simp [h01, h02, h03, h12, h13, h23, Ne.symm h01, Ne.symm h02, Ne.symm h03, Ne.symm h12, Ne.symm h13,
    Ne.symm h23]

/-- Length and capacity given as one object: refused, and nothing changes. -/
theorem push_aliased (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (aliased : lL = lC) (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next { pub := pub5, frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  subst aliased
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  simp [pushTemplate, push, instantiate, instantiateMany, pushParams,
    value, statements, statement, typeOf, typeAtom, hcount, helem, hint, bind, Except.bind, pure,
    Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, State.read, State.write, update, load,
    store, truth, boolean, place, MacroExportStateful.compare, release, Except.map, State.withPub]
  refine release_frame st _ fun x hx => ?_
  simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega]

/-- A length beyond the capacity: refused, and nothing changes. -/
theorem push_overfull (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (over : cap < len) (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next { pub := pub5, frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  simp [pushTemplate, push, instantiate, instantiateMany, pushParams,
    value, statements, statement, typeOf, typeAtom, hcount, helem, hint, bind, Except.bind, pure,
    Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, State.read, State.write, update, load,
    store, truth, boolean, place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, hlh, hlc, hch, hcc, separate, over, common]
  refine release_frame st _ fun x hx => ?_
  simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega]

/-- A nonzero capacity with no buffer: refused, and nothing changes. -/
theorem push_unallocated (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (within : len ≤ cap) (nonempty : cap ≠ 0) (empty : bufp = .null)
    (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next { pub := pub5, frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  subst empty
  have hle : ¬ cap < len := by omega
  simp [pushTemplate, push, instantiate, instantiateMany, pushParams,
    value, statements, statement, typeOf, typeAtom, hcount, helem, hint, bind, Except.bind, pure,
    Except.pure, lookup, List.lookup, h0, h1, convert, hz, ho, State.read, State.write, update, load,
    store, truth, boolean, place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, hbh, hbc, hlh, hlc, hch, hcc, separate, hle, nonempty, common]
  refine release_frame st _ fun x hx => ?_
  simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega]

/-- The element of a buffer at an index. -/
def slot (base : Loc) (i : Int) : Loc := { base with index := base.index + i }

/-- A heap after storing `w'` at `base[len]` and growing the length object to `len + 1`. -/
def appended (H : Memory) (base : Loc) (len : Int) (old : Cell) (w' : Val) (lL : Loc) (fC : IntegerFormat) :
    Memory :=
  update (update H (slot base len) { old with value := some w' }) lL (stored fC (len + 1))

theorem unsigned_successor {p : Nat} {len : Int} (h0 : 0 ≤ len) (h : len + 1 < powerOfTwo p) :
    (len + 1) % powerOfTwo p = len + 1 :=
  Int.emod_eq_of_lt (by omega) h

theorem unsigned_one {p : Nat} (hp : 0 < p) : (IntegerFormat.unsigned p hp).Represents 1 := by
  have := powerOfTwo_positive p
  have two : (2 : Int) ≤ powerOfTwo p := by
    unfold powerOfTwo
    calc (2 : Int) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hp
  simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]
  omega

/-- Room in the buffer: the value is stored after the last element and the
length grows by one, with no allocation. -/
theorem push_room (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (room : len < cap) (base : Loc) (hbuf : bufp = .ptr base) (hbase : base.region = .heap)
    (p : Nat) (hp : 0 < p) (hfmt : fC = .unsigned p hp) (hlen0 : 0 ≤ len) (hfit : len + 1 < powerOfTwo p)
    (old : Cell) (hold : pub5.heap (slot base len) = some old) (htype : old.type = tE)
    (w' : Val) (hw : convert profile tE w = .ok w') (slotL : slot base len ≠ lL)
    (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 1, release st.next
        { pub := { pub5 with heap := appended pub5.heap base len old w' lL fC },
          frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  subst hbuf hfmt
  have hle : ¬ cap < len := by omega
  have hne : len ≠ cap := by omega
  have hcap : cap ≠ 0 := by omega
  have hsucc := unsigned_successor hlen0 hfit
  have hone' := unsigned_one hp
  have hrepS : (IntegerFormat.unsigned p hp).Represents (len + 1) := by
    simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]; omega
  have hconvS : convertInteger profile.signedPolicy (len + 1) (.integer (.unsigned p hp)) = .value (len + 1) :=
    convertInteger_preserves_representable _ _ _ hrepS
  have hw' : convert profile old.type w = .ok w' := htype ▸ hw
  have hc1 : convert profile (.integer profile.int) (.int profile.int 1) = .ok (.int profile.int 1) := by
    simp [convert, ho]
  have hcS : convert profile (.integer (.unsigned p hp)) (.int (.unsigned p hp) (len + 1)) =
      .ok (.int (.unsigned p hp) (len + 1)) := by
    simp [convert, hconvS]
  obtain ⟨br, bo, bi⟩ := base
  simp only at hbase
  subst hbase
  simp only [appended, slot] at hold slotL hw' ⊢
  simp [pushTemplate, push, instantiate, instantiateMany, pushParams,
    value, statements, statement, typeOf, typeAtom, hcount, helem, hint, bind, Except.bind, pure,
    Except.pure, lookup, List.lookup, h1, State.read, State.write, update, load,
    store, truth, boolean, place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, hbh, hbc, hlh, hlc, hch, hcc, separate, hle, hne, hcap, hold, hw',
    Ne.symm slotL, common, arith, hsucc, hone', hc1, hcS]
  refine release_frame st _ fun x hx => ?_
  simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
    show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]

/-- The private objects a `worklist-push` use declares are distinct. -/
theorem slots_distinct (n : Nat) :
    (n = n + 1) = False ∧ (n = n + 1 + 1) = False ∧ (n = n + 1 + 1 + 1) = False ∧ (n + 1 = n) = False ∧
      (n + 1 = n + 1 + 1) = False ∧ (n + 1 = n + 1 + 1 + 1) = False ∧ (n + 1 + 1 = n) = False ∧
        (n + 1 + 1 = n + 1) = False ∧ (n + 1 + 1 = n + 1 + 1 + 1) = False ∧ (n + 1 + 1 + 1 = n) = False ∧
          (n + 1 + 1 + 1 = n + 1) = False ∧ (n + 1 + 1 + 1 = n + 1 + 1) = False := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact propext ⟨fun h => by omega, False.elim⟩

/-- A full buffer whose capacity cannot double: refused before any allocation. -/
theorem push_doubling_overflows (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (full : len = cap) (nonempty : cap ≠ 0) (base : Loc) (hbuf : bufp = .ptr base)
    (overflow : ¬ fC.Represents (cap + cap)) (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next { pub := pub5, frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have h8 : constant profile "8" = some (.int profile.int 8) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hc0 : convert profile (.integer profile.int) (.int profile.int 0) = .ok (.int profile.int 0) := by
    simp [convert, hz]
  have hc1 : convert profile (.integer profile.int) (.int profile.int 1) = .ok (.int profile.int 1) := by
    simp [convert, ho]
  subst full hbuf
  obtain ⟨m, hm⟩ := interval_value (len + len) fC
  obtain ⟨o01, o02, o03, o10, o12, o13, o20, o21, o23, o30, o31, o32⟩ := slots_distinct st.next
  simp [o02, o03, o30, pushTemplate, push, instantiate, instantiateMany, pushParams, b01, b02, b03,
    value, statements, statement, typeOf, typeAtom, hcount, helem, hint, bind, Except.bind,
    pure, Except.pure, lookup, List.lookup, h0, h1, hc0, hc1, values, State.read, State.write, update,
    load, store, truth, boolean, place, MacroExportStateful.compare, release, Except.map, State.withPub, stored,
    common, overflowBuiltin, IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, separate, nonempty, overflow, hm]
  refine release_frame st _ fun x hx => ?_
  simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
    show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]

/-- The capacity a full buffer grows to. -/
def grown (cap : Int) : Int := if cap = 0 then 8 else cap + cap

/-- A full buffer whose grown size in bytes overflows: refused before any allocation. -/
theorem push_bytes_overflow (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (full : len = cap) (guard : cap = 0 ∨ ∃ base, bufp = .ptr base)
    (grows : fC.Represents (grown cap)) (overflow : ¬ fC.Represents (grown cap * k))
    (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next { pub := pub5, frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  obtain ⟨o01, o02, o03, o10, o12, o13, o20, o21, o23, o30, o31, o32⟩ := slots_distinct st.next
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have h8 : constant profile "8" = some (.int profile.int 8) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hc0 : convert profile (.integer profile.int) (.int profile.int 0) = .ok (.int profile.int 0) := by
    simp [convert, hz]
  have hc1 : convert profile (.integer profile.int) (.int profile.int 1) = .ok (.int profile.int 1) := by
    simp [convert, ho]
  have hBL : lB ≠ lL := by rintro rfl; rw [hbc] at hlc; simp [stored] at hlc
  have hBC : lB ≠ lC := by rintro rfl; rw [hbc] at hcc; simp [stored] at hcc
  subst full
  have hgr : fC.Represents (grown len) := grows
  have hconv8 : len = 0 → convert profile (.integer fC) (.int profile.int 8) = .ok (.int fC 8) := by
    intro h; subst h
    simp [convert, convertInteger_preserves_representable _ _ _ (by simpa [grown] using hgr)]
  have hdbl : len ≠ 0 → convertInteger intervalReductionPolicy (len + len) (.integer fC) = .value (len + len) :=
    fun h => convertInteger_preserves_representable _ _ _ (by simpa [grown, h] using hgr)
  obtain ⟨m, hm⟩ := interval_value (grown len * k) fC
  by_cases hz0 : len = 0
  · subst hz0
    simp only [grown, if_true] at hm overflow
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, h8, hc0, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hlh, hlc, hch, hcc, separate,
    hconv8 rfl, hm, overflow]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]
  · obtain ⟨base, rfl⟩ := guard.resolve_left hz0
    simp only [grown, hz0, if_false] at hm overflow
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, hc0, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, separate,
    hz0, hdbl hz0, hm, overflow, (by simpa [grown, hz0] using hgr : fC.Represents (len + len))]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]

/-- A resize the world refuses with a null pointer: exactly one call, recorded
with the old buffer and the grown size in bytes, and the use is refused. Under
a realloc-like contract (`r.effect = id` for a refusal) the caller's memory is
unchanged. -/
theorem push_resize_refused (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (full : len = cap) (guard : cap = 0 ∨ ∃ base, bufp = .ptr base)
    (grows : fC.Represents (grown cap)) (fits : fC.Represents (grown cap * k))
    (r : Reply) (rest : List Reply) (hreplies : pub5.replies = r :: rest) (refused : r.value = .null)
    (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 0, release st.next
        { pub := { heap := r.effect pub5.heap, trace := pub5.trace ++ [.call g [bufp, .int fC (grown cap * k)]],
                   replies := rest },
          frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  obtain ⟨o01, o02, o03, o10, o12, o13, o20, o21, o23, o30, o31, o32⟩ := slots_distinct st.next
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have h8 : constant profile "8" = some (.int profile.int 8) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hc0 : convert profile (.integer profile.int) (.int profile.int 0) = .ok (.int profile.int 0) := by
    simp [convert, hz]
  have hc1 : convert profile (.integer profile.int) (.int profile.int 1) = .ok (.int profile.int 1) := by
    simp [convert, ho]
  have hBL : lB ≠ lL := by rintro rfl; rw [hbc] at hlc; simp [stored] at hlc
  have hBC : lB ≠ lC := by rintro rfl; rw [hbc] at hcc; simp [stored] at hcc
  subst full
  have hgr : fC.Represents (grown len) := grows
  have hconv8 : len = 0 → convert profile (.integer fC) (.int profile.int 8) = .ok (.int fC 8) := by
    intro h; subst h
    simp [convert, convertInteger_preserves_representable _ _ _ (by simpa [grown] using hgr)]
  have hdbl : len ≠ 0 → convertInteger intervalReductionPolicy (len + len) (.integer fC) = .value (len + len) :=
    fun h => convertInteger_preserves_representable _ _ _ (by simpa [grown, h] using hgr)
  have hmul : convertInteger intervalReductionPolicy (grown len * k) (.integer fC) = .value (grown len * k) :=
    convertInteger_preserves_representable _ _ _ fits
  have hnull : convert profile (.pointer tE) .null = .ok .null := rfl
  by_cases hz0 : len = 0
  · subst hz0
    simp only [grown, if_true] at hmul fits ⊢
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, b23, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, h8, hc0, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, separate,
    hconv8 rfl, hmul, fits, external, hreplies, refused, hnull]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]
  · obtain ⟨base, rfl⟩ := guard.resolve_left hz0
    simp only [grown, hz0, if_false] at hmul fits ⊢
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, b23, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, hc0, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, separate,
    hz0, hdbl hz0, hmul, fits, external, hreplies, refused, hnull,
      (by simpa [grown, hz0] using hgr : fC.Represents (len + len))]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]

/-- The caller's memory after a granted resize: the buffer object holds the new
buffer, the capacity object the grown capacity, the value sits after the last
element and the length object holds one more. -/
def regrown (H : Memory) (lB lL lC q : Loc) (len : Int) (old : Cell) (w' : Val) (tE : Ty) (fC : IntegerFormat)
    (nc : Int) : Memory :=
  update (update (update (update H lB { type := .pointer tE, value := some (.ptr q) }) lC (stored fC nc))
    (slot q len) { old with value := some w' }) lL (stored fC (len + 1))

/-- A resize the world grants: exactly one call, then the new buffer and
capacity are installed and the value is appended. The contract on the reply is
realloc-like: it leaves the caller's buffer, length and capacity objects alone
and provides the element after the last. -/
theorem push_resized (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k
      pub1 pub2 pub3 pub4 pub5)
    (separate : lL ≠ lC) (full : len = cap) (guard : cap = 0 ∨ ∃ base, bufp = .ptr base)
    (grows : fC.Represents (grown cap)) (fits : fC.Represents (grown cap * k))
    (r : Reply) (rest : List Reply) (hreplies : pub5.replies = r :: rest) (q : Loc) (granted : r.value = .ptr q)
    (hq : q.region = .heap) (keepB : r.effect pub5.heap lB = pub5.heap lB)
    (keepL : r.effect pub5.heap lL = pub5.heap lL) (keepC : r.effect pub5.heap lC = pub5.heap lC)
    (old : Cell) (hold : r.effect pub5.heap (slot q len) = some old) (htype : old.type = tE)
    (w' : Val) (hw : convert profile tE w = .ok w')
    (slotB : slot q len ≠ lB) (slotL : slot q len ≠ lL) (slotC : slot q len ≠ lC)
    (p : Nat) (hp : 0 < p) (hfmt : fC = .unsigned p hp) (hlen0 : 0 ≤ len) (hfit : len + 1 < powerOfTwo p)
    (n0 n1 n2 n3 : String) (hnd : [n0, n1, n2, n3].Nodup) :
    invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st =
      .ok (.int profile.int 1, release st.next
        { pub := { heap := regrown (r.effect pub5.heap) lB lL lC q len old w' tE fC (grown cap),
                   trace := pub5.trace ++ [.call g [bufp, .int fC (grown cap * k)]], replies := rest },
          frame := st.frame, next := st.next + 4 }) := by
  rw [push_acquired profile E C R B N K V operands st g lB lL lC bufp w len cap fC tE k pub1 pub2 pub3 pub4 pub5
    call]
  obtain ⟨-, -, -, -, -, hbh, hlh, hch, hbc, hlc, hcc, hcount, helem, hsize, hint, hone⟩ := call
  obtain ⟨b01, b02, b03, b12, b13, b23, b10, b20, b30, b21, b31, b32⟩ := distinct4 hnd
  obtain ⟨o01, o02, o03, o10, o12, o13, o20, o21, o23, o30, o31, o32⟩ := slots_distinct st.next
  have h0 : constant profile "0" = some (.int profile.int 0) := rfl
  have h1 : constant profile "1" = some (.int profile.int 1) := rfl
  have h8 : constant profile "8" = some (.int profile.int 8) := rfl
  have hz : convertInteger profile.signedPolicy 0 (.integer profile.int) = .value 0 :=
    convertInteger_preserves_representable _ _ _ profile.int.zero_representable
  have ho : convertInteger profile.signedPolicy 1 (.integer profile.int) = .value 1 :=
    convertInteger_preserves_representable _ _ _ hone
  have hc0 : convert profile (.integer profile.int) (.int profile.int 0) = .ok (.int profile.int 0) := by
    simp [convert, hz]
  have hc1 : convert profile (.integer profile.int) (.int profile.int 1) = .ok (.int profile.int 1) := by
    simp [convert, ho]
  have hBL : lB ≠ lL := by rintro rfl; rw [hbc] at hlc; simp [stored] at hlc
  have hBC : lB ≠ lC := by rintro rfl; rw [hbc] at hcc; simp [stored] at hcc
  subst full
  have hgr : fC.Represents (grown len) := grows
  have hconv8 : len = 0 → convert profile (.integer fC) (.int profile.int 8) = .ok (.int fC 8) := by
    intro h; subst h
    simp [convert, convertInteger_preserves_representable _ _ _ (by simpa [grown] using hgr)]
  have hdbl : len ≠ 0 → convertInteger intervalReductionPolicy (len + len) (.integer fC) = .value (len + len) :=
    fun h => convertInteger_preserves_representable _ _ _ (by simpa [grown, h] using hgr)
  have hmul : convertInteger intervalReductionPolicy (grown len * k) (.integer fC) = .value (grown len * k) :=
    convertInteger_preserves_representable _ _ _ fits
  have hptr : convert profile (.pointer tE) (.ptr q) = .ok (.ptr q) := rfl
  have hw' : convert profile old.type w = .ok w' := htype ▸ hw
  have hgc : convert profile (.integer fC) (.int fC (grown len)) = .ok (.int fC (grown len)) := by
    simp [convert, convertInteger_preserves_representable _ _ _ hgr]
  subst hfmt
  have hsucc := unsigned_successor hlen0 hfit
  have hone' := unsigned_one hp
  have hrepS : (IntegerFormat.unsigned p hp).Represents (len + 1) := by
    simp only [IntegerFormat.Represents, IntegerFormat.lower, IntegerFormat.upper]; omega
  have hcS : convert profile (.integer (.unsigned p hp)) (.int (.unsigned p hp) (len + 1)) =
      .ok (.int (.unsigned p hp) (len + 1)) := by
    simp [convert, convertInteger_preserves_representable _ _ _ hrepS]
  obtain ⟨qr, qo, qi⟩ := q
  simp only at hq
  subst hq
  simp only [regrown, slot] at hold slotB slotL slotC ⊢
  by_cases hz0 : len = 0
  · subst hz0
    simp only [grown, if_true, Int.add_zero, Int.zero_add] at hmul fits hgc hold slotB slotL slotC hsucc hcS ⊢
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, b23, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, h8, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, hBC, Ne.symm hBL,
    Ne.symm hBC, hconv8 rfl, hmul, fits, external, hreplies, granted, hptr, hw', hgc, keepB, keepL,
      keepC, hold, slotB, slotC, Ne.symm slotL, separate,
      arith, hsucc, hone', hcS]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]
  · obtain ⟨base, rfl⟩ := guard.resolve_left hz0
    simp only [grown, hz0, if_false] at hmul fits hgc ⊢
    simp [o02, o03, o20, o30, pushTemplate, push, instantiate,
    instantiateMany, pushParams, b01, b02, b03, b12, b13, b23, value, statements,
    statement, typeOf, typeAtom, hcount, helem, hsize, hint, bind, Except.bind, pure, Except.pure, lookup,
    List.lookup, h0, h1, hc1, values, State.read, State.write, update, load, store, truth, boolean,
    place, MacroExportStateful.compare, release, Except.map, State.withPub, stored, common, overflowBuiltin,
    IntegerFormat.zero_representable, hbh, hbc, hlh, hlc, hch, hcc, hBC, Ne.symm hBL,
    Ne.symm hBC, hz0, hdbl hz0, hmul, fits, external, hreplies, granted, hptr, hw', hgc, keepB, keepL,
      keepC, hold, slotB, slotC, Ne.symm slotL, separate,
      arith, hsucc, hone', hcS, (by simpa [grown, hz0] using hgr : (IntegerFormat.unsigned p hp).Represents (len + len))]
    refine release_frame st _ fun x hx => ?_
    simp (disch := omega) [below_frame hx, show ¬ st.next ≤ x.object by omega,
      show ¬ st.next + 1 + 1 + 1 + 1 ≤ x.object by omega]

/-- The readable export of any `worklist-push` use runs as the source use with
the four distinct names the exporter picked, so each law above holds for it. -/
theorem push_export (supply : List String) (block : Marked)
    (lowered : lower push [E, C, R, B, N, K, V] supply = some block) (distinct : supply.Nodup) :
    ∃ n0 n1 n2 n3, [n0, n1, n2, n3].Nodup ∧ ∀ (operands : Nat → Operand) (st : State),
      runBlock profile [E, C, R, B, N, K, V] operands true block st =
        invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st := by
  obtain ⟨hnd, hlen⟩ := chosenLocals_nodup lowered distinct
  generalize hc : chosenLocals push [E, C, R, B, N, K, V] supply = names at hnd hlen
  match names, hnd, hlen with
  | [n0, n1, n2, n3], hnd, _ =>
      refine ⟨n0, n1, n2, n3, hnd, fun operands st => ?_⟩
      rw [show true = push.expression from rfl,
        export_correct profile _ operands push supply block st lowered distinct push_admitted, hc]

end Push

/-! ## The exported header functions -/

section Headers

theorem lookup_some_mem {n : String} {b : Binding} : ∀ {l : Env}, l.lookup n = some b → n ∈ l.map Prod.fst
  | [], h => by simp at h
  | (k, c) :: rest, h => by
      by_cases hk : n = k
      · subst hk; simp
      · have : (n == k) = false := by simpa using hk
        simp only [List.lookup, this] at h
        exact List.mem_cons_of_mem _ (lookup_some_mem h)

/-- `ct_narrow_*`: called with a value and a pointer to the destination, the
exported function narrows as `try-narrow` does. -/
theorem tryNarrow_function (profile : Profile) (S T v o : Atom) (operands : Nat → Operand) (st : State)
    (n : Int) (fS fT : IntegerFormat) (l : Loc) (before : Int)
    (call : NarrowCall profile T operands st n fS fT st.pub st.pub l before)
    (p0 p1 a b : String) (parts : FunctionParts)
    (lowered : lowerFunctionParts tryNarrow [p0, p1, a, b] = some parts) (distinct : [p0, p1, a, b].Nodup) :
    runFunction profile [S, T, v, o] operands true parts.items [(p0, .value (.int fS n)), (p1, .value (.ptr l))] st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fT n before).1, release st.next
        { pub := { st.pub with heap := update st.pub.heap l (narrowed fT n before) },
          frame := st.frame, next := st.next + 2 }) := by
  have hslots : slotsOf tryNarrow = [(0, tryNarrow.arguments[0]), (1, tryNarrow.arguments[1]),
      (2, tryNarrow.arguments[2]), (3, tryNarrow.arguments[3])] := rfl
  have hev : evaluated tryNarrow = [(2, tryNarrow.arguments[2]), (3, tryNarrow.arguments[3])] := rfl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at distinct
  obtain ⟨⟨h01, h0a, h0b⟩, ⟨h1a, h1b⟩, hab⟩ := distinct
  have hacq : acquireArguments profile [S, T, v, o] operands (slotsOf tryNarrow) (fun _ => none) st =
      .ok ((fun k => if k = 3 then some (.place l) else if k = 2 then some (.value (.int fS n))
        else if k = 1 then some .syntax else if k = 0 then some .syntax else none), st) := by
    rw [hslots]
    simp only [acquireArguments, tryNarrow, callerValue, callerPlace, call.value, call.place, State.withPub,
      List.getElem_cons_zero, List.getElem_cons_succ]
  have bound : Bound tryNarrow ([p0, p1, a, b].take (evaluated tryNarrow).length)
      (fun k => if k = 3 then some (.place l) else if k = 2 then some (.value (.int fS n))
        else if k = 1 then some .syntax else if k = 0 then some .syntax else none)
      [(p0, .value (.int fS n)), (p1, .value (.ptr l))] := by
    refine ⟨fun k c m h => ?_, fun k c h hc => ?_, fun m c h => ?_⟩
    · rw [hev] at h
      simp only [List.length_cons, List.length_nil, List.take, List.zip_cons_cons, List.zip_nil_right,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      have b10 : (p1 == p0) = false := by simpa using Ne.symm h01
      rcases h with ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩
      · subst hk hc hm
        simp [tryNarrow, List.lookup]
      · subst hk hc hm
        simp [tryNarrow, List.lookup, b10]
    · rw [hslots] at h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [tryNarrow]
    · simp only [List.lookup] at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · cases h
  rw [show true = tryNarrow.expression from rfl,
    function_as_use profile _ operands tryNarrow [p0, p1, a, b] parts st _ _ lowered
    (by simp [h01, h0a, h0b, h1a, h1b, hab]) tryNarrow_admitted bound hacq]
  exact tryNarrow_runs profile S T v o operands st n fS fT st.pub st.pub l before call a b hab

/-- `ct_pair_bytes_*`: called with a count and a pointer to the destination,
the exported function stores the byte count as `array-bytes` does. -/
theorem arrayBytes_function (profile : Profile) (E C Z len o : Atom) (operands : Nat → Operand) (st : State)
    (n : Int) (fL fZ : IntegerFormat) (tE : Ty) (k : Nat) (l : Loc) (before : Int)
    (call : BytesCall profile E Z operands st n fL fZ tE k st.pub st.pub l before)
    (p0 p1 a b : String) (parts : FunctionParts)
    (lowered : lowerFunctionParts arrayBytes [p0, p1, a, b] = some parts) (distinct : [p0, p1, a, b].Nodup) :
    runFunction profile [E, C, Z, len, o] operands true parts.items
        [(p0, .value (.int fL n)), (p1, .value (.ptr l))] st =
      .ok (boolean profile (MacroCheckedNarrowing.execute fZ (n * k) before).1, release st.next
        { pub := { st.pub with heap := update st.pub.heap l (narrowed fZ (n * k) before) },
          frame := st.frame, next := st.next + 2 }) := by
  have hslots : slotsOf arrayBytes = [(0, arrayBytes.arguments[0]), (1, arrayBytes.arguments[1]),
      (2, arrayBytes.arguments[2]), (3, arrayBytes.arguments[3]), (4, arrayBytes.arguments[4])] := rfl
  have hev : evaluated arrayBytes = [(3, arrayBytes.arguments[3]), (4, arrayBytes.arguments[4])] := rfl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at distinct
  obtain ⟨⟨h01, h0a, h0b⟩, ⟨h1a, h1b⟩, hab⟩ := distinct
  have hacq : acquireArguments profile [E, C, Z, len, o] operands (slotsOf arrayBytes) (fun _ => none) st =
      .ok ((fun k => if k = 4 then some (.place l) else if k = 3 then some (.value (.int fL n))
        else if k = 2 then some .syntax else if k = 1 then some .syntax else if k = 0 then some .syntax
        else none), st) := by
    rw [hslots]
    simp only [acquireArguments, arrayBytes, callerValue, callerPlace, call.value, call.place, State.withPub,
      List.getElem_cons_zero, List.getElem_cons_succ]
  have bound : Bound arrayBytes ([p0, p1, a, b].take (evaluated arrayBytes).length)
      (fun k => if k = 4 then some (.place l) else if k = 3 then some (.value (.int fL n))
        else if k = 2 then some .syntax else if k = 1 then some .syntax else if k = 0 then some .syntax
        else none)
      [(p0, .value (.int fL n)), (p1, .value (.ptr l))] := by
    refine ⟨fun j c m h => ?_, fun j c h hc => ?_, fun m c h => ?_⟩
    · rw [hev] at h
      simp only [List.length_cons, List.length_nil, List.take, List.zip_cons_cons, List.zip_nil_right,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      have b10 : (p1 == p0) = false := by simpa using Ne.symm h01
      rcases h with ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩
      · subst hk hc hm; simp [arrayBytes, List.lookup]
      · subst hk hc hm; simp [arrayBytes, List.lookup, b10]
    · rw [hslots] at h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [arrayBytes]
    · simp only [List.lookup] at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · cases h
  rw [show true = arrayBytes.expression from rfl,
    function_as_use profile _ operands arrayBytes [p0, p1, a, b] parts st _ _ lowered
      (by simp [h01, h0a, h0b, h1a, h1b, hab]) arrayBytes_admitted bound hacq]
  exact arrayBytes_runs profile E C Z len o operands st n fL fZ tE k st.pub st.pub l before call a b hab

/-- `ct_doubled_capacity_*`: called with an initial value, a capacity and a
pointer to the destination, the exported function chooses as
`doubled-capacity` does. -/
theorem doubledCapacity_function (profile : Profile) (C init cap o : Atom) (operands : Nat → Operand)
    (st : State) (i c : Int) (fI fK fC : IntegerFormat) (l : Loc) (before : Int)
    (call : DoublingCall profile C operands st i c fI fK fC st.pub st.pub st.pub l before)
    (p0 p1 p2 a b : String) (parts : FunctionParts)
    (lowered : lowerFunctionParts doubledCapacity [p0, p1, p2, a, b] = some parts)
    (distinct : [p0, p1, p2, a, b].Nodup) :
    runFunction profile [C, init, cap, o] operands true parts.items
        [(p0, .value (.int fI i)), (p1, .value (.int fK c)), (p2, .value (.ptr l))] st =
      .ok (boolean profile (doubled fC i c before).1, release st.next
        { pub := { st.pub with heap := update st.pub.heap l (stored fC (doubled fC i c before).2) },
          frame := st.frame, next := st.next + 2 }) := by
  have hslots : slotsOf doubledCapacity = [(0, doubledCapacity.arguments[0]), (1, doubledCapacity.arguments[1]),
      (2, doubledCapacity.arguments[2]), (3, doubledCapacity.arguments[3])] := rfl
  have hev : evaluated doubledCapacity = [(1, doubledCapacity.arguments[1]), (2, doubledCapacity.arguments[2]),
      (3, doubledCapacity.arguments[3])] := rfl
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at distinct
  obtain ⟨⟨h01, h02, h0a, h0b⟩, ⟨h12, h1a, h1b⟩, ⟨h2a, h2b⟩, hab⟩ := distinct
  have hacq : acquireArguments profile [C, init, cap, o] operands (slotsOf doubledCapacity) (fun _ => none) st =
      .ok ((fun k => if k = 3 then some (.place l) else if k = 2 then some (.value (.int fK c))
        else if k = 1 then some (.value (.int fI i)) else if k = 0 then some .syntax else none), st) := by
    rw [hslots]
    simp only [acquireArguments, doubledCapacity, callerValue, callerPlace, call.initial, call.capacity,
      call.place, State.withPub, List.getElem_cons_zero, List.getElem_cons_succ]
  have bound : Bound doubledCapacity ([p0, p1, p2, a, b].take (evaluated doubledCapacity).length)
      (fun k => if k = 3 then some (.place l) else if k = 2 then some (.value (.int fK c))
        else if k = 1 then some (.value (.int fI i)) else if k = 0 then some .syntax else none)
      [(p0, .value (.int fI i)), (p1, .value (.int fK c)), (p2, .value (.ptr l))] := by
    refine ⟨fun j d m h => ?_, fun j d h hc => ?_, fun m d h => ?_⟩
    · rw [hev] at h
      simp only [List.length_cons, List.length_nil, List.take, List.zip_cons_cons, List.zip_nil_right,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      have b10 : (p1 == p0) = false := by simpa using Ne.symm h01
      have b20 : (p2 == p0) = false := by simpa using Ne.symm h02
      have b21 : (p2 == p1) = false := by simpa using Ne.symm h12
      rcases h with ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩
      · subst hk hc hm; simp [doubledCapacity, List.lookup]
      · subst hk hc hm; simp [doubledCapacity, List.lookup, b10]
      · subst hk hc hm; simp [doubledCapacity, List.lookup, b20, b21]
    · rw [hslots] at h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all [doubledCapacity]
    · simp only [List.lookup] at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · split at h
          · simp_all
          · cases h
  rw [show true = doubledCapacity.expression from rfl,
    function_as_use profile _ operands doubledCapacity [p0, p1, p2, a, b] parts st _ _ lowered
      (by simp [h01, h02, h0a, h0b, h12, h1a, h1b, h2a, h2b, hab]) doubledCapacity_admitted bound hacq]
  exact doubledCapacity_runs profile C init cap o operands st i c fI fK fC st.pub st.pub st.pub l before call a b hab

/-- `ct_worklist_push_*`: called with the resize function, pointers to the
buffer, length and capacity objects, and the value, the exported function runs
as the `worklist-push` use whose arguments are those values, so every push law
above holds for it. -/
theorem push_function (profile : Profile) (E C R B N K V : Atom) (operands : Nat → Operand) (st : State)
    (g : String) (lB lL lC : Loc) (bufp w : Val) (len cap : Int) (fC : IntegerFormat) (tE : Ty) (k : Nat)
    (call : PushCall profile E C operands st g lB lL lC bufp w len cap fC tE k st.pub st.pub st.pub st.pub st.pub)
    (p0 p1 p2 p3 p4 n0 n1 n2 n3 : String) (parts : FunctionParts)
    (lowered : lowerFunctionParts push [p0, p1, p2, p3, p4, n0, n1, n2, n3] = some parts)
    (distinct : [p0, p1, p2, p3, p4, n0, n1, n2, n3].Nodup) :
    runFunction profile [E, C, R, B, N, K, V] operands true parts.items
        [(p0, .value (.fn g)), (p1, .value (.ptr lB)), (p2, .value (.ptr lL)), (p3, .value (.ptr lC)),
          (p4, .value w)] st =
      invoke profile [E, C, R, B, N, K, V] operands push [n0, n1, n2, n3] st := by
  have hslots : slotsOf push = [(0, push.arguments[0]), (1, push.arguments[1]), (2, push.arguments[2]),
      (3, push.arguments[3]), (4, push.arguments[4]), (5, push.arguments[5]), (6, push.arguments[6])] := rfl
  have hev : evaluated push = [(2, push.arguments[2]), (3, push.arguments[3]), (4, push.arguments[4]),
      (5, push.arguments[5]), (6, push.arguments[6])] := rfl
  have hnd := distinct
  simp only [List.nodup_cons, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, List.nodup_nil,
    and_true] at distinct
  obtain ⟨⟨h01, h02, h03, h04, -⟩, ⟨h12, h13, h14, -⟩, ⟨h23, h24, -⟩, ⟨h34, -⟩, -⟩ := distinct
  have hacq : acquireArguments profile [E, C, R, B, N, K, V] operands (slotsOf push) (fun _ => none) st =
      .ok (pushParams g lB lL lC w, st) := by
    rw [hslots]
    simp only [acquireArguments, push, callerValue, callerPlace, call.resize, call.buffer, call.length,
      call.capacity, call.value, State.withPub, List.getElem_cons_zero, List.getElem_cons_succ]
    rfl
  have bound : Bound push ([p0, p1, p2, p3, p4, n0, n1, n2, n3].take (evaluated push).length)
      (pushParams g lB lL lC w)
      [(p0, .value (.fn g)), (p1, .value (.ptr lB)), (p2, .value (.ptr lL)), (p3, .value (.ptr lC)),
        (p4, .value w)] := by
    have b : ∀ x y : String, x ≠ y → (x == y) = false := fun x y h => by simpa using h
    refine ⟨fun j d m h => ?_, fun j d h hc => ?_, fun m d h => ?_⟩
    · rw [hev] at h
      simp only [List.length_cons, List.length_nil, List.take, List.zip_cons_cons, List.zip_nil_right,
        List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩ | ⟨⟨hk, hc⟩, hm⟩
      · subst hk hc hm; simp [push, pushParams, List.lookup]
      · subst hk hc hm; simp [push, pushParams, List.lookup, b _ _ (Ne.symm h01)]
      · subst hk hc hm; simp [push, pushParams, List.lookup, b _ _ (Ne.symm h02), b _ _ (Ne.symm h12)]
      · subst hk hc hm
        simp [push, pushParams, List.lookup, b _ _ (Ne.symm h03), b _ _ (Ne.symm h13), b _ _ (Ne.symm h23)]
      · subst hk hc hm
        simp [push, pushParams, List.lookup, b _ _ (Ne.symm h04), b _ _ (Ne.symm h14), b _ _ (Ne.symm h24),
          b _ _ (Ne.symm h34)]
    · rw [hslots] at h
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp_all [push, pushParams]
    · have := lookup_some_mem h
      rw [hev]
      simpa using this
  rw [show true = push.expression from rfl,
    function_as_use profile _ operands push [p0, p1, p2, p3, p4, n0, n1, n2, n3] parts st _ _ lowered hnd
      push_admitted bound hacq, hev]
  rfl

end Headers

/-! ## The exported probe macro -/

/-- At a use `ct_probe(E, X)`, the exported macro's expression runs the switch,
then the effect exactly when the switch is nonzero; the probe's static check is
a `sizeof` the compiler evaluates, which the profile must give a size. Its
outcome is the probe use's, without the use's private-frame release, which
changes nothing here. -/
theorem probe_macro (profile : Profile) (E X : Atom) (operands : Nat → Operand) (st : State) (pub1 : Public)
    (fname : String) (f : IntegerFormat) (e : Int)
    (hswitch : (operands 0).value st.pub = .ok (.int f e, pub1)) (ty : Ty) (k : Nat)
    (hstruct : profile.types (.list [.symbol "struct", .list [.symbol "_Static_assert",
        .list [.symbol "call", .symbol "__builtin_constant_p", E],
        .text "\"probe switch must be a constant expression\""], .list [.symbol "char", .symbol fname]]) = some ty)
    (hsize : profile.sizeOf ty = some k) :
    ∃ m, lowerMacro probe fname = some m ∧
      value (ctxOf profile [E, X] operands fun _ => none) [] m st =
        (if e = 0 then .ok (.void, st.withPub pub1)
         else (callerValue { profile, written := [E, X], operands, params := fun _ => none } 1
            (st.withPub pub1)).map fun r => (.void, r.2)) ∧
      invoke profile [E, X] operands probe [] st =
        (value (ctxOf profile [E, X] operands fun _ => none) [] m st).map fun r => (r.1, release st.next r.2) := by
  refine ⟨_, rfl, ?_, ?_⟩
  · have h0 : constant profile "0" = some (.int profile.int 0) := rfl
    by_cases he : e = 0
    · subst he
      simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
        typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, truth, State.withPub, bind, Except.bind, h0,
        pure, Except.pure]
    · rcases hx : (operands 1).value pub1 with err | ⟨w, p⟩
      · simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
          typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, hx, he, truth, State.withPub, bind, Except.bind,
          pure, Except.pure, Except.map]
      · simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
          typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, hx, he, truth, State.withPub, bind, Except.bind,
          pure, Except.pure, Except.map]
  · rw [probe_runs profile E X operands st pub1 f e hswitch]
    have h0 : constant profile "0" = some (.int profile.int 0) := rfl
    by_cases he : e = 0
    · subst he
      simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
        typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, truth, State.withPub, bind, Except.bind, h0,
        pure, Except.pure, Except.map]
    · rcases hx : (operands 1).value pub1 with err | ⟨w, p⟩
      · simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
          typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, hx, he, truth, State.withPub, bind, Except.bind,
          pure, Except.pure, Except.map]
      · simp [instantiate, instantiateMany, isStaticCheck, staticCheckPart, value,
          typeOf, typeAtom, typeAtomMany, hstruct, hsize, callerValue, hswitch, hx, he, truth, State.withPub, bind, Except.bind,
          pure, Except.pure, Except.map]

/-! ## The declared forms

Each shipped rule is in the forms `MacroExportComplete` covers: by
`export_complete` every use of it has a readable export that the check admits
and that behaves as the use, and by `checkHeader_function_complete` and
`checkHeader_macro_complete` every header definition of it is admitted. -/

theorem tryNarrow_forms : lowerable tryNarrow = true ∧ functionForm tryNarrow = true := by decide
theorem arrayBytes_forms : lowerable arrayBytes = true ∧ functionForm arrayBytes = true := by decide
theorem doubledCapacity_forms : lowerable doubledCapacity = true ∧ functionForm doubledCapacity = true := by decide
theorem push_forms : lowerable push = true ∧ functionForm push = true := by decide
theorem probe_forms : lowerable probe = true ∧ macroForm probe = true := by decide

end Mettapedia.GSLT.LanguageDef.MacroExportLibraries
