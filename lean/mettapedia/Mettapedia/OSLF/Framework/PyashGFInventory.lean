import Mettapedia.Languages.GF.HandCrafted.Abstract

/-!
# Pyash GF Inventory Interface

This module provides a broad GF-side inventory for upstream Pyash `be` words
observed in the current source corpus (examples/module/configure/world/mind).

It is intentionally data-level: every inventory item is representable as an
abstract-node constructor. Operational dispatch semantics remain in `PyashGF`
and `PyashCore*`.
-/

namespace Mettapedia.OSLF.Framework.PyashGFInventory

open Mettapedia.Languages.GF.HandCrafted.Core
open Mettapedia.Languages.GF.HandCrafted.Abstract

/-- GF category for normalized Pyash `be` words. -/
def pyashBeWordCat : Category := .base "PyashBeWord"

/-- GF category for normalized English heads in the Pyash parallel corpus. -/
def pyashEnglishHeadCat : Category := .base "PyashEnglishHead"

/-- GF category for typed Pyash-English parallel lexical pairs. -/
def pyashParallelPairCat : Category := .base "PyashParallelPair"

/-- Upstream-observed normalized `be`-word inventory
    (examples/module/configure/world/mind plus translation-pair runtime heads). -/
def pyashBeWordInventory : List String :=
  [ "abs"
  , "auto"
  , "begin"
  , "blend"
  , "body"
  , "build"
  , "bucket"
  , "bump"
  , "c"
  , "calendar"
  , "can"
  , "cast"
  , "ceremony"
  , "checked"
  , "chip"
  , "climb"
  , "command"
  , "compile"
  , "concatenate"
  , "copy"
  , "cut"
  , "date"
  , "def"
  , "default"
  , "depart"
  , "delete"
  , "directory"
  , "discharge"
  , "divide"
  , "do"
  , "door"
  , "download"
  , "draft"
  , "draw"
  , "ecology"
  , "equally"
  , "english"
  , "established"
  , "evoke"
  , "exists"
  , "export"
  , "false"
  , "filename"
  , "first"
  , "footnote"
  , "frequency"
  , "giant"
  , "get_current_time"
  , "glance"
  , "go"
  , "greet"
  , "guarantee"
  , "hear"
  , "hello"
  , "html"
  , "import"
  , "improve"
  , "input"
  , "inner"
  , "index"
  , "inspector"
  , "instead"
  , "invert"
  , "interpret"
  , "itinerary"
  , "javascript"
  , "judge"
  , "license"
  , "lie"
  , "line"
  , "list"
  , "loop"
  , "map"
  , "markdown"
  , "mcp"
  , "mind"
  , "minds"
  , "mix"
  , "mode"
  , "multiples"
  , "multiply"
  , "number"
  , "not"
  , "note"
  , "one"
  , "outer"
  , "output"
  , "pdf"
  , "pass"
  , "passes"
  , "picked"
  , "ping"
  , "plain"
  , "plus"
  , "primes"
  , "promptify"
  , "pyash"
  , "read"
  , "reform"
  , "refinery"
  , "rel"
  , "remains"
  , "remember"
  , "resemble"
  , "ret"
  , "rhs"
  , "root"
  , "round"
  , "say"
  , "search"
  , "second"
  , "see"
  , "series"
  , "service"
  , "session"
  , "sleep"
  , "step"
  , "stop"
  , "stream"
  , "subtract"
  , "target"
  , "tail"
  , "text"
  , "then"
  , "third"
  , "timebox"
  , "tiny"
  , "touch"
  , "translation"
  , "truth"
  , "turing"
  , "two"
  , "understand"
  , "unknown"
  , "vector"
  , "video"
  , "what"
  , "worker"
  , "write"
  , "ya"
  ]

/-- Normalized English heads observed in upstream Pyash↔English translation pairs. -/
def pyashEnglishHeadInventory : List String :=
  [ "abs"
  , "absolute"
  , "add"
  , "and"
  , "be"
  , "become"
  , "beneath"
  , "boolean"
  , "climb"
  , "collect"
  , "command"
  , "compile"
  , "copy"
  , "date"
  , "delete"
  , "directory"
  , "discharge"
  , "divide"
  , "do"
  , "download"
  , "ecology"
  , "espeak"
  , "first"
  , "fizzbuzz"
  , "flip"
  , "glance"
  , "go"
  , "group"
  , "hear"
  , "import"
  , "index"
  , "insertion"
  , "inspector"
  , "interpret"
  , "invert"
  , "least"
  , "license"
  , "list"
  , "logical"
  , "loop"
  , "mark"
  , "math"
  , "microphone"
  , "mind"
  , "mix"
  , "mood"
  , "most"
  , "multiply"
  , "noop"
  , "not"
  , "or"
  , "person"
  , "ping"
  , "piper"
  , "plain"
  , "plus"
  , "process"
  , "read"
  , "rel"
  , "relative"
  , "remainder"
  , "remains"
  , "remember"
  , "say"
  , "search"
  , "second"
  , "state"
  , "su"
  , "subtract"
  , "talk"
  , "text"
  , "toggle"
  , "tool"
  , "touch"
  , "trace"
  , "translate"
  , "understand"
  , "ve"
  , "vector"
  , "word"
  , "worker"
  , "write"
  , "ya"
  ]

/-- Constructor signature for a normalized Pyash `be` word. -/
def pyashBeWordCtor (word : String) : FunctionSig :=
  ⟨"PyBe_" ++ word, pyashBeWordCat⟩

/-- Constructor signature for a normalized English parallel head. -/
def pyashEnglishHeadCtor (word : String) : FunctionSig :=
  ⟨"PyEn_" ++ word, pyashEnglishHeadCat⟩

/-- Constructor signature for a typed Pyash-English lexical pair. -/
def pyashParallelPairCtor : FunctionSig :=
  ⟨"PyParallelPair", .arrow pyashBeWordCat (.arrow pyashEnglishHeadCat pyashParallelPairCat)⟩

/-- Abstract-node constructor for a normalized Pyash `be` word. -/
def pyashBeWordNode (word : String) : AbstractNode :=
  .apply (pyashBeWordCtor word) []

/-- Abstract-node constructor for a normalized English parallel head. -/
def pyashEnglishHeadNode (word : String) : AbstractNode :=
  .apply (pyashEnglishHeadCtor word) []

/-- Total lookup over the observed inventory. -/
def pyashBeWordNodeOf? (word : String) : Option AbstractNode :=
  if word ∈ pyashBeWordInventory then
    some (pyashBeWordNode word)
  else
    none

/-- Total lookup over observed English-head inventory. -/
def pyashEnglishHeadNodeOf? (word : String) : Option AbstractNode :=
  if word ∈ pyashEnglishHeadInventory then
    some (pyashEnglishHeadNode word)
  else
    none

/-- Typed pair lookup when both lexical sides are inventory-supported. -/
def pyashParallelPairNodeOf? (pyWord enHead : String) : Option AbstractNode := do
  let pyNode ← pyashBeWordNodeOf? pyWord
  let enNode ← pyashEnglishHeadNodeOf? enHead
  pure (.apply pyashParallelPairCtor [pyNode, enNode])

/-- Inventory support theorem: every inventory word has a GF constructor node. -/
theorem pyashBeWordInventory_supported :
    ∀ word ∈ pyashBeWordInventory, (pyashBeWordNodeOf? word).isSome := by
  intro word hword
  simp [pyashBeWordNodeOf?, hword]

/-- English-head support theorem: every observed head has a GF constructor node. -/
theorem pyashEnglishHeadInventory_supported :
    ∀ word ∈ pyashEnglishHeadInventory, (pyashEnglishHeadNodeOf? word).isSome := by
  intro word hword
  simp [pyashEnglishHeadNodeOf?, hword]

/-- If both sides are inventory-supported, the typed lexical pair node exists. -/
theorem pyashParallelPair_supported {pyWord enHead : String}
    (hpy : pyWord ∈ pyashBeWordInventory)
    (hen : enHead ∈ pyashEnglishHeadInventory) :
    (pyashParallelPairNodeOf? pyWord enHead).isSome := by
  simp [pyashParallelPairNodeOf?, pyashBeWordNodeOf?, pyashEnglishHeadNodeOf?, hpy, hen]

/-- Exportable constructor names for downstream tooling. -/
def pyashBeWordCtorNames : List String :=
  pyashBeWordInventory.map (fun word => (pyashBeWordCtor word).name)

/-- Exportable English-head constructor names for downstream tooling. -/
def pyashEnglishHeadCtorNames : List String :=
  pyashEnglishHeadInventory.map (fun word => (pyashEnglishHeadCtor word).name)

end Mettapedia.OSLF.Framework.PyashGFInventory
