import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.OSLF.MeTTaIL.Engine
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Pyash Core OSLF/GSLT Instance

This module formalizes a focused Pyash core from the current public spec and
implementation surface:

- sentence-first representation (`mood`, `verb`, role/type payload shape),
- signature-first dispatch staging,
- `do -> ya` result surfacing,
- alias normalization (`subj`/`obj` -> `su`/`ob`),
- signature-mismatch error surfacing.

References in the cloned upstream repository:
- `documentation/specifications/01-sentence-and-grammar.md`
- `documentation/specifications/02-core-execution.md`
- `program/understand/parse_tokens.mjs`
- `program/bridge/signature/derive.mjs`
- `program/bridge/index.mjs`
-/

namespace Mettapedia.OSLF.Framework.PyashCoreInstance

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.TypeSynthesis

/-- Focused, executable core model of Pyash sentence + dispatch semantics. -/
def pyashCore : LanguageDef := {
  name := "PyashCore",
  types := [
    "State", "Instr", "Sentence", "Mood", "Verb",
    "Role", "TypeTag", "RoleType", "RoleTypes",
    "Signature", "Outcome"
  ],
  terms := [
    { label := "State", category := "State",
      params := [
        .simple "instr" (.base "Instr"),
        .simple "sent" (.base "Sentence"),
        .simple "sig" (.base "Signature"),
        .simple "out" (.base "Outcome")
      ],
      syntaxPattern := [
        .terminal "State", .terminal "(",
        .nonTerminal "instr", .terminal ",",
        .nonTerminal "sent", .terminal ",",
        .nonTerminal "sig", .terminal ",",
        .nonTerminal "out", .terminal ")"
      ] },

    { label := "DeriveSignature", category := "Instr", params := [],
      syntaxPattern := [.terminal "DeriveSignature"] },
    { label := "Dispatch", category := "Instr", params := [],
      syntaxPattern := [.terminal "Dispatch"] },
    { label := "DispatchError", category := "Instr", params := [],
      syntaxPattern := [.terminal "DispatchError"] },
    { label := "RunDo", category := "Instr", params := [],
      syntaxPattern := [.terminal "RunDo"] },
    { label := "Done", category := "Instr", params := [],
      syntaxPattern := [.terminal "Done"] },

    { label := "SentenceCore", category := "Sentence",
      params := [
        .simple "m" (.base "Mood"),
        .simple "v" (.base "Verb"),
        .simple "rts" (.base "RoleTypes")
      ],
      syntaxPattern := [
        .terminal "SentenceCore", .terminal "(",
        .nonTerminal "m", .terminal ",",
        .nonTerminal "v", .terminal ",",
        .nonTerminal "rts", .terminal ")"
      ] },

    { label := "Signature", category := "Signature",
      params := [
        .simple "v" (.base "Verb"),
        .simple "rts" (.base "RoleTypes")
      ],
      syntaxPattern := [
        .terminal "Signature", .terminal "(",
        .nonTerminal "v", .terminal ",",
        .nonTerminal "rts", .terminal ")"
      ] },
    { label := "SigMismatch", category := "Signature",
      params := [
        .simple "expected" (.base "Signature"),
        .simple "actual" (.base "Signature")
      ],
      syntaxPattern := [
        .terminal "SigMismatch", .terminal "(",
        .nonTerminal "expected", .terminal ",",
        .nonTerminal "actual", .terminal ")"
      ] },

    { label := "RoleType", category := "RoleType",
      params := [
        .simple "role" (.base "Role"),
        .simple "ty" (.base "TypeTag")
      ],
      syntaxPattern := [
        .terminal "RoleType", .terminal "(",
        .nonTerminal "role", .terminal ",",
        .nonTerminal "ty", .terminal ")"
      ] },
    { label := "RTNil", category := "RoleTypes", params := [],
      syntaxPattern := [.terminal "RTNil"] },
    { label := "RTCons", category := "RoleTypes",
      params := [
        .simple "head" (.base "RoleType"),
        .simple "tail" (.base "RoleTypes")
      ],
      syntaxPattern := [
        .terminal "RTCons", .terminal "(",
        .nonTerminal "head", .terminal ",",
        .nonTerminal "tail", .terminal ")"
      ] },

    { label := "MYa", category := "Mood", params := [],
      syntaxPattern := [.terminal "ya"] },
    { label := "MDo", category := "Mood", params := [],
      syntaxPattern := [.terminal "do"] },
    { label := "MDef", category := "Mood", params := [],
      syntaxPattern := [.terminal "def"] },
    { label := "MPrah", category := "Mood", params := [],
      syntaxPattern := [.terminal "prah"] },
    { label := "MThen", category := "Mood", params := [],
      syntaxPattern := [.terminal "then"] },
    { label := "MRet", category := "Mood", params := [],
      syntaxPattern := [.terminal "ret"] },

    { label := "VPlus", category := "Verb", params := [],
      syntaxPattern := [.terminal "plus"] },
    { label := "VRead", category := "Verb", params := [],
      syntaxPattern := [.terminal "read"] },
    { label := "VWrite", category := "Verb", params := [],
      syntaxPattern := [.terminal "write"] },
    { label := "VSay", category := "Verb", params := [],
      syntaxPattern := [.terminal "say"] },
    { label := "VMap", category := "Verb", params := [],
      syntaxPattern := [.terminal "map"] },
    { label := "VCommand", category := "Verb", params := [],
      syntaxPattern := [.terminal "command"] },
    { label := "VSearch", category := "Verb", params := [],
      syntaxPattern := [.terminal "search"] },
    { label := "VMind", category := "Verb", params := [],
      syntaxPattern := [.terminal "mind"] },
    { label := "VChip", category := "Verb", params := [],
      syntaxPattern := [.terminal "chip"] },
    { label := "VHear", category := "Verb", params := [],
      syntaxPattern := [.terminal "hear"] },
    { label := "VConfigure", category := "Verb", params := [],
      syntaxPattern := [.terminal "configure"] },
    { label := "VWorld", category := "Verb", params := [],
      syntaxPattern := [.terminal "world"] },
    { label := "VPipeline", category := "Verb", params := [],
      syntaxPattern := [.terminal "pipeline"] },
    { label := "VCompile", category := "Verb", params := [],
      syntaxPattern := [.terminal "compile"] },
    { label := "VImport", category := "Verb", params := [],
      syntaxPattern := [.terminal "import"] },
    { label := "VDownload", category := "Verb", params := [],
      syntaxPattern := [.terminal "download"] },
    { label := "VTranslation", category := "Verb", params := [],
      syntaxPattern := [.terminal "translation"] },
    { label := "VCeremony", category := "Verb", params := [],
      syntaxPattern := [.terminal "ceremony"] },
    { label := "VDefault", category := "Verb", params := [],
      syntaxPattern := [.terminal "default"] },
    { label := "VError", category := "Verb", params := [],
      syntaxPattern := [.terminal "error"] },

    { label := "Su", category := "Role", params := [],
      syntaxPattern := [.terminal "su"] },
    { label := "Ob", category := "Role", params := [],
      syntaxPattern := [.terminal "ob"] },
    { label := "From", category := "Role", params := [],
      syntaxPattern := [.terminal "from"] },
    { label := "To", category := "Role", params := [],
      syntaxPattern := [.terminal "to"] },
    { label := "FromState", category := "Role", params := [],
      syntaxPattern := [.terminal "fromstate"] },
    { label := "Become", category := "Role", params := [],
      syntaxPattern := [.terminal "become"] },
    { label := "FromText", category := "Role", params := [],
      syntaxPattern := [.terminal "fromtext"] },
    { label := "AccordingTo", category := "Role", params := [],
      syntaxPattern := [.terminal "accordingto"] },
    { label := "ToText", category := "Role", params := [],
      syntaxPattern := [.terminal "totext"] },
    { label := "FromIndex", category := "Role", params := [],
      syntaxPattern := [.terminal "fromindex"] },
    { label := "AtIndex", category := "Role", params := [],
      syntaxPattern := [.terminal "atindex"] },
    { label := "ToIndex", category := "Role", params := [],
      syntaxPattern := [.terminal "toindex"] },
    { label := "During", category := "Role", params := [],
      syntaxPattern := [.terminal "during"] },
    { label := "AtLeast", category := "Role", params := [],
      syntaxPattern := [.terminal "atleast"] },
    { label := "AtMost", category := "Role", params := [],
      syntaxPattern := [.terminal "atmost"] },
    { label := "By", category := "Role", params := [],
      syntaxPattern := [.terminal "by"] },
    { label := "Vyah", category := "Role", params := [],
      syntaxPattern := [.terminal "vyah"] },
    { label := "SubjAlias", category := "Role", params := [],
      syntaxPattern := [.terminal "subj"] },
    { label := "ObjAlias", category := "Role", params := [],
      syntaxPattern := [.terminal "obj"] },

    { label := "TName", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "name"] },
    { label := "TNum", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "num"] },
    { label := "TText", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "text"] },
    { label := "TFilename", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "filename"] },
    { label := "TBool", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "bool"] },
    { label := "TWo", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "wo"] },
    { label := "TVec", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "vec"] },
    { label := "TDate", category := "TypeTag", params := [],
      syntaxPattern := [.terminal "date"] },

    { label := "Ok", category := "Outcome", params := [],
      syntaxPattern := [.terminal "ok"] },
    { label := "ErrSignature", category := "Outcome", params := [],
      syntaxPattern := [.terminal "signature-error"] },
    { label := "ErrDispatch", category := "Outcome", params := [],
      syntaxPattern := [.terminal "dispatch-error"] }
  ],
  equations := [],
  rewrites := [
    -- Aliases are normalized to canonical role names before signature dispatch.
    { name := "NormalizeSubjAlias",
      typeContext := [("t", .base "TypeTag")],
      premises := [],
      left := .apply "RoleType" [.apply "SubjAlias" [], .fvar "t"],
      right := .apply "RoleType" [.apply "Su" [], .fvar "t"] },
    { name := "NormalizeObjAlias",
      typeContext := [("t", .base "TypeTag")],
      premises := [],
      left := .apply "RoleType" [.apply "ObjAlias" [], .fvar "t"],
      right := .apply "RoleType" [.apply "Ob" [], .fvar "t"] },

    -- Signature-first staging.
    { name := "StepDeriveSignature",
      typeContext := [
        ("m", .base "Mood"), ("v", .base "Verb"), ("rts", .base "RoleTypes"),
        ("sig", .base "Signature"), ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "DeriveSignature" [],
        .apply "SentenceCore" [.fvar "m", .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.fvar "m", .fvar "v", .fvar "rts"],
        .apply "Signature" [.fvar "v", .fvar "rts"],
        .fvar "out"
      ] },

    -- Mood-based dispatch branches.
    { name := "StepDispatchDo",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MDo" [], .fvar "v", .fvar "rts"],
        .apply "Signature" [.fvar "v", .fvar "rts"],
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "RunDo" [],
        .apply "SentenceCore" [.apply "MDo" [], .fvar "v", .fvar "rts"],
        .apply "Signature" [.fvar "v", .fvar "rts"],
        .fvar "out"
      ] },
    { name := "StepDispatchYa",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("sig", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MYa" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MYa" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .apply "Ok" []
      ] },
    { name := "StepDispatchDef",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("sig", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MDef" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MDef" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .apply "Ok" []
      ] },
    { name := "StepDispatchPrah",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("sig", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MPrah" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MPrah" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .apply "Ok" []
      ] },
    { name := "StepDispatchRet",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("sig", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MRet" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MRet" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .apply "Ok" []
      ] },

    -- Explicit dispatch-error instruction for deterministic negative-path testing.
    { name := "StepDispatchErrorInstr",
      typeContext := [
        ("m", .base "Mood"), ("v", .base "Verb"), ("rts", .base "RoleTypes"),
        ("sig", .base "Signature"), ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "DispatchError" [],
        .apply "SentenceCore" [.fvar "m", .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], .fvar "rts"],
        .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
        .apply "ErrDispatch" []
      ] },

    -- Unsupported mood dispatch can surface an explicit dispatch error.
    { name := "StepDispatchThenError",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.apply "MThen" [], .fvar "v", .fvar "rts"],
        .apply "Signature" [.fvar "v", .fvar "rts"],
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], .fvar "rts"],
        .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
        .apply "ErrDispatch" []
      ] },

    -- Signature mismatch is surfaced as an error sentence outcome.
    { name := "StepDispatchMismatch",
      typeContext := [
        ("m", .base "Mood"), ("v", .base "Verb"), ("rts", .base "RoleTypes"),
        ("expected", .base "Signature"), ("actual", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "Dispatch" [],
        .apply "SentenceCore" [.fvar "m", .fvar "v", .fvar "rts"],
        .apply "SigMismatch" [.fvar "expected", .fvar "actual"],
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], .fvar "rts"],
        .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
        .apply "ErrSignature" []
      ] },

    -- `do` execution emits a `ya`-mood result sentence.
    { name := "StepRunDo",
      typeContext := [
        ("v", .base "Verb"), ("rts", .base "RoleTypes"), ("sig", .base "Signature"),
        ("out", .base "Outcome")
      ],
      premises := [],
      left := .apply "State" [
        .apply "RunDo" [],
        .apply "SentenceCore" [.apply "MDo" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .fvar "out"
      ],
      right := .apply "State" [
        .apply "Done" [],
        .apply "SentenceCore" [.apply "MYa" [], .fvar "v", .fvar "rts"],
        .fvar "sig",
        .apply "Ok" []
      ] }
  ]
}

/-- OSLF synthesis endpoint for `pyashCore` (process sort = `State`). -/
def pyashCoreOSLF := langOSLF pyashCore "State"

/-- Automatic Galois connection for Pyash core dispatch semantics. -/
theorem pyashCoreGalois :
    GaloisConnection (langDiamond pyashCore) (langBox pyashCore) :=
  langGalois pyashCore

/-- Structural recognizer for focused Pyash instruction constructors. -/
def isPyashInstr : Pattern → Prop
  | .apply "DeriveSignature" [] => True
  | .apply "Dispatch" [] => True
  | .apply "DispatchError" [] => True
  | .apply "RunDo" [] => True
  | .apply "Done" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash mood constructors. -/
def isPyashMood : Pattern → Prop
  | .apply "MYa" [] => True
  | .apply "MDo" [] => True
  | .apply "MDef" [] => True
  | .apply "MPrah" [] => True
  | .apply "MThen" [] => True
  | .apply "MRet" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash verb constructors. -/
def isPyashVerb : Pattern → Prop
  | .apply "VPlus" [] => True
  | .apply "VRead" [] => True
  | .apply "VWrite" [] => True
  | .apply "VSay" [] => True
  | .apply "VMap" [] => True
  | .apply "VCommand" [] => True
  | .apply "VSearch" [] => True
  | .apply "VMind" [] => True
  | .apply "VChip" [] => True
  | .apply "VHear" [] => True
  | .apply "VConfigure" [] => True
  | .apply "VWorld" [] => True
  | .apply "VPipeline" [] => True
  | .apply "VCompile" [] => True
  | .apply "VImport" [] => True
  | .apply "VDownload" [] => True
  | .apply "VTranslation" [] => True
  | .apply "VCeremony" [] => True
  | .apply "VDefault" [] => True
  | .apply "VError" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash role constructors. -/
def isPyashRole : Pattern → Prop
  | .apply "Su" [] => True
  | .apply "Ob" [] => True
  | .apply "From" [] => True
  | .apply "To" [] => True
  | .apply "FromState" [] => True
  | .apply "Become" [] => True
  | .apply "FromText" [] => True
  | .apply "AccordingTo" [] => True
  | .apply "ToText" [] => True
  | .apply "FromIndex" [] => True
  | .apply "AtIndex" [] => True
  | .apply "ToIndex" [] => True
  | .apply "During" [] => True
  | .apply "AtLeast" [] => True
  | .apply "AtMost" [] => True
  | .apply "By" [] => True
  | .apply "Vyah" [] => True
  | .apply "SubjAlias" [] => True
  | .apply "ObjAlias" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash type-tag constructors. -/
def isPyashTypeTag : Pattern → Prop
  | .apply "TName" [] => True
  | .apply "TNum" [] => True
  | .apply "TText" [] => True
  | .apply "TFilename" [] => True
  | .apply "TBool" [] => True
  | .apply "TWo" [] => True
  | .apply "TVec" [] => True
  | .apply "TDate" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash role/type pairs. -/
def isPyashRoleType : Pattern → Prop
  | .apply "RoleType" [role, ty] => isPyashRole role ∧ isPyashTypeTag ty
  | _ => False

/-- Structural recognizer for focused Pyash role/type lists. -/
def isPyashRoleTypes : Pattern → Prop
  | .apply "RTNil" [] => True
  | .apply "RTCons" [head, tail] => isPyashRoleType head ∧ isPyashRoleTypes tail
  | _ => False

/-- Structural recognizer for focused Pyash signatures and mismatch wrappers. -/
def isPyashSignature : Pattern → Prop
  | .apply "Signature" [verb, roleTypes] => isPyashVerb verb ∧ isPyashRoleTypes roleTypes
  | .apply "SigMismatch" [expected, actual] => isPyashSignature expected ∧ isPyashSignature actual
  | _ => False

/-- Structural recognizer for focused Pyash sentence cores. -/
def isPyashSentence : Pattern → Prop
  | .apply "SentenceCore" [mood, verb, roleTypes] =>
      isPyashMood mood ∧ isPyashVerb verb ∧ isPyashRoleTypes roleTypes
  | _ => False

/-- Structural recognizer for focused Pyash outcomes. -/
def isPyashOutcome : Pattern → Prop
  | .apply "Ok" [] => True
  | .apply "ErrSignature" [] => True
  | .apply "ErrDispatch" [] => True
  | _ => False

/-- Structural recognizer for focused Pyash runtime states. -/
def isPyashState : Pattern → Prop
  | .apply "State" [instr, sent, sig, out] =>
      isPyashInstr instr ∧ isPyashSentence sent ∧ isPyashSignature sig ∧ isPyashOutcome out
  | _ => False

/-- Canonical native top type over the `State` sort. -/
def pyashStateTop : langNativeType pyashCore "State" where
  sort := "State"
  pred := isPyashState

/-- Render focused Pyash patterns into runtime `C_...` constructor syntax. -/
partial def renderPyashCtorPattern : Pattern → String
  | .bvar n => s!"bvar{n}"
  | .fvar x => x
  | .apply c [] => "C_" ++ c
  | .apply c args =>
      "C_" ++ c ++ "(" ++ String.intercalate "," (args.map renderPyashCtorPattern) ++ ")"
  | .lambda body => s!"lambda({renderPyashCtorPattern body})"
  | .multiLambda n body => s!"multilambda({n},{renderPyashCtorPattern body})"
  | .subst body repl =>
      s!"subst({renderPyashCtorPattern body},{renderPyashCtorPattern repl})"
  | .collection .vec elems _ =>
      "[" ++ String.intercalate "," (elems.map renderPyashCtorPattern) ++ "]"
  | .collection .hashBag elems _ =>
      "{" ++ String.intercalate "," (elems.map renderPyashCtorPattern) ++ "}"
  | .collection .hashSet elems _ =>
      "#{" ++ String.intercalate "," (elems.map renderPyashCtorPattern) ++ "}"

/-- A small role/type list used by executable canaries. -/
def pyashRoleTypesDemo : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "Ob" [], .apply "TNum" []],
      .apply "RTNil" []
    ]
  ]

/-- Signature payload for `read`: subject name + from filename. -/
def pyashRoleTypesRead : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "From" [], .apply "TFilename" []],
      .apply "RTNil" []
    ]
  ]

/-- Signature payload for `write`: payload text + destination filename. -/
def pyashRoleTypesWrite : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
      .apply "RTNil" []
    ]
  ]

/-- Signature payload for `say`: payload text + destination filename. -/
def pyashRoleTypesSay : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
      .apply "RTNil" []
    ]
  ]

/-- Signature payload for `map`: map name anchor. -/
def pyashRoleTypesMap : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTNil" []
  ]

/-- Signature payload for `command`: command text + captured output text. -/
def pyashRoleTypesCommand : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "To" [], .apply "TText" []],
      .apply "RTNil" []
    ]
  ]

/-- Signature payload for `search`: named output + query text + web selector + result limit. -/
def pyashRoleTypesSearch : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "By" [], .apply "TNum" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Signature payload for `mind`: subject name + object text + destination text. -/
def pyashRoleTypesMind : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "To" [], .apply "TText" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for ceremony dispatch path. -/
def pyashRoleTypesCeremony : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `chip`: subject name + source text + boundary/text policy + destination text. -/
def pyashRoleTypesChip : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "By" [], .apply "TText" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Alternate `chip` signature payload: source text + boundary series name + destination text. -/
def pyashRoleTypesChipSeries : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "By" [], .apply "TName" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Alternate bounded `chip` signature payload with explicit byte constraints. -/
def pyashRoleTypesChipBounded : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "By" [], .apply "TName" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "AtLeast" [], .apply "TNum" []],
          .apply "RTCons" [
            .apply "RoleType" [.apply "AtMost" [], .apply "TNum" []],
            .apply "RTCons" [
              .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
              .apply "RTNil" []
            ]
          ]
        ]
      ]
    ]
  ]

/-- Signature payload for `hear`: subject name + source filename + destination text. -/
def pyashRoleTypesHear : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "From" [], .apply "TFilename" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "To" [], .apply "TText" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Alternate `hear` signature payload: microphone source + duration + recorded filename. -/
def pyashRoleTypesHearMicRecord : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "From" [], .apply "TWo" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "During" [], .apply "TNum" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Alternate `hear` signature payload: source filename to output subtitle filename. -/
def pyashRoleTypesHearFileSrt : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "From" [], .apply "TFilename" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
          .apply "RTNil" []
        ]
      ]
    ]
  ]

/-- Signature payload for `configure`: subject name + policy text + destination text. -/
def pyashRoleTypesConfigure : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "By" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `world`: subject name + world input text + world output text. -/
def pyashRoleTypesWorld : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "ToText" [], .apply "TText" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `pipeline`: subject name + source state + destination state. -/
def pyashRoleTypesPipeline : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `compile`: subject name + source text + source state + target state + output filename. -/
def pyashRoleTypesCompile : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
          .apply "RTCons" [
            .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
            .apply "RTNil" []
          ]
        ]
      ]
    ]
  ]

/-- Signature payload for `import`: subject name + source module name + destination binding name. -/
def pyashRoleTypesImport : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "From" [], .apply "TName" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "To" [], .apply "TName" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `download`: subject name + source URL text + output filename. -/
def pyashRoleTypesDownload : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "Ob" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "To" [], .apply "TFilename" []],
        .apply "RTNil" []
      ]
    ]
  ]

/-- Signature payload for `translation`: subject name + source text + target binding + source/target language states. -/
def pyashRoleTypesTranslation : Pattern :=
  .apply "RTCons" [
    .apply "RoleType" [.apply "Su" [], .apply "TName" []],
    .apply "RTCons" [
      .apply "RoleType" [.apply "FromText" [], .apply "TText" []],
      .apply "RTCons" [
        .apply "RoleType" [.apply "To" [], .apply "TName" []],
        .apply "RTCons" [
          .apply "RoleType" [.apply "FromState" [], .apply "TWo" []],
          .apply "RTCons" [
            .apply "RoleType" [.apply "Become" [], .apply "TWo" []],
            .apply "RTNil" []
          ]
        ]
      ]
    ]
  ]

/-- Initial state: parse-stage sentence still needs signature derivation. -/
def pyashStateDeriveSignature : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- After signature derivation, dispatch is ready with normalized signature payload. -/
def pyashStateDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Signature" [.apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Ok" []
  ]

/-- Dispatching `do` enters the run phase. -/
def pyashStateRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Signature" [.apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Ok" []
  ]

/-- Executing `do` surfaces a `ya` result and halts. -/
def pyashStateDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Signature" [.apply "VPlus" [], pyashRoleTypesDemo],
    .apply "Ok" []
  ]

/-- `read` state before signature derivation. -/
def pyashStateReadDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `read` state after signature derivation. -/
def pyashStateReadDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- `read` state after dispatch enters run phase. -/
def pyashStateReadRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- `read` done state. -/
def pyashStateReadDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- `write` state before signature derivation. -/
def pyashStateWriteDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `write` state after signature derivation. -/
def pyashStateWriteDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Signature" [.apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Ok" []
  ]

/-- `write` state after dispatch enters run phase. -/
def pyashStateWriteRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Signature" [.apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Ok" []
  ]

/-- `write` done state. -/
def pyashStateWriteDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Signature" [.apply "VWrite" [], pyashRoleTypesWrite],
    .apply "Ok" []
  ]

/-- `say` state before signature derivation. -/
def pyashStateSayDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSay" [], pyashRoleTypesSay],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `say` state after signature derivation. -/
def pyashStateSayDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSay" [], pyashRoleTypesSay],
    .apply "Signature" [.apply "VSay" [], pyashRoleTypesSay],
    .apply "Ok" []
  ]

/-- `say` state after dispatch enters run phase. -/
def pyashStateSayRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSay" [], pyashRoleTypesSay],
    .apply "Signature" [.apply "VSay" [], pyashRoleTypesSay],
    .apply "Ok" []
  ]

/-- `say` done state. -/
def pyashStateSayDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VSay" [], pyashRoleTypesSay],
    .apply "Signature" [.apply "VSay" [], pyashRoleTypesSay],
    .apply "Ok" []
  ]

/-- `map` state before signature derivation. -/
def pyashStateMapDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `map` state after signature derivation. -/
def pyashStateMapDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VMap" [], pyashRoleTypesMap],
    .apply "Ok" []
  ]

/-- `map` state after dispatch enters run phase. -/
def pyashStateMapRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VMap" [], pyashRoleTypesMap],
    .apply "Ok" []
  ]

/-- `map` done state. -/
def pyashStateMapDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VMap" [], pyashRoleTypesMap],
    .apply "Ok" []
  ]

/-- `map` (`def` mood) state before signature derivation. -/
def pyashStateMapDefDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `map` (`def` mood) state after signature derivation. -/
def pyashStateMapDefDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VMap" [], pyashRoleTypesMap],
    .apply "Ok" []
  ]

/-- `map` (`def` mood) terminal done state. -/
def pyashStateMapDefDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VMap" [], pyashRoleTypesMap],
    .apply "Signature" [.apply "VMap" [], pyashRoleTypesMap],
    .apply "Ok" []
  ]

/-- `command` state before signature derivation. -/
def pyashStateCommandDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `command` state after signature derivation. -/
def pyashStateCommandDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Signature" [.apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Ok" []
  ]

/-- `command` state after dispatch enters run phase. -/
def pyashStateCommandRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Signature" [.apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Ok" []
  ]

/-- `command` done state. -/
def pyashStateCommandDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Signature" [.apply "VCommand" [], pyashRoleTypesCommand],
    .apply "Ok" []
  ]

/-- `search` state before signature derivation. -/
def pyashStateSearchDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `search` state after signature derivation. -/
def pyashStateSearchDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Signature" [.apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Ok" []
  ]

/-- `search` state after dispatch enters run phase. -/
def pyashStateSearchRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Signature" [.apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Ok" []
  ]

/-- `search` done state. -/
def pyashStateSearchDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Signature" [.apply "VSearch" [], pyashRoleTypesSearch],
    .apply "Ok" []
  ]

/-- `mind` state before signature derivation. -/
def pyashStateMindDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMind" [], pyashRoleTypesMind],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `mind` state after signature derivation. -/
def pyashStateMindDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMind" [], pyashRoleTypesMind],
    .apply "Signature" [.apply "VMind" [], pyashRoleTypesMind],
    .apply "Ok" []
  ]

/-- `mind` state after dispatch enters run phase. -/
def pyashStateMindRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VMind" [], pyashRoleTypesMind],
    .apply "Signature" [.apply "VMind" [], pyashRoleTypesMind],
    .apply "Ok" []
  ]

/-- `mind` done state. -/
def pyashStateMindDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VMind" [], pyashRoleTypesMind],
    .apply "Signature" [.apply "VMind" [], pyashRoleTypesMind],
    .apply "Ok" []
  ]

/-- `ceremony` state before signature derivation. -/
def pyashStateCeremonyDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `ceremony` state after signature derivation. -/
def pyashStateCeremonyDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Signature" [.apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Ok" []
  ]

/-- `ceremony` state after dispatch enters run phase. -/
def pyashStateCeremonyRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Signature" [.apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Ok" []
  ]

/-- `ceremony` done state. -/
def pyashStateCeremonyDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Signature" [.apply "VCeremony" [], pyashRoleTypesCeremony],
    .apply "Ok" []
  ]

/-- `chip` state before signature derivation. -/
def pyashStateChipDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChip],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `chip` state after signature derivation. -/
def pyashStateChipDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChip],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChip],
    .apply "Ok" []
  ]

/-- `chip` state after dispatch enters run phase. -/
def pyashStateChipRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChip],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChip],
    .apply "Ok" []
  ]

/-- `chip` done state. -/
def pyashStateChipDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VChip" [], pyashRoleTypesChip],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChip],
    .apply "Ok" []
  ]

/-- `chip` (series variant) state before signature derivation. -/
def pyashStateChipSeriesDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `chip` (series variant) state after signature derivation. -/
def pyashStateChipSeriesDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Ok" []
  ]

/-- `chip` (series variant) state after dispatch enters run phase. -/
def pyashStateChipSeriesRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Ok" []
  ]

/-- `chip` (series variant) done state. -/
def pyashStateChipSeriesDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipSeries],
    .apply "Ok" []
  ]

/-- `chip` (bounded variant) state before signature derivation. -/
def pyashStateChipBoundedDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `chip` (bounded variant) state after signature derivation. -/
def pyashStateChipBoundedDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Ok" []
  ]

/-- `chip` (bounded variant) state after dispatch enters run phase. -/
def pyashStateChipBoundedRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Ok" []
  ]

/-- `chip` (bounded variant) done state. -/
def pyashStateChipBoundedDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Signature" [.apply "VChip" [], pyashRoleTypesChipBounded],
    .apply "Ok" []
  ]

/-- `hear` state before signature derivation. -/
def pyashStateHearDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHear],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `hear` state after signature derivation. -/
def pyashStateHearDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHear],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHear],
    .apply "Ok" []
  ]

/-- `hear` state after dispatch enters run phase. -/
def pyashStateHearRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHear],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHear],
    .apply "Ok" []
  ]

/-- `hear` done state. -/
def pyashStateHearDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VHear" [], pyashRoleTypesHear],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHear],
    .apply "Ok" []
  ]

/-- `hear` (microphone-recording variant) state before signature derivation. -/
def pyashStateHearMicRecordDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `hear` (microphone-recording variant) state after signature derivation. -/
def pyashStateHearMicRecordDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Ok" []
  ]

/-- `hear` (microphone-recording variant) state after dispatch enters run phase. -/
def pyashStateHearMicRecordRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Ok" []
  ]

/-- `hear` (microphone-recording variant) done state. -/
def pyashStateHearMicRecordDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearMicRecord],
    .apply "Ok" []
  ]

/-- `hear` (file->subtitle-file variant) state before signature derivation. -/
def pyashStateHearFileSrtDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `hear` (file->subtitle-file variant) state after signature derivation. -/
def pyashStateHearFileSrtDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Ok" []
  ]

/-- `hear` (file->subtitle-file variant) state after dispatch enters run phase. -/
def pyashStateHearFileSrtRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Ok" []
  ]

/-- `hear` (file->subtitle-file variant) done state. -/
def pyashStateHearFileSrtDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Signature" [.apply "VHear" [], pyashRoleTypesHearFileSrt],
    .apply "Ok" []
  ]

/-- `configure` state before signature derivation. -/
def pyashStateConfigureDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `configure` state after signature derivation. -/
def pyashStateConfigureDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

/-- `configure` state after dispatch enters run phase. -/
def pyashStateConfigureRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

/-- `configure` done state. -/
def pyashStateConfigureDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

/-- `configure` (`def` mood/map baseline) state before signature derivation. -/
def pyashStateConfigureDefDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `configure` (`def` mood/map baseline) state after signature derivation. -/
def pyashStateConfigureDefDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

/-- `configure` (`def` mood/map baseline) terminal done state. -/
def pyashStateConfigureDefDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MDef" [], .apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Signature" [.apply "VConfigure" [], pyashRoleTypesConfigure],
    .apply "Ok" []
  ]

/-- `world` state before signature derivation. -/
def pyashStateWorldDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `world` state after signature derivation. -/
def pyashStateWorldDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Ok" []
  ]

/-- `world` state after dispatch enters run phase. -/
def pyashStateWorldRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Ok" []
  ]

/-- `world` done state. -/
def pyashStateWorldDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Signature" [.apply "VWorld" [], pyashRoleTypesWorld],
    .apply "Ok" []
  ]

/-- `pipeline` state before signature derivation. -/
def pyashStatePipelineDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `pipeline` state after signature derivation. -/
def pyashStatePipelineDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Ok" []
  ]

/-- `pipeline` state after dispatch enters run phase. -/
def pyashStatePipelineRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Ok" []
  ]

/-- `pipeline` done state. -/
def pyashStatePipelineDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Signature" [.apply "VPipeline" [], pyashRoleTypesPipeline],
    .apply "Ok" []
  ]

/-- `compile` state before signature derivation. -/
def pyashStateCompileDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `compile` state after signature derivation. -/
def pyashStateCompileDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Signature" [.apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Ok" []
  ]

/-- `compile` state after dispatch enters run phase. -/
def pyashStateCompileRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Signature" [.apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Ok" []
  ]

/-- `compile` done state. -/
def pyashStateCompileDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Signature" [.apply "VCompile" [], pyashRoleTypesCompile],
    .apply "Ok" []
  ]

/-- `import` state before signature derivation. -/
def pyashStateImportDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VImport" [], pyashRoleTypesImport],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `import` state after signature derivation. -/
def pyashStateImportDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VImport" [], pyashRoleTypesImport],
    .apply "Signature" [.apply "VImport" [], pyashRoleTypesImport],
    .apply "Ok" []
  ]

/-- `import` state after dispatch enters run phase. -/
def pyashStateImportRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VImport" [], pyashRoleTypesImport],
    .apply "Signature" [.apply "VImport" [], pyashRoleTypesImport],
    .apply "Ok" []
  ]

/-- `import` done state. -/
def pyashStateImportDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VImport" [], pyashRoleTypesImport],
    .apply "Signature" [.apply "VImport" [], pyashRoleTypesImport],
    .apply "Ok" []
  ]

/-- `download` state before signature derivation. -/
def pyashStateDownloadDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `download` state after signature derivation. -/
def pyashStateDownloadDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Signature" [.apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Ok" []
  ]

/-- `download` state after dispatch enters run phase. -/
def pyashStateDownloadRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Signature" [.apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Ok" []
  ]

/-- `download` done state. -/
def pyashStateDownloadDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Signature" [.apply "VDownload" [], pyashRoleTypesDownload],
    .apply "Ok" []
  ]

/-- `translation` state before signature derivation. -/
def pyashStateTranslationDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `translation` state after signature derivation. -/
def pyashStateTranslationDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Signature" [.apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Ok" []
  ]

/-- `translation` state after dispatch enters run phase. -/
def pyashStateTranslationRunning : Pattern :=
  .apply "State" [
    .apply "RunDo" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Signature" [.apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Ok" []
  ]

/-- `translation` done state. -/
def pyashStateTranslationDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Signature" [.apply "VTranslation" [], pyashRoleTypesTranslation],
    .apply "Ok" []
  ]

/-- `ret`/`read` state before signature derivation. -/
def pyashStateRetReadDerive : Pattern :=
  .apply "State" [
    .apply "DeriveSignature" [],
    .apply "SentenceCore" [.apply "MRet" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "Ok" []
  ]

/-- `ret`/`read` state after signature derivation. -/
def pyashStateRetReadDispatched : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MRet" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- `ret`/`read` terminal state after explicit `ret` dispatch. -/
def pyashStateRetReadDoneOk : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MRet" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- Dispatch error trigger state (`then` with no runnable branch) used as a negative case. -/
def pyashStateDispatchThenError : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MThen" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- Explicit dispatch-error instruction trigger state used as deterministic negative case. -/
def pyashStateDispatchErrorInstr : Pattern :=
  .apply "State" [
    .apply "DispatchError" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
    .apply "Ok" []
  ]

/-- Dispatch error terminal state. -/
def pyashStateDoneDispatchErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrDispatch" []
  ]

/-- Malformed nested signature shape used as a negative signature regression case. -/
def pyashStateMalformedSignatureShape : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VRead" [], pyashRoleTypesRead],
    .apply "SigMismatch" [
      .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead],
      .apply "SigMismatch" [
        .apply "Signature" [.apply "VRead" [], .apply "RTNil" []],
        .apply "Signature" [.apply "VRead" [], pyashRoleTypesRead]
      ]
    ],
    .apply "Ok" []
  ]

/-- Malformed signature shape terminal error state. -/
def pyashStateDoneMalformedSignatureErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesRead],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrSignature" []
  ]

/-- Mismatch state used to verify error surfacing behavior. -/
def pyashStateMismatch : Pattern :=
  .apply "State" [
    .apply "Dispatch" [],
    .apply "SentenceCore" [.apply "MDo" [], .apply "VPlus" [], pyashRoleTypesDemo],
    .apply "SigMismatch" [
      .apply "Signature" [.apply "VPlus" [], pyashRoleTypesDemo],
      .apply "Signature" [.apply "VRead" [], pyashRoleTypesDemo]
    ],
    .apply "Ok" []
  ]

/-- Dispatch mismatch produces an error sentence in `ya` mood and halts. -/
def pyashStateDoneSignatureErr : Pattern :=
  .apply "State" [
    .apply "Done" [],
    .apply "SentenceCore" [.apply "MYa" [], .apply "VError" [], pyashRoleTypesDemo],
    .apply "Signature" [.apply "VError" [], .apply "RTNil" []],
    .apply "ErrSignature" []
  ]

end Mettapedia.OSLF.Framework.PyashCoreInstance
