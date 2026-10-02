import Mettapedia.GSLT.LanguageDef.NativeOpsCStatement
import Mettapedia.GSLT.LanguageDef.NativeOpsSource

/-!
# Admission of native C declarations

The header reader retains every include, forward declaration, record layout,
array typedef and prototype. It consumes the complete header, including a
matching include guard. Declaration spelling grants no external authority;
the separate representation check uses the admitted operational interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option Elab.async false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

inductive HeaderItem where
  | include (header : Name)
  | forward (tag spelling : Name)
  | record (tag : Name) (fields : List CParameter)
  | array (spelling : Name) (fields : List CParameter)
  | prototype (result : CType) (name : Name) (parameters : List CParameter)
  deriving DecidableEq, Repr

structure CHeader where
  guard : Name
  items : List HeaderItem
  deriving DecidableEq, Repr

/-- Parsing an identifier as a type does not authorize that type. -/
def rawType? : List Token → Option (CType × List Token)
  | .identifier name :: rest =>
      let suffix := pointerSuffix rest
      some (⟨name, suffix.1⟩, suffix.2)
  | _ => none

def headerFields? (fuel : Nat) (tokens : List Token) : Option (List CParameter × List Token) :=
  match tokens with
  | .punctuation ['}'] :: after => some ([], after)
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (type, afterType) ← rawType? tokens
        match afterType with
        | .identifier name :: .punctuation [';'] :: after => do
            let (others, rest) ← headerFields? fuel after
            some (⟨type, name⟩ :: others, rest)
        | _ => none

def headerParameters? (fuel : Nat) (tokens : List Token) :
    Option (List CParameter × List Token) :=
  match tokens with
  | .punctuation [')'] :: after => some ([], after)
  | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: after => some ([], after)
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (type, afterType) ← rawType? tokens
        match afterType with
        | .identifier name :: .punctuation [')'] :: after => some ([⟨type, name⟩], after)
        | .identifier name :: .punctuation [','] :: after => do
            match after with
            | .punctuation [')'] :: _ => none
            | .identifier ['v', 'o', 'i', 'd'] :: .punctuation [')'] :: _ => none
            | _ => pure ()
            let (others, rest) ← headerParameters? fuel after
            some (⟨type, name⟩ :: others, rest)
        | _ => none

def headerItem? (fuel : Nat) (tokens : List Token) : Option (HeaderItem × List Token) :=
  match tokens with
  | .punctuation ['#'] :: .identifier ['i', 'n', 'c', 'l', 'u', 'd', 'e'] ::
      .quoted header :: after => some (.include header, after)
  | .identifier ['t', 'y', 'p', 'e', 'd', 'e', 'f'] ::
      .identifier ['s', 't', 'r', 'u', 'c', 't'] :: .identifier tag ::
      .identifier spelling :: .punctuation [';'] :: after => some (.forward tag spelling, after)
  | .identifier ['t', 'y', 'p', 'e', 'd', 'e', 'f'] ::
      .identifier ['s', 't', 'r', 'u', 'c', 't'] :: .punctuation ['{'] :: rest => do
      let (fields, afterFields) ← headerFields? fuel rest
      match afterFields with
      | .identifier spelling :: .punctuation [';'] :: after => some (.array spelling fields, after)
      | _ => none
  | .identifier ['s', 't', 'r', 'u', 'c', 't'] :: .identifier tag ::
      .punctuation ['{'] :: rest => do
      let (fields, afterFields) ← headerFields? fuel rest
      match afterFields with
      | .punctuation [';'] :: after => some (.record tag fields, after)
      | _ => none
  | _ => do
      let (result, afterType) ← rawType? tokens
      match afterType with
      | .identifier name :: .punctuation ['('] :: rest => do
          let (parameters, afterParameters) ← headerParameters? fuel rest
          match afterParameters with
          | .punctuation [';'] :: after => some (.prototype result name parameters, after)
          | _ => none
      | _ => none

def headerItems? (fuel : Nat) (tokens : List Token) : Option (List HeaderItem) :=
  match tokens with
  | [.punctuation ['#'], .identifier ['e', 'n', 'd', 'i', 'f']] => some []
  | _ => match fuel with
    | 0 => none
    | fuel + 1 => do
        let (first, afterFirst) ← headerItem? fuel tokens
        let others ← headerItems? fuel afterFirst
        some (first :: others)

def completeHeader? (tokens : List Token) : Option CHeader :=
  match tokens with
  | .punctuation ['#'] :: .identifier ['i', 'f', 'n', 'd', 'e', 'f'] :: .identifier guard ::
      .punctuation ['#'] :: .identifier ['d', 'e', 'f', 'i', 'n', 'e'] :: .identifier defined :: rest =>
      if guard = defined then do
        let items ← headerItems? (2 * tokens.length + 4) rest
        some ⟨guard, items⟩
      else none
  | _ => none

def headerText? (characters : List Char) : Option CHeader := do
  let tokens ← (lex characters).toOption
  completeHeader? tokens

/-- Array aliases are checked through their actual typedefs; all other names
come from the source interface or the fixed scalar/context ABI. -/
structure Representation where
  moduleName : String
  interface : Interface
  arrayAliases : List (NativeType × Name)
  deriving Repr

def recordName (moduleName name : String) : Name :=
  ("CettaGslt_" ++ cIdentifier moduleName ++ "_" ++ cIdentifier name ++ "V1").toList

def sourceType? (representation : Representation) : NativeType → Option CType
  | .unit => some ⟨"void".toList, 0⟩
  | .word => some ⟨"uint64_t".toList, 0⟩
  | .byte => some ⟨"uint8_t".toList, 0⟩
  | .bool => some ⟨"bool".toList, 0⟩
  | .named name =>
      if (lookupRecord representation.interface name).isSome then
        some ⟨recordName representation.moduleName name, 0⟩
      else do
        let opaqueDecl ← representation.interface.opaques.find? (fun opaqueDecl => opaqueDecl.name == name)
        some ⟨opaqueDecl.cType.toList, 0⟩
  | .ref element => do
      let inner ← sourceType? representation element
      some { inner with pointers := inner.pointers + 1 }
  | .array .byte => some ⟨"CettaGsltNativeOpsBytesV1".toList, 0⟩
  | .array element => do
      let (_, name) ← representation.arrayAliases.find? (fun entry => entry.1 == element)
      some ⟨name, 0⟩

def sourceFields? (representation : Representation) (fields : List Parameter) : Option (List CParameter) :=
  fields.mapM fun field => do
    let type ← sourceType? representation field.type
    some ⟨type, (cIdentifier field.name).toList⟩

def sourceParameters? (representation : Representation) (parameters : List Parameter) :
    Option (List CParameter) := parameters.mapM fun parameter => do
  let type ← sourceType? representation parameter.type
  some ⟨type, ("local_" ++ cIdentifier parameter.name).toList⟩

def sourcePrototype? (representation : Representation) (header : Header)
    (symbol : Name) (internal : Bool) : Option HeaderItem := do
  let result ← sourceType? representation header.result
  let parameters ← sourceParameters? representation header.parameters
  let parameters := if internal then
    ⟨⟨"CettaGsltNativeOpsContextV1".toList, 1⟩, "ctx".toList⟩ :: parameters else parameters
  some (.prototype result symbol parameters)

def declaredLayouts? (representation : Representation) : Option (List HeaderItem) := do
  let forwards := representation.interface.records.map fun record =>
    HeaderItem.forward (recordName representation.moduleName record.name)
      (recordName representation.moduleName record.name)
  let arrays ← representation.arrayAliases.mapM fun (element, name) => do
    let type ← sourceType? representation element
    some (HeaderItem.array name [⟨{type with pointers := type.pointers + 1}, "data".toList⟩,
      ⟨⟨"uint64_t".toList, 0⟩, "length".toList⟩])
  let records ← representation.interface.records.mapM fun record => do
    let fields ← sourceFields? representation record.fields
    some (HeaderItem.record (recordName representation.moduleName record.name) fields)
  let externals ← representation.interface.externals.mapM fun declaration =>
    sourcePrototype? representation declaration.header declaration.cSymbol.toList false
  let functions ← representation.interface.functions.mapM fun header =>
    sourcePrototype? representation header
      (functionSymbol representation.moduleName header.name).toList true
  some (forwards ++ arrays ++ records ++ externals ++ functions)

def declarations (header : CHeader) : List HeaderItem := header.items.filter fun item =>
  match item with | .include _ => false | _ => true

def includes (header : CHeader) : List Name := header.items.filterMap fun item =>
  match item with | .include name => some name | _ => none

def permittedIncludes (representation : Representation) : List Name :=
  "gslt_native_ops_v1.h".toList ::
    (representation.interface.opaques.map fun opaqueDecl => opaqueDecl.includeHeader.toList) ++
    (representation.interface.externals.filterMap fun external => external.includeHeader.map String.toList)

def headerAgrees (representation : Representation) (header : CHeader) : Bool :=
  (representation.arrayAliases.map Prod.fst).eraseDups.length == representation.arrayAliases.length &&
  (representation.arrayAliases.map Prod.snd).eraseDups.length == representation.arrayAliases.length &&
  !representation.arrayAliases.any (fun entry => entry.1 == .byte) &&
  match declaredLayouts? representation with
  | none => false
  | some expected => declarations header == expected &&
      (includes header).all (fun name => (permittedIncludes representation).contains name) &&
      (permittedIncludes representation).all (fun name => (includes header).contains name)

/-- The body parser can use only these separately checked type names. -/
def representationTypeNames (representation : Representation) : TypeNames :=
  ["void".toList, "uint64_t".toList, "uint8_t".toList, "bool".toList,
    "CettaGsltNativeOpsContextV1".toList, "CettaGsltNativeOpsBytesV1".toList] ++
  representation.interface.records.map (fun record => recordName representation.moduleName record.name) ++
  representation.interface.opaques.map (fun opaqueDecl => opaqueDecl.cType.toList) ++
  representation.arrayAliases.map Prod.snd

private def smallHeader :=
  "#ifndef H\n#define H\n#include \"gslt_native_ops_v1.h\"\ntypedef struct Pair Pair;\nstruct Pair { uint64_t first; bool second; };\nuint64_t f(uint64_t local_x);\n#endif\n".toList

theorem complete_header_layout_retained : headerText? smallHeader = some
    ⟨['H'], [.include "gslt_native_ops_v1.h".toList, .forward "Pair".toList "Pair".toList,
      .record "Pair".toList [⟨⟨"uint64_t".toList, 0⟩, "first".toList⟩,
        ⟨⟨"bool".toList, 0⟩, "second".toList⟩],
      .prototype ⟨"uint64_t".toList, 0⟩ ['f'] [⟨⟨"uint64_t".toList, 0⟩, "local_x".toList⟩]]⟩ := by cbv

theorem different_include_guard_refused :
    headerText? "#ifndef A\n#define B\n#endif".toList = none := by cbv

theorem unaccounted_macro_refused :
    headerText? "#ifndef H\n#define H\n#define EXTRA 1\n#endif".toList = none := by cbv

theorem content_after_header_refused :
    headerText? "#ifndef H\n#define H\n#endif extra".toList = none := by cbv

theorem altered_array_layout_refused_by_representation :
    headerAgrees ⟨"Empty", ⟨[], [], [], []⟩, [(.word, "Words".toList)]⟩
      ⟨['H'], [.include "gslt_native_ops_v1.h".toList,
        .array "Words".toList [⟨⟨"uint64_t".toList, 1⟩, "data".toList⟩,
          ⟨⟨"uint8_t".toList, 0⟩, "length".toList⟩]]⟩ = false := by cbv

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
