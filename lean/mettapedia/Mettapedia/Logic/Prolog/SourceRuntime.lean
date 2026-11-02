import Mettapedia.Logic.Prolog.SourceSignature
import Mettapedia.Logic.Prolog.ReaderNumber
import Mettapedia.Logic.Prolog.RuntimeControl
import Mettapedia.Logic.Prolog.RuntimeClauseDecode
import Mettapedia.Logic.Prolog.ClauseReflection
import Mettapedia.Logic.Prolog.SourceTermOrder

/-!
# Concrete callable decoding for Prolog source terms

This module gives the concrete source signature a read-only realization of
`call/N`.  It is not a resolver or a second dispatch loop: `RuntimeQuery`
invokes this decoder from its single phase transition and installs the
predicate-like cut boundary.  The decoder only interprets an existing heap
graph as typed `RuntimeGoal` instructions.

The callable spine follows SWI-Prolog V10.1.9 `i_metacall_common` in
`src/pl-vmi.c`: an atom supplies a predicate name, a compound supplies its
functor and existing arguments, and `call/N` appends the extra arguments.
With no extra arguments, the standard control functors are decoded back into
the same typed control constructors produced by the source reader.
-/

namespace Mettapedia.Logic.Prolog.SourceRuntime

open Mettapedia.Logic
open LP.RuntimeTerm LP.RuntimeMaterialize
open SourceSignature RuntimeControl

abbrev Sigma := SourceSignature.signature
abbrev State := RuntimeControl.State Sigma
abbrev Session := RuntimeControl.Session Sigma

/-- SWI-Prolog's ISO instantiation-error term for `throw/1`, including the
predicate context reported by version 10.1.9. -/
def throwInstantiationErrorTerm : SourceSignature.Term :=
  compound "error" [
    atom "instantiation_error",
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "throw", integer 1]],
      var "_" 0
    ]
  ]

/-- Language-owned packet content for an unbound throw root.  `RuntimeQuery`
detects that root and owns every raise, match, unwind, and recovery
transition. -/
def throwInstantiationError : LP.RuntimeException.Packet Sigma := {
  term := LP.Term.atScope 0 throwInstantiationErrorTerm
}

@[simp]
theorem throwInstantiationError_term :
    throwInstantiationError.term =
      LP.Term.atScope 0 throwInstantiationErrorTerm := rfl

/-- SWI-Prolog's exception term for reading a missing non-backtrackable
global, normalized to the precise predicate context emitted by V10.1.9. -/
def undefinedGlobalErrorTerm (name : SourceSignature.Constant) :
    SourceSignature.Term :=
  compound "error" [
    compound "existence_error" [atom "variable", .const name],
    compound "context" [
      compound ":" [atom "system", compound "/" [atom "nb_getval", integer 2]],
      var "_" 0
    ]
  ]

/-- Language-owned immutable packet content for an absent `nb_getval/2`
name. The shared runtime owns the raise and every subsequent control step. -/
def undefinedGlobalError (name : SourceSignature.Constant) :
    LP.RuntimeException.Packet Sigma := {
  term := LP.Term.atScope 0 (undefinedGlobalErrorTerm name)
}

@[simp]
theorem undefinedGlobalError_term (name : SourceSignature.Constant) :
    (undefinedGlobalError name).term =
      LP.Term.atScope 0 (undefinedGlobalErrorTerm name) := rfl

/-- Concrete Prolog list symbols used by the shared collector. -/
def collectionEncoding : LP.RuntimeQuery.CollectionEncoding Sigma where
  nil := .nil
  cons := { name := "[|]", arity := 2 }
  cons_arity_two := rfl

/-- Source atoms name compound functors for `=../2`.  The arity is supplied
by the list length on construction and remains explicit in the canonical
`CompoundIndicator`; non-atom constants cannot name applications. -/
def univEncoding : LP.RuntimeQuery.UnivEncoding Sigma where
  list := collectionEncoding
  functorConstant symbol := .atom symbol.name
  functionOf constant arity :=
    match constant with
    | .atom name => some ⟨{ name, arity }, rfl⟩
    | _ => none

/-- Deterministic source identities for fresh arguments created by
`functor/3`.  The shared engine adds the persistent activation scope. -/
def functorVariable (index : Nat) : SourceSignature.Variable := {
  spelling := "_Functor"
  occurrence := index
}

theorem functorVariable_injective : Function.Injective functorVariable := by
  intro left right equal
  have := congrArg SourceSignature.Variable.occurrence equal
  simpa [functorVariable] using this

/-- Deterministic source identities for unbound result cells introduced by a
finite `maplist/3` expansion.  The shared engine supplies the enclosing
activation scope, so these names cannot collide with a source clause or a
different maplist activation. -/
def maplistVariable (index : Nat) : SourceSignature.Variable := {
  spelling := "_Maplist"
  occurrence := index
}

theorem maplistVariable_injective : Function.Injective maplistVariable := by
  intro left right equal
  have := congrArg SourceSignature.Variable.occurrence equal
  simpa [maplistVariable] using this

/-- Concrete list symbols and fresh source-variable identities for the
engine-owned result-spine construction in finite `maplist/3`. -/
def maplistEncoding : LP.RuntimeQuery.MaplistEncoding Sigma where
  list := collectionEncoding
  freshVariable := maplistVariable
  freshVariable_injective := maplistVariable_injective

/-- Concrete atom/arity representation for the shared `functor/3` action. -/
def functorEncoding : LP.RuntimeQuery.FunctorEncoding Sigma where
  nameConstant symbol := .atom symbol.name
  functionOf constant arity :=
    match constant with
    | .atom name => some ⟨{ name, arity }, rfl⟩
    | _ => none
  arityConstant arity := .integer (Int.ofNat arity)
  arityOf constant :=
    match constant with
    | .integer value => if value < 0 then none else some value.toNat
    | _ => none
  freshVariable := functorVariable
  freshVariable_injective := functorVariable_injective

/-- Concrete `$VAR/1` representation used by ISO `numbervars/3,4`.  The
shared runtime owns occurrence traversal, numbering order, allocation, and
unification; this value supplies only source-language symbols. -/
def numberVariablesEncoding : LP.RuntimeQuery.NumberVariablesEncoding Sigma where
  numberedSymbol := { name := "$VAR", arity := 1 }
  numberedArity := rfl
  indexConstant index := .integer (Int.ofNat index)
  singletonConstant := .atom "_"

/-- Concrete primitive-token encoding for pinned SWI's `term_hash/2`.
Clause references are opaque runtime capabilities rather than source terms and
therefore remain deliberately unhashable in this fragment.  Integers outside
pinned SWI's inline tagged range also fail closed: their indirect GMP-byte
encoding is intentionally outside this partial conformance claim. -/
def termHashEncoding : LP.RuntimeTermHash.Encoding Sigma where
  primitive
    | .nil => some (.atom "[]")
    | .atom name => some (.atom name)
    | .integer value =>
        if value < (-72057594037927936 : Int) ∨
            value > (72057594037927935 : Int) then none
        else some (.integer value)
    | .floatBits bits => some (.floatBits bits)
    | .string value => some (.string value)
    | .clauseReference _ => none
  functorName symbol := symbol.name
  resultConstant hash := .integer (Int.ofNat hash.toNat)

private def integerOperation (symbol : CompoundIndicator) :
    Option LP.RuntimeQuery.IntegerOperation :=
  if symbol.arity = 2 then
    match symbol.name with
    | "+" => some .add
    | "-" => some .subtract
    | "*" => some .multiply
    | "mod" => some .modulo
    | _ => none
  else none

/-- The exact unbounded-integer fragment currently realized from source
constants.  Float and transcendental arithmetic are separate obligations. -/
def integerArithmeticEncoding :
    LP.RuntimeQuery.IntegerArithmeticEncoding Sigma where
  decodeInteger
    | .integer value => some value
    | _ => none
  encodeInteger := .integer
  decode_encode _ := rfl
  operation := integerOperation

/-- Source list and unbounded-integer symbols for the shared `length/2`
transition. -/
def listLengthEncoding : LP.RuntimeQuery.ListLengthEncoding Sigma where
  list := collectionEncoding
  integer := integerArithmeticEncoding

/-- Concrete `Name/Arity` syntax for program reflection. -/
def predicateIndicatorEncoding :
    LP.RuntimeQuery.PredicateIndicatorEncoding Sigma where
  indicator := { name := "/", arity := 2 }
  indicator_arity_two := rfl
  relationOf name arity :=
    match name, arity with
    | .atom spelling, .integer value =>
        if value >= 0 then some { name := spelling, arity := value.toNat }
        else none
    | _, _ => none

/-- Canonical source symbols used by the shared engine to normalize and
inspect dynamic facts/rules and to expose opaque stable references. -/
def clauseEncoding : LP.RuntimeQuery.ClauseEncoding Sigma where
  trueConstant := .atom "true"
  rule := { name := ":-", arity := 2 }
  rule_arity_two := rfl
  referenceConstant := SourceSignature.Constant.clauseReference

/-- The exact function-symbol to relation-symbol bridge used by ordinary
callable compounds.  Extra `call/N` arguments extend, rather than replace,
the compound's existing arity. -/
def predicateOfCompound (symbol : CompoundIndicator) (extraArity : Nat) :
    PredicateIndicator := {
  name := symbol.name
  arity := symbol.arity + extraArity
}

@[simp]
theorem predicateOfCompound_arity (symbol : CompoundIndicator)
    (extraArity : Nat) :
    (predicateOfCompound symbol extraArity).arity =
      symbol.arity + extraArity := rfl

private def ordinaryCall (name : String) (arguments : List Addr) :
    RuntimeGoal Sigma.scoped :=
  .call {
    symbol := { name, arity := arguments.length }
    args := arguments.toArray
  }

private def compoundCall (symbol : CompoundIndicator)
    (arguments extraArgs : List Addr) : RuntimeGoal Sigma.scoped :=
  .call {
    symbol := predicateOfCompound symbol extraArgs.length
    args := (arguments ++ extraArgs).toArray
  }

/-- Dereference one callable root without exposing trail/checkpoint authority
to the decoder. -/
private def dereferencedCell (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError (Cell Sigma.scoped) :=
  match heap.deref address with
  | .error error => .error (.memory error)
  | .ok (.variableCycle cycle) =>
      .error (.memory (.variableReferenceCycle cycle))
  | .ok (.root root) =>
      match heap[root]? with
      | none => .error (.memory (.invalidAddress root))
      | some cell => .ok cell

/-- Bounded decoding of one finite callable graph.  Rational cycles are not
silently unfolded; exhausting the heap-sized bound fails closed until the
runtime exception channel can expose the corresponding ISO error term. -/
def decodeCallableAux : Nat → Heap Sigma.scoped → Addr → List Addr →
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped))
  | 0, _, _, _ => .error .unsupportedInstruction
  | fuel + 1, heap, address, extraArgs => do
      let cell ← dereferencedCell heap address
      match cell with
      | .var _ none => .error .unsupportedInstruction
      | .var _ (some _) => .error .unsupportedInstruction
      | .const (.atom name) =>
          if extraArgs.isEmpty then
            match name with
            | "true" => pure []
            | "fail" => pure [.fail]
            | "!" => pure [.cut]
            | _ => pure [ordinaryCall name []]
          else
            pure [ordinaryCall name extraArgs]
      | .const _ => .error .unsupportedInstruction
      | .app symbol arguments =>
          let arguments := arguments.toList
          if arguments.length != symbol.arity then
            .error (.memory .illFormedHeap)
          else if !extraArgs.isEmpty then
            pure [compoundCall symbol arguments extraArgs]
          else
            match symbol.name, arguments with
            | ",", [left, right] => do
                let decodedLeft ← decodeCallableAux fuel heap left []
                let decodedRight ← decodeCallableAux fuel heap right []
                pure (decodedLeft ++ decodedRight)
            | ";", [choice, elseBranch] => do
                let choiceCell ← dereferencedCell heap choice
                match choiceCell with
                | .app choiceSymbol choiceArguments =>
                    match choiceSymbol.name, choiceArguments.toList with
                    | "->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.ifThenElse decodedCondition decodedThen decodedElse]
                    | "*->", [condition, thenBranch] => do
                        let decodedCondition ←
                          decodeCallableAux fuel heap condition []
                        let decodedThen ←
                          decodeCallableAux fuel heap thenBranch []
                        let decodedElse ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.softIfThenElse decodedCondition decodedThen
                          decodedElse]
                    | _, _ => do
                        let decodedLeft ← decodeCallableAux fuel heap choice []
                        let decodedRight ←
                          decodeCallableAux fuel heap elseBranch []
                        pure [.disj decodedLeft decodedRight]
                | _ => do
                    let decodedLeft ← decodeCallableAux fuel heap choice []
                    let decodedRight ← decodeCallableAux fuel heap elseBranch []
                    pure [.disj decodedLeft decodedRight]
            | "->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.ifThenElse decodedCondition decodedThen [.fail]]
            | "*->", [condition, thenBranch] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedThen ← decodeCallableAux fuel heap thenBranch []
                pure [.softIfThenElse decodedCondition decodedThen [.fail]]
            | "once", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.once decoded]
            | "transaction", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.transaction decoded]
            /- Keep heap-built `call(memberchk(E,L))` on the same typed
            expansion as source `memberchk/2`.  Decoding is read-only; the
            shared engine runs the loaded `member/2` clauses and owns the
            once checkpoint.  This is the finite proper-list law only. -/
            | "memberchk", [element, list] =>
                pure [.once [ordinaryCall "member" [element, list]]]
            | "\\+", [goal] => do
                let decoded ← decodeCallableAux fuel heap goal []
                pure [.neg decoded]
            | "=", [left, right] => pure [.unify left right]
            | "\\=", [left, right] => pure [.notUnify left right]
            | "var", [term] => pure [.isVar term]
            | "nonvar", [term] => pure [.neg [.isVar term]]
            | "forall", [condition, action] => do
                let decodedCondition ← decodeCallableAux fuel heap condition []
                let decodedAction ← decodeCallableAux fuel heap action []
                pure [.neg (decodedCondition ++ [.neg decodedAction])]
            | "findall", [template, generator, bag] => do
                let decodedGenerator ← decodeCallableAux fuel heap generator []
                pure [.findall template decodedGenerator bag]
            | "catch", [guarded, catcher, recovery] => do
                let decodedGuarded ← decodeCallableAux fuel heap guarded []
                let decodedRecovery ← decodeCallableAux fuel heap recovery []
                pure [.catch decodedGuarded catcher decodedRecovery]
            | "throw", [ball] => pure [.throw ball]
            | _, _ => pure [compoundCall symbol arguments []]

/-- Decode one callable at the current heap high-water. -/
def decodeCallable (heap : Heap Sigma.scoped) (address : Addr)
    (extraArgs : List Addr) :
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped)) :=
  decodeCallableAux (heap.size + 1) heap address extraArgs

/-- Expand the finite proper-list `maplist/2` fragment into ordinary `call/2`
instructions.  Each element remains a distinct dynamic call, so each receives
the shared engine's usual predicate-like cut boundary.  The decoder reads only
the live heap; it cannot execute a closure or select its clauses. -/
private def decodeMaplist (heap : Heap Sigma.scoped) (closure list : Addr) :
    Except LP.RuntimeQuery.QueryError (List (RuntimeGoal Sigma.scoped)) := do
  let elements ← LP.RuntimeQuery.decodeAddressList collectionEncoding heap list
  pure <| elements.map fun element => ordinaryCall "call" [closure, element]

/-- Read a `maplist/3` output root without allocating or binding it.  Only a
wholly unbound root requests a new result spine; a partial spine remains a
visible unsupported open-list case instead of being silently treated as
complete.  SWI-Prolog can extend such a partial spine; that relational
generation is deliberately outside this finite native fragment. -/
private def decodeMaplistOutput (heap : Heap Sigma.scoped) (output : Addr) :
    Except LP.RuntimeQuery.QueryError (Option (List Addr)) :=
  match LP.RuntimeQuery.decodeAddressList collectionEncoding heap output with
  | .ok elements => .ok (some elements)
  | .error .univListUnbound =>
      match LP.RuntimeQuery.dereferencedRootCell heap output with
      | .ok (_, .var _ none) => .ok none
      | .ok _ => .error .univListUnbound
      | .error error => .error error
  | .error error => .error error

/-- Decode finite `maplist/3` without allocating.  The returned plan contains
only input roots and ordinary `call/3` instructions; the shared engine owns
the optional fresh output spine and its one canonical output unification. -/
private def decodeMaplist3 (heap : Heap Sigma.scoped)
    (closure input output : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.MetaCallPlan Sigma (RuntimeGoal Sigma.scoped)) := do
  let inputs ← LP.RuntimeQuery.decodeAddressList collectionEncoding heap input
  let knownOutputs ← decodeMaplistOutput heap output
  match knownOutputs with
  | some outputs =>
      if inputs.length = outputs.length then
        pure (.maplist3 maplistEncoding output inputs knownOutputs
          fun resultElements =>
            (List.zip inputs resultElements).map fun (input, result) =>
              ordinaryCall "call" [closure, input, result])
      else pure .fail
  | none =>
      pure (.maplist3 maplistEncoding output inputs none
        fun resultElements =>
          (List.zip inputs resultElements).map fun (input, result) =>
            ordinaryCall "call" [closure, input, result])

/-- Decode one dynamic-call request after the shared engine has selected it.
`maplist/2` is intentionally finite and proper-list only at this boundary;
unbound-list enumeration remains a visible unsupported extension. -/
def decodeMetaCall (heap : Heap Sigma.scoped) : LP.RuntimeQuery.MetaCallRequest →
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.MetaCallPlan Sigma (RuntimeGoal Sigma.scoped))
  | .call callable extraArgs => .goals <$> decodeCallable heap callable extraArgs
  | .maplist closure list => .goals <$> decodeMaplist heap closure list
  | .maplist3 closure input output => decodeMaplist3 heap closure input output

/-- Recognize `call/N` and the finite `maplist/2` entry without inspecting the
heap.  The classifier exposes only existing roots; the shared engine invokes
the read-only decoder afterwards. -/
def metaCall? (goal : RuntimeAtom Sigma.scoped) :
    Option LP.RuntimeQuery.MetaCallRequest :=
  match goal.symbol.name, goal.args.toList with
  | "call", callable :: extraArgs =>
      if goal.symbol.arity = extraArgs.length + 1 then
        some (.call callable extraArgs)
      else none
  | "maplist", [closure, list] | "apply:maplist", [closure, list] =>
      if goal.symbol.arity = 2 then some (.maplist closure list) else none
  | "maplist", [closure, input, output] |
      "apply:maplist", [closure, input, output] =>
      if goal.symbol.arity = 3 then some (.maplist3 closure input output) else none
  | _, _ => none

/-- Recognize the ISO `phrase/3` entry without inspecting its arguments.
`phrase/2` is elaborated to this form by the source goal classifier. -/
def dcgCall? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Addr) :=
  match goal.symbol.name, goal.args.toList with
  | "phrase", [body, input, rest] =>
      if goal.symbol.arity = 3 then some (body, input, rest) else none
  | _, _ => none

/-- Recognize `format/2` and `format/3`; the classifier exposes only existing
roots and does not read the destination, format text, or argument list. -/
def format? (goal : RuntimeAtom Sigma.scoped) : Option LP.RuntimeQuery.FormatRequest :=
  match goal.symbol.name, goal.args.toList with
  | "format", [format, arguments] =>
      if goal.symbol.arity = 2 then .some (.output format arguments)
      else none
  | "format", [destination, format, arguments] =>
      if goal.symbol.arity = 3 then .some (.codes destination format arguments)
      else none
  | _, _ => none

/-- SWI's `phrase_input/1` accepts an unbound variable, `[]`, or any outer
list cell.  It deliberately does not traverse the tail at this boundary. -/
private def checkPhraseState (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError Unit := do
  let cell ← dereferencedCell heap address
  match cell with
  | .var _ none => pure ()
  | .const value =>
      if value = collectionEncoding.nil then pure ()
      else .error .invalidDcgState
  | .app symbol arguments =>
      if symbol = collectionEncoding.cons && arguments.size = 2 then pure ()
      else .error .invalidDcgState
  | .var _ (some _) => .error (.memory .illFormedHeap)

private def stringCodeConstants (value : String) :
    List SourceSignature.Constant :=
  value.toList.map fun character =>
    .integer (Int.ofNat character.toNat)

private def formatText (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError String := do
  let cell ← dereferencedCell heap address
  match cell with
  | .const (.atom value) | .const (.string value) => pure value
  | .var _ none => .error .invalidFormatString
  | _ => .error .invalidFormatString

/-- The first source-execution fragment needs SWI's default `~w` rendering of
one atom, integer, or string.  Compound and floating-point writing and the
other format directives remain typed unsupported cases rather than being
approximated. -/
private def renderWriteAtomic (heap : Heap Sigma.scoped) (address : Addr) :
    Except LP.RuntimeQuery.QueryError String := do
  let cell ← dereferencedCell heap address
  match cell with
  | .const (.atom value) => pure value
  | .const (.integer value) => pure (toString value)
  /- PeTTa's `swrite/2` produces a Prolog string and SWI's `~w` writes its
  payload without the source-level string quotes. -/
  | .const (.string value) => pure value
  | .var _ none => .error .invalidFormatArguments
  | _ => .error .unsupportedFormatDirective

/-- Render the deliberately small, exact `format/2` fragment needed by the
currently supported source path.  It owns no heap mutation: every `~w` reads
one existing atomic root, while `~n` and `~~` consume no argument.  Other
directives remain structured errors rather than guessed output. -/
private def renderFormatAux (heap : Heap Sigma.scoped) :
    List Char → List Addr → Except LP.RuntimeQuery.QueryError (List Char)
  | [], [] => .ok []
  | [], _ => .error .invalidFormatArguments
  | '~' :: 'w' :: formatTail, argument :: argumentTail => do
      let rendered ← renderWriteAtomic heap argument
      let tail ← renderFormatAux heap formatTail argumentTail
      pure (rendered.toList ++ tail)
  | '~' :: 'n' :: formatTail, arguments => do
      let tail ← renderFormatAux heap formatTail arguments
      pure ('\n' :: tail)
  | '~' :: '~' :: formatTail, arguments => do
      let tail ← renderFormatAux heap formatTail arguments
      pure ('~' :: tail)
  | '~' :: _, _ => .error .unsupportedFormatDirective
  | character :: formatTail, arguments => do
      let tail ← renderFormatAux heap formatTail arguments
      pure (character :: tail)

private def renderFormat (heap : Heap Sigma.scoped) (format : String)
    (arguments : List Addr) : Except LP.RuntimeQuery.QueryError String := do
  String.ofList <$> renderFormatAux heap format.toList arguments

/-- Decode the two currently supported formatting shapes. `format/3` remains
the pure codes-difference-list fragment used by `dcg/basics:atom//1`; `format/2`
returns one explicit text observation. Allocation, difference-list sharing,
unification, continuation, and event delivery remain engine-owned. -/
def decodeFormat (heap : Heap Sigma.scoped) : LP.RuntimeQuery.FormatRequest →
    Except LP.RuntimeQuery.QueryError (LP.RuntimeQuery.FormatPlan Sigma)
  | .codes destination format arguments => do
      let destinationCell ← dereferencedCell heap destination
      let (head, tail) ←
        match destinationCell with
        | .app symbol roots =>
            match symbol.name, symbol.arity, roots.toList with
            | "codes", 2, [head, tail] => pure (head, tail)
            | _, _, _ => .error .invalidFormatDestination
        | _ => .error .invalidFormatDestination
      let text ← formatText heap format
      if text != "~w" then .error .unsupportedFormatDirective else
      let argumentRoots ←
        LP.RuntimeQuery.decodeAddressList collectionEncoding heap arguments
      let argument ←
        match argumentRoots with
        | [argument] => pure argument
        | _ => .error .invalidFormatArguments
      let rendered ← renderWriteAtomic heap argument
      pure (.codes collectionEncoding head tail (stringCodeConstants rendered))
  | .output format arguments => do
      let text ← formatText heap format
      let argumentRoots ←
        LP.RuntimeQuery.decodeAddressList collectionEncoding heap arguments
      pure (.output (← renderFormat heap text argumentRoots))

private inductive TextConversionKind where
  | atom
  | string

private def TextConversionKind.value? : TextConversionKind →
    SourceSignature.Constant → Option String
  | .atom, .atom value => some value
  | .string, .string value => some value
  | _, _ => none

private def TextConversionKind.constant : TextConversionKind → String →
    SourceSignature.Constant
  | .atom, value => .atom value
  | .string, value => .string value

private def codeCharacter (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError Char := do
  let cell ← dereferencedCell heap root
  match cell with
  | .var _ none => .error .textConversionUnbound
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.integer value) =>
      if value < 0 then .error .invalidCharacterCode else
      let code := value.toNat
      if h : code.isValidChar then .ok (Char.ofNatAux code h)
      else .error .invalidCharacterCode
  | _ => .error .invalidCharacterCode

private def codeCharacters (heap : Heap Sigma.scoped) (roots : List Addr) :
    Except LP.RuntimeQuery.QueryError (List Char) :=
  roots.mapM (codeCharacter heap)

private def decodedCodeRoots (heap : Heap Sigma.scoped) (codes : Addr) :
    Except LP.RuntimeQuery.QueryError (List Addr) :=
  match LP.RuntimeQuery.decodeAddressList collectionEncoding heap codes with
  | .ok roots => .ok roots
  | .error .univListUnbound => .error .textConversionUnbound
  | .error .invalidUnivList => .error .invalidTextCodes
  | .error error => .error error

/-- Decode the two ISO directions without binding either argument.  Ground
text produces code constants after first validating any bound list spine;
unbound text consumes a finite proper list of valid Unicode scalar codes. -/
private def decodeTextConversion (kind : TextConversionKind)
    (heap : Heap Sigma.scoped) (text codes : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.TextConversionPlan Sigma) := do
  let textCell ← dereferencedCell heap text
  match textCell with
  | .var _ none =>
      let roots ← decodedCodeRoots heap codes
      let characters ← codeCharacters heap roots
      pure (.text text (kind.constant (String.ofList characters)))
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const value =>
      let source ← match kind.value? value with
        | some source => pure source
        | none => .error .invalidTextValue
      let codesCell ← dereferencedCell heap codes
      match codesCell with
      | .var _ none =>
          pure (.codes collectionEncoding codes (stringCodeConstants source))
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | _ =>
          let proper ← LP.RuntimeQuery.termProperList collectionEncoding heap codes
          if proper then
            pure (.codes collectionEncoding codes
              (stringCodeConstants source))
          else .error .invalidTextCodes
  | .app _ _ => .error .invalidTextValue

def atomCodesDecoder : LP.RuntimeQuery.TextConversionDecoder Sigma where
  decode := decodeTextConversion .atom

def stringCodesDecoder : LP.RuntimeQuery.TextConversionDecoder Sigma where
  decode := decodeTextConversion .string

private def characterAtom (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError Char := do
  let cell ← dereferencedCell heap root
  match cell with
  | .var _ none => .error .textConversionUnbound
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.atom value) =>
      match value.toList with
      | [character] => pure character
      | _ => .error .invalidTextCodes
  | .const (.integer _) => codeCharacter heap root
  | _ => .error .invalidTextCodes

private def characterAtoms (heap : Heap Sigma.scoped) (roots : List Addr) :
    Except LP.RuntimeQuery.QueryError (List Char) :=
  roots.mapM (characterAtom heap)

private def characterAtomConstants (value : String) :
    List SourceSignature.Constant :=
  value.toList.map fun character => .atom (String.singleton character)

private def decodeCharacterText (heap : Heap Sigma.scoped)
    (characters : Addr) : Except LP.RuntimeQuery.QueryError String := do
  let charactersCell ← dereferencedCell heap characters
  match charactersCell with
  | .const (.string value) => pure value
  | _ =>
      let roots ← decodedCodeRoots heap characters
      let values ← characterAtoms heap roots
      pure (String.ofList values)

/-- Decode pinned SWI's `atom_chars/2` through the same bounded conversion
plan as `atom_codes/2`.  List input accepts one-scalar character atoms and
integer character codes; SWI string input is accepted as a whole text value.
The decoder remains read-only and the shared engine owns list allocation and
unification. -/
private def decodeAtomChars (heap : Heap Sigma.scoped)
    (atom characters : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.TextConversionPlan Sigma) := do
  let atomCell ← dereferencedCell heap atom
  match atomCell with
  | .var _ none =>
      let value ← decodeCharacterText heap characters
      pure (.text atom (.atom value))
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.atom value) =>
      let charactersCell ← dereferencedCell heap characters
      match charactersCell with
      | .var _ none =>
          pure (.codes collectionEncoding characters
            (characterAtomConstants value))
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | _ =>
          match decodeCharacterText heap characters with
          | .ok decoded => pure (.text atom (.atom decoded))
          | .error .textConversionUnbound =>
              let proper ←
                LP.RuntimeQuery.termProperList collectionEncoding heap characters
              if proper then
                pure (.codes collectionEncoding characters
                  (characterAtomConstants value))
              else .error .invalidTextCodes
          | .error error => .error error
  | .const _ | .app _ _ => .error .invalidTextValue

def atomCharsDecoder : LP.RuntimeQuery.TextConversionDecoder Sigma where
  decode := decodeAtomChars

private def sourceTextValue? : SourceSignature.Constant → Option String
  | .atom value | .string value => some value
  | _ => none

/-- Decode the atom/string modes exercised by pinned PeTTa's `sread/2` and
`swrite/2` wrappers.  Either a source atom or string may supply the textual
value; conversion still returns only one bounded constant-unification plan. -/
private def decodeAtomString (heap : Heap Sigma.scoped)
    (atom string : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.TextConversionPlan Sigma) := do
  let stringCell ← dereferencedCell heap string
  match stringCell with
  | .const value =>
      match sourceTextValue? value with
      | some text => pure (.text atom (.atom text))
      | none => .error .invalidTextValue
  | .app _ _ => .error .invalidTextValue
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .var _ none =>
      let atomCell ← dereferencedCell heap atom
      match atomCell with
      | .const value =>
          match sourceTextValue? value with
          | some text => pure (.text string (.string text))
          | none => .error .invalidTextValue
      | .app _ _ => .error .invalidTextValue
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | .var _ none => .error .textConversionUnbound

def atomStringDecoder : LP.RuntimeQuery.TextConversionDecoder Sigma where
  decode := decodeAtomString

private def negateNumberConstant : SourceSignature.Constant →
    Except LP.RuntimeQuery.QueryError SourceSignature.Constant
  | .integer value => pure (.integer (-value))
  | .floatBits bits => pure (.floatBits (bits ^^^ 0x8000000000000000))
  | _ => .error .invalidNumberCodes

/-- Parse the numeric text accepted by the canonical source reader, adding
the unary sign that `ReaderNumber.parse` deliberately leaves to its caller. -/
private def parseNumberText (text : String) :
    Except LP.RuntimeQuery.QueryError SourceSignature.Constant := do
  let (negative, unsigned) :=
    match text.toList with
    | '-' :: rest => (true, String.ofList rest)
    | '+' :: rest => (false, String.ofList rest)
    | _ => (false, text)
  let value ←
    match ReaderNumber.parse unsigned with
    | .ok value => pure value
    | .error (.unsupportedRational _) | .error (.unsupportedNaN _) =>
        .error .unsupportedInstruction
    | .error _ => .error .invalidNumberCodes
  if negative then negateNumberConstant value else pure value

/-- Decode the source-needed `number_codes/2` fragment.  Reverse conversion
accepts the numeric forms already normalized by `ReaderNumber`; forward
conversion is exact for arbitrary-precision integers.  Float rendering stays
typed unsupported until its SWI decimal-roundtrip rule is represented. -/
private def decodeNumberCodes (heap : Heap Sigma.scoped)
    (number codes : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.TextConversionPlan Sigma) := do
  let numberCell ← dereferencedCell heap number
  match numberCell with
  | .var _ none =>
      let roots ←
        match decodedCodeRoots heap codes with
        | .ok roots => pure roots
        | .error .textConversionUnbound => .error .numberConversionUnbound
        | .error .invalidTextCodes => .error .invalidNumberCodes
        | .error error => .error error
      let characters ← codeCharacters heap roots
      let value ← parseNumberText (String.ofList characters)
      pure (.text number value)
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.integer value) =>
      let codesCell ← dereferencedCell heap codes
      match codesCell with
      | .var _ none =>
          pure (.codes collectionEncoding codes
            (stringCodeConstants (toString value)))
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | _ =>
          let proper ← LP.RuntimeQuery.termProperList collectionEncoding heap codes
          if proper then
            pure (.codes collectionEncoding codes
              (stringCodeConstants (toString value)))
          else .error .invalidNumberCodes
  | .const (.floatBits _) => .error .unsupportedInstruction
  | .const _ | .app _ _ => .error .invalidNumberValue

def numberCodesDecoder : LP.RuntimeQuery.TextConversionDecoder Sigma where
  decode := decodeNumberCodes

/-- Recognize the code-list conversions needed by pinned PeTTa source. -/
def textConversion? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.TextConversionDecoder Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "atom_codes", [text, codes] =>
      if goal.symbol.arity = 2 then some (text, codes, atomCodesDecoder)
      else none
  | "string_codes", [text, codes] =>
      if goal.symbol.arity = 2 then some (text, codes, stringCodesDecoder)
      else none
  | "atom_chars", [atom, characters] =>
      if goal.symbol.arity = 2 then some (atom, characters, atomCharsDecoder)
      else none
  | "atom_string", [atom, string] =>
      if goal.symbol.arity = 2 then some (atom, string, atomStringDecoder)
      else none
  | "number_codes", [number, codes] =>
      if goal.symbol.arity = 2 then some (number, codes, numberCodesDecoder)
      else none
  | _, _ => none

/-! `dcg/basics:blanks//0` reaches SWI's `code_type/2` while consuming the
pinned PeTTa parser input.  This first source-needed fragment deliberately
supports only ground ASCII `space` and `digit` tests.  Other valid SWI class
modes, Unicode classification, and generative modes remain explicit
unsupported cases rather than being approximated. -/

private def asciiCharacterCode (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError Nat := do
  let cell ← dereferencedCell heap root
  match cell with
  | .var _ none => .error .characterTypeUnbound
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.integer value) =>
      if value < 0 then .error .invalidCharacterCode
      else
        let code := value.toNat
        if code < 128 then pure code
        else .error .unsupportedInstruction
  | _ => .error .invalidCharacterCode

private def decodeCodeType (heap : Heap Sigma.scoped) (code kindRoot : Addr) :
    Except LP.RuntimeQuery.QueryError Bool := do
  let code ← asciiCharacterCode heap code
  let classCell ← dereferencedCell heap kindRoot
  match classCell with
  | .var _ none => .error .characterTypeUnbound
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const (.atom "space") =>
      pure (code = 32 || (9 ≤ code && code ≤ 13))
  | .const (.atom "digit") =>
      pure (48 ≤ code && code ≤ 57)
  | .const (.atom _) | .app _ _ => .error .unsupportedInstruction
  | .const _ => .error .invalidCharacterType

def codeTypeDecoder : LP.RuntimeQuery.BinaryTestDecoder Sigma where
  decode := decodeCodeType

/-- Recognize `code_type/2` without inspecting its arguments.  Heap reading
and the success/failure transition occur later inside the shared engine. -/
def binaryTest? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.BinaryTestDecoder Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "code_type", [code, kindRoot] =>
      if goal.symbol.arity = 2 then some (code, kindRoot, codeTypeDecoder)
      else none
  | _, _ => none

private inductive SortKind where
  | sort
  | msort
  | keysort
  | sortBy (key order : Addr)

private def sortError : SourceTermOrder.Error → LP.RuntimeQuery.QueryError
  | .memory error => .memory error
  | .comparisonBudgetExhausted => .standardOrderBudgetExhausted
  | .unsupportedClauseReference => .unsupportedSortReference
  | .invalidSortKey => .invalidSortKey

private def sortListError : LP.RuntimeQuery.QueryError →
    LP.RuntimeQuery.QueryError
  | .invalidUnivList | .univListUnbound => .invalidSortList
  | error => error

private def sortKeyIndex (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError Nat := do
  match ← dereferencedCell heap root with
  | .const (.integer value) =>
      if value > 0 then return value.toNat else .error .invalidSortKey
  | _ => .error .invalidSortKey

private def decodeSortKey (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError SourceTermOrder.Key := do
  match ← dereferencedCell heap root with
  | .const (.integer value) =>
      if value = 0 then return .whole
      else if value > 0 then return .positions [value.toNat]
      else .error .invalidSortKey
  | .app symbol _ =>
      if symbol = collectionEncoding.cons then
        match LP.RuntimeQuery.decodeAddressList collectionEncoding heap root with
        | .error error => .error (sortListError error)
        | .ok roots =>
            let indices ← roots.mapM (sortKeyIndex heap)
            if indices.isEmpty then .error .invalidSortKey
            else return .positions indices
      else .error .invalidSortKey
  | _ => .error .invalidSortKey

private def decodeSortOrder (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError
      (SourceTermOrder.Direction × Bool) := do
  match ← dereferencedCell heap root with
  | .const (.atom "<") | .const (.atom "@<") =>
      return (.ascending, true)
  | .const (.atom "=<") | .const (.atom "@=<") =>
      return (.ascending, false)
  | .const (.atom ">") | .const (.atom "@>") =>
      return (.descending, true)
  | .const (.atom ">=") | .const (.atom "@>=") =>
      return (.descending, false)
  | _ => .error .invalidSortOrder

private def decodeSortSpec (heap : Heap Sigma.scoped) : SortKind →
    Except LP.RuntimeQuery.QueryError SourceTermOrder.Spec
  | .sort => .ok {
      key := .whole
      direction := .ascending
      removeDuplicates := true
    }
  | .msort => .ok {
      key := .whole
      direction := .ascending
      removeDuplicates := false
    }
  | .keysort => .ok {
      key := .pair
      direction := .ascending
      removeDuplicates := false
    }
  | .sortBy keyRoot orderRoot => do
      let key ← decodeSortKey heap keyRoot
      let (direction, removeDuplicates) ← decodeSortOrder heap orderRoot
      return { key, direction, removeDuplicates }

/-- Read and order existing roots only.  The result list is not built here;
`RuntimeQuery.sortStep` allocates its spine and invokes the canonical unifier. -/
private def decodeSort (kind : SortKind) (input output : Addr)
    (heap : Heap Sigma.scoped) :
    Except LP.RuntimeQuery.QueryError (LP.RuntimeQuery.SortPlan Sigma) := do
  let addresses ←
    match LP.RuntimeQuery.decodeAddressList collectionEncoding heap input with
    | .ok addresses => .ok addresses
    | .error error => .error (sortListError error)
  let spec ← decodeSortSpec heap kind
  match SourceTermOrder.sortAddresses heap spec addresses with
  | .error error => .error (sortError error)
  | .ok elements => .ok { encoding := collectionEncoding, output, elements }

/-- Recognize the four SWI sorting entry points without inspecting heap
content.  The attached decoder is read-only and carries no scheduling or
answer authority. -/
def sort? (goal : RuntimeAtom Sigma.scoped) :
    Option (LP.RuntimeQuery.SortDecoder Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "sort", [input, output] =>
      if goal.symbol.arity = 2 then
        some { decode := decodeSort .sort input output }
      else none
  | "msort", [input, output] =>
      if goal.symbol.arity = 2 then
        some { decode := decodeSort .msort input output }
      else none
  | "keysort", [input, output] =>
      if goal.symbol.arity = 2 then
        some { decode := decodeSort .keysort input output }
      else none
  | "sort", [key, order, input, output] =>
      if goal.symbol.arity = 4 then
        some { decode := decodeSort (.sortBy key order) input output }
      else none
  | _, _ => none

def termCompareEncoding : LP.RuntimeQuery.TermCompareEncoding Sigma where
  less := .atom "<"
  equal := .atom "="
  greater := .atom ">"

private def termCompareError : SourceTermOrder.Error →
    LP.RuntimeQuery.QueryError
  | .memory error => .memory error
  | .comparisonBudgetExhausted => .standardOrderBudgetExhausted
  | .unsupportedClauseReference => .unsupportedTermOrderReference
  | .invalidSortKey => .invalidSortKey

/-- Validate the result mode before comparing, matching SWI's distinction
between a non-order atom and a non-atom.  The decoder remains read-only and
returns no answer content beyond `Ordering`. -/
private def validateTermCompareResult (heap : Heap Sigma.scoped)
    (result : Addr) : Except LP.RuntimeQuery.QueryError Unit := do
  let (_, cell) ← LP.RuntimeQuery.dereferencedRootCell heap result
  match cell with
  | .var _ none => pure ()
  | .const (.atom "<") | .const (.atom "=") | .const (.atom ">") =>
      pure ()
  | .const (.atom _) => .error .invalidTermCompareOrder
  | _ => .error .invalidTermCompareOrderType

/-- Read the canonical heap through the already-established SWI standard-term
order.  The result is only `Ordering`; allocation and output unification stay
inside the shared engine. -/
def decodeTermCompare (heap : Heap Sigma.scoped) (result left right : Addr) :
    Except LP.RuntimeQuery.QueryError Ordering :=
  match validateTermCompareResult heap result with
  | .error error => .error error
  | .ok () =>
      match SourceTermOrder.compareAt heap left right with
      | .ok order => .ok order
      | .error error => .error (termCompareError error)

def termCompareDecoder : LP.RuntimeQuery.TermCompareDecoder Sigma where
  decode := decodeTermCompare

/-- Recognize ISO `compare/3` without inspecting its heap operands. -/
def termCompare? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Addr × LP.RuntimeQuery.TermCompareDecoder Sigma ×
      LP.RuntimeQuery.TermCompareEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "compare", [result, left, right] =>
      if goal.symbol.arity = 3 then
        some (result, left, right, termCompareDecoder, termCompareEncoding)
      else none
  | _, _ => none

/-- Recognize ISO `length/2`; all heap inspection and binding stay in the
shared engine. -/
def listLength? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.ListLengthEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "length", [listRoot, lengthRoot] =>
      if goal.symbol.arity = 2 then
        some (listRoot, lengthRoot, listLengthEncoding)
      else none
  | _, _ => none

/-- Recognize the one predicate-table reflection entry point.  Groundness is
checked later by `RuntimeQuery.decodePredicateIndicator`. -/
def currentPredicate? (goal : RuntimeAtom Sigma.scoped) : Option Addr :=
  match goal.symbol.name, goal.args.toList with
  | "current_predicate", [indicatorRoot] =>
      if goal.symbol.arity = 1 then some indicatorRoot else none
  | _, _ => none

/-- Read one dynamic grammar body in the finite fragment needed by the pinned
PeTTa parser.  Ordinary nonterminals reuse the callable decoder with the two
state arguments appended.  Proper lists and strings become terminal plans;
cut and braced goals become ordinary typed instructions under the engine's
meta-call boundary.  Compound DCG control remains fail-closed until its fresh
intermediate-state allocation is represented by an engine plan. -/
def decodeDcgAux : Nat → Heap Sigma.scoped → Addr → Addr → Addr →
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.DcgPlan Sigma (RuntimeGoal Sigma.scoped))
  | 0, _, _, _, _ => .error .unsupportedInstruction
  | fuel + 1, heap, body, input, rest => do
      let cell ← dereferencedCell heap body
      match cell with
      | .var _ none => .error .dcgBodyUnbound
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | .const .nil =>
          pure (.addressTerminals collectionEncoding [])
      | .const (.string value) =>
          pure (.constantTerminals collectionEncoding
            (stringCodeConstants value))
      | .const (.atom "!") =>
          pure (.goals [.cut, .unify rest input])
      | .const (.atom "{}") =>
          pure (.goals [.unify input rest])
      | .const (.atom name) =>
          pure (.goals [ordinaryCall name [input, rest]])
      | .const _ => .error .invalidDcgBody
      | .app symbol arguments =>
          let arguments := arguments.toList
          if arguments.length != symbol.arity then
            .error (.memory .illFormedHeap)
          else if symbol = collectionEncoding.cons then
            match LP.RuntimeQuery.decodeAddressList collectionEncoding heap body with
            | .ok heads =>
                pure (.addressTerminals collectionEncoding heads)
            | .error (.memory error) => .error (.memory error)
            | .error _ => .error .invalidDcgBody
          else
            match symbol.name, arguments with
            | "{}", [goal] => do
                let goals ← decodeCallableAux fuel heap goal []
                pure (.goals (goals ++ [.unify rest input]))
            | ",", _ | ";", _ | "|", _ | "->", _ | "*->", _
            | "\\+", _ => .error .unsupportedInstruction
            | _, _ =>
                pure (.goals [compoundCall symbol arguments [input, rest]])

/-- Decode `phrase/3` after enforcing its shallow ISO list contract. -/
def decodeDcg (heap : Heap Sigma.scoped) (body input rest : Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.DcgPlan Sigma (RuntimeGoal Sigma.scoped)) := do
  checkPhraseState heap input
  checkPhraseState heap rest
  decodeDcgAux (heap.size + 1) heap body input rest

private def isAtomConstant : SourceSignature.Constant → Bool
  | .atom _ => true
  | _ => false

private def isNumberConstant : SourceSignature.Constant → Bool
  | .integer _ | .floatBits _ => true
  | _ => false

private def isStringConstant : SourceSignature.Constant → Bool
  | .string _ => true
  | _ => false

/-- Recognize SWI's read-only term-test family without heap authority.  The
classifier supplies only a root and a test descriptor; the shared runtime
performs shallow dereference or recursive graph traversal and owns the
resulting transition. -/
def termTest? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × LP.RuntimeQuery.TermTest Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "atom", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isAtomConstant)
      else none
  | "atomic", [root] =>
      if goal.symbol.arity = 1 then some (root, .isAtomic) else none
  | "compound", [root] =>
      if goal.symbol.arity = 1 then some (root, .isCompound) else none
  | "number", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isNumberConstant)
      else none
  | "string", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .constantWhere isStringConstant)
      else none
  | "ground", [root] =>
      if goal.symbol.arity = 1 then some (root, .isGround) else none
  | "is_list", [root] =>
      if goal.symbol.arity = 1 then
        some (root, .isProperList collectionEncoding)
      else none
  | _, _ => none

/-- Recognize strict identity, variance, and their negations. The source layer
exposes only two roots, a relation tag, and the expected Bool; rational-graph
comparison remains in the shared LP runtime. -/
def termRelation? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.TermRelation × Bool) :=
  match goal.symbol.name, goal.args.toList with
  | "==", [left, right] =>
      if goal.symbol.arity = 2 then
        some (left, right, .identity, true)
      else none
  | "\\==", [left, right] =>
      if goal.symbol.arity = 2 then
        some (left, right, .identity, false)
      else none
  | "=@=", [left, right] =>
      if goal.symbol.arity = 2 then
        some (left, right, .variant, true)
      else none
  | "\\=@=", [left, right] =>
      if goal.symbol.arity = 2 then
        some (left, right, .variant, false)
      else none
  | _, _ => none

/-- Recognize `=../2` without inspecting the heap.  Direction selection and
all graph work occur later inside the shared runtime. -/
def univ? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.UnivEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "=..", [termRoot, listRoot] =>
      if goal.symbol.arity = 2 then
        some (termRoot, listRoot, univEncoding)
      else none
  | _, _ => none

/-- Recognize ISO `copy_term/2`; both arguments remain existing heap roots.
The shared runtime owns finite capture, freshening, materialization, and the
single output-unification attempt. -/
def copyTerm? (goal : RuntimeAtom Sigma.scoped) : Option (Addr × Addr) :=
  match goal.symbol.name, goal.args.toList with
  | "copy_term", [sourceRoot, targetRoot] =>
      if goal.symbol.arity = 2 then some (sourceRoot, targetRoot) else none
  | _, _ => none

def copyTermPredicate : PredicateIndicator := {
  name := "copy_term"
  arity := 2
}

/-- Recognize ISO `term_variables/2`; traversal and list construction stay in
the shared runtime. -/
def termVariables? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.CollectionEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "term_variables", [termRoot, variablesRoot] =>
      if goal.symbol.arity = 2 then
        some (termRoot, variablesRoot, collectionEncoding)
      else none
  | _, _ => none

def termVariablesPredicate : PredicateIndicator := {
  name := "term_variables"
  arity := 2
}

/-- Decode one `singletons(Boolean)` option.  This is deliberately the finite
option fragment used by pinned PeTTa; malformed or additional options fail
closed rather than being ignored. -/
private def decodeNumberVariablesSingletonOption
    (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError Bool := do
  let cell ← dereferencedCell heap root
  match cell with
  | .app symbol arguments =>
      if symbol.name = "singletons" ∧ symbol.arity = 1 ∧ arguments.size = 1 then
        match arguments[0]? with
        | none => .error .invalidNumberVariablesOptions
        | some valueRoot =>
            let value ← dereferencedCell heap valueRoot
            match value with
            | .const (.atom "true") => .ok true
            | .const (.atom "false") => .ok false
            | _ => .error .invalidNumberVariablesOptions
      else .error .invalidNumberVariablesOptions
  | _ => .error .invalidNumberVariablesOptions

/-- Read the nonnegative starting index and the supported singleton option
without acquiring heap mutation or control authority.  Negative starts and
unrecognized options are outside pinned PeTTa's call sites and fail closed;
pinned SWI accepts those cases, so full SWI option conformance is not claimed. -/
def decodeNumberVariables (heap : Heap Sigma.scoped) (startRoot : Addr)
    (optionsRoot : Option Addr) :
    Except LP.RuntimeQuery.QueryError
      (LP.RuntimeQuery.NumberVariablesPlan Sigma) := do
  let startCell ← dereferencedCell heap startRoot
  let start ←
    match startCell with
    | .var _ none => .error .numberVariablesStartUnbound
    | .const (.integer value) =>
        if value < 0 then .error .invalidNumberVariablesStart
        else .ok value.toNat
    | _ => .error .invalidNumberVariablesStart
  let singletons ←
    match optionsRoot with
    | none => .ok false
    | some root =>
        match LP.RuntimeQuery.decodeAddressList collectionEncoding heap root with
        | .error (.memory error) => .error (.memory error)
        | .error _ => .error .invalidNumberVariablesOptions
        | .ok [] => .ok false
        | .ok [optionRoot] =>
            decodeNumberVariablesSingletonOption heap optionRoot
        | .ok _ => .error .invalidNumberVariablesOptions
  pure { encoding := numberVariablesEncoding, start, singletons }

def numberVariablesDecoder : LP.RuntimeQuery.NumberVariablesDecoder Sigma where
  decode := decodeNumberVariables

/-- Recognize the ISO three-argument form and PeTTa's four-argument singleton
form without inspecting the heap. -/
def numberVariables? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Addr × Option Addr ×
      LP.RuntimeQuery.NumberVariablesDecoder Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "numbervars", [termRoot, startRoot, endRoot] =>
      if goal.symbol.arity = 3 then
        some (termRoot, startRoot, endRoot, none, numberVariablesDecoder)
      else none
  | "numbervars", [termRoot, startRoot, endRoot, optionsRoot] =>
      if goal.symbol.arity = 4 then
        some (termRoot, startRoot, endRoot, some optionsRoot,
          numberVariablesDecoder)
      else none
  | _, _ => none

def numberVariablesPredicateThree : PredicateIndicator := {
  name := "numbervars"
  arity := 3
}

def numberVariablesPredicateFour : PredicateIndicator := {
  name := "numbervars"
  arity := 4
}

/-- Recognize `term_hash/2`; the source layer supplies only operand roots and
the primitive encoding, never a hash value or answer. -/
def termHash? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeTermHash.Encoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "term_hash", [termRoot, hashRoot] =>
      if goal.symbol.arity = 2 then
        some (termRoot, hashRoot, termHashEncoding)
      else none
  | _, _ => none

def termHashPredicate : PredicateIndicator := {
  name := "term_hash"
  arity := 2
}

/-- Recognize ISO `functor/3`; mode selection and every heap mutation remain
inside the shared runtime. -/
def functor? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × Addr × LP.RuntimeQuery.FunctorEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "functor", [termRoot, nameRoot, arityRoot] =>
      if goal.symbol.arity = 3 then
        some (termRoot, nameRoot, arityRoot, functorEncoding)
      else none
  | _, _ => none

def functorPredicate : PredicateIndicator := {
  name := "functor"
  arity := 3
}

def nbSetvalPredicate : PredicateIndicator := {
  name := "nb_setval"
  arity := 2
}

def nbGetvalPredicate : PredicateIndicator := {
  name := "nb_getval"
  arity := 2
}

def nbDeletePredicate : PredicateIndicator := {
  name := "nb_delete"
  arity := 1
}

def readTextFilePredicate : PredicateIndicator := {
  name := "read_file_to_string"
  arity := 3
}

def integerIs? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.IntegerArithmeticEncoding Sigma) :=
  match goal.symbol.name, goal.args.toList with
  | "is", [resultRoot, expressionRoot] =>
      if goal.symbol.arity = 2 then
        some (resultRoot, expressionRoot, integerArithmeticEncoding)
      else none
  | _, _ => none

private def integerComparisonOfName : String →
    Option LP.RuntimeQuery.IntegerComparison
  | "<" => some .less
  | "=<" => some .lessEqual
  | ">" => some .greater
  | ">=" => some .greaterEqual
  | "=:=" => some .equal
  | "=\\=" => some .notEqual
  | _ => none

def integerComparison? (goal : RuntimeAtom Sigma.scoped) :
    Option (Addr × Addr × LP.RuntimeQuery.IntegerComparison ×
      LP.RuntimeQuery.IntegerArithmeticEncoding Sigma) :=
  match goal.args.toList with
  | [leftRoot, rightRoot] =>
      if goal.symbol.arity = 2 then
        match integerComparisonOfName goal.symbol.name with
        | some comparison =>
            some (leftRoot, rightRoot, comparison, integerArithmeticEncoding)
        | none => none
      else none
  | _ => none

/-- Recognize the first persistent mutation fragment without heap authority.
Clause decoding and database replacement remain separate engine/session
operations. -/
def databaseRequest? (goal : RuntimeAtom Sigma.scoped) :
    Option LP.RuntimeQuery.DatabaseRequest :=
  match goal.symbol.name, goal.args.toList with
  | "asserta", [clauseRoot] =>
      if goal.symbol.arity = 1 then some (.asserta clauseRoot) else none
  | "asserta", [clauseRoot, referenceRoot] =>
      if goal.symbol.arity = 2 then
        some (.assertaWithReference clauseRoot referenceRoot)
      else none
  | "assertz", [clauseRoot] =>
      if goal.symbol.arity = 1 then some (.assertz clauseRoot) else none
  | "assertz", [clauseRoot, referenceRoot] =>
      if goal.symbol.arity = 2 then
        some (.assertzWithReference clauseRoot referenceRoot)
      else none
  | "retract", [patternRoot] =>
      if goal.symbol.arity = 1 then some (.retract patternRoot) else none
  | "clause", [headRoot, bodyRoot, referenceRoot] =>
      if goal.symbol.arity = 3 then
        some (.clause headRoot bodyRoot referenceRoot)
      else none
  | "nb_setval", [nameRoot, valueRoot] =>
      if goal.symbol.arity = 2 then
        some (.globalSet nameRoot valueRoot)
      else none
  | "nb_getval", [nameRoot, valueRoot] =>
      if goal.symbol.arity = 2 then
        some (.globalGet nameRoot valueRoot)
      else none
  | "nb_delete", [nameRoot] =>
      if goal.symbol.arity = 1 then some (.globalDelete nameRoot) else none
  | _, _ => none

/-- Recognize the host-text predicate only for a realization that explicitly
installs such a capability.  Heap contents remain unavailable here. -/
def textFileRequest? (goal : RuntimeAtom Sigma.scoped) :
    Option LP.RuntimeQuery.DatabaseRequest :=
  match goal.symbol.name, goal.args.toList with
  | "read_file_to_string", [pathRoot, textRoot, optionsRoot] =>
      if goal.symbol.arity = 3 then
        some (.readTextFile pathRoot textRoot optionsRoot)
      else none
  | _, _ => none

def databaseRequestWithTextFiles? (goal : RuntimeAtom Sigma.scoped) :
    Option LP.RuntimeQuery.DatabaseRequest :=
  match textFileRequest? goal with
  | some request => some request
  | none => databaseRequest? goal

/-- A finite or otherwise pure resource table supplied by the host boundary.
The runtime never opens a path itself: the caller reads approved bytes and
installs exactly the mapping it intends this session to observe. -/
abbrev TextFileResources := String → Option String

/-- Decode the successful `read_file_to_string(Path, Text, [])` fragment used
by pinned PeTTa's `filereader.pl`.  Path and option inspection is read-only;
only one atomic string can cross the capability boundary. -/
def decodeTextFile (resources : TextFileResources)
    (heap : Heap Sigma.scoped) (pathRoot optionsRoot : Addr) :
    Except LP.RuntimeQuery.QueryError SourceSignature.Constant := do
  let options ←
    match LP.RuntimeQuery.decodeAddressList collectionEncoding heap optionsRoot with
    | .ok options => .ok options
    | .error (.memory error) => .error (.memory error)
    | .error _ => .error .invalidTextFileOptions
  if !options.isEmpty then
    .error .invalidTextFileOptions
  else
    let cell ← dereferencedCell heap pathRoot
    let path ← match cell with
      | .var _ none => .error .textFilePathUnbound
      | .var _ (some _) => .error (.memory .illFormedHeap)
      | .const (.atom path) => .ok path
      | .const (.string path) => .ok path
      | _ => .error .invalidTextFilePath
    match resources path with
    | some contents => .ok (.string contents)
    | none => .error .textFileUnavailable

/-- Decode exactly an atom name for SWI-style global variables. -/
def decodeGlobalName (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError SourceSignature.Constant := do
  let cell ← dereferencedCell heap root
  match cell with
  | .var _ none => .error .globalVariableNameUnbound
  | .var _ (some _) => .error (.memory .illFormedHeap)
  | .const name@(.atom _) => .ok name
  | _ => .error .invalidGlobalVariableName

/-- Map the precise local decoder boundary into runtime errors.  ISO packet
construction for these errors remains an explicit later conformance step. -/
def decodeClause (heap : Heap Sigma.scoped) (root : Addr) :
    Except LP.RuntimeQuery.QueryError SourceSignature.Clause :=
  match RuntimeClauseDecode.decodeClause heap root with
  | .ok clause => .ok clause
  | .error (.readback error) => .error (.dynamicClauseReadback error)
  | .error (.source _) => .error .invalidDynamicClause
  | .error .notClause => .error .invalidDynamicClause

def services : RuntimeControl.Services Sigma where
  metaCall? := metaCall?
  decoder := { decode := decodeMetaCall, decodeDcg := decodeDcg }
  dcgCall? := dcgCall?
  termTest? := termTest?
  termRelation? := termRelation?
  univ? := univ?
  integerIs? := integerIs?
  integerComparison? := integerComparison?
  format? := format?
  formatter := { decode := decodeFormat }
  textConversion? := textConversion?
  binaryTest? := binaryTest?
  sort? := sort?
  termCompare? := termCompare?
  listLength? := listLength?
  currentPredicate? := currentPredicate?
  predicateIndicatorEncoding := some predicateIndicatorEncoding
  runtimePredicates := [copyTermPredicate, termVariablesPredicate,
    numberVariablesPredicateThree, numberVariablesPredicateFour,
    termHashPredicate, functorPredicate, nbSetvalPredicate, nbGetvalPredicate,
    nbDeletePredicate]
  copyTerm? := copyTerm?
  termVariables? := termVariables?
  numberVariables? := numberVariables?
  termHash? := termHash?
  functor? := functor?
  databaseRequest? := databaseRequest?
  decodeGlobalName := decodeGlobalName
  decodeClause := decodeClause
  reflectClause := ClauseReflection.reflect?
  undefinedGlobalError := fun name => some (undefinedGlobalError name)
  unboundThrowError := some throwInstantiationError
  collectionEncoding := some collectionEncoding
  clauseEncoding := some clauseEncoding

/-- Install an explicit read-only text table without changing any other
language service.  Recognition is enabled together with the decoder and the
predicate becomes discoverable by `current_predicate/1` in the same update. -/
def servicesWithTextFiles (resources : TextFileResources) :
    RuntimeControl.Services Sigma := {
  services with
  runtimePredicates := readTextFilePredicate :: services.runtimePredicates
  databaseRequest? := databaseRequestWithTextFiles?
  textFileDecoder := { decode := decodeTextFile resources }
}

@[simp]
theorem databaseRequestWithTextFiles_readTextFile
    (pathRoot textRoot optionsRoot : Addr) :
    databaseRequestWithTextFiles? {
      symbol := readTextFilePredicate
      args := #[pathRoot, textRoot, optionsRoot]
    } = some (.readTextFile pathRoot textRoot optionsRoot) := rfl

@[simp]
theorem servicesWithTextFiles_decoder (resources : TextFileResources) :
    (servicesWithTextFiles resources).textFileDecoder.decode =
      decodeTextFile resources := rfl

@[simp]
theorem servicesWithTextFiles_runtimePredicates
    (resources : TextFileResources) :
    (servicesWithTextFiles resources).runtimePredicates =
      readTextFilePredicate :: services.runtimePredicates := rfl

@[simp]
theorem services_unboundThrowError :
    services.unboundThrowError = some throwInstantiationError := rfl

@[simp]
theorem services_undefinedGlobalError (name : SourceSignature.Constant) :
    services.undefinedGlobalError name = some (undefinedGlobalError name) := rfl

@[simp]
theorem services_clauseEncoding :
    services.clauseEncoding = some clauseEncoding := rfl

@[simp]
theorem services_collectionEncoding :
    services.collectionEncoding = some collectionEncoding := rfl

@[simp]
theorem services_dcgCall : services.dcgCall? = dcgCall? := rfl

@[simp]
theorem services_copyTerm : services.copyTerm? = copyTerm? := rfl

@[simp]
theorem services_runtimePredicates :
    services.runtimePredicates = [copyTermPredicate, termVariablesPredicate,
      numberVariablesPredicateThree, numberVariablesPredicateFour,
      termHashPredicate, functorPredicate, nbSetvalPredicate, nbGetvalPredicate,
      nbDeletePredicate] := rfl

@[simp]
theorem services_decodeGlobalName :
    services.decodeGlobalName = decodeGlobalName := rfl

@[simp]
theorem dispatchActionWith_nbSetval (program : SourceSignature.Program)
    (nameRoot valueRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := nbSetvalPredicate
      args := #[nameRoot, valueRoot]
    }) = .database (.globalSet nameRoot valueRoot) := by
  rfl

@[simp]
theorem dispatchActionWith_nbGetval (program : SourceSignature.Program)
    (nameRoot valueRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := nbGetvalPredicate
      args := #[nameRoot, valueRoot]
    }) = .database (.globalGet nameRoot valueRoot) := by
  rfl

@[simp]
theorem dispatchActionWith_nbDelete (program : SourceSignature.Program)
    (nameRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := nbDeletePredicate
      args := #[nameRoot]
    }) = .database (.globalDelete nameRoot) := by
  rfl

/-- The concrete source realization exposes `copy_term/2` as exactly the
shared copy action; no source clause, decoder result, or fallback call is
substituted. -/
@[simp]
theorem dispatchActionWith_copyTerm (program : SourceSignature.Program)
    (sourceRoot targetRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := copyTermPredicate
      args := #[sourceRoot, targetRoot]
    }) = .copyTerm sourceRoot targetRoot := by
  rfl

@[simp]
theorem services_termVariables : services.termVariables? = termVariables? := rfl

/-- The concrete source realization exposes `term_variables/2` as exactly the
shared ordered-root traversal action. -/
@[simp]
theorem dispatchActionWith_termVariables (program : SourceSignature.Program)
    (termRoot variablesRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := termVariablesPredicate
      args := #[termRoot, variablesRoot]
    }) = .termVariables termRoot variablesRoot collectionEncoding := by
  rfl

@[simp]
theorem services_numberVariables :
    services.numberVariables? = numberVariables? := rfl

/-- `numbervars/3` exposes exactly one shared-runtime numbering action. -/
@[simp]
theorem dispatchActionWith_numberVariablesThree
    (program : SourceSignature.Program) (termRoot startRoot endRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := numberVariablesPredicateThree
      args := #[termRoot, startRoot, endRoot]
    }) = .numberVariables termRoot startRoot endRoot none
      numberVariablesDecoder := by
  rfl

/-- `numbervars/4` differs only by supplying the existing options root to the
same read-only decoder. -/
@[simp]
theorem dispatchActionWith_numberVariablesFour
    (program : SourceSignature.Program)
    (termRoot startRoot endRoot optionsRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := numberVariablesPredicateFour
      args := #[termRoot, startRoot, endRoot, optionsRoot]
    }) = .numberVariables termRoot startRoot endRoot (some optionsRoot)
      numberVariablesDecoder := by
  rfl

@[simp]
theorem services_termHash : services.termHash? = termHash? := rfl

/-- `term_hash/2` exposes exactly one shared-runtime hashing action. -/
@[simp]
theorem dispatchActionWith_termHash (program : SourceSignature.Program)
    (termRoot hashRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := termHashPredicate
      args := #[termRoot, hashRoot]
    }) = .termHash termRoot hashRoot termHashEncoding := by
  rfl

@[simp]
theorem services_functor : services.functor? = functor? := rfl

/-- The source realization exposes `functor/3` as exactly the shared
construction/decomposition action. -/
@[simp]
theorem dispatchActionWith_functor (program : SourceSignature.Program)
    (termRoot nameRoot arityRoot : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := functorPredicate
      args := #[termRoot, nameRoot, arityRoot]
    }) = .functor termRoot nameRoot arityRoot functorEncoding := by
  rfl

@[simp]
theorem services_format : services.format? = format? := rfl

@[simp]
theorem services_formatter : services.formatter.decode = decodeFormat := rfl

@[simp]
theorem services_textConversion :
    services.textConversion? = textConversion? := rfl

@[simp]
theorem services_binaryTest : services.binaryTest? = binaryTest? := rfl

@[simp]
theorem services_sort : services.sort? = sort? := rfl

@[simp]
theorem services_termCompare : services.termCompare? = termCompare? := rfl

/-- The concrete source realization exposes `compare/3` as exactly one
read-only standard-order decoder followed by the shared engine's result
allocation and graph unification. -/
@[simp]
theorem dispatchActionWith_compare (program : SourceSignature.Program)
    (result left right : Addr) :
    RuntimeControl.dispatchActionWith services program (.call {
      symbol := { name := "compare", arity := 3 }
      args := #[result, left, right]
    }) = .termCompare result left right termCompareDecoder
      termCompareEncoding := by
  rfl

@[simp]
theorem services_listLength : services.listLength? = listLength? := rfl

@[simp]
theorem services_currentPredicate :
    services.currentPredicate? = currentPredicate? := rfl

@[simp]
theorem services_predicateIndicatorEncoding :
    services.predicateIndicatorEncoding = some predicateIndicatorEncoding := rfl

@[simp]
theorem services_decodeMetaCall : services.decoder.decode = decodeMetaCall := rfl

@[simp]
theorem services_decodeDcg : services.decoder.decodeDcg = decodeDcg := rfl

@[simp]
theorem services_termTest :
    services.termTest? = termTest? := rfl

@[simp]
theorem services_termRelation :
    services.termRelation? = termRelation? := rfl

@[simp]
theorem services_univ :
    services.univ? = univ? := rfl

@[simp]
theorem services_integerIs :
    services.integerIs? = integerIs? := rfl

@[simp]
theorem services_integerComparison :
    services.integerComparison? = integerComparison? := rfl

/-- Execute concrete source terms through the one shared runtime with
callable decoding enabled. -/
def step (program : SourceSignature.Program) (state : State) :
    RuntimeControl.StepResult Sigma :=
  RuntimeControl.stepWith services program state

def pull (program : SourceSignature.Program) : Nat → State →
    RuntimeControl.PullResult Sigma :=
  RuntimeControl.pullWith services program

def openSession (memory : Memory Sigma.scoped) (queryScope nextScope : Nat)
    (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionWith services memory queryScope nextScope program goal

def openEmpty (program : SourceSignature.Program) (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  openSession (Memory.empty Sigma.scoped) 0 1 program goal

/-- Open a later query against a database carried out of a completed source
session. -/
def openDatabase
    (database : LP.RuntimeDatabase.Database SourceSignature.Clause)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionDatabaseWith services
    (Memory.empty Sigma.scoped) 0 1 database goal

/-- Open a later top-level source goal over the complete persistent world,
including non-backtrackable global roots and their protected heap graph. -/
def openWorld (world : RuntimeControl.World Sigma)
    (goal : SourceSignature.Goal) :
    Except LP.RuntimeQuery.QueryError Session :=
  RuntimeControl.openSessionWorldWith services world goal

/-- Session resumption delegates to `RuntimeControl.pullSession`; the stored
service selects `pullCoreWithMeta` inside the same canonical phase loop. -/
def pullSession (fuel : Nat) (session : Session) :
    RuntimeControl.SessionPullResult Sigma :=
  RuntimeControl.pullSession fuel session

end Mettapedia.Logic.Prolog.SourceRuntime
