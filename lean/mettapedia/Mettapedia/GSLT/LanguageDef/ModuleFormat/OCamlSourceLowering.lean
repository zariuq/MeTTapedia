import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourcePacketView
import Mettapedia.GSLT.LanguageDef.ModuleFormat.GoldCoreSyntax
import Mettapedia.Languages.OCaml.ExpressionTree
import Mettapedia.Languages.OCaml.Scope
import Mettapedia.Languages.OCaml.NamedPattern
import Mettapedia.Data.Except.CheckedMap

/-! A selected OCaml source packet lowers to a concrete expression tree.
Assembly and the final arena formation check are separate stages. Source
names and declarations remain frontend data; runtime instructions contain
environment indices and constructor identifiers. Grammar readback, selection,
binding lowering and execution retain separate correspondence boundaries.
-/

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering

open Mettapedia.Languages.OCaml
open SourcePacket
open SourcePacketView (requireSome)

abbrev Lower := Except String

structure Context where
  names : List String := []
  constructors : List (String × Constructor) := []
  types : Nat := 0

private def description : Lower Portable.SyntaxDescription :=
  requireSome "OCaml syntax description is unavailable" GoldCoreSyntax.OCaml.description?

private def text (sort : String) (source : Packet) : Lower String :=
  SourcePacketView.text description sort source

private def keepField : Mettapedia.OSLF.MeTTaIL.Syntax.TermParam → Bool
    | .simple _ (.base "SrcTrivia") | .simple _ (.base "SrcSpacing") => false
    | _ => true

private def view (source : Packet) : Lower (String × List Packet) :=
  SourcePacketView.view description keepField source

private def sequence (single more leading empty : String) : Nat → Packet → Lower (List Packet)
  | 0, _ => .error "source sequence exceeds its packet size"
  | fuel + 1, source => do
      let (label, fields) ← view source
      match fields with
      | [] => if label == empty then pure [] else .error s!"unexpected empty {label}"
      | [first] =>
          if label == single then pure [first]
          else if label == leading then sequence single more leading empty fuel first
          else .error s!"unexpected sequence {label}"
      | [first, rest] =>
          if label == more then (first :: ·) <$> sequence single more leading empty fuel rest
          else .error s!"unexpected sequence {label}"
      | _ => .error s!"malformed sequence {label}"

def constructorAlternatives (context : Context) (name : String) : List Constructor :=
  context.constructors.filterMap fun (declared, constructor) =>
    if declared == name then some constructor else none

/-- An untyped source occurrence cannot resolve overloaded constructors.
The typed constructor-resolution boundary must supply that choice. -/
def resolveConstructorName (context : Context) (name : String) : Lower Constructor :=
  match constructorAlternatives context name with
  | [] => .error s!"unbound constructor {name}"
  | [constructor] => .ok constructor
  | _ => .error s!"ambiguous constructor {name}: multiple declarations require typed resolution"

theorem resolveConstructorName_ok (context : Context) (name : String) (constructor : Constructor) :
    resolveConstructorName context name = .ok constructor ↔ constructorAlternatives context name = [constructor] := by
  unfold resolveConstructorName
  cases candidates : constructorAlternatives context name with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second tail => simp

private def resolveConstructor (context : Context) (source : Packet) : Lower Constructor := do
  resolveConstructorName context (← text "SrcUpperName" source)

private def distinct (names : List String) : Bool := names.eraseDups.length == names.length

def namedPatternFuel : Nat → Context → Packet → Lower NamedPattern
  | 0, _, _ => .error "pattern exceeds its packet size"
  | fuel + 1, context, source => do
      let (label, fields) ← view source
      let lower := namedPatternFuel fuel context
      let finish := fun pattern =>
        if distinct pattern.names then pure pattern else .error "repeated variable in pattern"
      match label, fields with
      | "ocaml-src:pattern-base", [child] | "ocaml-src:pattern-atom", [child] => lower child
      | "ocaml-src:pattern-variable", [name] =>
          pure (.variable (← text "SrcLowerName" name))
      | "ocaml-src:pattern-wildcard", [] => pure .wildcard
      | "ocaml-src:pattern-integer", [number] =>
          let spelling ← text "SrcInteger" number
          let value ← requireSome "invalid integer pattern" spelling.toInt?
          pure (.literal (.integer value))
      | "ocaml-src:pattern-true", [] => pure (.literal (.boolean true))
      | "ocaml-src:pattern-false", [] => pure (.literal (.boolean false))
      | "ocaml-src:pattern-empty-list", [] => pure (.literal .nil)
      | "ocaml-src:pattern-cons", [head, tail] =>
          finish (.cons (← lower head) (← lower tail))
      | "ocaml-src:pattern-parenthesized", [items] =>
          let items ← sequence "ocaml-src:pattern-tuple-one" "ocaml-src:pattern-tuple-more" "" "" fuel items
          let items ← items.mapM lower
          match items with
          | [item] => pure item
          | _ => finish (.tuple items)
      | "ocaml-src:pattern-constructor-zero", [name] =>
          let constructor ← resolveConstructor context name
          unless constructor.arity == 0 do .error "constructor pattern needs fields"
          pure (.variant constructor.typeId constructor.ordinal [])
      | "ocaml-src:pattern-constructor", [name, argument]
      | "ocaml-src:pattern-constructor-parenthesized", [name, argument] =>
          let constructor ← resolveConstructor context name
          let arguments ← if label == "ocaml-src:pattern-constructor-parenthesized" then
              sequence "ocaml-src:pattern-tuple-one" "ocaml-src:pattern-tuple-more" "" "" fuel argument
            else pure [argument]
          let arguments ← arguments.mapM lower
          let patterns := if constructor.arity == 1 && arguments.length > 1 then
              [NamedPattern.tuple arguments]
            else if constructor.arity > 1 then
              match arguments with
              | [NamedPattern.tuple fields] => fields
              | fields => fields
            else arguments
          unless patterns.length == constructor.arity do .error "wrong constructor pattern arity"
          finish (.variant constructor.typeId constructor.ordinal patterns)
      | _, _ => .error s!"unsupported pattern {label}"

/-- Erasure and source names are projections of one named pattern. -/
def patternFuel (fuel : Nat) (context : Context) (source : Packet) : Lower (MatchPattern × List String) :=
  (namedPatternFuel fuel context source).map fun pattern => (pattern.erase, pattern.names)

def extendNames (context : Context) (names : List String) : Context :=
  { context with names := names.reverse ++ context.names }

def resolveName? (context : Context) (name : String) : Option Nat := context.names.idxOf? name

private def primitive? : String → Option Primitive
  | "ocaml-src:OcAdd-op0" => some .add
  | "ocaml-src:OcAdd-op1" => some .subtract
  | "ocaml-src:OcMultiply-op0" => some .multiply
  | "ocaml-src:OcMultiply-op1" => some .divide
  | "ocaml-src:OcMultiply-op2" => some .modulo
  | "ocaml-src:OcCompare-op0" => some .equal
  | "ocaml-src:OcCompare-op1" => some .different
  | "ocaml-src:OcCompare-op2" => some .less
  | "ocaml-src:OcCompare-op3" => some .lessEqual
  | "ocaml-src:OcCompare-op4" => some .greater
  | "ocaml-src:OcCompare-op5" => some .greaterEqual
  | _ => none

private def unwrap : Nat → Packet → Lower Packet
  | 0, _ => .error "expression wrapper exceeds its packet size"
  | fuel + 1, source => do
      let (label, fields) ← view source
      match label, fields with
      | "ocaml-src:expr-value", [child] | "ocaml-src:OcOr-base", [child]
      | "ocaml-src:OcAnd-base", [child] | "ocaml-src:OcCompare-base", [child]
      | "ocaml-src:OcCons-base", [child] | "ocaml-src:OcAdd-base", [child]
      | "ocaml-src:OcMultiply-base", [child] | "ocaml-src:unary-base", [child]
      | "ocaml-src:apply-base", [child] | "ocaml-src:parenthesized", [child] => unwrap fuel child
      | _, _ => pure source

private def recFlag (source : Packet) : Lower Bool := do
  match ← view source with
  | ("ocaml-src:rec-none", []) => pure false
  | ("ocaml-src:rec-some", []) => pure true
  | _ => .error "malformed recursion flag"

structure BindingGroup where
  context : Context
  wrap : ExpressionTree → ExpressionTree

mutual
  private def expression : Nat → Context → Packet → Lower ExpressionTree
    | 0, _, _ => .error "expression exceeds its packet size"
    | fuel + 1, context, source => do
        let source ← unwrap fuel source
        let (label, fields) ← view source
        let lower := expression fuel context
        match label, fields with
        | "ocaml-src:integer", [number] =>
            let value ← requireSome "invalid integer" (← text "SrcDigits" number).toInt?
            pure (ExpressionTree.integer value)
        | "ocaml-src:true", [] => pure (ExpressionTree.boolean true)
        | "ocaml-src:false", [] => pure (ExpressionTree.boolean false)
        | "ocaml-src:unit", [] => pure ExpressionTree.unit
        | "ocaml-src:name", [name] =>
            let name ← text "SrcLowerName" name
            match resolveName? context name with
            | some index => pure (ExpressionTree.variableRef index)
            | none =>
                if name == "not" then
                  pure (ExpressionTree.lambda .bind (ExpressionTree.primitive .notBool [ExpressionTree.variableRef 0]))
                else .error s!"unbound variable {name}"
        | "ocaml-src:constructor", [name] =>
            let constructor ← resolveConstructor context name
            unless constructor.arity == 0 do .error "constructor expression needs fields"
            pure (ExpressionTree.variant constructor.typeId constructor.ordinal [])
        | "ocaml-src:tuple", [first, rest] =>
            let rest ← sequence "ocaml-src:tuple-one" "ocaml-src:tuple-more" "" "" fuel rest
            pure (ExpressionTree.tuple (← (first :: rest).mapM lower))
        | "ocaml-src:list", [items] =>
            let items ← sequence "ocaml-src:list-one" "ocaml-src:list-more" "" "ocaml-src:list-empty" fuel items
            pure ((← items.mapM lower).foldr ExpressionTree.cons ExpressionTree.nil)
        | "ocaml-src:apply", [function, argument]
        | "ocaml-src:apply-parenthesized", [function, argument] =>
            let function ← unwrap fuel function
            match ← view function with
            | ("ocaml-src:constructor", [name]) =>
                let constructor ← resolveConstructor context name
                let argument ← unwrap fuel argument
                let arguments ← if constructor.arity == 1 then pure [argument] else do
                    match ← view argument with
                    | ("ocaml-src:tuple", [first, rest]) =>
                        pure (first :: (← sequence "ocaml-src:tuple-one" "ocaml-src:tuple-more" "" "" fuel rest))
                    | _ => .error "multi-field constructor expects a tuple"
                unless arguments.length == constructor.arity do .error "wrong constructor expression arity"
                pure (ExpressionTree.variant constructor.typeId constructor.ordinal (← arguments.mapM lower))
            | _ => pure (ExpressionTree.apply (← lower function) (← lower argument))
        | "ocaml-src:if", [condition, yes, no] =>
            pure (ExpressionTree.branch (← lower condition) (← lower yes) (← lower no))
        | "ocaml-src:fun", [parameters, body] =>
            let parameters ← sequence "ocaml-src:parameters-one" "ocaml-src:parameters-more" "" "" fuel parameters
            lambdas fuel context parameters body
        | "ocaml-src:let-in", [recursive, bindings, body] =>
            let group ← bindingGroup fuel context (← recFlag recursive) bindings
            pure (group.wrap (← expression fuel group.context body))
        | "ocaml-src:match", [scrutinee, clauses] =>
            let clauses ← sequence "ocaml-src:clauses-one" "ocaml-src:clauses-more"
              "ocaml-src:clauses-leading-bar" "" fuel clauses
            let clauses ← clauses.mapM fun clause => do
              let ("ocaml-src:clause", [pattern, body]) ← view clause
                | .error "malformed match clause"
              let (pattern, names) ← patternFuel fuel context pattern
              pure (pattern, ← expression fuel (extendNames context names) body)
            pure (ExpressionTree.matchValue (← lower scrutinee) clauses)
        | "ocaml-src:unary-minus", [argument] =>
            let argument ← unwrap fuel argument
            match ← view argument with
            | ("ocaml-src:integer", [number]) =>
                let magnitude ← requireSome "invalid integer" (← text "SrcDigits" number).toInt?
                pure (ExpressionTree.integer (-magnitude))
            | _ => pure (ExpressionTree.primitive .negate [← lower argument])
        | "ocaml-src:OcOr-op0", [left, right] => pure (ExpressionTree.orElse (← lower left) (← lower right))
        | "ocaml-src:OcAnd-op0", [left, right] => pure (ExpressionTree.andThen (← lower left) (← lower right))
        | "ocaml-src:OcCons-op0", [head, tail] => pure (ExpressionTree.cons (← lower head) (← lower tail))
        | operator, [left, right] =>
            let primitive ← requireSome s!"unsupported binary expression {operator}" (primitive? operator)
            pure (ExpressionTree.primitive primitive [← lower left, ← lower right])
        | _, _ => .error s!"unsupported expression {label}"

  private def lambdas : Nat → Context → List Packet → Packet → Lower ExpressionTree
    | 0, _, _, _ => .error "parameters exceed their packet size"
    | fuel + 1, context, parameters, body => do
        match parameters with
        | [] => expression fuel context body
        | first :: rest =>
            let (parameter, names) ← patternFuel fuel context first
            pure (ExpressionTree.lambda parameter (← lambdas fuel (extendNames context names) rest body))

  private def binding : Nat → Context → Packet → Lower (MatchPattern × List String × ExpressionTree)
    | 0, _, _ => .error "binding exceeds its packet size"
    | fuel + 1, context, source => do
        match ← view source with
        | ("ocaml-src:binding-value", [pattern, value]) =>
            let (pattern, names) ← patternFuel fuel context pattern
            pure (pattern, names, ← expression fuel context value)
        | ("ocaml-src:binding-function", [name, parameters, body]) =>
            let name ← text "SrcLowerName" name
            let parameters ← sequence "ocaml-src:parameters-one" "ocaml-src:parameters-more" "" "" fuel parameters
            pure (.bind, [name], ← lambdas fuel context parameters body)
        | (label, _) => .error s!"unsupported binding {label}"

  private def bindingGroup : Nat → Context → Bool → Packet → Lower BindingGroup
    | 0, _, _, _ => .error "binding group exceeds its packet size"
    | fuel + 1, context, recursive, source => do
        let sources ← sequence "ocaml-src:bindings-one" "ocaml-src:bindings-more" "" "" fuel source
        if recursive then
          let names ← sources.mapM fun source => do
            match ← view source with
            | ("ocaml-src:binding-function", [name, _, _]) => text "SrcLowerName" name
            | ("ocaml-src:binding-value", [pattern, _]) =>
                match ← view pattern with
                | ("ocaml-src:pattern-base", [pattern]) =>
                    match ← view pattern with
                    | ("ocaml-src:pattern-atom", [pattern]) =>
                        match ← view pattern with
                        | ("ocaml-src:pattern-variable", [name]) => text "SrcLowerName" name
                        | _ => .error "recursive binding needs a variable"
                    | _ => .error "recursive binding needs a variable"
                | _ => .error "recursive binding needs a variable"
            | _ => .error "malformed recursive binding"
          unless distinct names do .error "repeated name in recursive group"
          let inner := extendNames context names
          let definitions ← sources.mapM (binding fuel inner)
          unless definitions.all (fun entry => match entry.2.2 with
            | .lambda _ _ => true
            | _ => false) do
            .error "recursive bindings require function definitions"
          pure ⟨inner, ExpressionTree.letRecursive (definitions.map (·.2.2))⟩
        else
          let definitions ← sources.mapM (binding fuel context)
          let names := definitions.flatMap (·.2.1)
          unless distinct names do .error "repeated name in simultaneous binding group"
          let wrap := match definitions with
            | [(pattern, _, value)] => ExpressionTree.letValue pattern value
            | _ => ExpressionTree.letValue (.tuple (definitions.map (·.1)))
                (ExpressionTree.tuple (definitions.map (·.2.2)))
          pure ⟨extendNames context names, wrap⟩
end

private def typeArity : Nat → Packet → Lower Nat
  | 0, _ => .error "constructor type exceeds its packet size"
  | fuel + 1, source => do
      match ← view source with
      | ("ocaml-src:type-product", [left, right]) =>
          pure ((← typeArity fuel left) + (← typeArity fuel right))
      | _ => pure 1

private def declareType (fuel : Nat) (context : Context) (variants : Packet) : Lower Context := do
  let variants ← sequence "ocaml-src:variant-one" "ocaml-src:variant-more"
    "ocaml-src:variant-leading-bar" "" fuel variants
  let declarations ← variants.mapIdxM fun ordinal source => do
    match ← view source with
    | ("ocaml-src:variant-constant", [name]) =>
        pure (← text "SrcUpperName" name, Constructor.mk context.types ordinal 0)
    | ("ocaml-src:variant-fields", [name, fields]) =>
        pure (← text "SrcUpperName" name, Constructor.mk context.types ordinal (← typeArity fuel fields))
    | _ => .error "malformed variant declaration"
  unless distinct (declarations.map (·.1)) do .error "repeated constructor in type declaration"
  pure {context with types := context.types + 1, constructors := declarations ++ context.constructors}

private def file : Nat → Context → Packet → Lower (ExpressionTree × Context)
  | 0, _, _ => .error "source file exceeds its packet size"
  | fuel + 1, context, source => do
      match ← view source with
      | ("ocaml-src:file-empty", []) => pure (ExpressionTree.unit, context)
      | ("ocaml-src:file-result", [result]) | ("ocaml-src:file-result-terminated", [result]) =>
          pure (← expression fuel context result, context)
      | ("ocaml-src:file-top", [top, rest]) | ("ocaml-src:file-top-terminated", [top, rest]) =>
          match ← view top with
          | ("ocaml-src:top-type", [_, _, variants]) => file fuel (← declareType fuel context variants) rest
          | ("ocaml-src:top-let", [recursive, bindings]) =>
              let group ← bindingGroup fuel context (← recFlag recursive) bindings
              let (body, final) ← file fuel group.context rest
              pure (group.wrap body, final)
          | _ => .error "unsupported top-level declaration"
      | (label, _) => .error s!"unsupported source file {label}"

/-- The caller supplies one explicitly retained tree. No parse is chosen here;
the assembled arena's formation check is performed by `lower`. -/
@[irreducible] def lowerTree (input : String) (source : Packet) : Lower TreeProgram := do
  let grammar ← description
  unless validates grammar.grammar grammar.profile "SourceProgram" input source do
    .error "source packet readback differs from the complete original input"
  let ("ocaml-src:program", [body]) ← view source | .error "expected an OCaml program"
  let (expression, context) ← file (packetNodes source + 1) {} body
  pure ⟨context.constructors.map (·.2), expression⟩

def lower (input : String) (source : Packet) : Lower Program :=
  Except.checkedMap (lowerTree input source) TreeProgram.assemble (fun program => program.checkScope)
    "lowered program fails the independent IR formation check"

end Mettapedia.GSLT.LanguageDef.ModuleFormat.OCamlSourceLowering
