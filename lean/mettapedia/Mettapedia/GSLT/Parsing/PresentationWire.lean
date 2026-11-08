import Mettapedia.GSLT.Parsing.PresentationReplay
import Mettapedia.GSLT.Parsing.ParserProfileSemantics
import Lean

/-!
# Presentation data and finite native derivation certificates

The wire carries the existing expression language and lexical-class data.
Native certificates decode to choices only; PresentationReplay checks them
against the original presentation and input before their output is used.
-/

namespace Mettapedia.GSLT.Parsing.PresentationWire

open _root_.Lean
open ParserProfileSemantics

abbrev SourceExpr := LanguageDefSyntaxCompiler.Expr

def expression : SourceExpr → Json
  | .epsilon => Json.arr #[toJson "epsilon"]
  | .char cp => Json.arr #[toJson "char", toJson cp]
  | .class name => Json.arr #[toJson "class", toJson name]
  | .literal values => Json.arr #[toJson "literal", toJson values]
  | .alt left right => Json.arr #[toJson "alt", expression left, expression right]
  | .seq first second => Json.arr #[toJson "seq", expression first, expression second]
  | .left first second => Json.arr #[toJson "left", expression first, expression second]
  | .right first second => Json.arr #[toJson "right", expression first, expression second]
  | .node label body => Json.arr #[toJson "node", toJson label, expression body]
  | .ref name => Json.arr #[toJson "ref", toJson name]
  | .star body => Json.arr #[toJson "star", expression body]
  | .plus body => Json.arr #[toJson "plus", expression body]
  | .eof => Json.arr #[toJson "eof"]

def lexicalClass (declaration : LexicalClassDecl) : Json :=
  match declaration.kind with
  | .points values => Json.mkObj [("name", toJson declaration.name), ("kind", toJson "points"), ("values", toJson values)]
  | .except values => Json.mkObj [("name", toJson declaration.name), ("kind", toJson "except"), ("values", toJson values)]

def encode (presentation : LanguageDefSyntaxCompiler.Presentation) (profile : ParserProfileLayer) (root : String) : Json :=
  Json.mkObj [
    ("root", toJson root),
    ("definitions", Json.arr (presentation.definitions.toArray.map fun definition =>
      Json.mkObj [("name", toJson definition.name), ("body", expression definition.body)])),
    ("classes", Json.arr (profile.classes.toArray.map lexicalClass))]

def certificate : Nat → Json → Except String PresentationReplay.Certificate
  | 0, _ => .error "native certificate nesting bound exhausted"
  | fuel + 1, json => do
      let items ← json.getArr?
      match items.toList with
      | [.str "leaf"] => return .leaf
      | [.str "unary", child] => return .unary (← certificate fuel child)
      | [.str "pair", first, second] => return .pair (← certificate fuel first) (← certificate fuel second)
      | [.str "choice", right, child] => return .choice (← right.getBool?) (← certificate fuel child)
      | [.str "reference", occurrence, child] => return .reference (← occurrence.getNat?) (← certificate fuel child)
      | _ => throw "malformed native certificate"

def classTest (profile : ParserProfileLayer) : PresentationReplay.ClassTest := fun name cp =>
  profile.classAccepts? name cp == some true

end Mettapedia.GSLT.Parsing.PresentationWire
