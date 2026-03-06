import MeTTailCore

namespace Algorithms.MeTTa.Simple.Semantics.TranslatorOps

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.Match

structure Interface (σ : Type) where
  rewrites : σ → List RewriteRule
  applyBindings : Bindings → Pattern → Pattern
  matchPattern : Pattern → Pattern → List Bindings

def headOfTranslatorArg? : Pattern → Option String
  | .apply head [] =>
      let h := head.trimAscii.toString
      if h.isEmpty then none else some h
  | .fvar v =>
      let h := v.trimAscii.toString
      if h.isEmpty then none else some h
  | _ => none

def addHead (heads : List String) (arg : Pattern) : List String :=
  match headOfTranslatorArg? arg with
  | none => heads
  | some h =>
      if heads.contains h then heads else h :: heads

def removeHead (heads : List String) (arg : Pattern) : List String :=
  match headOfTranslatorArg? arg with
  | none => heads
  | some h => heads.filter (fun x => x != h)

def hasHead (heads : List String) (head : String) : Bool :=
  heads.contains head

private partial def renameFVarsWith (tag : String) : Pattern → Pattern
  | .fvar x => .fvar (tag ++ x)
  | .bvar n => .bvar n
  | .apply ctor args =>
      let ctor' :=
        if ctor.startsWith "$" then
          let name := (ctor.drop 1).toString
          if name.isEmpty then ctor else "$" ++ tag ++ name
        else
          ctor
      .apply ctor' (args.map (renameFVarsWith tag))
  | .lambda body => .lambda (renameFVarsWith tag body)
  | .multiLambda n body => .multiLambda n (renameFVarsWith tag body)
  | .subst body repl => .subst (renameFVarsWith tag body) (renameFVarsWith tag repl)
  | .collection ct elems rest => .collection ct (elems.map (renameFVarsWith tag)) rest

private def unwrapQuote : Pattern → Pattern
  | .apply "quote" [q] => q
  | p => p

def translateCall (I : Interface σ) (s : σ) (enabledHeads : List String)
    (term : Pattern) : List Pattern :=
  match term with
  | .apply head _ =>
      if !hasHead enabledHeads head then
        []
      else
        (I.rewrites s).flatMap fun rule =>
          if rule.premises.isEmpty then
            let tag := s!"__tr::{rule.name}::"
            let leftFresh := renameFVarsWith tag rule.left
            let rightFresh := renameFVarsWith tag rule.right
            match leftFresh with
            | .apply lHead _ =>
                if lHead == head then
                  (I.matchPattern leftFresh term).map
                    (fun (bs : Bindings) => unwrapQuote (I.applyBindings bs rightFresh))
                else
                  []
            | _ => []
          else
            []
  | _ => []

end Algorithms.MeTTa.Simple.Semantics.TranslatorOps
