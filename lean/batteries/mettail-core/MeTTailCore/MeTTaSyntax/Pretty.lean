import MeTTailCore.MeTTaIL.Syntax
import MeTTailCore.MeTTaSyntax.CommandIR
import MeTTailCore.MeTTaSyntax.Spec

namespace MeTTailCore.MeTTaSyntax

open MeTTailCore.MeTTaIL.Syntax

def SyntaxSpec.displayCommandHead (s : SyntaxSpec) (head : String) : String :=
  match s.headAliases.find? (fun a => a.canonical == head) with
  | some a => a.alias
  | none => head

private def renderList (xs : List String) : String :=
  String.intercalate " " xs

partial def renderPatternWith (spec : SyntaxSpec) : Pattern → String
  | .bvar n => s!"@{n}"
  | .fvar x => s!"${x}"
  -- Preserve data constructors exactly; command sugar is rendered only at command level.
  | .apply ctor [] => ctor
  | .apply ctor args =>
      let body := renderList (args.map (renderPatternWith spec))
      if body.isEmpty then
        s!"({ctor})"
      else
        s!"({ctor} {body})"
  | .lambda body =>
      s!"(lambda {renderPatternWith spec body})"
  | .multiLambda n body =>
      s!"(multilambda {n} {renderPatternWith spec body})"
  | .subst body repl =>
      s!"(subst {renderPatternWith spec body} {renderPatternWith spec repl})"
  | .collection _ elems _ =>
      s!"(collection {renderList (elems.map (renderPatternWith spec))})"

def renderCommandWith (spec : SyntaxSpec) : SyntaxCommand → String
  | .empty => ""
  | .eval p => s!"{spec.evalPrefix.evalPrefixToken}{renderPatternWith spec p}"
  | .fact p => renderPatternWith spec p
  | .defineEq lhs rhs =>
      let head := spec.displayCommandHead "="
      s!"({head} {renderPatternWith spec lhs} {renderPatternWith spec rhs})"
  | .defineRule lhs rhs premises =>
      let rendered := [renderPatternWith spec lhs, renderPatternWith spec rhs]
        ++ premises.map (renderPatternWith spec)
      s!"(rule! {renderList rendered})"
  | .defineType lhs rhs =>
      let head := spec.displayCommandHead ":"
      s!"({head} {renderPatternWith spec lhs} {renderPatternWith spec rhs})"
  | .relationFact rel args =>
      let body := renderList ((rel :: args.map (renderPatternWith spec)))
      s!"({spec.loweringHeads.relationFactHead} {body})"
  | .builtinFact rel args =>
      let body := renderList ((rel :: args.map (renderPatternWith spec)))
      s!"({spec.loweringHeads.builtinFactHead} {body})"
  | .setFuel n =>
      s!"(set-fuel {n})"
  | .import space path =>
      s!"(import! {renderPatternWith spec space} {renderPatternWith spec path})"
  | .newSpace name =>
      s!"(new-space! {name})"
  | .addAtom space atom =>
      s!"(add-atom! {renderPatternWith spec space} {renderPatternWith spec atom})"
  | .removeAtom space atom =>
      s!"(remove-atom! {renderPatternWith spec space} {renderPatternWith spec atom})"
  | .directive head args =>
      let body := renderList (args.map (renderPatternWith spec))
      if body.isEmpty then
        s!"({head})"
      else
        s!"({head} {body})"

end MeTTailCore.MeTTaSyntax
