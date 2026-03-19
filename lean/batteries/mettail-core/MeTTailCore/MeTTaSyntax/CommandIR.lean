import MeTTailCore.MeTTaIL.Syntax

namespace MeTTailCore.MeTTaSyntax

open MeTTailCore.MeTTaIL.Syntax

/-- Normalized syntax command IR shared across parser frontends. -/
inductive SyntaxCommand where
  /-- Empty / comment line no-op. -/
  | empty : SyntaxCommand
  /-- `! expr` -/
  | eval : Pattern → SyntaxCommand
  /-- Top-level fact insertion (non-`!` atom form). -/
  | fact : Pattern → SyntaxCommand
  /-- `(= lhs rhs)` -/
  | defineEq : Pattern → Pattern → SyntaxCommand
  /-- `(rule! lhs rhs premise1 ...)` — explicit premise-bearing rule definition. -/
  | defineRule : Pattern → Pattern → List Pattern → SyntaxCommand
  /-- `(: atom ty)` -/
  | defineType : Pattern → Pattern → SyntaxCommand
  /-- `(relation! rel a b ...)` fact insertion into relation env. -/
  | relationFact : String → List Pattern → SyntaxCommand
  /-- `(builtin! rel a b ...)` fact insertion into builtin relation env. -/
  | builtinFact : String → List Pattern → SyntaxCommand
  /-- `(set-fuel n)` or equivalent runtime tuning command. -/
  | setFuel : Nat → SyntaxCommand
  /-- `(import! path)` or `(import! space path)` — canonical import command.
      First arg = target space, second arg = import path/module. -/
  | import : Pattern → Pattern → SyntaxCommand
  /-- `(new-space! name)` style command. -/
  | newSpace : String → SyntaxCommand
  /-- `(add-atom! space atom)` style command. -/
  | addAtom : Pattern → Pattern → SyntaxCommand
  /-- `(remove-atom! space atom)` style command. -/
  | removeAtom : Pattern → Pattern → SyntaxCommand
  /-- Fallback escape hatch for dialect-specific directives. -/
  | directive : String → List Pattern → SyntaxCommand
deriving Repr, DecidableEq, BEq

end MeTTailCore.MeTTaSyntax
