/-
# GFCore.Atom — Semantic propositions (PLN-compatible)

Atoms represent judgments/propositions about Terms.
Maps to PLN link types:
  isa     → InheritanceLink
  rel     → EvaluationLink (1-arg = attribution, n-arg = relation)
  causes  → PredictiveImplicationLink
  implies → ImplicationLink

Attr(X, P) is Rel(P, [X]) — same PLN EvaluationLink, unified representation.
Council (de Paiva): "Two representations for one concept is a liability."

Council: Martin-Löf (judgments), Goertzel/Geisweiller (PLN mapping),
         de Paiva (Attr/Rel unification)
-/

import GFCore.Term

namespace GFCore

/-- Comparison relation for comparative constructions. -/
inductive CmpRel where
  | more | less | equal
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A semantic proposition, PLN-compatible.
    Operates on structured `Term` arguments.
    Note: Attr(X, P) is represented as Rel(P, [X]). Use `Atom.attr` smart
    constructor and `Atom.isAttr?` recognizer for the 1-arg pattern. -/
inductive Atom where
  | isa     (sub sup : Term)                              -- InheritanceLink
  | rel     (pred : GroundedLexeme) (args : List Term)    -- EvaluationLink (n-arg)
  | compare (cmp : CmpRel) (prop : GroundedLexeme)
            (x y : Term)                                  -- Comparative
  | causes  (cause effect : Atom)                         -- PredictiveImplicationLink
  | implies (ante cons : Atom)                            -- ImplicationLink
  | conj    (xs : List Atom)
  | neg     (x : Atom)
  | forAll  (var : String) (body : Atom)
  | opaque  (description : String)
  deriving Repr, Inhabited

namespace Atom

/-- Smart constructor: Attr(entity, prop) is Rel(prop, [entity]). -/
def attr (entity : Term) (prop : GroundedLexeme) : Atom :=
  .rel prop [entity]

/-- Detect 1-arg Rel (the "attribute" pattern). -/
def isAttr? : Atom → Option (Term × GroundedLexeme)
  | .rel pred [arg] => some (arg, pred)
  | _ => none

/-- Pretty-print an Atom. 1-arg Rel displays as Attr for readability. -/
partial def pretty : Atom → String
  | .isa sub sup => s!"IsA({sub.pretty}, {sup.pretty})"
  | .rel pred args => match args with
    | [single] => s!"Attr({single.pretty}, {pred.baseName})"
    | _ =>
      let argStr := args.map Term.pretty
      s!"Rel({pred.baseName}, {String.intercalate ", " argStr})"
  | .compare cmp prop x y =>
    let c := match cmp with | .more => ">" | .less => "<" | .equal => "="
    s!"Compare({x.pretty} {c} {y.pretty} on {prop.baseName})"
  | .causes c e => s!"Causes({pretty c}, {pretty e})"
  | .implies a c => s!"Implies({pretty a}, {pretty c})"
  | .conj xs => s!"And({String.intercalate ", " (xs.map pretty)})"
  | .neg x => s!"Not({pretty x})"
  | .forAll v b => s!"ForAll({v}, {pretty b})"
  | .opaque d => s!"Opaque({d})"

/-- Is this atom a non-opaque proposition? -/
def isSubstantive : Atom → Bool
  | .opaque _ => false
  | _ => true

/-- Get all terms mentioned in an atom. -/
partial def allTerms : Atom → List Term
  | .isa sub sup => [sub, sup]
  | .rel _ args => args
  | .compare _ _ x y => [x, y]
  | .causes c e => allTerms c ++ allTerms e
  | .implies a c => allTerms a ++ allTerms c
  | .conj xs => xs.flatMap allTerms
  | .neg x => allTerms x
  | .forAll _ b => allTerms b
  | .opaque _ => []

/-- Get all predicate lexemes from an atom. -/
partial def allPreds : Atom → List GroundedLexeme
  | .rel pred _ => [pred]
  | .compare _ prop _ _ => [prop]
  | .causes c e => allPreds c ++ allPreds e
  | .implies a c => allPreds a ++ allPreds c
  | .conj xs => xs.flatMap allPreds
  | .neg x => allPreds x
  | .forAll _ b => allPreds b
  | _ => []

/-- Get all head lexemes from an atom (predicates + term heads). -/
def allHeads (a : Atom) : List GroundedLexeme :=
  a.allPreds ++ (a.allTerms).filterMap Term.head?

end Atom

end GFCore
