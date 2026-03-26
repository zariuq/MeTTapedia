/-
# GFCore.Term — Structured semantic terms

Terms represent entities and events with modifier structure.
Modifiers can contain Terms (e.g., prepPhrase), making this
a mutually recursive definition.
-/

import GFCore.Syntax
import GFCore.Frame  -- for GroundedLexeme

namespace GFCore

/-- Semantic role labels for event arguments. -/
inductive Role where
  | agent | patient | theme | instrument | location | cause | goal | unspecified
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Typed modifier on an entity term.
    Uses GroundedLexeme for PP objects (not full Term) to avoid mutual recursion. -/
inductive Modifier where
  | adj     (a : GroundedLexeme)                      -- "bright star"
  | nounMod (n : GroundedLexeme)                      -- CompoundAP: "element in" as modifier
  | prep    (p : GroundedLexeme) (obj : GroundedLexeme) -- "in stars" → prep=in, obj=star
  | appos   (head : GroundedLexeme)                   -- apposition: "sun" in ApposCN
  | superl  (a : GroundedLexeme)                      -- superlative: "most common"
  | opaqueMod (raw : String)                          -- fallback
  deriving Repr, DecidableEq, BEq, Inhabited

/-- A structured semantic term.
    Entities have head + typed modifiers.
    Events have predicate + role-labeled arguments. -/
inductive Term where
  | entity  (head : GroundedLexeme) (det : Option DetKind)
            (number : Option NumKind) (mods : List Modifier)
  | event   (pred : GroundedLexeme) (args : List (Role × Term))
  | var     (name : String)
  | opaque  (description : String)
  deriving Repr, Inhabited

namespace Term

def simple (lex : GroundedLexeme) : Term :=
  .entity lex none none []

def mk (gfFun cat : String) : Term :=
  .entity { gfFun := gfFun, cat := cat } none none []

def head? : Term → Option GroundedLexeme
  | .entity h _ _ _ => some h
  | .event p _ => some p
  | _ => none

def addMod (t : Term) (m : Modifier) : Term :=
  match t with
  | .entity h d n mods => .entity h d n (mods ++ [m])
  | other => other

partial def pretty : Term → String
  | .entity h det num mods =>
    let detStr := match det with
      | some .definite => "the " | some .indefinite => "a "
      | some .mass => "" | some (.possessive o) => s!"{o}'s " | none => ""
    let numStr := match num with
      | some .plural => "(pl)" | _ => ""
    let modStr := if mods.isEmpty then "" else
      "[" ++ String.intercalate ", " (mods.map prettyMod) ++ "]"
    s!"{detStr}{h.baseName}{numStr}{modStr}"
  | .event p args =>
    let argStr := args.map fun (r, t) =>
      let rs := match r with
        | .agent => "ag" | .patient => "pt" | .theme => "th"
        | .instrument => "inst" | .location => "loc"
        | .cause => "cause" | .goal => "goal" | .unspecified => "_"
      s!"{rs}:{pretty t}"
    s!"{p.baseName}({String.intercalate ", " argStr})"
  | .var n => s!"?{n}"
  | .opaque d => s!"<{d}>"
where
  prettyMod : Modifier → String
    | .adj a => a.baseName
    | .nounMod n => s!"nmod:{n.baseName}"
    | .prep p obj => s!"{p.baseName}({obj.baseName})"
    | .appos h => s!"={h.baseName}"
    | .superl a => s!"most({a.baseName})"
    | .opaqueMod r => s!"?{r}"

def sameHead (a b : Term) : Bool :=
  match a.head?, b.head? with
  | some ha, some hb => ha.baseName == hb.baseName
  | _, _ => false

/-- Get all lexemes from modifiers. -/
def modLexemes : Modifier → List GroundedLexeme
  | .adj a => [a]
  | .nounMod n => [n]
  | .prep p obj => [p, obj]
  | .appos h => [h]
  | .superl a => [a]
  | .opaqueMod _ => []

/-- Get all head lexemes recursively (including from modifiers). -/
partial def allHeads : Term → List GroundedLexeme
  | .entity h _ _ mods => h :: mods.flatMap modLexemes
  | .event p args => p :: args.flatMap (fun (_, t) => allHeads t)
  | _ => []

/-- Find PP modifier objects (the nouns that PPs point to). -/
def ppObjects : Term → List GroundedLexeme
  | .entity _ _ _ mods => mods.filterMap fun
    | .prep _ obj => some obj
    | _ => none
  | _ => []

end Term

end GFCore
