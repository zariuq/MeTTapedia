/-
# GFCore.Background — Background knowledge from WordNet hypernymy

Loads hypernymy.json (extracted from GF WordNet taxonomy.txt).
Provides background IsA relations that entailment rules can use
without extracting them from parsed text.

Council: Goertzel (PLN background knowledge), Geisweiller (IsA = inheritance),
         de Paiva (ontological grounding)
-/

import Lean.Data.Json
import GFCore.Atom
import GFCore.Grounding

namespace GFCore

open Lean (Json fromJson? FromJson)

/-- Background knowledge store with WordNet hypernym chains. -/
structure Background where
  /-- synsetId → list of ancestor synsetIds (up to depth 5) -/
  chains : Std.HashMap String (Array String)
  /-- synsetId → direct parent synsetIds -/
  direct : Std.HashMap String (Array String)
  deriving Inhabited

namespace Background

/-- Load background knowledge from hypernymy.json. -/
def readFromFile (path : System.FilePath) : IO Background := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  let directJson := (json.getObjValAs? Json "direct").toOption.getD (.obj default)
  let chainsJson := (json.getObjValAs? Json "chains").toOption.getD (.obj default)
  let mut direct : Std.HashMap String (Array String) := {}
  let mut chains : Std.HashMap String (Array String) := {}
  match directJson with
  | .obj kvs =>
    for (k, v) in kvs.toList do
      match v.getArr? with
      | .ok arr =>
        let strs := arr.filterMap fun j => j.getStr?.toOption
        direct := direct.insert k strs
      | .error _ => pure ()
  | _ => pure ()
  match chainsJson with
  | .obj kvs =>
    for (k, v) in kvs.toList do
      match v.getArr? with
      | .ok arr =>
        let strs := arr.filterMap fun j => j.getStr?.toOption
        chains := chains.insert k strs
      | .error _ => pure ()
  | _ => pure ()
  pure { chains, direct }

/-- Check if synset `child` is a descendant of synset `ancestor`
    in the WordNet hypernym hierarchy. -/
def isDescendantOf (bg : Background) (child ancestor : String) : Bool :=
  match bg.chains.get? child with
  | some chain => chain.contains ancestor
  | none => false

/-- Check if concept `sub` IsA concept `sup` according to background
    WordNet hypernymy. Both must have synset grounding. -/
def backgroundIsA (bg : Background) (sub sup : ConceptId) : Bool :=
  match sub.synset?, sup.synset? with
  | some s1, some s2 =>
    s1 == s2 || bg.isDescendantOf s1 s2
  | _, _ => false

/-- Generate background IsA atoms for a concept: all its ancestors
    that also appear in our grounding table. -/
def ancestorSynsets (bg : Background) (synsetId : String) : Array String :=
  match bg.chains.get? synsetId with
  | some chain => chain
  | none => #[]

/-- Get direct parent synsets. -/
def directParents (bg : Background) (synsetId : String) : Array String :=
  match bg.direct.get? synsetId with
  | some parents => parents
  | none => #[]

end Background

end GFCore
