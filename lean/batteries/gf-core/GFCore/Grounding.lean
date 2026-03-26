/-
# GFCore.Grounding — Load concept grounding from WordNet

Reads concept_grounding.json and provides lookup:
  gfFun → ConceptId (with synset, domain, gloss)

Ground structured types (Term, Modifier, Atom) via groundTerm/groundAtom.
-/

import Lean.Data.Json
import GFCore.Atom

namespace GFCore

open Lean (Json FromJson fromJson? ToJson toJson)

/-- A grounding entry from the JSON export. -/
structure GroundingEntry where
  cat     : String
  synset  : String
  domain  : String
  gloss   : String
  deriving Repr, Inhabited

instance : FromJson GroundingEntry where
  fromJson? j := do
    let cat ← j.getObjValAs? String "cat"
    let synset ← j.getObjValAs? String "synset"
    let domain := (j.getObjValAs? String "domain").toOption.getD ""
    let gloss := (j.getObjValAs? String "gloss").toOption.getD ""
    pure { cat, synset, domain, gloss }

/-- The full grounding table: gfFun → GroundingEntry. -/
structure GroundingTable where
  entries : Std.HashMap String GroundingEntry
  deriving Inhabited

namespace GroundingTable

/-- Load from JSON file. -/
def readFromFile (path : System.FilePath) : IO GroundingTable := do
  let contents ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse contents)
  match json with
  | .obj kvs =>
    let mut entries : Std.HashMap String GroundingEntry := Std.HashMap.emptyWithCapacity 120000
    for (k, v) in kvs.toList do
      match fromJson? v with
      | .ok entry => entries := entries.insert k entry
      | .error _ => pure ()
    pure { entries }
  | _ => throw (IO.userError "concept_grounding.json must be a JSON object")

/-- Look up a GF function name and return a grounded ConceptId. -/
def ground (table : GroundingTable) (gfFun cat : String) : ConceptId :=
  match table.entries.get? gfFun with
  | some entry => {
      gfFun := gfFun
      cat := cat
      synset? := some entry.synset
      gloss? := some entry.gloss
    }
  | none => ConceptId.fromGF gfFun cat

/-- Ground an existing ConceptId (add synset if available). -/
def groundId (table : GroundingTable) (id : ConceptId) : ConceptId :=
  match table.entries.get? id.gfFun with
  | some entry => { id with synset? := some entry.synset, gloss? := some entry.gloss }
  | none => id

end GroundingTable

/-- Ground a Modifier's lexemes. -/
def groundModifier (gt : GroundingTable) : Modifier → Modifier
  | .adj a => .adj (gt.groundId a)
  | .nounMod n => .nounMod (gt.groundId n)
  | .prep p obj => .prep (gt.groundId p) (gt.groundId obj)
  | .appos h => .appos (gt.groundId h)
  | .superl a => .superl (gt.groundId a)
  | .opaqueMod r => .opaqueMod r

/-- Ground all ConceptIds in a Term. -/
partial def groundTerm (gt : GroundingTable) : Term → Term
  | .entity h det num mods =>
    .entity (gt.groundId h) det num (mods.map (groundModifier gt))
  | .event p args =>
    .event (gt.groundId p) (args.map fun (r, t) => (r, groundTerm gt t))
  | t@(.var _) => t
  | t@(.opaque _) => t

/-- Ground all ConceptIds in an Atom. -/
partial def groundAtom (gt : GroundingTable) : Atom → Atom
  | .isa sub sup => .isa (groundTerm gt sub) (groundTerm gt sup)
  | .rel p args => .rel (gt.groundId p) (args.map (groundTerm gt))
  | .compare c p x y => .compare c (gt.groundId p) (groundTerm gt x) (groundTerm gt y)
  | .causes c e => .causes (groundAtom gt c) (groundAtom gt e)
  | .implies a c => .implies (groundAtom gt a) (groundAtom gt c)
  | .conj xs => .conj (xs.map (groundAtom gt))
  | .neg x => .neg (groundAtom gt x)
  | .forAll v b => .forAll v (groundAtom gt b)
  | a@(.opaque _) => a

end GFCore
