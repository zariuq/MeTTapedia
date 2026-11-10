import Mettapedia.Languages.Lean.Declarations.BlockProfile
import Mettapedia.Languages.Lean.Declarations.GuardData
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData

/-!
# Tagged constructor inventories as MeTTa data

Ordinal tags precede the original dependent indices. Source constructor
origins and recursor motive/minor order accompany the admitted inventory.
This is declaration data, not a certificate of source-carrier equivalence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.BlockData

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData (termData bindersData)
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Profile (Model DataSort IndexTerm Guard)

def node (name : String) (arguments : List Atom) : Atom := .expression (.symbol name :: arguments)
def number (value : Nat) : Atom := .symbol (toString value)

def sourceData : STerm → Atom
  | .name name => node "const" [.symbol name]
  | .app function argument => node "app" [sourceData function, sourceData argument]
  | .arrow domain codomain => node "arrow" [sourceData domain, sourceData codomain]
  | .pi binder domain codomain => node "pi" [.symbol binder, sourceData domain, sourceData codomain]
  | .project owner field record => node "project" [.symbol owner, number field, sourceData record]

def expressionData (positions : List Nat) : {depth : Nat} → IndexTerm depth → Atom
  | _, .var position => node "field" [number (positions.getD position.val 0)]
  | _, .name name => node "const" [.symbol name]
  | _, .app function argument => node "app" [expressionData positions function, expressionData positions argument]

def indexData (positions : List Nat) {depth : Nat} (index : Nat × List (IndexTerm depth)) : Atom :=
  .expression (node "tag" [number index.1] :: index.2.map (expressionData positions))

def codeData : {context : List DataSort} → Code (BlockProfile.interface Model.syntactic) context →
    List Nat → List Nat → List (Atom × Bool) × Atom
  | _, .result index, _, positions => ([], node "result" [indexData positions index])
  | _, .data sort body, slots, positions =>
      let position := slots.headD 0
      let (fields, result) := codeData body slots.tail (position :: positions)
      ((node "data" [termData sort.term], true) :: fields, result)
  | _, .recursive index rest, slots, positions =>
      let (fields, result) := codeData rest slots.tail positions
      ((node "rec" [indexData positions index], false) :: fields, result)

def mergeGuards (fields : List (Atom × Bool)) (slots : List Nat) (guards : List Guard) : List Atom :=
  let positions := (fields.zip slots).filterMap fun ((_, isData), position) =>
    if isData then some position else none
  let total := fields.length + guards.length
  let rec go : Nat → List (Atom × Bool) → List Atom
    | 0, _ => []
    | fuel + 1, rest =>
        let position := total - (fuel + 1)
        match guards.find? (·.position == position) with
        | some guard => node "guard" [GuardData.termData (positions.take guard.depth).reverse guard.proposition] ::
            go fuel rest
        | none => (rest.headD (.expression [], false)).1 :: go fuel rest.tail
  go total fields

def fieldCount : {context : List DataSort} → Code (BlockProfile.interface Model.syntactic) context → Nat
  | _, .result _ => 0
  | _, .data _ body => fieldCount body + 1
  | _, .recursive _ rest => fieldCount rest + 1

def memberData (member : BlockMember) : Atom :=
  node "member" [number member.tag, sourceData member.source,
    node "indices" [bindersData member.reading.family.indices], termData member.reading.family.sort]

def admittedData (block : BlockReading) : Except BlockProfile.Refusal Atom := do
  let admitted ← BlockProfile.admit Model.syntactic block
  let source ← BlockProfile.lower Model.syntactic block
  let constructors := (admitted.constructors.zip source).map fun (constructor, (_, guards)) =>
    let total := fieldCount constructor.body + guards.length
    let slots := (List.range total).filter fun position => !guards.any (·.position == position)
    let (fields, result) := codeData constructor.body slots []
    node constructor.name [node "fields" (mergeGuards fields slots guards), result]
  return node "LeanAdmittedBlock" [.symbol block.name,
    node "members" (block.members.map memberData), .expression constructors]

def originData (block : BlockReading) (origin : ConstructorOrigin) : Atom :=
  node "LeanBlockConstructorOrigin" [.symbol block.name, .symbol origin.identifier, .symbol origin.source,
    .expression (origin.arguments.map sourceData)]

def recursorData (block : BlockReading) (recursor : BlockRecursor) : Atom :=
  node "LeanBlockRecursor" [.symbol block.name, .symbol recursor.source,
    node "result" [number recursor.resultMember], node "motives" (recursor.motives.map number),
    node "minors" (recursor.minors.map Atom.symbol), node "K" [.symbol (if recursor.kRule then "true" else "false")]]

def data (block : BlockReading) : Except BlockProfile.Refusal (List Atom) := do
  return (← admittedData block) :: block.origins.map (originData block) ++ block.recursors.map (recursorData block)

end Mettapedia.Languages.Lean.Declarations.BlockData
