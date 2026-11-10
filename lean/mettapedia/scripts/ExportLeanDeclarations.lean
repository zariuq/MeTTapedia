import Mettapedia.Languages.Lean.Declarations.ReaderControls
import Mettapedia.Languages.Lean.Declarations.Terms
import Mettapedia.Languages.Lean.Declarations.Manifest
import Mettapedia.Languages.Lean.Declarations.BlockData
import Mettapedia.Languages.Lean.Declarations.TargetEnvironment
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData
import Mettapedia.Languages.MeTTa.PeTTa.ProgramReplayProtocol

/-!
Export Lean inductive declarations as MeTTa atoms, in the authoring form of
the shared declaration syntax (`InductiveMeTTaData.familyData`), with the
reader's elimination and erasure facts.

Run from the project root:
`lake env lean scripts/ExportLeanDeclarations.lean`
writes `artifacts/lean-declarations/families.metta`, one atom per declaration:

  (LeanFamily <family> (Universes u ...) (Elimination anySort|propOnly)
     (KeptFields (<flags of each constructor's fields>) ...))

and `artifacts/lean-declarations/refusals.metta`, one atom per refused
declaration with the reader's reason.

`LEAN_DECLARATIONS_ROOTS` selects the roots file. `LEAN_DECLARATIONS_ROOT_KIND`
is `families` for an explicit ordered family inventory (the default slice),
or `declarations` to discover every family in the reconstruction closure.
`LEAN_DECLARATIONS_OUT` selects the output directory. With
`LEAN_DECLARATIONS_CHECK=1`, fresh output is compared without modifying files.
-/

open Lean Meta Elab
open Mettapedia.Languages.Lean.Declarations
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.PeTTa.ProgramReplayProtocol (atomString)

/-- The explicit root plan is data, shared with the other export lanes. -/
def declarations : MetaM (List Name) := do
  let file := (← IO.getEnv "LEAN_DECLARATIONS_ROOTS").getD
    "artifacts/lean-declarations/slice-family-roots.txt"
  let roots ← match Manifest.resolveRoots (← getEnv) (← IO.FS.readFile file) with
    | .ok roots => pure roots
    | .error reason => throwError reason
  match (← IO.getEnv "LEAN_DECLARATIONS_ROOT_KIND").getD "families" with
  | "families" =>
      for name in roots do
        unless (← getEnv).find? name |>.any (fun info => match info with
            | .inductInfo _ => true | _ => false) do
          throwError "family root is not an inductive: {name}"
      return roots.toList
  | "declarations" =>
      match Manifest.closure (← getEnv) roots with
      | .ok names => return (Manifest.directFamilies (← getEnv) names).toList
      | .error reason => throwError reason
  | mode => throwError "unknown declaration root kind: {mode}"

def eliminationName : Elimination → String
  | .anySort => "anySort"
  | .propOnly => "propOnly"

def flagsText (flags : List Bool) : String :=
  "(" ++ " ".intercalate (flags.map fun flag => if flag then "true" else "false") ++ ")"

def readingText (reading : Reading) : String :=
  "(LeanFamily " ++ atomString (InductiveMeTTaData.familyData reading.family) ++
    " (Universes" ++ String.join (reading.universes.map (" " ++ ·)) ++ ")" ++
    " (Elimination " ++ eliminationName reading.elimination ++ ")" ++
    " (KeptFields" ++ String.join (reading.keptFields.map (" " ++ flagsText ·)) ++ "))"

section Admitted
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Languages.Lean.Declarations.Profile (IndexTerm Model admit guards DataSort inventoryKept)

def termText (t : STerm) : String := atomString (InductiveMeTTaData.termData t)

/-- An index term, its data variables replaced by field positions. -/
def indexText (positions : List Nat) : {depth : Nat} → IndexTerm depth → String
  | _, .var p => s!"(field {positions.getD p.val 0})"
  | _, .name c => s!"(const {c})"
  | _, .app f x => s!"(app {indexText positions f} {indexText positions x})"

def indicesText (positions : List Nat) {depth : Nat} (terms : List (IndexTerm depth)) : String :=
  "(" ++ " ".intercalate (terms.map (indexText positions)) ++ ")"

/-- The fields of an admitted constructor code, in order, each with whether it
is data, and its result.  `slots` are the field positions of the code's fields
(the positions of guards are skipped); `positions` the positions of the data
fields in scope, nearest first. -/
def codeText : {context : List DataSort} → Code (Model.syntactic.interface) context →
    List Nat → List Nat → List (String × Bool) × String
  | context, .result index, _, positions =>
      ([], "(result " ++ indicesText positions (show List (IndexTerm context.length) from index) ++ ")")
  | _, .data sort body, slots, positions =>
      let position := slots.headD 0
      let (fields, result) := codeText body slots.tail (position :: positions)
      (("(data " ++ termText (show DataSort from sort).term ++ ")", true) :: fields, result)
  | context, .recursive index rest, slots, positions =>
      let (fields, result) := codeText rest slots.tail positions
      (("(rec " ++ indicesText positions (show List (IndexTerm context.length) from index) ++ ")", false)
        :: fields, result)

/-- A constructor's fields with its guards at their positions: a guard's
proposition is an index term over the data fields before it. -/
def mergeGuards (fields : List (String × Bool)) (slots : List Nat) (guards : List Profile.Guard) :
    List String :=
  let dataPositions := (fields.zip slots).filterMap fun ((_, isData), slot) =>
    if isData then some slot else none
  let total := fields.length + guards.length
  let rec go : Nat → List (String × Bool) → List String
    | 0, _ => []
    | fuel + 1, rest =>
      let position := total - (fuel + 1)
      match guards.find? (·.position == position) with
      | some guard =>
          ("(guard " ++ atomString (GuardData.termData
            (dataPositions.take guard.depth).reverse guard.proposition) ++ ")")
            :: go fuel rest
      | none => (rest.headD ("", false)).1 :: go fuel rest.tail
  go total fields

/-- The admitted `Description` inventory of a read family with its guards, or why not. -/
def admittedText (reading : Reading) : Except String String :=
  match admit Model.syntactic reading.family reading.proofFields reading.keptFields,
        guards Model.syntactic reading.family reading.proofFields with
  | .error refusal, _ | _, .error refusal => .error (toString (repr refusal))
  | .ok admitted, .ok allGuards =>
      let constructors := (admitted.constructors.zip allGuards).map fun (constructor, guards) =>
        let total := (codeText constructor.body (List.range 1000) []).1.length + guards.length
        let slots := (List.range total).filter fun q => !guards.any (·.position == q)
        let (fields, result) := codeText constructor.body slots []
        "(" ++ constructor.name ++ " (fields" ++
          String.join ((mergeGuards fields slots guards).map (" " ++ ·)) ++ ") " ++ result ++ ")"
      .ok ("(LeanAdmitted " ++ reading.family.name ++ " (" ++ " ".intercalate constructors ++ "))")

/-- The code-equation exporter reads the fields it keeps from the inventory
(`inventoryKept`, through `Profile.constructorFields`).  For an admitted
family they must be exactly Lean's erasure, constructor by constructor. -/
def agreesWithInventory (reading : Reading) : Bool :=
  match inventoryKept reading with
  | some table =>
      table.length == reading.family.constructors.length &&
        (table.zip reading.keptFields).all fun ((_, kept), lean) => kept == lean
  | none => true

end Admitted

def namesText (reading : Reading) : String :=
  let names := reading.family.name :: reading.family.constructors.map (·.name)
  String.join (names.map fun name => s!"(EgalName {name} {egalIdent name})\n")

def refusalText (name : Name) (refusal : Refusal) : String :=
  "(LeanRefusal " ++ name.toString ++ " " ++ (Json.str (toString (repr refusal))).compress ++ ")"

def export_ (declarations : List Name) (blocks : Bool) : MetaM (String × String) := do
  let mut families := ""
  let mut refusals := ""
  let mut seenBlocks : List String := []
  for name in declarations do
    match ← read name blocks with
    | .ok reading =>
        unless agreesWithInventory reading do
          throwError "{name}: the inventory and the exporter's kept fields disagree"
        families := families ++ readingText reading ++ "\n" ++ namesText reading
        match admittedText reading with
        | .ok text => families := families ++ text ++ "\n"
        | .error reason =>
            refusals := refusals ++ "(LeanProfileRefusal " ++ name.toString ++ " " ++
              (Json.str reason).compress ++ ")\n"
    | .error refusal =>
        if !blocks then
          refusals := refusals ++ refusalText name refusal ++ "\n"
        else
          match ← readBlock name with
          | .error reason =>
              refusals := refusals ++ "(LeanBlockRefusal " ++ name.toString ++ " " ++
                (Json.str (toString (repr reason))).compress ++ ")\n"
          | .ok block =>
              if seenBlocks.contains block.name then continue
              seenBlocks := block.name :: seenBlocks
              match BlockData.data block with
              | .error reason =>
                  refusals := refusals ++ "(LeanBlockProfileRefusal " ++ name.toString ++ " " ++
                    (Json.str (toString (repr reason))).compress ++ ")\n"
              | .ok atoms =>
                  let some kept := BlockProfile.inventoryKept block
                    | throwError "block has no erasure inventory: {name}"
                  for member in block.members do
                    for (constructor, expected) in
                        member.reading.family.constructors.zip member.reading.keptFields do
                      unless kept.lookup constructor.name == some expected do
                        throwError "block erasure differs from Lean: {constructor.name}"
                    families := families ++ readingText member.reading ++ "\n" ++ namesText member.reading
                  families := families ++ String.join (atoms.map (fun atom => atomString atom ++ "\n"))
  return (families, refusals)

def runExport : MetaM Unit := do
  let roots : System.FilePath := (← IO.getEnv "LEAN_DECLARATIONS_ROOTS").getD
    "artifacts/lean-declarations/slice-family-roots.txt"
  let some directory := roots.parent | throwError "declaration roots have no target directory"
  discard <| TargetEnvironment.load directory
  let declarations ← declarations
  let blocks := (← IO.getEnv "LEAN_DECLARATIONS_BLOCKS") == some "1" ||
    (← IO.getEnv "LEAN_DECLARATIONS_ROOT_KIND") == some "declarations"
  let (families, refusals) ← export_ declarations blocks
  let dir : System.FilePath := (← IO.getEnv "LEAN_DECLARATIONS_OUT").getD "artifacts/lean-declarations"
  let check := (← IO.getEnv "LEAN_DECLARATIONS_CHECK") == some "1"
  let outputs := [("families.metta", families), ("refusals.metta", refusals)]
  if check then
    for (file, fresh) in outputs do
      let committed ← IO.FS.readFile (dir / file)
      if fresh != committed then throwError s!"check: {file} differs"
    IO.println "check: the committed export equals a fresh export"
  else
    IO.FS.createDirAll dir
    for (file, text) in outputs do IO.FS.writeFile (dir / file) text
    IO.println s!"exported {declarations.length} declarations"

#eval runExport
