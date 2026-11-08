import Mettapedia.Languages.Lean.Declarations.Reader

/-!
# Mutual and registered-list members read from Lean recursors

The recursor's motive telescope identifies every member, including nested
list instances. Its minor premises identify constructor order. Member tags
are finite ordinals; original indices are retained separately. Synthetic
constructor IDs have explicit source constructors and type arguments.

This reads declaration data. Positive admission and semantic correspondence
are separate obligations; unsupported containers are refused by name.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations

open _root_.Lean _root_.Lean.Meta _root_.Lean.Elab

structure BlockMember where
  tag : Nat
  source : STerm
  reading : Reading
  nested : Bool
  deriving Repr

structure ConstructorOrigin where
  identifier : String
  member : Nat
  source : String
  arguments : List STerm
  deriving Repr

structure BlockRecursor where
  source : String
  resultMember : Nat
  motives : List Nat
  minors : List String
  kRule : Bool
  deriving Repr

structure BlockReading where
  name : String
  members : List BlockMember
  origins : List ConstructorOrigin
  recursors : List BlockRecursor
  deriving Repr

inductive BlockRefusal where
  | family (reason : Refusal)
  | malformedRecursor (name : String)
  | unknownContainer (owner container : String)
  | indexedNestedMember (owner : String)
  | nonUniformParameters (owner : String)
  | unknownMinor (recursor constructor : String)
  deriving Repr

abbrev BlockReadM := ExceptT BlockRefusal MetaM

def BlockReadM.family {α : Type} (action : ReadM α) : BlockReadM α := do
  match ← action.run with
  | .ok value => return value
  | .error reason => throwThe BlockRefusal (.family reason)

def BlockReadM.readFamily (name : Name) : BlockReadM Reading := do
  match ← readFamilyShape name true with
  | .ok reading => return reading
  | .error reason => throwThe BlockRefusal (.family reason)

def appliedFamily (family : SFamily) : STerm :=
  family.parameters.foldl (fun term parameter => .app term (.name parameter.name)) (.name family.name)

def readInstantiatedConstructor (known : Names) (taken : List String)
    (identifier : String) (application : Expr) :
    BlockReadM (SConstructor × List Bool × List (Option STerm)) := do
  let type ← inferType application
  ExceptT.mk <| forallTelescopeReducing type fun fields result => ExceptT.run do
    let (names, _) ← nameAll known taken fields "field"
    let binders ← BlockReadM.family (binders names identifier fields)
    let proofFields ← fields.toList.mapM fun field => do
      let type ← inferType field
      if ← isProp type then
        return some (← BlockReadM.family (toTerm names identifier (← whnfD type)))
      else return none
    let kept ← fields.toList.mapM fun field => return !(← erasedType (← inferType field))
    return (⟨identifier, binders, ← BlockReadM.family (toTerm names identifier result)⟩, kept, proofFields)

def readBlock (typeName : Name) : MetaM (Except BlockRefusal BlockReading) := ExceptT.run do
  let first ← BlockReadM.readFamily typeName
  let info ← getConstInfoInduct typeName
  let mut members : List BlockMember := []
  let mut origins : List ConstructorOrigin := []
  for name in info.all do
    let reading ← BlockReadM.readFamily name
    if reading.family.parameters != first.family.parameters then
      throwThe BlockRefusal (.nonUniformParameters name.toString)
    let tag := members.length
    members := members ++ [⟨tag, appliedFamily reading.family, reading, false⟩]
    origins := origins ++ reading.family.constructors.map fun ctor =>
      ⟨ctor.name, tag, ctor.name, reading.family.parameters.map (fun p => .name p.name)⟩
  let recName := typeName ++ `rec
  let recursor ← getConstInfoRec recName
  let (allMembers, allOrigins) ← ExceptT.mk <|
    forallTelescopeReducing recursor.type fun xs _ => ExceptT.run do
      if recursor.numParams + recursor.numMotives > xs.size then
        throwThe BlockRefusal (.malformedRecursor recName.toString)
      let mut known : Names := {}
      let parameterNames := first.family.parameters.map (·.name)
      for i in [0:recursor.numParams] do
        known := known.insert xs[i]!.fvarId! (parameterNames[i]?.getD s!"p{i}")
      let mut nestedMembers := members
      let mut nestedOrigins := origins
      for i in [info.all.length:recursor.numMotives] do
        let (source, element) ← ExceptT.mk <|
          forallTelescopeReducing (← inferType xs[recursor.numParams + i]!) fun fields _ => ExceptT.run do
            if fields.size != 1 then throwThe BlockRefusal (.indexedNestedMember recName.toString)
            let sourceType ← whnf (← inferType fields[0]!)
            let args := sourceType.getAppArgs
            unless sourceType.isAppOfArity ``List 1 do
              throwThe BlockRefusal (.unknownContainer typeName.toString (toString (← ppExpr sourceType.getAppFn)))
            return (← BlockReadM.family (toTerm known typeName.toString sourceType), args[0]!)
        let memberName := s!"{typeName}._nested_{i}"
        let mut constructors := []
        let mut keptFields := []
        let mut proofFields := []
        for ctorName in [``List.nil, ``List.cons] do
          let identifier := s!"{memberName}.{ctorName.getString!}"
          let application ← mkAppOptM ctorName #[some element]
          let (ctor, kept, proofs) ← readInstantiatedConstructor known parameterNames identifier application
          constructors := constructors ++ [ctor]
          keptFields := keptFields ++ [kept]
          proofFields := proofFields ++ [proofs]
          nestedOrigins := nestedOrigins ++ [⟨identifier, i, ctorName.toString,
            [← BlockReadM.family (toTerm known identifier element)]⟩]
        let reading : Reading := {
          family := ⟨memberName, first.family.parameters, [], .name "Type", constructors⟩
          universes := first.universes
          elimination := first.elimination
          keptFields, proofFields }
        nestedMembers := nestedMembers ++ [⟨i, source, reading, true⟩]
      return (nestedMembers, nestedOrigins)
  let mut recursors := []
  for (name, resultMember) in info.all.zipIdx do
    let recName := name ++ `rec
    let recursor ← getConstInfoRec recName
    if recursor.numMotives != allMembers.length then throwThe BlockRefusal (.malformedRecursor recName.toString)
    let minors ← ExceptT.mk <|
      forallTelescopeReducing recursor.type fun xs _ => ExceptT.run do
        let mut minors := []
        for i in [0:recursor.numMinors] do
          let position := recursor.numParams + recursor.numMotives + i
          if position >= xs.size then throwThe BlockRefusal (.malformedRecursor recName.toString)
          let (tag, ctorName) ← ExceptT.mk <|
            forallTelescopeReducing (← inferType xs[position]!) fun _ result => ExceptT.run do
              let some tag := (List.range recursor.numMotives).find? fun tag =>
                result.getAppFn == xs[recursor.numParams + tag]!
                | throwThe BlockRefusal (.malformedRecursor recName.toString)
              let some ctorName := result.getAppArgs.back!.getAppFn.constName?
                | throwThe BlockRefusal (.malformedRecursor recName.toString)
              return (tag, ctorName)
          let some origin := allOrigins.find? (fun origin => origin.member == tag && origin.source == ctorName.toString)
            | throwThe BlockRefusal (.unknownMinor recName.toString ctorName.toString)
          minors := minors ++ [origin.identifier]
        return minors
    recursors := recursors ++ [⟨recName.toString, resultMember, List.range recursor.numMotives, minors, recursor.k⟩]
  return ⟨info.all.head!.toString, allMembers, allOrigins, recursors⟩

deriving instance ToExpr for BlockMember
deriving instance ToExpr for ConstructorOrigin
deriving instance ToExpr for BlockRecursor
deriving instance ToExpr for BlockReading

elab "lean_block% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  match ← readBlock name with
  | .ok reading => return toExpr reading
  | .error reason => throwError "lean_block%: {name}: {repr reason}"

end Mettapedia.Languages.Lean.Declarations
