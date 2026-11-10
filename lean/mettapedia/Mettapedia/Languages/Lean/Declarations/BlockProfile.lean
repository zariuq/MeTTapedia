import Mettapedia.Languages.Lean.Declarations.BlockReader
import Mettapedia.Languages.Lean.Declarations.Profile

/-!
# Tagged block admission into the existing description inventory

The index is a member ordinal paired with the member's original indices.
Recursive fields retain that entire index. Data fields extend the expression
scope; recursive fields do not. Unknown nested containers and function-valued
recursive fields are refused. No source constructor or field is silently lost.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.BlockProfile

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef
open Profile (Model DataSort IndexTerm Guard)

def interface (model : Model) : Interface.{0} where
  SortCode := DataSort
  Value := model.SortValue
  Index := Nat × List model.Domain
  IndexExpr := fun context => Nat × List (IndexTerm context.length)
  evalIndex := fun expression environment =>
    (expression.1, expression.2.map (model.eval environment))

inductive Refusal where
  | malformedBlock (owner : String)
  | unsupportedField (constructor field : String)
  | functionField (constructor field : String)
  | unknownContainer (constructor field : String)
  | missingResult (constructor : String)
  | profile (reason : Profile.Refusal)
  | duplicateConstructors
  deriving DecidableEq, Repr

/-- An occurrence repeats the member's fixed parameters and supplies exactly
its original indices. Nested instances use their complete registered head. -/
def occurrence (members : List BlockMember) (term : STerm) : Option (Nat × List STerm) :=
  let (head, arguments) := Profile.spine term
  members.findSome? fun member =>
    let (expected, parameters) := Profile.spine member.source
    if head = expected && arguments.take parameters.length = parameters &&
        arguments.length = parameters.length + member.reading.family.indices.length then
      some (member.tag, arguments.drop parameters.length)
    else none

def recursiveName (block : BlockReading) (term : STerm) : Bool :=
  block.members.any fun member =>
    !member.nested && Profile.mentions member.reading.family.name term

def resolveIndex (owner : SFamily) (constructor : String) (context : List DataSort)
    (scope recursive : List String) (index : Nat × List STerm) :
    Except Refusal (Nat × List (IndexTerm context.length)) := do
  let expressions ← index.2.mapM fun term =>
    (Profile.resolve (Profile.header owner) constructor context.length scope recursive term).mapError Refusal.profile
  return (index.1, expressions)

def lowerFields (model : Model) (block : BlockReading) (owner : SFamily)
    (constructor : String) (result : STerm) :
    (context : List DataSort) → (scope recursive : List String) → (position : Nat) →
      List SBinder → List (Option STerm) → List Bool →
      Except Refusal (IndexedInductive.RawCode (interface model) context × List Guard)
  | context, scope, recursive, _, [], [], [] => do
      let some index := occurrence block.members result | throw (.missingResult constructor)
      return (.result (← resolveIndex owner constructor context scope recursive index), [])
  | context, scope, recursive, position, field :: rest, proof :: proofs, kept :: remaining => do
      match occurrence block.members field.type with
      | some index =>
          let index ← resolveIndex owner constructor context scope recursive index
          let (body, guards) ← lowerFields model block owner constructor result context scope
            (field.name :: recursive) (position + 1) rest proofs remaining
          return (.recursive index body, guards)
      | none =>
          if recursiveName block field.type then
            match field.type with
            | .arrow _ _ => throw (.functionField constructor field.name)
            | _ => throw (.unknownContainer constructor field.name)
          if recursive.any (Profile.mentions · field.type) then
            throw (.unsupportedField constructor field.name)
          if scope.any (Profile.mentions · field.type) || proof.any Profile.hasDependentProduct then
            let some proposition := proof | throw (.unsupportedField constructor field.name)
            let expression ← (Profile.resolveGuard (Profile.header owner) constructor context.length
              scope recursive proposition).mapError Refusal.profile
            let (body, guards) ← lowerFields model block owner constructor result context scope recursive
              (position + 1) rest proofs remaining
            return (body, ⟨field.name, position, context.length, expression⟩ :: guards)
          else
            let sort : DataSort := ⟨proof.getD field.type, kept⟩
            let (body, guards) ← lowerFields model block owner constructor result (sort :: context)
              (field.name :: scope) recursive (position + 1) rest proofs remaining
            return (.data sort body, guards)
  | _, _, _, _, _, _, _ => .error (.malformedBlock constructor)

def lower (model : Model) (block : BlockReading) :
    Except Refusal (List (IndexedInductive.RawConstructor (interface model) [] × List Guard)) := do
  if block.members.isEmpty || block.members.map (·.tag) != List.range block.members.length then
    throw (.malformedBlock block.name)
  let mut output := []
  for member in block.members do
    let reading := member.reading
    if reading.family.constructors.length != reading.keptFields.length ||
        reading.family.constructors.length != reading.proofFields.length then
      throw (.malformedBlock reading.family.name)
    for ((constructor, proofs), kept) in
        (reading.family.constructors.zip reading.proofFields).zip reading.keptFields do
      let (body, guards) ← lowerFields model block reading.family constructor.name constructor.result
        [] [] [] 0 constructor.fields proofs kept
      output := output ++ [(⟨constructor.name, body⟩, guards)]
  return output

def admit (model : Model) (block : BlockReading) :
    Except Refusal (IndexedInductive.Admitted (interface model) []) := do
  let source ← lower model block
  match IndexedInductive.admitList? (source.map (·.1)) with
  | some admitted => return admitted
  | none => throw .duplicateConstructors

/-- Erasure uses the recursive member's sort, not the block owner's sort. -/
def codeRelevance {model : Model} (block : BlockReading) :
    {context : List DataSort} → Code (interface model) context → List Bool
  | _, .result _ => []
  | _, .data sort body => sort.relevant :: codeRelevance block body
  | _, .recursive index rest =>
      ((block.members[index.1]?).any (fun member => member.reading.family.sort != .name "Prop")) ::
        codeRelevance block rest

def inventoryKept (block : BlockReading) : Option (List (String × List Bool)) := do
  let admitted ← (admit Model.syntactic block).toOption
  let source ← (lower Model.syntactic block).toOption
  return (admitted.constructors.zip source).map fun (constructor, (_, guards)) =>
    (constructor.name, Profile.withGuards (codeRelevance block constructor.body) guards)

end Mettapedia.Languages.Lean.Declarations.BlockProfile
