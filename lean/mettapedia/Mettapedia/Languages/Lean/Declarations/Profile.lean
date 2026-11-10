import Mettapedia.Languages.Lean.Declarations.Reader
import Mettapedia.Languages.Lean.Declarations.GuardSyntax
import Mettapedia.GSLT.LanguageDef.IndexedInductive

/-!
# Lean declarations into indexed admission

A family read from Lean (`Reader`) is lowered into the constructor telescopes
of `IndexedInductive`, whose admission yields an inventory of
`IndexedPolynomial.Description` constructors.  The interface is syntactic: a
data sort is the field's type term, and an index expression is a list of index
terms, one per index of the family, over the data fields before it.  Data
fields extend that scope; recursive fields do not, as `Description` requires.
The meaning of sorts and index terms is a separate `Model`; lowering and
admission do not depend on it.

Lowering keeps every field and refuses by name what the fragment does not
cover: a recursive occurrence with other parameters than the family's, an
index mentioning a recursive field, a data sort depending on an earlier field,
and an occurrence of the family nested inside another type.  A function field
is lowered as one, so that admission refuses it as `IndexedInductive` does
for every source.

**Guards.** A proof field whose proposition mentions earlier data fields
(`isLt : val < n` in `Fin`, `h : p w` in `Exists`) is a guard on them.  It adds
no data: Lean erases it, and its value is the proof.  The `Description` code
keeps the constructor's data and recursive fields; each guard is recorded
beside it, with its position among the fields and its proposition (read by the
Reader in weak head normal form) as a scoped guard over the data before it.
Guard products bind variables locally; family indices retain the first-order
index language.
Without the Reader's proof information (`admit` with no `proofs`), such a field
is a dependent data sort and is refused; a dependent field that is data, not a
proof, is refused in every case.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.Declarations.Profile

open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.GSLT.LanguageDef

/-- An index term over a data scope of `depth` fields; `var 0` is the nearest
data field.  Parameters and global constants are names. -/
inductive IndexTerm (depth : Nat) where
  | var (position : Fin depth)
  | name (identifier : String)
  | app (function argument : IndexTerm depth)
  deriving DecidableEq, Repr

/-- A data field's sort with its use at run time: `relevant` unless Lean
erases its values (proofs, types and type formers), the usages ω and 0 of
quantitative type theory.  The code-equation exporter keeps exactly the
relevant fields. -/
structure DataSort where
  term : STerm
  relevant : Bool
  deriving DecidableEq, Repr

/-- The meaning of declaration syntax: carriers of data sorts, and a domain
of index values built from field values, constants and application. -/
structure Model where
  Value : STerm → Type
  Domain : Type
  inject : (sort : STerm) → Value sort → Domain
  constant : String → Domain
  apply : Domain → Domain → Domain

namespace Model

variable (M : Model)

/-- The carrier of a data sort. -/
abbrev SortValue (sort : DataSort) : Type := M.Value sort.term

def lookup : {context : List DataSort} → Fin context.length → Env M.SortValue context → M.Domain
  | sort :: _, ⟨0, _⟩, environment => M.inject sort.term environment.1
  | _ :: _, ⟨k + 1, bound⟩, environment =>
      lookup ⟨k, Nat.lt_of_succ_lt_succ bound⟩ environment.2

def eval {context : List DataSort} (environment : Env M.SortValue context) :
    IndexTerm context.length → M.Domain
  | .var position => M.lookup position environment
  | .name identifier => M.constant identifier
  | .app function argument => M.apply (eval environment function) (eval environment argument)

/-- The interface of Lean declarations under this meaning. -/
def interface : Interface.{0} where
  SortCode := DataSort
  Value := M.SortValue
  Index := List M.Domain
  IndexExpr := fun context => List (IndexTerm context.length)
  evalIndex := fun expressions environment => expressions.map (M.eval environment)

/-- The meaning used for admission alone: every carrier is a point. -/
def syntactic : Model where
  Value := fun _ => PUnit
  Domain := PUnit
  inject := fun _ _ => PUnit.unit
  constant := fun _ => PUnit.unit
  apply := fun _ _ => PUnit.unit

end Model

/-- Why a read family is not lowered. -/
inductive Refusal where
  | notFamilyResult (constructor : String)
  | nonUniformParameters (constructor : String)
  | indexArity (constructor : String)
  | indexMentionsRecursive (constructor field : String)
  | dependentDataSort (constructor field : String)
  | nestedOccurrence (constructor field : String)
  | functionField (constructor field : String)
  | unsupportedIndex (constructor : String)
  | duplicateConstructors
  deriving DecidableEq, Repr

/-- Head and arguments of an application. -/
def spine : STerm → STerm × List STerm
  | .app function argument =>
      let (head, arguments) := spine function
      (head, arguments ++ [argument])
  | term => (term, [])

/-- Whether a name occurs in a term. -/
def mentions (name : String) : STerm → Bool
  | .name identifier => identifier == name
  | .app function argument => mentions name function || mentions name argument
  | .arrow domain codomain => mentions name domain || mentions name codomain
  | .pi binder domain codomain =>
      mentions name domain || (binder != name && mentions name codomain)
  | .project _ _ record => mentions name record

/-- A dependent product in a proof field needs the scoped guard interpreter,
even when the proposition mentions no earlier constructor field. -/
def hasDependentProduct : STerm → Bool
  | .name _ => false
  | .app function argument => hasDependentProduct function || hasDependentProduct argument
  | .arrow domain codomain => hasDependentProduct domain || hasDependentProduct codomain
  | .pi _ _ _ => true
  | .project _ _ record => hasDependentProduct record

/-- A guard: a proof field whose proposition mentions earlier data fields. -/
structure Guard where
  field : String
  /-- Its position among the constructor's fields. -/
  position : Nat
  /-- The number of data fields before it: the scope of its proposition. -/
  depth : Nat
  proposition : GuardSyntax.Term depth
  deriving Repr

/-- What lowering needs to know of the family. -/
structure Header where
  family : String
  parameters : List String
  indexCount : Nat

/-- An index term over the named data scope, nearest field first. -/
def resolve (header : Header) (owner : String) (depth : Nat) (scope recursive : List String) :
    STerm → Except Refusal (IndexTerm depth)
  | .name identifier =>
      match scope.idxOf? identifier with
      | some position =>
          if bound : position < depth then .ok (.var ⟨position, bound⟩)
          else .error (.unsupportedIndex owner)
      | none =>
          if recursive.contains identifier then .error (.indexMentionsRecursive owner identifier)
          else if identifier == header.family then .error (.unsupportedIndex owner)
          else .ok (.name identifier)
  | .app function argument => do
      return .app (← resolve header owner depth scope recursive function)
        (← resolve header owner depth scope recursive argument)
  | .arrow _ _ => .error (.unsupportedIndex owner)
  | .pi _ _ _ => .error (.unsupportedIndex owner)
  | .project _ _ _ => .error (.unsupportedIndex owner)

/-- First-order index expressions embed in the richer syntax of proof fields. -/
def guardOfIndex {depth : Nat} : IndexTerm depth → GuardSyntax.Term depth
  | .var position => .var position
  | .name identifier => .name identifier
  | .app function argument => .app (guardOfIndex function) (guardOfIndex argument)

/-- Quantified proof fields retain bound variables separately from their free
field references. Nondependent arrows weaken the body under the new binder. -/
def resolveGuard (header : Header) (owner : String) (depth : Nat)
    (scope recursive : List String) : STerm → Except Refusal (GuardSyntax.Term depth)
  | term@(.name _) => guardOfIndex <$> resolve header owner depth scope recursive term
  | .app function argument => do
      return .app (← resolveGuard header owner depth scope recursive function)
        (← resolveGuard header owner depth scope recursive argument)
  | .arrow domain codomain => do
      return .pi (← resolveGuard header owner depth scope recursive domain)
        ((← resolveGuard header owner depth scope recursive codomain).rename Fin.succ)
  | .pi binder domain codomain => do
      return .pi (← resolveGuard header owner depth scope recursive domain)
        (← resolveGuard header owner (depth + 1) (binder :: scope) recursive codomain)
  | .project structureName field record => do
      return .project structureName field (← resolveGuard header owner depth scope recursive record)

/-- The index arguments of an occurrence of the family with its own parameters. -/
def familyIndices (header : Header) (owner : String) (term : STerm) :
    Except Refusal (Option (List STerm)) := do
  let (head, arguments) := spine term
  if head != .name header.family then return none
  let count := header.parameters.length
  if arguments.take count != header.parameters.map (fun parameter => (.name parameter : STerm)) then
    throw (.nonUniformParameters owner)
  let indices := arguments.drop count
  if indices.length != header.indexCount then throw (.indexArity owner)
  return some indices

variable (M : Model)

/-- A field type under a function arrow, kept for explicit refusal. -/
def fieldType (header : Header) (owner : String) (context : List DataSort) (scope recursive : List String) :
    STerm → Except Refusal (IndexedInductive.FieldType (M.interface) context)
  | .arrow domain codomain => do
      return .arrow (← fieldType header owner context scope recursive domain)
        (← fieldType header owner context scope recursive codomain)
  | term => do
      match ← familyIndices header owner term with
      | some indices =>
          return .family (← indices.mapM (resolve header owner context.length scope recursive))
      | none =>
          if mentions header.family term then throw (.nestedOccurrence owner header.family)
          else return .ground ⟨term, true⟩

/-- Lower the fields of one constructor, then its result; `proofs` gives the
proposition of each proof field, `kept` whether Lean keeps each field at run
time, `position` counts the fields. -/
def lowerFields (header : Header) (owner : String) (result : STerm) :
    (context : List DataSort) → (scope recursive : List String) → (position : Nat) →
      List SBinder → List (Option STerm) → List Bool →
      Except Refusal (IndexedInductive.RawCode (M.interface) context × List Guard)
  | context, scope, recursive, _, [], _, _ => do
      match ← familyIndices header owner result with
      | some indices =>
          return (.result (← indices.mapM (resolve header owner context.length scope recursive)), [])
      | none => throw (.notFamilyResult owner)
  | context, scope, recursive, position, field :: rest, proofs, kept => do
      let proof := proofs.head?.join
      match ← familyIndices header owner field.type with
      | some indices =>
          let index ← indices.mapM (resolve header owner context.length scope recursive)
          let (body, guards) ← lowerFields header owner result context scope
            (recursive ++ [field.name]) (position + 1) rest proofs.tail kept.tail
          return (.recursive index body, guards)
      | none =>
          if mentions header.family field.type then
            match field.type with
            | .arrow domain codomain =>
                let (body, guards) ← lowerFields header owner result context scope recursive
                  (position + 1) rest proofs.tail kept.tail
                return (.functionField
                  (← fieldType M header owner context scope recursive domain)
                  (← fieldType M header owner context scope recursive codomain) body, guards)
            | _ => throw (.nestedOccurrence owner field.name)
          else if recursive.any (mentions · field.type) then
            throw (.dependentDataSort owner field.name)
          else if scope.any (mentions · field.type) || proof.any hasDependentProduct then
            match proof with
            | some proposition =>
                let guard : Guard := ⟨field.name, position, context.length,
                  ← resolveGuard header owner context.length scope recursive proposition⟩
                let (body, guards) ← lowerFields header owner result context scope recursive
                  (position + 1) rest proofs.tail kept.tail
                return (body, guard :: guards)
            | none => throw (.dependentDataSort owner field.name)
          else
            -- A proof field's sort is its proposition in weak head normal form
            -- (`¬p` is `p → False`), as the Reader records it.
            let sort : DataSort := ⟨proof.getD field.type, kept.head?.getD true⟩
            let (body, guards) ← lowerFields header owner result (sort :: context)
              (field.name :: scope) recursive (position + 1) rest proofs.tail kept.tail
            return (.data sort body, guards)

def header (family : SFamily) : Header :=
  ⟨family.name, family.parameters.map (·.name), family.indices.length⟩

/-- Every constructor of a read family, as admission source, with its guards. -/
def lowerGuarded (family : SFamily) (proofs : List (List (Option STerm)) := [])
    (kept : List (List Bool) := []) :
    Except Refusal (List (IndexedInductive.RawConstructor (M.interface) [] × List Guard)) :=
  (family.constructors.zip (family.constructors.mapIdx fun i _ => (proofs.getD i [], kept.getD i []))).mapM
    fun (constructor, fieldProofs, fieldsKept) => do
      let (body, guards) ← lowerFields M (header family) constructor.name constructor.result
        [] [] [] 0 constructor.fields fieldProofs fieldsKept
      return (⟨constructor.name, body⟩, guards)

/-- Every constructor of a read family, as admission source. -/
def lower (family : SFamily) (proofs : List (List (Option STerm)) := [])
    (kept : List (List Bool) := []) :
    Except Refusal (List (IndexedInductive.RawConstructor (M.interface) [])) :=
  return (← lowerGuarded M family proofs kept).map (·.1)

/-- The guards of each constructor of a read family. -/
def guards (family : SFamily) (proofs : List (List (Option STerm))) :
    Except Refusal (List (List Guard)) :=
  return (← lowerGuarded M family proofs).map (·.2)

/-- The first function field of a lowered constructor, for a named refusal. -/
def firstFunctionField : {context : List DataSort} → IndexedInductive.RawCode (M.interface) context →
    Bool
  | _, .result _ => false
  | _, .data _ body => firstFunctionField body
  | _, .recursive _ rest => firstFunctionField rest
  | _, .functionField _ _ _ => true

/-- Admission of a read family: its `Description` inventory, or why not. -/
def admit (family : SFamily) (proofs : List (List (Option STerm)) := [])
    (kept : List (List Bool) := []) :
    Except Refusal (IndexedInductive.Admitted (M.interface) []) := do
  let source ← lower M family proofs kept
  if let some constructor := source.find? (fun raw => firstFunctionField M raw.body) then
    throw (.functionField constructor.name "")
  match IndexedInductive.admitList? source with
  | some admitted => return admitted
  | none => throw .duplicateConstructors

/-! ## The code-equation exporter's constructor table -/

/-- The run-time use of each field a constructor code lists: a data field as
its sort records, a recursive field as the family (an inductive proposition's
values are proofs, erased). -/
def codeRelevance {M : Model} (familyRelevant : Bool) :
    {context : List DataSort} → Code (M.interface) context → List Bool
  | _, .result _ => []
  | _, .data sort body => sort.relevant :: codeRelevance familyRelevant body
  | _, .recursive _ rest => familyRelevant :: codeRelevance familyRelevant rest

/-- Interleave a code's fields with its guards at their positions; a guard
is never kept. -/
def withGuards (fields : List Bool) (guards : List Guard) : List Bool :=
  let total := fields.length + guards.length
  let rec go : Nat → List Bool → List Bool
    | 0, _ => []
    | fuel + 1, rest =>
      if guards.any (·.position == total - (fuel + 1)) then false :: go fuel rest
      else rest.headD false :: go fuel rest.tail
  go total fields

/-- For each constructor of an admitted reading, the fields the code-equation
exporter keeps, read from the inventory alone. -/
def inventoryKept (reading : Reading) : Option (List (String × List Bool)) :=
  match admit Model.syntactic reading.family reading.proofFields reading.keptFields,
        guards Model.syntactic reading.family reading.proofFields with
  | .ok admitted, .ok allGuards =>
      let familyRelevant := reading.family.sort != .name "Prop"
      some ((admitted.constructors.zip allGuards).map fun (constructor, guardsHere) =>
        (constructor.name, withGuards (codeRelevance familyRelevant constructor.body) guardsHere))
  | _, _ => none

/-- The fields the code-equation exporter keeps for a constructor: from the
inventory of its family when the profile admits it, otherwise the Reader's
erasure. -/
def constructorFields (c : Lean.Name) : Lean.Meta.MetaM (List Bool) := do
  let some (.ctorInfo info) := (← Lean.getEnv).find? c | keptConstructorFields c
  match ← read info.induct with
  | .error _ => keptConstructorFields c
  | .ok reading =>
    match (inventoryKept reading).bind (·.lookup c.toString) with
    | some kept => return kept
    | none => keptConstructorFields c

end Mettapedia.Languages.Lean.Declarations.Profile
