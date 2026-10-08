import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentLevelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbersLevelTransport

/-!
# Canonical declaration schemas and their instantiated source contracts

A schema has its own level-parameter slots. Arguments supplied by a caller
are substituted simultaneously into its written type. The independent physical
entry lookup agrees with that scoped operation on lowered canonical schemas.
Omitting all arguments selects the lowest instance, as the native lookup does.
This adapter does not certify native allocation, budgets or compiled execution.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSchemaInstantiation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Normalization
open Mettapedia.TypeTheory.UniverseLevel
open NativeDependentSourceWire NativeDependentLevelSubstitution

structure Schema where
  name : String
  parameterCount : Nat
  type : ATm Tower.Head 0

def argumentsSubstitution (arguments : List (LevelExpr Nat)) (index : Nat) : LevelExpr Nat :=
  arguments[index]?.getD (.param index)

def key (name : String) (arguments : List (LevelExpr Nat)) : Wire :=
  .application "DeclConst" (.symbol name :: arguments.map encodeLevel)

def Schema.boundArguments (schema : Schema) : List (LevelExpr Nat) :=
  (List.range schema.parameterCount).map LevelExpr.param

def Schema.lower (schema : Schema) (rest : Wire) : Option Wire := do
  return .application "PrimeCtxDecl" [key schema.name schema.boundArguments,
    ← NativeDependentSourceWire.lower schema.type, rest]

def Schema.instantiate (schema : Schema) (arguments : List (LevelExpr Nat)) : ATm Tower.Head 0 :=
  schema.type.mapHead (LevelTower.substLevelsHead (argumentsSubstitution arguments))

def decodeArguments : List Wire → Option (List (LevelExpr Nat))
  | [] => some []
  | argument :: rest => do return (← decodeLevel argument) :: (← decodeArguments rest)

@[simp] theorem decodeArguments_encoded (arguments : List (LevelExpr Nat)) :
    decodeArguments (arguments.map encodeLevel) = some arguments := by
  induction arguments <;> simp_all [decodeArguments]

def chooseArguments (count : Nat) (arguments : List (LevelExpr Nat)) :
    Option (List (LevelExpr Nat)) :=
  if arguments = [] then some (List.replicate count (.const 0))
  else if arguments.length = count then some arguments else none

theorem chooseArguments_explicit (count : Nat) (arguments : List (LevelExpr Nat))
    (length : arguments.length = count) : chooseArguments count arguments = some arguments := by
  cases arguments with
  | nil => simp only [List.length_nil] at length; subst count; rfl
  | cons argument rest => simp [chooseArguments, length]

@[simp] theorem chooseArguments_lowest (count : Nat) :
    chooseArguments count [] = some (List.replicate count (.const 0)) := rfl

/-- Lookup of one canonical closed declaration entry. Local-context lifting
and search through the rest of a signature are separate operations. -/
def lookupEntry (wanted entry : Wire) : Option Wire := do
  match wanted, entry with
  | .application "DeclConst" (.symbol name :: arguments),
      .application "PrimeCtxDecl"
        [.application "DeclConst" (.symbol declaredName :: parameters), type, _] =>
      if name ≠ declaredName then none else
      if parameters ≠ (List.range parameters.length).map (fun index => encodeLevel (.param index))
        then none else do
        let decoded ← decodeArguments arguments
        let selected ← chooseArguments parameters.length decoded
        return transform (argumentsSubstitution selected) type
  | _, _ => none

theorem lookupEntry_lower_explicit (schema : Schema) (rest : Wire)
    (arguments : List (LevelExpr Nat)) (length : arguments.length = schema.parameterCount)
    {wire : Wire} (lowered : schema.lower rest = some wire) :
    lookupEntry (key schema.name arguments) wire =
      NativeDependentSourceWire.lower (schema.instantiate arguments) := by
  cases typed : NativeDependentSourceWire.lower schema.type with
  | none => simp [Schema.lower, typed] at lowered
  | some typeWire =>
      simp [Schema.lower, typed] at lowered
      subst wire
      simp [lookupEntry, key, Schema.boundArguments, List.map_map, decodeArguments_encoded,
        chooseArguments_explicit _ _ length, Schema.instantiate, transform_lower, typed]

theorem lookupEntry_lower_lowest (schema : Schema) (rest : Wire)
    {wire : Wire} (lowered : schema.lower rest = some wire) :
    lookupEntry (key schema.name []) wire = NativeDependentSourceWire.lower
      (schema.instantiate (List.replicate schema.parameterCount (.const 0))) := by
  cases typed : NativeDependentSourceWire.lower schema.type with
  | none => simp [Schema.lower, typed] at lowered
  | some typeWire =>
      simp [Schema.lower, typed] at lowered
      subst wire
      simp [lookupEntry, key, Schema.boundArguments, List.map_map, decodeArguments,
        Schema.instantiate, transform_lower, typed]

/-- A constructed computing-model instance: an annotated schema type checked
in the number package remains checked at every tuple of level arguments. -/
theorem instantiated_formation {schema : Schema} {head : Tower.Head}
    {level : LevelExpr Nat} (arguments : List (LevelExpr Nat))
    (typed : TypedEquality.ATyped (TowerNumbersModel.rules level) .nil schema.type (.head head)) :
    TypedEquality.ATyped
      (TowerNumbersModel.rules (level.subst (argumentsSubstitution arguments))) .nil
      (schema.instantiate arguments)
      (.head (LevelTower.substLevelsHead (argumentsSubstitution arguments) head)) := by
  simpa only [Ctx.mapHead, Tm.mapHead, Schema.instantiate] using
    TowerNumbersModel.annotated_substLevels (argumentsSubstitution arguments) typed

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSchemaInstantiation
