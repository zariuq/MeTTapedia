import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSchemaInstantiation
import Mettapedia.TypeTheory.UniverseLevel.AssignmentResolution

/-!
# Constructed schema formation and capture controls

The two-parameter function schema has a checked implementing body in the
computing number model. Every tuple of levels yields a formed annotated
instance. The physical controls distinguish simultaneous arguments, recursive
assignments, argument permutations and the lowest default instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSchemaControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ExecutableWrittenChecking
open Mettapedia.TypeTheory.UniverseLevel
open NativeDependentSourceWire NativeDependentLevelSubstitution NativeDependentSchemaInstantiation

def polymorphic : Schema := ⟨"poly", 2,
  .pi (.head (.sort (.param 0))) (.head (.sort (.param 1)))⟩

def implementingBody : ATm Tower.Head 0 :=
  .lamTyped (.head (.sort (.param 0))) (.const TowerNumbersModel.num)

def formationLevel : Tower.Head := .sort (.max (.succ (.param 0)) (.succ (.param 1)))

theorem polymorphic_formed :
    ATyped (TowerNumbersModel.rules (.const 0)) .nil polymorphic.type (.head formationLevel) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem implementingBody_typed :
    ATyped (TowerNumbersModel.rules (.const 0)) .nil implementingBody polymorphic.type.erase := by
  refine .lamTyped (.headType (.sort _)) (.sort _) (.refl (.headType (.sort _)))
    polymorphic_formed.erase (.sort _) ?_
  exact .cumul
    (.const (TowerNumbersModel.declaredNum (.const 0))
      (.headType (LevelTower.HeadTyping.sort (.const 0))) (.sort _))
    (fun valuation => Nat.zero_le ((LevelExpr.param 1).eval valuation))

def sourceCertificate : SourceJudgmentCertificate (TowerNumbersModel.rules (.const 0))
    .nil implementingBody polymorphic.type where
  contextChecked := .nil
  expectedUniverse := formationLevel
  expectedIsUniverse := .sort _
  expectedChecked := polymorphic_formed
  termChecked := implementingBody_typed

/-- Construction at every tuple of level expressions, including open ones. -/
def allInstances (arguments : List (LevelExpr Nat)) :
    SourceJudgmentCertificate (TowerNumbersModel.rules (.const 0)) .nil
      (implementingBody.mapHead (LevelTower.substLevelsHead (argumentsSubstitution arguments)))
      (polymorphic.instantiate arguments) :=
  TowerNumbersModel.transportSource (argumentsSubstitution arguments) sourceCertificate

/-- The family depends on both the supplied type and its element. -/
def dependentIdentityType (level : LevelExpr Nat) : ATm Tower.Head 0 :=
  .pi (.head (.sort level)) (.pi (.var 0) (.id (.var 1) (.var 0) (.var 0)))

def dependentIdentityBody (level : LevelExpr Nat) : ATm Tower.Head 0 :=
  .lamTyped (.head (.sort level)) (.lamTyped (.var 0) (.refl (.var 0)))

def dependentFormationLevel (level : LevelExpr Nat) : Tower.Head :=
  .sort (.max (.succ level) (.max level level))

theorem dependentIdentity_formed (level : LevelExpr Nat) :
    ATyped (TowerNumbersModel.rules (.const 0)) .nil (dependentIdentityType level)
      (.head (dependentFormationLevel level)) :=
  .piForm (.headType (.sort _)) (.sort _)
    (.piForm (.var 0) (.sort _) (.idForm (.var 1) (.sort _) (.var 0) (.var 0))
      (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)

theorem dependentIdentity_typed (level : LevelExpr Nat) :
    ATyped (TowerNumbersModel.rules (.const 0)) .nil (dependentIdentityBody level)
      (dependentIdentityType level).erase := by
  refine .lamTyped (.headType (.sort _)) (.sort _) (.refl (.headType (.sort _)))
    (dependentIdentity_formed level).erase (.sort _) ?_
  refine .lamTyped (u := .sort (.max level level))
    (.var 0) (.sort _) (.refl (.var 0)) ?_ (.sort _) (.reflIntro (.var 0))
  exact .piForm (.var 0) (.sort _) (.idForm (.var 1) (.sort _) (.var 0) (.var 0))
    (.sort _) (.sorts _ _)

def dependentCertificate (level : LevelExpr Nat) :
    SourceJudgmentCertificate (TowerNumbersModel.rules (.const 0)) .nil
      (dependentIdentityBody level) (dependentIdentityType level) where
  contextChecked := .nil
  expectedUniverse := dependentFormationLevel level
  expectedIsUniverse := .sort _
  expectedChecked := dependentIdentity_formed level
  termChecked := dependentIdentity_typed level

/-- A genuinely dependent checked consumer survives every level instance. -/
def allDependentInstances (substitution : Nat → LevelExpr Nat) (level : LevelExpr Nat) :
    SourceJudgmentCertificate (TowerNumbersModel.rules (.const 0)) .nil
      ((dependentIdentityBody level).mapHead (LevelTower.substLevelsHead substitution))
      ((dependentIdentityType level).mapHead (LevelTower.substLevelsHead substitution)) :=
  TowerNumbersModel.transportSource substitution (dependentCertificate level)

def canonicalEntry : Wire := .application "PrimeCtxDecl"
  [key "poly" [.param 0, .param 1],
    .application "Pi" [.application "Sort" [encodeLevel (.param 0)],
      .application "Sort" [encodeLevel (.param 1)]], .symbol "PrimeCtxNil"]

theorem entry_is_lowered : polymorphic.lower (.symbol "PrimeCtxNil") = some canonicalEntry := rfl

theorem every_full_instance_lowering (arguments : List (LevelExpr Nat)) (two : arguments.length = 2) :
    lookupEntry (key "poly" arguments) canonicalEntry =
      NativeDependentSourceWire.lower (polymorphic.instantiate arguments) :=
  lookupEntry_lower_explicit polymorphic (.symbol "PrimeCtxNil") arguments two entry_is_lowered

theorem caller_parameter_preserved :
    lookupEntry (key "poly" [.param 1, .const 0]) canonicalEntry =
      some (.application "Pi" [.application "Sort" [encodeLevel (.param 1)],
        .application "Sort" [encodeLevel (.const 0)]]) := by decide +kernel

theorem caller_parameter_not_captured :
    lookupEntry (key "poly" [.param 1, .const 0]) canonicalEntry ≠
      some (.application "Pi" [.application "Sort" [encodeLevel (.const 0)],
        .application "Sort" [encodeLevel (.const 0)]]) := by decide +kernel

theorem permuted_arguments_preserved :
    lookupEntry (key "poly" [.param 1, .param 0]) canonicalEntry =
      some (.application "Pi" [.application "Sort" [encodeLevel (.param 1)],
        .application "Sort" [encodeLevel (.param 0)]]) := by decide +kernel

theorem nested_argument_preserved :
    lookupEntry (key "poly" [.succ (.param 1), .const 0]) canonicalEntry =
      some (.application "Pi" [.application "Sort" [encodeLevel (.succ (.param 1))],
        .application "Sort" [encodeLevel (.const 0)]]) := by decide +kernel

theorem own_index_argument_preserved :
    lookupEntry (key "poly" [.succ (.param 0), .const 0]) canonicalEntry =
      some (.application "Pi" [.application "Sort" [encodeLevel (.succ (.param 0))],
        .application "Sort" [encodeLevel (.const 0)]]) := by decide +kernel

theorem lowest_arguments : lookupEntry (key "poly" []) canonicalEntry =
    some (.application "Pi" [.application "Sort" [encodeLevel (.const 0)],
      .application "Sort" [encodeLevel (.const 0)]]) := by decide +kernel

theorem wrong_arity_not_instantiated :
    lookupEntry (key "poly" [.const 0]) canonicalEntry = none := by decide +kernel

theorem unknown_name_not_instantiated :
    lookupEntry (key "other" [.const 0, .const 0]) canonicalEntry = none := by decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSchemaControls
