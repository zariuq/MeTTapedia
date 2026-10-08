import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceWire
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedHeadMapping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLevelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSourceTransport

/-!
# Level substitution on physical annotated-source wires

The physical operation traverses syntax and substitutes a `LevelParam` node.
The scoped operation independently maps universe heads of `ATm`. Their
agreement retains lambda domains and commutes with local binder substitution.
The source fragment here has monomorphic declaration names. Bound parameters
in declaration schemas and admission of such schemas are separate contracts.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentLevelSubstitution

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Mettapedia.TypeTheory.UniverseLevel
open NativeDependentSourceWire
open TypedEquality.Normalization.ExecutableWrittenChecking

mutual

def transform (substitution : Nat → LevelExpr Nat) : Wire → Wire
  | .application name arguments =>
      if name == "LevelParam" then match arguments with
        | [.natural index] => encodeLevel (substitution index)
        | _ => .application name (transformList substitution arguments)
      else .application name (transformList substitution arguments)
  | other => other

def transformList (substitution : Nat → LevelExpr Nat) : List Wire → List Wire
  | [] => []
  | term :: terms => transform substitution term :: transformList substitution terms

end

@[simp] theorem transform_level (substitution : Nat → LevelExpr Nat) (level : LevelExpr Nat) :
    transform substitution (encodeLevel level) = encodeLevel (level.subst substitution) := by
  induction level <;>
    simp_all only [encodeLevel, transform, transformList, LevelExpr.subst,
      String.reduceBEq, Bool.false_eq_true, ↓reduceIte]

theorem transform_encode (substitution : Nat → LevelExpr Nat) (raw : Raw) :
    encode (raw.mapHead (LevelTower.substLevelsHead substitution)) =
      (encode raw).map (transform substitution) := by
  induction raw with
  | const name => cases named : nameText name <;>
      simp only [encode, NativeSyntax.Raw.mapHead, named, transform, transformList,
        Option.bind_none, Option.bind_some, Option.pure_def, Option.bind_eq_bind,
        Option.map_none, Option.map_some, String.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  | head value => cases value <;> simp only [encode, NativeSyntax.Raw.mapHead,
      LevelTower.substLevelsHead, transform, transformList, transform_level,
      Option.map_some, String.reduceBEq, Bool.false_eq_true, ↓reduceIte]
  | _ => simp_all only [encode, NativeSyntax.Raw.mapHead, transform, transformList,
      Option.bind_map, Option.map_bind, Option.map_some, Option.pure_def,
      Option.bind_eq_bind, Function.comp_def, String.reduceBEq, Bool.false_eq_true, ↓reduceIte]

theorem transform_lower {n : Nat} (substitution : Nat → LevelExpr Nat) (source : ATm Tower.Head n) :
    lower (source.mapHead (LevelTower.substLevelsHead substitution)) =
      (lower source).map (transform substitution) := by
  simp only [lower, ← NativeSyntax.mapHead_encode, transform_encode]

theorem transform_decodes {n : Nat} (substitution : Nat → LevelExpr Nat)
    {source : ATm Tower.Head n} {wire : Wire} (lowered : lower source = some wire) :
    decodeScoped n (transform substitution wire) =
      some (source.mapHead (LevelTower.substLevelsHead substitution)) := by
  apply lower_decode
  rw [transform_lower, lowered, Option.map_some]

/-- Level substitution cannot change a source's local variable scope. -/
theorem scope_stable (substitution : Nat → LevelExpr Nat) (n : Nat) (raw : Raw) :
    NativeSyntax.checkScope n (raw.mapHead (LevelTower.substLevelsHead substitution)) =
      NativeSyntax.checkScope n raw := NativeSyntax.checkScope_mapHead _ _ _

theorem binder_substitution_commutes {n : Nat} (substitution : Nat → LevelExpr Nat)
    (argument : ATm Tower.Head n) (body : ATm Tower.Head (n+1)) :
    lower ((ATm.inst0 argument body).mapHead (LevelTower.substLevelsHead substitution)) =
      lower (ATm.inst0 (argument.mapHead (LevelTower.substLevelsHead substitution))
        (body.mapHead (LevelTower.substLevelsHead substitution))) := by
  rw [ATm.mapHead_inst0]

theorem transform_contextOver (substitution : Nat → LevelExpr Nat) (base : Wire)
    {n : Nat} (context : SourceContext Tower.Head n) :
    lowerContextOver (transform substitution base)
      (context.mapHead (LevelTower.substLevelsHead substitution)) =
      (lowerContextOver base context).map (transform substitution) := by
  induction context with
  | nil => simp only [lowerContextOver, SourceContext.mapHead, Option.map_some]
  | snoc previous domain ih =>
      simp only [lowerContextOver, SourceContext.mapHead, transform_lower, ih,
        transform, transformList, Option.bind_map, Option.map_bind, Option.map_some,
        Option.pure_def, Option.bind_eq_bind, Function.comp_def,
        String.reduceBEq, Bool.false_eq_true, ↓reduceIte]

theorem transform_scopedOver (substitution : Nat → LevelExpr Nat) (base : Wire)
    {n : Nat} (context : SourceContext Tower.Head n) (source : ATm Tower.Head n) :
    lowerScopedOver (transform substitution base)
      (context.mapHead (LevelTower.substLevelsHead substitution))
      (source.mapHead (LevelTower.substLevelsHead substitution)) =
      (lowerScopedOver base context source).map (transform substitution) := by
  simp only [lowerScopedOver, transform_contextOver, transform_lower, transform, transformList,
    Option.bind_map, Option.map_bind, Option.map_some, Option.pure_def,
    Option.bind_eq_bind, Function.comp_def, String.reduceBEq, Bool.false_eq_true, ↓reduceIte]

theorem transform_declarations (substitution : Nat → LevelExpr Nat)
    (declarations : List (DeclName × ATm Tower.Head 0)) :
    lowerDeclarations (declarations.map (fun declaration =>
      (declaration.1, declaration.2.mapHead (LevelTower.substLevelsHead substitution)))) =
      (lowerDeclarations declarations).map (transform substitution) := by
  induction declarations with
  | nil => simp only [lowerDeclarations, transform, List.map_nil, Option.map_some]
  | cons declaration rest ih =>
      cases named : nameText declaration.1 <;>
        simp only [lowerDeclarations, named, transform_lower, ih, transform, transformList,
          Option.bind_map, Option.map_bind, Option.map_some, Option.map_none,
          Option.bind_some, Option.bind_none, Option.pure_def, Option.bind_eq_bind,
          Function.comp_def, List.map_cons, String.reduceBEq, Bool.false_eq_true, ↓reduceIte]

def sample : ATm Tower.Head 0 :=
  .lamTyped (.head (.sort (.param 0))) (.var 0)

def chosenLevels : Nat → LevelExpr Nat := fun index => .max (.param (index+1)) (.const 2)

theorem written_domain_substituted :
    decodeScoped 0 (transform chosenLevels
      (.application "Lam" [.application "Sort" [encodeLevel (.param 0)],
        .application "idx" [.natural 0]])) =
      some (.lamTyped (.head (.sort (.max (.param 1) (.const 2)))) (.var 0)) := by
  exact transform_decodes chosenLevels (source := sample) rfl

theorem local_index_is_not_level_parameter :
    transform chosenLevels (.application "idx" [.natural 0]) = .application "idx" [.natural 0] := by
  decide +kernel

theorem ignored_domain_substitution_is_wrong :
    transform chosenLevels
      (.application "Lam" [.application "Sort" [encodeLevel (.param 0)],
        .application "idx" [.natural 0]]) ≠
      .application "Lam" [.application "Sort" [encodeLevel (.param 0)],
        .application "idx" [.natural 0]] := by decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentLevelSubstitution
