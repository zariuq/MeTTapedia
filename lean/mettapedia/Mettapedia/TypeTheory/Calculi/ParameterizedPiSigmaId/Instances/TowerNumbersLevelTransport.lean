import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerLevelSubstitution
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.InductiveHeadMapping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableSourceTransport

/-!
# Actual computing natural-number packages under level substitution

All declaration types and all recursor equations are transported by the
constructed morphism. The number type stays in its lowest universe; the
dependent recursor's result universe changes with its level expression.
Complete source-checking certificates are transported with their annotations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.TowerNumbersModel

open Mettapedia.TypeTheory.UniverseLevel
open ExecutableWrittenChecking

theorem constantType_substLevels (substitution : Nat → LevelExpr Nat)
    (level : LevelExpr Nat) (name : DeclName) :
    (constantType level name).map (Tm.mapHead (LevelTower.substLevelsHead substitution)) =
      constantType (level.subst substitution) name := by
  unfold constantType
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  split <;> first | rfl | skip
  split <;> rfl

theorem levelSubstitution (substitution : Nat → LevelExpr Nat) (level : LevelExpr Nat) :
    (rules level).Morphism (rules (level.subst substitution))
      (LevelTower.substLevelsHead substitution) where
  headTyping := by
    intro h u known
    cases known with
    | legacyGround => exact .legacyGround
    | sort _ => exact .sort _
  isUniverse := by
    intro h known
    cases known with
    | sort _ => exact .sort _
  join := by
    intro u v w known
    cases known with
    | sorts _ _ => exact .sorts _ _
  cumulative := by
    intro lower upper known
    cases lower with
    | legacyGround => exact known.elim
    | sort first =>
        cases upper with
        | legacyGround => exact known.elim
        | sort second =>
            intro valuation
            simpa only [LevelTower.substLevelsHead, LevelExpr.eval_subst] using
              known (fun index => (substitution index).eval valuation)
  headEq := by
    intro first second known
    cases first with
    | legacyGround =>
        cases second with
        | legacyGround => exact known
        | sort _ => exact known.elim
    | sort a =>
        cases second with
        | legacyGround => exact known.elim
        | sort b =>
            intro valuation
            simpa only [LevelTower.substLevelsHead, LevelExpr.eval_subst] using
              known (fun index => (substitution index).eval valuation)
  constantType := by
    intro name type known
    change constantType level name = some type at known
    have mapped := constantType_substLevels substitution level name
    rw [known, Option.map_some] at mapped
    exact mapped.symm
  computation := by
    intro n left right step
    change IotaStep numRec ctors left right at step
    have mapped := IotaStep.mapHead (LevelTower.substLevelsHead substitution) step
    change IotaStep numRec ctors _ _
    simpa only [mapConstructors, ctors, List.map_cons, List.map_nil, Field.mapHead] using mapped

theorem annotated_substLevels {n : Nat} {context : Ctx Tower.Head n} {term : ATm Tower.Head n}
    {type : Tm Tower.Head n} {level : LevelExpr Nat} (substitution : Nat → LevelExpr Nat)
    (typed : ATyped (rules level) context term type) :
    ATyped (rules (level.subst substitution))
      (context.mapHead (LevelTower.substLevelsHead substitution))
      (term.mapHead (LevelTower.substLevelsHead substitution))
      (type.mapHead (LevelTower.substLevelsHead substitution)) :=
  typed.mapHead (levelSubstitution substitution level)

def transportSource {n : Nat} {context : SourceContext Tower.Head n} {term type : ATm Tower.Head n}
    {level : LevelExpr Nat} (substitution : Nat → LevelExpr Nat)
    (certificate : SourceJudgmentCertificate (rules level) context term type) :
    SourceJudgmentCertificate (rules (level.subst substitution))
      (context.mapHead (LevelTower.substLevelsHead substitution))
      (term.mapHead (LevelTower.substLevelsHead substitution))
      (type.mapHead (LevelTower.substLevelsHead substitution)) :=
  certificate.mapHead (levelSubstitution substitution level)

end TypedEquality.Normalization.TowerNumbersModel
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
