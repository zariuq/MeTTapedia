import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.UniverseProfiles
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ExecutableChecking

/-!
# Constructed primitive choices for cumulative levels

The algorithm chooses the actual successor of each explicit level and the
maximum of the two formation levels. These are constructions over every level
order, including its symbolic parameters. No successor, join or universe
recognition certificate is supplied by the caller.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Normalization.ExecutableTowerChoices

open Mettapedia.TypeTheory.UniverseLevel

variable {L : Type} [LevelOrder L]

def headTarget : LevelTower.Head L → LevelTower.Head L
  | .legacyGround => .sort LevelTower.zero
  | .sort level => .sort (.succ level)

def typing (head : LevelTower.Head L) :
    {target : LevelTower.Head L // LevelTower.HeadTyping head target} :=
  match head with
  | .legacyGround => ⟨.sort LevelTower.zero, .legacyGround⟩
  | .sort level => ⟨.sort (.succ level), .sort level⟩

@[simp] theorem typing_val (head : LevelTower.Head L) : (typing head).val = headTarget head := by
  cases head <;> rfl

theorem typing_exact (head target : LevelTower.Head L) :
    LevelTower.HeadTyping head target ↔ target = headTarget head := by
  constructor
  · intro derivation; cases derivation <;> rfl
  · intro same; subst target; simpa only [typing_val] using (typing head).property

def join (first second : LevelTower.Head L) :
    Option {result : LevelTower.Head L // LevelTower.Join first second result} :=
  match first, second with
  | .sort u, .sort v => some ⟨.sort (.max u v), .sorts u v⟩
  | _, _ => none

instance universeDecidable (head : LevelTower.Head L) :
    Decidable (LevelTower.IsUniverse head) := by
  cases head with
  | legacyGround => exact .isFalse (by intro impossible; cases impossible)
  | sort level => exact .isTrue (.sort level)

def choices : ExecutableChecking.HeadChoices (LevelTower.rules L) where
  typing head := some (typing head)
  join := join

omit [LevelOrder L] in
@[simp] theorem join_sorts (u v : LevelExpr L) :
    (join (.sort u) (.sort v)).map Subtype.val = some (.sort (.max u v)) := rfl

omit [LevelOrder L] in
@[simp] theorem join_left_ground (head : LevelTower.Head L) :
    join .legacyGround head = none := by cases head <;> rfl

omit [LevelOrder L] in
@[simp] theorem join_right_ground (head : LevelTower.Head L) :
    join head .legacyGround = none := by cases head <;> rfl

end TypedEquality.Normalization.ExecutableTowerChoices
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
