import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# One definition at two universe levels, on the dependent full step

The tree's terms carry no level arguments (`Presentation.Tm.const` names a constant, nothing more),
and abstractions carry no domain annotation. So the code of the polymorphic identity,
`polyCode = λA. λx. x`, is typed at `Π (A : U_l). A → A` for every level `l`, and one code serves at
every level.

**Used at two levels** (`two_levels_admitted`). One firing makes two rows with the same function:
`polyCode Ground : Ground → Ground` (level 0, by cumulativity `U0 ≤ U1`) and
`polyCode U0 : U0 → U0` (level 1). It is admitted. The same code is typed at level 2 as well
(`polyCode_at_two_typed`).

**Matching across levels is refused** (`cross_level_take_refused`). Rows are typed terms, and the
knowledge equates two typed terms only when their types are equal. A row holding `polyCode` at
`Π (A : U1). A → A` is not matched by a take pattern holding the same code at
`Π (A : U2). A → A`: the information has no solution, since the domains `U1` and `U2` are different
heads (`cross_level_unsolvable`). The take with the pattern at the row's own level is admitted
(`same_level_take_admitted`). A level parameter does not help: `U_l` for a level parameter `l` is
not `U1` (`param_level_unsolvable`), since level parameters range over every valuation.

So a polymorphic definition can be used at many levels, but its uses at different levels are
different terms for the knowledge: a program that matches on a polymorphic value needs level
variables that the knowledge can solve, or matching on erased terms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ProgrammingOnTheStep.UniverseLevels

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull Interface.DependentFull.Controls

/-! ## The polymorphic identity -/

/-- `U_l` as a head. -/
abbrev sortAt (l : LevelExpr Nat) : Tower.Head := .sort l

def level1 : LevelExpr Nat := .succ Tower.zero
def level2 : LevelExpr Nat := .succ (.succ Tower.zero)

/-- `λA. λx. x`, with no annotation. -/
def polyCode {n : Nat} : Tower.Tm n := .lam (.lam (.var 0))

/-- `Π (A : U_l). A → A`. -/
def polyType {n : Nat} (l : LevelExpr Nat) : Tower.Tm n := .pi (.head (sortAt l)) (.pi (.var 0) (.var 1))

/-- The level at which `Π (A : U_l). A → A` is formed. -/
def polyLevel (l : LevelExpr Nat) : LevelExpr Nat := .max (.succ l) (.max l l)

theorem polyType_formed {n : Nat} (Γ : Tower.Ctx n) (l : LevelExpr Nat) :
    Typed Tower.rules Γ (polyType l) (.head (sortAt (polyLevel l))) := by
  have inner : Typed Tower.rules (.snoc (.snoc Γ (.head (sortAt l))) (.var 0)) (.var 1) (.head (sortAt l)) :=
    Derivable.var 1
  have arrow : Typed Tower.rules (.snoc Γ (.head (sortAt l))) (.pi (.var 0) (.var 1))
      (.head (sortAt (.max l l))) :=
    .piForm (Derivable.var 0) (.sort _) inner (.sort _) (.sorts _ _)
  exact .piForm (.headType (.sort _)) (.sort _) arrow (.sort _) (.sorts _ _)

/-- **The code is typed at every level.** -/
theorem polyCode_typed {n : Nat} (Γ : Tower.Ctx n) (l : LevelExpr Nat) :
    Typed Tower.rules Γ polyCode (polyType l) := by
  have arrow : Typed Tower.rules (.snoc Γ (.head (sortAt l))) (.pi (.var 0) (.var 1))
      (.head (sortAt (.max l l))) :=
    .piForm (Derivable.var 0) (.sort _) (Derivable.var 1) (.sort _) (.sorts _ _)
  have body : Typed Tower.rules (.snoc Γ (.head (sortAt l))) (.lam (.var 0)) (.pi (.var 0) (.var 1)) :=
    .lamIntro arrow (.sort _) (Derivable.var 0)
  exact .lamIntro (polyType_formed Γ l) (.sort _) body

/-! ## Two uses at two levels, one firing -/

theorem ground_at_one {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ ground (.head (sortAt level1)) := by
  have raise : Tower.rules.cumulative (.sort Tower.zero) (sortAt level1) := by
    change LevelTower.Cumulative (.sort Tower.zero) (.sort (.succ Tower.zero))
    intro valuation
    simp [LevelExpr.eval]
  exact .cumul (ground_typed Γ) raise

/-- `polyCode Ground : Ground → Ground`: the use at level 0. -/
theorem use_ground_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ (.app polyCode ground) arrow := by
  have typed := Derivable.appElim (polyCode_typed Γ level1) (ground_at_one Γ)
  exact typed

/-- `U0 → U0`. -/
def smallEndo {n : Nat} : Tower.Tm n := .pi (.head (.sort Tower.zero)) (.head (.sort Tower.zero))

theorem smallEndo_formed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ smallEndo (.head (sortAt (.max level1 level1))) :=
  .piForm (.headType (.sort _)) (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- `polyCode U0 : U0 → U0`: the use at level 1. -/
theorem use_universe_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ (.app polyCode (.head (.sort Tower.zero))) smallEndo := by
  have typed := Derivable.appElim (polyCode_typed Γ level1)
    (Derivable.headType (R := Tower.rules) (Γ := Γ) (LevelTower.HeadTyping.sort Tower.zero))
  exact typed

/-- **The same code at level 2**: `polyCode U1 : U1 → U1`. -/
theorem polyCode_at_two_typed {n : Nat} (Γ : Tower.Ctx n) :
    Typed Tower.rules Γ (.app polyCode (.head (sortAt level1)))
      (.pi (.head (sortAt level1)) (.head (sortAt level1))) := by
  have typed := Derivable.appElim (polyCode_typed Γ level2)
    (Derivable.headType (R := Tower.rules) (Γ := Γ) (LevelTower.HeadTyping.sort level1))
  exact typed

/-- The empty frame with no rows. -/
def emptyRows : State Tower.rules Nat :=
  ⟨empty Tower.rules, [], ∅, fun _ => ⟨smallUniverse _, ⟨ground, ground_typed _⟩⟩⟩

/-- `Ground → Ground`, as a formed type of the empty frame. -/
def arrowType : TypeOver (empty Tower.rules) := ⟨arrow, .sort Tower.zero, .sort _, arrow_typed _⟩

/-- `U0 → U0`, as a formed type of the empty frame. -/
def smallEndoType : TypeOver (empty Tower.rules) :=
  ⟨smallEndo, sortAt (.max level1 level1), .sort _, smallEndo_formed _⟩

/-- **Make both uses**: row `0 : polyCode Ground : Ground → Ground` and row
`1 : polyCode U0 : U0 → U0`. -/
def twoLevelsFiring : Firing setting.levels emptyRows where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, ⟨arrowType, .app polyCode ground⟩), (1, ⟨smallEndoType, .app polyCode (.head (.sort Tower.zero))⟩)]
  tells := []
  guards := []
  queries := []

theorem twoLevelsFiring_information : twoLevelsFiring.information = [] := rfl

/-- **One definition, used at two levels, by one admitted firing.** -/
theorem two_levels_admitted : (step setting.levels Nat).Admits twoLevelsFiring := by
  refine ⟨⟨List.nodup_nil, by decide, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff twoLevelsFiring).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩,
    ⟨empty Tower.rules, 𝟙 _, by rw [twoLevelsFiring_information]; exact Frames.models_nil _⟩, ?_⟩
  · rcases List.mem_cons.mp member with rfl | rest
    · exact use_ground_typed _
    · obtain rfl := List.mem_singleton.mp rest
      exact use_universe_typed _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

/-! ## Matching across levels -/

/-- `polyCode` at `Π (A : U_l). A → A`, as a typed term of the empty frame. -/
def polyRow (l : LevelExpr Nat) : TotalTerm (empty Tower.rules) :=
  ⟨⟨polyType l, sortAt (polyLevel l), .sort _, polyType_formed _ l⟩, ⟨polyCode, polyCode_typed _ l⟩⟩

/-- One row, `0 : polyCode` at level 1. -/
def polyState : State Tower.rules Nat := ⟨empty Tower.rules, [], {0}, fun _ => polyRow level1⟩

/-- Take row `0` with the pattern `polyCode` at level `l`. -/
def takeAt (l : LevelExpr Nat) : Firing setting.levels polyState where
  helpers := .nil _
  taken := [0]
  read := []
  takes := [polyRow l]
  reads := []
  makes := []
  tells := []
  guards := []
  queries := []

theorem takeAt_information (l : LevelExpr Nat) :
    (takeAt l).information = [(polyRow l, (takeAt l).row 0)] := rfl

/-- The polymorphic types at two levels are equal types in no frame, when the levels differ at some
valuation. -/
theorem polyType_apart {n : Nat} {Γ : Tower.Ctx n} (formed : CtxFormed Tower.rules Γ) {l l' : LevelExpr Nat}
    (differ : ∃ ν : Nat → Nat, LevelExpr.eval ν l ≠ LevelExpr.eval ν l') :
    ¬ TypeEq Tower.rules Γ (polyType l) (polyType l') := by
  intro equal
  have domains := (TypeEq.pi_injective (TowerModel.facts (L := Nat)) equal formed).1
  rcases TypeEq.head_injective (TowerModel.facts (L := Nat)) domains formed with same | same
  · obtain ⟨ν, apart⟩ := differ
    cases same
    exact apart rfl
  · obtain ⟨ν, apart⟩ := differ
    exact apart (same ν)

/-- A take whose pattern's type is apart from its row's type has no solution. -/
theorem take_unsolvable {l : LevelExpr Nat} (differ : ∃ ν : Nat → Nat, LevelExpr.eval ν l ≠ LevelExpr.eval ν level1) :
    ¬ (frames setting.levels).Solvable (takeAt l).information := by
  rintro ⟨Δ, σ, solved⟩
  rw [takeAt_information] at solved
  have equation := solved _ (List.mem_singleton_self _)
  obtain ⟨types, -⟩ := (equivalent_iff setting.levels _ _).mp equation
  exact polyType_apart Δ.formed differ types

/-- **The same code at levels 1 and 2 has no common solution.** -/
theorem cross_level_unsolvable : ¬ (frames setting.levels).Solvable (takeAt level2).information :=
  take_unsolvable ⟨fun _ => 0, by simp [level2, level1, LevelExpr.eval]⟩

/-- **The take across levels is refused.** -/
theorem cross_level_take_refused : ¬ (step setting.levels Nat).Admits (takeAt level2) :=
  fun admitted => cross_level_unsolvable admitted.2.2.1

/-- **A level parameter is not level 1**: the type at `U_l` for a level parameter `l` meets the row
at no solution. -/
theorem param_level_unsolvable : ¬ (frames setting.levels).Solvable (takeAt (.param 0)).information :=
  take_unsolvable ⟨fun _ => 0, by simp [level1, LevelExpr.eval]⟩

/-- **The take at the row's own level is admitted.** -/
theorem same_level_take_admitted : (step setting.levels Nat).Admits (takeAt level1) := by
  refine ⟨⟨List.nodup_singleton _, List.nodup_nil, rfl, rfl, fun _ member => absurd member List.not_mem_nil⟩,
    (enabled_iff (takeAt level1)).mpr ⟨fun o member => ?_, fun _ member => absurd member List.not_mem_nil,
      fun _ _ readToo => absurd readToo List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩,
    ⟨empty Tower.rules, 𝟙 _, ?_⟩, ?_⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.mem_singleton_self 0
  · rw [takeAt_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    exact ((frames setting.levels).equivalence _).refl _
  · intro b τ _
    exact ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩

end ProgrammingOnTheStep.UniverseLevels

#print axioms ProgrammingOnTheStep.UniverseLevels.polyCode_typed
#print axioms ProgrammingOnTheStep.UniverseLevels.polyCode_at_two_typed
#print axioms ProgrammingOnTheStep.UniverseLevels.two_levels_admitted
#print axioms ProgrammingOnTheStep.UniverseLevels.cross_level_unsolvable
#print axioms ProgrammingOnTheStep.UniverseLevels.cross_level_take_refused
#print axioms ProgrammingOnTheStep.UniverseLevels.param_level_unsolvable
#print axioms ProgrammingOnTheStep.UniverseLevels.same_level_take_admitted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
