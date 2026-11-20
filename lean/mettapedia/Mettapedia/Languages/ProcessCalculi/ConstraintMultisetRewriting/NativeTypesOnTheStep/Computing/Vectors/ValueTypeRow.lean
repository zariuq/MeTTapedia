import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.RowsAfterMatch

/-!
# The typed interpreter's value type, on the converting step over the vectors package

The audit's typed interpreter returns `n : nat` from `eval tnat (lit n)`, and the answer never had
the declared type `val tnat` there, because `val` was a rigid constant. In the vectors package the
value type of a code is computed by the recursor of the numbers at level one, a large elimination:

`val code = num-rec (λ _. U0) num (λ _ X. X → X) code`, so `val 0 ≡ num` and
`val (k + 1) ≡ val k → val k` (`valC`, typed at `U0`: `valC_typed`).

**The literal row** `eval code (lit x) = x` is a firing of the converting step: its frame holds
`x : num` and, newest, the call's code; the match teaches `code ≐ zero`; it makes `x` at the call's
declared type `val code`. The row is not typed in its frame (`valRow_not_frameTyped`); the package's
computable settler solves the match and its executable conversion takes `val zero` to `num`, by kernel
evaluation (`val_decided`), so the computable converting step admits the row (`val_admitted`) and it is
typed after its match (`val_typedAfterMatch`).

**Control**: the same row, told `code ≐ 1` instead, makes `x : num` where the type is
`val 1 ≡ num → num`, and is refused for every settler (`valOne_refused`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (U0 numC zeroC succC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-! ## The value type -/

/-- The universe of level one, where the recursor's motives land. -/
abbrev U1 {n : Nat} : Tower.Tm n := .head (.sort level1)

/-- The motive `λ _. U0`. -/
abbrev valMotive {n : Nat} : Tower.Tm n := .lam U0

/-- The successor case `λ _ X. X → X`. -/
abbrev valStep {n : Nat} : Tower.Tm n := .lam (.lam (.pi (.var 0) (.var 1)))

/-- **The value type of a code**: `val 0 = num`, `val (k + 1) = val k → val k`. -/
abbrev valC {n : Nat} (code : Tower.Tm n) : Tower.Tm n := numRecAt valMotive numC valStep code

section Typing

variable {m : Nat} {Δ : Ctx Tower.Head m}

theorem valRec_typed : Typed pkg Δ (.const numRec) (liftClosed (recType num (.sort level1) ctors)) := by
  obtain ⟨w, hw, typed⟩ := TowerNumbersModel.recType_typed level1
  exact .const rfl (Derivable.mono (TowerVectorsModel.sub_numbers₂ level1) typed) hw

theorem valMotiveTy_typed :
    Typed pkg Δ (.pi numC U1) (.head (.sort (.max (.const 0) (.succ level1)))) :=
  .piForm D.num_typed (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

theorem valMotive_typed : Typed pkg Δ valMotive (.pi numC U1) :=
  .lamIntro valMotiveTy_typed (.sort _) (.headType (.sort _))

theorem valMotive_beta {t : Tower.Tm m} (typed : Typed pkg Δ t numC) :
    Equal pkg Δ (.app valMotive t) U0 U1 :=
  .betaPi valMotiveTy_typed (.sort _) (.headType (.sort _)) typed

theorem valZero_typed : Typed pkg Δ numC (.app valMotive zeroC) :=
  .conv D.num_typed (.symm (valMotive_beta D.zero_typed)) (.sort _)

theorem valStep_typed :
    Typed pkg Δ valStep (.pi numC (.pi (.app valMotive (.var 0)) (.app valMotive (succC (.var 1))))) := by
  have x1 : Typed pkg (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (.var 1) numC := .var 1
  have succX : Typed pkg (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (succC (.var 1)) numC :=
    D.succ_typed x1
  have bigX : Typed pkg (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (.var 0) U0 :=
    .conv (.var 0) (valMotive_beta x1) (.sort _)
  have x2 : Typed pkg (.snoc (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (.var 0)) (.var 2) numC :=
    .var 2
  have bigX' : Typed pkg (.snoc (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (.var 0)) (.var 1) U0 :=
    .conv (.var 1) (valMotive_beta x2) (.sort _)
  have body : Typed pkg (.snoc (.snoc Δ numC) (.app valMotive (.var 0))) (.pi (.var 0) (.var 1))
      (.app valMotive (succC (.var 1))) :=
    .conv (D.tower.pi_small bigX bigX') (.symm (valMotive_beta succX)) (.sort _)
  have x0 : Typed pkg (.snoc Δ numC) (.var 0) numC := .var 0
  have innerPi : Typed pkg (.snoc Δ numC)
      (.pi (.app valMotive (.var 0)) (.app valMotive (succC (.var 1))))
      (.head (.sort (.max level1 level1))) :=
    .piForm (.appElim valMotive_typed x0) (.sort _) (.appElim valMotive_typed succX) (.sort _) (.sorts _ _)
  have outerPi : Typed pkg Δ
      (.pi numC (.pi (.app valMotive (.var 0)) (.app valMotive (succC (.var 1)))))
      (.head (.sort (.max (.const 0) (.max level1 level1)))) :=
    .piForm D.num_typed (.sort _) innerPi (.sort _) (.sorts _ _)
  exact .lamIntro outerPi (.sort _) (.lamIntro innerPi (.sort _) body)

/-- **The value type of a code is a small type.** -/
theorem valC_typed {code : Tower.Tm m} (typed : Typed pkg Δ code numC) : Typed pkg Δ (valC code) U0 :=
  .conv (recApp_typed valRec_typed valMotive_typed (.cons valZero_typed (.cons valStep_typed .nil)) typed)
    (valMotive_beta typed) (.sort _)

end Typing

/-! ## The literal row -/

/-- The frame `x : num`. -/
abbrev valCtxX : Context pkg := extend (empty pkg) (numType _)

/-- **The frame of the literal row**: `x : num`, then the call's code, newest. -/
abbrev valFrame : Context pkg := extend valCtxX (numType _)

/-- The call's declared type, `val code`. -/
def valCallType : TypeOver valFrame :=
  ⟨valC (.var 0), u, LevelTower.IsUniverse.sort _, valC_typed (Derivable.var (0 : Fin 2))⟩

/-- **The literal row** `eval code (lit x) = x`: `x`, made at the call's declared type. -/
def valRow : Make valFrame := ⟨valCallType, .var 1⟩

/-- `x`'s own type, `num`. -/
def xOwn : TypeOver valFrame := ⟨numC, u, LevelTower.IsUniverse.sort _, D.num_typed⟩

theorem valRow_frameTyped : FrameTypedAt valRow xOwn := Derivable.var (1 : Fin 2)

/-- `zero`, the code of literals. -/
def zeroCode : Term valCtxX (numType _) := ⟨zeroC, D.zero_typed⟩

/-- **What matching a literal teaches**: `code ≐ zero`. -/
def matchLit : Equation (TotalTerm valFrame) := Elimination.definition valCtxX zeroCode

def valState : State pkg Nat := ⟨valFrame, [], ∅, fun _ => ⟨numType _, ⟨.var 0, Derivable.var (0 : Fin 2)⟩⟩⟩

/-- **The literal row as a firing.** -/
def valFiring : Firing vecS.levels valState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, valRow)]
  tells := [matchLit]
  guards := []
  queries := []

def valFrameType : ∀ m ∈ valFiring.makes, Σ' B : TypeOver valFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨xOwn, by obtain rfl := List.mem_singleton.mp member; exact valRow_frameTyped⟩

/-- **Decided by the kernel**: at the solution `code ↦ zero`, `val zero` computes to `num`. -/
theorem val_decided : vecAdmits? [vecFamily 16 4] 16 valFiring valFrameType = some true := by
  decide +kernel

theorem val_admitted : (convertingStep vecS.levels Nat (vecSettler 16 4)).Admits valFiring :=
  vecAdmits?_sound val_decided

/-- **The literal row is typed after its match**: the answer `x` has the declared type `val code` at
every solution of `code ≐ zero`. -/
theorem val_typedAfterMatch : TypedAfterMatch vecS.levels valFiring.information valRow :=
  converting_typedAfterMatch vecS.levels (vecSettler 16 4) val_admitted (0, valRow) (List.mem_singleton_self _)

/-- `val code` is stuck on the variable code. -/
theorem valCall_stuck : Neutral TowerVectorsModel.roles (valC (.var 0) : Tower.Tm 2) :=
  Neutral.stuck_single (before := [valMotive, numC, valStep]) (after := []) TowerVectorsModel.roles_numRec rfl
    (.var 0)

/-- **Not typed in its frame**: `num` is no stuck `val code`. -/
theorem valRow_not_frameTyped : ¬ valRow.WellTyped := by
  intro typed
  have formed : CtxFormed pkg valFrame.raw := valFrame.formed
  have le : TypeLe pkg valFrame.raw numC (valC (.var 0)) := Typed.generation typed
  have equal : TypeEq pkg valFrame.raw numC (valC (.var 0)) :=
    TypeLe.rigid (S := vecS) le valCallType.isType formed
      (fun _ _ e => TypeEq.inductive_ne_head (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
  exact (TypeEq.neutral_form (TowerVectorsModel.facts level1) equal.symm formed valCall_stuck
    (.inr (.inr (.inr (.inr (.inr ⟨num, ctors, TowerVectorsModel.roles_num, rfl⟩)))))).ne_inductive
      TowerVectorsModel.roles_num rfl

/-- **So the present step refuses it.** -/
theorem val_present_refused : ¬ (DependentFull.step vecS.levels Nat).Admits valFiring := fun admitted =>
  valRow_not_frameTyped (admitted.1.2.2.2.2 (0, valRow) (List.mem_singleton_self _))

/-! ## Control: the wrong code -/

/-- `1`, as a code. -/
def oneCode : Term valCtxX (numType _) := ⟨succC zeroC, D.succ_typed D.zero_typed⟩

/-- Told `code ≐ 1`. -/
def matchOne : Equation (TotalTerm valFrame) := Elimination.definition valCtxX oneCode

/-- `val 1` runs to `num → num`, by kernel evaluation of the package's reduction. -/
theorem valOne_runs : vecNormalize level1 16 (valC (succC zeroC) : Tower.Tm 1) = some (.pi numC numC) := by
  decide +kernel

/-- **Not typed after the match**: `x : num` where the type is `val 1 ≡ num → num`. -/
theorem valOne_not_typedAfterMatch : ¬ TypedAfterMatch vecS.levels [matchOne] valRow := by
  intro after
  have typed := (typedAfterMatch_iff vecS.levels _ valRow).mp after valCtxX
    (Elimination.instantiate valCtxX oneCode) (definition_initial vecS.levels valCtxX oneCode).solves
  have formed : CtxFormed pkg valCtxX.raw := valCtxX.formed
  have atOne : Typed pkg valCtxX.raw (.var 0) (valC (succC zeroC)) := typed
  have toArrow : TypeEq pkg valCtxX.raw (valC (succC zeroC)) (.pi numC numC) :=
    TowerVectorsPrograms.typeEq_of_reduces level1 formed (vecNormalize_sound level1 valOne_runs)
      (valC_typed (D.succ_typed D.zero_typed))
  have le : TypeLe pkg valCtxX.raw numC (.pi numC numC) :=
    Typed.generation (Typed.convType atOne toArrow)
  have equal : TypeEq pkg valCtxX.raw numC (.pi numC numC) :=
    TypeLe.rigid (S := vecS) le ⟨_, D.tower.isUniverse _, D.tower.pi_small D.num_typed D.num_typed⟩ formed
      (fun _ _ e => TypeEq.inductive_ne_head (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num
        formed e)
  exact TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) TowerVectorsModel.roles_num formed equal

/-- The literal row told the wrong code. -/
def valOneFiring : Firing vecS.levels valState := { valFiring with tells := [matchOne] }

/-- **Refused, for every settler.** -/
theorem valOne_refused (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits valOneFiring := fun admitted =>
  valOne_not_typedAfterMatch
    (converting_typedAfterMatch vecS.levels settler admitted (0, valRow) (List.mem_singleton_self _))

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.valC_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.val_decided
#print axioms NativeTypesOnTheStep.Computing.Vectors.val_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.val_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.valRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Vectors.val_present_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.valOne_runs
#print axioms NativeTypesOnTheStep.Computing.Vectors.valOne_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.valOne_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
