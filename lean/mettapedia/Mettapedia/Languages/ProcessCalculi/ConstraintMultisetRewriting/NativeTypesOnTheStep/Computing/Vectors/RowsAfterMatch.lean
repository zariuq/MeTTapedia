import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Settler
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsHead

/-!
# The audit's programs on the converting step, admitted by a settler that runs

Each row of a program is a firing of the converting step over the qualified vectors package: its
frame holds the row's pattern variables and, newest, the length of the call; it is told what matching
its left side teaches; it makes its right side **at the call's declared type**. The type mentions the
call's length, so the row is not typed in its frame; it is typed after its match, where the declared
`add` (or `below-step`) computes in the type.

* **The nil row of `append`** (`nilFiring`): the match teaches `n ≐ zero`; `ys : vec A m` is made at
  `vec A (add n m)`.
* **The cons row of `append`**, the recursive firing (`consFiring`): the match teaches `n ≐ succ k`;
  `pair a (append A k m v ys)` is made at `vec A (add n m)`.
* **The cons row of `head`** (`headFiring`), the head written with the eliminator and the motive
  `λ n _. below-step (λ _. A) n`: the match teaches `n ≐ succ k`; `a : A` is made at
  `below-step (λ _. A) n`.

For each, **admission is decided by kernel evaluation** of the package's computable settler and its
executable conversion (`nil_decided`, `cons_decided`, `head_decided`): the settler finds the initial
solution of the information, and the made row converts along it, with `add` or `below-step`
computing. So the computable converting step admits the firing (`nil_admitted`, `cons_admitted`,
`head_admitted`), and its made row is typed at every solution of what the match teaches
(`nil_typedAfterMatch`, `cons_typedAfterMatch`, `head_typedAfterMatch`). The present step, which asks
for typing in the frame, refuses all three (`nil_present_refused`, `cons_present_refused`,
`head_present_refused`). On the nil row the computable settler and the semantic one agree
(`nil_ideal_admitted`).

**Mistyped rows are refused, for every settler.**
* `append xs ys = xs`, the shape real HE lets through: no match, the first argument `xs : vec A k`
  made at `vec A (add k m)` (`keep_refused`).
* The nil row answering its first argument `tt` at `vec A (add n m)`: after the match the type is
  `vec A m`, which `tt` does not have (`nilFirst_refused`).
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
open TowerNumbersModel (u)
open TowerVectorsModel (U0 numC zeroC succC unitC ttC vecC addC belowStepC)
open TowerVectorsPrograms (consResult add_typed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D ctxA ctxK ctxM numType frame
  result_typed_own)

/-! ## Controls on types -/

section Controls

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- **A variable vector type is no wider than itself**: `vec A x` is usable at `vec A (add y z)` only if
`x ≡ add y z`, which fails on variables, since `add y z` is stuck on `y`. -/
theorem vec_var_not_below_add (formed : CtxFormed pkg Γ) (A : Tower.Tm n) (x y : Fin n) (z : Tower.Tm n)
    (target : IsType pkg Γ (vecC A (addC (.var y) z)))
    (le : TypeLe pkg Γ (vecC A (.var x)) (vecC A (addC (.var y) z))) : False := by
  have stuck : Neutral TowerVectorsModel.roles (vecC A (.var x)) := TowerVectorsConversion.vec_stuck A (.var x)
  have equal : TypeEq pkg Γ (vecC A (.var x)) (vecC A (addC (.var y) z)) :=
    TypeLe.rigid (S := vecS) le target formed
      (fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed stuck
        (.inl ⟨_, rfl⟩)).not_former.1 _ rfl)
      (fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed stuck
        (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl)
      (fun _ _ e => TowerVectorsConversion.vec_stuck_not_sigma formed (.var x) e)
  obtain ⟨T, lengths⟩ := TowerVectorsConversion.neutral_application_arguments formed stuck
    (TowerVectorsConversion.vec_stuck A (TowerVectorsConversion.add_stuck y z)) equal
  exact not_equal_of_neutral_heads (S := vecS) (TowerVectorsConversion.complete level1) formed
    (TowerVectorsConversion.add_stuck y z) (.var x) nofun (.symm lengths)

/-- **`tt` is no vector of a variable length.** -/
theorem tt_not_vec_var (formed : CtxFormed pkg Γ) {A : Tower.Tm n} (tA : Typed pkg Γ A U0) (x : Fin n)
    (tx : Typed pkg Γ (.var x) numC) : ¬ Typed pkg Γ ttC (vecC A (.var x)) := by
  intro typing
  obtain ⟨type, w, declared, _, _, le⟩ := Typed.generation typing
  have known : pkg.constantType TowerVectorsModel.tt = some unitC := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have equal : TypeEq pkg Γ unitC (vecC A (.var x)) :=
    TypeLe.rigid (S := vecS) le ⟨_, D.tower.isUniverse _, D.vec_typed tA tx⟩ formed
      (fun _ _ e => TypeEq.inductive_ne_head (TowerVectorsModel.facts level1) TowerVectorsModel.roles_unit
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (TowerVectorsModel.facts level1) TowerVectorsModel.roles_unit
        formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (TowerVectorsModel.facts level1) TowerVectorsModel.roles_unit
        formed e)
  exact TowerVectorsConversion.vec_stuck_not_unit formed (.var x) equal.symm

end Controls

/-! ## The nil row of `append` -/

section Nil

/-- The frame `A : U0, m : num`. -/
abbrev nilCtxM : Context pkg := extend ctxA (numType _)

/-- `vec A m`. -/
def nilYsType : TypeOver nilCtxM :=
  ⟨vecC (.var 1) (.var 0), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (1 : Fin 2)) (Derivable.var (0 : Fin 2))⟩

/-- The frame `A : U0, m : num, ys : vec A m`. -/
abbrev nilCtxY : Context pkg := extend nilCtxM nilYsType

/-- **The frame of the nil row**: `A, m, ys`, then the call's length `n : num`, newest. -/
abbrev nilFrame : Context pkg := extend nilCtxY (numType _)

/-- The call's declared type, `vec A (add n m)`. -/
def nilCallType : TypeOver nilFrame :=
  ⟨vecC (.var 3) (addC (.var 0) (.var 2)), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (3 : Fin 4))
      (add_typed level1 (Derivable.var (0 : Fin 4)) (Derivable.var (2 : Fin 4)))⟩

/-- **The nil row** `append A n m tt ys = ys`: its right side `ys`, made at the call's declared type. -/
def nilRow : Make nilFrame := ⟨nilCallType, .var 1⟩

/-- `ys`'s own type in the frame, `vec A m`. -/
def nilYsOwn : TypeOver nilFrame :=
  ⟨vecC (.var 3) (.var 2), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (3 : Fin 4)) (Derivable.var (2 : Fin 4))⟩

theorem nilRow_frameTyped : FrameTypedAt nilRow nilYsOwn := Derivable.var (1 : Fin 4)

/-- `zero`, over `A, m, ys`. -/
def zeroValue : Term nilCtxY (numType _) := ⟨zeroC, D.zero_typed⟩

/-- **What matching the nil row teaches**: `n ≐ zero`. -/
def matchNil : Equation (TotalTerm nilFrame) := Elimination.definition nilCtxY zeroValue

/-- The call's length, as a row of the state. -/
def nilState : State pkg Nat := ⟨nilFrame, [], ∅, fun _ => ⟨numType _, ⟨.var 0, Derivable.var (0 : Fin 4)⟩⟩⟩

/-- **The nil row as a firing**: told what the match teaches, it makes `ys` at `vec A (add n m)`. -/
def nilFiring : Firing vecS.levels nilState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, nilRow)]
  tells := [matchNil]
  guards := []
  queries := []

/-- The made row with its own type in its frame. -/
def nilFrameType : ∀ m ∈ nilFiring.makes, Σ' B : TypeOver nilFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨nilYsOwn, by obtain rfl := List.mem_singleton.mp member; exact nilRow_frameTyped⟩

/-- **The package's family settles what the match teaches**, by kernel evaluation. -/
theorem nil_family_settles : (vecFamily 16 4 nilFiring.information).isSettled = true := by
  decide +kernel

/-- **Decided by the kernel**: the computable converting step admits the nil row. -/
theorem nil_decided : vecAdmits? [vecFamily 16 4] 16 nilFiring nilFrameType = some true := by
  decide +kernel

/-- **A budget that runs out claims nothing**: with no round of the driver, the decision is `none`. -/
theorem nil_budget : vecAdmits? [vecFamily 16 0] 16 nilFiring nilFrameType = none := by decide +kernel

theorem nil_admitted : (convertingStep vecS.levels Nat (vecSettler 16 4)).Admits nilFiring :=
  vecAdmits?_sound nil_decided

/-- **The nil row is typed after its match**, at every solution of `n ≐ zero`. -/
theorem nil_typedAfterMatch : TypedAfterMatch vecS.levels nilFiring.information nilRow :=
  converting_typedAfterMatch vecS.levels (vecSettler 16 4) nil_admitted (0, nilRow) (List.mem_singleton_self _)

/-- **It is not typed in its frame**: `vec A m` is not usable at `vec A (add n m)` for a variable `n`. -/
theorem nilRow_not_frameTyped : ¬ nilRow.WellTyped := fun typed =>
  vec_var_not_below_add nilFrame.formed (.var 3) 2 0 (.var 2) nilCallType.isType (Typed.generation typed)

/-- **So the present step refuses it.** -/
theorem nil_present_refused : ¬ (DependentFull.step vecS.levels Nat).Admits nilFiring := fun admitted =>
  nilRow_not_frameTyped (admitted.1.2.2.2.2 (0, nilRow) (List.mem_singleton_self _))

/-- A decision that settles is decisive. -/
theorem decisive_of_isSettled {Δ : Context vecS.R} {I : EquationStore (TotalTerm Δ)}
    {d : Decision vecS.levels I} (settles : d.isSettled = true) : d.Decisive := by
  cases d with
  | settled M σ initial => trivial
  | refuted none => cases settles
  | undecided => cases settles

/-- The information is decided by the package's family. -/
theorem nil_decidedBy : DecidedBy vecS.levels [vecFamily 16 4] nilFiring.information :=
  ⟨vecFamily 16 4, List.mem_singleton_self _, decisive_of_isSettled nil_family_settles⟩

/-- **The computable settler and the semantic one agree on the nil row.** -/
theorem nil_ideal_admitted : (convertingStep vecS.levels Nat (Settler.ideal vecS.levels)).Admits nilFiring :=
  (ofFamilies_converting_iff_ideal vecS.levels [vecFamily 16 4] nil_decidedBy).mp nil_admitted

/-! ### A mistyped nil row: answering the first argument -/

/-- `tt` made at the call's declared type. -/
def nilFirstRow : Make nilFrame := ⟨nilCallType, ttC⟩

/-- The nil row answering its first argument `tt`. -/
def nilFirstFiring : Firing vecS.levels nilState :=
  { nilFiring with makes := [(0, nilFirstRow)] }

/-- **Not typed after the match**: at the solution `n ↦ zero` the type is `vec A (add zero m)`, which
is `vec A m`, and `tt` is no vector of the variable length `m`. -/
theorem nilFirst_not_typedAfterMatch : ¬ TypedAfterMatch vecS.levels [matchNil] nilFirstRow := by
  intro after
  have typed := (typedAfterMatch_iff vecS.levels _ nilFirstRow).mp after nilCtxY
    (Elimination.instantiate nilCtxY zeroValue) (definition_initial vecS.levels nilCtxY zeroValue).solves
  have formed : CtxFormed pkg nilCtxY.raw := nilCtxY.formed
  have tA : Typed pkg nilCtxY.raw (.var 2) U0 := Derivable.var (2 : Fin 3)
  have tm : Typed pkg nilCtxY.raw (.var 1) numC := Derivable.var (1 : Fin 3)
  have atZero : Typed pkg nilCtxY.raw ttC (vecC (.var 2) (addC zeroC (.var 1))) := typed
  exact tt_not_vec_var formed tA 1 tm
    (Typed.convType atZero (TowerVectorsConversion.vec_left_zero_meets tA tm))

/-- **Refused, for every settler.** -/
theorem nilFirst_refused (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits nilFirstFiring := fun admitted =>
  nilFirst_not_typedAfterMatch
    (converting_typedAfterMatch vecS.levels settler admitted (0, nilFirstRow) (List.mem_singleton_self _))

/-- `tt`'s own type, `unit`. -/
def unitOwn : TypeOver nilFrame := ⟨unitC, u, LevelTower.IsUniverse.sort _, D.unit_typed⟩

def nilFirstFrameType :
    ∀ m ∈ nilFirstFiring.makes, Σ' B : TypeOver nilFirstFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨unitOwn, by obtain rfl := List.mem_singleton.mp member; exact D.tt_typed⟩

/-- **The same decision claims nothing on the mistyped row**: the settler solves the match, and the
executable conversion finds no way from `unit` to `vec A (add zero m)`; the refusal is the theorem
above, for every settler. -/
theorem nilFirst_undecided : vecAdmits? [vecFamily 16 4] 16 nilFirstFiring nilFirstFrameType = none := by
  decide +kernel

end Nil

/-! ## The cons row of `append`: the recursive firing -/

section Cons

/-- **The frame of the cons row**: `A : U0, k m : num, a : A, v : vec A k, ys : vec A m`, then the
call's length `n : num`, newest. -/
abbrev consFrame : Context pkg := extend frame (numType _)

/-- The call's declared type, `vec A (add n m)`. -/
def consCallType : TypeOver consFrame :=
  ⟨vecC (.var 6) (addC (.var 0) (.var 4)), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (6 : Fin 7))
      (add_typed level1 (Derivable.var (0 : Fin 7)) (Derivable.var (4 : Fin 7)))⟩

/-- The result's own pair type `Σ A (vec A (add k m))`, over the equation's frame. -/
def pairType : TypeOver frame :=
  ⟨.sigma (.var 5) (vecC (.var 6) (addC (.var 5) (.var 4))), u, LevelTower.IsUniverse.sort _,
    D.tower.sigma_small (Derivable.var (5 : Fin 6))
      (D.vec_typed (Derivable.var (6 : Fin 7))
        (add_typed level1 (Derivable.var (5 : Fin 7)) (Derivable.var (4 : Fin 7))))⟩

theorem consResult_pair_typed : Typed pkg frame.raw consResult pairType.code :=
  Typed.convType result_typed_own
    (D.vec_succ_eq (Derivable.var (5 : Fin 6))
      (add_typed level1 (Derivable.var (4 : Fin 6)) (Derivable.var (3 : Fin 6))))

/-- The result `pair a (append A k m v ys)`, at its pair type. -/
def pairRow : TotalTerm frame := ⟨pairType, ⟨consResult, consResult_pair_typed⟩⟩

/-- The result over the cons row's frame. -/
def pairRowN : TotalTerm consFrame := pairRow.reindex (projectionHom frame (numType frame))

/-- **The cons row** `append A n m (pair a v) ys = pair a (append A k m v ys)`: its right side, made at
the call's declared type. -/
def consRow : Make consFrame := ⟨consCallType, pairRowN.2.code⟩

/-- `succ k`, over the equation's frame. -/
def succK : Term frame (numType _) := ⟨succC (.var 4), D.succ_typed (Derivable.var (4 : Fin 6))⟩

/-- **What matching the cons row teaches**: `n ≐ succ k`. -/
def matchCons : Equation (TotalTerm consFrame) := Elimination.definition frame succK

def consState : State pkg Nat := ⟨consFrame, [], ∅, fun _ => ⟨numType _, ⟨.var 0, Derivable.var (0 : Fin 7)⟩⟩⟩

/-- **The recursive firing of `append`**: told what the match teaches, it makes
`pair a (append A k m v ys)` at `vec A (add n m)`. -/
def consFiring : Firing vecS.levels consState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, consRow)]
  tells := [matchCons]
  guards := []
  queries := []

/-- The made row with its own pair type in its frame. -/
def consFrameType : ∀ m ∈ consFiring.makes, Σ' B : TypeOver consFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨pairRowN.1, by obtain rfl := List.mem_singleton.mp member; exact pairRowN.2.typed⟩

/-- **Decided by the kernel**: the settler solves `n ≐ succ k`, and at the solution the executable
conversion takes `vec A (add (succ k) m)` to `Σ A (vec A (add k m))`, the made row's own type. -/
theorem cons_decided : vecAdmits? [vecFamily 16 4] 16 consFiring consFrameType = some true := by
  decide +kernel

/-- **The computable converting step admits the recursive firing.** -/
theorem cons_admitted : (convertingStep vecS.levels Nat (vecSettler 16 4)).Admits consFiring :=
  vecAdmits?_sound cons_decided

/-- **The recursive firing's made row is typed after its match**, at every solution of `n ≐ succ k`. -/
theorem cons_typedAfterMatch : TypedAfterMatch vecS.levels consFiring.information consRow :=
  converting_typedAfterMatch vecS.levels (vecSettler 16 4) cons_admitted (0, consRow)
    (List.mem_singleton_self _)

/-- **It is not typed in its frame**: a pair has no type `vec A (add n m)` for a variable `n`, that
type being stuck, and a stuck type being no pair type. -/
theorem consRow_not_frameTyped : ¬ consRow.WellTyped := by
  intro typed
  have formed : CtxFormed pkg consFrame.raw := consFrame.formed
  obtain ⟨A', B', w, tS, hw, _, _, le⟩ := Typed.generation typed
  have below := TypeLe.toBelow le consCallType.isType
  obtain ⟨A'', B'', eT, _, _⟩ :=
    Below.sigma_source (S := vecS) (TowerVectorsModel.facts level1) below formed (IsType.refl ⟨w, hw, tS⟩)
  exact TowerVectorsConversion.vec_stuck_not_sigma formed (TowerVectorsConversion.add_stuck 0 (.var 4)) eT

/-- **So the present step refuses the recursive firing.** -/
theorem cons_present_refused : ¬ (DependentFull.step vecS.levels Nat).Admits consFiring := fun admitted =>
  consRow_not_frameTyped (admitted.1.2.2.2.2 (0, consRow) (List.mem_singleton_self _))

end Cons

/-! ## The cons row of `head` -/

section Head

/-- `a : A`, over `A, k`. -/
def headAType : TypeOver ctxK := ⟨.var 1, u, LevelTower.IsUniverse.sort _, Derivable.var (1 : Fin 2)⟩

/-- The frame `A, k, a`. -/
abbrev headCtxA : Context pkg := extend ctxK headAType

/-- `w : vec A k`. -/
def headWType : TypeOver headCtxA :=
  ⟨vecC (.var 2) (.var 1), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (2 : Fin 3)) (Derivable.var (1 : Fin 3))⟩

/-- The frame `A, k, a, w`. -/
abbrev headCtxW : Context pkg := extend headCtxA headWType

/-- **The frame of head's cons row**: `A : U0, k : num, a : A, w : vec A k`, then the call's length
`n : num`, newest. -/
abbrev headFrame : Context pkg := extend headCtxW (numType _)

/-- The call's declared type, the motive at the call: `below-step (λ _. A) n`. -/
def headCallType : TypeOver headFrame :=
  ⟨belowStepC (.lam (.var 5)) (.var 0), u, LevelTower.IsUniverse.sort _,
    TowerVectorsLookup.belowStep_typed level1
      (TowerVectorsHead.constFamily_typed level1 (Derivable.var (5 : Fin 6))) (Derivable.var (0 : Fin 5))⟩

/-- **Head's cons row** `head A n (pair a w) = a`: `a`, made at the call's declared type. -/
def headRow : Make headFrame := ⟨headCallType, .var 2⟩

/-- `a`'s own type, `A`. -/
def headAOwn : TypeOver headFrame := ⟨.var 4, u, LevelTower.IsUniverse.sort _, Derivable.var (4 : Fin 5)⟩

theorem headRow_frameTyped : FrameTypedAt headRow headAOwn := Derivable.var (2 : Fin 5)

/-- `succ k`, over `A, k, a, w`. -/
def succKHead : Term headCtxW (numType _) := ⟨succC (.var 2), D.succ_typed (Derivable.var (2 : Fin 4))⟩

/-- **What matching the cons row teaches**: `n ≐ succ k`. -/
def matchHead : Equation (TotalTerm headFrame) := Elimination.definition headCtxW succKHead

def headState : State pkg Nat := ⟨headFrame, [], ∅, fun _ => ⟨numType _, ⟨.var 0, Derivable.var (0 : Fin 5)⟩⟩⟩

/-- **Head's cons row as a firing.** -/
def headFiring : Firing vecS.levels headState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, headRow)]
  tells := [matchHead]
  guards := []
  queries := []

def headFrameType : ∀ m ∈ headFiring.makes, Σ' B : TypeOver headFiring.helpers.frame, FrameTypedAt m.2 B :=
  fun m member => ⟨headAOwn, by obtain rfl := List.mem_singleton.mp member; exact headRow_frameTyped⟩

/-- **Decided by the kernel**: at the solution `n ↦ succ k`, `below-step (λ _. A) (succ k)` computes to
`A`. -/
theorem head_decided : vecAdmits? [vecFamily 16 4] 16 headFiring headFrameType = some true := by
  decide +kernel

theorem head_admitted : (convertingStep vecS.levels Nat (vecSettler 16 4)).Admits headFiring :=
  vecAdmits?_sound head_decided

/-- **Head's cons row is typed after its match.** -/
theorem head_typedAfterMatch : TypedAfterMatch vecS.levels headFiring.information headRow :=
  converting_typedAfterMatch vecS.levels (vecSettler 16 4) head_admitted (0, headRow)
    (List.mem_singleton_self _)

/-- `below-step (λ _. A) n` is stuck on the variable `n`. -/
theorem headCall_stuck : Neutral TowerVectorsModel.roles (belowStepC (.lam (.var 5)) (.var 0) : Tower.Tm 5) :=
  Neutral.stuck_single (before := [.lam (.var 5)]) (after := []) TowerVectorsModel.roles_belowStep rfl (.var 0)

/-- **It is not typed in its frame**: `A` and the stuck `below-step (λ _. A) n` are different neutral
types. -/
theorem headRow_not_frameTyped : ¬ headRow.WellTyped := by
  intro typed
  have formed : CtxFormed pkg headFrame.raw := headFrame.formed
  have le : TypeLe pkg headFrame.raw (.var 4) (belowStepC (.lam (.var 5)) (.var 0)) := Typed.generation typed
  have stuck : Neutral TowerVectorsModel.roles (.var 4 : Tower.Tm 5) := .var 4
  have equal : TypeEq pkg headFrame.raw (.var 4) (belowStepC (.lam (.var 5)) (.var 0)) :=
    TypeLe.rigid (S := vecS) le headCallType.isType formed
      (fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed stuck
        (.inl ⟨_, rfl⟩)).not_former.1 _ rfl)
      (fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed stuck
        (.inr (.inl ⟨_, _, rfl⟩))).not_former.2.1 _ _ rfl)
      (fun _ _ e => (TypeEq.neutral_form (TowerVectorsModel.facts level1) e formed stuck
        (.inr (.inr (.inl ⟨_, _, rfl⟩)))).not_former.2.2.1 _ _ rfl)
  obtain ⟨w, -, e⟩ := equal
  exact not_equal_of_neutral_heads (S := vecS) (TowerVectorsConversion.complete level1) formed
    (.var 4) headCall_stuck nofun e

/-- **So the present step refuses it.** -/
theorem head_present_refused : ¬ (DependentFull.step vecS.levels Nat).Admits headFiring := fun admitted =>
  headRow_not_frameTyped (admitted.1.2.2.2.2 (0, headRow) (List.mem_singleton_self _))

end Head

/-! ## The shape real HE lets through: `append xs ys = xs` -/

section Keep

/-- `xs : vec A k`, over `A, k, m`. -/
def keepXsType : TypeOver ctxM :=
  ⟨vecC (.var 2) (.var 1), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (2 : Fin 3)) (Derivable.var (1 : Fin 3))⟩

abbrev keepCtxX : Context pkg := extend ctxM keepXsType

/-- `ys : vec A m`, over `A, k, m, xs`. -/
def keepYsType : TypeOver keepCtxX :=
  ⟨vecC (.var 3) (.var 1), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (3 : Fin 4)) (Derivable.var (1 : Fin 4))⟩

/-- The frame `A : U0, k m : num, xs : vec A k, ys : vec A m`. -/
abbrev keepFrame : Context pkg := extend keepCtxX keepYsType

/-- The call's declared type, `vec A (add k m)`. -/
def keepCallType : TypeOver keepFrame :=
  ⟨vecC (.var 4) (addC (.var 3) (.var 2)), u, LevelTower.IsUniverse.sort _,
    D.vec_typed (Derivable.var (4 : Fin 5))
      (add_typed level1 (Derivable.var (3 : Fin 5)) (Derivable.var (2 : Fin 5)))⟩

/-- **The mistyped row** `append xs ys = xs`: the first argument, made at the call's declared type. -/
def keepRow : Make keepFrame := ⟨keepCallType, .var 1⟩

def keepState : State pkg Nat := ⟨keepFrame, [], ∅, fun _ => ⟨keepYsType.reindex
  (projectionHom keepCtxX keepYsType), ⟨.var 0, newest keepCtxX keepYsType |>.typed⟩⟩⟩

/-- The row as a firing: no match, nothing told. -/
def keepFiring : Firing vecS.levels keepState where
  helpers := .nil _
  taken := []
  read := []
  takes := []
  reads := []
  makes := [(0, keepRow)]
  tells := []
  guards := []
  queries := []

/-- **Not typed in its frame**: `vec A k` is not usable at `vec A (add k m)`. -/
theorem keepRow_not_frameTyped : ¬ keepRow.WellTyped := fun typed =>
  vec_var_not_below_add keepFrame.formed (.var 4) 3 3 (.var 2) keepCallType.isType (Typed.generation typed)

/-- **Refused, for every settler**: with nothing learned, typed after the match is typed in the frame. -/
theorem keep_refused (settler : Settler vecS.levels) :
    ¬ (convertingStep vecS.levels Nat settler).Admits keepFiring := by
  intro admitted
  have after := converting_typedAfterMatch vecS.levels settler admitted (0, keepRow) (List.mem_singleton_self _)
  have typed := (typedAfterMatch_iff vecS.levels _ keepRow).mp after keepFrame (𝟙 _) (Frames.models_nil _)
  exact keepRow_not_frameTyped typed

end Keep

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.vec_var_not_below_add
#print axioms NativeTypesOnTheStep.Computing.Vectors.tt_not_vec_var
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_family_settles
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_decided
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_budget
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.nilRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_present_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_decidedBy
#print axioms NativeTypesOnTheStep.Computing.Vectors.nil_ideal_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.nilFirst_not_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.nilFirst_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.nilFirst_undecided
#print axioms NativeTypesOnTheStep.Computing.Vectors.consResult_pair_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.cons_decided
#print axioms NativeTypesOnTheStep.Computing.Vectors.cons_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.cons_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.consRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Vectors.cons_present_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.head_decided
#print axioms NativeTypesOnTheStep.Computing.Vectors.head_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.head_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.Vectors.headRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Vectors.head_present_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.keepRow_not_frameTyped
#print axioms NativeTypesOnTheStep.Computing.Vectors.keep_refused

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
