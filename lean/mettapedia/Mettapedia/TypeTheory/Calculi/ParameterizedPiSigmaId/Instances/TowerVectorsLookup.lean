import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsPrograms

/-!
# Finite indices, and lookup by the dependent eliminator

In the package `TowerVectorsModel.rules`, the order `below n i` (inhabited exactly when `i < n`)
computes in conversion:

`below zero i ≡ void`, `below (succ k) zero ≡ unit`, `below (succ k) (succ j) ≡ below k j`,

so the finite type `fin n = Σ (i : num). below n i` has `fz = pair zero tt : fin (succ k)` and
`fs i = pair (succ (fst i)) (snd i) : fin (succ k)` for `i : fin k` (`fz_typed`, `fs_typed`), and
`fin zero ≡ Σ (i : num). void` (`fin_zero_void`).

**Lookup by the eliminator**:

`lookup A n v i = vec-elim A (λ k _. fin k → A) (λ i. void-rec (λ _. A) (snd i))
   (λ k a w ih i. num-rec (λ j. below (succ k) j → A) (λ _. a) (λ j _ p. ih (pair j p))
     (fst i) (snd i)) n v i`,

typed at `A` (`lookup_typed`). The case of the empty vector is discharged by the empty type's
recursor, with no method. Its equations hold in conversion: `lookup A (succ k) (pair a w) fz ≡ a`
(`lookup_fz`) and `lookup A (succ k) (pair a w) (fs i) ≡ lookup A k w i` (`lookup_fs`, by eta).

Every program is a judgment in the context of its variables.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerVectorsModel TowerVectorsPrograms
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

namespace TowerVectorsLookup

variable (lv : LevelExpr Nat)

abbrev numRecC {n : Nat} (M Z S t : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.const numRec) M) Z) S) t

/-! ## The equations of the order and of the recursor of numbers, as steps -/

theorem below_zero_step {n : Nat} (i : Tm Tower.Head n) :
    (rules lv).computation.step (belowC zeroC i) voidC :=
  RootComputation.step_unionAll mem_below
    ⟨zero, [], consSub i (consSub zeroC fun j => Fin.elim0 j), [], mem_zero, rfl, rfl, rfl⟩

theorem below_succ_step {n : Nat} (k i : Tm Tower.Head n) :
    (rules lv).computation.step (belowC (succC k) i) (belowStepC (.app (.const below) k) i) :=
  RootComputation.step_unionAll mem_below
    ⟨succ, [.recursive], consSub i (consSub (succC k) fun j => Fin.elim0 j), [k], mem_succ, rfl, rfl,
      rfl⟩

theorem belowStep_zero_step {n : Nat} (h : Tm Tower.Head n) :
    (rules lv).computation.step (belowStepC h zeroC) unitC :=
  RootComputation.step_unionAll mem_belowStep
    ⟨zero, [], consSub zeroC (consSub h fun j => Fin.elim0 j), [], mem_zero, rfl, rfl, rfl⟩

theorem belowStep_succ_step {n : Nat} (h j : Tm Tower.Head n) :
    (rules lv).computation.step (belowStepC h (succC j)) (.app h j) :=
  RootComputation.step_unionAll mem_belowStep
    ⟨succ, [.recursive], consSub (succC j) (consSub h fun i => Fin.elim0 i), [j], mem_succ, rfl, rfl,
      rfl⟩

theorem num_zero_step {n : Nat} (M Z S : Tm Tower.Head n) :
    (rules lv).computation.step (numRecC M Z S zeroC) Z :=
  RootComputation.step_unionAll mem_numRec
    ⟨M, [Z, S], 0, zero, [], [], Z, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem num_succ_step {n : Nat} (M Z S x : Tm Tower.Head n) :
    (rules lv).computation.step (numRecC M Z S (succC x)) (.app (.app S x) (numRecC M Z S x)) :=
  RootComputation.step_unionAll mem_numRec
    ⟨M, [Z, S], 1, succ, [.recursive], [x], S, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Typings -/

section Typing

variable {n : Nat} {Γ : Ctx Tower.Head n}

theorem void_typed : Typed (rules lv) Γ voidC U0 := (towerLike_rules lv).small rfl

theorem below_typed {k i : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC)
    (ti : Typed (rules lv) Γ i numC) : Typed (rules lv) Γ (belowC k i) U0 := by
  have tw := towerLike_rules lv
  have tBelow : Typed (rules lv) Γ (.const below) (.pi numC (.pi numC U0)) :=
    .const (type := .pi numC (.pi numC U0)) rfl (.piForm (tw.small rfl) (tw.isUniverse _)
      (family_typed tw rfl) (tw.isUniverse _) (tw.join _ _)) (tw.isUniverse _)
  exact .appElim (.appElim tBelow tk) ti

theorem belowStep_typed {h i : Tm Tower.Head n} (th : Typed (rules lv) Γ h (.pi numC U0))
    (ti : Typed (rules lv) Γ i numC) : Typed (rules lv) Γ (belowStepC h i) U0 := by
  have tw := towerLike_rules lv
  have tStep : Typed (rules lv) Γ (.const belowStep) (.pi (.pi numC U0) (.pi numC U0)) :=
    .const (type := .pi (.pi numC U0) (.pi numC U0)) rfl (.piForm (family_typed tw rfl)
      (tw.isUniverse _) (family_typed tw rfl) (tw.isUniverse _) (tw.join _ _)) (tw.isUniverse _)
  exact .appElim (.appElim tStep th) ti

theorem belowFun_typed {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Typed (rules lv) Γ (.app (.const below) k) (.pi numC U0) := by
  have tw := towerLike_rules lv
  have tBelow : Typed (rules lv) Γ (.const below) (.pi numC (.pi numC U0)) :=
    .const (type := .pi numC (.pi numC U0)) rfl (.piForm (tw.small rfl) (tw.isUniverse _)
      (family_typed tw rfl) (tw.isUniverse _) (tw.join _ _)) (tw.isUniverse _)
  exact .appElim tBelow tk

/-- `fin k` is a small type. -/
theorem fin_typed {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Typed (rules lv) Γ (finC k) U0 :=
  (towerLike_rules lv).sigma_small (vecDeclared_rules lv).num_typed
    (below_typed lv tk.weaken (Derivable.var 0))

/-- `below zero i ≡ void`. -/
theorem below_zero_eq {i : Tm Tower.Head n} (ti : Typed (rules lv) Γ i numC) :
    Equal (rules lv) Γ (belowC zeroC i) voidC U0 :=
  .root (below_zero_step lv i) (below_typed lv (vecDeclared_rules lv).zero_typed ti) (void_typed lv)

/-- `below (succ k) zero ≡ unit`. -/
theorem below_succ_zero_eq {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Equal (rules lv) Γ (belowC (succC k) zeroC) unitC U0 := by
  have D := vecDeclared_rules lv
  exact .trans (.root (below_succ_step lv k zeroC) (below_typed lv (D.succ_typed tk) D.zero_typed)
      (belowStep_typed lv (belowFun_typed lv tk) D.zero_typed))
    (.root (belowStep_zero_step lv _) (belowStep_typed lv (belowFun_typed lv tk) D.zero_typed)
      D.unit_typed)

/-- `below (succ k) (succ j) ≡ below k j`. -/
theorem below_succ_succ_eq {k j : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC)
    (tj : Typed (rules lv) Γ j numC) :
    Equal (rules lv) Γ (belowC (succC k) (succC j)) (belowC k j) U0 := by
  have D := vecDeclared_rules lv
  exact .trans (.root (below_succ_step lv k (succC j)) (below_typed lv (D.succ_typed tk) (D.succ_typed tj))
      (belowStep_typed lv (belowFun_typed lv tk) (D.succ_typed tj)))
    (.root (belowStep_succ_step lv _ j) (belowStep_typed lv (belowFun_typed lv tk) (D.succ_typed tj))
      (below_typed lv tk tj))

theorem inst0_below (a K : Tm Tower.Head n) :
    inst0 a (belowC (Presentation.rename wk K) (.var 0)) = belowC K a := by
  show Tm.app (Tm.app (.const below) (inst0 a (Presentation.rename wk K))) a = _
  rw [inst0_rename_wk]

/-- The first index of `fin (succ k)`: `fz = pair zero tt`. -/
def fzC {m : Nat} : Tm Tower.Head m := .pair zeroC ttC

/-- The successor index: `fs i = pair (succ (fst i)) (snd i)`. -/
def fsC {m : Nat} (i : Tm Tower.Head m) : Tm Tower.Head m := .pair (succC (.fst i)) (.snd i)

theorem fz_typed {k : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC) :
    Typed (rules lv) Γ fzC (finC (succC k)) := by
  have D := vecDeclared_rules lv
  have ttt : Typed (rules lv) Γ ttC (inst0 zeroC (belowC (Presentation.rename wk (succC k)) (.var 0))) := by
    rw [inst0_below]
    exact Typed.convType D.tt_typed ⟨u, D.tower.isUniverse _, (below_succ_zero_eq lv tk).symm⟩
  exact .pairIntro (fin_typed lv (D.succ_typed tk)) (D.tower.isUniverse _) D.zero_typed ttt

theorem fs_typed {k i : Tm Tower.Head n} (tk : Typed (rules lv) Γ k numC)
    (ti : Typed (rules lv) Γ i (finC k)) : Typed (rules lv) Γ (fsC i) (finC (succC k)) := by
  have D := vecDeclared_rules lv
  have tfst : Typed (rules lv) Γ (.fst i) numC := .fstElim ti
  have tsnd : Typed (rules lv) Γ (.snd i) (belowC k (.fst i)) := by
    have h := Derivable.sndElim ti
    rwa [inst0_below] at h
  have tsnd' : Typed (rules lv) Γ (.snd i)
      (inst0 (succC (.fst i)) (belowC (Presentation.rename wk (succC k)) (.var 0))) := by
    rw [inst0_below]
    exact Typed.convType tsnd ⟨u, D.tower.isUniverse _, (below_succ_succ_eq lv tk tfst).symm⟩
  exact .pairIntro (fin_typed lv (D.succ_typed tk)) (D.tower.isUniverse _) (D.succ_typed tfst) tsnd'

/-- **`fin zero` is a pair type over the empty type**: `fin zero ≡ Σ (i : num). void`. -/
theorem fin_zero_void : TypeEq (rules lv) Γ (finC zeroC) (.sigma numC voidC) := by
  have D := vecDeclared_rules lv
  have e : Equal (rules lv) (.snoc Γ numC) (belowC zeroC (.var 0)) voidC U0 :=
    below_zero_eq lv (Derivable.var 0)
  exact ⟨_, D.tower.isUniverse _, Derivable.cumulEq (.sigmaCong (.refl D.num_typed) (D.tower.isUniverse _)
    e (D.tower.isUniverse _) (D.tower.join _ _)) D.tower.collapse⟩

/-- `void-rec Q t : Q t`. -/
theorem voidRec_typed {Q t : Tm Tower.Head n} (tQ : Typed (rules lv) Γ Q (.pi voidC (.head (.sort lv))))
    (tt' : Typed (rules lv) Γ t voidC) : Typed (rules lv) Γ (voidRecC Q t) (.app Q t) := by
  obtain ⟨w, hw, typed⟩ := voidRecType_typed lv
  have tc : Typed (rules lv) Γ (.const voidRec) (liftClosed (recType void (.sort lv) [])) :=
    .const rfl (Derivable.mono (sub_void lv) typed) hw
  have m₀ : SubstMor (rules lv) .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele void (.sort lv) []) Γ (consSub t (consSub Q fun i => Fin.elim0 i)) :=
    SubstMor.cons (SubstMor.cons m₀ tQ) tt'
  exact Typed.telescope_apply mor tc

end Typing

/-! ## Lookup -/

/-- Weakening past seven binders. -/
def wk7 {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head (n + 1 + 1 + 1 + 1 + 1 + 1 + 1) :=
  Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
    (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk A))))))

/-- The motive of lookup: `λ k _. fin k → A`. -/
def lookupMotive {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (.pi (finC (.var 1)) (Presentation.rename wk (Presentation.rename wk
    (Presentation.rename wk A)))))

/-- At the empty vector there is no index: `λ i. void-rec (λ _. A) (snd i)`. -/
def lookupNil {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (voidRecC (.lam (Presentation.rename wk (Presentation.rename wk A))) (.snd (.var 0)))

/-- At `pair a w`: `λ k a w ih i. num-rec (λ j. below (succ k) j → A) (λ _. a)
(λ j _ p. ih (pair j p)) (fst i) (snd i)`. -/
def lookupCons {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (.lam (.lam (.lam (.app (numRecC
    (.lam (.pi (belowC (succC (.var 5)) (.var 0)) (wk7 A)))
    (.lam (.var 4))
    (.lam (.lam (.lam (.app (.var 4) (.pair (.var 2) (.var 0))))))
    (.fst (.var 0))) (.snd (.var 0)))))))

/-- **Lookup, by the eliminator on the vector.** -/
def lookupTm {n : Nat} (A k v i : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (vecElimC A (lookupMotive A) (lookupNil A) (lookupCons A) k v) i

/-- The context of lookup's variables: `A : U0, n : num, v : vec A n, i : fin n`. -/
abbrev lookupCtx : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))) (finC (.var 1))

theorem lookupCtx_formed : CtxFormed (rules lv) lookupCtx := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tn : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 0) numC := .var 0
  have tn₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))) (.var 1)
      numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA tn⟩)
    ⟨_, D.tower.isUniverse _, fin_typed lv tn₃⟩

/-- The motive at its type. -/
theorem lookupMotive_typed :
    Typed (rules lv) lookupCtx (lookupMotive (.var 3)) (vecMotive (.var 3)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc (.snoc lookupCtx numC) (vecC (.var 4) (.var 0)))
      (finC (.var 1))) (.var 6) U0 := .var 6
  have tk : Typed (rules lv) (.snoc (.snoc lookupCtx numC) (vecC (.var 4) (.var 0))) (.var 1) numC := .var 1
  have tBody := D.tower.pi_small (fin_typed lv tk) tA
  have tA₁ : Typed (rules lv) (.snoc lookupCtx numC) (.var 4) U0 := .var 4
  have tk₁ : Typed (rules lv) (.snoc lookupCtx numC) (.var 0) numC := .var 0
  have tInner : Typed (rules lv) (.snoc lookupCtx numC) (.pi (vecC (.var 4) (.var 0)) U0)
      (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
    .piForm (D.vec_typed tA₁ tk₁) (D.tower.isUniverse _) D.tower.u0_typed (D.tower.isUniverse _)
      (D.tower.join _ _)
  have tOuter : Typed (rules lv) lookupCtx (vecMotive (.var 3))
      (.head (.sort (.max (.const 0) (.max (.const 0) (.succ (.const 0)))))) :=
    .piForm D.num_typed (D.tower.isUniverse _) tInner (D.tower.isUniverse _) (D.tower.join _ _)
  exact .lamIntro tOuter (D.tower.isUniverse _) (.lamIntro tInner (D.tower.isUniverse _) tBody)

/-- The method at the empty vector: `fin zero → A`, by the empty type's recursor. -/
theorem lookupNil_typed :
    Typed (rules lv) lookupCtx (lookupNil (.var 3))
      (.app (.app (lookupMotive (.var 3)) zeroC) ttC) := by
  have D := vecDeclared_rules lv
  have formed := lookupCtx_formed lv
  have tA₆ : Typed (rules lv) (.snoc (.snoc lookupCtx (finC zeroC)) voidC) (.var 5) U0 := .var 5
  have tQty : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.pi voidC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm (void_typed lv) (D.tower.isUniverse _) (.headType (D.tower.headTyping _)) (D.tower.isUniverse _)
      (D.tower.join _ _)
  have tQ : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.lam (.var 5)) (.pi voidC (.head (.sort lv))) :=
    .lamIntro tQty (D.tower.isUniverse _) (D.tower.lift tA₆ lv)
  have ti : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.var 0) (finC zeroC) := .var 0
  have tsnd : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.snd (.var 0)) (belowC zeroC (.fst (.var 0))) :=
    .sndElim ti
  have tvoid : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.snd (.var 0)) voidC :=
    Typed.convType tsnd ⟨u, D.tower.isUniverse _, below_zero_eq lv (.fstElim ti)⟩
  have tRec := voidRec_typed lv tQ tvoid
  have tA₅ : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.var 4) U0 := .var 4
  have beta : Equal (rules lv) (.snoc lookupCtx (finC zeroC)) (.app (.lam (.var 5)) (.snd (.var 0)))
      (.var 4) (.head (.sort lv)) :=
    .betaPi tQty (D.tower.isUniverse _) (D.tower.lift tA₆ lv) tvoid
  have tBody : Typed (rules lv) (.snoc lookupCtx (finC zeroC))
      (voidRecC (.lam (.var 5)) (.snd (.var 0))) (.var 4) :=
    Typed.convType tRec ⟨_, D.tower.isUniverse _, beta⟩
  have tA₄ : Typed (rules lv) (.snoc lookupCtx (finC zeroC)) (.var 4) U0 := tA₅
  have tFun : Typed (rules lv) lookupCtx (lookupNil (.var 3)) (.pi (finC zeroC) (.var 4)) :=
    .lamIntro (D.tower.pi_small (fin_typed lv D.zero_typed) tA₄) (D.tower.isUniverse _) tBody
  have tPzt : Typed (rules lv) lookupCtx (.app (.app (lookupMotive (.var 3)) zeroC) ttC) U0 :=
    .appElim (.appElim (lookupMotive_typed lv) D.zero_typed) (D.nil_typed (.var 3))
  have ePzt : TypeEq (rules lv) lookupCtx (.app (.app (lookupMotive (.var 3)) zeroC) ttC)
      (.pi (finC zeroC) (.var 4)) :=
    typeEq_of_reduces lv formed (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tPzt
  exact Typed.convType tFun ePzt.symm

/-- A type of a universe is equal to the type it reduces to. -/
theorem typeEq_of_reduces_at {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    {T T' : Tm Tower.Head n} {l : LevelExpr Nat} (red : Reduces (rules lv) T T')
    (typed : Typed (rules lv) Γ T (.head (.sort l))) : TypeEq (rules lv) Γ T T' :=
  ⟨_, LevelTower.IsUniverse.sort _, (TowerVectors.reduces_preserve formed red typed).2⟩

/-! ### The method at `pair a w` -/

/-- The method's context up to the vector: `lookupCtx, k : num, a : A, w : vec A k`. -/
abbrev lookupCtx₇ : Ctx Tower.Head 7 :=
  .snoc (.snoc (.snoc lookupCtx numC) (.var 4)) (vecC (.var 5) (.var 1))

/-- The hypothesis' type `P k w`. -/
abbrev lookupIh : Tm Tower.Head 7 :=
  .app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
    (lookupMotive (.var 3))))) (.var 2)) (.var 0)

/-- With the hypothesis `ih : P k w`. -/
abbrev lookupCtx₈ : Ctx Tower.Head 8 := .snoc lookupCtx₇ lookupIh

/-- The method's result type `P (succ k) (pair a w)`. -/
abbrev lookupTarget : Tm Tower.Head 8 :=
  .app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
    (Presentation.rename wk (lookupMotive (.var 3)))))) (succC (.var 3))) (.pair (.var 2) (.var 1))

/-- With the index `i : fin (succ k)`. -/
abbrev lookupCtx₉ : Ctx Tower.Head 9 := .snoc lookupCtx₈ (finC (succC (.var 3)))

theorem lookupIh_typed : Typed (rules lv) lookupCtx₇ lookupIh U0 := by
  have tP : Typed (rules lv) lookupCtx₇
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (lookupMotive (.var 3)))))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (vecMotive (.var 3))))) :=
    (lookupMotive_typed lv).weaken.weaken.weaken
  have tk : Typed (rules lv) lookupCtx₇ (.var 2) numC := .var 2
  have tw : Typed (rules lv) lookupCtx₇ (.var 0) (vecC (.var 6) (.var 2)) := .var 0
  exact .appElim (.appElim tP tk) tw

theorem lookupCtx₈_formed : CtxFormed (rules lv) lookupCtx₈ := by
  have D := vecDeclared_rules lv
  have tA₅ : Typed (rules lv) (.snoc lookupCtx numC) (.var 4) U0 := .var 4
  have tA₆ : Typed (rules lv) (.snoc (.snoc lookupCtx numC) (.var 4)) (.var 5) U0 := .var 5
  have tk₆ : Typed (rules lv) (.snoc (.snoc lookupCtx numC) (.var 4)) (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc (lookupCtx_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tA₅⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA₆ tk₆⟩)
    ⟨_, D.tower.isUniverse _, lookupIh_typed lv⟩

theorem lookupCtx₉_formed : CtxFormed (rules lv) lookupCtx₉ := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) lookupCtx₈ (.var 3) numC := .var 3
  exact .snoc (lookupCtx₈_formed lv) ⟨_, D.tower.isUniverse _, fin_typed lv (D.succ_typed tk)⟩

theorem lookupTarget_typed : Typed (rules lv) lookupCtx₈ lookupTarget U0 := by
  have D := vecDeclared_rules lv
  have tP : Typed (rules lv) lookupCtx₈
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (lookupMotive (.var 3))))))
      (.pi numC (.pi (vecC (.var 8) (.var 0)) U0)) :=
    (lookupMotive_typed lv).weaken.weaken.weaken.weaken
  have tA : Typed (rules lv) lookupCtx₈ (.var 7) U0 := .var 7
  have tk : Typed (rules lv) lookupCtx₈ (.var 3) numC := .var 3
  have ta : Typed (rules lv) lookupCtx₈ (.var 2) (.var 7) := .var 2
  have tw : Typed (rules lv) lookupCtx₈ (.var 1) (vecC (.var 7) (.var 3)) := .var 1
  exact .appElim (.appElim tP (D.succ_typed tk)) (D.cons_typed tA tk ta tw)

/-- The method's result type is `fin (succ k) → A`, by beta. -/
theorem lookupTarget_eq :
    TypeEq (rules lv) lookupCtx₈ lookupTarget (.pi (finC (succC (.var 3))) (.var 8)) :=
  typeEq_of_reduces lv (lookupCtx₈_formed lv)
    (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) (lookupTarget_typed lv)

/-- The motive of the case analysis on the index: `λ j. below (succ k) j → A`. -/
abbrev caseMotive : Tm Tower.Head 9 := .lam (.pi (belowC (succC (.var 5)) (.var 0)) (.var 10))

/-- At the index zero: `λ _. a`. -/
abbrev caseZero : Tm Tower.Head 9 := .lam (.var 4)

/-- At a successor index: `λ j _ p. ih (pair j p)`. -/
abbrev caseSucc : Tm Tower.Head 9 := .lam (.lam (.lam (.app (.var 4) (.pair (.var 2) (.var 0)))))

/-- The method's body: the case analysis on the index, applied to its proof. -/
abbrev lookupBody : Tm Tower.Head 9 :=
  .app (numRecC caseMotive caseZero caseSucc (.fst (.var 0))) (.snd (.var 0))

theorem lookupCons_eq :
    lookupCons (.var 3 : Tm Tower.Head 4) = .lam (.lam (.lam (.lam (.lam lookupBody)))) := rfl

theorem caseMotive_typed : Typed (rules lv) lookupCtx₉ caseMotive (.pi numC (.head (.sort lv))) := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) (.snoc lookupCtx₉ numC) (.var 5) numC := .var 5
  have tj : Typed (rules lv) (.snoc lookupCtx₉ numC) (.var 0) numC := .var 0
  have tA : Typed (rules lv) (.snoc (.snoc lookupCtx₉ numC) (belowC (succC (.var 5)) (.var 0))) (.var 10)
      U0 := .var 10
  have tBody : Typed (rules lv) (.snoc lookupCtx₉ numC)
      (.pi (belowC (succC (.var 5)) (.var 0)) (.var 10)) (.head (.sort lv)) :=
    D.tower.lift (D.tower.pi_small (below_typed lv (D.succ_typed tk) tj) tA) lv
  have tPi : Typed (rules lv) lookupCtx₉ (.pi numC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm D.num_typed (D.tower.isUniverse _) (.headType (D.tower.headTyping _)) (D.tower.isUniverse _)
      (D.tower.join _ _)
  exact .lamIntro tPi (D.tower.isUniverse _) tBody

theorem caseZero_typed : Typed (rules lv) lookupCtx₉ caseZero (.app caseMotive zeroC) := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) lookupCtx₉ (.var 4) numC := .var 4
  have tDom : Typed (rules lv) lookupCtx₉ (belowC (succC (.var 4)) zeroC) U0 :=
    below_typed lv (D.succ_typed tk) D.zero_typed
  have tA : Typed (rules lv) (.snoc lookupCtx₉ (belowC (succC (.var 4)) zeroC)) (.var 9) U0 := .var 9
  have ta : Typed (rules lv) (.snoc lookupCtx₉ (belowC (succC (.var 4)) zeroC)) (.var 4) (.var 9) := .var 4
  have natural : Typed (rules lv) lookupCtx₉ caseZero (.pi (belowC (succC (.var 4)) zeroC) (.var 9)) :=
    .lamIntro (D.tower.pi_small tDom tA) (D.tower.isUniverse _) ta
  have tApp : Typed (rules lv) lookupCtx₉ (.app caseMotive zeroC) (.head (.sort lv)) :=
    .appElim (caseMotive_typed lv) D.zero_typed
  have e : TypeEq (rules lv) lookupCtx₉ (.app caseMotive zeroC)
      (.pi (belowC (succC (.var 4)) zeroC) (.var 9)) :=
    typeEq_of_reduces_at lv (lookupCtx₉_formed lv) (.single (.betaPi _ _)) tApp
  exact Typed.convType natural e.symm

/-- With the index `j : num` of the case analysis. -/
abbrev caseCtx₁₀ : Ctx Tower.Head 10 := .snoc lookupCtx₉ numC

/-- With the hypothesis of the case analysis, `r : below (succ k) j → A`. -/
abbrev caseCtx₁₁ : Ctx Tower.Head 11 :=
  .snoc caseCtx₁₀ (.app (Presentation.rename wk caseMotive) (.var 0))

/-- With the proof `p : below (succ k) (succ j)`. -/
abbrev caseCtx₁₂ : Ctx Tower.Head 12 := .snoc caseCtx₁₁ (belowC (succC (.var 6)) (succC (.var 1)))

theorem caseCtx₁₁_formed : CtxFormed (rules lv) caseCtx₁₁ := by
  have D := vecDeclared_rules lv
  have tM : Typed (rules lv) caseCtx₁₀ (Presentation.rename wk caseMotive) (.pi numC (.head (.sort lv))) :=
    (caseMotive_typed lv).weaken
  have tj : Typed (rules lv) caseCtx₁₀ (.var 0) numC := .var 0
  have tDom : Typed (rules lv) caseCtx₁₀ (.app (Presentation.rename wk caseMotive) (.var 0))
      (.head (.sort lv)) := .appElim tM tj
  exact .snoc (.snoc (lookupCtx₉_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tDom⟩

theorem caseCtx₁₂_formed : CtxFormed (rules lv) caseCtx₁₂ := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) caseCtx₁₁ (.var 6) numC := .var 6
  have tj : Typed (rules lv) caseCtx₁₁ (.var 1) numC := .var 1
  exact .snoc (caseCtx₁₁_formed lv)
    ⟨_, D.tower.isUniverse _, below_typed lv (D.succ_typed tk) (D.succ_typed tj)⟩

/-- In the successor case, the recursive call at the predecessor index: `ih (pair j p) : A`, since
`below (succ k) (succ j) ≡ below k j`. -/
theorem caseSucc_inner :
    Typed (rules lv) caseCtx₁₂ (.app (.var 4) (.pair (.var 2) (.var 0))) (.var 11) := by
  have D := vecDeclared_rules lv
  have tIhTy : Typed (rules lv) caseCtx₁₂
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (Presentation.rename wk lookupIh))))) U0 :=
    (lookupIh_typed lv).weaken.weaken.weaken.weaken.weaken
  have eIh : TypeEq (rules lv) caseCtx₁₂
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (Presentation.rename wk lookupIh))))) (.pi (finC (.var 7)) (.var 12)) :=
    typeEq_of_reduces lv (caseCtx₁₂_formed lv)
      (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tIhTy
  have tih₀ : Typed (rules lv) caseCtx₁₂ (.var 4)
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (Presentation.rename wk lookupIh))))) := .var 4
  have tih : Typed (rules lv) caseCtx₁₂ (.var 4) (.pi (finC (.var 7)) (.var 12)) :=
    Typed.convType tih₀ eIh
  have tk : Typed (rules lv) caseCtx₁₂ (.var 7) numC := .var 7
  have tj : Typed (rules lv) caseCtx₁₂ (.var 2) numC := .var 2
  have tp₀ : Typed (rules lv) caseCtx₁₂ (.var 0) (belowC (succC (.var 7)) (succC (.var 2))) := .var 0
  have tp : Typed (rules lv) caseCtx₁₂ (.var 0) (belowC (.var 7) (.var 2)) :=
    Typed.convType tp₀ ⟨u, D.tower.isUniverse _, below_succ_succ_eq lv tk tj⟩
  have tpair : Typed (rules lv) caseCtx₁₂ (.pair (.var 2) (.var 0)) (finC (.var 7)) :=
    .pairIntro (fin_typed lv tk) (D.tower.isUniverse _) tj tp
  exact .appElim tih tpair

theorem caseSucc_typed :
    Typed (rules lv) lookupCtx₉ caseSucc
      (.pi numC (.pi (.app (Presentation.rename wk caseMotive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk caseMotive)) (succC (.var 1))))) := by
  have D := vecDeclared_rules lv
  have tM₁ : Typed (rules lv) caseCtx₁₀ (Presentation.rename wk caseMotive)
      (.pi numC (.head (.sort lv))) := (caseMotive_typed lv).weaken
  have tM₂ : Typed (rules lv) caseCtx₁₁ (Presentation.rename wk (Presentation.rename wk caseMotive))
      (.pi numC (.head (.sort lv))) := (caseMotive_typed lv).weaken.weaken
  have tj₁₀ : Typed (rules lv) caseCtx₁₀ (.var 0) numC := .var 0
  have tj₁₁ : Typed (rules lv) caseCtx₁₁ (.var 1) numC := .var 1
  have tk₁₁ : Typed (rules lv) caseCtx₁₁ (.var 6) numC := .var 6
  have tDom : Typed (rules lv) caseCtx₁₀ (.app (Presentation.rename wk caseMotive) (.var 0))
      (.head (.sort lv)) := .appElim tM₁ tj₁₀
  have tCod : Typed (rules lv) caseCtx₁₁
      (.app (Presentation.rename wk (Presentation.rename wk caseMotive)) (succC (.var 1)))
      (.head (.sort lv)) := .appElim tM₂ (D.succ_typed tj₁₁)
  have tBelow : Typed (rules lv) caseCtx₁₁ (belowC (succC (.var 6)) (succC (.var 1))) U0 :=
    below_typed lv (D.succ_typed tk₁₁) (D.succ_typed tj₁₁)
  have tA₁₂ : Typed (rules lv) caseCtx₁₂ (.var 11) U0 := .var 11
  have natural : Typed (rules lv) caseCtx₁₁ (.lam (.app (.var 4) (.pair (.var 2) (.var 0))))
      (.pi (belowC (succC (.var 6)) (succC (.var 1))) (.var 11)) :=
    .lamIntro (D.tower.pi_small tBelow tA₁₂) (D.tower.isUniverse _) (caseSucc_inner lv)
  have e : TypeEq (rules lv) caseCtx₁₁
      (.app (Presentation.rename wk (Presentation.rename wk caseMotive)) (succC (.var 1)))
      (.pi (belowC (succC (.var 6)) (succC (.var 1))) (.var 11)) :=
    typeEq_of_reduces_at lv (caseCtx₁₁_formed lv) (.single (.betaPi _ _)) tCod
  have tInner : Typed (rules lv) caseCtx₁₁ (.lam (.app (.var 4) (.pair (.var 2) (.var 0))))
      (.app (Presentation.rename wk (Presentation.rename wk caseMotive)) (succC (.var 1))) :=
    Typed.convType natural e.symm
  have pInner := Derivable.piForm tDom (D.tower.isUniverse _) tCod (D.tower.isUniverse _)
    (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _) (.lamIntro pInner (D.tower.isUniverse _) tInner)

/-- **The method's body has type `A`**: the case analysis on the index by the recursor of numbers,
applied to the index's proof. -/
theorem lookupBody_typed : Typed (rules lv) lookupCtx₉ lookupBody (.var 8) := by
  have ti : Typed (rules lv) lookupCtx₉ (.var 0) (finC (succC (.var 4))) := .var 0
  have tfst : Typed (rules lv) lookupCtx₉ (.fst (.var 0)) numC := .fstElim ti
  have tsnd : Typed (rules lv) lookupCtx₉ (.snd (.var 0)) (belowC (succC (.var 4)) (.fst (.var 0))) :=
    .sndElim ti
  obtain ⟨w, hw, typed⟩ := TowerNumbersModel.recType_typed lv
  have tc : Typed (rules lv) lookupCtx₉ (.const numRec) (liftClosed (recType num (.sort lv) ctors)) :=
    .const rfl (Derivable.mono (sub_numbers₂ lv) typed) hw
  have m₀ : SubstMor (rules lv) .nil lookupCtx₉ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele num (.sort lv) ctors) lookupCtx₉
      (consSub (.fst (.var 0)) (consSub caseSucc (consSub caseZero
        (consSub caseMotive fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ (caseMotive_typed lv))
      (caseZero_typed lv)) (caseSucc_typed lv)) tfst
  have tRec : Typed (rules lv) lookupCtx₉ (numRecC caseMotive caseZero caseSucc (.fst (.var 0)))
      (.app caseMotive (.fst (.var 0))) := Typed.telescope_apply mor tc
  have tApp : Typed (rules lv) lookupCtx₉ (.app caseMotive (.fst (.var 0))) (.head (.sort lv)) :=
    .appElim (caseMotive_typed lv) tfst
  have e : TypeEq (rules lv) lookupCtx₉ (.app caseMotive (.fst (.var 0)))
      (.pi (belowC (succC (.var 4)) (.fst (.var 0))) (.var 9)) :=
    typeEq_of_reduces_at lv (lookupCtx₉_formed lv) (.single (.betaPi _ _)) tApp
  exact .appElim (Typed.convType tRec e) tsnd

/-- **The method at `pair a w`, at its type.** -/
theorem lookupCons_typed :
    Typed (rules lv) lookupCtx (lookupCons (.var 3)) (vecMethod (.var 3) (lookupMotive (.var 3))) := by
  have D := vecDeclared_rules lv
  have tk₈ : Typed (rules lv) lookupCtx₈ (.var 3) numC := .var 3
  have tA₉ : Typed (rules lv) lookupCtx₉ (.var 8) U0 := .var 8
  have natural : Typed (rules lv) lookupCtx₈ (.lam lookupBody) (.pi (finC (succC (.var 3))) (.var 8)) :=
    .lamIntro (D.tower.pi_small (fin_typed lv (D.succ_typed tk₈)) tA₉) (D.tower.isUniverse _)
      (lookupBody_typed lv)
  have tInner : Typed (rules lv) lookupCtx₈ (.lam lookupBody) lookupTarget :=
    Typed.convType natural (lookupTarget_eq lv).symm
  have tA₅ : Typed (rules lv) (.snoc lookupCtx numC) (.var 4) U0 := .var 4
  have tA₆ : Typed (rules lv) (.snoc (.snoc lookupCtx numC) (.var 4)) (.var 5) U0 := .var 5
  have tk₆ : Typed (rules lv) (.snoc (.snoc lookupCtx numC) (.var 4)) (.var 1) numC := .var 1
  have p₄ := D.tower.pi_small (lookupIh_typed lv) (lookupTarget_typed lv)
  have p₃ := D.tower.pi_small (D.vec_typed tA₆ tk₆) p₄
  have p₂ := D.tower.pi_small tA₅ p₃
  have p₁ := D.tower.pi_small D.num_typed p₂
  exact .lamIntro p₁ (D.tower.isUniverse _) (.lamIntro p₂ (D.tower.isUniverse _)
    (.lamIntro p₃ (D.tower.isUniverse _) (.lamIntro p₄ (D.tower.isUniverse _) tInner)))

/-- The eliminator on the vector gives a function on the indices: `fin n → A`. -/
theorem lookupFun_typed :
    Typed (rules lv) lookupCtx
      (vecElimC (.var 3) (lookupMotive (.var 3)) (lookupNil (.var 3)) (lookupCons (.var 3)) (.var 2)
        (.var 1))
      (.pi (finC (.var 2)) (.var 4)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) lookupCtx (.var 3) U0 := .var 3
  have tn : Typed (rules lv) lookupCtx (.var 2) numC := .var 2
  have tv : Typed (rules lv) lookupCtx (.var 1) (vecC (.var 3) (.var 2)) := .var 1
  have typing := D.vecElim_typed rfl tA (lookupMotive_typed lv) (lookupNil_typed lv)
    (lookupCons_typed lv) tn tv
  have tPnv : Typed (rules lv) lookupCtx (.app (.app (lookupMotive (.var 3)) (.var 2)) (.var 1)) U0 :=
    .appElim (.appElim (lookupMotive_typed lv) tn) tv
  have ePnv : TypeEq (rules lv) lookupCtx (.app (.app (lookupMotive (.var 3)) (.var 2)) (.var 1))
      (.pi (finC (.var 2)) (.var 4)) :=
    typeEq_of_reduces lv (lookupCtx_formed lv)
      (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tPnv
  exact Typed.convType typing ePnv

/-- **Lookup is typed at `A`**, in the context of its variables. -/
theorem lookup_typed :
    Typed (rules lv) lookupCtx (lookupTm (.var 3) (.var 2) (.var 1) (.var 0)) (.var 3) := by
  have ti : Typed (rules lv) lookupCtx (.var 0) (finC (.var 2)) := .var 0
  exact .appElim (lookupFun_typed lv) ti

/-! ### The equations of lookup, in conversion -/

/-- The context of the first equation: `A : U0, k : num, a : A, w : vec A k`. -/
abbrev fzCtx : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (vecC (.var 2) (.var 1))

theorem fzCtx_formed : CtxFormed (rules lv) fzCtx := by
  have D := vecDeclared_rules lv
  have tA₂ : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tA₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (.var 2) U0 := .var 2
  have tk₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, tA₂⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₃ tk₃⟩

/-- **Lookup at the first index**: `lookup A (succ k) (pair a w) fz ≡ a : A`. -/
theorem lookup_fz :
    Equal (rules lv) fzCtx (lookupTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) fzC) (.var 1)
      (.var 3) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) fzCtx (.var 3) U0 := .var 3
  have tk : Typed (rules lv) fzCtx (.var 2) numC := .var 2
  have ta : Typed (rules lv) fzCtx (.var 1) (.var 3) := .var 1
  have tw : Typed (rules lv) fzCtx (.var 0) (vecC (.var 3) (.var 2)) := .var 0
  have m₀ : SubstMor (rules lv) .nil fzCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) lookupCtx fzCtx
      (consSub fzC (consSub (.pair (.var 1) (.var 0)) (consSub (succC (.var 2)) (consSub (.var 3)
        fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) (D.succ_typed tk))
      (D.cons_typed tA tk ta tw)) (fz_typed lv tk)
  have typing := (lookup_typed lv).substitute mor
  have red : Reduces (rules lv)
      (lookupTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) fzC : Tm Tower.Head 4) (.var 1) := by
    refine .head (.congAppFun (.root (elim_succ_step lv (.var 3) (lookupMotive (.var 3))
      (lookupNil (.var 3)) (lookupCons (.var 3)) (.var 2) (.pair (.var 1) (.var 0))))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _))))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.congAppFun (.congAppArg (.betaSigmaFst _ _))) ?_
    refine .head (.congAppArg (.betaSigmaSnd _ _)) ?_
    refine .head (.congAppFun (.root (num_zero_step lv _ _ _))) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.betaSigmaFst _ _) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (fzCtx_formed lv) red typing).2

/-- The context of the second equation: `A : U0, k : num, a : A, w : vec A k, i : fin k`. -/
abbrev fsCtx : Ctx Tower.Head 5 := .snoc fzCtx (finC (.var 2))

theorem fsCtx_formed : CtxFormed (rules lv) fsCtx := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) fzCtx (.var 2) numC := .var 2
  exact .snoc (fzCtx_formed lv) ⟨_, D.tower.isUniverse _, fin_typed lv tk⟩

/-- **Lookup at a successor index**: `lookup A (succ k) (pair a w) (fs i) ≡ lookup A k w i : A`.
The eliminator computes to the lookup at `pair (fst i) (snd i)`, which is `i` by eta for pairs. -/
theorem lookup_fs :
    Equal (rules lv) fsCtx
      (lookupTm (.var 4) (succC (.var 3)) (.pair (.var 2) (.var 1)) (fsC (.var 0)))
      (lookupTm (.var 4) (.var 3) (.var 1) (.var 0)) (.var 4) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) fsCtx (.var 4) U0 := .var 4
  have tk : Typed (rules lv) fsCtx (.var 3) numC := .var 3
  have ta : Typed (rules lv) fsCtx (.var 2) (.var 4) := .var 2
  have tw : Typed (rules lv) fsCtx (.var 1) (vecC (.var 4) (.var 3)) := .var 1
  have ti : Typed (rules lv) fsCtx (.var 0) (finC (.var 3)) := .var 0
  have m₀ : SubstMor (rules lv) .nil fsCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) lookupCtx fsCtx
      (consSub (fsC (.var 0)) (consSub (.pair (.var 2) (.var 1)) (consSub (succC (.var 3))
        (consSub (.var 4) fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) (D.succ_typed tk))
      (D.cons_typed tA tk ta tw)) (fs_typed lv tk ti)
  have typing := (lookup_typed lv).substitute mor
  have red : Reduces (rules lv)
      (lookupTm (.var 4) (succC (.var 3)) (.pair (.var 2) (.var 1)) (fsC (.var 0)) : Tm Tower.Head 5)
      (lookupTm (.var 4) (.var 3) (.var 1) (.pair (.fst (.var 0)) (.snd (.var 0)))) := by
    refine .head (.congAppFun (.root (elim_succ_step lv (.var 4) (lookupMotive (.var 4))
      (lookupNil (.var 4)) (lookupCons (.var 4)) (.var 3) (.pair (.var 2) (.var 1))))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _))))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.congAppFun (.congAppArg (.betaSigmaFst _ _))) ?_
    refine .head (.congAppArg (.betaSigmaSnd _ _)) ?_
    refine .head (.congAppFun (.root (num_succ_step lv _ _ _ _))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.congAppFun (.congAppArg (.betaSigmaSnd _ _))) ?_
    exact .refl
  have computed := (TowerVectors.reduces_preserve (fsCtx_formed lv) red typing).2
  -- eta: `pair (fst i) (snd i) ≡ i`
  have m₁ : SubstMor (rules lv) lookupCtx fsCtx
      (consSub (.var 0) (consSub (.var 1) (consSub (.var 3) (consSub (.var 4)
        fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tk) tw) ti
  have tFun : Typed (rules lv) fsCtx
      (vecElimC (.var 4) (lookupMotive (.var 4)) (lookupNil (.var 4)) (lookupCons (.var 4)) (.var 3)
        (.var 1)) (.pi (finC (.var 3)) (.var 5)) := (lookupFun_typed lv).substitute m₁
  have tFin : Typed (rules lv) fsCtx (finC (.var 3)) U0 := fin_typed lv tk
  have tfst : Typed (rules lv) fsCtx (.fst (.var 0)) numC := .fstElim ti
  have tsnd : Typed (rules lv) fsCtx (.snd (.var 0)) (belowC (.var 3) (.fst (.var 0))) := .sndElim ti
  have tpair : Typed (rules lv) fsCtx (.pair (.fst (.var 0)) (.snd (.var 0))) (finC (.var 3)) :=
    .pairIntro tFin (D.tower.isUniverse _) tfst tsnd
  have eta : Equal (rules lv) fsCtx (.var 0) (.pair (.fst (.var 0)) (.snd (.var 0))) (finC (.var 3)) :=
    .etaSigma ti tpair (.symm (.betaFst tFin (D.tower.isUniverse _) tfst tsnd))
      (.symm (.betaSnd tFin (D.tower.isUniverse _) tfst tsnd))
  exact .trans computed (.appCong (.refl tFun) eta.symm)

/-! ### No closed index of the empty vector -/

/-- The head constant of a typed spine is declared. -/
theorem spine_head_declared {R : Rules Tower.Head} {n : Nat} {Γ : Ctx Tower.Head n} {c : DeclName}
    (args : List (Tm Tower.Head n)) :
    ∀ {T : Tm Tower.Head n}, Typed R Γ (appSpine (.const c) args) T →
      ∃ type, R.constantType c = some type := by
  induction args using List.reverseRecOn with
  | nil =>
      intro T typing
      have typing' : Typed R Γ (.const c) T := typing
      obtain ⟨type, w, declared, _, _, _⟩ := Typed.generation typing'
      exact ⟨type, declared⟩
  | append_singleton init last ih =>
      intro T typing
      rw [appSpine_concat] at typing
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation typing
      exact ih tf

/-- Every argument of a typed spine is typed. -/
theorem spine_args_typed {R : Rules Tower.Head} {n : Nat} {Γ : Ctx Tower.Head n} {c : DeclName}
    (args : List (Tm Tower.Head n)) :
    ∀ {T : Tm Tower.Head n}, Typed R Γ (appSpine (.const c) args) T →
      ∀ a ∈ args, ∃ A, Typed R Γ a A := by
  induction args using List.reverseRecOn with
  | nil =>
      intro T _ a mem
      exact absurd mem List.not_mem_nil
  | append_singleton init last ih =>
      intro T typing a mem
      rw [appSpine_concat] at typing
      obtain ⟨A, B, tf, ta, _⟩ := Typed.generation typing
      rcases List.mem_append.mp mem with h | h
      · exact ih tf a h
      · obtain rfl := List.mem_singleton.mp h
        exact ⟨A, ta⟩

/-- Every computing constant of the package inspects one argument, for a constructor. -/
theorem roles_computes {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : roles c = .computes arity inspect) :
    ∃ k, inspect = .split k .constructor fun _ => .leaf := by
  unfold roles at role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  split at role
  · cases role
    exact ⟨_, rfl⟩
  unfold TowerNumbersModel.roles at role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
    exact ⟨_, rfl⟩
  · cases role

/-- No declared constant of the package is rigid. -/
theorem declared_not_rigid {c : DeclName} {type : Tm Tower.Head 0}
    (declared : (rules lv).constantType c = some type) : roles c ≠ .rigid := by
  change constantType lv c = some type at declared
  unfold constantType at declared
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_add] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_vecElim] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_numRec] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_voidRec] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_below] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_belowStep] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_idElim] at role; cases role
  change (if c = vec then some vecType
    else if c = unitRec then some (recType unit (.sort lv) unitCtors)
    else baseStage.constantType c) = some type at declared
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_vec] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_unitRec] at role; cases role
  change (if c = unit then some (.head u) else if c = tt then some (ctorType unit [])
    else if c = void then some (.head u)
    else TowerNumbersModel.rules₂.constantType c) = some type at declared
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_unit] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_tt] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_void] at role; cases role
  change (if c = num then some (.head u) else if c = zero then some (ctorType num [])
    else if c = succ then some (ctorType num [.recursive]) else none) = some type at declared
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_num] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_zero] at role; cases role
  split at declared
  · rename_i h; subst h; exact fun role => by rw [roles_succ] at role; cases role
  · cases declared

/-- **No closed neutral term is typed**: a neutral term is headed by a variable or by a rigid
constant, and the package declares no rigid constant. -/
theorem no_closed_neutral : ∀ {n : Nat} {t : Tm Tower.Head n}, Neutral roles t → n = 0 →
    ∀ (Γ : Ctx Tower.Head n) (T : Tm Tower.Head n), ¬ Typed (rules lv) Γ t T := by
  intro n t neutral
  induction neutral with
  | var i =>
      intro h
      subst h
      exact i.elim0
  | app _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tf, _, _⟩ := Typed.generation typing
      exact ih h Γ _ tf
  | fst _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      exact ih h Γ _ tp
  | snd _ ih =>
      intro h Γ T typing
      obtain ⟨A, B, tp, _⟩ := Typed.generation typing
      exact ih h Γ _ tp
  | rigid args role =>
      intro _ Γ T typing
      obtain ⟨type, declared⟩ := spine_head_declared args typing
      exact declared_not_rigid lv declared role
  | @stuck _ _ _ args _ a role _ focus _ _ ih =>
      intro h Γ T typing
      obtain ⟨k, rfl⟩ := roles_computes role
      obtain ⟨before, after, _, split, _, _⟩ := focus.single
      have mem : a ∈ args := by
        rw [split]
        simp
      obtain ⟨A, ta⟩ := spine_args_typed args typing a mem
      exact ih h Γ A ta

/-- **The empty type has no closed term.** A closed term of `void` reduces, in the model, to a
constructor form, of which `void` has none, or to a neutral term, of which there is none. -/
theorem void_empty {t : Tm Tower.Head 0} : ¬ Typed (rules lv) .nil t voidC := by
  intro typing
  have laws' := laws lv fun _ => 0
  have reducible := (Typed.reducible (S := settingAt lv (fun _ => 0) (declarative (rules lv))) laws'
    (constants lv _) typing .nil).2
  rw [(declaresVoid lv (fun _ => 0) (E := declarative (rules lv))).packOf_type laws' .nil] at reducible
  change IndRedTm (settingAt lv (fun _ => 0) (declarative (rules lv))) .nil void [] _ t at reducible
  cases reducible with
  | mk red conv normal =>
      cases normal with
      | ctor mem _ => exact absurd mem List.not_mem_nil
      | neutral neutral _ => exact no_closed_neutral lv neutral rfl .nil _ red.target

/-- **`fin zero` has no closed term**: the empty vector has no index. -/
theorem fin_zero_empty {t : Tm Tower.Head 0} : ¬ Typed (rules lv) .nil t (finC zeroC) := by
  intro typing
  have tsnd : Typed (rules lv) .nil (.snd t) (belowC zeroC (.fst t)) := .sndElim typing
  exact void_empty lv (Typed.convType tsnd
    ⟨u, LevelTower.IsUniverse.sort _, below_zero_eq lv (.fstElim typing)⟩)

/-- **Positive control: `fin (succ zero)` has a closed term**, the first index. -/
theorem fin_one_inhabited : Typed (rules lv) .nil fzC (finC (succC zeroC)) :=
  fz_typed lv (vecDeclared_rules lv).zero_typed

end TowerVectorsLookup

#print axioms TowerVectorsLookup.fz_typed
#print axioms TowerVectorsLookup.fs_typed
#print axioms TowerVectorsLookup.fin_zero_void
#print axioms TowerVectorsLookup.lookupNil_typed
#print axioms TowerVectorsLookup.lookupCons_typed
#print axioms TowerVectorsLookup.lookup_typed
#print axioms TowerVectorsLookup.lookup_fz
#print axioms TowerVectorsLookup.lookup_fs
#print axioms TowerVectorsLookup.no_closed_neutral
#print axioms TowerVectorsLookup.void_empty
#print axioms TowerVectorsLookup.fin_zero_empty
#print axioms TowerVectorsLookup.fin_one_inhabited

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
