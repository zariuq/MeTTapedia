import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectors

/-!
# Vector programs by the dependent eliminator

Programs over the package `TowerVectorsModel.rules`, written with the eliminator `vec-elim`:

* `append A n m xs ys = vec-elim A (λ k _. vec A (add k m)) ys (λ k a v ih. pair a ih) n xs`,
  typed at `vec A (add n m)` (`append_typed`), with both equations in conversion:
  `append A zero m tt ys ≡ ys` (`append_nil`) and
  `append A (succ k) m (pair a v) ys ≡ pair a (append A k m v ys)` (`append_cons`), each at the
  declared type `vec A (add n m)` of its call, by addition computing in conversion;
* `head v = fst v` on vectors of successor length (`head_typed`, `head_cons`), with the empty vector
  rejected (`head_nil_rejected`). The same function written with the eliminator and a motive
  computed from the length is in `TowerVectorsHead`, where the two are proved equal.

Each program is stated as a judgment in the context of its variables; its instances are its
substitutions (`append_nil` and `append_cons` are obtained from `append_typed` that way). The
closed program `appendProgram` has the dependent function type
`Π (A : U0) (n m : num). vec A n → vec A m → vec A (add n m)` (`appendProgram_typed`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TowerVectorsModel
open TowerNumbersModel (num zero succ u)

namespace TowerVectorsPrograms

variable (lv : LevelExpr Nat)

/-! ## Helpers -/

theorem add_typed {n : Nat} {Γ : Ctx Tower.Head n} {a b : Tm Tower.Head n}
    (ta : Typed (rules lv) Γ a numC) (tb : Typed (rules lv) Γ b numC) :
    Typed (rules lv) Γ (addC a b) numC := by
  have D := vecDeclared_rules lv
  have tAdd : Typed (rules lv) Γ (.const add) (.pi numC (.pi numC numC)) :=
    .const (type := .pi numC (.pi numC numC)) rfl (D.tower.pi_small D.num_typed
      (D.tower.pi_small D.num_typed D.num_typed)) (D.tower.isUniverse _)
  exact .appElim (.appElim tAdd ta) tb

/-- `vec A k ≡ vec A k'` when `k ≡ k'`. -/
theorem vec_congr {n : Nat} {Γ : Ctx Tower.Head n} {A k k' : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (e : Equal (rules lv) Γ k k' numC) :
    TypeEq (rules lv) Γ (vecC A k) (vecC A k') := by
  have D := vecDeclared_rules lv
  have tvA : Typed (rules lv) Γ (.app (.const vec) A) (.pi numC U0) := .appElim D.vec_const_typed tA
  exact ⟨u, D.tower.isUniverse _, .appCong (.refl tvA) e⟩

/-- A small type is equal to the type it reduces to. -/
theorem typeEq_of_reduces {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    {T T' : Tm Tower.Head n} (red : Reduces (rules lv) T T') (typed : Typed (rules lv) Γ T U0) :
    TypeEq (rules lv) Γ T T' :=
  ⟨u, LevelTower.IsUniverse.sort _, (TowerVectors.reduces_preserve formed red typed).2⟩

/-! ## Append -/

/-- The motive of append: `λ k _. vec A (add k m)`. -/
def appendMotive {n : Nat} (A m : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (vecC (Presentation.rename wk (Presentation.rename wk A))
    (addC (.var 1) (Presentation.rename wk (Presentation.rename wk m)))))

/-- The method of append for `pair`: `λ k a v ih. pair a ih`. -/
def appendMethod {n : Nat} : Tm Tower.Head n := .lam (.lam (.lam (.lam (.pair (.var 2) (.var 0)))))

/-- **Append, by the eliminator on its first vector.** -/
def appendTm {n : Nat} (A k m xs ys : Tm Tower.Head n) : Tm Tower.Head n :=
  vecElimC A (appendMotive A m) ys appendMethod k xs

/-- The context of append's variables: `A : U0, n m : num, xs : vec A n, ys : vec A m`. -/
abbrev appendCtx : Ctx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (vecC (.var 2) (.var 1)))
    (vecC (.var 3) (.var 1))

theorem appendCtx_formed : CtxFormed (rules lv) appendCtx := by
  have D := vecDeclared_rules lv
  have tA₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2) U0 := .var 2
  have tn₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 1) numC := .var 1
  have tA₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (vecC (.var 2) (.var 1)))
      (.var 3) U0 := .var 3
  have tm₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (vecC (.var 2) (.var 1)))
      (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₃ tn₃⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA₄ tm₄⟩

/-- The motive at its type. -/
theorem appendMotive_typed :
    Typed (rules lv) appendCtx (appendMotive (.var 4) (.var 2)) (vecMotive (.var 4)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc appendCtx numC) (vecC (.var 5) (.var 0))) (.var 6) U0 :=
    .var 6
  have tk : Typed (rules lv) (.snoc (.snoc appendCtx numC) (vecC (.var 5) (.var 0))) (.var 1) numC :=
    .var 1
  have tm : Typed (rules lv) (.snoc (.snoc appendCtx numC) (vecC (.var 5) (.var 0))) (.var 4) numC :=
    .var 4
  have tBody := D.vec_typed tA (add_typed lv tk tm)
  have tA₁ : Typed (rules lv) (.snoc appendCtx numC) (.var 5) U0 := .var 5
  have tk₁ : Typed (rules lv) (.snoc appendCtx numC) (.var 0) numC := .var 0
  have tInner : Typed (rules lv) (.snoc appendCtx numC) (.pi (vecC (.var 5) (.var 0)) U0)
      (.head (.sort (.max (.const 0) (.succ (.const 0))))) :=
    .piForm (D.vec_typed tA₁ tk₁) (D.tower.isUniverse _) D.tower.u0_typed (D.tower.isUniverse _)
      (D.tower.join _ _)
  have tOuter : Typed (rules lv) appendCtx (vecMotive (.var 4))
      (.head (.sort (.max (.const 0) (.max (.const 0) (.succ (.const 0)))))) :=
    .piForm D.num_typed (D.tower.isUniverse _) tInner (D.tower.isUniverse _) (D.tower.join _ _)
  exact .lamIntro tOuter (D.tower.isUniverse _) (.lamIntro tInner (D.tower.isUniverse _) tBody)

/-- The context of the method's hypothesis: `appendCtx, k : num, a : A, v : vec A k`. -/
abbrev methodCtx₈ : Ctx Tower.Head 8 :=
  .snoc (.snoc (.snoc appendCtx numC) (.var 5)) (vecC (.var 6) (.var 1))

/-- The hypothesis' type `P k v`, over `methodCtx₈`. -/
abbrev ihType : Tm Tower.Head 8 :=
  .app (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
    (appendMotive (.var 4) (.var 2))))) (.var 2)) (.var 0)

/-- The context of the method's body: `methodCtx₈, ih : P k v`. -/
abbrev methodCtx : Ctx Tower.Head 9 := .snoc methodCtx₈ ihType

theorem ihType_typed : Typed (rules lv) methodCtx₈ ihType U0 := by
  have tP : Typed (rules lv) methodCtx₈
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (appendMotive (.var 4) (.var 2)))))
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (vecMotive (.var 4))))) :=
    (appendMotive_typed lv).weaken.weaken.weaken
  have tk : Typed (rules lv) methodCtx₈ (.var 2) numC := .var 2
  have tv : Typed (rules lv) methodCtx₈ (.var 0) (vecC (.var 7) (.var 2)) := .var 0
  exact .appElim (.appElim tP tk) tv

theorem methodCtx_formed : CtxFormed (rules lv) methodCtx := by
  have D := vecDeclared_rules lv
  have tA₆ : Typed (rules lv) (.snoc appendCtx numC) (.var 5) U0 := .var 5
  have tA₇ : Typed (rules lv) (.snoc (.snoc appendCtx numC) (.var 5)) (.var 6) U0 := .var 6
  have tk₇ : Typed (rules lv) (.snoc (.snoc appendCtx numC) (.var 5)) (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc (appendCtx_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tA₆⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA₇ tk₇⟩)
    ⟨_, D.tower.isUniverse _, ihType_typed lv⟩

/-- **The method at its type**: in the method's body, `pair a ih : P (succ k) (pair a v)`, because
`P (succ k) (pair a v) ≡ vec A (add (succ k) m) ≡ vec A (succ (add k m)) ≡ Σ A (vec A (add k m))`,
by beta, by addition and by `vec`'s equation. -/
theorem appendMethod_typed :
    Typed (rules lv) appendCtx appendMethod (vecMethod (.var 4) (appendMotive (.var 4) (.var 2))) := by
  have D := vecDeclared_rules lv
  have formed := methodCtx_formed lv
  have tA : Typed (rules lv) methodCtx (.var 8) U0 := .var 8
  have tk : Typed (rules lv) methodCtx (.var 3) numC := .var 3
  have tm : Typed (rules lv) methodCtx (.var 6) numC := .var 6
  have ta : Typed (rules lv) methodCtx (.var 2) (.var 8) := .var 2
  have tv : Typed (rules lv) methodCtx (.var 1) (vecC (.var 8) (.var 3)) := .var 1
  have tP : Typed (rules lv) methodCtx
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (appendMotive (.var 4) (.var 2))))))
      (.pi numC (.pi (vecC (.var 9) (.var 0)) U0)) :=
    (appendMotive_typed lv).weaken.weaken.weaken.weaken
  -- the hypothesis has type `vec A (add k m)`
  have tIhTy : Typed (rules lv) methodCtx (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (appendMotive (.var 4) (.var 2)))))) (.var 3))
      (.var 1)) U0 := .appElim (.appElim tP tk) tv
  have eIh : TypeEq (rules lv) methodCtx (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (appendMotive (.var 4) (.var 2)))))) (.var 3))
      (.var 1)) (vecC (.var 8) (addC (.var 3) (.var 6))) :=
    typeEq_of_reduces lv formed (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tIhTy
  have tih₀ : Typed (rules lv) methodCtx (.var 0) (.app (.app (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (appendMotive (.var 4) (.var 2)))))) (.var 3)) (.var 1)) := .var 0
  have tih : Typed (rules lv) methodCtx (.var 0) (vecC (.var 8) (addC (.var 3) (.var 6))) :=
    Typed.convType tih₀ eIh
  -- the pair
  have tPair : Typed (rules lv) methodCtx (.pair (.var 2) (.var 0))
      (vecC (.var 8) (succC (addC (.var 3) (.var 6)))) :=
    D.cons_typed tA (add_typed lv tk tm) ta tih
  have eAdd : TypeEq (rules lv) methodCtx (vecC (.var 8) (succC (addC (.var 3) (.var 6))))
      (vecC (.var 8) (addC (succC (.var 3)) (.var 6))) :=
    vec_congr lv tA (TowerVectors.add_succ tk tm).symm
  -- the target type, by beta
  have tPair' : Typed (rules lv) methodCtx (.pair (.var 2) (.var 1)) (vecC (.var 8) (succC (.var 3))) :=
    D.cons_typed tA tk ta tv
  have tTarget : Typed (rules lv) methodCtx (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (appendMotive (.var 4) (.var 2))))))
      (succC (.var 3))) (.pair (.var 2) (.var 1))) U0 := .appElim (.appElim tP (D.succ_typed tk)) tPair'
  have eTarget : TypeEq (rules lv) methodCtx (.app (.app (Presentation.rename wk (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (appendMotive (.var 4) (.var 2))))))
      (succC (.var 3))) (.pair (.var 2) (.var 1))) (vecC (.var 8) (addC (succC (.var 3)) (.var 6))) :=
    typeEq_of_reduces lv formed (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tTarget
  have tBody : Typed (rules lv) methodCtx (.pair (.var 2) (.var 0)) (.app (.app (Presentation.rename wk
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (appendMotive (.var 4) (.var 2)))))) (succC (.var 3))) (.pair (.var 2) (.var 1))) :=
    Typed.convType tPair (TypeEq.trans (levels lv fun _ => 0) eAdd eTarget.symm)
  -- the four abstractions
  have tA₆ : Typed (rules lv) (.snoc appendCtx numC) (.var 5) U0 := .var 5
  have tA₇ : Typed (rules lv) (.snoc (.snoc appendCtx numC) (.var 5)) (.var 6) U0 := .var 6
  have tk₇ : Typed (rules lv) (.snoc (.snoc appendCtx numC) (.var 5)) (.var 1) numC := .var 1
  have p₄ := D.tower.pi_small (ihType_typed lv) tTarget
  have p₃ := D.tower.pi_small (D.vec_typed tA₇ tk₇) p₄
  have p₂ := D.tower.pi_small tA₆ p₃
  have p₁ := D.tower.pi_small D.num_typed p₂
  exact .lamIntro p₁ (D.tower.isUniverse _) (.lamIntro p₂ (D.tower.isUniverse _)
    (.lamIntro p₃ (D.tower.isUniverse _) (.lamIntro p₄ (D.tower.isUniverse _) tBody)))

/-- **Append is typed at `vec A (add n m)`**, in the context of its variables. -/
theorem append_typed :
    Typed (rules lv) appendCtx (appendTm (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (vecC (.var 4) (addC (.var 3) (.var 2))) := by
  have D := vecDeclared_rules lv
  have formed := appendCtx_formed lv
  have tA : Typed (rules lv) appendCtx (.var 4) U0 := .var 4
  have tn : Typed (rules lv) appendCtx (.var 3) numC := .var 3
  have tm : Typed (rules lv) appendCtx (.var 2) numC := .var 2
  have txs : Typed (rules lv) appendCtx (.var 1) (vecC (.var 4) (.var 3)) := .var 1
  have tys : Typed (rules lv) appendCtx (.var 0) (vecC (.var 4) (.var 2)) := .var 0
  have tP := appendMotive_typed lv
  -- `ys : P zero tt`
  have tPzt : Typed (rules lv) appendCtx (.app (.app (appendMotive (.var 4) (.var 2)) zeroC) ttC) U0 :=
    .appElim (.appElim tP D.zero_typed) (D.nil_typed tA)
  have ePzt : TypeEq (rules lv) appendCtx (.app (.app (appendMotive (.var 4) (.var 2)) zeroC) ttC)
      (vecC (.var 4) (addC zeroC (.var 2))) :=
    typeEq_of_reduces lv formed (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tPzt
  have eZero : TypeEq (rules lv) appendCtx (vecC (.var 4) (addC zeroC (.var 2))) (vecC (.var 4) (.var 2)) :=
    vec_congr lv tA (TowerVectors.add_zero tm)
  have tpn : Typed (rules lv) appendCtx (.var 0) (.app (.app (appendMotive (.var 4) (.var 2)) zeroC) ttC) :=
    Typed.convType tys (TypeEq.trans (levels lv fun _ => 0) eZero.symm ePzt.symm)
  have typing := D.vecElim_typed rfl tA tP tpn (appendMethod_typed lv) tn txs
  -- `P n xs ≡ vec A (add n m)`
  have tPnx : Typed (rules lv) appendCtx (.app (.app (appendMotive (.var 4) (.var 2)) (.var 3)) (.var 1))
      U0 := .appElim (.appElim tP tn) txs
  have ePnx : TypeEq (rules lv) appendCtx (.app (.app (appendMotive (.var 4) (.var 2)) (.var 3)) (.var 1))
      (vecC (.var 4) (addC (.var 3) (.var 2))) :=
    typeEq_of_reduces lv formed (.tail (.single (.congAppFun (.betaPi _ _))) (.betaPi _ _)) tPnx
  exact Typed.convType typing ePnx

/-- **The closed program** `λ A n m xs ys. append A n m xs ys`. -/
def appendProgram : Tm Tower.Head 0 :=
  .lam (.lam (.lam (.lam (.lam (appendTm (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))))))

/-- Its type: `Π (A : U0) (n m : num). vec A n → vec A m → vec A (add n m)`. -/
def appendProgramType : Tm Tower.Head 0 :=
  .pi U0 (.pi numC (.pi numC (.pi (vecC (.var 2) (.var 1)) (.pi (vecC (.var 3) (.var 1))
    (vecC (.var 4) (addC (.var 3) (.var 2)))))))

theorem appendProgram_typed : Typed (rules lv) .nil appendProgram appendProgramType := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) appendCtx (.var 4) U0 := .var 4
  have tn : Typed (rules lv) appendCtx (.var 3) numC := .var 3
  have tm : Typed (rules lv) appendCtx (.var 2) numC := .var 2
  have tA₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2) U0 := .var 2
  have tn₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 1) numC := .var 1
  have tA₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (vecC (.var 2) (.var 1)))
      (.var 3) U0 := .var 3
  have tm₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (vecC (.var 2) (.var 1)))
      (.var 1) numC := .var 1
  have p₅ := D.tower.pi_small (D.vec_typed tA₄ tm₄) (D.vec_typed tA (add_typed lv tn tm))
  have p₄ := D.tower.pi_small (D.vec_typed tA₃ tn₃) p₅
  have p₃ := D.tower.pi_small D.num_typed p₄
  have p₂ := D.tower.pi_small D.num_typed p₃
  have p₁ := Derivable.piForm D.tower.u0_typed (D.tower.isUniverse _) p₂ (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro p₁ (D.tower.isUniverse _) (.lamIntro p₂ (D.tower.isUniverse _)
    (.lamIntro p₃ (D.tower.isUniverse _) (.lamIntro p₄ (D.tower.isUniverse _)
      (.lamIntro p₅ (D.tower.isUniverse _) (append_typed lv)))))

/-! ### The two equations of append, in conversion -/

/-- The context of the base case: `A : U0, m : num, ys : vec A m`. -/
abbrev nilCtx : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))

theorem nilCtx_formed : CtxFormed (rules lv) nilCtx := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tm : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 0) numC := .var 0
  exact .snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA tm⟩

/-- **The base case of append**: `append A zero m tt ys ≡ ys : vec A (add zero m)`. -/
theorem append_nil :
    Equal (rules lv) nilCtx (appendTm (.var 2) zeroC (.var 1) ttC (.var 0)) (.var 0)
      (vecC (.var 2) (addC zeroC (.var 1))) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) nilCtx (.var 2) U0 := .var 2
  have tm : Typed (rules lv) nilCtx (.var 1) numC := .var 1
  have tys : Typed (rules lv) nilCtx (.var 0) (vecC (.var 2) (.var 1)) := .var 0
  have m₀ : SubstMor (rules lv) .nil nilCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) appendCtx nilCtx
      (consSub (.var 0) (consSub ttC (consSub (.var 1) (consSub zeroC (consSub (.var 2)
        fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) D.zero_typed) tm)
      (D.nil_typed tA)) tys
  have typing := (append_typed lv).substitute mor
  have red : Reduces (rules lv) (appendTm (.var 2) zeroC (.var 1) ttC (.var 0) : Tm Tower.Head 3) (.var 0) :=
    .tail (.single (.root (elim_zero_step lv (.var 2) (appendMotive (.var 2) (.var 1)) (.var 0)
      appendMethod ttC))) (.root (unit_iota_step lv _ _))
  exact (TowerVectors.reduces_preserve (nilCtx_formed lv) red typing).2

/-- The context of the recursive case: `A : U0, k m : num, a : A, v : vec A k, ys : vec A m`. -/
abbrev consCtx : Ctx Tower.Head 6 :=
  .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2)) (vecC (.var 3) (.var 2)))
    (vecC (.var 4) (.var 2))

theorem consCtx_formed : CtxFormed (rules lv) consCtx := by
  have D := vecDeclared_rules lv
  have tA₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2) U0 := .var 2
  have tA₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2)) (.var 3) U0 :=
    .var 3
  have tk₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2)) (.var 2) numC :=
    .var 2
  have tA₅ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2))
      (vecC (.var 3) (.var 2))) (.var 4) U0 := .var 4
  have tm₅ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 2))
      (vecC (.var 3) (.var 2))) (.var 2) numC := .var 2
  exact .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tA₃⟩) ⟨_, D.tower.isUniverse _, D.vec_typed tA₄ tk₄⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₅ tm₅⟩

/-- The call of the recursive case: `append A (succ k) m (pair a v) ys`. -/
abbrev consCall : Tm Tower.Head 6 := appendTm (.var 5) (succC (.var 4)) (.var 3) (.pair (.var 2) (.var 1)) (.var 0)

/-- Its result: `pair a (append A k m v ys)`. -/
abbrev consResult : Tm Tower.Head 6 := .pair (.var 2) (appendTm (.var 5) (.var 4) (.var 3) (.var 1) (.var 0))

/-- The call at its declared type `vec A (add (succ k) m)`. -/
theorem consCall_typed :
    Typed (rules lv) consCtx consCall (vecC (.var 5) (addC (succC (.var 4)) (.var 3))) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) consCtx (.var 5) U0 := .var 5
  have tk : Typed (rules lv) consCtx (.var 4) numC := .var 4
  have tm : Typed (rules lv) consCtx (.var 3) numC := .var 3
  have ta : Typed (rules lv) consCtx (.var 2) (.var 5) := .var 2
  have tv : Typed (rules lv) consCtx (.var 1) (vecC (.var 5) (.var 4)) := .var 1
  have tys : Typed (rules lv) consCtx (.var 0) (vecC (.var 5) (.var 3)) := .var 0
  have m₀ : SubstMor (rules lv) .nil consCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) appendCtx consCtx
      (consSub (.var 0) (consSub (.pair (.var 2) (.var 1)) (consSub (.var 3) (consSub (succC (.var 4))
        (consSub (.var 5) fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) (D.succ_typed tk)) tm)
      (D.cons_typed tA tk ta tv)) tys
  exact (append_typed lv).substitute mor

/-- **The recursive case of append, in conversion**:
`append A (succ k) m (pair a v) ys ≡ pair a (append A k m v ys) : vec A (add (succ k) m)`. -/
theorem append_cons :
    Equal (rules lv) consCtx consCall consResult (vecC (.var 5) (addC (succC (.var 4)) (.var 3))) := by
  have red : Reduces (rules lv) consCall consResult := by
    refine .head (.root (elim_succ_step lv (.var 5) (appendMotive (.var 5) (.var 3)) (.var 0)
      appendMethod (.var 4) (.pair (.var 2) (.var 1)))) ?_
    refine .head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.congPairFst (.betaSigmaFst _ _)) ?_
    refine .head (.congPairSnd (.congAppArg (.betaSigmaSnd _ _))) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (consCtx_formed lv) red (consCall_typed lv)).2

/-- **The result of the recursive case has the call's declared type**, `vec A (add (succ k) m)`,
by conversion: `vec A (add (succ k) m) ≡ vec A (succ (add k m)) ≡ Σ A (vec A (add k m))`. -/
theorem consResult_typed :
    Typed (rules lv) consCtx consResult (vecC (.var 5) (addC (succC (.var 4)) (.var 3))) :=
  (Equal.typed (S := setting lv fun _ => 0) (append_cons lv) (consCtx_formed lv)).2

/-- The declared type of the call and the type of the result, related by addition:
`vec A (add (succ k) m) ≡ vec A (succ (add k m))`. -/
theorem cons_types :
    TypeEq (rules lv) consCtx (vecC (.var 5) (addC (succC (.var 4)) (.var 3)))
      (vecC (.var 5) (succC (addC (.var 4) (.var 3)))) := by
  have tA : Typed (rules lv) consCtx (.var 5) U0 := .var 5
  have tk : Typed (rules lv) consCtx (.var 4) numC := .var 4
  have tm : Typed (rules lv) consCtx (.var 3) numC := .var 3
  exact vec_congr lv tA (TowerVectors.add_succ tk tm)

/-! ## Head -/

/-- **Head on non-empty vectors**: `fst v : A` for `v : vec A (succ k)`. -/
theorem head_typed {n : Nat} {Γ : Ctx Tower.Head n} {A k v : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tk : Typed (rules lv) Γ k numC)
    (tv : Typed (rules lv) Γ v (vecC A (succC k))) : Typed (rules lv) Γ (.fst v) A :=
  (vecDeclared_rules lv).fst_typed tA tk tv

/-- **Head computes on an extended vector**: `head (pair a v) ≡ a`. -/
theorem head_cons {n : Nat} {Γ : Ctx Tower.Head n} {A k a v : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tk : Typed (rules lv) Γ k numC) (ta : Typed (rules lv) Γ a A)
    (tv : Typed (rules lv) Γ v (vecC A k)) : Equal (rules lv) Γ (.fst (.pair a v)) a A := by
  have D := vecDeclared_rules lv
  have tS : Typed (rules lv) Γ (.sigma A (Presentation.rename wk (vecC A k))) U0 :=
    D.tower.sigma_small tA (D.vec_typed tA.weaken tk.weaken)
  have tb : Typed (rules lv) Γ v (inst0 a (Presentation.rename wk (vecC A k))) := by
    rw [inst0_rename_wk]
    exact tv
  exact .betaFst tS (D.tower.isUniverse _) ta tb

/-- **Negative control: the head of the empty vector is rejected.** `fst tt` has no type: `tt`
would need a dependent pair type, and its type is the unit type. -/
theorem head_nil_rejected {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed (rules lv) Γ)
    {T : Tm Tower.Head n} : ¬ Typed (rules lv) Γ (.fst ttC) T := by
  intro typing
  obtain ⟨A', B', tp, _⟩ := Typed.generation typing
  obtain ⟨type, w, declared, _, _, le⟩ := Typed.generation tp
  have known : (rules lv).constantType tt = some unitC := rfl
  rw [known] at declared
  obtain rfl := Option.some.inj declared
  have equal : TypeEq (rules lv) Γ unitC (.sigma A' B') :=
    TypeLe.rigid (S := setting lv fun _ => 0) le
      (Typed.isType (S := setting lv fun _ => 0) tp formed) formed
      (fun _ _ e => TypeEq.inductive_ne_head (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_pi (facts lv) roles_unit formed e)
      (fun _ _ e => TypeEq.inductive_ne_sigma (facts lv) roles_unit formed e)
  exact TowerVectors.unit_ne_sigma formed equal

end TowerVectorsPrograms

#print axioms TowerVectorsPrograms.appendMotive_typed
#print axioms TowerVectorsPrograms.appendMethod_typed
#print axioms TowerVectorsPrograms.append_typed
#print axioms TowerVectorsPrograms.appendProgram_typed
#print axioms TowerVectorsPrograms.append_nil
#print axioms TowerVectorsPrograms.append_cons
#print axioms TowerVectorsPrograms.consResult_typed
#print axioms TowerVectorsPrograms.cons_types
#print axioms TowerVectorsPrograms.head_cons
#print axioms TowerVectorsPrograms.head_nil_rejected

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
