import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsCoercion

/-!
# Transport of vectors along proved equations between lengths

The package of `TowerVectorsModel` declares the based eliminator of identity types, `id-elim`,
beside the eliminator of vectors. So an equation between lengths that conversion does not see
can be **proved** inside the package and then used:

* `idElim_typed`: `id-elim A x P d y p : P y p`, for `A` in the lowest universe and a motive `P`
  into the universe of the recursors.
* **Transport** (`transport_typed`): for `p : Id num k m` and `v : vec A k`,
  `transport A k m p v : vec A m`, by the identity eliminator with the motive `λ y _. vec A y`.
  It is the identity at reflexivity (`transport_refl`) and stuck on a variable proof
  (`transport_stuck`).
* **`add n zero = n`, proved by induction** (`rightZero_typed`): the recursor of numbers with the
  motive `λ n. Id num (add n zero) n`; the successor case is the identity eliminator with the
  motive `λ y _. Id num (succ (add k zero)) (succ y)`.
* **The coercion by the proof** (`transport_rightZero_typed`):
  `transport A (add n zero) n (add-right-zero n) v : vec A n` for `v : vec A (add n zero)`, at every
  length `n`. At the closed length `zero` the proof computes to reflexivity and the transport
  disappears (`transport_rightZero_zero`).

The negative control is `TowerVectorsConversion.vec_right_zero_apart`: without a transport, the
two types are apart.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

namespace TowerVectorsIdentity

variable (lv : LevelExpr Nat)

/-! ## The identity eliminator in the package -/

/-- `id-elim A x P d y p`. -/
abbrev idElimC {n : Nat} (A x P d y p : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.app (.app (.const idElim) A) x) P) d) y) p

/-- The eliminator's equation: at reflexivity, the method. -/
theorem idElim_step {n : Nat} (A x P d y z : Tm Tower.Head n) :
    (rules lv).computation.step (idElimC A x P d y (.refl z)) d :=
  RootComputation.step_unionAll mem_idElim ⟨A, x, P, d, y, z, rfl, rfl⟩

/-- **The eliminator applies**: `id-elim A x P d y p : P y p`. -/
theorem idElim_typed {n : Nat} {Γ : Ctx Tower.Head n} {A x P d y p : Tm Tower.Head n}
    (tA : Typed (rules lv) Γ A U0) (tx : Typed (rules lv) Γ x A)
    (tP : Typed (rules lv) Γ P
      (.pi A (.pi (.id (Presentation.rename wk A) (Presentation.rename wk x) (.var 0))
        (.head (.sort lv)))))
    (td : Typed (rules lv) Γ d (.app (.app P x) (.refl x))) (ty : Typed (rules lv) Γ y A)
    (tp : Typed (rules lv) Γ p (.id A x y)) :
    Typed (rules lv) Γ (idElimC A x P d y p) (.app (.app P y) p) := by
  have m₀ : SubstMor (rules lv) .nil Γ fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (elimTelescope u (.sort lv)) Γ
      (consSub p (consSub y (consSub d (consSub P (consSub x (consSub A fun i => Fin.elim0 i)))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tx)
      tP) td) ty) tp
  exact (declaresIdElim lv (fun _ => 0) (E := declarative (rules lv))).typed_app mor

/-! ## Transport of vectors -/

/-- The motive of the transport: `λ y _. vec A y`. -/
def transportMotive {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (vecC (Presentation.rename wk (Presentation.rename wk A)) (.var 1)))

/-- **The transport** of a vector `v : vec A k` along `p : Id num k m`. -/
def transportTm {n : Nat} (A k m p v : Tm Tower.Head n) : Tm Tower.Head n :=
  idElimC numC k (transportMotive A) v m p

/-- The context of the transport's variables:
`A : U0, k m : num, p : Id num k m, v : vec A k`. -/
abbrev transportCtx : Ctx Tower.Head 5 :=
  .snoc (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC) (.id numC (.var 1) (.var 0)))
    (vecC (.var 3) (.var 2))

theorem transportCtx_formed : CtxFormed (rules lv) transportCtx := by
  have D := vecDeclared_rules lv
  have tk₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 1) numC := .var 1
  have tm₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) numC) (.var 0) numC := .var 0
  have tA₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC)
      (.id numC (.var 1) (.var 0))) (.var 3) U0 := .var 3
  have tk₄ : Typed (rules lv) (.snoc (.snoc (.snoc (.snoc .nil U0) numC) numC)
      (.id numC (.var 1) (.var 0))) (.var 2) numC := .var 2
  exact .snoc (.snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, .idForm D.num_typed (D.tower.isUniverse _) tk₃ tm₃⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₄ tk₄⟩

/-- The motive is a family over the lengths equal to `k`. -/
theorem transportMotive_typed :
    Typed (rules lv) transportCtx (transportMotive (.var 4))
      (.pi numC (.pi (.id numC (.var 4) (.var 0)) (.head (.sort lv)))) := by
  have D := vecDeclared_rules lv
  have tk₆ : Typed (rules lv) (.snoc transportCtx numC) (.var 4) numC := .var 4
  have ty₆ : Typed (rules lv) (.snoc transportCtx numC) (.var 0) numC := .var 0
  have tId : Typed (rules lv) (.snoc transportCtx numC) (.id numC (.var 4) (.var 0)) U0 :=
    .idForm D.num_typed (D.tower.isUniverse _) tk₆ ty₆
  have tA₇ : Typed (rules lv) (.snoc (.snoc transportCtx numC) (.id numC (.var 4) (.var 0))) (.var 6)
      U0 := .var 6
  have ty₇ : Typed (rules lv) (.snoc (.snoc transportCtx numC) (.id numC (.var 4) (.var 0))) (.var 1)
      numC := .var 1
  have tBody : Typed (rules lv) (.snoc (.snoc transportCtx numC) (.id numC (.var 4) (.var 0)))
      (vecC (.var 6) (.var 1)) (.head (.sort lv)) := D.tower.lift (D.vec_typed tA₇ ty₇) lv
  have pInner := Derivable.piForm tId (D.tower.isUniverse _)
    (.headType (D.tower.headTyping _) : Typed (rules lv)
      (.snoc (.snoc transportCtx numC) (.id numC (.var 4) (.var 0))) (.head (.sort lv))
      (.head (.sort (.succ lv)))) (D.tower.isUniverse _) (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _) (.lamIntro pInner (D.tower.isUniverse _) tBody)

/-- **The transport is typed**: `transport A k m p v : vec A m`. -/
theorem transport_typed :
    Typed (rules lv) transportCtx (transportTm (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
      (vecC (.var 4) (.var 2)) := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) transportCtx (.var 3) numC := .var 3
  have tm : Typed (rules lv) transportCtx (.var 2) numC := .var 2
  have tp : Typed (rules lv) transportCtx (.var 1) (.id numC (.var 3) (.var 2)) := .var 1
  have tv : Typed (rules lv) transportCtx (.var 0) (vecC (.var 4) (.var 3)) := .var 0
  have tP := transportMotive_typed lv
  have tAtRefl : Typed (rules lv) transportCtx
      (.app (.app (transportMotive (.var 4)) (.var 3)) (.refl (.var 3))) (.head (.sort lv)) :=
    .appElim (.appElim tP tk) (.reflIntro tk)
  have eRefl : TypeEq (rules lv) transportCtx
      (.app (.app (transportMotive (.var 4)) (.var 3)) (.refl (.var 3))) (vecC (.var 4) (.var 3)) :=
    typeEq_of_reduces_at lv (transportCtx_formed lv)
      (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl)) tAtRefl
  have td : Typed (rules lv) transportCtx (.var 0)
      (.app (.app (transportMotive (.var 4)) (.var 3)) (.refl (.var 3))) :=
    Typed.convType tv eRefl.symm
  have tJ := idElim_typed lv D.num_typed tk tP td tm tp
  have tAtPath : Typed (rules lv) transportCtx
      (.app (.app (transportMotive (.var 4)) (.var 2)) (.var 1)) (.head (.sort lv)) :=
    .appElim (.appElim tP tm) tp
  have ePath : TypeEq (rules lv) transportCtx
      (.app (.app (transportMotive (.var 4)) (.var 2)) (.var 1)) (vecC (.var 4) (.var 2)) :=
    typeEq_of_reduces_at lv (transportCtx_formed lv)
      (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl)) tAtPath
  exact Typed.convType tJ ePath

/-- The context of the transport's equation: `A : U0, k : num, v : vec A k`. -/
abbrev reflCtx : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))

/-- **At reflexivity the transport is the identity**:
`transport A k k (refl k) v ≡ v : vec A k`. -/
theorem transport_refl :
    Equal (rules lv) reflCtx (transportTm (.var 2) (.var 1) (.var 1) (.refl (.var 1)) (.var 0))
      (.var 0) (vecC (.var 2) (.var 1)) := by
  have tA : Typed (rules lv) reflCtx (.var 2) U0 := .var 2
  have tk : Typed (rules lv) reflCtx (.var 1) numC := .var 1
  have tv : Typed (rules lv) reflCtx (.var 0) (vecC (.var 2) (.var 1)) := .var 0
  have m₀ : SubstMor (rules lv) .nil reflCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) transportCtx reflCtx
      (consSub (.var 0) (consSub (.refl (.var 1)) (consSub (.var 1) (consSub (.var 1) (consSub (.var 2)
        fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tk) tk)
      (.reflIntro tk)) tv
  have typing := (transport_typed lv).substitute mor
  have red : Reduces (rules lv)
      (transportTm (.var 2) (.var 1) (.var 1) (.refl (.var 1)) (.var 0) : Tm Tower.Head 3) (.var 0) :=
    .head (.root (idElim_step lv _ _ _ _ _ _)) .refl
  exact (TowerVectors.reduces_preserve (nilCtx_formed lv) red typing).2

/-- **Negative control: the transport is stuck on a variable proof.** `transport A k m p v` is
neutral when `p` is a variable: the identity eliminator computes at reflexivity only. -/
theorem transport_stuck {n : Nat} {A k m v : Tm Tower.Head n} (p : Fin n) :
    Neutral roles (transportTm A k m (.var p) v) ∧
      Whnf (rules lv) roles (transportTm A k m (.var p) v) := by
  have neutral : Neutral roles (transportTm A k m (.var p) v) :=
    Neutral.stuck_single (before := [numC, k, transportMotive A, v, m]) (after := []) roles_idElim rfl
      (.var p)
  exact ⟨neutral, neutral.whnf (shape lv)⟩

/-! ## `add n zero = n`, by induction -/

/-- The motive: `λ n. Id num (add n zero) n`. -/
def rightZeroMotive {n : Nat} : Tm Tower.Head n := .lam (.id numC (addC (.var 0) zeroC) (.var 0))

/-- The motive of the successor case: `λ y _. Id num (succ a) (succ y)`. -/
def apSuccMotive {n : Nat} (a : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.lam (.id numC (succC (Presentation.rename wk (Presentation.rename wk a))) (succC (.var 1))))

/-- The successor case: from `ih : Id num (add k zero) k`, the identity eliminator gives
`Id num (succ (add k zero)) (succ k)`. -/
def rightZeroSucc {n : Nat} : Tm Tower.Head n :=
  .lam (.lam (idElimC numC (addC (.var 1) zeroC) (apSuccMotive (addC (.var 1) zeroC))
    (.refl (succC (addC (.var 1) zeroC))) (.var 1) (.var 0)))

/-- **The proof** `add-right-zero k : Id num (add k zero) k`. -/
def rightZeroTm {n : Nat} (k : Tm Tower.Head n) : Tm Tower.Head n :=
  numRecC rightZeroMotive (.refl zeroC) rightZeroSucc k

/-- The context `n : num`. -/
abbrev numCtx : Ctx Tower.Head 1 := .snoc .nil numC

theorem numCtx_formed : CtxFormed (rules lv) numCtx := by
  have D := vecDeclared_rules lv
  exact .snoc .nil ⟨_, D.tower.isUniverse _, D.num_typed⟩

theorem rightZeroMotive_typed :
    Typed (rules lv) numCtx rightZeroMotive (.pi numC (.head (.sort lv))) := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) (.snoc numCtx numC) (.var 0) numC := .var 0
  have tBody : Typed (rules lv) (.snoc numCtx numC) (.id numC (addC (.var 0) zeroC) (.var 0))
      (.head (.sort lv)) :=
    D.tower.lift (.idForm D.num_typed (D.tower.isUniverse _) (add_typed lv tk D.zero_typed) tk) lv
  have tPi : Typed (rules lv) numCtx (.pi numC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm D.num_typed (D.tower.isUniverse _) (.headType (D.tower.headTyping _)) (D.tower.isUniverse _)
      (D.tower.join _ _)
  exact .lamIntro tPi (D.tower.isUniverse _) tBody

/-- **The case of `zero`**: `refl zero`, since `add zero zero ≡ zero`. -/
theorem rightZeroBase_typed :
    Typed (rules lv) numCtx (.refl zeroC) (.app rightZeroMotive zeroC) := by
  have D := vecDeclared_rules lv
  have natural : Typed (rules lv) numCtx (.refl zeroC) (.id numC zeroC zeroC) :=
    .reflIntro D.zero_typed
  have eId : TypeEq (rules lv) numCtx (.id numC zeroC zeroC) (.id numC (addC zeroC zeroC) zeroC) :=
    ⟨u, D.tower.isUniverse _, .idCong (.refl D.num_typed) (D.tower.isUniverse _)
      (.symm (TowerVectors.add_zero D.zero_typed)) (.refl D.zero_typed)⟩
  have tApp : Typed (rules lv) numCtx (.app rightZeroMotive zeroC) (.head (.sort lv)) :=
    .appElim (rightZeroMotive_typed lv) D.zero_typed
  have eBeta : TypeEq (rules lv) numCtx (.app rightZeroMotive zeroC)
      (.id numC (addC zeroC zeroC) zeroC) :=
    typeEq_of_reduces_at lv (numCtx_formed lv) (.single (.betaPi _ _)) tApp
  exact Typed.convType (Typed.convType natural eId) eBeta.symm

/-- With the predecessor `k : num`. -/
abbrev stepCtx₂ : Ctx Tower.Head 2 := .snoc numCtx numC

/-- With the hypothesis `ih`, at the motive: `Id num (add k zero) k`. -/
abbrev stepCtx₃ : Ctx Tower.Head 3 :=
  .snoc stepCtx₂ (.app (Presentation.rename wk rightZeroMotive) (.var 0))

theorem stepCtx₃_formed : CtxFormed (rules lv) stepCtx₃ := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) stepCtx₂ (.var 0) numC := .var 0
  have tDom : Typed (rules lv) stepCtx₂ (.app (Presentation.rename wk rightZeroMotive) (.var 0))
      (.head (.sort lv)) := .appElim (rightZeroMotive_typed lv).weaken tk
  exact .snoc (.snoc (numCtx_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tDom⟩

/-- The motive of the successor case is a family over the numbers equal to `add k zero`. -/
theorem apSuccMotive_typed :
    Typed (rules lv) stepCtx₃ (apSuccMotive (addC (.var 1) zeroC))
      (.pi numC (.pi (.id numC (addC (.var 2) zeroC) (.var 0)) (.head (.sort lv)))) := by
  have D := vecDeclared_rules lv
  have tk₄ : Typed (rules lv) (.snoc stepCtx₃ numC) (.var 2) numC := .var 2
  have ty₄ : Typed (rules lv) (.snoc stepCtx₃ numC) (.var 0) numC := .var 0
  have tId : Typed (rules lv) (.snoc stepCtx₃ numC) (.id numC (addC (.var 2) zeroC) (.var 0)) U0 :=
    .idForm D.num_typed (D.tower.isUniverse _) (add_typed lv tk₄ D.zero_typed) ty₄
  have tk₅ : Typed (rules lv) (.snoc (.snoc stepCtx₃ numC) (.id numC (addC (.var 2) zeroC) (.var 0)))
      (.var 3) numC := .var 3
  have ty₅ : Typed (rules lv) (.snoc (.snoc stepCtx₃ numC) (.id numC (addC (.var 2) zeroC) (.var 0)))
      (.var 1) numC := .var 1
  have tBody : Typed (rules lv) (.snoc (.snoc stepCtx₃ numC) (.id numC (addC (.var 2) zeroC) (.var 0)))
      (.id numC (succC (addC (.var 3) zeroC)) (succC (.var 1))) (.head (.sort lv)) :=
    D.tower.lift (.idForm D.num_typed (D.tower.isUniverse _)
      (D.succ_typed (add_typed lv tk₅ D.zero_typed)) (D.succ_typed ty₅)) lv
  have pInner := Derivable.piForm tId (D.tower.isUniverse _)
    (.headType (D.tower.headTyping _) : Typed (rules lv)
      (.snoc (.snoc stepCtx₃ numC) (.id numC (addC (.var 2) zeroC) (.var 0))) (.head (.sort lv))
      (.head (.sort (.succ lv)))) (D.tower.isUniverse _) (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _) (.lamIntro pInner (D.tower.isUniverse _) tBody)

/-- **The successor case, at the predecessor**: from `ih : Id num (add k zero) k`, a proof of
`Id num (add (succ k) zero) (succ k)`, the motive at `succ k`. -/
theorem rightZeroSucc_inner :
    Typed (rules lv) stepCtx₃
      (idElimC numC (addC (.var 1) zeroC) (apSuccMotive (addC (.var 1) zeroC))
        (.refl (succC (addC (.var 1) zeroC))) (.var 1) (.var 0))
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (succC (.var 1))) := by
  have D := vecDeclared_rules lv
  have formed := stepCtx₃_formed lv
  have tk : Typed (rules lv) stepCtx₃ (.var 1) numC := .var 1
  have ta : Typed (rules lv) stepCtx₃ (addC (.var 1) zeroC) numC := add_typed lv tk D.zero_typed
  have tM : Typed (rules lv) stepCtx₃ (Presentation.rename wk (Presentation.rename wk rightZeroMotive))
      (.pi numC (.head (.sort lv))) := (rightZeroMotive_typed lv).weaken.weaken
  -- the hypothesis, at the identity type
  have tIhTy : Typed (rules lv) stepCtx₃
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (.var 1))
      (.head (.sort lv)) := .appElim tM tk
  have eIh : TypeEq (rules lv) stepCtx₃
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (.var 1))
      (.id numC (addC (.var 1) zeroC) (.var 1)) :=
    typeEq_of_reduces_at lv formed (.single (.betaPi _ _)) tIhTy
  have tih₀ : Typed (rules lv) stepCtx₃ (.var 0)
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (.var 1)) := .var 0
  have tih : Typed (rules lv) stepCtx₃ (.var 0) (.id numC (addC (.var 1) zeroC) (.var 1)) :=
    Typed.convType tih₀ eIh
  -- the method, at the motive
  have tP := apSuccMotive_typed lv
  have tAtRefl : Typed (rules lv) stepCtx₃
      (.app (.app (apSuccMotive (addC (.var 1) zeroC)) (addC (.var 1) zeroC))
        (.refl (addC (.var 1) zeroC))) (.head (.sort lv)) :=
    .appElim (.appElim tP ta) (.reflIntro ta)
  have eRefl : TypeEq (rules lv) stepCtx₃
      (.app (.app (apSuccMotive (addC (.var 1) zeroC)) (addC (.var 1) zeroC))
        (.refl (addC (.var 1) zeroC)))
      (.id numC (succC (addC (.var 1) zeroC)) (succC (addC (.var 1) zeroC))) :=
    typeEq_of_reduces_at lv formed (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl))
      tAtRefl
  have td : Typed (rules lv) stepCtx₃ (.refl (succC (addC (.var 1) zeroC)))
      (.app (.app (apSuccMotive (addC (.var 1) zeroC)) (addC (.var 1) zeroC))
        (.refl (addC (.var 1) zeroC))) :=
    Typed.convType (.reflIntro (D.succ_typed ta)) eRefl.symm
  have tJ := idElim_typed lv D.num_typed ta tP td tk tih
  -- the result, at the motive of the recursor
  have tAtPath : Typed (rules lv) stepCtx₃
      (.app (.app (apSuccMotive (addC (.var 1) zeroC)) (.var 1)) (.var 0)) (.head (.sort lv)) :=
    .appElim (.appElim tP tk) tih
  have ePath : TypeEq (rules lv) stepCtx₃
      (.app (.app (apSuccMotive (addC (.var 1) zeroC)) (.var 1)) (.var 0))
      (.id numC (succC (addC (.var 1) zeroC)) (succC (.var 1))) :=
    typeEq_of_reduces_at lv formed (.head (.congAppFun (.betaPi _ _)) (.head (.betaPi _ _) .refl))
      tAtPath
  have eAdd : TypeEq (rules lv) stepCtx₃ (.id numC (succC (addC (.var 1) zeroC)) (succC (.var 1)))
      (.id numC (addC (succC (.var 1)) zeroC) (succC (.var 1))) :=
    ⟨u, D.tower.isUniverse _, .idCong (.refl D.num_typed) (D.tower.isUniverse _)
      (.symm (TowerVectors.add_succ tk D.zero_typed)) (.refl (D.succ_typed tk))⟩
  have tTarget : Typed (rules lv) stepCtx₃
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (succC (.var 1)))
      (.head (.sort lv)) := .appElim tM (D.succ_typed tk)
  have eTarget : TypeEq (rules lv) stepCtx₃
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (succC (.var 1)))
      (.id numC (addC (succC (.var 1)) zeroC) (succC (.var 1))) :=
    typeEq_of_reduces_at lv formed (.single (.betaPi _ _)) tTarget
  exact Typed.convType (Typed.convType (Typed.convType tJ ePath) eAdd) eTarget.symm

/-- **The case of a successor**, at the type the recursor asks for. -/
theorem rightZeroSucc_typed :
    Typed (rules lv) numCtx rightZeroSucc
      (.pi numC (.pi (.app (Presentation.rename wk rightZeroMotive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (succC (.var 1))))) := by
  have D := vecDeclared_rules lv
  have tk₂ : Typed (rules lv) stepCtx₂ (.var 0) numC := .var 0
  have tk₃ : Typed (rules lv) stepCtx₃ (.var 1) numC := .var 1
  have tDom : Typed (rules lv) stepCtx₂ (.app (Presentation.rename wk rightZeroMotive) (.var 0))
      (.head (.sort lv)) := .appElim (rightZeroMotive_typed lv).weaken tk₂
  have tCod : Typed (rules lv) stepCtx₃
      (.app (Presentation.rename wk (Presentation.rename wk rightZeroMotive)) (succC (.var 1)))
      (.head (.sort lv)) := .appElim (rightZeroMotive_typed lv).weaken.weaken (D.succ_typed tk₃)
  have pInner := Derivable.piForm tDom (D.tower.isUniverse _) tCod (D.tower.isUniverse _)
    (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _)
    (.lamIntro pInner (D.tower.isUniverse _) (rightZeroSucc_inner lv))

/-- **`add n zero = n` is proved in the package**, for a variable `n`:
`add-right-zero n : Id num (add n zero) n`. Conversion does not identify the two sides
(`TowerVectorsConversion.add_right_zero_apart`). -/
theorem rightZero_typed :
    Typed (rules lv) numCtx (rightZeroTm (.var 0)) (.id numC (addC (.var 0) zeroC) (.var 0)) := by
  have tn : Typed (rules lv) numCtx (.var 0) numC := .var 0
  obtain ⟨w, hw, typed⟩ := TowerNumbersModel.recType_typed lv
  have tc : Typed (rules lv) numCtx (.const numRec) (liftClosed (recType num (.sort lv) ctors)) :=
    .const rfl (Derivable.mono (sub_numbers₂ lv) typed) hw
  have m₀ : SubstMor (rules lv) .nil numCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele num (.sort lv) ctors) numCtx
      (consSub (.var 0) (consSub rightZeroSucc (consSub (.refl zeroC)
        (consSub rightZeroMotive fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ (rightZeroMotive_typed lv))
      (rightZeroBase_typed lv)) (rightZeroSucc_typed lv)) tn
  have tRec : Typed (rules lv) numCtx (rightZeroTm (.var 0)) (.app rightZeroMotive (.var 0)) :=
    Typed.telescope_apply mor tc
  have tApp : Typed (rules lv) numCtx (.app rightZeroMotive (.var 0)) (.head (.sort lv)) :=
    .appElim (rightZeroMotive_typed lv) tn
  have e : TypeEq (rules lv) numCtx (.app rightZeroMotive (.var 0))
      (.id numC (addC (.var 0) zeroC) (.var 0)) :=
    typeEq_of_reduces_at lv (numCtx_formed lv) (.single (.betaPi _ _)) tApp
  exact Typed.convType tRec e

/-! ## The coercion by the proof -/

open TowerVectorsCoercion (castCtx castCtx_formed zeroCtx zeroCtx_formed)

/-- **Transport along the proved equation**: in the context
`A : U0, n : num, v : vec A (add n zero)`,
`transport A (add n zero) n (add-right-zero n) v : vec A n`. -/
theorem transport_rightZero_typed :
    Typed (rules lv) castCtx
      (transportTm (.var 2) (addC (.var 1) zeroC) (.var 1) (rightZeroTm (.var 1)) (.var 0))
      (vecC (.var 2) (.var 1)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) castCtx (.var 2) U0 := .var 2
  have tn : Typed (rules lv) castCtx (.var 1) numC := .var 1
  have tv : Typed (rules lv) castCtx (.var 0) (vecC (.var 2) (addC (.var 1) zeroC)) := .var 0
  have m₀ : SubstMor (rules lv) .nil castCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have proofMor : SubstMor (rules lv) numCtx castCtx (consSub (.var 1) fun i => Fin.elim0 i) :=
    SubstMor.cons m₀ tn
  have tProof : Typed (rules lv) castCtx (rightZeroTm (.var 1))
      (.id numC (addC (.var 1) zeroC) (.var 1)) := (rightZero_typed lv).substitute proofMor
  have mor : SubstMor (rules lv) transportCtx castCtx
      (consSub (.var 0) (consSub (rightZeroTm (.var 1)) (consSub (.var 1)
        (consSub (addC (.var 1) zeroC) (consSub (.var 2) fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA)
      (add_typed lv tn D.zero_typed)) tn) tProof) tv
  exact (transport_typed lv).substitute mor

/-- **At the closed length `zero` the proof computes to reflexivity and the transport
disappears**: `transport A (add zero zero) zero (add-right-zero zero) v ≡ v : vec A zero`. -/
theorem transport_rightZero_zero :
    Equal (rules lv) zeroCtx
      (transportTm (.var 1) (addC zeroC zeroC) zeroC (rightZeroTm zeroC) (.var 0)) (.var 0)
      (vecC (.var 1) zeroC) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) zeroCtx (.var 1) U0 := .var 1
  have tv : Typed (rules lv) zeroCtx (.var 0) (vecC (.var 1) (addC zeroC zeroC)) := .var 0
  have m₀ : SubstMor (rules lv) .nil zeroCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) castCtx zeroCtx
      (consSub (.var 0) (consSub zeroC (consSub (.var 1) fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) D.zero_typed) tv
  have typing := (transport_rightZero_typed lv).substitute mor
  have red : Reduces (rules lv)
      (transportTm (.var 1) (addC zeroC zeroC) zeroC (rightZeroTm zeroC) (.var 0) : Tm Tower.Head 2)
      (.var 0) := by
    refine .head (.congAppArg (.root (num_zero_step lv _ _ _))) ?_
    refine .head (.root (idElim_step lv _ _ _ _ _ _)) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (zeroCtx_formed lv) red typing).2

end TowerVectorsIdentity

#print axioms TowerVectorsIdentity.idElim_typed
#print axioms TowerVectorsIdentity.transport_typed
#print axioms TowerVectorsIdentity.transport_refl
#print axioms TowerVectorsIdentity.transport_stuck
#print axioms TowerVectorsIdentity.rightZero_typed
#print axioms TowerVectorsIdentity.transport_rightZero_typed
#print axioms TowerVectorsIdentity.transport_rightZero_zero

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
