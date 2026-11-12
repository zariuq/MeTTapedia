import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsLookup
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerVectorsConversion

/-!
# A coercion of vectors along a length equation that conversion does not see

Addition recurses on its first argument, so `vec A (add n zero)` and `vec A n` are different
types at a variable `n` (`TowerVectorsConversion.vec_right_zero_apart`). The way across is a
program of the package: the coercion

  `cast A n : vec A (add n zero) → vec A n`

by the recursor of numbers with the motive `λ k. vec A (add k zero) → vec A k`, a function type
computed from the length. At `zero` it is the identity, since `vec A (add zero zero) ≡ vec A zero`;
at a successor it rebuilds the vector, `λ k ih v. pair (fst v) (ih (snd v))`, since
`vec A (add (succ k) zero) ≡ vec A (succ (add k zero))`.

* `cast_typed`: the coercion is typed, for a vector of any length.
* `cast_zero`, `cast_succ`: it computes on the constructors,
  `cast A zero v ≡ v` and `cast A (succ k) (pair a w) ≡ pair a (cast A k w)`.
* `append_right_nil_typed`: `cast A n (append A n zero xs tt) : vec A n`. Without the coercion the
  two types are apart (`append_right_nil_types_apart`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerVectorsModel TowerVectorsPrograms TowerVectorsLookup
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

namespace TowerVectorsCoercion

variable (lv : LevelExpr Nat)

/-! ## The program -/

/-- The motive: `λ k. vec A (add k zero) → vec A k`. -/
def castMotive {n : Nat} (A : Tm Tower.Head n) : Tm Tower.Head n :=
  .lam (.pi (vecC (Presentation.rename wk A) (addC (.var 0) zeroC))
    (vecC (Presentation.rename wk (Presentation.rename wk A)) (.var 1)))

/-- At `zero`: the identity. -/
def castZero {n : Nat} : Tm Tower.Head n := .lam (.var 0)

/-- At a successor: `λ k ih v. pair (fst v) (ih (snd v))`. -/
def castSucc {n : Nat} : Tm Tower.Head n :=
  .lam (.lam (.lam (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0))))))

/-- **The coercion** `cast A k v`, for `v : vec A (add k zero)`. -/
def castTm {n : Nat} (A k v : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (numRecC (castMotive A) castZero castSucc k) v

/-- The context of the coercion's variables: `A : U0, n : num, v : vec A (add n zero)`. -/
abbrev castCtx : Ctx Tower.Head 3 :=
  .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (addC (.var 0) zeroC))

theorem castCtx_formed : CtxFormed (rules lv) castCtx := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tn : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 0) numC := .var 0
  exact .snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA (add_typed lv tn D.zero_typed)⟩

/-- The motive is a family of types over the numbers. -/
theorem castMotive_typed :
    Typed (rules lv) castCtx (castMotive (.var 2)) (.pi numC (.head (.sort lv))) := by
  have D := vecDeclared_rules lv
  have tA₄ : Typed (rules lv) (.snoc castCtx numC) (.var 3) U0 := .var 3
  have tk₄ : Typed (rules lv) (.snoc castCtx numC) (.var 0) numC := .var 0
  have tDom : Typed (rules lv) (.snoc castCtx numC) (vecC (.var 3) (addC (.var 0) zeroC)) U0 :=
    D.vec_typed tA₄ (add_typed lv tk₄ D.zero_typed)
  have tA₅ : Typed (rules lv) (.snoc (.snoc castCtx numC) (vecC (.var 3) (addC (.var 0) zeroC)))
      (.var 4) U0 := .var 4
  have tk₅ : Typed (rules lv) (.snoc (.snoc castCtx numC) (vecC (.var 3) (addC (.var 0) zeroC)))
      (.var 1) numC := .var 1
  have tBody : Typed (rules lv) (.snoc castCtx numC)
      (.pi (vecC (.var 3) (addC (.var 0) zeroC)) (vecC (.var 4) (.var 1))) (.head (.sort lv)) :=
    D.tower.lift (D.tower.pi_small tDom (D.vec_typed tA₅ tk₅)) lv
  have tPi : Typed (rules lv) castCtx (.pi numC (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm D.num_typed (D.tower.isUniverse _) (.headType (D.tower.headTyping _)) (D.tower.isUniverse _)
      (D.tower.join _ _)
  exact .lamIntro tPi (D.tower.isUniverse _) tBody

/-- **The case of `zero`**: the identity, since `vec A (add zero zero) ≡ vec A zero`. -/
theorem castZero_typed :
    Typed (rules lv) castCtx castZero (.app (castMotive (.var 2)) zeroC) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) castCtx (.var 2) U0 := .var 2
  have tDom : Typed (rules lv) castCtx (vecC (.var 2) (addC zeroC zeroC)) U0 :=
    D.vec_typed tA (add_typed lv D.zero_typed D.zero_typed)
  have tA' : Typed (rules lv) (.snoc castCtx (vecC (.var 2) (addC zeroC zeroC))) (.var 3) U0 := .var 3
  have tCod : Typed (rules lv) (.snoc castCtx (vecC (.var 2) (addC zeroC zeroC))) (vecC (.var 3) zeroC)
      U0 := D.vec_typed tA' D.zero_typed
  have tv₀ : Typed (rules lv) (.snoc castCtx (vecC (.var 2) (addC zeroC zeroC))) (.var 0)
      (vecC (.var 3) (addC zeroC zeroC)) := .var 0
  have tv : Typed (rules lv) (.snoc castCtx (vecC (.var 2) (addC zeroC zeroC))) (.var 0)
      (vecC (.var 3) zeroC) :=
    Typed.convType tv₀ (vec_congr lv tA' (TowerVectors.add_zero D.zero_typed))
  have natural : Typed (rules lv) castCtx castZero
      (.pi (vecC (.var 2) (addC zeroC zeroC)) (vecC (.var 3) zeroC)) :=
    .lamIntro (D.tower.pi_small tDom tCod) (D.tower.isUniverse _) tv
  have tApp : Typed (rules lv) castCtx (.app (castMotive (.var 2)) zeroC) (.head (.sort lv)) :=
    .appElim (castMotive_typed lv) D.zero_typed
  have e : TypeEq (rules lv) castCtx (.app (castMotive (.var 2)) zeroC)
      (.pi (vecC (.var 2) (addC zeroC zeroC)) (vecC (.var 3) zeroC)) :=
    typeEq_of_reduces_at lv (castCtx_formed lv) (.single (.betaPi _ _)) tApp
  exact Typed.convType natural e.symm

/-- With the predecessor `k : num`. -/
abbrev succCtx₄ : Ctx Tower.Head 4 := .snoc castCtx numC

/-- With the hypothesis `ih`, at the motive: `vec A (add k zero) → vec A k`. -/
abbrev succCtx₅ : Ctx Tower.Head 5 :=
  .snoc succCtx₄ (.app (Presentation.rename wk (castMotive (.var 2))) (.var 0))

/-- With the vector `v : vec A (add (succ k) zero)`. -/
abbrev succCtx₆ : Ctx Tower.Head 6 := .snoc succCtx₅ (vecC (.var 4) (addC (succC (.var 1)) zeroC))

theorem succCtx₅_formed : CtxFormed (rules lv) succCtx₅ := by
  have D := vecDeclared_rules lv
  have tk : Typed (rules lv) succCtx₄ (.var 0) numC := .var 0
  have tDom : Typed (rules lv) succCtx₄ (.app (Presentation.rename wk (castMotive (.var 2))) (.var 0))
      (.head (.sort lv)) := .appElim (castMotive_typed lv).weaken tk
  exact .snoc (.snoc (castCtx_formed lv) ⟨_, D.tower.isUniverse _, D.num_typed⟩)
    ⟨_, D.tower.isUniverse _, tDom⟩

theorem succCtx₆_formed : CtxFormed (rules lv) succCtx₆ := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) succCtx₅ (.var 4) U0 := .var 4
  have tk : Typed (rules lv) succCtx₅ (.var 1) numC := .var 1
  exact .snoc (succCtx₅_formed lv)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA (add_typed lv (D.succ_typed tk) D.zero_typed)⟩

/-- In the successor case the vector is a pair, since
`vec A (add (succ k) zero) ≡ vec A (succ (add k zero))`; its tail goes through the hypothesis. -/
theorem castSucc_inner :
    Typed (rules lv) succCtx₆ (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0))))
      (vecC (.var 5) (succC (.var 2))) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) succCtx₆ (.var 5) U0 := .var 5
  have tk : Typed (rules lv) succCtx₆ (.var 2) numC := .var 2
  have tlen : Typed (rules lv) succCtx₆ (addC (.var 2) zeroC) numC := add_typed lv tk D.zero_typed
  have tv₀ : Typed (rules lv) succCtx₆ (.var 0) (vecC (.var 5) (addC (succC (.var 2)) zeroC)) := .var 0
  have tv : Typed (rules lv) succCtx₆ (.var 0) (vecC (.var 5) (succC (addC (.var 2) zeroC))) :=
    Typed.convType tv₀ (vec_congr lv tA (TowerVectors.add_succ tk D.zero_typed))
  have tfst : Typed (rules lv) succCtx₆ (.fst (.var 0)) (.var 5) := D.fst_typed tA tlen tv
  have tsnd : Typed (rules lv) succCtx₆ (.snd (.var 0)) (vecC (.var 5) (addC (.var 2) zeroC)) :=
    D.snd_typed tA tlen tv
  have tM : Typed (rules lv) succCtx₆
      (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk (castMotive (.var 2)))))
      (.pi numC (.head (.sort lv))) := (castMotive_typed lv).weaken.weaken.weaken
  have tIhTy : Typed (rules lv) succCtx₆
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (castMotive (.var 2))))) (.var 2)) (.head (.sort lv)) := .appElim tM tk
  have eIh : TypeEq (rules lv) succCtx₆
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (castMotive (.var 2))))) (.var 2))
      (.pi (vecC (.var 5) (addC (.var 2) zeroC)) (vecC (.var 6) (.var 3))) :=
    typeEq_of_reduces_at lv (succCtx₆_formed lv) (.single (.betaPi _ _)) tIhTy
  have tih₀ : Typed (rules lv) succCtx₆ (.var 1)
      (.app (Presentation.rename wk (Presentation.rename wk (Presentation.rename wk
        (castMotive (.var 2))))) (.var 2)) := .var 1
  have tih : Typed (rules lv) succCtx₆ (.var 1)
      (.pi (vecC (.var 5) (addC (.var 2) zeroC)) (vecC (.var 6) (.var 3))) := Typed.convType tih₀ eIh
  have tcall : Typed (rules lv) succCtx₆ (.app (.var 1) (.snd (.var 0))) (vecC (.var 5) (.var 2)) :=
    .appElim tih tsnd
  exact D.cons_typed tA tk tfst tcall

/-- **The case of a successor**, at the type the recursor asks for. -/
theorem castSucc_typed :
    Typed (rules lv) castCtx castSucc
      (.pi numC (.pi (.app (Presentation.rename wk (castMotive (.var 2))) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk (castMotive (.var 2))))
          (succC (.var 1))))) := by
  have D := vecDeclared_rules lv
  have tk₄ : Typed (rules lv) succCtx₄ (.var 0) numC := .var 0
  have tk₅ : Typed (rules lv) succCtx₅ (.var 1) numC := .var 1
  have tA₅ : Typed (rules lv) succCtx₅ (.var 4) U0 := .var 4
  have tA₆ : Typed (rules lv) succCtx₆ (.var 5) U0 := .var 5
  have tk₆ : Typed (rules lv) succCtx₆ (.var 2) numC := .var 2
  have tDom : Typed (rules lv) succCtx₄ (.app (Presentation.rename wk (castMotive (.var 2))) (.var 0))
      (.head (.sort lv)) := .appElim (castMotive_typed lv).weaken tk₄
  have tCod : Typed (rules lv) succCtx₅
      (.app (Presentation.rename wk (Presentation.rename wk (castMotive (.var 2)))) (succC (.var 1)))
      (.head (.sort lv)) := .appElim (castMotive_typed lv).weaken.weaken (D.succ_typed tk₅)
  have tSource : Typed (rules lv) succCtx₅ (vecC (.var 4) (addC (succC (.var 1)) zeroC)) U0 :=
    D.vec_typed tA₅ (add_typed lv (D.succ_typed tk₅) D.zero_typed)
  have tTarget : Typed (rules lv) succCtx₆ (vecC (.var 5) (succC (.var 2))) U0 :=
    D.vec_typed tA₆ (D.succ_typed tk₆)
  have natural : Typed (rules lv) succCtx₅
      (.lam (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))))
      (.pi (vecC (.var 4) (addC (succC (.var 1)) zeroC)) (vecC (.var 5) (succC (.var 2)))) :=
    .lamIntro (D.tower.pi_small tSource tTarget) (D.tower.isUniverse _) (castSucc_inner lv)
  have e : TypeEq (rules lv) succCtx₅
      (.app (Presentation.rename wk (Presentation.rename wk (castMotive (.var 2)))) (succC (.var 1)))
      (.pi (vecC (.var 4) (addC (succC (.var 1)) zeroC)) (vecC (.var 5) (succC (.var 2)))) :=
    typeEq_of_reduces_at lv (succCtx₅_formed lv) (.single (.betaPi _ _)) tCod
  have tInner : Typed (rules lv) succCtx₅
      (.lam (.pair (.fst (.var 0)) (.app (.var 1) (.snd (.var 0)))))
      (.app (Presentation.rename wk (Presentation.rename wk (castMotive (.var 2)))) (succC (.var 1))) :=
    Typed.convType natural e.symm
  have pInner := Derivable.piForm tDom (D.tower.isUniverse _) tCod (D.tower.isUniverse _)
    (D.tower.join _ _)
  have pOuter := Derivable.piForm D.num_typed (D.tower.isUniverse _) pInner (D.tower.isUniverse _)
    (D.tower.join _ _)
  exact .lamIntro pOuter (D.tower.isUniverse _) (.lamIntro pInner (D.tower.isUniverse _) tInner)

/-- **The coercion is typed**: `cast A n v : vec A n` for `v : vec A (add n zero)`, at every
length. -/
theorem cast_typed :
    Typed (rules lv) castCtx (castTm (.var 2) (.var 1) (.var 0)) (vecC (.var 2) (.var 1)) := by
  have tn : Typed (rules lv) castCtx (.var 1) numC := .var 1
  have tv : Typed (rules lv) castCtx (.var 0) (vecC (.var 2) (addC (.var 1) zeroC)) := .var 0
  obtain ⟨w, hw, typed⟩ := TowerNumbersModel.recType_typed lv
  have tc : Typed (rules lv) castCtx (.const numRec) (liftClosed (recType num (.sort lv) ctors)) :=
    .const rfl (Derivable.mono (sub_numbers₂ lv) typed) hw
  have m₀ : SubstMor (rules lv) .nil castCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) (recTele num (.sort lv) ctors) castCtx
      (consSub (.var 1) (consSub castSucc (consSub castZero
        (consSub (castMotive (.var 2)) fun i => Fin.elim0 i)))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ (castMotive_typed lv))
      (castZero_typed lv)) (castSucc_typed lv)) tn
  have tRec : Typed (rules lv) castCtx (numRecC (castMotive (.var 2)) castZero castSucc (.var 1))
      (.app (castMotive (.var 2)) (.var 1)) := Typed.telescope_apply mor tc
  have tApp : Typed (rules lv) castCtx (.app (castMotive (.var 2)) (.var 1)) (.head (.sort lv)) :=
    .appElim (castMotive_typed lv) tn
  have e : TypeEq (rules lv) castCtx (.app (castMotive (.var 2)) (.var 1))
      (.pi (vecC (.var 2) (addC (.var 1) zeroC)) (vecC (.var 3) (.var 2))) :=
    typeEq_of_reduces_at lv (castCtx_formed lv) (.single (.betaPi _ _)) tApp
  exact .appElim (Typed.convType tRec e) tv

/-! ## Computation on the constructors -/

/-- The context of the first equation: `A : U0, v : vec A (add zero zero)`. -/
abbrev zeroCtx : Ctx Tower.Head 2 := .snoc (.snoc .nil U0) (vecC (.var 0) (addC zeroC zeroC))

theorem zeroCtx_formed : CtxFormed (rules lv) zeroCtx := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) (.snoc .nil U0) (.var 0) U0 := .var 0
  exact .snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA (add_typed lv D.zero_typed D.zero_typed)⟩

/-- **At length zero the coercion is the identity**: `cast A zero v ≡ v : vec A zero`. -/
theorem cast_zero :
    Equal (rules lv) zeroCtx (castTm (.var 1) zeroC (.var 0)) (.var 0) (vecC (.var 1) zeroC) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) zeroCtx (.var 1) U0 := .var 1
  have tv : Typed (rules lv) zeroCtx (.var 0) (vecC (.var 1) (addC zeroC zeroC)) := .var 0
  have m₀ : SubstMor (rules lv) .nil zeroCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) castCtx zeroCtx
      (consSub (.var 0) (consSub zeroC (consSub (.var 1) fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) D.zero_typed) tv
  have typing := (cast_typed lv).substitute mor
  have red : Reduces (rules lv) (castTm (.var 1) zeroC (.var 0) : Tm Tower.Head 2) (.var 0) := by
    refine .head (.congAppFun (.root (num_zero_step lv _ _ _))) ?_
    refine .head (.betaPi _ _) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (zeroCtx_formed lv) red typing).2

/-- The context of the second equation: `A : U0, k : num, a : A, w : vec A (add k zero)`. -/
abbrev stepCtx : Ctx Tower.Head 4 :=
  .snoc (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (vecC (.var 2) (addC (.var 1) zeroC))

theorem stepCtx_formed : CtxFormed (rules lv) stepCtx := by
  have D := vecDeclared_rules lv
  have tA₂ : Typed (rules lv) (.snoc (.snoc .nil U0) numC) (.var 1) U0 := .var 1
  have tA₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (.var 2) U0 := .var 2
  have tk₃ : Typed (rules lv) (.snoc (.snoc (.snoc .nil U0) numC) (.var 1)) (.var 1) numC := .var 1
  exact .snoc (.snoc (.snoc (.snoc .nil ⟨_, D.tower.isUniverse _, D.tower.u0_typed⟩)
    ⟨_, D.tower.isUniverse _, D.num_typed⟩) ⟨_, D.tower.isUniverse _, tA₂⟩)
    ⟨_, D.tower.isUniverse _, D.vec_typed tA₃ (add_typed lv tk₃ D.zero_typed)⟩

/-- **At a successor the coercion goes under the constructor**:
`cast A (succ k) (pair a w) ≡ pair a (cast A k w) : vec A (succ k)`. -/
theorem cast_succ :
    Equal (rules lv) stepCtx (castTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)))
      (.pair (.var 1) (castTm (.var 3) (.var 2) (.var 0))) (vecC (.var 3) (succC (.var 2))) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) stepCtx (.var 3) U0 := .var 3
  have tk : Typed (rules lv) stepCtx (.var 2) numC := .var 2
  have ta : Typed (rules lv) stepCtx (.var 1) (.var 3) := .var 1
  have tw : Typed (rules lv) stepCtx (.var 0) (vecC (.var 3) (addC (.var 2) zeroC)) := .var 0
  have tpair : Typed (rules lv) stepCtx (.pair (.var 1) (.var 0))
      (vecC (.var 3) (addC (succC (.var 2)) zeroC)) :=
    Typed.convType (D.cons_typed tA (add_typed lv tk D.zero_typed) ta tw)
      (vec_congr lv tA (TowerVectors.add_succ tk D.zero_typed)).symm
  have m₀ : SubstMor (rules lv) .nil stepCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have mor : SubstMor (rules lv) castCtx stepCtx
      (consSub (.pair (.var 1) (.var 0)) (consSub (succC (.var 2)) (consSub (.var 3)
        fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) (D.succ_typed tk)) tpair
  have typing := (cast_typed lv).substitute mor
  have red : Reduces (rules lv)
      (castTm (.var 3) (succC (.var 2)) (.pair (.var 1) (.var 0)) : Tm Tower.Head 4)
      (.pair (.var 1) (castTm (.var 3) (.var 2) (.var 0))) := by
    refine .head (.congAppFun (.root (num_succ_step lv _ _ _ _))) ?_
    refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
    refine .head (.congAppFun (.betaPi _ _)) ?_
    refine .head (.betaPi _ _) ?_
    refine .head (.congPairFst (.betaSigmaFst _ _)) ?_
    refine .head (.congPairSnd (.congAppArg (.betaSigmaSnd _ _))) ?_
    exact .refl
  exact (TowerVectors.reduces_preserve (stepCtx_formed lv) red typing).2

/-! ## Append with the empty vector on the right -/

/-- **`append xs nil`, at the length of `xs`**: in the context `A : U0, n : num, xs : vec A n`,
`cast A n (append A n zero xs tt) : vec A n`. -/
theorem append_right_nil_typed :
    Typed (rules lv) nilCtx
      (castTm (.var 2) (.var 1) (appendTm (.var 2) (.var 1) zeroC (.var 0) ttC))
      (vecC (.var 2) (.var 1)) := by
  have D := vecDeclared_rules lv
  have tA : Typed (rules lv) nilCtx (.var 2) U0 := .var 2
  have tn : Typed (rules lv) nilCtx (.var 1) numC := .var 1
  have txs : Typed (rules lv) nilCtx (.var 0) (vecC (.var 2) (.var 1)) := .var 0
  have m₀ : SubstMor (rules lv) .nil nilCtx fun i => Fin.elim0 i := fun i => Fin.elim0 i
  have appendMor : SubstMor (rules lv) appendCtx nilCtx
      (consSub ttC (consSub (.var 0) (consSub zeroC (consSub (.var 1) (consSub (.var 2)
        fun i => Fin.elim0 i))))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tn) D.zero_typed)
      txs) (D.nil_typed tA)
  have tAppend : Typed (rules lv) nilCtx (appendTm (.var 2) (.var 1) zeroC (.var 0) ttC)
      (vecC (.var 2) (addC (.var 1) zeroC)) := (append_typed lv).substitute appendMor
  have castMor : SubstMor (rules lv) castCtx nilCtx
      (consSub (appendTm (.var 2) (.var 1) zeroC (.var 0) ttC) (consSub (.var 1) (consSub (.var 2)
        fun i => Fin.elim0 i))) :=
    SubstMor.cons (SubstMor.cons (SubstMor.cons m₀ tA) tn) tAppend
  exact (cast_typed lv).substitute castMor

/-- **Without the coercion the two types are apart**: `vec A (add n zero)` is not `vec A n`. -/
theorem append_right_nil_types_apart :
    ¬ TypeEq (rules lv) nilCtx (vecC (.var 2) (addC (.var 1) zeroC)) (vecC (.var 2) (.var 1)) :=
  TowerVectorsConversion.vec_right_zero_apart (nilCtx_formed lv) (.var 2) 1

end TowerVectorsCoercion

#print axioms TowerVectorsCoercion.castMotive_typed
#print axioms TowerVectorsCoercion.castZero_typed
#print axioms TowerVectorsCoercion.castSucc_typed
#print axioms TowerVectorsCoercion.cast_typed
#print axioms TowerVectorsCoercion.cast_zero
#print axioms TowerVectorsCoercion.cast_succ
#print axioms TowerVectorsCoercion.append_right_nil_typed
#print axioms TowerVectorsCoercion.append_right_nil_types_apart

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
