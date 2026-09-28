import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectChurch

/-!
# Formation in the annotation of the object package

Typings in the annotated calculus of the object package (`objectChurch`), the
counterpart of the formation lemmas of `ExecutableModel/Typings.lean`:

* formation of dependent function, pair and identity types at a universe level,
  and the raise of `U₀` into `U₁`;
* each declared constant the executable package's right-hand sides use, at its
  annotated declared type: the declared types have no abstraction, so their
  annotation is themselves (`objectChurch_declared`), and each is formed in the
  empty context.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Annotated
open Package (jName numRecName eqAtName sucMoveName transportName iterName U0 numT jType
  numRecType eqAtType sucMoveType transportType iterType)

namespace CodeModel

/-! ## Annotated terms of the tower -/

section Terms

variable {n : Nat}

/-- The universe at a level. -/
abbrev cU (l : LevelExpr) : CTm Tower.Head n := .head (.sort l)
abbrev cU0 : CTm Tower.Head n := cU Tower.zero
abbrev cU1 : CTm Tower.Head n := cU (.succ Tower.zero)
abbrev cnum : CTm Tower.Head n := .const numN
abbrev cset : CTm Tower.Head n := .const setN
abbrev czero : CTm Tower.Head n := .const zeroN
abbrev csuc (x : CTm Tower.Head n) : CTm Tower.Head n := .app (.const sucN) x
abbrev cadd (a b : CTm Tower.Head n) : CTm Tower.Head n := .app (.app (.const addN) a) b
abbrev ceqAt (x : CTm Tower.Head n) : CTm Tower.Head n := .app (.const eqAtName) x

end Terms

/-! ## Formation at a universe level -/

section Toolkit

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem cuniv_typed (l : LevelExpr) : CTyped objectChurch Γ (cU l) (cU (.succ l)) :=
  .headType (.sort l)

theorem cU0_typed : CTyped objectChurch Γ cU0 cU1 := cuniv_typed Tower.zero

/-- A type of `U₀` is a type of `U₁`. -/
theorem craise {T : CTm Tower.Head n} (typed : CTyped objectChurch Γ T cU0) :
    CTyped objectChurch Γ T cU1 :=
  CDerivable.cumul typed (fun valuation => by simp [LevelExpr.eval, Tower.zero])

theorem cpiT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr}
    (domain : CTyped objectChurch Γ D (cU l))
    (codomain : CTyped objectChurch (.snoc Γ D) B (cU l)) :
    CTyped objectChurch Γ (.pi D B) (cU l) :=
  CDerivable.cumul (.piForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

theorem csigmaT {D : CTm Tower.Head n} {B : CTm Tower.Head (n + 1)} {l : LevelExpr}
    (domain : CTyped objectChurch Γ D (cU l))
    (codomain : CTyped objectChurch (.snoc Γ D) B (cU l)) :
    CTyped objectChurch Γ (.sigma D B) (cU l) :=
  CDerivable.cumul (.sigmaForm domain (.sort l) codomain (.sort l) (.sorts l l))
    (fun valuation => by simp [LevelExpr.eval])

theorem cidT {C a b : CTm Tower.Head n} {l : LevelExpr}
    (carrier : CTyped objectChurch Γ C (cU l)) (left : CTyped objectChurch Γ a C)
    (right : CTyped objectChurch Γ b C) : CTyped objectChurch Γ (.id C a b) (cU l) :=
  .idForm carrier (.sort l) left right

/-- A declared type without abstractions is its own annotation. -/
theorem objectChurch_declared {c : DeclName} {T : Tm Tower.Head 0}
    (declared : objectRules.constantType c = some T) (lf : lamFree T = true) :
    objectChurch.constantType c = some (liftTm T) := by
  rw [objectChurch_constantType]
  exact elabDeclarations_lamFree objectRules.constantType declared lf

/-- A declared constant at its annotated declared type. -/
theorem cconst {c : DeclName} (T : Tm Tower.Head 0) {l : LevelExpr}
    (declared : objectRules.constantType c = some T) (lf : lamFree T = true)
    (typed : CTyped objectChurch .nil (liftTm T) (cU l)) :
    CTyped objectChurch Γ (.const c) (liftTm T).liftClosed :=
  .const (objectChurch_declared declared lf) typed (.sort l)

end Toolkit

/-! ## The numbers and the sets -/

section Numbers

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem cnum_typed : CTyped objectChurch Γ cnum cU0 :=
  cconst (c := numN) U0 (l := .succ Tower.zero) (by decide) (by decide) cU0_typed

theorem cset_typed : CTyped objectChurch Γ cset cU0 :=
  cconst (c := setN) U0 (l := .succ Tower.zero) (by decide) (by decide) cU0_typed

theorem czero_typed : CTyped objectChurch Γ czero cnum :=
  cconst (c := zeroN) numT (l := Tower.zero) (by decide) (by decide) cnum_typed

theorem csucConst_typed : CTyped objectChurch Γ (.const sucN) (.pi cnum cnum) :=
  cconst (c := sucN) (.pi numT numT) (l := Tower.zero) (by decide) (by decide)
    (cpiT cnum_typed cnum_typed)

theorem csuc_typed {a : CTm Tower.Head n} (ta : CTyped objectChurch Γ a cnum) :
    CTyped objectChurch Γ (csuc a) cnum :=
  .appElim (B := cnum) csucConst_typed ta

theorem caddConst_typed : CTyped objectChurch Γ (.const addN) (.pi cnum (.pi cnum cnum)) :=
  cconst (c := addN) addType (l := Tower.zero) (by decide) (by decide)
    (cpiT cnum_typed (cpiT cnum_typed cnum_typed))

theorem cadd_typed {a b : CTm Tower.Head n} (ta : CTyped objectChurch Γ a cnum)
    (tb : CTyped objectChurch Γ b cnum) : CTyped objectChurch Γ (cadd a b) cnum :=
  .appElim (B := cnum) (.appElim (B := .pi cnum cnum) caddConst_typed ta) tb

theorem cpowerConst_typed : CTyped objectChurch Γ (.const powerN) (.pi cset cset) :=
  cconst (c := powerN) powerType (l := Tower.zero) (by decide) (by decide)
    (cpiT cset_typed cset_typed)

theorem cpowConst_typed : CTyped objectChurch Γ (.const powN) (.pi cnum (.pi cset cset)) :=
  cconst (c := powN) powType (l := Tower.zero) (by decide) (by decide)
    (cpiT cnum_typed (cpiT cset_typed cset_typed))

end Numbers

/-! ## The recursor and the identity eliminator -/

section Declared

variable {n : Nat} {Γ : CCtx Tower.Head n}

/-- The annotated type of `num-rec`. -/
theorem numRecType_formed : CTyped objectChurch .nil (liftTm numRecType) cU1 := by
  show CTyped objectChurch .nil
    (.pi (.pi cnum cU0) (.pi (.app (.var 0) czero)
      (.pi (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1)))))
        (.pi cnum (.app (.var 3) (.var 0)))))) cU1
  have tMotive : CTyped objectChurch .nil (.pi cnum cU0) cU1 :=
    cpiT (craise cnum_typed) cU0_typed
  let Γ₁ : CCtx Tower.Head 1 := .snoc .nil (.pi cnum cU0)
  have tZeroCase : CTyped objectChurch Γ₁ (.app (.var 0) czero) cU0 :=
    .appElim (B := cU0) (.var 0) czero_typed
  let Γ₂ : CCtx Tower.Head 2 := .snoc Γ₁ (.app (.var 0) czero)
  let Γ₃ : CCtx Tower.Head 3 := .snoc Γ₂ cnum
  have tHyp : CTyped objectChurch Γ₃ (.app (.var 2) (.var 0)) cU0 :=
    .appElim (B := cU0) (.var 2) (.var 0)
  let Γ₄ : CCtx Tower.Head 4 := .snoc Γ₃ (.app (.var 2) (.var 0))
  have tGoal : CTyped objectChurch Γ₄ (.app (.var 3) (csuc (.var 1))) cU0 :=
    .appElim (B := cU0) (.var 3) (csuc_typed (.var 1))
  have tSucCase : CTyped objectChurch Γ₂
      (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1))))) cU0 :=
    cpiT cnum_typed (cpiT tHyp tGoal)
  let Γ₅ : CCtx Tower.Head 3 :=
    .snoc Γ₂ (.pi cnum (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (csuc (.var 1)))))
  have tBody : CTyped objectChurch (.snoc Γ₅ cnum) (.app (.var 3) (.var 0)) cU0 :=
    .appElim (B := cU0) (.var 3) (.var 0)
  exact cpiT tMotive (cpiT (craise tZeroCase) (cpiT (craise tSucCase)
    (cpiT (craise cnum_typed) (craise tBody))))

theorem cnumRec_typed :
    CTyped objectChurch Γ (.const numRecName) (liftTm numRecType).liftClosed :=
  cconst numRecType (by decide) (by decide) numRecType_formed

/-- The annotated type of the identity eliminator. -/
theorem jType_formed : CTyped objectChurch .nil (liftTm jType) cU1 := by
  show CTyped objectChurch .nil
    (.pi cU0 (.pi (.var 0)
      (.pi (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
        (.pi (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
          (.pi (.var 3) (.pi (.id (.var 4) (.var 3) (.var 0))
            (.app (.app (.var 3) (.var 1)) (.var 0)))))))) cU1
  let Γ₁ : CCtx Tower.Head 1 := .snoc .nil cU0
  let Γ₂ : CCtx Tower.Head 2 := .snoc Γ₁ (.var 0)
  have tMotiveInner : CTyped objectChurch (.snoc Γ₂ (.var 1))
      (.pi (.id (.var 2) (.var 1) (.var 0)) cU0) cU1 :=
    cpiT (craise (cidT (.var 2) (.var 1) (.var 0))) cU0_typed
  have tMotive : CTyped objectChurch Γ₂ (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
      cU1 :=
    cpiT (craise (.var 1)) tMotiveInner
  let Γ₃ : CCtx Tower.Head 3 := .snoc Γ₂ (.pi (.var 1) (.pi (.id (.var 2) (.var 1) (.var 0)) cU0))
  have tMx := CDerivable.appElim (P := objectChurch) (Γ := Γ₃) (.var 0) (.var 1)
  have tRefl : CTyped objectChurch Γ₃ (.refl (.var 1)) (.id (.var 2) (.var 1) (.var 1)) :=
    .reflIntro (.var 1)
  have tCase : CTyped objectChurch Γ₃ (.app (.app (.var 0) (.var 1)) (.refl (.var 1))) cU0 :=
    .appElim (B := cU0) tMx tRefl
  let Γ₄ : CCtx Tower.Head 4 := .snoc Γ₃ (.app (.app (.var 0) (.var 1)) (.refl (.var 1)))
  let Γ₅ : CCtx Tower.Head 5 := .snoc Γ₄ (.var 3)
  let Γ₆ : CCtx Tower.Head 6 := .snoc Γ₅ (.id (.var 4) (.var 3) (.var 0))
  have tPy := CDerivable.appElim (P := objectChurch) (Γ := Γ₆) (.var 3) (.var 1)
  have tResult : CTyped objectChurch Γ₆ (.app (.app (.var 3) (.var 1)) (.var 0)) cU0 :=
    .appElim (B := cU0) tPy (.var 0)
  have tPath : CTyped objectChurch Γ₅
      (.pi (.id (.var 4) (.var 3) (.var 0)) (.app (.app (.var 3) (.var 1)) (.var 0))) cU1 :=
    cpiT (craise (cidT (.var 4) (.var 3) (.var 0))) (craise tResult)
  exact cpiT cU0_typed (cpiT (craise (.var 0)) (cpiT tMotive (cpiT (craise tCase)
    (cpiT (craise (.var 3)) tPath))))

theorem cj_typed : CTyped objectChurch Γ (.const jName) (liftTm jType).liftClosed :=
  cconst jType (by decide) (by decide) jType_formed

end Declared

/-! ## The definitions' declared types -/

section Definitions

variable {n : Nat} {Γ : CCtx Tower.Head n}

theorem ceqAtConst_typed : CTyped objectChurch Γ (.const eqAtName) (.pi cnum cU0) :=
  cconst eqAtType (l := .succ Tower.zero) (by decide) (by decide)
    (cpiT (craise cnum_typed) cU0_typed)

theorem ceqAt_typed {a : CTm Tower.Head n} (ta : CTyped objectChurch Γ a cnum) :
    CTyped objectChurch Γ (ceqAt a) cU0 :=
  .appElim (B := cU0) ceqAtConst_typed ta

theorem sucMoveType_formed : CTyped objectChurch .nil (liftTm sucMoveType) cU0 := by
  show CTyped objectChurch .nil
    (.pi cnum (.pi (ceqAt (.var 0)) (ceqAt (csuc (.var 1))))) cU0
  exact cpiT cnum_typed (cpiT (ceqAt_typed (.var 0)) (ceqAt_typed (csuc_typed (.var 1))))

theorem csucMove_typed :
    CTyped objectChurch Γ (.const sucMoveName) (liftTm sucMoveType).liftClosed :=
  cconst sucMoveType (by decide) (by decide) sucMoveType_formed

/-- The step type `Π x : A. P x → Σ y : A. P y` over the context `A, P`. -/
theorem cstepFamily_formed {Δ : CCtx Tower.Head n} :
    CTyped objectChurch (.snoc (.snoc Δ cU0) (.pi (.var 0) cU0))
      (.pi (.var 1) (.pi (.app (.var 1) (.var 0))
        (.sigma (.var 3) (.app (.var 3) (.var 0))))) cU0 :=
  cpiT (.var 1) (cpiT (.appElim (B := cU0) (.var 1) (.var 0))
    (csigmaT (.var 3) (.appElim (B := cU0) (.var 3) (.var 0))))

theorem transportType_formed : CTyped objectChurch .nil (liftTm transportType) cU1 := by
  show CTyped objectChurch .nil
    (.pi cU0 (.pi (.pi (.var 0) cU0)
      (.pi (.pi (.var 1) (.var 2))
        (.pi (.pi (.var 2) (.pi (.app (.var 2) (.var 0)) (.app (.var 3) (.app (.var 2) (.var 1)))))
          (.pi (.var 3) (.pi (.app (.var 3) (.var 0))
            (.sigma (.var 5) (.app (.var 5) (.var 0))))))))) cU1
  exact cpiT cU0_typed (cpiT (cpiT (craise (.var 0)) cU0_typed)
    (cpiT (craise (cpiT (.var 1) (.var 2)))
      (cpiT
        (craise (cpiT (.var 2)
          (cpiT (.appElim (B := cU0) (.var 2) (.var 0))
            (.appElim (B := cU0) (.var 3) (.appElim (B := .var 5) (.var 2) (.var 1))))))
        (cpiT (craise (.var 3))
          (cpiT (craise (.appElim (B := cU0) (.var 3) (.var 0)))
            (craise (csigmaT (.var 5) (.appElim (B := cU0) (.var 5) (.var 0)))))))))

theorem ctransport_typed :
    CTyped objectChurch Γ (.const transportName) (liftTm transportType).liftClosed :=
  cconst transportType (by decide) (by decide) transportType_formed

theorem iterType_formed : CTyped objectChurch .nil (liftTm iterType) cU1 := by
  show CTyped objectChurch .nil
    (.pi cnum (.pi cU0 (.pi (.pi (.var 0) cU0)
      (.pi (.pi (.var 1) (.pi (.app (.var 1) (.var 0)) (.sigma (.var 3) (.app (.var 3) (.var 0)))))
        (.pi (.var 2) (.pi (.app (.var 2) (.var 0))
          (.sigma (.var 4) (.app (.var 4) (.var 0))))))))) cU1
  exact cpiT (craise cnum_typed) (cpiT cU0_typed (cpiT (cpiT (craise (.var 0)) cU0_typed)
    (cpiT (craise cstepFamily_formed)
      (cpiT (craise (.var 2))
        (cpiT (craise (.appElim (B := cU0) (.var 2) (.var 0)))
          (craise (csigmaT (.var 4) (.appElim (B := cU0) (.var 4) (.var 0)))))))))

theorem citer_typed :
    CTyped objectChurch Γ (.const iterName) (liftTm iterType).liftClosed :=
  cconst iterType (by decide) (by decide) iterType_formed

end Definitions

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
