import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.VectorFunction

/-!
# The rows of `append`, typed after their match

The declaration-time typing check of a row is the step's check after the match: the row's right side,
made at the call's declared type, must be typed at every solution of what matching its left side
teaches. For `append`, whose length argument is inaccessible, the match teaches the length.

* **The `nil` row** is the clause `vappend nil ys = ys` (`VectorAppend.vappend_typedAfterMatch`): the
  match teaches `m ≐ 0`.
* **The `cons` row** (`consRow_typedAfterMatch`): over `k, ys : vec k, m', x, xs : vec m', m`, the match
  teaches `m ≐ succ m'`, and the right side `cons (add m' k) x (append m' k xs ys)`, whose type is
  `vec (succ (add m' k))`, is typed at the declared `vec (add m k)`: at every solution `m` is `succ m'`,
  and `add (succ m') k` computes to `succ (add m' k)`.

So both rows of the vector function pass the typing check of the definitional class, in the step's own
package with addition and append declared computing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.VectorRows

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make)
open ProgrammingOnTheStep.VectorPackage
open VectorFunction (VecStep vecComputation arules)

/-- The level model of the package with addition and append computing. -/
abbrev alevels : LevelModel arules Nat := declareLevels levels vecComputation

theorem atyped {n : Nat} {Γ : Tower.Ctx n} {t A : Tower.Tm n} (typed : Typed rules Γ t A) :
    Typed arules Γ t A :=
  typed_declare vecComputation typed

/-- `nat` over any frame. -/
def anat (Γ : Context arules) : TypeOver Γ := ⟨natC, u0, .sort _, atyped (nat_typed _)⟩

/-- The frame `k : nat`. -/
abbrev ctxK : Context arules := extend (empty arules) (anat _)

/-- `vec k`. -/
def vecK : TypeOver ctxK := ⟨vecC (.var 0), u0, .sort _, atyped (vec_typed (Derivable.var (R := rules) (Γ := ctxK.raw) 0))⟩

/-- `k, ys : vec k`. -/
abbrev ctxKY : Context arules := extend ctxK vecK

/-- `k, ys, m'`. -/
abbrev ctxKYM : Context arules := extend ctxKY (anat _)

/-- `k, ys, m', x`. -/
abbrev ctxKYMX : Context arules := extend ctxKYM (anat _)

/-- `vec m'`, over `k, ys, m', x`. -/
def vecM' : TypeOver ctxKYMX :=
  ⟨vecC (.var 1), u0, .sort _, atyped (vec_typed (Derivable.var (R := rules) (Γ := ctxKYMX.raw) 1))⟩

/-- `k, ys, m', x, xs : vec m'`. -/
abbrev ctxPattern : Context arules := extend ctxKYMX vecM'

/-- The call frame `k, ys, m', x, xs, m`. -/
abbrev consFrame : Context arules := extend ctxPattern (anat _)

/-- The declared result type `vec (add m k)`. -/
def consCallType : TypeOver consFrame :=
  ⟨vecC (addC (.var 0) (.var 5)), u0, .sort _,
    atyped (vec_typed (add_typed (Derivable.var (R := rules) (Γ := consFrame.raw) 0)
      (Derivable.var (R := rules) (Γ := consFrame.raw) 5)))⟩

/-- **The cons row**: `cons (add m' k) x (append m' k xs ys)` at `vec (add m k)`. -/
def consRow : Make consFrame :=
  ⟨consCallType, consC (addC (.var 3) (.var 5)) (.var 2) (appendC (.var 3) (.var 5) (.var 1) (.var 4))⟩

/-- `succ m'`, over the pattern frame. -/
def succM' : Term ctxPattern (anat _) :=
  ⟨succC (.var 2), atyped (succ_typed (Derivable.var (R := rules) (Γ := ctxPattern.raw) 2))⟩

/-- **What matching `cons m' x xs` at `vec m` teaches**: `m ≐ succ m'`. -/
def matchCons : Equation (TotalTerm consFrame) := Elimination.definition ctxPattern succM'

theorem addConst {n : Nat} (Γ : Tower.Ctx n) : Typed arules Γ (.const addN) (.pi natC (.pi natC natC)) :=
  atyped (.const declared_add addTy_typed (.sort _))

theorem vecConst {n : Nat} (Γ : Tower.Ctx n) : Typed arules Γ (.const vecN) (.pi natC U0) :=
  atyped (.const declared_vec vecTy_typed (.sort _))

theorem succConst {n : Nat} (Γ : Tower.Ctx n) : Typed arules Γ (.const succN) (.pi natC natC) :=
  atyped (.const declared_succ succTy_typed (.sort _))

/-- The right side of the cons row, typed in the row's frame at `vec (succ (add m' k))`. -/
theorem consCode_typed : Typed arules consFrame.raw
    (consC (addC (.var 3) (.var 5)) (.var 2) (appendC (.var 3) (.var 5) (.var 1) (.var 4)))
    (vecC (succC (addC (.var 3) (.var 5)))) := by
  have m' : Typed arules consFrame.raw (.var 3) natC := Derivable.var (3 : Fin 6)
  have k : Typed arules consFrame.raw (.var 5) natC := Derivable.var (5 : Fin 6)
  have x : Typed arules consFrame.raw (.var 2) natC := Derivable.var (2 : Fin 6)
  have xs : Typed arules consFrame.raw (.var 1) (vecC (.var 3)) := Derivable.var (1 : Fin 6)
  have ys : Typed arules consFrame.raw (.var 4) (vecC (.var 5)) := Derivable.var (4 : Fin 6)
  have sum : Typed arules consFrame.raw (addC (.var 3) (.var 5)) natC := .appElim (.appElim (addConst _) m') k
  have appendRaw := Derivable.appElim (Derivable.appElim (Derivable.appElim (Derivable.appElim
    (atyped (append_const_typed consFrame.raw)) m') k) xs) ys
  have consRaw := Derivable.appElim (Derivable.appElim (Derivable.appElim
    (atyped (cons_const_typed consFrame.raw)) sum) x) appendRaw
  exact consRaw

/-- **The cons row is typed after its match.** -/
theorem consRow_typedAfterMatch :
    TypedAfterMatch alevels ([matchCons] : EquationStore (TotalTerm consFrame)) consRow := by
  rw [typedAfterMatch_iff]
  intro Θ τ solved
  have mSucc : Equal arules Θ.raw (τ.substitution 0) (succC (τ.substitution 3)) natC :=
    (solved matchCons (List.mem_singleton_self _)).2
  have kT : Typed arules Θ.raw (τ.substitution 5) natC := τ.typed 5
  have m'T : Typed arules Θ.raw (τ.substitution 3) natC := τ.typed 3
  have sumT : Typed arules Θ.raw (addC (τ.substitution 3) (τ.substitution 5)) natC :=
    .appElim (.appElim (addConst _) m'T) kT
  have consT : Typed arules Θ.raw
      (Presentation.subst τ.substitution
        (consC (addC (.var 3) (.var 5)) (.var 2) (appendC (.var 3) (.var 5) (.var 1) (.var 4))))
      (vecC (succC (addC (τ.substitution 3) (τ.substitution 5)))) :=
    consCode_typed.substitute τ.typed
  have toSucc : Equal arules Θ.raw (addC (τ.substitution 0) (τ.substitution 5))
      (addC (succC (τ.substitution 3)) (τ.substitution 5)) natC :=
    .appCong (.appCong (.refl (addConst _)) mSucc) (.refl kT)
  have computes : Equal arules Θ.raw (addC (succC (τ.substitution 3)) (τ.substitution 5))
      (succC (addC (τ.substitution 3) (τ.substitution 5))) natC :=
    .root (declare_step (VecStep.addSucc (τ.substitution 3) (τ.substitution 5)))
      (.appElim (.appElim (addConst _) (.appElim (succConst _) m'T)) kT)
      (.appElim (succConst _) sumT)
  have vecEq : Equal arules Θ.raw (vecC (addC (τ.substitution 0) (τ.substitution 5)))
      (vecC (succC (addC (τ.substitution 3) (τ.substitution 5)))) U0 :=
    .appCong (.refl (vecConst _)) (.trans toSucc computes)
  exact .conv consT (.symm vecEq) (.sort _)

/-- **Both rows of `append` pass the typing check after their match**: the `nil` row is the step's
clause `vappend nil ys = ys`. -/
theorem append_rows_typed :
    TypedAfterMatch VectorAppend.vlevels [VectorAppend.matchNil] VectorAppend.vappendRow ∧
      TypedAfterMatch alevels ([matchCons] : EquationStore (TotalTerm consFrame)) consRow :=
  ⟨VectorAppend.vappend_typedAfterMatch, consRow_typedAfterMatch⟩

end NativeTypesOnTheStep.Computing.VectorRows

#print axioms NativeTypesOnTheStep.Computing.VectorRows.consRow_typedAfterMatch
#print axioms NativeTypesOnTheStep.Computing.VectorRows.append_rows_typed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
